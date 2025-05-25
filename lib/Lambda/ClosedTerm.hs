{-# language PatternSynonyms #-}
{-# language PartialTypeSignatures #-}
{-# language StrictData #-}
{-# options_GHC -Wno-unrecognised-pragmas #-}
{-# hlint ignore "Use camelCase" #-}

-- | The context of this module is closed lambda terms only (aka: lawful lambda term that has no free variables)
module Lambda.ClosedTerm
where

-- ** Import

import Lambda.Prelude
import Lambda.Atom
import Relude.Extra.Enum (next)
import qualified Text.Show
import Data.Attoparsec.Text
    ( decimal, char, parseOnly, string, Parser )
import Data.Functor.Classes ( Eq1(..) )
import Yaya.Fold ( Steppable(..), Projectable(..), Mu(..), lambek, Recursive(..), Algebra, Coalgebra )

-- ** Lambda calculi

-- *** Initial type primitive boundaries

-- **** New type typisation for closed Lambda term

-- | If Lambda term has no free variables, it is called Closed.

newtype F_AppTarget a = F_AppTarget (F a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype F_AppParam a = F_AppParam (F a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype F_LamBody a = F_LamBody (F a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

-- **** Functorial Lambda term/expression

data F a
  = F_BjIx !BjIx
  | F_App    !(F_AppTarget a) !(F_AppParam a)
  | F_Lam    !(F_LamBody a)
 deriving (Eq, Show, Generic, Functor, Traversable, Foldable)

-- ***** Instances

instance Recursive (->) Closed F where
  cata :: Algebra (->) F a -> Closed -> a
  cata φ (Closed (Mu f)) = f φ

instance Projectable (->) Closed F where
  project :: Coalgebra (->) F Closed
  project = lambek

instance Steppable (->) Closed F where
  embed :: Algebra (->) F Closed
  embed m = Closed $ Mu $ \ f -> f $ fmap (cata f) m

instance Eq1 F where
  liftEq :: (a -> b -> Bool) -> F a -> F b -> Bool
  --  2025-05-20: FIXME: eq function `(a -> b -> Bool)` is ignored.
  -- If there was Applicative to `F` the implementation then is `fold $ liftA2 eq a b`
  liftEq _ = go  -- Making shure GHC detects that there is no point to go through typeclass dictionary searches, all other instances derive from here.
   where
    go (F_Lam           b1 ) (F_Lam           b2 ) =      crc go b1 b2
    go (F_App        f1 p1 ) (F_App        f2 p2 ) = (&&) (crc go f1 f2)
                                                         (crc go p1 p2)
    go (F_BjIx idx1 ) (F_BjIx idx2 ) = (==) idx1
                                           idx2
    go _ _ = False

-- **** Finished term

newtype Closed = Closed (Mu F)
 deriving (Eq, Generic)

-- *** Isomorphism of lambda term to human readable representation

-- | Abstraction for representation of human readable view of the closed lambda term datatype
newtype ClosedBJHumanReadable = ClosedBJHumanReadable Closed

-- **** Instances

instance Show ClosedBJHumanReadable where
  show :: ClosedBJHumanReadable -> String
  show = l_showHR . crc
   where
    -- | There is a newtype boundary between main lambda term data type and human readable, code prefers to preserve the general GHC derived @Show@ instances for the general case (showing term/expression internals) for the lambda term and its components, which is why this coersion enforsment is needed.
    l_showHR :: Closed -> String
    l_showHR =
      caseClosed
        show
        showApp
        showLam
     where
      showApp :: Closed -> Closed -> String
      showApp f a = "(" <> l_showHR f <> ") " <> l_showHR a
      showLam :: Closed -> String
      showLam b = "\\ " <> l_showHR b

instance Show Closed where
  show :: Closed -> String
  show (crc @ClosedBJHumanReadable -> a) = show a

-- **** Functions

turnReadable :: Closed -> Text
turnReadable = show . ClosedBJHumanReadable

-- *** Patterns

pattern Pat_BjIx :: Int -> Closed
pattern Pat_BjIx n <- (project -> F_BjIx (BjIx n)) where
        Pat_BjIx n =     embed (  F_BjIx (BjIx n))

pattern Pat_App :: Closed -> Closed -> Closed
pattern Pat_App f a <- (project -> F_App (F_AppTarget (embed -> f)) (F_AppParam (embed -> a))) where
        Pat_App f a =     embed (  F_App (F_AppTarget (project  f)) (F_AppParam (project  a)))

pattern Pat_Lam :: Closed -> Closed
pattern Pat_Lam b <- (project -> F_Lam (F_LamBody (embed -> b))) where
        Pat_Lam b =     embed (  F_Lam (F_LamBody (project  b)))

{-# complete Pat_BjIx, Pat_App, Pat_Lam #-}

-- *** Builders

mkBjIx :: Int -> Closed
mkBjIx = Pat_BjIx

mkApp :: Closed -> Closed -> Closed
mkApp = Pat_App

mkLam :: Closed -> Closed
mkLam = Pat_Lam

-- *** Helpers

-- | Takes a set of for lambda term cases, takes a lambda term, detects term and applies according function to it:
caseClosed
  :: (Int -> a)     -- ^ For index
  -> (Closed -> Closed -> a) -- ^ For application
  -> (Closed -> a)      -- ^ For function
  -> Closed            -- ^ ClosedTerm
  -> a             -- ^ Result
caseClosed cf ca cl =
 \case
  Pat_BjIx i -> cf   i
  Pat_App       f a -> ca f a
  Pat_Lam         b -> cl   b

-- *** Parser

parserClosed :: Parser Closed
parserClosed =
  bjIx <|>
  fn <|>
  app
 where
  bjIx :: Parser Closed =
    mkBjIx <$> decimal
  fn :: Parser Closed =
    mkLam <$> (string "\\ " *> bjIx)
  app :: Parser Closed =
    liftA2
      mkApp
      appFn
      appPar
   where
    appFn :: Parser Closed =
      between '(' ')' parserClosed
    appPar :: Parser Closed =
      char ' ' *> parserClosed
    between bra ket p = char bra *> p <* char ket

-- *** Normal form

-- | Normal form lambda term.
newtype NClosed = NClosed Closed

normalize :: Closed -> NClosed
normalize = crc .
  caseClosed
    Pat_BjIx
    forApplication
    forFn
 where
  forApplication =
    flip betaReduce

  forFn =
    Pat_Lam . crc . normalize

  -- | Lambda function application.
  -- Does beta-reduce when lambda term matches definition, otherwise does id.
  -- TODO: Try for this function to return Maybe.
  betaReduce
    :: Closed -- ^ Argument to bind
    -> Closed -- ^ Base expression to bind in
    -> Closed -- ^ Expression with the bind applied
  betaReduce a =
    \case
      (Pat_Lam lb) -> substitute a 0 lb -- Apply value to this level binding
      other -> Pat_App other a
   where
    substitute :: Closed -> BjIx -> Closed -> Closed
    substitute v bji =
      caseClosed
        searchIndexAndSubstituteOnMatch
        recurseIntoBothBranches
        recurseIntoFunction
     where
      searchIndexAndSubstituteOnMatch =
        bool
          v  -- so substitution under index
          . Pat_BjIx -- do `id` ("pass")
          <*> -- patthrough into both branches
            indexNotFound
       where
        indexNotFound = (crc bji /=)
      recurseIntoBothBranches =
        on Pat_App (substituteWithPermutatedIndex id)
      -- | Outside Btuijn indexes increase +1 when enterning a scope of deeper function.
      --  2025-05-05: NOTE: This is considered costly compared to nameless encoding style. Since it increments/decrements all instances.
      recurseIntoFunction = substituteWithPermutatedIndex next
      substituteWithPermutatedIndex f = substitute v (f bji)

-- *** Testing

mk0 :: Closed
mk0 = mkBjIx 0

unitTests :: Seq Closed
unitTests =
  cons
    mk0
    $ (`mkApp` mk0) . ($ mk0) <$>
      [ id
      , Pat_Lam
      , Pat_Lam
      ]

-- | Parse the expression recieved.
-- Wrapper around @parseOnly@, so expects full expression at once, hence strict.
parse' :: Text -> Either Text Closed
parse' =
  mapLeft
    fromString
    . parseWith parseOnly

-- | Internalizes Closed parser, takes utility parser function of parser, and takes Text into it to parse.
parseWith :: (Parser Closed -> Text -> b) -> Text -> b
parseWith f =
  f parserClosed . (<> "\\n")

turnReadableThenParseBack :: Closed -> Either Text Closed
turnReadableThenParseBack = parse' . turnReadable

