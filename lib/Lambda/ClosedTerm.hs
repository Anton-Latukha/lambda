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

newtype TermF_AppFunc a = TermF_AppFunc (TermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype TermF_AppParam a = TermF_AppParam (TermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype TermF_LamBody a = TermF_LamBody (TermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

-- **** Functorial Lambda term/expression

data TermF a
  = TermF_BjIx !BjIx
  | TermF_App    !(TermF_AppFunc a) !(TermF_AppParam a)
  | TermF_Lam    !(TermF_LamBody a)
 deriving (Eq, Show, Generic, Functor, Traversable, Foldable)

-- ***** Instances

instance Recursive (->) Term TermF where
  cata :: Algebra (->) TermF a -> Term -> a
  cata φ (Term (Mu f)) = f φ

instance Projectable (->) Term TermF where
  project :: Coalgebra (->) TermF Term
  project = lambek

instance Steppable (->) Term TermF where
  embed :: Algebra (->) TermF Term
  embed m = Term $ Mu $ \ f -> f $ fmap (cata f) m

instance Eq1 TermF where
  liftEq :: (a -> b -> Bool) -> TermF a -> TermF b -> Bool
  --  2025-05-20: FIXME: eq function `(a -> b -> Bool)` is ignored.
  -- If there was Applicative to `TermF` the implementation then is `fold $ liftA2 eq a b`
  liftEq _ = go  -- Making shure GHC detects that there is no point to go through typeclass dictionary searches, all other instances derive from here.
   where
    go (TermF_Lam           b1 ) (TermF_Lam           b2 ) =      crc go b1 b2
    go (TermF_App        f1 p1 ) (TermF_App        f2 p2 ) = (&&) (crc go f1 f2)
                                                                                       (crc go p1 p2)
    go (TermF_BjIx idx1 ) (TermF_BjIx idx2 ) = (==) idx1
                                                                                       idx2
    go _ _ = False

-- **** Finished Term

newtype Term = Term (Mu TermF)
 deriving (Eq, Generic)

-- *** Isomorphism of lambda term to human readable representation

-- | Abstraction for representation of human readable view of the closed lambda term datatype
newtype TermBJHumanReadable = TermBJHumanReadable Term

-- **** Instances

instance Show TermBJHumanReadable where
  show :: TermBJHumanReadable -> String
  show = l_showHR . crc
   where
    -- | There is a newtype boundary between main lambda term data type and human readable, code prefers to preserve the general GHC derived @Show@ instances for the general case (showing term/expression internals) for the lambda term and its components, which is why this coersion enforsment is needed.
    l_showHR :: Term -> String
    l_showHR =
      caseTerm
        show
        showApp
        showLam
     where
      showApp :: Term -> Term -> String
      showApp f a = "(" <> l_showHR f <> ") " <> l_showHR a
      showLam :: Term -> String
      showLam b = "\\ " <> l_showHR b

instance Show Term where
  show :: Term -> String
  show (crc @TermBJHumanReadable -> a) = show a

-- **** Functions

turnReadable :: Term -> Text
turnReadable = show . TermBJHumanReadable

-- *** Patterns

pattern PatTerm_BjIx :: Int -> Term
pattern PatTerm_BjIx n <- (project -> TermF_BjIx (BjIx n)) where
        PatTerm_BjIx n =     embed (  TermF_BjIx (BjIx n))

pattern PatTerm_App :: Term -> Term -> Term
pattern PatTerm_App f a <- (project -> TermF_App (TermF_AppFunc (embed -> f)) (TermF_AppParam (embed -> a))) where
        PatTerm_App f a =     embed (  TermF_App (TermF_AppFunc (project  f)) (TermF_AppParam (project  a)))

pattern PatTerm_Lam :: Term -> Term
pattern PatTerm_Lam b <- (project -> TermF_Lam (TermF_LamBody (embed -> b))) where
        PatTerm_Lam b =     embed (  TermF_Lam (TermF_LamBody (project  b)))

{-# complete PatTerm_BjIx, PatTerm_App, PatTerm_Lam #-}

-- *** Builders

mkTermBjIx :: Int -> Term
mkTermBjIx = PatTerm_BjIx

mkTermApp :: Term -> Term -> Term
mkTermApp = PatTerm_App

mkTermLam :: Term -> Term
mkTermLam = PatTerm_Lam

-- *** Helpers

-- | Takes a set of for lambda term cases, takes a lambda term, detects term and applies according function to it:
caseTerm
  :: (Int -> a)     -- ^ For index
  -> (Term -> Term -> a) -- ^ For application
  -> (Term -> a)      -- ^ For function
  -> Term            -- ^ Term
  -> a             -- ^ Result
caseTerm cf ca cl =
 \case
  PatTerm_BjIx i -> cf   i
  PatTerm_App       f a -> ca f a
  PatTerm_Lam         b -> cl   b

-- *** Parser

parserTerm :: Parser Term
parserTerm =
  bjIxParser <|>
  fnParser <|>
  appParser
 where
  bjIxParser :: Parser Term =
    mkTermBjIx <$> decimal
  fnParser :: Parser Term =
    mkTermLam <$> (string "\\ " *> bjIxParser)
  appParser :: Parser Term =
    liftA2
      mkTermApp
      appFuncParser
      appParamParser
   where
    appFuncParser :: Parser Term =
      between '(' ')' parserTerm
    appParamParser :: Parser Term =
      char ' ' *> parserTerm
    between bra ket p = char bra *> p <* char ket

-- *** Normal form

-- | Normal form lambda term.
newtype NTerm = NTerm Term

normalize :: Term -> NTerm
normalize = crc .
  caseTerm
    PatTerm_BjIx
    forApplication
    forFn
 where
  forApplication =
    flip betaReduce

  forFn =
    PatTerm_Lam . crc . normalize

  -- | Lambda function application.
  -- Does beta-reduce when lambda term matches definition, otherwise does id.
  -- TODO: Try for this function to return Maybe.
  betaReduce
    :: Term -- ^ Argument to bind
    -> Term -- ^ Base expression to bind in
    -> Term -- ^ Expression with the bind applied
  betaReduce a =
    \case
      (PatTerm_Lam lb) -> substitute a 0 lb -- Apply value to this level binding
      other -> PatTerm_App other a
   where
    substitute :: Term -> BjIx -> Term -> Term
    substitute v bji =
      caseTerm
        searchIndexAndSubstituteOnMatch
        recurseIntoBothBranches
        recurseIntoFunction
     where
      searchIndexAndSubstituteOnMatch =
        bool
          v  -- so substitution under index
          . PatTerm_BjIx -- do `id` ("pass")
          <*> -- patthrough into both branches
            indexNotFound
       where
        indexNotFound = (crc bji /=)
      recurseIntoBothBranches =
        on PatTerm_App (substituteWithPermutatedIndex id)
      -- | Outside Btuijn indexes increase +1 when enterning a scope of deeper function.
      --  2025-05-05: NOTE: This is considered costly compared to nameless encoding style. Since it increments/decrements all instances.
      recurseIntoFunction = substituteWithPermutatedIndex next
      substituteWithPermutatedIndex f = substitute v (f bji)

-- *** Testing

mk0 :: Term
mk0 = mkTermBjIx 0

unitTests :: Seq Term
unitTests =
  cons
    mk0
    $ (`mkTermApp` mk0) . ($ mk0) <$>
      [ id
      , PatTerm_Lam
      , PatTerm_Lam
      ]

-- | Parse the expression recieved.
-- Wrapper around @parseOnly@, so expects full expression at once, hence strict.
parse' :: Text -> Either Text Term
parse' =
  mapLeft
    fromString
    . parseWith parseOnly

-- | Internalizes Term parser, takes utility parser function of parser, and takes Text into it to parse.
parseWith :: (Parser Term -> Text -> b) -> Text -> b
parseWith f =
  f parserTerm . (<> "\\n")

turnReadableThenParseBack :: Term -> Either Text Term
turnReadableThenParseBack = parse' . turnReadable

