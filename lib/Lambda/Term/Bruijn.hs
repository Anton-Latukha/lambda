{-# language PatternSynonyms #-}
{-# language PartialTypeSignatures #-}
{-# language StrictData #-}
{-# options_GHC -Wno-unrecognised-pragmas #-}
{-# hlint ignore "Use camelCase" #-}

-- | The context of this module is closed lambda terms only (aka: lawful lambda term that has no free variables)
module Lambda.Term.Bruijn
where

-- ** Import

import Lambda.Prelude
import GHC.Num ( naturalZero )
import Lambda.Atom
import qualified Text.Show
import Data.Attoparsec.Text
    ( decimal, char, parseOnly, parseTest, string, Parser )
import Data.Functor.Classes ( Eq1(..) )
import Yaya.Fold ( Steppable(..), Projectable(..), Mu(..), lambek, Recursive(..), Algebra)

-- ** Lambda calculi

-- *** Initial type primitive boundaries

-- **** New type typisation for closed Lambda term

newtype F_AppTarget a = F_AppTarget (F a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype F_AppParam a = F_AppParam (F a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype F_LamBody a = F_LamBody (F a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

-- | Level of lambda term.
-- Used in reverese to normal brujuin index, and as such does not need to increment the stack under in-depth substitution, and always can relate variable index to level.
-- `throw (Underflow :: ArithException).`
newtype F_LamLvl = F_LamLvl Natural
 deriving (Eq, Show, Generic)

-- **** Functorial Lambda term/expression

data F a
  = F_BjIx !BjIx
  | F_App    !(F_AppTarget a) !(F_AppParam a)
  | F_Lam    !(F_LamBody a)
 deriving (Eq, Show, Generic, Functor, Traversable, Foldable)

-- | Lets `Semigroup` in terms of Lambda Calculus would be simply applying expressions after another (because of also see `Monoid`)
instance Semigroup (F a) where
  (<>) :: F a -> F a -> F a
  (<>) fa fb = F_App (crc fa) (crc fb)

-- | `Monoid` for Lambda Calculus is id function, aka `\ a -> a`
instance Monoid (F a) where
  mempty :: F a
  mempty = F_Lam $ crc $ F_BjIx $ crc naturalZero

-- ***** Instances

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

newtype Bruijn = Bruijn (Mu F)
 deriving (Eq, Generic)

-- ***** Instances for `Bruijn`
-- Are based on the default instances of the `Mu`
instance Recursive (->) Bruijn F where
  cata :: Algebra (->) F a -> Bruijn -> a
  cata φ (Bruijn (Mu f)) = f φ

instance Projectable (->) Bruijn F where
  project :: Bruijn -> F Bruijn
  project = lambek

instance Steppable (->) Bruijn F where
  embed :: Algebra (->) F Bruijn
  embed m = Bruijn $ Mu $ \ f -> f $ fmap (cata f) m

-- *** Isomorphism of lambda term to human readable representation

-- | Abstraction for representation of human readable view of the closed lambda term datatype
newtype BruijnBJHumanReadable = BruijnBJHumanReadable Bruijn

-- **** Instances

instance Show BruijnBJHumanReadable where
  show :: BruijnBJHumanReadable -> String
  show = l_showHR . crc
   where
    -- | There is a newtype boundary between main lambda term data type and human readable, code prefers to preserve the general GHC derived @Show@ instances for the general case (showing term/expression internals) for the lambda term and its components, which is why this coersion enforsment is needed.
    l_showHR :: Bruijn -> String
    l_showHR =
      caseBruijn
        (show . crc @Natural)
        showApp
        showLam
     where
      showApp :: Bruijn -> Bruijn -> String
      showApp f a = "(" <> l_showHR f <> ") " <> l_showHR a
      showLam :: Bruijn -> String
      showLam b = "\\ " <> l_showHR b

instance Show Bruijn where
  show :: Bruijn -> String
  show (crc @BruijnBJHumanReadable -> a) = show a

-- **** Functions

turnReadable :: Bruijn -> Text
turnReadable = show . BruijnBJHumanReadable

-- *** Patterns

pattern Pat_BjIx :: BjIx -> Bruijn
pattern Pat_BjIx n <- (project -> F_BjIx n) where
        Pat_BjIx n =     embed (  F_BjIx n)

pattern Pat_App :: Bruijn -> Bruijn -> Bruijn
pattern Pat_App f a <- (project -> F_App (F_AppTarget (embed -> f)) (F_AppParam (embed -> a))) where
        Pat_App f a =     embed (  F_App (F_AppTarget (project  f)) (F_AppParam (project  a)))

pattern Pat_Lam :: Bruijn -> Bruijn
pattern Pat_Lam b <- (project -> F_Lam (F_LamBody (embed -> b))) where
        Pat_Lam b =     embed (  F_Lam (F_LamBody (project  b)))

{-# complete Pat_BjIx, Pat_App, Pat_Lam #-}

-- *** Builders

mkBjIx :: Natural -> Bruijn
mkBjIx = Pat_BjIx . crc

mkApp :: Bruijn -> Bruijn -> Bruijn
mkApp = Pat_App

mkLam :: Bruijn -> Bruijn
mkLam = Pat_Lam

-- *** Helpers

-- | Takes a set of for lambda term cases, takes a lambda term, detects term and applies according function to it:
caseBruijn
  :: (BjIx -> a)     -- ^ For index
  -> (Bruijn -> Bruijn -> a) -- ^ For application
  -> (Bruijn -> a)      -- ^ For function
  -> Bruijn            -- ^ BruijnTerm
  -> a             -- ^ Result
caseBruijn cf ca cl =
 \case
  Pat_BjIx  i -> cf   i
  Pat_App f a -> ca f a
  Pat_Lam   b -> cl   b

-- *** Parser

parser :: Parser Bruijn
parser =
  bjIx <|>
  fn <|>
  app
 where
  bjIx :: Parser Bruijn =
    mkBjIx <$> decimal
  fn :: Parser Bruijn =
    mkLam <$> (string "\\ " *> bjIx)
  app :: Parser Bruijn =
    liftA2
      mkApp
      appFn
      appPar
   where
    appFn :: Parser Bruijn =
      between '(' ')' parser
    appPar :: Parser Bruijn =
      char ' ' *> parser
    between bra ket p = char bra *> p <* char ket

-- *** Normal form

-- | Normal form lambda term.
newtype NBruijn = NBruijn Bruijn

normalize :: Bruijn -> NBruijn
normalize = crc .
  caseBruijn
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
    :: Bruijn -- ^ Argument to bind
    -> Bruijn -- ^ Base expression to bind in
    -> Bruijn -- ^ Expression with the bind applied
  betaReduce a =
    \case
      (Pat_Lam lb) -> substitute a 0 lb -- Apply value to this level binding
      other -> Pat_App other a
   where
    substitute :: Bruijn -> BjIx -> Bruijn -> Bruijn
    substitute v bji =
      caseBruijn
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
      recurseIntoFunction = substituteWithPermutatedIndex succ
      substituteWithPermutatedIndex f = substitute v (f bji)

-- *** Testing

mk0 :: Bruijn
mk0 = mkBjIx 0

unitTests :: Seq Bruijn
unitTests =
  cons
    mk0
    $ (`mkApp` mk0) . ($ mk0) <$>
      [ id
      , Pat_Lam
      , Pat_Lam
      ]

runUnitTestsWith :: Applicative f => (Bruijn -> f b) -> f ()
runUnitTestsWith f =
  traverse_
    f
    unitTests

runTurnReadableUnitTests :: IO ()
runTurnReadableUnitTests =
  runUnitTestsWith
    (putTextLn . turnReadable)

-- | Parses only lawful Bruijin lambda terms.
runParserUnitTestsFromTurningTermReadable :: IO ()
runParserUnitTestsFromTurningTermReadable =
  runUnitTestsWith
    (parseWith parseTest . turnReadable)

-- | Parse the expression recieved.
-- Wrapper around @parseOnly@, so expects full expression at once, hence strict.
parse' :: Text -> Either Text Bruijn
parse' =
  mapLeft
    fromString
    . parseWith parseOnly

-- | Internalizes Bruijn parser, takes utility parser function of parser, and takes Text into it to parse.
parseWith :: (Parser Bruijn -> Text -> b) -> Text -> b
parseWith f =
  f parser . (<> "\\n")

turnReadableThenParseBack :: Bruijn -> Either Text Bruijn
turnReadableThenParseBack = parse' . turnReadable

