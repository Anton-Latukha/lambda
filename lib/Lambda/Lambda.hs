{-# language PatternSynonyms #-}
{-# language PartialTypeSignatures #-}

module Lambda.Lambda
  (
  ) where

-- ** Import

import Lambda.Prelude
import Relude.Extra.Enum (prev, next)
import qualified Text.Show
import Data.Attoparsec.Text
    ( decimal, parseTest, char, parseOnly, string, Parser )
import Data.Functor.Classes ( Eq1(..) )
import Yaya.Fold ( Steppable(..), Projectable(..), Mu(..), lambek, Recursive(..), Algebra, Coalgebra )

-- ** Lambda calculi

-- *** Initial type primitive boundaries

-- **** New type typisation

-- | Bruijn index in lambda term.
-- Index < number of external lambda binds => index == binded lambda value
-- Index >= number of external lambda binds => index == free variable
newtype BruijnIndex = BruijnIndex Int
 deriving (Eq, Enum, Num, Bounded, Show, Generic)

newtype LambdaTermFAppFunc a = LambdaTermFAppFunc (LambdaTermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype LambdaTermFAppParam a = LambdaTermFAppParam (LambdaTermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype LambdaTermFLamBody a = LambdaTermFLamBody (LambdaTermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

-- **** Functorial Lambda term/expression

data LambdaTermF a
  = LambdaTermFBruijnIndex !BruijnIndex
  | LambdaTermFApp    !(LambdaTermFAppFunc a) !(LambdaTermFAppParam a)
  | LambdaTermFLam    !(LambdaTermFLamBody a)
 deriving (Eq, Show, Generic, Functor, Traversable, Foldable)

-- ***** Instances

instance Recursive (->) LambdaTerm LambdaTermF where
  cata :: Algebra (->) LambdaTermF a -> LambdaTerm -> a
  cata φ (LambdaTerm (Mu f)) = f φ

instance Projectable (->) LambdaTerm LambdaTermF where
  project :: Coalgebra (->) LambdaTermF LambdaTerm
  project = lambek

instance Steppable (->) LambdaTerm LambdaTermF where
  embed :: Algebra (->) LambdaTermF LambdaTerm
  embed m = LambdaTerm $ Mu $ \ f -> f $ fmap (cata f) m

instance Eq1 LambdaTermF where
  liftEq :: (a -> b -> Bool) -> LambdaTermF a -> LambdaTermF b -> Bool
  liftEq = go  -- Making shure GHC detects that there is no point to go through typeclass dictionary searches, all other instances derive from here.
   where
    go eq (LambdaTermFLam    b1   ) (LambdaTermFLam    b2   ) = crc go eq b1 b2
    go eq (LambdaTermFApp    f1 p1) (LambdaTermFApp    f2 p2) = crc go eq f1 f2 && crc go eq p1 p2
    go _  (LambdaTermFBruijnIndex idx1 ) (LambdaTermFBruijnIndex idx2 ) = idx1 == idx2
    go _ _ _ = False

-- **** Finished LambdaTerm

newtype LambdaTerm = LambdaTerm (Mu LambdaTermF)
 deriving (Eq, Generic)

-- *** Isomorphism of lambda term to human readable representation

-- | Abstraction for representation of human readable view of the main lambda term datatype
newtype LambdaTermBJHumanReadable = LambdaTermBJHumanReadable LambdaTerm

-- **** Instances

instance Show LambdaTermBJHumanReadable where
  show :: LambdaTermBJHumanReadable -> String
  show = l_showHR . crc
   where
    -- | There is a newtype boundary between main lambda term data type and human readable, code prefers to preserve the general GHC derived @Show@ instances for the general case (showing term/expression internals) for the lambda term and its components, which is why this coersion enforsment is needed.
    l_showHR :: LambdaTerm -> String
    l_showHR =
      caseLambdaTerm
        show
        showApp
        showLam
     where
      showApp :: LambdaTerm -> LambdaTerm -> String
      showApp f a = "(" <> l_showHR f <> ") " <> l_showHR a
      showLam :: LambdaTerm -> String
      showLam b = "\\ " <> l_showHR b

instance Show LambdaTerm where
  show (crc @LambdaTermBJHumanReadable -> a) = show a

-- **** Functions

turnReadable :: LambdaTerm -> Text
turnReadable = show . LambdaTermBJHumanReadable

-- *** Patterns

pattern PatLambdaTermBruijnIndex :: Int -> LambdaTerm
pattern PatLambdaTermBruijnIndex n <- (project -> LambdaTermFBruijnIndex (BruijnIndex n)) where
        PatLambdaTermBruijnIndex n =     embed (  LambdaTermFBruijnIndex (BruijnIndex n))

pattern PatLambdaTermApp :: LambdaTerm -> LambdaTerm -> LambdaTerm
pattern PatLambdaTermApp f a <- (project -> LambdaTermFApp (LambdaTermFAppFunc (embed -> f)) (LambdaTermFAppParam (embed -> a))) where
        PatLambdaTermApp f a =     embed (  LambdaTermFApp (LambdaTermFAppFunc (project  f)) (LambdaTermFAppParam (project  a)))

pattern PatLambdaTermLam :: LambdaTerm -> LambdaTerm
pattern PatLambdaTermLam b <- (project -> LambdaTermFLam (LambdaTermFLamBody (embed -> b))) where
        PatLambdaTermLam b =     embed (  LambdaTermFLam (LambdaTermFLamBody (project  b)))

{-# complete PatLambdaTermBruijnIndex, PatLambdaTermApp, PatLambdaTermLam #-}

-- *** Builders

mkLambdaTermBruijnIndex :: Int -> LambdaTerm
mkLambdaTermBruijnIndex = PatLambdaTermBruijnIndex

mkLambdaTermApp :: LambdaTerm -> LambdaTerm -> LambdaTerm
mkLambdaTermApp = PatLambdaTermApp

mkLambdaTermLam :: LambdaTerm -> LambdaTerm
mkLambdaTermLam = PatLambdaTermLam

-- *** Helpers

-- | Takes a set of for lambda term cases, takes a lambda term, detects term and applies according function to it:
caseLambdaTerm
  :: (Int -> a)     -- ^ For index
  -> (LambdaTerm -> LambdaTerm -> a) -- ^ For application
  -> (LambdaTerm -> a)      -- ^ For function
  -> LambdaTerm            -- ^ Term
  -> a             -- ^ Result
caseLambdaTerm cf ca cl =
 \case
  PatLambdaTermBruijnIndex i -> cf   i
  PatLambdaTermApp       f a -> ca f a
  PatLambdaTermLam         b -> cl   b

-- *** Parser

parserLambdaTerm :: Parser LambdaTerm
parserLambdaTerm =
  bruijnIndexParser <|>
  lambdaParser <|>
  appParser
 where
  bruijnIndexParser :: Parser LambdaTerm
   = mkLambdaTermBruijnIndex <$> decimal
  lambdaParser :: Parser LambdaTerm
   = mkLambdaTermLam <$> (string "\\ " *> bruijnIndexParser)
  appParser :: Parser LambdaTerm
   = mkLambdaTermApp <$> appFuncParser <*> appParamParser
   where
    appFuncParser :: Parser LambdaTerm
     = char '(' *> parserLambdaTerm <* char ')'
    appParamParser :: Parser LambdaTerm
     = char ' ' *> parserLambdaTerm

-- *** Normal form

-- | Normal form lambda term.
newtype NLambdaTerm = NLambdaTerm LambdaTerm

normalize :: LambdaTerm -> NLambdaTerm
normalize = crc .
  caseLambdaTerm
    PatLambdaTermBruijnIndex
    forLambdaApplication
    forLambdaFunction
 where
  forLambdaApplication :: LambdaTerm -> LambdaTerm -> LambdaTerm
  forLambdaApplication =
    flip betaReduce

  forLambdaFunction :: LambdaTerm -> LambdaTerm
  forLambdaFunction =
    PatLambdaTermLam . crc . normalize

  -- | Lambda function application.
  -- Does beta-reduce when lambda term matches definition, otherwise does id.
  -- TODO: Try for this function to return Maybe.
  betaReduce
    :: LambdaTerm -- ^ Argument to bind
    -> LambdaTerm -- ^ Base expression to bind in
    -> LambdaTerm -- ^ Expression with the bind applied
  betaReduce a =
    \case
      (PatLambdaTermLam lb) -> substitute a 0 lb -- Apply value to this level binding
      other -> PatLambdaTermApp other a
   where
    substitute :: LambdaTerm -> BruijnIndex -> LambdaTerm -> LambdaTerm
    substitute v bji =
      caseLambdaTerm
        (\ indx ->
           bool
             (PatLambdaTermBruijnIndex indx)  -- do `id` ("pass")
             v  -- so substitution under index
             $ indexMatches indx
        )
        --  (bool v . PatLambdaTermBruijnIndex <*> isThisThePlace)
        (on PatLambdaTermApp (substituteWithValue bji))
        substituteInDeeperFunction
     where
      indexMatches = (crc bji /=)
      substituteWithValue = substitute v
      -- | Outside Btuijn indexes increase +1 when enterning a scope of deeper function.
      substituteInDeeperFunction = substituteWithValue $! next bji -- 2025-05-05: NOTE: This is considered costly to nameless encoding style. Since it increments/decrements all instances.


-- *** Testing

runOutputUnitTests :: IO ()
runOutputUnitTests =
  traverse_
    (putTextLn . turnReadable)
    lambdaTermUnitTests

-- | Parses only lawful Bruijin lambda terms.
runParserUnitTests :: IO ()
runParserUnitTests =
  traverse_ (parseTest parserLambdaTerm . (<> "\\n") . turnReadable) lambdaTermUnitTests

lambdaTermUnitTests :: Seq LambdaTerm
lambdaTermUnitTests =
  (<>)
    (one mk0)
    ((`mkLambdaTermApp` mk0) <$>
      [ mk0
      , PatLambdaTermLam mk0
      , PatLambdaTermLam mk0
      ]
    )

mk0 :: LambdaTerm
mk0 = mkLambdaTermBruijnIndex 0

turnReadableThenParseBack :: LambdaTerm -> Either String LambdaTerm
turnReadableThenParseBack = parseOnly parserLambdaTerm . (<> "\\n") . turnReadable
