{-# language PatternSynonyms #-}
{-# language PartialTypeSignatures #-}
{-# language StrictData #-}

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

newtype TermFAppFunc a = TermFAppFunc (TermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype TermFAppParam a = TermFAppParam (TermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype TermFLamBody a = TermFLamBody (TermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

-- **** Functorial Lambda term/expression

data TermF a
  = TermFBruijnIndex !BruijnIndex
  | TermFApp    !(TermFAppFunc a) !(TermFAppParam a)
  | TermFLam    !(TermFLamBody a)
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
    go (TermFLam           b1 ) (TermFLam           b2 ) =      crc go b1 b2
    go (TermFApp        f1 p1 ) (TermFApp        f2 p2 ) = (&&) (crc go f1 f2)
                                                                                       (crc go p1 p2)
    go (TermFBruijnIndex idx1 ) (TermFBruijnIndex idx2 ) = (==) idx1
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

pattern PatTermBruijnIndex :: Int -> Term
pattern PatTermBruijnIndex n <- (project -> TermFBruijnIndex (BruijnIndex n)) where
        PatTermBruijnIndex n =     embed (  TermFBruijnIndex (BruijnIndex n))

pattern PatTermApp :: Term -> Term -> Term
pattern PatTermApp f a <- (project -> TermFApp (TermFAppFunc (embed -> f)) (TermFAppParam (embed -> a))) where
        PatTermApp f a =     embed (  TermFApp (TermFAppFunc (project  f)) (TermFAppParam (project  a)))

pattern PatTermLam :: Term -> Term
pattern PatTermLam b <- (project -> TermFLam (TermFLamBody (embed -> b))) where
        PatTermLam b =     embed (  TermFLam (TermFLamBody (project  b)))

{-# complete PatTermBruijnIndex, PatTermApp, PatTermLam #-}

-- *** Builders

mkTermBruijnIndex :: Int -> Term
mkTermBruijnIndex = PatTermBruijnIndex

mkTermApp :: Term -> Term -> Term
mkTermApp = PatTermApp

mkTermLam :: Term -> Term
mkTermLam = PatTermLam

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
  PatTermBruijnIndex i -> cf   i
  PatTermApp       f a -> ca f a
  PatTermLam         b -> cl   b

-- *** Parser

parserTerm :: Parser Term
parserTerm =
  bruijnIndexParser <|>
  lambdaParser <|>
  appParser
 where
  bruijnIndexParser :: Parser Term =
    mkTermBruijnIndex <$> decimal
  lambdaParser :: Parser Term =
    mkTermLam <$> (string "\\ " *> bruijnIndexParser)
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
    PatTermBruijnIndex
    forLambdaApplication
    forLambdaFunction
 where
  forLambdaApplication =
    flip betaReduce

  forLambdaFunction =
    PatTermLam . crc . normalize

  -- | Lambda function application.
  -- Does beta-reduce when lambda term matches definition, otherwise does id.
  -- TODO: Try for this function to return Maybe.
  betaReduce
    :: Term -- ^ Argument to bind
    -> Term -- ^ Base expression to bind in
    -> Term -- ^ Expression with the bind applied
  betaReduce a =
    \case
      (PatTermLam lb) -> substitute a 0 lb -- Apply value to this level binding
      other -> PatTermApp other a
   where
    substitute :: Term -> BruijnIndex -> Term -> Term
    substitute v bji =
      caseTerm
        searchIndexAndSubstituteOnMatch
        recurseIntoBothBranches
        recurseIntoFunction
     where
      searchIndexAndSubstituteOnMatch =
        bool
          v  -- so substitution under index
          . PatTermBruijnIndex -- do `id` ("pass")
          <*> -- patthrough into both branches
            indexNotFound
       where
        indexNotFound = (crc bji /=)
      recurseIntoBothBranches =
        on PatTermApp (substituteWithPermutatedIndex id)
      -- | Outside Btuijn indexes increase +1 when enterning a scope of deeper function.
      --  2025-05-05: NOTE: This is considered costly compared to nameless encoding style. Since it increments/decrements all instances.
      recurseIntoFunction = substituteWithPermutatedIndex next
      substituteWithPermutatedIndex f = substitute v (f bji)

-- *** Testing

mk0 :: Term
mk0 = mkTermBruijnIndex 0

lambdaTermUnitTests :: Seq Term
lambdaTermUnitTests =
  cons
    mk0
    $ (`mkTermApp` mk0) . ($ mk0) <$>
      [ id
      , PatTermLam
      , PatTermLam
      ]

-- | Parse the expression recieved.
-- Wrapper around @parseOnly@, so expects full expression at once, hence strict.
parse' :: Text -> Either Text Term
parse' =
  mapLeft
    fromString
    . parseTermWith parseOnly

-- | Internalizes Term parser, takes utility parser function of parser, and takes Text into it to parse.
parseTermWith :: (Parser Term -> Text -> b) -> Text -> b
parseTermWith f =
  f parserTerm . (<> "\\n")

turnReadableThenParseBack :: Term -> Either Text Term
turnReadableThenParseBack = parse' . turnReadable

