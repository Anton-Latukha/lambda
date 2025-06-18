{-# language PatternSynonyms #-}
{-# language PartialTypeSignatures #-}
{-# language StrictData #-}
{-# options_GHC -Wno-unrecognised-pragmas #-}
{-# hlint ignore "Use camelCase" #-}

-- | This module is about/for:
--   * Lambda terms;
--   * in de Bruijn form;
--   * with lambda binds represented as de Bruijn levels (not de Bruijn indexes, which is classical, because it saves a lot of compute in manipulation. Indexes are reverse numbered from the brunches to the root, which means calculating trees on every manipulation and newertheless to bind variable traking (counting) back up the tree is needed, while levels allow to have an adress map and go to particular level of the branch of the tree;
--   * allows free variables;
--   * input expects only lawful lambda binds (allows only non-negative de Bruijn levels) should bind inside the term scope.
module Lambda.Term.Bruijn.Leveled
where

-- ** Import

import Lambda.Prelude
import Data.Char ( isAlphaNum )
import qualified Text.Show
import Data.Attoparsec.Text
    ( decimal, char, parseOnly, string, Parser)
import Data.Functor.Classes ( Eq1(..) )
import Yaya.Fold ( Steppable(..), Projectable(..), Mu(..), lambek, Recursive(..), Algebra)


-- ** Lambda calculi

-- *** Initial type primitive boundaries

-- **** New type typisation for closed Lambda term

-- | Bruijn lambda in lambda term.
-- | pretty much a bind.
-- Index < number of external lambda binds => index == binded lambda value
-- Index >= number of external lambda binds => index == free variable
newtype LvlBind = LvlBind Natural
 deriving (Eq, Enum, Num, Show, Generic, Ord, Real, Integral)

newtype F_AppTarget a = F_AppTarget (F a)
 deriving (Eq, Eq1, Show, Generic, Functor, Foldable, Traversable)

newtype F_AppParam a = F_AppParam (F a)
 deriving (Eq, Eq1, Show, Generic, Functor, Foldable, Traversable)

newtype F_LamBody a = F_LamBody (F a)
 deriving (Eq, Eq1, Show, Generic, Functor, Foldable, Traversable)

-- | Level of lambda term.
-- Used in reverese to normal brujuin index, and as such does not need to increment the stack under in-depth substitution, and always can relate variable index to level.
-- `throw (Underflow :: ArithException).`
newtype F_LamLvl = F_LamLvl Natural
 deriving (Eq, Show, Generic)

newtype FreeVar = FreeVar Text
 deriving (Eq, Show, Generic)

-- | Value binded to formerly free var.
newtype VarValue = VarValue Text
 deriving (Eq, Show, Generic)

-- | What free vars maps to what.
newtype ContextBinds = ContextBinds (HashMap FreeVar VarValue)
 deriving (Eq, Show, Generic)

-- | Environment to drag into Lambda to be what Bruijn level bind to
newtype LamEnv binding = LamEnv (NonEmpty binding)
 deriving (Eq, Show, Generic, Eq1, Functor, Foldable, Traversable)

-- **** Functorial form of Lambda expression

data F a
  = F_LvlBind    !LvlBind
  | F_Lam     !(F_LamBody a)
  | F_App     !(F_AppTarget a) !(F_AppParam a)
  | F_FreeVar !FreeVar
 deriving (Eq, Show, Generic, Functor, Traversable, Foldable)

-- | Lets `Semigroup` in terms of Lambda Calculus would be simply applying expressions.
instance Semigroup (F a) where
  (<>) :: F a -> F a -> F a
  (<>) fa fb = F_App (crc fa) (crc fb)

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
    go (F_LvlBind idx1 ) (F_LvlBind idx2 ) = (==) idx1
                                           idx2
    go (F_FreeVar bind1 ) (F_FreeVar bind2 ) = (==) bind1
                                             bind2
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
        show
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

-- | Turn level of bind into expression (and back).
pattern Pat_LvlBind :: LvlBind -> Bruijn
pattern Pat_LvlBind n <- (project -> F_LvlBind n) where
        Pat_LvlBind n =    embed ( F_LvlBind n)

-- | Take (or turn back):
-- 1 -> Target of application;
-- 2 -> Parameter to apply to;
-- \therefore: expression of applicaiton.
pattern Pat_App :: Bruijn -> Bruijn -> Bruijn
pattern Pat_App f a <- (project -> F_App (F_AppTarget (embed -> f)) (F_AppParam (embed -> a))) where
        Pat_App f a =    embed ( F_App (F_AppTarget (project f)) (F_AppParam (project a)))

-- | Take expression and wrap it into a lambda (and back).
pattern Pat_Lam :: Bruijn -> Bruijn
pattern Pat_Lam b <- (project -> F_Lam (F_LamBody (embed -> b))) where
        Pat_Lam b =    embed ( F_Lam (F_LamBody (project b)))

-- | Take FreeVar and produce expression primitive (and back).
pattern Pat_FreeVar :: FreeVar -> Bruijn
pattern Pat_FreeVar b <- (project -> F_FreeVar b) where
        Pat_FreeVar b =    embed ( F_FreeVar b)

{-# complete Pat_LvlBind, Pat_App, Pat_Lam, Pat_FreeVar #-}

-- *** Builders

-- | Encode level to bind to into expression.
mkLvlBind :: Natural -> Bruijn
mkLvlBind = Pat_LvlBind . crc

mkApp :: Bruijn -> Bruijn -> Bruijn
mkApp = Pat_App

mkLam :: Bruijn -> Bruijn
mkLam = Pat_Lam

mkFreeVar :: Text -> Bruijn
mkFreeVar = Pat_FreeVar . crc

-- *** Helpers

-- | Takes a set of for lambda term cases, takes a lambda term, detects term and applies according function to it:
caseBruijn
  :: (LvlBind -> a)     -- ^ For index
  -> (Bruijn -> Bruijn -> a) -- ^ For application
  -> (Bruijn -> a)      -- ^ For function
  -> (FreeVar -> a)     -- ^ For free var
  -> Bruijn            -- ^ BruijnTerm
  -> a             -- ^ Result
caseBruijn cf ca cl cv =
 \case
  Pat_LvlBind i -> cf i
  Pat_App   f a -> ca f a
  Pat_Lam     b -> cl b
  Pat_FreeVar b -> cv b

-- *** Parser

-- | Synthax rules follow general guidelines (from Wikipedia)
-- Outermost parentheses are dropped: `M N` instead of `(M N)`.
-- Applications ` ` are assumed to be left-associative: instead of ((M N) P) the M N P may be written.
-- The body of an abstraction extends as far right as possible: λ M N means λ (M N) and not (λ M) N.

--  2025-06-16: NOTE: Implement lexemes (possibly with lexer `Alex`), with parsing `(...)` from any direction, then for ` ` (application) from right, for lambda from the left.

--  2025-06-16: TODO: there is no `FreeVar` support in parser so far.
-- | The most strict outer parser, aka expects only sound expression
parser :: Parser Bruijn
parser =
  app <|>
  lambda <|>
  bind
  -- <|>
  -- isEndOfLine
  -- <|>
  -- freeVar
 where
  app :: Parser Bruijn =
    liftA2
      mkApp
      appFn
      appPar
   where
    appFn :: Parser Bruijn =
      abs (lambda <|> app) <|> bind
    appPar :: Parser Bruijn =
      char ' ' *> (abs app <|> app <|> lambda <|> bind)
    abs p = char '(' *> p <* char ')'
  -- freeVar :: Parser Bruijn =
  --   mkFreeVar <$> takeWhile1 isAlphaNum
  lambda :: Parser Bruijn =
    mkLam <$> ((string "\\ " <|> string "λ ") *> parser)
  bind :: Parser Bruijn =
    mkLvlBind <$> decimal

-- | Internalizes Bruijn parser, takes utility parser function of parser, and takes Text into it to parse.
parseWith :: (Parser Bruijn -> Text -> b) -> Text -> b
parseWith f =
  f parser . (<> "\\n")

-- | Parse the expression recieved.
-- Wrapper around @parseOnly@, so expects full expression at once, hence strict.
parseFull :: Text -> Either Text Bruijn
parseFull =
  mapLeft
    fromString
    . parseWith parseOnly

-- *** Testing

mk0 :: Bruijn
mk0 = mkLvlBind 0

unitTests :: Seq Bruijn
unitTests =
  cons
    mk0
    $ (`mkApp` mk0) . ($ mk0) <$>
      [ id
      , Pat_Lam
      , Pat_Lam
      ]

unitTestsText :: [Text]
unitTestsText =
  [ "λ 0"
  , "λ λ 2"
  , "((λ λ (λ 3) 1) λ 2) 1"
  , "(λ (λ 0) λ 0) ((λ 2) 1)"
  , "(λ λ (λ 0) λ 0) λ 0"
  , "λ (λ 0 (1 1)) λ 0 (1 1)"
  , "1 2 3 4 5 6 7 8 9 10 11 12"
  ]

-- *** Normalization by evaluation (NeB)

-- newtype ContextedTerm = ContextedTerm (ContextBinds a)

-- neb :: ContextedTerm -> Bruijn -> _
-- neb cnt =
--   traverse (replaceFreeVars) lt
--  where
--   findFreeVar f =
--     caseBruijn
--       id
--       id
--       id
--       (\ fv -> lookup fv cnt)
