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
module Lambda.Term.Bruijn.Leveled ()
where

-- ** Import

import Lambda.Prelude hiding ( fromEither )
import qualified Text.Show
import Data.Attoparsec.Text
    ( decimal, char, parseOnly, string, Parser)
import Data.Functor.Classes ( Eq1(..) )
import Yaya.Fold ( Steppable(..), Projectable(..), Mu(..), lambek, Recursive(..), Algebra)
import Data.Validation (Validation(..))
import qualified Data.Validation as Validation


-- ** Lambda calculi

-- *** Initial type primitive boundaries

-- **** New type typisation for closed Lambda term

-- | Bruijn lambda in lambda term.
-- | pretty much a bind.
-- Index < number of external lambda binds => index == binded lambda value
-- Index >= number of external lambda binds => index == free variable
newtype LvlBind = LvlBind Natural
 deriving (Eq, Enum, Num, Show, Generic, Ord, Real, Integral)

newtype F_AppTarget b a = F_AppTarget (F b a)
 deriving (Eq, Eq1, Show, Generic, Functor, Foldable, Traversable)

newtype F_AppParam b a = F_AppParam (F b a)
 deriving (Eq, Eq1, Show, Generic, Functor, Foldable, Traversable)

newtype F_LamBody b a = F_LamBody (F b a)
 deriving (Eq, Eq1, Show, Generic, Functor, Foldable, Traversable)

-- | Level of lambda term.
-- Used in reverese to normal brujuin index, and as such does not need to increment the stack under in-depth substitution, and always can relate variable index to level.
-- `throw (Underflow :: ArithException).`
newtype F_LamLvl = F_LamLvl Natural
 deriving (Eq, Show, Generic)

newtype FreeVar = FreeVar Text
 deriving (Eq, Show, Generic, Hashable)

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

-- | Data type expects/keeps internal bindings in terms of de Bruijn levels.
-- The `F_Feature` allows to combine a lot of data types (with `FreeVar`iables, without them, with evaluated values or without them, etc.)
data F b f
  = F_LvlBind    !LvlBind
  | F_Lam     !(F_LamBody b f)
  | F_App     !(F_AppTarget b f) !(F_AppParam b f)
  | F_Feature !b
 deriving (Eq, Show, Generic, Functor, Traversable, Foldable)

-- | Lets `Semigroup` in terms of Lambda Calculus would be simply applying expressions.
instance Semigroup (F b a) where
  (<>) :: F b a -> F b a -> F b a
  (<>) fa fb = F_App (crc fa) (crc fb)

-- ***** Instances

instance Eq f => Eq1 (F f) where
  liftEq :: (a -> b -> Bool) -> F f a -> F f b -> Bool
  --  2025-05-20: FIXME: eq function `(a -> b -> Bool)` is ignored.
  -- If there was Applicative to `F` the implementation then is `fold $ liftA2 eq a b`
  liftEq _ = go  -- Making shure GHC detects that there is no point to go through typeclass dictionary searches, all other instances derive from here.
   where
    go (F_Lam           b1 ) (F_Lam           b2 ) =      crc go b1 b2
    go (F_App        f1 p1 ) (F_App        f2 p2 ) = (&&) (crc go f1 f2)
                                                         (crc go p1 p2)
    go (F_LvlBind idx1 ) (F_LvlBind idx2 ) = (==) idx1
                                           idx2
    go (F_Feature bind1 ) (F_Feature bind2 ) = (==) bind1
                                             bind2
    go _ _ = False

-- **** Finished term

newtype Bruijn b = Bruijn (Mu (F b))
 deriving (Eq, Generic)

-- ***** Instances for `Bruijn`
-- Are based on the default instances of the `Mu`
instance Recursive (->) (Bruijn b) (F b) where
  cata :: Algebra (->) (F b) a -> Bruijn b -> a
  cata φ (Bruijn (Mu f)) = f φ

instance Projectable (->) (Bruijn b) (F b) where
  project :: Bruijn b -> F b (Bruijn b)
  project = lambek

instance Steppable (->) (Bruijn b) (F b) where
  embed :: Algebra (->) (F b) (Bruijn b)
  embed m = Bruijn $ Mu $ \ f -> f $ fmap (cata f) m

-- *** Isomorphism of lambda term to human readable representation

-- | Abstraction for representation of human readable view of the closed lambda term datatype
newtype BruijnBJHumanReadable b = BruijnBJHumanReadable (Bruijn b)

-- **** Instances

instance Show b => Show (BruijnBJHumanReadable b) where
  show :: BruijnBJHumanReadable b -> String
  show = l_showHR . crc
   where
    -- | There is a newtype boundary between main lambda term data type and human readable, code prefers to preserve the general GHC derived @Show@ instances for the general case (showing term/expression internals) for the lambda term and its components, which is why this coersion enforsment is needed.
    l_showHR :: Bruijn b -> String
    l_showHR =
      caseBruijn
        (show . crc @Natural)
        showApp
        showLam
        show
     where
      showApp :: Bruijn b -> Bruijn b -> String
      showApp f a = "(" <> l_showHR f <> ") " <> l_showHR a
      showLam :: Bruijn b -> String
      showLam b = "\\ " <> l_showHR b

-- **** Functions

turnReadable :: Show b => Bruijn b -> Text
turnReadable = show . BruijnBJHumanReadable

-- *** Patterns

-- | Turn level of bind into expression (and back).
pattern Pat_LvlBind :: LvlBind -> Bruijn b
pattern Pat_LvlBind n <- (project -> F_LvlBind n) where
        Pat_LvlBind n =    embed ( F_LvlBind n)

-- | Take (or turn back):
-- 1 -> Target of application;
-- 2 -> Parameter to apply to;
-- \therefore: expression of applicaiton.
pattern Pat_App :: Bruijn b -> Bruijn b -> Bruijn b
pattern Pat_App f a <- (project -> F_App (F_AppTarget (embed -> f)) (F_AppParam (embed -> a))) where
        Pat_App f a =    embed ( F_App (F_AppTarget (project f)) (F_AppParam (project a)))

-- | Take expression and wrap it into a lambda (and back).
pattern Pat_Lam :: Bruijn b -> Bruijn b
pattern Pat_Lam b <- (project -> F_Lam (F_LamBody (embed -> b))) where
        Pat_Lam b =    embed ( F_Lam (F_LamBody (project b)))

-- | Take FreeVar and produce expression primitive (and back).
pattern Pat_Feature :: b -> Bruijn b
pattern Pat_Feature b <- (project -> F_Feature b) where
        Pat_Feature b =    embed ( F_Feature b)

{-# complete Pat_LvlBind, Pat_App, Pat_Lam, Pat_Feature #-}

-- *** Builders

-- | Encode level to bind to into expression.
mkLvlBind :: Natural -> Bruijn b
mkLvlBind = Pat_LvlBind . crc

mkApp :: Bruijn b -> Bruijn b -> Bruijn b
mkApp = Pat_App

mkLam :: Bruijn b -> Bruijn b
mkLam = Pat_Lam

mkFreeVar :: Text -> Bruijn FreeVar
mkFreeVar = Pat_Feature . crc

-- *** Helpers

-- | Takes a set of for lambda term cases, takes a lambda term, detects term and applies according function to it:
caseBruijn
  :: (LvlBind -> a)             -- ^ For index
  -> (Bruijn b -> Bruijn b -> a) -- ^ For application
  -> (Bruijn b -> a)            -- ^ For function
  -> (b -> a)                   -- ^ For free var
  -> Bruijn b                  -- ^ BruijnTerm
  -> a                         -- ^ Result
caseBruijn cf ca cl cv =
 \case
  Pat_LvlBind i -> cf i
  Pat_App   f a -> ca f a
  Pat_Lam     b -> cl b
  Pat_Feature b -> cv b

-- *** Parser

-- | Synthax rules follow general guidelines (from Wikipedia)
-- Outermost parentheses are dropped: `M N` instead of `(M N)`.
-- Applications ` ` are assumed to be left-associative: instead of ((M N) P) the M N P may be written.
-- The body of an abstraction extends as far right as possible: λ M N means λ (M N) and not (λ M) N.

--  2025-06-16: NOTE: Implement lexemes (possibly with lexer `Alex`), with parsing `(...)` from any direction, then for ` ` (application) from right, for lambda from the left.

--  2025-06-16: TODO: there is no `FreeVar` support in parser so far.
-- | The most strict outer parser, aka expects only sound expression
parser :: forall b . Parser (Bruijn b)
parser =
  app <|>
  lambda <|>
  bind
  -- <|>
  -- isEndOfLine
  -- <|>
  -- freeVar
 where
  app :: Parser (Bruijn b) =
    liftA2
      mkApp
      appFn
      appPar
   where
    appFn :: Parser (Bruijn b) =
      abs (lambda <|> app) <|> bind
    appPar :: Parser (Bruijn b) =
      char ' ' *> (abs app <|> app <|> lambda <|> bind)
    abs p = char '(' *> p <* char ')'
  -- freeVar :: Parser Bruijn =
  --   mkFreeVar <$> takeWhile1 isAlphaNum
  lambda :: Parser (Bruijn b) =
    mkLam <$> ((string "\\ " <|> string "λ ") *> parser)
  bind :: Parser (Bruijn b) =
    mkLvlBind <$> decimal

-- | Internalizes Bruijn parser, takes utility parser function of parser, and takes Text into it to parse.
parseWith :: (Parser (Bruijn b) -> Text -> a) -> Text -> a
parseWith f =
  f parser . (<> "\\n")

-- | Parse the expression recieved.
-- Wrapper around @parseOnly@, so expects full expression at once, hence strict.
parseFull :: Text -> Either Text (Bruijn b)
parseFull =
  mapLeft
    fromString
    . parseWith parseOnly

-- *** Testing

mk0 :: Bruijn b
mk0 = mkLvlBind 0

unitTests :: Seq (Bruijn b)
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

newtype OutsideValName = OutsideValName Text

newtype OutsideVal
  = OutsideVal (OutsideVal -> IO OutsideVal)

newtype BindedValue = BindedValue VarValue

newtype NotFoundFreeVar = NotFoundFreeVar FreeVar

newtype NotFoundFreeVarsOnEval = NotFoundFreeVarsOnEval (NonEmpty FreeVar)
 deriving (Semigroup)

neb :: forall f . (Functor f, Traversable f) => ContextBinds  -> f FreeVar -> Either      (f (Either NotFoundFreeVar BindedValue), NotFoundFreeVarsOnEval)      (f BindedValue)
neb ctx lt = returnSuccessOrReportState
 where
  returnSuccessOrReportState :: Either (f (Either NotFoundFreeVar BindedValue), NotFoundFreeVarsOnEval) (f BindedValue)
  returnSuccessOrReportState =
    either
      (Left . (eitherBindOrNotFound ctx lt,))
      pure
      eitherFullyValidOrBindsNotFound
   where
    -- | Right - Succesful binding of all free variables, Left - all unbound FreeVars
    eitherFullyValidOrBindsNotFound :: Either NotFoundFreeVarsOnEval (f BindedValue) = Validation.toEither $ sequenceA validatedBindFreeVars
     where
      -- | Produce a `NonEmpty` singleton on Failure to `mappend` them later.
      validatedBindFreeVars :: f (Validation NotFoundFreeVarsOnEval BindedValue) = bindAllWith Validation.validationNel ctx lt


eitherBindOrNotFound :: Functor f => ContextBinds -> f FreeVar ->  f (Either NotFoundFreeVar BindedValue)
eitherBindOrNotFound = bindAllWith id

bindAllWith :: (Coercible c b, Functor f) => (Either NotFoundFreeVar VarValue -> c) -> ContextBinds -> f FreeVar -> f b
bindAllWith f ctx =  (crc (f . metaBind lookupHM id ctx) <$>)

metaBind :: (Coercible t1 a1, Coercible a2 t2) => (t2 -> a3 -> Maybe b) -> (t1 -> a3) -> a2 -> t1 -> Either a1 b
metaBind f transform ctx a =
  maybe
    (Left $ crc a)
    pure
    $ f (crc ctx) $ transform a

newtype LvlBinds a = LvlBinds (IntMap (Bruijn a))

newtype NotFoundLvl = NotFoundLvl LvlBind

eval :: ContextBinds -> LvlBinds FreeVar -> Bruijn FreeVar -> Either (Either NotFoundLvl (Bruijn FreeVar)) (Either NotFoundFreeVar BindedValue)
eval ctx upLvls lt =
  caseBruijn
    (\ l -> undefined $ fmap (eval ctx upLvls) $ bind $ l)  -- bind Lambda term into place and at-once recurce into its evaluation.
    (undefined)
    (undefined)
    (pure . metaBind lookupHM id ctx)
    $ lt
 where

  bind :: LvlBind -> Either NotFoundLvl (Bruijn FreeVar)
  bind =
    metaBind lookupIM fromEnum upLvls

  -- bindLvl :: LvlBind -> _
  -- bindLvl lvl = Seq.lookup (fromEnum lvl) allLvls
  allLvls :: Recursive (->) (F FreeVar (Bruijn FreeVar)) f0 => Seq (Bruijn FreeVar)
  allLvls = cata (getLvl :: Algebra (->) f0 (Seq (Bruijn FreeVar))) $ project lt
   where
    getLvl :: w2
    getLvl = undefined
