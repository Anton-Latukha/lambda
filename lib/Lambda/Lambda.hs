{-# language PatternSynonyms #-}
{-# language PartialTypeSignatures #-}

module Lambda.Lambda
  ( main
  ) where

-- ** Import

import Lambda.Prelude
import Relude.Extra.Enum (prev, next)
import qualified Text.Show
import qualified Data.Text as Text
import Data.Attoparsec.Text
    ( decimal, parseTest, char, parseOnly, string, Parser )
import Data.Functor.Classes ( Eq1(..) )
import Yaya.Fold ( Steppable(..), Projectable(..), Mu(..), lambek, Recursive(..), Algebra, Coalgebra )
import qualified System.Console.Repline as R
import System.Process (callCommand)

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
  show :: LambdaTerm -> String
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
        searchIndexAndSubstituteOnMatch
        recurseIntoBothBranches
        recurseIntoFunction
     where
      searchIndexAndSubstituteOnMatch =
        bool
          v  -- so substitution under index
          . PatLambdaTermBruijnIndex -- do `id` ("pass")
          <*> -- patthrough into both branches
            indexNotFound
       where
        indexNotFound = (crc bji /=)
      recurseIntoBothBranches =
        on PatLambdaTermApp (substituteWithPermutatedIndex id)
      -- | Outside Btuijn indexes increase +1 when enterning a scope of deeper function.
      --  2025-05-05: NOTE: This is considered costly compared to nameless encoding style. Since it increments/decrements all instances.
      recurseIntoFunction = substituteWithPermutatedIndex next
      substituteWithPermutatedIndex f = substitute v (f bji)


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

-- | Parse the expression recieved.
-- Wrapper around @parseOnly@, so expects full expression at once, hence strict.
parse' :: Text -> Either Text LambdaTerm
parse' t =
  either
    (Left . fromString)
    pure
    . parseOnly parserLambdaTerm $! (<> "\\n") t

turnReadableThenParseBack :: LambdaTerm -> Either Text LambdaTerm
turnReadableThenParseBack = parse' . turnReadable

-- *** REPL

type Repl = R.HaskelineT IO

banner :: R.MultiLine -> Repl String
banner =
  pure . bool
    mempty -- Multiline mode entry
    "λ> "  -- Standart single line entry
    . (R.MultiLine /=)

-- Evaluation : handle each line user inputs
evalPrint :: Text -> Repl ()
evalPrint = print

command :: (Text -> Repl ()) -> (String -> Repl ())
command c = c . fromString

prefix :: Maybe Char
prefix = pure ':'

multilineCommand :: Maybe String
multilineCommand = pure "paste"

-- | Tab Completion: return a completion for partial words entered
completer :: R.CompleterStyle IO
completer = R.Word cmp
 where
  cmp :: String -> IO [String]
  cmp =
    pure .
      extend to . from
   where
    from = isPrefixOf
    extend = flip filter
    to = ["kirk", "spock", "mccoy"]

newtype CommandName = CommandName Text
 deriving (Eq, Ord, IsString, ToString)

newtype CommandDocs = CommandDox Text
 deriving (Eq, Ord, IsString, Semigroup)

type CommandComm = (Text -> Repl ())

data Command = Command
  { -- | Command name
    name :: CommandName,
    -- | Command docs
    docs :: CommandDocs,
    -- | Command function
    comm :: CommandComm
  }

-- | Set of all options (+ multiline mode command), available inside REPL.
optionSet :: Map CommandName Command
optionSet = fromList
  [
    makeEntry "help" "documentation on REPL commands" help,
    makeEntry "say" "" say,
    makeEntry "norm" "Produce normal form" norm,
    makeEntry "print" "Echo what was put in" print,
    makeEntry "showExpr" "Parse and print back lambda expression" showExpr
  ]
 where
  makeEntry :: Text -> Text -> CommandComm -> (CommandName, Command)
  makeEntry n d f =
    (crc n, cmd)
   where
    cmd =
      Command {
        name = crc n,
        docs = crc $ makeDoc n d,
        comm = f
      }

  -- | Doc builder
  makeDoc :: Text -> Text -> Text
  makeDoc c d = Text.toUpper c <> "\n\nNAME\n\t" <> c <> " - " <> d <> "\n\nSYNOPSIS\n\t" <> c <> "[command]\n\nDESCRIPTION\n\t" <> c <> ""

  help :: CommandComm
  help = putTextLn . ("Help: " <>)

  say :: CommandComm
  say arg =
    liftIO (callCommand . toString $ "cowsay " <> arg)

  norm :: CommandComm
  norm =
    putTextLn . fromEither . ((turnReadable . crc . normalize) <$>) . parse'

  print :: CommandComm
  print = putTextLn

  showExpr :: CommandComm
  showExpr =
    putTextLn . fromEither . (turnReadable <$>) . parse'

-- | What to do/print on entering REPL.
initialiser :: Repl ()
initialiser =
  putStrLn "Simple Lamba calculus REPL. Enter \":help\" for information."

-- | What to do/print on Ctrl+D (aka user making exit)
finalizer :: Repl R.ExitDecision
finalizer =
  putStrLn mempty $> R.Exit

-- | Running the REPL
main :: IO ()
main =
  do
    runOutputUnitTests

    R.evalRepl
      banner
      (command evalPrint)
      options
      prefix
      multilineCommand
      completer
      initialiser
      finalizer
   where
    options :: R.Options Repl
    options =
      formOptionREPLMap <$> toList optionSet
     where
      formOptionREPLMap :: Command -> (String, String -> Repl ())
      formOptionREPLMap c =
        (toString $ name c, comm c . toText)
