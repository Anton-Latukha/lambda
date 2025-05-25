{-# language PatternSynonyms #-}
{-# language PartialTypeSignatures #-}
{-# language StrictData #-}

module Lambda.Lambda
  ( main
  ) where

-- ** Import

import Lambda.Prelude
import Relude.Extra.Enum (next)
import Relude.Extra.Map
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

-- **** New type typisation for closed Lambda term

-- | If Lambda term has no free variables, it is called Closed.

-- | Bruijn index in lambda term.
-- Index < number of external lambda binds => index == binded lambda value
-- Index >= number of external lambda binds => index == free variable
newtype BruijnIndex = BruijnIndex Int
 deriving (Eq, Enum, Num, Bounded, Show, Generic)

newtype ClosedLambdaTermFAppFunc a = ClosedLambdaTermFAppFunc (ClosedLambdaTermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype ClosedLambdaTermFAppParam a = ClosedLambdaTermFAppParam (ClosedLambdaTermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

newtype ClosedLambdaTermFLamBody a = ClosedLambdaTermFLamBody (ClosedLambdaTermF a)
 deriving (Eq, Eq1, Show, Generic, Functor, Traversable, Foldable)

-- **** Functorial Lambda term/expression

data ClosedLambdaTermF a
  = ClosedLambdaTermFBruijnIndex !BruijnIndex
  | ClosedLambdaTermFApp    !(ClosedLambdaTermFAppFunc a) !(ClosedLambdaTermFAppParam a)
  | ClosedLambdaTermFLam    !(ClosedLambdaTermFLamBody a)
 deriving (Eq, Show, Generic, Functor, Traversable, Foldable)

-- ***** Instances

instance Recursive (->) ClosedLambdaTerm ClosedLambdaTermF where
  cata :: Algebra (->) ClosedLambdaTermF a -> ClosedLambdaTerm -> a
  cata φ (ClosedLambdaTerm (Mu f)) = f φ

instance Projectable (->) ClosedLambdaTerm ClosedLambdaTermF where
  project :: Coalgebra (->) ClosedLambdaTermF ClosedLambdaTerm
  project = lambek

instance Steppable (->) ClosedLambdaTerm ClosedLambdaTermF where
  embed :: Algebra (->) ClosedLambdaTermF ClosedLambdaTerm
  embed m = ClosedLambdaTerm $ Mu $ \ f -> f $ fmap (cata f) m

instance Eq1 ClosedLambdaTermF where
  liftEq :: (a -> b -> Bool) -> ClosedLambdaTermF a -> ClosedLambdaTermF b -> Bool
  --  2025-05-20: FIXME: eq function `(a -> b -> Bool)` is ignored.
  -- If there was Applicative to `ClosedLambdaTermF` the implementation then is `fold $ liftA2 eq a b`
  liftEq _ = go  -- Making shure GHC detects that there is no point to go through typeclass dictionary searches, all other instances derive from here.
   where
    go (ClosedLambdaTermFLam           b1 ) (ClosedLambdaTermFLam           b2 ) =      crc go b1 b2
    go (ClosedLambdaTermFApp        f1 p1 ) (ClosedLambdaTermFApp        f2 p2 ) = (&&) (crc go f1 f2)
                                                                                       (crc go p1 p2)
    go (ClosedLambdaTermFBruijnIndex idx1 ) (ClosedLambdaTermFBruijnIndex idx2 ) = (==) idx1
                                                                                       idx2
    go _ _ = False

-- **** Finished ClosedLambdaTerm

newtype ClosedLambdaTerm = ClosedLambdaTerm (Mu ClosedLambdaTermF)
 deriving (Eq, Generic)

-- *** Isomorphism of lambda term to human readable representation

-- | Abstraction for representation of human readable view of the main lambda term datatype
newtype ClosedLambdaTermBJHumanReadable = ClosedLambdaTermBJHumanReadable ClosedLambdaTerm

-- **** Instances

instance Show ClosedLambdaTermBJHumanReadable where
  show :: ClosedLambdaTermBJHumanReadable -> String
  show = l_showHR . crc
   where
    -- | There is a newtype boundary between main lambda term data type and human readable, code prefers to preserve the general GHC derived @Show@ instances for the general case (showing term/expression internals) for the lambda term and its components, which is why this coersion enforsment is needed.
    l_showHR :: ClosedLambdaTerm -> String
    l_showHR =
      caseClosedLambdaTerm
        show
        showApp
        showLam
     where
      showApp :: ClosedLambdaTerm -> ClosedLambdaTerm -> String
      showApp f a = "(" <> l_showHR f <> ") " <> l_showHR a
      showLam :: ClosedLambdaTerm -> String
      showLam b = "\\ " <> l_showHR b

instance Show ClosedLambdaTerm where
  show :: ClosedLambdaTerm -> String
  show (crc @ClosedLambdaTermBJHumanReadable -> a) = show a

-- **** Functions

turnReadable :: ClosedLambdaTerm -> Text
turnReadable = show . ClosedLambdaTermBJHumanReadable

-- *** Patterns

pattern PatClosedLambdaTermBruijnIndex :: Int -> ClosedLambdaTerm
pattern PatClosedLambdaTermBruijnIndex n <- (project -> ClosedLambdaTermFBruijnIndex (BruijnIndex n)) where
        PatClosedLambdaTermBruijnIndex n =     embed (  ClosedLambdaTermFBruijnIndex (BruijnIndex n))

pattern PatClosedLambdaTermApp :: ClosedLambdaTerm -> ClosedLambdaTerm -> ClosedLambdaTerm
pattern PatClosedLambdaTermApp f a <- (project -> ClosedLambdaTermFApp (ClosedLambdaTermFAppFunc (embed -> f)) (ClosedLambdaTermFAppParam (embed -> a))) where
        PatClosedLambdaTermApp f a =     embed (  ClosedLambdaTermFApp (ClosedLambdaTermFAppFunc (project  f)) (ClosedLambdaTermFAppParam (project  a)))

pattern PatClosedLambdaTermLam :: ClosedLambdaTerm -> ClosedLambdaTerm
pattern PatClosedLambdaTermLam b <- (project -> ClosedLambdaTermFLam (ClosedLambdaTermFLamBody (embed -> b))) where
        PatClosedLambdaTermLam b =     embed (  ClosedLambdaTermFLam (ClosedLambdaTermFLamBody (project  b)))

{-# complete PatClosedLambdaTermBruijnIndex, PatClosedLambdaTermApp, PatClosedLambdaTermLam #-}

-- *** Builders

mkClosedLambdaTermBruijnIndex :: Int -> ClosedLambdaTerm
mkClosedLambdaTermBruijnIndex = PatClosedLambdaTermBruijnIndex

mkClosedLambdaTermApp :: ClosedLambdaTerm -> ClosedLambdaTerm -> ClosedLambdaTerm
mkClosedLambdaTermApp = PatClosedLambdaTermApp

mkClosedLambdaTermLam :: ClosedLambdaTerm -> ClosedLambdaTerm
mkClosedLambdaTermLam = PatClosedLambdaTermLam

-- *** Helpers

-- | Takes a set of for lambda term cases, takes a lambda term, detects term and applies according function to it:
caseClosedLambdaTerm
  :: (Int -> a)     -- ^ For index
  -> (ClosedLambdaTerm -> ClosedLambdaTerm -> a) -- ^ For application
  -> (ClosedLambdaTerm -> a)      -- ^ For function
  -> ClosedLambdaTerm            -- ^ Term
  -> a             -- ^ Result
caseClosedLambdaTerm cf ca cl =
 \case
  PatClosedLambdaTermBruijnIndex i -> cf   i
  PatClosedLambdaTermApp       f a -> ca f a
  PatClosedLambdaTermLam         b -> cl   b

-- *** Parser

parserClosedLambdaTerm :: Parser ClosedLambdaTerm
parserClosedLambdaTerm =
  bruijnIndexParser <|>
  lambdaParser <|>
  appParser
 where
  bruijnIndexParser :: Parser ClosedLambdaTerm =
    mkClosedLambdaTermBruijnIndex <$> decimal
  lambdaParser :: Parser ClosedLambdaTerm =
    mkClosedLambdaTermLam <$> (string "\\ " *> bruijnIndexParser)
  appParser :: Parser ClosedLambdaTerm =
    liftA2
      mkClosedLambdaTermApp
      appFuncParser
      appParamParser
   where
    appFuncParser :: Parser ClosedLambdaTerm =
      between '(' ')' parserClosedLambdaTerm
    appParamParser :: Parser ClosedLambdaTerm =
      char ' ' *> parserClosedLambdaTerm
    between bra ket p = char bra *> p <* char ket

-- *** Normal form

-- | Normal form lambda term.
newtype NClosedLambdaTerm = NClosedLambdaTerm ClosedLambdaTerm

normalize :: ClosedLambdaTerm -> NClosedLambdaTerm
normalize = crc .
  caseClosedLambdaTerm
    PatClosedLambdaTermBruijnIndex
    forLambdaApplication
    forLambdaFunction
 where
  forLambdaApplication =
    flip betaReduce

  forLambdaFunction =
    PatClosedLambdaTermLam . crc . normalize

  -- | Lambda function application.
  -- Does beta-reduce when lambda term matches definition, otherwise does id.
  -- TODO: Try for this function to return Maybe.
  betaReduce
    :: ClosedLambdaTerm -- ^ Argument to bind
    -> ClosedLambdaTerm -- ^ Base expression to bind in
    -> ClosedLambdaTerm -- ^ Expression with the bind applied
  betaReduce a =
    \case
      (PatClosedLambdaTermLam lb) -> substitute a 0 lb -- Apply value to this level binding
      other -> PatClosedLambdaTermApp other a
   where
    substitute :: ClosedLambdaTerm -> BruijnIndex -> ClosedLambdaTerm -> ClosedLambdaTerm
    substitute v bji =
      caseClosedLambdaTerm
        searchIndexAndSubstituteOnMatch
        recurseIntoBothBranches
        recurseIntoFunction
     where
      searchIndexAndSubstituteOnMatch =
        bool
          v  -- so substitution under index
          . PatClosedLambdaTermBruijnIndex -- do `id` ("pass")
          <*> -- patthrough into both branches
            indexNotFound
       where
        indexNotFound = (crc bji /=)
      recurseIntoBothBranches =
        on PatClosedLambdaTermApp (substituteWithPermutatedIndex id)
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
  traverse_
    (parseClosedLambdaTermWith parseTest . turnReadable)
    lambdaTermUnitTests

mk0 :: ClosedLambdaTerm
mk0 = mkClosedLambdaTermBruijnIndex 0

lambdaTermUnitTests :: Seq ClosedLambdaTerm
lambdaTermUnitTests =
  cons
    mk0
    $ (`mkClosedLambdaTermApp` mk0) . ($ mk0) <$>
      [ id
      , PatClosedLambdaTermLam
      , PatClosedLambdaTermLam
      ]

-- | Parse the expression recieved.
-- Wrapper around @parseOnly@, so expects full expression at once, hence strict.
parse' :: Text -> Either Text ClosedLambdaTerm
parse' =
  mapLeft
    fromString
    . parseClosedLambdaTermWith parseOnly

-- | Internalizes ClosedLambdaTerm parser, takes utility parser function of parser, and takes Text into it to parse.
parseClosedLambdaTermWith :: (Parser ClosedLambdaTerm -> Text -> b) -> Text -> b
parseClosedLambdaTermWith f =
  f parserClosedLambdaTerm . (<> "\\n")

turnReadableThenParseBack :: ClosedLambdaTerm -> Either Text ClosedLambdaTerm
turnReadableThenParseBack = parse' . turnReadable

newtype RoundTripSuccess = RoundTripSuccess Bool
 deriving (Show)

checkRoundtripParseReadable :: ClosedLambdaTerm -> RoundTripSuccess
checkRoundtripParseReadable = crc $
  either
    (const False)
    . (==)
    <*> turnReadableThenParseBack

-- ** REPL

newtype ReplF a = ReplF (R.HaskelineT IO a)
 deriving (Functor, Applicative, Monad, MonadIO)

type Repl = ReplF ()

newtype CommandName = CommandName Text
 deriving (Eq, Ord, IsString, ToString)

newtype CommandDocs = CommandDox Text
 deriving (Eq, Ord, IsString, Semigroup)

data Command = Command
  { -- | Command name
    name :: CommandName,
    -- | Command docs
    docs :: CommandDocs,
    -- | Command function
    comm :: Text -> Repl
  }

output :: Text -> ReplF ()
output = putTextLn

-- | Set of all options (+ multiline mode command), available inside REPL.
optionSet :: Map CommandName Command
optionSet = fullMap
 where
  -- | It is internalized to have optimized internal recursive search to produce `:help` output
  fullMap :: Map CommandName Command =
    fromList commandList

  commandList :: [(CommandName, Command)] =
    [
      makeEntry "help"     "documentation on REPL commands"         help,
      makeEntry "print"    "Echo what was put in"                   output,
      makeEntry "showExpr" "Parse and print back lambda expression" showExpr,
      makeEntry "norm"     "Produce normal form"                    norm,
      makeEntry "cowsay"   ""                                       cowsay
    ]
  makeEntry :: CommandName -> Text -> (Text -> Repl) -> (CommandName, Command)
  makeEntry n d f = (n, cmd)
   where
    cmd =
      Command {
        name = n,
        docs = commandDocBuilder n d,
        comm = f
      }

  -- | Doc builder
  commandDocBuilder :: CommandName -> Text -> CommandDocs
  commandDocBuilder (crc -> c) d = crc $ "\n\n>:" <> c <> "\n\nNAME\n\t" <> c <> " - " <> d <> "\n\nSYNOPSIS\n\t" <> c <> " [command]\n\nDESCRIPTION\n\t" <> c <> ""

  help :: Text -> Repl
  help =
    whenText
      outputWhenNoArgument
      outputWhenParticularCommand
   where
    outputWhenNoArgument :: Repl =
      helpPreamble $ Text.concat $ crc allDocs
     where
      allDocs :: [CommandDocs] =
        docs . snd <$> commandList
    outputWhenParticularCommand :: Text -> Repl
    outputWhenParticularCommand =
      helpPreamble . outputParticularCommand
     where
      outputParticularCommand :: Text -> Text
      outputParticularCommand a =
        maybe
          ("The '" <> a <> "' not found and not supported, check the simple `:help` for all supported commands.")
          (crc . docs)
          $ lookup (crc a) fullMap
    helpPreamble =
      output . ("Help: " <>)

  cowsay :: Text -> Repl
  cowsay =
    liftIO . callCommand . toString . ("cowsay " <>)

  norm :: Text -> Repl
  norm =
    parseThenApplyThenPrint (crc . normalize)

  showExpr :: Text -> Repl
  showExpr =
    parseThenApplyThenPrint id

  parseThenApplyThenPrint :: (ClosedLambdaTerm -> ClosedLambdaTerm) -> Text -> Repl
  parseThenApplyThenPrint f =
    output . fromEither . ((turnReadable . f) <$>) . parse'

-- | Running the REPL
main :: IO ()
main =
  do
    putTextLn "\nRunning Output Unit Tests ..."
    runOutputUnitTests

    putTextLn "\nRunning Parser Unit Tests ..."
    runParserUnitTests

    putTextLn "\nRunning Roundtrip Unit Tests ..."
    putTextLn $ show allTermUnitTestsRoundtrip

    R.evalRepl
      (crc . banner)
      (crc . evalPrint . fromString)
      (crc options)
      prefix
      multilineCommand
      completer
      (crc initialiser)
      (crc finalizer)
   where
    banner :: R.MultiLine -> ReplF String
    banner =
      pure . bool
        mempty -- Multiline mode entry
        "λ> "  -- Standart single line entry
        . (R.MultiLine /=)

    -- Evaluation : handle each line user inputs
    evalPrint :: Text -> Repl
    evalPrint = output

    options :: R.Options ReplF =
      crc formOptionREPLMap <$> toList optionSet
     where
      formOptionREPLMap :: Command -> (String, String -> Repl)
      formOptionREPLMap c =
        (toString $ name c, comm c . toText)

    prefix :: Maybe Char =
      pure ':'

    multilineCommand :: Maybe String =
      pure "paste"

    -- | Tab Completion: return a completion for partial words entered
    completer :: R.CompleterStyle IO=
      R.Word cmp
     where
      cmp :: String -> IO [String]
      cmp =
        pure .
          extend to . from
       where
        extend = flip filter
        to     = ["kirk", "spock", "mccoy"]
        from   = isPrefixOf

    -- | What to do/print on entering REPL.
    initialiser :: Repl =
      output "Simple Lamba calculus REPL. Enter \":help\" for information."

    -- | What to do/print on Ctrl+D (aka user making exit)
    finalizer :: ReplF R.ExitDecision =
      output mempty $> R.Exit

    allTermUnitTestsRoundtrip :: RoundTripSuccess
    allTermUnitTestsRoundtrip = crc $ foldr ((&&) . crc checkRoundtripParseReadable) True lambdaTermUnitTests

-- ** Open Lambda calculus term
