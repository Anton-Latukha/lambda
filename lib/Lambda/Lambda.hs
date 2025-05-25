{-# language PartialTypeSignatures #-}
{-# language StrictData #-}

module Lambda.Lambda
  ( main
  ) where

-- ** Import

import Lambda.Prelude
import qualified Lambda.ClosedTerm as Closed
import Relude.Extra.Map
import qualified Data.Text as Text
import Data.Attoparsec.Text ( parseTest )
import qualified System.Console.Repline as R
import System.Process (callCommand)

-- ** Lambda calculi

-- *** Initial type primitive boundaries

-- **** New type typisation for closed Lambda term

-- | If Lambda term has no free variables, it is called Closed.





-- *** Testing

runOutputUnitTests :: IO ()
runOutputUnitTests =
  traverse_
    (putTextLn . Closed.turnReadable)
    Closed.lambdaTermUnitTests

-- | Parses only lawful Bruijin lambda terms.
runParserUnitTests :: IO ()
runParserUnitTests =
  traverse_
    (Closed.parseTermWith parseTest . Closed.turnReadable)
    Closed.lambdaTermUnitTests

checkRoundtripParseReadable :: Closed.Term -> RoundTripSuccess
checkRoundtripParseReadable = crc $
  either
    (const False)
    . (==)
    <*> Closed.turnReadableThenParseBack

parseThenApplyThenPrint :: (Closed.Term -> Closed.Term) -> Text -> Repl
parseThenApplyThenPrint f =
  output . fromEither . ((Closed.turnReadable . f) <$>) . Closed.parse'

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
    parseThenApplyThenPrint (crc . Closed.normalize)

  showExpr :: Text -> Repl
  showExpr =
    parseThenApplyThenPrint id

newtype RoundTripSuccess = RoundTripSuccess Bool
 deriving (Show)


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
    allTermUnitTestsRoundtrip = crc $ foldr ((&&) . crc checkRoundtripParseReadable) True Closed.lambdaTermUnitTests

-- ** Open Lambda calculus term
