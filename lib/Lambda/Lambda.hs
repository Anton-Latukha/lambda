{-# language PartialTypeSignatures #-}
{-# language StrictData #-}

module Lambda.Lambda
  ( main
  ) where

-- ** Import

import Lambda.Prelude
import Lambda.ClosedTerm (Closed(..))
import qualified Lambda.ClosedTerm as Closed
import Relude.Extra.Map
import qualified Data.Text as Text
import Data.Attoparsec.Text ( parseTest )
import qualified System.Console.Repline as R
import System.Process (callCommand)

-- *** Testing

runOutputUnitTests :: IO ()
runOutputUnitTests =
  traverse_
    (putTextLn . Closed.turnReadable)
    Closed.unitTests

-- | Parses only lawful Bruijin lambda terms.
runParserUnitTests :: IO ()
runParserUnitTests =
  traverse_
    (Closed.parseWith parseTest . Closed.turnReadable)
    Closed.unitTests

checkRoundtripParseReadable :: Closed -> RoundTripSuccess
checkRoundtripParseReadable = crc $
  either
    (const False)
    . (==)
    <*> Closed.turnReadableThenParseBack

parseApplyPrint :: (Closed -> Closed) -> Text -> Repl
parseApplyPrint f =
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
    fromList $ makeEntry <$> commandList
   where
    commandList :: [(CommandName, Text, Text -> Repl)] =
      [
        ("help"     ,"documentation on REPL commands"        ,help      ),
        ("print"    ,"Echo what was put in"                  ,output    ),
        ("showExpr" ,"Parse and print back lambda expression",showTerm  ),
        ("norm"     ,"Produce normal form"                   ,normalForm),
        ("cowsay"   ,""                                      ,cowsay    )
      ]
    makeEntry :: (CommandName, Text, Text -> Repl) -> (CommandName, Command)
    makeEntry (n, d, f) = (n, cmd)
      where
      cmd =
        Command {
          name = n,
          docs = mkCommandDoc,
          comm = f
        }
       where
        -- | Doc builder
        mkCommandDoc:: CommandDocs
        mkCommandDoc= crc $ "\n\n>:" <> name <> "\n\nNAME\n\t" <> name <> " - " <> d <> "\n\nSYNOPSIS\n\t" <> name <> " [command]\n\nDESCRIPTION\n\t" <> name <> ""
         where
          name = crc n

    help :: Text -> Repl
    help =
      whenText
        helpNoArgument
        helpForCommand
     where
      helpNoArgument :: Repl =
        helpPreamble $ Text.concat $ crc allDocs
       where
        allDocs :: [CommandDocs] =
          (\ (_,docs,_) -> crc docs) <$> commandList
      helpForCommand :: Text -> Repl
      helpForCommand =
        helpPreamble . helpParticularCommand
       where
        helpParticularCommand :: Text -> Text
        helpParticularCommand a =
          maybe
            ("The '" <> a <> "' not found and not supported, check the simple `:help` for all supported commands.")
            (crc . docs)
            $ lookup (crc a) fullMap
      helpPreamble =
        output . ("Help: " <>)

    showTerm :: Text -> Repl
    showTerm =
      parseApplyPrint id

    normalForm :: Text -> Repl
    normalForm =
      parseApplyPrint (crc . Closed.normalize)

    cowsay :: Text -> Repl
    cowsay =
      liftIO . callCommand . toString . ("cowsay " <>)

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
    putTextLn "\n"

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
    allTermUnitTestsRoundtrip :: RoundTripSuccess
    allTermUnitTestsRoundtrip = crc $ foldr ((&&) . crc checkRoundtripParseReadable) True Closed.unitTests

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
      formOptionREPLMap <$> toList optionSet
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

-- ** Open Lambda calculus term
