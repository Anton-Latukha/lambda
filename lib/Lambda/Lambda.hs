{-# language PartialTypeSignatures #-}
{-# language StrictData #-}

module Lambda.Lambda
  ( main
  ) where

-- ** Import

import Lambda.Prelude
import Lambda.Term.Bruijn (Bruijn(..))
import qualified Lambda.Term.Bruijn as Bruijn
import Relude.Extra.Map
import qualified Data.Text as Text
import Data.Attoparsec.Text ( parseTest )
import qualified System.Console.Repline as R
import System.Process (callCommand)

-- *** Testing

runOutputUnitTests :: IO ()
runOutputUnitTests =
  traverse_
    (putTextLn . Bruijn.turnReadable)
    Bruijn.unitTests

-- | Parses only lawful Bruijin lambda terms.
runParserUnitTests :: IO ()
runParserUnitTests =
  traverse_
    (Bruijn.parseWith parseTest . Bruijn.turnReadable)
    Bruijn.unitTests

checkRoundtripParseReadable :: Bruijn -> RoundTripSuccess
checkRoundtripParseReadable = crc $
  either
    (const False)
    . (==)
    <*> Bruijn.turnReadableThenParseBack

parseApplyPrint :: (Bruijn -> Bruijn) -> Text -> Repl
parseApplyPrint f =
  output . fromEither . ((Bruijn.turnReadable . f) <$>) . Bruijn.parse'

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
        helpPreamble $ Text.concat $ (\ (crc->n, crc->d) -> n <> " - " <> d <> "\n") <$> allDocs
       where
        allDocs :: [(CommandName, CommandDocs)] =
          (\ (name,docs,_) -> (name , crc docs)) <$> commandList
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
        output . ("Help:\n" <>)

    showTerm :: Text -> Repl
    showTerm =
      parseApplyPrint id

    normalForm :: Text -> Repl
    normalForm =
      parseApplyPrint (crc . Bruijn.normalize)

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
    allTermUnitTestsRoundtrip = crc $ foldr ((&&) . crc checkRoundtripParseReadable) True Bruijn.unitTests

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
