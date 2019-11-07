module Cmdline

import Options.Applicative
import Util.Misc

%default total

public export
data InFSM = FSMFile String

public export
Show InFSM where
  show (FSMFile str) = str

public export
data InTD = TDFile String

public export
Show InTD where
  show (TDFile str) = str

inFSMP : Parser InFSM
inFSMP = FSMFile <$> strOption (long "fsm")

inTDP : Parser InTD
inTDP = TDFile <$> strOption (long "tdef")

firingsP : Parser (List Nat)
firingsP = option parseNatSeq (long "fire" . short 'f')
  where
  parseNatSeq : String -> Either ParseError (List Nat)
  parseNatSeq = traverse (maybeToEither (ErrorMsg "not a number") . parseNat) . split (== ',')

public export
record CoreOpts where
  constructor MkCoreOpts
  tdef    : InTD
  fsm     : InFSM
  firings : List Nat

public export
data CommandLineOpts = Help | Run CoreOpts | HelpFallback

Show CoreOpts where
  show (MkCoreOpts tdef fsm firings) = "fsm : " ++ show fsm ++ " tdef : " ++ show tdef ++ " firings : " ++ show firings

export
helpMessage : String
helpMessage = """
Usage:
  core --tdef TDEFSFILE --fsm GRAPHFILE (--fire | -f) FIRINGS

  --tdef     : path to the Typedefs definition file
  --fsm      : path to the FSM graph spec file
  --fire, -f : comma-separated list of edge labels (currently natural numbers) to fire
"""

export
fallbackMessage : String
fallbackMessage = "Wrong arguments, expected --help or --tdef TDEFSFILE --fsm GRAPHFILE (--fire | -f) FIRINGS"

parseCoreOpts : Parser CoreOpts
parseCoreOpts = [| MkCoreOpts inTDP inFSMP firingsP |]

export
parseCmdlineOpts : Parser CommandLineOpts
parseCmdlineOpts = (Run <$> parseCoreOpts)
               <|> flag' Help (long "help" . short 'h')
               <|> pure HelpFallback
