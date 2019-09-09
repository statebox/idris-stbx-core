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
data InFFI = FFIFile String

public export
Show InFFI where
  show (FFIFile str) = str

inFSMP : Parser InFSM
inFSMP = FSMFile <$> strOption (long "fsm")

inFFIP : Parser InFFI
inFFIP = FFIFile <$> strOption (long "ffi")

firingsP : Parser (List Nat)
firingsP = option parseNatSeq (long "fire" . short 'f')
  where
  parseNatSeq : String -> Either ParseError (List Nat)
  parseNatSeq = traverse (maybeToEither (ErrorMsg "not a number") . parseNat) . split (== ',')

public export
record CoreOpts where
  constructor MkCoreOpts
  fsm : InFSM
  ffi : InFFI
  firings : List Nat

public export
data CommandLineOpts = Help | Run CoreOpts | HelpFallback

Show CoreOpts where
  show (MkCoreOpts fsm ffi firings) = "fsm : " ++ show fsm ++ " ffi : " ++ show ffi ++ " firings : " ++ show firings

export
helpMessage : String
helpMessage = """
Usage:
  core --fsm GRAPHFILE --ffi FFIMAP (--fire | -f) FIRINGS

  --fsm      : path to the FSM graph spec file
  --ffi      : path to the FFI mapping file
  --fire, -f : comma-separated list of edge labels (currently natural numbers) to fire
"""

export
fallbackMessage : String
fallbackMessage = "Wrong arguments, expected --help or --fsm GRAPHFILE --ffi FFIMAP (--fire | -f) FIRINGS"

parseCoreOpts : Parser CoreOpts
parseCoreOpts = [| MkCoreOpts inFSMP inFFIP firingsP |]

export
parseCmdlineOpts : Parser CommandLineOpts
parseCmdlineOpts = (Run <$> parseCoreOpts)
               <|> flag' Help (long "help" . short 'h')
               <|> pure HelpFallback
