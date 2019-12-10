module ErrDef

-- optparse
import Options.Applicative

-- typedefs
import Typedefs.Parse

%access public export
%default total

||| We aggregate errors from different libraries at the toplevel
data ProcError = FErr FileError | PErr ParseError | TPErr Parse.Error | TDefErr

Show ProcError where
  show (FErr ferr)           = "Filesystem error: " ++ show ferr
  show (PErr (ErrorMsg err)) = "Parse error: " ++ err
  show (TPErr err)           = "Tparsec error: " ++ show err
  show  TDefErr              = "Typedefs error: not closed."
