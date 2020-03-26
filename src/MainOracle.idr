
module Main

-- idris-ct
import Basic.Category
import Graph.Graph
import Graph.Path
import Basic.Functor
import Discrete.DiscreteCategory

-- typedefs
import Typedefs.Typedefs
import Typedefs.TermParse
import Typedefs.TermWrite

-- tparsec
import Relation.Indexed
import Data.NEList

import Parser.TGraph
import GraphCat

-- base
import Data.Vect
import Language.JSON
import Language.JSON.Data

%access public export
%default total

partial
main : IO ()
main = do

          -- [_,filename] <- getArgs
          --  | _ => putStrLn "Wrong cmdline args"
          -- Right content <- readFile filename
          --  | Left err => putStrLn ("Filesystem error: " ++ show err)
          -- let Just fsm = Typedefs.TermParse.deserialize [] [] FSMExec content
          --  | Nothing => putStrLn "invalid FSM termdef"
          printLn (TermWrite.serializeJSON [Nat] [JNumber . cast] FSMExec valid2)
          let Right (cat ** a ** b ** m) = validateExec invalid2
            | Left err => putStrLn "fail" -- printLn (TermWrite.serializeJSON [] [] TFSMErr (toTDefErr err))
          let v = lastStep cat a b m
          putStrLn "FSM is valid"
