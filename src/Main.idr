module Main

-- base
import Control.Isomorphism
import Data.Vect

-- contrib
import Data.SortedMap

-- idris-ct
import Basic.Category
import Basic.Functor
import Graph.Graph
import Graph.Path
import Idris.TypesAsCategoryExtensional

-- optparse
import Options.Applicative

-- typedefs
import Typedefs.Parse
import Typedefs.Typedefs
import Typedefs.TypedefsDecEq -- TODO: remove

-- tparsec
import Data.NEList
import TParsec
import TParsec.Running

import Computer.Computer
import Computer.Example2A
import Computer.Example2Helper -- TODO: remove
import Cmdline
import GraphFunctor.ClosedTypedefsAsCategory -- TODO: remove
import GraphFunctor.GraphEmbedding
import Util.Misc
import Util.Max

%access public export
%default total

-- %include c "fficat.h"

[showFin] Show (Fin n) where
  show = show . finToNat

data ProcError = FErr FileError | PErr ParseError | TPErr Parse.Error | TDefErr

Show ProcError where
  show (FErr ferr) = "Filesystem error: " ++ show ferr
  show (PErr (ErrorMsg err)) = "Parse error: " ++ err
  show (TPErr err) = "Tparsec error: " ++ show err
  show (TDefErr) = "Typedefs error: not closed."

processArgs : List String -> Either ParseError CommandLineOpts
processArgs (_ :: opts) = runParserFully parseCmdlineOpts opts
processArgs  _          = Left (ErrorMsg "Not enough arguments")

readInput : String -> (String -> Result Error a) -> IO (Either ProcError a)
readInput fn parse = do Right str <- readFile fn
                         | Left err => pure (Left $ FErr err)
                        pure $ result (Left . TPErr) (Left . TPErr) Right $ parse str

checkClosedTNamed : (n ** TNamed n) -> Either ProcError (TNamed 0)
checkClosedTNamed (Z ** def) = pure def
checkClosedTNamed _ = Left TDefErr

checkClosed : NEList (n ** TNamed n) -> Either ProcError (NEList (TNamed 0))
checkClosed = traverse checkClosedTNamed

readTypedefs : InTD -> IO (Either ProcError (NEList (TNamed 0)))
readTypedefs (TDFile f) = do
  Right ls <- readInput f parseTNameds
    | Left err => pure (Left err)
  pure $ checkClosed ls

ParserF : Type -> Nat -> Type
ParserF = Parser (TParsecT Error Void Identity) chars

fsmParser : All (ParserF (NEList (Nat, String), NEList (Nat, Nat, String)))
fsmParser = states `and` (withSpaces (string "---") `rand` transitions)
  where
  states : All (ParserF (NEList (Nat, String)))
  states = nelist $ decimalNat `and` withSpaces alphas
  transitions : All (ParserF (NEList (Nat, Nat, String)))
  transitions = nelist $ decimalNat `and` (withSpaces decimalNat `and` withSpaces alphas)

readFSM : InFSM -> IO (Either ProcError (NEList (Nat, String), NEList (Nat, Nat, String)))
readFSM (FSMFile f) = readInput f (\s => getResult $ parseResult s fsmParser)

buildPath : (graph : Graph (Fin lenV))
         -> (prf : numEdges graph = lenE)
         -> List (Fin lenE)
         -> Maybe (s ** t ** Path graph s t)
buildPath graph prf labels = firingPath graph (rewrite prf in labels)

-- buildFunctorToTDef : {g : Graph vertices} -> (vertices -> TDef 0) -> CFunctor (FreeCategory g) (CompletePreorder (TDef 0))
-- buildFunctorToTDef {g} f = (completePreorderMorphism f) `functorComposition` collapser (FreeCategory g)



-- createFunctionFromVerticesToTdefs : Vect len (Nat, String) -> List (TNamed 0) -> ((Nat, String) -> TDef 0)
-- createFunctionFromVerticesToTdefs vertices tdefs = lookforalllabel
--        yes -> Just
--        no -> Nothing

computeWithOptions : {vs : NEList (Nat, String)}
                  -> (graph : Graph (Fin $ length vs))
                  -> (verticesTypedefs : Vect (length vs) (TDef 0))
                  -> Vect (numEdges graph) (mor' $ Computer.cClosedTypedefsKleiliCategory FFI_C)
                  -> Path graph initialVertex finalVertex
                  -> (Maybe (IO (Ty [] (Vect.index finalVertex verticesTypedefs))) -> IO ())
                  -> IO ()
computeWithOptions {vs} {initialVertex} graph verticesTypedefs edgesMorphisms path cont with (Vect.index initialVertex verticesTypedefs) proof prf
  computeWithOptions {vs} {initialVertex} graph verticesTypedefs edgesMorphisms path cont | T1 =
    (cont $ (Computer.compute {ffi=FFI_C}
                              @{showFin}
                              graph
                              (isoRefl {a=Fin (length vs)})
                              verticesTypedefs
                              edgesMorphisms
                              path
                              (rewrite sym prf in ())))
  computeWithOptions {vs} {initialVertex} graph verticesTypedefs edgesMorphisms path cont | _ = putStrLn "path not starting at Unit"

runWithOptions : CoreOpts -> IO ()
runWithOptions (MkCoreOpts tdf fsmf firings) = do
  disableBuffering  -- don't remove this!
  Right tdef <- readTypedefs tdf
    | Left err => putStrLn ("Typedefs read error: " ++ show err)
  Right (vs, es) <- readFSM fsmf
    | Left err => putStrLn ("FSM read error:" ++ show err)
  case (parseEdges (toVect vs) (toVect es), lookupEdges (toVect es) firings) of
    (Just edges, Just pathEdges) =>
      let (graph ** prf) = mkGraph ((\edge => (fst edge, fst $ snd edge)) <$> edges)
      in case buildPath graph prf pathEdges of
        Just (initialVertex ** finalVertex ** path) => do
          case (verticesAsTypedefs (NEList.toList tdef) (toVect vs), edgesAsMorphisms edges) of
            (Just verticesTypedefs, Just edgesMorphisms) =>
              computeWithOptions {vs}
                                  graph
                                  (snd <$> verticesTypedefs)
                                  (rewrite prf in edgesMorphisms)
                                  path
                                  (\mComputation => case mComputation of
                                                     Just computation => ignore computation
                                                     Nothing          => putStrLn "error while performing the computation")
            (Just _               , Nothing            ) => putStrLn "Unrecognised morphism associated to an edge"
            _                                            => putStrLn "Vertices have invalid typedefs"
        Nothing   => putStrLn "Invalid path"
    (Just _    , Nothing    ) => putStrLn "Labels lookup failed"
    _                         => putStrLn "Edges parsing failed"

partial
main : IO ()
main = do Right options <- processArgs <$> getArgs
            | Left (ErrorMsg msg) => putStrLn msg
          case options of
               Help => putStrLn helpMessage
               HelpFallback => putStrLn fallbackMessage
               Run o => runWithOptions o
