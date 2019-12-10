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

-- tparsec
import Data.NEList
import TParsec
import TParsec.Running

import Computer.Computer
import Computer.Example2A
import GraphFunctor.GraphEmbedding
import ErrDef
import Parser.Cmdline
import Parser.Input
import Util.Misc
import Util.Max

%access public export
%default total

data ComputeError
  = ComputationError
  | PathDoesNotStartAtUnit

Show ComputeError where
  show ComputationError       = "error while performing the computation"
  show PathDoesNotStartAtUnit = "path not starting at Unit"

computeOnPath : {vs : NEList (Nat, String)}
                  -> (graph : Graph (Fin $ length vs))
                  -> (verticesTypedefs : Vect (length vs) (TDef 0))
                  -> Vect (numEdges graph) (mor' $ Computer.cClosedTypedefsKleiliCategory FFI_C)
                  -> Path graph initialVertex finalVertex
                  -> Either ComputeError (IO (Ty [] (Vect.index finalVertex verticesTypedefs)))
computeOnPath {vs} {initialVertex} graph verticesTypedefs edgesMorphisms path with (Vect.index initialVertex verticesTypedefs) proof prf
  computeOnPath {vs} {initialVertex} graph verticesTypedefs edgesMorphisms path | T1 =
    maybe (Left ComputationError) Right $
      Computer.compute {ffi=FFI_C}
                       graph
                       (isoRefl {a=Fin (length vs)})
                       verticesTypedefs
                       edgesMorphisms
                       path
                       (rewrite sym prf in ())
  computeOnPath {vs} {initialVertex} graph verticesTypedefs edgesMorphisms path | _ = Left PathDoesNotStartAtUnit

runWithOptions : CoreOpts -> IO ()
runWithOptions (MkCoreOpts (TDFile tdf) (FSMFile fsmf) firings) = do
  disableBuffering  -- don't remove this!
  Right tdef <- Input.readTypedefs tdf
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
              case computeOnPath {vs}
                                 graph
                                 (snd <$> verticesTypedefs)
                                 (rewrite prf in edgesMorphisms)
                                 path of
                Right computation => ignore computation
                Left  error       => printLn error
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
