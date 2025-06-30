Require Import Extraction.

Require Import GraphVerification.src.inductive.IG.
Require Import GraphVerification.src.inductive.IG_wf_operations.

Require Import GraphVerification.src.algebraic.AG.


Require Import GraphVerification.src.relational.RG.

Extraction Language Haskell.

(** For both inductive graphs and algebraic graphs, the exported code need to be tweaked lightly, to be user-friendly
    All functions have been tested on basic testcases.
    Some testcases which can be manually run in ghci can be found in "testcases.hs".

    Notice that the extracted code is mostly translation
    of the verified (balanced-search-tree-based) map and set implementations  *)


Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extract Inductive list => "[]" ["[]" "(:)"].

Extract Inductive prod => "(,)" ["(,)"].


Extraction "IG_extracted'.hs"
    IG_empty
    IG_isEmpty
    IG_match
    IG_and
    IG_mkGraph
    IG_labNodes
    IG_matchAny
    IG_noNodes
    IG_nodeRange
    IG_labEdges
    IG_ufold
    IG_gmap
    IG_transpose
    IG_DFS
.
  
 
Extraction "AG_extracted'.hs"
    AG_empty
    AG_vertex
    AG_overlay
    AG_connect
    AG_vertices
    AG_edge
    AG_edges
    AG_makeGraph
    AG_transpose
    AG_toList
    AG_gmap
    AG_mergeVertices
    AG_bind
    AG_induce
    AG_removeVertex
    AG_removeEdge
    AG_nodeSet
    AG_nodeAmount
    AG_BFS
.






(* Extraction Language OCaml.
Extraction "extractionTest.ml" turn_both_to_0_L_Caller. *)


