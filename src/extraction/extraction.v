Require Import Extraction.

Require Import GraphVerification.src.inductive.IG.
Require Import GraphVerification.src.inductive.IG_wf_operations.

Require Import GraphVerification.src.algebraic.AG.


Require Import GraphVerification.src.relational.RG.

Extraction Language Haskell.

(** This file initiates extraction of the executable code of algebraic and inductive graphs respectively.
    The code gets extracted to Haskell and nat, bool, list, and prod are turned into their Haskell counterparts.
    MSet and FMap are not translated, which is why most of the extracted code is code to implement the
    balanced-search-tree from the standard library

    The exported code need to be tweaked lightly, to be user-friendly. The tweaks can be found in
    "IG_extraction_tweaks.hs"

    Basic code snippets to tun the examples with can be found in "example_operations.hs" *)


Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extract Inductive list => "[]" ["[]" "(:)"].

Extract Inductive prod => "(,)" ["(,)"].


Extraction "IG_extracted.hs"
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
  
 
Extraction "AG_extracted.hs"
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
