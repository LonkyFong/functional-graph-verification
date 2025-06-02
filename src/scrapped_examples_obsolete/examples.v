Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Relations.Relation_Operators.
Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Require Import GraphVerification.src.relational_graph.

Require Import GraphVerification.src.algebraic.algebraic_graph.
Require Import GraphVerification.src.algebraic.algebraic_graph_to_RG.
Require Import GraphVerification.src.algebraic.algebraic_graph_theory.

Require Import GraphVerification.src.inductive.inductive_graph.
Require Import GraphVerification.src.inductive.basic.inductive_graph_basic.



(* Mini examples, I had in other files but I moved here for cleanness *)


(* RGs --------------------------------------------------------------------------- *)
(* Definition Powerset : Type -> Type :=
    fun X => X -> Prop. *)

Definition my_Finite_Type : (Ensemble nat) := 
    fun X => (X = 0) \/ (X = 1) \/ (X = 2) .


Definition my_Basic_Graph : RG nat unit.
Proof.
  refine ({|
    RG_nodes := my_Finite_Type;
    RG_edges := (fun (A B : nat) l => ((A = 0) /\ (B = 1)) \/ 
                                    ((A = 1) /\ (B = 2)));
    RG_valid := _
  |}).
  RG_valid_prover.
Defined.



Print my_Basic_Graph.

Compute my_Basic_Graph.(RG_nodes).
Compute my_Basic_Graph.(RG_edges).

(* 0 -> 1 -> 2 *)

Example RG_existsPath_example : RG_existsPath 0 1 my_Basic_Graph.
Proof.
    compute. apply t_step. exists tt. auto.
Qed.

(* 0 -> 1 -> 2 *)
Example RG_existsPath_example' : RG_existsPath 0 2 my_Basic_Graph.
Proof.
    compute. apply (t_trans _ _ _ 1).
    - apply t_step. exists tt. auto.
    - apply t_step. exists tt. auto.
Qed.





Definition my_Basic_Labelled_Graph : RG nat string.
Proof.

  refine ({|
    RG_nodes := fun X => (X = 0) \/ (X = 1) \/ (X = 2);
    RG_edges := (fun (A B : nat) (l : string)  => ((A = 0) /\ (B = 1) /\ (l = "this is a label")) \/ 
                                                  ((A = 0) /\ (B = 1) /\ (l = "We can have multigraphs??")) \/ 
                                                  ((A = 1) /\ (B = 2) /\ (l = "this is a label")));
    RG_valid := _
  |}).
  RG_valid_prover.
Defined.






(* AGs --------------------------------------------------------------------------- *)

Theorem AG_equiv_rewrite_test_basic : forall (ag1 ag2 ag3 : AG nat), AG_equiv ag1 ag2 -> AG_equiv ag2 ag3 -> AG_equiv ag1 ag3.
Proof.
    intros. rewrite H. rewrite H0. reflexivity.
Qed.


Theorem AG_equiv_rewrite_test_advanced : forall (ag1 ag2 ag3 : AG nat), AG_equiv ag1 ag2 -> AG_equiv (ag2 +++ Empty) ag3 -> AG_equiv (ag1 +++ Empty) ag3.
Proof.
    intros. rewrite H. rewrite H0. reflexivity.
Qed.


(* Messing around --------------------------------------------------------------------------- *)
(* 
Compute IG_show (add ([], 2, "a", [("nodel", 1); ("nose",1)]) (add ([], 1, "a", []) IG_empty)). 

Definition my_basic_graph := IG_mkGraph [(1, "a"); (2, "b"); (3, "c")] [(1, 2, "edge1"); (2, 3, "edge2"); (3, 1, "edge3")].
Compute IG_show my_basic_graph.


Definition my_basic_graph' := IG_mkGraph [(1, "a"); (2, "b"); (3, "c")] [(3, 1, "edge3")].
Compute IG_show my_basic_graph'.
Compute IG_show (insEdge (1, 2 , "edge1") my_basic_graph').

Compute IG_show (add ([("edge3", 3)], 1, "a", [("edge1", 2)]) (IG_mkGraph [(2, "b"); (3, "c")] [])).

Theorem bla : IG_match 2 my_basic_graph = (None, IG_empty).
Proof.
  compute.


Theorem bla : insEdge (1, 2 , "edge1") my_basic_graph' = IG_empty.
Proof.
  unfold insEdge.
  unfold my_basic_graph'.
  unfold IG_match.
  


Theorem bla : my_basic_graph = IG_empty.
Proof.
  unfold my_basic_graph.
  unfold IG_mkGraph.
  unfold insEdges.
  unfold fold_right.
 *)



(* IGs --------------------------------------------------------------------------- *)


Compute IG_show (IG_mkGraph [(1, 1); (2, 2); (3, 3)] [(1, 2, 1); (2, 3, 2); (3, 1, 3)]).

Definition my_basic_graph := IG_mkGraph [(1, "a"); (2, "b"); (3, "c")] [(1, 2, "edge1"); (2, 3, "edge2"); (3, 1, "edge3")].

(* Here come the tests for each defined function (that is in the graph class): *)

Compute IG_show IG_empty.

Compute IG_isEmpty IG_empty.
Compute IG_isEmpty my_basic_graph.

Compute IG_show my_basic_graph.
Compute Decomp_show (IG_match 2 my_basic_graph).

Compute IG_show (IG_mkGraph [(1, "a"); (2, "b"); (3, "c")] [(1, 2, "edge1"); (2, 3, "edge2"); (3, 1, "edge3")]).

Compute IG_labNodes my_basic_graph.


(* IG_basic s --------------------------------------------------------------------------- *)


Compute IG_basic_showIG (IG_basic_mkGraph [1; 2; 3] [(1, 2); (2, 3); (3, 1)]).

Definition myBasicGraph := IG_basic_mkGraph [1; 2; 3] [(1, 2); (2, 3); (3, 1)].

(* Here come the tests for each defined function (that is in the graph class): *)

Compute IG_basic_showIG IG_basic_empty.

Compute IG_basic_isEmpty IG_basic_empty.
Compute IG_basic_isEmpty myBasicGraph.

Compute IG_basic_showDecomp (IG_basic_match 2 myBasicGraph).

Compute IG_basic_showIG (IG_basic_mkGraph [1; 2; 3] [(1, 2); (2, 3); (3, 1)]).

Compute IG_basic_labNodes myBasicGraph.

(* Self-loops *)
Compute IG_basic_showIG (IG_basic_mkGraph [1] [(1, 1)]).


Example basic_equivalence_test : (IG_basic_mkGraph [1; 2] []) I== (IG_basic_mkGraph [2; 1] []).
Proof.
    unfold IG_basic_equiv. unfold RG_equiv. firstorder.
Qed.

Example basic_equivalence_test' : (IG_basic_mkGraph [1; 2; 3] [(1, 2); (2, 3)]) I== (IG_basic_mkGraph [2; 1; 3] [(2, 3); (1, 2)]).
Proof.
    unfold IG_basic_equiv. unfold RG_equiv. firstorder.
Qed.