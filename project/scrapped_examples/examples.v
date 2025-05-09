Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Relations.Relation_Operators.
Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Require Import MyProject.project.relational_graph.

Require Import MyProject.project.algebraic.algebraic_graph.
Require Import MyProject.project.algebraic.algebraic_graph_to_RG.
Require Import MyProject.project.algebraic.algebraic_graph_theory.

Require Import MyProject.project.inductive.inductive_graph.



(* Mini examples, I had in other files but I moved here for cleanness *)


(* RGs --------------------------------------------------------------------------- *)
(* Definition Powerset : Type -> Type :=
    fun X => X -> Prop. *)

Definition my_Finite_Type : (Ensemble nat) := 
    fun X => (X = 0) \/ (X = 1) \/ (X = 2) .


Definition my_Basic_Graph : RG nat.
Proof.
  refine ({|
    RG_nodes := my_Finite_Type;
    RG_edges := (fun (A B : nat) => ((A = 0) /\ (B = 1)) \/ 
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
    compute. apply t_step. auto.
Qed.

(* 0 -> 1 -> 2 *)
Example RG_existsPath_example' : RG_existsPath 0 2 my_Basic_Graph.
Proof.
    compute. apply (t_trans _ _ _ 1).
    - apply t_step. auto.
    - apply t_step. auto.
Qed.


(* AGs --------------------------------------------------------------------------- *)

Theorem AG_equiv_rewrite_test_basic : forall (ag1 ag2 ag3 : AG nat), AG_equiv ag1 ag2 -> AG_equiv ag2 ag3 -> AG_equiv ag1 ag3.
Proof.
    intros. rewrite H. rewrite H0. reflexivity.
Qed.


Theorem AG_equiv_rewrite_test_advanced : forall (ag1 ag2 ag3 : AG nat), AG_equiv ag1 ag2 -> AG_equiv (ag2 +++ Empty) ag3 -> AG_equiv (ag1 +++ Empty) ag3.
Proof.
    intros. rewrite H. rewrite H0. reflexivity.
Qed.








(* IGs --------------------------------------------------------------------------- *)


Compute show_IG (mkGraph [(1, 1); (2, 2); (3, 3)] [(1, 2, 1); (2, 3, 2); (3, 1, 3)]).

Definition my_basic_graph := mkGraph [(1, "a"); (2, "b"); (3, "c")] [(1, 2, "edge1"); (2, 3, "edge2"); (3, 1, "edge3")].

(* Here come the tests for each defined function (that is in the graph class): *)

Compute show_IG empty.

Compute isEmpty empty.
Compute isEmpty my_basic_graph.

Compute show_Decomp (matsh 2 my_basic_graph).

Compute show_IG (mkGraph [(1, "a"); (2, "b"); (3, "c")] [(1, 2, "edge1"); (2, 3, "edge2"); (3, 1, "edge3")]).

Compute labNodes my_basic_graph.