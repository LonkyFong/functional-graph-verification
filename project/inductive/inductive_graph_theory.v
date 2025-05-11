Require Import String.
Require Import Coq.Arith.Arith.

Require Import List.
Require Import Bool.
Import ListNotations.
Require Import Setoid Morphisms.


Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_theory.

Require Import MyProject.project.inductive.inductive_graph.
Require Import MyProject.project.inductive.inductive_graph_to_RG.

Open Scope nat_scope.


(* Section to make rewrite work with IG_equiv *)
(* This proof is based on === being an equivalence relation *)
Instance IG_Equivalence_eq {A : Type} : Equivalence (@IG_equiv A).
Proof.
    G_derived_equivalence_prover A unit (@id (IG A unit)).
Qed. 


Example basic_equivalence_test : (mkGraph [(1, "1"); (2, "2")] []) I== (mkGraph [(2, "2"); (1, "1")] []).
Proof.
  unfold IG_equiv. unfold RG_equiv. simpl. split; split; intros.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.




(* (attempt at) direct equational specifications of an IG: *)


Theorem spec1 : forall A B, isEmpty (@empty A B) = true.
Proof.
  intros. compute. reflexivity.
Qed.

Theorem spec2 : forall (A B : Type) (nl : list (LNode A)) (el : list (LEdge B)), labNodes (mkGraph nl el) = nl.
Proof.
  intros. compute.
Admitted.

Theorem spec3 : forall (A B : Type) (n : node), matsh n (@empty A B) = (None, empty).
Proof.
  intros. compute.
Admitted.

Theorem spec4 : forall (A B : Type) (n : LNode A) (nl : list (LNode A)) (el : list (LEdge B)), 
  In n nl -> exists map1 map2, matsh (fst n) (mkGraph nl el) =
  (Some ((map1), snd n, (map2)), mkGraph (filter (fun '(idx, lab) => negb (fst n =? idx)) nl) (filter (fun '(to, from, lab) => negb ((to =? fst n) || (from =? fst n))) el)).
(* This is not even a complete specification and it looks like a nightmare to prove... *)
Admitted.

Theorem spec5 : forall (A B : Type) (n : LNode A) (nl : list (LNode A)) (el : list (LEdge B)), 
  not (In n nl) -> matsh (fst n) (mkGraph nl el) = (None, mkGraph nl el).
Admitted.

