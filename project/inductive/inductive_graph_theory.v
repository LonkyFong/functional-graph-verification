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
Instance IG_Equivalence {A : Type} : Equivalence (@IG_equiv A).
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



(* Stuff for the vaolidity checker *)

Definition set_from_list (l : list node) : option NatSet.t :=
  fold_right (fun (k : node) (acc : option NatSet.t) =>
                bind acc (fun (acc : NatSet.t) => if NatSet.mem k acc then None else Some (NatSet.add k acc))
              ) (Some NatSet.empty) l.

  

Definition IG_map_out_keys {A B : Type} (IG_data : NatMap.t (Context' A B)) : option NatSet.t :=
  set_from_list (
    concat (
      map (fun '((_, (_, _, out_map)) : (node * Context' A B)) => map fst (NatMap.elements out_map))
        
      (NatMap.elements IG_data)
    )
  )
.


Definition IG_map_in_keys {A B : Type} (IG_data : NatMap.t (Context' A B)) : option NatSet.t :=
  set_from_list (
    concat (
      map ( fun '((_, (in_map, _, t_step)) : (node * Context' A B)) => map fst (NatMap.elements in_map))
      (NatMap.elements IG_data)
    )
  )
.

Definition IG_nodes_keys {A B : Type} (IG_data : NatMap.t (Context' A B)) : option NatSet.t :=
  set_from_list (map fst (NatMap.elements IG_data))
.


Definition IG_valid_cond_fun {A B : Type} (IG_data : NatMap.t (Context' A B)) : bool :=
  let in_keys := IG_map_in_keys IG_data in
  let out_keys := IG_map_out_keys IG_data in

  let edge_diffs := bind in_keys (fun (in_keys : NatSet.t) => bind out_keys
                                  (fun (out_keys : NatSet.t) => Some (NatSet.diff in_keys out_keys))) in

  let edge_keys := bind in_keys (fun (in_keys : NatSet.t) => bind out_keys
                                  (fun (out_keys : NatSet.t) => Some (NatSet.union in_keys out_keys))) in

  
  let node_keys := IG_nodes_keys IG_data in

  match edge_diffs, edge_keys, node_keys with
  | Some edge_diffs, Some edge_keys, Some node_keys =>
    NatSet.is_empty edge_diffs && NatSet.equal edge_keys node_keys
  | _, _, _ => false
  end
.
  

Definition _valid_cond {A B : Type} (IG_data : NatMap.t (Context' A B)) : Prop :=
  IG_valid_cond_fun IG_data = true.



Definition IG_data_unsafe (A B : Type) : Type :=
  NatMap.t (Context' A B).