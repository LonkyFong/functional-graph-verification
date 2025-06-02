Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

(*
Require Import Coq.Arith.Arith.

Require Import Bool.


Require Import MyProject.project.util.util.

Require Import MyProject.project.relational_graph_theory.


Require Import Coq.Sets.Ensembles.
Require Import MyProject.project.util.NatSet.
*)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.

Require Import MyProject.project.relational_graph.

Require Import MyProject.project.util.util.



(* Defines the IG functions in terms of an RG (notice that it has generic edge or node label types) *)


  (* {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-} *)


(* A "set" of adjacencies with the edge label and the label of the neighbour  *)
(* type Adj b = [(b, Node)] *)
Definition RG_Adj (A B : Type) := B -> A -> Prop.

(* type Context a b  = (Adj b,Node,a,Adj b) *)
Definition RG_Context (A B : Type) := (RG_Adj A B * A * RG_Adj A B)%type.

(* type Decomp g a b = (MContext a b,g a b) *)
Definition RG_Decomp (A B : Type) := ((Prop * RG_Context A B) * RG A B)%type.

(* type LEdge b = (Node,Node,b) *)
Definition RG_Edge (A B : Type) :=  (A * A * B)%type.






(* Defining equivalences for the sake of proving stuff *)

Definition RG_Adj_equiv {A B : Type} (adj1 adj2 : RG_Adj A B) : Prop :=
  forall (a : A) (b : B), adj1 b a <-> adj2 b a.


Notation "adj1 A== adj2" := (RG_Adj_equiv adj1 adj2) (at level 100, right associativity).


Definition RG_Context_equiv {A B : Type} (c1 c2 : RG_Context A B) : Prop :=
  match c1, c2 with | (fromsC1, nC1, tosC1), (fromsC2, nC2, tosC2) =>
      nC1 = nC2 /\ RG_Adj_equiv fromsC1 fromsC2 /\ RG_Adj_equiv tosC1 tosC2
  end
.

Notation "c1 C== c2" := (RG_Context_equiv c1 c2) (at level 79, right associativity).

Definition RG_Decomp_equiv {A B : Type} (d1 d2 : RG_Decomp A B) : Prop :=
  match d1, d2 with | ((opt1, context1), rg1), ((opt2, context2), rg2) =>
    (opt1 <-> opt2) /\ context1 C== context2 /\ (rg1 === rg2)
  end
.

Notation "c1 D== c2" := (RG_Decomp_equiv c1 c2) (at level 79, right associativity).


(* Start defining functionality: *)
Print RG_empty.
(* Definition RG_empty {A B} : RG A B :=
    RG_empty. *)

Print RG_isEmpty.
(* Definition RG_isEmpty {A B: Type} (rg : RG A B) : Prop :=
  RG_isEmpty rg. *)



(* Helper for match *)
(* Removes a node from the nodeset and any edges *)
Definition _eliminate {A B : Type} (node : A) (rg : RG A B) : RG A B.
Proof.
  refine {|
      RG_nodes := Subtract A rg.(RG_nodes) node;
      RG_edges := fun (n1 n2 : A) (l : B) => n1 <> node /\ n2 <> node /\  rg.(RG_edges) n1 n2 l;
      RG_valid := _
  |}.
  RG_valid_prover_with rg.
  - unfold not. intros. inversion H3. congruence.
  - unfold not. intros. inversion H3. congruence.
Defined.



(* Checks if the node is in the RG (the Prop return) and returns two sets of alls incoming neighbors and outgoing neighbors *)
Definition _getFromsAndTos {A B : Type} (node : A) (rg : RG A B) : Prop * RG_Context A B :=
  let isValid := rg.(RG_nodes) node in
  (isValid, ((fun l (from : A) => isValid /\ rg.(RG_edges) from node l),
              node,
              (fun l (to : A) => isValid /\ rg.(RG_edges) node to l)))
.


Definition RG_match {A B : Type} (node : A) (rg : RG A B) : RG_Decomp A B :=
  (_getFromsAndTos node rg, _eliminate node rg)
.


Definition _add {A B : Type} (context : RG_Context A B) (rg : RG A B) : RG A B.
Proof.
  destruct context as [[froms node] tos].
  Print RG_Adj.
  refine {|
      RG_nodes := fun (n : A) =>  (exists l, froms l n) \/
                                  (exists l, tos l n) \/
                                  Ensemble_add node rg.(RG_nodes) n;
      RG_edges := fun (n1 n2 : A) (l : B) =>  (froms l n1 /\ n2 = node) \/
                                              (n1 = node /\ tos l n2) \/ 
                                              rg.(RG_edges) n1 n2 l;
      RG_valid := _
  |}.
  RG_valid_prover_with rg.
Defined.


Definition _insNode {A B : Type} (node : A) (rg : RG A B) : RG A B :=
  _add (fun x y => False, node , fun x y => False) rg.
  

Definition _insNodes {A B : Type} (nodes : list A) (rg : RG A B) : RG A B :=
  fold_right _insNode rg nodes.


(* If one of the nodes of the edge does not exist, nothing happens *)
Definition _insEdge {A B : Type} (edge : RG_Edge A B) (rg : RG A B) : RG A B.
Proof.
  destruct edge as [[node1 node2] elabel].
    refine {|
      RG_nodes := rg.(RG_nodes);
      RG_edges := fun (n1 n2 : A) (l : B) =>  (n1 = node1 /\ n2 = node2 /\ l = elabel /\ rg.(RG_nodes) node1 /\ rg.(RG_nodes) node2) \/ 
                                              rg.(RG_edges) n1 n2 l;
      RG_valid := _
  |}.
  RG_valid_prover_with rg.
  - congruence.
  - congruence.
Defined.


Definition _insEdges {A B : Type} (edges : list (RG_Edge A B)) (rg : RG A B) : RG A B :=
  fold_right _insEdge rg edges.

Definition RG_mkGraph {A B : Type} (nodes : list A) (edges : list (RG_Edge A B)) : RG A B :=
  _insEdges edges (_insNodes nodes RG_empty).
 

Definition RG_labNodes {A B : Type} (rg : RG A B) : Ensemble A :=
  rg.(RG_nodes).

