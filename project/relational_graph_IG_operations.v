Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

(*
Require Import Coq.Arith.Arith.

Require Import Bool.


Require Import MyProject.project.util.util.

Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_theory.


Require Import Coq.Sets.Ensembles.
Require Import MyProject.project.util.NatSet.
*)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.


(* Defines the IG functions in terms of an RG (notice that it has generic edge or node label types) *)


  (* {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-} *)

Definition edgeRelation (A B: Type) := A -> A -> B -> Prop.


(* Here, I first _temporarily_ define a more powerful RG, which has edge labels. The current RG can be derived from it *)


Definition _valid_cond {A B: Type} (nodes : Ensemble A) (edges : edgeRelation A B) : Prop :=
    forall (a1 a2 : A) (b : B), edges a1 a2 b -> nodes a1 /\ nodes a2.


Record RG (A B: Type) := {
    RG_nodes : Ensemble A;
    RG_edges : edgeRelation A B;
    RG_valid : _valid_cond RG_nodes RG_edges
}.


Arguments RG_nodes {A B}.
Arguments RG_edges {A B}.
Arguments RG_valid {A B}.


Ltac RG_valid_prover := unfold _valid_cond; firstorder.
Ltac RG_valid_prover_with rg := pose proof rg.(RG_valid); RG_valid_prover.
Ltac RG_valid_prover_withs rg1 rg2 := pose proof rg1.(RG_valid); RG_valid_prover_with rg2.

(* Two relational graphs are "the same", when their Ensemble and relation are the same *)
Definition RG_equiv {A B : Type} (rg1 rg2 : RG A B) : Prop :=
    (* The first condition is definitely needed, as we can have "singleton" graphs *)
    (forall (a : A), rg1.(RG_nodes) a <-> rg2.(RG_nodes) a)
    /\ (forall (a1 a2 : A) (b : B), rg1.(RG_edges) a1 a2 b <-> rg2.(RG_edges) a1 a2 b)
.
Notation "g1 === g2" := (RG_equiv g1 g2) (at level 100, right associativity).


Definition RG_unlE (A : Type) := RG A unit.
(* The followign two don't actually make sense, since one needs a node type for... well nodes to exists *)
(* Definition RG_unlN (B : Type) := RG unit B.
Definition RG_unl (B : Type) := RG unit unit. *)


Definition my_Basic_Graph : RG_unlE nat.
Proof.
  refine ({|
    RG_nodes :=     fun X => (X = 0) \/ (X = 1) \/ (X = 2);
    RG_edges := (fun (A B: nat) l => ((A = 0) /\ (B = 1)) \/ 
                                                ((A = 1) /\ (B = 2)));
    RG_valid := _
  |}).
  RG_valid_prover.
Defined.


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







(* Defining fundamental Operations on RGs: *)

Definition RG_empty {A B : Type} : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => False;
        RG_edges := fun a1 a2 l => False;
        RG_valid := _
    |}.
    RG_valid_prover.
Defined.

Definition RG_isEmpty {A B: Type} (rg : RG A B) : Prop :=
    forall (a : A), rg.(RG_nodes) a = False
.



(* There's more but I didn't bring it over from relational_graph yet *)



(* Now go to defining the IG ("not basic") operations,  this is what in the end will stay in this file *)


                                             
(* A "set" of adjacencies with the edge label and the label of the neighbour  *)
(* type Adj b = [(b, Node)] *)
Definition Adj (A B : Type) := B -> A -> Prop.

(* type Context a b  = (Adj b,Node,a,Adj b) *)
Definition Context (A B : Type) := (Adj A B * A * Adj A B)%type.

(* type LEdge b = (Node,Node,b) *)
Definition Edge (A B : Type) :=  (A * A * B)%type.

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
Definition _getFromsAndTos {A B : Type} (node : A) (rg : RG A B) : Prop * Context A B :=
  (rg.(RG_nodes) node, ((fun l (from : A) => rg.(RG_edges) from node l), node, (fun l (to : A) => rg.(RG_edges) node to l)))
.




Definition RG_match {A B : Type} (node : A) (rg : RG A B) : (Prop * Context A B) * RG A B :=
  (_getFromsAndTos node rg, _eliminate node rg)
.

Require Import MyProject.project.util.util.

Definition _add {A B : Type} (context : Context A B) (rg : RG A B) : RG A B.
Proof.
  destruct context as [[froms node] tos].
  Print Adj.
  refine {|
      RG_nodes := fun (n : A) =>  (exists l, froms l n) \/
                                  (exists l, tos l n) \/
                                  _customEnsembleAdd node rg.(RG_nodes) n;
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
Definition _insEdge {A B : Type} (edge : Edge A B) (rg : RG A B) : RG A B.
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


Definition _insEdges {A B : Type} (edges : list (Edge A B)) (rg : RG A B) : RG A B :=
  fold_right _insEdge rg edges.

Definition RG_mkGraph {A B : Type} (nodes : list A) (edges : list (Edge A B)) : RG A B :=
  _insEdges edges (_insNodes nodes RG_empty).
 

Definition RG_labNodes {A B : Type} (rg : RG A B) : Ensemble A :=
  rg.(RG_nodes).

