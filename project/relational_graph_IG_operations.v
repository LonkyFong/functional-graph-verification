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


(* Defines the IG functions in terms of an RG (notice that it has generic edge or node label types) *)


  (* {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-} *)


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

