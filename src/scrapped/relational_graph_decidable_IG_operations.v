

Require Import String.

Require Import List.
Import ListNotations.


Require Import Bool.
Require Import Coq.Sorting.Permutation.


Require Import GraphVerification.src.RG_decidable.
Require Import GraphVerification.src.util.util.
Require Import GraphVerification.src.util.NatMap.

Require Import Coq.Arith.Arith.

Open Scope nat_scope.





(* Defines the IG functions in terms of an RG (notice that it has generic edge or node label types) *)


  (* {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-} *)

(* These are the interfacing types of an IG _copied_ from the paper *)
(* type Adj b = [(b, Node)] *)
Definition Adj (B : Type) := list (B * Node).

(* type Context a b  = (Adj b,Node,a,Adj b) *)
Definition Context (A B : Type) : Type := (Adj B * Node * A * Adj B)%type.

(* type Decomp g a b = (MContext a b,g a b) *)
Definition Decomp (A B : Type) := (option (Context A B) * RG_dec A B)%type. 

(* type LEdge b = (Node,Node,b) *)
Definition LEdge (B : Type) :=  (Node * Node * B)%type. 

(* type LNode a = (Node,a) *)
Definition LNode (A : Type) :=  (Node * A)%type.



(* Defining equivalences for the sake of proving stuff *)

Definition Adj_equiv {B : Type} (adj1 adj2 : Adj B) : Prop :=
  Permutation adj1 adj2
. 

Notation "adj1 A== adj2" := (Adj_equiv adj1 adj2) (at level 100, right associativity).


Definition Context_equiv {A B : Type} (c1 c2 : Context A B) : Prop :=
  match c1, c2 with | (fromsC1, nC1, lC1, tosC1), (fromsC2, nC2, lC2, tosC2) =>
      Adj_equiv fromsC1 fromsC2 /\ nC1 = nC2 /\ lC1 = lC2 /\ Adj_equiv tosC1 tosC2
  end
.

Notation "c1 C== c2" := (Context_equiv c1 c2) (at level 79, right associativity).

Definition Decomp_equiv {A B : Type} (d1 d2 : Decomp A B) : Prop :=
  match d1, d2 with
    | (Some (context1), rg1), (Some (context2), rg2) =>
      context1 C== context2 /\ (rg1 R== rg2)
    | (None, rg1), (None, rg2) =>
      rg1 R== rg2
    | _, _ => False
  end
.

Notation "c1 D== c2" := (Decomp_equiv c1 c2) (at level 79, right associativity).


(* Start defining functionality: *)
Print RG_dec_empty.
(* Definition RG_empty {A B} : RG A B :=
    RG_empty. *)

Print RG_dec_isEmpty.
(* Definition RG_isEmpty {A B: Type} (rg : RG A B) : Prop :=
  RG_isEmpty rg. *)


Definition filter_map {A : Type} (pred : PairNatMap.key -> A -> bool) (m : PairNatMap.t A) : PairNatMap.t A :=
  PairNatMap.fold (fun k v acc =>
            if pred k v then PairNatMap.add k v acc else acc)
         m
         (PairNatMap.empty A)
.


(* Helper for match *)
(* Removes a node from the nodeset and any edges *)
Definition _eliminate {A B : Type} (node : Node) (rg : RG_dec A B) : RG_dec A B.
Proof.
  refine {|
      RG_dec_nodes := NatMap.remove node rg.(RG_dec_nodes); 
      RG_dec_edges := filter_map (fun '((from, to) : (nat*nat)) labels => negb ((from =? node) || (to =? node))) rg.(RG_dec_edges); 
      RG_dec_valid := _
  |}.
Admitted.

Check fold_right.
(* (B -> A -> A) -> A -> list B -> A *)

(* Checks if the node is in the RG_dec (the Prop return) and returns two sets of alls incoming neighbors and outgoing neighbors *)
Definition _getFromsAndTos {A B : Type} (node : Node) (rg : RG_dec A B) : option (Context A B) :=
  match NatMap.find node rg.(RG_dec_nodes) with
    | Some _ => match NatMap.find node rg.(RG_dec_nodes) with
                 | Some label => Some (
                  fold_right (fun '((n, l) : Node * A) acc => 
                        let edges := PairNatMap.find (n, node) rg.(RG_dec_edges) in
                        match edges with
                          | Some edges => (map (fun '(b : B) => (b, n)) edges) ++ acc
                          | None => acc
                        end
                 ) [] (NatMap.elements rg.(RG_dec_nodes))
                 
                 ,
                                   node,
                                   label,
                                   fold_right (fun '((n, l) : Node * A) acc => 
                        let edges := PairNatMap.find (node, n) rg.(RG_dec_edges) in
                        match edges with
                          | Some edges => (map (fun '(b : B) => (b, n)) edges) ++ acc
                          | None => acc
                        end
                 ) [] (NatMap.elements rg.(RG_dec_nodes))
                 )
                                   
                 | None => None
               end
    | None => None
  end
.


(* The code for match is basically as complicated as the code for match on a "real" rg.... *)
Definition RG_dec_match {A B : Type} (node : Node) (rg : RG_dec A B) : Decomp A B :=
  (_getFromsAndTos node rg, _eliminate node rg)
.


(* Definition _add {A B : Type} (context : RG_dec_Context A B) (rg : RG_dec A B) : RG_dec A B.
Proof.
  destruct context as [[froms node] tos].
  Print RG_dec_Adj.
  refine {|
      RG_dec_nodes := fun (n : A) =>  (exists l, froms l n) \/
                                  (exists l, tos l n) \/
                                  Ensemble_add node rg.(RG_dec_nodes) n;
      RG_dec_edges := fun (n1 n2 : A) (l : B) =>  (froms l n1 /\ n2 = node) \/
                                              (n1 = node /\ tos l n2) \/ 
                                              rg.(RG_dec_edges) n1 n2 l;
      RG_dec_valid := _
  |}.
  RG_dec_valid_prover_with rg.
Defined. *)


Definition _insNode {A B : Type} (node : LNode A) (rg : RG_dec A B) : RG_dec A B.
Proof.
  destruct node as [n l].
    refine {|
      RG_dec_nodes := NatMap.add n l rg.(RG_dec_nodes);
      RG_dec_edges := rg.(RG_dec_edges);
      RG_dec_valid := _
  |}.
Admitted.


Definition _insNodes {A B : Type} (nodes : list (LNode A)) (rg : RG_dec A B) : RG_dec A B :=
  fold_right _insNode rg nodes.


Definition update_with_default {A : Type} (f : A -> A) (d : A) (k : PairNatMap.key) (m : PairNatMap.t A) : PairNatMap.t A :=
  let v := match PairNatMap.find k m with
           | Some x => x
           | None => d
           end in
  PairNatMap.add k (f v) m.

(* If one of the nodes of the edge does not exist, nothing happens *)
Definition _insEdge {A B : Type} (edge : LEdge B) (rg : RG_dec A B) : RG_dec A B. 
Proof.
  destruct edge as [[from to] l].
    refine {|
      RG_dec_nodes := rg.(RG_dec_nodes);
      RG_dec_edges := update_with_default (fun labels => l::labels) [l] (from, to) rg.(RG_dec_edges);
      RG_dec_valid := _
  |}.
Admitted.


Definition _insEdges {A B : Type} (edges : list (LEdge B)) (rg : RG_dec A B) : RG_dec A B :=
  fold_right _insEdge rg edges.

Definition RG_dec_mkGraph {A B : Type} (nodes : list (LNode A)) (edges : list (LEdge B)) : RG_dec A B :=
  _insEdges edges (_insNodes nodes RG_dec_empty).
 

Definition RG_dec_labNodes {A B : Type} (rg : RG_dec A B) : list (LNode A) :=
  NatMap.elements rg.(RG_dec_nodes).


