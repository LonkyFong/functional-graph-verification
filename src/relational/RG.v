Require Import Relation_Definitions.
Require Import Relations.Relation_Operators.
Require Import Ensembles.
Require Import List.
Require Import Permutation.
Require Import Bool.


Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.util.


(** Defining a relational_graph (RG) and its operations.
    It it most similar to the typical graph from discrete mathematics.
    It is useful as a model for verification. *)


Definition _edgeRelation (A B : Type) := A -> A -> B -> Prop.

Definition _unlabelEdgeRelation {A B: Type} (edges : _edgeRelation A B) : relation A :=
    fun (a1 a2 : A) => exists (l : B), edges a1 a2 l.


(* Edges can only connect _existing_ nodes *)
Definition _valid_cond {A B : Type} (nodes : Ensemble A) (edges : _edgeRelation A B) : Prop :=
    forall (a1 a2 : A) (b : B), edges a1 a2 b -> nodes a1 /\ nodes a2.


Record RG (A B : Type) := {
    RG_nodes : Ensemble A;
    RG_edges : _edgeRelation A B;
    RG_valid : _valid_cond RG_nodes RG_edges
}.

Arguments RG_nodes {A B}.
Arguments RG_edges {A B}.
Arguments RG_valid {A B}.

(* Trivialize proving of _valid_cond in most cases *)
Ltac _RG_valid_prover := unfold _valid_cond; firstorder.
Ltac _RG_valid_prover_with rg := pose proof rg.(RG_valid); _RG_valid_prover.
Ltac _RG_valid_prover_withs rg1 rg2 := pose proof rg1.(RG_valid); _RG_valid_prover_with rg2.


Tactic Notation "RG_valid_prover" := _RG_valid_prover.

Tactic Notation "RG_valid_prover" open_constr(rg) :=
  _RG_valid_prover_with rg.

Tactic Notation "RG_valid_prover" open_constr(rg1) open_constr(rg2) :=
  _RG_valid_prover_withs rg1 rg2.





(* Two relational graphs are "the same", when their Ensemble and relation are the same. *)
Definition RG_equiv {A B : Type} (rg1 rg2 : RG A B) : Prop :=
    (* The first condition is definitely needed, as we can have "singleton" graphs *)
    (forall (a : A), rg1.(RG_nodes) a <-> rg2.(RG_nodes) a)
        /\ (forall (a1 a2 : A) (b : B), rg1.(RG_edges) a1 a2 b <-> rg2.(RG_edges) a1 a2 b).

Notation "g1 ==R g2" := (RG_equiv g1 g2) (at level 100, right associativity).

(* A variant of and RG with only single, un-id-able edges *)
Definition RG_unlE (A : Type) := RG A unit.


(* Start defining operations, which are mostly used to verify AG: *)
Definition RG_empty {A B : Type} : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => False;
        RG_edges := fun a1 a2 l => False;
        RG_valid := _
    |}.
    RG_valid_prover.
Defined.


Definition RG_union {A B : Type} (rg1 rg2 : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => rg1.(RG_nodes) a \/ rg2.(RG_nodes) a;
        RG_edges := fun a1 a2 l => rg1.(RG_edges) a1 a2 l \/ rg2.(RG_edges) a1 a2 l;
        RG_valid := _
    |}.
    RG_valid_prover rg1 rg2.
Defined.



Definition RG_vertices {A B : Type} (l : list A) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => In a l;
        RG_edges := fun a1 a2 l => False;
        RG_valid := _
    |}.
    RG_valid_prover.
Defined.

Definition RG_edge {A B : Type} (x y : A) (label : B) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => a = x \/ a = y;
        RG_edges := fun a1 a2 l => a1 = x /\ a2 = y /\ l = label;
        RG_valid := _ 
    |}.
    RG_valid_prover.
Defined.




Definition RG_edgez {A B : Type} (l : list (A * A * B)) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => exists n lab, In (a, n, lab) l \/ In (n, a, lab) l;
        RG_edges := fun a1 a2 lab => In (a1, a2, lab) l;
        RG_valid := _
    |}.
    RG_valid_prover.
Defined.


Definition RG_makeGraph {A B : Type} (vs : list A) (es : list (A * A * B)) : RG A B :=
    RG_union (RG_vertices vs) (RG_edgez es).


Definition RG_toList {A B : Type} (rg : RG A B) : Ensemble A :=
    rg.(RG_nodes).


Definition RG_gmap {A B A' : Type} (f : A -> A') (rg : RG A B) : RG A' B. 
Proof.
    refine {|
        RG_nodes := fun a => exists n, rg.(RG_nodes) n /\ f n = a;
        RG_edges := fun a1 a2 l => exists n1 n2, rg.(RG_edges) n1 n2 l /\ f n1 = a1 /\ f n2 = a2;
        RG_valid := _
    |}.
    RG_valid_prover rg.
    - subst. exists x. firstorder.
    - subst. exists x0. firstorder.
Defined.


Definition RG_mergeVertices {A B : Type} (f : A -> bool) (v : A) (rg : RG A B) : RG A B :=
    RG_gmap (fun x => if f x then v else x) rg.


Definition RG_bind {A B A' : Type} (f : A -> RG A' B) (rg : RG A B) : RG A' B.
Proof.
    refine {|
        RG_nodes := fun (a : A') => exists n, rg.(RG_nodes) n /\ (f n).(RG_nodes) a;
        RG_edges := fun a1 a2 l => 
                                    (* Existing edge *)
                                    (exists n1 n2, rg.(RG_edges) n1 n2 l
                                        /\ (f n1).(RG_nodes) a1
                                        /\ (f n2).(RG_nodes) a2)
                                    (* New edge from f *)
                                    \/ (exists n, rg.(RG_nodes) n
                                        /\ (f n).(RG_edges) a1 a2 l) 
                                    ;
        RG_valid := _
    |}.
    RG_valid_prover rg.
    - exists x. firstorder.
    - exists x. firstorder. RG_valid_prover (f x).
    - exists x0. firstorder.
    - exists x. firstorder. RG_valid_prover (f x).
Defined.



Definition RG_induce {A B : Type} (f : A -> bool) (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => if f a then rg.(RG_nodes) a else False;
        RG_edges := fun a1 a2 l => if f a1 && f a2 then rg.(RG_edges) a1 a2 l else False;
        RG_valid := _
    |}.
    RG_valid_prover rg; destruct (f a1); destruct (f a2); firstorder.
Defined.



(* Also removes all associated edges *)
Definition RG_removeVertex {A B : Type} (x : A) (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => x <> a /\ rg.(RG_nodes) a;
        RG_edges := fun a1 a2 l => a1 <> x /\ a2 <> x /\ rg.(RG_edges) a1 a2 l;
        RG_valid := _
    |}.
    RG_valid_prover rg.
Defined.

Definition RG_removeEdge {A B : Type} (from to : A) (label : B) (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := rg.(RG_nodes);
        RG_edges := fun a1 a2 l => not (a1 = from /\ a2 = to /\ l = label)
                                    /\ rg.(RG_edges) a1 a2 l;
        RG_valid := _
    |}.
    RG_valid_prover rg.
Defined.








Definition RG_transpose {A B : Type} (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := rg.(RG_nodes);
        RG_edges := fun a1 a2 l => rg.(RG_edges) a2 a1 l;
        RG_valid := _
    |}.
    RG_valid_prover rg.
Defined.

(* Start characterizing paths and search (so far unused) *)

Definition RG_existsPath {A B : Type} (node1 node2 : A) (rg : RG A B) : Prop :=
    clos_trans A (_unlabelEdgeRelation rg.(RG_edges)) node1 node2.

(* Is node reachable from froms in exactly a single step? *)
Definition RG_reachableInOneStep {A B : Type} (froms : Ensemble A) (node : A) (rg : RG A B) : Prop :=
    exists from l, froms from /\ rg.(RG_edges) from node l.



    
(* Start characterizing the order of a BFS (so far unused) *)

(* Recursive helper for  sameDistance. *) 
Inductive sameDistance_rec {A B : Type} (rg : RG A B) : Ensemble A -> A -> Ensemble A -> A -> Prop :=
    | bothInStart (start1 start2 : Ensemble A) : forall (a1 a2 : A), start1 a1 -> start2 a2 -> sameDistance_rec rg start1 a1 start2 a2
    | bothOneStep (start1 start2 : Ensemble A) : forall (a1 a2 : A),
        sameDistance_rec rg (fun x => RG_reachableInOneStep start1 x rg) a1 (fun x => RG_reachableInOneStep start2 x rg) a2
        -> sameDistance_rec rg start1 a1 start2 a2. 

(* Do the nodes have exactly the same distances to the start set?  *) 
Definition sameDistance {A B : Type} (start : Ensemble A) (a1 a2 : A) (rg : RG A B) : Prop :=
    sameDistance_rec rg start a1 start a2.


(* Is the distance from a1 to start one plus the distance from a2 to start? *)
Definition distanceSecondOneLower {A B : Type} (start : Ensemble A) (a1 a2 : A) (rg : RG A B) : Prop :=
    sameDistance_rec rg (fun x => RG_reachableInOneStep start x rg) a1 start a2.



(* Recursive helper for BFS_Order *)
Inductive revBFS_Order {B : Type} (start : NatSet.t) (rg : RG nat B) : list nat -> Prop :=
    | revBFS_Order_start (l : list nat) : Permutation (NatSet.elements start) l -> revBFS_Order start rg l

    | revBFS_Order_same (noww next : nat) (l : list nat) :
        sameDistance (fun x => NatSet.In x start) noww next rg -> revBFS_Order start rg (next :: l) -> revBFS_Order start rg (noww :: next :: l)   

    | revBFS_Order_next (noww next : nat) (l : list nat) :
        distanceSecondOneLower  (fun x => NatSet.In x start) noww next rg 
        -> revBFS_Order start rg (next :: l) -> revBFS_Order start rg (noww :: next :: l).

(* Is the result list a valid BFS order on the graph, starting from the given start nodes? *)
Definition BFS_Order {B : Type} (startL result : list nat) (rg : RG nat B) :=
    revBFS_Order (NatSet_fromList startL) rg (rev result).

