

(* Require Import MyProject.project.util.NatSet.
Require Import MyProject.project.util.util. *)


Require Import List.
Import ListNotations.

Require Import MyProject.project.util.NatMap.

Print NatMap.

(* SO far, this lives a little bit isolated from the rest, since code for it is not much simpler than for the representations from the paper *)

(* Define decidable RG: *)
Definition _valid_cond {A B : Type} (nodes : NatMap.t A) (edges : PairNatMap.t (list B)) : Prop :=
    forall (a1 a2 : nat) (b : B), PairNatMap.In (a1, a2) edges -> NatMap.In a1 nodes /\ NatMap.In a2 nodes.


(* For it to be decidable, there needs to be some decision procedure on equality of the As
 wait, but if you want to allow for multiple nodes to have the same label, then it would not even be needed  *)
Record RG_dec (A B : Type) := {
    RG_dec_nodes : NatMap.t A;
    (* list is here to implement a bag/multiset *)
    RG_dec_edges : PairNatMap.t (list B);
    RG_dec_valid : _valid_cond RG_dec_nodes RG_dec_edges
}.

Arguments RG_dec_nodes {A B}.
Arguments RG_dec_edges {A B}.
Arguments RG_dec_valid {A B}.


(* Ltac RG_valid_prover := unfold _valid_cond; firstorder.
Ltac RG_valid_prover_with rg := pose proof rg.(RG_valid); RG_valid_prover.
Ltac RG_valid_prover_withs rg1 rg2 := pose proof rg1.(RG_valid); RG_valid_prover_with rg2. *)


(* Two relational graphs are "the same", when their Ensemble and relation are the same *)
Definition RG_dec_equiv {A B : Type} (rg1 rg2 : RG_dec A B) : Prop :=
    (* The first condition is definitely needed, as we can have "singleton" graphs *)
    (NatMap.Equal rg1.(RG_dec_nodes) rg2.(RG_dec_nodes)) 
    /\ (PairNatMap.Equal rg1.(RG_dec_edges) rg2.(RG_dec_edges)) 
.
Notation "g1 === g2" := (RG_dec_equiv g1 g2) (at level 79, right associativity).


Definition RG_dec_unlE (A : Type) := RG_dec A unit.
(* The followign two actually do make sense in this case *)
Definition RG_dec_RG_unlN (B : Type) := RG_dec unit B.
Definition RG_dec_unl := RG_dec unit unit.




(* Defining fundamental Operations on RGs: *)

Definition RG_dec_empty {A B : Type} : RG_dec A B.
Proof.
    refine {|
        RG_dec_nodes := NatMap.empty A;
        RG_dec_edges := PairNatMap.empty (list B);
        RG_dec_valid := _
    |}.
    unfold _valid_cond.
    intros.
    apply PWF.empty_in_iff in H.
    destruct H.
Defined.


Definition RG_dec_isEmpty {A B: Type} (rg : RG_dec A B) : bool :=
    NatMap.is_empty rg.(RG_dec_nodes)
.


(* The following stuff is just copied over from rg undecidable, and not yet adapted *)

(* Definition RG_dec_addNode {A B : Type} (node : A) (rg : RG_dec A B) : RG_dec A B.
Proof.
    refine {|
        RG_dec_nodes := fun a => node = a \/ rg.(RG_dec_nodes) a;
        RG_dec_edges := rg.(RG_dec_edges);
        RG_dec_valid := _
    |}.
    RG_dec_valid_prover_with rg.
Defined. 


Definition RG_dec_addEdge {A B : Type} (from to : A) (label : B) (rg : RG_dec A B) : RG_dec A B.
Proof.
    refine {|
        RG_dec_nodes := fun a => (RG_dec_addNode to (RG_dec_addNode from rg)).(RG_dec_nodes) a;
        RG_dec_edges := fun a1 a2 l =>  (a1 = from /\ a2 = to /\ l = label) \/
                                    rg.(RG_dec_edges) a1 a2 l;
        RG_dec_valid := _
    |}.    
    RG_dec_valid_prover_with rg.
Defined.


(* Also removes all associated edges *)
Definition RG_dec_removeNode {A B : Type} (node : A) (rg : RG_dec A B) : RG_dec A B.
Proof.
    refine {|
        RG_dec_nodes := fun a => node <> a /\ rg.(RG_dec_nodes) a;
        RG_dec_edges := fun a1 a2 l => a1 <> node /\ a2 <> node /\ rg.(RG_dec_edges) a1 a2 l;
        RG_dec_valid := _
    |}.
    RG_dec_valid_prover_with rg.
Defined.


(* Does not remove associated nodes *)
Definition RG_dec_removeEdge {A B : Type} (from to : A) (label : B) (rg : RG_dec A B) : RG_dec A B.
Proof.
    refine {|
        RG_dec_nodes := rg.(RG_dec_nodes);
        RG_dec_edges := fun a1 a2 l =>  not (a1 = from /\ a2 = to /\ l = label) /\
                                    rg.(RG_dec_edges) a1 a2 l;
        RG_dec_valid := _
    |}.
    RG_dec_valid_prover_with rg.
Defined.
 


Definition RG_dec_getOutgoingEdges {A B : Type} (node : A) (rg : RG_dec A B) : _edgeRelation A B :=
    fun (a1 a2 : A) l => rg.(RG_dec_edges) a1 a2 l /\ a1 = node.

Definition RG_dec_getIncomingEdges {A B : Type} (node : A) (rg : RG_dec A B) : _edgeRelation A B :=
    fun (a1 a2 : A) l => rg.(RG_dec_edges) a1 a2 l /\ a2 = node.

Definition RG_dec_getIncidentEdges {A B : Type} (node : A) (rg : RG_dec A B) : _edgeRelation A B :=
    fun (a1 a2 : A) l =>    (RG_dec_getOutgoingEdges node rg) a1 a2 l \/
                            (RG_dec_getIncomingEdges node rg) a1 a2 l.

(* There can also be variations of this, where you the the neighbor nodes and not just edges ... *)



(* Connectedness *)
Definition RG_dec_existsPath {A B : Type} (node1 node2 : A) (rg : RG_dec A B) : Prop :=
    clos_trans A (_unlabelEdgeRelation rg.(RG_dec_edges)) node1 node2.

Start implementing search *)

