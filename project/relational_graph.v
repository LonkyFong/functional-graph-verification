Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.

Require Import MyProject.project.util.NatSet.
Require Import MyProject.project.util.util.



(* Defining a Relational Graph and its (possible) operations *)


Definition _valid_cond {A : Type} (nodes : Ensemble A) (edges : relation A) : Prop :=
    forall (a1 a2 : A), edges a1 a2 -> nodes a1 /\ nodes a2.


Record RG (A : Type) := {
    RG_nodes : Ensemble A;
    RG_edges : relation A;
    RG_valid : _valid_cond RG_nodes RG_edges
}.

Arguments RG_nodes {A}.
Arguments RG_edges {A}.
Arguments RG_valid {A}.

Ltac RG_valid_prover := unfold _valid_cond; firstorder.
Ltac RG_valid_prover_with rg := pose proof rg.(RG_valid); RG_valid_prover.
Ltac RG_valid_prover_withs rg1 rg2 := pose proof rg1.(RG_valid); RG_valid_prover_with rg2.


(* Two record graphs are "the same", when their Ensemble and relation are the same *)
Definition RG_equiv {A : Type} (rg1 rg2 : RG A) : Prop :=
    (* The first condition is definitely needed, as we can have "singleton" graphs *)
    (forall (a : A), rg1.(RG_nodes) a <-> rg2.(RG_nodes) a)
    /\ (forall (a1 a2 : A), rg1.(RG_edges) a1 a2 <-> rg2.(RG_edges) a1 a2)
.
Notation "g1 === g2" := (RG_equiv g1 g2) (at level 100, right associativity).



(* Defining Basic Operations on RGs: *)

Definition RG_empty {A : Type} : RG A.
Proof.
    refine {|
        RG_nodes := fun A => False;
        RG_edges := fun A B => False;
        RG_valid := _
    |}.
    RG_valid_prover.
Defined.

Definition RG_isEmpty {A : Type} (rg : RG A) : Prop :=
    forall (a : A), rg.(RG_nodes) a = False
.

Definition RG_addNode {A : Type} (node : A) (rg : RG A) : RG A.
Proof.
    refine {|
        RG_nodes := fun a => node = a \/ rg.(RG_nodes) a;
        RG_edges := rg.(RG_edges);
        RG_valid := _
    |}.
    RG_valid_prover_with rg.
Defined. 


Definition RG_addEdge {A : Type} (from to : A) (rg : RG A) : RG A.
Proof.
    refine {|
        RG_nodes := fun a => (RG_addNode to (RG_addNode from rg)).(RG_nodes) a;
        RG_edges := fun a1 a2 => (a1 = from /\ a2 = to) \/ rg.(RG_edges) a1 a2;
        RG_valid := _
    |}.    
    RG_valid_prover_with rg.
Defined.


(* Also removes all associated edges *)
Definition RG_removeNode {A : Type} (node : A) (rg : RG A) : RG A.
Proof.
    refine {|
        RG_nodes := fun a => node <> a /\ rg.(RG_nodes) a;
        RG_edges := fun a1 a2 => node <> a1 /\ node <> a2 /\ rg.(RG_edges) a1 a2;
        RG_valid := _
    |}.
    RG_valid_prover_with rg.
Defined.


(* Does not remove associated nodes *)
Definition RG_removeEdge {A : Type} (from to : A) (rg : RG A) : RG A.
Proof.
    refine {|
        RG_nodes := rg.(RG_nodes);
        RG_edges := fun a1 a2 => from <> a1 /\ to <> a2 /\ rg.(RG_edges) a1 a2;
        RG_valid := _
    |}.
    RG_valid_prover_with rg.
Defined.
 


Definition RG_getOutgoingEdges {A : Type} (node : A) (rg : RG A) : relation A :=
    fun (a1 a2 : A) => rg.(RG_edges) a1 a2 /\ a1 = node.

Definition RG_getIncomingEdges {A : Type} (node : A) (rg : RG A) : relation A :=
    fun (a1 a2 : A) => rg.(RG_edges) a1 a2 /\ a2 = node.

Definition RG_getIncidentEdges {A : Type} (node : A) (rg : RG A) : relation A :=
    fun (a1 a2 : A) => (RG_getOutgoingEdges node rg) a1 a2 \/ (RG_getIncomingEdges node rg) a1 a2.

(* There can also be variations of this, where you the the neighbor nodes and not just edges ... *)



(* A little exotic, but useful for IGs *)
(* Adds a node and its in- and out- going edges (= its IG context) to an RG.
    Adds the neighbouring nodes, in case they do not exists *)
Definition _extendByContext (node : nat) (froms tos : NatSet.t) (rg : RG nat) : RG nat.
Proof.
    refine {|
        RG_nodes := fun (n : nat) => NatSet.In n froms \/ NatSet.In n tos \/ (_customEnsembleAdd node rg.(RG_nodes))  n;
        RG_edges := fun (n1 n2 : nat) =>
                                (NatSet.In n1 froms /\ n2 = node)
                                \/ (n1 = node /\ NatSet.In n2 tos)
                                \/ rg.(RG_edges) n1 n2
                                ;
                     
        RG_valid := _
    |}.
    RG_valid_prover_with rg.
Defined.

(* Connectedness *)
Definition RG_existsPath {A : Type} (node1 node2 : A) (rg : RG A) : Prop :=
    clos_trans A rg.(RG_edges) node1 node2.

(* Start implementing search *)



