Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.

Require Import MyProject.project.util.NatSet.
Require Import MyProject.project.util.util.



(* Defining a Relational Graph and its (possible) operations *)

Definition _edgeRelation (A B: Type) := A -> A -> B -> Prop.

Definition _unlabelEdgeRelation {A B: Type} (edges : _edgeRelation A B) : relation A :=
    fun (a1 a2 : A) => exists (l: B), edges a1 a2 l.



(* Here, I first _temporarily_ define a more powerful RG, which has edge labels. The current RG can be derived from it *)


Definition _valid_cond {A B: Type} (nodes : Ensemble A) (edges : _edgeRelation A B) : Prop :=
    forall (a1 a2 : A) (b : B), edges a1 a2 b -> nodes a1 /\ nodes a2.


Record RG (A B: Type) := {
    RG_nodes : Ensemble A;
    RG_edges : _edgeRelation A B;
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


Definition RG_addNode {A B : Type} (node : A) (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => node = a \/ rg.(RG_nodes) a;
        RG_edges := rg.(RG_edges);
        RG_valid := _
    |}.
    RG_valid_prover_with rg.
Defined. 


Definition RG_addEdge {A B : Type} (from to : A) (label : B) (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => (RG_addNode to (RG_addNode from rg)).(RG_nodes) a;
        RG_edges := fun a1 a2 l =>  (a1 = from /\ a2 = to /\ l = label) \/
                                    rg.(RG_edges) a1 a2 l;
        RG_valid := _
    |}.    
    RG_valid_prover_with rg.
Defined.


(* Also removes all associated edges *)
Definition RG_removeNode {A B : Type} (node : A) (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => node <> a /\ rg.(RG_nodes) a;
        RG_edges := fun a1 a2 l => a1 <> node /\ a2 <> node /\ rg.(RG_edges) a1 a2 l;
        RG_valid := _
    |}.
    RG_valid_prover_with rg.
Defined.


(* Does not remove associated nodes *)
Definition RG_removeEdge {A B : Type} (from to : A) (label : B) (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := rg.(RG_nodes);
        RG_edges := fun a1 a2 l =>  not (a1 = from /\ a2 = to /\ l = label) /\
                                    rg.(RG_edges) a1 a2 l;
        RG_valid := _
    |}.
    RG_valid_prover_with rg.
Defined.
 


Definition RG_getOutgoingEdges {A B : Type} (node : A) (rg : RG A B) : _edgeRelation A B :=
    fun (a1 a2 : A) l => rg.(RG_edges) a1 a2 l /\ a1 = node.

Definition RG_getIncomingEdges {A B : Type} (node : A) (rg : RG A B) : _edgeRelation A B :=
    fun (a1 a2 : A) l => rg.(RG_edges) a1 a2 l /\ a2 = node.

Definition RG_getIncidentEdges {A B : Type} (node : A) (rg : RG A B) : _edgeRelation A B :=
    fun (a1 a2 : A) l =>    (RG_getOutgoingEdges node rg) a1 a2 l \/
                            (RG_getIncomingEdges node rg) a1 a2 l.

(* There can also be variations of this, where you the the neighbor nodes and not just edges ... *)



(* A little exotic, but useful for IGs *)
(* Adds a node and its in- and out- going edges (= its IG context) to an RG.
    Adds the neighbouring nodes, in case they do not exists *)
Definition _extendByContext (node : nat) (froms tos : NatSet.t) (rg : RG_unlE nat) : RG_unlE nat.
Proof.
    refine {|
        RG_nodes := fun (n : nat) => NatSet.In n froms \/ NatSet.In n tos \/ (_customEnsembleAdd node rg.(RG_nodes))  n;
        RG_edges := fun (n1 n2 : nat) l =>
                                (NatSet.In n1 froms /\ n2 = node)
                                \/ (n1 = node /\ NatSet.In n2 tos)
                                \/ rg.(RG_edges) n1 n2 l
                                ;
                     
        RG_valid := _
    |}.
    RG_valid_prover_with rg.
Defined.

(* Connectedness *)
Definition RG_existsPath {A B : Type} (node1 node2 : A) (rg : RG A B) : Prop :=
    clos_trans A (_unlabelEdgeRelation rg.(RG_edges)) node1 node2.

(* Start implementing search *)



