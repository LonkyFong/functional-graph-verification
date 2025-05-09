Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.

(* Defining a Relational Graph *)


Definition valid_cond {t : Type} (nodes : Ensemble t) (rel : relation t) : Type :=
    forall (x y : t), rel x y -> nodes x /\ nodes y.

Record RG (t : Type) := {
    RG_nodes : Ensemble t;
    RG_edges : relation t;
    RG_valid : valid_cond RG_nodes RG_edges
}.

Arguments RG_nodes {t}.
Arguments RG_edges {t}.
Arguments RG_valid {t}.


(* Two record graphs are "the same", when their Ensemble and relation are the same *)
Definition RG_equiv {A : Type} (rg1 rg2 : RG A) : Prop :=
    (* The first condition is definitely needed, as we can have "singleton" graphs *)
    (forall (x : A), rg1.(RG_nodes) x <-> rg2.(RG_nodes) x)
    /\ (forall (x y : A), rg1.(RG_edges) x y <-> rg2.(RG_edges) x y)
.
Notation "g1 === g2" := (RG_equiv g1 g2) (at level 100, right associativity).



(* "RG_equiv" is an equivalence relation: *)
(* Reflexive *)
Theorem RG_RG_equiv_Reflexive {A : Type}: forall (x : RG A), RG_equiv x x .
Proof.
    unfold RG_equiv. intros. split; split; auto.
Qed.
    

(* Symmetric *)
Theorem RG_RG_equiv_Symmetric {A : Type}: forall (x y : RG A), RG_equiv x y <-> RG_equiv y x.
Proof.
    split; split; split; unfold RG_equiv in H; apply H.
Qed. 

(* Transitive *)
Theorem RG_RG_equiv_Transitive {A : Type}: forall (x y z : RG A), RG_equiv x y -> RG_equiv y z -> RG_equiv x z.
Proof.
    split; split; intros; unfold RG_equiv in H; unfold RG_equiv in H0.
    - apply H0. apply H. apply H1.
    - apply H. apply H0. apply H1.
    - apply H0. apply H. apply H1.
    - apply H. apply H0. apply H1.
Qed.

(* Section to make rewrite work with equiv_RG *)

(* Source for rewrite: https://stackoverflow.com/questions/56099646/use-rewrite-tactic-with-my-own-operator-in-coq *)
Require Import Setoid Morphisms.
Instance RG_Equivalence_eq {A : Type} : Equivalence (@RG_equiv A).
Proof.
    unfold RG_equiv. split.
    - unfold Reflexive. intros. pose proof (@RG_RG_equiv_Reflexive A). apply H.
    - unfold Symmetric. intros. pose proof (@RG_RG_equiv_Symmetric A). apply H0. apply H.
    - unfold Transitive. intros. pose proof (@RG_RG_equiv_Transitive A). apply (H1 x y).
        + apply H.
        + apply H0.
Qed.

(* Defining Operations on RGs: *)

Definition RG_empty {A : Type} : RG A.
Proof.
    refine {|
        RG_nodes := fun A => False;
        RG_edges := fun A B => False;
        RG_valid := _
    |}.
    unfold valid_cond. intros. destruct H.
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
    unfold valid_cond. intros. split.
    - pose proof rg.(RG_valid). unfold valid_cond in X. apply X in H. right. apply H.
    - pose proof rg.(RG_valid). unfold valid_cond in X. apply X in H. right. apply H.
Defined.

Definition RG_addEdge {A : Type} (from to : A) (rg : RG A) : RG A.
Proof.
    refine {|
        RG_nodes := fun a => (RG_addNode to (RG_addNode from rg)).(RG_nodes) a;
        RG_edges := fun a1 a2 => (a1 = from /\ a2 = to) \/ rg.(RG_edges) a1 a2;
        RG_valid := _
    |}.    
    unfold valid_cond. simpl. intros. split.
    - destruct H.
        + right. left. destruct H. auto.
        + right. right. pose proof rg.(RG_valid). unfold valid_cond in X. apply X in H. apply H.
    - destruct H.
        + left. destruct H. auto.
        + right. right. pose proof rg.(RG_valid). unfold valid_cond in X. apply X in H. apply H.
Qed.

(* Also removes all associated edges *)
Definition RG_removeNode {A : Type} (node : A) (rg : RG A) : RG A.
Proof.
    refine {|
        RG_nodes := fun a => node <> a /\ rg.(RG_nodes) a;
        RG_edges := fun a1 a2 => node <> a1 /\ node <> a2 /\ rg.(RG_edges) a1 a2;
        RG_valid := _
    |}.    
    unfold valid_cond. intros. split.
    - split.
        + apply H.
        + destruct H as [? [? ?]]. pose proof rg.(RG_valid). unfold valid_cond in X. apply X in H1. apply H1.
    - split.
        + apply H.
        + destruct H as [? [? ?]]. pose proof rg.(RG_valid). unfold valid_cond in X. apply X in H1. apply H1.
Qed.


(* Does not remove associated nodes *)
Definition RG_removeEdge {A : Type} (from to : A) (rg : RG A) : RG A.
Proof.
    refine {|
        RG_nodes := rg.(RG_nodes);
        RG_edges := fun a1 a2 => from <> a1 /\ to <> a2 /\ rg.(RG_edges) a1 a2;
        RG_valid := _
    |}.    
    unfold valid_cond. intros. destruct H as [? [? ?]]. split.
    - pose proof rg.(RG_valid). unfold valid_cond in X. apply X in H1. apply H1.
    - pose proof rg.(RG_valid). unfold valid_cond in X. apply X in H1. apply H1.
Qed.



Definition RG_getOutgoingEdges {A : Type} (node : A) (rg : RG A) : relation A :=
    fun (a1 a2 : A) => rg.(RG_edges) a1 a2 /\ a1 = node.

Definition RG_getIncomingEdges {A : Type} (node : A) (rg : RG A) : relation A :=
    fun (a1 a2 : A) => rg.(RG_edges) a1 a2 /\ a2 = node.

Definition RG_getIncidentEdges {A : Type} (node : A) (rg : RG A) : relation A :=
    fun (a1 a2 : A) => (RG_getOutgoingEdges node rg) a1 a2 \/ (RG_getIncomingEdges node rg) a1 a2.

(* There can also be variations of this, where you the the neighbor nodes and not just edges ... *)

Require Import Coq.Relations.Relation_Operators.
Definition RG_existsPath {A : Type} (node1 node2 : A) (rg : RG A) : Prop :=
    clos_trans A rg.(RG_edges) node1 node2.


(* Start implementing search *)

