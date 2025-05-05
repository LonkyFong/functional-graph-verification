Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.
(* Defining a Relational Graph *)

Print relation.

(* Definition Powerset : Type -> Type :=
    fun X => X -> Prop. *)

Definition my_Finite_Type : (Ensemble nat) := 
    fun X => (X = 0) \/ (X = 1) .

    
Definition valid_cond {t : Type} (nodes : Ensemble t) (rel : relation t) : Type :=
    forall (x y : t), rel x y -> nodes x /\ nodes y.

Record RG (t : Type) := {
    gr_nodes : Ensemble t;
    gr_edges : relation t;
    gr_valid : valid_cond gr_nodes gr_edges
}.

Arguments gr_nodes {t}.
Arguments gr_edges {t}.
Arguments gr_valid {t}.


Definition my_Basic_Graph : RG nat.
Proof.
  refine ({|
    gr_nodes := my_Finite_Type;
    gr_edges := (fun (A B : nat) => (A = 0) /\ (B = 1));
    gr_valid := _
  |}).
  unfold valid_cond. intros. split; unfold my_Finite_Type.
  - left. apply H.
  - right. apply H.
Defined.


Print my_Basic_Graph.

Compute my_Basic_Graph.(gr_nodes).
Compute my_Basic_Graph.(gr_edges).


(* Two record graphs are "the same", when their Ensemble and relation are the same *)
Definition equiv_G {X : Type} (rg1 rg2 : RG X) : Prop :=
(* The first condition is definitely needed, as we can have "singleton" graphs *)
(forall (x : X), rg1.(gr_nodes) x <-> rg2.(gr_nodes) x)
/\ (forall (x y : X), rg1.(gr_edges) x y <-> rg2.(gr_edges) x y)
.
Notation "g1 === g2" := (equiv_G g1 g2) (at level 100, right associativity).



(* "equiv_G" is an equivalence relation: *)
(* Reflexive *)
Theorem RG_equiv_G_Reflexive {X : Type}: forall (x : RG X), equiv_G x x .
Proof.
    unfold equiv_G. intros. split; split; auto.
Qed.
    

(* Symmetric *)
Theorem RG_equiv_G_Symmetric {X : Type}: forall (x y : RG X), equiv_G x y <-> equiv_G y x.
Proof.
    split; split; split; unfold equiv_G in H; apply H.
Qed. 

(* Transitive *)
Theorem RG_equiv_G_Transitive {X : Type}: forall (x y z : RG X), equiv_G x y -> equiv_G y z -> equiv_G x z.
Proof.
    split; split; intros; unfold equiv_G in H; unfold equiv_G in H0.
    - apply H0. apply H. apply H1.
    - apply H. apply H0. apply H1.
    - apply H0. apply H. apply H1.
    - apply H. apply H0. apply H1.
Qed.

(* Section to make rewrite work with equiv_RG *)

(* Source for rewrite: https://stackoverflow.com/questions/56099646/use-rewrite-tactic-with-my-own-operator-in-coq *)
Require Import Setoid Morphisms.
Instance RG_Equivalence_eq {X : Type} : Equivalence (@equiv_G X).
Proof.
    unfold equiv_G. split.
    - unfold Reflexive. intros. pose proof (@RG_equiv_G_Reflexive X). apply H.
    - unfold Symmetric. intros. pose proof (@RG_equiv_G_Symmetric X). apply H0. apply H.
    - unfold Transitive. intros. pose proof (@RG_equiv_G_Transitive X). apply (H1 x y).
        + apply H.
        + apply H0.
Qed.


