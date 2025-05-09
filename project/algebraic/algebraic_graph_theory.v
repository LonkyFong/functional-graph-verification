Require Import MyProject.project.algebraic.algebraic_graph.
Require Import MyProject.project.relational_graph.


(* Defining Conversion from Algebraic Graph to Record Graph *)
Definition empty_RG {X : Type} : RG X.
Proof.
    exact RG_empty.
Qed.


Definition singleton_RG {X : Type} (x : X) : RG X.
Proof.
    refine {|
        RG_nodes := fun A => x = A;
        RG_edges := fun A B => False;
        RG_valid := _
    |}.
    unfold valid_cond. intros. destruct H.
Defined.


Definition overlay_RG {X : Type} (rg1 rg2 : RG X) : RG X.
Proof.
    refine {|
        RG_nodes := fun A => (rg1.(RG_nodes) A) \/ (rg2.(RG_nodes) A);
        RG_edges := fun A B => (rg1.(RG_edges) A B) \/ (rg2.(RG_edges) A B);
        RG_valid := _
    |}.
    unfold valid_cond. intros. split.
    - destruct H.
        + pose proof rg1.(RG_valid). unfold valid_cond in X0. apply X0 in H. left. apply H.
        + pose proof rg2.(RG_valid). unfold valid_cond in X0. apply X0 in H. right. apply H.
    - destruct H.
        + pose proof rg1.(RG_valid). unfold valid_cond in X0. apply X0 in H. left. apply H.
        + pose proof rg2.(RG_valid). unfold valid_cond in X0. apply X0 in H. right. apply H.
Defined.



Definition connect_RG {X : Type} (rg1 rg2 : RG X) : RG X.
Proof.
    let overlay := constr:(overlay_RG rg1 rg2) in
    refine {|
        RG_nodes := overlay.(RG_nodes);
        RG_edges := fun A B => overlay.(RG_edges) A B \/ (rg1.(RG_nodes) A /\ rg2.(RG_nodes) B);
        RG_valid := _
    |}.
    unfold valid_cond. intros. split.
    - destruct H.
        + pose proof (overlay_RG rg1 rg2).(RG_valid). unfold valid_cond in X0. apply X0 in H. apply H.
        + simpl. left. apply H.
    - destruct H.
        + pose proof (overlay_RG rg1 rg2).(RG_valid). unfold valid_cond in X0. apply X0 in H. apply H.
        + simpl. right. apply H.
Defined.


Fixpoint AG_to_RG {X : Type} (ag : AG X) : RG X :=
match ag with
| Empty => empty_RG
| Vertex x => singleton_RG x
| Overlay ag1 ag2 => overlay_RG (AG_to_RG ag1) (AG_to_RG ag2)
| Connect ag1 ag2 => connect_RG (AG_to_RG ag1) (AG_to_RG ag2)
end.

(* TODO: this coercion may or may not be good to have *)
Coercion AG_to_RG : AG >-> RG.

Definition equiv_AG {X : Type} (ag1 ag2 : AG X) : Prop :=
RG_equiv ag1 ag2.

Notation "g1 A== g2" := (equiv_AG g1 g2) (at level 80).





(* These are the "8 axioms" originally proposed by  functional graphs with class *)

(* +++ is commutative and associative *)
Theorem AG_Overlay_Commutative {X : Type}: forall (x y : AG X), x +++ y A== y +++ x.
Proof.
    intros. unfold RG_equiv. split; split; intros; simpl; simpl in H; destruct H;
    (right; apply H) || (left; apply H).
Qed.

(* TODO: consider making the mega proof a custom tactic (using LTac or probably something more modern) *)
Theorem AG_Overlay_Associative {X : Type}: forall (x y z : AG X), x +++ (y +++ z) A== (x +++ y) +++ z.
Proof.
    unfold RG_equiv. intros. split; split; intros; simpl; simpl in H; repeat (destruct H || destruct H0); auto.
Qed.


(* (G, ***, e) is a monoid *)
Theorem AG_Empty_Connect_L_Identity {X : Type}: forall (g : AG X), Empty *** g A== g.
Proof.
    unfold RG_equiv. intros. split; split; intros; simpl; simpl in H; repeat (destruct H || destruct H0); auto.
Qed.

Theorem AG_Empty_Connect_R_Identity {X : Type}: forall (g : AG X), g *** Empty A== g.
Proof.
    unfold RG_equiv. intros. split; split; intros; simpl; simpl in H; repeat (destruct H || destruct H0); auto.
Qed.

Theorem AG_Connect_Associative {X : Type}: forall (x y z : AG X), x *** (y *** z) A== (x *** y) *** z.
Proof.
    unfold RG_equiv. intros. split; split; intros; simpl; simpl in H; repeat (destruct H || destruct H0); auto.
Qed.


(* *** distributes over +++ *)
Theorem AG_Connect_Overlay_L_Distributes {X : Type}: forall (x y z : AG X), x *** (y +++ z) A== x *** y +++ x *** z.
Proof.
    unfold RG_equiv. intros. split; split; intros; simpl; simpl in H; repeat (destruct H || destruct H0); auto.
Qed.
    


Theorem AG_Connect_Overlay_R_Distributes {X : Type}: forall (x y z : AG X), (x +++ y) *** z A== x *** z +++ y *** z.
Proof.
    unfold RG_equiv. intros. split; split; intros; simpl; simpl in H; repeat (destruct H || destruct H0); auto.
Qed.


(* Decomposition *)
Theorem AG_Connect_Decomposition {X : Type}: forall (x y z : AG X), x *** y *** z A== x *** y +++ x *** z +++ y *** z.
Proof.
    unfold RG_equiv. intros. split; split; intros; simpl; simpl in H; repeat (destruct H || destruct H0); auto.
Qed.



(* Show that AG a are "complete" and "sound"  *)
(* TODO: this is not very urgent right now *)

(* Complete: *)
(* Look at paper *)

(* Sound: *)



(* Section to make rewrite work with equiv_AG *)
(* Source for rewrite: https://stackoverflow.com/questions/56099646/use-rewrite-tactic-with-my-own-operator-in-coq *)
Require Import Setoid Morphisms.

(* This proof is based on === being an equivalence relation *)
Instance AG_Equivalence_eq {X : Type} : Equivalence (@equiv_AG X).
Proof.
    pose proof (@RG_Equivalence_eq X). destruct H. split.
    - unfold Reflexive. intros. unfold Reflexive in Equivalence_Reflexive. apply Equivalence_Reflexive.
    - unfold Symmetric. intros. unfold Symmetric in Equivalence_Symmetric. apply Equivalence_Symmetric. apply H.
    - unfold Transitive. intros. unfold Transitive in Equivalence_Transitive. apply (Equivalence_Transitive x y z).
        + apply H.
        + apply H0.
Qed. 
         



Instance Proper_add {X : Type} : Proper ((@equiv_AG X) ==> equiv_AG ==> equiv_AG) Overlay.
Proof.
    split; split; intros; simpl in *; destruct H1.
    - left. apply H. auto.
    - right. apply H0. auto.
    - left. apply H. auto.
    - right. apply H0. auto.
    - left. apply H. auto.
    - right. apply H0. auto.
    - left. apply H. auto.
    - right. apply H0. auto.
Qed.
    

Instance Proper_mul {X : Type} : Proper ((@equiv_AG X) ==> equiv_AG ==> equiv_AG) Connect.
Proof.
    split; split; intros; simpl in *; destruct H1.
    - left. apply H. auto.
    - right. apply H0. auto.
    - left. apply H. auto.
    - right. apply H0. auto.
    - left. destruct H1.
        + left. apply H. auto.
        + right. apply H0. auto.
    - right. destruct H1. split.
        + apply H. auto.
        + apply H0. auto.
    - left. destruct H1.
        + left. apply H. auto.
        + right. apply H0. auto.
    - right. destruct H1. split.
        + apply H. auto.
        + apply H0. auto.
Qed.    

Theorem AG_equiv_rewrite_test_basic : forall (a b c : AG nat), equiv_AG a b -> equiv_AG b c -> equiv_AG a c.
Proof.
    intros. rewrite H. rewrite H0. reflexivity.
Qed.


Theorem AG_equiv_rewrite_test_advanced : forall (a b c : AG nat), equiv_AG a b -> equiv_AG (b +++ Empty) c -> equiv_AG (a +++ Empty) c.
Proof.
    intros. rewrite H. rewrite H0. reflexivity.
Qed.




(* Theorems that can be made based on the "8 axioms": 
They can all be proven using the mega proof from above, but I should find a way to do it using the axioms *)
(* These proofs are heavily inspired by: http://async.org.uk/tech-reports/NCL-EEE-MICRO-TR-2014-191.pdf *)



(* This is a helper for Identity of + *)
Lemma rdeco {X : Type}: forall (x : AG X), x +++ x +++ Empty A== x.
Proof.
    intros.
    pose proof (AG_Connect_Decomposition x Empty Empty).


    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite <- H.

    reflexivity.
Qed.


(* Identity of + *)
Theorem AG_Empty_Overlay_R_Identity {X : Type}: forall (g : AG X), g +++ Empty A== g.
Proof.
    intros.
    rewrite <- rdeco.

    rewrite <- AG_Overlay_Associative.
    rewrite (AG_Overlay_Associative Empty (g +++ Empty)). 
    rewrite (AG_Overlay_Commutative Empty (g +++ Empty)).
    rewrite <- AG_Overlay_Associative.
    rewrite <- AG_Overlay_Associative.

    rewrite (rdeco).
    rewrite (rdeco).
    reflexivity.
Qed.


(* idempotence of + *)
Theorem AG_Overlay_Idempotence {X : Type}: forall (x : AG X), x +++ x A== x.
Proof.
    intros.
    pose proof rdeco x.
    rewrite AG_Empty_Overlay_R_Identity in H.
    auto.
Qed.



(* Absorption (proof is mine) *)
Theorem AG_Absorption {X : Type}: forall (x y : AG X), x *** y +++ x +++ y A== x *** y.
Proof.
    intros. pose proof AG_Connect_Decomposition x y Empty.
    rewrite (AG_Connect_Associative) in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    symmetry in H.
    auto.
Qed.



(* Saturation (proof is mine) *)
Theorem AG_Saturation {X : Type}: forall (x : AG X), x *** x *** x A== x *** x.
Proof.
    intros.
    rewrite AG_Connect_Decomposition.

    rewrite AG_Overlay_Idempotence.
    rewrite AG_Overlay_Idempotence.
    reflexivity.
Qed.


