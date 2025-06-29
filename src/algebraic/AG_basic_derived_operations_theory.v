Require Import Setoid Morphisms.
Require Import Ensembles.

Require Import List.
Import ListNotations.
Require Import Permutation.
Require Import Arith.
Require Import Lia.
Require Import Bool.

Require Import GraphVerification.src.util.util.

Require Import GraphVerification.src.relational.RG.
Require Import GraphVerification.src.relational.RG_theory.

Require Import GraphVerification.src.algebraic.AG.
Require Import GraphVerification.src.algebraic.AG_to_RG.

Require Import GraphVerification.src.algebraic.AG_algebra_theory.

Open Scope bool.


(** Stating and proving Lemmas and Theorems about functions which are
    defined using the primitive operations of an AG using a model-based approach
    Notably: Relating AG_transpose
*)





Lemma AG_vertices_relates : forall (A : Type) (l : list A),
    AG_to_RG (AG_vertices l) ==R RG_vertices l.
Proof.
    intros. induction l.
    - firstorder.
    - simpl in *. firstorder.
Qed.



Lemma AG_edge_relates : forall (A : Type) (a1 a2 : A),
    AG_to_RG (AG_edge a1 a2) ==R RG_edge a1 a2 tt.
Proof.
    intros. firstorder; simpl; subst; firstorder.
    destruct b. reflexivity.
Qed.




(* Showing that one can rewrite in expressions with RG_overlay and RG_connect when there is ==R *)
Instance Proper_overlay {A : Type} : Proper ((@RG_equiv A unit) ==> RG_equiv ==> RG_equiv) RG_overlay.
Proof.
    Proper_proof_automation.
Qed.

Instance Proper_connect {A : Type} : Proper ((@RG_equiv A unit) ==> RG_equiv ==> RG_equiv) RG_connect. 
Proof.
    Proper_proof_automation.
Qed.

Lemma AG_edges_relates : forall (A : Type) (l : list (A * A)),
    AG_to_RG (AG_edges l) ==R RG_edgez (map (fun '(x, y) => (x, y, tt)) l).
Proof.
    intros. induction l.
    - firstorder. 
    - destruct a. simpl. rewrite IHl. clear. firstorder; inversion H; simpl in *; firstorder.
        + exists a0, tt. firstorder.
        + exists a, tt. firstorder.
        + subst. destruct b. firstorder.
Qed.





Lemma AG_makeGraph_relates : forall (A : Type) (vs : list A) (es : list (A * A)),
    AG_to_RG (AG_makeGraph vs es) ==R RG_makeGraph vs (map (fun '(x, y) => (x, y, tt)) es).
Proof.
    intros. unfold AG_makeGraph.
    unfold RG_makeGraph.
    rewrite <- AG_vertices_relates.
    rewrite <- AG_edges_relates.
    reflexivity.
Qed.
    

(* AG_transpose relates to RG_transpose *)
Theorem AG_transpose_relates : forall (ag : AG nat),
    AG_to_RG (AG_transpose ag) ==R RG_transpose (AG_to_RG ag). 
Proof.
    intros. induction ag; simpl; firstorder.
Qed.
    


Lemma AG_toList_relates : forall (A : Type) (ag : AG A),
    forall x, In x (AG_toList ag) <-> RG_toList (AG_to_RG ag) x. 
Proof.
    intros. induction ag; simpl.
    - firstorder.
    - firstorder.
    - rewrite <- IHag1. rewrite <- IHag2. clear. rewrite in_app_iff. firstorder.
    - rewrite <- IHag1. rewrite <- IHag2. clear. rewrite in_app_iff. firstorder.
Qed.



Lemma AG_gmap_relates : forall (A A' : Type) (f : A -> A') (ag : AG A),
    AG_to_RG (AG_gmap f ag) ==R RG_gmap f (AG_to_RG ag).
Proof.
    intros. induction ag.
    - firstorder.
    - compute. firstorder. subst. reflexivity.
    - simpl. rewrite IHag1. rewrite IHag2. clear. firstorder.
    - simpl. rewrite IHag1. rewrite IHag2. clear. firstorder.
Qed.



Lemma AG_mergeVertices_relates : forall (A : Type) (f : A -> bool) (v : A) (ag : AG A),
    AG_to_RG (AG_mergeVertices f v ag) ==R RG_mergeVertices f v (AG_to_RG ag).
Proof.
    intros. unfold AG_mergeVertices. rewrite AG_gmap_relates. reflexivity.
Qed.



Lemma AG_bind_relates : forall (A A' : Type) (f : A -> AG A') (ag : AG A),
    AG_to_RG (AG_bind f ag) ==R RG_bind (fun a => AG_to_RG (f a)) (AG_to_RG ag).
Proof.
    intros. induction ag; simpl.
    - firstorder.
    - firstorder; simpl in H; subst; firstorder. 
    - rewrite IHag1. rewrite IHag2. clear. firstorder.
    - rewrite IHag1. rewrite IHag2. clear. firstorder.
Qed.



Lemma AG_induce_relates : forall (A : Type) (f : A -> bool) (ag : AG A),
    AG_to_RG (AG_induce f ag) ==R RG_induce f (AG_to_RG ag).
Proof.
    intros. unfold AG_induce. rewrite AG_bind_relates. firstorder; simpl in *;
        try (destruct (f a) eqn:fres);
        try (destruct (f x) eqn:fres0);
        try (destruct (f a1) eqn:fres1);
        try (destruct (f a2) eqn:fres2);
        try (destruct (f x0) eqn:fres4); simpl in *; subst; firstorder; try congruence.
    - exists a. rewrite fres. firstorder.
    - left. exists a1, a2. rewrite fres1. rewrite fres2. firstorder.
Qed.




Lemma AG_removeVertex_relates : forall (ag : AG nat) (x : nat),
    AG_to_RG (AG_removeVertex x ag) ==R RG_removeVertex x (AG_to_RG ag).
Proof.
    intros. unfold AG_removeVertex. rewrite AG_induce_relates. firstorder; simpl in *;
        try (bdestruct (x =? a)); try (bdestruct (x =? a1); bdestruct (x =? a2)); subst; firstorder.
Qed.




Ltac AG_removeEdge_relates_prover := firstorder; try ((bdall_in_hyp; firstorder); try (simpl in *; subst; firstorder) ).


(* This is quite a big achievement since AG_removeEdge is very exotically implemented *)
Lemma AG_removeEdge_relates : forall (ag : AG nat) (x y : nat),
    AG_to_RG (AG_removeEdge x y ag) ==R RG_removeEdge x y tt (AG_to_RG ag).
Proof.
    intros. induction ag.
    - firstorder.
    - firstorder.
    - simpl. rewrite IHag1. rewrite IHag2. clear. firstorder.
    - simpl. rewrite IHag1. rewrite IHag2. clear. rewrite !AG_removeVertex_relates.
        AG_removeEdge_relates_prover.
        destruct b. simpl. bdestruct (a1 =? x).
        + subst. bdestruct (a2 =? y).
            -- subst. firstorder.
            -- firstorder.
        + left. right. firstorder.
Qed.

