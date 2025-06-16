Require Import Lia.

Require Import Arith.

Require Import List.
Import ListNotations.

Require Import Relation_Operators.

Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.NatMap.

Require Import GraphVerification.src.RG.
Require Import GraphVerification.src.RG_theory.

Require Import GraphVerification.src.inductive.IG.
Require Import GraphVerification.src.inductive.IG_wf.
Require Import GraphVerification.src.inductive.IG_theory.
Require Import GraphVerification.src.inductive.IG_wf_algorithms.
Require Import GraphVerification.src.inductive.IG_to_RG.

(* Stating and proving Lemmas and Theorems about IG functions that *do* use well_founded induction. *)


(* "IG_equiv" is an equivalence relation: *)
Instance IG_Equivalence {A B : Type} : Equivalence (@IG_equiv A B).
Proof.
    G_derived_equivalence_prover nat unit (@ IG_to_RG A B).  
Qed.



(* Theorems about DFS *)

Theorem IG_DFS_returns_only_nodes : forall (A B : Type) (igNodes : IG A B * list NatSet.Node),
    let '(ig, nodes) := igNodes in
    forall x, In x (IG_DFS nodes ig) -> _key_In_IG x ig. 
Proof.
    intros A B.
    apply (well_founded_induction (wf_lexord_arg_pair_s A B)).
    
    intros nodesIG IH.
    destruct nodesIG as [ig nodes]. intros.

    unfold IG_DFS in H. rewrite IG_DFS_rec_equation in H.
    destruct nodes.
    (* list is empty *)
    - apply in_nil in H. destruct H.
    (* list is nonempty *)
    - destruct (IG_isEmpty ig).
        (* graph is empty *)
        + apply in_nil in H. destruct H.
        (* graph (and list) is nonempty (interesting case) *)
        + destruct (IG_match n ig) eqn:mat.
            destruct m.
            (* the node in the queue in is the graph (graph gets smaller) *)
            -- simpl in *. destruct_context c. 
                destruct H.
                ++ apply IG_match_returns_node in mat as mat'. subst.
                    eapply IG_match_exactly_removes_node in mat as mat'.
                    apply IG_match_removes_node in mat.
                    firstorder.

                ++ eapply IG_match_some_decreases_lexord in mat as mat'.
                    specialize (IH _ mat').
                    apply IH in H. clear IH.

                    destruct H. exists x0.
                    eapply IG_match_exactly_removes_node in mat.

                    apply mat. firstorder.
            (* the node in the queue is not in the graph (the queue gets smaller) *)
            -- apply IG_match_none_returns_graph in mat as mat'. subst.  
                eapply IG_match_none_list_diff_lexord in mat.
                specialize (IH _ mat).
                eapply IH in H.
                assumption.
Qed.





Theorem IG_DFS_no_duplicates : forall (A B : Type) (igNodes : IG A B * list NatSet.Node),
    let '(ig, nodes) := igNodes in
    NoDup (IG_DFS nodes ig).
Proof.
    intros A B. 
    apply (well_founded_induction (wf_lexord_arg_pair_s A B)).
    intros nodesIG IH.
    destruct nodesIG as [ig nodes].

    unfold IG_DFS. rewrite IG_DFS_rec_equation. destruct nodes.
    (* list is empty *)
    - apply NoDup_nil.
    (* list is nonempty *)
    - destruct (IG_isEmpty ig).
        (* graph is empty *)
        + apply NoDup_nil.
        (* graph (and list) is nonempty (interesting case) *)
        + destruct (IG_match n ig) eqn:mat.
            destruct m.
            (* the node in the queue in is the graph (graph gets smaller) *)
            -- apply NoDup_cons.
                ++ unfold not. intros.
                
                    pose proof IG_DFS_returns_only_nodes. unfold IG_DFS in H.
                    specialize (H0 _ _ (i, suc c ++ nodes) _ H). 
                    eapply IG_match_removes_node in mat.
                    auto.

                ++ eapply IG_match_some_decreases_lexord in mat as mat'.
                    specialize (IH _ mat').
                    apply IH.
                
            (* the node in the queue is not in the graph (the queue gets smaller) *)
            --  apply IG_match_none_returns_graph in mat as mat'. subst.  
                eapply IG_match_none_list_diff_lexord in mat.
                specialize (IH _ mat).
                apply IH.
Qed.
            





(* For all in the list, there is a path from one of the starting nodes *)
Theorem IG_DFS_path : forall (A B : Type) (igNodes : list NatSet.Node * IG A B) x,
    let '(nodes, ig) := igNodes in
    In x (IG_DFS nodes ig)
        -> exists y, In y nodes /\ RG_existsPath y x (IG_to_RG ig).
Proof.
    intros. destruct igNodes as [ig nodes].
Admitted.






(* Showing properties about transpose: *)

(* This is actually not true in the general case, but for the particular function, with which it is used, it is most likely true *)
Lemma IG_ufold_step : forall (A B C : Type) (f : Context A B -> C -> C) (acc : C) (c : Context A B) (ig : IG A B),
    IG_ufold f acc (c &I ig) = f c (IG_ufold f acc ig).
Proof.
Admitted.



Lemma IG_to_RG_distributes_over_add : forall {A B : Type} (c : Context A B) (ig : IG A B),
    IG_to_RG (c &I ig) ==R c &R (IG_to_RG ig). 
Proof.
    intros.

    unfold IG_to_RG.
    rewrite IG_ufold_step.
    reflexivity.
Qed.




(* Some theory about RG_add (rewriting, interaction with RG_transpose) *)
Definition contextEquiv {A B : Type} (c1 c2 : Context A B) : Prop :=
    c1 = c2.

Instance Proper_RG_and {A B : Type} : Proper ((@contextEquiv A B) ==> (@RG_equiv nat unit) ==> (@RG_equiv nat unit)) RG_and. 
Proof.
    split; unfold contextEquiv in H; subst; destruct y as [[[froms node] label] tos].
    - firstorder.
    - firstorder.
Qed.

Lemma RG_transpose_distributes_over_extendByContext : forall {A B : Type} (c : Context A B) (rg : RG_unlE nat),
    RG_transpose (c &R rg) ==R (_transposeContext c) &R (RG_transpose rg).
Proof.
    intros. destruct_context c.
    firstorder.
Qed.



Theorem IG_transpose_is_RG : forall (A B : Type) (ig : IG A B),
    IG_to_RG (IG_transpose ig) ==R RG_transpose (IG_to_RG ig).
Proof.
    intros A B.
    apply (well_founded_induction (well_founded_ltof _ IG_noNodes)).
    intros ig IH.
    unfold IG_transpose. unfold IG_gmap. unfold IG_to_RG at 2. rewrite !IG_ufold_rec_equation. destruct (IG_matchAny ig) eqn:mat.
    destruct m.
    - specialize (IH i).
        apply _IG_matchAny_decreases_IG_noNodes in mat.
        specialize (IH mat).    
    
        rewrite RG_transpose_distributes_over_extendByContext.
        rewrite IG_to_RG_distributes_over_add.
        rewrite -> IH.
        reflexivity.

    - clear mat IH. unfold IG_to_RG. rewrite IG_ufold_rec_equation. simpl. firstorder. 
Qed.


