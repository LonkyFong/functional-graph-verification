Require Import Lia.

Require Import Arith.

Require Import List.
Import ListNotations.

Require Import Relation_Operators.

Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.NatMap.
Require Import GraphVerification.src.util.util.


Require Import GraphVerification.src.relational.RG.
Require Import GraphVerification.src.relational.RG_theory.

Require Import GraphVerification.src.inductive.IG.
Require Import GraphVerification.src.inductive.IG_wf.
Require Import GraphVerification.src.inductive.IG_theory.
Require Import GraphVerification.src.inductive.IG_wf_operations.
Require Import GraphVerification.src.inductive.IG_to_RG.

(** Stating and proving Lemmas and Theorems about IG functions that *do* use well_founded induction. 
    In particular, transpose and DFS *)


(* "IG_equiv" is an equivalence relation: *)
Instance IG_Equivalence {A B : Type} : Equivalence (@IG_equiv A B).
Proof.
    G_derived_equivalence_prover nat unit (@ IG_to_RG A B).  
Qed.



(* Showing properties about transpose: *)


Lemma _key_In_IG_relates : forall (A B : Type) (node : Node) (ig : IG A B),
    _key_In_IG node ig <-> (IG_to_RG ig).(RG_nodes) node.
Proof.
    intros A B n. setoid_rewrite _key_In_IG_mem_iff.
    apply (well_founded_induction (well_founded_ltof _ (@IG_noNodes A B))).
    intros ig IH. unfold IG_to_RG.
    rewrite IG_ufold_rec_equation.
    destruct (IG_matchAny ig) eqn:mat.
    destruct m.
    - specialize (IH i).
        apply _IG_matchAny_decreases_IG_noNodes in mat as mat'.
        specialize (IH mat'). clear mat'.
        destruct_context c. simpl. unfold Ensemble_add. 
        unfold IG_matchAny in mat. destruct (IG_labNodes ig).
        + inversion mat.
        + destruct l. simpl in *. apply IG_match_returns_node in mat as mat'. subst.
            rewrite <- MFacts.mem_in_iff.

            bdestruct (n =? node).
            (* same *)
            -- clear IH. subst. assert (NatMap.In node ig). {
                    apply NatMap_In_exists_MapsTo_iff.
                    apply (IG_match_exactly_removes_node _ _ _ _ _ _ (node, label)) in mat as mat'.
                    simpl in *.
                    rewrite _In_labNodes_is_some_MapsTo in mat'.
                    assert ((node, label) = (node, label) /\ ~ _key_In_IG node i \/ In (node, label) (IG_labNodes i)). {
                        apply (IG_match_removes_node _ _ node) in mat.
                        left. auto. 
                    }
                    apply mat' in H.
                    destruct_eMapsTo H.
                    exists (efroms, label, etos).
                    assumption.
                } clear mat. split; intros.
                ++ left. reflexivity.
                ++ assumption.
        
            -- rewrite <- IH. clear IH.
                rewrite <- !MFacts.mem_in_iff.
                rewrite !NatMap_In_exists_MapsTo_iff.
                firstorder.

                ++ right. destruct_context' x.
                    apply (IG_match_exactly_removes_node _ _ _ _ _ _ (n, label')) in mat.
                    rewrite !_In_labNodes_is_some_MapsTo in mat.
                    assert (exists froms tos : Adj B, NatMap.MapsTo n (froms, label', tos) ig). {
                        exists froms', tos'. assumption. 
                    }
                    apply mat in H1. destruct H1.
                    --- destruct H1. inversion H1. rewrite H4 in H. firstorder.
                    --- destruct_eMapsTo H1. firstorder.
                ++ destruct_context' x. 
                    apply (IG_match_exactly_removes_node _ _ _ _ _ _ (n, label')) in mat.
                    rewrite !_In_labNodes_is_some_MapsTo in mat.
                    assert ((n, label') = (node, label) /\ ~ _key_In_IG (fst (n, label')) i \/ exists froms tos : Adj B, NatMap.MapsTo n (froms, label', tos) i). {
                        right. firstorder. 
                    }
                    apply mat in H1. destruct_eMapsTo H1. firstorder.
    - simpl. apply IG_matchAny_None_is_empty in mat. 
        apply NatMap_is_empty_Equal_empty_iff in mat.
        rewrite mat.
        compute.
        clear. firstorder. inversion H.
Qed.

Lemma IG_and_relates_for_nodes : forall (A B : Type) (ig : IG A B) (c : Context A B) n,
    (c &R (IG_to_RG ig)).(RG_nodes) n
        <-> (IG_to_RG (c &I ig)).(RG_nodes) n.
Proof.
    intros.
    rewrite <- _key_In_IG_relates.
    pose proof (IG_and_adds_key _ _ c).

    destruct_context c.
    rewrite H. clear H.
    simpl.
    unfold Ensemble_add.
    rewrite _key_In_IG_relates.
    reflexivity.
Qed.

(* This would be good to prove for completion, but there is the issue that as is stands,
    &I and &R behave slightly differently with respect to edges.
    &I may insert "phantom" edges, but &R cannot since RG has _valid_cond *)
Lemma IG_and_relates_for_edges : forall (A B : Type) (ig : IG A B) (c : Context A B) e,
    let '(from, to, l) := e in
    (c &R (IG_to_RG ig)).(RG_edges) from to l
        <-> (IG_to_RG (c &I ig)).(RG_edges) from to l.
Proof.
Admitted.


(* Warning: This depends on unproven IG_and_relates_for_edges *)
Lemma IG_and_relates : forall {A B : Type} (c : Context A B) (ig : IG A B),
    IG_to_RG (c &I ig) ==R c &R (IG_to_RG ig). 
Proof.
    intros. unfold RG_equiv. split.
    - intros. rewrite IG_and_relates_for_nodes. reflexivity.
    - intros. rewrite (IG_and_relates_for_edges _ _ _ _ (a1, a2, b)). reflexivity.
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


(* Warning: This depends on unproven IG_and_relates_for_edges *)
Theorem IG_transpose_relates : forall (A B : Type) (ig : IG A B),
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
        rewrite IG_and_relates.
        rewrite -> IH.
        reflexivity.

    - clear mat IH. unfold IG_to_RG. rewrite IG_ufold_rec_equation. simpl. firstorder. 
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
            



(* Only reachable and all reachable nodes are included *)
Theorem IG_DFS_path : forall (A B : Type) (igNodes : list NatSet.Node * IG A B) x,
    let '(nodes, ig) := igNodes in
    In x (IG_DFS nodes ig)
        <-> exists y, In y nodes /\ RG_existsPath y x (IG_to_RG ig).
Proof.
    intros. destruct igNodes as [ig nodes].
Admitted.