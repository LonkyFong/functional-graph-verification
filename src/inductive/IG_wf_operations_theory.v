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


(* TODO: apply this *)
(* Lemma mergesort_sorts: forall l, sorted (mergesort l).
Proof.
  apply mergesort_ind; intros. *)

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
    unfold IG_to_RG. unfold IG_ufold.
    apply (IG_ufold_rec_ind _ _ _ _ _ (fun ig acc => NatMap.mem n ig = true <-> RG_nodes acc n)).
    - intros. rename e into mat. destruct_context c. simpl. unfold Ensemble_add. 
        unfold IG_matchAny in mat. destruct (IG_labNodes ig).
        + inversion mat.
        + destruct l. simpl in *. apply IG_match_returns_node in mat as mat'. subst.
            rewrite <- MFacts.mem_in_iff.

            bdestruct (n =? node).
            (* same *)
            -- subst. assert (NatMap.In node ig). {
                    apply NatMap_In_exists_MapsTo_iff.
                    apply (IG_match_exactly_removes_node _ _ _ _ _ _ (node, label)) in mat as mat'.
                    simpl in *.
                    rewrite _In_labNodes_is_some_MapsTo in mat'.
                    assert ((node, label) = (node, label) /\ ~ _key_In_IG node rest \/ In (node, label) (IG_labNodes rest)). {
                        apply (IG_match_removes_node _ _ node) in mat.
                        left. auto. 
                    }
                    apply mat' in H0.
                    destruct_eMapsTo H0.
                    exists (efroms, label, etos).
                    assumption.
                } clear mat. split; intros.
                ++ left. reflexivity.
                ++ assumption.
        
            -- rewrite <- H. clear H.
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
                    assert ((n, label') = (node, label) /\ ~ _key_In_IG (fst (n, label')) rest \/ exists froms tos : Adj B, NatMap.MapsTo n (froms, label', tos) rest). {
                        right. firstorder. 
                    }
                    apply mat in H1. destruct_eMapsTo H1. firstorder.
    - intros. rename e into mat. simpl. apply IG_matchAny_None_is_empty in mat. 
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
    intros.
    unfold IG_transpose.
    unfold IG_gmap.
    unfold IG_to_RG at 2.
    apply IG_ufold_rec_ind.
    - intros.
        unfold IG_ufold.
        rewrite !IG_ufold_rec_equation.
        rewrite e in *.

        rewrite RG_transpose_distributes_over_extendByContext.
        rewrite IG_and_relates.
        rewrite <- H.
        rewrite !IG_ufold_rec_equation.

        reflexivity.

    - intros. rewrite !IG_ufold_rec_equation. rewrite e. clear. firstorder. 
Qed.









(* Theorems about DFS *)


Theorem IG_DFS_returns_only_nodes : forall (A B : Type) (ig : IG A B) (nodes : list Node),
    forall x, In x (IG_DFS nodes ig) -> _key_In_IG x ig. 
Proof.
    intros A B.
    unfold IG_DFS.

    assert (forall (igNodes : IG A B * list Node) (x : Node), let '(ig, _) := igNodes in In x (IG_DFS_rec A B igNodes) -> _key_In_IG x ig). {

    apply (IG_DFS_rec_ind _ _ (fun igNodes acc => forall (x : Node),
        let '(ig, nodes) := igNodes in
        In x acc -> _key_In_IG x ig)); intros; subst.
        (* list is empty *)
        - inversion H.
        (* graph is empty *)
        - inversion H.

        (* graph (and list) is nonempty (interesting 2 cases) *)

        (* the node in the queue in is the graph (graph gets smaller) *)
        - rename e2 into mat.
            simpl in *. destruct_context cntxt. 
            destruct H0.
            + subst. apply IG_match_returns_node in mat as mat'. subst.
                eapply IG_match_exactly_removes_node in mat as mat'.
                apply IG_match_removes_node in mat.
                firstorder.

            + specialize (H _ H0). clear H0.
                    destruct H. exists x0.
                    eapply IG_match_exactly_removes_node in mat.

                    apply mat. clear mat. firstorder.
        (* the node in the queue is not in the graph (the queue gets smaller) *)
        - rename e2 into mat.
            apply IG_match_none_returns_graph in mat. subst. auto.
    }

    intros.
    specialize (H (ig, nodes)).
    auto.
Qed.







Theorem IG_DFS_no_duplicates : forall (A B : Type) (ig : IG A B) (nodes : list Node),
    NoDup (IG_DFS nodes ig).
Proof.
    intros.
    unfold IG_DFS.

    apply (IG_DFS_rec_ind _ _ (fun igNodes acc => NoDup acc)); intros; subst.

    (* list is empty *)
    - apply NoDup_nil.
    (* graph is empty *)
    - apply NoDup_nil.

    (* graph (and list) is nonempty (interesting 2 cases) *)

    (* the node in the queue in is the graph (graph gets smaller) *)
    - rename e2 into mat.
        apply NoDup_cons.
        + unfold not. intros.
            pose proof IG_DFS_returns_only_nodes. unfold IG_DFS in H1.
            specialize (H1 _ _ rest (suc cntxt ++ ns) _ H0). 
            eapply IG_match_removes_node in mat.
            auto.
        + auto.

    (* the node in the queue is not in the graph (the queue gets smaller) *)
    - assumption.
Qed.









(* Only reachable and all reachable nodes are included *)
Theorem IG_DFS_path : forall (A B : Type) (igNodes : list NatSet.Node * IG A B) x,
    let '(nodes, ig) := igNodes in
    In x (IG_DFS nodes ig)
        <-> exists y, In y nodes /\ RG_existsPath y x (IG_to_RG ig).
Proof.
    intros. destruct igNodes as [ig nodes].
Admitted.