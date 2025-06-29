Require Import Lia.

Require Import Arith.

Require Import List.
Import ListNotations.

Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.NatMap.

Require Import Relation_Operators.


Require Import GraphVerification.src.relational.RG.
Require Import GraphVerification.src.relational.RG_theory.

Require Import GraphVerification.src.inductive.IG.
Require Import GraphVerification.src.inductive.IG_wf.
Require Import GraphVerification.src.inductive.IG_theory.
Require Import GraphVerification.src.inductive.IG_wf_operations.
Require Import GraphVerification.src.inductive.IG_to_RG.

Require Import GraphVerification.src.inductive.IG_theory.
Require Import GraphVerification.src.inductive.IG_wf_operations_theory.

Require Import GraphVerification.src.inductive.IG_mkGraph_theory.

Require Import GraphVerification.src.util.util.


(* TODO: delete this file, before handing in *)







(* Only reachable and all reachable nodes are included *)
Theorem IG_DFS_path : forall (A B : Type) (igNodes : list NatSet.Node * IG A B) x,
    let '(nodes, ig) := igNodes in
    In x (IG_DFS nodes ig)
        <-> exists y, In y nodes /\ RG_existsPath y x (IG_to_RG ig).
Proof.
    intros. destruct igNodes as [ig nodes].
Admitted.







Print IG_labEdges.

(* Try proving the same, but now for edges *)

Definition _edge_In_IG {A B : Type} (e : Node * Node) (ig : IG A B) : Prop :=
    let '(from, to) := e in
    exists l, In (from, to, l) (IG_labEdges ig).

Definition addedByContext {A B : Type} (e : Node * Node) (c : Context A B) : Prop.
Proof.
Admitted.





Lemma and_relates_for_edges : forall (A B : Type) (ig : IG A B) (c : Context A B) e,
    let '(from, to, l) := e in
    (c &R (IG_to_RG ig)).(RG_edges) from to l
        <-> (IG_to_RG (c &I ig)).(RG_edges) from to l.
Proof.
    intros. destruct e as [[from to] l].
    assert (
    forall (A B : Type) e (ig : IG A B),
        let '(from, to, l) := e in
        _edge_In_IG (from, to) ig <-> (IG_to_RG ig).(RG_edges) from to l). {
        clear.
            
        intros A B e.
        apply (well_founded_induction (well_founded_ltof _ (@IG_noNodes A B))).
        intros ig IH. unfold IG_to_RG.
        rewrite IG_ufold_rec_equation.
        destruct (IG_matchAny ig) eqn:mat.
        destruct m.
        - specialize (IH i).
            apply IG_matchAny_decreases_IG_noNodes in mat as mat'.
            specialize (IH mat'). clear mat'. destruct_edge e. destruct_context c. simpl.
            unfold IG_labEdges.
            (* Now, I need to distinguish between the case where the edge was added by the new context, or already existed *)

            (* In the end, I would need to prove similar heorems about match also for edges and not just nodes *)

(* Lemma IG_match_removes_edge : forall (A B : Type) (query : Node) (mContext : MContext A B) (ig i : IG A B),
    IG_match query ig = (Some c, i)
        -> forall e in c, e not in i. 

Lemma IG_match_exactly_removes_edge : forall (A B : Type) (query : Node) (c : Context A B) (ig i : IG A B) (x : LNode A),
    IG_match query ig = (Some c, i)
        -> In e (IG_labEdges ig)
                <->(e in c and e not in i) or e in I *)
                (* the left and right of the or would yield the "split" of the ig, I need *)


            admit.
        - admit.


    }
    rewrite <- (H _ _ (from, to, l)).

    assert (forall (A B : Type) (c : Context A B) (ig : IG A B) (e : Node * Node),
            _edge_In_IG e (c &I ig) <->
            _edge_In_IG e ig \/
            let '(froms, node, label, tos) := c in
            let '(n1, n2) := e in
                (not (_key_In_IG node ig) /\ (_key_In_IG n1 ig \/ node = n1) /\ (_key_In_IG n2 ig \/ node = n2) /\
                    ((In n1 (map snd froms) /\ n2 = node)
                        \/ (n1 = node /\ In n2 (map snd tos))
                    )
                )
            
            
            ). {
        admit.
    }

    rewrite H0.
    destruct_context c.
    simpl.
Admitted.



(* This is actually not true in the general case, but for the particular function, with which it is used, it is most likely true *)
Lemma IG_ufold_step : forall (A B C : Type) (f : Context A B -> C -> C) (acc : C) (c : Context A B) (ig : IG A B),
    IG_ufold f acc (c &I ig) = f c (IG_ufold f acc ig).
Proof.
Admitted.


Lemma IG_to_RG_distributes_over_add_dep_on_incompl : forall {A B : Type} (c : Context A B) (ig : IG A B),
    IG_to_RG (c &I ig) ==R c &R (IG_to_RG ig). 
Proof.
    intros.

    unfold RG_equiv. split.
    - intros. rewrite IG_and_relates_for_nodes. reflexivity.
    - intros. rewrite (and_relates_for_edges _ _ _ _ (a1, a2, b)). reflexivity.
Qed.
















































(* New model where it is easer to show some stuff *)


(* This is actually not true in most cases ;/ *)
Lemma IG_to_RG'_valid : forall (A B : Type) (ig : IG A B),
_valid_cond (fun n : nat => _key_In_IG n ig)
(fun (n1 n2 : nat) (_ : unit) => exists l : B, In (n1, n2, l) (IG_labEdges ig)).
Proof.
Admitted.

Definition IG_to_RG' {A B : Type} (ig : IG A B) : RG_unlE nat.
Proof.
    refine {|
        RG_nodes := fun (n : nat) => _key_In_IG n ig;
        RG_edges := fun (n1 n2 : nat) l => exists l, In (n1, n2, l) (IG_labEdges ig);
        RG_valid := _
    |}.
    apply IG_to_RG'_valid. (* Bypass*)
Defined.









(* Now, I try a fully new approach, where I look at what the paper has done *)

(* Fact 2, for each graph h and each node v. there exists p l s an d g' such that (p v ö s) & g' = G *)

Definition IG_equiv' {A B : Type} (ig1 ig2 : IG A B) : Prop :=
    RG_equiv (IG_to_RG' ig1) (IG_to_RG' ig2).

Notation "g1 ==I' g2" := (IG_equiv' g1 g2) (at level 80).






Lemma IG_match_rev_and : forall (A B : Type) (c : Context A B) (ig i : IG A B),
    let '(froms, node, label, tos) := c in
    IG_match node ig = (Some (froms, node, label, tos), i)
    -> ig ==I' (froms, node, label, tos) &I i.
Proof.
    intros. destruct_context c. intros.
    simpl.
    destruct (NatMap.mem node i) eqn:cond.
    - exfalso. apply IG_match_removes_node in H as mat. apply mat.
        unfold _key_In_IG. setoid_rewrite _In_labNodes_is_some_MapsTo.
        apply MFacts.mem_in_iff in cond.
        apply -> NatMap_In_exists_MapsTo_iff in cond.
        destruct cond. destruct_context' x.
        exists label'.
        exists froms', tos'.
        assumption.
    
    - unfold IG_match in H. destruct (NatMap.find node ig) eqn:found.
        + destruct (_cleanSplit node c (NatMap.remove node ig)) eqn:split.
            destruct_contextt c0.
            inversion H. subst. clear H.
            unfold _cleanSplit in split.
            destruct_context' c.
            inversion split. subst. clear split.

            unfold IG_equiv'.
            unfold RG_equiv. simpl. 
            split; intros.
            -- unfold _key_In_IG.
                setoid_rewrite _updAdj_addSucc_does_not_change_IG_labNodes.
                setoid_rewrite _updAdj_addPred_does_not_change_IG_labNodes.
                setoid_rewrite _In_labNodes_is_some_MapsTo.

                rewrite <- MFacts.find_mapsto_iff in found.
                simpl. setoid_rewrite MFacts.add_mapsto_iff.
                
                bdestruct (node =? a).
                ++ subst. firstorder.
                    exists label, (filter (fun '(_, n) => negb (n =? a)) froms'), tos. firstorder.
                ++ assert ((exists (other : A) (froms tos0 : Adj B), NatMap.MapsTo a (froms, other, tos0) ig)
                                <-> (exists (other : A) (froms tos0 : Adj B), NatMap.MapsTo a (froms, other, tos0) (_updAdj (filter (fun '(_, n) => negb (n =? node)) tos) (fun (_ : B) (y : Context' A B) => _clearPred node y) (_updAdj (filter (fun '(_, n) => negb (n =? node)) froms') (fun (_ : B) (y : Context' A B) => _clearSucc node y) (NatMap.remove (elt:=Context' A B) node ig))))). {
                                pose proof _updAdj_does_not_change_key_set.
                                unfold _key_In_IG in H0.
                                setoid_rewrite _In_labNodes_is_some_MapsTo in H0.
                                setoid_rewrite H0.
                                setoid_rewrite H0.
                                setoid_rewrite MProps.F.remove_neq_mapsto_iff.
                                - reflexivity.
                                - assumption.
                    }

                    rewrite H0. clear H0. 
                    split; intros.
                    --- firstorder.
                    --- firstorder.

            -- admit. (* Edges (NMUUUUUUUCH harder) I have no theorems about IG_labEdges *) 
        
        + inversion H.

Admitted.



(* STAR *)

(* This thoof is finished unless IG_match_rev_and relies on IG_to_RG' The same amount of stuff can be proved usign IG_to_RG (no prime) *)
Theorem Erwig_Fact2' : forall (A B : Type) (ig : IG A B) (n : Node),
    _key_In_IG n ig
        -> exists froms label tos i, ig ==I' (froms, n, label, tos) &I i.
Proof.
    intros.
    destruct (IG_match n ig) eqn:mat. destruct m.
    - destruct_context c. exists froms, label, tos, i.
        apply IG_match_returns_node in mat as mat'.
        subst.
        apply (IG_match_rev_and _ _ (froms, node, label, tos)).
        assumption.

    - exfalso. unfold _key_In_IG in H. unfold IG_match in mat.
        destruct (NatMap.find n ig) eqn:found.
        + destruct (_cleanSplit n c (NatMap.remove n ig)). inversion mat.
        + apply MFacts.not_find_in_iff in found.
            setoid_rewrite _In_labNodes_is_some_MapsTo in H.
            rewrite NatMap_In_exists_MapsTo_iff in found.
            apply found.
            destruct H.
            destruct_eMapsTo H.
            exists (efroms, x, etos).
            assumption.

Qed.





(* STAR *)

(* This thoof is finished unless IG_match_rev_and *)
Theorem Erwig_Fact2 : forall (A B : Type) (ig : IG A B) (n : Node),
    _key_In_IG n ig
        -> exists froms label tos i, ig ==I (froms, n, label, tos) &I i.
Proof.
    intros.
    unfold IG_equiv.
    unfold RG_equiv.
    esplit. esplit. esplit. esplit. split.
    - setoid_rewrite <- _key_In_IG_relates. intros.
        unfold _key_In_IG.
        (* This is possible, but somewhat tedious to prove. I will do this, if it is decided that it is worth it *)

        setoid_rewrite IG_and_adds_node.
Admitted.
    
    












(* STAR *)

(* Same as above, but now onIG_to_RG'. This is provable *)
Lemma node_is_ins_added_node' : forall (A B : Type) (c : Context A B) (ig : IG A B),
    let '(froms, node, label, tos) := c in
    RG_nodes (IG_to_RG' (_updAdj froms (_addSucc node) (_updAdj tos (_addPred node)
            (NatMap.add node (froms, label, tos) ig)))) node.
Proof.
    intros. destruct_context c. simpl.
    unfold _key_In_IG. exists label.
    apply _updAdj_addSucc_does_not_change_IG_labNodes.
    apply _updAdj_addPred_does_not_change_IG_labNodes.
    apply _In_labNodes_is_some_MapsTo.
    exists froms, tos.
    simpl.
    apply MFacts.add_mapsto_iff.
    auto.
Qed.

























(* More theorems about basic IG operations, that are quite advanced *)


(* This is a useful, and hopefully true lemma. A better version will be proven later *)
Lemma matchIsAdd : forall (A B : Type) (n : Node) (ig i : IG A B) (c : Context A B),
    IG_match n ig = (Some c,  i) -> ig ==I c &I i.
Proof.
    intros. unfold IG_equiv.
    unfold IG_match in H. destruct (NatMap.find n ig) eqn:HH.
    - destruct (_cleanSplit n c0 (NatMap.remove n ig)) eqn:split0. inversion H. subst.
        unfold _cleanSplit in split0.
        destruct c0 as [[froms0 label0] tos0].
        destruct c as [[[froms node] label] tos].
        inversion split0.
        rewrite H1 in *. clear H1.
        rewrite H2 in *. clear H2.
        rewrite H3 in *. clear H3.
        rewrite H4 in *. clear H4.
        clear H.

        (* Now, it's down to showing that if you IG_and a contexrt into an ig, that has just been cleared of it, you get the same ig *)
        unfold IG_and.
        destruct (NatMap.mem node (_updAdj (filter (fun '(_, n0) => negb (n0 =? node)) tos)
        (fun (_ : B) (y : Context' A B) => _clearPred node y)
        (_updAdj (filter (fun '(_, n0) => negb (n0 =? node)) froms0)
        (fun (_ : B) (y : Context' A B) => _clearSucc node y)
        (NatMap.remove (elt:=Context' A B) node ig)))) eqn:alreadyIn.


        + (* this case is a contradiction, since we know alreadyIn is true, but we removed the node *) 
        admit.
        + 

 
Admitted.


(* depends on unproved matchIsAdd *)
Lemma matchAnyIsAdd : forall (A B : Type) (ig i : IG A B) (c : Context A B),
    IG_matchAny ig = (Some c,  i) -> ig ==I IG_and c i.
Proof.
    intros. unfold IG_matchAny in H.
    destruct (IG_labNodes ig).
    - inversion H.
    - eapply matchIsAdd. apply H.
Qed.












(* This one is really hard... *)
Instance Proper_and {A B : Type} : Proper ((@contextEquiv A B) ==> (@IG_equiv A B) ==> (@IG_equiv A B)) (IG_and).  
Proof.
Admitted. 





(* Doable with some lemmas probably *)
Lemma IG_isEmpty_equiv_empty : forall (A B : Type) (ig : IG A B),
    IG_isEmpty ig = true <-> ig ==I IG_empty.
Proof.
Admitted.


(* Relies on unproven lemmas:
Proper_and
matchAnyIsAdd
... *)
Lemma IG_ufold_nothing : forall (A B : Type) (ig : IG A B),
    IG_ufold IG_and IG_empty ig ==I ig.
Proof.
    intros A B.
            apply (well_founded_induction
            (well_founded_ltof _ IG_noNodes)).

    intros ig IH.
    (* unfold IG_equiv. *)
    rewrite IG_ufold_rec_equation.
    destruct (IG_matchAny ig) eqn:mat.
    destruct m eqn:mm.
    (* The "smaller" graph I use for IH is i *) 
    - specialize (IH i). apply IG_matchAny_decreases_IG_noNodes in mat as mat'. unfold ltof in IH.
        specialize (IH mat'). clear mat'.

        rewrite IH.
        apply matchAnyIsAdd in mat. rewrite <- mat. reflexivity.

    - apply IG_matchAny_None_is_empty in mat. apply IG_isEmpty_equiv_empty in mat.
        rewrite mat. reflexivity.
Qed.




(* ERelies on unproved Proper_and *)
Lemma IG_ufold_add : forall (A B : Type)  (c : Context A B) (ig : IG A B),
    IG_ufold IG_and IG_empty (c &I ig) ==I c &I (IG_ufold IG_and IG_empty ig).
Proof.
    intros.
    rewrite IG_ufold_nothing.
    rewrite IG_ufold_nothing.
    reflexivity.
Qed.



(* Messing around with fold on IGs *)



(* Inductive principel for fold on IG? *)
Lemma IG_ufold_rec :
    forall (A B C : Type) (P : IG A B -> C -> Prop) (f : Context A B -> C -> C),
        forall (i : C) (g : IG A B), 
        (forall g, IG_isEmpty g = true -> P g i) -> 

        (forall k c any a g' g'', IG_match k g = (Some c, any) -> ~_key_In_IG k g' ->
        g' ==I c &I g'' -> P g' a -> P g'' (f c a)) ->


        P g (IG_ufold f i g).
Proof.
    intros.
Admitted.



(* This depends on these lemmas to be true:
IG_matchAny_None_is_empty
IG_isEmpty_equiv_empty
matchAnyIsAdd
*)
Lemma IG_induction : forall (A B : Type) (g : IG A B) (P : IG A B -> Prop) (rewriteP : Proper (IG_equiv ==> eq) P),
    P IG_empty -> (forall g' c, P g' -> P (c &I g')) ->
    P g.
Proof.
    intros A B ig P rewriteP base IH.
    apply (well_founded_induction
            (well_founded_ltof _ (@IG_noNodes A B))). 
    intros.
    destruct (IG_matchAny x) eqn:mat.
    destruct m eqn:mm.
    - subst. specialize (IH i c).
        apply matchAnyIsAdd in mat as isAdd.
        rewrite (rewriteP _ _ isAdd).
        apply IH. 
        apply H.

        apply IG_matchAny_decreases_IG_noNodes in mat.
        unfold ltof. assumption.
    (* No hit: *)
    - apply IG_matchAny_None_is_empty in mat. apply IG_isEmpty_equiv_empty in mat.
        rewrite (rewriteP _ _ mat). assumption.
Qed.













































(* This fails, since it just needs to be done by rewriting, for the nodes case, it's done, but not for the edges *)
Lemma IG_to_RG_distributes_over_add_using_IG_induction : forall {A B : Type} (c : Context A B) (ig : IG A B),
    IG_to_RG (c &I ig) ==R c &R (IG_to_RG ig). 
Proof.
    intros.
    generalize dependent c.
    apply (IG_induction A B ig (fun ig => forall c : Context A B, IG_to_RG (c &I ig)
==R c &R (IG_to_RG ig))). 
    - admit. (* Doable *)
    - admit. (* Doable *)
    - intros. rewrite H . admit.  (* IH Does not help *)
Admitted.

























(* Using different IG to RG *)

Lemma IG_to_RG_distributes_over_add' : forall {A B : Type} (c : Context A B) (ig : IG A B),
    IG_to_RG' (c &I ig) ==R c &R (IG_to_RG' ig). 
Proof.
Admitted.







Theorem IG_transpose_is_RG : forall (A B : Type) (ig : IG A B),
    IG_to_RG' (IG_transpose ig) ==R RG_transpose (IG_to_RG' ig).
Proof.
    intros A B.
    apply (well_founded_induction (well_founded_ltof _ IG_noNodes)).
    intros ig IH.
    unfold IG_transpose. unfold IG_gmap.
    unfold IG_to_RG.
    rewrite !IG_ufold_rec_equation. destruct (IG_matchAny ig) eqn:mat.
    destruct m.
    - specialize (IH i).
        apply IG_matchAny_decreases_IG_noNodes in mat as mat'.
        specialize (IH mat').
        (* This one is not fully proven *)
        rewrite IG_to_RG_distributes_over_add'.
        rewrite -> IH.
        rewrite <- RG_transpose_distributes_over_extendByContext.

    
        (* Now, I somehow need to show that if I have a match, I can derive a &I from it *)
        (* Also then, I would need to show that IG_to_RG' is a morphism and that it distributes over &I *)
         
Admitted.


(* Idunction does not work, since it need to be sone by just simplifying *)
Theorem IG_transpose_is_RG_using_own_induction : forall (A B : Type) (ig : IG A B),
    IG_to_RG' (IG_transpose ig) ==R RG_transpose (IG_to_RG' ig).
Proof.
    intros.
    apply (IG_induction A B ig (fun ig => IG_to_RG' (IG_transpose ig) ==R RG_transpose (IG_to_RG' ig))).
    - admit.
    - firstorder.
    - intros.
        (* I can't continue here, since there is the problem, that &I does not really enforce any order, so one cannot distribute over it *)
Admitted. 




























































(* Thinking about which operations are usable in a gmap, kinda failed *)





Definition _annihilate {A B : Type} (n : Node) (context : Context A B) : Context A B :=
    let '(froms, node, label, tos) := context in
    let c' := _clearPred n (froms, label, tos) in
    let '(fromss, labell, toss) := _clearSucc n c' in
    (fromss, node, labell, toss).

Print Adj.

Definition megaContext {A B : Type} (base extender : Context A B) : Context A B :=
    let '(efroms, enode, elabel, etos) := extender in
    let '(bfroms, bnode, blabel, btos) := base in
    let fromExtender := map (fun '(l, n) => (l, enode)) (filter (fun '(_, n) => n =? bnode) etos) in
    let toExtender := map (fun '(l, n) => (l, enode)) (filter (fun '(_, n) => n =? bnode) efroms) in
    (bfroms ++ fromExtender, bnode, blabel, btos ++ toExtender).





Lemma IG_and_semi_commutative : forall (A B : Type) (c1 c2 : Context A B) (ig : IG A B),
    c1 &I c2 &I ig ==I 
            let '(_, node2, _, _) := c2 in
        megaContext c2 c1 &I _annihilate node2 c1 &I ig.
Proof.
    intros.
    

    
    
    destruct_context c1. destruct_contextt c2. simpl.
    destruct (NatMap.mem nodee ig) eqn:cond1.
    - destruct (NatMap.mem node ig) eqn:cond2.
        + destruct (NatMap.mem nodee ig) eqn:cond3.
            -- reflexivity.
            -- inversion cond1.
        + destruct (NatMap.mem (elt:=Context' A B) nodee
(_updAdj (filter (fun '(_, n) => negb (n =? nodee)) froms) (_addSucc node)
(_updAdj (filter (fun '(_, n) => negb (n =? nodee)) tos) (_addPred node)
(NatMap.add node
(filter (fun '(_, n) => negb (n =? nodee)) froms, label,
filter (fun '(_, n) => negb (n =? nodee)) tos) ig)))); 
(* does nothing ??? *)
        
        admit. (* I have no clue, why destruct, rewrite, remember do not work here *)
        
    - destruct (NatMap.mem (elt:=Context' A B) node
(_updAdj fromss (_addSucc nodee) (_updAdj toss (_addPred nodee) (NatMap.add nodee (fromss, labell, toss) ig)))) eqn:cond2.
        + destruct (NatMap.mem node ig) eqn:cond3.
            -- destruct (NatMap.mem nodee ig) eqn:cond4.
                ++ inversion cond1.
                ++ admit. (* Here, there is work to do *)
            -- admit. (* I have no clue, why destruct, rewrite, remember do not work here *)
        + destruct (NatMap.mem node ig) eqn:cond3.
            -- destruct (NatMap.mem nodee ig) eqn:cond4.
                ++ inversion cond1.
                ++ admit. (* Here, there is work to do *)
            -- admit. (* I have no clue, why destruct, rewrite, remember do not work here *)

Admitted.
















Check incl.
Print incl.

(* Characterizing the functions for which gmap is universally correct *)

Lemma IG_map_splits_when : forall (A B C D: Type) (f : Context A B -> Context C D) (c : Context A B) (ig : IG A B),
    (forall anyC,
    let '(froms, node, label, tos) := anyC in
    let '(froms', node', label', tos') := f anyC in
    let possibleNeighbours := map snd froms ++ map snd tos in
    node = node' /\
    incl (map snd froms') possibleNeighbours /\  
    incl (map snd tos') possibleNeighbours)
    
    ->

    IG_gmap f (c &I ig) ==I f c &I IG_gmap f ig.
Proof.
    intros.
    destruct_context c.
Admitted.















Definition _mappable_based_on_edge {A B : Type} (nStart nEnd : Node) (whatToDoBasedConnections : list (LEdge B) -> (Adj B * Adj B)) (c : Context A B) : Context A B :=  
    let '(froms, node, label, tos) := c in
    if node =? nEnd then
        let listOfEdges := map (fun '(l, _) => (nStart, nEnd, l)) (filter (fun '(_, n) => n =? nStart) froms) in
        let '(newFroms, newTos) := whatToDoBasedConnections listOfEdges in
        (froms ++ newFroms, node, label, tos ++ newTos)
    else
        if node =? nStart then
            let listOfEdges := map (fun '(l, _) => (nStart, nEnd, l)) (filter (fun '(_, n) => n =? nEnd) tos) in
            let '(newFroms, newTos) := whatToDoBasedConnections listOfEdges in
            (froms ++ newFroms, node, label, tos ++ newTos)
            
        else
            c.
Require Import Permutation.


Lemma _mappable_based_on_edge_is_mappable : forall (A B : Type) (nStart nEnd : Node) (whatToDoBasedConnections : list (LEdge B) -> (Adj B * Adj B)) (c : Context A B) (ig1 ig2 : IG A B),

    (forall (input : list (LEdge B)),
    Forall (fun '(n1, n2, l) => nStart = n1 /\ nEnd = n2) input ->
        let '(froms, tos) := whatToDoBasedConnections input in
        Forall (fun '(l, n) => nStart = n \/ nEnd = n) froms /\ Forall (fun '(l, n) => nStart = n \/ nEnd = n) tos)

    ->

    (forall (input1 input2 : list (LEdge B)), Permutation input1 input2 ->
        let '(froms1, tos1) := whatToDoBasedConnections input1 in
        let '(froms2, tos2) := whatToDoBasedConnections input2 in
        Permutation froms1 froms2 /\ Permutation tos1 tos2)
    ->
 
    ig1 ==I ig2 ->
    IG_gmap (fun c => _mappable_based_on_edge nStart nEnd whatToDoBasedConnections c) ig1
    ==I IG_gmap (fun c => _mappable_based_on_edge nStart nEnd whatToDoBasedConnections c) ig2.
Proof.
Admitted.






Definition _rename_node_label {A B C : Type} (f : LNode A -> C) (c : Context A B) : Context C B :=
    let '(froms, node, label, tos) := c in
    (froms, node, f (node, label), tos).

Lemma _rename_node_label_correct : forall (A B C : Type) (f : LNode A -> C) (ig1 ig2 : IG A B),
    ig1 ==I ig2
    -> IG_gmap (fun c => _rename_node_label f c) ig1 ==I IG_gmap (fun c => _rename_node_label f c) ig2.
Proof.
Admitted.





Definition _rename_edge_label {A B C : Type} (f : LEdge B -> C) (c : Context A B) : Context A C :=
    let '(froms, node, label, tos) := c in
    (map (fun '(l, n) => (f (n, node, l), n)) froms, node, label, map (fun '(l, n) => (f (node, n, l), n)) tos).

Lemma _rename_edge_label_correct : forall (A B C : Type) (f : LEdge B -> C) (ig1 ig2 : IG A B),
    ig1 ==I ig2
    -> IG_gmap (fun c => _rename_edge_label f c) ig1 ==I IG_gmap (fun c => _rename_edge_label f c) ig2.
Proof.
Admitted.






