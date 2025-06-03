Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import Coq.Arith.Arith.

Require Import List.
Require Import Coq.Structures.OrdersTac.
Require Import Bool.
Import ListNotations.

Require Import FSets.
Require Import FMaps.
Require Import OrderedTypeEx.
Require Import Setoid Morphisms.


Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.NatMap.


Require Import GraphVerification.src.inductive.inductive_graph.
Require Import GraphVerification.src.inductive.inductive_graph_measure.
Require Import GraphVerification.src.inductive.inductive_graph_theory.
Require Import GraphVerification.src.inductive.inductive_graph_measured_algorithms.
Require Import GraphVerification.src.inductive.inductive_graph_to_RG.

Require Import GraphVerification.src.relational_graph.
Require Import GraphVerification.src.relational_graph_theory.

Require Import Coq.Relations.Relation_Operators.



(* This file shows that I== is an equivalence and attempts at "direct equational specification" of IG s  *)

(* Section to make rewrite work with IG_equiv *)
(* This proof is based on R== being an equivalence relation *)
Instance IG_Equivalence {A B : Type} : Equivalence (@IG_equiv A B).
Proof.
  G_derived_equivalence_prover nat unit (@ IG_to_RG A B).  
Qed.




(* Definition  *)
Theorem IG_DFS_returns_only_nodes : forall (A B : Type) (igNodes : IG A B * list NatSet.Node),
  let '(ig, nodes) := igNodes in
  incl (IG_DFS nodes ig) (map fst (IG_labNodes ig)). 
Proof.
  intros A B. (* Maybe the l needs to stay general in the induction hypothesis....*)
  apply (well_founded_induction
           (wf_lexord_arg_pair_s A B)).  (* induction nodes. *)
  
  intros nodesIG IH.
  destruct nodesIG as [ig nodes].

  unfold incl in *. intros.
  unfold IG_DFS in H. rewrite IG_DFS_rec_equation in H.
  destruct nodes.
  - apply in_nil in H. destruct H.
  - destruct (IG_isEmpty ig) eqn:em.
    + apply in_nil in H. destruct H.
    + destruct (IG_match n ig) eqn:mat.
      destruct m (*eqn:mm*).
      -- simpl in *.
          destruct H.
          (* Continue here: *)
        ++ destruct c as [[[froms node] label] tos]. 
            apply IG_match_returns_node in mat as mmmm.
            subst.

          
          eapply IG_match_just_removes_node in mat.
          apply _In_map_fst_exists_second.
          exists label.
          apply mat.
          simpl. left. reflexivity.

        ++ destruct c as [[[froms node] label] tos].
            specialize (IH (i, suc (froms, node, label, tos) ++ nodes)).
            assert (lexord_arg_pair_s A B (i, suc (froms, node, label, tos) ++ nodes) (ig, n :: nodes)). {
              unfold lexord_arg_pair_s. unfold lexord_dep_arg_pair_s. 
              unfold prodTo_dep_arg_pair_s.
              simpl.
              apply left_lex.
              apply _IG_match_decreases_IG_noNodes in mat.
              assumption.
            }
            specialize (IH H0).
            apply IH in H.

            rewrite _In_map_fst_exists_second in H.
            destruct H.
            rewrite _In_map_fst_exists_second.
            exists x.

            pose proof IG_match_just_removes_node.


            specialize (H1 _ _ _ _ _ _ _ _ _ (a, x) mat).
            apply H1.
            simpl.
            right. assumption.
      -- unfold IG_match in mat. destruct (NatMap.find n ig) eqn:HH.
        ++ destruct (_cleanSplit n c (NatMap.remove n ig)) eqn:split0. inversion mat.
        ++ (*i * ig*) inversion mat. subst.
            specialize (IH (i, nodes)).
            assert (lexord_arg_pair_s A B (i, nodes) (i, n :: nodes)). {
              unfold lexord_arg_pair_s. unfold lexord_dep_arg_pair_s. 
              unfold prodTo_dep_arg_pair_s.
              simpl.
              apply right_lex.
              auto.
            } specialize (IH H0).
            apply IH. apply H.
Qed.











(* Following this website: *)
(* https://sharmaeklavya2.github.io/theoremdep/nodes/graph-theory/dfs/dfs.html *)






Theorem IG_DFS_no_duplicates : forall (A B : Type) (igNodes : IG A B * list NatSet.Node),
  let '(ig, nodes) := igNodes in
  NoDup (IG_DFS nodes ig).
Proof.
  intros A B. 
  apply (well_founded_induction
          (wf_lexord_arg_pair_s A B)).  (* induction nodes. *)
  intros nodesIG IH.
  destruct nodesIG as [ig nodes].

  unfold IG_DFS. rewrite IG_DFS_rec_equation. destruct nodes.
    - apply NoDup_nil.
    - destruct (IG_isEmpty ig) eqn:igEmpty.
      + apply NoDup_nil.
      + destruct (IG_match n ig) eqn:mat.
         destruct m eqn:mm.
         -- apply NoDup_cons.
            ++ pose proof IG_DFS_returns_only_nodes.
              unfold incl in H. unfold not. intros. unfold IG_DFS in H.
              specialize (H _ _ (i, suc c ++ nodes) _ H0). apply _In_map_fst_exists_second in H. destruct H.
             eapply IG_match_removes_node in mat.
             apply mat in H.
             apply H.

            ++ specialize (IH (i, suc c ++ nodes)).
                assert (lexord_arg_pair_s A B (i, suc c ++ nodes) (ig, n :: nodes)). {
                  unfold lexord_arg_pair_s. unfold lexord_dep_arg_pair_s. 
                  unfold prodTo_dep_arg_pair_s.
                  simpl.
                  apply left_lex.
                  apply _IG_match_decreases_IG_noNodes in mat.
                  assumption.
                }
                specialize (IH H).
                apply IH.
        --  apply IG_match_none_returns_graph in mat. subst.
            specialize (IH (i, nodes)).
            assert (lexord_arg_pair_s A B (i, nodes) (i, n :: nodes)). {
              unfold lexord_arg_pair_s. unfold lexord_dep_arg_pair_s. 
              unfold prodTo_dep_arg_pair_s.
              simpl.
              apply right_lex.
              auto.
            }
            specialize (IH H).
            apply IH.
Qed.
            



(* I nned to show that the remainder of the graph , does not have a anymore *) 


(* For all in the list, there is a path from the starting nodes *)

Theorem IG_DFSpath : forall (A B : Type) (igNodes : list NatSet.Node * IG A B) x y,
  let '(nodes, ig) := igNodes in
  In x nodes -> In y (IG_DFS nodes ig) -> RG_existsPath x y (IG_to_RG ig).
Proof.
  intros. destruct igNodes as [ig nodes].
Admitted.













































Lemma RG_transpose_distributes_over_extendByContext : forall {A B : Type} (c : Context A B) (rg : RG_unlE nat),
  RG_transpose (RG_add c rg) R== RG_add (_transposeContext c) (RG_transpose rg).
Proof.
  intros.
  firstorder.
  - simpl. unfold RG_transpose in H. simpl in H. destruct c as [[[froms node] label] tos]. unfold RG_add in H. simpl in H. firstorder.
  - simpl. unfold RG_transpose in H. simpl in H. destruct c as [[[froms node] label] tos]. unfold RG_add in H. simpl in H. firstorder.
  - unfold RG_transpose in H. simpl in H. destruct c as [[[froms node] label] tos]. unfold RG_add in H. simpl in H. firstorder.
  - unfold RG_transpose in H. simpl in H. destruct c as [[[froms node] label] tos]. unfold RG_add in H. simpl in H. firstorder.
Qed.

Definition contextEquiv {A B : Type} (c1 c2 : Context A B) : Prop :=
    c1 = c2.


Require Import Setoid Morphisms.

Instance Proper_add {A B : Type} : Proper ((@contextEquiv A B) ==> (@IG_equiv A B) ==> (@IG_equiv A B)) IG_and. 
Proof.
Admitted.



Instance Proper_RG_add {A B : Type}  : Proper ((@contextEquiv A B) ==> (@RG_equiv nat unit) ==> (@RG_equiv nat unit)) RG_add. 
Proof.
    split; unfold contextEquiv in H; subst; destruct y as [[[froms node] label] tos].
    - firstorder.
    - firstorder.
Qed.



Lemma blah : forall A B node froms0 label tos,
  forall ig,
  NatMap.Equal
  (
    NatMap.add node (filter (fun '(_, n0) => negb (n0 =? node)) froms0, label, tos)
      (_updAdj (filter (fun '(_, n0) => negb (n0 =? node)) tos) (fun (_ : B) (y : Context' A B) => _clearPred node y)
        (_updAdj (filter (fun '(_, n0) => negb (n0 =? node)) froms0) (fun (_ : B) (y : Context' A B) => _clearSucc node y)
          (NatMap.remove (elt:=Context' A B) node ig)))
  )
  (
    _updAdj (filter (fun '(_, n0) => negb (n0 =? node)) tos) (fun (_ : B) (y : Context' A B) => _clearPred node y)
      (_updAdj (filter (fun '(_, n0) => negb (n0 =? node)) froms0) (fun (_ : B) (y : Context' A B) => _clearSucc node y)
        (NatMap.add node (filter (fun '(_, n0) => negb (n0 =? node)) froms0, label, tos)
          (NatMap.remove (elt:=Context' A B) node ig)))
  ).
Proof.
Admitted.



(* This is a useful, and hopefully true lemma *)
Lemma matchIsAdd : forall (A B : Type) (n : Node) (ig i : IG A B) (c : Context A B),
  IG_match n ig = (Some c,  i) -> ig I== IG_and c i.
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


    + (* this case is a contradiction*) 
      admit.

    + admit. 
    (* rewrite blah.  unfold _addSucc. unfold _addPred. *)


Admitted.



Lemma matchAnyIsAdd : forall (A B : Type) (ig i : IG A B) (c : Context A B),
  IG_matchAny ig = (Some c,  i) -> ig = IG_and c i.
Proof.
  intros.
Admitted.

Lemma matchAnyIsAdd' : forall (A B : Type) (ig i : IG A B) (c : Context A B),
  IG_matchAny ig = (Some c,  i) -> ig I== IG_and c i.
Proof.
  intros. unfold IG_equiv.
  unfold IG_matchAny in H.
Admitted.




Lemma IG_ufold_nothing : forall (A B : Type) (ig : IG A B),
  IG_ufold _ _ _ IG_and IG_empty ig I== ig.
Proof.
  intros A B.
        apply (well_founded_induction
           (well_founded_ltof _ IG_noNodes)).

  intros ig IH.
   (* unfold IG_equiv. *)
  rewrite IG_ufold_equation.
  destruct (IG_matchAny ig) eqn:mat.
  destruct m eqn:mm.
  - specialize (IH i). assert (ltof (IG A B) IG_noNodes i ig). {
    unfold ltof.
    apply _IG_matchAny_decreases_IG_noNodes in mat.
    assumption.
    }
    specialize (IH H). clear H.
    rewrite IH.
    apply matchAnyIsAdd' in mat. rewrite <- mat. reflexivity.

  - admit. (*easy*)
Admitted.



Lemma IG_ufold_add : forall (A B : Type)  (c : Context A B) (ig : IG A B),
  IG_ufold _ _ _ IG_and IG_empty (IG_and c ig) I== IG_and c (IG_ufold _ _ _ IG_and IG_empty ig).
Proof.
  intros.
  rewrite IG_ufold_nothing.
  rewrite IG_ufold_nothing.
  reflexivity.
Qed.








Lemma IG_ufold_step : forall (A B C : Type) (f : Context A B -> C -> C) (acc : C) (c : Context A B) (ig : IG A B),
  IG_ufold _ _ _ f acc (IG_and c ig) = f c (IG_ufold _ _ _ f acc ig).
Proof.
Admitted.




Lemma IG_to_RG_distributes_over_add : forall {A B : Type} (c : Context A B) (ig : IG A B),
  IG_to_RG (IG_and c ig) R== RG_add c (IG_to_RG ig). 
Proof.
  intros.

  unfold IG_to_RG.
  rewrite IG_ufold_step.
  reflexivity.
Qed.





Lemma IG_to_RG_distributes_over_add' : forall {A B : Type} (cIG : Context A B * IG A B),
  let '(c, ig) := cIG in
  IG_to_RG (IG_and c ig) R== RG_add c (IG_to_RG ig). 
Proof.
  intros A B.
        apply (well_founded_induction
           (well_founded_ltof _ (fun x : Context A B * IG A B => IG_noNodes (snd x)))).
    intros cIg IH.
    destruct cIg as [c ig].

    (* unfold IG_and. *)
    unfold IG_to_RG at 2. rewrite !IG_ufold_equation. destruct (IG_matchAny ig) eqn:mat.
    destruct m eqn:mm.

  - apply matchAnyIsAdd in mat as bb.
      rewrite bb.
      assert (IG_ufold _ _ _ RG_add RG_empty i = IG_to_RG i). {
        reflexivity.
      }

      rewrite H.

      (* pose proof IH as IH2. *)
      
      
      specialize (IH (c0, i)). assert (ltof (Context A B * IG A B) (fun x : Context A B * IG A B => IG_noNodes (snd x)) (c0, i) (c, ig)). {
      unfold ltof.
      apply _IG_matchAny_decreases_IG_noNodes in mat.
      assumption.
      }
      specialize (IH H0). clear H0.

      simpl in IH.

      rewrite <- IH.


      (* rewrite <- mat. *)


      destruct c as [[[froms node] label] tos].
      destruct c0 as [[[froms0 node0] label0] tos0].
Admitted.






























(* Showing properties about transpose: *)

Theorem IG_transpose_is_RG : forall (A B : Type) (ig : IG A B),
    IG_to_RG (IG_grev ig) R== RG_transpose (IG_to_RG ig).
Proof.
  intros A B.
  apply (well_founded_induction
        (well_founded_ltof _ IG_noNodes)).
    intros ig IH.
    unfold IG_grev. unfold IG_gmap. unfold IG_to_RG at 2. rewrite !IG_ufold_equation. destruct (IG_matchAny ig) eqn:mat.
    destruct m eqn:mm.
    - specialize (IH i). assert (ltof (IG A B) IG_noNodes i ig). {
      unfold ltof.
      apply _IG_matchAny_decreases_IG_noNodes in mat.
      assumption.
      }
      specialize (IH H). clear H.
      rewrite RG_transpose_distributes_over_extendByContext.
      (* RHS is now "ready" for IH *)
      rewrite <- IH.
      
      destruct c as [[[froms node] label] tos].
      
      rewrite IG_to_RG_distributes_over_add.
      assert (IG_ufold A B (IG A B) (fun (c : Context A B) (acc : IG A B) => IG_and (_transposeContext c) acc) IG_empty i = IG_grev i). {
        reflexivity.
      }
      rewrite H.
      rewrite IH.
      reflexivity.

    - clear mat mm IH. unfold IG_to_RG. rewrite IG_ufold_equation. simpl. unfold RG_transpose. firstorder. 

Qed.








(* Messing around with fold on IGs *)




Lemma IG_ufold_rec :
  forall (A B C : Type) (P : IG A B -> C -> Prop) (f : Context A B -> C -> C),
    forall (i : C) (g : IG A B), 
    (forall g, IG_isEmpty g = true -> P g i) -> 
    (forall k a g' g'', (In k (map fst (IG_labNodes g))) -> ~ (In k (map fst (IG_labNodes g'))) -> 
    match IG_match k g with
      | (Some context, rest) => P g' (f context a) -> P g'' (f context a)
      | _ => False
    end) ->

    P g (IG_ufold _ _ _ f i g).
Proof.
  intros.
Admitted.

(* This is probably true, but does not really work in my case *)
(* This can make it to the final thesism however relies on an unfinished lemma *)
Lemma IG_induction : forall (A B : Type) g (P : IG A B -> Prop) (rewriteP : Proper (IG_equiv ==> eq) P),
  P IG_empty -> (forall g c, P g -> P (IG_and c g)) ->
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
    subst.
    apply IH.
    specialize (H i).
    apply H.
    apply _IG_matchAny_decreases_IG_noNodes in mat.
    unfold ltof. auto.
  (* No hit: *)
    - unfold IG_matchAny in mat. destruct (IG_labNodes x) eqn:labNodes.
    + inversion mat. subst. unfold IG_labNodes in labNodes.
      apply map_eq_nil in labNodes.
      apply MProps.elements_Empty in labNodes.
      assert (NatMap.Equal i IG_empty). {
        unfold IG_empty.
        unfold NatMap.Equal.
        intros.
        Search NatMap.find.
        rewrite MFacts.empty_o.
        apply MFacts.not_find_in_iff.
        unfold not. intros.
        Search NatMap.In.
        unfold NatMap.Empty in labNodes.
        unfold NatMap.In in H0.
        admit.
      }
      destruct (rewriteP i IG_empty). 
      -- admit.
      -- assumption.

    + unfold IG_match in mat. destruct (NatMap.find (fst l) x) eqn:found.
      -- destruct (_cleanSplit (fst l) c (NatMap.remove (elt:=Context' A B) (fst l) x)).
        inversion mat.
      -- assert (x = IG_empty). {
          admit.
        }
        rewrite H0.
        assumption.
Admitted.





Lemma _matchAny_add_IG_empty : forall (A B : Type) (c hit : Context A B) (i : IG A B),
  IG_matchAny (IG_and c IG_empty) = (Some hit, i)
  -> let '(froms, node, label, tos) := c in IG_isEmpty i = true /\ hit = ([], node, label, []).
Proof.
Admitted.


Lemma IG_to_RG_distributes_over_add_using_IG_induction : forall {A B : Type} (c : Context A B) (ig : IG A B),
  IG_to_RG (IG_and c ig) R== RG_add c (IG_to_RG ig). 
Proof.
  intros.
  unfold IG_to_RG at 2.
  apply (IG_ufold_rec A B). 
  - admit. (* Here, I need some thinking *)
  - intros. unfold IG_to_RG.
   rewrite !IG_ufold_equation.

  

Admitted.






