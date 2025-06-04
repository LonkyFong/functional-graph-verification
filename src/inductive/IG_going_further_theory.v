Require Import Lia.

Require Import Arith.

Require Import List.
Import ListNotations.

Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.NatMap.

Require Import Relation_Operators.


Require Import GraphVerification.src.RG.
Require Import GraphVerification.src.RG_theory.

Require Import GraphVerification.src.inductive.IG.
Require Import GraphVerification.src.inductive.IG_wf.
Require Import GraphVerification.src.inductive.IG_theory.
Require Import GraphVerification.src.inductive.IG_wf_algorithms.
Require Import GraphVerification.src.inductive.IG_to_RG.

(* More theorems about basic IG operations, that are quite advanced *)


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

 
Admitted.


Lemma matchAnyIsAdd : forall (A B : Type) (ig i : IG A B) (c : Context A B),
    IG_matchAny ig = (Some c,  i) -> ig I== IG_and c i.
Proof.
    intros. unfold IG_equiv.
    unfold IG_matchAny in H.
Admitted.


(* 

Instance Proper_add {A B : Type} : Proper ((@contextEquiv A B) ==> (@IG_equiv A B) ==> (@IG_equiv A B)) IG_and. 
Proof.
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
        apply matchAnyIsAdd in mat. rewrite <- mat. reflexivity.

    -  
    
    admit. (*easy*)
Admitted.




Lemma IG_ufold_add : forall (A B : Type)  (c : Context A B) (ig : IG A B),
    IG_ufold _ _ _ IG_and IG_empty (IG_and c ig) I== IG_and c (IG_ufold _ _ _ IG_and IG_empty ig).
Proof.
    intros.
    rewrite IG_ufold_nothing.
    rewrite IG_ufold_nothing.
    reflexivity.
Qed.



(* Messing around with fold on IGs *)




Lemma IG_ufold_rec :
    forall (A B C : Type) (P : IG A B -> C -> Prop) (f : Context A B -> C -> C),
        forall (i : C) (g : IG A B), 
        (forall g, IG_isEmpty g = true -> P g i) -> 
        (forall k a g' g'', (_key_In_IG k ( g))) -> ~ (_key_In_IG k ( g'))) -> 
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
    IG_to_RG (IG_and c ig) R== RG_and c (IG_to_RG ig). 
Proof.
    intros.
    unfold IG_to_RG at 2.
    apply (IG_ufold_rec A B). 
    - admit. (* Here, I need some thinking *)
    - intros. unfold IG_to_RG.
    rewrite !IG_ufold_equation.

    

Admitted.



*)





