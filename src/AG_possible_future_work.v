Require Import Setoid Morphisms.
Require Import Ensembles.

Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.util.

Require Import GraphVerification.src.relational.RG.
Require Import GraphVerification.src.relational.RG_theory.

Require Import GraphVerification.src.algebraic.AG.
Require Import GraphVerification.src.algebraic.AG_to_RG.

Require Import Relation_Operators.

Require Import GraphVerification.src.util.util.
Require Import Arith.

Require Import GraphVerification.src.algebraic.AG_derived_operations_theory.

(* TODO: delete this file before handing in *)


(* Here are attempts at specifying which elements are in BFS and in which order *)


Lemma AG_nodeAmount_empty :
    AG_nodeAmount AG_empty = 0.
Proof.
    unfold AG_nodeAmount. reflexivity.
Qed.

Lemma NatSet_emptyElements : forall (nodes : list Node),
    NatSet.elements (NatSet.inter (NatSet_fromList nodes) NatSet.empty) = [].
Proof.
    intros.
    apply SProps.MP.elements_Empty. apply SProps.MP.empty_inter_2. apply NatSet.empty_spec.
Qed.




Lemma if_same_result : forall (A : Type) (a : A) (b : bool),
    (if b then a else a) = a.
Proof.
    intros. destruct b. reflexivity. reflexivity.
Qed.


(* About what is included, can also add that every node that has a path is i the result *)
Theorem AG_BFS_path : forall (nodes : list nat) (ag : AG nat) x,
    In x (AG_BFS nodes ag)
        -> In x nodes \/ exists y, In y nodes /\ RG_existsPath y x (AG_to_RG ag). 
Proof.
    intros. induction ag.
    - exfalso. unfold AG_BFS in H. simpl in H. rewrite NatSet_emptyElements in H. destruct (NatSet.equal (NatSet.inter (NatSet_fromList nodes) NatSet.empty)
(NatSet.union (NatSet.inter (NatSet_fromList nodes) NatSet.empty) NatSet.empty)).
        ++ simpl in H. inversion H.
        ++ simpl in H. inversion H.
    - left. 
        unfold AG_BFS in H.
        apply _consolidation_fold_right_preserves_nodes in H.
        destruct H. destruct H.
        simpl in H. destruct H.
        + destruct (existsb (Nat.eqb a) nodes) eqn:has.
            -- admit.
            -- exfalso. admit. 
        + rewrite if_same_result in H.
            destruct (NatSet.equal (NatSet.inter (NatSet_fromList nodes) (NatSet.singleton a)) (NatSet.union (NatSet.inter (NatSet_fromList nodes) (NatSet.singleton a)) NatSet.empty)).
            -- inversion H.
            -- simpl in *. destruct H. 
                ++ subst. apply SProps.MP.FM.empty_iff in H0. inversion H0.
                ++ inversion H.
    - unfold AG_BFS in H.
        apply _consolidation_fold_right_preserves_nodes in H.
        destruct H. destruct H.
        simpl in H. destruct H.

Admitted.





Theorem AG_BFS_path' : forall (nodes : list nat) (ag : AG nat) x,
    In x (AG_BFS nodes ag)
        -> In x nodes \/ exists y, In y nodes /\ RG_existsPath y x (AG_to_RG ag). 
Proof.
    intros.  
    unfold AG_BFS in H.
    apply _consolidation_fold_right_preserves_nodes in H.
    destruct H. destruct H.
    induction ag.
    - admit.
    - admit.
    - simpl in H. destruct H.
        + left. admit.
        + destruct (NatSet.equal (NatSet.inter (NatSet_fromList nodes) (NatSet.union (AG_nodeSet ag1) (AG_nodeSet ag2)))
(NatSet.union (NatSet.inter (NatSet_fromList nodes) (NatSet.union (AG_nodeSet ag1) (AG_nodeSet ag2)))
(NatSet.union (_singleStep (NatSet.inter (NatSet_fromList nodes) (NatSet.union (AG_nodeSet ag1) (AG_nodeSet ag2))) ag1)
(_singleStep (NatSet.inter (NatSet_fromList nodes) (NatSet.union (AG_nodeSet ag1) (AG_nodeSet ag2))) ag2)))).
            -- inversion H.
            -- unfold RG_existsPath.
                 (* Now that I think of how RG_existsPath would even be split up, I don't really know how this could be continued..... hmmm. There is the problem, that if one does a zig zag from ag1 to ag2. combining the two IH is not really enough, right? *)
            
            
            

Admitted.



(* Actual specification about the order of nodes from BFS *)
Theorem AG_BFS_order : forall (nodes : list nat) (ag : AG nat),
    BFS_Order nodes (AG_BFS nodes ag) (AG_to_RG ag).
Proof.
    intros.
Admitted.

