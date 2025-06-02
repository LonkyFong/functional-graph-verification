Require Import Setoid Morphisms.


Require Import MyProject.project.algebraic.algebraic_graph.

Require Import MyProject.project.algebraic.algebraic_graph_to_RG.

Require Import MyProject.project.relational_graph.
(* Notice how this file "does"  need relational_graph_theory  *)
Require Import MyProject.project.relational_graph_theory.




Ltac AG_axiom_proof_automation_via_RG H H0 :=
    unfold AG_equiv; intros; split; split; intros; simpl; simpl in H; repeat (destruct H || destruct H0); auto
.

(* These are the "8 axioms" originally proposed by  functional graphs with class *)

(* +++ is commutative and associative *)
Theorem AG_Overlay_Commutative {A : Type} : forall (ag1 ag2 : AG A), ag1 +++ ag2 A== ag2 +++ ag1.
Proof.
        AG_axiom_proof_automation_via_RG H H0.
Qed.

Theorem AG_Overlay_Associative {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 +++ (ag2 +++ ag3) A== (ag1 +++ ag2) +++ ag3.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

(* (G, ***, e) is a monoid *)
Theorem AG_Empty_Connect_L_Identity {A : Type} : forall (ag : AG A), Empty *** ag A== ag.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

Theorem AG_Empty_Connect_R_Identity {A : Type} : forall (ag : AG A), ag *** Empty A== ag.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

Theorem AG_Connect_Associative {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 *** (ag2 *** ag3) A== (ag1 *** ag2) *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

(* *** distributes over +++ *)
Theorem AG_Connect_Overlay_L_Distributes {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 *** (ag2 +++ ag3) A== ag1 *** ag2 +++ ag1 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

Theorem AG_Connect_Overlay_R_Distributes {A : Type} : forall (ag1 ag2 ag3 : AG A), (ag1 +++ ag2) *** ag3 A== ag1 *** ag3 +++ ag2 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

(* Decomposition *)
Theorem AG_Connect_Decomposition {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 *** ag2 *** ag3 A== ag1 *** ag2 +++ ag1 *** ag3 +++ ag2 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.



(* Show that AG_to_RG is are "complete" and "sound"  *)
(* TODO: this is not very urgent right now, but is possibly necessary for model-based specification *)

(* Complete: *)
(* Look at paper *)

(* Sound: *)



(* Section to make rewrite work with equiv_AG *)
(* This proof is based on === being an equivalence relation *)
Instance AG_Equivalence {A : Type} : Equivalence (@AG_equiv A).
Proof.
    G_derived_equivalence_prover A unit (@AG_to_RG_unlE A).
Qed.
         

Ltac Proper_proof_automation H1 := split; split; intros; simpl in *; destruct H1; firstorder.


Instance Proper_add {A : Type} : Proper ((@AG_equiv A) ==> AG_equiv ==> AG_equiv) Overlay.
Proof.
    Proper_proof_automation H1.
Qed.


Instance Proper_mul {A : Type} : Proper ((@AG_equiv A) ==> AG_equiv ==> AG_equiv) Connect.
Proof.
    Proper_proof_automation H1.
Qed.




(* Theorems that can be made based on the "8 axioms": 
They can all be proven using "AG_axiom_proof_automation_via_RG", but I should find a way to do it using the axioms *)
(* These proofs are heavily inspired by: http://async.org.uk/tech-reports/NCL-EEE-MICRO-TR-2014-191.pdf *)


(* This is a helper for Identity of + *)
Lemma rdeco {A : Type}: forall (ag : AG A), ag +++ ag +++ Empty A== ag.
Proof.
    intros.
    pose proof (AG_Connect_Decomposition ag Empty Empty).

    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite <- H.

    reflexivity.
Qed.


(* Identity of + *)
Theorem AG_Empty_Overlay_R_Identity {A : Type}: forall (g : AG A), g +++ Empty A== g.
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
Theorem AG_Overlay_Idempotence {A : Type}: forall (ag : AG A), ag +++ ag A== ag.
Proof.
    intros.
    pose proof rdeco ag.
    rewrite AG_Empty_Overlay_R_Identity in H.
    auto.
Qed.



(* Absorption (proof is mine) *)
Theorem AG_Absorption {A : Type}: forall (ag1 ag2 : AG A), ag1 *** ag2 +++ ag1 +++ ag2 A== ag1 *** ag2.
Proof.
    intros. pose proof AG_Connect_Decomposition ag1 ag2 Empty.
    rewrite (AG_Connect_Associative) in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    symmetry in H.
    auto.
Qed.


(* Saturation (proof is mine) *)
Theorem AG_Saturation {A : Type}: forall (ag : AG A), ag *** ag *** ag A== ag *** ag.
Proof.
    intros.
    rewrite AG_Connect_Decomposition.

    rewrite AG_Overlay_Idempotence.
    rewrite AG_Overlay_Idempotence.
    reflexivity.
Qed.

























(* Here, I start proving things about BFS *)

Require Import List.

Require Import MyProject.project.util.NatSet.

Lemma if_result_same : forall (A : Type) (b : bool) (x : A), 
    (if b then x else x) = x.
Proof.
    intros.
    destruct b.
    - reflexivity.
    - reflexivity.
Qed.

Lemma NatSet_intersection_singleton : forall (s : NatSet.t) (x : nat),
NatSet.mem x s = true -> NatSet.inter s (NatSet.singleton x) = NatSet.singleton x.
Proof.
Admitted.



Lemma NatList_filterOutOf_makes_subset : forall (s : NatSet.t) (l : list nat),
    incl (NatList_filterOutOf s l) l.
Proof.
    unfold incl. intros. unfold NatList_filterOutOf in H. apply filter_In in H. firstorder.
Qed.



Lemma NatList_filterOutOf_splits_In : forall (s : NatSet.t) (l : list nat) x,
    In x l -> In x (NatSet.elements s) \/ In x (NatList_filterOutOf s l).
Proof.
    intros. induction l.
    - simpl in H. firstorder.
    - simpl in H. destruct H.
        + subst. simpl. destruct (negb (NatSet.mem x s)) eqn:mem.
            -- right. firstorder.
            -- left. apply Bool.negb_false_iff in mem. apply NatSet.mem_spec in mem. apply NatSet.elements_spec1 in mem.
                apply SetoidList.InA_alt in mem. destruct mem. destruct H. subst. assumption.
        + specialize (IHl H). destruct IHl.
            -- left.  assumption.
            -- right. simpl. destruct (negb (NatSet.mem a s)).
                ++ simpl. right. assumption.
                ++ assumption.
Qed.



 



Lemma consolidation_fold_right_preserves_nodes : forall (l : list (NatSet.t)) y,
    (exists x, In x l /\ NatSet.In y x) <-> (In y (fold_right (fun (next : NatSet.t) (acc : list nat) => NatSet.elements next ++ NatList_filterOutOf next acc) nil l)) .
Proof.
    intros. induction l.
    - simpl. firstorder.
    - split; intros.
        + destruct H. simpl in H. destruct H. destruct H.
            -- subst. simpl. apply in_or_app. left. apply NatSet.elements_spec1 in H0.
                apply SetoidList.InA_alt in H0. destruct H0. destruct H. subst. assumption.
            -- assert (exists x : NatSet.t, In x l /\ NatSet.In y x). { firstorder.
            } destruct IHl. specialize (H2 H1).
              simpl. apply in_or_app. apply NatList_filterOutOf_splits_In. assumption.
        + simpl in H.  apply in_app_or in H.  destruct H.
            -- exists a. split.
                ++ simpl. auto.
                ++ apply NatSet.elements_spec1. apply SetoidList.InA_alt. exists y. auto.
            -- destruct IHl. apply NatList_filterOutOf_makes_subset in H. apply H1 in H. firstorder.
Qed.

Lemma NatSet_In_is_In_elements : forall (s : NatSet.t) (x : nat),
    NatSet.In x s <-> In x (NatSet.elements s).
Proof.
    intros. split; intros.
    - apply NatSet.elements_spec1 in H. apply SetoidList.InA_alt in H. destruct H. destruct H. subst. assumption.
    - apply NatSet.elements_spec1. apply SetoidList.InA_alt. exists x. auto.
Qed.


Lemma In_AG_nodeSet_is_In_RG : forall (ag : AG nat) (x : nat),
    NatSet.In x (AG_nodeSet ag) <-> (AG_to_RG_unlE ag).(RG_nodes) x.
Proof.
Admitted.


Lemma _singleStep_returns_only_nodes : forall (ag : AG nat) (from : NatSet.t),
    forall x, NatSet.In x (_singleStep from ag) -> (AG_to_RG_unlE ag).(RG_nodes) x.
Proof.
    intros. induction ag.
    - simpl in H. apply NatSet_In_is_In_elements in H. simpl in H. destruct H.
    - simpl in H. apply NatSet_In_is_In_elements in H. simpl in H. destruct H.
    - simpl. simpl in H. apply NatSet.union_spec in H. destruct H.
     + left. apply IHag1. assumption.
     + right. apply IHag2. assumption.
     
    - simpl. simpl in H. apply NatSet.union_spec in H. destruct H. 
        + apply NatSet.union_spec in H. destruct H.
            -- left. apply IHag1. assumption.
            -- right. apply IHag2. assumption.
        + destruct (NatSet.is_empty (NatSet.inter (AG_nodeSet ag1) from)) eqn:split.
            -- apply NatSet_In_is_In_elements in H. simpl in H. destruct H.
            -- right. apply In_AG_nodeSet_is_In_RG. assumption.
Qed.

(* Tactic Notation "skip" := admit. *)


Lemma _upToNStepsCap_returns_only_nodes : forall (ag : AG nat) (from s: NatSet.t) (n : nat) x y,
    NatSet.Subset from (AG_nodeSet ag) ->
    In x (_upToNStepsCap_rec from s ag n) -> NatSet.In y x -> (AG_to_RG_unlE ag).(RG_nodes) y.
Proof.
    intros. generalize dependent from. generalize dependent s. induction n.
    - intros. simpl in H. contradiction.
    - intros. simpl in H0. destruct H0.
        + subst. apply In_AG_nodeSet_is_In_RG. unfold NatSet.Subset in H. apply H. assumption.
        + destruct (NatSet.equal s (NatSet.union s (_singleStep from ag))).  
            -- simpl in H0. contradiction.
            -- specialize (IHn (NatSet.union s (_singleStep from ag))  (_singleStep from ag)).
               apply IHn.
               ++ unfold NatSet.Subset. intros.
               apply _singleStep_returns_only_nodes in H2. apply In_AG_nodeSet_is_In_RG. assumption.
               ++ assumption.
Qed.


            
            
Lemma _upToNStepsCapCaller_returns_only_nodes : forall (ag : AG nat) (from : NatSet.t) (n : nat) x y,
    In x (_upToNStepsCap from ag n) -> NatSet.In y x -> (AG_to_RG_unlE ag).(RG_nodes) y.
Proof.
    intros.
    pose proof _upToNStepsCap_returns_only_nodes.
    specialize (H1 ag (NatSet.inter from (AG_nodeSet ag)) (NatSet.inter from (AG_nodeSet ag)) (S n) x).
    apply H1.
    - unfold NatSet.Subset. intros. apply NatSet.inter_spec in H2. destruct H2. assumption.
    - unfold _upToNStepsCap in H. apply H.
    - assumption.
Qed.






Theorem AG_BFS_returns_only_nodes : forall (nodes : list nat) (ag : AG nat),
  forall x, In x (AG_BFS nodes ag) -> (AG_to_RG_unlE ag).(RG_nodes) x. 
Proof.
    intros. unfold AG_BFS in H. apply consolidation_fold_right_preserves_nodes in H.
        destruct H. destruct H.
        apply (_upToNStepsCapCaller_returns_only_nodes _ _ _ _ x) in H.
        + assumption.
        + assumption.
Qed.





(* https://plv.mpi-sws.org/c11comp/coq/extralib.html *)
Definition disjoint {A : Type} (l1 l2 : list A) :=
  forall a, In a l1 /\ In a l2 -> False.  


Lemma nodup_app: forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ disjoint l1 l2.
Proof.
Admitted.


Lemma NatList_filterOutOf_disjoint : forall (s : NatSet.t) (l : list nat),
    disjoint (NatSet.elements s) (NatList_filterOutOf s l).
Proof.
Admitted.


Lemma NoDup_NatSet_elements : forall (s : NatSet.t),
    NoDup (NatSet.elements s).
Proof.
    intros. pose proof (NatSet.elements_spec2w s). induction (NatSet.elements s).
    - apply NoDup_nil.
    - inversion H. apply NoDup_cons.
        + unfold not in *. intros. apply H2. apply SetoidList.InA_alt. exists a. auto.
        + apply IHl. assumption.
Qed.



Lemma NoDup_fold_right_filterOutOf : forall (l : list (NatSet.t)),
    NoDup (fold_right (fun (next : NatSet.t) (acc : list nat) => NatSet.elements next ++ NatList_filterOutOf next acc) nil l).
Proof.
    intros. induction l.
    - simpl. apply NoDup_nil.
    - simpl. apply nodup_app. split.
        + apply NoDup_NatSet_elements.
        + split.
            -- apply NoDup_filter. assumption.
            -- apply NatList_filterOutOf_disjoint.
Qed.





Theorem AG_BFS_no_duplicates : forall (nodes : list nat) (ag : AG nat),
  NoDup (AG_BFS nodes ag).
Proof.
    intros.
    unfold AG_BFS.
    apply NoDup_fold_right_filterOutOf.
Qed.

Theorem AG_BFS_path : forall (nodes : list nat) (ag : AG nat) x y,
  In x nodes -> (In y (AG_BFS nodes ag) <-> RG_existsPath x y (AG_to_RG_unlE ag)).
Proof.
  intros.
Admitted.

Import ListNotations.

(* 
Inductive Is_BFS_ordered {A : Type} : list A -> Prop :=
  | Is_BFS_ordered_nil : Is_BFS_ordered []
  | Is_BFS_ordered_cons : forall (a : A) (l : list A), Is_BFS_ordered l -> Is_BFS_ordered (a :: l). *)


(* Is, in general the search ordered in some single step manner? *)
Fixpoint Is_Search_ordered_helper {A B : Type} (l passed : list A) (rg : RG A B) : Prop :=
  match l with
  | [] => True
  | x :: xs => RG_reachableInOneStep (fun x => In x passed) x rg /\ Is_Search_ordered_helper xs (x :: passed) rg
  end.


Fixpoint trim {A : Type} (l passed : list A) : list A :=
  match l, passed with
  | le::ls, pe::ps => trim ls ps
  | ls, [] => ls
  | _, _ => nil
  end.

Fixpoint doesMatch {A : Type} (l passed : list A) : Prop :=
  match l, passed with
  | le::ls, pe::ps => le = pe /\ doesMatch ls ps
  | _, [] => True
  | _, _ => False
  end.

Definition Is_Search_ordered {A B : Type} (l passed : list A) (rg : RG A B) : Prop :=
   let trimmedL := trim l passed in
   let didMatch := doesMatch l passed in
   didMatch /\ Is_Search_ordered_helper trimmedL passed rg. 


Theorem AG_BFS_search_order : forall (nodes : list nat) (ag : AG nat),
    Is_Search_ordered (AG_BFS nodes ag) nodes (AG_to_RG_unlE ag).
Proof.
Admitted.




Require Import Coq.Sorting.Permutation.


(* Now, the specification of a BFS search order: *)



Require Import Coq.Sets.Ensembles.


Inductive sameDistance {A B : Type} (rg : RG A B) : Ensemble A -> Ensemble A -> A -> A -> Prop :=
    | bothInStart (start1 start2 : Ensemble A) : forall (a1 a2 : A), start1 a1 -> start2 a2 -> sameDistance rg start1 start2 a1 a2
    | bothOneStep (start1 start2 : Ensemble A) : forall (a1 a2 : A),
        sameDistance rg (fun x => RG_reachableInOneStep start1 x rg) (fun x => RG_reachableInOneStep start2 x rg) a1 a2
        -> sameDistance rg start1 start2 a1 a2 
. 

Definition sameDistanceCaller {A B : Type} (rg : RG A B) (start : Ensemble A) (a1 a2 : A) : Prop :=
    sameDistance rg start start a1 a2.

Lemma sameDistance_caller_test1 : sameDistanceCaller (AG_to_RG_unlE (1 *** 2 +++ 1 *** 3)) (fun x => NatSet.In x (NatSet.singleton 1)) 2 3.
Proof.
    unfold sameDistanceCaller.
    apply bothOneStep.
    apply bothInStart.
    - simpl. unfold RG_reachableInOneStep. exists 1, tt. firstorder. apply SProps.MP.FM.singleton_iff. reflexivity.
 
    - simpl. unfold RG_reachableInOneStep. exists 1, tt. firstorder. apply SProps.MP.FM.singleton_iff. reflexivity.
Qed.


(* Returns true, if the distance from a1 to start is one plus the distance from a2 to start *)
Definition distanceSecondOneLower {A B : Type} (rg : RG A B) (start : Ensemble A) (a1 a2 : A) : Prop :=
    sameDistance rg (fun x => RG_reachableInOneStep start x rg) start a1 a2.

    
Lemma distanceSecondOneLower_test1 : distanceSecondOneLower (AG_to_RG_unlE (1 *** 2 +++ 1 *** 3 +++ 3 *** 4)) (fun x => NatSet.In x (NatSet.singleton 1)) 4 2.
Proof.
    unfold distanceSecondOneLower.
    apply bothOneStep.
    apply bothInStart.
    - simpl. unfold RG_reachableInOneStep. exists 3, tt. firstorder. exists 1, tt. firstorder. apply SProps.MP.FM.singleton_iff. reflexivity. 
    - simpl. unfold RG_reachableInOneStep. exists 1, tt. firstorder. apply SProps.MP.FM.singleton_iff. reflexivity.
Qed.





Inductive revBFSOrder (start : NatSet.t) (ag : AG nat) : list nat -> Prop :=
  | revBFSOrder_start (l : list nat) : Permutation (NatSet.elements start) l -> revBFSOrder start ag l

  | revBFSOrder_same (noww next : nat) (l : list nat) :
    sameDistanceCaller (AG_to_RG_unlE ag) (fun x => NatSet.In x start) noww next -> revBFSOrder start ag (next :: l) -> revBFSOrder start ag (noww :: next :: l)   

  | revBFSOrder_next (noww next : nat) (l : list nat) :
    distanceSecondOneLower (AG_to_RG_unlE ag) (fun x => NatSet.In x start) noww next 
    -> revBFSOrder start ag (next :: l) -> revBFSOrder start ag (noww :: next :: l).



Lemma revBFSOrder_test1 : revBFSOrder (NatSet.singleton 1) (1 *** 2 +++ 3 *** 4) [1; 2; 3; 4].
Proof.
Admitted.






(* Here some things about "Transpose:" *)

Theorem AG_transpose_is_RG : forall (ag : AG nat),
    AG_to_RG_unlE (transpose ag) === RG_transpose (AG_to_RG_unlE ag). 
Proof.
    intros. induction ag; simpl; firstorder.
Qed.
    

