Require Import Bool.
Require Import Ensembles.
Require Import Lia.
Require Import Arith.
Require Import List.
Import ListNotations.


(** Defines miscellaneous utilities useful across the project  *)


(* Custom additional functions for Ensembles. Standard library equivalents may exist,
    but they are less transparent and more difficult to work with *)
Definition Ensemble_add {A : Type} (a : A) (en : Ensemble A) : Ensemble A :=
    fun (x : A) => x = a \/ en x.

Definition Ensemble_union {A : Type} (en1 en2 : Ensemble A) : Ensemble A :=
    fun (a : A) => en1 a \/ en2 a.



(* Leads to define "bdestruct", a useful tactic from
    Software Foundations, Volume 3: Verified Functional Algorithms, Chapter Perm *)
Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
    intros x y. apply iff_reflect. symmetry.
    apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
    intros x y. apply iff_reflect. symmetry.
    apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
    intros x y. apply iff_reflect. symmetry.
    apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
    let H := fresh in let e := fresh "e" in
        evar (e: Prop);
        assert (H: reflect e X); subst e;
        [ auto with bdestruct
        | destruct H as [H|H];
            [ | try first [apply not_lt in H | apply not_le in H]]
        ].




        
(* "bdestruct_guard_in_hyp" and "bdall_in_hyp" are adapted versions of "bdestruct_guard" and "bdall" from
    Software Foundations, Volume 3: Verified Functional Algorithms, Chapter SearchTree *)
Ltac bdestruct_guard_in_hyp :=
    match goal with
    | H: context [ if Nat.eqb ?X ?Y then _ else _ ] |- _ => bdestruct (Nat.eqb X Y)
    | H: context [ if Nat.ltb ?X ?Y then _ else _ ] |- _ => bdestruct (Nat.ltb X Y)
    | H: context [ if Nat.leb ?X ?Y then _ else _ ] |- _ => bdestruct (Nat.leb X Y)

    | H: context [ if negb (Nat.eqb ?X ?Y) then _ else _ ] |- _ => bdestruct (Nat.eqb X Y)
    | H: context [ if negb (Nat.ltb ?X ?Y) then _ else _ ] |- _ => bdestruct (Nat.ltb X Y)
    | H: context [ if negb (Nat.leb ?X ?Y) then _ else _ ] |- _ => bdestruct (Nat.leb X Y)
end.

Ltac bdall_in_hyp :=
    repeat (bdestruct_guard_in_hyp; simpl in *; try lia; auto).





(* Defining the notion of disjointedness and what it means with respect to NoDup *)
Definition disjoint {A : Type} (l1 l2 : list A) :=
    forall a, In a l1 /\ In a l2 -> False.  


Lemma nodup_app: forall (A: Type) (l1 l2: list A),
    NoDup (l1 ++ l2) <->
    NoDup l1 /\ NoDup l2 /\ disjoint l1 l2.
Proof.
    intros. unfold disjoint. induction l1; simpl.
    - firstorder. apply NoDup_nil.
    - split; intros.
        + inversion H. apply IHl1 in H3. destruct H3 as [H30 [H31 H32]].
            split.
            -- apply NoDup_cons.
                ++ unfold not. intros. unfold not in H2. apply H2. apply in_or_app. firstorder.
                ++ assumption.
            -- split.
                ++ assumption.
                ++ subst. intros. unfold not in H2. apply H2.
                    simpl in *. destruct H0. apply in_or_app. destruct H0.
                    --- subst. auto.
                    --- firstorder.
        + destruct H. destruct H0. inversion H. apply NoDup_cons.
            -- subst. unfold not. intros.
                apply in_app_or in H2. apply (H1 a). firstorder.
            -- apply IHl1. firstorder.
Qed.



(* A basic amortized O(1) queue implementation to be potentially used in BFS.
    It is not used yet. *)
Definition Queue (A : Type) : Type :=
    (list A) * (list A).

Definition emptyQueue {A : Type} : Queue A := ([], []).

Definition enqueue {A : Type} (a : A) (q : Queue A) : Queue A :=
    match q with
    | (q1, q2) => (a :: q1, q2)
    end.

Definition removeFirst {A : Type} (l : list A) : list A :=
    match l with
    | [] => []
    | a::l => l
    end.

Definition dequeue {A : Type} (q : Queue A) : (option A) * Queue A :=
    match q with
    | ([], []) => (None, q)
    | (a1::q1, []) => (Some (last (a1::q1) a1), ([], removeFirst (rev (a1::q1))))
    | (q1, a2::q2) => (Some a2, (q1, q2))
    end.
