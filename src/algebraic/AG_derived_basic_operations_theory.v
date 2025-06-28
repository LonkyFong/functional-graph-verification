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








(* Todo: clean this up *)


(* Showing some experimental properties about AGs *)


(* Initially functions from the paper *)

(* Definition AG_edge {A : Type} (a1 a2 : A) : AG A :=
    (AG_vertex a1) *** (AG_vertex a2). *)



Check AG_edge.
Definition AG_edge {A : Type} (a1 a2 : A) : AG A :=
    (AG_vertex a1) *** (AG_vertex a2).

Definition RG_edge {A : Type} (a1 a2 : A) : RG A unit :=
    RG_addEdge a1 a2 tt RG_empty.

Lemma AG_edge_relates : forall (A : Type) (a1 a2 : A),
    RG_edge a1 a2 ==R AG_to_RG (AG_edge a1 a2).
Proof.
    intros. unfold AG_edge. unfold AG_to_RG. firstorder.
    - subst. firstorder.
    - destruct b. firstorder.
Qed.



Definition AG_vertices {A : Type} (l : list A) : AG A :=
    fold_right AG_overlay AG_empty (map AG_vertex l).

Definition RG_vertices {A : Type} (l : list A) : RG A unit :=
    fold_right RG_addNode RG_empty l.

Lemma AG_vertices_relates : forall (A : Type) (l : list A),
    RG_vertices l ==R AG_to_RG (AG_vertices l).
Proof.
    intros. induction l.
    - firstorder.
    - unfold AG_vertices in *. simpl in *. firstorder.
Qed.



Definition AG_edges {A : Type} (l : list (A * A)) : AG A :=
    fold_right AG_overlay AG_empty (map (fun x => AG_edge (fst x) (snd x)) l).

Definition RG_edgez {A : Type} (l : list (A * A)) : RG A unit :=
    fold_right RG_overlay RG_empty (map (fun x => RG_edge (fst x) (snd x)) l).



    
Ltac Proper_proof_automation := split; simpl in *; firstorder.

Instance Proper_overlay {A : Type} : Proper ((@RG_equiv A unit) ==> RG_equiv ==> RG_equiv) RG_overlay.
Proof.
    Proper_proof_automation.
Qed.

Instance Proper_connect {A : Type} : Proper ((@RG_equiv A unit) ==> RG_equiv ==> RG_equiv) RG_connect. 
Proof.
    Proper_proof_automation.
Qed.




Lemma AG_edges_relates : forall (A : Type) (l : list (A * A)),
    RG_edgez l ==R AG_to_RG (AG_edges l).
Proof.
    intros. induction l.
    - firstorder.
    - destruct a. unfold AG_edges in *. simpl in *.
        unfold RG_edgez. simpl.
        rewrite <- IHl.
        rewrite AG_edge_relates.
        reflexivity.
Qed.
    




Definition AG_clique {A : Type} (l : list A) : AG A :=
    fold_right AG_connect AG_empty (map AG_vertex l).

Definition RG_clique {A : Type} (l : list A) : RG A unit :=
    fold_right RG_connect RG_empty (map RG_vertex l).

Lemma AG_clique_relates : forall (A : Type) (l : list A),
    RG_clique l ==R AG_to_RG (AG_clique l).
Proof.
    intros. induction l.
    - firstorder.
    - unfold AG_clique in *. simpl in *. firstorder.
Qed.




Definition AG_makeGraph {A : Type} (vs : list A) (es : list (A * A)) : AG A :=
    (AG_vertices vs) +++ (AG_edges es).

Definition RG_makeGraph {A : Type} (vs : list A) (es : list (A * A)) : RG A unit :=
    RG_overlay (RG_vertices vs) (RG_edgez es).

Lemma AG_makeGraph_relates : forall (A : Type) (vs : list A) (es : list (A * A)),
    RG_makeGraph vs es ==R AG_to_RG (AG_makeGraph vs es).
Proof.
    intros. unfold AG_makeGraph.
    unfold RG_makeGraph.
    rewrite AG_vertices_relates.
    rewrite AG_edges_relates.
    reflexivity.
Qed.
    


Definition AG_path {A : Type} (l : list A) : AG A :=
    match l with
    | [] => AG_empty
    | [x] => AG_vertex x
    | _::xs => AG_edges (combine l xs)
    end.

Definition RG_path {A : Type} (l : list A) : RG A unit :=
    match l with
    | [] => RG_empty
    | [x] => RG_vertex x
    | _::xs => RG_edgez (combine l xs)
    end.

Lemma AG_path_relates : forall (A : Type) (l : list A),
    RG_path l ==R AG_to_RG (AG_path l).
Proof.
    intros. destruct l.
    - firstorder.
    - simpl. destruct l.
        + firstorder.
        + simpl. rewrite AG_edges_relates. reflexivity.
Qed.


Definition AG_circuit {A : Type} (l : list A) : AG A :=
    match l with
    | [] => AG_empty
    | x::_ => AG_path (l ++ [x])
    end.

Definition RG_circuit {A : Type} (l : list A) : RG A unit :=
    match l with
    | [] => RG_empty
    | x::_ => RG_path (l ++ [x])
    end.

Lemma AG_circuit_relates : forall (A : Type) (l : list A),
    RG_circuit l ==R AG_to_RG (AG_circuit l).   
Proof.
    intros. destruct l.
    - firstorder.
    - unfold RG_circuit. unfold AG_circuit. rewrite AG_path_relates. reflexivity.
Qed.



Definition AG_star {A : Type} (x : A) (l : list A) : AG A :=
    AG_vertex x *** AG_vertices l.

Definition RG_star {A : Type} (x : A) (l : list A) : RG A unit :=
    RG_connect (RG_vertex x) (RG_vertices l).




Lemma AG_star_relates : forall (A : Type) (x : A) (l : list A),
    RG_star x l ==R AG_to_RG (AG_star x l).
Proof.
    intros. unfold RG_star. rewrite AG_vertices_relates. reflexivity.
Qed.






Fixpoint AG_gmap {A A' : Type} (f : A -> A') (ag : AG A) : AG A' := 
    match ag with
    | AG_empty => AG_empty
    | AG_vertex x => AG_vertex (f x)
    | ag1 +++ ag2 => AG_gmap f ag1 +++ AG_gmap f ag2
    | ag1 *** ag2 => AG_gmap f ag1 *** AG_gmap f ag2
    end.


Definition RG_gmap {A A' : Type} (f : A -> A') (rg : RG_unlE A) : RG_unlE A'. 
Proof.
    refine {|
        RG_nodes := fun a => exists n, rg.(RG_nodes) n /\ f n = a;
        RG_edges := fun a1 a2 l => exists n1 n2, rg.(RG_edges) n1 n2 l /\ f n1 = a1 /\ f n2 = a2;
        RG_valid := _
    |}.
    RG_valid_prover rg.
    - subst. exists x. firstorder.
    - subst. exists x0. firstorder.
Defined.

Lemma AG_gmap_relates : forall (A A' : Type) (f : A -> A') (ag : AG A),
    RG_gmap f (AG_to_RG ag) ==R AG_to_RG (AG_gmap f ag).
Proof.
    intros. induction ag.
    - firstorder.
    - compute. firstorder. subst. reflexivity.
    - simpl. rewrite <- IHag1. rewrite <- IHag2. clear. firstorder.
    - simpl. rewrite <- IHag1. rewrite <- IHag2. clear. firstorder.
Qed.






Definition AG_mergeVertices {A : Type} (f : A -> bool) (v : A) (ag : AG A) : AG A :=
    AG_gmap (fun x => if f x then v else x) ag.

Definition RG_mergeVertices {A : Type} (f : A -> bool) (v : A) (rg : RG_unlE A) : RG_unlE A :=
    RG_gmap (fun x => if f x then v else x) rg.

Lemma AG_mergeVertices_relates : forall (A : Type) (f : A -> bool) (v : A) (ag : AG A),
    RG_mergeVertices f v (AG_to_RG ag) ==R AG_to_RG (AG_mergeVertices f v ag).
Proof.
    intros. unfold AG_mergeVertices. rewrite <- AG_gmap_relates. reflexivity.
Qed.



Fixpoint AG_toList {A : Type} (ag : AG A) : list A :=
    match ag with
    | AG_empty => []
    | AG_vertex x => [x]
    | ag1 +++ ag2 => AG_toList ag1 ++ AG_toList ag2
    | ag1 *** ag2 => AG_toList ag1 ++ AG_toList ag2
    end.

Definition RG_toList {A : Type} (rg : RG_unlE A) : Ensemble A :=
    rg.(RG_nodes).

Lemma AG_toList_relates : forall (A : Type) (ag : AG A),
    forall x, (AG_to_RG ag).(RG_nodes) x <-> In x (AG_toList ag).
Proof.
    intros. induction ag; simpl.
    - firstorder.
    - firstorder.
    - rewrite IHag1. rewrite IHag2. clear. rewrite in_app_iff. firstorder.
    - rewrite IHag1. rewrite IHag2. clear. rewrite in_app_iff. firstorder.
Qed.



(* TODO: this one is different, since we changed the function *)
Fixpoint AG_gmapVertex {A A' : Type} (f : A -> AG A') (ag : AG A) : AG A' :=
    match ag with
    | AG_empty => AG_empty
    | AG_vertex x => f x
    | ag1 +++ ag2 => AG_gmapVertex f ag1 +++ AG_gmapVertex f ag2
    | ag1 *** ag2 => AG_gmapVertex f ag1 *** AG_gmapVertex f ag2
    end.


(* This function is not super suitable to this kind of verification, since one still passes in a function from AG to AG, since other *)
Definition RG_gmapVertex {A A' : Type} (f : A -> RG_unlE A') (rg : RG_unlE A) : RG_unlE A'.
Proof.
    refine {|
        RG_nodes := fun (a : A') => exists n, rg.(RG_nodes) n /\ (f n).(RG_nodes) a;
        RG_edges := fun a1 a2 l => (exists n1 n2, rg.(RG_edges) n1 n2 l
                                    /\ (f n1).(RG_nodes) a1
                                    /\ (f n2).(RG_nodes) a2)
                                    \/ (exists n, rg.(RG_nodes) n
                                        /\ (f n).(RG_edges) a1 a2 l) 
                                    ;
        RG_valid := _
    |}.
    RG_valid_prover rg.
    - exists x. firstorder.
    - exists x. firstorder. RG_valid_prover (f x).
    - exists x0. firstorder.
    - exists x. firstorder. RG_valid_prover (f x).
Defined.






Lemma AG_gmapVertex_relates : forall (A A' : Type) (f : A -> AG A') (ag : AG A),
    RG_gmapVertex (fun a => AG_to_RG (f a)) (AG_to_RG ag) ==R AG_to_RG (AG_gmapVertex f ag).
Proof.
    intros. induction ag; simpl.
    - firstorder.
    - firstorder.
        + simpl in H. subst. firstorder.
        + simpl in H. subst. firstorder.
    - rewrite <- IHag1. rewrite <- IHag2. clear. firstorder.
    - rewrite <- IHag1. rewrite <- IHag2. clear. firstorder.
Qed.






Definition AG_induce {A : Type} (f : A -> bool) (ag : AG A) : AG A :=
    AG_gmapVertex (fun a => if f a then AG_vertex a else AG_empty) ag.

Definition RG_induce {A : Type} (f : A -> bool) (rg : RG_unlE A) : RG_unlE A :=
    RG_gmapVertex (fun a => if f a then RG_vertex a else RG_empty) rg.


Require Import FunctionalExtensionality.

Lemma AG_induce_relates : forall (A : Type) (f : A -> bool) (ag : AG A),
    RG_induce f (AG_to_RG ag) ==R AG_to_RG (AG_induce f ag).
Proof.
    intros. unfold AG_induce. rewrite <- AG_gmapVertex_relates. unfold RG_induce.
    assert ((fun a : A => if f a then RG_vertex a else RG_empty) = (fun a : A => AG_to_RG
(if f a then AG_vertex a else AG_empty))). {
        intros. apply functional_extensionality. intros. destruct (f x).
        - reflexivity.
        - reflexivity.
    }
    rewrite H. clear H.
    reflexivity.
Qed.
        






Definition AG_removeVertex (x : nat) (ag : AG nat) : AG nat :=
    AG_induce (fun y => negb (Nat.eqb x y)) ag.

Definition RG_removeVertex (x : nat) (rg : RG_unlE nat) : RG_unlE nat :=
    RG_induce (fun y => negb (Nat.eqb x y)) rg.

Lemma AG_removeVertex_relates : forall (ag : AG nat) (x : nat),
    RG_removeVertex x (AG_to_RG ag) ==R AG_to_RG (AG_removeVertex x ag).
Proof.
    intros. unfold AG_removeVertex. unfold RG_removeVertex. rewrite <- AG_induce_relates. reflexivity.
Qed.



(* This one, I skipped *)
Definition AG_splitVertex {A : Type} (x : nat) (l : list nat) (ag : AG nat) : AG nat :=
    AG_gmapVertex (fun y => if Nat.eqb x y then AG_vertices l else AG_vertex y) ag.




Fixpoint AG_removeEdge (x y : nat) (ag : AG nat) : AG nat :=
    match ag with
    | AG_empty => AG_empty
    | AG_vertex z => AG_vertex z
    | ag1 +++ ag2 => AG_removeEdge x y ag1 +++ AG_removeEdge x y ag2
    | ag1 *** ag2 => ((AG_removeVertex x ag1) *** (AG_removeEdge x y ag2)) +++ ((AG_removeEdge x y ag1) *** (AG_removeVertex y ag2))
    end.

(* Copied from RG.v *)
Definition RG_removeEdge {A B : Type} (from to : A) (label : B) (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := rg.(RG_nodes);
        RG_edges := fun a1 a2 l => not (a1 = from /\ a2 = to /\ l = label)
                                    /\ rg.(RG_edges) a1 a2 l;
        RG_valid := _
    |}.
    RG_valid_prover rg.
Defined.

Require Import GraphVerification.src.util.util.
Require Import Arith.
Require Import Bool.
Require Import Lia.


(* TODO: this can go to util.v *)

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
    repeat (simpl; bdestruct_guard_in_hyp; try lia; auto).


Ltac AG_removeEdge_relates_prover := firstorder; try ((bdall_in_hyp; firstorder); try (simpl in *; subst; firstorder) ).



(* This is quite a big archivevent *)
Lemma AG_removeEdge_relates : forall (ag : AG nat) (x y : nat),
    RG_removeEdge x y tt (AG_to_RG ag) ==R AG_to_RG (AG_removeEdge x y ag).
Proof.
    intros. induction ag.
    - firstorder.
    - firstorder.
    - simpl. rewrite <- IHag1. rewrite <- IHag2. clear. firstorder.
    - simpl. rewrite <- IHag1. rewrite <- IHag2. clear. rewrite <- !AG_removeVertex_relates.
        AG_removeEdge_relates_prover.
        destruct b. simpl. bdestruct (a1 =? x).
        + subst. bdestruct (a2 =? y).
            -- subst. firstorder.
            -- firstorder. right. right. firstorder. exists a2. firstorder.
                assert (negb (y =? a2) = true). {
                    bdestruct (y =? a2).
                    - firstorder.
                    - firstorder.
                }
                rewrite H3. firstorder.
        + left. right. firstorder. exists a1. firstorder.
            assert (negb (x =? a1) = true). {
                bdestruct (x =? a1).
                - firstorder.
                - firstorder.
            }
            rewrite H3. firstorder.
Qed.









