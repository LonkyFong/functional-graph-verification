Require Import Recdef.
Require Import Lia.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.

Import ListNotations.

Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Relations.Relation_Operators.

Require Import GraphVerification.src.inductive.inductive_graph_measure.
Require Import GraphVerification.src.util.NatMap.

Require Import GraphVerification.src.inductive.inductive_graph.

(* Defining operations on an IG that depend on well-founded recursion for their termination.
They require the Theorems about IG_noNodes etc. from inductive_graph_measure.
At the moment, has DFS and transpose *) 


Definition suc {A B : Type} (c : Context A B) : list Node :=
    let '(_, _, _, tos) := c in map snd tos.


(* Defining the argument pair to be used in the DFS. It starts as a dependent pair, since lexprod expects this *)
Definition dep_arg_pair_s (A B : Type) := {_ : IG A B & list Node}. 

Definition lexord_dep_arg_pair_s (A B : Type) :=
    lexprod (IG A B)
            (fun a => list Node)
            (fun ig1 ig2 => Peano.lt (IG_noNodes ig1) (IG_noNodes ig2))
            (fun a => fun l1 l2 => Peano.lt (length l1) (length l2)).

(* Prove lexicographic order is well-founded *)
Lemma wf_lexord_dep_arg_pair_s (A B : Type) : well_founded (lexord_dep_arg_pair_s A B).
Proof.
    apply wf_lexprod.
    - apply well_founded_ltof. 
    - intros. apply well_founded_ltof.
Qed.

Definition prodTo_dep_arg_pair_s {A B : Type} (p : IG A B * list Node) : dep_arg_pair_s A B := 
    existT _ (fst p) (snd p).

Definition lexord_arg_pair_s (A B : Type) (igNodes1 igNodes2 : IG A B * list Node) : Prop :=  
    lexord_dep_arg_pair_s _ _ (prodTo_dep_arg_pair_s igNodes1) (prodTo_dep_arg_pair_s igNodes2).


(* Prove lexicographic order is well-founded *)
Lemma wf_lexord_arg_pair_s (A B : Type) : well_founded (lexord_arg_pair_s A B).
Proof.
    unfold lexord_arg_pair_s.
    pose proof (wf_lexord_dep_arg_pair_s A B).
    pose proof (wf_inverse_image (IG A B * list Node) _ (lexord_dep_arg_pair_s A B)).

    apply (H0 (@prodTo_dep_arg_pair_s A B)) in H.
    assumption.
Qed.

Ltac break_up_lexord := intros;
                            unfold lexord_arg_pair_s;
                            unfold lexord_dep_arg_pair_s;
                            unfold prodTo_dep_arg_pair_s;
                            simpl.





Function IG_DFS_rec {A B : Type} (igNodes : IG A B * list Node) {wf (lexord_arg_pair_s A B) igNodes} : list Node := 
    let '(ig, nodes) := igNodes in
        match nodes with
        | [] => []
        | n :: ns => if IG_isEmpty ig then [] else
                    match IG_match n ig with
                    | (Some cntxt, rest) => n :: IG_DFS_rec (rest, (suc cntxt ++ ns))
                    | (None, same) => IG_DFS_rec (same, ns)
                    end
  end.
Proof.
    - break_up_lexord.
        apply _IG_match_decreases_IG_noNodes in teq2.
        apply left_lex. auto.
    - break_up_lexord.
        apply IG_match_none_returns_graph in teq2. subst.
        apply right_lex. auto.

    - exact wf_lexord_arg_pair_s.
Defined.






Definition IG_DFS {A B : Type} (nodes : list Node) (ig : IG A B) : list Node :=
    IG_DFS_rec A B (ig, nodes).

Ltac IG_DFS_computer := unfold IG_DFS; repeat (rewrite IG_DFS_rec_equation; simpl).




































(* Demo queue implementation to allow for BFS: *)
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


(* Test the implementation *)
Compute dequeue (enqueue 1 (enqueue 2 (enqueue 3 (emptyQueue)))).
Compute dequeue (emptyQueue).
Compute dequeue (enqueue 1 (emptyQueue)).
Compute dequeue (enqueue 1 (enqueue 2 (emptyQueue))).












































(* Transpose: *)

(* TODO: this remination proof becomes basically trivial, once the project is refactored, and there is access to _nodeAmount and its < *)
Function IG_ufold {A B C : Type} (f : Context A B -> C -> C) (acc : C) (ig : IG A B) {measure NatMap.cardinal ig} : C :=
  match IG_matchAny ig with
    | (Some c, rest) => f c (IG_ufold f acc rest)
    | (None, rest) => acc
  end
.
Proof.
Admitted.

Function IG_gmap_diy {A B C D : Type} (f : Context A B -> Context C D) (ig : IG A B) {measure NatMap.cardinal ig} : IG C D :=
  match IG_matchAny ig with
    | (Some c, rest) => IG_and (f c) (IG_gmap_diy f rest)
    | (None, rest) => IG_gmap_diy f rest
  end
.
Proof.
Admitted.


Definition IG_gmap {A B C D : Type} (f : Context A B -> Context C D) (ig : IG A B) : IG C D :=
  IG_ufold _ _ (IG C D) (fun (c : Context A B) (acc : IG C D) => IG_and (f c) acc) IG_empty ig.

Definition _transposeContext {A B : Type} (c : Context A B) : Context A B :=
  let '(froms, node, l, tos) := c in (tos, node, l, froms). 

  
Definition IG_grev {A B : Type} (ig : IG A B) : IG A B :=
  IG_gmap _transposeContext ig
.



