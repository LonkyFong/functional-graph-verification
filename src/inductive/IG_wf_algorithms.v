Require Import Coq.Arith.Arith.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Relations.Relation_Operators.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import GraphVerification.src.util.NatMap.

Require Import GraphVerification.src.inductive.IG.
Require Import GraphVerification.src.inductive.IG_wf.


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

(* Convert dependent pair to an ordinary product, since that is more user-friendly *)
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
    (* Case 1: graph gets smaller *)
    - break_up_lexord.
        apply _IG_match_decreases_IG_noNodes in teq2.
        apply left_lex. auto.
    (* Case 2: stack gets smaller *)
    - break_up_lexord.
        apply IG_match_none_returns_graph in teq2. subst.
        apply right_lex. auto.
    (* lexord_arg_pair_s is indeed well-founded *) 
    - exact wf_lexord_arg_pair_s.
Defined.


(* Caller for user-friendliness *)
Definition IG_DFS {A B : Type} (nodes : list Node) (ig : IG A B) : list Node :=
    IG_DFS_rec A B (ig, nodes).






(* Other typical functional operations (leading to transpose) *)

Function IG_ufold {A B C : Type} (f : Context A B -> C -> C) (acc : C) (ig : IG A B) {measure IG_noNodes ig} : C :=
    match IG_matchAny ig with
    | (Some c, rest) => f c (IG_ufold f acc rest)
    | (None, rest) => acc
    end.
Proof.
    intros. apply _IG_matchAny_decreases_IG_noNodes in teq. assumption.
Defined.


(* This is the direct way of writing gmap, but it can also be done in terms of ufold *)
Function IG_gmap_diy {A B C D : Type} (f : Context A B -> Context C D) (ig : IG A B) {measure IG_noNodes ig} : IG C D :=
    match IG_matchAny ig with
    | (Some c, rest) => IG_and (f c) (IG_gmap_diy f rest)
    | (None, rest) => IG_empty
    end.
Proof.
    intros. apply _IG_matchAny_decreases_IG_noNodes in teq. assumption.
Defined.


Definition IG_gmap {A B C D : Type} (f : Context A B -> Context C D) (ig : IG A B) : IG C D :=
    IG_ufold _ _ (IG C D) (fun (c : Context A B) (acc : IG C D) => IG_and (f c) acc) IG_empty ig.


Definition _transposeContext {A B : Type} (c : Context A B) : Context A B :=
    let '(froms, node, label, tos) := c in
    (tos, node, label, froms). 

  
Definition IG_transpose {A B : Type} (ig : IG A B) : IG A B :=
    IG_gmap _transposeContext ig.

