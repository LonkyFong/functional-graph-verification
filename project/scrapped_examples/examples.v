Require Import Coq.Sets.Ensembles.

Require Import MyProject.project.relational_graph.

(* Mini examples, I had in other files but I moved here for cleanness *)

(* Definition Powerset : Type -> Type :=
    fun X => X -> Prop. *)

Definition my_Finite_Type : (Ensemble nat) := 
    fun X => (X = 0) \/ (X = 1) \/ (X = 2) .


Definition my_Basic_Graph : RG nat.
Proof.
  refine ({|
    RG_nodes := my_Finite_Type;
    RG_edges := (fun (A B : nat) => ((A = 0) /\ (B = 1)) \/ 
                                    ((A = 1) /\ (B = 2)));
    RG_valid := _
  |}).
  unfold valid_cond. intros. split; unfold my_Finite_Type.
  - destruct H.
    + left. apply H.
    + right. left. apply H. 
  - destruct H.
    + right. left. apply H.
    + right. right. apply H.
Defined.


Print my_Basic_Graph.

Compute my_Basic_Graph.(RG_nodes).
Compute my_Basic_Graph.(RG_edges).

(* 0 -> 1 -> 2 *)

Example RG_existsPath_example : RG_existsPath 0 1 my_Basic_Graph.
Proof.
    compute. apply t_step. auto.
Qed.

(* 0 -> 1 -> 2 *)
Example RG_existsPath_example' : RG_existsPath 0 2 my_Basic_Graph.
Proof.
    compute. apply (t_trans _ _ _ 1).
    - apply t_step. auto.
    - apply t_step. auto.
Qed.
