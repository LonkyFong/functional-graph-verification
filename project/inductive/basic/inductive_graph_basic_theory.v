Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import MyProject.project.inductive.basic.inductive_graph_basic.
Require Import MyProject.project.relational_graph.

Require Import Coq.Sets.Ensembles.


(* Defining Conversion from basic Inductive Graph to Relational Graph *)

(* This works better in proofs than the library Add for ensembles *)
Definition _customEnsembleAdd {A : Type} (a : A) (en : Ensemble A) : Ensemble A :=
  fun (x : A) => x = a \/ en x
.

Definition _listToEnsemble {A : Type} (az : list A) : Ensemble A :=
  fold_right _customEnsembleAdd (Empty_set A) az
.


(* Adds a node and its in- and out- going edges (= its IG context) to an RG.
    Assumes that the neighboring nodes exist *)
Definition _extendByContext (node : Node) (froms tos : NatSet.t) (rg : RG nat) : RG nat.
Proof.
    refine {|
        RG_nodes := fun (n : nat) => NatSet.In n froms \/ NatSet.In n tos \/ (_customEnsembleAdd node rg.(RG_nodes))  n;
        RG_edges := fun (n0 n1 : nat) =>
                                (NatSet.In n0 froms /\ n1 = node)
                                \/ (n0 = node /\ NatSet.In n1 tos)
                                \/ rg.(RG_edges) n0 n1
                                ;
                     
        RG_valid := _
    |}.
    unfold valid_cond. pose proof rg.(RG_valid). firstorder.
Defined.




Definition _accTo_RG (node : Node) (rgIg : RG nat * IG) : RG nat * IG :=
    match rgIg with | (rg, ig) =>
        match matsh node ig with
        | (Some (froms, tos), rest) => (_extendByContext node froms tos rg, rest)
        | (None, sameIg)            => (rg, sameIg)
        end
    end
.

Definition IG_basic_to_RG (ig : IG) : RG nat :=
    match fold_right _accTo_RG (RG_empty, ig) (labNodes ig) with
    | (rg, acc) => rg
    end
.


(* Coercion IG_basic_to_RG : IG >-> RG. *)

Definition IG_equiv (ig1 ig2 : IG) : Prop :=
    RG_equiv (IG_basic_to_RG ig1) (IG_basic_to_RG ig2)
.

Notation "g1 I== g2" := (IG_equiv g1 g2) (at level 80).


(* Section to make rewrite work with IG_equiv *)

(* Source for rewrite: https://stackoverflow.com/questions/56099646/use-rewrite-tactic-with-my-own-operator-in-coq *)
Require Import Setoid Morphisms.

(* This proof is based on === being an equivalence relation *)
Instance IG_Equivalence_eq : Equivalence IG_equiv.
Proof.
    pose proof (@RG_Equivalence_eq nat). destruct H. split.
    - unfold Reflexive. intros. unfold Reflexive in Equivalence_Reflexive. apply Equivalence_Reflexive.
    - unfold Symmetric. intros. unfold Symmetric in Equivalence_Symmetric. apply Equivalence_Symmetric. apply H.
    - unfold Transitive. intros. unfold Transitive in Equivalence_Transitive. apply (Equivalence_Transitive _ (IG_basic_to_RG y) _).
        + apply H.
        + apply H0.
Qed. 


Example basic_equivalence_test : (mkGraph [1; 2] []) I== (mkGraph [2; 1] []).
Proof.
    unfold IG_equiv. unfold RG_equiv. firstorder.
Qed.

Example basic_equivalence_test' : (mkGraph [1; 2; 3] [(1, 2); (2, 3)]) I== (mkGraph [2; 1; 3] [(2, 3); (1, 2)]).
Proof.
    unfold IG_equiv. unfold RG_equiv. firstorder.
Qed.



(* Now start defining the basic IG functions in terms of an RG *)
  (* {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-} *)


(* Start defining functionality: *)
Definition RG_empty : RG nat :=
    RG_empty.


Definition RG_isEmpty (rg : RG nat) : Prop :=
  RG_isEmpty rg.



(* Helper for matsh *)
Definition _eliminate (node : Node) (rg : RG nat) : RG nat.
Proof.
  refine {|
      RG_nodes := Subtract nat (rg.(RG_nodes)) node;
      RG_edges := fun (n0 n1 : nat) => n0 <> node /\ n1 <> node /\  rg.(RG_edges) n0 n1;
      RG_valid := _
  |}.
  unfold valid_cond. pose proof rg.(RG_valid). firstorder.
  - unfold not. intros. inversion H2. congruence.
  - unfold not. intros. inversion H2. congruence.
Defined.

Definition _getFromsAndTos (node : Node) (rg : RG nat) : Prop * (Ensemble nat * Ensemble nat) :=
  (rg.(RG_nodes) node, ((fun (from : nat) => rg.(RG_edges) from node), (fun (to : nat) => rg.(RG_edges) node to)))
.


(* (Ensemble nat * Ensemble nat) is not a relation, it is two _independent_ sets of from- and to- neighbors *)
Definition RG_matsh (node : Node) (rg : RG nat) : (Prop * (Ensemble nat * Ensemble nat)) * RG nat :=
  (_getFromsAndTos node rg, _eliminate node rg)
.



Definition _add (node : Node) (fromsTos : (NatSet.t * NatSet.t)) (rg : RG nat) : RG nat :=
  match fromsTos with | (froms, tos) =>
    _extendByContext node froms tos rg
  end
.


Definition _insNode (node : Node) (rg : RG nat) : RG nat :=
  _add node (NatSet.empty, NatSet.empty) rg.
  

Definition _insNodes (nodes : list Node) (rg : RG nat) : RG nat :=
  fold_right _insNode rg nodes.


(* If one of the nodes of the edge does not exist, nothing happens *)
Definition _insEdge (edge : (Node * Node)) (rg : RG nat) : RG nat.
Proof.
  destruct edge as [node0 node1].
    refine {|
      RG_nodes := rg.(RG_nodes);
      RG_edges := fun (n0 n1 : nat) => (n0 = node0 /\ n1 = node1 /\ rg.(RG_nodes) node0 /\ rg.(RG_nodes) node1) \/  rg.(RG_edges) n0 n1;
      RG_valid := _
  |}.
  unfold valid_cond. pose proof rg.(RG_valid). firstorder.
  - congruence.
  - congruence.
Defined.


Definition _insEdges (edges : list (Node * Node)) (rg : RG nat) : RG nat :=
  fold_right _insEdge rg edges.

Definition RG_mkGraph (nodes : list Node) (edges : list (Node * Node)) : RG nat :=
  _insEdges edges (_insNodes nodes RG_empty).
 
Definition RG_labNodes (rg : RG nat) : Ensemble Node :=
  rg.(RG_nodes).


(* Here come some proofs about equations: *)

(* Here start "meaningful statements" *)

(* 5 statements on inserting (helpers for mkGraph): update, insEdge, insEdges, insNode, insNodes *)

Lemma RG_insEdge_does_not_add_node : forall (edge : (Node * Node)) (rg : RG nat),
  RG_labNodes (_insEdge edge rg) = RG_labNodes rg.
Proof.
  intros. simpl. unfold RG_labNodes. unfold _insEdge. destruct edge. simpl. reflexivity.
Qed.


Lemma RG_insEdges_does_not_add_nodes : forall (edges : list (Node * Node)) (rg : RG nat),
  RG_labNodes (_insEdges edges rg) = RG_labNodes rg.
Proof.
Admitted.


Lemma RG_insNode_any_ins_node : forall (node : Node) (rg : RG nat),
  RG_labNodes (_insNode node rg) = _customEnsembleAdd node (RG_labNodes rg).
Proof.
Admitted.




Lemma RG_insNodes_any_ins_all_nodes : forall (nodes : list Node) (rg : RG nat),
  RG_labNodes (_insNodes nodes rg) = Union nat (_listToEnsemble nodes) (RG_labNodes rg).
Proof.
Admitted.



Lemma RG_insEdge_on_empty_is_empty : forall (edge : Node * Node),
  _insEdge edge RG_empty = RG_empty.
Proof.
Admitted.


Lemma RG_insEdges_on_empty_is_empty : forall (edges : list (Node * Node)),
  _insEdges edges RG_empty = RG_empty.
(* This proof is very similar to "insEdges_does_not_add_nodes", but using it here it is more complicated than just doing it again  *)
Proof.
Admitted.



(* "big" statement: *)
Theorem RG_mkGraph_any_ins_all_nodes : forall (nodes : list Node) (edges : list (Node * Node)),
  RG_labNodes (RG_mkGraph nodes edges) = _listToEnsemble nodes.
Proof.
Admitted.


Theorem RG_empty_isEmpty : RG_isEmpty RG_empty.
Proof.
  compute. reflexivity.
Qed.

Theorem RG_labNodes_empty_nil : RG_labNodes RG_empty = Empty_set nat.
Proof.
Admitted.



Theorem RG_non_empty_isEmpty_false : forall (nodes : list Node) (edges : list (Node * Node)),
  length nodes <> 0 <-> not (RG_isEmpty ((RG_mkGraph nodes edges))).
Proof.
Admitted.




Theorem RG_matsh_empty_is_nothing : forall (node : Node),
  RG_matsh node RG_empty = ((False, (Empty_set nat, Empty_set nat)), RG_empty).
Proof.
Admitted.



Theorem RG_spec4 : forall (node : Node) (nodes : list Node) (edges : list (Node * Node)), 
  List.In node nodes -> exists froms tos, RG_matsh node (RG_mkGraph nodes edges) =
  ((True, (froms, tos)), RG_mkGraph (filter (fun n => negb (node =? n)) nodes) (filter (fun '(from, to) => negb ((from =? node) || (to =? node))) edges)).
(* This is not even a complete specification and it looks like a hard one to prove... *)
Proof.
Admitted.


Theorem RG_spec5 : forall (node : Node) (nodes : list Node) (edges : list (Node * Node)), 
  not (List.In node nodes) -> RG_matsh node (RG_mkGraph nodes edges) = ((False, (Empty_set nat, Empty_set nat)), RG_mkGraph nodes edges).
Proof.
Admitted.


(* Now go to proving that the implementations from IG basic relate to the RG ones *)
(* Filling in all the admitteds, should suffice to show that IG_basic operations are equivalent to RG operations *)
(* Hence, all theorems from one apply to the other *)
(*   {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-} *)
Definition IG_basic_Propify_isEmpty (result : bool) : Prop.
Proof.
Admitted.

Definition IG_basic_Propify_matsh (result : option (NatSet.t * NatSet.t) * IG) : (Prop * (Ensemble nat * Ensemble nat)) * RG nat.
Proof.
Admitted.

Definition IG_basic_Propify_labNodes (result : list Node) : Ensemble Node.
Proof.
Admitted.


Theorem IG_basic_empty_relate :
  IG_basic_to_RG empty = RG_empty.
Proof.
Admitted.

Theorem IG_basic_isEmpty_relate : forall (ig : IG),
  IG_basic_Propify_isEmpty (isEmpty ig) = RG_isEmpty (IG_basic_to_RG ig).
Proof.
Admitted.


Theorem IG_basic_matsh_relate : forall (node : Node) (ig : IG),
  IG_basic_Propify_matsh (matsh node ig) = RG_matsh node (IG_basic_to_RG ig).
Proof.
Admitted.

Theorem IG_basic_mkGraph_relate : forall (nodes : list Node) (edges : list (Node * Node)),
  IG_basic_to_RG (mkGraph nodes edges) = RG_mkGraph nodes edges.
Proof.
Admitted.

Theorem IG_basic_labNodes_relate : forall (ig : IG),
  IG_basic_Propify_labNodes (labNodes ig) = RG_labNodes (IG_basic_to_RG ig).
Proof.
Admitted.