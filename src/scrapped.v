(* TODO: delete this file before handing in *)

Definition RG_vertices {A : Type} (l : list A) : RG A unit :=
    fold_right RG_addNode RG_empty l.

    Definition RG_edgez {A : Type} (l : list (A * A)) : RG A unit :=
    fold_right RG_overlay RG_empty (map (fun x => RG_edge (fst x) (snd x)) l).



Require Import GraphVerification.src.algebraic.AG_algebra_theory.
    

Instance Proper_overlay {A : Type} : Proper ((@RG_equiv A unit) ==> RG_equiv ==> RG_equiv) RG_overlay.
Proof.
    Proper_proof_automation.
Qed.

Instance Proper_connect {A : Type} : Proper ((@RG_equiv A unit) ==> RG_equiv ==> RG_equiv) RG_connect. 
Proof.
    Proper_proof_automation.
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


Definition AG_path {A : Type} (l : list A) : AG A :=
    match l with
    | [] => AG_empty
    | [x] => AG_vertex x
    | _::xs => AG_edges (combine l xs)
    end.

Definition RG_path {A : Type} (l : list A) : RG A unit.
Proof.
    refine {|
        RG_nodes := fun a => In a l;
        RG_edges := fun a1 a2 lab => match l with
                                        | [] => False
                                        | _::rest => In (a1, a2) (combine l rest)
                                        end;
        RG_valid := _
    |}.
    RG_valid_prover.
    - destruct l.
        + firstorder.
        + apply in_combine_l in H. assumption.
    - destruct l.
        + firstorder.
        + apply in_combine_r in H. firstorder.
Defined.
    
    

Lemma AG_path_relates : forall (A : Type) (l : list A),
    RG_path l ==R AG_to_RG (AG_path l).
Proof.
    intros. induction l.
    - firstorder.
    - simpl. firstorder.
        + subst. simpl in *.
    
    destruct l.
        + firstorder.
        + simpl. firstorder.
            -- simpl. firstorder.  rewrite <- AG_edges_relates. reflexivity.
Qed.




(*     -- * Standard families of graphs *)
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




Definition AG_biclique {A : Type} (l1 l2 : list A) : AG A :=
    match l1, l2 with
    | some, [] => AG_vertices l1
    | [], some => AG_vertices l2
    | _, _ => AG_connect (AG_vertices l1) (AG_vertices l2)
    end.





Definition AG_star {A : Type} (x : A) (l : list A) : AG A :=
    AG_vertex x *** AG_vertices l.

Definition RG_star {A : Type} (x : A) (l : list A) : RG A unit :=
    RG_connect (RG_vertex x) (RG_vertices l).




Lemma AG_star_relates : forall (A : Type) (x : A) (l : list A),
    RG_star x l ==R AG_to_RG (AG_star x l).
Proof.
    intros. unfold RG_star. rewrite AG_vertices_relates. reflexivity.
Qed.



(* We skip trees and forests *)


Definition AG_induce {A : Type} (f : A -> bool) (ag : AG A) : AG A :=
    AG_bind (fun a => if f a then AG_vertex a else AG_empty) ag.

Definition RG_induce {A : Type} (f : A -> bool) (rg : RG_unlE A) : RG_unlE A :=
    RG_bind (fun a => if f a then RG_vertex a else RG_empty) rg.


Require Import FunctionalExtensionality.

Lemma AG_induce_relates : forall (A : Type) (f : A -> bool) (ag : AG A),
    RG_induce f (AG_to_RG ag) ==R AG_to_RG (AG_induce f ag).
Proof.
    intros. unfold AG_induce. rewrite <- AG_bind_relates. unfold RG_induce.
    assert ((fun a : A => if f a then RG_vertex a else RG_empty) = (fun a : A => AG_to_RG
(if f a then AG_vertex a else AG_empty))). {
        intros. apply functional_extensionality. intros. destruct (f x).
        - reflexivity.
        - reflexivity.
    }
    rewrite H. clear H.
    reflexivity.
Qed.




Require Import FunctionalExtensionality.

Lemma AG_induce_relates : forall (A : Type) (f : A -> bool) (ag : AG A),
    RG_induce f (AG_to_RG ag) ==R AG_to_RG (AG_induce f ag).
Proof.
    intros. unfold AG_induce. rewrite <- AG_bind_relates. unfold RG_induce.
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




(* FROM RG *)



Definition RG_addNode {A B : Type} (node : A) (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => node = a \/ rg.(RG_nodes) a;
        RG_edges := rg.(RG_edges);
        RG_valid := _
    |}.
    RG_valid_prover rg.
Defined. 


Definition RG_addEdge {A B : Type} (from to : A) (label : B) (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => (RG_addNode to (RG_addNode from rg)).(RG_nodes) a;
        RG_edges := fun a1 a2 l => (a1 = from /\ a2 = to /\ l = label)
                                        \/ rg.(RG_edges) a1 a2 l;
        RG_valid := _
    |}.    
    RG_valid_prover rg.
Defined.


(* Also removes all associated edges *)
Definition RG_removeNode {A B : Type} (node : A) (rg : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => node <> a /\ rg.(RG_nodes) a;
        RG_edges := fun a1 a2 l => a1 <> node /\ a2 <> node /\ rg.(RG_edges) a1 a2 l;
        RG_valid := _
    |}.
    RG_valid_prover rg.
Defined.


(* Does not remove associated nodes *)
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
 


Definition RG_getOutgoingEdges {A B : Type} (node : A) (rg : RG A B) : _edgeRelation A B :=
    fun (a1 a2 : A) l => rg.(RG_edges) a1 a2 l /\ a1 = node.

Definition RG_getIncomingEdges {A B : Type} (node : A) (rg : RG A B) : _edgeRelation A B :=
    fun (a1 a2 : A) l => rg.(RG_edges) a1 a2 l /\ a2 = node.

Definition RG_getIncidentEdges {A B : Type} (node : A) (rg : RG A B) : _edgeRelation A B :=
    fun (a1 a2 : A) l => (RG_getOutgoingEdges node rg) a1 a2 l
                            \/ (RG_getIncomingEdges node rg) a1 a2 l.



Definition RG_isEmpty {A B: Type} (rg : RG A B) : Prop :=
    forall (a : A), rg.(RG_nodes) a <-> False.


(* This one is a helper *)
Lemma if_same_result : forall (A : Type) (a : A) (b : bool),
    (if b then a else a) = a.
Proof.
    intros. destruct b. reflexivity. reflexivity.
Qed.