Require Import Coq.Arith.Arith.
Require Import String.
Open Scope string_scope.

Require Import Bool.
Require Import List.
Import ListNotations.

Require Import MyProject.project.util.NatMap.
Require Import MyProject.project.util.NatSet.
Open Scope nat_scope.

(* This file defines an inductive graph using maps like Erwig *)
(* Note that A is the node label type and B is the edge label type *)
(* At the moment, there are only the "MINIMAL" implementations  *)

(*{-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-}
  *)

Definition Adj (B : Type) := list (B * Node). 

Definition Context (A B : Type) : Type :=
    (Adj B * Node * A * Adj B).

Definition MContext (A B : Type) : Type :=
    option (Context A B).


(* Definition Adj' (B : Type) := NatMap.t (list B). *)

(* No node needed, since the node is the key *)
Definition Context' (A B : Type) : Type :=
  (Adj B * A * Adj B).  

Definition IG (A B : Type) := NatMap.t (Context' A B).

Definition Decomp (A B : Type) : Type :=
  (MContext A B * IG A B). 


Definition LNode (A : Type) : Type := (Node * A).
Definition LEdge (B : Type) : Type := (Node * Node * B).





(* Start defining functionality: *)
Definition IG_empty {A B : Type} : IG A B :=
  NatMap.empty (Context' A B).


Definition IG_isEmpty {A B : Type} (ig : IG A B) : bool :=
  NatMap.is_empty ig.

Compute IG_isEmpty IG_empty.



(* Here start the helper functions for "match" *)




(* Applies a function to a map entry if it exists quickly *)
Definition _updateEntry {A B : Type} (node : Node) (f : Context' A B -> Context' A B) (ig : IG A B) : IG A B := 
  match NatMap.find node ig with
    | Some v => NatMap.add node (f v) ig
    | None => ig
  end.

Definition _addSucc {A B : Type} (node : Node) (label : B) (context' : Context' A B) : Context' A B :=
  match context' with
  | (froms, l, tos) => (froms, l, (label, node) :: tos)
  end.
  
Definition _addPred {A B : Type} (node : Node) (label : B) (context' : Context' A B) : Context' A B :=
  match context' with
  | (froms, l, tos) => ((label, node) :: froms, l, tos)
  end.


Definition _clearSucc {A B : Type} (node : Node) (context' : Context' A B) : Context' A B :=
  match context' with
  | (froms, label, tos) => (froms, label, filter (fun '(_, n) => negb (n =? node)) tos)
  end.


Definition _clearPred {A B : Type} (node : Node) (context' : Context' A B) : Context' A B :=
  match context' with
  | (froms, label, tos) => (filter (fun '(_, n) => negb (n =? node)) froms, label, tos)
  end.


Definition _updAdj {A B : Type} (adj : Adj B) (f : B -> Context' A B -> Context' A B) (gr : IG A B) : IG A B :=
  fold_right (fun '(l, n) (acc : IG A B) => _updateEntry n (f l) acc) gr adj.  


Definition _cleanSplit {A B : Type} (node : Node) (context' : Context' A B) (ig : IG A B) : Context A B * IG A B :=
  match context' with
  | (froms, label, tos) =>
                          let rmLoops :=  filter (fun '(_, n) => negb (n =? node)) in

                          let froms' := rmLoops froms in
                          let tos' := rmLoops tos in
                          let context := (froms', node, label, tos (*no '*)) in
                          
                          let ig' := _updAdj froms' (fun x y => _clearSucc node y) ig in 
                          let ig'' := _updAdj tos' (fun x y => _clearPred node y) ig' in
                          (context, ig'')
  end.


Definition IG_match {A B : Type} (node : Node) (ig : IG A B) : Decomp A B :=
  match NatMap.find node ig with
  | None => (None, ig)
  | Some context' => match _cleanSplit node context' (NatMap.remove node ig) with
                    | (context, ig') => (Some context, ig')
                    end
  end.




(* Here start the helper functions for "mkGraph" *)

(* This is the "&" constructor, but it has to be defined as a function, since it is too advanced *)
Definition add {A B : Type} (context : Context A B) (ig : IG A B) : IG A B :=
  match context with
  | (froms, node, label, tos) =>
                                let ig' := NatMap.add node (froms, label, tos) ig in
                                let ig'' := _updAdj tos (_addPred node) ig' in
                                _updAdj froms (_addSucc node) ig''
  end.


Definition insNode {A B : Type} (node : LNode A) (ig : IG A B) : IG A B :=
  match node with
  | (n, l) => add ([], n, l, []) ig
  end.

Definition insNodes {A B : Type} (nodes : list (LNode A)) (ig : IG A B) : IG A B :=
  fold_right insNode ig nodes.



Definition insEdge {A B : Type} (edge : LEdge B) (ig : IG A B) : IG A B :=
  match edge with
  | (from, to, l) =>
                    let (mcxt, ig') := IG_match from ig in
                    match mcxt with
                    | (Some (froms, _, label, tos)) => add (froms, from, label, (l, to) :: tos) ig'
                    | None => ig
                    end
  end.


Definition insEdges {A B : Type} (edges : list (LEdge B)) (ig : IG A B) : IG A B :=
  fold_right insEdge ig edges.



Definition IG_mkGraph {A B : Type} (nodes : list (LNode A)) (edges : list (LEdge B)) : IG A B :=
  insEdges edges (insNodes nodes IG_empty).

 
Definition IG_labNodes {A B : Type} (ig : IG A B) : list (LNode A) :=
  map (fun '(v, (_, l, _)) => (v,l)) (NatMap.elements ig).



(* Make IGs visible  *)

Definition IG_show {A B : Type} (ig : IG A B) :=
  NatMap.elements ig. 

Definition Decomp_show {A B : Type} (d : Decomp A B) := 
  match d with
  | (mContext, x) => (mContext, IG_show x)
  end
.



(* Now come some more advanced operations *)

(* Auxiliary graph class functions: *)
Definition IG_matchAny {A B : Type} (ig : IG A B) : Decomp A B :=
  match IG_labNodes ig with
  | [] => (None, ig)
  | node :: nodes => IG_match (fst node)  ig
  end.
  


Definition IG_noNodes {A B : Type} (ig : IG A B) : nat :=
  length (IG_labNodes ig).

Definition _minimum (l : list nat) : nat :=
  fold_right min 0 l.

(* This is a hack *)
Definition _maximum (l : list nat) : nat :=
  fold_right max 1000 l.

Definition IG_nodeRange {A B : Type} (ig : IG A B) : Node * Node :=
  match IG_isEmpty ig with
  | true => (0, 0)
  | false =>
    let nodes := map fst (IG_labNodes ig) in
    (_minimum nodes, _maximum nodes)
  end.
    


Definition IG_labEdges {A B : Type} (ig : IG A B) : list (LEdge B) :=
  fold_right (fun '(node, (_, _, tos)) acc => map (fun '(l, to) => (node, to, l)) tos ++ acc) [] (NatMap.elements ig). 



(* Here stars DFS stuff *)



Definition suc {A B : Type} (c : Context A B) : list Node :=
  match c with
  | (_, _, _, tos) => map snd tos
  end.

Fixpoint IG_dfs_fuled {A B : Type} (nodes : list Node) (ig : IG A B) (fuel : nat) : list Node :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match nodes with
    | [] => []
    | n :: ns => if IG_isEmpty ig then [] else
                  match IG_match n ig with
                  | (Some cntxt, rest) => n :: IG_dfs_fuled (suc cntxt ++ ns) rest fuel'
                  | (None, same) => IG_dfs_fuled ns same fuel'
                  end
    end
  end.
Definition my_complicated_graph :=
  IG_mkGraph
    [(1, "a"); (2, "b"); (3, "c"); (4, "d"); (5, "e"); (6, "f")]
    [ (1, 2, "edge1");
      (2, 3, "edge2");
      (3, 1, "edge3");
      (2, 4, "edge4");
      (4, 5, "edge5");
      (5, 6, "edge6");
      (6, 3, "edge7");
      (1, 5, "edge8");
      (6, 1, "edge9")]
.

Compute IG_dfs_fuled [1] my_complicated_graph 50.











(* https://fzn.fr/teaching/coq/ecole10/summer/lectures/lec10.pdf *)

  

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Recdef. (* Must import this to use the Function feature *)

Import ListNotations.
Require Import Coq.Wellfounded.Inverse_Image.




Definition dProdDfs (A B : Type) := {_ : list Node & IG A B}.

(* Lexicographic order on (nat * nat) *)
Definition lex_dProdDfs (A B : Type) := Relation_Operators.lexprod (list Node)
                                                (fun a => IG A B)
                                                (fun l1 l2 => Peano.lt (length l1) (length l2))
                                                (fun a:list Node => fun ig1 ig2 => Peano.lt (NatMap.cardinal ig1) (NatMap.cardinal ig2)). 


(* Prove lexicographic order is well-founded *)
Lemma wf_lex_dProdDfs (A B : Type) : well_founded (lex_dProdDfs A B).
Proof.
  apply wf_lexprod.
  - apply well_founded_ltof. 
  - intros. apply well_founded_ltof.
Qed.





Definition prodTodPairDfs {A B : Type} (p : list Node * IG A B) : dProdDfs A B :=
  existT _ (fst p) (snd p).

Definition lex_prodDfs (A B : Type) (nodesIg1 nodesIg2 : list Node * IG A B) : Prop := 
  lex_dProdDfs _ _ (prodTodPairDfs nodesIg1) (prodTodPairDfs nodesIg2).


(* Prove lexicographic order is well-founded *)
Lemma wf_lex_prodDfs (A B : Type) : well_founded (lex_prodDfs A B).
Proof.
  unfold lex_prodDfs.
  pose proof (wf_lex_dProdDfs A B).
  pose proof (wf_inverse_image (list Node * IG A B) _ (lex_dProdDfs A B)).

  apply (H0 (@prodTodPairDfs A B)) in H.
  assumption.
Qed.







Function IG_dfs' {A B : Type} (nodesIg : list Node * IG A B) {wf (lex_prodDfs A B) nodesIg} : list Node := 
  match nodesIg with
  | (nodes, ig) =>
    match nodes with
    | [] => []
    | n :: ns => if IG_isEmpty ig then [] else
                  match IG_match n ig with
                  | (Some cntxt, rest) => n :: IG_dfs' ((suc cntxt ++ ns), rest)
                  | (None, same) => IG_dfs' (ns, same)
                  end
    end
  end.
Proof.
  - admit.
  - admit.
  - apply  wf_lex_prodDfs.
Admitted.















(* Vanilla version: *)
Fixpoint IG_dfs {A B : Type} (nodes : list Node) (ig : IG A B) : list Node :=
  match nodes with
  | [] => []
  | n :: ns => if IG_isEmpty ig then [] else
                match IG_match n ig with
                | (Some cntxt, rest) => n :: IG_dfs (suc cntxt ++ ns) rest
                | (None, same) => IG_dfs ns same
                end
  end.
Proof.
- intros. Admitted.































(* 
(* Here starts stuff from the paper, that I did not bother to implement *)
Require Import Recdef. (* Must import this to use the Function feature *)

Function IG_gmap {A B C D : Type} (f : IG_Context A B -> IG_Context C D) (ig : IG A B) {measure IG_measure ig} : IG C D :=
  match IG_matchAny ig with
    | ((True, c), rest) => _add (f c) (IG_gmap f rest)
    (* | ((False, c), rest) => _add (f c) (IG_gmap f rest) *)
  end
.
Proof. Admitted.



Definition IG_grev {A B : Type} (ig : IG A B) : IG A B :=
  IG_gmap _ _ _ _ (fun '((froms, node, tos) : IG_Context A B) => (tos, node, froms)) ig
.

Function IG_ufold {A B C : Type} (f : IG_Context A B -> C -> C) (acc : C) (ig : IG A B) {measure IG_measure ig} : C :=
  match IG_matchAny ig with
    | ((True, c), rest) => f c (IG_ufold f acc rest)
    (* | ((False, c), rest) => _add (f c) (IG_gmap f rest) *)
  end
.
Proof. Admitted.


Definition IG_gmap' {A B C D : Type} (f : IG_Context A B -> IG_Context C D) (ig : IG A B) : IG C D :=
  IG_ufold _ _ (IG C D) (fun (c : IG_Context A B) (acc : IG C D) => _add (f c) acc) IG_empty ig.


Definition IG_nodes' {A B : Type} (ig : IG A B) : list A :=
  IG_ufold _ _ _ (fun '(froms, node, tos) acc => node :: acc ) [] ig.
  
Definition IG_undir {A B : Type} (ig : IG A B) : IG A B :=
  IG_gmap _ _ _ _ (fun '(froms, node, tos) =>
    let fromsTos := (fun (b : B) (a : A) => froms b a \/ tos b a) in
    (fromsTos, node, fromsTos)) ig
.

Definition IG_gsuc {A B : Type} (node : A) (ig : IG A B) : Ensemble A :=
  match IG_match node ig with
    | ((True, (_, _, tos)), rest) => fun (a : A) => exists l, tos l a 
  end
.

(* IG_deg is hard to implement, as is is hard to count *)
Definition IG_deg {A B : Type} (node : A) (ig : IG A B) : nat.
Proof. Admitted.
(* :=
  match IG_match node ig with
    | ((True, (froms, nodeAgain, tos)), rest) => fun (a : A) => CARDINALITY froms tos 
  end
. *)

Definition IG_del {A B : Type} (node : A) (ig : IG A B) : IG A B :=
  match IG_match node ig with
    | ((True, _), rest) => rest
  end
.

Definition IG_suc {A B : Type} (node : A) (c : IG_Context A B) : Ensemble A :=
  match c with | (_, _, tos) =>
    fun (a : A) => exists l, tos l a 
  end
.



(* More advanced stuff *)

dfs :: [Node] → Graph a b → [Node]
dfs [ ]
g
= []
v
dfs (v :vs) (c & g) = v :dfs (suc c++vs) g
dfs (v :vs) g
= dfs vs g

(* Possible extensions: *)
dfs vs Empty = [ ]
dfs vs g | null vs || isEmpty g = [ ]


dfs [ ]
g0 = [ ]
dfs (v :vs) g 0 = case match v g 0 of
(Just c, g) → v :dfs (suc c++vs) g
(Nothing, g) → dfs vs g

data Tree a = Br a [Tree a]
postorder :: Tree a → [a]
postorder (Br v ts) = concatMap postorder ts++[v ]

concatMap :: (a → [b]) → [a] → [b]
concatMap f = concat . map f


df :: [Node] → Graph a b → ([Tree Node], Graph a b)
df [ ]
g
= ([ ], g)
v
df (v :vs) (c & g) = (Br v f :f 0 , g2 ) where (f , g1 ) = df (suc c) g
(f 0 , g2 ) = df vs g1
df (v :vs) g
= df vs g

dff :: [Node] → Graph a b → [Tree Node]
dff vs g = fst (df vs g)


topsort :: Graph a b → [Node]
topsort = reverse . concatMap postorder . dff
scc :: Graph a b → [Tree Node]
scc g = dff (topsort g) (grev g)




(* BFS *)

bfs :: [Node] → Graph a b → [Node]
bfs [ ]
g
= []
v
bfs (v :vs) (c & g) = v :bfs (vs++suc c) g
bfs (v :vs) g
= bfs vs g

type Path = [Node]
type RTree = [Path]
bft :: Node → Graph a b → RTree
bft v = bf [[v ]]
bf :: [Path] → Graph a b → RTree
bf [ ]
g
= []
v
bf (p@(v : ):ps) (c & g) = p:bf (ps++map (:p) (suc c)) g
bf (p:ps)
g
= bf ps g


first :: (a → Bool ) → [a] → a
first p = head . filter p
esp :: Node → Node → Graph a b → Path
esp s t = reverse . first (\(v : ) → v t) . bft s


(* Shortest path: *)

type LNode a = (Node, a)
type LPath a = [LNode a]
type LRTree a = [LPath a]
instance Eq a ⇒ Eq (LPath a) where
(( , x ): ) (( , y): ) = x y
instance Ord a ⇒ Ord (LPath a) where
(( , x ): ) < (( , y): ) = x < y
getPath :: Node → LRTree a → Path
getPath v = reverse . map fst . first (\((w , ): ) → w == v)



expand :: Real b ⇒ b → LPath b → Context a b → [Heap (LPath b)]
expand d p ( , , , s) = map (\(l , v ) → unitHeap ((v , l + d ):p)) s
dijkstra :: Real b ⇒ Heap (LPath b) → Graph a b → LRTree b
dijkstra h g | isEmptyHeap h || isEmpty g = [ ]
v
dijkstra (p@((v , d ): )≺h) (c & g) = p:dijkstra (meigeAll (h:expand d p c)) g
dijkstra ( ≺h) g
= dijkstra h g




spt :: Real b ⇒ Node → Graph a b → LRTree b
spt v = spt (unitHeap [(v , 0)])
sp :: Real b ⇒ Node → Node → Graph a b → Path
sp s t = getPath t . spt s



(* Minimum spanning tree *)
addEdges :: Real b ⇒ LPath b → Context a b → [Heap (LPath b)]
addEdges p ( , , , s) = map (\(l , v ) → unitHeap ((v , l ):p)) s

mst :: Real b ⇒ Node → Graph a b → LRTree b
mst v g = prim (unitHeap [(v , 0)]) g
prim :: Real b ⇒ Heap (LPath b) → Graph a b → LRTree b
prim h g | isEmptyHeap h || isEmpty g = [ ]
v
prim (p@((v , ): )≺h) (c & g) = p:prim (meigeAll (h:addEdges p c)) g
prim ( ≺h) g
= prim h g

mstp :: Real b ⇒ LRTree b → Node → Node → Path
mstp t a b = joinPaths (getPath a t) (getPath b t)
joinPaths :: Path → Path → Path
joinPaths p q = joinAt (head p) (tail p) (tail q)
joinAt :: Node → Path → Path → Path
joinAt x (v :vs) (w :ws) | v w = joinAt v vs ws
joinAt x p
q
= reverse p++(x :q)



(* Maximum independent node set: *)


indep :: Graph a b → [Node]
indep Empty = [ ]
indep g
= if length i1 > length i2 then i1 else i2
where vs
= nodes g
m
= maximum (map (flip deg g) vs)
v
= first (\v → deg v g m) vs
v
c & g0 = g
i1
= indep g 0
i2
= v :indep (foldr del g 0 (pre c++suc c))
 *)
