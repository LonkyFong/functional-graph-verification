Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

(*
Require Import Coq.Arith.Arith.

Require Import Bool.


Require Import MyProject.project.util.util.

Require Import MyProject.project.relational_graph_theory.


Require Import Coq.Sets.Ensembles.
Require Import MyProject.project.util.NatSet.
*)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.

Require Import MyProject.project.util.util.
Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_IG_operations.


(* Auxiliary graph class functions: *)
Definition RG_matchAny {A B : Type} (rg : RG A B) : RG_Decomp A B.
Proof. Admitted.
   (* :=
  let isValid := exists node, rg.(RG_nodes) node in
  (isValid, ((fun l (from : A) => isValid /\ rg.(RG_edges) from node l),
              node,
              (fun l (to : A) => isValid /\ rg.(RG_edges) node to l)))
. *)

(* Difficult, as lack of decidability *)
Definition RG_noNodes {A B : Type} (rg : RG A B) : nat.
Proof. Admitted.
  
(* RG_nodeRange makes no sense, as As are not ordered *)
  (* Definition RG_nodeRange {A B : Type} (rg : RG A B) : (A, A). *)


Definition RG_labEdges {A B : Type} (rg : RG A B) : _edgeRelation A B :=
  rg.(RG_edges).


Require Import Recdef. (* Must import this to use the Function feature *)

(* This is a problem *)
Definition RG_measure {A B : Type} (rg : RG A B) : nat.
Proof. Admitted.

Function RG_gmap {A B C D : Type} (f : RG_Context A B -> RG_Context C D) (rg : RG A B) {measure RG_measure rg} : RG C D :=
  match RG_matchAny rg with
    | ((True, c), rest) => _add (f c) (RG_gmap f rest)
    (* | ((False, c), rest) => _add (f c) (RG_gmap f rest) *)
  end
.
Proof. Admitted.



Definition RG_grev {A B : Type} (rg : RG A B) : RG A B :=
  RG_gmap _ _ _ _ (fun '((froms, node, tos) : RG_Context A B) => (tos, node, froms)) rg
.

Function RG_ufold {A B C : Type} (f : RG_Context A B -> C -> C) (acc : C) (rg : RG A B) {measure RG_measure rg} : C :=
  match RG_matchAny rg with
    | ((True, c), rest) => f c (RG_ufold f acc rest)
    (* | ((False, c), rest) => _add (f c) (RG_gmap f rest) *)
  end
.
Proof. Admitted.


Definition RG_gmap' {A B C D : Type} (f : RG_Context A B -> RG_Context C D) (rg : RG A B) : RG C D :=
  RG_ufold _ _ (RG C D) (fun (c : RG_Context A B) (acc : RG C D) => _add (f c) acc) RG_empty rg.


Definition RG_nodes' {A B : Type} (rg : RG A B) : list A :=
  RG_ufold _ _ _ (fun '(froms, node, tos) acc => node :: acc ) [] rg.
  
Definition RG_undir {A B : Type} (rg : RG A B) : RG A B :=
  RG_gmap _ _ _ _ (fun '(froms, node, tos) =>
    let fromsTos := (fun (b : B) (a : A) => froms b a \/ tos b a) in
    (fromsTos, node, fromsTos)) rg
.

Definition RG_gsuc {A B : Type} (node : A) (rg : RG A B) : Ensemble A :=
  match RG_match node rg with
    | ((True, (_, _, tos)), rest) => fun (a : A) => exists l, tos l a 
  end
.

(* RG_deg is hard to implement, as is is hard to count *)
Definition RG_deg {A B : Type} (node : A) (rg : RG A B) : nat.
Proof. Admitted.
(* :=
  match RG_match node rg with
    | ((True, (froms, nodeAgain, tos)), rest) => fun (a : A) => CARDINALITY froms tos 
  end
. *)

Definition RG_del {A B : Type} (node : A) (rg : RG A B) : RG A B :=
  match RG_match node rg with
    | ((True, _), rest) => rest
  end
.

Definition RG_suc {A B : Type} (node : A) (c : RG_Context A B) : Ensemble A :=
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
dijkstra (p@((v , d ): )≺h) (c & g) = p:dijkstra (mergeAll (h:expand d p c)) g
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
prim (p@((v , ): )≺h) (c & g) = p:prim (mergeAll (h:addEdges p c)) g
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

