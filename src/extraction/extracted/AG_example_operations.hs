-- Example operations for extracted haskell code for algebraic graphs

aG_vertices [1, 2, 3, 4]

aG_edge 1 2

aG_edges [(1, 2), (2, 3), (3, 4)]

aG_makeGraph [1, 2, 3, 4] [(1, 2), (2, 3), (3, 4)]

aG_transpose (1 + 2 * 3 + 1 * 5)

aG_toList (1 + 2 * 3 + 1 * 5)

aG_gmap (\x -> x + 1) (1 + 2 * 3 + 1 * 5)

aG_mergeVertices (\x -> x Prelude.< 3) 30 (1 + 2 * 3 + 1 * 5)

aG_bind (\x -> AG_vertex x + 30) (1 + 2 * 3 + 1 * 5)

aG_induce (\x -> x Prelude.< 3) (1 + 2 * 3 + 1 * 5)

aG_removeVertex 1 (1 + 2 * 3 + 1 * 5)

aG_removeEdge 1 2 (1 * 2 + 2 * 1 + 1 * (2 + 3))

aG_nodeAmount (1 + 2 * 3 + 1 * 5)

aG_BFS [1] (1 + 2 * 3 + 1 * 5)

