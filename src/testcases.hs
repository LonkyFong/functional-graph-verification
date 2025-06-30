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





iG_empty

iG_isEmpty iG_empty

iG_mkGraph [(1, "node1"), (2, "node2"), (3, "node3")] [((1, 2), "edge1"), ((2, 3), "edge2")]

iG_match 1 (iG_mkGraph [(1, "node1"), (2, "node2"), (3, "node3")] [((1, 2), "edge1"), ((2, 3), "edge2")])

iG_and ((([("newEdge3", 1)], 4), "node4"), [("newEdge4", 2)]) (iG_mkGraph [(1, "node1"), (2, "node2"), (3, "node3")] [((1, 2), "edge1"), ((2, 3), "edge2")])

iG_isEmpty (iG_mkGraph [(1, "node1"), (2, "node2"), (3, "node3")] [((1, 2), "edge1"), ((2, 3), "edge2")])


iG_matchAny (iG_mkGraph [(1, "node1"), (2, "node2"), (3, "node3")] [((1, 2), "edge1"), ((2, 3), "edge2")])

iG_noNodes (iG_mkGraph [(1, "node1"), (2, "node2"), (3, "node3")] [((1, 2), "edge1"), ((2, 3), "edge2")])

iG_nodeRange (iG_mkGraph [(1, "node1"), (2, "node2"), (3, "node3")] [((1, 2), "edge1"), ((2, 3), "edge2")])

iG_labEdges (iG_mkGraph [(1, "node1"), (2, "node2"), (3, "node3")] [((1, 2), "edge1"), ((2, 3), "edge2")])

iG_transpose (iG_mkGraph [(1, "node1"), (2, "node2"), (3, "node3")] [((1, 2), "edge1"), ((2, 3), "edge2")])

iG_DFS [1] (iG_mkGraph [(1, "node1"), (2, "node2"), (3, "node3")] [((1, 2), "edge1"), ((2, 3), "edge2")])
