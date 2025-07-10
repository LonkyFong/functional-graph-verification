-- Example operations for extracted haskell code for inductive graphs
-- These are just code snippets, not complete executable Haskell code.

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
