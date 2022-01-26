# Min_Vertex_Cover
Comparison between three different algorithms for solving the minimum vertex cover problem on basis of their running time and approximation ratio.
The ﬁrst algorithm, which will be named “CNF-SAT-VC”, is based on a polynomial-time reduction to CNF-SAT and the use of a SAT solver.
The second algorithm picks a vertex of highest degree (most incident edges), adds it to the vertex cover and throw away all edge’s incident on that vertex, and repeats the same instruction till no edges remain. We will call this algorithm “APPROX-VC-1”.
The last algorithm picks an edge <u,v>, and adds both “u” and “v” to the vertex cover. Then it will throw away all edges attached to u and v and repeat the same above steps till no edges remain. This algorithm will be called “APPROX-VC-2”.
