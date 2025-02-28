struct GraphIndexedRing{S, T, U, V, W, X}
  ring::MPolyRing{S}
  g::Graph{T}
  edge_gens::Dict{U, V}
  vertex_gens::Dict{W, X}
end

@doc raw"""
    graph_indexed_ring(F::Field, G::Graph{T}; edge_var::VarName="e", vertex_var::VarName="v", edge_ngens::Int=1, vertex_ngens::Int=1, cached=false) where T <: Union{Directed, Undirected}

Constructs a ring with generators indexed by edges and vertices of a labelled or unlabelled graph.


# Examples
```jldoctest
julia> G = graph_from_edges(Directed, [[1, 2], [2, 3]])
Directed graph with 3 nodes and the following edges:
(1, 2)(2, 3)

julia> R = graph_indexed_ring(QQ, G)
Multivariate polynomial ring in 5 variables over QQ
 with the following generators on the edges
Edge(1, 2) -> e[1, 2]
Edge(2, 3) -> e[2, 3]

 and the following generators on the vertices
1 -> v[1]
2 -> v[2]
3 -> v[3]

julia> G = graph_from_labelled_edges(Directed, Dict((1, 2) => 1, (2, 3) => 2, (1, 3) => 1))
Directed graph with 3 nodes and
edges labels:
(1, 2) -> 1
(1, 3) -> 1
(2, 3) -> 2

julia> R = graph_indexed_ring(QQ, G)
Multivariate polynomial ring in 5 variables over QQ
 with the following generators on the edges
Edge(1, 2) -> e[1]
Edge(1, 3) -> e[1]
Edge(2, 3) -> e[2]

 and the following generators on the vertices
1 -> v[1]
2 -> v[2]
3 -> v[3]
```
"""
function graph_indexed_ring(F::Field, G::Graph{T};
                            edge_var::VarName="e", vertex_var::VarName="v",
                            edge_ngens::Int=1, vertex_ngens::Int=1,
                            cached=false) where T <: Union{Directed, Undirected}
  if has_attribute(G, :edge_map)
    U = typeof(G[first(edges(G))])
    edge_keys = unique([G[e] for e in edges(G)])
    e_vars = ["$(edge_var)[$l]" for l in edge_keys]
  else
    U = Edge
    edge_keys = edges(G)
    e_vars = ["$(edge_var)[$(src(e)), $(dst(e))]" for e in edges(G)]
  end

  if edge_ngens > 1
    e_vars = [["$e_var[$i]"] for i in 1:edge_ngens]
    V = Vector{MPolyRingElem{elem_type(F)}}
  else
    V = MPolyRingElem{elem_type(F)}
  end
  
  if has_attribute(G, :node_map)
    W = typeof(G[1])
    vertex_keys = unique([G[e] for i in 1:n_vertices(G)])
  else
    W = Int
    vertex_keys = 1:n_vertices(G)
  end
  v_vars = ["$(vertex_var)[$l]" for l in vertex_keys]

  if vertex_ngens > 1
    v_vars = [["$e_var[$i]"] for i in 1:edge_ngens]
    X = Vector{MPolyRingElem{elem_type(F)}}
  elseif v_vars == 0
    v_vars = VarName[]
    X = MPolyRingElem{elem_type(F)}
  else
    X = MPolyRingElem{elem_type(F)}
  end

  R, e_gens, v_gens = polynomial_ring(F, e_vars, v_vars; cached=cached)

  edge_gens = Dict{U, V}()
  for (i, k) in enumerate(edge_keys)
    edge_gens[k] = e_gens[i]
  end

  vertex_gens = Dict{W, V}()
  for (i, k) in enumerate(vertex_keys)
    vertex_gens[k] = v_gens[i]
  end

  GraphIndexedRing{elem_type(F), T, U, V, W, X}(R, G, edge_gens, vertex_gens)
end

graph(R::GraphIndexedRing) = R.g
_vertex_gens(R::GraphIndexedRing) = R.vertex_gens
_edge_gens(R::GraphIndexedRing) = R.edge_gens
ring(R::GraphIndexedRing) = R.ring

# get edge generators
function Base.getindex(R::GraphIndexedRing, i::Int, j::Int)
  G = graph(R)
  @req has_edge(G, i, j) "invalid edge"
  edge_gens = _edge_gens(R)
  has_attribute(G, :edge_map) ? edge_gens[G[i, j]] : edge_gens[Edge(i, j)]
end
Base.getindex(R::GraphIndexedRing, e::Edge) = R[src(e), dst(e)]
Base.getindex(R::GraphIndexedRing, index::NTuple{2, Int}) = R[index[1], index[2]]

# get vertex generators
function Base.getindex(R::GraphIndexedRing, v::Int)
  vertex_gens = _vertex_gens(R)
  @req !isempty(vertex_gens) "Ring doesn't have generators on the vertices"
  G = graph(R)
  @req _has_node(G, v) "invalid node number"

  has_attribute(G, :node_map) ? vertex_gens[G[v]] : vertex_gens[v]
end
  
function Base.show(io::IO, R::GraphIndexedRing)
  show(io, ring(R))
  println(io, "\n with the following generators on the edges")
  G = graph(R)
  e_gens = _edge_gens(R)
  for e in edges(G)
    println("$e -> $(R[e])")
  end

  v_gens = _vertex_gens(R)
  if !isempty(v_gens)
    println(io, "\n and the following generators on the vertices")
    for v in 1:n_vertices(G)
      println("$v -> $(R[v])")
    end
  end
end
