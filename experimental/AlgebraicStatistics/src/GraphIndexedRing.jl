struct GraphIndexedRing{T, EdgeMap{T, S}, NodeMap{T, U}, V} where W <: Union{MPolyRingElem{V}, Vector{MPolyRingElem{V}}}
  ring::MPolyRing{V}
  g::Graph{T}
  edge_gens::Dict{S, W}
  node_gens::Dict{U, W}
end

function graph_indexed_ring(F::Field, G::Graph{T};
                            edge_var::VarName="e", node_var::VarName="v",
                            edge_ngens::Int=1, node_ngens::Int=1,
                            cached=false)
  edge_map = get_attribute!(G, :edge_map, nothing)
  node_map = get_attribute!(G, :node_map, nothing)
  if !isnothing(edge_map)
    e_indices = unique(e -> G[e], edges(G))
  else
    
  end
  
  R, e_gens, v_gens = polynomial_ring(
    F,

  )
end
