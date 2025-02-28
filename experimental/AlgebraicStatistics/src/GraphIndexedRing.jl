struct GraphIndexedRing{T, EdgeMap{T, S}, NodeMap{T, U}, V}
  ring::MPolyRing{V}
  g::Graph{T}
  edge_gens::Dict{S, MPolyRingElem{V}}
  node_gens::Dict{U, MPolyRingElem{V}}
end

function graph_indexed_ring(F::Field, G::Graph{T}, edge_var="e", node_var="v")
  edge_map = get_attribute!(G, :edge_map, nothing)
  
end
