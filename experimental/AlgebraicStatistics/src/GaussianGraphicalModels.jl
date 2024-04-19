###################################################################################
#
#       Gaussian Rings
#
###################################################################################


struct GaussianRing
    ring::Ring
    gens::Dict
    covariance_matrix
end


Base.show(io::IO, R::GaussianRing) = print("Multivariate polynomial ring over "*string(base_ring(R.ring))*" in "*string(ngens(R.ring))*" variables", "\n", chop(string(gens(R.ring)), head = 16, tail = 1))

# functions for getting attributes of Gaussian rings

# todo
function ring(R::GaussianRing)

    R.ring
end



# todo
function gens(R::GaussianRing)

    R.gens
end



# todo 
function covariance_matrix(R::GaussianRing)

    R.covariance_matrix
end



###################################################################################
#
#       Directed Gaussian Graphical Models
#
###################################################################################


# creates a ring with variables corresponding to the entries of a (n x n) symmetric matrix
function gaussian_ring(n::Int64, s_var_name::String="s")::GaussianRing

    S, s = polynomial_ring(QQ, reduce(vcat, [[s_var_name*string([i,j]) for j in i:n] for i in 1:n]))

    s = Dict([(Tuple(var_index(x)), x) for x in s])

    cov_matrix = matrix([[i < j ? s[i,j] : s[j,i] for j in 1:n] for i in 1:n])

    GaussianRing(S, s, cov_matrix)
end



# creates a GraphicalModel with a GaussianRing and a Directed Graph
function graphical_model(G::Graph{Directed}, S::GaussianRing, l_var_name::String="l")::GraphicalModel

    R, l, w = polynomial_ring(QQ, ["l"*string([src(e), dst(e)]) for e in edges(G)], ["w"*string([v]) for v in vertices(G)])

    l = Dict([(Tuple(var_index(x)), x) for x in l])

    GraphicalModel(G, S, R, [l, w])
end



# creates matrix of parameters which correspond to the directed edges of a digraph
function directed_edges_matrix(M::GraphicalModel{Graph{Directed}, GaussianRing})

    G = graph(M)
    l = param_gens(M)[1]
    L = matrix(M.param_ring, [[has_edge(G, i, j) ? l[i,j] : 0 for j in vertices(G)] for i in vertices(G)])
end



# creates matrix of parameters which correspond to the directed edges of a digraph
function error_covariance(M::GraphicalModel{Graph{Directed}, GaussianRing})

    G = graph(M)
    w = param_gens(M)[2]
    W = matrix(M.param_ring, [[i == j ? w[i] : 0 for j in vertices(G)] for i in vertices(G)])
end



# creates matrix of parameters which correspond to the directed edges of a digraph
# creates the parameterization of the model as a ring map
function parameterization(M::GraphicalModel{Graph{Directed}, GaussianRing})

    S = ring(M)
    R = param_ring(M)
    G = graph(M)

    L = directed_edges_matrix(M)
    Id = identity_matrix(R, n_vertices(G))
    W = error_covariance(M)
    Sigma = transpose(inv(Id-L))*W*inv(Id-L)
    
    hom(S.ring, R, reduce(vcat, [[Sigma[i,j] for j in i:n_vertices(G)] for i in 1:n_vertices(G)]))
end



# computes the ideal generated by all trek separations
function trek_ideal(M::GraphicalModel{Graph{Directed}, GaussianRing})

    #todo
end



###################################################################################
#
#       Undirected Gaussian Graphical Models
#
###################################################################################


# creates a GraphicalModel with a GaussianRing and a Undirected Graph
function graphical_model(G::Graph{Undirected}, S::GaussianRing, k_var_name::String="k")

    R, k = polynomial_ring(QQ, vcat([k_var_name*string([v, v]) for v in vertices(G)], [k_var_name*string([dst(e), src(e)]) for e in edges(G)]))

    k = Dict([(Tuple(var_index(x)), x) for x in k])

    GraphicalModel(G, S, R, k)
end



# creates the concentration matrix of a undirected Gaussian graphical models with zeroes corresponding to non-edges
function concentration_matrix(M::GraphicalModel{Graph{Undirected}, GaussianRing})

    G = graph(M)
    k = param_gens(M)
    K = zero_matrix(param_ring(M), n_vertices(G), n_vertices(G))

    for e in edges(G)

        K[dst(e), src(e)] = k[dst(e), src(e)]
        K[src(e), dst(e)] = k[dst(e), src(e)]
    end
    
    for v in vertices(G)

        K[v, v] = k[v,v]
    end

    K
end



# creates the parameterization of a undirected Gaussian graphical model using the adjoint
function parameterization(M::GraphicalModel{Graph{Undirected}, GaussianRing})

    G = graph(M)
    S = ring(M)
    R = param_ring(M)
    K = concentration_matrix(M)
    adj = adjoint(K)

    hom(ring(S), fraction_field(R), reduce(vcat, [[adj[i,j]//det(K) for j in i:n_vertices(G)] for i in 1:n_vertices(G)]))
end


# computes the vanishing ideal of a gaussian graphical model by eliminating the concentration varaibles k from Sigma*K - I after saturating by det(K)
function vanishing_ideal(M::GraphicalModel{Graph{Undirected}, GaussianRing})

    G = graph(M)
    S = ring(M)
    R = param_ring(M)

    # there simply must be a better way to do this but I cannot find one currently
    elim_ring, elim_gens = polynomial_ring(coefficient_ring(R), vcat([string(x) for x in gens(R)], [string(x) for x in gens(ring(S))]))
    inject_R = hom(R, elim_ring, elim_gens[1:ngens(R)])
    inject_S = hom(S.ring, elim_ring, elim_gens[ngens(R)+1:ngens(elim_ring)])

    Sigma = inject_S.(covariance_matrix(S))
    K = inject_R.(concentration_matrix(M))

    elim_ideal = ideal(reduce(vcat, Sigma*K - identity_matrix(elim_ring, n_vertices(G))))


    eliminate(saturation(elim_ideal, ideal([det(K)])), elim_gens[1:ngens(R)])
end

