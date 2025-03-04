function load_phylogenetic_model(tree_model_id::String)
    try
        file_path = joinpath(oscardir, "data", "AlgebraicStatistics",  "PhylogeneticModels", tree_model_id * ".mrdi")
        phylo_model = load(file_path)
        return phylo_model
    catch e 
        if isa(e, SystemError)
            println("You possibly did not enter the identifier in the correct format: treeid-modelid.mrdi, e.g. '3-0-0-JC.mrdi'.")
        end
    end
end

@doc raw"""
    load_phylogenetic_model(tree_model_id::String)

Loads a phylogenetic model using the identifier given on the website. 
The identifier has the form tree_id-model_id, e.g. "3-0-0-JC" for the star3 graph
with Jukes-Cantor model. 
"""