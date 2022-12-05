using Pkg
Pkg.instantiate()


using ProbabilisticCircuits
using LogicCircuits
using CSV
using DataFrames
using Random
using DataStructures
using Profile
using Combinatorics
using ArgParse
using StatsBase


#------ CIRCUIT LEARNERS ----------

function learn_pc(data_path, decision_column)
    df = CSV.read(data_path,  DataFrame , type=Bool);

    clt_df=df[!, Not(decision_column)];
    data=DataFrame((BitArray(Base.convert(Matrix{Bool}, clt_df))))
    clt = learn_chow_liu_tree(data)
    vtree = learn_vtree_from_clt(clt; vtree_mode="balanced" )
    lc1 = compile_sdd_from_clt(clt, vtree)
    pc1 = ProbCircuit(lc1) # left
    estimate_parameters(pc1, data; pseudocount=1.0)
    lc2 = compile_sdd_from_clt(clt, vtree)
    pc2 = ProbCircuit(lc2) # right
    estimate_parameters(pc2, data; pseudocount=1.0)

    clt_df.D=df[!,decision_column];
    df=clt_df;
    df=DataFrame((BitArray(Base.convert(Matrix{Bool}, df))))

    D=UInt32(size(df)[2]);
    v_D= PlainVtreeLeafNode(D); # D_id=num_columns as last variable is D
    v_root= PlainVtreeInnerNode(v_D, vtree);
    T = StructProbCircuit
    pos_n_D = compile(T, v_D, var2lit(D))
    neg_n_D = compile(T, v_D, - var2lit(D))

    pc_root=pos_n_D*pc1 + neg_n_D*pc2

    estimate_parameters(pc_root, df; pseudocount=1.0)
    pc_root, v_root
end

function get_compas_circuit(data_path, decision_column, num_iter)
    df = CSV.read(data_path,  DataFrame , type=Bool);

    clt_df=df[!, Not(decision_column)];
    v_1= PlainVtreeLeafNode(1);
    v_2= PlainVtreeLeafNode(2);
    v_3= PlainVtreeLeafNode(3);
    v_4= PlainVtreeLeafNode(4);
    v_5= PlainVtreeLeafNode(5);
    v_6= PlainVtreeLeafNode(6);
    v_7= PlainVtreeLeafNode(7);
    v_4_7= PlainVtreeInnerNode(v_4, v_7);
    v_47_5= PlainVtreeInnerNode(v_4_7, v_5);
    v_6_475= PlainVtreeInnerNode(v_6, v_47_5);
    v_2_6475= PlainVtreeInnerNode(v_2, v_6_475);
    v_1_26475= PlainVtreeInnerNode(v_1, v_2_6475);
    v_3_126475= PlainVtreeInnerNode(v_3, v_1_26475);
    v_subroot=v_3_126475


    data=DataFrame((BitArray(Base.convert(Matrix{Bool}, clt_df))))
    lc1= fully_factorized_circuit(StructProbCircuit, v_subroot).children[1] # remove dummy node at top
    estimate_parameters(lc1, data; pseudocount=1.0)
    lc1=learn_circuit(data, lc1, v_subroot; maxiter=num_iter)
    pc1=lc1
    estimate_parameters(pc1, data; pseudocount=1.0)
    lc2= fully_factorized_circuit(StructProbCircuit, v_subroot).children[1] # remove dummy node at top
    estimate_parameters(lc2, data; pseudocount=1.0)
    lc2=learn_circuit(data, lc2, v_subroot; maxiter=num_iter)
    pc2=lc2
    estimate_parameters(pc2, data; pseudocount=1.0)

    clt_df.D=df[!,decision_column];
    df=clt_df;
    df=DataFrame((BitArray(Base.convert(Matrix{Bool}, df))))

    D=UInt32(size(df)[2]);
    v_D= PlainVtreeLeafNode(D); # D_id=num_columns as last variable is D
    v_root= PlainVtreeInnerNode(v_D, v_subroot);
    T = StructProbCircuit
    pos_n_D = compile(T, v_D, var2lit(D))
    neg_n_D = compile(T, v_D, - var2lit(D))

    pc_root=pos_n_D*pc1 + neg_n_D*pc2

    estimate_parameters(pc_root, df; pseudocount=1.0)
    pc_root, v_root
end

function get_adult_circuit(data_path, decision_column, num_iter)
    df = CSV.read(data_path,  DataFrame , type=Bool);

    clt_df=df[!, Not(decision_column)];
    v_1= PlainVtreeLeafNode(1);
    v_2= PlainVtreeLeafNode(2);
    v_3= PlainVtreeLeafNode(3);
    v_4= PlainVtreeLeafNode(4);
    v_5= PlainVtreeLeafNode(5);
    v_6= PlainVtreeLeafNode(6);
    v_7= PlainVtreeLeafNode(7);
    v_8= PlainVtreeLeafNode(8);
    v_9= PlainVtreeLeafNode(9);
    v_10= PlainVtreeLeafNode(10);
    v_11= PlainVtreeLeafNode(11);
    v_12= PlainVtreeLeafNode(12);
    v_13= PlainVtreeLeafNode(13);
    v_3_7= PlainVtreeInnerNode(v_3, v_7);
    v_4_37= PlainVtreeInnerNode(v_4, v_3_7);
    v_437_13= PlainVtreeInnerNode(v_4_37, v_13);
    v_12_43713= PlainVtreeInnerNode(v_12, v_437_13);
    v_10_5= PlainVtreeInnerNode(v_10, v_5);
    v_105_1243713= PlainVtreeInnerNode(v_10_5, v_12_43713);
    v_11_2= PlainVtreeInnerNode(v_11, v_2);
    v_9_112= PlainVtreeInnerNode(v_9, v_11_2);
    v_9112_1051243713= PlainVtreeInnerNode(v_9_112, v_105_1243713);
    v_1_6= PlainVtreeInnerNode(v_1, v_6);
    v_16_91121051243713= PlainVtreeInnerNode(v_1_6, v_9112_1051243713);
    v_8_1691121051243713= PlainVtreeInnerNode(v_8, v_16_91121051243713);
    v_subroot=v_8_1691121051243713


    data=DataFrame((BitArray(Base.convert(Matrix{Bool}, clt_df))))
    lc1= fully_factorized_circuit(StructProbCircuit, v_subroot).children[1] # remove dummy node at top
    estimate_parameters(lc1, data; pseudocount=1.0)
    lc1=learn_circuit(data, lc1, v_subroot; maxiter=num_iter)
    pc1=lc1
    estimate_parameters(pc1, data; pseudocount=1.0)
    lc2= fully_factorized_circuit(StructProbCircuit, v_subroot).children[1] # remove dummy node at top
    estimate_parameters(lc2, data; pseudocount=1.0)
    lc2=learn_circuit(data, lc2, v_subroot; maxiter=num_iter)
    pc2=lc2
    estimate_parameters(pc2, data; pseudocount=1.0)

    clt_df.D=df[!,decision_column];
    df=clt_df;
    df=DataFrame((BitArray(Base.convert(Matrix{Bool}, df))))

    D=UInt32(size(df)[2]);
    v_D= PlainVtreeLeafNode(D); # D_id=num_columns as last variable is D
    v_root= PlainVtreeInnerNode(v_D, v_subroot);
    T = StructProbCircuit
    pos_n_D = compile(T, v_D, var2lit(D))
    neg_n_D = compile(T, v_D, - var2lit(D))

    pc_root=pos_n_D*pc1 + neg_n_D*pc2

    estimate_parameters(pc_root, df; pseudocount=1.0)
    pc_root, v_root
end

function get_likelihood(pc::StructSumNode, data_path, decision_column)
    df = CSV.read(data_path,  DataFrame , type=Bool);
    clt_df=df[!, Not(decision_column)];
    clt_df.D=df[!,decision_column];
    df=clt_df;
    df=DataFrame((BitArray(Base.convert(Matrix{Bool}, df))))

    println(log_likelihood_avg(pc, df))
    println(log_likelihood(pc, df))
end


#------ DISCRIMINATION/DIVERGENCE SCORES and BOUNDS ---------

function disc_score(circuit::ProbCircuit, x::Array{<:Any,1}, y::Array{<:Any,1}, num_vars::Int64, D::Int64)
    evidence=[missing for i in range(1,stop=num_vars)]
    evidence=DataFrame(reshape(evidence, 1, :))
    evidence=DataFrame(Base.convert(Matrix{Union{Int64,Missing}}, evidence))
    #p(d|y)
    for el in y
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_y=marginal(circuit,evidence )[1]
    evidence[D]=1
    p_dy=marginal(circuit,evidence )[1]

    #p(d|xy)
    evidence[D]=missing
    for el in x
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_xy=marginal(circuit,evidence )[1]
    evidence[D]=1
    p_dxy=marginal(circuit,evidence )[1]

    return exp(p_dxy-p_xy)-exp(p_dy-p_y)
end

# dummy version of the function to match divergence signature
function disc_score(circuit::ProbCircuit, x::Array{<:Any,1}, y::Array{<:Any,1}, delta::Float64, num_vars::Int64, D::Int64)
    return disc_score(circuit,x,y,num_vars,D)
end

function divergence_score(circuit::ProbCircuit, x::Array{<:Any,1}, y::Array{<:Any,1}, delta::Float64, num_vars::Int64, D::Int64)
    evidence=[missing for i in range(1,stop=num_vars)]
    evidence=DataFrame(reshape(evidence, 1, :))
    evidence=DataFrame(Base.convert(Matrix{Union{Int64,Missing}}, evidence))
    #p(d|y)
    for el in y
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_y=marginal(circuit,evidence )[1]
    evidence[D]=1
    p_dy=marginal(circuit,evidence )[1]

    #p(d|xy)
    evidence[D]=missing
    for el in x
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_xy=marginal(circuit,evidence )[1]
    evidence[D]=1
    p_dxy=marginal(circuit,evidence )[1]

    disc_score=exp(p_dxy-p_xy)-exp(p_dy-p_y)
    r = 0
    if disc_score > delta
        r = (delta - disc_score)/(exp(-p_xy)-exp(-p_y))
    end
    if disc_score < -delta
        r = (-delta - disc_score)/(exp(-p_xy)-exp(-p_y))
    end

    div = exp(p_dxy)*(log(exp(p_dxy))-log(exp(p_dxy)+r)) + (exp(p_xy)-exp(p_dxy))*(log(exp(p_xy)-exp(p_dxy))-log(exp(p_xy)-exp(p_dxy)-r))
    return div
end

# return probability of pattern P(xy) in addition to the absolute discrimination score
function abs_disc_score_with_p(circuit::ProbCircuit, x::Array{<:Any,1}, y::Array{<:Any,1}, num_vars::Int64, D::Int64)
    evidence=[missing for i in range(1,stop=num_vars)]
    evidence=DataFrame(reshape(evidence, 1, :))
    evidence=DataFrame(Base.convert(Matrix{Union{Int64,Missing}}, evidence))
    #p(d|y)
    for el in y
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_y=marginal(circuit,evidence )[1]
    evidence[D]=1
    p_dy=marginal(circuit,evidence )[1]

    #p(d|xy)
    evidence[D]=missing
    for el in x
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_xy=marginal(circuit,evidence )[1]
    evidence[D]=1
    p_dxy=marginal(circuit,evidence )[1]

    return Float64(abs(exp(p_dxy-p_xy)-exp(p_dy-p_y))), Float64(exp(p_xy))
end

function BR(n::StructProbLiteralNode, m::StructProbLiteralNode, cache::Dict{Pair{T where T <: StructProbCircuit, T where T <: StructProbCircuit}, Tuple{Float64,Bool}}, evidence::Array{<:Any,1})
    get!(cache, Pair(n, m)) do
        variable=abs(n.literal)
        negation=n.literal<0
        pr=nothing
        if n.literal != m.literal
            pr=Inf
        elseif (evidence[abs(n.literal)]===missing) ||  (evidence[abs(n.literal)]==2) # funky syntax about missing! not a typo :)
            pr=0.0
        elseif  (evidence[variable]==1 && !negation) || (evidence[variable]==0 && negation)
            pr=0.0
        else
            pr=Inf
        end

        if evidence[abs(n.literal)]===missing || evidence[abs(m.literal)]===missing
            excluded=false
        else
            excluded=(evidence[abs(n.literal)]==2 && evidence[abs(m.literal)]==2)
        end

        return pr, excluded
    end
end

function BR(n::StructSumNode, m::StructSumNode, cache::Dict{Pair{T where T <: StructProbCircuit, T where T <: StructProbCircuit}, Tuple{Float64,Bool}}, evidence::Array{<:Any,1})
    get!(cache, Pair(n, m)) do
        valid=false
        pr=-Inf
        excluded=true
        for i=1:length(n.children)
            for j=1:length(m.children)
                child_pr, child_excluded=BR(n.children[i], m.children[j], cache, evidence)
                valid= (valid || (child_pr!=Inf))
                if child_pr!=Inf
                    pr =max(pr,child_pr + (n.log_probs[i])-(m.log_probs[j]))
                end
                excluded= (excluded && child_excluded)
            end
        end

        if excluded
            return 0.0,excluded
        elseif !valid
            return Inf, excluded
        else
            return pr, excluded
        end
    end
end

function BR(n::StructMulNode, m::StructMulNode, cache::Dict{Pair{T where T <: StructProbCircuit, T where T <: StructProbCircuit}, Tuple{Float64,Bool}}, evidence::Array{<:Any,1})
    get!(cache, Pair(n, m)) do
        valid=true
        pr=0.0
        excluded=true

        child_pr,child_excluded=BR(n.prime, m.prime, cache, evidence)
        valid= (valid && (child_pr!=Inf))
        if child_pr!=Inf
            pr =pr + child_pr
        end

        excluded=(excluded&&child_excluded)

        child_pr,child_excluded=BR(n.sub, m.sub, cache, evidence)
        valid= (valid && (child_pr!=Inf))
        if child_pr!=Inf
            pr =pr + child_pr
        end

        excluded=(excluded&&child_excluded)

        if !valid
            return Inf, excluded
        else
            return pr, excluded
        end
    end
end


# single variable literal vs ornode
function BR(n::StructProbLiteralNode, m::StructSumNode, cache::Dict{Pair{T where T <: StructProbCircuit, T where T <: StructProbCircuit}, Tuple{Float64,Bool}}, evidence::Array{<:Any,1})
    get!(cache, Pair(n, m)) do
        valid=false
        pr=-Inf
        excluded=true
        for j=1:length(m.children)
            child_pr,child_excluded =BR(n, m.children[j], cache, evidence)
            valid= (valid || (child_pr!=Inf))
            if child_pr!=Inf
                pr =max(pr,child_pr -(m.log_probs[j]))
            end
            excluded=(excluded&&child_excluded)
        end

        if excluded
            return 0.0,excluded
        elseif !valid
            return Inf, excluded
        else
            return pr, excluded
        end
    end
end

function BR(n::StructSumNode, m::StructProbLiteralNode, cache::Dict{Pair{T where T <: StructProbCircuit, T where T <: StructProbCircuit}, Tuple{Float64,Bool}}, evidence::Array{<:Any,1})
    get!(cache, Pair(n, m)) do
        valid=false
        pr=-Inf
        excluded=true
        for i=1:length(n.children)
            child_pr,child_excluded=BR(n.children[i], m, cache, evidence)
            valid= (valid || (child_pr!=Inf))
            if child_pr!=Inf
                pr =max(pr,child_pr + (n.log_probs[i]))
            end
            excluded=(excluded&&child_excluded)
        end

        if excluded
            return 0.0,excluded
        elseif !valid
            return Inf, excluded
        else
            return pr, excluded
        end
    end
end


# Implements Algorithm 3 in the paper.

# maximizes conditional P(d|e) by extending evidence
# Assumption: PC is partitioned by decision variable at the root
# negation is set to -1 for P(-d|e), 1 for P(d|e)

function MAXC(pc::StructSumNode, evidence::Array{<:Any,1}, negate::Int64)
    cache = Dict{Pair{T where T <: StructProbCircuit, T where T <: StructProbCircuit}, Tuple{Float64,Bool}}()
    if pc.children[1].prime.literal * negate > 0  # left child is d (assuming negate=1)
        # ratio is max log(p(e|d)/p(e|-d))
        ratio = BR(pc.children[1].sub,pc.children[2].sub,cache,evidence)[1]
        return (1/(exp(pc.log_probs[1]) + exp(pc.log_probs[2]-ratio)))*exp(pc.log_probs[1])
    else  # left child is -d (assuming negate=1)
        # ratio is max log(p(e|d)/p(e|-d))
        ratio = BR(pc.children[2].sub,pc.children[1].sub,cache,evidence)[1]
        return (1/(exp(pc.log_probs[2]) + exp(pc.log_probs[1]-ratio)))*exp(pc.log_probs[2])
    end
end

# minimizes conditional P(d|e) by extending evidence
# Assumption: PC is partitioned by decision variable at the root
# negation is set to -1 for P(-d|e), 1 for P(d|e)

function MINC(pc::StructSumNode, evidence::Array{<:Any,1}, negate::Int64)
    cache = Dict{Pair{T where T <: StructProbCircuit, T where T <: StructProbCircuit}, Tuple{Float64,Bool}}()
    if pc.children[1].prime.literal * negate > 0  # left child is d (assuming negate=1)
        # ratio is max log(p(e|-d)/p(e|d))
        ratio = BR(pc.children[2].sub,pc.children[1].sub,cache,evidence)[1]
        return (1/(exp(pc.log_probs[1]) + exp(pc.log_probs[2]+ratio)))*exp(pc.log_probs[1])
    else  # left child is -d (assuming negate=1)
        # ratio is max log(p(e|-d)/p(e|d))
        ratio = BR(pc.children[1].sub,pc.children[2].sub,cache,evidence)[1]
        return (1/(exp(pc.log_probs[2]) + exp(pc.log_probs[1]+ratio)))*exp(pc.log_probs[2])
    end
end

# x and y should be like [-1,3,-7]
function disc_bound(pc::StructSumNode, x::Array{<:Any,1}, y::Array{<:Any,1},num_vars::Int64, D::Int64)
    evidence=[missing for i in range(1,stop=num_vars)]
    evidence= Base.convert(Array{Union{Int64,Missing},1}, evidence)

    #p(d|y)
    for el in y
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_d_y_max=MAXC(pc,evidence,1)
    p_d_y_min=MINC(pc,evidence,1)

    #p(d|xy)
    for el in x
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_d_xy_max=MAXC(pc,evidence,1)
    p_d_xy_min=MINC(pc,evidence,1)

    lower_bound = p_d_xy_min - p_d_y_max
    upper_bound = p_d_xy_max - p_d_y_min
    return max(abs(lower_bound), abs(upper_bound))
end

# x and y should be like [-1,3,-7]
function disc_bound(pc::StructSumNode, x::Array{<:Any,1}, y::Array{<:Any,1}, E::Array{<:Any,1}, num_vars::Int64, D::Int64)
    evidence=[missing for i in range(1,stop=num_vars)]
    evidence= Base.convert(Array{Union{Int64,Missing},1}, evidence)

    # excluded
    for el in E
        evidence[abs(el)]= 2;
    end

    #p(d|y)
    for el in x
        evidence[abs(el)]= 2;
    end
    for el in y
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_d_y_max=MAXC(pc,evidence,1)
    p_d_y_min=MINC(pc,evidence,1)

    #p(d|xy)
    for el in x
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_d_xy_max=MAXC(pc,evidence,1)
    p_d_xy_min=MINC(pc,evidence,1)

    lower_bound = p_d_xy_min - p_d_y_max
    upper_bound = p_d_xy_max - p_d_y_min
    return max(abs(lower_bound), abs(upper_bound))
end

# x and y should be like [-1,3,-7]
function divergence_bound(pc::ProbCircuit, x::Array{<:Any,1}, y::Array{<:Any,1}, num_vars::Int64, D::Int64)
    evidence=[missing for i in range(1,stop=num_vars)]
    evidence= Base.convert(Array{Union{Int64,Missing},1}, evidence)

    #p(d|y)
    for el in y
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_d_y_min=MINC(pc,evidence,1)
    p_dprime_y_min=MINC(pc,evidence,-1)

    #p(d|xy)
    for el in x
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_d_xy_max=MAXC(pc,evidence,1)
    p_dprime_xy_max=MAXC(pc,evidence,-1)

    evidence=DataFrame(reshape(evidence, 1, :))
    evidence=DataFrame(Base.convert(Matrix{Union{Int64,Missing}}, evidence))
    evidence[D]=1
    p_dxy=exp(marginal(pc,evidence)[1])
    evidence[D]=0
    p_dprimexy=exp(marginal(pc,evidence)[1])

    bound=p_dxy*log(p_d_xy_max/p_d_y_min)+p_dprimexy*log(p_dprime_xy_max/p_dprime_y_min)
    return bound
end

# x and y should be like [-1,3,-7]
function divergence_bound(pc::ProbCircuit, x::Array{<:Any,1}, y::Array{<:Any,1}, E::Array{<:Any,1}, num_vars::Int64, D::Int64)
    evidence=[missing for i in range(1,stop=num_vars)]
    evidence= Base.convert(Array{Union{Int64,Missing},1}, evidence)

    # excluded
    for el in E
        evidence[abs(el)]= 2;
    end

    #p(d|y)
    for el in y
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_d_y_min=MINC(pc,evidence,1)
    p_dprime_y_min=MINC(pc,evidence,-1)


    #p(d|xy)
    for el in x
        evidence[abs(el)]= (el>0) ? 1 : 0;
    end
    p_d_xy_max=MAXC(pc,evidence,1)
    p_dprime_xy_max=MAXC(pc,evidence,-1)

    # excluded
    for el in E
        evidence[abs(el)]= missing;
    end
    evidence=DataFrame(reshape(evidence, 1, :))
    evidence=DataFrame(Base.convert(Matrix{Union{Int64,Missing}}, evidence))
    evidence[D]=1
    p_dxy=exp(marginal(pc,evidence)[1])
    evidence[D]=0
    p_dprimexy=exp(marginal(pc,evidence)[1])

    bound=p_dxy*log(p_d_xy_max/p_d_y_min)+p_dprimexy*log(p_dprime_xy_max/p_dprime_y_min)
    return bound
end

# x and y should be like [-1,3,-7]
function trivial_bound(pc::StructSumNode, x::Array{<:Any,1}, y::Array{<:Any,1}, num_vars::Int64, D::Int64)
    return 1.0
end

# x and y should be like [-1,3,-7]
function trivial_bound(pc::StructSumNode, x::Array{<:Any,1}, y::Array{<:Any,1}, E::Array{<:Any,1}, num_vars::Int64, D::Int64)
    return 1.0
end

#------ EXACT PATTERN MINER ---------

# Implements Algorithm 1 in the paper.
# delta is used only for divergence score
function patterns(pc::StructSumNode, x::Array{Any,1}, y::Array{Any,1}, visited::Array{Any,1}, ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64, threshold::Float64, count::Array{Int64,1}, num_vars::Int64, D::Int64, bound::Function, score::Function)
    remaining= Set([i for i in range(1,stop=num_vars)])
    setdiff!(remaining,Set([D]))
    setdiff!(remaining,Set([abs(el) for el in x]))
    setdiff!(remaining,Set([abs(el) for el in y]))
    setdiff!(remaining,Set([el for el in visited]))

    if length(remaining)==0
        return
    end

    z=0
    # pick some z in z\xy
    for el in ordering
        if (el in remaining) && (length(x)!=0 || (el in sensitive_vars))
            z=el
            break
        end
    end

    if z==0
        return
    end

    if z in sensitive_vars
        count[2]+=2
        push!(x,z)
        if abs(score(pc,x,y,delta,num_vars,D))>threshold
            count[1]+=1
            # println(x,y,abs(score(pc,x,y,delta,num_vars,D)))
        end

        # if bound ok, recurse
        if bound(pc,x,y,visited,num_vars,D)>threshold
            patterns(pc,x,y,visited, ordering, sensitive_vars, delta, threshold, count,num_vars,D, bound, score)
        end
        pop!(x)


        push!(x,-z)
        if abs(score(pc,x,y,delta,num_vars,D))>threshold
            count[1]+=1
            # println(x,y,abs(score(pc,x,y,delta,num_vars,D)))
        end

        # if bound ok, recurse
        if bound(pc,x,y,visited,num_vars,D)>threshold
            patterns(pc,x,y,visited, ordering, sensitive_vars, delta, threshold, count,num_vars,D, bound, score)
        end
        pop!(x)

    end

    count[2]+=2
    push!(y,z)
    if abs(score(pc,x,y,delta,num_vars,D))>threshold
        count[1]+=1
        # println(x,y,abs(score(pc,x,y,delta,num_vars,D)))
    end

    # if bound ok, recurse
    if bound(pc,x,y,visited,num_vars,D)>threshold
        patterns(pc,x,y,visited, ordering, sensitive_vars, delta, threshold, count,num_vars,D, bound, score)
    end
    pop!(y)


    push!(y,-z)
    if abs(score(pc,x,y,delta,num_vars,D))>threshold
        count[1]+=1
        # println(x,y,abs(score(pc,x,y,delta,num_vars,D)))
    end

    # if bound ok, recurse
    if bound(pc,x,y,visited,num_vars,D)>threshold
        patterns(pc,x,y,visited, ordering, sensitive_vars, delta, threshold, count,num_vars,D, bound, score)
    end
    pop!(y)

    push!(visited,abs(z))
    # if bound ok, recurse
    if bound(pc,x,y,visited,num_vars,D)>threshold
        patterns(pc,x,y,visited, ordering, sensitive_vars, delta, threshold, count,num_vars,D, bound, score)
    end
    pop!(visited)

end

function num_disc_patterns(pc::StructSumNode,ordering::Array{Int64,1},sensitive_vars::Set{Int64}, threshold::Float64,  num_vars::Int64, D::Int64)
    x=[]
    y=[]
    visited=[]
    counts=Int64.([0,0])
    patterns(pc,x,y,visited, ordering,sensitive_vars, -1.0, threshold, counts, num_vars ,D, disc_bound, disc_score)
    println(counts)
    return counts[1]
end

function num_divergence_patterns(pc::StructSumNode,ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64,  num_vars::Int64, D::Int64)
    x=[]
    y=[]
    visited=[]
    counts=Int64.([0,0])
    patterns(pc,x,y,visited, ordering,sensitive_vars, delta, -1.0, counts, num_vars ,D, divergence_bound, divergence_score)
    print(counts)
    return counts[1]
end

function get_top_k_helper(pc::StructSumNode, x::Array{Any,1}, y::Array{Any,1}, visited::Array{Any,1}, ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64, threshold::Float64, count::Array{Int64,1}, num_vars::Int64, D::Int64,k::Int64, top_k::BinaryMinHeap{Float64}, bound::Function, score::Function)
    remaining= Set([i for i in range(1,stop=num_vars)])
    setdiff!(remaining,Set([D]))
    setdiff!(remaining,Set([abs(el) for el in x]))
    setdiff!(remaining,Set([abs(el) for el in y]))
    setdiff!(remaining,Set([el for el in visited]))
    # println("Remaining: ", remaining)

    if length(remaining)==0
        return
    end

    z=0
    # pick some z in z\xy
    for el in ordering
        if (el in remaining) && (length(x)!=0 || (el in sensitive_vars))
            z=el
            break
        end
    end

    if z==0
        return
    end

    if z in sensitive_vars
        count[2]+=2
        push!(x,z)
        if length(top_k)<k || abs(score(pc,x,y,delta,num_vars,D))>max(top(top_k), threshold)
            if length(top_k)==k
                pop!(top_k)
            end
            push!(top_k,abs(score(pc,x,y,delta,num_vars,D)))
            # println(x,y,abs(score(pc,x,y,delta,num_vars,D)))
        end

        # if bound ok, recurse
        if (bound(pc,x,y,visited,num_vars,D)>max(top(top_k), threshold) && bound(pc,x,y,num_vars,D)>max(top(top_k), threshold)) || length(top_k)<k
            get_top_k_helper(pc,x,y,visited, ordering, sensitive_vars, delta, threshold, count,num_vars,D,k,top_k, bound, score)
        end
        pop!(x)


        push!(x,-z)
        if length(top_k)<k || abs(score(pc,x,y,delta,num_vars,D))>max(top(top_k), threshold)
            if length(top_k)==k
                pop!(top_k)
            end
            push!(top_k,abs(score(pc,x,y,delta,num_vars,D)))
            # println(x,y,abs(score(pc,x,y,delta,num_vars,D)))
        end

        # if bound ok, recurse
        if (bound(pc,x,y,visited,num_vars,D)>max(top(top_k), threshold) && bound(pc,x,y,num_vars,D)>max(top(top_k), threshold)) || length(top_k)<k
            get_top_k_helper(pc,x,y,visited, ordering, sensitive_vars,delta,threshold,count,num_vars,D,k,top_k, bound, score)
        end
        pop!(x)

    end

    count[2]+=2
    push!(y,z)
    if length(top_k)<k || abs(score(pc,x,y,delta,num_vars,D))>max(top(top_k), threshold)
        if length(top_k)==k
            pop!(top_k)
        end
        push!(top_k,abs(score(pc,x,y,delta,num_vars,D)))
        # println(x,y,abs(score(pc,x,y,delta,num_vars,D)))
    end

    # if bound ok, recurse
    if (bound(pc,x,y,visited,num_vars,D)>max(top(top_k), threshold) && bound(pc,x,y,num_vars,D)>max(top(top_k), threshold)) || length(top_k)<k
        get_top_k_helper(pc,x,y,visited, ordering, sensitive_vars, delta, threshold,count,num_vars,D,k,top_k, bound, score)
    end
    pop!(y)


    push!(y,-z)
    if length(top_k)<k || abs(score(pc,x,y,delta,num_vars,D))>max(top(top_k), threshold)
        if length(top_k)==k
            pop!(top_k)
        end
        push!(top_k,abs(score(pc,x,y,delta,num_vars,D)))
        # println(x,y,abs(score(pc,x,y,delta,num_vars,D)))
    end

    # if bound ok, recurse
    if (bound(pc,x,y,visited,num_vars,D)>max(top(top_k), threshold) && bound(pc,x,y,num_vars,D)>max(top(top_k), threshold)) || length(top_k)<k
        get_top_k_helper(pc,x,y,visited, ordering, sensitive_vars,delta,threshold,count,num_vars,D,k,top_k, bound, score)
    end
    pop!(y)

    push!(visited,abs(z))
    # if bound ok, recurse
    if (bound(pc,x,y,visited,num_vars,D)>max(top(top_k), threshold) && bound(pc,x,y,num_vars,D)>max(top(top_k), threshold)) || length(top_k)<k
        get_top_k_helper(pc,x,y,visited, ordering, sensitive_vars,delta,threshold,count,num_vars,D,k,top_k, bound, score)
    end
    pop!(visited)

    # if count[2]%1000==0
    #     println("total: ", count[2], ", min_so_far: ", top(top_k))
    # end

end

function get_top_k(pc::StructSumNode,  ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64, threshold::Float64, num_vars::Int64, D::Int64, k::Int64, bound::Function, score::Function)
    x=[]
    y=[]
    visited=[]
    counts=Int64.([0,0])

    lower_bound=-1.0

    h=BinaryMinHeap{Float64}()
    for i=1:k
        push!(h,lower_bound)
    end
    get_top_k_helper(pc,x,y,visited,ordering,sensitive_vars, delta, threshold, counts, num_vars, D, k,h, bound, score)
    println(counts)
    return top(h), length(h)
end

# only complete assignments
function get_top_k_complete_assignments_helper(pc::StructSumNode, x::Array{Any,1}, y::Array{Any,1}, visited::Array{Any,1}, ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64, threshold::Float64, count::Array{Int64,1}, num_vars::Int64, D::Int64,k::Int64, top_k::BinaryMinHeap{Float64}, x_pattern::Array{Any,1}, y_pattern::Array{Any,1}, bound::Function, score::Function, save_last_pattern::Bool)
    remaining= Set([i for i in range(1,stop=num_vars)])
    setdiff!(remaining,Set([D]))
    setdiff!(remaining,Set([abs(el) for el in x]))
    setdiff!(remaining,Set([abs(el) for el in y]))
    # setdiff!(remaining,Set([el for el in visited]))
    # println("Remaining: ", remaining)
    # println(x,y)

    if length(remaining)==0
        if length(top_k)<k || abs(score(pc,x,y,delta,num_vars,D))>max(top(top_k), threshold)
            if length(top_k)==k
                pop!(top_k)
            end
            push!(top_k,abs(score(pc,x,y,delta,num_vars,D)))
            # println(top(top_k))
            if save_last_pattern
                empty!(x_pattern)
                for el in x
                    push!(x_pattern, el)
                end
                empty!(y_pattern)
                for el in y
                    push!(y_pattern, el)
                end
            end
        end
        return
    end

    z=0
    # pick some z in z\xy
    for el in ordering
        if (el in remaining) && (length(x)!=0 || (el in sensitive_vars))
            z=el
            break
        end
    end

    if z==0
        return
    end


    if z in sensitive_vars
        count[2]+=2
        push!(x,z)
        # if bound ok, recurse
        # println(x,y,bound(pc,x,y,visited,num_vars,D))
        if (bound(pc,x,y,visited,num_vars,D)>max(top(top_k), threshold) && bound(pc,x,y,num_vars,D)>max(top(top_k), threshold)) || length(top_k)<k
            get_top_k_complete_assignments_helper(pc,x,y,visited, ordering, sensitive_vars,delta,threshold,count,num_vars,D,k,top_k,x_pattern,y_pattern, bound, score, save_last_pattern)
        end
        pop!(x)


        push!(x,-z)
        # if bound ok, recurse
        # println(x,y,bound(pc,x,y,visited,num_vars,D))
        if (bound(pc,x,y,visited,num_vars,D)>max(top(top_k), threshold) && bound(pc,x,y,num_vars,D)>max(top(top_k), threshold)) || length(top_k)<k
            get_top_k_complete_assignments_helper(pc,x,y,visited, ordering, sensitive_vars,delta,threshold,count,num_vars,D,k,top_k,x_pattern,y_pattern, bound, score, save_last_pattern)
        end
        pop!(x)

    end

    count[2]+=2
    push!(y,z)
    # if bound ok, recurse
    # println(x,y,bound(pc,x,y,visited,num_vars,D))
    if (bound(pc,x,y,visited,num_vars,D)>max(top(top_k), threshold) && bound(pc,x,y,num_vars,D)>max(top(top_k), threshold)) || length(top_k)<k
        get_top_k_complete_assignments_helper(pc,x,y,visited, ordering, sensitive_vars,delta,threshold,count,num_vars,D,k,top_k,x_pattern,y_pattern, bound, score, save_last_pattern)
    end
    pop!(y)

    push!(y,-z)
    # if bound ok, recurse
    # println(x,y,bound(pc,x,y,visited,num_vars,D))
    if (bound(pc,x,y,visited,num_vars,D)>max(top(top_k), threshold) && bound(pc,x,y,num_vars,D)>max(top(top_k), threshold)) || length(top_k)<k
        get_top_k_complete_assignments_helper(pc,x,y,visited, ordering, sensitive_vars,delta,threshold,count,num_vars,D,k,top_k,x_pattern,y_pattern, bound, score, save_last_pattern)
    end
    pop!(y)


    # if count[2]%1000==0
    #     println("total: ", count[2], ", min_so_far: ", top(top_k))
    # end
end

# only check complete assignments
function get_top_k_complete(pc::StructSumNode,  ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64, threshold::Float64, num_vars::Int64, D::Int64, k::Int64, bound::Function, score::Function)
    x=[]
    y=[]
    visited=[]
    x_pattern=[]
    y_pattern=[]
    counts=Int64.([0,0])
    h=BinaryMinHeap{Float64}()
    for i=1:k
        push!(h,-i)
    end
    get_top_k_complete_assignments_helper(pc,x,y,visited,ordering,sensitive_vars,delta,threshold,counts, num_vars, D, k,h, x_pattern, y_pattern, bound, score, false)
    println(counts)
    return top(h)
end

# only check complete assignments
function get_top_one_complete(pc::StructSumNode,  ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64, threshold::Float64, num_vars::Int64, D::Int64, bound::Function, score::Function)
    x=[]
    y=[]
    visited=[]
    x_pattern=[]
    y_pattern=[]
    counts=Int64.([0,0])
    h=BinaryMinHeap{Float64}()
    k=1
    for i=1:k
        push!(h,-i)
    end
    get_top_k_complete_assignments_helper(pc,x,y,visited,ordering,sensitive_vars,delta,threshold,counts, num_vars, D, k,h, x_pattern, y_pattern, bound, score, true)
    println(counts)
    return x_pattern, y_pattern, top(h), length(h)
end

#------ SAMPLING ---------


# Implements Algorithm 4 in the paper.
function get_top_one_random_memo_avg(pc::StructSumNode, sensitive_vars::Set{Int64},delta::Float64, threshold::Float64, num_vars::Int64, D::Int64, bound::Function, score::Function, global_cache::Dict{Tuple{Int64,Int64,Int64}, Tuple{Float64,Int64}}, children_cache::Dict{Tuple{Int64,Int64,Int64}, Array{Tuple{Int64,Int64,Int64},1}})
    remaining= Set([i for i in range(1,stop=num_vars)])
    setdiff!(remaining,Set([D]))
    x=[]
    y=[]
    highest_score=-1
    visited = Array{Tuple{Int64,Int64,Int64},1}()
    for i in range(1,stop=num_vars-1)
        cur_mask=get_mask(x,y)
        cache = Dict{Tuple{Int64,Int64,Int64}, Float64}()
        children= get!(children_cache,cur_mask) do
            get_children_masks(cur_mask, sensitive_vars, num_vars, D)
        end
        for child in children
            x_new, y_new= get_assignments_from_mask(child,num_vars,D)
            cached_score, _=get!(global_cache,child) do
                new_score=abs(score(pc,x_new,y_new,delta,num_vars,D))
                return (new_score,1)
            end
            cache[child]=cached_score
        end
        power_factor= 1+(i/(num_vars-1)) # 1 #2-(i/(num_vars-1))
        next_mask=StatsBase.sample(collect(keys(cache)), Weights([x^power_factor for x in collect(values(cache))]))
        x,y=get_assignments_from_mask(next_mask,num_vars,D)
        highest_score=max(highest_score,cache[next_mask])
        push!(visited, next_mask)
        # println(x,y,cache[next_mask])
    end
    reverse!(visited)
    current_score=0
    seen_so_far=0
    for state in visited
        old_score, num_visits=get(global_cache,state,(-1,-1))
        @assert old_score!=-1 # should never happen
        current_score=(current_score*seen_so_far+old_score)/(seen_so_far+1)
        seen_so_far+=1
        new_score=(old_score*num_visits+current_score)/(num_visits+1)
        global_cache[state]=(new_score,num_visits+1)
    end
    return highest_score
end


function get_top_one_random_memo_avg_benchmarking(pc::StructSumNode, sensitive_vars::Set{Int64},delta::Float64, threshold::Float64, num_vars::Int64, D::Int64, score::Function, phi_cache::Dict{Tuple{Int64,Int64,Int64}, Tuple{Float64,Int64}}, score_cache::Dict{Tuple{Int64,Int64,Int64}, Float64}, children_cache::Dict{Tuple{Int64,Int64,Int64}, Array{Tuple{Int64,Int64,Int64},1}}, count::Array{Int64,1})
    remaining= Set([i for i in range(1,stop=num_vars)])
    setdiff!(remaining,Set([D]))
    x=[]
    y=[]
    highest_score=-1
    visited = Array{Tuple{Int64,Int64,Int64},1}()
    for i in range(1,stop=num_vars-1)
        cur_mask=get_mask(x,y)
        cache = Dict{Tuple{Int64,Int64,Int64}, Float64}()
        children= get!(children_cache,cur_mask) do
            get_children_masks(cur_mask, sensitive_vars, num_vars, D)
        end
        for child in children
            cached_score, _=get!(phi_cache,child) do
                pattern_score= get!(score_cache,child) do
                    x_new, y_new= get_assignments_from_mask(child,num_vars,D)
                    new_score=abs(score(pc,x_new,y_new,delta,num_vars,D))
                    highest_score=max(highest_score,new_score)
                    if new_score > threshold
                        count[1]+=1
                    end
                    return new_score
                end
                return (pattern_score,1)
            end
            cache[child]=cached_score
        end
        power_factor=1+(i/(num_vars-1)) # 1 #2-(i/(num_vars-1))
        next_mask=StatsBase.sample(collect(keys(cache)), Weights([x^power_factor for x in collect(values(cache))]))
        x,y=get_assignments_from_mask(next_mask,num_vars,D)
        highest_score=max(highest_score,score_cache[next_mask])
        push!(visited, next_mask)
        # println(x,y,cache[next_mask])
    end
    reverse!(visited)
    current_score=0
    seen_so_far=0
    for state in visited
        old_score, num_visits=get(phi_cache,state,(-1,-1))
        @assert old_score!=-1 # should never happen
        current_score=(current_score*seen_so_far+score_cache[state])/(seen_so_far+1)
        seen_so_far+=1
        new_score=(old_score*num_visits+current_score)/(num_visits+1)
        phi_cache[state]=(new_score,num_visits+1)
    end
    return highest_score
end



#----- SUMMARY PATTERNS HELPERS -----

function get_mask(x::Array{Any,1}, y::Array{Any,1})
    presence_mask=Int64(0) # present?
    negation_mask=Int64(0) # negated?
    sensitive_mask=Int64(0) # if present, is it in x?
    for el in x
        sensitive_mask = sensitive_mask | (1<<abs(el))
        presence_mask = presence_mask | (1<<abs(el))
        if(el<0)
            negation_mask = negation_mask | (1<<abs(el))
        end
    end
    for el in y
        presence_mask = presence_mask | (1<<abs(el))
        if(el<0)
            negation_mask = negation_mask | (1<<abs(el))
        end
    end
    return (presence_mask,negation_mask,sensitive_mask)
end

function get_children_masks(mask::Tuple{Int64,Int64,Int64}, sensitive_vars::Set{Int64}, num_vars::Int64, D::Int64,)
    children=Array{Tuple{Int64,Int64,Int64},1}()
    for el in 1:num_vars
        if abs(el)==D
            continue
        end
        if (mask[1] & (1<<abs(el)))==0 # element missing
            new_presence_mask=mask[1]|(1<<abs(el))
            new_negation_mask=mask[2] # add positive z to y
            new_mask=(new_presence_mask,new_negation_mask,mask[3])
            push!(children, new_mask)
            new_negation_mask=mask[2]|(1<<abs(el)) # add negated z to y
            new_mask=(new_presence_mask,new_negation_mask,mask[3])
            push!(children, new_mask)

            if abs(el) in sensitive_vars
                new_sensitive_mask=mask[3]|(1<<abs(el))
                new_negation_mask=mask[2] # add positive z to x
                new_mask=(new_presence_mask,new_negation_mask,new_sensitive_mask)
                push!(children, new_mask)
                new_negation_mask=mask[2]|(1<<abs(el)) # add negated z to x
                new_mask=(new_presence_mask,new_negation_mask,new_sensitive_mask)
                push!(children, new_mask)
            end
        end
    end
    return children
end

function get_assignments_from_mask(mask::Tuple{Int64,Int64,Int64}, num_vars::Int64, D::Int64)
    x=[]
    y=[]
    for el in 1:num_vars
        if el==D || ((mask[1] & (1<<el))==0)
            continue
        end
        z=el
        if ((mask[2] & (1<<el))!=0) # negated
            z*=-1
        end
        if ((mask[3] & (1<<el))!=0) # sensitive
            append!(x,z)
        else
            append!(y,z)
        end
    end
    return x,y
end


#----- PARETO OPTIMAL PATTERNS -----


# Insert the new element and re-calculate the pareto front
function maintain_front(element:: Tuple{Float64, Float64}, pareto::Array{Tuple{Float64, Float64},1})
    s = Stack{Tuple{Float64, Float64}}()
    push!(pareto, element)
    sort!(pareto, lt = (x, y) -> (x[1] < y[1] || (x[1] == y[1] && x[2] > y[2])))
    for el in pareto
        while !isempty(s) && first(s)[2]<=el[2]
            pop!(s)
        end
        push!(s, el)
    end
    empty!(pareto)
    while !isempty(s)
        push!(pareto, first(s))
        pop!(s)
    end
    reverse!(pareto)
end

function get_pareto_threshold(prob::Float64, pareto::Array{Tuple{Float64, Float64},1})
    threshold = 0
    for el in pareto
        if el[1]>=prob
            threshold=max(threshold, el[2])
        end
    end

    return threshold
end

# Pareto: array {prob, score}
function pareto_front(pc::StructSumNode, x::Array{Any,1}, y::Array{Any,1}, visited::Array{Any,1}, ordering::Array{Int64,1},sensitive_vars::Set{Int64},  delta::Float64, count::Array{Int64,1}, num_vars::Int64, D::Int64, pareto::Array{Tuple{Float64, Float64},1} )
    remaining= Set([i for i in range(1,stop=num_vars)])
    setdiff!(remaining,Set([D]))
    setdiff!(remaining,Set([abs(el) for el in x]))
    setdiff!(remaining,Set([abs(el) for el in y]))
    setdiff!(remaining,Set([el for el in visited]))

    if length(remaining)==0
        return
    end

    z=0
    # pick some z in z\xy
    for el in ordering
        if (el in remaining) && (length(x)!=0 || (el in sensitive_vars))
            z=el
            break
        end
    end

    if z==0
        return
    end

    if z in sensitive_vars
        count[1]+=2
        push!(x,z)
        score, prob = abs_disc_score_with_p(pc,x,y,num_vars,D)
        if score > delta
            maintain_front((prob, score), pareto)
        end
        threshold = max(delta,get_pareto_threshold(prob, pareto))

        # if bound ok, recurse
        if bound(pc,x,y,visited,num_vars,D)>threshold && bound(pc,x,y,num_vars,D)>threshold
            pareto_front(pc,x,y,visited, ordering, sensitive_vars, delta, count,num_vars,D,pareto)
        end
        pop!(x)


        push!(x,-z)
        score, prob = abs_disc_score_with_p(pc,x,y,num_vars,D)
        if score > delta
            maintain_front((prob, score), pareto)
        end
        threshold = max(delta,get_pareto_threshold(prob, pareto))

        # if bound ok, recurse
        if bound(pc,x,y,visited,num_vars,D)>threshold && bound(pc,x,y,num_vars,D)>threshold
            pareto_front(pc,x,y,visited, ordering, sensitive_vars, delta, count,num_vars,D,pareto)
        end
        pop!(x)

    end

    count[1]+=2
    push!(y,z)
    score, prob = abs_disc_score_with_p(pc,x,y,num_vars,D)
    if score > delta
        maintain_front((prob, score), pareto)
    end
    threshold = max(delta,get_pareto_threshold(prob, pareto))

    # if bound ok, recurse
    if bound(pc,x,y,visited,num_vars,D)>threshold && bound(pc,x,y,num_vars,D)>threshold
        pareto_front(pc,x,y,visited, ordering, sensitive_vars, delta, count,num_vars,D,pareto)
    end
    pop!(y)


    push!(y,-z)
    score, prob = abs_disc_score_with_p(pc,x,y,num_vars,D)
    if score > delta
        maintain_front((prob, score), pareto)
    end
    threshold = max(delta,get_pareto_threshold(prob, pareto))

    # if bound ok, recurse
    if bound(pc,x,y,visited,num_vars,D)>threshold && bound(pc,x,y,num_vars,D)>threshold
        pareto_front(pc,x,y,visited, ordering, sensitive_vars, delta, count,num_vars,D,pareto)
    end
    pop!(y)

    push!(visited,abs(z))

    score, prob = abs_disc_score_with_p(pc,x,y,num_vars,D)
    threshold = max(delta,get_pareto_threshold(prob, pareto))

    # if bound ok, recurse
    if bound(pc,x,y,visited,num_vars,D)>threshold && bound(pc,x,y,num_vars,D)>threshold
        pareto_front(pc,x,y,visited, ordering, sensitive_vars, delta, count,num_vars,D,pareto)
    end
    pop!(visited)

    # if count[1]%1000==0
    #     println("total: ", count[1])
    # end

end

function get_pareto_front(pc::StructSumNode,ordering::Array{Int64,1},sensitive_vars::Set{Int64},  delta::Float64, num_vars::Int64, D::Int64)
    x=[]
    y=[]
    visited=[]
    count=Int64.([0])
    pareto = Tuple{Float64, Float64}[]
    pareto_front(pc,x,y,visited, ordering,sensitive_vars, delta, count, num_vars ,D, pareto)
    println(ordering," ",count)
    return pareto, count
end

#----- MINIMAL AND MAXIMAL PATTERNS -----

# returns a) does subgraph have patterns, b) is the node maximal
function get_maximal_patterns_helper(pc::StructSumNode, x::Array{Any,1}, y::Array{Any,1}, ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64, threshold::Float64, count::Array{Int64,1}, num_vars::Int64, D::Int64, cache::Dict{Tuple{Int64,Int64,Int64}, Tuple{Bool,Bool}}, bound::Function, score::Function)
    mask = get_mask(x,y)
    get!(cache, mask) do
        count[1]+=1
        children=get_children_masks(mask,sensitive_vars,num_vars,D)
        current_score=abs(score(pc,x,y,delta,num_vars,D))
        if length(children)==0
            return (current_score>=threshold,false)
        end
        is_maximal_pattern=(current_score>=threshold)
        subgraph_has_patterns=(current_score>=threshold)
        for child in children
            x_new,y_new=get_assignments_from_mask(child, num_vars,D)
            if bound(pc,x_new,y_new,num_vars,D)<threshold
                continue
            end
            child_has_patterns, _ = get_maximal_patterns_helper(pc,x_new, y_new, ordering, sensitive_vars, delta,threshold,count,num_vars, D, cache, bound, score)
            subgraph_has_patterns=subgraph_has_patterns||child_has_patterns
            is_maximal_pattern=is_maximal_pattern&&(!child_has_patterns)
        end

        if is_maximal_pattern
            count[2]+=1
        end

        return subgraph_has_patterns, is_maximal_pattern
    end

end

function get_maximal_patterns(pc::StructSumNode,  ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64, threshold::Float64, num_vars::Int64, D::Int64, bound::Function, score::Function)
    cache = Dict{Tuple{Int64,Int64,Int64}, Tuple{Bool,Bool}}()
    x=[]
    y=[]
    counts=Int64.([0,0])
    get_maximal_patterns_helper(pc,x,y,ordering,sensitive_vars,delta,threshold,counts,num_vars,D,cache,bound,score)
    println(counts)
end

# returns a) is everything in my subgraph a pattern (including myself)
function get_minimal_patterns_helper(pc::StructSumNode, x::Array{Any,1}, y::Array{Any,1}, ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64, threshold::Float64, count::Array{Int64,1}, num_vars::Int64, D::Int64, cache::Dict{Tuple{Int64,Int64,Int64}, Bool}, bound::Function, score::Function)
    mask = get_mask(x,y)
    get!(cache, mask) do
        count[1]+=1
        children=get_children_masks(mask,sensitive_vars,num_vars,D)
        if length(children)==0
            return abs(score(pc,x,y,delta,num_vars,D))>=threshold
        end

        is_subgraph_full=abs(score(pc,x,y,delta,num_vars,D))>=threshold
        # print(children)
        for child in children
            x_new,y_new=get_assignments_from_mask(child, num_vars,D)
            # if lower_bound(pc,x_new,y_new,num_vars,D)>=threshold # WE DO NOT HAVE A LOWER BOUND THOUGH :(
            #     continue
            # end
            is_child_subgraph_full = get_minimal_patterns_helper(pc,x_new, y_new, ordering, sensitive_vars, delta,threshold,count,num_vars, D, cache, bound, score)
            is_subgraph_full=is_subgraph_full&&is_child_subgraph_full
        end

        if is_subgraph_full   # this is a minimal node
            # println(x,y,is_subgraph_full)
            count[2]+=1
        end

        return is_subgraph_full
    end

end

function finalize_minimal_patterns(pc::StructSumNode, x::Array{Any,1}, y::Array{Any,1}, ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64, threshold::Float64, count::Array{Int64,1}, num_vars::Int64, D::Int64, cache::Dict{Tuple{Int64,Int64,Int64}, Bool}, is_minimal_pattern::Dict{Tuple{Int64,Int64,Int64}, Bool}, bound::Function, score::Function)
    to_visit=Set()
    next_to_visit=Set()
    root=get_mask(x,y);
    push!(to_visit,root)

    do_not_visit=Set()

    while length(to_visit)!=0

        additional_do_not_visit=Set()
        for mask in do_not_visit
            children=get_children_masks(mask,sensitive_vars,num_vars,D)
            union!(additional_do_not_visit, Set(children))
        end
        union!(do_not_visit, additional_do_not_visit)

        cur_minimal_children=Set()
        for mask in to_visit
            is_minimal=get!(cache, mask, false)
            children=get_children_masks(mask,sensitive_vars,num_vars,D)
            if is_minimal   # this is a minimal node
                x_new,y_new=get_assignments_from_mask(mask, num_vars,D)
                println(x_new,y_new)
                count[2]+=1
                union!(cur_minimal_children, Set(children))
                is_minimal_pattern[mask]=true
            else
                union!(next_to_visit, Set(children))
            end
        end

        union!(do_not_visit,cur_minimal_children)
        setdiff!(next_to_visit, do_not_visit)
        to_visit=copy(next_to_visit)
        next_to_visit=Set()
    end
end

function get_minimal_patterns(pc::StructSumNode,  ordering::Array{Int64,1},sensitive_vars::Set{Int64}, delta::Float64, threshold::Float64, num_vars::Int64, D::Int64, bound::Function, score::Function)
    cache = Dict{Tuple{Int64,Int64,Int64}, Bool}()
    is_minimal_pattern = Dict{Tuple{Int64,Int64,Int64}, Bool}()
    x=[]
    y=[]
    counts=Int64.([0,0])
    get_minimal_patterns_helper(pc,x,y,ordering,sensitive_vars,delta,threshold,counts,num_vars,D,cache,bound,score)
    counts=Int64.([0,0])
    finalize_minimal_patterns(pc,x,y,ordering,sensitive_vars,delta,threshold,counts,num_vars,D,cache,is_minimal_pattern,bound,score)
    println(counts)
end


#----- MAIN SCRIPT -----

s = ArgParseSettings()
@add_arg_table s begin
    "--scoretype", "-s"
        help = "discrimination/divergence"
    "--dataset", "-x"
        help = "compas/adult/income"
    "--threshold", "-t"
        help = "threshold to be considered a pattern"
        arg_type = Float64
        default = -1.0
    "--delta", "-d"
        help = "delta for divergence score calculation"
        arg_type = Float64
        default = -1.0
end

parsed_args = parse_args(ARGS, s)
if(parsed_args["dataset"]=="compas")
    # COMPAS
    pc,vtree = load_struct_prob_circuit("compas_good.psdd", "compas_good.vtree")
    ordering=Int64.([7,4,3,5,2,1,6])
    sensitive_vars=Set(Int64.([4,5,6,7]))
    num_vars=8
    D=8
end
if(parsed_args["dataset"]=="adult")
    # ADULT
    data_path="./data/adult_binerized.csv";
    decision_column="target";
    pc, vtree=get_adult_circuit(data_path, decision_column, 32)
    ordering=Int64.([7,3,4,13,12,10,5,11,2,9,1,6,8])
    sensitive_vars=Set([6,9,10,11])
    num_vars=14
    D=14
end
if(parsed_args["dataset"]=="income")
    # ACS INCOME
    data_path="./data/ACS_Income_binerized.csv";
    decision_column="D";
    pc,vtree = learn_pc(data_path,"D")
    ordering=Int64.([5,4,8,2,3,7,1,6])
    sensitive_vars=Set(Int64.([7,8]))
    num_vars=9
    D=9
end

th=parsed_args["threshold"]
delta=parsed_args["delta"]

if(parsed_args["scoretype"]=="discrimination")
    num_disc_patterns(pc,ordering,sensitive_vars,th,num_vars,D)
else
    num_divergence_patterns(pc,ordering,sensitive_vars,th,num_vars,D)
end
