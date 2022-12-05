# Sample script that estimates number of trails required by the
# sampling algorithm to find the top 1 discrimination pattern for
# PC trained on the COMPAS dataset.

# This script keeps running the sampling algorithm until it finds
# the top 1 pattern.

# In our experiments, for instance, we perform these trials multiple
# times and report the average and standard deviations.

pc,vtree = load_struct_prob_circuit("compas_good.psdd", "compas_good.vtree")
ordering=Int64.([7,4,3,5,2,1,6])
sensitive_vars=Set(Int64.([4,5,6,7]))
num_vars=8
D=8

delta=-1.0
th=0.1

children_cache=Dict{Tuple{Int64,Int64,Int64}, Array{Tuple{Int64,Int64,Int64},1}}()
phi_cache=Dict{Tuple{Int64,Int64,Int64}, Tuple{Float64,Int64}}()
score_cache=Dict{Tuple{Int64,Int64,Int64}, Float64}()
best_score=-1
i=1

search_count=Int64.([0])
# Top 1 Pattern Score 0.2236 obtained using exact search method get_top_k
while(best_score<0.2236)
    new_try=get_top_one_random_memo_avg_benchmarking(pc,sensitive_vars,delta, th,num_vars,D, disc_score,phi_cache,score_cache, children_cache, search_count)
    if new_try>best_score
        global best_score=new_try
        println(i, " ",best_score)
    end
    global i+=1
end

println(search_count[1])
