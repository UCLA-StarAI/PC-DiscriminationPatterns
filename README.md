# Certifying Fairness of Probabilistic Circuits

This repository contains the implementation of the exact and approximate search algorithms presented in our AAAI23 paper `Certifying Fairness of Probabilistic Circuits`. The code is written in Julia.

## Requirements

- Julia 1.5.3
- Julia Packages
    - Juice.jl Packages: ProbabilisticCircuits, LogicCircuits
    - CSV
    - DataFrames
    - Random
    - DataStructures
    - Profile
    - Combinatorics
    - ArgParse
    - StatsBase

Julia can be obtained from `https://julialang.org/downloads/oldreleases/`. The required Julia packages can be installed by running `import Pkg; Pkg.add("PackageName")` in Julia.

## Usage

All the required methods are provided in a modular format in `pc_fairness.jl`. This file also includes a main script that allows the user to quickly check PCs learnt on different datasets for discrimination and divergence patterns using our exact search algorithm.

The program takes 4 arguments:
-    `--scoretype / -s` :  "discrimination"/"divergence"
- `--dataset / -x` : "compas"/"adult"/"income"
-  `--threshold / -t` : `Float64` threshold to be considered a pattern.
- `--delta / -d` : `Float64` delta for divergence score calculation.

Sample usage: `julia  pc_fairness.jl -s discrimination -x compas -t 0.1 `

The function signatures in `pc_fairness.jl` are self-descriptive and the user is encouraged to flexibly leverage these methods and modify the main script according to their needs. For instance, one could replace `num_disc_patterns` with `get_maximal_patterns` in the main script to obtain maximal patterns instead. We also provide sample scripts for evaluation of our sampling algorithm as example usage (see `sampling_experiment.jl`).

Some of the most useful top level functions are:
- `learn_pc`: Learn a PC from a given dataset.
- `get_likelihood`: Obtain log likelihood and average log likelihood per instance of PC.
- `num_disc_patterns`: Find number of discrimination patterns in PC.
- `num_divergence_patterns`: Find number of divergence patterns in PC.
- `get_top_k`: Find top k discrimination/divergence patterns in PC.
- `get_top_one_random_memo_avg`: Runs one iteration of the sampling algorithm and returns the highest score of pattern found. Other partial patterns visited in the run can be optinally cached.
- `get_pareto_front`: Find the set of pareto optimal patterns.
- `get_maximal_patterns`: Find the set of maximal patterns.
- `get_minimal_patterns`: Find the set of minimal patterns.

## Other Notes

- All the datasets are included in the `data` directory. The user can add more datasets to the directory and learn a PC on the dataset using the `learn_pc` method. The user can leverage our library to check the learnt model for fairness.

- We provide pre-trained PCs for COMPAS datasets: `compas_good.psdd` and `compas_good.vtree`.


