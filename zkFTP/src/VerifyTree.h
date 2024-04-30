#pragma once

#include "BuildTree.h"
#include "sumcheck.h"
#include "config_pc.hpp"
#include "GKR.h"




partition_indexes verify_partition_proof(struct partition_SNARK_proof P, vector<F> &x, vector<F> &y);
histogram_indexes verify_histogram_proof(struct histogram_SNARK_proof P, vector<F> &x, vector<F> &y);
split_indexes verify_split_proof(struct split_SNARK_proof P, vector<F> &x, vector<F> &y);
node_histogram_indexes verify_node_histogram_proof(struct nodes_histogram_SNARK_proof P,vector<F> &x, vector<F> &y);
