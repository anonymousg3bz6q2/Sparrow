#pragma once

#include "sumcheck.h"
#include "config_pc.hpp"
#include "GKR.h"
#include "BuildTree.h"

struct partition_SNARK_data_forest{
	vector<vector<F>> input_data;
	vector<vector<F>> permuted_data;
	vector<vector<F>> input_aux;
	vector<vector<F>> paths;
	vector<vector<F>> paths_aux;
	vector<vector<F>> bit_vectors;
	vector<vector<F>> diff_data;
	vector<vector<F>> powers,power_bits;
	vector<vector<int>> int_pows;
	vector<int> data_partitions,label;
	vector<F> path_diff;
};

struct histogram_SNARK_data_forest{
	vector<vector<vector<F>>> read_transcript,final_memory,memory_init,write_transcript;
	vector<vector<F>> input_data;
	vector<int> data_partitions,label;
	vector<vector<int>> idx_matrix;
};

struct nodes_histogram_SNARK_data_forest{
	vector<vector<vector<vector<F>>>> node_histograms,leaf_histograms;
	vector<vector<vector<int>>> node_index_matrix,leaf_index_matrix,leaf_matrix;
	vector<vector<F>> node_coeff,leaf_coeff;
	vector<vector<vector<F>>> witness_hist,out_hist;

};
struct split_SNARK_data_forest{
	int nodes,attr;
	vector<vector<vector<vector<F>>>> node_histograms;
	vector<vector<vector<F>>> sums,gini_inputs,ginis;
	vector<vector<vector<F>>> quotients,remainders,inverses,N,divisors,dividents;
	vector<vector<F>> best_gini;
};


typedef struct partition_SNARK_data_forest partition_SNARK_data_forest;
typedef struct histogram_SNARK_data_forest histogram_SNARK_data_forest;

partition_SNARK_proof prove_correct_partitions_forest(partition_SNARK_data_forest &data, Dataset &D, vector<vector<vector<F>>> Tree,int max_depth);
void get_partitions_forest(partition_SNARK_data_forest &data,Dataset D, vector<vector<int>> Partitions, vector<vector<vector<Node>>> Trees);
void get_histograms_forest(histogram_SNARK_data_forest &transcript ,Dataset &D, vector<int> data_partitions, vector<vector<int>> idx_matrix, vector<int> label, vector<vector<vector<F>>> forest, int Attr);
histogram_SNARK_proof prove_histograms_forest(histogram_SNARK_data_forest &data, int Attr, int forest_size, F previous_r);
nodes_histogram_SNARK_data_forest get_node_histograms_transcript_forest(vector<vector<F>> _histograms, vector<vector<vector<int>>> leaf_index_matrix, vector<vector<vector<int>>> leaf_matrix,int attr,vector<vector<vector<F>>> _leaf_coeff,int trees,int leaves);
nodes_histogram_SNARK_proof prove_node_histograms_forest(nodes_histogram_SNARK_data_forest &data, int trees , F previous_r);
void get_split_transcript_forest(split_SNARK_data &data,vector<vector<vector<F>>> node_histograms, int trees);