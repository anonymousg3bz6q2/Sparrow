#pragma once

#include "sumcheck.h"
#include "config_pc.hpp"
#include "GKR.h"

struct Dataset{
	vector<int> type;
	vector<int> remaining_attr;
	vector<vector<int>> data;
	vector<int> label;
	vector<int> indexes;
};	

struct Node{
	int split_value;
	int attr; // the split attribute
	int h; // the height of the node
	int pos; // position in the given height between [0,2^h]
	int classification;
	int direction;
};

struct partition_SNARK_data{

	vector<vector<F>> input_data;
	vector<vector<F>> permuted_data;
	vector<vector<F>> paths;
	vector<vector<F>> paths_aux;
	vector<vector<F>> bit_vectors;
	vector<vector<F>> diff_data;
	vector<F> powers,power_bits;
	vector<int> int_pows,label;
	vector<int> data_partitions;
	vector<F> path_diff;
};

struct partition_SNARK_proof{
	F commitment;
	vector<F> compress_vector,tree_compress_vector;
	partition_sumcheck1_proof P1;
	partition_sumcheck2_proof P2;
	partition_sumcheck3_proof P3;
	proof GKR_proof1;
	F path_eval,perm_data_eval;
	vector<F> path_eval_x,perm_data_eval_x;
	F x1,x2;
	F final_rand;
};

struct histogram_SNARK_proof{
	F previous_r,commitments;
	leaves_sumcheck_proof P1;
	mul_tree_proof mP1,mP2;
	proof sP1,sP2,sP3,sP4,sP5;
	F final_rand;
};

struct histogram_SNARK_data{
	vector<vector<F>> read_transcript,write_transcript;
	vector<vector<F>> memory_init;
	vector<vector<F>> final_memory;
	vector<vector<F>> input_data;	
};

struct nodes_histogram_SNARK_data{
	vector<vector<vector<F>>> node_histograms,leaf_histograms;
	vector<vector<int>> node_index_matrix,leaf_index_matrix,leaf_matrix;
	vector<F> node_coeff,leaf_coeff;

};

struct nodes_histogram_SNARK_proof{
	F commitment,previous_r,final_rand;
	proof GKR_proof1,GKR_proof2;
	proof sP1,sP2,sP3,sP4;
	vector<F> r;
	F node_eval,leaf_eval,comp_wit_eval,comp_node_eval,comp_out_eval,comp_leaf_eval,wit_eval;
};

struct split_SNARK_data{
	int nodes,attr;
	vector<vector<vector<F>>> node_histograms,sums,gini_inputs,ginis;
	vector<vector<vector<F>>> quotients,remainders,inverses,N,divisors,dividents;
	vector<vector<F>> best_gini;
};

struct split_SNARK_proof{
	F commitment,previous_r;
	lookup_proof lP1,lP2;
	mul_tree_proof mP1;
	F ginis_eval1,best_gini_eval1,ginis_eval2,best_gini_eval2;
	gini_sumcheck1_proof P1;
	gini_sumcheck2_proof P2;
	proof GKR_proof1;
};

typedef struct Dataset;
typedef struct Node;
typedef struct partition_SNARK_data;
typedef struct histogram_SNARK_data;
typedef struct nodes_histogram_SNARK_data;
typedef struct split_SNARK_data;
typedef struct partition_SNARK_proof partition_SNARK_proof;
typedef struct histogram_SNARK_proof;
typedef struct split_SNARK_proof;
typedef struct nodes_histogram_SNARK_proof;

void LoadDummyDataset_inference(int test_instances, Dataset &D_train,Dataset &D_test);
void LoadDummyDataset(int test_instances,int instances, int attributes , Dataset &D_train,Dataset &D_test);
void LoadDummyDataset2(int test_instances,int instances, int attributes , Dataset &D_train,Dataset &D_test);
void LoadDiabetesDataset(Dataset &D, string fname);
vector<vector<Node>> BuildTree(Dataset D,vector<Dataset> &Partitions, int max_depth);
void LoadDiabetesDataset(Dataset &D_train,Dataset &D_test, int test_instances, string fname);
void LoadIrisDataset(Dataset &D_train,Dataset &D_test);

partition_SNARK_data get_partitions_transcript(Dataset D, vector<Dataset> Partitions, vector<vector<Node>> Tree);
partition_SNARK_proof prove_correct_partitions(partition_SNARK_data data, Dataset &D, vector<vector<F>> Tree,int max_depth);
histogram_SNARK_data get_histograms_transcript(Dataset &D, vector<int> data, vector<int> label, vector<vector<Node>> Tree, int Attr);
histogram_SNARK_proof prove_histograms(histogram_SNARK_data data, int Attr, F previous_r);
nodes_histogram_SNARK_proof prove_node_histograms(nodes_histogram_SNARK_data data, F previous_r);
nodes_histogram_SNARK_data get_node_histograms_transcript(vector<vector<F>> _histograms, vector<vector<int>> leaf_index_matrix, vector<vector<int>> leaf_matrix,int attr,vector<vector<F>> _leaf_coeff,int leaves);
split_SNARK_data get_split_transcript(vector<vector<vector<F>>> node_histograms);
split_SNARK_proof prove_split(split_SNARK_data data, F previous_r);

