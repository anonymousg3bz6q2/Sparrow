#pragma once

#include "sumcheck.h"
#include "config_pc.hpp"
#include "GKR.h"
#include "BuildTree.h"
#include "witness_stream.h"

struct partition_SNARK_data_streaming_forest{
	stream_descriptor input_data,permuted_data,paths,paths_aux;
	stream_descriptor bit_vectors,diff_data,path_diff,input_aux;
	vector<F> compress_vector,tree_compress_vector;
    vector<vector<F>> compressed_tree;
	vector<vector<F>> tree;
	vector<vector<F>> powers,power_bits;
	vector<vector<int>> int_pows;
	vector<int> data_partitions,label;
	
};
struct histogram_SNARK_data_streaming_forest{
	stream_descriptor read_transcript,write_transcript,input_data,read_write_transcript,histograms_counter,compressed_final;
	//stream read_transcript,write_transcript,input_data;
	vector<vector<int>> memory_init;
	vector<vector<vector<F>>> final_memory;
	vector<F> compressed_init,random_vector;
	stream_descriptor input_aux;	
};

struct nodes_histogram_data_streaming{
	stream_descriptor node_histograms,leaf_histograms,witness_hist,out_hist;
	vector<vector<vector<int>>> node_index_matrix,leaf_index_matrix,leaf_matrix;
	vector<vector<F>> node_coeff,leaf_coeff;
};

struct split_SNARK_streaming_forest{
	int nodes,attr;
	vector<vector<vector<vector<F>>>> node_histograms;
	vector<vector<vector<unsigned long long int>>> sums;
	stream_descriptor gini_inputs,ginis;
	stream_descriptor quotients,remainders,inverses,N,divisors,dividents;
	vector<vector<unsigned long long int>> best_gini;
};


struct streaming_bagging_SNARK{
	F seed;
	stream_descriptor randomness,randomness_quotient,randomness_remainder,bits_fd;
	stream_descriptor pairs,compressed_pairs,s1,s2;
	vector<F> discretized_table;
	vector<F> powers;
	vector<F> power_bits;
};


typedef struct partition_SNARK_data_streaming_forest partition_SNARK_data_streaming_forest;
typedef struct split_SNARK_streaming_forest split_SNARK_streaming_forest;
typedef struct streaming_bagging_SNARK streaming_bagging_SNARK;
typedef struct nodes_histogram_data_streaming nodes_histogram_data_streaming;

void prove_correct_partitions_streaming_forest(partition_SNARK_data_streaming_forest data, Dataset &D, vector<vector<vector<F>>> forest,int max_depth);
void prove_correct_histograms_streaming_forest(histogram_SNARK_data_streaming_forest data, int Attr, F previous_r);


partition_SNARK_data_streaming_forest get_partitions_transcript_streaming_forest(Dataset D, vector<vector<int>> Partitions, vector<vector<vector<Node>>> _forest,
 vector<vector<vector<F>>> forest, int max_depth, int write);
histogram_SNARK_data_streaming_forest get_histograms_transcript_streaming_forest(Dataset &D,  vector<vector<vector<Node>>> forest);

void prove_correct_node_histograms_streaming_forest(nodes_histogram_data_streaming data, int trees, int attr, int leaves , F previous_r);
nodes_histogram_data_streaming get_node_histograms_transcript_forest_stream(vector<vector<vector<int>>> leaf_index_matrix, vector<vector<vector<int>>> leaf_matrix,
	int attr,vector<vector<vector<F>>> _leaf_coeff,int trees,int leaves);

split_SNARK_streaming_forest get_split_transcript_streaming_forest( int trees, int nodes, int attr );
void prove_correct_split_forest(split_SNARK_streaming_forest &data, F previous_r);

streaming_bagging_SNARK get_split_transcript_streaming_forest(int dataset_size, int trees );
void prove_bagging(streaming_bagging_SNARK data);