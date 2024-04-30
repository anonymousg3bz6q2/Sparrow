#pragma once

#include "sumcheck.h"
#include "config_pc.hpp"
#include "GKR.h"
#include "BuildTree.h"
#include "witness_stream.h"

struct stream{
	string file_name;
	int row_size,col_size,size;
	int padded_size_col;

};

typedef struct stream stream;

struct partition_SNARK_data_streaming{
	stream_descriptor input_data,permuted_data,paths,paths_aux;
	stream_descriptor bit_vectors,diff_data,path_diff,input_aux;
	vector<F> powers,power_bits;
	vector<int> int_pows,label;
	vector<int> data_partitions;
	vector<F> compress_vector,tree_compress_vector,compressed_tree;
	vector<vector<F>> tree;
	/*
	stream input_data;
	stream permuted_data;
	stream paths;
	stream paths_aux;
	stream bit_vectors;
	stream diff_data;
	vector<F> powers,power_bits;
	vector<int> int_pows,label;
	vector<int> data_partitions;
	vector<F> tree_compress_vector,compressed_tree;
	vector<vector<F>> tree;
	stream path_diff,input_aux;	
	*/
};

struct histogram_SNARK_data_streaming{
	stream_descriptor read_transcript,write_transcript,input_data,read_write_transcript,histograms_counter;
	//stream read_transcript,write_transcript,input_data;
	vector<vector<F>> memory_init;
	vector<vector<F>> final_memory;
	vector<F> compressed_init,compressed_final,random_vector;
	stream_descriptor input_aux;	
};


typedef struct partition_SNARK_data_streaming partition_SNARK_data_streaming;
typedef struct histogram_SNARK_data_streaming histogram_SNARK_data_streaming;

void prove_correct_partitions_streaming(partition_SNARK_data_streaming data, Dataset &D, vector<vector<F>> Tree,int max_depth);
partition_SNARK_data_streaming get_partitions_transcript_streaming(Dataset D, vector<Dataset> Partitions, vector<vector<Node>> Tree, vector<vector<F>> tree, int max_depth, int write);
histogram_SNARK_data_streaming get_histograms_transcript_streaming(Dataset &D, vector<int> data_partitions, vector<int> label, vector<vector<Node>> Tree, int Attr, int write);
void prove_correct_histograms_streaming(histogram_SNARK_data_streaming data, int Attr, F previous_r);