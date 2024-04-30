#pragma once
#include "config_pc.hpp"
#include "BuildTree_streaming.h"

struct mul_tree_proof_streaming{
	F final_r,final_eval;
	vector<F> individual_randomness,global_randomness,r;
		
};

struct proof_streaming{
	F sum,new_sum;
	vector<proof> P;
	vector<F> randomness;
	vector<F> vr;
};

typedef struct mul_tree_proof_streaming mul_tree_proof_streaming; 
typedef struct proof_streaming proof_streaming; 



void generate_mul_tree_transcript(int fd, int vectors, int size);
void _prove_bit_decomposition_stream(int bits_fd, size_t size, vector<F> r1, F previous_sum, F previous_r, int domain);
proof_streaming generate_3product_sumcheck_proof_disk(int fp1, int fp2, size_t size, vector<F> beta_rand, F previous_r, int mod);
vector<F> prepare_matrix_streaming(vector<int> fd, vector<size_t> fd_cols, vector<size_t> fd_size, size_t row_size, vector<F> r, int cols);
mul_tree_proof_streaming prove_multiplication_tree_stream(int fd,int vectors,int size, F previous_r, vector<F> prev_x);
proof_streaming generate_2product_sumcheck_proof_disk_beta(int fp1, vector<vector<F>> beta_rand,vector<F> a,size_t size, F previous_r);
void streaming_sumcheck_partition_1(partition_SNARK_data_streaming data);
void streaming_sumcheck_partition_2(partition_SNARK_data_streaming data, vector<vector<F>> Tree);
void streaming_sumcheck_partition_3(partition_SNARK_data_streaming data, vector<vector<F>> Tree);
void streaming_sumcheck_leaves_1(histogram_SNARK_data_streaming data, int Attr, F previous_r);
void streaming_sumcheck_leaves_2(histogram_SNARK_data_streaming data, int Attr, F previous_r);
