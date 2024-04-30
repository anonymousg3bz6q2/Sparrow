#pragma once
#include "config_pc.hpp"
#include "BuildTree_streaming.h"
#include "BuildForest_streaming.h"
#include "witness_stream.h"


struct mul_tree_proof_stream{
	F final_r,final_eval;
    F prod;
	vector<F> individual_randomness,global_randomness,r;
	vector<F> out;
		
};

struct recursion_proof{
	G1 comm1,comm2;
	F sum,sum1,sum2;
	proof P1,P2;
	vector<G1> Proof1,Proof2;
	vector<F> a1,a2;
};

struct proof_stream{
	F sum,new_sum;
    int c;
	size_t size;
    vector<vector<F>> polynomials;
    vector<F> randomness,beta1,beta2,a;
	vector<proof> P;
	vector<F> vr;
	recursion_proof RP;

};

typedef struct mul_tree_proof_stream mul_tree_proof_stream; 
typedef struct proof_stream proof_stream; 
typedef struct recursion_proof recursion_proof; 



void generate_mul_tree_transcript(stream_descriptor fd, int vectors, int size);
void _prove_bit_decomposition_stream(stream_descriptor bits_fd, size_t size, vector<F> r1, F previous_sum, F previous_r, int domain);
proof_stream generate_3product_sumcheck_proof_disk(stream_descriptor fp1, stream_descriptor fp2, size_t size, vector<F> beta_rand, F previous_r, int mod);
vector<F> prepare_matrix_streaming(vector<stream_descriptor> fd, vector<size_t> fd_cols, vector<size_t> fd_size, size_t row_size, vector<F> r, int cols);
mul_tree_proof_stream prove_multiplication_tree_stream(stream_descriptor fd,int vectors,int size, F previous_r, vector<F> prev_x);
mul_tree_proof_stream prove_multiplication_tree_stream_shallow(stream_descriptor fd,int vectors,int size, F previous_r, int distance, vector<F> prev_x);
proof_stream generate_2product_sumcheck_proof_disk_beta(stream_descriptor fp1, vector<vector<F>> beta_rand,vector<F> a,size_t size, F previous_r);
void streaming_sumcheck_partition_1(partition_SNARK_data_streaming data);
void streaming_sumcheck_partition_2(partition_SNARK_data_streaming data, vector<vector<F>> Tree);
void streaming_sumcheck_partition_3(partition_SNARK_data_streaming data, vector<vector<F>> Tree);
void streaming_sumcheck_leaves_1(histogram_SNARK_data_streaming data, int Attr, F previous_r);
void streaming_sumcheck_leaves_2(histogram_SNARK_data_streaming data, int Attr, F previous_r);
proof_stream generate_3product_sumcheck_proof_stream(stream_descriptor fp1, stream_descriptor fp2, size_t size, vector<F> beta_rand, F previous_r, int mod);
proof_stream generate_2product_sumcheck_proof_stream_beta(stream_descriptor fp1, vector<vector<F>> beta_rand,vector<F> a,size_t size, F previous_r);
proof_stream generate_2product_sumcheck_proof_stream(stream_descriptor fp1, stream_descriptor fp2,size_t size, F previous_r);
void prove_permutation(vector<stream_descriptor> perm1,vector<stream_descriptor> perm2, F previous_r);
proof_stream generate_3product_sumcheck_proof_stream_batch(stream_descriptor fp1, vector<size_t> size, vector<F> a_r, int distance, vector<F> beta_rand, F previous_r, int mod);

proof_stream generate_2product_sumcheck_proof_stream_naive(stream_descriptor fp1,stream_descriptor fp2, size_t size, F previous_r);
void streaming_forest_partition_sumcheck_1(partition_SNARK_data_streaming_forest data, int forest_size );
void streaming_forest_partition_sumcheck_2(partition_SNARK_data_streaming_forest data, vector<vector<vector<F>>> forest);
void streaming_forest_partition_sumcheck_3(partition_SNARK_data_streaming_forest data, vector<vector<vector<F>>> forest);
void streaming_forest_sumcheck_leaves_1( histogram_SNARK_data_streaming_forest data, int Attr, F previous_r);
void streaming_forest_sumcheck_leaves_2( histogram_SNARK_data_streaming_forest data, int Attr, F previous_r);
	
void streaming_gini_sumcheck_1( split_SNARK_streaming_forest data,vector<F> x, int Attr, F final_eval, F previous_r,
	vector<F> &x_dividents, vector<F> &x_divisors, F &divident_eval, F &divisor_eval);
void streaming_gini_sumcheck_2( split_SNARK_streaming_forest data, vector<F> x_dividents,vector<F> x_divisors ,F divisors_eval, F dividents_eval, F previous_r);
recursion_proof reduce_proof_size(vector<F> poly, int c, F omega, F r,F previous_r);
void streaming_bagging_1( streaming_bagging_SNARK data, vector<F> &x_compressed, F &compresssed_eval , F previous_r);
void streaming_bagging_2(streaming_bagging_SNARK data, vector<F> x_compressed, F compresssed_eval , F previous_r);
