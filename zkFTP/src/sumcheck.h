#pragma once
#include "config_pc.hpp"
#include "GKR.h"





struct mul_tree_proof{
	F initial_randomness;
	// If we have a single product
	size_t size;
	F in1,in2;
	F out_eval;
	vector<struct proof> proofs;
	vector<F> output;
	vector<F> final_r;
	vector<F> global_randomness,individual_randomness;
	vector<F> partial_eval;
	F final_eval;
};

struct lookup_proof{
	F previous_r;
	mul_tree_proof mP1,mP2;
	vector<F> mul_out1,mul_out2,read_eval_x,write_eval_x,indexes_eval,x1;
	F read_eval,read_eval1,read_eval2,write_eval,write_eval1,write_eval2,sum1,sum2;
	F final_eval;
	F final_rand;
	vector<F> input_x;

};

typedef struct lookup_proof;
typedef struct mul_tree_proof mul_tree_proof;

struct partition_sumcheck1_proof{
	F previous_r,final_rand,_c;
	mul_tree_proof mP1,mP2;
	proof sP1,sP2,sP3,sP4;

	F eval_input;
	F eval_perm_input;
	F eval1_data,eval2_data,eval3_data;
	F eval1_perm_data,eval2_perm_data;
	
	vector<F> eval1_data_x,eval2_data_x,eval3_data_x; 
	vector<F> eval1_perm_data_x,eval2_perm_data_x;

};

struct partition_sumcheck2_proof{
	F previous_r;
	F final_rand;
	mul_tree_proof mP1,mP2,mP3;
	proof sP1,sP2,sP3,sP4;
	proof tP1,tP2;
    F eval_powers1,eval_powers2,eval_powers3,eval_powers4,eval_tree,eval_bits1,final_powers_input_eval,sum1;

	vector<F> eval_powers1_x,eval_powers2_x,eval_powers3_x,eval_powers4_x,eval_tree_x,eval_bits1_x,final_powers_input_eval_x;
};

struct partition_sumcheck3_proof{
	F previous_r;
	F final_rand;
	F diff_eval;
	vector<F> diff_eval_x;
	vector<proof> range_proof;
};

struct leaves_sumcheck_proof{
	F previous_r;
	F final_rand,sparse_vector_eval;
	vector<vector<F>> readwrite_x,input_x,metadata_x;
	vector<F> write_evals,read_evals,input_evals,metadata_evals;
	proof sP1,sP2,sP3,sP4;
};

struct gini_sumcheck1_proof{
	F previous_r,final_rand;
	proof tP1,tP2,tP3,tP4;
	proof sP;
	F eval1,eval2,cond_eval1,cond_eval2,cond_eval3;
	vector<F> a,dividents_eval;
};

struct gini_sumcheck2_proof{
	F previous_r,final_rand;
	proof tP1,tP2,tP3;
	proof sP1,sP2;
	vector<F> r1,r2;
	F square_N_eval,pairwise_prod_eval;
	F eval1_N0,eval1_N1,eval1_N,eval2_N;
	F gini_eval1,gini_eval2,gini_eval3,gini_eval4;
};


typedef struct partition_sumcheck1_proof partition_sumcheck1_proof;
typedef struct partition_sumcheck2_proof partition_sumcheck2_proof;
typedef struct partition_sumcheck3_proof partition_sumcheck3_proof;
typedef struct leaves_sumcheck_proof leaves_sumcheck_proof;
typedef struct gini_sumcheck1_proof gini_sumcheck1_proof;
typedef struct gini_sumcheck2_proof gini_sumcheck2_proof;



struct proof generate_2product_sumcheck_proof_disk(int fp1, int fp2,int size, F previous_r);
struct proof generate_2product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, F previous_r);
struct proof generate_2product_sumcheck_proof_disk_const(int fp1, int fp2,int size, F previous_r);
struct proof generate_2product_sumcheck_proof_disk_hybrid(int fp1, int fp2,int size, F previous_r);


struct proof _prove_binary(vector<F> bits);
struct proof _prove_matrix2vector(vector<vector<F>> M, vector<F> v, vector<F> r, F previous_sum,F previous_r);

vector<proof> _prove_bit_decomposition(vector<F> bits, vector<F> r1, F previous_sum,F previous_r, int domain);
mul_tree_proof prove_multiplication_tree_new(vector<vector<F>> input, F previous_r, vector<F> prev_x);
mul_tree_proof prove_multiplication_tree(vector<vector<F>> in, F previous_r, vector<F> prev_x);
struct proof generate_2product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, F previous_r);

gini_sumcheck1_proof gini_sumcheck_1(vector<F> &input, F previous_r, vector<F> x, F final_eval, int nodes, int attr, int bin_size);
gini_sumcheck2_proof gini_sumcheck_2(vector<F> &input,F previous_r, vector<F> x_dividents, vector<F> x_divisors, F dividents_eval,F divisors_eval, int nodes, int attr, int bin_size);

mul_tree_proof leaves_sumcheck_1(vector<F> &compressed_read,vector<F> &compressed_write,F previous_r);
leaves_sumcheck_proof leaves_sumcheck_2(vector<F> input,vector<F> input_metadata,vector<F> read_transcript,vector<F> write_transcript,vector<F> eval2_x, vector<F> beta1, vector<F> beta2, F eva1, F eval2, F previous_r);
leaves_sumcheck_proof forest_leaves_sumcheck_2(vector<F> input, vector<F> idx,vector<F> &partitions,vector<F> labels, vector<F> &read_transcript,
	vector<F> &write_transcript, vector<F> eval2_x, vector<F> beta1, vector<F> beta2, F eval1, F eval2, int forest_size , F previous_r );


partition_sumcheck1_proof partition_sumcheck_1( vector<vector<F>> data, vector<vector<F>> permuted_data, vector<F> compress_vector, F _c,F previous_r);
partition_sumcheck2_proof partition_sumcheck_2(vector<F> compressed_tree, vector<F> compressed_paths, vector<F> powers, vector<F> power_bits, vector<vector<F>> paths, vector<vector<F>> tree,vector<F> tree_compress_vector, F c, F previous_r);
partition_sumcheck3_proof partition_sumcheck_3(vector<vector<F>> paths,vector<vector<F>> permuted_data, vector<vector<F>> diff,vector<vector<F>> bit_vectors,F previous_r,int max_depth);
struct proof _generate_3product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, vector<F> &_v3,F previous_r);
struct proof generate_batch_3product_sumcheck_proof(vector<vector<F>> &v1, vector<vector<F>> &v2, vector<vector<F>> &v3,vector<F> a,F previous_r);
struct proof _generate_batch_3product_sumcheck_proof(vector<vector<F>> &v1, vector<vector<F>> &v2, vector<F> &v3,vector<F> a,F previous_r);
partition_sumcheck1_proof forest_partition_sumcheck_1( vector<vector<F>> data, vector<vector<F>> permuted_data, vector<F> compress_vector, int trees , F _c, F previous_r);
partition_sumcheck2_proof forest_partition_sumcheck_2( vector<vector<F>> power_bits, vector<vector<F>> paths, vector<vector<F>> paths_aux,
 vector<vector<vector<F>>> forest, vector<F> tree_compress_vector, int dataset_size , F c, F previous_r);
partition_sumcheck3_proof forest_partition_sumcheck_3(vector<vector<F>> paths,vector<vector<F>> permuted_data, vector<vector<F>> diff,
	vector<vector<F>> bit_vectors, F previous_r, int forest_size, int dataset_size , int max_depth);

