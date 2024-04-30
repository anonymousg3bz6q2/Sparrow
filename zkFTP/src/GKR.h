#pragma once

#include "verifier.h"
#include "inputCircuit.hpp"
#include <gmp.h>
#include <stdlib.h>
#include "polynomial.h"
#include "config_pc.hpp"
#include <map>
//#include "sumcheck.h"

#define GKR_PROOF 1
#define RANGE_PROOF 2
#define RANGE_PROOF_OPT 6
#define RANGE_PROOF_LOOKUP 7

#define MATMUL_PROOF 3 
#define ADD_PROOF 4
#define DIVISION_CHECK 5


struct MulTree_indexes{
	int previous_r,final_r,sum,initial_sum;
	vector<vector<vector<int>>> polynomials;
	vector<vector<int>> randomness;
	vector<int> individual_randomness;
	vector<int> global_randomness;
	vector<int> first_r;
	vector<int> vr,in,rand;
};


struct sumcheck2Prod{
	int previous_r,final_r,sum;
	vector<vector<int>> polynomials;
	vector<int> randomness;
	vector<int> vr;
};
struct gkr_proof_indexes{
	vector<struct sumcheck2Prod> sumcheck;
	vector<int> vr,gr,sums;
	int sum,layers;
};

struct sumcheck3Prod{
	int previous_r,final_r,sum;
	vector<vector<int>> polynomials;
	vector<int> randomness;
	vector<int> vr;
};

typedef struct MulTree_indexes;

struct lookup_proof_indexes{
	int previous_r,a,b,c;
	vector<MulTree_indexes> mul_proofs;
	vector<int> mul_out1,mul_out2,read_eval_x,write_eval_x,indexes_eval,x1;
	vector<int> r1,r2;
	int read_eval,read_eval1,read_eval2,write_eval,write_eval1,write_eval2,sum1,sum2;
	int final_eval;
	int final_rand;
};

typedef struct gkr_proof_indexes;
typedef struct sumcheck2Prod;
typedef struct sumcheck3Prod;
typedef struct lookup_proof_indexes;



struct partition_indexes{
	vector<int> randomness;
	vector<MulTree_indexes> mul_proofs;
	vector<sumcheck2Prod> sumcheck2Prod_proofs;
	vector<sumcheck3Prod> sumcheck3Prod_proofs;
	gkr_proof_indexes GKR;
	int eval_input,eval_perm_input,eval1_data,eval2_data,eval1_perm_data,eval2_perm_data,eval3_data;
	int eval_bits1,final_powers_input_eval,sum1,diff_eval,eval_powers2;
	vector<int> aggr_r,r1,r2,r3,range_proof_rand;
	int a,b,c,_c;

};

struct histogram_indexes{
	vector<int> randomness;
	vector<MulTree_indexes> mul_proofs;
	vector<sumcheck2Prod> sumcheck2Prod_proofs;
	vector<sumcheck3Prod> sumcheck3Prod_proofs;
	int peval1,peval2,peval3;
	vector<int> input_evals,metadata_evals,read_evals,write_evals,r;
};

struct node_histogram_indexes{
	int previous_r,commitment;
	vector<int> compress_r;
	gkr_proof_indexes GKR1,GKR2;
	vector<sumcheck2Prod> sumcheck2Prod_proofs;
	int node_eval,leaf_eval,comp_wit_eval,comp_node_eval,comp_out_eval,comp_leaf_eval,wit_eval;
	int a,b,c,r;
};

struct split_indexes{
	vector<lookup_proof_indexes> lookup_indexes;
	MulTree_indexes mul_proof;
	gkr_proof_indexes GKR;
	int best_gini_eval2,ginis_eval2,best_gini_eval1,ginis_eval1;
	vector<sumcheck2Prod> sumcheck2Prod_proofs;
	vector<sumcheck3Prod> sumcheck3Prod_proofs;
	vector<int> a,r1,r2;
	int gini_eval4,gini_eval3,eval1_N0,eval1_N1,pairwise_prod_eval,square_N_eval;
	int dividents_cond_eval,divisors_quot_eval;
	
};


typedef struct partition_indexes;
typedef struct histogram_indexes;
typedef struct node_histogram_indexes;


struct proof{
	int type;
	vector<vector<F>> randomness;
	vector<quadratic_poly> q_poly;
	vector<cubic_poly> c_poly;
	vector<F> output;
	vector<F> vr;
	vector<F> gr;
	vector<F> liu_sum;
	vector<vector<F>> sig;
	vector<vector<F>> final_claims_v;
	F divident,divisor,quotient,remainder;
	// Witnesses to make hash calclulation circuit less deep
	vector<vector<vector<F>>> w_hashes;
	vector<F> r,individual_sums;
	vector<vector<F>> Partial_sums;
	vector<quadratic_poly> q_poly1;
	vector<quadratic_poly> q_poly2;
	F final_rand;
	F final_sum;
	int K;

};

typedef struct proof;

struct polynomial_data{
	vector<F> poly;
	vector<vector<F>> eval_point;
	vector<F> eval;
};

struct feedforward_proof{
	map<string,struct polynomial_data> poly_map;
	vector<struct proof> proofs;
};



typedef struct Point Point;

struct proof permutation_check(vector<F> data, vector<F> randomness, int Attr);
struct proof single_inference_phase2(vector<F> data, vector<F> randomness, int Attr, int max_depth);
struct proof single_inference_phase1(vector<F> data, vector<F> randomness, int Attr);
struct proof permutation_check_partitions_input(vector<F> data, vector<F> randomness, int N, int Attr);

struct proof permutation_check_partitions_data(vector<F> data, vector<F> randomness, int N,	int nodes, int Attr);
struct proof permutation_check_partitions_tree(vector<F> data, vector<F> randomness, int N, int nodes);
struct proof batch_inference(vector<F> data, vector<F> randomness,F previous_r, int diff_size, int Attr, int max_depth, int N,int path_col,int perm_col);
struct proof path_consistency(vector<F> data, vector<F> randomness, int Attr, int max_depth, int N);
struct proof histogram_check(vector<F> data, vector<F> randomness, int N, int Attr, int compressed_size);

struct proof node_histogram_consistency(vector<F> data, vector<F> randomness, int leaves, int nodes);
struct proof prove_node_sum(vector<F> data, vector<F> randomness,F rand, int hist_size, int leaves, int nodes);
struct proof prove_gini_check_phase1(vector<F> data, vector<F> randomness, int nodes, int attr, int bin_size);
struct proof prove_gini_check_phase2(vector<F> data, vector<F> randomness, int nodes, int attr, int bin_size);
struct proof range_lookup(vector<F> data, vector<F> randomness, int segments, int elements);

struct proof prove_recursion(vector<F> data, vector<F> randomness, vector<partition_indexes> P1,vector<histogram_indexes> P2 ,vector<node_histogram_indexes> P3, vector<split_indexes> P4, int input_size);
struct proof node_histogram_consistency_forest(vector<F> data, vector<F> randomness, int leaves, int nodes, int trees);
struct proof prove_test_circuit(vector<F> data, vector<F> randomness, int N, int layers);
struct proof prepare_coeff(vector<F> data, vector<F> randomness, int N);
struct proof inference_proof(vector<F> data, vector<F> randomness,  int Attr, int max_depth, int trees);
void test_gkr(vector<F> data, vector<F> randomness, int N, int M, int layers);