#pragma once
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

void test_gkr(vector<F> data, vector<F> randomness, int N, int M, int layer);
void test_m2m(vector<F> data, vector<F> randomness, int cols, int rows, int circuits);
void test_sha256(vector<F> data, vector<F> randomness, int hashes);
void test_multree(vector<F> data, vector<F> randomness, int N, int M, int layers);