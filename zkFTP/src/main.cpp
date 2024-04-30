#include <stdio.h>
//#include <mcl/bn256.hpp>
#include <mcl/bls12_381.hpp>
//#include <mcl/bn.h>
#include <vector>
#include <polynomial.h>
#include <math.h>
#include "MLP.h"
#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include <time.h>
#include "mimc.h"
#include "quantization.h"
#include "GKR.h"
#include <time.h>
#include <chrono>
#include "utils.hpp"
#include "pol_verifier.h"
#include "elliptic_curves.h"
#include "Poly_Commit.h"
#include "Aggr.h"
#include <thread>
#include "OpenAll.cpp"
#include "Inference.h"
#include "BuildTree.h"
#include "BuildTree_streaming.h"
#include "sumcheck.h"
#include "lookups.h"
#include "VerifyTree.h"
#include <chrono>
#include <fcntl.h>
#include "BuildForest.h"
#include "witness_stream.h"
#include "space_efficient_sumcheck.h"
#include "BuildForest_streaming.h"

#define FILE_MODE (S_IRWXU | S_IRWXG | S_IRWXO)

using namespace std::chrono;

using namespace mcl::bn;

#define F Fr


#define F_ONE (Fr::one())
#define F_ZERO (Fr(0))
extern int partitions;
using namespace std;
double proving_time;
//double verification_time;
double serialization_time;
double read_time;
double clear_cache_time;
int comm_size;
size_t data_read = 0;
double total_time;
double range_proof_time = 0.0;
struct _temp{
	vector<int> v;
};

extern vector<F> powers_two;
int threads = 1;
unsigned long int mul_counter = 0;
double Forward_propagation;
double dx_computation;
double gradients_computation;
double range_proof_verification_time;
int range_proof_size;
int bin_size ;
size_t MAX_CHUNCK;
int _WRITE = 1;
int max_depth;
extern int proof_len;
extern double verification_time;
extern double MIPP_verify_time;
float total_p = 0.0,total_v= 0.0 ,total_s =0.0;
int _commitment_test = 0;

MIPP_Comm pp;
MIPP_Comm pp_mul;
Comm pp_recursion;
string dir;
vector<int> predicates_size;
vector<struct proof> Transcript;
Dataset D_train;
vector<vector<F>> tree;
vector<vector<Node>> _tree;
vector<vector<vector<vector<int>>>> histograms;
vector<vector<vector<int>>> node_histogram;
vector<vector<vector<Node>>> _forest;
vector<vector<vector<F>>> forest;
int correct_prediction = 0;
vector<vector<vector<vector<int>>>> histograms_forest;
vector<unsigned long long int> gini_input;





void generate_inference_proof(Tree_Inference_Data &data, int Attr, int max_depth){
	struct proof P;
	vector<F> gkr_input;
	vector<F> randomness = generate_randomness(10,F(0));
	
	//gkr_input.insert(gkr_input.end(),data.path.begin(),data.path.end());  
	//gkr_input.insert(gkr_input.end(),data.bit_vector.begin(),data.bit_vector.end());  
	//gkr_input.push_back(F(1));
	//single_inference_phase1(gkr_input, randomness, max_depth);
	
	//gkr_input.clear();

	gkr_input.insert(gkr_input.end(),data.path.begin(),data.path.end());  
	gkr_input.insert(gkr_input.end(),data.permuted_input.begin(),data.permuted_input.end());  
	gkr_input.push_back(F(1));
	F two = F(2);
	two.inv(two,two);
	gkr_input.push_back(two);
	P = single_inference_phase2(gkr_input, randomness, Attr ,max_depth);
	
	vector<F> r1;
	for(int i = 0; i < P.randomness[0].size()-3; i++){
		r1.push_back(P.randomness[0][i]);
	}

	pad_vector(data.diff);
	pad_vector(data.bit_vector);
	_prove_bit_decomposition(data.bit_vector,r1,evaluate_vector(data.diff,r1),F(0),(int)log2(bin_size));


	gkr_input.clear();

	gkr_input.insert(gkr_input.end(),data.input.begin(),data.input.end());  
	gkr_input.insert(gkr_input.end(),data.permuted_input.begin(),data.permuted_input.end());  
	F a,b;
	a.setByCSPRNG();
	b.setByCSPRNG();
	gkr_input.push_back(a);
	gkr_input.push_back(b);
	permutation_check(gkr_input,  randomness, Attr);
	gkr_input.clear();
	printf("Inference Prove Time : %lf\n",proving_time);
	//

	
}

// Add padding information and inactive layers in order to compute the tree commitment
vector<vector<F>> expand_tree(vector<vector<vector<int>>> tree, int Attr){
	vector<vector<F>> expanded_tree(tree.size());
	for(int i = 0; i < tree.size(); i++){
		vector<int> attributes(tree[i].size()-1),inactive_attributes(Attr);
		for(int j = 0; j < Attr; j++){
			inactive_attributes[j] = j;
		}
		for(int j = 0; j < tree[i].size()-1; j++){
			attributes[j] = tree[i][j][1];
		}
		for(int j = 0; j < attributes.size(); j++){
			inactive_attributes.erase(std::remove(inactive_attributes.begin(), inactive_attributes.end(), attributes[j]), inactive_attributes.end());
		}
		for(int j = 0; j < tree[i].size()-1; j++){
			expanded_tree[i].push_back(tree[i][j][0]);
			expanded_tree[i].push_back(tree[i][j][1]);
			expanded_tree[i].push_back(tree[i][j][2]);
		}
		for(int j = 0; j < inactive_attributes.size(); j++){
			expanded_tree[i].push_back(F(0));
			expanded_tree[i].push_back(F(inactive_attributes[j]));
			expanded_tree[i].push_back(F(-1));
		}
	}
	return expanded_tree;
}

vector<vector<F>> prepare_tree(vector<vector<Node>> tree){
	vector<vector<F>> tree_data(tree.size());
	for(int i = 0; i < tree.size(); i++){
		for(int j = 0; j < tree[i].size()-1; j++){
			tree_data[i].push_back(tree[i][j].split_value);
			tree_data[i].push_back(tree[i][j].attr);
			tree_data[i].push_back(tree[i][j].direction);
			tree_data[i].push_back(F(0));	
		}
		tree_data[i].push_back(F(i));
		tree_data[i].push_back(tree[i][tree[i].size()-1].classification);
	}
	return tree_data;
}

vector<vector<G1>> commit_forest(vector<vector<vector<Node>>> forest, vector<vector<F>> &lookup_matrix,Comm &commitment){
	vector<F> tree_vector;
	int nodes,h;

	for(int k = 0; k < forest.size(); k++){
		vector<vector<F>> expanded_tree = prepare_tree(forest[k]);
		if(1 << ((int)log2(expanded_tree[0].size())) != expanded_tree[0].size()){
			h = 1<<((int)log2(expanded_tree[0].size()) + 1);
			for(int i = 0; i < expanded_tree.size(); i++){
				expanded_tree[i].resize(h,F(0));
			}
		}else{
			h = 1<<((int)log2(expanded_tree[0].size()));
		}
		
		if(1 << ((int)log2(expanded_tree.size())+1) != expanded_tree.size()){
			vector<F> dummy_path(h,F(0));
		

			int size = expanded_tree.size();
			for(int i = size; i < (1 << ((int)log2(size)+1)); i++){
				expanded_tree.push_back(dummy_path);
			}
		}
		nodes = expanded_tree.size();
		if(tree_vector.size() == 0){
			tree_vector.resize(nodes*h*forest.size());
		}
		for(int j = 0; j < nodes; j++){
			lookup_matrix.push_back(expanded_tree[j]);
		}
		for(int i = 0; i < h; i++){
			for(int j = 0; j < nodes; j++){
				tree_vector[k*nodes*h + i*nodes + j] = expanded_tree[j][i];
			}
		}
	}
	

	generate_pp_hyperproofs(commitment,(int)log2(h*nodes*forest.size()),(int)log2(h));
	vector<vector<G1>> table = SVL_commit(tree_vector,commitment,nodes*forest.size());
	
	
	//int pos = 3;
	//vector<F> x = generate_randomness((int)log2(h),F(0));
	
	//single_SVL_Proof P = single_SVL_prove(expanded_tree,table,x,pos,commitment);
	//single_SVL_verify(P, x, evaluate_vector(expanded_tree[pos],x), commitment);
	return table;

	
 }




vector<vector<G1>> commit_tree(vector<vector<Node>> tree){
	
	vector<vector<F>> expanded_tree = prepare_tree(tree);
	
	//vector<vector<F>> expanded_tree(2);
	//expanded_tree[0].push_back(F(2));
	//expanded_tree[0].push_back(F(1));
	//expanded_tree[1].push_back(F(1));
	//expanded_tree[1].push_back(F(5));
	
	
	int h;
	if(1 << ((int)log2(expanded_tree[0].size())) != expanded_tree[0].size()){
		h = 1<<((int)log2(expanded_tree[0].size()) + 1);
		for(int i = 0; i < expanded_tree.size(); i++){
			expanded_tree[i].resize(h,F(0));
		}
	}else{
		h = 1<<((int)log2(expanded_tree[0].size()));
	}
	
	if(1 << ((int)log2(expanded_tree.size())+1) != expanded_tree.size()){
		vector<F> dummy_path(h,F(0));
	

		int size = expanded_tree.size();
		for(int i = size; i < (1 << ((int)log2(size)+1)); i++){
			expanded_tree.push_back(dummy_path);
		}
	}
	int nodes = expanded_tree.size();
	//printf("Number of nodes : %d, path size : %d\n",expanded_tree.size(),expanded_tree[0].size());
	vector<F> tree_vector(nodes*h);
	//for(int i = 0; i < expanded_tree.size(); i++){
	//	tree_vector.insert(tree_vector.end(),expanded_tree[i].begin(),expanded_tree[i].end());
	//}
	for(int i = 0; i < h; i++){
		for(int j = 0; j < nodes; j++){
			tree_vector[i*nodes + j] = expanded_tree[j][i];
		}
	}

	Comm commitment;
	generate_pp_hyperproofs(commitment,(int)log2(h*nodes),(int)log2(h));
	vector<vector<G1>> table = SVL_commit(tree_vector,commitment,nodes);
	
	int pos = 3;
	vector<F> x = generate_randomness((int)log2(h),F(0));
	
	single_SVL_Proof P = single_SVL_prove(expanded_tree,table,x,pos,commitment);
	single_SVL_verify(P, x, evaluate_vector(expanded_tree[pos],x), commitment);
	return table;

	
 }

void segmented_lookup(vector<vector<F>> table,vector<int> pos, vector<F> x1,vector<F> x2,vector<F> y,  vector<vector<G1>> &cached_quotients, Comm &pp, vector<float> &perf){
	int lookups = pos.size();
	vector<vector<G1>> proofs;
	vector<vector<int>> idx;
	vector<vector<F>> x(lookups);
	vector<vector<F>> binary((int)log2(table.size())),inv_binary((int)log2(table.size()));
	
	clock_t t1,t2;
	t1 = clock();
	for(int i = 0 ; i < pos.size(); i++){
		proofs.push_back(get_proof(table[pos[i]], x2 , pos[i],idx, table.size(),table[0].size(), cached_quotients, pp ));
		x[i].insert(x[i].end(),x2.begin(),x2.end());
		
		for(int j = 0; j < idx[0].size(); j++){
			x[i].push_back(F(idx[0][j]));
			binary[j].push_back(F(idx[0][j]));
			inv_binary[j].push_back(1-F(idx[0][j]));
		}
		//KZG_verify(x[i], y[i], pp);
	}
	t2 = clock();
	float preprocess = (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	vector<G2> u(lookups);
	vector<G1> w(lookups);
	G1 G;
	G2 H;
	char rand[256];
	for(int i = 0; i < 256; i++){
		rand[i] = i+'4';
	}
	mcl::bn::hashAndMapToG1(G,rand,256);

	mcl::bn::hashAndMapToG2(H,rand,256);
	F s;
	
	for(int i = 0; i < lookups; i++){
		s.setByCSPRNG();
		w[i] = G*s;
		s.setByCSPRNG();
		u[i] = H*s;
	}

	
	aggregation_proof P = Aggregate(proofs,w,u,x,y,pp.H,(int)log2(lookups),pp);
	
	vector<F> beta;
	
	t1 = clock();
	precompute_beta(x1,beta);
	proof P1 = generate_2product_sumcheck_proof(y,beta,s);
	verify_2product_sumcheck(P1,P1.q_poly[0].eval(F_ONE)  +P1.q_poly[0].eval(F_ZERO) );
		
	beta.clear();
	precompute_beta(P1.randomness[0],beta);
	proof_len += MIPP(P.Y, u,beta, w, P.C_y,compute_G1_commitment(P.Y,beta),pp.G);
	vector<F> r = generate_randomness((int)log2(lookups),F(32));
	
	beta.clear();

	precompute_beta(r,beta);
	proof P2;
	
	
	for(int i = 0; i < (int)log2(table.size()); i++){
		P2 = _generate_3product_sumcheck_proof(binary[i],inv_binary[i],beta,r[r.size()-1]);
		verify_3product_sumcheck(P2,r,P2.c_poly[0].eval(F_ONE)  +P2.c_poly[0].eval(F_ZERO) );
	}
	
	r = generate_randomness((int)log2(P.C_I.size()),P2.final_rand);
	vector<G2> I_aggr(P.H[0].size());
	vector<G2> buff(P.H.size());
	for(int i = 0; i < P.H[0].size(); i++){
		for(int j = 0; j <P.H.size(); j++){
			buff[j] = P.H[j][i];
		}
		G2::mulVec(I_aggr[i], buff.data(),r.data(), r.size());
	}
	GT temp,aggr;
	temp.pow(P.C_I[0],P.C_I[0],r[0]);
	aggr = temp;
	for(int i = 1; i < r.size(); i++){
		temp.pow(P.C_I[i],P.C_I[i],r[i]);
		aggr = aggr*temp;
	}
	beta.clear();
	precompute_beta(P2.randomness[0],beta);
	proof_len +=MIPP(w,I_aggr,beta,w,aggr,pp.G,pp.G);
	t2 = clock();
	verification_time += MIPP_verify_time;
	MIPP_verify_time = 0.0;
	//printf("Aggr : P : %lf , V : %lf, L : %lf\n", P.proving_time + (double)(t2-t1)/(double)CLOCKS_PER_SEC,P.verification_time+verification_time,(double)(P.proof_size + proof_len)/1024.0 );
	printf("%lf,%lf,%lf\n",P.proving_time,preprocess,(double)(t2-t1)/(double)CLOCKS_PER_SEC);
	perf.push_back(P.proving_time+  preprocess + (double)(t2-t1)/(double)CLOCKS_PER_SEC);
	perf.push_back(P.verification_time+verification_time);
	perf.push_back((double)(P.proof_size + proof_len)/1024.0 );
}


void forest_inference_sumcheck(vector<int> x, int max_depth,int attr, int data_insances, int trees){
	Dataset D_test;
	Comm svl_pp;
	int test_samples = 0;
	double Pt = 0.0,Vt = 0.0,Ps = 0.0;
	F two_inv = F(2);two_inv.inv(two_inv,two_inv);
	vector<F> prev_x;
	F previous_r;previous_r.setByCSPRNG();

	_forest.clear();
	forest.clear();
	
	LoadDummyDataset(test_samples,data_insances,attr, D_train,D_test);

	
	vector<Dataset> partitions;
	
	vector<vector<Node>> tree = BuildTree(D_train,partitions,max_depth);
	printf("Tree size : %d\n",tree.size());
	for(int i = 0; i < trees; i++){
		_forest.push_back(tree);
		forest.push_back(prepare_tree(tree));
	}
	
	// Commitment phase
	vector<vector<F>> lookup_matrix;
	vector<vector<G1>> cached_proofs = commit_forest(_forest,  lookup_matrix,svl_pp);
	
	
	vector<F> paths,perm_input,diff,bits;
	int path_size;
	vector<int> pos;
	vector<vector<F>> mul_input_paths;
	for(int i = 0; i < trees; i++){
		Tree_Inference_Data data = Tree_Inference(_forest[i],x,1);
		paths.insert(paths.end(), data.path.begin(),data.path.end());
		pos.push_back(data.pos + i*( lookup_matrix.size()/trees));
		perm_input.insert(perm_input.end(), data.permuted_input.begin(),data.permuted_input.end());
		diff.insert(diff.end(),data.diff.begin(),data.diff.end());
		bits.insert(bits.end(), data.bit_vector.begin(),data.bit_vector.end());
	}
	

	vector<F> compress_vector = generate_randomness(3,previous_r);
	vector<F> compressed_path(x.size());
	for(int i = 0; i < trees; i++){
		for(int j = 0; j < x.size(); j++){
			compressed_path[j] = F(perm_input[i*2*x.size() + 2*j])*compress_vector[0]+ F(perm_input[i*2*x.size() + 2*j+1])*compress_vector[1] + compress_vector[2];
		}
		mul_input_paths.push_back(compressed_path);
	}
	vector<F> gkr_input;
	gkr_input.insert(gkr_input.end(),paths.begin(),paths.end());
	gkr_input.insert(gkr_input.end(),perm_input.begin(),perm_input.end());
	gkr_input.push_back(1);
	gkr_input.push_back(two_inv);

	pad_vector(diff);
	pad_vector(bits);
	pad_vector(paths);
	
	
	vector<vector<G1>> commitments;
	vector<G1> C;
	
	MIPP_commit(bits,pp,C);
	commitments.push_back(C);
	MIPP_commit(perm_input,pp,C);
	commitments.push_back(C);
	
	printf("OK\n");
	
	// Circuit proving phase
	vector<F> r = generate_randomness((int)log2(diff.size()),previous_r);
	
	
	proof P1 = inference_proof(gkr_input,r ,  attr,  max_depth,  trees);
	clock_t t1,t2;
	t1 = clock();
	F eval_diff = evaluate_vector(diff,r);
	
	_prove_bit_decomposition(bits,r,eval_diff,F(0),8);
	mul_tree_proof mP = prove_multiplication_tree(mul_input_paths,previous_r,prev_x);
	F prod = F_ONE;
	for(int i = 0; i < x.size(); i++){
		prod *= (F(i)*compress_vector[0] + F(x[i])*compress_vector[1] + compress_vector[2]);
	}
	if(prod != mP.output[0]){
		printf("Input consistency error\n");
	}
	t2 = clock();
	float sumcheck_time = (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	//printf("Sumcheck : P : %lf, V : %lf, L : %lf\n",sumcheck_time,verification_time,(double)proof_len/1024.0);
	Pt+= sumcheck_time;
	printf("Verification %lf\n",verification_time);
	Vt += verification_time;
	Ps += (double)proof_len/1024.0;
	// Open phase
	MIPP_open(bits,generate_randomness((int)log2(bits.size()),F(231)),pp,commitments[0]);
	MIPP_open(perm_input,generate_randomness((int)log2(perm_input.size()),F(34)),pp,commitments[1]);
	
	//printf("P : %lf, V : %lf, L : %lf\n",pp.prove_time,pp.verification_time,(double)pp.proof_size/1024.0);

	Pt+= pp.prove_time;
	printf("Verification %lf\n",pp.verification_time);
	Vt += pp.verification_time;
	Ps += (double)pp.proof_size/1024.0;

	// lookup phase
	if(trees > 1){
		printf("%d,%d\n",_forest.size(),lookup_matrix[0].size());
		vector<F> x1 = generate_randomness((int)log2(_forest.size()),F(0));
		vector<F> x2 = generate_randomness((int)log2(lookup_matrix[0].size()),F(32));
		vector<F> y(forest.size());
		for(int i = 0; i < forest.size(); i++){
		
			y[i] = evaluate_vector(lookup_matrix[pos[i]],x2);
		}
		verification_time = 0.0;
		proof_len = 0.0;
		vector<float> perf;
		
		segmented_lookup(lookup_matrix, pos, x1, x2,y,  cached_proofs, svl_pp,perf);
		printf("P : %lf, V : %lf, L : %lf\n",Pt + perf[0],Vt + perf[1],Ps + perf[2]);
		verification_time = 0.0;
		proof_len = 0.0;
		pp.verification_time = 0;
		pp.proof_size = 0;
		pp.proof_size = 0;
		
	}else{
		
		vector<F> x2 = generate_randomness((int)log2(lookup_matrix[0].size()),F(32));
		
		clock_t t1,t2;
		t1 = clock();
		single_SVL_Proof P = single_SVL_prove(lookup_matrix,cached_proofs,x2,pos[0],svl_pp);
		t2 = clock();
		Pt += (double)(t2 - t1)/(double)(CLOCKS_PER_SEC);
		
		t1 = clock();
		single_SVL_verify(P, x2, evaluate_vector(lookup_matrix[pos[0]],x2), svl_pp);
		t2 = clock();
		printf("SVL verify: %lf\n",(double)(t2 - t1)/(double)(CLOCKS_PER_SEC));
		Vt += (double)(t2 - t1)/(double)(CLOCKS_PER_SEC);
		Ps += (double)(7*sizeof(P.C1) + 3*P.plaintext_proofs.size()*sizeof(P.plaintext_proofs[0]) + 2*P.B.size()*sizeof(P.B[0]))/1024.0;
		printf("P : %lf, V : %lf, L : %lf\n",Pt ,Vt,Ps);
		
	}
	
	
}

void benchmark_lookup(int M, int N, int k){
	Comm commitment;
	vector<vector<F>> table(M);
	for(int i = 0; i < M; i++){
		table[i] = generate_randomness(N,F(i));	
	}
	vector<int> queries;
	if(k > M){
		exit(-1);
	}
	for(int i = 0; i < k; i++){
		queries.push_back(i);
	}
	generate_pp_hyperproofs(commitment,(int)log2(M*N),(int)log2(N));
	clock_t t1,t2;
	t1 = clock();
	vector<vector<G1>> proofs = SVL_commit(convert2vector(table),commitment,M*N);
	t2 = clock();
	printf("Commit : %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);

	vector<F> x2 = generate_randomness((int)log2(N),F(21));
	vector<F> y;
	for(int i = 0; i < queries.size(); i++){
		y.push_back(evaluate_vector(table[queries[i]],x2));
	}
	
	vector<float> perf; 
	segmented_lookup(table,queries,generate_randomness((int)log2(queries.size()),F(1)),x2,y,proofs,commitment,perf);
	printf("P : %lf, V : %lf, L : %lf\n", perf[0],perf[1], perf[2]);
		
}

void test_forest_training(int data_size, int attr, int trees){
	
	Dataset D_test;
	int data_insances = data_size;
	int test_samples = 0;
	max_depth = 5;
	if(attr < 8){
		max_depth = attr-1;
	}
	int attributes_num = 8;
	

	
	LoadDummyDataset2(test_samples,data_insances,attr, D_train,D_test);
	
	vector<Dataset> partitions;
	
	
	
	vector<vector<Node>> tree = BuildTree(D_train,partitions,max_depth);
	
	for(int i = 0; i < trees; i++){
		_forest.push_back(tree);
		forest.push_back(prepare_tree(tree));
	}

	
	
	vector<vector<vector<F>>> leaf_coeff(trees);
	vector<vector<vector<int>>> leaf_coeff_int(trees);
 	vector<vector<vector<F>>> node_coeff(trees);
 	vector<vector<vector<int>>> node_coeff_int(trees);
	
	
	vector<vector<vector<int>>> Node_matrix(trees);
	vector<vector<vector<int>>> leaf_matrix(trees);
	vector<vector<vector<int>>> leaf_index_matrix(trees);
	
	for(int k = 0; k < trees; k++){
		leaf_coeff[k].resize(tree.size());leaf_coeff_int[k].resize(tree.size());node_coeff[k].resize(tree.size());node_coeff_int[k].resize(tree.size());
		Node_matrix[k].resize(max_depth+1);leaf_matrix[k].resize(max_depth+1);leaf_index_matrix[k].resize(max_depth+1);
		for(int i = 0; i <= max_depth; i++){
			Node_matrix[k][i].resize(1<<i,-1);
			leaf_matrix[k][i].resize(1<<i,-1);
			leaf_index_matrix[k][i].resize(1<<i,-1);
		}

	}
	for(int k = 0; k < trees; k++){
		for(int i = 0; i < tree.size(); i++){
			leaf_coeff[k][i].resize(2);
			leaf_coeff_int[k][i].resize(2);
			leaf_coeff[k][i][0] = F(tree[i][tree[i].size()-1].h);
			leaf_coeff[k][i][1] = F(tree[i][tree[i].size()-1].pos);
			leaf_coeff_int[k][i][0] = (tree[i][tree[i].size()-1].h);
			leaf_coeff_int[k][i][1] = (tree[i][tree[i].size()-1].pos);
			leaf_matrix[k][leaf_coeff_int[k][i][0]][leaf_coeff_int[k][i][1]] = 2;
			Node_matrix[k][leaf_coeff_int[k][i][0]][leaf_coeff_int[k][i][1]] = 2;
			leaf_index_matrix[k][leaf_coeff_int[k][i][0]][leaf_coeff_int[k][i][1]] = i;
		}
	}
	


	vector<vector<vector<Node>>> temp_forest;
	for(int i = 0; i < trees; i++){
		temp_forest.push_back(tree);
	}
	vector<vector<int>> partitions_card;
	vector<int> temp_partitions;
	for(int i = 0; i < partitions.size(); i++){
		temp_partitions.push_back(partitions[i].indexes.size());
	} 
	for(int i = 0; i < trees; i++){
		partitions_card.push_back(temp_partitions);
	}

	
	vector<vector<int>> ones(trees);
	for(int i = 0; i < trees; i++){
		ones[i].resize(D_train.label.size(),1);
	}	
	
	
	partition_SNARK_data_streaming_forest partition_data = get_partitions_transcript_streaming_forest(D_train,  partitions_card, _forest, forest, max_depth, 0);
	
	prove_correct_partitions_streaming_forest( partition_data, D_train, forest,max_depth);
	
	
	
	histogram_SNARK_data_streaming_forest hist_data = get_histograms_transcript_streaming_forest(D_train,  _forest);
	hist_data.input_data = partition_data.input_data;
	hist_data.input_data.pos = 0;
	
	prove_correct_histograms_streaming_forest(hist_data, attr, F(234));
	hist_data.memory_init.clear();
	vector<vector<int>>().swap(hist_data.memory_init);
	
	

	nodes_histogram_data_streaming data3 = get_node_histograms_transcript_forest_stream(leaf_index_matrix, leaf_matrix,attr,leaf_coeff,trees,forest[0].size());
	prove_correct_node_histograms_streaming_forest(data3, trees, attr, forest[0].size() , F(666));
	
	
	printf("TOTAL PROVE TIME PHASE 3 : %lf \n",proving_time);
	printf("TOTAL VERIFICATION TIME PHASE 3 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	
	
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	clear_cache_time = 0.0;
	read_time = 0.0;
	
	

	vector<vector<vector<int>>> transformed_histograms;
	
	split_SNARK_streaming_forest data4 = get_split_transcript_streaming_forest( forest.size(), forest[0].size()-1, attr );
	
	prove_correct_split_forest(data4, F(213));

	printf("TOTAL Proving time : %lf, Verification time : %lf, Proof size : %lf\n",total_p,total_v,total_s);

}

void test_tree_training_monolithic(int data_size, int attr){
	Dataset D_test;
	int data_insances = data_size;
	int test_samples = 0;
	max_depth = 5;
	int attributes_num = attr;

	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	read_time = 0.0;
	total_p = 0.0;
	total_v = 0.0;
	total_s = 0.0;
	
	LoadDummyDataset(test_samples,data_insances,attr, D_train,D_test);
	

	vector<Dataset> partitions;
	
	_tree = BuildTree(D_train,partitions,max_depth);
	
	vector<vector<F>> leaf_coeff(_tree.size());
	vector<vector<int>> leaf_coeff_int(_tree.size());
 	vector<vector<F>> node_coeff(_tree.size());
 	vector<vector<int>> node_coeff_int(_tree.size());
	
	
	vector<vector<int>> Node_matrix(max_depth+1);
	vector<vector<int>> leaf_matrix(max_depth+1);
	vector<vector<int>> leaf_index_matrix(max_depth+1);
	for(int i = 0; i <= max_depth; i++){
		Node_matrix[i].resize(1<<i,-1);
		leaf_matrix[i].resize(1<<i,-1);
		leaf_index_matrix[i].resize(1<<i,-1);
	}

	for(int i = 0; i < _tree.size(); i++){
		leaf_coeff[i].resize(2);
		leaf_coeff_int[i].resize(2);
		leaf_coeff[i][0] = F(_tree[i][_tree[i].size()-1].h);
		leaf_coeff[i][1] = F(_tree[i][_tree[i].size()-1].pos);
		leaf_coeff_int[i][0] = (_tree[i][_tree[i].size()-1].h);
		leaf_coeff_int[i][1] = (_tree[i][_tree[i].size()-1].pos);
		leaf_matrix[leaf_coeff_int[i][0]][leaf_coeff_int[i][1]] = 2;
		Node_matrix[leaf_coeff_int[i][0]][leaf_coeff_int[i][1]] = 2;
		leaf_index_matrix[leaf_coeff_int[i][0]][leaf_coeff_int[i][1]] = i;
	}
	tree = prepare_tree(_tree);
	reset_histograms();

	//partition_SNARK_data_streaming spartition_data = get_partitions_transcript_streaming(D_train, partitions, _tree, tree,  max_depth, 0);
	//prove_correct_partitions_streaming(spartition_data, D_train, tree, max_depth);
	clock_t s,e;
	s = clock();
	partition_SNARK_data spartition_data = get_partitions_transcript(D_train, partitions, _tree); 
	e = clock();
	proving_time += (double)(e-s)/(double)CLOCKS_PER_SEC;
	prove_correct_partitions(spartition_data,D_train,tree,max_depth);
	
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	read_time = 0.0;
	//histogram_SNARK_data_streaming data =  get_histograms_transcript_streaming(D_train, spartition_data.data_partitions, spartition_data.label, _tree, attributes_num, 0);
	s = clock();
	histogram_SNARK_data data = get_histograms_transcript(D_train,spartition_data.data_partitions,spartition_data.label,_tree,attr);
	data.input_data = spartition_data.input_data;
	e = clock();
	proving_time += (double)(e-s)/(double)CLOCKS_PER_SEC;
	
	prove_histograms(data,attr,F(32));
	//prove_correct_histograms_streaming(data, attributes_num, F(0));
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	clear_cache_time = 0.0;
	read_time = 0.0;
	clock_t t1,t2;
	
	t1 = clock();
	nodes_histogram_SNARK_data node_histogram_data = get_node_histograms_transcript(data.final_memory,  leaf_index_matrix, leaf_matrix,attr, leaf_coeff,tree.size());
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	prove_node_histograms(node_histogram_data, F(123));
	
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	printf("TOTAL PROVE TIME PHASE 3 : %lf \n",proving_time);
	printf("TOTAL VERIFICATION TIME PHASE 3 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	clear_cache_time = 0.0;
	read_time = 0.0;
	
	
	
	
	t1 = clock();
	split_SNARK_data split_data = get_split_transcript(node_histogram_data.node_histograms);	
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	prove_split(split_data, F(332));
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	
	printf("TOTAL PROVE TIME PHASE 4 : %lf \n",proving_time);
	printf("TOTAL VERIFICATION TIME PHASE 4 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	printf("TOTAL VERIFICATION TIME PHASE 4 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	printf("TOTAL Proving time : %lf, Verification time : %lf, Proof size : %lf\n",total_p,total_v,total_s);
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	clear_cache_time = 0.0;
	read_time = 0.0;

}


void test_tree_training(int data_size, int attr){
	Dataset D_test;
	int data_insances = data_size;
	int test_samples = 0;
	max_depth = 5;
	if(attr <= 4){
		max_depth = attr;
	
	}
	int attributes_num = attr;

	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	read_time = 0.0;
	total_p = 0.0;
	total_v = 0.0;
	total_s = 0.0;
	
	LoadDummyDataset(test_samples,data_insances,attr, D_train,D_test);
	

	vector<Dataset> partitions;
	
	_tree = BuildTree(D_train,partitions,max_depth);
	
	vector<vector<F>> leaf_coeff(_tree.size());
	vector<vector<int>> leaf_coeff_int(_tree.size());
 	vector<vector<F>> node_coeff(_tree.size());
 	vector<vector<int>> node_coeff_int(_tree.size());
	
	
	vector<vector<int>> Node_matrix(max_depth+1);
	vector<vector<int>> leaf_matrix(max_depth+1);
	vector<vector<int>> leaf_index_matrix(max_depth+1);
	for(int i = 0; i <= max_depth; i++){
		Node_matrix[i].resize(1<<i,-1);
		leaf_matrix[i].resize(1<<i,-1);
		leaf_index_matrix[i].resize(1<<i,-1);
	}

	for(int i = 0; i < _tree.size(); i++){
		leaf_coeff[i].resize(2);
		leaf_coeff_int[i].resize(2);
		leaf_coeff[i][0] = F(_tree[i][_tree[i].size()-1].h);
		leaf_coeff[i][1] = F(_tree[i][_tree[i].size()-1].pos);
		leaf_coeff_int[i][0] = (_tree[i][_tree[i].size()-1].h);
		leaf_coeff_int[i][1] = (_tree[i][_tree[i].size()-1].pos);
		leaf_matrix[leaf_coeff_int[i][0]][leaf_coeff_int[i][1]] = 2;
		Node_matrix[leaf_coeff_int[i][0]][leaf_coeff_int[i][1]] = 2;
		leaf_index_matrix[leaf_coeff_int[i][0]][leaf_coeff_int[i][1]] = i;
	}
	tree = prepare_tree(_tree);
	reset_histograms();

	partition_SNARK_data_streaming spartition_data = get_partitions_transcript_streaming(D_train, partitions, _tree, tree,  max_depth, 0);
	prove_correct_partitions_streaming(spartition_data, D_train, tree, max_depth);
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	read_time = 0.0;
	histogram_SNARK_data_streaming data =  get_histograms_transcript_streaming(D_train, spartition_data.data_partitions, spartition_data.label, _tree, attributes_num, 0);
	data.input_data = spartition_data.input_data;data.input_data.pos = 0;
	data.input_aux = spartition_data.input_aux;data.input_aux.pos = 0;
	
	prove_correct_histograms_streaming(data, attributes_num, F(0));
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	clear_cache_time = 0.0;
	read_time = 0.0;
	clock_t t1,t2;
	
	t1 = clock();
	nodes_histogram_SNARK_data node_histogram_data = get_node_histograms_transcript(data.final_memory,  leaf_index_matrix, leaf_matrix,attr, leaf_coeff,tree.size());
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	prove_node_histograms(node_histogram_data, F(123));
	
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	printf("TOTAL PROVE TIME PHASE 3 : %lf \n",proving_time);
	printf("TOTAL VERIFICATION TIME PHASE 3 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	clear_cache_time = 0.0;
	read_time = 0.0;
	
	
	
	
	t1 = clock();
	split_SNARK_data split_data = get_split_transcript(node_histogram_data.node_histograms);	
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	prove_split(split_data, F(332));
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	
	printf("TOTAL PROVE TIME PHASE 4 : %lf \n",proving_time);
	printf("TOTAL VERIFICATION TIME PHASE 4 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	printf("TOTAL VERIFICATION TIME PHASE 4 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	printf("TOTAL Proving time : %lf, Verification time : %lf, Proof size : %lf\n",total_p,total_v,total_s);
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	clear_cache_time = 0.0;
	read_time = 0.0;

}

vector<vector<vector<int>>> prove_first_part(vector<vector<int>> partitions_card, int trees,int attr){
	vector<vector<int>> ones(trees);
	for(int i = 0; i < trees; i++){
		ones[i].resize(D_train.label.size(),1);
	}	
	

	clock_t t1,t2;
	t1 = clock();
	partition_SNARK_data_forest partition_data;
	get_partitions_forest(partition_data,D_train,  partitions_card, _forest);
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	
	
	prove_correct_partitions_forest( partition_data, D_train, forest,max_depth);
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	
	
	for(int i = 0; i < partition_data.permuted_data.size(); i++){
		vector<F>().swap(partition_data.permuted_data[i]);
		//free(partition_data.permuted_data[i].data());
	}
	for(int i = 0; i < partition_data.bit_vectors.size(); i++){
		vector<F>().swap(partition_data.bit_vectors[i]);
	}
	for(int i = 0; i < partition_data.paths.size(); i++){
		vector<F>().swap(partition_data.paths[i]);
		//free(partition_data.paths[i].data());
	}
	for(int i = 0; i < partition_data.paths_aux.size(); i++){
		vector<F>().swap(partition_data.paths_aux[i]);
		//free(partition_data.paths_aux[i].data());
	}
	for(int i = 0 ; i< partition_data.diff_data.size(); i++){
		vector<F>().swap(partition_data.diff_data[i]);
		//free(partition_data.diff_data[i].data());
	}
	vector<vector<F>>().swap(partition_data.permuted_data);
	vector<vector<F>>().swap(partition_data.bit_vectors);
	vector<vector<F>>().swap(partition_data.paths);
	vector<vector<F>>().swap(partition_data.paths_aux);
	vector<vector<F>>().swap(partition_data.diff_data);
	
	
	/*
	free(partition_data.permuted_data.data());
	free(partition_data.bit_vectors.data());
	free(partition_data.paths.data());
	free(partition_data.paths_aux.data());
	free(partition_data.diff_data.data());
	free(partition_data.path_diff.data());
	partition_data.permuted_data.clear();
	partition_data.bit_vectors.clear();
	partition_data.paths_aux.clear();
	partition_data.paths.clear();
	partition_data.diff_data.clear();
	partition_data.path_diff.clear();
	*/
	
	printf("TOTAL PROVE TIME PHASE 1 : %lf \n",proving_time);
	printf("TOTAL VERIFICATION TIME PHASE 1 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	read_time = 0.0;

	
	t1 = clock();
	histogram_SNARK_data_forest hist_data;
	get_histograms_forest(hist_data,D_train, partition_data.data_partitions,  ones, D_train.label, forest, attr);
	


	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;

	
	hist_data.input_data = partition_data.input_data;
	hist_data.data_partitions = partition_data.data_partitions;
	hist_data.label = partition_data.label;
	
	
	for(int i = 0; i < partition_data.input_data.size(); i++){
		vector<F>().swap(partition_data.input_data[i]);
	}
	vector<vector<F>>().swap(partition_data.input_data);
	partition_data.input_data.clear();

	
	
	prove_histograms_forest(hist_data, attr,trees, F(234));
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	
	/*
	for(int i = 0; i < hist_data.read_transcript.size(); i++){
		for(int j = 0; j < hist_data.read_transcript[i].size(); j++){
			free(hist_data.read_transcript[i][j].data());
			free(hist_data.write_transcript[i][j].data());
		}
		free(hist_data.read_transcript[i].data());
		free(hist_data.write_transcript[i].data());
	}
	free(hist_data.read_transcript.data());
	free(hist_data.write_transcript.data());
	for(int i = 0 ;i  < partition_data.input_data.size(); i++){
		//free(hist_data.input_data[i].data());
		free(partition_data.input_data[i].data());
	}	
	
	//free(hist_data.input_data.data());
	free(partition_data.input_data.data());
	
	
	
	//free(hist_data.data_partitions.data());
	free(partition_data.data_partitions.data());
	
	free(hist_data.label.data());
	for(int i = 0; i < hist_data.memory_init.size(); i++){
		for(int j = 0; j < hist_data.memory_init[i].size(); j++){
			free(hist_data.memory_init[i][j].data());
		}
		free(hist_data.memory_init[i].data());
	}
	
	
	free(hist_data.memory_init.data());
	
	*/
	vector<vector<vector<int>>> final_memory(hist_data.final_memory.size());
	for(int i = 0 ; i < final_memory.size(); i++){
		final_memory[i].resize(hist_data.final_memory[i].size());
		for(int j = 0; j < final_memory[i].size(); j++){
			final_memory[i][j].resize(hist_data.final_memory[i][j].size());
			for(int k = 0; k < final_memory[i][j].size(); k++){
				final_memory[i][j][k] = hist_data.final_memory[i][j][k].getInt64();
			}
		}
	}
	printf("TOTAL PROVE TIME PHASE 2 : %lf \n",proving_time);
	printf("TOTAL VERIFICATION TIME PHASE 2 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	read_time = 0.0;
	
	
	/*
	for(int i = 0; i < hist_data.final_memory.size(); i++){
		for(int j = 0; j < hist_data.final_memory[i].size(); j++){
			free(hist_data.final_memory[i][j].data());
		}
		free(hist_data.final_memory[i].data());
	}
	free(hist_data.final_memory.data());
	*/
	
	return final_memory;
}

void test_forest_training_monolithic(int data_size, int attr, int trees){

	Dataset D_test;
	int data_insances = data_size;
	int test_samples = 0;
	max_depth = 5;
	if(attr < 5){
		max_depth  =attr;
	}
	int attributes_num = 8;
	float total_p = 0.0;
	float total_v = 0.0;
	float total_s = 0.0;
	
	LoadDummyDataset(test_samples,data_insances,attr, D_train,D_test);

	vector<Dataset> partitions;
	
	vector<vector<Node>> tree = BuildTree(D_train,partitions,max_depth);
	for(int i = 0; i < trees; i++){
		_forest.push_back(tree);
		forest.push_back(prepare_tree(tree));
	}

	vector<vector<vector<F>>> leaf_coeff(trees);
	vector<vector<vector<int>>> leaf_coeff_int(trees);
 	vector<vector<vector<F>>> node_coeff(trees);
 	vector<vector<vector<int>>> node_coeff_int(trees);
	
	
	vector<vector<vector<int>>> Node_matrix(trees);
	vector<vector<vector<int>>> leaf_matrix(trees);
	vector<vector<vector<int>>> leaf_index_matrix(trees);
	
	for(int k = 0; k < trees; k++){
		leaf_coeff[k].resize(tree.size());leaf_coeff_int[k].resize(tree.size());node_coeff[k].resize(tree.size());node_coeff_int[k].resize(tree.size());
		Node_matrix[k].resize(max_depth+1);leaf_matrix[k].resize(max_depth+1);leaf_index_matrix[k].resize(max_depth+1);
		for(int i = 0; i <= max_depth; i++){
			Node_matrix[k][i].resize(1<<i,-1);
			leaf_matrix[k][i].resize(1<<i,-1);
			leaf_index_matrix[k][i].resize(1<<i,-1);
		}

	}
	for(int k = 0; k < trees; k++){
		for(int i = 0; i < tree.size(); i++){
			leaf_coeff[k][i].resize(2);
			leaf_coeff_int[k][i].resize(2);
			leaf_coeff[k][i][0] = F(tree[i][tree[i].size()-1].h);
			leaf_coeff[k][i][1] = F(tree[i][tree[i].size()-1].pos);
			leaf_coeff_int[k][i][0] = (tree[i][tree[i].size()-1].h);
			leaf_coeff_int[k][i][1] = (tree[i][tree[i].size()-1].pos);
			leaf_matrix[k][leaf_coeff_int[k][i][0]][leaf_coeff_int[k][i][1]] = 2;
			Node_matrix[k][leaf_coeff_int[k][i][0]][leaf_coeff_int[k][i][1]] = 2;
			leaf_index_matrix[k][leaf_coeff_int[k][i][0]][leaf_coeff_int[k][i][1]] = i;
		}
	}
	


	vector<vector<vector<Node>>> temp_forest;
	for(int i = 0; i < trees; i++){
		temp_forest.push_back(tree);
	}
	vector<vector<int>> partitions_card;
	vector<int> temp_partitions;
	for(int i = 0; i < partitions.size(); i++){
		temp_partitions.push_back(partitions[i].indexes.size());
	} 
	for(int i = 0; i < trees; i++){
		partitions_card.push_back(temp_partitions);
	}

	
	vector<vector<vector<int>>> final_memory = prove_first_part(partitions_card, trees,attr);
	
	
	vector<vector<F>> final_mem(final_memory.size());
	for(int i = 0; i < final_mem.size(); i++){
		final_mem[i].resize(final_memory[i].size());
		for(int j = 0; j < final_mem[i].size(); j++){
			final_mem[i][j] = final_memory[i][j][4];
		}
	}
	
	clock_t t1,t2;
	
	t1 = clock();
	nodes_histogram_SNARK_data_forest data3 = get_node_histograms_transcript_forest(final_mem,  leaf_index_matrix, leaf_matrix,attr, leaf_coeff,trees,tree.size());
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	prove_node_histograms_forest(data3, trees , F(0));
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	
	printf("TOTAL PROVE TIME PHASE 3 : %lf \n",proving_time);
	printf("TOTAL VERIFICATION TIME PHASE 3 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	read_time = 0.0;
	
	vector<vector<vector<F>>> transformed_histograms(data3.node_histograms.size()*data3.node_histograms[0].size());
	
	for(int i = 0; i < data3.node_histograms.size(); i++){
		for(int j = 0; j < data3.node_histograms[i].size(); j++){
			transformed_histograms[i*data3.node_histograms[i].size()+j].resize(data3.node_histograms[i][j].size());
			for(int k = 0; k < data3.node_histograms[i][j].size(); k++){
				for(int l = 0; l < data3.node_histograms[i][j][k].size(); l++){
					transformed_histograms[i*data3.node_histograms[i].size()+j][k].push_back(data3.node_histograms[i][j][k][l].getInt64());	
				}
			}
		}
	}
	
	t1 = clock();
	
	split_SNARK_data data4;
	get_split_transcript_forest(data4,transformed_histograms, trees);
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	
	prove_split(data4,F(32));
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	
	printf("TOTAL PROVE TIME PHASE 4 : %lf \n",proving_time);
	printf("TOTAL VERIFICATION TIME PHASE 4 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	printf("TOTAL Proving time : %lf, Verification time : %lf, Proof size : %lf\n",total_p,total_v,total_s);
}


void test_lookups(){
	int nodes = 256;
	int h = 1024;
	vector<vector<F>> table(nodes);
	for(int i = 0; i < nodes; i++){
		table[i] = generate_randomness(h,F(32));
	}
	Comm commitment;
	generate_pp_hyperproofs(commitment,(int)log2(h*nodes),(int)log2(h));
	vector<vector<G1>> proofs = SVL_commit(convert2vector(table),commitment,nodes);
	vector<int> pos;
	for(int i = 0 ; i < nodes/2; i++){
		pos.push_back(2*i);
	}
	vector<F> y;
	vector<F> x2 = generate_randomness((int)log2(h),F(21));
	for(int i = 0; i < pos.size(); i++){
		y.push_back(evaluate_vector(table[pos[i]],x2));
	}
	printf("test ready\n");
	vector<float> perf; 
	segmented_lookup(table,pos,generate_randomness((int)log2(pos.size()),F(1)),x2,y,proofs,commitment,perf);

}

void test_aggr(){
	int lookups = 4;
	int poly_degree = 15;
	vector<F> poly = generate_randomness(1<<poly_degree,F(666));
	vector<vector<F>> x(lookups);
	vector<F> y;
	vector<F> x_common = generate_randomness(poly_degree - (int)log2(lookups),F(2));
	vector<vector<G1>> P(lookups);
	
	F s;
	for(int i = 0; i < lookups; i++){
		x[i] = x_common;
		for(int j = 0; j < (int)log2(lookups); j++){
			s.setByCSPRNG();
			x[i].push_back(s);
		}
		y.push_back(evaluate_vector(poly,x[i]));
	}
	Comm pp;
	
	generate_pp(pp,poly_degree);
	commit(poly,pp);
	for(int i = 0; i < lookups; i++){
		KZG_open(poly, x[i], pp);
		P[i] = pp.Proof;
		KZG_verify(x[i], y[i], pp);
	}
	
	
	vector<G2> u(lookups);
	vector<G1> w(lookups);
	G1 G;
	G2 H;
	char rand[256];
	for(int i = 0; i < 256; i++){
		rand[i] = i+'4';
	}
	mcl::bn::hashAndMapToG1(G,rand,256);

	mcl::bn::hashAndMapToG2(H,rand,256);
	
	
	for(int i = 0; i < lookups; i++){
		s.setByCSPRNG();
		w[i] = G*s;
		s.setByCSPRNG();
		u[i] = H*s;
	}
	Aggregate(P,w,u,x,y,pp.H,(int)log2(lookups),pp);

}



int main(int argc, char *argv[]){
	initPairing(mcl::BN_SNARK1);
	//initPairing(mcl::BLS12_381);
	elliptic_curves_init();
	init_hash();
	init_table();


	int mod = atoi(argv[1]);
	int size = atoi(argv[2]);
	int attributes = atoi(argv[3]);
	int trees = atoi(argv[4]);
	//int vectors = atoi(argv[4]);

	
	
	if(mod == 1){
		MAX_CHUNCK = 1ULL<<atoi(argv[5]);
		MIPP_gen_stream(pp_mul);
		
		if(_commitment_test){
			MIPP_gen_stream(pp);
			pp.prove_time = 0.0;
		}
		if(trees == 1){
			test_forest_training(1<<size,attributes,1);
			//test_tree_training(1<<size,attributes);
		}else{
			test_forest_training(1<<size,attributes,trees);
		}
	}else if(mod == 2){
		if(trees == 1){
			//test_forest_training_monolithic(1<<size,attributes,trees);

			test_tree_training_monolithic(1<<size,attributes);
		}else{
			test_forest_training_monolithic(1<<size,attributes,trees);
		}
	}else if(mod == 3){
		vector<F> data((1ULL<<size)/(trees));
		for(int i = 0; i  <data.size(); i++){
			data[i] = F(i+321);
		}
		printf("%d,%d,%d\n",data.size(),(1ULL<<size)/(trees),1ULL<<attributes);
		test_gkr(data, data, (1ULL<<size)/(trees), 1ULL<<attributes, trees);
		
	}else if(mod == 4){
		MAX_CHUNCK = 1<<atoi(argv[5]);
		if(_commitment_test){
			MIPP_gen_stream(pp);
			pp.prove_time = 0.0;
		}
		q_table_init();
		streaming_bagging_SNARK data = get_split_transcript_streaming_forest(1ULL<<size,  trees );
		prove_bagging(data);
	}else if(mod == 5){

		benchmark_lookup(1<<size, 1<<attributes, trees);
	}else if(mod == 6){
		MAX_CHUNCK = 1<<atoi(argv[5]);
		if(_commitment_test){
			MIPP_gen_stream(pp);
			pp.prove_time = 0.0;
		}
		proving_time = 0.0;
		
		vector<F> arr((1ULL<<size)*(1ULL<<attributes)/trees);
		for(int i = 0; i < arr.size(); i++){
			arr[i] = F(i+1);
		}
		test_gkr(arr, generate_randomness(10,F(21)), 1ULL<<size, 1ULL<<attributes, trees);
		
	}else if(mod == 9){
		MAX_CHUNCK = 1<<atoi(argv[5]);
		MIPP_gen_stream(pp);
		stream_descriptor fd; fd.name = "test"; fd.size = 1<<size; fd.pos = 0;
		vector<G1> comms;
		clock_t s,e;
		s = clock();
		MIPP_commit_stream(fd,fd.size,pp,comms);
		e = clock();
		
	}
	else if(mod == 7){
		vector<F> arr((1ULL<<size)*(trees));
		vector<F> bits;
		for(int i = 0; i < arr.size(); i++){
			arr[i] = F(rand());
		}
		clock_t s1,s2;
		s1 = clock();
		bits = prepare_bit_vector(arr,256);
		vector<F> eval = generate_randomness(size+(int)log2(trees),F(3));
		_prove_bit_decomposition(bits,eval,evaluate_vector(arr,eval),F(31),256);
		s2 = clock();
		printf("P : %lf, V : %lf, L : %lf\n",(double)(s2-s1)/(double)CLOCKS_PER_SEC,verification_time,(double)proof_len/1024.0);

	}else if(mod == 8){
		MAX_CHUNCK = 1<<atoi(argv[5]);
		clock_t s1,s2;
		s1 = clock();
		if(attributes == 1){
			stream_descriptor fd; fd.name = "sumcheck_test"; fd.size = 1ULL<<size;fd.pos =0;
			
			generate_2product_sumcheck_proof_stream(fd,fd,1ULL<<size, F(21));
		}else if(attributes == 2){
			stream_descriptor fd; fd.name = "sumcheck_test"; fd.size = 1ULL<<size;fd.pos =0;
			generate_2product_sumcheck_proof_stream_naive(fd,fd,1ULL<<size, F(21));
		}else{
			vector<F> arr1(1ULL<<size),arr2(1ULL<<size);
			F num = F(12);
			for(int i = 0; i < arr1.size(); i++){
				arr1[i] = num + (i);
				arr2[i] = num+ (i);
			}
			printf("OK\n");
			
			generate_2product_sumcheck_proof(arr1,arr2,F(21));
		}
		s2 = clock();
		printf("time : %lf, size : %lld\n", (double)(s2-s1)/(double)CLOCKS_PER_SEC,1ULL<<size);

	}
	else{
		
		MIPP_gen_stream(pp);
		int max_depth = atoi(argv[5]);
		vector<int> x;
		for(int i = 0; i < attributes; i++){
			x.push_back(rand()%100);
		}
		forest_inference_sumcheck(x,  max_depth, attributes, 1ULL<<size, trees);
	}
	

	
	exit(-1);
	
	
	/*
	FILE *fp = fopen("test_big","w");
	vector<F> arr(32*1024*1024);
	for(int i = 0; i < arr.size(); i++){
		arr[i] = F(2*i + 2103);
	}
	write_file(arr,fp);
	fclose(fp);
	printf("Data written\n");
	*/
	
	
	exit(-1);

	Dataset D_train,D_test;
	int data_insances = atoi(argv[1]);
	int test_samples = 0;
	max_depth = 5;
	int attributes_num = 8;


	//int data_insances = atoi(argv[1]);
	int write = atoi(argv[2]);
	MAX_CHUNCK = 1ULL <<(atoi(argv[3]));


	LoadDummyDataset(test_samples,data_insances,attributes, D_train,D_test);

	//vector<vector<Node>> dummy_tree = BuildTree(D_train,max_depth);
	//test_accuracy(D_test,dummy_tree);

	//printf("%d\n",D_train.data[0].size() );
	//exit(-1);

	vector<Dataset> partitions;
	
	//LoadDiabetesDataset(D_train,D_test,test_samples,"/home/christodoulos/datasets/Healthcare-Diabetes.csv");
	
	//LoadIrisDataset(D_train,D_test);
	vector<vector<Node>> tree = BuildTree(D_train,partitions,max_depth);
	


	// =================================================
	// TRAINING PROVE FOREST


	


	/***********************************/
	/*
	partition_SNARK_data_streaming spartition_data = get_partitions_transcript_streaming(D_train, partitions, tree, prepare_tree(tree),  max_depth, write);
	prove_correct_partitions_streaming(spartition_data, D_train, prepare_tree(tree), max_depth);
	histogram_SNARK_data_streaming data =  get_histograms_transcript_streaming(D_train, spartition_data.data_partitions, spartition_data.label, tree, attributes_num, write);
	data.input_data = spartition_data.input_data;
	data.input_aux = spartition_data.input_aux;

	prove_correct_histograms_streaming(data, attributes_num, F(0));
	*/



	/***********************************/
	vector<F> y;
	partition_SNARK_data partition_data =  get_partitions_transcript(D_train, partitions, tree);
	
	partition_SNARK_proof P1 = prove_correct_partitions(partition_data, D_train, prepare_tree(tree) ,max_depth);
	
	printf("Data size : %d\n",D_train.data.size()*D_train.data[0].size() );
	histogram_SNARK_data histogram_data = get_histograms_transcript(D_train, partition_data.data_partitions, partition_data.label, tree, attributes_num);
	histogram_data.input_data = partition_data.input_data;
	histogram_SNARK_proof P2 = prove_histograms(histogram_data, attributes_num, P1.final_rand);




	return 0;
}