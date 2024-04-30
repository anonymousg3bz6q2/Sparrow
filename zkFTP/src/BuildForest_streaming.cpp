#include "BuildTree.h"
#include "config_pc.hpp"
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <sstream>
#include <bits/stdc++.h>
#include <chrono>
#include "Inference.h"
#include "utils.hpp"
#include "GKR.h"
#include "sumcheck.h"
#include "quantization.h"
#include "lookups.h"
#include "mimc.h"
#include "BuildForest_streaming.h"
#include "witness_stream.h"
#include "space_efficient_sumcheck.h"
#include "utils.hpp"
#include "Poly_Commit.h"
#include "utils.hpp"
#include "pol_verifier.h"

int total_nodes;
int attr;
extern int bin_size;
extern size_t MAX_CHUNCK;
extern double proving_time;
extern double read_time;
extern double clear_cache_time;
extern double stream_access_time;
extern double inference_time;
extern double verification_time;
extern int proof_len;
extern vector<int> discrete_table;
extern F A_,B_,seed;
extern MIPP_Comm pp;
stream_descriptor lookup_stream;
extern vector<unsigned long long int> gini_input;
vector<vector<unsigned long long int>> best_gini;
extern float total_p,total_v,total_s;
extern int _commitment_test;
	
vector<G1> input_commit;

void commit_partitions(partition_SNARK_data_streaming_forest data, vector<vector<vector<F>>> forest, vector<vector<G1>> &commitments){
	vector<G1> C;
	MIPP_commit_stream(data.permuted_data,data.permuted_data.size,pp,C);
	commitments.push_back(C);
	MIPP_commit_stream(data.input_data,data.input_data.size,pp,C);
	input_commit = C;
	commitments.push_back(C);
	MIPP_commit_stream(data.paths,data.paths.size,pp,C);
	commitments.push_back(C);
	MIPP_commit_stream(data.paths_aux,data.paths_aux.size,pp,C);
	commitments.push_back(C);
	MIPP_commit_stream(data.diff_data,data.diff_data.size,pp,C);
	commitments.push_back(C);
	MIPP_commit_stream(data.bit_vectors,data.bit_vectors.size,pp,C);
	commitments.push_back(C);

	
	vector<F> forest_poly;
	for(int i = 0; i < forest.size(); i++){
		for(int j = 0; j < forest[i].size(); j++){
			forest_poly.insert(forest_poly.end(),forest[i][j].begin(),forest[i][j].end());
		}
	}
	printf("OK\n");
	MIPP_commit(forest_poly,pp,C);
	commitments.push_back(C);
	vector<F> bits = convert2vector(data.power_bits);
	MIPP_commit(bits,pp,C);
	commitments.push_back(C);
	

}

void open_partitions(partition_SNARK_data_streaming_forest data,vector<vector<vector<F>>> forest , vector<vector<G1>> commitments){
	
	MIPP_open_stream(data.permuted_data,data.permuted_data.size,generate_randomness((int)log2(data.permuted_data.size),F(321)),pp,commitments[0]);
	MIPP_open_stream(data.input_data,data.input_data.size,generate_randomness((int)log2(data.input_data.size),F(321)),pp,commitments[1]);
	MIPP_open_stream(data.paths,data.paths.size,generate_randomness((int)log2(data.paths.size),F(321)),pp,commitments[2]);
	MIPP_open_stream(data.paths_aux,data.paths_aux.size,generate_randomness((int)log2(data.paths_aux.size),F(321)),pp,commitments[3]);
	MIPP_open_stream(data.diff_data,data.diff_data.size,generate_randomness((int)log2(data.diff_data.size),F(321)),pp,commitments[4]);
	MIPP_open_stream(data.bit_vectors,data.bit_vectors.size,generate_randomness((int)log2(data.bit_vectors.size),F(321)),pp,commitments[5]);
	
	vector<F> forest_poly;
	for(int i = 0; i < forest.size(); i++){
		for(int j = 0; j < forest[i].size(); j++){
			forest_poly.insert(forest_poly.end(),forest[i][j].begin(),forest[i][j].end());
		}
	}
	pad_vector(forest_poly);
	MIPP_open(forest_poly,generate_randomness((int)log2(forest_poly.size()),F(321)),pp,commitments[6]);
	vector<F> bits = convert2vector(data.power_bits);
	
	MIPP_open(bits,generate_randomness((int)log2(bits.size()),F(321)),pp,commitments[7]);
	
	printf("P : %lf, V : %lf, L : %lf\n",pp.prove_time,pp.verification_time,(double)pp.proof_size/1024.0);
	total_p += pp.prove_time;
	total_v += pp.verification_time;
	total_s += (double)pp.proof_size/1024.0;
	
	pp.prove_time = 0.0;
	pp.verification_time = 0.0;
	pp.proof_size =0;
}

void prove_correct_partitions_streaming_forest(partition_SNARK_data_streaming_forest data, Dataset &D, vector<vector<vector<F>>> forest,int max_depth){
	vector<vector<G1>> commitments;
	if(_commitment_test){
		printf("Commiting Partitions\n");

		commit_partitions(data,forest,commitments);
		printf("Opening Partitions\n");
		open_partitions(data,forest,commitments);
		commitments.clear();
		return;
	}
	
	printf("Proving correctness of partitions\n");
	streaming_forest_partition_sumcheck_1(data, forest.size());
	printf("sumcheck partition 1 completed\n");
	streaming_forest_partition_sumcheck_2(data, forest);
	printf("sumcheck partition 2 completed\n");
	streaming_forest_partition_sumcheck_3(data, forest);
	printf("sumcheck partition 3 completed\n");
	printf("TOTAL PROVE TIME PHASE 1 : %lf , %lf ,%lf\n",proving_time,stream_access_time,inference_time);
	printf("TOTAL VERIFICATION TIME PHASE 1 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	stream_access_time = 0.0;
	clear_cache_time = 0.0;
	read_time = 0.0;
}




void commit_histograms_leaves(histogram_SNARK_data_streaming_forest data , vector<vector<G1>> &commitments){
	vector<G1> C;
	//printf("OKL");
	printf("OK\n");
	
	MIPP_commit_stream(data.histograms_counter,data.histograms_counter.size,pp,C);
	commitments.push_back(C);
	//MIPP_commit_stream(data.write_transcript,data.write_transcript.size,pp,C);
	//commitments.push_back(C);
	vector<vector<F>> final_memory(data.memory_init.size());//(Tree.size()*D.data.size()*2*bin_size);
	for(int i = 0; i < data.memory_init.size(); i++){
		final_memory[i].resize(data.memory_init[i].size());
		//for(int j = 0; j < data.memory_init[i].size(); j++){
		//	final_memory[i][j].resize(8,F_ZERO);
		//}
	}
	
	get_final_hist_forest(final_memory);
	// commit final histograms
	vector<F> hist_poly;
	for(int i = 0; i < final_memory.size(); i++){
		hist_poly.insert(hist_poly.end(), final_memory[i].begin(),final_memory[i].end());
		//for(int j = 0 ; j < final_memory[i].size(); j++){
		//	hist_poly.insert(hist_poly.end(), final_memory[i][j].begin(),final_memory[i][j].end());
		//}
	}
	pad_vector(hist_poly);
	MIPP_commit(hist_poly,pp,C);
	commitments.push_back(C);
	hist_poly.clear();
}

void open_histograms_leaves(histogram_SNARK_data_streaming_forest data , vector<vector<G1>> &commitments){
	vector<G1> C;
	printf("Opne leaves\n");
	MIPP_open_stream(data.input_data,data.input_data.size,generate_randomness((int)log2(data.input_data.size),F(321)),pp,input_commit);
	MIPP_open_stream(data.histograms_counter,data.histograms_counter.size,generate_randomness((int)log2(data.histograms_counter.size),F(321)),pp,commitments[0]);
	//MIPP_open_stream(data.write_transcript,data.write_transcript.size,generate_randomness((int)log2(data.write_transcript.size),F(321)),pp,commitments[0]);
	vector<vector<F>> final_memory(data.memory_init.size());//(Tree.size()*D.data.size()*2*bin_size);
	for(int i = 0; i < data.memory_init.size(); i++){
		final_memory[i].resize(data.memory_init[i].size());
		//for(int j = 0; j < data.memory_init[i].size(); j++){
		//	final_memory[i][j].resize(8,F_ZERO);
		//}
	}
	get_final_hist_forest(final_memory);
	
	vector<F> hist_poly;
	for(int i = 0; i < final_memory.size(); i++){
		hist_poly.insert(hist_poly.end(), final_memory[i].begin(),final_memory[i].end());
		//for(int j = 0 ; j < final_memory[i].size(); j++){
		//	hist_poly.insert(hist_poly.end(), final_memory[i][j].begin(),final_memory[i][j].end());
		//}
	}
	pad_vector(hist_poly);
	
	MIPP_open(hist_poly,generate_randomness((int)log2(hist_poly.size()),F(321)),pp,commitments[1]);
	

	hist_poly.clear();
	
	total_p += pp.prove_time;
	total_v += pp.verification_time;
	total_s += (double)pp.proof_size/1024.0;
	printf("P : %lf, V : %lf, L : %lf\n",pp.prove_time,pp.verification_time,(double)pp.proof_size/1024.0);
	
	pp.prove_time = 0.0;
	pp.verification_time = 0.0;
	pp.proof_size =0;

	
}


void prove_correct_histograms_streaming_forest(histogram_SNARK_data_streaming_forest data, int Attr, F previous_r){
	vector<vector<G1>> commitments;
	if(_commitment_test){
		printf("Commit Histograms\n");
		commit_histograms_leaves(data,commitments);
		printf("Open Histograms\n");
		open_histograms_leaves(data,commitments);
		commitments.clear();
		return;
	}
	printf("Proving correctness of histograms\n");
	streaming_forest_sumcheck_leaves_1( data, Attr, previous_r);
	
	streaming_forest_sumcheck_leaves_2( data, Attr, previous_r);
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	
	printf("TOTAL PROVE TIME PHASE 2 : %lf , %lf , %lf\n",proving_time,stream_access_time, inference_time);
	printf("TOTAL VERIFICATION TIME PHASE 2 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	clear_cache_time = 0.0;
	read_time = 0.0;

}


void prove_correct_node_histograms_streaming_forest(nodes_histogram_data_streaming data, int trees, int attr, int leaves , F previous_r){
	vector<vector<F>> witness_coeff(trees);
	vector<F> randomness(1);
	
	for(int k = 0; k < data.leaf_matrix.size(); k++){
		for(int i = data.leaf_matrix[k].size()-1; i > 0; i--){
			for(int j = 0; j < data.leaf_matrix[k][i].size(); j+=2){
				if(data.leaf_matrix[k][i][j] != -1){
					witness_coeff[k].push_back(F(i));
					witness_coeff[k].push_back(F(j));
					witness_coeff[k].push_back(F(i));
					witness_coeff[k].push_back(F(j+1));	
				}
			}
		}
	}
	F two_inv = F(2);
	two_inv.inv(two_inv,two_inv);
	
	int witness_size = attr*bin_size*2;
	vector<F> r = generate_randomness((int)log2(witness_size),previous_r);
	vector<F> compress_vector;
	precompute_beta(r,compress_vector);
	
	vector<vector<F>> compressed_leaf_hist,compressed_node_hist,compressed_witness,compressed_out;

	compute_compressed_histograms(compressed_leaf_hist,compressed_node_hist,compressed_witness,compressed_out,compress_vector);
	printf("%d\n",compress_vector.size());
    printf("%d,%d,%d,%d,%d,%d,%d,%d,\n",compressed_leaf_hist.size(),compressed_leaf_hist[0].size(),compressed_node_hist.size(),compressed_node_hist[0].size(),
	compressed_witness.size(),compressed_witness[0].size(),compressed_out.size(),compressed_out[0].size());
	vector<F> gkr_data;
	F rand;
	F a = mimc_hash(r[r.size()-1],F(0));
	F b = mimc_hash(a,F(1));
	F c = mimc_hash(b,F(2));
	F d = mimc_hash(c,F(3));
	rand = mimc_hash(d,F(0));

	

	for(int k = 0; k < trees; k++){
		pad_vector(data.leaf_coeff[k]);
		pad_vector(data.node_coeff[k]);
		pad_vector(witness_coeff[k]);
		pad_vector(compressed_leaf_hist[k]);
		pad_vector(compressed_node_hist[k]);
		pad_vector(compressed_out[k]);
		pad_vector(compressed_witness[k]);
		
	}
	
	for(int i = 0; i < witness_coeff.size(); i++){
		gkr_data.insert(gkr_data.end(),witness_coeff[i].begin(),witness_coeff[i].end());
	}
	for(int i = 0; i < trees; i++ ){
		gkr_data.insert(gkr_data.end(),data.node_coeff[i].begin(),data.node_coeff[i].end());
	}
	for(int i = 0; i < trees; i++ ){
		gkr_data.insert(gkr_data.end(),data.leaf_coeff[i].begin(),data.leaf_coeff[i].end());
	}
	for(int i = 0; i < trees; i++ ){
		gkr_data.insert(gkr_data.end(),compressed_witness[i].begin(),compressed_witness[i].end());
	}
	for(int i = 0; i < trees; i++ ){
		gkr_data.insert(gkr_data.end(),compressed_node_hist[i].begin(),compressed_node_hist[i].end());
	}
	for(int i = 0; i < trees; i++ ){
		gkr_data.insert(gkr_data.end(),compressed_out[i].begin(),compressed_out[i].end());
	}
	for(int i = 0; i < trees; i++ ){
		gkr_data.insert(gkr_data.end(),compressed_leaf_hist[i].begin(),compressed_leaf_hist[i].end());
	}
	

	gkr_data.push_back(a);
	gkr_data.push_back(b);
	gkr_data.push_back(c);
	gkr_data.push_back(d);
	gkr_data.push_back(two_inv);
	gkr_data.push_back(F(1));
	
	// Compute arr1 = a*leaf_coef[2*i]+b*leaf_coef[2*i+1] + c*compressed_leaf_hist[i] -c
	
	// Prove consistency of compressed histograms and tree coefficients
	randomness[0] = rand;
	
	proof GKR_proof1 = node_histogram_consistency_forest(gkr_data,randomness,leaves,leaves-1,trees);
	vector<F> x_leaf,x_node,x_witness,x_compressed_leaf,x_compressed_node,x_compressed_witness,x_compressed_out;
	vector<F> x = GKR_proof1.randomness[GKR_proof1.randomness.size()-1];
	if(GKR_proof1.q_poly[0].eval(0) + GKR_proof1.q_poly[0].eval(1) != F(0)){
		printf("Error in nodes histograms 1\n");
		//exit(-1);
	}

	for(int i = 0; i < (int)log2(convert2vector(witness_coeff).size()); i++){x_witness.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(convert2vector(data.node_coeff).size()); i++){x_node.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(convert2vector(data.leaf_coeff).size()); i++){x_leaf.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(convert2vector(compressed_witness).size()); i++){x_compressed_witness.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(convert2vector(compressed_node_hist).size()); i++){x_compressed_node.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(convert2vector(compressed_leaf_hist).size()); i++){x_compressed_leaf.push_back(x[i]);}

	F wit_eval = evaluate_vector(convert2vector(witness_coeff),x_witness);
	F node_eval = evaluate_vector(convert2vector(data.node_coeff),x_node);
	F leaf_eval = evaluate_vector(convert2vector(data.leaf_coeff),x_leaf);
	F comp_wit_eval = evaluate_vector(convert2vector(compressed_witness),x_compressed_witness);
	F comp_node_eval = evaluate_vector(convert2vector(compressed_node_hist),x_compressed_node);
	F comp_out_eval = evaluate_vector(convert2vector(compressed_out),x_compressed_node);
	F comp_leaf_eval = evaluate_vector(convert2vector(compressed_leaf_hist),x_compressed_leaf);

	// Prove that the histograms compressed correctly
	
	rand = mimc_hash(GKR_proof1.final_rand,wit_eval);
	rand = mimc_hash(rand,node_eval);
	rand = mimc_hash(rand,leaf_eval);
	rand = mimc_hash(rand,comp_wit_eval);
	rand = mimc_hash(rand,comp_node_eval);
	rand = mimc_hash(rand,comp_out_eval);
	rand = mimc_hash(rand,comp_leaf_eval);
	
	vector<stream_descriptor> fd;fd.push_back(data.leaf_histograms);
	vector<size_t> fd_cols; fd_cols.push_back(compress_vector.size());
	vector<size_t> fd_size; fd_size.push_back(data.leaf_histograms.size/compress_vector.size()); 
	
	
	clock_t t1,t2;
	t1 = clock();
	vector<F> prod = prepare_matrix_streaming(fd,fd_cols,fd_size,data.leaf_histograms.size/compress_vector.size(),x_compressed_leaf,compress_vector.size()); 
	proof Pr1 = generate_2product_sumcheck_proof(prod,compress_vector,previous_r);
	verify_2product_sumcheck(Pr1,Pr1.q_poly[0].eval(F_ONE)+Pr1.q_poly[0].eval(F_ZERO));
	fd.clear();fd_size.clear();

	fd.push_back(data.node_histograms);fd_size.push_back(data.node_histograms.size/compress_vector.size());
	prod = prepare_matrix_streaming(fd,fd_cols,fd_size,data.node_histograms.size/compress_vector.size(),x_compressed_node,compress_vector.size()); 
	Pr1 = generate_2product_sumcheck_proof(prod,compress_vector,previous_r);
	verify_2product_sumcheck(Pr1,Pr1.q_poly[0].eval(F_ONE)+Pr1.q_poly[0].eval(F_ZERO));
	fd.clear();fd_size.clear();

	fd.push_back(data.witness_hist);fd_size.push_back(data.witness_hist.size/compress_vector.size());
	prod = prepare_matrix_streaming(fd,fd_cols,fd_size,data.witness_hist.size/compress_vector.size(),x_compressed_witness,compress_vector.size()); 
	Pr1 = generate_2product_sumcheck_proof(prod,compress_vector,previous_r);
	verify_2product_sumcheck(Pr1,Pr1.q_poly[0].eval(F_ONE)+Pr1.q_poly[0].eval(F_ZERO));
	fd.clear();fd_size.clear();

	fd.push_back(data.out_hist);fd_size.push_back(data.out_hist.size/compress_vector.size());
	prod = prepare_matrix_streaming(fd,fd_cols,fd_size,data.out_hist.size/compress_vector.size(),x_compressed_node,compress_vector.size()); 
	Pr1 = generate_2product_sumcheck_proof(prod,compress_vector,previous_r);
	verify_2product_sumcheck(Pr1,Pr1.q_poly[0].eval(F_ONE)+Pr1.q_poly[0].eval(F_ZERO));
	fd.clear();fd_size.clear();
	t2 = clock();
	proving_time+= (float)(t2-t1)/(float)CLOCKS_PER_SEC;	

}


void commit_bagging(streaming_bagging_SNARK data, vector<vector<G1>> &commitments){
	vector<G1> C;
	printf("%d,%lld\n",data.randomness_quotient.size,data.bits_fd.size);
	MIPP_commit_stream_bits(data.bits_fd,data.bits_fd.size,pp,C);
	commitments.push_back(C);	

	MIPP_commit_stream(data.randomness_quotient,data.randomness_quotient.size,pp,C);
	commitments.push_back(C);
	MIPP_commit_stream(data.randomness,data.randomness.size,pp,C);
	commitments.push_back(C);
	MIPP_commit_stream(data.randomness_remainder,data.randomness_remainder.size,pp,C);
	commitments.push_back(C);

}

void open_bagging(streaming_bagging_SNARK data, vector<vector<G1>> commitments){
	MIPP_open_stream(data.randomness_quotient,data.randomness_quotient.size,generate_randomness((int)log2(data.randomness_quotient.size),F(32)),pp,commitments[0]);
	MIPP_open_stream(data.randomness,data.randomness.size,generate_randomness((int)log2(data.randomness.size),F(32)),pp,commitments[1]);
	MIPP_open_stream(data.randomness_remainder,data.randomness_remainder.size,generate_randomness((int)log2(data.randomness_remainder.size),F(32)),pp,commitments[2]);
	MIPP_open_stream(data.bits_fd,data.bits_fd.size,generate_randomness((int)log2(data.bits_fd.size),F(32)),pp,commitments[3]);
}

void prove_bagging(streaming_bagging_SNARK data){
	data.bits_fd;data.bits_fd.name = "quotient_bits";data.bits_fd.size = data.randomness_quotient.size*256;
	data.bits_fd.pos = 0;
	if(_commitment_test){
		vector<vector<G1>> commitments;
		commit_bagging(data,commitments);
		open_bagging(data,commitments);
		printf("P : %lf, V : %lf, size : %lf\n",pp.prove_time,pp.verification_time,(double)pp.proof_size/1024.0);
		return;
	}

	stream_descriptor dummy_descriptor;dummy_descriptor.pos = -1;
	lookup_stream.name = "randomness_quotient";lookup_stream.size = data.randomness_quotient.size;lookup_stream.pos = 0;
	printf("size : %lld\n",data.bits_fd.size);
	clock_t ls,le;
	ls = clock();
	proof_stream P = generate_3product_sumcheck_proof_stream(data.bits_fd, dummy_descriptor, data.bits_fd.size, generate_randomness((int)log2(data.bits_fd.size),F(32)), F(32), 1);
	
	//lookup_proof P1 = lookup_range_proof_streaming( F(213), 256);
	le = clock();
	printf("%lf\n",(double)(le-ls)/(double)CLOCKS_PER_SEC);
	//if(evaluate_vector_stream(data.randomness_quotient,P1.input_x,data.randomness_quotient.size) != P1.final_eval){
	//	printf("Error\n");
	//}
	vector<F> x_compressed;
	F compressed_eval;
	printf("%lf \n",proving_time);
	clock_t s,e;
	s = clock();
	streaming_bagging_1( data,x_compressed,compressed_eval, F(321));
	streaming_bagging_2( data,x_compressed,compressed_eval, F(321));
	e = clock();
	printf("Ptime : %lf, Vtime : %lf, Pzie : %lf\n",(double)(e-s)/(double)CLOCKS_PER_SEC+(double)(le-ls)/(double)CLOCKS_PER_SEC,verification_time,(float)proof_len/1024.0);
}

void commit_split_data(split_SNARK_streaming_forest &data, vector<vector<G1>> &commitments){
	stream_descriptor cond; cond.name = "cond"; cond.pos = 0; cond.size  = data.divisors.size;
	stream_descriptor cond_inv; cond_inv.name = "cond_inv"; cond_inv.pos = 0; cond_inv.size  = data.divisors.size;
	vector<G1> C;
	stream_descriptor s_ginis;s_ginis.size = data.gini_inputs.size/4; s_ginis.pos  =0;s_ginis.name = "sub_ginis";
	stream_descriptor gini_bits;gini_bits.name = "sub_ginis_bits";gini_bits.size = 32*s_ginis.size;gini_bits.pos = 0;
	stream_descriptor bits;bits.name = "remainders_bits"; bits.size = data.remainders.size*64; bits.pos = 0;
	
	MIPP_commit_stream(cond_inv,cond_inv.size,pp,C);
	commitments.push_back(C);
	MIPP_commit_stream(cond_inv,cond_inv.size,pp,C);
	commitments.push_back(C);
	MIPP_commit_stream(data.gini_inputs,data.gini_inputs.size,pp,C);
	commitments.push_back(C);
	MIPP_commit_stream(data.quotients,data.quotients.size,pp,C);
	commitments.push_back(C);
	MIPP_commit_stream_bits(gini_bits,gini_bits.size,pp,C);
	commitments.push_back(C);
	MIPP_commit_stream_bits(bits,bits.size,pp,C);
	commitments.push_back(C);
	
	printf("OK\n");
	

}

void open_split_data(split_SNARK_streaming_forest &data, vector<vector<G1>> commitments){
	stream_descriptor cond; cond.name = "cond"; cond.pos = 0; cond.size  = data.divisors.size;
	stream_descriptor cond_inv; cond_inv.name = "cond_inv"; cond_inv.pos = 0; cond_inv.size  = data.divisors.size;
	vector<G1> C;
	stream_descriptor s_ginis;s_ginis.size = data.gini_inputs.size/4; s_ginis.pos  =0;s_ginis.name = "sub_ginis";
	stream_descriptor gini_bits;gini_bits.name = "sub_ginis_bits";gini_bits.size = 32*s_ginis.size;gini_bits.pos = 0;
	stream_descriptor bits;bits.name = "remainders_bits"; bits.size = data.remainders.size*64; bits.pos = 0;
	
	MIPP_open_stream(cond,cond.size,generate_randomness((int)log2(cond.size),F(4223)),pp,commitments[0]);
	
	MIPP_open_stream(cond_inv,cond_inv.size,generate_randomness((int)log2(cond_inv.size),F(4223)),pp,commitments[1]);
	
	MIPP_open_stream(data.gini_inputs,data.gini_inputs.size,generate_randomness((int)log2(data.gini_inputs.size),F(4223)),pp,commitments[2]);
	
	MIPP_open_stream(data.quotients,data.quotients.size,generate_randomness((int)log2(data.quotients.size),F(4223)),pp,commitments[3]);
	
	MIPP_open_stream(gini_bits,gini_bits.size,generate_randomness((int)log2(gini_bits.size),F(4223)),pp,commitments[4]);
	MIPP_open_stream(bits,bits.size,generate_randomness((int)log2(bits.size),F(4223)),pp,commitments[5]);
	
	total_p += pp.prove_time;
	total_v += pp.verification_time;
	total_s += (double)pp.proof_size/1024.0;
	
	printf("OK\n");
	pp.prove_time = 0.0;
	pp.verification_time = 0.0;
	pp.proof_size =0;

}



void prove_correct_split_forest(split_SNARK_streaming_forest &data, F previous_r){
	proving_time = 0.0;
	stream_descriptor s_ginis;s_ginis.size = data.gini_inputs.size/4; s_ginis.pos  =0;s_ginis.name = "sub_ginis";
	vector<F> eval_x = generate_randomness((int)log2(gini_input.size()/2), previous_r );
	vector<F> x_dividents,x_divisors;
	F divident_eval,divisor_eval;
	vector<vector<G1>> commitments;
	if(_commitment_test){
		printf("Commit split\n");
		commit_split_data(data,commitments);
		printf("Open split\n");
		open_split_data(data,commitments);
	
		
		
		///lookup_stream.name = "sub_ginis";lookup_stream.size = data.ginis.size;lookup_stream.pos = 0;
		//test_lookup_commitment_streaming(32);
		//lookup_stream.name = "remainders";lookup_stream.size = data.remainders.size;lookup_stream.pos = 0;
		//test_lookup_commitment_streaming(64);
		printf("lookup : P : %lf, V : %lf, L : %lf\n",pp.prove_time,pp.verification_time,(double)pp.proof_size/1024.0);
	
		total_p += pp.prove_time;
		total_v += pp.verification_time;
		total_s += (double)pp.proof_size/1024.0;
		
		return;
	}

	auto t1 = chrono::high_resolution_clock::now();
    
	F eval = evaluate_vector_stream(data.remainders,eval_x,data.remainders.size);
	vector<F> x_sub = generate_randomness((int)log2(s_ginis.size),F(321));
	F eval_sub = evaluate_vector_stream(s_ginis,x_sub,s_ginis.size);
	
	
	//lookup_stream.name = "sub_ginis";lookup_stream.size = data.ginis.size;lookup_stream.pos = 0;
	//lookup_proof P1 = lookup_range_proof_streaming( F(213), 32);

	stream_descriptor bits;bits.name = "sub_ginis_bits";bits.size = 32*s_ginis.size;bits.pos = 0;
	
	printf("Size : %ld\n",bits.size);
	_prove_bit_decomposition_stream(bits, bits.size, x_sub , eval_sub , x_sub[x_sub.size()-1], 32);
	

	vector<F> x1,x2; 
	x1 = x_sub;
	//for(int i = 0; i < (int)log2(s_ginis.size); i++){
	//	x1.push_back(P1.read_eval_x[i]);
	//}
	//data.ginis.pos = 0;
	//F eval_ginis = evaluate_vector_stream(data.ginis,x1,data.ginis.size);
	
	vector<F> best_ginis;
	for(int i = 0; i < best_gini.size(); i++){
		for(int j = 0 ; j  < best_gini[i].size(); j++){
			best_ginis.push_back(F(best_gini[i][j]));
		}
	}
	
	pad_vector(best_ginis);
	int total_nodes_pad = best_ginis.size();
	
	//if(P1.final_eval !=  eval_ginis - evaluate_vector(best_ginis,x1)){
	//	printf("Error\n");
	//}
	
	
	vector<F> prev_x;
	
	mul_tree_proof_stream mP1 = prove_multiplication_tree_stream(s_ginis,best_ginis.size(),128,x1[x1.size()-1],prev_x);
	F eval_ginis_2 = evaluate_vector_stream(data.ginis,mP1.r,data.ginis.size);
	if(mP1.final_eval != eval_ginis_2 - evaluate_vector(best_ginis,mP1.r)){
		printf("Error 2\n");
	}
	best_ginis.clear();
	
	//lookup_stream.name = "remainders";lookup_stream.size = data.remainders.size;lookup_stream.pos = 0;
	//lookup_range_proof_streaming( F(213), 64);
	
	
	x1 = generate_randomness((int)log2(data.remainders.size),x1[x1.size()-1]);
	
	bits.name = "remainders_bits"; bits.size = data.remainders.size*64; bits.pos = 0;
	F eval_remainder = evaluate_vector_stream(data.remainders,x1,data.remainders.size);
	printf("Size : %ld\n",bits.size);
	_prove_bit_decomposition_stream(bits,bits.size,x1,eval_remainder,x1[x1.size()-1],64);
	
	streaming_gini_sumcheck_1( data,x1, attr, eval_remainder,previous_r,x_dividents,x_divisors,divident_eval,divisor_eval);
	
	streaming_gini_sumcheck_2(data, x_dividents,x_divisors ,divisor_eval, divident_eval, previous_r);
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    printf("TOTAL PROVE TIME PHASE 4 : %lf , %lf\n",proving_time,stream_access_time);
	printf("TOTAL VERIFICATION TIME PHASE 4 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	total_p += proving_time;
	total_v += verification_time;
	total_s += (float)proof_len/1024.0;
	
	verification_time = 0.0;
	proof_len = 0;
	proving_time = 0.0;
	clear_cache_time = 0.0;
	read_time = 0.0;
	
	
	
}



partition_SNARK_data_streaming_forest get_partitions_transcript_streaming_forest(Dataset D, vector<vector<int>> Partitions, vector<vector<vector<Node>>> _forest,
 vector<vector<vector<F>>> forest, int max_depth, int write){
	partition_SNARK_data_streaming_forest data;
	data.input_data.name = "input";data.input_data.pos = 0;
	data.input_data.col_size = D.data.size()*2;data.input_data.row_size = D.data[0].size();
	data.input_data.size = D.data[0].size()*D.data.size()*2;

	data.permuted_data.name = "permuted_input"; data.permuted_data.pos = 0;
	data.permuted_data.col_size = D.data.size()*2;data.permuted_data.row_size = forest.size()*D.data[0].size(); 
	data.permuted_data.size = forest.size()*D.data[0].size()*D.data.size()*2;

	data.paths.name = "path";data.paths.pos =0;
	data.paths.row_size = forest.size()*D.data[0].size();
	data.paths.col_size =  normalize_number(4*max_depth);
	data.paths.size = data.paths.row_size*data.paths.col_size;

	data.bit_vectors.name = "bit_vector";data.bit_vectors.pos = 0;
	int q = ((int)log2(bin_size));
	if(1 << ((int)log2(q)) != q){
		q = 1 << ((int)log2(q)+1);
	}
	data.bit_vectors.size = forest.size()*normalize_number((size_t)max_depth*(size_t)D.data[0].size()*(size_t)q);
	

	data.diff_data.name = "diff"; data.diff_data.pos = 0;
	data.diff_data.size = forest.size()*normalize_number((size_t)max_depth*(size_t)D.data[0].size());
	
	data.input_aux.name = "input_aux";data.input_aux.pos = 0;
	data.input_aux.size = forest.size()*2*D.data[0].size();
	data.input_aux.col_size = 2;data.input_aux.row_size = D.data[0].size();

	data.paths_aux.name = "path_aux"; data.paths_aux.pos = 0;
	data.paths_aux.size = forest.size()*2*D.data[0].size();
	data.paths_aux.col_size = 2;data.paths_aux.row_size = forest.size()*D.data[0].size();

	data.powers.resize(Partitions.size());
	data.int_pows.resize(Partitions.size());
	
	
	for(int i = 0; i < Partitions.size(); i++){
		for(int j = 0; j < Partitions[i].size(); j++){
			data.powers[i].push_back(F(Partitions[i][j]));
			data.int_pows[i].push_back(Partitions[i][j]);
		}
		pad_vector(data.powers[i]);
	}
	for(int i = 1; i < forest.size(); i++){
		for(int j= 0; j < data.powers[i].size(); j++){
			if(data.powers[i][j] !=data.powers[0][j] ){
				printf("error %d %d\n",i,j);
			}
		}
	}
	//pad_matrix(data.powers);
	data.power_bits.resize(forest.size());
	for(int i = 0; i < forest.size(); i++){
		data.power_bits[i] = prepare_bit_vector(data.powers[i],32);
	}


	F commitment = F(0);
	vector<F> compress_vector = generate_randomness(3,F(0));
	//P.compress_vector = compress_vector;
	vector<F> tree_compress_vector = generate_randomness(data.paths.col_size+2,compress_vector[2]);
	vector<vector<F>> compressed_tree(forest.size());
	for(int i = 0; i < forest.size(); i++){
		compressed_tree[i].resize(forest[i].size(),F(1));
	}
	data.tree_compress_vector = tree_compress_vector;
	for(int k = 0; k < forest.size(); k++){
		for(int i = 0; i < forest[k].size(); i++){
			int j;
			for(int j = 0; j < forest[k][i].size()-2; j++){
				compressed_tree[k][i] += forest[k][i][j]*tree_compress_vector[j];
			}
			compressed_tree[k][i] += tree_compress_vector[data.paths.col_size ]*forest[k][i][j] + tree_compress_vector[data.paths.col_size +1]*forest[k][i][j+1] ;
		}
		pad_vector_with_num(compressed_tree[k],F(1));
	}
	for(int i = 1; i < compressed_tree.size(); i++){
		for(int j = 0; j < compressed_tree[i].size(); j++){
			if(compressed_tree[i][j] != compressed_tree[0][j]){
				printf("Error\n");
			}
		}
	}
	data.compressed_tree = compressed_tree;
	data.compress_vector = compress_vector;
	
	return data;	
}


histogram_SNARK_data_streaming_forest get_histograms_transcript_streaming_forest(Dataset &D,  vector<vector<vector<Node>>> forest){
	histogram_SNARK_data_streaming_forest transcript;
	// Histograms :  Partitions x Attributes x [class * |C|]
	vector<F> random_vector = generate_randomness(8,F(0));
	transcript.histograms_counter.name = "histogram_counter";
	transcript.histograms_counter.pos = 0;
	transcript.histograms_counter.row_size =forest.size()*D.data[0].size()*D.data.size();
	transcript.histograms_counter.col_size = 1;
	transcript.histograms_counter.size = forest.size()*D.data[0].size()*D.data.size();
	
	
	transcript.read_transcript.name = "read_transcript";
	transcript.read_transcript.pos = 0;
	transcript.read_transcript.row_size = forest.size()*D.data[0].size()*D.data.size();
	transcript.read_transcript.col_size = 8;
	transcript.read_transcript.size = transcript.read_transcript.col_size*transcript.read_transcript.row_size;
	
	
	transcript.write_transcript.name = "write_transcript";
	transcript.write_transcript.pos = 0;
	transcript.write_transcript.row_size = forest.size()*D.data[0].size()*D.data.size();
	transcript.write_transcript.col_size = 8;
	transcript.write_transcript.size = transcript.write_transcript.col_size*transcript.write_transcript.row_size;
	
	transcript.read_write_transcript.name = "read_write_transcript";
	transcript.read_write_transcript.pos = 0;
	transcript.read_write_transcript.row_size = 2*forest.size()*D.data[0].size()*D.data.size();
	transcript.read_write_transcript.col_size = 8;
	transcript.read_write_transcript.size = transcript.read_write_transcript.col_size*transcript.read_write_transcript.row_size;
	
	transcript.input_aux.name = "input_aux";
	transcript.input_aux.pos = 0;
	transcript.input_aux.row_size = forest.size()*D.data[0].size();
	transcript.input_aux.col_size = 2;
	transcript.input_aux.size = transcript.input_aux.col_size*transcript.input_aux.row_size;
	
	transcript.compressed_final.name = "compressed_final_hist";
	transcript.compressed_final.pos = 0;
	transcript.compressed_final.row_size = forest.size()*forest[0].size()*D.data.size()*2*bin_size;
	if(1ULL<<((int)log2(transcript.compressed_final.row_size)) != transcript.compressed_final.row_size){
		transcript.compressed_final.row_size = 1ULL<<((int)log2(transcript.compressed_final.row_size)+1);
	}
	transcript.compressed_final.col_size = 1;
	transcript.compressed_final.size = transcript.compressed_final.col_size*transcript.compressed_final.row_size;
	transcript.compressed_final.compress_vector = random_vector;

	
	transcript.random_vector = random_vector;
	
	return transcript;
}



nodes_histogram_data_streaming get_node_histograms_transcript_forest_stream( vector<vector<vector<int>>> leaf_index_matrix, vector<vector<vector<int>>> leaf_matrix,
	int attr,vector<vector<vector<F>>> _leaf_coeff,int trees,int leaves){
	
	nodes_histogram_data_streaming data;
	data.leaf_histograms.name = "final_hist";data.leaf_histograms.pos = 0;data.leaf_histograms.size = trees*leaves*2*attr*bin_size;
	data.node_histograms.name = "node_hist";data.node_histograms.pos = 0;data.node_histograms.size = trees*(leaves-1)*2*attr*bin_size;
	data.witness_hist.name = "witness_hist";data.witness_hist.pos = 0;data.witness_hist.size = trees*(leaves-1)*4*attr*bin_size;
	data.out_hist.name = "out_hist";data.out_hist.pos = 0;data.out_hist.size = trees*(leaves-1)*2*attr*bin_size;


	if(1ULL<<((int)log2(data.node_histograms.size)) != data.node_histograms.size)data.node_histograms.size = 1ULL<<((int)log2(data.node_histograms.size)+1); 
	if(1ULL<<((int)log2(data.leaf_histograms.size)) != data.leaf_histograms.size)data.leaf_histograms.size = 1ULL<<((int)log2(data.leaf_histograms.size)+1); 
	if(1ULL<<((int)log2(data.out_hist.size)) != data.out_hist.size)data.out_hist.size = 1ULL<<((int)log2(data.out_hist.size)+1); 
	if(1ULL<<((int)log2(data.witness_hist.size)) != data.witness_hist.size)data.witness_hist.size = 1ULL<<((int)log2(data.witness_hist.size)+1); 

	vector<vector<F>> node_coeff(trees);
	vector<vector<F>> leaf_coeff(trees);
	
	printf("\n======= Node Histograms Proof =======\n");
	
	
	for(int i = 0; i < _leaf_coeff.size(); i++){
		for(int j = 0; j < _leaf_coeff[i].size(); j++){
			for(int k = 0; k <  _leaf_coeff[i][j].size(); k++){
				leaf_coeff[i].push_back(_leaf_coeff[i][j][k]);
			}
		}
	}
	vector<vector<vector<int>>> node_index_matrix(leaf_index_matrix.size());
	for(int i = 0; i < node_index_matrix.size(); i++){
		node_index_matrix[i].resize(leaf_index_matrix[i].size());
		for(int j = 0; j < node_index_matrix[i].size(); j++){
			node_index_matrix[i][j].resize(leaf_index_matrix[i][j].size(),-1);
		}
	}
	for(int k = 0; k < leaf_matrix.size(); k++){
		for(int i = leaf_matrix[k].size()-1; i > 0; i--){
			for(int j = 0; j < leaf_matrix[k][i].size(); j+=2){
				if(leaf_matrix[k][i][j] != -1){
					vector<int> temp_coeff;
					node_coeff[k].push_back(F(i-1));
					node_coeff[k].push_back(F(j/2));
					leaf_matrix[k][i-1][j/2] = 1;
					
					node_index_matrix[k][i-1][j/2] = node_coeff[k].size()/2-1; 
				}
			}
		}
	}
	data.node_index_matrix = node_index_matrix;
	data.leaf_index_matrix = leaf_index_matrix;

	data.leaf_matrix = leaf_matrix;
	data.node_coeff = node_coeff;
	data.leaf_coeff = leaf_coeff;
	return data;

}

split_SNARK_streaming_forest get_split_transcript_streaming_forest( int trees, int nodes, int _attr ){
	split_SNARK_streaming_forest data;
	//int nodes = node_histograms.size()/trees;
	//printf("%d,%d\n",nodes,trees);
	attr = _attr;
	
	vector<vector<vector<unsigned long long int>>> sums(trees*nodes);
	best_gini.resize(trees*nodes);

	for(int i = 0; i < trees*nodes; i++){
		best_gini[i].resize(attr);
	}
	/*
	for(int l = 0; l < trees; l++){
		for(int i = 0; i < nodes; i++){
			sums[l*nodes + i].resize(attr);
			
			for(int j = 0; j < attr; j++){
				sums[l*nodes + i][j].resize(2,0);
				for(int k = 0; k < node_histograms[l*nodes + i][j].size(); k+=2){
					sums[l*nodes + i][j][0] += node_histograms[l*nodes + i][j][k];
					sums[l*nodes + i][j][1] += node_histograms[l*nodes + i][j][k+1];
				}
			}
		}
	}*/
	
	/*
	gini_input.resize(trees*nodes*attr*4*bin_size);
	for(int l = 0; l < trees; l++){
		for(int i = 0; i < nodes; i++){
			//gini_inputs[l*nodes + i].resize(attr);
			for(int j = 0; j < attr; j++){
				//gini_inputs[l*nodes + i][j].resize(4*(bin_size));
				gini_input[l*nodes*attr*4*bin_size + i*attr*4*bin_size + j*4*bin_size] = node_histograms[l*nodes + i][j][0];
				gini_input[l*nodes*attr*4*bin_size + i*attr*4*bin_size + j*4*bin_size+1] = node_histograms[l*nodes + i][j][1];
				gini_input[l*nodes*attr*4*bin_size + i*attr*4*bin_size + j*4*bin_size+2] = sums[l*nodes + i][j][0] - node_histograms[l*nodes + i][j][0];
				gini_input[l*nodes*attr*4*bin_size + i*attr*4*bin_size + j*4*bin_size+3] = sums[l*nodes + i][j][1] - node_histograms[l*nodes + i][j][1];
				for(int k = 1; k < bin_size; k++){
					gini_input[l*nodes*attr*4*bin_size + i*attr*4*bin_size + j*4*bin_size+2*k] = node_histograms[l*nodes + i][j][0];
					gini_input[l*nodes*attr*4*bin_size + i*attr*4*bin_size + j*4*bin_size+1+2*k+1] = node_histograms[l*nodes + i][j][1];
					gini_input[l*nodes*attr*4*bin_size + i*attr*4*bin_size + j*4*bin_size+2+2*k+2] = sums[l*nodes + i][j][0] - node_histograms[l*nodes + i][j][0];
					gini_input[l*nodes*attr*4*bin_size + i*attr*4*bin_size + j*4*bin_size+3+2*k+3] = sums[l*nodes + i][j][1] - node_histograms[l*nodes + i][j][1];
					
				}
			}
		}
	}
	
	int size = gini_input.size();
	printf("Initial size : %d\n",size/4);
	if(1ULL<<((int)log2(size)) != size){
		size = 1ULL<<((int)log2(size)+1);
	}
	gini_input.resize(size,0);
*/
	
	int size = trees*nodes*attr*4*bin_size;
	if(1ULL<<((int)log2(size)) != size){
		size = 1ULL<<((int)log2(size)+1);
	}
	data.N.name = "N";data.N.pos = 0;data.N.size = size/2;
	data.divisors.name = "divisors";data.divisors.pos = 0;data.divisors.size = size/2;
	data.dividents.name = "dividents";data.dividents.pos = 0;data.dividents.size = size/2;
	data.quotients.name = "quotients";data.quotients.pos = 0;data.quotients.size = size/2;
	data.remainders.name = "remainders";data.remainders.pos = 0;data.remainders.size = size/2;
	data.inverses.name = "inverses";data.inverses.pos = 0;data.inverses.size = size/2;
	data.gini_inputs.name = "gini_input"; data.gini_inputs.pos = 0;data.gini_inputs.size = size; 
	data.ginis.name = "ginis";data.ginis.pos = 0;data.ginis.size = size/4;
	data.sums = sums;
	total_nodes = best_gini.size();
	attr = best_gini[0].size();
	
	vector<F> buff(bin_size);
	for(int i = 0; i < trees*nodes; i++){
		for(int j = 0; j < attr; j++){
			float min = 100.0;
			read_stream(data.ginis,buff,buff.size());
			for(int k = 0; k < bin_size; k++){
				float n = dequantize(buff[k],1);
				if(min - n > 0){
					min = n;
					best_gini[i][j] = buff[k].getInt64();
				}
			}
		}
	}
	
	
	data.sums = sums;
	
	
	data.ginis.pos = 0;
	return data;
}



// Process for proving bagging:
// Take as input the table of binomial distribution : T (p1,0),(p2,1),...,(p16,16)
// If we have N data instance and T trees, generate TN uniformly random points 
// For the i-th instance and j-th tree, and v_{ij} the randomly generated value, 
// select k s.t p_{k-1} < v_{ij} < p_{k} 
streaming_bagging_SNARK get_split_transcript_streaming_forest(int dataset_size, int trees ){
	std::random_device rd;
    std::mt19937 gen(rd());
	streaming_bagging_SNARK data;
	data.randomness.name = "randomness";data.randomness.size =dataset_size*trees;data.randomness.pos = 0;
	data.randomness_quotient.name = "randomness_quotient";data.randomness_quotient.size = dataset_size*trees;data.randomness_quotient.pos = 0;
	data.randomness_remainder.name = "randomness_remainder";data.randomness_remainder.size = dataset_size*trees;data.randomness_remainder.pos = 0;
	data.pairs.name = "pairs";data.pairs.size = 2*dataset_size*trees;data.pairs.pos = 0;
	data.compressed_pairs.name = "compressed_pairs";data.compressed_pairs.size =dataset_size*trees;data.compressed_pairs.pos = 0;
	data.s1.name = "s1";data.s1.size = dataset_size*trees;data.s1.pos = 0;
	data.s2.name = "s2";data.s2.size = dataset_size*trees;data.s2.pos = 0;
	
	data.compressed_pairs.compress_vector = generate_randomness(3,F(32));
	data.s1.compress_vector = generate_randomness(2,F(32));
	data.s2.compress_vector = data.s1.compress_vector;
	seed.setByCSPRNG();
	A_.setByCSPRNG();
	B_.setByCSPRNG();

	discrete_table.resize(1ULL<<16);
	
	
	std::binomial_distribution<> d(dataset_size, 1.0/(double)dataset_size);

	for(int i = 0; i < discrete_table.size(); i++){
		int count = 0;
		discrete_table[i] = d(gen);
	}
	
	data.powers.resize(1<<16,F_ZERO);
	get_powers(data.powers,dataset_size,trees);
	data.power_bits = prepare_bit_vector(data.powers,32);
	return data;
}