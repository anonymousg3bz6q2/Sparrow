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
#include "BuildTree_streaming.h"
#include "space_efficient_sumcheck.h"
#include "utils.hpp"
#include "Poly_Commit.h"

extern int bin_size;

extern size_t MAX_CHUNCK;
extern double proving_time;
extern double read_time;
extern double clear_cache_time;
extern double stream_access_time;
extern double inference_time;
extern double verification_time;
extern int proof_len;
extern MIPP_Comm pp;
extern vector<G1> input_commit;
extern float total_p,total_v,total_s; 
	
extern int _commitment_test;

void commit_partitions(partition_SNARK_data_streaming data, vector<vector<F>> tree, vector<vector<G1>> &commitments){
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
	for(int i = 0; i < tree.size(); i++){
		forest_poly.insert(forest_poly.end(),tree[i].begin(),tree[i].end());
	}

	MIPP_commit(forest_poly,pp,C);
	commitments.push_back(C);
	MIPP_commit(data.power_bits,pp,C);
	commitments.push_back(C);
	

}

void open_partitions(partition_SNARK_data_streaming data,vector<vector<F>> tree , vector<vector<G1>> commitments){
	
	MIPP_open_stream(data.permuted_data,data.permuted_data.size,generate_randomness((int)log2(data.permuted_data.size),F(321)),pp,commitments[0]);
	MIPP_open_stream(data.input_data,data.input_data.size,generate_randomness((int)log2(data.input_data.size),F(321)),pp,commitments[1]);
	MIPP_open_stream(data.paths,data.paths.size,generate_randomness((int)log2(data.paths.size),F(321)),pp,commitments[2]);
	MIPP_open_stream(data.paths_aux,data.paths_aux.size,generate_randomness((int)log2(data.paths_aux.size),F(321)),pp,commitments[3]);
	MIPP_open_stream(data.diff_data,data.diff_data.size,generate_randomness((int)log2(data.diff_data.size),F(321)),pp,commitments[4]);
	MIPP_open_stream(data.bit_vectors,data.bit_vectors.size,generate_randomness((int)log2(data.bit_vectors.size),F(321)),pp,commitments[5]);
	
	vector<F> forest_poly;
	for(int i = 0; i < tree.size(); i++){
		forest_poly.insert(forest_poly.end(),tree[i].begin(),tree[i].end());
	}
	
	MIPP_open(forest_poly,generate_randomness((int)log2(forest_poly.size()),F(321)),pp,commitments[6]);
	vector<F> bits = data.power_bits;
	
	MIPP_open(bits,generate_randomness((int)log2(bits.size()),F(321)),pp,commitments[7]);
	printf("P : %lf, V : %lf, L : %lf\n",pp.prove_time,pp.verification_time,(double)pp.proof_size/1024.0);
	total_p += pp.prove_time;
	total_v += pp.verification_time;
	total_s += (double)pp.proof_size/1024.0;

	pp.prove_time = 0.0;
	pp.verification_time = 0.0;
	pp.proof_size =0;
}




void commit_histograms_leaves(histogram_SNARK_data_streaming data , vector<vector<G1>> &commitments){
	vector<G1> C;
	
	//MIPP_commit_stream(data.read_transcript,data.read_transcript.size,pp,C);
	MIPP_commit_stream(data.histograms_counter,data.histograms_counter.size,pp,C);
	commitments.push_back(C);
	//MIPP_commit_stream(data.write_transcript,data.write_transcript.size,pp,C);
	//commitments.push_back(C);

	// commit final histograms
	vector<F> hist_poly;
	for(int i = 0; i < data.final_memory.size(); i++){
		hist_poly.insert(hist_poly.end(), data.final_memory[i].begin(),data.final_memory[i].end());
	}
	MIPP_commit(hist_poly,pp,C);
	commitments.push_back(C);
	hist_poly.clear();
}

void open_histograms_leaves(histogram_SNARK_data_streaming data , vector<vector<G1>> &commitments){
	vector<G1> C;
	
	MIPP_open_stream(data.input_data,data.input_data.size,generate_randomness((int)log2(data.input_data.size),F(321)),pp,input_commit);
	
	MIPP_open_stream(data.histograms_counter,data.histograms_counter.size,generate_randomness((int)log2(data.histograms_counter.size),F(321)),pp,commitments[0]);
	//MIPP_open_stream(data.read_transcript,data.read_transcript.size,generate_randomness((int)log2(data.read_transcript.size),F(321)),pp,commitments[0]);
	//MIPP_open_stream(data.write_transcript,data.write_transcript.size,generate_randomness((int)log2(data.write_transcript.size),F(321)),pp,commitments[0]);
	
	vector<F> hist_poly;
	for(int i = 0; i < data.final_memory.size(); i++){
		hist_poly.insert(hist_poly.end(), data.final_memory[i].begin(),data.final_memory[i].end());
	}
	pad_vector(hist_poly);
	MIPP_open(hist_poly,generate_randomness((int)log2(hist_poly.size()),F(321)),pp,commitments[1]);

	total_p += pp.prove_time;
	total_v += pp.verification_time;
	total_s += (double)pp.proof_size/1024.0;

	hist_poly.clear();
	
}


void prove_correct_histograms_streaming(histogram_SNARK_data_streaming data, int Attr, F previous_r){
	printf("OK\n");
	if(_commitment_test){
		vector<vector<G1>> commitments;
		commit_histograms_leaves(data,commitments);
		open_histograms_leaves(data,commitments);
		return;
	}	
	streaming_sumcheck_leaves_1( data, Attr, previous_r);
	streaming_sumcheck_leaves_2( data, Attr, previous_r);
	printf("TOTAL PROVE TIME PHASE 2 : %lf , %lf ,%lf\n",proving_time,stream_access_time,inference_time);
	printf("TOTAL VERIFICATION TIME PHASE 2 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	
	//verification_time = 0.0;
	//proof_len = 0;
	//proving_time = 0.0;
	//stream_access_time = 0.0;
	//clear_cache_time = 0.0;
	//read_time = 0.0;
}



void prove_correct_partitions_streaming(partition_SNARK_data_streaming data, Dataset &D, vector<vector<F>> Tree,int max_depth){

	if(_commitment_test){
		vector<vector<G1>> commitments;
		commit_partitions(data,Tree,commitments);
		open_partitions(data,Tree,commitments);
		return;
		
	}
	streaming_sumcheck_partition_1(data);
	printf("sumcheck 1 finished\n");
	streaming_sumcheck_partition_2(data, Tree);
	printf("sumcheck 2 finished\n");
	streaming_sumcheck_partition_3(data, Tree);
	printf("TOTAL PROVE TIME PHASE 1 : %lf , %lf ,%lf\n",proving_time,stream_access_time,inference_time);
	printf("TOTAL VERIFICATION TIME PHASE 1 : %lf , %lf Kb\n",verification_time,(float)proof_len/1024.0);
	//verification_time = 0.0;
	//proof_len = 0;
	//proving_time = 0.0;
	//stream_access_time = 0.0;
	//clear_cache_time = 0.0;
	//read_time = 0.0;	
}




partition_SNARK_data_streaming get_partitions_transcript_streaming(Dataset D, vector<Dataset> Partitions, vector<vector<Node>> Tree,
 vector<vector<F>> tree, int max_depth, int write){
	partition_SNARK_data_streaming data;
	data.input_data.name = "input";data.input_data.pos = 0;
	data.input_data.col_size = D.data.size()*2;data.input_data.row_size = D.data[0].size();
	data.input_data.size = D.data[0].size()*D.data.size()*2;

	data.permuted_data.name = "permuted_input"; data.permuted_data.pos = 0;
	data.permuted_data.col_size = D.data.size()*2;data.permuted_data.row_size = D.data[0].size(); 
	data.permuted_data.size = D.data[0].size()*D.data.size()*2;

	data.paths.name = "path";data.paths.pos =0;
	data.paths.row_size = D.data[0].size();
	data.paths.col_size =  normalize_number(4*max_depth);
	data.paths.size = data.paths.row_size*data.paths.col_size;

	data.bit_vectors.name = "bit_vector";data.bit_vectors.pos = 0;
	int q = ((int)log2(bin_size));
	if(1 << ((int)log2(q)) != q){
		q = 1 << ((int)log2(q)+1);
	}
	data.bit_vectors.size = normalize_number((size_t)max_depth*(size_t)D.data[0].size()*(size_t)q);
	

	data.diff_data.name = "diff"; data.diff_data.pos = 0;
	data.diff_data.size = normalize_number((size_t)max_depth*(size_t)D.data[0].size());
	
	data.input_aux.name = "input_aux";data.input_aux.pos = 0;
	data.input_aux.size = 2*D.data[0].size();
	data.input_aux.col_size = 2;data.input_aux.row_size = D.data[0].size();

	data.paths_aux.name = "path_aux"; data.paths_aux.pos = 0;
	data.paths_aux.size = 2*D.data[0].size();
	data.paths_aux.col_size = 2;data.paths_aux.row_size = D.data[0].size();

	
	F commitment = F(0);
	vector<F> compress_vector = generate_randomness(3,F(0));
	//P.compress_vector = compress_vector;
	vector<F> tree_compress_vector = generate_randomness(data.paths.col_size+2,compress_vector[2]);
	vector<F> compressed_tree(tree.size());
	data.tree_compress_vector = tree_compress_vector;
	
	for(int i = 0; i < tree.size(); i++){
		int j = 0;
		for(j = 0; j < tree[i].size()-2; j++){
			compressed_tree[i] += tree[i][j]*tree_compress_vector[j];
		}
		compressed_tree[i] += F(1);
		compressed_tree[i] += tree[i][j]*tree_compress_vector[data.paths.col_size] + tree[i][j+1]*tree_compress_vector[data.paths.col_size+1];
	}
	data.compressed_tree = compressed_tree;
	data.compress_vector = compress_vector;
	
	for(int i = 0; i < Partitions.size(); i++){
		data.powers.push_back(F(Partitions[i].indexes.size()));
		data.int_pows.push_back(Partitions[i].indexes.size());
	}
	data.power_bits = prepare_bit_vector(data.powers,32);
	pad_vector(data.power_bits);
	
	return data;
}




histogram_SNARK_data_streaming get_histograms_transcript_streaming(Dataset &D, vector<int> data_partitions, vector<int> label, vector<vector<Node>> Tree, int Attr, int write){
	histogram_SNARK_data_streaming transcript;
	// Histograms :  Partitions x Attributes x [class * |C|]
	transcript.histograms_counter.name = "histogram_counter";
	transcript.histograms_counter.pos = 0;
	transcript.histograms_counter.row_size =D.data[0].size()*D.data.size();
	transcript.histograms_counter.col_size = 1;
	transcript.histograms_counter.size = D.data[0].size()*D.data.size();
	
	
	transcript.read_transcript.name = "read_transcript";
	transcript.read_transcript.pos = 0;
	transcript.read_transcript.row_size = D.data[0].size()*D.data.size();
	transcript.read_transcript.col_size = 8;
	transcript.read_transcript.size = transcript.read_transcript.col_size*transcript.read_transcript.row_size;
	
	
	transcript.write_transcript.name = "write_transcript";
	transcript.write_transcript.pos = 0;
	transcript.write_transcript.row_size = D.data[0].size()*D.data.size();
	transcript.write_transcript.col_size = 8;
	transcript.write_transcript.size = transcript.write_transcript.col_size*transcript.write_transcript.row_size;
	
	transcript.read_write_transcript.name = "read_write_transcript";
	transcript.read_write_transcript.pos = 0;
	transcript.read_write_transcript.row_size = 2*D.data[0].size()*D.data.size();
	transcript.read_write_transcript.col_size = 8;
	transcript.read_write_transcript.size = transcript.read_write_transcript.col_size*transcript.read_write_transcript.row_size;
	

	vector<vector<F>> memory_init(Tree.size()*D.data.size()*2*bin_size);
	transcript.final_memory.resize(Tree.size()*D.data.size()*2*bin_size);
	for(int i = 0; i < memory_init.size(); i++){
		memory_init[i].resize(8,F_ZERO);
		transcript.final_memory[i].resize(8,F_ZERO);
	}
	for(int i = 0; i < Tree.size(); i++){
		for(int j = 0; j < D.data.size(); j++){
			for(int k = 0; k < bin_size; k++){
				
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][0] = F(i);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][1] = F(j);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][2] = F(k);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][3] = F(0);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][4] = F(0);

				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][0] = F(i);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][1] = F(j);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][2] = F(k);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][3] = F(1);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][4] = F(0);

			}
		}
	}
	transcript.memory_init = memory_init;
	
	get_final_hist(transcript.final_memory);

	//transcript.final_memory = final_memory;
	
	vector<F> random_vector = generate_randomness(8,F(0));
	vector<F> compressed_final(transcript.memory_init.size(),F(0)),compressed_init(transcript.memory_init.size(),F(0));
	for(int i = 0; i < transcript.memory_init.size(); i++){
		for(int j = 0; j < 5; j++){
			compressed_init[i] += transcript.memory_init[i][j]*random_vector[j];
			compressed_final[i] += transcript.final_memory[i][j]*random_vector[j];
		}
		compressed_init[i]+= F(1);
		compressed_final[i]+= F(1);
		
	}
	transcript.random_vector = random_vector;
	transcript.compressed_init = compressed_init;
	transcript.compressed_final = compressed_final;
	
	return transcript;
}

