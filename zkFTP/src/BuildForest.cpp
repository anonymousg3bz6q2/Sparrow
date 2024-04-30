#include "BuildForest.h"
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
#include "BuildTree.h"
#include "pol_verifier.h"

#define NUMERICAL 1 
#define CATEGORICAL 2
using namespace chrono;

extern int bin_size;

extern int _commitment_test;

extern MIPP_Comm pp;
extern float total_p,total_v,total_s;



histogram_SNARK_proof prove_histograms_forest(histogram_SNARK_data_forest &data, int Attr, int forest_size, F previous_r){
	histogram_SNARK_proof P;
	// Under development
	F commitments;commitments.setByCSPRNG();
	P.commitments = commitments;
	P.previous_r = previous_r;
	F rand = mimc_hash(previous_r,commitments);
	clock_t t1,t2;
	t1 = clock();
	
	
	vector<F> random_vector = generate_randomness(8,rand);
	previous_r = random_vector[random_vector.size()-1];
	vector<F> compressed_final(forest_size*data.memory_init[0].size(),F(1)),compressed_init(forest_size*data.memory_init[0].size(),F(1));
	vector<F> compressed_write(forest_size*data.write_transcript[0].size(),F(1));
	vector<F> compressed_read(forest_size*data.write_transcript[0].size(),F(1));
	vector<F> read_data,write_data,input_data,input_metadata;

	
	for(int k = 0; k < forest_size; k++){
		for(int i = 0; i < data.memory_init[k].size(); i++){
			for(int j = 0; j < 5; j++){
				compressed_init[data.memory_init[k].size()*k + i] += data.memory_init[k][i][j]*random_vector[j];
				compressed_final[data.memory_init[k].size()*k +i] += data.final_memory[k][i][j]*random_vector[j];
			}
			
		}

		for(int i = 0; i < data.read_transcript[k].size(); i++){
			for(int j = 0; j < 5; j++){
				compressed_write[data.read_transcript[k].size()*k + i] += random_vector[j]*data.write_transcript[k][i][j];
				compressed_read[data.read_transcript[k].size()*k + i] += random_vector[j]*data.read_transcript[k][i][j];
			}
		}
	}

	
	P.mP1 = leaves_sumcheck_1(compressed_read,compressed_write,previous_r);
	vector<F>().swap(compressed_read);
	vector<F>().swap(compressed_write);
	
	vector<vector<F>> padded_read_transcript;
	vector<vector<F>> padded_write_transcript;
	vector<vector<F>> padded_histograms;
	
	

	
	pad_vector(random_vector);

	if((F(1)-P.mP1.global_randomness[0])*P.mP1.partial_eval[0] + P.mP1.global_randomness[0]*P.mP1.partial_eval[1] != P.mP1.final_eval){
		printf("Error\n");
		exit(-1);
	}

	rand = mimc_hash(P.mP1.individual_randomness[P.mP1.individual_randomness.size()-1],P.mP1.partial_eval[0]);
	rand = mimc_hash(rand,P.mP1.partial_eval[1]);

	for(int k = 0; k < forest_size; k++){
		for(int i = 0; i < data.read_transcript[k].size(); i++){
			padded_read_transcript.push_back(data.read_transcript[k][i]);
		}
	}
	P.sP1 = _prove_matrix2vector(_transpose(padded_read_transcript),random_vector,P.mP1.individual_randomness,P.mP1.partial_eval[0]-F(1),rand);
	pad_matrix(padded_read_transcript);
	for(int i = 0; i < padded_read_transcript.size(); i++){
		vector<F>().swap(padded_read_transcript[i]);
	}
	vector<vector<F>>().swap(padded_read_transcript);
	padded_read_transcript.clear();

	for(int k = 0; k < forest_size; k++){
		for(int i = 0; i < data.write_transcript[k].size(); i++){
			padded_write_transcript.push_back(data.write_transcript[k][i]);
		}
	}
	pad_matrix(padded_write_transcript);
	P.sP2 = _prove_matrix2vector(_transpose(padded_write_transcript),random_vector,P.mP1.individual_randomness,P.mP1.partial_eval[1]-F(1),P.sP1.final_rand);
	
	for(int i = 0; i < padded_write_transcript.size(); i++){
		vector<F>().swap(padded_write_transcript[i]);
	}
	vector<vector<F>>().swap(padded_write_transcript);
	
	pad_vector_with_num(compressed_init,F(1));pad_vector_with_num(compressed_final,F(1));
	
	
	P.mP2 = leaves_sumcheck_1(compressed_init,compressed_final,P.sP2.final_rand);
	if(P.mP1.output[0]*P.mP2.output[1] != P.mP2.output[0]*P.mP1.output[1]){
		printf("Error in histogram proof 1\n");
		exit(-1);
	}
	
	rand = mimc_hash(P.mP2.final_r[P.mP2.final_r.size()-1],P.mP2.partial_eval[1]);
	for(int k = 0; k < forest_size; k++){
		for(int i = 0; i < data.final_memory[k].size(); i++){
			padded_histograms.push_back(data.final_memory[k][i]);
		}
	}
	pad_matrix(padded_histograms);
	P.sP3 = _prove_matrix2vector(_transpose(padded_histograms),random_vector,P.mP2.individual_randomness,P.mP2.partial_eval[1]-F(1),rand);	



	
	vector<F> r1,r2,beta1,beta2;

	r1 = P.sP1.randomness[0];
	for(int i = 0; i < P.mP1.individual_randomness.size(); i++){
		r1.push_back(P.mP1.individual_randomness[i]);
	}

	r2 = P.sP2.randomness[0];
	for(int i = 0; i < P.mP1.individual_randomness.size(); i++){
		r2.push_back(P.mP1.individual_randomness[i]);
	}

	//precompute_beta(r1,beta1);
	//precompute_beta(r2,beta2);

	
	vector<F> idx(forest_size*data.input_data.size()),labels(data.input_data.size()),partitions(forest_size*data.input_data.size());
	for(int i = 0; i < partitions.size(); i++){
		partitions[i] = F(data.data_partitions[i]);
	}
	for(int i = 0; i < labels.size(); i++){
		labels[i] = F(data.label[i]);
	}
	int counter = 0;
	for(int i = 0; i < data.idx_matrix.size(); i++){
		for(int j = 0; j < data.idx_matrix[i].size(); j++){
			idx[counter] = data.idx_matrix[i][j];
			counter++;
		}
	}
	for(int k = 0; k < forest_size; k++){
		for(int i = 0; i < data.read_transcript[k].size(); i++){
			read_data.insert(read_data.end(),data.read_transcript[k][i].begin(),data.read_transcript[k][i].end());
		}

		for(int i = 0; i < data.write_transcript[k].size(); i++){
			write_data.insert(write_data.end(),data.write_transcript[k][i].begin(),data.write_transcript[k][i].end());		
		}
	}
	for(int i = 0; i < data.read_transcript.size(); i++){
		for(int j = 0; j < data.read_transcript[i].size(); j++){
			vector<F>().swap(data.read_transcript[i][j]);
			vector<F>().swap(data.write_transcript[i][j]);
		}
		vector<vector<F>>().swap(data.read_transcript[i]);
		vector<vector<F>>().swap(data.write_transcript[i]);
	}
	vector<vector<vector<F>>>().swap(data.read_transcript);
	vector<vector<vector<F>>>().swap(data.write_transcript);
	
	
	
	P.P1 = forest_leaves_sumcheck_2(convert2vector(data.input_data),idx,partitions,labels,read_data,write_data,r2,beta1,beta2,P.sP1.vr[0],P.sP2.vr[0],forest_size,P.sP3.final_rand);
	
	
	P.final_rand = P.P1.final_rand;
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	return P;

}




// Assume the following vetors: [inputs],[permuted_inputs],[individual paths],[paths],[frequency],[bits]
// We need two permutation checks: 1) Between [inputs] and [permuted_inputs]/ 2) [individual paths],[paths],[frequency]
// Apply inference proof using [permuted_inputs],[individual paths],[bits]
// Check path consistency : The difference between the previous and the current pos of [individual paths] will be >=0 

partition_SNARK_proof prove_correct_partitions_forest(partition_SNARK_data_forest &data, Dataset &D, vector<vector<vector<F>>> forest,int max_depth){
	partition_SNARK_proof P;
	vector<F> randomness = generate_randomness(10,F(0));
	
	// Permutation checks 
	// Use Matrix-vector multiplication to compress dataset and individual paths
	clock_t t1,t2;
	t1 = clock();
	
	pad_matrix(data.input_data);
	
	F commitment;commitment.setByCSPRNG();
	P.commitment = commitment;
	vector<F> compress_vector = generate_randomness(D.data.size()+1,commitment);
	P.compress_vector = compress_vector;
	vector<F> tree_compress_vector = generate_randomness(4*max_depth+2,compress_vector[compress_vector.size()-1]);
	P.tree_compress_vector = tree_compress_vector;
	F c = mimc_hash(tree_compress_vector[tree_compress_vector.size()-1],F(1));
	int dataset_size = D.label.size();
	int forest_size = forest.size();
	
	//pad_vector_with_num(compressed_paths,F(1));
	//pad_vector_with_num(compressed_tree,F(1));

	vector<F> gkr_data;
	
	
	pad_vector(compress_vector);
	
	
	//P.P1 = partition_sumcheck_1(data.input_data,data.permuted_data,compress_vector,c,c);
	P.P1 = forest_partition_sumcheck_1( data.input_data, data.permuted_data, compress_vector, forest.size() , c, c);

	

	
	//P.P2 = partition_sumcheck_2(compressed_tree, compressed_paths, powers, data.power_bits, paths, tree, tree_compress_vector,c,P.P1.final_rand);
	P.P2 = forest_partition_sumcheck_2( data.power_bits, data.paths, data.paths_aux, forest, tree_compress_vector, D.label.size() , c, P.P1.final_rand);

	
	vector<vector<F>> paths(dataset_size*forest_size);
	for(int i = 0; i < dataset_size; i++){
		for(int j = 0; j < forest_size; j++){
			paths[i*forest_size + j].resize(4*max_depth);
			for(int k = 0; k <  paths[i*forest_size + j].size(); k++){
				paths[i*forest_size + j][k] = data.paths[j*dataset_size + i][k];
			}
		}
	}
	
	forest_partition_sumcheck_3(paths, data.permuted_data,  data.diff_data, data.bit_vectors, P.P2.final_rand, forest.size(), D.label.size() , max_depth);
	
	//P.P3 = partition_sumcheck_3(data.paths, data.permuted_data, data.diff_data,data.bit_vectors,P.P2.final_rand,max_depth);
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;

	return P;
}


// Partitions : the path of each tree the instance belongs to
// idx_matrix : the a data point is present to a bagged dataset
void get_histograms_forest(histogram_SNARK_data_forest &transcript ,Dataset &D, vector<int> data_partitions, vector<vector<int>> idx_matrix, vector<int> label, vector<vector<vector<F>>> forest, int Attr){
	// Histograms :  Partitions x Attributes x [class * |C|]
	transcript.read_transcript.resize(forest.size());
	transcript.write_transcript.resize(forest.size());
	//vector<vector<vector<F>>> read_transcript(forest.size()),write_transcript(forest.size());
	transcript.memory_init.resize(forest.size());
	//vector<vector<vector<F>>> memory_init(forest.size());
	//vector<vector<vector<F>>> final_memory(forest.size());
	printf("\n======= Leaves Histograms Proof =======\n");
	transcript.final_memory.resize(forest.size());
	
	vector<vector<vector<vector<vector<F>>>>> histograms(forest.size());
	
	
	for(int l = 0; l < forest.size(); l++){
		transcript.memory_init[l].resize(forest[l].size()*D.data.size()*bin_size*2);
		for(int i = 0; i < forest[l].size(); i++){
			for(int j = 0; j < D.data.size(); j++){
				for(int k = 0; k < bin_size; k++){
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k].resize(8,F(0));
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1].resize(8,F(0));
					
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][0] = F(i);
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][1] = F(j);
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][2] = F(k);
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][3] = F(0);
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][4] = F(0);
	
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][0] = F(i);
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][1] = F(j);
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][2] = F(k);
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][3] = F(1);
					transcript.memory_init[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][4] = F(0);
	
				}
			}
		}
	}
	for(int l = 0; l < forest.size(); l++){
		histograms[l].resize(forest[l].size());
		for(int i = 0; i < histograms[l].size(); i++){
			histograms[l][i].resize(D.data.size());
			for(int j = 0; j < D.data.size(); j++){
				histograms[l][i][j].resize(2);
				for(int k = 0; k < 2; k++){
					histograms[l][i][j][k].resize(bin_size,F(0));

				}
			}
		}
	}

	
	for(int l = 0; l < forest.size(); l++){
		transcript.read_transcript[l].resize(Attr*D.data[0].size());
		transcript.write_transcript[l].resize(Attr*D.data[0].size());
		for(int i = 0; i < D.data[0].size(); i++){
			int partition = data_partitions[l + i*forest.size()];
			
			for(int j = 0; j < Attr; j++){
				transcript.read_transcript[l][i*Attr + j].resize(8,F(0));
				transcript.write_transcript[l][i*Attr + j].resize(8,F(0));
				transcript.read_transcript[l][i*Attr + j][0] = F(partition);
				transcript.read_transcript[l][i*Attr + j][1] = F(j);
				transcript.read_transcript[l][i*Attr + j][2] = F(D.data[j][i]);
				transcript.read_transcript[l][i*Attr + j][3] = label[i];
				transcript.read_transcript[l][i*Attr + j][4] = histograms[l][partition][j][label[i]][D.data[j][i]];
				transcript.write_transcript[l][i*Attr + j][0] = F(partition);
				transcript.write_transcript[l][i*Attr + j][1] = F(j);
				transcript.write_transcript[l][i*Attr + j][2] = F(D.data[j][i]);
				transcript.write_transcript[l][i*Attr + j][3] = label[i];
				transcript.write_transcript[l][i*Attr + j][4] = histograms[l][partition][j][label[i]][D.data[j][i]] + F(idx_matrix[l][i]);
				histograms[l][partition][j][label[i]][D.data[j][i]] += F(idx_matrix[l][i]);
			}
		}
	}
	for(int l = 1; l < forest.size(); l++){
		histograms[l].resize(forest[l].size());
		for(int i = 0; i < histograms[l].size(); i++){
			histograms[l][i].resize(D.data.size());
			for(int j = 0; j < D.data.size(); j++){
				histograms[l][i][j].resize(2);
				for(int k = 0; k < 2; k++){
					for(int z =0; z < bin_size; z++){
						if(histograms[0][i][j][k][z] != histograms[l][i][j][k][z]){
							printf("%d,%d,%d,%d,%d\n",l,i,j,k,z);
							exit(-1);
						}
					}
					
				}
			}
		}
	}

	for(int l = 0; l < forest.size(); l++){
		transcript.final_memory[l].resize(forest[l].size()*D.data.size()*2*bin_size);
		for(int i = 0; i < forest[l].size(); i++){
			for(int j = 0; j < D.data.size(); j++){
				for(int k = 0; k < bin_size; k++){
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k].resize(8,F(0));
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1].resize(8,F(0));
					
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][0] = F(i);
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][1] = F(j);
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][2] = F(k);
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][3] = F(0);
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][4] = histograms[l][i][j][0][k];
	
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][0] = F(i);
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][1] = F(j);
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][2] = F(k);
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][3] = F(1);
					transcript.final_memory[l][i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][4] = histograms[l][i][j][1][k];
				}
			}
		}
	}
	
	/*
	transcript.read_transcript = read_transcript;
	transcript.final_memory = final_memory;
	transcript.memory_init = memory_init;
	transcript.write_transcript = write_transcript;
	return transcript;
	*/
	transcript.idx_matrix = idx_matrix;
	
}




// WARNING : All tree tables need to have the same depth
void get_partitions_forest(partition_SNARK_data_forest &data,Dataset D, vector<vector<int>> Partitions, vector<vector<vector<Node>>> Trees){
	Tree_Inference_Data inference_data;
	//partition_SNARK_data_forest data;


	//vector<vector<F>> input_data;
	//vector<int> data_partitions;
	//vector<int> label;
	//vector<vector<F>> permuted_data;
	//vector<vector<F>> paths(D.data[0].size()*Trees.size()),paths_aux(D.data[0].size()*Trees.size());
	data.paths_aux.resize(D.data[0].size()*Trees.size());
	data.paths.resize(D.data[0].size()*Trees.size());
	
	//vector<vector<F>> bit_vectors;
	//vector<vector<F>> diff_data;
	vector<F> partitions;
	vector<F> path_diff;

	int check = 0;
	


	for(int i = 0; i < D.data[0].size(); i++){
		vector<int> x;
		int y;
		for(int k = 0; k < D.type.size(); k++){
			x.push_back(D.data[k][i]);
		}
		y = D.label[i];
		data.label.push_back(y);
		

		for(int j = 0; j < Trees.size(); j++){
			inference_data = Tree_Inference(Trees[j],x,y);
			
			if(j == 0){
				data.input_data.push_back(inference_data.input);
			}
	
			
			partitions.push_back(F(inference_data.pos));
			data.permuted_data.push_back(inference_data.permuted_input);
			data.paths[j*D.data[0].size() + i] = inference_data.path;
			data.paths_aux[j*D.data[0].size() + i] = inference_data.paths_aux;
			data.bit_vectors.push_back(inference_data.bit_vector);
			data.diff_data.push_back(inference_data.diff);	
			data.data_partitions.push_back(inference_data.pos);
		}
	}

	data.powers.resize(Partitions.size());
	data.int_pows.resize(Partitions.size());
	for(int i = 0; i < Partitions.size(); i++){
		for(int j = 0; j < Partitions[i].size(); j++){
			data.powers[i].push_back(F(Partitions[i][j]));
			data.int_pows[i].push_back(Partitions[i][j]);
		}
	}
	//pad_matrix(data.powers);
	data.power_bits.resize(Trees.size());
	for(int i = 0; i < Trees.size(); i++){
		data.power_bits[i] = prepare_bit_vector(data.powers[i],32);
	}
	
	pad_matrix(data.power_bits);

	
	pad_matrix(data.permuted_data);
	//data.input_data =input_data;

	//data.permuted_data = permuted_data;
	//data.paths = paths;
	pad_matrix(data.paths);
	//data.paths_aux = paths_aux;
	//data.bit_vectors = bit_vectors;
	//data.diff_data = diff_data;
	data.path_diff = path_diff;
	//data.data_partitions = data_partitions;
	//data.label = label;
	//return data;
}


vector<vector<F>> _padded_hist(vector<vector<vector<vector<F>>>> Hist){
	vector<vector<F>> matrix;
	for(int k = 0; k < Hist.size(); k++){
		for(int i = 0; i < Hist[k].size(); i++){
			vector<F> vec;
			for(int j = 0; j < Hist[k][i].size(); j++){
				vec.insert(vec.end(),Hist[k][i][j].begin(),Hist[k][i][j].end());
			}
			matrix.push_back(vec);
		}
	}
	
	pad_matrix(matrix);
	return _transpose(matrix);
}

void _compute_compressed_hist(vector<vector<F>> &compressed_hist, vector<vector<vector<vector<F>>>> Hist, vector<F> compress_vector){
	int counter;
	for(int l = 0; l < compressed_hist.size(); l++){
		for(int i = 0; i < compressed_hist[l].size(); i++){
			counter = 0;
			for(int j = 0; j < Hist[l][i].size(); j++){
				for(int k = 0; k < Hist[l][i][j].size(); k++){
					compressed_hist[l][i] += compress_vector[counter]*Hist[l][i][j][k];
					counter++;
				}
			}
		}	

	}
}

void commit_histograms_nodes_forest(nodes_histogram_SNARK_data_forest data, vector<vector<G1>> &commitments){
	vector<G1> C;
	vector<F> poly;
	for(int i = 0; i < data.node_histograms.size(); i++){
		for(int j = 0; j < data.node_histograms[i].size(); j++){
			for(int k = 0; k < data.node_histograms[i][j].size(); k++){
				poly.insert(poly.end(), data.node_histograms[i][j][k].begin(),data.node_histograms[i][j][k].end());

			}
		}
	}
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	//vector<vector<int>> node_index_matrix,leaf_index_matrix,leaf_matrix;
	poly.clear();

	for(int i = 0; i < data.node_index_matrix.size(); i++){
		for(int j = 0; j < data.node_index_matrix[i].size(); j++){
			for(int k = 0; k < data.node_index_matrix[i][j].size(); k++){
				poly.push_back(F(data.node_index_matrix[i][j][k]));
			}
		}
	}
	MIPP_commit(poly,pp,C);
	
	commitments.push_back(C);
	poly.clear();
	for(int i = 0; i < data.leaf_index_matrix.size(); i++){
		for(int j = 0; j < data.leaf_index_matrix[i].size(); j++){
			for(int k = 0; k < data.leaf_index_matrix[i][j].size(); k++){
				poly.push_back(F(data.leaf_index_matrix[i][j][k]));
			}
		}
	}
	MIPP_commit(poly,pp,C);
	
	commitments.push_back(C);
	poly.clear();
	for(int i = 0; i < data.leaf_matrix.size(); i++){
		for(int j = 0; j < data.leaf_matrix[i].size(); j++){
			for(int k = 0; k < data.leaf_matrix[i][j].size(); k++){
				poly.push_back(F(data.leaf_matrix[i][j][k]));
			}
		}
	}
	MIPP_commit(poly,pp,C);
	
	commitments.push_back(C);
	poly = convert2vector(data.node_coeff);
	
	
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	poly = convert2vector(data.leaf_coeff);
	
	
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	
}

void open_histograms_nodes_forest(nodes_histogram_SNARK_data_forest data, vector<vector<G1>> &commitments){
	vector<F> poly;
	for(int i = 0; i < data.node_histograms.size(); i++){
		for(int j = 0; j < data.node_histograms[i].size(); j++){
			for(int k = 0; k < data.node_histograms[i][j].size(); k++){
				poly.insert(poly.end(), data.node_histograms[i][j][k].begin(),data.node_histograms[i][j][k].end());

			}
		}
	}
	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[0]);
	
	//vector<vector<int>> node_index_matrix,leaf_index_matrix,leaf_matrix;
	poly.clear();
	for(int i = 0; i < data.node_index_matrix.size(); i++){
		for(int j = 0; j < data.node_index_matrix[i].size(); j++){
			for(int k = 0; k < data.node_index_matrix[i][j].size(); k++){
				poly.push_back(F(data.node_index_matrix[i][j][k]));
			}
		}
	}
	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[1]);
	poly.clear();
	for(int i = 0; i < data.leaf_index_matrix.size(); i++){
		for(int j = 0; j < data.leaf_index_matrix[i].size(); j++){
			for(int k = 0; k < data.leaf_index_matrix[i][j].size(); k++){
				poly.push_back(F(data.leaf_index_matrix[i][j][k]));
			}
		}
	}
	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[2]);
	poly.clear();
	for(int i = 0; i < data.leaf_matrix.size(); i++){
		for(int j = 0; j < data.leaf_matrix[i].size(); j++){
			for(int k = 0; k < data.leaf_matrix[i][j].size(); k++){
				poly.push_back(F(data.leaf_matrix[i][j][k]));
			}
		}
	}
	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[3]);
	poly = convert2vector(data.node_coeff);
	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[4]);
	poly = convert2vector(data.leaf_coeff);

	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[5]);
	total_p += pp.prove_time;
	total_v += pp.verification_time;
	total_s += (double)pp.proof_size/1024.0;
	printf("P : %lf, V : %lf, L : %lf\n",pp.prove_time,pp.verification_time,(double)pp.proof_size/1024.0);
	
	pp.prove_time = 0.0;
	pp.verification_time = 0.0;
	pp.proof_size =0;
}


nodes_histogram_SNARK_proof prove_node_histograms_forest(nodes_histogram_SNARK_data_forest &data, int trees , F previous_r){
	vector<vector<vector<F>>> witness_hist(trees);
	vector<vector<F>> witness_coeff(trees);
	vector<F> randomness(1);
	nodes_histogram_SNARK_proof P;
	vector<vector<G1>> commitments;
	if(_commitment_test){
		printf("Commit forest\n");
		commit_histograms_nodes_forest(data,commitments);
		printf("Open forest\n");
		open_histograms_nodes_forest(data,commitments);		
		printf("Finis\n");
		commitments.clear();

		return P;
	}
	
	auto t1 = chrono::high_resolution_clock::now();
    
	vector<vector<F>> H;
	vector<F> H_v;
				
	for(int k = 0; k < data.leaf_matrix.size(); k++){
		for(int i = data.leaf_matrix[k].size()-1; i > 0; i--){
		for(int j = 0; j < data.leaf_matrix[k][i].size(); j+=2){
			
			if(data.leaf_matrix[k][i][j] != -1){
				H_v.clear();
				witness_coeff[k].push_back(F(i));
				witness_coeff[k].push_back(F(j));
				witness_coeff[k].push_back(F(i));
				witness_coeff[k].push_back(F(j+1));
				
				if(data.leaf_index_matrix[k][i][j] != -1){
					H = data.leaf_histograms[k][data.leaf_index_matrix[k][i][j]];
				}else{
					H = data.node_histograms[k][data.node_index_matrix[k][i][j]];
				}
				for(int k = 0; k < H.size(); k++){
					H_v.insert(H_v.end(),H[k].begin(),H[k].end());
				}
				witness_hist[k].push_back(H_v);
				H_v.clear();
				if(data.leaf_index_matrix[k][i][j+1] != -1){
					H = data.leaf_histograms[k][data.leaf_index_matrix[k][i][j+1]];
				}else{
					H = data.node_histograms[k][data.node_index_matrix[k][i][j+1]];
				}
				for(int k = 0; k < H.size(); k++){
					H_v.insert(H_v.end(),H[k].begin(),H[k].end());
				}
				
				witness_hist[k].push_back(H_v);
			}
		}
	}
	}

	F two_inv = F(2);
	two_inv.inv(two_inv,two_inv);
	vector<vector<vector<F>>> out_hist(witness_hist.size());//(witness_hist.size()/2);	
	for(int k = 0; k < witness_hist.size(); k++){
		out_hist[k].resize(witness_hist[k].size()/2);
		for(int i = 0; i < out_hist[k].size(); i++){
			vector<F> hist_aggr(witness_hist[k][i].size());
			
			for(int j = 0; j < hist_aggr.size(); j++){
				hist_aggr[j] = witness_hist[k][2*i][j] + witness_hist[k][2*i+1][j];
			}
			out_hist[k][i] = hist_aggr;
		}
	}
	

	int witness_size = witness_hist[0][0].size();
	printf("%d\n",witness_size);
	if(1ULL<<((int)log2(witness_size)) != witness_hist[0][0].size()){
		witness_size = 1ULL<<((int)log2(witness_size)+1);
	}


	P.commitment.setByCSPRNG();P.previous_r = previous_r;
	F rand = mimc_hash(previous_r,P.commitment);
	
	P.r = generate_randomness((int)log2(witness_size),rand);
	vector<F> compress_vector;
	precompute_beta(P.r,compress_vector);
	vector<vector<F>> compressed_leaf_hist(trees),compressed_node_hist(trees);
	vector<vector<F>> compressed_witness(trees),compressed_out(trees);
	for(int i = 0; i < trees; i++){
		compressed_leaf_hist[i].resize(data.leaf_histograms[i].size(),F(0));
		compressed_node_hist[i].resize(data.node_histograms[i].size(),F(0));
		compressed_witness[i].resize(witness_hist[i].size(),F(0));
		compressed_out[i].resize(witness_hist[i].size()/2,F(0));
		
	}
	
	
	_compute_compressed_hist(compressed_leaf_hist,data.leaf_histograms,compress_vector);
	_compute_compressed_hist(compressed_node_hist,data.node_histograms,compress_vector);
	
	for(int k = 0; k < trees; k++){
		for(int i = 0; i < witness_hist[k].size()/2; i++){
			for(int j = 0; j < witness_hist[k][i].size(); j++){
				compressed_witness[k][2*i] += compress_vector[j]*witness_hist[k][2*i][j];
				compressed_witness[k][2*i+1] += compress_vector[j]*witness_hist[k][2*i+1][j];
				compressed_out[k][i] += compress_vector[j]*out_hist[k][i][j];
			}
		}
	}
	
	printf("%d,%d,%d,%d,%d,%d,%d,%d,\n",compressed_leaf_hist.size(),compressed_leaf_hist[0].size(),compressed_node_hist.size(),compressed_node_hist[0].size(),
	compressed_witness.size(),compressed_witness[0].size(),compressed_out.size(),compressed_out[0].size());

	vector<F> gkr_data;

	F a = mimc_hash(P.r[P.r.size()-1],F(0));
	F b = mimc_hash(a,F(1));
	F c = mimc_hash(b,F(2));
	F r = mimc_hash(c,F(3));
	rand = mimc_hash(r,F(0));

	

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
	gkr_data.push_back(r);
	gkr_data.push_back(two_inv);
	gkr_data.push_back(F(1));
	
	// Compute arr1 = a*leaf_coef[2*i]+b*leaf_coef[2*i+1] + c*compressed_leaf_hist[i] -c
	
	// Prove consistency of compressed histograms and tree coefficients
	randomness[0] = rand;
	printf("%d,%d,%d\n",gkr_data.size(),data.leaf_histograms[0].size(),data.node_histograms[0].size());
	P.GKR_proof1 = node_histogram_consistency_forest(gkr_data,randomness,data.leaf_histograms[0].size(),data.node_histograms[0].size(),trees);
	vector<F> x_leaf,x_node,x_witness,x_compressed_leaf,x_compressed_node,x_compressed_witness,x_compressed_out;
	vector<F> x = P.GKR_proof1.randomness[P.GKR_proof1.randomness.size()-1];
	if(P.GKR_proof1.q_poly[0].eval(0) + P.GKR_proof1.q_poly[0].eval(1) != F(0)){
		printf("Error in nodes histograms 1\n");
		//exit(-1);
	}

	for(int i = 0; i < (int)log2(convert2vector(witness_coeff).size()); i++){x_witness.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(convert2vector(data.node_coeff).size()); i++){x_node.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(convert2vector(data.leaf_coeff).size()); i++){x_leaf.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(convert2vector(compressed_witness).size()); i++){x_compressed_witness.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(convert2vector(compressed_node_hist).size()); i++){x_compressed_node.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(convert2vector(compressed_leaf_hist).size()); i++){x_compressed_leaf.push_back(x[i]);}

	P.wit_eval = evaluate_vector(convert2vector(witness_coeff),x_witness);
	P.node_eval = evaluate_vector(convert2vector(data.node_coeff),x_node);
	P.leaf_eval = evaluate_vector(convert2vector(data.leaf_coeff),x_leaf);
	P.comp_wit_eval = evaluate_vector(convert2vector(compressed_witness),x_compressed_witness);
	P.comp_node_eval = evaluate_vector(convert2vector(compressed_node_hist),x_compressed_node);
	P.comp_out_eval = evaluate_vector(convert2vector(compressed_out),x_compressed_node);
	P.comp_leaf_eval = evaluate_vector(convert2vector(compressed_leaf_hist),x_compressed_leaf);

	// Prove that the histograms compressed correctly
	
	rand = mimc_hash(P.GKR_proof1.final_rand,P.wit_eval);
	rand = mimc_hash(rand,P.node_eval);
	rand = mimc_hash(rand,P.leaf_eval);
	rand = mimc_hash(rand,P.comp_wit_eval);
	rand = mimc_hash(rand,P.comp_node_eval);
	rand = mimc_hash(rand,P.comp_out_eval);
	rand = mimc_hash(rand,P.comp_leaf_eval);


	int wit_row_size = witness_hist[0].size();
	vector<vector<F>> witness_hist_matrix;
	vector<vector<F>> out_hist_matrix;
	for(int i = 0; i < witness_hist.size(); i++){
		for(int j = 0; j  < witness_hist[i].size(); j++){
			witness_hist_matrix.push_back(witness_hist[i][j]);	
		}
		for(int j = 0; j < out_hist[i].size(); j++){
			out_hist_matrix.push_back(out_hist[i][j]);
		}
	}
	
	
	
	//pad_matrix(witness_hist);
	//pad_matrix(out_hist);

	
	P.sP1 = _prove_matrix2vector(_transpose(witness_hist_matrix),compress_vector,x_compressed_witness,P.comp_wit_eval,rand);
	verify_2product_sumcheck(P.sP1, P.sP1.q_poly[0].eval(F_ZERO) + P.sP1.q_poly[0].eval(F_ONE));
	P.sP2 = _prove_matrix2vector(_transpose(out_hist_matrix),compress_vector,x_compressed_node,P.comp_out_eval,P.sP1.final_rand);
	verify_2product_sumcheck(P.sP2, P.sP2.q_poly[0].eval(F_ZERO) + P.sP2.q_poly[0].eval(F_ONE));
	int leaves = data.leaf_histograms.size();
	int nodes = data.node_histograms.size();
	P.sP3 = _prove_matrix2vector(_padded_hist(data.leaf_histograms),compress_vector,x_compressed_leaf,P.comp_leaf_eval,P.sP2.final_rand);
	verify_2product_sumcheck(P.sP3, P.sP3.q_poly[0].eval(F_ZERO) + P.sP3.q_poly[0].eval(F_ONE));
	P.sP4 = _prove_matrix2vector(_padded_hist(data.node_histograms),compress_vector,x_compressed_node,P.comp_node_eval,P.sP3.final_rand);
	verify_2product_sumcheck(P.sP4, P.sP4.q_poly[0].eval(F_ZERO) + P.sP4.q_poly[0].eval(F_ONE));
	

	//prove_compression(data,witness_hist,out_hist,compressed_leaf_hist,compressed_node_hist,compressed_witness,compressed_out,compress_vector);
	// Prove that the out histograms computed correctly
	gkr_data.clear();
	for(int k = 0; k < trees; k++){
		for(int i = 0; i < witness_hist[k].size(); i++){
			gkr_data.insert(gkr_data.end(),witness_hist[k][i].begin(),witness_hist[k][i].end());
		}
	}
	
	
	randomness.clear();
	randomness = P.sP2.randomness[0];
	vector<F> x1;// = randomness;x1.push_back(0);
	vector<F> x2;// = randomness;x2.push_back(1);
	x1.insert(x1.end(),x_compressed_node.begin(),x_compressed_node.end());
	x2.insert(x2.end(),x_compressed_node.begin(),x_compressed_node.end());
	x1.push_back(F(0));
	x2.push_back(F(1));
	
	for(int i = 0; i < randomness.size(); i++){
		x1.push_back(randomness[i]);
		x2.push_back(randomness[i]);		
	}
	
	randomness.insert(randomness.end(),x_compressed_node.begin(),x_compressed_node.end());
	pad_vector(gkr_data);
	
	//P.GKR_proof2 = prove_node_sum(gkr_data,randomness,P.sP4.final_rand,witness_hist[0].size(),witness_hist.size(),nodes);
	F y1 = evaluate_vector(gkr_data,x1);
	F y2 = evaluate_vector(gkr_data,x2);
	

	
	P.final_rand = P.GKR_proof2.final_rand;
	
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);

	// need to reduce witness_hist
	return P;

}

void _add_histograms(vector<vector<vector<F>>> &node_histograms, vector<vector<F>> hist1, vector<vector<F>> hist2){
	vector<vector<F>> hist(hist1.size());
	for(int i = 0; i < hist.size(); i++){
		hist[i].resize(hist1[0].size());
		for(int j = 0; j < hist[i].size(); j++){
			hist[i][j] = hist1[i][j] + hist2[i][j];
		}
	}
	node_histograms.push_back(hist);
}

// Get histograms, the tree matrix and output the histogram of each node
nodes_histogram_SNARK_data_forest get_node_histograms_transcript_forest(vector<vector<F>> _histograms, vector<vector<vector<int>>> leaf_index_matrix, vector<vector<vector<int>>> leaf_matrix,int attr,vector<vector<vector<F>>> _leaf_coeff,int trees,int leaves){
	nodes_histogram_SNARK_data_forest data;
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
	
	// re-organize histograms
	// [node,attr,data]
	vector<vector<vector<vector<F>>>> histograms(trees);
	vector<vector<vector<vector<F>>>> node_histograms(trees);
	for(int i = 0; i < histograms.size(); i++){
		histograms[i].resize(leaves);
		
		for(int j = 0; j < leaves; j++){
			histograms[i][j].resize(attr);
			for(int l = 0; l < attr; l++){
				histograms[i][j][l].resize(bin_size*2);
				for(int k = 0; k < bin_size; k++){
					histograms[i][j][l][2*k] = _histograms[i][j*(attr*bin_size*2) + l*(2*bin_size) + 2*k];
					histograms[i][j][l][2*k+1] = _histograms[i][j*(attr*bin_size*2) + l*(2*bin_size) + 2*k+1];
				}	
			}
			
		}
	}
	_histograms.clear();
	
	for(int i = 1; i < trees; i++){
		for(int j = 0; j < leaves; j++){
			for(int l = 0; l < attr; l++){
				for(int k = 0; k < 2*bin_size; k++){
					if(histograms[0][j][l][k] != histograms[i][j][l][k]){
						printf("Error %d,%d,%d,%d\n",i,j,l,k);
						exit(-1);
					}
				}	
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

	vector<vector<F>> hist1,hist2;
	for(int k = 0; k < leaf_matrix.size(); k++){
		for(int i = leaf_matrix[k].size()-1; i > 0; i--){
			for(int j = 0; j < leaf_matrix[k][i].size(); j+=2){
				if(leaf_matrix[k][i][j] != -1){
					vector<int> temp_coeff;
					node_coeff[k].push_back(F(i-1));
					node_coeff[k].push_back(F(j/2));
					leaf_matrix[k][i-1][j/2] = 1;
					
					node_index_matrix[k][i-1][j/2] = node_coeff[k].size()/2-1; 
					if(leaf_index_matrix[k][i][j] != -1){
						hist1 = histograms[k][leaf_index_matrix[k][i][j]];
					}else{
						hist1 = node_histograms[k][node_index_matrix[k][i][j]];
					}
					if(leaf_index_matrix[k][i][j+1] != -1){
						hist2 = histograms[k][leaf_index_matrix[k][i][j+1]];		
					}else{
						hist2 = node_histograms[k][node_index_matrix[k][i][j+1]];				
					}
					_add_histograms(node_histograms[k],hist1,hist2);
				}
			}
		}
	}
 	
	

	data.node_histograms = node_histograms;
	data.leaf_histograms = histograms;

	data.node_index_matrix = node_index_matrix;
	data.leaf_index_matrix = leaf_index_matrix;

	data.leaf_matrix = leaf_matrix;
	data.node_coeff = node_coeff;
	data.leaf_coeff = leaf_coeff;
	return data;
}





void get_split_transcript_forest(split_SNARK_data &data,vector<vector<vector<F>>> node_histograms, int trees){
	printf("\n======= SPLIT Proof =======\n");
	int nodes = node_histograms.size()/trees;
	
	int attr = node_histograms[0].size();
	data.gini_inputs.resize(trees*nodes);
	//vector<vector<vector<F>>> gini_inputs(trees*nodes);
	data.sums.resize(trees*nodes);
	//vector<vector<vector<F>>> sums(trees*nodes);
	
	vector<vector<vector<float>>> fginis(trees*nodes);
	//vector<vector<vector<F>>> N(trees*nodes),dividents(trees*nodes),divisors(trees*nodes),quotients(trees*nodes),inverses(trees*nodes);
	data.N.resize(trees*nodes);
	data.dividents.resize(trees*nodes);
	data.divisors.resize(trees*nodes);
	data.quotients.resize(trees*nodes);
	data.inverses.resize(trees*nodes);
	// For debug purposes
	data.remainders.resize(trees*nodes);
	data.best_gini.resize(trees*nodes);
	//vector<vector<vector<F>>> remainders(trees*nodes);
	//vector<vector<F>> best_gini(trees*nodes);
	vector<vector<float>> _best_gini(trees*nodes);
	vector<vector<int>> _best_pos(trees*nodes);
	printf("%d,%d,%d\n",nodes,attr,trees);
	for(int i = 0; i < trees*nodes; i++){
		data.divisors[i].resize(attr);
		data.dividents[i].resize(attr);
		data.quotients[i].resize(attr);
		data.inverses[i].resize(attr);
		data.remainders[i].resize(attr);
		fginis[i].resize(attr);
		_best_gini[i].resize(attr);
		data.best_gini[i].resize(attr);
		_best_pos[i].resize(attr);
		data.N[i].resize(attr);
		for(int j = 0; j < attr; j++){
			data.dividents[i][j].resize(2*bin_size);
			data.divisors[i][j].resize(2*bin_size);
			data.quotients[i][j].resize(2*bin_size);
			data.inverses[i][j].resize(2*bin_size);
			data.remainders[i][j].resize(2*bin_size);
			data.N[i][j].resize(2*bin_size);
			fginis[i][j].resize(bin_size);
		}
	}

	
	for(int l = 0; l < trees; l++){
		for(int i = 0; i < nodes; i++){
			data.sums[l*nodes + i].resize(attr);
			
			for(int j = 0; j < attr; j++){
				data.sums[l*nodes + i][j].resize(2,F(0));
				for(int k = 0; k < node_histograms[l*nodes + i][j].size(); k+=2){
					data.sums[l*nodes + i][j][0] += node_histograms[l*nodes + i][j][k];
					data.sums[l*nodes + i][j][1] += node_histograms[l*nodes + i][j][k+1];
				}
				if(data.sums[l*nodes + i][j][0] == F(0) && data.sums[l*nodes + i][j][1] == F(0)){
					printf("Zero sum %d,%d \n",l,i);

				}
			}
		}
	}

	for(int l = 0; l < trees; l++){
		for(int i = 0; i < nodes; i++){
			data.gini_inputs[l*nodes + i].resize(attr);
			for(int j = 0; j < attr; j++){
				data.gini_inputs[l*nodes + i][j].resize(4*(bin_size));
				data.gini_inputs[l*nodes + i][j][0] = node_histograms[l*nodes + i][j][0];
				data.gini_inputs[l*nodes + i][j][1] = node_histograms[l*nodes + i][j][1];
				data.gini_inputs[l*nodes + i][j][2] = data.sums[l*nodes + i][j][0] - node_histograms[l*nodes + i][j][0];
				data.gini_inputs[l*nodes + i][j][3] = data.sums[l*nodes + i][j][1] - node_histograms[l*nodes + i][j][1];
				for(int k = 1; k < bin_size; k++){
					data.gini_inputs[l*nodes + i][j][4*k] = node_histograms[l*nodes + i][j][2*k] + data.gini_inputs[l*nodes + i][j][4*(k-1)];
					data.gini_inputs[l*nodes + i][j][4*k+1] = node_histograms[l*nodes + i][j][2*k+1] + data.gini_inputs[l*nodes + i][j][4*(k-1)+1];
					data.gini_inputs[l*nodes + i][j][4*k+2] = data.gini_inputs[l*nodes + i][j][4*(k-1)+2] - node_histograms[l*nodes + i][j][2*k];
					data.gini_inputs[l*nodes + i][j][4*k+3] = data.gini_inputs[l*nodes + i][j][4*(k-1)+3] - node_histograms[l*nodes + i][j][2*k+1];
				
				}

			}
		}
	}
	
	
	for(int l = 0; l < trees; l++){
		
	
	for(int i = 0; i < nodes; i++){
		
		
		fginis[l*nodes + i].resize(attr);
		for(int j = 0; j < attr; j++){
			fginis[l*nodes + i][j].resize(bin_size);
			float min1 = 100,min2 = 100;
			int idx1,idx2;
			for(int k = 0; k < bin_size; k++){
				// Compute 
				char num_str[64];
				int N11,N10,N21,N20;
				data.gini_inputs[l*nodes + i][j][4*k].getStr(num_str,64,10);
				N11 = stoi(num_str);
				data.gini_inputs[l*nodes + i][j][4*k+1].getStr(num_str,64,10);
				N10 = stoi(num_str);
				data.gini_inputs[l*nodes + i][j][4*k+2].getStr(num_str,64,10);
				N21 = stoi(num_str);
				data.gini_inputs[l*nodes + i][j][4*k+3].getStr(num_str,64,10);
				N20 = stoi(num_str);
				float N1 = (float)(N10+N11);
				float N2 = (float)(N20+N21);

		
				if(N1 && N2){
					float _G1 = ((float)N11/(float)N1)*((float)N11/(float)N1) + ((float)N10/(float)N1)*((float)N10/(float)N1);
					//float _G1 = ((float)N11*N11+(float)N10*N10)/(float)((N11+N10)*(N11+N10));
					float _G2 = ((float)N21/(float)N2)*((float)N21/(float)N2) + ((float)N20/(float)N2)*((float)N20/(float)N2);
					//float _G2 = ((float)N21*N21+(float)N20*N20)/(float)((N21+N20)*(N21+N20));
					
					fginis[l*nodes + i][j][k] = 1 - _G1*N1/(N2+N1) - _G2*N2/(N1+N2);
					if(fginis[l*nodes + i][j][k] > 1.0){
						printf("Error\n");
						printf("%d,%d,%d,%d,%lf,%lf,%lf,%lf\n",N10,N11,N20,N21,N1,N2,_G1,_G2 );
						exit(-1);
					}
				}else if(N1 == 0){
				
					float _G2 = ((float)N21/(float)N2)*((float)N21/(float)N2) + ((float)N20/(float)N2)*((float)N20/(float)N2);
					//float _G2 = ((float)N21*N21+(float)N20*N20)/(float)((N21+N20)*(N21+N20));
					fginis[l*nodes + i][j][k] = 1.0 - _G2;					
				}else if(N2 == 0){
					float _G1 = ((float)N11/(float)N1)*((float)N11/(float)N1) + ((float)N10/(float)N1)*((float)N10/(float)N1);
					fginis[l*nodes + i][j][k] = 1.0 - _G1;						
				}
				
				F _N1 = (data.gini_inputs[l*nodes + i][j][4*k]+data.gini_inputs[l*nodes + i][j][4*k+1]);
				F _N2 = (data.gini_inputs[l*nodes + i][j][4*k+2]+data.gini_inputs[l*nodes + i][j][4*k+3]);
				data.N[l*nodes + i][j][2*k] = _N1;
				data.N[l*nodes + i][j][2*k+1] = _N2;
				data.divisors[l*nodes + i][j][2*k] = _N1*(_N1+_N2);
				data.divisors[l*nodes + i][j][2*k+1] = _N2*(_N1+_N2);
				data.dividents[l*nodes + i][j][2*k] = (_N1*_N1 - F(2)*data.gini_inputs[l*nodes + i][j][4*k]*data.gini_inputs[l*nodes + i][j][4*k+1]);  
				data.dividents[l*nodes + i][j][2*k+1] = (_N2*_N2 - F(2)*data.gini_inputs[l*nodes + i][j][4*k+2]*data.gini_inputs[l*nodes + i][j][4*k+3]);
				float d1 = 0.0,d2 = 0.0;
				/*
				if(_N1 == F(0) && _N2 == F(0)){
					quotients[l*nodes + i][j][2*k] = F_ZERO;
					quotients[l*nodes + i][j][2*k+1] = F_ZERO;
					inverses[l*nodes + i][j][2*k] = F_ZERO;
					
					inverses[l*nodes + i][j][2*k+1] = F_ZERO;
					remainders[l*nodes + i][j][2*k] = F_ZERO;
					remainders[l*nodes + i][j][2*k+1] = F_ZERO;
					continue;
				}
				*/
				if(_N1 != F(0) && _N2 != F(0)){
					
					d1 = dequantize(divide(F(1<<Q)*data.dividents[l*nodes + i][j][2*k],data.divisors[l*nodes + i][j][2*k]),1);
					d2 = dequantize(divide(F(1<<Q)*data.dividents[l*nodes + i][j][2*k+1],data.divisors[l*nodes + i][j][2*k+1]),1);
					data.quotients[l*nodes + i][j][2*k] = divide(F(1<<Q)*data.dividents[l*nodes + i][j][2*k],data.divisors[l*nodes + i][j][2*k]);
					data.quotients[l*nodes + i][j][2*k+1] = divide(F(1<<Q)*data.dividents[l*nodes + i][j][2*k+1],data.divisors[l*nodes + i][j][2*k+1]);
					data.inverses[l*nodes + i][j][2*k].inv(data.inverses[l*nodes + i][j][2*k],_N1);
					
					data.inverses[l*nodes + i][j][2*k+1].inv(data.inverses[l*nodes + i][j][2*k+1],_N2);
					data.remainders[l*nodes + i][j][2*k] = F(1<<Q)*data.dividents[l*nodes + i][j][2*k] - data.divisors[l*nodes + i][j][2*k]*data.quotients[l*nodes + i][j][2*k];
					data.remainders[l*nodes + i][j][2*k+1] = F(1<<Q)*data.dividents[l*nodes + i][j][2*k+1] - data.divisors[l*nodes + i][j][2*k+1]*data.quotients[l*nodes + i][j][2*k+1];
				
				}
				else if(_N1 == F(0)){
		
		
					d2 = dequantize(divide(F(1<<Q)*data.dividents[l*nodes + i][j][2*k+1],data.divisors[l*nodes + i][j][2*k+1]),1);					
					data.quotients[l*nodes + i][j][2*k] = F(0);
					data.quotients[l*nodes + i][j][2*k+1] = divide(F(1<<Q)*data.dividents[l*nodes + i][j][2*k+1],data.divisors[l*nodes + i][j][2*k+1]);
					data.inverses[l*nodes + i][j][2*k] = F(0);
					data.inverses[l*nodes + i][j][2*k+1].inv(data.inverses[l*nodes + i][j][2*k+1],_N2);
					data.remainders[l*nodes + i][j][2*k] = F(0);
					data.remainders[l*nodes + i][j][2*k+1] = F(1<<Q)*data.dividents[l*nodes + i][j][2*k+1] - data.divisors[l*nodes + i][j][2*k+1]*data.quotients[l*nodes + i][j][2*k+1];
				}
				else{
					d1 = dequantize(divide(F(1<<Q)*data.dividents[l*nodes + i][j][2*k],data.divisors[l*nodes + i][j][2*k]),1);
					data.quotients[l*nodes + i][j][2*k] = divide(F(1<<Q)*data.dividents[l*nodes + i][j][2*k],data.divisors[l*nodes + i][j][2*k]);
					data.quotients[l*nodes + i][j][2*k+1] = F(0);							
					data.inverses[l*nodes + i][j][2*k].inv(data.inverses[l*nodes + i][j][2*k],_N1);
					data.inverses[l*nodes + i][j][2*k+1] = F(0);
					data.remainders[l*nodes + i][j][2*k] = F(1<<Q)*data.dividents[l*nodes + i][j][2*k] - data.divisors[l*nodes + i][j][2*k]*data.quotients[l*nodes + i][j][2*k];
					data.remainders[l*nodes + i][j][2*k+1] = F(0);
				}
				
				
				if(fginis[l*nodes + i][j][k] - 1 + d1 +d2 > 0.0001){
					printf("Error %lf,%lf\n", fginis[l*nodes + i][j][k],1-d1-d2);
					exit(-1);
				}
				if(min1 - fginis[l*nodes + i][j][k] > 0){
					//printf("Ok, %.16lf,%.16lf,%d,%d,%d,%d\n",fginis[i][j][k],min1,((double)min1 - (double)fginis[i][j][k]) > 0.0,i,j,k);
					min1 = fginis[l*nodes + i][j][k];
					idx1 = k;
				
					data.best_gini[l*nodes + i][j] = F(1<<Q) - data.quotients[l*nodes + i][j][2*k] - data.quotients[l*nodes + i][j][2*k+1];
					idx2 = k;
					
				}
				//if(min2 > 1 - d1 - d2){
				//	min2 =  1 - d1 - d2;
				//	best_gini[i][j] = F(1<<Q) - quotients[i][j][2*k] - quotients[i][j][2*k+1];
				//	idx2 = k;
				//	printf(">>Ok %lf,%d,%d,%d\n",min2,i,j,k);
				//}
				//printf("%lf\n", 1 - _G1*N1/(N2+N1) - _G2*N2/(N1+N2));
			}
			if(idx1 != idx2){
				
				printf("Error in split value, increase quantization\n");
				exit(-1);
			}
			//printf("%d\n",min2 );

			_best_gini[l*nodes + i][j] = min1;
			_best_pos[l*nodes + i][j] = idx1;
		}
	}
	}
	
	
	vector<vector<vector<F>>> ginis(trees*nodes);
	for(int l = 0; l < trees; l++){
		for(int i = 0; i < nodes; i++){
			ginis[l*nodes + i].resize(attr);
			for(int j = 0; j < attr; j++){
				ginis[l*nodes + i][j].resize(bin_size);
				for(int k = 0; k < bin_size; k++){
					ginis[l*nodes + i][j][k] = F(1<<Q)- data.quotients[l*nodes + i][j][2*k] - data.quotients[l*nodes + i][j][2*k+1]; 
				}
			}
		}
	}
	
	

	data.nodes = trees*nodes;
	data.attr = attr;
	//data.gini_inputs = gini_inputs;
	//data.sums = sums;
	data.node_histograms = node_histograms;
	//data.inverses = inverses;
	//data.quotients = quotients;
	//data.remainders = remainders;
	//data.divisors = divisors;
	//data.dividents = dividents;
	//data.N = N;
	//data.best_gini = best_gini;
	data.ginis = ginis;
	//return data;
}
