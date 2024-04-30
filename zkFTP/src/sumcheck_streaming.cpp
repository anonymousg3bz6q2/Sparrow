#include "config_pc.hpp"
#include "GKR.h"
#include "mimc.h"
#include "utils.hpp"
#include "sumcheck.h"
#include <chrono>
#include "quantization.h"
#include "sumcheck_streaming.h"
#define RANGE 1
#define SUM 2

using namespace std::chrono;

extern int threads;
extern int bin_size;
extern double range_proof_verification_time;
extern int range_proof_size;
extern size_t MAX_CHUNCK;
extern double proving_time;


/*

proof_streaming generate_3product_sumcheck_proof_disk(int fp1, int fp2, size_t size, vector<F> beta_rand, F previous_r, int mod){
	proof_streaming Pr;
	int M = 8;
	vector<int> _M;
			
	if(size > (size_t)MAX_CHUNCK*(size_t)MAX_CHUNCK){
		printf("Increase MAX_CHUNCK, size : %d\n",size );
		exit(-1);
	}

	printf("%d,%d\n",size,beta_rand.size() );
	vector<vector<vector<F>>> Acc_Sums;
	vector<vector<F>> P_sum(M);
	F sum = F(0);
	for(int i = 0; i < M; i++){
		P_sum[i].resize(M,F(0));
	}
	
	vector<F> v1(MAX_CHUNCK),v2(MAX_CHUNCK);
	vector<F> v;
	if(fp2 == -1){
		v.resize(2*MAX_CHUNCK);
	}
	vector<F> partitions_rand(beta_rand.size() - (int)log2(MAX_CHUNCK));
	for(int i = 0; i < beta_rand.size()-(int)log2(MAX_CHUNCK); i++){
		partitions_rand[i] = beta_rand[i];
	}

	vector<F> beta_partitions,beta;
	precompute_beta(partitions_rand,beta_partitions);
	partitions_rand.clear();
	for(int i = beta_rand.size()-(int)log2(MAX_CHUNCK); i < beta_rand.size(); i++){
		partitions_rand.push_back(beta_rand[i]);
	}

	precompute_beta(partitions_rand,beta);

	F rand = previous_r;
	vector<quadratic_poly> p;
	vector<F> rand_v,r;
	vector<vector<F>> R1,R2;
	int temp_size = size;
	int cluster_size = 1;
	printf("%d,%d\n", MAX_CHUNCK,size/MAX_CHUNCK);
	int seg = MAX_CHUNCK/M,counter;
	
	

	while(1){
		lseek(fp1, 0, SEEK_SET);
		if(fp2 != -1){
			lseek(fp2, 0, SEEK_SET);
		}
		counter = 0;
		if((size/MAX_CHUNCK)/(cluster_size*M) == 0){
			M = (size/MAX_CHUNCK)/cluster_size;
		}
		for(int i = 0; i < size/MAX_CHUNCK; i++){
			if(fp2 != -1){
				read_chunk(fp1,v1,MAX_CHUNCK);
				read_chunk(fp2,v2,MAX_CHUNCK);
			}else{
				if(mod == RANGE){
					read_chunk(fp1,v,MAX_CHUNCK);
					for(int j = 0; j < MAX_CHUNCK; j++){
						v1[j] = v[j];
						v2[j] = F(1) - v[j];
					}
				}else{
					read_chunk(fp1,v,2*MAX_CHUNCK);
					for(int j = 0; j < MAX_CHUNCK; j++){
						v1[j] = v[2*j];
						v2[j] = v[2*j+1];
					}
				}

			}
			for(int j = 0; j < MAX_CHUNCK; j+=size/MAX_CHUNCK){
				for(int k = 0; k < size/MAX_CHUNCK; k++){
					v1[j + k] = beta[counter]*beta_partitions[k]*v1[j+k];
				}
				counter++;
			}
			if(cluster_size != 1){
				F temp1 = F(0),temp2 = F(0);
				int offset = MAX_CHUNCK;
				for(int j = 0; j < R1.size(); j++){
					offset = offset/_M[j];
					
					for(int k = 0; k < offset; k++){
						temp1 = F(0);temp2 = F(0);
						for(int l = 0; l < _M[j]; l++){
							temp1 += v1[_M[j]*k + l]*R1[j][l];
							temp2 += v2[_M[j]*k + l]*R2[j][l];
						}
						v1[k] = temp1;
						v2[k] = temp2;	 
					}
				}
			}
		
		

			for(int j = 0; j < MAX_CHUNCK/cluster_size; j+= M){
				for(int k1 = 0; k1 < M; k1++){
					for(int k2 = 0; k2 < M; k2++){
						if(k1==k2)continue;
						P_sum[k1][k2] += v1[j + k1]*v2[j + k2];
					}
				}
			}

		}	
		Acc_Sums.push_back(P_sum);
		for(int j = 0; j < M; j++){
			for(int k = 0; k < M; k++){
				P_sum[j][k] = F(0);
			}
		}
		
		cluster_size *= M;
		temp_size = temp_size/M;
		_M.push_back(M);

		//printf("OK %d,%d,%d,%d\n",cluster_size,temp_size,MAX_CHUNCK/cluster_size,temp_size/MAX_CHUNCK);
		
		//printf("temp size : %d, cluster_size : %d\n", temp_size,cluster_size);
		vector<F> r = generate_randomness(M,F(0));
		vector<F> r_inverse(M,0);
		for(int i = 0; i < r.size(); i++){
			r_inverse[i].inv(r_inverse[i],r[i]);
			if(r_inverse[i]*r[i] != F(1)){
				printf("Error\n");
				exit(-1);
			}
		}
		R1.push_back(r);
		R2.push_back(r_inverse);
		if(temp_size <= MAX_CHUNCK){
			break;
		}
	}


	lseek(fp1, 0, SEEK_SET);
	if(fp2 != -1){
		lseek(fp2, 0, SEEK_SET);
	}
			
	//printf("%d,%d\n",_M.size(),R1.size());
	//for(int i = 0; i < _M.size(); i++){
	//	printf("%d\n",_M[i]);
	//}
	vector<F> fv1(MAX_CHUNCK),fv2(MAX_CHUNCK);
	counter = 0;
	for(int i = 0; i < size/MAX_CHUNCK; i++){
		if(fp2 != -1){
				read_chunk(fp1,v1,MAX_CHUNCK);
				read_chunk(fp2,v2,MAX_CHUNCK);
		}else{
			if(mod == RANGE){
				read_chunk(fp1,v,MAX_CHUNCK);
				for(int j = 0; j < MAX_CHUNCK; j++){
					v1[j] = v[j];
					v2[j] = F(1) - v[j];
				}
			}else{
				read_chunk(fp1,v,2*MAX_CHUNCK);
				for(int j = 0; j < MAX_CHUNCK; j++){
					v1[j] = v[2*j];
					v2[j] = v[2*j+1];
				}
			}

		}
		for(int j = 0; j < MAX_CHUNCK; j+=size/MAX_CHUNCK){
			for(int k = 0; k < size/MAX_CHUNCK; k++){
				v1[j + k] = beta_partitions[k]*v1[j+k];
			}
		}
		F temp1 = F(0),temp2 = F(0);
		int offset = MAX_CHUNCK;
		for(int j = 0; j < R1.size(); j++){
			offset = offset/_M[j];
			for(int k = 0; k < offset; k++){
				temp1 = F(0);temp2 = F(0);
				for(int l = 0; l < _M[j]; l++){
					temp1 += v1[_M[j]*k + l]*R1[j][l];
					temp2 += v2[_M[j]*k + l]*R2[j][l];
				}
				v1[k] = temp1;
				v2[k] = temp2;	 
			}
		}

		for(int j = 0; j < offset; j++){
			fv1[counter] = v1[j];
			fv2[counter] = v2[j];
			counter++;
		}
	}

	
	F f_sum = F(0);

	for(int k = 0; k < R1.size(); k++){
		for(int i = 0; i < _M[k]; i++){
			for(int j = 0; j < _M[k]; j++){
				f_sum += R1[k][i]*R2[k][j]*Acc_Sums[k][i][j];
			}
		}
	}

	Pr.new_sum = f_sum;
	
	proof P1 = _generate_3product_sumcheck_proof(fv1,fv2,beta, F(0));
	Pr.P.push_back(P1);
	P1.final_sum = f_sum;
	r = P1.randomness[0];
	
	beta.clear();
	precompute_beta(r,beta);
	vector<F> evals1(size/MAX_CHUNCK,F(0)),evals2(size/MAX_CHUNCK,F(0));
	counter = 0;
	lseek(fp1, 0, SEEK_SET);
	if(fp2 != -1){
		lseek(fp2, 0, SEEK_SET);
	}

	for(int i = 0; i < size/MAX_CHUNCK; i++){
		if(fp2 != -1){
			read_chunk(fp1,v1,MAX_CHUNCK);
			read_chunk(fp2,v2,MAX_CHUNCK);
		}else{
			if(mod == RANGE){
				read_chunk(fp1,v,MAX_CHUNCK);
				for(int j = 0; j < MAX_CHUNCK; j++){
					v1[j] = v[j];
					v2[j] = F(1) - v[j];
				}
			}else{
				read_chunk(fp1,v,2*MAX_CHUNCK);
				for(int j = 0; j < MAX_CHUNCK; j++){
					v1[j] = v[2*j];
					v2[j] = v[2*j+1];
				}
			}

		}
		for(int j = 0; j < MAX_CHUNCK; j+=size/MAX_CHUNCK){
			for(int k = 0; k < size/MAX_CHUNCK; k++){
				evals1[k] += beta[counter]*v1[j+k];
				evals2[k] += beta[counter]*v2[j+k];
			}
			counter++;
		}
	}
	
	vector<F> challenge_vector = R1[0];
	for(int i = 1; i < R1.size(); i++){
		vector<F> temp(challenge_vector.size()*R1[i].size());
		for(int k = 0; k < R1[i].size(); k++){
			for(int j = 0; j  < challenge_vector.size(); j++){
				temp[k*challenge_vector.size() + j] = challenge_vector[j]*R1[i][k];
			}
		}
		challenge_vector = temp;
		temp.clear();
	}
	vector<F> inv_challenge(challenge_vector.size());
	for(int i = 0; i < challenge_vector.size(); i++){
		inv_challenge[i].inv(inv_challenge[i],challenge_vector[i]);
	}

	proof P2 = _generate_3product_sumcheck_proof(evals1,beta_partitions,challenge_vector,F(0));
	Pr.P.push_back(P2);
	Pr.randomness = P2.randomness[0];
	Pr.randomness.insert(Pr.randomness.end(),P1.randomness[0].begin(),P1.randomness[0].end());
	Pr.vr.push_back(P2.vr[0]);
	if(P2.c_poly[0].eval(F(0)) + P2.c_poly[0].eval(F(1)) != P1.vr[0]){
		printf("Error on merging first polynomial\n");
		exit(-1);
	}
	

	F eval = evaluate_vector(evals2,P2.randomness[0]);
	Pr.vr.push_back(eval);
	proof P3 = generate_2product_sumcheck_proof(evals2,inv_challenge,F(0));
	if(P3.q_poly[0].eval(F(0))+P3.q_poly[0].eval(F(1)) != P1.vr[1]){
		printf("Error on merging second polynomial\n");
		exit(-1);
	}
	Pr.P.push_back(P3);
	P3.vr[0] = eval;
	

	return Pr;
} 



vector<F> prepare_matrix_streaming(vector<int> fd, vector<size_t> fd_cols, vector<size_t> fd_size, size_t row_size, vector<F> r, int cols){
	vector<F> compressed_col(cols,F(0));
	vector<F> v1(MAX_CHUNCK);
	vector<F> x1,x2,beta1,beta2;
	
	int counter = 0;
	for(int k = 0; k < fd.size(); k++){
		lseek(fd[k],0,SEEK_SET);
		int _MAX_CHUNCK = MAX_CHUNCK;
		if(_MAX_CHUNCK > fd_size[k]){
			_MAX_CHUNCK = fd_size[k];
		}
	
		x1.clear();x2.clear();beta1.clear();beta2.clear();
		for(int i = 0; i < (int)log2(_MAX_CHUNCK/fd_cols[k]); i++){
			x1.push_back(r[i]);
		}
		for(int i = (int)log2(_MAX_CHUNCK/fd_cols[k]); i < r.size(); i++){
			x2.push_back(r[i]);
		}
		precompute_beta(x1,beta1);
		precompute_beta(x2,beta2);
		printf("%d,%d,%d,%d\n",x1.size(),x2.size(),r.size(),_MAX_CHUNCK/fd_cols[k] );

		for(int i = 0; i < fd_size[k]/_MAX_CHUNCK; i++){
			read_chunk(fd[k],v1,_MAX_CHUNCK);
			for(int j = 0; j < fd_cols[k]; j++){
				for(int l = 0; l < _MAX_CHUNCK/fd_cols[k]; l++){
					compressed_col[counter + j] += beta1[l]*beta2[i]*v1[l*fd_cols[k] + j];
				}
			}
		}
		counter += fd_cols[k];
		printf("%d\n",counter );
	}
	return compressed_col;

}	

void _prove_bit_decomposition_stream(int bits_fd, size_t size, vector<F> r1, F previous_sum, F previous_r, int domain){
	vector<F> powers;
	powers.push_back(F(1));
	for(int i = 1; i < domain; i++){
		powers.push_back(F(2)*powers[i-1]);
	}
	pad_vector(powers);
	printf("size : %lld\n",size );
	vector<int> fd;fd.push_back(bits_fd);
	vector<size_t> fd_cols; fd_cols.push_back(domain);
	vector<size_t> fd_size; fd_size.push_back(size); 
	vector<F> prod = prepare_matrix_streaming(fd, fd_cols, fd_size, size/domain, r1, domain);
	proof Pr1 = generate_2product_sumcheck_proof(prod,powers,previous_r);
	//if(previous_sum != Pr1.q_poly[0].eval(0) + Pr1.q_poly[0].eval(1)){
	//	printf("Error in bit_decomposition 1\n");
	//	exit(-1);
	//}

	vector<F> r2 = generate_randomness(int(log2(size)),Pr1.final_rand);
	lseek(bits_fd,0, SEEK_SET);
	printf("OK\n");
	proof_streaming P = generate_3product_sumcheck_proof_disk(bits_fd, -1, size, r2, r2[r2.size()-1], RANGE);
	printf("OK2\n");
	if(P.P[0].c_poly[0].eval(F(0)) + P.P[0].c_poly[0].eval(F(1)) != P.new_sum){
		printf("Error in bit_decomposition 2\n");
		exit(-1);
	}
	printf("OK\n");
}	


void compute_temp_beta(vector<vector<F>> &beta1,vector<vector<F>> &beta2, vector<F> &a, vector<F> &v, int idx){

	for(int i = 0; i < v.size(); i++){
		v[i] = a[0]*beta1[0][i]*beta2[0][idx];
	}
	for(int k = 1; k < beta1.size(); k++){
		for(int i = 0; i < v.size(); i++){
			v[i] += a[k]*beta1[k][i]*beta2[k][idx];
		}	
	}
}


proof_streaming generate_2product_sumcheck_proof_disk_beta(int fp1, vector<vector<F>> beta_rand,vector<F> a,size_t size, F previous_r){
	
	int M = 8;
	vector<int> _M;
	proof_streaming P;
	
	if(MAX_CHUNCK > size){
		vector<F> beta,temp_beta;
		vector<F> v(size);
		precompute_beta(beta_rand[0],beta);
		for(int i = 0; i < beta.size(); i++){
			beta[i] = a[0]*beta[i];
		}
		for(int i = 1; i < a.size(); i++){
			precompute_beta(beta_rand[i],temp_beta);
			for(int j = 0; j < beta.size(); j++){
				beta[j] += a[i]*temp_beta[j];
			}
		}
		read_chunk(fp1,v,size);
		P.P.push_back(generate_2product_sumcheck_proof(beta,v,previous_r));
		return P;
	}


	if(size > (size_t)MAX_CHUNCK*(size_t)MAX_CHUNCK){
		printf("Increase MAX_CHUNCK, size : %d\n",size );
		exit(-1);
	}

	vector<vector<vector<F>>> Acc_Sums;
	vector<vector<F>> P_sum(M);
	F sum = F(0);
	for(int i = 0; i < M; i++){
		P_sum[i].resize(M,F(0));
	}
	
	vector<F> v1(MAX_CHUNCK),v2(MAX_CHUNCK);
	F rand = previous_r;
	vector<quadratic_poly> p;
	vector<F> rand_v,r;
	vector<vector<F>> R1,R2;
	int temp_size = size;
	int cluster_size = 1;
	printf("%d,%d,%d,%d\n", MAX_CHUNCK/M,M,size,size/MAX_CHUNCK);
	int seg = MAX_CHUNCK/M;
	
	vector<vector<F>> x1(a.size()),x2(a.size());
	vector<vector<F>> beta1(a.size()),beta2(a.size());
	for(int i = 0; i < a.size(); i++){
		for(int j = 0; j < (int)log2(MAX_CHUNCK); j++){
			x1[i].push_back(beta_rand[i][j]);
		}
		for(int j = (int)log2(MAX_CHUNCK); j < (int)log2(size); j++){
			x2[i].push_back(beta_rand[i][j]);
		}
		precompute_beta(x1[i],beta1[i]);
		precompute_beta(x2[i],beta2[i]);
	}
	
	while(1){
		lseek(fp1, 0, SEEK_SET);
		//lseek(fp2, 0, SEEK_SET);
		if((size/MAX_CHUNCK)/(cluster_size*M) == 0){
			M = (size/MAX_CHUNCK)/cluster_size;
		}
		for(int i = 0; i < size/MAX_CHUNCK; i++){
			read_chunk(fp1,v1,MAX_CHUNCK);
			compute_temp_beta(beta1,beta2,a,v2,i);
			//read_chunk(fp2,v2,MAX_CHUNCK);
			if(cluster_size != 1){
				F temp1 = F(0),temp2 = F(0);
				int offset = MAX_CHUNCK;
				for(int j = 0; j < R1.size(); j++){
					offset = offset/_M[j];
					
					for(int k = 0; k < offset; k++){
						temp1 = F(0);temp2 = F(0);
						for(int l = 0; l < _M[j]; l++){
							temp1 += v1[_M[j]*k + l]*R1[j][l];
							temp2 += v2[_M[j]*k + l]*R2[j][l];
						}
						v1[k] = temp1;
						v2[k] = temp2;	 
					}
				}
			}else{
				for(int j = 0; j < MAX_CHUNCK; j++){
					sum += v1[j]*v2[j];
				}
			}


			for(int j = 0; j < MAX_CHUNCK/cluster_size; j+= M){
				for(int k1 = 0; k1 < M; k1++){
					for(int k2 = 0; k2 < M; k2++){
						if(k1==k2)continue;
						P_sum[k1][k2] += v1[j + k1]*v2[j + k2];
					}
				}
			}

		}	
		Acc_Sums.push_back(P_sum);
		for(int j = 0; j < M; j++){
			for(int k = 0; k < M; k++){
				P_sum[j][k] = F(0);
			}
		}
		
		cluster_size *= M;
		temp_size = temp_size/M;
		_M.push_back(M);

		printf("OK %d,%d,%d,%d\n",cluster_size,temp_size,MAX_CHUNCK/cluster_size,temp_size/MAX_CHUNCK);
		
		//printf("temp size : %d, cluster_size : %d\n", temp_size,cluster_size);
		vector<F> r = generate_randomness(M,F(0));
		vector<F> r_inverse(M,0);
		for(int i = 0; i < r.size(); i++){
			r_inverse[i].inv(r_inverse[i],r[i]);
			if(r_inverse[i]*r[i] != F(1)){
				printf("Error\n");
				exit(-1);
			}
		}
		R1.push_back(r);
		R2.push_back(r_inverse);
		if(temp_size <= MAX_CHUNCK){
			printf("Break\n");
			break;
		}
	}


	lseek(fp1, 0, SEEK_SET);
	//lseek(fp2, 0, SEEK_SET);
			
	//printf("%d,%d\n",_M.size(),R1.size());
	for(int i = 0; i < _M.size(); i++){
		printf("%d\n",_M[i]);
	}
	vector<F> fv1(MAX_CHUNCK),fv2(MAX_CHUNCK);
	int counter = 0;
	for(int i = 0; i < size/MAX_CHUNCK; i++){
		read_chunk(fp1,v1,MAX_CHUNCK);
		compute_temp_beta(beta1,beta2,a,v2,i);
		//read_chunk(fp2,v2,MAX_CHUNCK);
		F temp1 = F(0),temp2 = F(0);
		int offset = MAX_CHUNCK;
		for(int j = 0; j < R1.size(); j++){
			offset = offset/_M[j];
			for(int k = 0; k < offset; k++){
				temp1 = F(0);temp2 = F(0);
				for(int l = 0; l < _M[j]; l++){
					temp1 += v1[_M[j]*k + l]*R1[j][l];
					temp2 += v2[_M[j]*k + l]*R2[j][l];
				}
				v1[k] = temp1;
				v2[k] = temp2;	 
			}
		}

		for(int j = 0; j < offset; j++){
			fv1[counter] = v1[j];
			fv2[counter] = v2[j];
			counter++;
		}
	}

	F f_sum = sum;
	P.sum = sum;
	for(int k = 0; k < R1.size(); k++){
		for(int i = 0; i < _M[k]; i++){
			for(int j = 0; j < _M[k]; j++){
				f_sum += R1[k][i]*R2[k][j]*Acc_Sums[k][i][j];
			}
		}

	}
	P.new_sum = f_sum;

	F r_sum = F(0);
	for(int i = 0; i < fv1.size(); i++){
		r_sum += fv1[i]*fv2[i];
	}
	if(f_sum != r_sum){
		printf("Error in sum\n");
		exit(-1);
	}

	P.P.push_back(generate_2product_sumcheck_proof(fv1,fv2, F(0)));
	lseek(fp1, 0, SEEK_SET);
	
	r = P.P[0].randomness[0];
	vector<F> beta;
	precompute_beta(r,beta);
	vector<F> evals1(size/MAX_CHUNCK,F(0)),evals2(size/MAX_CHUNCK,F(0));
	counter = 0;
	for(int i = 0; i < size/MAX_CHUNCK; i++){
		read_chunk(fp1,v1,MAX_CHUNCK);
		compute_temp_beta(beta1,beta2,a,v2,i);
		//read_chunk(fp2,v2,MAX_CHUNCK);
		for(int j = 0; j < MAX_CHUNCK; j+=size/MAX_CHUNCK){
			for(int k = 0; k < size/MAX_CHUNCK; k++){
				evals1[k] += beta[counter]*v1[k];
				//evals2[k] += beta[counter]*v2[k];
			}
			counter++;
		}
		
	}
	
	return P;

}

void check_consistency(int fd, int size, int vectors){
	int depth = (int)log2(size);
	int vfd[depth];
	for(int i = 0; i < depth; i++){
		string name = "mul_tree" + to_string(i);
		vfd[i] = open(name.c_str(),O_RDWR);
	}
	lseek(fd, 0, SEEK_SET);
	
	if(vectors == 1){
		vector<F> input(size);
		vector<F> intermidiate_states;
		read_chunk(fd,input,size);
		F prod = F(1);
		for(int i = 0; i < input.size(); i++){
			prod = prod*input[i];
		}
		
		for(int i = 0; i < depth; i++){
			intermidiate_states.clear();
			intermidiate_states.resize(size/(1<<(i+1)));
			read_chunk(vfd[i],intermidiate_states,intermidiate_states.size());
			F new_prod = F(1);
			for(int j = 0; j < intermidiate_states.size(); j++){
				new_prod = new_prod*intermidiate_states[j];
			}
			if(prod != new_prod){
				printf("Error in store %d\n",i);
				exit(-1);
			}
		}
	}else{

		vector<F> input(size*vectors);
		vector<F> intermidiate_states;
		read_chunk(fd,input,size*vectors);
		vector<F> prods(vectors,F(1));
		for(int j = 0; j < vectors; j++){
			for(int i = 0; i < size; i++){
				prods[j] = prods[j]*input[j*size + i];
			}
		}
		for(int i = 0; i < depth; i++){
			intermidiate_states.clear();
			intermidiate_states.resize(size*vectors/(1<<(i+1)));
			read_chunk(vfd[i],intermidiate_states,intermidiate_states.size());
			vector<F> new_prods(vectors,F(1));
			for(int k = 0; k < vectors; k++){
				for(int j = 0; j < intermidiate_states.size()/vectors; j++){
					new_prods[k] = new_prods[k]*intermidiate_states[k*intermidiate_states.size()/vectors + j];
				}
			}
			for(int j = 0; j < vectors; j++){
				if(new_prods[j] != prods[j]){
					printf("Error %d %d \n", i,j);
					exit(-1);
				}
			}
		}
	}


}


void generate_mul_tree_transcript_single(int fd, FILE *vfd[], int size){
	int depth = (int)log2(size);
	int _MAX_CHUNK = MAX_CHUNCK;
	if((int)log2(_MAX_CHUNK) > depth){
		_MAX_CHUNK = size;
	}
	printf("> %d\n",depth );
	vector<F> input(_MAX_CHUNK);
	vector<vector<F>> temp_buff((int)log2(_MAX_CHUNK));
		
	for(int i = 0; i < (int)log2(_MAX_CHUNK); i++){
		temp_buff[i].resize(_MAX_CHUNK/(1<<(i+1)));
	}
		
		int final_levels = depth - (int)log2(_MAX_CHUNK)+1;
		vector<vector<F>> final_buff(final_levels);
		vector<vector<F>> middle_buff(10);
		F prod = F(1);
		for(int i = 0; i < size/_MAX_CHUNK; i++){
			
			read_chunk(fd,input,_MAX_CHUNK);
			for(int j = 0; j < (int)log2(_MAX_CHUNK); j++){
				for(int k = 0; k < _MAX_CHUNK/(1<<(j+1)); k++){
					if(j == 0){
						temp_buff[j][k] = input[2*k]*input[2*k+1];
						prod = prod*input[2*k]*input[2*k+1];
		
					}else{

						temp_buff[j][k] = temp_buff[j-1][2*k]*temp_buff[j-1][2*k+1];
					}
				}
			}
			//printf("%d\n",temp_buff[temp_buff.size()-1].size());
			F num = temp_buff[temp_buff.size()-1][0];
			

			//prod = prod*num;
			for(int j = 0; j <  final_levels; j++){
				final_buff[j].push_back(num);
				if(final_buff[j].size()%2 == 1){
					break;
				}
				if(j == final_levels-1){
					printf("OK\n");
				}
				num = num*final_buff[j][final_buff[j].size()-2];
			}
			for(int j = 0; j < (int)log2(_MAX_CHUNK)-10; j++){
				write_file(temp_buff[j],vfd[j]);
			}
			int offset = (int)log2(_MAX_CHUNK)-10;
			for(int j = (int)log2(_MAX_CHUNK)-10; j < (int)log2(_MAX_CHUNK); j++){
				
				middle_buff[j-offset].insert(middle_buff[j-offset].end(),temp_buff[j].begin(),temp_buff[j].end());
				if(middle_buff[j-offset].size() >= 2048){
					write_file(middle_buff[j-offset],vfd[j]);
					middle_buff[j-offset].clear();
				}
			}
		}
	for(int i = 0; i < middle_buff.size(); i++){
		write_file(middle_buff[i],vfd[(int)log2(_MAX_CHUNK)-10 + i]);
	}
	
	for(int i = 0; i < final_buff.size()-1; i++){
		write_file(final_buff[i+1],vfd[(int)log2(_MAX_CHUNK)+ i]);	
	}
	
}



void generate_mul_tree_transcript(int fd, int vectors, int size){
	int depth = (int)log2(size);
	FILE *vfd[depth];
	for(int i = 0; i < depth; i++){
		string name = "mul_tree" + to_string(i);
		vfd[i] = fopen(name.c_str(),"w");
	}
	size_t total_size = (size_t)(vectors*size);
	
	if(vectors == 1){
		generate_mul_tree_transcript_single(fd, vfd, size);
	}else{
		vector<F> input(MAX_CHUNCK);
		
		int final_levels = depth - (int)log2(MAX_CHUNCK);
		printf("%d\n",final_levels );
		// In case the size of each instance is larger than the MAX_CHUNCK
		if(final_levels > 0){
		
			for(int i = 0; i < vectors; i++){
				generate_mul_tree_transcript_single(fd,vfd,size);
			}
		
		}else{
			
			vector<vector<F>> write_buff(depth);
			vector<vector<F>> temp_buff(depth);
			for(int i = 0; i < depth; i++){
				temp_buff[i].resize(size/(1<<(i+1)));
			}
			for(int i = 0; i < total_size/size; i++){
				read_chunk(fd,input,size);
				for(int j = 0; j < depth; j++){
					for(int k = 0; k < size/(1<<(j+1)); k++){
						if(j == 0){
							temp_buff[j][k] = input[2*k]*input[2*k+1];
						}else{
							temp_buff[j][k] = temp_buff[j-1][2*k]*temp_buff[j-1][2*k+1];
						}
					}
				}
				for(int j = 0; j < depth; j++){
					write_buff[j].insert(write_buff[j].end(),temp_buff[j].begin(),temp_buff[j].end());
				}
				for(int j = 0; j < depth; j++){
					if(write_buff[j].size() >= 4096){
						write_file(write_buff[j],vfd[j]);
						write_buff[j].clear();
					}
				}
			}

			for(int i = 0; i < write_buff.size(); i++){
				write_file(write_buff[i],vfd[i]);
				write_buff[i].clear();
			}
		}
	}
	for(int i = 0; i < depth; i++){
		fclose(vfd[i]);
	}
	//check_consistency(fd,  size, vectors);
}

// takes as input vectors x of equal size and for each 
// vector outputs Prod_i = x[0]*x[1]*x[2]...x[N]
mul_tree_proof_streaming prove_multiplication_tree_stream(int fd,int vectors,int size, F previous_r, vector<F> prev_x){
	
	// Initialize total input
	mul_tree_proof_streaming Proof;
	int depth = (int)log2(size);
	int vfd[depth];
		
	generate_mul_tree_transcript(fd,vectors,size);
	
	//proving_time

	auto t1 = chrono::high_resolution_clock::now();
    
    for(int i = 0; i < depth; i++){
		string name = "mul_tree" + to_string(i);
		vfd[i] = open(name.c_str(),O_RDWR);
	}

	//printf("Final prod len : %d\n",transcript[depth-1].size());
	proof_streaming P;
	if(vectors == 1){
		vector<F> r;
		vector<F> out(1);
		read_chunk(vfd[depth-1],out,1);
		previous_r = mimc_hash(previous_r,out[0]);
		
		//Proof.output = transcript[transcript.size()-1];

		F sum = out[0];
		//Proof.out_eval = sum;
		clock_t s,e;
		s = clock();
		for(int i = depth-1; i >= 0; i--){
			
			vector<F> beta;
			if(r.size() == 0){
				vector<F> in(2);
				read_chunk(vfd[depth-2],in,2);

				//Proof.in1 = in[0];
				//Proof.in2 = in[1];
				F num = mimc_hash(previous_r,in[0]);
				previous_r = mimc_hash(num,in[1]);		
				sum = (1-previous_r)*in[0]+(previous_r)*in[1];
				in.clear();
				r.push_back(previous_r);	
			}else{
			
				if(1<<r.size() <= MAX_CHUNCK){
					precompute_beta(r,beta);

					vector<F> in(1<<(depth - i));
					vector<F> in1(in.size()/2),in2(in.size()/2);
					
					//printf(">OK %d\n", in.size());
					
					if(i != 0){
						read_chunk(vfd[i-1],in,in.size());
						for(int i = 0; i < in.size()/2; i++){
							in1[i] = in[2*i];
							in2[i] = in[2*i + 1];
						}
						in.clear();
					}else{
						lseek(fd,0,SEEK_SET);

						read_chunk(fd,in,in.size());
						for(int i = 0; i < in.size()/2; i++){
							in1[i] = in[2*i];
							in2[i] = in[2*i + 1];
						}
					}
					//printf("OK %d\n",i);
					
					proof tP = _generate_3product_sumcheck_proof(in1, in2,beta,  previous_r);
					//Proof.proofs.push_back(P);
					if(sum != tP.c_poly[0].eval(F(1)) +  tP.c_poly[0].eval(F(0))){
						printf("error %d\n",i );
					}
					r = tP.randomness[0];
					//previous_r = generate_randomness(1,r[r.size()-1])[0];
					previous_r = tP.final_rand;
					//previous_r = mimc_hash(P.final_rand,P.vr[0]);
					//previous_r = mimc_hash(previous_r,P.vr[1]);
					sum = tP.vr[0]*(F(1) - previous_r) + tP.vr[1]*previous_r;
					
					beta.clear();
					in1.clear();
					in2.clear();
					r.insert(r.begin(),previous_r);

				}else{
					
					if(i != 0){
						P = generate_3product_sumcheck_proof_disk(vfd[i-1], -1, 1<<(depth - i -1), r, previous_r,SUM);
					}else{
						P = generate_3product_sumcheck_proof_disk(fd, -1, 1<<(depth - i -1), r, previous_r,SUM);	
					}
					if(sum + P.new_sum != P.P[0].c_poly[0].eval(F(1)) + P.P[0].c_poly[0].eval(F(0))){
						printf("Error in sum : %d\n", i);
						exit(-1);
					}
					r = P.P[1].randomness[0];
					r.insert(r.end(),P.P[0].randomness[0].begin(),P.P[0].randomness[0].end());
					previous_r = P.P[2].final_rand;
					sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
					r.insert(r.begin(),previous_r);
					//r = 
				}

			}
			//sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
		}
		e = clock();
		printf(">>Mul Tree time : %lf\n",(float)(e-s)/(float)CLOCKS_PER_SEC );
		Proof.final_r = r[r.size()-1];
		Proof.final_eval = sum;

		vector<F> individual_randomness;
		vector<F> global_randomness;
		
		for(int i = 0; i < (int)log2(size); i++){
			individual_randomness.push_back(r[r.size()-(int)log2(size)+i]);
		}
		Proof.individual_randomness = individual_randomness;
		for(int i = 0; i < r.size()-(int)log2(size); i++){
			global_randomness.push_back(r[i]);
		}
		Proof.global_randomness = global_randomness;
		Proof.r = r;
	}
	else{
		F initial_randomness = previous_r;
		vector<F> r;
		if(prev_x.size() == 0){
			r = generate_randomness((int)log2(vectors),previous_r); 	
		}else{
			r = prev_x;
		}
		F sum;

		if(vectors <= MAX_CHUNCK){
			vector<F> output(vectors);
			read_chunk(vfd[depth-1],output,vectors);
			sum = evaluate_vector(output,r);
		}
		else{
			sum = evaluate_vector_stream(vfd[depth-1], r, vectors);
		}
		//F output = transcript[depth-1];
		//vector<F> r;
		//if(prev_x.size() == 0){
		//	r = generate_randomness((int)log2(transcript[depth-1].size()),previous_r); 	
		//}else{
		//	r = prev_x;
		//}
		
		//F sum = evaluate_vector(transcript[depth-1],r);
		//Proof.out_eval = sum;
		vector<F> beta;
		if(prev_x.size() == 0){
			previous_r = mimc_hash(r[r.size()-1],sum);
		}
		clock_t s,e;
		s = clock();
		//precompute_beta(r,beta);
		for(int i = depth-1; i >= 0; i--){
			if(1<<r.size() <= MAX_CHUNCK){
				vector<F> in(vectors*(1<<(depth - i)));
				vector<F> in1(in.size()/2),in2(in.size()/2);
				
				if(i != 0){
					read_chunk(vfd[i-1],in,in.size());
					for(int i = 0; i < in.size()/2; i++){
						in1[i] = in[2*i];
						in2[i] = in[2*i + 1];
					}
					in.clear();
				}else{
					read_chunk(fd,in,in.size());
					for(int i = 0; i < in.size()/2; i++){
						in1[i] = in[2*i];
						in2[i] = in[2*i + 1];
					}
				}
				precompute_beta(r,beta);
				
				proof tP = _generate_3product_sumcheck_proof(in1, in2,beta,  previous_r);
				//Proof.proofs.push_back(tP);
				if(sum != tP.c_poly[0].eval(F(1)) +  tP.c_poly[0].eval(F(0))){
					printf("error %d\n",i );
				}
				r = tP.randomness[0];
				
				previous_r = tP.final_rand;
				
				sum = tP.vr[0]*(F(1) - previous_r) + tP.vr[1]*previous_r;
				beta.clear();
				r.insert(r.begin(),previous_r);
			}else{
				printf(">OK\n");
				if(i != 0){
					P = generate_3product_sumcheck_proof_disk(vfd[i-1], -1, vectors*(1<<(depth - i -1)), r, previous_r,SUM);
				}else{
					P = generate_3product_sumcheck_proof_disk(fd, -1, vectors*(1<<(depth - i -1)), r, previous_r,SUM);	
				}
				if(sum + P.new_sum != P.P[0].c_poly[0].eval(F(1)) + P.P[0].c_poly[0].eval(F(0))){
					printf("Error in sum : %d\n", i);
					exit(-1);
				}
				r = P.P[1].randomness[0];
				r.insert(r.end(),P.P[0].randomness[0].begin(),P.P[0].randomness[0].end());
				previous_r = P.P[2].final_rand;
				sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
				r.insert(r.begin(),previous_r);
					
			}
		
		}
		e = clock();
		printf("Mul Tree time : %lf\n",(float)(e-s)/(float)CLOCKS_PER_SEC );
		// Correctness verification
		Proof.final_r = r[r.size()-1];
		Proof.final_eval = sum;
		vector<F> individual_randomness;
		vector<F> global_randomness;
		
		for(int i = 0; i < (int)log2(size); i++){
			individual_randomness.push_back(r[i]);
		}
		Proof.individual_randomness = individual_randomness;
		for(int i = 0; i < r.size()-(int)log2(size); i++){
			global_randomness.push_back(r[i+(int)log2(size)]);
		}
		Proof.global_randomness = global_randomness;
		Proof.r = r;
	
	

	}
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    
	return Proof;
}




void streaming_sumcheck_partition_1(partition_SNARK_data_streaming data){

	int compress_vector_fd = open("compressed_input_fp",O_RDWR);
	int input_fd = open(data.input_data.file_name.c_str(),O_RDWR);
	int perm_input_fd = open(data.permuted_data.file_name.c_str(),O_RDWR);
	vector<F> prev_x;
	
	mul_tree_proof_streaming mP1 = prove_multiplication_tree_stream(compress_vector_fd, 2*data.input_data.row_size, data.input_data.col_size/2,F(0), prev_x);

	auto t1 = chrono::high_resolution_clock::now();
    
	mP1.r.pop_back();
	vector<F> r0 = mP1.r,r1 = mP1.r;
	r0.insert(r0.begin(),F(0));
	r1.insert(r1.begin(),F(1));
	vector<vector<F>> rand;rand.push_back(r0);rand.push_back(r1);
	int size = data.input_data.row_size*data.input_data.col_size;
	

	vector<F> input_eval = evaluate_vector_stream_batch(input_fd, rand, size);
	vector<F> perm_input_eval = evaluate_vector_stream_batch(perm_input_fd, rand, size);
	F temp_r = mimc_hash(mP1.final_r,input_eval[0]);
	temp_r = mimc_hash(temp_r,input_eval[1]);
	temp_r = mimc_hash(temp_r,perm_input_eval[0]);
	temp_r = mimc_hash(temp_r,perm_input_eval[1]);
	vector<F> agg_r = generate_randomness(2,temp_r);
	
	//vector<F> f(size);
	//lseek(input_fd,0,SEEK_SET);
	//read_chunk(input_fd,f,size);


	proof_streaming sP1 = generate_2product_sumcheck_proof_disk_beta(input_fd,rand,agg_r,size,agg_r[1]);
	

	if(sP1.sum != agg_r[0]*input_eval[0] + agg_r[1]*input_eval[1]){
		printf("Error in partition sumcheck 1\n");
		exit(-1);
	}
	proof_streaming sP2 = generate_2product_sumcheck_proof_disk_beta(perm_input_fd,rand,agg_r,size,agg_r[1]);
	if(sP2.sum != agg_r[0]*perm_input_eval[0] + agg_r[1]*perm_input_eval[1]){
		printf("Error in partition sumcheck 2\n");
		exit(-1);
	}
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    
	close(compress_vector_fd);
	close(input_fd);
	close(perm_input_fd);
}

void streaming_sumcheck_partition_2(partition_SNARK_data_streaming data, vector<vector<F>> Tree){
	pad_vector_with_num(data.compressed_tree,F(1));
	
	vector<F> powers;
	for(int i = 0; i < data.compressed_tree.size(); i++){
		powers.push_back(data.compressed_tree[i]);
		F prev = data.compressed_tree[i];
		for(int j = 1; j < 32; j++){
			powers.push_back(prev*prev);
			prev = prev*prev;
		}
	}


	// streaming_partition_sumcheck_1(data.input_data,data.permuted_data,compress_vector,c);
	vector<F> prev_x;
	int compressed_path_fd = open("compressed_path_fp",O_RDWR);
	int fd_paths = open(data.paths.file_name.c_str(),O_RDWR);
	int fd_aux_paths = open(data.paths_aux.file_name.c_str(),O_RDWR);
	

	mul_tree_proof_streaming mP1 = prove_multiplication_tree_stream(compressed_path_fd, 1, data.paths.row_size,F(0), prev_x);
 	vector<int> fds;fds.push_back(fd_paths);fds.push_back(fd_aux_paths);
	vector<size_t> fd_cols;fd_cols.push_back(data.paths.col_size);fd_cols.push_back(2);
	vector<size_t> fd_size;fd_size.push_back(data.paths.row_size*data.paths.col_size);fd_size.push_back(2*data.paths.row_size);

	auto t1 = chrono::high_resolution_clock::now();
    
	vector<F> compressed_col = prepare_matrix_streaming(fds,fd_cols,fd_size,data.paths.row_size, mP1.r, 2 + data.paths.col_size);
	
	pad_vector(compressed_col);pad_vector(data.tree_compress_vector);
	proof sP1 = generate_2product_sumcheck_proof(compressed_col,data.tree_compress_vector,mP1.final_r);
	if(sP1.q_poly[0].eval(0) + sP1.q_poly[0].eval(1) != mP1.final_eval-F(1)){
		printf("Error in partition sumcheck 2\n");
		exit(-1);
	}
	
	
	
	vector<vector<F>> final_powers_tree_input;
	vector<F> final_powers(powers.size()/32);
	vector<vector<F>> mul_tree_input;
	vector<F> final_powers_input;
	
	// Compute the path exponents
	for(int i = 0; i < powers.size()/32; i++){
		vector<F> temp(32);
		final_powers[i] = F(1);
		for(int j = 0; j < 32; j++){
			final_powers_input.push_back(powers[i*32+j]*data.power_bits[i*32+j]);
			temp[j] = (F(1)-data.power_bits[i*32+j]) + powers[i*32+j]*data.power_bits[i*32+j];
			final_powers[i] *= temp[j];
		}
		final_powers_tree_input.push_back(temp);
	}
	
	mul_tree_input.clear();
	mul_tree_input.push_back(final_powers);
	
	mul_tree_proof mP2 = prove_multiplication_tree(mul_tree_input,mP1.final_r,prev_x);
	
	mul_tree_input = final_powers_tree_input;
	printf("%d\n",final_powers_tree_input.size() );
	mul_tree_proof mP3 = prove_multiplication_tree(mul_tree_input,mP2.individual_randomness[mP2.individual_randomness.size()-1],mP2.final_r);
	
	vector<F> r = mP3.individual_randomness;
	for(int i = 0; i < mP3.global_randomness.size(); i++){
		r.push_back(mP3.global_randomness[i]);
	}
	F eval_bits1 = evaluate_vector(data.power_bits,r);
	F final_powers_input_eval = evaluate_vector(final_powers_input,r);
	
	//P.eval_bits1 = eval_bits1;
	//P.final_powers_input_eval = final_powers_input_eval;
	//P.eval_bits1_x = r;
	//P.final_powers_input_eval_x = r;

	if(mP3.final_eval != F(1)-eval_bits1 + final_powers_input_eval){
		printf("Error in partition sumcheck 2--2\n");
		exit(-1);
	}

	vector<F> beta;
	precompute_beta(r,beta);

	F rand = mimc_hash(mP3.individual_randomness[mP3.individual_randomness.size()-1],eval_bits1);
	rand = mimc_hash(rand,final_powers_input_eval);	

	vector<F> temp_powers = powers;
	proof tP1 = _generate_3product_sumcheck_proof(data.power_bits,temp_powers,beta,rand);
	if(tP1.c_poly[0].eval(0) + tP1.c_poly[0].eval(1) != final_powers_input_eval){
		printf("Error in partition sumcheck 2--3\n");
		exit(-1);
	}
	F eval_bits2 = tP1.vr[0];
	F eval_powers1 = tP1.vr[1];
	vector<F> eval_powers1_x = tP1.randomness[0];
	// Check power consistency with compressed tree
	

	vector<F> eval_tree_x = generate_randomness((int)log2(data.compressed_tree.size()),tP1.final_rand);
	vector<F> eval_powers2_x(5,F(0));
	eval_powers2_x.insert(eval_powers2_x.end(),eval_tree_x.begin(),eval_tree_x.end());
	
	F eval_powers2 = evaluate_vector(powers,eval_powers2_x);
	F eval_tree = evaluate_vector(data.compressed_tree,eval_tree_x);
	if(eval_powers2 != eval_tree){
		printf("Error in partition sumcheck 2--4\n");
		exit(-1);
	}

	
	rand = mimc_hash(eval_tree_x[eval_tree_x.size()-1],eval_powers2);

	vector<vector<F>> padded_tree(Tree.size());
	pad_vector(data.tree_compress_vector);
	for(int i = 0; i < padded_tree.size(); i++){
		int j;
		padded_tree[i].resize(data.tree_compress_vector.size(),F(0));
		for(j = 0; j < Tree[i].size()-2; j++){
			padded_tree[i][j] = Tree[i][j];
		}
		padded_tree[i][data.paths.col_size] = Tree[i][j];
		padded_tree[i][data.paths.col_size + 1] = Tree[i][j+1];
	}
	pad_matrix(padded_tree);
	
	proof sP2 = _prove_matrix2vector(padded_tree,data.tree_compress_vector,eval_tree_x,eval_tree-F(1),rand);
	
	// Check power consistency
	F gamma = sP2.final_rand;
	vector<F> gamma_subvector1(32),gamma_subvector2(32);
	vector<F> gamma_vector1,gamma_vector2;
	gamma_subvector1[0] = F(0);
	gamma_subvector1[1] = gamma;
	gamma_subvector2[0] = gamma;
	gamma_subvector2[1] = gamma*gamma;
	for(int i = 2; i < 32; i++){
		gamma_subvector1[i] = gamma_subvector1[i-1]*gamma;
		gamma_subvector2[i] = gamma_subvector2[i-1]*gamma;	
	}
	gamma_subvector2[31] = F(0);
	for(int i = 0; i < powers.size()/32; i++){
		gamma_vector1.insert(gamma_vector1.end(),gamma_subvector1.begin(),gamma_subvector1.end());
		gamma_vector2.insert(gamma_vector2.end(),gamma_subvector2.begin(),gamma_subvector2.end());
	}
	F sum1 = F(0);
	for(int i = 0; i < gamma_vector2.size(); i++){
		sum1 += gamma_vector2[i]*powers[i]*powers[i];
	}
	
	temp_powers = powers;
	vector<F> temp_powers2 = powers;
	proof tP2 = _generate_3product_sumcheck_proof(gamma_vector2,temp_powers,temp_powers2,mimc_hash(gamma,sum1));
	//F sum1 = P.tP2.c_poly[0].eval(0) + P.tP2.c_poly[0].eval(1);
	F eval_powers3 = tP2.vr[1];
	

	vector<F> eval_powers3_x = tP2.randomness[0];
	temp_powers = powers;
	proof sP3 = generate_2product_sumcheck_proof(gamma_vector1,temp_powers,tP2.final_rand);
	F sum2 = sP3.q_poly[0].eval(0) +sP3.q_poly[0].eval(1); 
	if(sum1 != sum2){
		printf("Error in partition sumcheck 2--5\n");
		exit(-1);
	}
	
	F eval_powers4 = sP3.vr[1];
	vector<F> eval_powers4_x = sP3.randomness[0];
	
	vector<F> aggr_beta(1ULL<<eval_powers1_x.size()),beta1,beta2,beta3,beta4;
	

	precompute_beta(eval_powers1_x,beta1);
	precompute_beta(eval_powers2_x,beta2);
	precompute_beta(eval_powers3_x,beta3);
	precompute_beta(eval_powers4_x,beta4);

	r = generate_randomness(4,sP3.final_rand);

	for(int i = 0; i < aggr_beta.size(); i++){
		aggr_beta[i] = r[0]*beta1[i] + r[1]*beta2[i] +r[2]*beta3[i] + r[3]*beta4[i];
	}
	proof sP4 = generate_2product_sumcheck_proof(aggr_beta,powers,r[3]);
	if(sP4.q_poly[0].eval(F(0)) + sP4.q_poly[0].eval(F(1)) != r[0]*eval_powers1 + r[1]*eval_powers2 +r[2]*eval_powers3 + r[3]*eval_powers4){
		printf("Error in partition sumcheck 2--6\n");
		exit(-1);	
	}
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    
	close(compressed_path_fd);
	close(fd_paths);
	close(fd_aux_paths);


}

void streaming_sumcheck_partition_3(partition_SNARK_data_streaming data, vector<vector<F>> Tree){
	int fd_diff = open(data.diff_data.file_name.c_str(),O_RDWR);
	int comp11 = open("inference_data_1",O_RDWR);
	int comp12 = open("inference_data_2",O_RDWR);
	int comp1 = open("inference_data_3",O_RDWR);
	int comp2 = open("inference_data_4",O_RDWR);
	int fd_paths = open(data.paths.file_name.c_str(),O_RDWR);
	int permuted_data_fd = open(data.permuted_data.file_name.c_str(),O_RDWR);
	int bits_fd = open(data.bit_vectors.file_name.c_str(),O_RDWR);
	
	auto t1 = chrono::high_resolution_clock::now();
    
	vector<F> r = generate_randomness((int)log2(data.diff_data.size),F(0));
	F diff_eval = evaluate_vector_stream(fd_diff,r,data.diff_data.size);
	

	int q = (int)log2(bin_size);
	if(1 << ((int)log2(q)) != q){
		q = 1 << (((int)log2(q))+1);
	}
	
	_prove_bit_decomposition_stream(bits_fd, data.bit_vectors.size, r, diff_eval, r[r.size()-1], q);


	proof_streaming P1 = generate_3product_sumcheck_proof_disk(comp1,comp2,data.diff_data.size , r, F(0), 2);
	proof_streaming P2 = generate_3product_sumcheck_proof_disk(comp11,comp12, data.diff_data.size, P1.randomness, P1.P[2].final_rand,2 );
	vector<F> path_x1 = P1.randomness,path_x2 = P2.randomness,path_x3 = P2.randomness;
	path_x1.insert(path_x1.begin(),F(1));path_x1.insert(path_x1.begin(),F(0));
	path_x2.insert(path_x2.begin(),F(0));path_x2.insert(path_x2.begin(),F(0));
	path_x3.insert(path_x3.begin(),F(1));path_x3.insert(path_x3.begin(),F(0));
	vector<vector<F>> path_x;path_x.push_back(path_x1);path_x.push_back(path_x2);path_x.push_back(path_x3);

	vector<F> eval_path = evaluate_vector_stream_batch(fd_paths,path_x,data.paths.row_size*data.paths.col_size);
	vector<F> permuted_data_x = P2.randomness;
	permuted_data_x.insert(permuted_data_x.begin(),F(1));
	F permuted_data_eval = evaluate_vector_stream(permuted_data_fd,permuted_data_x,data.permuted_data.col_size*data.permuted_data.row_size);
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    
	close(fd_diff);
	close(comp11);
	close(comp12);
	close(comp1);
	close(comp2);
	close(fd_paths);
	close(permuted_data_fd);
}


void streaming_sumcheck_leaves_1(histogram_SNARK_data_streaming data, int Attr, F previous_r){
	int read_write_fd = open("read_write_compressed",O_RDWR);
	int read_transcript_fd = open(data.read_transcript.file_name.c_str(),O_RDWR);
	int write_transcript_fd = open(data.write_transcript.file_name.c_str(),O_RDWR);
	vector<F> prev_x;
	mul_tree_proof_streaming mP1 = prove_multiplication_tree_stream(read_write_fd, 2, data.read_transcript.row_size, previous_r, prev_x);
	vector<F> x = mP1.individual_randomness;
	auto t1 = chrono::high_resolution_clock::now();
    
	lseek(read_write_fd,0,SEEK_SET);
	F eval_read_tr = evaluate_vector_stream(read_write_fd,x,data.read_transcript.row_size);
	F eval_write_tr = evaluate_vector_stream(read_write_fd,x,data.write_transcript.row_size);
	if((F(1)-mP1.global_randomness[0])*eval_read_tr + mP1.global_randomness[0]*eval_write_tr != mP1.final_eval){
		printf("Error in histograms sumcheck 1\n");
		exit(-1);
	}
	vector<int> fd;fd.push_back(read_transcript_fd);
	vector<size_t> fd_cols; fd_cols.push_back(8);
	vector<size_t> fd_size; fd_size.push_back(data.read_transcript.row_size*8);

	vector<F> evals_read = prepare_matrix_streaming(fd, fd_cols, fd_size, data.read_transcript.row_size, x, 8);
	fd.clear();fd_cols.clear();fd_size.clear();
	fd.push_back(write_transcript_fd);fd_cols.push_back(8);fd_size.push_back(data.read_transcript.row_size*8);
	vector<F> evals_write = prepare_matrix_streaming(fd, fd_cols, fd_size, data.read_transcript.row_size, x, 8);
	F sum = F(0);
	for(int i = 0; i < evals_read.size(); i++){
		sum += data.random_vector[i]*evals_read[i];
	}
	if(sum != eval_read_tr - F(1)){
		printf("Error in histograms sumcheck 2\n");
		exit(-1);
	}
	sum = F(0);
	for(int i = 0; i < evals_write.size(); i++){
		sum += data.random_vector[i]*evals_write[i];
	}
	if(sum != eval_write_tr - F(1)){
		printf("Error in histograms sumcheck 3\n");
		exit(-1);
	}
	vector<vector<F>> mul_tree_input(2);
	
	mul_tree_input[0] = data.compressed_init;
	mul_tree_input[1] = data.compressed_final;
	mul_tree_proof mP2 = prove_multiplication_tree(mul_tree_input,previous_r,prev_x);

	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    

	close(read_write_fd);
	close(read_transcript_fd);
	close(write_transcript_fd);
}

void streaming_sumcheck_leaves_2(histogram_SNARK_data_streaming data, int Attr, F previous_r){

	int read_transcript_fd = open(data.read_transcript.file_name.c_str(),O_RDWR);
	int write_transcript_fd = open(data.write_transcript.file_name.c_str(),O_RDWR);
	int input_fd = open(data.input_data.file_name.c_str(),O_RDWR);
	int input_aux_fd = open(data.input_aux.file_name.c_str(),O_RDWR);
	vector<F> x = generate_randomness((int)log2(data.read_transcript.row_size),F(0));
	//printf(">> %d\n",P.P1.sP3.randomness[0].size() );
	
	vector<F> x0_metadata,x1_metadata;
	vector<F> x0_input = x,x1_input = x;
	vector<vector<F>> x_input_acc,x_metadata_acc;
	vector<F> x0_readwrite,x1_readwrite,x2_readwrite,x3_readwrite,x4_readwrite;
	x0_input.insert(x0_input.begin(), F(0));
	x1_input.insert(x1_input.begin(), F(1));
	x0_metadata.push_back(F(0));
	x1_metadata.push_back(F(1));
	vector<F> metadata_randomness;
	for(int i = x.size() - (int)log2(data.input_aux.row_size); i < x.size(); i++){
		x0_metadata.push_back(x[i]);
		x1_metadata.push_back(x[i]);	
		metadata_randomness.push_back(x[i]);
	}

	x_input_acc.push_back(x0_input);x_input_acc.push_back(x1_input);
	x_metadata_acc.push_back(x0_metadata);x_metadata_acc.push_back(x1_metadata);

	x0_readwrite.push_back(F(0));x0_readwrite.push_back(F(0));x0_readwrite.push_back(F(0));
	x1_readwrite.push_back(F(1));x1_readwrite.push_back(F(0));x1_readwrite.push_back(F(0));
	x2_readwrite.push_back(F(0));x2_readwrite.push_back(F(1));x2_readwrite.push_back(F(0));
	x3_readwrite.push_back(F(1));x3_readwrite.push_back(F(1));x3_readwrite.push_back(F(0));
	x4_readwrite.push_back(F(0));x4_readwrite.push_back(F(0));x4_readwrite.push_back(F(1));
	x0_readwrite.insert(x0_readwrite.end(),x.begin(),x.end());
	x1_readwrite.insert(x1_readwrite.end(),x.begin(),x.end());
	x2_readwrite.insert(x2_readwrite.end(),x.begin(),x.end());
	x3_readwrite.insert(x3_readwrite.end(),x.begin(),x.end());
	x4_readwrite.insert(x4_readwrite.end(),x.begin(),x.end());
	vector<vector<F>> x_acc;x_acc.push_back(x0_readwrite);x_acc.push_back(x1_readwrite);x_acc.push_back(x2_readwrite);
	x_acc.push_back(x3_readwrite);x_acc.push_back(x4_readwrite);

	auto t1 = chrono::high_resolution_clock::now();
    
	vector<F> read_evals = evaluate_vector_stream_batch(read_transcript_fd,x_acc,data.read_transcript.col_size*data.read_transcript.row_size);
	
	vector<F> write_evals = evaluate_vector_stream_batch(write_transcript_fd,x_acc,data.read_transcript.col_size*data.read_transcript.row_size);
	
	vector<F> input_evals = evaluate_vector_stream_batch(input_fd,x_input_acc,data.input_data.row_size*data.input_data.col_size);
	
	vector<F> aux_evals = evaluate_vector_stream_batch(input_aux_fd,x_metadata_acc,data.input_aux.row_size*data.input_aux.col_size);
	
	if(input_evals[0] != read_evals[1] || input_evals[0] != write_evals[1]){
		printf("Error leaves_sumcheck 2---1\n");
		exit(-1);
	}
	if(input_evals[1] != read_evals[2] || input_evals[1] != write_evals[2]){
		printf("Error leaves_sumcheck 2---2\n");
		exit(-1);
	}
	// Error will be thrown if attributes are not power of 2
	if(aux_evals[0] != read_evals[0] || aux_evals[0] != write_evals[0]){
		printf("Error leaves_sumcheck 2---3\n");
		exit(-1);	
	}
	if(aux_evals[1] != read_evals[3] || aux_evals[1] != write_evals[3]){
		printf("Error leaves_sumcheck 2---4\n");
		exit(-1);	
	}
	if(write_evals[4] - read_evals[4] - F(1) != F(0)){
		printf("Error leaves_sumcheck 2---5\n");
		exit(-1);
	}

	lseek(read_transcript_fd, 0, SEEK_SET);
	lseek(write_transcript_fd, 0, SEEK_SET);
	lseek(input_fd, 0, SEEK_SET);
	lseek(input_aux_fd, 0, SEEK_SET);
	
	previous_r = chain_hash(chain_hash(chain_hash(chain_hash(x[x.size()-1],aux_evals),input_evals),read_evals),write_evals);

	vector<F> r1 = generate_randomness(4,previous_r);
	vector<F> r2 = generate_randomness(2,r1[r1.size()-1]);
	generate_2product_sumcheck_proof_disk_beta(read_transcript_fd, x_acc, r1,data.read_transcript.col_size*data.read_transcript.row_size, r2[r2.size()-1]);
	generate_2product_sumcheck_proof_disk_beta(write_transcript_fd, x_acc, r1,data.read_transcript.col_size*data.read_transcript.row_size, r2[r2.size()-1]);
	generate_2product_sumcheck_proof_disk_beta(input_fd, x_input_acc, r2,data.input_data.row_size*data.input_data.col_size, r2[r2.size()-1]);
	generate_2product_sumcheck_proof_disk_beta(input_aux_fd, x_metadata_acc, r2, data.input_aux.row_size*data.input_aux.col_size , r2[r2.size()-1]);
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    
	close(read_transcript_fd);
	close(write_transcript_fd);
	close(input_fd);
	close(input_aux_fd);

}
*/
