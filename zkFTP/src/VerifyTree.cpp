#include "config_pc.hpp"

#include "mimc.h"
#include "utils.hpp"
#include "sumcheck.h"
#include <chrono>
#include "quantization.h"
#include "VerifyTree.h"
#include "BuildTree.h"

using namespace std::chrono;

extern int threads;
extern int bin_size;
extern double range_proof_verification_time;
extern int range_proof_size;

F compute_beta_point(vector<F> r1, vector<F> r2){
	F prod = F(1);
	for(int i = 0; i < r1.size(); i++){
		prod *= (r1[i]*r2[i] + (F(1)-r1[i])*(F(1)-r2[i]));
	}	
	return prod;
}





F verify_gkr(struct proof P, gkr_proof_indexes &IP, F sum, F previous_r, vector<F> &x, vector<F> &y){
	char buff[256];
	
	F rand = previous_r;

	int layers = ((P.randomness).size()-1)/3;
	
	//F temp_sum = F(P.q_poly[0].eval(0) + P.q_poly[0].eval(1));
	int counter = 1;
	int poly_counter = 0;
	IP.layers = layers;
	vector<vector<int>> poly;
	vector<int> randomness;

	IP.sumcheck.resize(3*layers);
	for(int i = 0; i < layers; i++){
		poly.clear();
		poly.resize(P.randomness[counter].size());
		randomness.clear();
		for(int j = 0; j < P.randomness[counter].size(); j++){
			//printf("%d\n",j );
			if(sum != P.q_poly[poly_counter].eval(0) + P.q_poly[poly_counter].eval(1)){
				printf("Error in sumcheck 1 %d %d\n",i,j );
				exit(-1);
			}

			randomness.push_back(x.size());
			x.push_back(rand);
			x.push_back(P.q_poly[poly_counter].a);
			poly[j].push_back(x.size()-1);
			rand = mimc_hash(rand,P.q_poly[poly_counter].a);
			y.push_back(rand);
			x.push_back(rand);
			x.push_back(P.q_poly[poly_counter].b);
			poly[j].push_back(x.size()-1);
			rand = mimc_hash(rand,P.q_poly[poly_counter].b);
			y.push_back(rand);
			x.push_back(rand);
			x.push_back(P.q_poly[poly_counter].c);
			poly[j].push_back(x.size()-1);
			rand = mimc_hash(rand,P.q_poly[poly_counter].c);
			y.push_back(rand);
			sum = P.q_poly[poly_counter].eval(rand);
			poly_counter += 1;
		}
		
		IP.sumcheck[counter-1].polynomials = poly;
		IP.sumcheck[counter-1].randomness = randomness;
		poly.clear();
		counter += 1;
		poly.resize(P.randomness[counter].size());
		randomness.clear();
		for(int j = 0; j < P.randomness[counter].size(); j++){
			if(sum != P.q_poly[poly_counter].eval(0) + P.q_poly[poly_counter].eval(1)){
				printf("Error in sumcheck 2 %d\n",i );
				exit(-1);
			}
			randomness.push_back(x.size());
			x.push_back(rand);
			x.push_back(P.q_poly[poly_counter].a);
			poly[j].push_back(x.size()-1);
			rand = mimc_hash(rand,P.q_poly[poly_counter].a);
			y.push_back(rand);
			x.push_back(rand);
			x.push_back(P.q_poly[poly_counter].b);
			poly[j].push_back(x.size()-1);
			rand = mimc_hash(rand,P.q_poly[poly_counter].b);
			y.push_back(rand);
			x.push_back(rand);
			x.push_back(P.q_poly[poly_counter].c);
			poly[j].push_back(x.size()-1);
			rand = mimc_hash(rand,P.q_poly[poly_counter].c);
			y.push_back(rand);	
			
			sum = P.q_poly[poly_counter].eval(rand);
			poly_counter += 1;
			
		}
		sum = F(0);
		
		for(int j = 0; j < P.sig[i].size(); j++){
			sum += P.sig[i][j]*P.final_claims_v[i][j];
		}
		x.push_back(rand);
		x.push_back(sum);
		IP.sums.push_back(x.size()-1);
		rand = mimc_hash(rand,sum);
		y.push_back(rand);			
		IP.sumcheck[counter-1].polynomials = poly;
		IP.sumcheck[counter-1].randomness = randomness;
		counter += 1;

		poly.clear();
		poly.resize(P.randomness[counter].size());
		randomness.clear();
		

		for(int j = 0; j < P.randomness[counter].size(); j++){
			if(sum != P.q_poly[poly_counter].eval(0) + P.q_poly[poly_counter].eval(1)){
				printf("Error in sumcheck 3 %d\n",i );
				exit(-1);
			}
			randomness.push_back(x.size());
			x.push_back(rand);
			x.push_back(P.q_poly[poly_counter].a);
			poly[j].push_back(x.size()-1);
			rand = mimc_hash(rand,P.q_poly[poly_counter].a);
			y.push_back(rand);
			x.push_back(rand);
			x.push_back(P.q_poly[poly_counter].b);
			poly[j].push_back(x.size()-1);
			rand = mimc_hash(rand,P.q_poly[poly_counter].b);
			y.push_back(rand);
			x.push_back(rand);
			x.push_back(P.q_poly[poly_counter].c);
			poly[j].push_back(x.size()-1);
			rand = mimc_hash(rand,P.q_poly[poly_counter].c);
			y.push_back(rand);	
		
			sum = P.q_poly[poly_counter].eval(rand);
			poly_counter += 1;
			
		}

		x.push_back(rand);
		x.push_back(P.vr[i]);
		IP.vr.push_back(x.size()-1);
		rand = mimc_hash(rand,P.vr[i]);
		y.push_back(rand);
		x.push_back(rand);
		x.push_back(P.gr[i]);
		IP.gr.push_back(x.size()-1);
		rand = mimc_hash(rand,P.gr[i]);
		y.push_back(rand);
		
		if(sum != P.vr[i]*P.gr[i]){
			printf("Error in final check %d\n",i);
			exit(-1);
		}
		sum = P.vr[i];
		
		IP.sumcheck[counter-1].polynomials = poly;
		IP.sumcheck[counter-1].randomness = randomness;
		counter+=1;
	}
	return rand;
}

F verify_3prod_sumcheck(proof P, sumcheck3Prod &IP, F sum, F previous_r, vector<F> &x, vector<F> &y){
	F rand = previous_r;
	IP.polynomials.resize(P.c_poly.size());
	
	for(int i = 0; i < P.c_poly.size(); i++){
		if(sum != P.c_poly[i].eval(F(1))+P.c_poly[i].eval(F(0))){
			printf("Error in 3prod sumcheck 1, %d\n",i);
			exit(-1);
		}
		sum = P.c_poly[i].eval(rand);
		IP.randomness.push_back(x.size());
		x.push_back(rand);
		x.push_back(P.c_poly[i].a);
		IP.polynomials[i].push_back(x.size()-1);
		rand = mimc_hash(rand,P.c_poly[i].a);
		y.push_back(rand);
		x.push_back(rand);
		x.push_back(P.c_poly[i].b);
		IP.polynomials[i].push_back(x.size()-1);
		rand = mimc_hash(rand,P.c_poly[i].b);
		y.push_back(rand);
		x.push_back(rand);
		x.push_back(P.c_poly[i].c);
		IP.polynomials[i].push_back(x.size()-1);
		rand = mimc_hash(rand,P.c_poly[i].c);
		y.push_back(rand);
		x.push_back(rand);
		x.push_back(P.c_poly[i].d);
		IP.polynomials[i].push_back(x.size()-1);
		rand = mimc_hash(rand,P.c_poly[i].d);
		y.push_back(rand);
	}
	x.push_back(rand);
	x.push_back(P.vr[0]);
	IP.vr.push_back(x.size()-1);
	rand = mimc_hash(rand,P.vr[0]);
	y.push_back(rand);
	x.push_back(rand);
	x.push_back(P.vr[1]);
	IP.vr.push_back(x.size()-1);
	rand = mimc_hash(rand,P.vr[1]);
	y.push_back(rand);
	
	if(sum != P.vr[0]*P.vr[1]*P.vr[2]){
		printf("Error in 3prodsumcheck 2\n");
		exit(-1);
	}
	return rand;
}


F verify_2prod_sumcheck(proof P, sumcheck2Prod &IP, F sum, F previous_r, vector<F> &x, vector<F> &y){
	F rand = previous_r;
	IP.polynomials.resize(P.q_poly.size());
	
	for(int i = 0; i < P.q_poly.size(); i++){
		if(sum != P.q_poly[i].eval(F(1))+P.q_poly[i].eval(F(0))){
			printf("Error in 2prod sumcheck 1, %d\n",i);
			exit(-1);
		}
		IP.randomness.push_back(x.size());		
		sum = P.q_poly[i].eval(rand);
		x.push_back(rand);
		x.push_back(P.q_poly[i].a);
		IP.polynomials[i].push_back(x.size()-1);
		rand = mimc_hash(rand,P.q_poly[i].a);
		y.push_back(rand);
		x.push_back(rand);
		x.push_back(P.q_poly[i].b);
		IP.polynomials[i].push_back(x.size()-1);
		rand = mimc_hash(rand,P.q_poly[i].b);
		y.push_back(rand);
		x.push_back(rand);
		x.push_back(P.q_poly[i].c);
		IP.polynomials[i].push_back(x.size()-1);
		rand = mimc_hash(rand,P.q_poly[i].c);
		y.push_back(rand);
	}
	x.push_back(rand);
	x.push_back(P.vr[0]);
	IP.vr.push_back(x.size()-1);
	rand = mimc_hash(rand,P.vr[0]);
	y.push_back(rand);
	x.push_back(rand);
	x.push_back(P.vr[1]);
	IP.vr.push_back(x.size()-1);
	rand = mimc_hash(rand,P.vr[1]);
	y.push_back(rand);

	if(sum != P.vr[0]*P.vr[1]){
		printf("Error in multree 2\n");
		exit(-1);
	}
	return rand;
}


F verify_multiplication_tree(mul_tree_proof P, MulTree_indexes &IP,F previous_r,vector<F> previous_x,vector<F> &x, vector<F> &y){
	F rand;
	if(P.output.size() == 1){
		vector<F> r;// = generate_randomness_verify((int)log2(P.output.size()),previous_r,x,y);
		F sum = P.out_eval;
		x.push_back(previous_r);
		x.push_back(P.out_eval);
		IP.initial_sum = x.size()-1;
		previous_r = mimc_hash(previous_r,P.out_eval);
		y.push_back(previous_r);
		rand = previous_r;

			x.push_back(previous_r);
			x.push_back(P.in1);
			IP.in.push_back(x.size()-1);
			previous_r = mimc_hash(previous_r,P.in1);
			y.push_back(previous_r);
			x.push_back(previous_r);
			x.push_back(P.in2);
			IP.in.push_back(x.size()-1);
			previous_r = mimc_hash(previous_r,P.in2);
			y.push_back(previous_r);
			if(sum != P.in1*P.in2){
				printf("Error in mul tree sumcheck 1\n");
				exit(-1);
			}
			rand = previous_r;
			
			sum = (1-previous_r)*P.in1+(previous_r)*P.in2;
			r.push_back(rand);

			IP.randomness.resize(P.proofs.size()+1);
			IP.polynomials.resize(P.proofs.size());
			IP.randomness[0].push_back(x.size());
		
			
			for(int i = 0; i < P.proofs.size(); i++){
				IP.polynomials[i].resize(P.proofs[i].c_poly.size());
				for(int j = 0; j < P.proofs[i].c_poly.size(); j++){
					
					if(sum != P.proofs[i].c_poly[j].eval(0)+P.proofs[i].c_poly[j].eval(1)){
						printf("Error in multree 1 %d,%d\n",i,j);
						exit(-1);
					}
					
					sum = P.proofs[i].c_poly[j].eval(rand);
					if(P.proofs[i].randomness[0][j] != rand){
						printf("Error\n");
					}
					
					IP.randomness[i+1].push_back(x.size());
					x.push_back(rand);
					x.push_back(P.proofs[i].c_poly[j].a);
					IP.polynomials[i][j].push_back(x.size()-1);
					rand = mimc_hash(rand,P.proofs[i].c_poly[j].a);
					y.push_back(rand);
					x.push_back(rand);
					x.push_back(P.proofs[i].c_poly[j].b);
					IP.polynomials[i][j].push_back(x.size()-1);
					rand = mimc_hash(rand,P.proofs[i].c_poly[j].b);
					y.push_back(rand);
					x.push_back(rand);
					x.push_back(P.proofs[i].c_poly[j].c);
					IP.polynomials[i][j].push_back(x.size()-1);
					rand = mimc_hash(rand,P.proofs[i].c_poly[j].c);
					y.push_back(rand);
					x.push_back(rand);
					x.push_back(P.proofs[i].c_poly[j].d);
					IP.polynomials[i][j].push_back(x.size()-1);
					rand = mimc_hash(rand,P.proofs[i].c_poly[j].d);
					y.push_back(rand);

				}


				if(sum != P.proofs[i].vr[0]*P.proofs[i].vr[1]*P.proofs[i].vr[2]){
					printf("Error in multree 2, %d\n",i);
					exit(-1);
				}
				x.push_back(rand);
				x.push_back(P.proofs[i].vr[0]);
				IP.vr.push_back(x.size()-1);
				rand = mimc_hash(rand,P.proofs[i].vr[0]);
				y.push_back(rand);
				x.push_back(rand);
				x.push_back(P.proofs[i].vr[1]);
				IP.vr.push_back(x.size()-1);
				rand = mimc_hash(rand,P.proofs[i].vr[1]);
				y.push_back(rand);
				IP.randomness[i+1].push_back(x.size());
				IP.rand.push_back(x.size());
				sum = P.proofs[i].vr[0]*(F(1) - rand) + P.proofs[i].vr[1]*rand;

				if(P.proofs[i].vr[2] != compute_beta_point(P.proofs[i].randomness[0],r)){
					printf("Error in multree 3\n");
					exit(-1);
				}
				r = P.proofs[i].randomness[0];
				
				r.push_back(rand);
				
			}
			IP.individual_randomness = IP.randomness[IP.randomness.size()-1];
	
	}else{
		vector<F> r;
	
		if(previous_x.size() == 0){

			for(int i = 0; i < (int)log2(P.output.size()); i++ ){
				IP.first_r.push_back(x.size() + 2 + 2*i);
			}
			r = generate_randomness_verify((int)log2(P.output.size()),previous_r,x,y);
			x.push_back(r[r.size()-1]);
			x.push_back(P.out_eval);
			IP.initial_sum = x.size()-1;
			previous_r = mimc_hash(r[r.size()-1],P.out_eval);
			y.push_back(previous_r);
		}else{
			r = previous_x;
		}
		F sum = P.out_eval;
		
		rand = previous_r;
		IP.randomness.resize(P.proofs.size());
		IP.polynomials.resize(P.proofs.size());
		//IP.randomness[0].push_back(x.size());
		for(int i = 0; i < P.proofs.size(); i++){
			IP.polynomials[i].resize(P.proofs[i].c_poly.size());
			for(int j = 0; j < P.proofs[i].c_poly.size(); j++){
				
				if(sum != P.proofs[i].c_poly[j].eval(0)+P.proofs[i].c_poly[j].eval(1)){
					printf("Error in multree 1 %d,%d\n",i,j);
					exit(-1);
				}
				
				sum = P.proofs[i].c_poly[j].eval(rand);
				if(P.proofs[i].randomness[0][j] != rand){
					printf("Error\n");
				}
				
				IP.randomness[i].push_back(x.size());
				x.push_back(rand);
				x.push_back(P.proofs[i].c_poly[j].a);
				IP.polynomials[i][j].push_back(x.size()-1);
				rand = mimc_hash(rand,P.proofs[i].c_poly[j].a);
				y.push_back(rand);
				x.push_back(rand);
				x.push_back(P.proofs[i].c_poly[j].b);
				IP.polynomials[i][j].push_back(x.size()-1);
				rand = mimc_hash(rand,P.proofs[i].c_poly[j].b);
				y.push_back(rand);
				x.push_back(rand);
				x.push_back(P.proofs[i].c_poly[j].c);
				IP.polynomials[i][j].push_back(x.size()-1);
				rand = mimc_hash(rand,P.proofs[i].c_poly[j].c);
				y.push_back(rand);
				x.push_back(rand);
				x.push_back(P.proofs[i].c_poly[j].d);
				IP.polynomials[i][j].push_back(x.size()-1);
				rand = mimc_hash(rand,P.proofs[i].c_poly[j].d);
				y.push_back(rand);
			}


			if(sum != P.proofs[i].vr[0]*P.proofs[i].vr[1]*P.proofs[i].vr[2]){
				printf("Error in multree 2, %d\n",i);
				exit(-1);
			}

			x.push_back(rand);
			x.push_back(P.proofs[i].vr[0]);
			IP.vr.push_back(x.size()-1);
			rand = mimc_hash(rand,P.proofs[i].vr[0]);
			y.push_back(rand);
			x.push_back(rand);
			x.push_back(P.proofs[i].vr[1]);
			IP.vr.push_back(x.size()-1);
			rand = mimc_hash(rand,P.proofs[i].vr[1]);
			y.push_back(rand);
			IP.randomness[i].push_back(x.size());
			IP.rand.push_back(x.size());
			sum = P.proofs[i].vr[0]*(F(1) - rand) + P.proofs[i].vr[1]*rand;

			if(P.proofs[i].vr[2] != compute_beta_point(P.proofs[i].randomness[0],r)){
				printf("Error in multree 3\n");
				exit(-1);
			}
			r = P.proofs[i].randomness[0];
			
			r.push_back(rand);			
		}
		for(int i = 0; i < (int)log2(P.size); i++){
			IP.individual_randomness.push_back(IP.randomness[IP.randomness.size()-1][IP.randomness[IP.randomness.size()-1].size()-(int)log2(P.size)+i]);
		}
		for(int i = 0; i < IP.randomness[IP.randomness.size()-1].size() - (int)log2(P.size); i++){
			IP.global_randomness.push_back(IP.randomness[IP.randomness.size()-1][i]);
		}
	}
	// Last sum is the final_eval
	return rand;
}

F verify_lookup(lookup_proof P, lookup_proof_indexes &IP, vector<F> &x, vector<F> &y){
	IP.previous_r = x.size();
	IP.mul_proofs.resize(2);
	x.push_back(P.previous_r);
	x.push_back(F(0));
	F a = mimc_hash(P.previous_r,F(0));
	IP.a = x.size();
	y.push_back(a);
	x.push_back(a);
	x.push_back(F(1));
	F b = mimc_hash(a,F(1));
	IP.b = x.size();
	y.push_back(b);
	x.push_back(b);
	x.push_back(F(2));
	F c = mimc_hash(b,F(2));
	IP.c = x.size();
	y.push_back(c);
	F rand = c;
	for(int i = 0; i < P.mul_out1.size(); i++){
		IP.mul_out1.push_back(x.size() + 1 + 2*i);
	}
	rand = chain_hash_verify(rand,P.mul_out1,x,y);
	for(int i = 0; i < (int)log2(P.mul_out1.size()); i++){
		IP.r1.push_back(x.size() + 2+2*i);
	}
	vector<F> r = generate_randomness_verify((int)log2(P.mul_out1.size()),rand,x,y);
	x.push_back(r[r.size()]-1);
	x.push_back(P.sum1);
	IP.sum1 = x.size()-1;
	rand = mimc_hash(rand,P.sum1); 
	y.push_back(rand);
	rand = verify_multiplication_tree(P.mP1,IP.mul_proofs[0],rand,r,x,y);
	x.push_back(rand);
	x.push_back(P.read_eval);
	IP.read_eval = x.size()-1;
	rand = mimc_hash(rand,P.read_eval);
	y.push_back(rand);
	x.push_back(rand);
	x.push_back(P.write_eval);
	IP.write_eval = x.size()-1;
	rand = mimc_hash(rand,P.write_eval);
	y.push_back(rand);

	if(P.read_eval + P.mP1.global_randomness[P.mP1.global_randomness.size()-1]*(P.write_eval-P.read_eval) != P.mP1.final_eval){
		printf("lookup error 1\n");
		exit(-1);
	}

	for(int i = 0; i < P.mul_out2.size(); i++){
		IP.mul_out2.push_back(x.size() + 1 + 2*i);
	}
	rand = chain_hash_verify(rand,P.mul_out2,x,y);
	for(int i = 0; i < (int)log2(P.mul_out2.size()); i++){
		IP.r2.push_back(x.size() + 2+2*i);
	}
	r = generate_randomness_verify((int)log2(P.mul_out1.size()),rand,x,y);
	x.push_back(r[r.size()]-1);
	x.push_back(P.sum2);
	IP.sum2 = x.size()-1;
	rand = mimc_hash(rand,P.sum2); 
	y.push_back(rand);
	rand = verify_multiplication_tree(P.mP2,IP.mul_proofs[1],rand,r,x,y);
	
	x.push_back(rand);
	x.push_back(P.read_eval1);
	IP.read_eval1 = x.size()-1;
	rand = mimc_hash(rand,P.read_eval1); 
	y.push_back(rand);
	
	x.push_back(rand);
	x.push_back(P.read_eval2);
	IP.read_eval2 = x.size()-1;
	rand = mimc_hash(rand,P.read_eval2); 
	y.push_back(rand);
	
	x.push_back(rand);
	x.push_back(P.write_eval1);
	IP.write_eval1 = x.size()-1;
	rand = mimc_hash(rand,P.write_eval1); 
	y.push_back(rand);
	
	x.push_back(rand);
	x.push_back(P.write_eval2);
	IP.write_eval2 = x.size()-1;
	rand = mimc_hash(rand,P.write_eval2); 
	y.push_back(rand);

	for(int i = 0; i < P.x1.size(); i++){
		IP.x1.push_back(IP.mul_proofs[0].individual_randomness[i]);
	}

	for(int i = 0; i < P.indexes_eval.size(); i++){
		IP.indexes_eval.push_back(x.size() + 1 + 2*i);
	}
	rand = chain_hash_verify(rand,P.indexes_eval,x,y);
	if((P.read_eval != c+P.read_eval1*a+P.read_eval2*b)||(P.write_eval != c+P.write_eval1*a+P.write_eval2*b)){
		printf("Lookup error 1 \n");
		exit(-1);
	}
	if(P.read_eval1 - P.write_eval1 != 0){
		printf("Lookup error 2\n");
		exit(-1);
	}
	if( P.write_eval2-P.read_eval2 != F(1)){
		printf("Lookup error 3\n");
		exit(-1);
	}
	IP.final_rand = x.size();
	// WE NEED TO EVALUATE final_sum

	return rand;
}


partition_indexes verify_partition_proof(struct partition_SNARK_proof P, vector<F> &x, vector<F> &y){

	partition_indexes IP;
	generate_randomness_verify(P.compress_vector.size(),P.commitment,x,y);
	generate_randomness_verify(P.tree_compress_vector.size(),P.commitment,x,y);
	x.push_back(P.tree_compress_vector[P.tree_compress_vector.size()-1]);
	x.push_back(F(1));
	F rand = mimc_hash(P.tree_compress_vector[P.tree_compress_vector.size()-1],F(1));
	y.push_back(rand);

	IP._c = x.size();


	IP.a = x.size()+3;
	IP.b = x.size()+5;
	IP.c = x.size()+7;
	
	vector<F> randomness = generate_randomness_verify(3,P.P1.previous_r,x,y);
	vector<F> previous_x;
	IP.mul_proofs.resize(5);
	IP.sumcheck2Prod_proofs.resize(9);
	IP.sumcheck3Prod_proofs.resize(3);
	F a = randomness[0];
	F b = randomness[1];
	F c = randomness[2];
	
	F final_r = verify_multiplication_tree( P.P1.mP1,IP.mul_proofs[0],c,previous_x,x, y);

	rand = final_r;
	x.push_back(rand);
	x.push_back(P.P1.eval1_data);
	IP.eval1_data = x.size()-1;
	rand = mimc_hash(rand,P.P1.eval1_data);
	y.push_back(rand);
	x.push_back(rand);
	x.push_back(P.P1.eval2_data);
	IP.eval2_data = x.size()-1;
	rand = mimc_hash(rand,P.P1.eval2_data);
	y.push_back(rand);
	x.push_back(rand);
	x.push_back(P.P1.eval1_perm_data);
	IP.eval1_perm_data = x.size()-1;
	rand = mimc_hash(rand,P.P1.eval1_perm_data);
	y.push_back(rand);
	x.push_back(rand);
	x.push_back(P.P1.eval2_perm_data);
	IP.eval2_perm_data = x.size()-1;
	rand = mimc_hash(rand,P.P1.eval2_perm_data);
	y.push_back(rand);
	IP.aggr_r.push_back(x.size()+3);
	IP.aggr_r.push_back(x.size()+5);
	vector<F> aggr_r = generate_randomness_verify(2,rand,x,y);
	if(P.P1.mP1.final_eval -c != (F(1)-P.P1.mP1.global_randomness[P.P1.mP1.global_randomness.size()-1])*(a*P.P1.eval1_data + b*P.P1.eval2_data) +
	 P.P1.mP1.global_randomness[P.P1.mP1.global_randomness.size()-1]*(a*P.P1.eval1_perm_data + b*P.P1.eval2_perm_data)){
		printf("Error in input mul tree check 1\n");
		exit(-1);
	}

	final_r = verify_2prod_sumcheck(P.P1.sP1,IP.sumcheck2Prod_proofs[0], aggr_r[0]*P.P1.eval1_perm_data + aggr_r[1]*P.P1.eval2_perm_data, aggr_r[1], x, y);
	
	final_r = verify_multiplication_tree( P.P1.mP2,IP.mul_proofs[1],final_r,previous_x,x,y);
	if(P.P1.mP2.output[0] != P.P1.mP2.output[1]){
		printf("Error in mul tree output 1\n");
		exit(-1);
	}
	F x1 = P.P1.mP2.global_randomness[P.P1.mP2.global_randomness.size()-1];
	if(P.P1.mP2.final_eval != (F(1)-x1)*P.P1.eval_input + x1*P.P1.eval_perm_input){
		printf("Error in input mul tree check 2\n");
	}
	
	x.push_back(final_r);
	x.push_back(P.P1.eval_input);
	IP.eval_input = x.size()-1;
	rand = mimc_hash(final_r,P.P1.eval_input);
	y.push_back(rand);
	x.push_back(rand);
	x.push_back(P.P1.eval_perm_input);
	IP.eval_perm_input = x.size()-1;
	rand = mimc_hash(rand,P.P1.eval_perm_input);
	y.push_back(rand);
	// ********************************
	// GET A RANDOM EVAL POINT FOR DATA 
	final_r = verify_2prod_sumcheck(P.P1.sP2,IP.sumcheck2Prod_proofs[1], P.P1.eval_input-P.P1._c, rand, x, y);
	x.push_back(final_r);
	x.push_back(P.P1.eval3_data);
	IP.eval3_data = x.size()-1;
	rand = mimc_hash(final_r,P.P1.eval3_data);
	y.push_back(rand);
	IP.aggr_r.push_back(x.size());
	final_r = verify_2prod_sumcheck(P.P1.sP3,IP.sumcheck2Prod_proofs[2],aggr_r[0]*P.P1.eval1_data + aggr_r[1]*P.P1.eval2_data + rand*P.P1.eval3_data, rand, x, y);
	// Need to compute betas

	// ********************************

	// ********************************
	// GET A RANDOM EVAL POINT FOR DATA MATRIX 
	
	final_r = verify_2prod_sumcheck(P.P1.sP4, IP.sumcheck2Prod_proofs[3],P.P1.eval_perm_input-P.P1._c, final_r, x, y);
	//
	final_r = verify_multiplication_tree(P.P2.mP1,IP.mul_proofs[2],final_r,previous_x,x,y);
	
	// Evaluate tree compress vector locally. 
	// GET A RANDOM EVAL POINT FOR PATHS
	final_r = verify_2prod_sumcheck(P.P2.sP1,IP.sumcheck2Prod_proofs[4],P.P2.mP1.final_eval - F(1), final_r, x, y);
	
	final_r = verify_multiplication_tree(P.P2.mP2,IP.mul_proofs[3],final_r,previous_x,x,y);
	if(P.P2.mP2.output[0] != P.P2.mP1.output[0]){
		printf("Error in check products of P2\n");
		exit(-1);
	}
	// OUTPUT EVAL POINTS from committed data : Power_bits
	IP.mul_proofs[4].first_r = IP.mul_proofs[3].randomness[IP.mul_proofs[3].randomness.size()-1];
	final_r = verify_multiplication_tree(P.P2.mP3,IP.mul_proofs[4],final_r,P.P2.mP2.final_r,x,y);
	
	if(P.P2.mP3.out_eval != P.P2.mP2.final_eval){
		printf("Error in IO check1\n");
		exit(-1);
	}
	if(P.P2.mP3.final_eval != F(1) - P.P2.eval_bits1 + P.P2.final_powers_input_eval){
		printf("Error in IO check2\n");
		exit(-1);
	}
	

	x.push_back(final_r);
	x.push_back(P.P2.eval_bits1);
	IP.eval_bits1 = x.size()-1;
	rand = mimc_hash(final_r,P.P2.eval_bits1);
	y.push_back(rand);
	x.push_back(rand);
	x.push_back(P.P2.final_powers_input_eval);
	IP.final_powers_input_eval = x.size()-1;
	rand = mimc_hash(rand,P.P2.final_powers_input_eval);
	y.push_back(rand);
	// OUTPUT EVAL POINTS from committed data : Power_bits, 
	final_r = verify_3prod_sumcheck(P.P2.tP1,IP.sumcheck3Prod_proofs[0], P.P2.final_powers_input_eval, rand, x, y);
	// *****
	
	for(int i = 0; i < P.P2.eval_tree_x.size(); i++){
		IP.r1.push_back(x.size()+2 + 2*i);
	}
	vector<F> r = generate_randomness_verify(P.P2.eval_tree_x.size(), final_r, x, y);
	// OUTPUT EVAL POINTS from committed data : Tree 
	x.push_back(r[r.size()-1]);
	x.push_back(P.P2.eval_powers2);
	IP.eval_powers2 = x.size()-1;
	rand = mimc_hash(r[r.size()-1],P.P2.eval_powers2);
	y.push_back(rand);

	final_r = verify_2prod_sumcheck(P.P2.sP2,IP.sumcheck2Prod_proofs[5],P.P2.eval_powers2 - F(1), rand, x, y);
	
	F gamma = final_r;
	// TO DO IN GKR : COMPUTE THE GAMMAS EVALUATION
	x.push_back(final_r);
	x.push_back(P.P2.sum1);
	IP.sum1 = x.size()-1;
	rand = mimc_hash(final_r,P.P2.sum1);
	y.push_back(rand);

	final_r = verify_3prod_sumcheck(P.P2.tP2, IP.sumcheck3Prod_proofs[1],P.P2.sum1,rand,x,y);
	final_r = verify_2prod_sumcheck(P.P2.sP3,IP.sumcheck2Prod_proofs[6],P.P2.sum1,final_r,x,y);
	
	// OUTPUT EVAL POINTS from committed data : Tree
	// TO DO IN GKR : COMPUTE AGGREGATED FINAL BETAS
	for(int i = 0; i < 4; i++){
		IP.r2.push_back(x.size()+2 + 2*i);
	}
	r = generate_randomness_verify(4,final_r,x,y);
	final_r = verify_2prod_sumcheck(P.P2.sP4,IP.sumcheck2Prod_proofs[7],r[0]*P.P2.eval_powers1 + r[1]*P.P2.eval_powers2 +r[2]*P.P2.eval_powers3 + r[3]*P.P2.eval_powers4,r[3],x,y);

	for(int i = 0; i < P.P3.diff_eval_x.size(); i++){
		IP.r3.push_back(x.size()+2 + 2*i);
	}
	r =  generate_randomness_verify(P.P3.diff_eval_x.size(),final_r,x,y);
	x.push_back(r[r.size()-1]);
	x.push_back(P.P3.diff_eval);
	IP.diff_eval = x.size()-1;
	rand = mimc_hash(r[r.size()-1],P.P3.diff_eval);
	y.push_back(rand);
	// TO DO IN GKR : COMPUTE powers
	final_r = verify_2prod_sumcheck(P.P3.range_proof[0],IP.sumcheck2Prod_proofs[8],P.P3.diff_eval,rand,x,y);
	// OUTPUT EVAL POINTS from committed data: diff_bit values
	// TO DO IN GKR: COMPUTE BETA
	for(int i = 0; i < P.P3.range_proof[1].c_poly.size(); i++){
		IP.range_proof_rand.push_back(x.size()+2+2*i);
	}
	r =  generate_randomness_verify(P.P3.range_proof[1].c_poly.size(),final_r,x,y);
	
	final_r = verify_3prod_sumcheck(P.P3.range_proof[1],IP.sumcheck3Prod_proofs[2],F(0),r[r.size()-1],x,y);
	verify_gkr(P.GKR_proof1, IP.GKR, P.P3.diff_eval, final_r, x, y);
	
	return IP;
}




histogram_indexes verify_histogram_proof(struct histogram_SNARK_proof P, vector<F> &x, vector<F> &y){
	F rand;
	vector<F> previous_x;
	histogram_indexes IP;
	IP.mul_proofs.resize(2);
	IP.sumcheck2Prod_proofs.resize(7);


	x.push_back(P.previous_r);
	x.push_back(P.commitments);
	rand = mimc_hash(P.previous_r,P.commitments);
	y.push_back(rand);



	vector<F> random_vector = generate_randomness_verify(8,rand,x,y);
	rand = verify_multiplication_tree( P.mP1,IP.mul_proofs[0],random_vector[random_vector.size()-1],previous_x,x,y);
	x.push_back(rand);
	x.push_back(P.mP1.partial_eval[0]);
	IP.peval1 = x.size()-1;
	rand = mimc_hash(rand,P.mP1.partial_eval[0]);
	y.push_back(rand);
	x.push_back(rand);
	x.push_back(P.mP1.partial_eval[1]);
	IP.peval2 = x.size()-1;
	rand = mimc_hash(rand,P.mP1.partial_eval[1]);
	y.push_back(rand);

	rand = verify_2prod_sumcheck(P.sP1,IP.sumcheck2Prod_proofs[0],P.mP1.partial_eval[0]-F(1),rand,x,y);
	rand = verify_2prod_sumcheck(P.sP2,IP.sumcheck2Prod_proofs[1],P.mP1.partial_eval[1]-F(1),rand,x,y);
	rand = verify_multiplication_tree( P.mP2,IP.mul_proofs[1],rand,previous_x,x,y);
	x.push_back(rand);
	x.push_back(P.mP2.partial_eval[1]);
	IP.peval3 = x.size()-1;
	rand = mimc_hash(rand,P.mP2.partial_eval[1]);
	y.push_back(rand);

	
	rand = verify_2prod_sumcheck(P.sP3,IP.sumcheck2Prod_proofs[2],P.mP2.partial_eval[1]-F(1),rand,x,y);
	

	// TO DO IN GKR : VALIDATE INITIAL STATE + Evaluate random vector
	////////////////////////////////////////
	
	
	vector<F> randomness = generate_randomness_verify(P.P1.sP3.randomness[0].size()-1,rand,x,y);
	IP.metadata_evals.push_back(x.size()+1);IP.metadata_evals.push_back(x.size()+3);
	IP.input_evals.push_back(x.size()+5);IP.input_evals.push_back(x.size()+7);
	IP.read_evals.push_back(x.size()+9);IP.read_evals.push_back(x.size()+11);IP.read_evals.push_back(x.size()+13);IP.read_evals.push_back(x.size()+15);
	IP.read_evals.push_back(x.size()+17);
	IP.write_evals.push_back(x.size()+19);IP.write_evals.push_back(x.size()+21);IP.write_evals.push_back(x.size()+23);
	IP.write_evals.push_back(x.size()+25);IP.write_evals.push_back(x.size()+27);
	rand = chain_hash_verify(chain_hash_verify(chain_hash_verify(chain_hash_verify(randomness[randomness.size()-1],P.P1.metadata_evals,x,y),P.P1.input_evals,x,y),P.P1.read_evals,x,y),P.P1.write_evals,x,y);

	if(P.P1.input_evals[0] != P.P1.read_evals[1] || P.P1.input_evals[0] != P.P1.write_evals[1]){
		printf("Error leaves_sumcheck 2---1\n");
		exit(-1);
	}
	if(P.P1.input_evals[1] != P.P1.read_evals[2] || P.P1.input_evals[1] != P.P1.write_evals[2]){
		printf("Error leaves_sumcheck 2---2\n");
		exit(-1);
	}
	// Error will be thrown if attributes are not power of 2
	if(P.P1.metadata_evals[0] != P.P1.read_evals[0] || P.P1.metadata_evals[0] != P.P1.write_evals[0]){
		printf("Error leaves_sumcheck 2---3\n");
		exit(-1);	
	}
	if(P.P1.metadata_evals[1] != P.P1.read_evals[3] || P.P1.metadata_evals[1] != P.P1.write_evals[3]){
		printf("Error leaves_sumcheck 2---4\n");
		exit(-1);	
	}
	if(P.P1.write_evals[4] - P.P1.read_evals[4] - F(1) != F(0)){
		printf("Error leaves_sumcheck 2---5\n");
		exit(-1);
	}

	for(int i = 0; i < 6; i++){
		IP.r.push_back(x.size()+2+2*i);
	}
	vector<F> r = generate_randomness_verify(6,rand,x,y);

	F sum = r[0]*P.P1.read_evals[0]+r[1]*P.P1.read_evals[1]+r[2]*P.P1.read_evals[2]+r[3]*P.P1.read_evals[3]+r[4]*P.P1.read_evals[4]+r[5]*P.sP1.vr[0];
	rand = verify_2prod_sumcheck(P.P1.sP1,IP.sumcheck2Prod_proofs[3],sum,r[r.size()-1],x,y);
	sum = r[0]*P.P1.write_evals[0]+r[1]*P.P1.write_evals[1]+r[2]*P.P1.write_evals[2]+r[3]*P.P1.write_evals[3]+r[4]*P.P1.write_evals[4]+r[5]*(P.P1.sparse_vector_eval + P.sP2.vr[0]);
	rand = verify_2prod_sumcheck(P.P1.sP2,IP.sumcheck2Prod_proofs[4],sum,rand,x,y);
	sum = r[0]*P.P1.input_evals[0] + r[1]*P.P1.input_evals[1];
	rand = verify_2prod_sumcheck(P.P1.sP3,IP.sumcheck2Prod_proofs[5],sum,rand,x,y);
	sum = r[0]*P.P1.metadata_evals[0] + r[1]*P.P1.metadata_evals[1];
	rand = verify_2prod_sumcheck(P.P1.sP4,IP.sumcheck2Prod_proofs[6],sum,rand,x,y);
	return IP;
}

node_histogram_indexes verify_node_histogram_proof(struct nodes_histogram_SNARK_proof P,vector<F> &x, vector<F> &y){
	node_histogram_indexes IP;	

	x.push_back(P.previous_r);x.push_back(P.commitment);
	F rand = mimc_hash(P.previous_r,P.commitment);
	y.push_back(rand);
	IP.previous_r = x.size()-2;
	IP.commitment = x.size()-1;
	IP.sumcheck2Prod_proofs.resize(4);
	for(int i = 0; i < P.r.size(); i++){
		IP.compress_r.push_back(x.size()+ 2*i +2);
	}
	vector<F> compress_r = generate_randomness_verify(P.r.size(),rand,x,y);
	x.push_back(compress_r[compress_r.size()-1]);x.push_back(F(0));
	F a = mimc_hash(compress_r[compress_r.size()-1],F(0));
	IP.a = x.size();
	y.push_back(a);
	x.push_back(a);x.push_back(F(1));
	F b = mimc_hash(a,F(1));
	IP.b = x.size();
	y.push_back(b);
	x.push_back(b);x.push_back(F(2));
	F c = mimc_hash(b,F(2));
	IP.c = x.size();
	y.push_back(c);
	x.push_back(c);x.push_back(F(3));
	F r = mimc_hash(c,F(3));
	IP.r = x.size();
	y.push_back(r);
	x.push_back(r);x.push_back(F(0));
	rand = mimc_hash(r,F(0));
	y.push_back(rand);
	
	rand = verify_gkr(P.GKR_proof1, IP.GKR1, F(0), rand, x, y);

	x.push_back(rand);x.push_back(P.wit_eval);
	rand = mimc_hash(rand,P.wit_eval);
	IP.wit_eval = x.size()-1;
	y.push_back(rand);
	x.push_back(rand);x.push_back(P.node_eval);
	rand = mimc_hash(rand,P.node_eval);
	IP.node_eval = x.size()-1;
	y.push_back(rand);
	x.push_back(rand);x.push_back(P.leaf_eval);
	rand = mimc_hash(rand,P.leaf_eval);
	IP.leaf_eval = x.size()-1;
	y.push_back(rand);
	x.push_back(rand);x.push_back(P.comp_wit_eval);
	rand = mimc_hash(rand,P.comp_wit_eval);
	IP.comp_wit_eval = x.size()-1;
	y.push_back(rand);
	x.push_back(rand);x.push_back(P.comp_node_eval);
	rand = mimc_hash(rand,P.comp_node_eval);
	IP.comp_node_eval = x.size()-1;
	y.push_back(rand);
	x.push_back(rand);x.push_back(P.comp_out_eval);
	rand = mimc_hash(rand,P.comp_out_eval);
	IP.comp_out_eval = x.size()-1;
	y.push_back(rand);
	x.push_back(rand);x.push_back(P.comp_leaf_eval);
	rand = mimc_hash(rand,P.comp_leaf_eval);
	IP.comp_leaf_eval = x.size()-1;
	y.push_back(rand);
	rand = verify_2prod_sumcheck(P.sP1, IP.sumcheck2Prod_proofs[0], P.comp_wit_eval, rand,x,y);
	rand = verify_2prod_sumcheck(P.sP2, IP.sumcheck2Prod_proofs[1], P.comp_out_eval, rand,x,y);
	rand = verify_2prod_sumcheck(P.sP3, IP.sumcheck2Prod_proofs[2], P.comp_leaf_eval, rand,x,y);
	rand = verify_2prod_sumcheck(P.sP4, IP.sumcheck2Prod_proofs[3], P.comp_node_eval, rand,x,y);
	
	rand = verify_gkr(P.GKR_proof2, IP.GKR2, P.sP2.vr[0], rand, x, y);

	return IP;
	//rand = verify_gkr(P.GKR_proof1, IP.GKR1, F(0), rand, x, y);

}

split_indexes verify_split_proof(struct split_SNARK_proof P, vector<F> &x, vector<F> &y){
	F rand;
	vector<F> dummy_x;
	vector<F> previous_x;
	split_indexes IP;
	IP.sumcheck3Prod_proofs.resize(7);IP.sumcheck2Prod_proofs.resize(3);
	x.push_back(P.previous_r);
	x.push_back(P.commitment);
	rand = mimc_hash(P.previous_r,P.commitment);
	y.push_back(rand);

	IP.lookup_indexes.resize(2);
	
	rand = verify_lookup(P.lP1,IP.lookup_indexes[0],x,y);

	x.push_back(rand);
	x.push_back(P.ginis_eval1);
	IP.ginis_eval1 = x.size()-1;
	rand = mimc_hash(rand,P.ginis_eval1);
	y.push_back(rand);

	x.push_back(rand);
	x.push_back(P.best_gini_eval1);
	IP.best_gini_eval1 = x.size()-1;
	rand = mimc_hash(rand,P.best_gini_eval1);
	y.push_back(rand);

	if(P.lP1.final_eval != P.ginis_eval1 - P.best_gini_eval1){
		printf("Error in split verify 1\n");
		exit(-1);
	}

	rand = verify_multiplication_tree(P.mP1,IP.mul_proof,rand,dummy_x,x,y);
	x.push_back(rand);x.push_back(P.ginis_eval2);IP.ginis_eval2 = x.size()-1;
	rand = mimc_hash(rand,P.ginis_eval2);
	y.push_back(rand);
	x.push_back(rand);x.push_back(P.best_gini_eval2);IP.best_gini_eval2 = x.size()-1;
	rand = mimc_hash(rand,P.best_gini_eval2);
	y.push_back(rand);
	
	if(P.mP1.final_eval != P.ginis_eval2- P.best_gini_eval2){
		printf("Error in split verify 2\n");
	}
	rand = verify_lookup(P.lP2,IP.lookup_indexes[1],x,y);
	x.push_back(rand);x.push_back(P.P1.eval1);IP.divisors_quot_eval = x.size()-1;
	rand = mimc_hash(rand,P.P1.eval1);
	y.push_back(rand);
	x.push_back(rand);x.push_back(P.P1.eval2);IP.dividents_cond_eval = x.size()-1;
	rand = mimc_hash(rand,P.P1.eval2);
	y.push_back(rand);
	if(F(1<<Q)*P.P1.eval2 - P.P1.eval1 != P.lP2.final_eval){
		printf("Error in split verify 3\n");
		exit(-1);
	}
	// GINI SUMCHECK 1
	// Note v[1] = divisors_eval, v[0] = quotients_eval 
	rand = verify_3prod_sumcheck(P.P1.tP1, IP.sumcheck3Prod_proofs[0], P.P1.eval1, rand,x,y);
	// v[0] = cond_eval v[1] =dividents_eval 
	rand = verify_3prod_sumcheck(P.P1.tP2, IP.sumcheck3Prod_proofs[1], P.P1.eval2, rand,x,y);

	
	// cond_eval2 = 1-v[0] 
	rand = verify_3prod_sumcheck(P.P1.tP3, IP.sumcheck3Prod_proofs[2], F(0), rand,x,y);

	for(int i = 0; i < 2; i++){
		IP.a.push_back(x.size()+2+2*i);
	}
	vector<F> a = generate_randomness_verify(2,rand,x,y);
	
	// cond_eval3 = v[0]
	rand = verify_2prod_sumcheck(P.P1.sP, IP.sumcheck2Prod_proofs[0], a[0]*P.P1.cond_eval1+a[1]*P.P1.cond_eval2, a[1],x,y);

	// Get N_eval1,N_eval2 and inverses_eval (committed)
	rand = verify_3prod_sumcheck(P.P1.tP4, IP.sumcheck3Prod_proofs[3],P.P1.cond_eval3, rand,x,y);
	

	// OUTPUT OF GINI SUMCHECK : 2 evaluation points of N, 1 evaluation point for inverses 

	// GINI SUMCHECK 2

	x.push_back(rand);x.push_back(P.P2.square_N_eval);IP.square_N_eval = x.size()-1;
	rand = mimc_hash(rand,P.P2.square_N_eval);
	y.push_back(rand);
	x.push_back(rand);x.push_back(P.P2.pairwise_prod_eval);IP.pairwise_prod_eval = x.size()-1;
	rand = mimc_hash(rand,P.P2.pairwise_prod_eval);
	y.push_back(rand);
	if(P.P1.tP2.vr[1] != P.P2.square_N_eval - F(2)*P.P2.pairwise_prod_eval){
		printf("Error in split verify 4\n");
	}
	// eval1_N = v[0]

	rand = verify_3prod_sumcheck(P.P2.tP1, IP.sumcheck3Prod_proofs[4],P.P1.tP1.vr[1], rand,x,y);

	
	x.push_back(rand);x.push_back(P.P2.eval1_N0);IP.eval1_N0 = x.size()-1;
	rand = mimc_hash(rand,P.P2.eval1_N0);
	y.push_back(rand);
	x.push_back(rand);x.push_back(P.P2.eval1_N1);IP.eval1_N1 = x.size()-1;
	rand = mimc_hash(rand,P.P2.eval1_N1);
	y.push_back(rand);
	
	if(P.P2.eval1_N0 + P.P2.eval1_N1 != P.P2.tP1.vr[1]){
		printf("Error in split verify 5\n");
		exit(-1);
	}
	// eval2_N = vr[0] = vr[1]
	rand = verify_3prod_sumcheck(P.P2.tP2, IP.sumcheck3Prod_proofs[5], P.P2.square_N_eval, rand,x,y);

	// gini_eval1 = vr[0]; gini_eval2 = vr[1];
	rand = verify_3prod_sumcheck(P.P2.tP3, IP.sumcheck3Prod_proofs[6], P.P2.pairwise_prod_eval, rand,x,y);

	
	for(int i = 0; i < 4; i++){
		IP.r1.push_back(x.size()+2*i+2);
	}
	a = generate_randomness_verify(4,rand,x,y);
	rand = verify_2prod_sumcheck(P.P2.sP1, IP.sumcheck2Prod_proofs[1], a[0]*P.P2.tP1.vr[0] + a[1]*P.P2.eval1_N0+a[2]*P.P2.eval1_N1 + a[3]*P.P2.tP2.vr[1], a[3],x,y);
	
	x.push_back(rand);x.push_back(P.P2.gini_eval3);IP.gini_eval3 = x.size()-1;
	rand = mimc_hash(P.P2.sP1.final_rand,P.P2.gini_eval3);
	y.push_back(rand);
	
	x.push_back(rand);x.push_back(P.P2.gini_eval4);IP.gini_eval4 = x.size()-1;
	rand = mimc_hash(rand,P.P2.gini_eval4);
	y.push_back(rand);
	

	for(int i = 0; i < 4; i++){
		IP.r2.push_back(x.size()+2*i+2);
	}
	a = generate_randomness_verify(4,rand,x,y);

	rand = verify_2prod_sumcheck(P.P2.sP2, IP.sumcheck2Prod_proofs[2], a[0]*P.P2.tP3.vr[0] + a[1]*P.P2.tP3.vr[1]+a[2]*P.P2.gini_eval3 + a[3]*P.P2.gini_eval4, a[3],x,y);
	// OUTPUT : 1 gini evaluation

	verify_gkr(P.GKR_proof1, IP.GKR, F(0), rand, x, y);
	

	return IP;
}