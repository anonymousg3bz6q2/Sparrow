#include "config_pc.hpp"
#include "mimc.h"
#include "utils.hpp"
#include "sumcheck.h"
#include <chrono>
#include "quantization.h"
#include "space_efficient_sumcheck.h"
#include "witness_stream.h"
#include "Poly_Commit.h"
#include "pol_verifier.h"

#define RANGE 1
#define SUM 2
#define SUM_INV 3

using namespace std::chrono;

extern int threads;
extern int bin_size;
extern double range_proof_verification_time;
extern int range_proof_size;
extern size_t MAX_CHUNCK;
extern double proving_time;
int recursion = 0;
extern Comm pp_recursion;
extern MIPP_Comm pp_mul;
extern F A_,B_;
F eval_poly(vector<F> poly,int c){
	F sum = 0;
	for(int i = poly.size() - (1ULL<<c); i < poly.size(); i++){
		sum += poly[i];
	}
	return sum;

}

proof_stream generate_2product_sumcheck_proof_stream_naive(stream_descriptor fp1,stream_descriptor fp2, size_t size, F previous_r){
	
		int rounds = int(log2(size));
	
	proof_stream P;
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	vector<F> v1(MAX_CHUNCK),v2(MAX_CHUNCK),v3(MAX_CHUNCK);
	F rand = previous_r;
	vector<quadratic_poly> p;
	vector<F> rand_v;
	
		int i;
		int pos;
		for(i = 0; i < rounds; i++){
			pos = 0;
			quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			//printf("%d\n",i );
			int L = 1 << (rounds - 1-i);
			if(2*L > MAX_CHUNCK){
				for(int j = 0; j < size/MAX_CHUNCK; j++){
					read_stream(fp1,v1,MAX_CHUNCK);
					read_stream(fp2,v1,MAX_CHUNCK);
						
					for(int k = 0; k < i; k++){
						for(int l = 0; l < MAX_CHUNCK/(1ULL<<(k+1)); l++){
							v1[l] = v1[2*l] + rand_v[k]*(v1[2*l+1]-v1[2*l]);
							v2[l] = v2[2*l] + rand_v[k]*(v2[2*l+1]-v2[2*l]);
						}
					}
					
					for(int k = 0; k < MAX_CHUNCK/(1<<(i+1)); k++){
						l1 = linear_poly(v1[2*k+1] - v1[2*k],v1[2*k]);
						l2 = linear_poly(v2[2*k+1] - v2[2*k],v2[2*k]);
						temp_poly = l1*l2;
						poly = poly + temp_poly;
					}				
				}
				reset_stream(fp1);
				reset_stream(fp2);
				rand_v.push_back(rand);
				r.push_back(rand);
				rand = mimc_hash(rand,poly.a);
				rand = mimc_hash(rand,poly.b);
				rand = mimc_hash(rand,poly.c);
				p.push_back(poly);
			}else{
				break;
			}
		}
		vector<F> fv1(MAX_CHUNCK),fv3(MAX_CHUNCK),fv2(MAX_CHUNCK);
		
		reset_stream(fp1);
		pos = 0;
    	int counter = 0;
		for(int j = 0; j < size/MAX_CHUNCK; j++){
			read_stream(fp1,v1,MAX_CHUNCK);
			read_stream(fp2,v2,MAX_CHUNCK);
					
			for(int k = 0; k < i; k++){
				for(int l = 0; l < MAX_CHUNCK/(1ULL<<(k+1)); l++){
					v1[l] = v1[2*l] + rand_v[k]*(v1[2*l+1]-v1[2*l]);
					v2[l] = v2[2*l] + rand_v[k]*(v2[2*l+1]-v2[2*l]);
				}
			}
			for(int k = 0; k < MAX_CHUNCK/(1ULL<<(i)); k++){
				fv1[counter] = v1[k];
				fv2[counter] = v2[k];
				counter++;
			}
		}
		v1 = fv1;
		v2 = fv2;
		for(; i < rounds; i++){
			quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			
			int L = 1 << (rounds - 1-i);
			for(int j = 0; j < L; j++){
				l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
				l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
				temp_poly = l1*l2;
				poly = poly + temp_poly;
				v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
				v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);						
			}
			r.push_back(rand);
			rand = mimc_hash(rand,poly.a);
			rand = mimc_hash(rand,poly.b);
			rand = mimc_hash(rand,poly.c);
			p.push_back(poly);
		}
		
		rand = mimc_hash(rand,v1[0]);
		rand = mimc_hash(rand,v2[0]);
		
		Pr.vr.push_back(v1[0]);
		Pr.vr.push_back(v2[0]);
		Pr.vr.push_back(v3[0]);
		P.vr.push_back(v1[0]);
		P.vr.push_back(v2[0]);
		P.vr.push_back(v3[0]);
		Pr.q_poly = p;
		Pr.randomness.push_back(r);
		Pr.final_rand = rand;
		P.P.push_back(Pr);
		return P;
}


recursion_proof reduce_proof_size(vector<F> poly, int c, F omega, F r,F previous_r){
	recursion_proof P;
	if(c <= 4){
		int poly_log = (int)log2(poly.size());
		int old_poly_size = poly.size();

		if(1ULL<<poly_log != poly.size()){
			poly_log++;
		}
		vector<F> ones(1ULL<<poly_log,F_ZERO);
		for(int i = old_poly_size - (1ULL<<c); i < old_poly_size; i++){
			ones[i] = F_ONE;
		}
		poly.resize(1ULL<<poly_log,F_ZERO);
		commit(poly,pp_recursion);
		vector<F> temp_poly = poly;
		
		//generate_2product_sumcheck_proof(temp_poly,ones,previous_r);
		
		// note that correctness of pows can be checked efficiently by
		//the verifier
		vector<F> pows(1ULL<<c);
		pows[0] = F_ONE;
		for(int i = 1; i < 1ULL<<c; i++){
			pows[i] = pows[i-1]*omega;
		}
		vector<F> d(1ULL<<c),d_inv(1ULL<<c);
		vector<F> L = compute_lagrange_coeff(omega,r,1ULL<<c);
		vector<F> L_out(poly.size(),F_ZERO);
		int counter = 0;
		for(int i = 0; i < d.size(); i++){
			for(int j = i+1; j < d.size(); j++){
				L_out[counter] = L[i]*L[j];
				counter++;
			}
		} 
		for(int i = 0; i < d.size(); i++){
				L_out[counter] = L[i]*L[i];
				counter++;
		}
		for(int i = 0; i < d.size(); i++){
			d[i] = r-pows[i];
			d_inv[i].inv(d_inv[i],d[i]);
			if(d_inv[i]*d[i] != F_ONE){
				printf("Error inverse\n");
				exit(-1);
			}
		}
		
		printf("Naive proof size : %lf Kb\n",(float)(old_poly_size*32)/1024.0);
		proof P1 = generate_2product_sumcheck_proof(temp_poly,L_out,previous_r);
		proof P2 = prepare_coeff(L,P1.randomness[0],1<<c);
		vector<F> beta,r = P2.randomness[P2.randomness.size()-1];
		if(1<<r.size() != L.size()){
			printf("error in gkr rand\n");
			exit(-1);
		}
		precompute_beta(r,beta);
		proof P3 = _generate_3product_sumcheck_proof(d_inv,pows,beta,r[r.size()-1]);
		//proof P4 = _generate_3product_sumcheck_proof(d_inv,inv,beta,r[r.size()-1]);
		printf("Sumcheck size : %f kb\n", (float)(32*(3*P1.randomness[0].size() + 4*P2.randomness[0].size() + 4))/1024.0);
	}else{
		vector<F> ones(1ULL<<(c+1),F_ZERO);
		F test_sum = 0;
		for(int i = 0; i < 1<<c; i++){
			ones[i] = F_ONE;
			test_sum += poly[i];
		}
		
		vector<F> pows(1ULL<<(c+1));
		pows[0] = F_ONE;
		for(int i = 1; i < 1ULL<<(c+1); i++){
			pows[i] = pows[i-1]*omega;
		}


		F new_sum = F(0);
		
		vector<F> L = compute_lagrange_coeff(getRootOfUnit((int)log2(poly.size())),r,1ULL<<((int)log2(poly.size())));
		
		for(int i = 0; i < L.size(); i++){
			new_sum += L[i]*poly[i];
		}


		//for(int i = 0; i < L.size()/2; i++){
		//	new_sum += L[2*i+1]*poly[i+L.size()/2];
		//}
		

		vector<F> d(1ULL<<(c+1)),d_inv(1ULL<<(c+1));
		for(int i = 0; i < d.size(); i++){
			d[i] = r-pows[i];
			d_inv[i].inv(d_inv[i],d[i]);
			if(d_inv[i]*d[i] != F_ONE){
				printf("Error inverse\n");
				exit(-1);
			}
		}
		F A; A.pow(A,r,F(1<<(c+1)));
		A = A-F(1);
		A.inv(A,A);
		A = A*F(1<<(c+1));

		vector<F> a = generate_randomness(2,previous_r);
		vector<F> aggr_poly(L.size());
		for(int i  = 0; i < L.size(); i++){
			aggr_poly[i] = a[0]*L[i] + a[1]*ones[i];
		}
		commit(poly,pp_recursion);
		P.comm1 = pp_recursion.C;
		P.a1 = a;
		proof P1 = generate_2product_sumcheck_proof(poly,aggr_poly,a[1]);
		
		KZG_open(poly,P1.randomness[0],pp_recursion);
		P.Proof1 = pp_recursion.Proof;pp_recursion.Proof.clear();
		P.P1 = P1;
		P.sum1 = P1.q_poly[0].eval(F(0))+P1.q_poly[0].eval(F(1));
		F L_eval = evaluate_vector(L, P1.randomness[0]);
		vector<F> beta;precompute_beta(P1.randomness[0],beta);
		a = generate_randomness(2,P1.randomness[0][P1.randomness[0].size()-1]);
		for(int i = 0; i < L.size(); i++){
			aggr_poly[i] = a[0]*pows[i] + a[1]*d[i];
		}
		commit(poly,pp_recursion);
		P.comm2 = pp_recursion.C;
		P.a2 = a;
		proof P2 = _generate_3product_sumcheck_proof(d_inv,aggr_poly,beta,a[1]);
		P.P2 = P2;
		if(P2.c_poly[0].eval(F_ZERO) + P2.c_poly[0].eval(F_ONE) != a[0]*L_eval*A + a[1]){
			printf("Error\n");
		}
		P.sum2 = P2.c_poly[0].eval(F(0))+P2.c_poly[0].eval(F(1));
		P.sum = new_sum;
		KZG_open(d_inv,P2.randomness[0],pp_recursion);
		P.Proof2 = pp_recursion.Proof;pp_recursion.Proof.clear();
		
		
	}
	return P;
}


proof_stream local_3product_sumcheck_proof(stream_descriptor fp1, stream_descriptor fp2, size_t size, vector<F> beta_rand, F previous_r, int mod){
	vector<F> v1(size),v2(size);
    if(fp2.pos != -1){
        read_stream(fp1,v1,size);
		read_stream(fp2,v2,size);
	}else{
		if(mod == RANGE){
			read_stream(fp1,v1,size);
			for(int k = 0; k < size; k++){
				v2[k] = F_ONE - v1[k];
			}
		}else{
            vector<F> v(2*size);
            read_stream(fp1,v,2*size);
			for(int k = 0; k < size; k++){
				v1[k] = v[2*k];
				v2[k] = v[2*k+1];
			}
            v.clear();
		}
	}
    vector<F> beta;
    precompute_beta(beta_rand,beta);
	
	proof P = _generate_3product_sumcheck_proof(v1,v2,beta,previous_r);
    proof_stream Proof;
    Proof.P.push_back(P);
    Proof.vr.push_back(P.vr[0]);
    Proof.vr.push_back(P.vr[1]);
	Proof.new_sum = P.c_poly[0].eval(0) + P.c_poly[0].eval(1);
    return Proof;
}

void prepare_fft_aux(vector<F> &w, vector<u32> &rev, vector<F> &w_prod, vector<u32> &rev_prod, int degree){
	
	rev_prod[0] = 0;
	rev[0] = 0;
    w[0] = F(1);w[1] = getRootOfUnit((int)log2(w.size()));w[1].inv(w[1],w[1]);
	w_prod[0] = F_ONE; w_prod[1] = getRootOfUnit((int)log2(degree));
	int c = (int)log2(degree);
	
	for (u32 i = 1; i < rev_prod.size(); ++i){
		rev_prod[i] = rev_prod[i >> 1] >> 1 | (i & 1) << (c-1 );
	}
	for (u32 i = 1; i < rev.size(); ++i){
		rev[i] = rev[i >> 1] >> 1 | (i & 1) << (c-2 );
	}
    
	for (u32 i = 2; i < w_prod.size(); ++i) w_prod[i] = w_prod[i - 1] * w_prod[1];
    for (u32 i = 2; i < w.size(); ++i) w[i] = w[i - 1] * w[1];
    
}


// put size in increasing order
proof_stream generate_3product_sumcheck_proof_stream_batch(stream_descriptor fp1, vector<size_t> size, vector<F> a_r, int distance, vector<F> beta_rand, F previous_r, int mod){
	
	for(int i = 1; i < size.size(); i++){
		if(size[i-1] < size[i]){
			printf("Set sizes in increasing order\n");
			exit(-1);
		}
	}
	if(MAX_CHUNCK < size[0]/MAX_CHUNCK){
		printf("Error, increase buffer %d\n",size);
		exit(-1);
	}
	
	proof_stream Proof;
    vector<int> total_c;// = (int)log2(size/MAX_CHUNCK);
    for(int i = 0; i < size.size(); i++){
		total_c.push_back((int)log2(size[i]/MAX_CHUNCK));
	}
	vector<int> c;
	
	
	for(int i = 0; i < total_c.size(); i++){
		//printf(">> %d\n",total_c[i]);
		if(4 >= total_c[i]){
			c.push_back(total_c[i]);
		}else{
			c.push_back((int)log2(log2(size[i]/MAX_CHUNCK)) + 1);
		}
	}
	
	
	
	vector<int> new_c(size.size(),0),offset(size.size()),poly_degree(size.size()),new_degree(size.size(),0);
	vector<F> omega(size.size());
	vector<int> degree(size.size());
	//F omega = getRootOfUnit(c);
	vector<F> len,ilen(size.size());// = F(1<<c);
    
	vector<vector<F>> v1(size.size()),v2(size.size());
	vector<vector<F>> temp_v1(size.size()),temp_v2(size.size());
	vector<vector<F>> poly(size.size()),l1(size.size()),l2(size.size());
    

	for(int i = 0; i < c.size(); i++){
		omega[i] = getRootOfUnit(c[0]);
		degree[i] = 1<<c[0];
		len.push_back(F(1<<c[0]));
		F::inv(ilen[i], len[i]);
		v1[i].resize(MAX_CHUNCK);
		v2[i].resize(MAX_CHUNCK);
		temp_v1[i].resize(degree[i]);
		temp_v2[i].resize(degree[i]);
		poly[i].resize(2*degree[i]);
		if(c[0] <= 4){
     	   poly[i].clear();
     	   poly[i].resize(degree[i]*(degree[i]+1)/2);
    	}
		l1[i].resize(2*degree[i]);
		l2[i].resize(2*degree[i]);
	}
   	Proof.size = size[0];
    Proof.c = c[0];
	
    vector<vector<F>> poly_proofs;
	vector<vector<F>> Lv;
	vector<int> idx(c.size(),0);
	vector<F> rand;
    /// ********(*(*(())))
	vector<vector<F>> v(c.size());
	for(int i = 0; i < v.size(); i++){
		v[i].resize(2*MAX_CHUNCK/(1<<(i*distance)));
	}
	/// ********(*(*(())))
	
	vector<u32> rev,rev_prod;
	vector<F> w,w_prod;
	
	
	vector<F> partitions_rand;
	vector<F> beta_partitions;
	partitions_rand.resize(beta_rand.size() - (int)log2(MAX_CHUNCK));
	for(int j = 0; j < partitions_rand.size(); j++){
		partitions_rand[j] = beta_rand[j + (int)log2(MAX_CHUNCK)];
	}	
	precompute_beta(partitions_rand,beta_partitions);
	//(beta_rand.size() - (int)log2(MAX_CHUNCK));
	//for(int i = 0; i < beta_rand.size()-(int)log2(MAX_CHUNCK); i++){
	//	partitions_rand[i] = beta_rand[i];
	//}

	vector<F> beta;
	partitions_rand.clear();
	
	for(int i = 0; i < (int)log2(MAX_CHUNCK); i++){
		partitions_rand.push_back(beta_rand[i]);
	}

	precompute_beta(partitions_rand,beta);
    vector<int> counter(size.size(),0);
    clock_t s,e;
	clock_t stream_s,stream_e;
	double stream_access_time = 0.0;
	F check_sum = F(-1),test_sum = F(0);
	int i;

	///////////
	vector<F> Sums(a_r.size(),F(0));
	F eval_chalenge  = F(0);
	//////////
	s = clock();
	for(i = 0; i < 2; i++){
		for(int j = 0; j < counter.size(); j++)counter[j] = 0;
		
		reset_stream(fp1);
		for(int k = 0; k < c.size(); k++){
			for(int j = 0; j < poly[k].size(); j++){
				poly[k][j] = F_ZERO;
			}
		}

        
		for(int j = 0; j < size[0]/MAX_CHUNCK; j++){
			stream_s = clock();
			read_stream_batch(fp1,v,2*MAX_CHUNCK,distance);
			
			for(int l = 0; l < c.size(); l++){
				if(idx[l] == MAX_CHUNCK)idx[l] = 0;
			
				for(int k = 0; k < MAX_CHUNCK/(1<<(l*distance)); k++){
					v1[l][idx[l]] = v[l][2*k];
					v2[l][idx[l]] = v[l][2*k+1];
					idx[l]++;
				}
			}
	
			stream_e = clock();
			stream_access_time += (double)(stream_e-stream_s)/(double)CLOCKS_PER_SEC;
            for(int l = 0; l < c.size(); l++){
				if(idx[l] != MAX_CHUNCK) continue;
				for(int h = 0; h < MAX_CHUNCK; h++){
					v1[l][h] = beta[h]*beta_partitions[counter[l]]*v1[l][h];
				}
				counter[l]++;
			}

			for(int n = 0; n < c.size(); n++){
				if(idx[n] != MAX_CHUNCK) continue;
				
				for(int k = 0; k < i; k++){
					for(int l = 0; l < MAX_CHUNCK/(1ULL<<(c[0]*(k+1))); l++){
						v1[n][l] = Lv[k][0]*v1[n][Lv[k].size()*l];
						v2[n][l] = Lv[k][0]*v2[n][Lv[k].size()*l];
						for(int h = 1; h < Lv[k].size(); h++){
							v1[n][l] += Lv[k][h]*v1[n][degree[0]*l + h];
							v2[n][l] += Lv[k][h]*v2[n][degree[0]*l + h];
						}
					}
				}
			
				int current_size = MAX_CHUNCK/(1<<(c[0]*i));
				if(new_c[n] == 0){
					offset[n] = current_size/degree[n];
					poly_degree[n] = degree[n]; 
				}else{
					offset[n] = current_size/new_degree[n];
					poly_degree[n] = new_degree[n]; 
				}
				//printf("%d,%d \n",offset,poly_degree);
				for(int k = 0; k < offset[n]; k++){
					for(int l = 0; l < poly_degree[n]; l++){
						temp_v1[n][l] = v1[n][poly_degree[n]*k + l];
						temp_v2[n][l] = v2[n][poly_degree[n]*k + l];
						//test_sum += temp_v1[l]*temp_v2[l]; 
						l1[n][l + poly_degree[n]] = F_ZERO;
						l2[n][l + poly_degree[n]] = F_ZERO;
					}
					
					if((c[0] <= 4 && new_c[n] == 0) || (new_c[n] <= 4 && new_c[n] > 0)){
						int _idx = 0;
						for(int l = 0; l < poly_degree[n]; l++){
							for(int h = l+1; h < poly_degree[n]; h++){
								poly[n][_idx] += temp_v1[n][l]*temp_v2[n][h] + temp_v1[n][h]*temp_v2[n][l];
								_idx++;
							}
						}
						for(int l = 0; l < poly_degree[n]; l++){
							poly[n][_idx] += temp_v1[n][l]*temp_v2[n][l];
							_idx++;
						}
				
					}else{
						
						
						my_fft(temp_v1[n],w,rev,ilen[0],true);
						my_fft(temp_v2[n],w,rev,ilen[0],true);
						for(int l = 0; l < poly_degree[n]; l++){
							l1[n][l] = temp_v1[n][l];
							l2[n][l] = temp_v2[n][l];
						}
						
						my_fft(l1[n],w_prod,rev_prod,F(1),false);
						my_fft(l2[n],w_prod,rev_prod,F(1),false);
						for(int l = 0; l < 2*poly_degree[n]; l++){
							poly[n][l] += l1[n][l]*l2[n][l];
							
						}
					}
					
				}
			}
			
		}
		vector<F> final_poly(poly[0].size(),F(0));
		for(int j = 0; j < poly.size(); j++){
			for(int k = 0; k < poly[j].size(); k++){
				final_poly[k] = final_poly[k] + a_r[j]*poly[j][k];
			}
		}
        poly_proofs.push_back(final_poly);
		F r;r.setByCSPRNG();
		rand.push_back(r);

		

		if(!new_c[0]){
			Lv.push_back(compute_lagrange_coeff(omega[0],r,degree[0]));
		}else{
			if(recursion == 1 && new_c[0] > 4){	
				Proof.RP = reduce_proof_size(final_poly,new_c[0],getRootOfUnit(new_c[0]+1),r,r);
			}
			F new_omega = getRootOfUnit((int)log2(new_degree[0]));
			Lv.push_back(compute_lagrange_coeff(new_omega,r,new_degree[0]));		
		}
		if(!new_c[0]){
			
			for(int k = 0; k < c.size(); k++){
				new_c[k] = total_c[0] -c[0];
				new_degree[k] = 1ULL<<new_c[0];
			}

			if(new_c[0] == 0){
				i++;
				break;
			}
			for(int k = 0; k < c.size(); k++){
				temp_v1[k].resize(new_degree[k]);
				temp_v2[k].resize(new_degree[k]);
				poly[k].resize(2*new_degree[k]);
				l1[k].resize(2*new_degree[k]);
				l2[k].resize(2*new_degree[k]);
			
				if(new_c[k] <= 4){
					poly[k].clear();
					poly[k].resize(new_degree[k]*(new_degree[k]+1)/2);
				}else{
					if(k == 0){
						F::inv(ilen[k], 1ULL<<(new_c[k]));
						
						w.resize(1ULL<<(new_c[k]));
						w_prod.resize(1ULL<<(new_c[k]+1));
						rev_prod.resize(1ULL<<(new_c[k]+1));
						rev.resize(1ULL<<(new_c[k]));
						prepare_fft_aux(w,rev,w_prod,rev_prod,1ULL<<(new_c[k]+1));
					}		
				}
			}
		}
	}

	
	Proof.polynomials = poly_proofs;
    Proof.c = c[0];
    Proof.randomness = rand;

    Proof.new_sum = F(0);
    for(int k = poly_proofs[0].size()-degree[0]; k < poly_proofs[0].size(); k++){
        Proof.new_sum += poly_proofs[0][k];
    }

    beta.clear();beta_partitions.clear();
    partitions_rand.clear();
	vector<F> conv;
	compute_convolution(Lv,conv);

	for(int j = 0; j < (int)log2(conv.size()); j++){
        partitions_rand.push_back(beta_rand[j]);
    }
    precompute_beta(partitions_rand,beta);
	Proof.beta2 = partitions_rand;
	
    reset_stream(fp1);
	
	
	int final_size = 1;
    for(int i = 0; i < Lv.size(); i++){
        final_size *= Lv[i].size();
    }
	vector<vector<F>> final_v1(counter.size()),final_v2(counter.size());
	
	for(int j = 0; j < counter.size(); j++){
		//final_size = size[0]/final_size;
		final_v1[j].resize(size[j]/final_size,F_ZERO);
		final_v2[j].resize(size[j]/final_size,F_ZERO);
	}

    for(int j = 0; j < counter.size(); j++)counter[j] = 0;
	
	for(int j = 0; j < size[0]/MAX_CHUNCK; j++){
		stream_s = clock();
		read_stream_batch(fp1,v,2*MAX_CHUNCK,distance);
		for(int l = 0; l < c.size(); l++){
			if(idx[l] == MAX_CHUNCK)idx[l] = 0;
			for(int k = 0; k < MAX_CHUNCK/(1<<(l*distance)); k++){
				v1[l][idx[l]] = v[l][2*k];
				v2[l][idx[l]] = v[l][2*k+1];
				idx[l]++;
			}
		}
		stream_e = clock();
		stream_access_time += (double)(stream_e-stream_s)/(double)CLOCKS_PER_SEC;
		for(int n = 0; n < c.size(); n++){
			if(idx[n] != MAX_CHUNCK) continue;
			for(int k = 0; k < MAX_CHUNCK/beta.size(); k++){
            	for(int l = 0; l < beta.size(); l++){
            	    v1[n][k*beta.size() + l] = v1[n][k*beta.size() + l]*beta[l];
            	}
        	}
			for(int k = 0; k < MAX_CHUNCK/conv.size(); k++){
            	for(int l = 0; l < conv.size(); l++){
                	final_v1[n][counter[n]] += conv[l]*v1[n][k*conv.size() + l];
			    	final_v2[n][counter[n]] += conv[l]*v2[n][k*conv.size() + l];
            	}
            	counter[n]++;
        	}
		}
	}
		
	
    partitions_rand.clear();
    for(int j = (int)log2(conv.size()); j < beta_rand.size(); j++){
        partitions_rand.push_back(beta_rand[j]);
    }
    precompute_beta(partitions_rand,beta_partitions);
	Proof.beta1 = partitions_rand;


	//vector<F> a = generate_randomness(c.size(),rand[rand.size()-1]);
    proof P = _generate_batch_3product_sumcheck_proof(final_v1,final_v2,beta_partitions,a_r,a_r[a_r.size()-1]);
	
	
	Proof.P.push_back(P);
    
	// Compute convolution
	
	
	
	reset_stream(fp1);
	//printf("%d,%d,%d\n",P.randomness[0].size(),final_v1.size(),conv.size());
	int conv_size = conv.size();
	vector<F> _beta;precompute_beta(P.randomness[0],_beta);
	
	vector<vector<F>> partial_eval1(counter.size()),partial_eval2(counter.size());//partial_eval(conv_size);
	
	for(int i = 0; i < counter.size(); i++){
		counter[i] = 0;
		partial_eval1[i].resize(conv_size,F_ZERO);
		partial_eval2[i].resize(conv_size,F_ZERO);
		
	}

	for(int i = 0; i < size[0]/MAX_CHUNCK; i++){
		stream_s = clock();
		
		read_stream_batch(fp1,v,2*MAX_CHUNCK,distance);
		
		for(int l = 0; l < c.size(); l++){
			if(idx[l] == MAX_CHUNCK)idx[l] = 0;
			for(int k = 0; k < MAX_CHUNCK/(1<<(l*distance)); k++){
				v1[l][idx[l]] = v[l][2*k];
				v2[l][idx[l]] = v[l][2*k+1];
				idx[l]++;
			}
		}
		
		stream_e = clock();
		stream_access_time += (double)(stream_e-stream_s)/(double)CLOCKS_PER_SEC;
		
		for(int n = 0; n < c.size(); n++){
			if(idx[n] != MAX_CHUNCK) continue;	
			for(int j = 0; j < MAX_CHUNCK; j+=conv_size){
				for(int k = 0; k < conv_size; k++){
					partial_eval1[n][k] += _beta[counter[n]]*v1[n][j + k];
					partial_eval2[n][k] += _beta[counter[n]]*v2[n][j + k];
				}
				counter[n]++;
			}
		}
	}
	
	_beta.clear();
	
	vector<F> a = generate_randomness(size.size()+2,P.randomness[0][P.randomness[0].size()-1]);
	//vector<F> a2 = generate_randomness(2,a[a.size()-1]);
    vector<F> _partial_eval1(partial_eval1[0].size(),F(0)),_partial_eval2(partial_eval2[0].size(),F(0));
	for(int i = 0; i < size.size(); i++){
		for(int j = 0; j < partial_eval1[i].size(); j++){
			_partial_eval1[j] += a[i]*partial_eval1[i][j];
		}
		for(int j = 0; j < partial_eval2[i].size(); j++){
			_partial_eval2[j] += a[i]*partial_eval2[i][j];
		}
	}

    
	
	vector<F> V1,V2;
	for(int i = 0; i < a_r.size(); i++){
		V1.push_back(P.vr[ 1 + 2*i ]);
		V2.push_back(P.vr[ 1 + 2*i + 1]);
	}

	F sum = F(0);
	for(int i = 0; i < V1.size(); i++){
		sum += V1[i]*a[i]*a[a.size()-2];
		sum += V2[i]*a[i]*a[a.size()-1];
	}
	//sum = 0;
	//for(int i = 0; i < V.size(); i++){
	//	sum += a[i]*V[i]; 
	//}

	vector<vector<F>> _v1,_v2,_v3;
	_v1.push_back(_partial_eval1);_v1.push_back(_partial_eval2);
    _v2.push_back(conv);_v2.push_back(conv);
    _v3.push_back(beta);
	vector<F> a2;a2.push_back(a[a.size()-2]);a2.push_back(a[a.size()-1]);
    proof P2 = generate_batch_3product_sumcheck_proof(_v1,_v2,_v3,a2,a2[1]);
    //proof P2 = _generate_3product_sumcheck_proof(conv,_partial_eval1,beta,a[a.size()-1]);
	Proof.P.push_back(P2);
    
	if(sum != P2.c_poly[0].eval(F(0))+P2.c_poly[0].eval(F(1))){
		printf(">>Error \n");
		exit(-1);
	}
	Proof.a = a;
	beta.clear();
	
	//precompute_beta(P2.randomness[0],beta);
	vector<F> evals(2*partial_eval1.size(),F(0));
	for(int i = 0; i  < partial_eval1.size(); i++){
		evals[i] = evaluate_vector(partial_eval1[i],P2.randomness[0]); //beta[j]*partial_eval1[i][j];
	}
	for(int i = 0; i  < partial_eval1.size(); i++){
		evals[i+partial_eval1.size()] = evaluate_vector(partial_eval2[i],P2.randomness[0]);
	}
	
	for(int i = 0; i < partial_eval1.size(); i++){
		P2.vr[0] -= a[i]*evals[i];	
		P2.vr[3] -= a[i]*evals[i+partial_eval1.size()];	
	}
	if(P2.vr[0] != 0 || P2.vr[3] != 0)printf("Error\n");
	Proof.vr = evals;
	//Proof.vr.push_back(P2.vr[0]);
    //Proof.vr.push_back(P2.vr[3]);
	e = clock();
	printf("Total sumcheck : %lf,%lf\n", (double)(e-s)/(double)CLOCKS_PER_SEC, stream_access_time);
	v1.clear();
	v2.clear();
	beta.clear();
	_beta.clear();
	conv.clear();
	partial_eval1.clear();
	partial_eval2.clear();
	final_v1.clear();
	final_v2.clear();
	
	return Proof;
}




proof_stream generate_3product_sumcheck_proof_stream(stream_descriptor fp1, stream_descriptor fp2, size_t size, vector<F> beta_rand, F previous_r, int mod){
	if(MAX_CHUNCK < size/MAX_CHUNCK){
		printf("Error, increase buffer %d\n",size);
		exit(-1);
	}
	
	if(MAX_CHUNCK >= size){
        return local_3product_sumcheck_proof(fp1, fp2, size, beta_rand, previous_r, mod);
    }
	int total_c = (int)log2(size/MAX_CHUNCK);
    int c = 4;
	if(c >= total_c){
        c = total_c;
    }else{
		c = (int)log2(log2(size/MAX_CHUNCK)) + 1;
	}
	
	int new_c = 0,offset,poly_degree,new_degree  = 0;
	F omega = getRootOfUnit(c);
	int degree = 1<<c;
    proof_stream Proof;
    F len = F(1<<c);
    F ilen;
	Proof.size = size;
    F::inv(ilen, len);

	vector<F> v1(MAX_CHUNCK),v2(MAX_CHUNCK);
	vector<F> temp_v1(degree),temp_v2(degree);
	vector<F> poly(2*degree),l1(2*degree),l2(2*degree);
    if(c <= 4){
        poly.clear();
        poly.resize(degree*(degree+1)/2);
    }
    vector<vector<F>> poly_proofs;
	vector<vector<F>> Lv;
	vector<F> rand;
    vector<F> v;
	if(fp2.pos == -1){
		v.resize(2*MAX_CHUNCK);
	}
	vector<u32> rev,rev_prod;
	vector<F> w,w_prod;
	
	
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
    int counter;
    clock_t s,e;
	clock_t stream_s,stream_e;
	double stream_access_time = 0.0;
	F check_sum = F(-1),test_sum = F(0);
	int i;
	F one = F(1);
	F temp_eval;
	
	s = clock();
	for(i = 0; i < 2; i++){
	    counter = 0;
		
		reset_stream(fp1);
		if(fp2.pos != -1){
            reset_stream(fp2);
        }
        for(int j = 0; j < poly.size(); j++){
			poly[j] = F_ZERO;
		}
		for(int j = 0; j < size/MAX_CHUNCK; j++){
			stream_s = clock();
			if(fp2.pos != -1){
				read_stream(fp1,v1,MAX_CHUNCK);
				read_stream(fp2,v2,MAX_CHUNCK);
			}else{
				if(mod == RANGE){
					read_stream(fp1,v,MAX_CHUNCK);
					for(int k = 0; k < MAX_CHUNCK; k++){
						v1[k] = v[k];
						v2[k] = one - v[k];
					}
				}else if(mod == SUM_INV){
					read_stream(fp1,v,MAX_CHUNCK);
					for(int k = 0; k < MAX_CHUNCK; k++){
						v1[k] = v[k];
						v2[k].inv(v2[k],v1[k]);
					}
					
				}
				else{        
                    read_stream(fp1,v,2*MAX_CHUNCK);
					for(int k = 0; k < MAX_CHUNCK; k++){
						v1[k] = v[2*k];
						v2[k] = v[2*k+1];
					}
				}
			}
			stream_e = clock();
			stream_access_time += (double)(stream_e-stream_s)/(double)CLOCKS_PER_SEC;
            for(int h = 0; h < MAX_CHUNCK; h+=size/MAX_CHUNCK){
				for(int k = 0; k < size/MAX_CHUNCK; k++){
					v1[h + k] = beta[counter]*beta_partitions[k]*v1[h+k];
				}
				counter++;
			}
			for(int k = 0; k < i; k++){
				
					for(int l = 0; l < MAX_CHUNCK/(1ULL<<(c*(k+1))); l++){
						v1[l] = Lv[k][0]*v1[Lv[k].size()*l];
						v2[l] = Lv[k][0]*v2[Lv[k].size()*l];
						for(int h = 1; h < Lv[k].size(); h++){
							v1[l] += Lv[k][h]*v1[degree*l + h];
							v2[l] += Lv[k][h]*v2[degree*l + h];
						}
					}
				
				
			}
			int current_size = MAX_CHUNCK/(1<<(c*i));
			if(new_c == 0){
				offset = current_size/degree;
				poly_degree = degree; 
			}else{
				offset = current_size/new_degree;
				poly_degree = new_degree; 
			}
			//printf("%d,%d \n",offset,poly_degree);
			for(int k = 0; k < offset; k++){
				for(int l = 0; l < poly_degree; l++){
					temp_v1[l] = v1[poly_degree*k + l];
					temp_v2[l] = v2[poly_degree*k + l];
					//test_sum += temp_v1[l]*temp_v2[l]; 
					l1[l + poly_degree] = F_ZERO;
					l2[l+poly_degree] = F_ZERO;
				}
				if((c <= 4 && new_c == 0) || (new_c <= 4)){
                    
                    int idx = 0;
					for(int l = 0; l < poly_degree; l++){
						for(int h = l+1; h < poly_degree; h++){
							poly[idx] += temp_v1[l]*temp_v2[h] + temp_v1[h]*temp_v2[l];
                            idx++;
                        }
					}
                    for(int l = 0; l < poly_degree; l++){
                        poly[idx] += temp_v1[l]*temp_v2[l];
                        idx++;
                    }
             
             	}else{
                	my_fft(temp_v1,w,rev,ilen,true);
					my_fft(temp_v2,w,rev,ilen,true);
					
					for(int l = 0; l < poly_degree; l++){
						l1[l] = temp_v1[l];
						l2[l] = temp_v2[l];
					}
					
					my_fft(l1,w_prod,rev_prod,F(1),false);
					my_fft(l2,w_prod,rev_prod,F(1),false);
					for(int l = 0; l < 2*poly_degree; l++){
						poly[l] += l1[l]*l2[l];
						
					}
				}
				
			}
		}
        poly_proofs.push_back(poly);
		
		F r;r.setByCSPRNG();
		rand.push_back(r);
		if(!new_c){
			
			Lv.push_back(compute_lagrange_coeff(omega,r,degree));
		}else{
			
			if(recursion == 1 && new_c > 4){	
				Proof.RP = reduce_proof_size(poly,new_c,getRootOfUnit(new_c+1),r,r);
			}
			F new_omega = getRootOfUnit((int)log2(new_degree));
			Lv.push_back(compute_lagrange_coeff(new_omega,r,new_degree));		
		}
		if(!new_c){
			
			new_c = total_c -c;
			new_degree = 1ULL<<new_c;
			
			if(new_c == 0){
				i++;
				break;
			}
			temp_v1.resize(new_degree);
			temp_v2.resize(new_degree);
			poly.resize(2*new_degree);
			l1.resize(2*new_degree);
			l2.resize(2*new_degree);
		
			if(new_c <= 4){
		        poly.clear();
        		poly.resize(new_degree*(new_degree+1)/2);
    		}else{
				F::inv(ilen, 1ULL<<(new_c));
				w.resize(1ULL<<(new_c));
				w_prod.resize(1ULL<<(new_c+1));
				rev_prod.resize(1ULL<<(new_c+1));
				rev.resize(1ULL<<(new_c));
				prepare_fft_aux(w,rev,w_prod,rev_prod,1ULL<<(new_c+1));
		
			}
		}
	}
    Proof.polynomials = poly_proofs;
    Proof.c = c;
    Proof.randomness = rand;

    Proof.new_sum = F(0);
    for(int k = poly_proofs[0].size()-degree; k < poly_proofs[0].size(); k++){
        Proof.new_sum += poly_proofs[0][k];
    }

    beta.clear();
	
	vector<F>().swap(beta_partitions);
	beta_partitions.clear();

    partitions_rand.clear();
	vector<F> conv;
	compute_convolution(Lv,conv);

	for(int j = 0; j < (int)log2(conv.size()); j++){
        partitions_rand.push_back(beta_rand[j]);
    }
    precompute_beta(partitions_rand,beta);
	Proof.beta2 = partitions_rand;
	
    reset_stream(fp1);
	if(fp2.pos != -1){
        reset_stream(fp2);
    }
	int final_size = 1;
    for(int i = 0; i < Lv.size(); i++){
        final_size *= Lv[i].size();
    }
    final_size = size/final_size;
    vector<F> final_v1(final_size,F_ZERO),final_v2(final_size,F_ZERO);

    counter = 0;
	for(int j = 0; j < size/MAX_CHUNCK; j++){
		int final_size;
		stream_s = clock();
		if(fp2.pos != -1){
			read_stream(fp1,v1,MAX_CHUNCK);
			read_stream(fp2,v2,MAX_CHUNCK);
		}else{
			if(mod == RANGE){
				read_stream(fp1,v,MAX_CHUNCK);
				for(int k = 0; k < MAX_CHUNCK; k++){
					v1[k] = v[k];
					v2[k] = one - v[k];
				}
			}else if(mod == SUM_INV){
					read_stream(fp1,v,MAX_CHUNCK);
					for(int k = 0; k < MAX_CHUNCK; k++){
						v1[k] = v[k];
						v2[k].inv(v2[k],v1[k]);
					}
				}
			else{
                read_stream(fp1,v,2*MAX_CHUNCK);
				for(int k = 0; k < MAX_CHUNCK; k++){
					v1[k] = v[2*k];
					v2[k] = v[2*k+1];
				}
			}
		}
		stream_e = clock();
		stream_access_time += (double)(stream_e-stream_s)/(double)CLOCKS_PER_SEC;

        for(int k = 0; k < MAX_CHUNCK/beta.size(); k++){
            for(int l = 0; l < beta.size(); l++){
                v1[k*beta.size() + l] = v1[k*beta.size() + l]*beta[l];
            }
        }
		 for(int k = 0; k < MAX_CHUNCK/conv.size(); k++){
            
				for(int l = 0; l < conv.size(); l++){
                	final_v1[counter] += conv[l]*v1[k*conv.size() + l];
			    	final_v2[counter] += conv[l]*v2[k*conv.size() + l];
            	}
			
			
            counter++;
        }
		
        
	}
    partitions_rand.clear();
    for(int j = (int)log2(conv.size()); j < beta_rand.size(); j++){
        partitions_rand.push_back(beta_rand[j]);
    }
    precompute_beta(partitions_rand,beta_partitions);
	Proof.beta1 = partitions_rand;
    //printf("%d,%d \n",final_v1.size(),beta_partitions.size());
    proof P = _generate_3product_sumcheck_proof(final_v1,final_v2,beta_partitions,rand[rand.size()-1]);
	vector<F>().swap(final_v1);
	vector<F>().swap(final_v2);
	
	Proof.P.push_back(P);
    //proof P = generate_2product_sumcheck_proof(final_v1,final_v2,rand[rand.size()-1]);
	// Compute convolution
	
	

	reset_stream(fp1);
	if(fp2.pos != -1){
        reset_stream(fp2);
    }
    //printf("%d,%d,%d\n",P.randomness[0].size(),final_v1.size(),conv.size());
	int conv_size = conv.size();
	vector<F> _beta;precompute_beta(P.randomness[0],_beta);
	vector<F> partial_eval1(conv_size,F(0)),partial_eval2(conv_size,F(0)),partial_eval(conv_size);
	counter = 0;
	for(int i = 0; i < size/MAX_CHUNCK; i++){
		stream_s = clock();
		if(fp2.pos != -1){
			read_stream(fp1,v1,MAX_CHUNCK);
			read_stream(fp2,v2,MAX_CHUNCK);
		}else{
			if(mod == RANGE){
				read_stream(fp1,v,MAX_CHUNCK);
				for(int j = 0; j < MAX_CHUNCK; j++){
					v1[j] = v[j];
					v2[j] = one - v[j];
				}
			}else if(mod == SUM_INV){
					read_stream(fp1,v,MAX_CHUNCK);
					for(int k = 0; k < MAX_CHUNCK; k++){
						v1[k] = v[k];
						v2[k].inv(v2[k],v1[k]);
					}
				}
			else{
                read_stream(fp1,v,2*MAX_CHUNCK);
				for(int j = 0; j < MAX_CHUNCK; j++){
					v1[j] = v[2*j];
					v2[j] = v[2*j+1];
				}
			}
		}
		stream_e = clock();
		stream_access_time += (double)(stream_e-stream_s)/(double)CLOCKS_PER_SEC;

        for(int j = 0; j < MAX_CHUNCK; j+=conv_size){
			if(mod == RANGE){
				for(int k = 0; k < conv_size; k++){
					temp_eval = _beta[counter]*v1[j + k];
					partial_eval1[k] += temp_eval;
					//partial_eval2[k] += _beta[counter]*v2[j + k];
					partial_eval2[k] += _beta[counter] - temp_eval;
				}
			}else{
				for(int k = 0; k < conv_size; k++){
					partial_eval1[k] += _beta[counter]*v1[j + k];
					partial_eval2[k] += _beta[counter]*v2[j + k];
				}
			}
			
			counter++;
		}
	}
	
	_beta.clear();
	vector<F> a = generate_randomness(2,P.randomness[0][P.randomness[0].size()-1]);
	
    
    vector<vector<F>> _v1,_v2,_v3;
    _v1.push_back(partial_eval1);_v1.push_back(partial_eval2);
    _v2.push_back(conv);_v2.push_back(conv);
    _v3.push_back(beta);
    proof P2 = generate_batch_3product_sumcheck_proof(_v1,_v2,_v3,a,a[1]);
    
	//proof P2 = _generate_3product_sumcheck_proof(conv,partial_eval1,beta,rand[rand.size()-1]);
	Proof.P.push_back(P2);
    
	if(a[0]*P.vr[0] + a[1]*P.vr[1] != P2.c_poly[0].eval(F(0))+P2.c_poly[0].eval(F(1))){
		printf(">>Error \n");
		exit(-1);
	}
	Proof.a = a;
    Proof.vr.push_back(P2.vr[0]);
    Proof.vr.push_back(P2.vr[3]);
	e = clock();
	printf("Total sumcheck : %lf,%lf\n", (double)(e-s)/(double)CLOCKS_PER_SEC, stream_access_time);
	v1.clear();
	v2.clear();
	_v1[0].clear();
	_v1[1].clear();
	_v2[0].clear();
	_v2[1].clear();
	_v3[0].clear();
	beta.clear();
	_beta.clear();
	conv.clear();
	partial_eval1.clear();
	partial_eval2.clear();
	final_v1.clear();
	final_v2.clear();
	
	return Proof;
}


proof_stream generate_3product_sumcheck_proof_disk(stream_descriptor fp1, stream_descriptor fp2, size_t size, vector<F> beta_rand, F previous_r, int mod){
	proof_stream Pr;
	int M = 8;
   
	vector<int> _M;
			
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
	vector<F> v;
	if(fp2.pos == -1){
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
	
    int seg = MAX_CHUNCK/M,counter;
	
	

	while(1){
        reset_stream(fp1);
		if(fp2.pos != -1){
            reset_stream(fp2);
        }
		counter = 0;
		if((size/MAX_CHUNCK)/(cluster_size*M) == 0){
			M = (size/MAX_CHUNCK)/cluster_size;
		}
		for(int i = 0; i < size/MAX_CHUNCK; i++){
			if(fp2.pos != -1){
				read_stream(fp1,v1,MAX_CHUNCK);
				read_stream(fp2,v2,MAX_CHUNCK);
			}else{
				if(mod == RANGE){
					read_stream(fp1,v,MAX_CHUNCK);
					for(int j = 0; j < MAX_CHUNCK; j++){
						v1[j] = v[j];
						v2[j] = F(1) - v[j];
					}
				}else{
                    
                    read_stream(fp1,v,2*MAX_CHUNCK);
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
			/*else{
				for(int j = 0; j < MAX_CHUNCK; j++){
					sum += v1[j]*v2[j];
				}
			}*/


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
    reset_stream(fp1);
    if(fp2.pos != -1){
        reset_stream(fp2);
	}
  
  
  	vector<F> fv1(MAX_CHUNCK),fv2(MAX_CHUNCK);
	counter = 0;
	for(int i = 0; i < size/MAX_CHUNCK; i++){
		if(fp2.pos != -1){
				read_stream(fp1,v1,MAX_CHUNCK);
				read_stream(fp2,v2,MAX_CHUNCK);
		}else{
			if(mod == RANGE){
				read_stream(fp1,v,MAX_CHUNCK);
				for(int j = 0; j < MAX_CHUNCK; j++){
					v1[j] = v[j];
					v2[j] = F(1) - v[j];
				}
			}else{
				read_stream(fp1,v,2*MAX_CHUNCK);
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
	reset_stream(fp1);
    if(fp2.pos != -1){
        reset_stream(fp2);
	}

	for(int i = 0; i < size/MAX_CHUNCK; i++){
		if(fp2.pos != -1){
			read_stream(fp1,v1,MAX_CHUNCK);
			read_stream(fp2,v2,MAX_CHUNCK);
		}else{
			if(mod == RANGE){
				read_stream(fp1,v,MAX_CHUNCK);
				for(int j = 0; j < MAX_CHUNCK; j++){
					v1[j] = v[j];
					v2[j] = F(1) - v[j];
				}
			}else{
				read_stream(fp1,v,2*MAX_CHUNCK);
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



vector<F> prepare_matrix_streaming(vector<stream_descriptor> fd, vector<size_t> fd_cols, vector<size_t> fd_size, size_t row_size, vector<F> r, int cols){
	vector<F> compressed_col(cols,F(0));
	vector<F> v1(MAX_CHUNCK);
	vector<F> x1,x2,beta1,beta2;
	
	int counter = 0;
	for(int k = 0; k < fd.size(); k++){
		reset_stream(fd[k]);
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
		
		
		for(int i = 0; i < fd_size[k]/_MAX_CHUNCK; i++){
			read_stream(fd[k],v1,_MAX_CHUNCK);
			for(int l = 0; l < _MAX_CHUNCK/fd_cols[k]; l++){
				F prod =  beta1[l]*beta2[i];
				for(int j = 0; j < fd_cols[k]; j++){
					compressed_col[counter + j] += prod*v1[l*fd_cols[k] + j];
				}
			}
		}
		counter += fd_cols[k];
	
	}
    return compressed_col;

}	

void _prove_bit_decomposition_stream(stream_descriptor bits_fd, size_t size, vector<F> r1, F previous_sum, F previous_r, int domain){
	vector<F> powers;
	powers.push_back(F(1));
	for(int i = 1; i < domain; i++){
		powers.push_back(F(2)*powers[i-1]);
	}
	pad_vector(powers);
	
	vector<stream_descriptor> fd;fd.push_back(bits_fd);
	vector<size_t> fd_cols; fd_cols.push_back(domain);
	vector<size_t> fd_size; fd_size.push_back(size); 
	vector<F> prod = prepare_matrix_streaming(fd, fd_cols, fd_size, size/domain, r1, domain);
	proof Pr1 = generate_2product_sumcheck_proof(prod,powers,previous_r);
	verify_2product_sumcheck(Pr1,Pr1.q_poly[0].eval(F_ONE)+Pr1.q_poly[0].eval(F_ZERO));
	
	//if(previous_sum != Pr1.q_poly[0].eval(0) + Pr1.q_poly[0].eval(1)){
	//	printf("Error in bit_decomposition 1\n");
	//	exit(-1);
	//}

	vector<F> r2 = generate_randomness(int(log2(size)),Pr1.final_rand);
	reset_stream(bits_fd);
    
    stream_descriptor dummy_descriptor;dummy_descriptor.pos = -1;

    proof_stream P = generate_3product_sumcheck_proof_stream(bits_fd, dummy_descriptor, size, r2, r2[r2.size()-1], RANGE);
	
	verify_stream_3product_sumcheck(P, r2, F(0));
	
	
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


proof_stream generate_2product_sumcheck_proof_stream_local(stream_descriptor fp1, vector<vector<F>> beta_rand,vector<F> a,size_t size, F previous_r){
	proof_stream P;    
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
	
	read_stream(fp1,v,size);
	
	P.P.push_back(generate_2product_sumcheck_proof(beta,v,previous_r));
    
	P.vr.push_back(P.P[0].vr[1]);
	P.new_sum = P.P[0].q_poly[0].eval(F(0)) + P.P[0].q_poly[0].eval(F(1));
	return P;
}

proof_stream generate_2product_sumcheck_proof_stream_local_2(stream_descriptor fp1, stream_descriptor fp2,size_t size, F previous_r){
	proof_stream P;    
    vector<F> beta,temp_beta;
	vector<F> v1(size),v2(size);
	
	read_stream(fp1,v1,size);
	read_stream(fp2,v2,size);
	
	P.P.push_back(generate_2product_sumcheck_proof(v1,v2,previous_r));
    P.vr.push_back(P.P[0].vr[1]);
	P.new_sum = P.P[0].q_poly[0].eval(F(0)) + P.P[0].q_poly[0].eval(F(1));
	return P;
}

proof_stream generate_2product_sumcheck_proof_stream(stream_descriptor fp1, stream_descriptor fp2,size_t size, F previous_r){
	if(MAX_CHUNCK < size/MAX_CHUNCK){
		printf("Error, increase buffer %d\n",size);
		exit(-1);
	}
    
	if(MAX_CHUNCK >= size){
		return generate_2product_sumcheck_proof_stream_local_2(fp1,fp2,size, previous_r);
	}


    int total_c = (int)log2(size/MAX_CHUNCK);
    int c = 4;
	if(c >= total_c){
        c = total_c;
    }else{
		c = (int)log2(log2(size/MAX_CHUNCK)) + 1;
	}
    printf("%d : \n", c);
	int new_c = 0,offset,poly_degree,new_degree  = 0;
	F omega = getRootOfUnit(c);
	int degree = 1<<c;
    proof_stream P;
    F len = F(1<<c);
    F ilen;
	P.size = size;
    F::inv(ilen, len);

	vector<F> v1(MAX_CHUNCK),v2(MAX_CHUNCK);
	vector<F> temp_v1(degree),temp_v2(degree);
	vector<F> poly(2*degree),l1(2*degree),l2(2*degree);
    if(c <= 4){
        poly.clear();
        poly.resize(degree*(degree+1)/2);
    }
    vector<vector<F>> poly_proofs;
	vector<vector<F>> Lv;
	vector<F> rand;
    vector<F> v;
	
	vector<u32> rev_prod,rev;
    vector<F> w_prod,w;
		

	if(size > (size_t)MAX_CHUNCK*(size_t)MAX_CHUNCK){
		printf("Increase MAX_CHUNCK, size : %d\n",size );
		exit(-1);
	}

	vector<vector<vector<F>>> Acc_Sums;
	
	
    
    vector<quadratic_poly> p;
	vector<F> rand_v,r;
	vector<vector<F>> R1,R2;
	int temp_size = size;
	
    
	
	int counter,i =0;
    //printf("%d,%d \n",1<<c,size/MAX_CHUNCK);
    
    
    
    for(i = 0; i < 2; i++){
	    counter = 0;
		reset_stream(fp1);
		reset_stream(fp2);
        for(int j = 0; j < poly.size(); j++){
			poly[j] = F_ZERO;
		}
      
	  	for(int j = 0; j < size/MAX_CHUNCK; j++){
			read_stream(fp1,v1,MAX_CHUNCK);
			read_stream(fp2,v2,MAX_CHUNCK);
			
			//compute_temp_beta(beta1,beta2,a,v2,j);
			
			for(int k = 0; k < i; k++){
				for(int l = 0; l < MAX_CHUNCK/(1ULL<<(c*(k+1))); l++){
					v1[l] = Lv[k][0]*v1[Lv[k].size()*l];
					v2[l] = Lv[k][0]*v2[Lv[k].size()*l];
					for(int h = 1; h < Lv[k].size(); h++){
						v1[l] += Lv[k][h]*v1[degree*l + h];
						v2[l] += Lv[k][h]*v2[degree*l + h];
					}
				}
			}
			int current_size = MAX_CHUNCK/(1<<(c*i));
			if(new_c == 0){
				offset = current_size/degree;
				poly_degree = degree; 
			}else{
				offset = current_size/new_degree;
				poly_degree = new_degree; 
                //printf("%d\n",current_size);
            }
			//printf("%d,%d \n",offset,poly_degree);
			for(int k = 0; k < offset; k++){
				for(int l = 0; l < poly_degree; l++){
					temp_v1[l] = v1[poly_degree*k + l];
					temp_v2[l] = v2[poly_degree*k + l];
					l1[l + poly_degree] = 0;
					l2[l+poly_degree] = 0;
				}
				if((c <= 4 && new_c == 0) || (new_c <= 4)){
                    
                    int idx = 0;
					for(int l = 0; l < poly_degree; l++){
						for(int h = l+1; h < poly_degree; h++){
							poly[idx] += temp_v1[l]*temp_v2[h] + temp_v1[h]*temp_v2[l];
                            idx++;
                        }
					}
                    for(int l = 0; l < poly_degree; l++){
                        poly[idx] += temp_v1[l]*temp_v2[l];
                        idx++;
                    }
             
             	}else{
                    
                    my_fft(temp_v1,w,rev,ilen,true);
					my_fft(temp_v2,w,rev,ilen,true);
					
					for(int l = 0; l < poly_degree; l++){
						l1[l] = temp_v1[l];
						l2[l] = temp_v2[l];
					}
					my_fft(l1,w_prod,rev_prod,F(1),false);
					my_fft(l2,w_prod,rev_prod,F(1),false);
					for(int l = 0; l < 2*poly_degree; l++){
						poly[l] += l1[l]*l2[l];
					}
				}
				
			}
		}
        poly_proofs.push_back(poly);
		
		F r;r.setByCSPRNG();
		rand.push_back(r);
		if(!new_c){
			Lv.push_back(compute_lagrange_coeff(omega,r,degree));
		}else{
			if(recursion == 1 && new_c > 4){	
				P.RP = reduce_proof_size(poly,new_c,getRootOfUnit(new_c+1),r,r);
			}
			F new_omega = getRootOfUnit((int)log2(new_degree));
            Lv.push_back(compute_lagrange_coeff(new_omega,r,new_degree));		
		}
		
		
		if(!new_c){
			
			new_c = total_c -c;
			new_degree = 1ULL<<new_c;
			
			if(new_c == 0){
				i++;
				break;
			}
			
			temp_v1.resize(new_degree);
			temp_v2.resize(new_degree);
			poly.resize(2*new_degree);
			l1.resize(2*new_degree);
			l2.resize(2*new_degree);
			if(new_c <= 4){
		        poly.clear();
        		poly.resize(new_degree*(new_degree+1)/2);
    		}else{
				F::inv(ilen, 1ULL<<(new_c));
				w.resize(1ULL<<(new_c));
				w_prod.resize(1ULL<<(new_c+1));
				rev_prod.resize(1ULL<<(new_c+1));
				rev.resize(1ULL<<(new_c));
				prepare_fft_aux(w,rev,w_prod,rev_prod,1ULL<<(new_c+1));
		
			}
		}
	}
    
    P.polynomials = poly_proofs;
    P.c = c;
    P.randomness = rand;
    P.new_sum = F(0);
    for(int k = poly_proofs[0].size()-degree; k < poly_proofs[0].size(); k++){
        P.new_sum += poly_proofs[0][k];
    }
    reset_stream(fp1);
	reset_stream(fp2);
	
    // SOME CHANGES
    int final_size = 1;
    for(int i = 0; i < Lv.size(); i++){
       
        final_size *= Lv[i].size();
    }
    final_size = size/final_size;
    
    
	vector<F> final_v1(final_size,F_ZERO),final_v2(final_size,F_ZERO);
	
	
    counter = 0;
    vector<F> conv;
	compute_convolution(Lv,conv);

	for(int j = 0; j < size/MAX_CHUNCK; j++){
		int final_size;
		read_stream(fp1,v1,MAX_CHUNCK);
		read_stream(fp2,v2,MAX_CHUNCK);
			
		//compute_temp_beta(beta1,beta2,a,v2,j);
		
        int _c = 0;
        for(int k = 0; k < MAX_CHUNCK/conv.size(); k++){
            for(int l = 0; l < conv.size(); l++){
                final_v1[counter] += conv[l]*v1[k*conv.size() + l];
			    final_v2[counter] += conv[l]*v2[k*conv.size() + l];
            }
            counter++;
        }
	}
    
    //printf("%d,%d \n",final_v1.size(),beta_partitions.size());
    proof P1 = generate_2product_sumcheck_proof(final_v1,final_v2,rand[rand.size()-1]);
	P.P.push_back(P1);
    //proof P = generate_2product_sumcheck_proof(final_v1,final_v2,rand[rand.size()-1]);
	// Compute convolution
	
	
	reset_stream(fp1);
	reset_stream(fp2);
	
    //printf("%d,%d,%d\n",P.randomness[0].size(),final_v1.size(),conv.size());
	int conv_size = conv.size();
	vector<F> _beta;precompute_beta(P1.randomness[0],_beta);
	vector<F> partial_eval1(conv_size,F(0)),partial_eval2(conv_size,F(0));
	counter = 0;
	
    for(int i = 0; i < size/MAX_CHUNCK; i++){
		
        read_stream(fp1,v1,MAX_CHUNCK);
		read_stream(fp2,v2,MAX_CHUNCK);
		
		//compute_temp_beta(beta1,beta2,a,v2,i);
		
        for(int j = 0; j < MAX_CHUNCK; j+=conv_size){
			for(int k = 0; k < conv_size; k++){
				partial_eval1[k] += _beta[counter]*v1[j + k];
				partial_eval2[k] += _beta[counter]*v2[j + k];
			}
			counter++;
		}
	}
	
    _beta.clear();
	vector<F> _a = generate_randomness(2,P1.randomness[0][P1.randomness[0].size()-1]);
	
    
	vector<vector<F>> _v1,_v2,_v3;
    _v1.push_back(partial_eval1);_v1.push_back(partial_eval2);
    _v2.push_back(conv);_v2.push_back(conv);
    

    proof P2 = generate_batch_3product_sumcheck_proof(_v1,_v2,_v3,_a,_a[1]);
    
    //proof P2 = _generate_3product_sumcheck_proof(conv,partial_eval1,beta,rand[rand.size()-1]);
	
	P.P.push_back(P2);
	P.a = _a;

    if(_a[0]*P1.vr[0] + _a[1]*P1.vr[1] != P2.c_poly[0].eval(F(0))+P2.c_poly[0].eval(F(1))){
		printf(">>Error \n");
		exit(-1);
	}
    
    P.vr.push_back(P2.vr[0]);
    P.vr.push_back(P2.vr[2]);
	
    return P;

}



proof_stream generate_2product_sumcheck_proof_stream_beta(stream_descriptor fp1, vector<vector<F>> beta_rand,vector<F> a,size_t size, F previous_r){
	if(MAX_CHUNCK < size/MAX_CHUNCK){
		printf("Error, increase buffer %d\n",size);
		exit(-1);
	}
    
	if(MAX_CHUNCK >= size){
		return generate_2product_sumcheck_proof_stream_local(fp1, beta_rand,a,size, previous_r);
	}


    int total_c = (int)log2(size/MAX_CHUNCK);
    int c = 4;
	if(c >= total_c){
        c = total_c;
    }else{
		c = (int)log2(log2(size/MAX_CHUNCK)) + 1;
	}
    
	int new_c = 0,offset,poly_degree,new_degree  = 0;
	F omega = getRootOfUnit(c);
	int degree = 1<<c;
    proof_stream P;
    F len = F(1<<c);
    F ilen;
	P.size = size;
    F::inv(ilen, len);

	vector<F> v1(MAX_CHUNCK),v2(MAX_CHUNCK);
	vector<F> temp_v1(degree),temp_v2(degree);
	vector<F> poly(2*degree),l1(2*degree),l2(2*degree);
    if(c <= 4){
        poly.clear();
        poly.resize(degree*(degree+1)/2);
    }
    vector<vector<F>> poly_proofs;
	vector<vector<F>> Lv;
	vector<F> rand;
    vector<F> v;
	
	vector<u32> rev_prod,rev;
    vector<F> w_prod,w;
		

	if(size > (size_t)MAX_CHUNCK*(size_t)MAX_CHUNCK){
		printf("Increase MAX_CHUNCK, size : %d\n",size );
		exit(-1);
	}

	vector<vector<vector<F>>> Acc_Sums;
	
	
    
    vector<quadratic_poly> p;
	vector<F> rand_v,r;
	vector<vector<F>> R1,R2;
	int temp_size = size;
	
    
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
	
	int counter,i =0;
    //printf("%d,%d \n",1<<c,size/MAX_CHUNCK);
    
    
    
    for(i = 0; i < 2; i++){
	    counter = 0;
		reset_stream(fp1);
		
        for(int j = 0; j < poly.size(); j++){
			poly[j] = F_ZERO;
		}
      
	  	for(int j = 0; j < size/MAX_CHUNCK; j++){
			read_stream(fp1,v1,MAX_CHUNCK);
			compute_temp_beta(beta1,beta2,a,v2,j);
			
			for(int k = 0; k < i; k++){
				for(int l = 0; l < MAX_CHUNCK/(1ULL<<(c*(k+1))); l++){
					v1[l] = Lv[k][0]*v1[Lv[k].size()*l];
					v2[l] = Lv[k][0]*v2[Lv[k].size()*l];
					for(int h = 1; h < Lv[k].size(); h++){
						v1[l] += Lv[k][h]*v1[degree*l + h];
						v2[l] += Lv[k][h]*v2[degree*l + h];
					}
				}
			}
			int current_size = MAX_CHUNCK/(1<<(c*i));
			if(new_c == 0){
				offset = current_size/degree;
				poly_degree = degree; 
			}else{
				offset = current_size/new_degree;
				poly_degree = new_degree; 
                //printf("%d\n",current_size);
            }
			//printf("%d,%d \n",offset,poly_degree);
			for(int k = 0; k < offset; k++){
				for(int l = 0; l < poly_degree; l++){
					temp_v1[l] = v1[poly_degree*k + l];
					temp_v2[l] = v2[poly_degree*k + l];
					l1[l + poly_degree] = 0;
					l2[l+poly_degree] = 0;
				}
				if((c <= 4 && new_c == 0) || (new_c <= 4)){
                    
                    int idx = 0;
					for(int l = 0; l < poly_degree; l++){
						for(int h = l+1; h < poly_degree; h++){
							poly[idx] += temp_v1[l]*temp_v2[h] + temp_v1[h]*temp_v2[l];
                            idx++;
                        }
					}
                    for(int l = 0; l < poly_degree; l++){
                        poly[idx] += temp_v1[l]*temp_v2[l];
                        idx++;
                    }
             
             	}else{
                    
                    my_fft(temp_v1,w,rev,ilen,true);
					my_fft(temp_v2,w,rev,ilen,true);
					
					for(int l = 0; l < poly_degree; l++){
						l1[l] = temp_v1[l];
						l2[l] = temp_v2[l];
					}
					my_fft(l1,w_prod,rev_prod,F(1),false);
					my_fft(l2,w_prod,rev_prod,F(1),false);
					for(int l = 0; l < 2*poly_degree; l++){
						poly[l] += l1[l]*l2[l];
					}
				}
				
			}
		}
        poly_proofs.push_back(poly);
		
		F r;r.setByCSPRNG();
		rand.push_back(r);
		if(!new_c){
			Lv.push_back(compute_lagrange_coeff(omega,r,degree));
		}else{
			if(recursion == 1 && new_c > 4){	
				P.RP = reduce_proof_size(poly,new_c,getRootOfUnit(new_c+1),r,r);
			}
			F new_omega = getRootOfUnit((int)log2(new_degree));
            Lv.push_back(compute_lagrange_coeff(new_omega,r,new_degree));		
		}
		
		
		if(!new_c){
			
			new_c = total_c -c;
			new_degree = 1ULL<<new_c;
			
			if(new_c == 0){
				i++;
				break;
			}
			
			temp_v1.resize(new_degree);
			temp_v2.resize(new_degree);
			poly.resize(2*new_degree);
			l1.resize(2*new_degree);
			l2.resize(2*new_degree);
			if(new_c <= 4){
		        poly.clear();
        		poly.resize(new_degree*(new_degree+1)/2);
    		}else{
				F::inv(ilen, 1ULL<<(new_c));
				w.resize(1ULL<<(new_c));
				w_prod.resize(1ULL<<(new_c+1));
				rev_prod.resize(1ULL<<(new_c+1));
				rev.resize(1ULL<<(new_c));
				prepare_fft_aux(w,rev,w_prod,rev_prod,1ULL<<(new_c+1));
		
			}
		}
	}
    
    P.polynomials = poly_proofs;
    P.c = c;
    P.randomness = rand;
    P.new_sum = F(0);
    for(int k = poly_proofs[0].size()-degree; k < poly_proofs[0].size(); k++){
        P.new_sum += poly_proofs[0][k];
    }
    reset_stream(fp1);
	
    // SOME CHANGES
    int final_size = 1;
    for(int i = 0; i < Lv.size(); i++){
       
        final_size *= Lv[i].size();
    }
    final_size = size/final_size;
    
    
	vector<F> final_v1(final_size,F_ZERO),final_v2(final_size,F_ZERO);
	
	
    counter = 0;
    vector<F> conv;
	compute_convolution(Lv,conv);

	for(int j = 0; j < size/MAX_CHUNCK; j++){
		int final_size;
		read_stream(fp1,v1,MAX_CHUNCK);
		compute_temp_beta(beta1,beta2,a,v2,j);
		
        int _c = 0;
        for(int k = 0; k < MAX_CHUNCK/conv.size(); k++){
            for(int l = 0; l < conv.size(); l++){
                final_v1[counter] += conv[l]*v1[k*conv.size() + l];
			    final_v2[counter] += conv[l]*v2[k*conv.size() + l];
            }
            counter++;
        }
	}
    
    //printf("%d,%d \n",final_v1.size(),beta_partitions.size());
    proof P1 = generate_2product_sumcheck_proof(final_v1,final_v2,rand[rand.size()-1]);
	P.P.push_back(P1);
    //proof P = generate_2product_sumcheck_proof(final_v1,final_v2,rand[rand.size()-1]);
	// Compute convolution
	
	
	reset_stream(fp1);
	
    //printf("%d,%d,%d\n",P.randomness[0].size(),final_v1.size(),conv.size());
	int conv_size = conv.size();
	vector<F> _beta;precompute_beta(P1.randomness[0],_beta);
	vector<F> partial_eval1(conv_size,F(0)),partial_eval2(conv_size,F(0));
	counter = 0;
	
    for(int i = 0; i < size/MAX_CHUNCK; i++){
		
        read_stream(fp1,v1,MAX_CHUNCK);
		compute_temp_beta(beta1,beta2,a,v2,i);
		
        for(int j = 0; j < MAX_CHUNCK; j+=conv_size){
			for(int k = 0; k < conv_size; k++){
				partial_eval1[k] += _beta[counter]*v1[j + k];
				partial_eval2[k] += _beta[counter]*v2[j + k];
			}
			counter++;
		}
	}
	
    _beta.clear();
	vector<F> _a = generate_randomness(2,P1.randomness[0][P1.randomness[0].size()-1]);
	
    
	vector<vector<F>> _v1,_v2,_v3;
    _v1.push_back(partial_eval1);_v1.push_back(partial_eval2);
    _v2.push_back(conv);_v2.push_back(conv);
    

    proof P2 = generate_batch_3product_sumcheck_proof(_v1,_v2,_v3,_a,_a[1]);
    
    //proof P2 = _generate_3product_sumcheck_proof(conv,partial_eval1,beta,rand[rand.size()-1]);
	
	P.P.push_back(P2);
	P.a = _a;

    if(_a[0]*P1.vr[0] + _a[1]*P1.vr[1] != P2.c_poly[0].eval(F(0))+P2.c_poly[0].eval(F(1))){
		printf(">>Error \n");
		exit(-1);
	}
    
    P.vr.push_back(P2.vr[0]);
    P.vr.push_back(P2.vr[2]);
	
	v1.clear();v2.clear();
	final_v1.clear();final_v2.clear();
	partial_eval1.clear();partial_eval2.clear();
	_beta.clear();
	_v1[0].clear();
	_v1[1].clear();
	_v2[0].clear();
	_v2[1].clear();
	for(int i = 0; i < a.size(); i++){
		beta1[i].clear();
		beta2[i].clear();
	}
    return P;

}


proof_stream generate_2product_sumcheck_proof_disk_beta(stream_descriptor fp1, vector<vector<F>> beta_rand,vector<F> a,size_t size, F previous_r){
	
	int M = 8;
	vector<int> _M;
	proof_stream P;
	
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
		read_stream(fp1,v,size);
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
	//printf("%d,%d,%d,%d\n", MAX_CHUNCK/M,M,size,size/MAX_CHUNCK);
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
		reset_stream(fp1);
        //lseek(fp1, 0, SEEK_SET);
		//lseek(fp2, 0, SEEK_SET);
		if((size/MAX_CHUNCK)/(cluster_size*M) == 0){
			M = (size/MAX_CHUNCK)/cluster_size;
		}
		for(int i = 0; i < size/MAX_CHUNCK; i++){
			read_stream(fp1,v1,MAX_CHUNCK);
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


	//lseek(fp1, 0, SEEK_SET);
	reset_stream(fp1);
    //lseek(fp2, 0, SEEK_SET);
			
	//printf("%d,%d\n",_M.size(),R1.size());
	
	vector<F> fv1(MAX_CHUNCK),fv2(MAX_CHUNCK);
	int counter = 0;
	for(int i = 0; i < size/MAX_CHUNCK; i++){
		read_stream(fp1,v1,MAX_CHUNCK);
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
//	lseek(fp1, 0, SEEK_SET);
	reset_stream(fp1);

	r = P.P[0].randomness[0];
	vector<F> beta;
	precompute_beta(r,beta);
	vector<F> evals1(size/MAX_CHUNCK,F(0)),evals2(size/MAX_CHUNCK,F(0));
	counter = 0;
	for(int i = 0; i < size/MAX_CHUNCK; i++){
		read_stream(fp1,v1,MAX_CHUNCK);
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


// takes as input vectors x of equal size and for each 
// vector outputs Prod_i = x[0]*x[1]*x[2]...x[N]
mul_tree_proof_stream prove_multiplication_tree_stream_shallow(stream_descriptor fd,int vectors,int size, F previous_r, int distance, vector<F> prev_x){
	
	// Initialize total input
	mul_tree_proof_stream Proof;
	int depth = (int)log2(size);
    stream_descriptor dummy_descriptor;dummy_descriptor.pos = -1;
    
	
	
	
   
	//printf("Final prod len : %d\n",transcript[depth-1].size());
	proof_stream P;

    if(size*vectors <= 2*MAX_CHUNCK){
        vector<F> v(size*vectors);
        vector<vector<F>> input(vectors);
        for(int i = 0; i < vectors; i++){
            input[i].resize(size);
        }
        clock_t s,e;
		s = clock();

		
		read_stream(fd,v,size*vectors);
       
	   
	    
        
        int counter = 0;
        for(int i = 0; i < vectors; i++){
            for(int j = 0; j < size; j++){
                input[i][j] = v[counter];
                counter++;
            }
        }
        v.clear();

		mul_tree_proof mP =  prove_multiplication_tree_new(input,previous_r,prev_x);
        Proof.final_eval = mP.final_eval;
        Proof.final_r = mP.final_r[mP.final_r.size()-1];
        Proof.global_randomness = mP.global_randomness;
        Proof.individual_randomness = mP.individual_randomness;
        Proof.r = mP.final_r;
        Proof.out = mP.output;
        e = clock();
		return Proof;
    }

	if(vectors == 1){
		vector<F> r;
		vector<F> out(1);
		vector<F> v(2*MAX_CHUNCK);
        vector<vector<F>> input(1);
        
		
        int max_depth = (int)log2(size) - (int)log2(MAX_CHUNCK);
        int chunck_size = 2*MAX_CHUNCK;
        clock_t s,e;
		s = clock();

       	generate_mul_tree(fd,v,chunck_size,max_depth-2);
		 input[0] = v;
        v.clear();
        mul_tree_proof mP = prove_multiplication_tree_new(input,previous_r,prev_x);
        Proof.prod = mP.output[0];
        
        F sum = mP.final_eval;
        
        r = mP.final_r;
        

       // printf(">>OK %d\n",r.size());
        reset_stream(fd);
        for(int i = max_depth - 2; i >= 0; i--){
            if(i != 0){
                stream_descriptor vfd;vfd.pos = 0; vfd.name = "mul_tree"; vfd.layer = i-1;
                //printf("Depth : %d \n", i-1);
                vfd.input_name = fd.name;vfd.input_pos = 0;vfd.input_pos_j = 0;vfd.input_data_size = fd.data_size;
                vfd.input_size = fd.size;vfd.compress_vector = fd.compress_vector;
				P = generate_3product_sumcheck_proof_stream(vfd, dummy_descriptor, 1<<(depth - i -1), r, previous_r,SUM);
				verify_stream_3product_sumcheck(P, r, sum);
	
			}else{
				P = generate_3product_sumcheck_proof_stream(fd,dummy_descriptor, 1<<(depth - i -1), r, previous_r,SUM);	
				verify_stream_3product_sumcheck(P, r, sum);
			}
			
			if(sum != P.new_sum){
            //if(sum + P.new_sum != P.P[0].c_poly[0].eval(F(1)) + P.P[0].c_poly[0].eval(F(0))){
				printf("Error in sum : %d\n", i);
				exit(-1);
			}
            r = P.P[1].randomness[0];
			r.insert(r.end(),P.P[0].randomness[0].begin(),P.P[0].randomness[0].end());
			previous_r = mimc_hash(P.P[1].final_rand,1);
			sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
			r.insert(r.begin(),previous_r);
        }
        //read_chunk(vfd[depth-1],out,1);
		previous_r = mimc_hash(previous_r,out[0]);
		
		e = clock();
		
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
        int current_depth;
		if(vectors <= MAX_CHUNCK){
			vector<F> output(vectors);
            
			int chunck_size = 2*MAX_CHUNCK;
			current_depth = depth - 1 - (int)log2(2*MAX_CHUNCK/vectors) ;
			
			//printf("%d,%d,%d\n",depth,current_depth,chunck_size);
			if(distance > 1){
				while(true){
					if((current_depth+1)%distance == 0){
						break;
					}
					chunck_size = chunck_size*2;
					current_depth--;
				}
			}
			//printf("%d,%d\n", current_depth,chunck_size);
			
			vector<F> v(chunck_size);
            
			
			vector<vector<F>> input(vectors);
            for(int i = 0; i < vectors; i++){
                input[i].resize(chunck_size/vectors);
            }
             
		    generate_mul_tree_parallel(fd , v ,chunck_size, depth,current_depth);
            for(int i = 0; i < vectors; i++){
                for(int j = 0; j < input[i].size(); j++){
                    input[i][j] = v[i*input[i].size() + j];
                }
            }
            reset_stream(fd);
			mul_tree_proof mP = prove_multiplication_tree_new(input,previous_r,r);
            sum = mP.final_eval;
			printf("Input size : %d\n",chunck_size);
			Proof.out = mP.output;
            r = mP.final_r;
			current_depth++;
            //read_chunk(vfd[depth-1],output,vectors);
			//sum = evaluate_vector(output,r);
		}
		else{
			
            stream_descriptor vfd;vfd.pos = 0; vfd.name = "mul_tree"; vfd.layer = depth-1;
            vfd.input_name = fd.name;vfd.input_pos = 0;vfd.input_pos_j = 0;vfd.input_data_size = fd.data_size;
            vfd.input_size = fd.size;vfd.compress_vector = fd.compress_vector;
			sum = evaluate_vector_stream(vfd , r, vectors);
            //printf("OK1\n");
            current_depth = depth-1; 
        }
		
		vector<F> beta;
		if(prev_x.size() == 0){
			previous_r = mimc_hash(r[r.size()-1],sum);
		}
		//precompute_beta(r,beta);
		vector<size_t> sizes;
		for(int i = 0; i < current_depth/distance; i++){
			sizes.push_back(vectors*(1<<(depth - distance*(i+1))));
		}
		vector<size_t> sizes_open;
		for(int i = 0; i < sizes.size()-1; i++){
			sizes_open.push_back(sizes[i]);
		}
		vector<F> a = generate_randomness(current_depth/distance,previous_r);
		beta = generate_randomness((int)log2(sizes[0]) - r.size(),a[a.size()-1]);
		r.insert(r.end(),beta.begin(),beta.end());
		beta = r;
		
		stream_descriptor vfd;vfd.pos = 0; vfd.name = "mul_tree"; vfd.layer = distance - 1;
        vfd.input_name = fd.name;vfd.input_pos = 0;vfd.input_pos_j = 0;vfd.input_data_size = fd.data_size;
        vfd.input_size = fd.size;vfd.compress_vector = fd.compress_vector;
		vector<vector<G1>> commitments(sizes.size()-1);
		vector<GT> C;
		
		
		printf("OK\n");
		MIPP_commit_stream_multree(vfd, sizes,distance, pp_mul, commitments, C);
		printf("OK\n");
		clock_t s = clock();
		
		vector<F> sums = evaluate_multree(vfd, beta, sizes, distance);
		if(sums[sums.size() - 1] != sum){
			printf("Error in first sum\n");
			exit(-1);
		}
		//printf("Batch size : %d\n",a.size());
		for(int i = 0; i < distance; i++){
			vfd.layer = distance-i-2;
			P = generate_3product_sumcheck_proof_stream_batch(vfd,sizes,a,distance,beta,beta[beta.size()-1],1);
			verify_stream_3product_batch(P, beta, a, sums);
			for(int j = 0; j  < sizes.size(); j++){
				sizes[j] = 2*sizes[j];
			}
			r = P.P[1].randomness[0];
			r.insert(r.end(),P.P[0].randomness[0].begin(),P.P[0].randomness[0].end());
			previous_r = mimc_hash(P.P[1].final_rand,1);
			r.insert(r.begin(),previous_r);		
			beta = r;
			for(int j = 0; j < a.size(); j++){
				sums[j] = P.vr[j]*(F(1) - previous_r) + P.vr[j + a.size()]*previous_r;
			}
			
		}
		clock_t e = clock();
		vfd.layer = distance-1;
		MIPP_open_stream_multree(vfd, sizes_open, distance,generate_randomness((int)log2(sizes_open[0]),F(1)), pp_mul, commitments);
		printf("Prove time : %lf\n",pp_mul.prove_time + (float)(e-s)/(float)CLOCKS_PER_SEC);
		// Correctness verification
		Proof.final_r = r[r.size()-1];
		Proof.final_eval = sums[0];
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
	
    
	return Proof;
}



// takes as input vectors x of equal size and for each 
// vector outputs Prod_i = x[0]*x[1]*x[2]...x[N]
mul_tree_proof_stream prove_multiplication_tree_stream(stream_descriptor fd,int vectors,int size, F previous_r, vector<F> prev_x){
	
	// Initialize total input
	mul_tree_proof_stream Proof;
	int depth = (int)log2(size);
    stream_descriptor dummy_descriptor;dummy_descriptor.pos = -1;
    
	
	
	
   
	//printf("Final prod len : %d\n",transcript[depth-1].size());
	proof_stream P;

    if(size*vectors <= 2*MAX_CHUNCK){
        vector<F> v(size*vectors);
        vector<vector<F>> input(vectors);
        for(int i = 0; i < vectors; i++){
            input[i].resize(size);
        }
        clock_t s,e;
		s = clock();

		
		read_stream(fd,v,size*vectors);
       
	   
	    
        
        int counter = 0;
        for(int i = 0; i < vectors; i++){
            for(int j = 0; j < size; j++){
                input[i][j] = v[counter];
                counter++;
            }
        }
        
		vector<F>().swap(v);
		//v.clear();

		mul_tree_proof mP =  prove_multiplication_tree_new(input,previous_r,prev_x);
        Proof.final_eval = mP.final_eval;
        Proof.final_r = mP.final_r[mP.final_r.size()-1];
        Proof.global_randomness = mP.global_randomness;
        Proof.individual_randomness = mP.individual_randomness;
        Proof.r = mP.final_r;
        Proof.out = mP.output;
		e = clock();
		for(int i = 0; i < input.size(); i++){
			vector<F>().swap(input[i]);
		}
		vector<vector<F>>().swap(input);
		return Proof;
    }

	if(vectors == 1){
		vector<F> r;
		vector<F> out(1);
		vector<F> v(2*MAX_CHUNCK);
        vector<vector<F>> input(1);
        
		
        int max_depth = (int)log2(size) - (int)log2(MAX_CHUNCK);
        int chunck_size = 2*MAX_CHUNCK;
        clock_t s,e;
		s = clock();

       	generate_mul_tree(fd,v,chunck_size,max_depth-2);
		 input[0] = v;
        
		
		vector<F>().swap(v);
		
		
		mul_tree_proof mP = prove_multiplication_tree_new(input,previous_r,prev_x);
        
		Proof.prod = mP.output[0];
        for(int i = 0; i < input.size(); i++){
			vector<F>().swap(input[i]);
		}
		vector<vector<F>>().swap(input);
		
        F sum = mP.final_eval;
        
        r = mP.final_r;
        
		// printf(">>OK %d\n",r.size());
        reset_stream(fd);
        for(int i = max_depth - 2; i >= 0; i--){
            if(i != 0){
                stream_descriptor vfd;vfd.pos = 0; vfd.name = "mul_tree"; vfd.layer = i-1;
                printf("Depth : %d \n", i-1);
                vfd.input_name = fd.name;vfd.input_pos = 0;vfd.input_pos_j = 0;vfd.input_data_size = fd.data_size;
                vfd.input_size = fd.size;vfd.compress_vector = fd.compress_vector;
				P = generate_3product_sumcheck_proof_stream(vfd, dummy_descriptor, 1<<(depth - i -1), r, previous_r,SUM);
				verify_stream_3product_sumcheck(P, r, sum);
	
			}else{
				P = generate_3product_sumcheck_proof_stream(fd,dummy_descriptor, 1<<(depth - i -1), r, previous_r,SUM);	
				verify_stream_3product_sumcheck(P, r, sum);
			}
			
			if(sum != P.new_sum){
            //if(sum + P.new_sum != P.P[0].c_poly[0].eval(F(1)) + P.P[0].c_poly[0].eval(F(0))){
				printf("Error in sum : %d\n", i);
				exit(-1);
			}
            r = P.P[1].randomness[0];
			r.insert(r.end(),P.P[0].randomness[0].begin(),P.P[0].randomness[0].end());
			previous_r = mimc_hash(P.P[1].final_rand,1);
			sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
			r.insert(r.begin(),previous_r);
        }
        //read_chunk(vfd[depth-1],out,1);
		previous_r = mimc_hash(previous_r,out[0]);
		
		e = clock();
		
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
        int current_depth;
		if(vectors <= MAX_CHUNCK){
			vector<F> output(vectors);
            vector<F> v(2*MAX_CHUNCK);
            vector<vector<F>> input(vectors);
            for(int i = 0; i < vectors; i++){
                input[i].resize(2*MAX_CHUNCK/vectors);
            }
            int chunck_size = 2*MAX_CHUNCK;
			 
		    generate_mul_tree_parallel(fd , v ,chunck_size, depth,depth - 1- (int)log2(2*MAX_CHUNCK/vectors));
            for(int i = 0; i < vectors; i++){
                for(int j = 0; j < input[i].size(); j++){
                    input[i][j] = v[i*input[i].size() + j];
                }
            }
			vector<F>().swap(v);
			
            reset_stream(fd);
            mul_tree_proof mP = prove_multiplication_tree_new(input,previous_r,r);
			for(int i = 0; i < input.size(); i++){
				vector<F>().swap(input[i]);
			}
			vector<vector<F>>().swap(input);
		
            sum = mP.final_eval;
		
			Proof.out = mP.output;
            r = mP.final_r;
            current_depth = depth - 1 - (int)log2(2*MAX_CHUNCK/vectors) ;
            //read_chunk(vfd[depth-1],output,vectors);
			//sum = evaluate_vector(output,r);
		}
		else{
			
            stream_descriptor vfd;vfd.pos = 0; vfd.name = "mul_tree"; vfd.layer = depth-1;
            vfd.input_name = fd.name;vfd.input_pos = 0;vfd.input_pos_j = 0;vfd.input_data_size = fd.data_size;
            vfd.input_size = fd.size;vfd.compress_vector = fd.compress_vector;
			sum = evaluate_vector_stream(vfd , r, vectors);
            //printf("OK1\n");
            current_depth = depth-1; 
        }
		
		vector<F> beta;
		if(prev_x.size() == 0){
			previous_r = mimc_hash(r[r.size()-1],sum);
		}
		clock_t s,e;
		s = clock();
		//precompute_beta(r,beta);
		for(int i = current_depth; i >= 0; i--){
			
			
			if(i != 0){
                stream_descriptor vfd;vfd.pos = 0; vfd.name = "mul_tree"; vfd.layer = i-1;
                vfd.input_name = fd.name;vfd.input_pos = 0;vfd.input_pos_j = 0;vfd.input_data_size = fd.data_size;
                vfd.input_size = fd.size;vfd.compress_vector = fd.compress_vector;
				//P = generate_3product_sumcheck_proof_disk(vfd, dummy_descriptor, vectors*(1<<(depth - i -1)), r, previous_r,SUM);
			
                P = generate_3product_sumcheck_proof_stream(vfd, dummy_descriptor, vectors*(1<<(depth - i -1)), r, previous_r,SUM);
				verify_stream_3product_sumcheck(P, r, sum);
			}else{
				//P = generate_3product_sumcheck_proof_disk(fd, dummy_descriptor, vectors*(1<<(depth - i -1)), r, previous_r,SUM);	
			
                P = generate_3product_sumcheck_proof_stream(fd, dummy_descriptor, vectors*(1<<(depth - i -1)), r, previous_r,SUM);	
				verify_stream_3product_sumcheck(P, r, sum);
			}
            
            if(sum != P.new_sum){
			//if(sum + P.new_sum != P.P[0].c_poly[0].eval(F(1)) + P.P[0].c_poly[0].eval(F(0))){
				printf("Error in sum : %d\n", i);
				exit(-1);
			}
			r = P.P[1].randomness[0];
			r.insert(r.end(),P.P[0].randomness[0].begin(),P.P[0].randomness[0].end());
			previous_r = mimc_hash(P.P[1].final_rand,1);
			sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
			r.insert(r.begin(),previous_r);		
		}
		e = clock();
		
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
	
    
	return Proof;
}


void prove_permutation(vector<stream_descriptor> perm1,vector<stream_descriptor> perm2, F previous_r){
	vector<F> beta_rand;
	stream_descriptor temp; temp.pos = -1; 
	
	// run simple sumchecks
	// run consistency sumchecks
	for(int i = 0; i < perm1.size(); i++){
		beta_rand = generate_randomness((int)log2(perm1[i].size),previous_r);
	
		generate_3product_sumcheck_proof_stream(perm1[i],temp,perm1[i].size,beta_rand,beta_rand[beta_rand.size()-1],SUM_INV);
		generate_3product_sumcheck_proof_stream(perm2[i],temp,perm2[i].size,beta_rand,beta_rand[beta_rand.size()-1],SUM_INV);
	}
}


void streaming_sumcheck_partition_1(partition_SNARK_data_streaming data){

	//int compress_vector_fd = open("compressed_input_fp",O_RDWR);
	//int input_fd = open(data.input_data.file_name.c_str(),O_RDWR);
	//int perm_input_fd = open(data.permuted_data.file_name.c_str(),O_RDWR);
	vector<F> prev_x;
	
    stream_descriptor compress_vector_fd;compress_vector_fd.name = "compressed_input";
    compress_vector_fd.size = data.input_data.size;
    compress_vector_fd.compress_vector = data.compress_vector;compress_vector_fd.pos = 0;
    printf("Size : %d %d\n",data.input_data.size,data.compress_vector.size());
	
	auto t1 = chrono::high_resolution_clock::now();
   
	mul_tree_proof_stream mP1 = prove_multiplication_tree_stream(compress_vector_fd, 2*data.input_data.row_size, data.input_data.col_size/2,F(0), prev_x);
    
	
	mP1.r.pop_back();
	vector<F> r0 = mP1.r,r1 = mP1.r;
	r0.insert(r0.begin(),F(0));
	r1.insert(r1.begin(),F(1));
	vector<vector<F>> rand;rand.push_back(r0);rand.push_back(r1);
	int size = data.input_data.row_size*data.input_data.col_size;
	

	vector<F> input_eval = evaluate_vector_stream_batch(data.input_data, rand, size);
	vector<F> perm_input_eval = evaluate_vector_stream_batch(data.permuted_data, rand, size);
	F temp_r = mimc_hash(mP1.final_r,input_eval[0]);
	temp_r = mimc_hash(temp_r,input_eval[1]);
	temp_r = mimc_hash(temp_r,perm_input_eval[0]);
	temp_r = mimc_hash(temp_r,perm_input_eval[1]);
	vector<F> agg_r = generate_randomness(2,temp_r);
	
	//vector<F> f(size);
	//lseek(input_fd,0,SEEK_SET);
	//read_chunk(input_fd,f,size);

	
	proof_stream sP1 = generate_2product_sumcheck_proof_stream_beta(data.input_data,rand,agg_r,size,agg_r[1]);
	verify_stream_2product_sumcheck(sP1,  rand, agg_r, agg_r[0]*input_eval[0] + agg_r[1]*input_eval[1]);
	if(sP1.polynomials.size()!=0){
        F sum = F(0);
        for(int i = sP1.polynomials[0].size() - (1<<sP1.c); i < sP1.polynomials[0].size(); i++){
            sum += sP1.polynomials[0][i];
        }
        if(sum != agg_r[0]*input_eval[0] + agg_r[1]*input_eval[1]){
            printf("Error in partition sumcheck 1\n");
            exit(-1);
        }
    }
  
  	
	proof_stream sP2 = generate_2product_sumcheck_proof_stream_beta(data.permuted_data,rand,agg_r,size,agg_r[1]);
	verify_stream_2product_sumcheck(sP2,  rand, agg_r, agg_r[0]*perm_input_eval[0] + agg_r[1]*perm_input_eval[1]);

	if(sP2.polynomials.size() != 0){
        F sum = F(0);
        for(int i = sP2.polynomials[0].size() - (1<<sP2.c); i < sP2.polynomials[0].size(); i++){
            sum += sP2.polynomials[0][i];
        }
        if(sum != agg_r[0]*perm_input_eval[0] + agg_r[1]*perm_input_eval[1]){
            printf("Error in partition sumcheck 2\n");
            exit(-1);
        }    
    }
    
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
}


void streaming_forest_partition_sumcheck_1(partition_SNARK_data_streaming_forest data, int forest_size ){
	vector<F> prev_x;
	stream_descriptor compressed_input;compressed_input.name = "compressed_input_forest";
	compressed_input.size = data.input_data.size/2;compressed_input.pos = 0;
	compressed_input.compress_vector = data.compress_vector;
	stream_descriptor compressed_perm;compressed_perm.name = "compressed_perm_forest";
	compressed_perm.size =  data.permuted_data.size/2;compressed_perm.pos = 0;
	compressed_perm.compress_vector = data.compress_vector;
	
	auto t1 = chrono::high_resolution_clock::now();
	
	mul_tree_proof_stream mP1 = prove_multiplication_tree_stream(compressed_input, data.input_data.row_size, data.input_data.col_size/2,F(0), prev_x);
    
	
	
	mul_tree_proof_stream mP1_input = prove_multiplication_tree_stream(compressed_perm, forest_size*data.input_data.row_size, data.input_data.col_size/2,F(0), prev_x);
    
	
	
	vector<F> r0 = mP1.r,r1 = mP1.r;
	r0.insert(r0.begin(),F(0));
	r1.insert(r1.begin(),F(1));
	vector<vector<F>> rand1,rand2;rand1.push_back(r0);rand1.push_back(r1);
	
	
	vector<F> input_eval = evaluate_vector_stream_batch(data.input_data, rand1, data.input_data.size);
	
	r0 = mP1_input.r;r1 = mP1_input.r;
	r0.insert(r0.begin(),F(0));
	r1.insert(r1.begin(),F(1));
	rand2.push_back(r0);rand2.push_back(r1);
	
	vector<F> perm_input_eval = evaluate_vector_stream_batch(data.permuted_data, rand2, data.permuted_data.size);
	F temp_r = mimc_hash(mP1.final_r,input_eval[0]);
	temp_r = mimc_hash(temp_r,input_eval[1]);
	temp_r = mimc_hash(temp_r,perm_input_eval[0]);
	temp_r = mimc_hash(temp_r,perm_input_eval[1]);
	vector<F> agg_r = generate_randomness(2,temp_r);

	proof_stream sP1 = generate_2product_sumcheck_proof_stream_beta(data.input_data,rand1,agg_r,data.input_data.size,agg_r[1]);
	verify_stream_2product_sumcheck(sP1,  rand1, agg_r, agg_r[0]*input_eval[0] + agg_r[1]*input_eval[1]);

	if(sP1.polynomials.size()!=0){
        F sum = F(0);
        for(int i = sP1.polynomials[0].size() - (1<<sP1.c); i < sP1.polynomials[0].size(); i++){
            sum += sP1.polynomials[0][i];
        }
        if(sum != agg_r[0]*input_eval[0] + agg_r[1]*input_eval[1]){
            printf("Error in partition sumcheck 1\n");
            exit(-1);
        }
    }
    
	proof_stream sP2 = generate_2product_sumcheck_proof_stream_beta(data.permuted_data,rand2,agg_r,data.permuted_data.size,agg_r[1]);
	verify_stream_2product_sumcheck(sP2,  rand2, agg_r, agg_r[0]*perm_input_eval[0] + agg_r[1]*perm_input_eval[1]);
	if(sP2.polynomials.size() != 0){
        F sum = F(0);
        for(int i = sP2.polynomials[0].size() - (1<<sP2.c); i < sP2.polynomials[0].size(); i++){
            sum += sP2.polynomials[0][i];
        }
        if(sum != agg_r[0]*perm_input_eval[0] + agg_r[1]*perm_input_eval[1]){
            printf("Error in partition sumcheck 2\n");
            exit(-1);
        }    
    }
    
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);

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
    stream_descriptor compressed_path_fd; compressed_path_fd.name = "compressed_path";compressed_path_fd.pos = 0;
    compressed_path_fd.size = data.paths.row_size;compressed_path_fd.compress_vector = data.tree_compress_vector;
	//int compressed_path_fd = open("compressed_path_fp",O_RDWR);
	reset_stream(data.paths);
    reset_stream(data.paths_aux);

    //int fd_paths = open(data.paths.file_name.c_str(),O_RDWR);
	//int fd_aux_paths = open(data.paths_aux.file_name.c_str(),O_RDWR);
	
    
	mul_tree_proof_stream mP1 = prove_multiplication_tree_stream(compressed_path_fd, 1, data.paths.row_size,F(0), prev_x);
    
    vector<stream_descriptor> fds;fds.push_back(data.paths);fds.push_back(data.paths_aux);
	vector<size_t> fd_cols;fd_cols.push_back(data.paths.col_size);fd_cols.push_back(2);
	vector<size_t> fd_size;fd_size.push_back(data.paths.row_size*data.paths.col_size);fd_size.push_back(2*data.paths.row_size);

	auto t1 = chrono::high_resolution_clock::now();
    
	vector<F> compressed_col = prepare_matrix_streaming(fds,fd_cols,fd_size,data.paths.row_size, mP1.r, 2 + data.paths.col_size);
	
	pad_vector(compressed_col);pad_vector(data.tree_compress_vector);
	
    proof sP1 = generate_2product_sumcheck_proof(compressed_col,data.tree_compress_vector,mP1.final_r);
	verify_2product_sumcheck(sP1,mP1.final_eval-F(1));

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
	verify_3product_sumcheck(tP1,r,final_powers_input_eval);
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
	vector<F> temp;
	verify_3product_sumcheck(tP2,temp,tP2.c_poly[0].eval(0)+tP2.c_poly[0].eval(1));
	
	//F sum1 = P.tP2.c_poly[0].eval(0) + P.tP2.c_poly[0].eval(1);
	F eval_powers3 = tP2.vr[1];
	

	vector<F> eval_powers3_x = tP2.randomness[0];
	temp_powers = powers;
	proof sP3 = generate_2product_sumcheck_proof(gamma_vector1,temp_powers,tP2.final_rand);
	verify_2product_sumcheck(sP3,sum1);

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
	verify_2product_sumcheck(sP4,r[0]*eval_powers1 + r[1]*eval_powers2 +r[2]*eval_powers3 + r[3]*eval_powers4);

	if(sP4.q_poly[0].eval(F(0)) + sP4.q_poly[0].eval(F(1)) != r[0]*eval_powers1 + r[1]*eval_powers2 +r[2]*eval_powers3 + r[3]*eval_powers4){
		printf("Error in partition sumcheck 2--6\n");
		exit(-1);	
	}
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    
	//close(compressed_path_fd);
	//close(fd_paths);
	//close(fd_aux_paths);
}


void streaming_forest_partition_sumcheck_2(partition_SNARK_data_streaming_forest data, vector<vector<vector<F>>> forest){
	partition_sumcheck2_proof P;
	vector<vector<F>> final_powers(forest.size());
	vector<F> final_powers_input;
	vector<vector<F>> mul_tree_input;
	vector<vector<F>> final_powers_tree_input;
	
	vector<vector<F>> powers(forest.size());
	for(int k = 0; k < forest.size(); k++){
		for(int i = 0; i < data.compressed_tree[k].size(); i++){
			powers[k].push_back(data.compressed_tree[k][i]);
			F prev = data.compressed_tree[k][i];
			for(int j = 1; j < 32; j++){
				powers[k].push_back(prev*prev);
				prev = prev*prev;
			}
		
		}
		
		pad_vector(powers[k]);
	}
	for(int i = 1; i < forest.size(); i++){
		for(int j = 0; j < powers[i].size(); j++){
			if(data.power_bits[i][j] != data.power_bits[0][j]){
				printf("Error %d,%d\n",i,j);
			}
		}
	}
	// Compute the path exponents
	for(int k = 0; k < forest.size(); k++){
		final_powers[k].resize(powers[k].size()/32);
		for(int i = 0; i < powers[k].size()/32; i++){
			vector<F> temp(32);
			final_powers[k][i] = F(1);
			
			for(int j = 0; j < 32; j++){
				final_powers_input.push_back(powers[k][i*32+j]*data.power_bits[k][i*32+j]);
				temp[j] = (F(1)-data.power_bits[k][i*32+j]) + powers[k][i*32+j]*data.power_bits[k][i*32+j];
				final_powers[k][i] *= temp[j];
			}
			final_powers_tree_input.push_back(temp);
		}		
	}

	
	
	
	
	vector<F> prev_x;
    stream_descriptor compressed_path_fd; compressed_path_fd.name = "compressed_path";compressed_path_fd.pos = 0;
    compressed_path_fd.size = data.paths.row_size;compressed_path_fd.compress_vector = data.tree_compress_vector;
	//int compressed_path_fd = open("compressed_path_fp",O_RDWR);
	data.paths.name = "path_transpose";
	data.paths_aux.name = "path_aux_transpose";
	
	
	reset_stream(data.paths);
    reset_stream(data.paths_aux);

    //int fd_paths = open(data.paths.file_name.c_str(),O_RDWR);
	//int fd_aux_paths = open(data.paths_aux.file_name.c_str(),O_RDWR);
	
   auto t1 = chrono::high_resolution_clock::now();

   mul_tree_proof_stream mP1 = prove_multiplication_tree_stream(compressed_path_fd, forest.size(), data.paths.row_size/forest.size(),F(0), prev_x);
     
   	if(forest.size() > 1 && mP1.out[0] != mP1.out[1]){
		printf("Error need to check that\n");
	}
	

	vector<stream_descriptor> fds;fds.push_back(data.paths);fds.push_back(data.paths_aux);
	vector<size_t> fd_cols;fd_cols.push_back(data.paths.col_size);fd_cols.push_back(2);
	vector<size_t> fd_size;fd_size.push_back(data.paths.row_size*data.paths.col_size);fd_size.push_back(2*data.paths.row_size);
	
	
	
	
	vector<F> compressed_col = prepare_matrix_streaming(fds,fd_cols,fd_size,data.paths.row_size, mP1.r, 2 + data.paths.col_size);
	
	pad_vector(compressed_col);pad_vector(data.tree_compress_vector);
	
    proof sP1 = generate_2product_sumcheck_proof(compressed_col,data.tree_compress_vector,mP1.final_r);
	verify_2product_sumcheck(sP1,mP1.final_eval-F(1));

	if(sP1.q_poly[0].eval(0) + sP1.q_poly[0].eval(1) != mP1.final_eval-F(1)){
		printf("Error in partition sumcheck 2\n");
		//exit(-1);
	}

	P.mP2 = prove_multiplication_tree(final_powers,P.sP1.final_rand,prev_x);
	
	
	
	for(int i = 0; i < forest.size(); i++){
		if(P.mP2.output[i] != mP1.out[i]){
		//	printf("Error in partition sumcheck 2--1, %d\n",i);
		//	exit(-1);
		}

	}
	
	
	
	P.mP3 = prove_multiplication_tree(final_powers_tree_input,P.mP2.individual_randomness[P.mP2.individual_randomness.size()-1],P.mP2.final_r);
	
	vector<F> r = P.mP3.individual_randomness;r.insert(r.end(),P.mP3.global_randomness.begin(),P.mP3.global_randomness.end());

	F eval_bits1 = evaluate_vector(convert2vector(data.power_bits),r);
	F final_powers_input_eval = evaluate_vector(final_powers_input,r);
	
	P.eval_bits1 = eval_bits1;
	P.final_powers_input_eval = final_powers_input_eval;
	P.eval_bits1_x = r;
	P.final_powers_input_eval_x = r;

	if(P.mP3.final_eval != F(1)-eval_bits1 + final_powers_input_eval){
		printf("Error in partition sumcheck 2--2\n");
		exit(-1);
	}

	vector<F> beta;
	precompute_beta(r,beta);

	F rand = mimc_hash(P.mP3.individual_randomness[P.mP3.individual_randomness.size()-1],eval_bits1);
	rand = mimc_hash(rand,final_powers_input_eval);	

	vector<F> v1 = convert2vector(data.power_bits);
	vector<F> v2 = convert2vector(powers);
	P.tP1 = _generate_3product_sumcheck_proof(v1,v2,beta,rand);
	verify_3product_sumcheck(P.tP1,r,final_powers_input_eval);
	
	v1.clear();v2.clear();

	if(P.tP1.c_poly[0].eval(0) + P.tP1.c_poly[0].eval(1) != final_powers_input_eval){
		printf("Error in partition sumcheck 2--3\n");
		exit(-1);
	}
	F eval_bits2 = P.tP1.vr[0];
	F eval_powers1 = P.tP1.vr[1];
	vector<F> eval_powers1_x = P.tP1.randomness[0];
	// Check power consistency with compressed tree
	P.eval_powers1 = eval_powers1;
	P.eval_powers1_x = eval_powers1_x;


	vector<F> eval_tree_x = generate_randomness((int)log2(data.compressed_tree.size()) + (int)log2(data.compressed_tree[0].size()),P.tP1.final_rand);
	vector<F> eval_powers2_x(5,F(0));
	eval_powers2_x.insert(eval_powers2_x.end(),eval_tree_x.begin(),eval_tree_x.end());
	

	v1 = convert2vector(powers);
	F eval_powers2 = evaluate_vector(v1,eval_powers2_x);
	v1.clear();
	v1 = convert2vector(data.compressed_tree);
	F eval_tree = evaluate_vector(v1,eval_tree_x);
	v1.clear();
	if(eval_powers2 != eval_tree){
		printf("Error in partition sumcheck 2--4\n");
		exit(-1);
	}

	P.eval_tree_x = eval_tree_x;
	P.eval_powers2_x = eval_powers2_x;
	P.eval_powers2 =eval_powers2; 

	rand = mimc_hash(eval_tree_x[eval_tree_x.size()-1],eval_powers2);

	vector<vector<F>> tree_matrix;
	for(int i = 0; i < forest.size(); i++){
		for(int j = 0; j < forest[i].size(); j++){
			tree_matrix.push_back(forest[i][j]);
		}
	}
	P.sP2 = _prove_matrix2vector(_transpose(tree_matrix),data.tree_compress_vector,eval_tree_x,eval_tree-F(1),rand);
	


	// Check power consistency
	F gamma = P.sP2.final_rand;
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
	for(int i = 0; i < forest.size()*powers[0].size()/32; i++){
		gamma_vector1.insert(gamma_vector1.end(),gamma_subvector1.begin(),gamma_subvector1.end());
		gamma_vector2.insert(gamma_vector2.end(),gamma_subvector2.begin(),gamma_subvector2.end());
	}
	F sum1 = F(0);
	for(int k = 0; k <  forest.size(); k++){
		for(int i = 0; i < powers[k].size(); i++){
			sum1 += gamma_subvector2[i%32]*powers[k][i]*powers[k][i];
		}
	}
	P.sum1 = sum1;
	
	v1 = convert2vector(powers);v2 = convert2vector(powers);
	P.tP2 = _generate_3product_sumcheck_proof(gamma_vector2,v1,v2,mimc_hash(gamma,sum1));
	
	vector<F> temp;
	verify_3product_sumcheck(P.tP2,temp,P.tP2.c_poly[0].eval(F(0))+P.tP2.c_poly[0].eval(F(1)));
	
	v2.clear();
	P.eval_powers3 = P.tP2.vr[1];
	P.eval_powers3_x = P.tP2.randomness[0];

	vector<F> eval_powers3_x = P.tP2.randomness[0];
	
	v1 = convert2vector(powers);
	P.sP3 = generate_2product_sumcheck_proof(gamma_vector1,v1,P.tP2.final_rand);
	verify_2product_sumcheck(P.sP3,sum1);

	F sum2 = P.sP3.q_poly[0].eval(0) +P.sP3.q_poly[0].eval(1); 
	if(sum1 != sum2){
		printf("Error in partition sumcheck 2--5\n");
		exit(-1);
	}
	
	P.eval_powers4 = P.sP3.vr[1];
	P.eval_powers4_x = P.sP3.randomness[0];
	
	vector<F> aggr_beta(1ULL<<P.eval_powers1_x.size()),beta1,beta2,beta3,beta4;
	
	

	precompute_beta(P.eval_powers1_x,beta1);
	precompute_beta(P.eval_powers2_x,beta2);
	precompute_beta(P.eval_powers3_x,beta3);
	precompute_beta(P.eval_powers4_x,beta4);
	r = generate_randomness(4,P.sP3.final_rand);

	for(int i = 0; i < aggr_beta.size(); i++){
		aggr_beta[i] = r[0]*beta1[i] + r[1]*beta2[i] +r[2]*beta3[i] + r[3]*beta4[i];
	}
	v1 = convert2vector(powers);
	P.sP4 = generate_2product_sumcheck_proof(aggr_beta,v1,r[3]);
	verify_2product_sumcheck(P.sP4,r[0]*P.eval_powers1 + r[1]*P.eval_powers2 +r[2]*P.eval_powers3 + r[3]*P.eval_powers4);

	if(P.sP4.q_poly[0].eval(F(0)) + P.sP4.q_poly[0].eval(F(1)) != r[0]*P.eval_powers1 + r[1]*P.eval_powers2 +r[2]*P.eval_powers3 + r[3]*P.eval_powers4){
		printf("Error in partition sumcheck 2--6\n");
		exit(-1);	
	}
	P.final_rand = P.sP4.final_rand;
	auto t2 = chrono::high_resolution_clock::now();
    
	proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);

	//return P;
	
}



void streaming_sumcheck_partition_3(partition_SNARK_data_streaming data, vector<vector<F>> Tree){
	//int fd_diff = open(data.diff_data.file_name.c_str(),O_RDWR);
	stream_descriptor comp11,comp12,comp1,comp2;
    comp11.name = "inference_layer1";comp11.size = data.diff_data.size;comp11.pos = 0;
    comp12.name = "inference_layer2";comp12.size = data.diff_data.size;comp12.pos = 0;
    comp1.name = "inference_layer3";comp1.size = data.diff_data.size;comp1.pos = 0;
    comp2.name = "inference_layer4";comp2.size = data.diff_data.size;comp2.pos = 0;
    //int comp11 = open("inference_data_1",O_RDWR);
	//int comp12 = open("inference_data_2",O_RDWR);
	//int comp1 = open("inference_data_3",O_RDWR);
	//int comp2 = open("inference_data_4",O_RDWR);
	//int fd_paths = open(data.paths.file_name.c_str(),O_RDWR);
	//int permuted_data_fd = open(data.permuted_data.file_name.c_str(),O_RDWR);
	//int bits_fd = open(data.bit_vectors.file_name.c_str(),O_RDWR);
	reset_stream(data.paths);
    reset_stream(data.permuted_data);
    reset_stream(data.bit_vectors);
    reset_stream(data.diff_data);

	auto t1 = chrono::high_resolution_clock::now();
    
	vector<F> r = generate_randomness((int)log2(data.diff_data.size),F(0));
	F diff_eval = evaluate_vector_stream(data.diff_data,r,data.diff_data.size);
	

	int q = (int)log2(bin_size);
	if(1 << ((int)log2(q)) != q){
		q = 1 << (((int)log2(q))+1);
	}
	
	_prove_bit_decomposition_stream(data.bit_vectors, data.bit_vectors.size, r, diff_eval, r[r.size()-1], q);
	
    proof_stream P1 = generate_3product_sumcheck_proof_stream(comp1,comp2,data.diff_data.size , r, F(0), 2);
	verify_stream_3product_sumcheck(P1, r, P1.new_sum);

    vector<F> path_x1;
    if(P1.polynomials.size()!= 0){
        path_x1 = P1.P[1].randomness[0];path_x1.insert(path_x1.end(),P1.P[0].randomness[0].begin(),P1.P[0].randomness[0].end());
    }else{
        path_x1 = P1.P[0].randomness[0];
    }
    
    proof_stream P2 = generate_3product_sumcheck_proof_stream(comp11,comp12, data.diff_data.size, path_x1, P1.P[2].final_rand,2 );
	verify_stream_3product_sumcheck(P2, path_x1, P2.new_sum);

    vector<F> path_x2,path_x3;
    if(P2.polynomials.size()!= 0){
        path_x2 = P2.P[1].randomness[0],path_x3 = P2.P[1].randomness[0];
        path_x2.insert(path_x2.end(),P2.P[0].randomness[0].begin(),P2.P[0].randomness[0].end());
        path_x3.insert(path_x3.end(),P2.P[0].randomness[0].begin(),P2.P[0].randomness[0].end());
        
        path_x1.insert(path_x1.begin(),F(1));path_x1.insert(path_x1.begin(),F(0));
        path_x2.insert(path_x2.begin(),F(0));path_x2.insert(path_x2.begin(),F(0));
        path_x3.insert(path_x3.begin(),F(1));path_x3.insert(path_x3.begin(),F(0));
        
    }else{
        path_x2 = path_x3 = P2.P[0].randomness[0];
        path_x1.insert(path_x1.begin(),F(1));path_x1.insert(path_x1.begin(),F(0));
        path_x2.insert(path_x2.begin(),F(0));path_x2.insert(path_x2.begin(),F(0));
        path_x3.insert(path_x3.begin(),F(1));path_x3.insert(path_x3.begin(),F(0));
    
    }
    vector<vector<F>> path_x;path_x.push_back(path_x1);path_x.push_back(path_x2);path_x.push_back(path_x3);
    
    vector<F> eval_path = evaluate_vector_stream_batch(data.paths,path_x,data.paths.row_size*data.paths.col_size);
	vector<F> permuted_data_x;
    if(P2.polynomials.size()!= 0){
        permuted_data_x = P2.P[1].randomness[0];
        permuted_data_x.insert(permuted_data_x.end(),P2.P[0].randomness[0].begin(),P2.P[0].randomness[0].end());
        permuted_data_x.insert(permuted_data_x.begin(),F(1));	    
    }else{
        permuted_data_x = P2.P[0].randomness[0];
        permuted_data_x.insert(permuted_data_x.begin(),F(1));	    
    }
    F permuted_data_eval = evaluate_vector_stream(data.permuted_data,permuted_data_x,data.permuted_data.col_size*data.permuted_data.row_size);
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    
}



void streaming_forest_partition_sumcheck_3(partition_SNARK_data_streaming_forest data, vector<vector<vector<F>>> forest){
	//int fd_diff = open(data.diff_data.file_name.c_str(),O_RDWR);
	stream_descriptor comp11,comp12,comp1,comp2;
    comp11.name = "inference_layer1";comp11.size = data.diff_data.size;comp11.pos = 0;
    comp12.name = "inference_layer2";comp12.size = data.diff_data.size;comp12.pos = 0;
    comp1.name = "inference_layer3";comp1.size = data.diff_data.size;comp1.pos = 0;
    comp2.name = "inference_layer4";comp2.size = data.diff_data.size;comp2.pos = 0;
    //int comp11 = open("inference_data_1",O_RDWR);
	//int comp12 = open("inference_data_2",O_RDWR);
	//int comp1 = open("inference_data_3",O_RDWR);
	//int comp2 = open("inference_data_4",O_RDWR);
	//int fd_paths = open(data.paths.file_name.c_str(),O_RDWR);
	//int permuted_data_fd = open(data.permuted_data.file_name.c_str(),O_RDWR);
	//int bits_fd = open(data.bit_vectors.file_name.c_str(),O_RDWR);
	reset_stream(data.paths);
    reset_stream(data.permuted_data);
    reset_stream(data.bit_vectors);
    reset_stream(data.diff_data);

	auto t1 = chrono::high_resolution_clock::now();
    
	vector<F> r = generate_randomness((int)log2(data.diff_data.size),F(0));
	F diff_eval = evaluate_vector_stream(data.diff_data,r,data.diff_data.size);
	

	int q = (int)log2(bin_size);
	if(1 << ((int)log2(q)) != q){
		q = 1 << (((int)log2(q))+1);
	}
	_prove_bit_decomposition_stream(data.bit_vectors, data.bit_vectors.size, r, diff_eval, r[r.size()-1], q);
	

	proof_stream P1 = generate_3product_sumcheck_proof_stream(comp1,comp2,data.diff_data.size , r, F(0), 2);
	verify_stream_3product_sumcheck(P1, r, P1.new_sum);

    vector<F> path_x1;
    if(P1.polynomials.size()!= 0){
        path_x1 = P1.P[1].randomness[0];path_x1.insert(path_x1.end(),P1.P[0].randomness[0].begin(),P1.P[0].randomness[0].end());
    }else{
        path_x1 = P1.P[0].randomness[0];
    }
    
    proof_stream P2 = generate_3product_sumcheck_proof_stream(comp11,comp12, data.diff_data.size, path_x1, P1.P[2].final_rand,2 );
	verify_stream_3product_sumcheck(P2, path_x1, P2.new_sum);

	vector<F> path_x2,path_x3;
    if(P2.polynomials.size()!= 0){
        path_x2 = P2.P[1].randomness[0],path_x3 = P2.P[1].randomness[0];
        path_x2.insert(path_x2.end(),P2.P[0].randomness[0].begin(),P2.P[0].randomness[0].end());
        path_x3.insert(path_x3.end(),P2.P[0].randomness[0].begin(),P2.P[0].randomness[0].end());
        
        path_x1.insert(path_x1.begin(),F(1));path_x1.insert(path_x1.begin(),F(0));
        path_x2.insert(path_x2.begin(),F(0));path_x2.insert(path_x2.begin(),F(0));
        path_x3.insert(path_x3.begin(),F(1));path_x3.insert(path_x3.begin(),F(0));
        
    }else{
        path_x2 = path_x3 = P2.P[0].randomness[0];
        path_x1.insert(path_x1.begin(),F(1));path_x1.insert(path_x1.begin(),F(0));
        path_x2.insert(path_x2.begin(),F(0));path_x2.insert(path_x2.begin(),F(0));
        path_x3.insert(path_x3.begin(),F(1));path_x3.insert(path_x3.begin(),F(0));
    
    }
    vector<vector<F>> path_x;path_x.push_back(path_x1);path_x.push_back(path_x2);path_x.push_back(path_x3);
    
    vector<F> eval_path = evaluate_vector_stream_batch(data.paths,path_x,data.paths.row_size*data.paths.col_size);
	vector<F> permuted_data_x;
    if(P2.polynomials.size()!= 0){
        permuted_data_x = P2.P[1].randomness[0];
        permuted_data_x.insert(permuted_data_x.end(),P2.P[0].randomness[0].begin(),P2.P[0].randomness[0].end());
        permuted_data_x.insert(permuted_data_x.begin(),F(1));	    
    }else{
        permuted_data_x = P2.P[0].randomness[0];
        permuted_data_x.insert(permuted_data_x.begin(),F(1));	    
    }
    F permuted_data_eval = evaluate_vector_stream(data.permuted_data,permuted_data_x,data.permuted_data.col_size*data.permuted_data.row_size);
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    

}

void streaming_sumcheck_leaves_1(histogram_SNARK_data_streaming data, int Attr, F previous_r){
	stream_descriptor compressed_transcript;compressed_transcript.name = "compressed_read_write";
    compressed_transcript.pos = 0;compressed_transcript.size = 2*data.read_transcript.row_size;
    compressed_transcript.compress_vector = data.random_vector;

    //int read_write_fd = open("read_write_compressed",O_RDWR);
	//int read_transcript_fd = open(data.read_transcript.file_name.c_str(),O_RDWR);
	//int write_transcript_fd = open(data.write_transcript.file_name.c_str(),O_RDWR);
	
	auto t1 = chrono::high_resolution_clock::now();
    vector<F> prev_x;
	mul_tree_proof_stream mP1 = prove_multiplication_tree_stream(compressed_transcript, 2, data.read_transcript.row_size, previous_r, prev_x);
	vector<F> x = mP1.individual_randomness;
   
    reset_stream(compressed_transcript);
    reset_histograms();
	
   
    F eval_read_tr = evaluate_vector_stream(compressed_transcript,x,data.read_transcript.row_size);
	compressed_transcript.pos = data.read_transcript.row_size;
   
    F eval_write_tr = evaluate_vector_stream(compressed_transcript,x,data.write_transcript.row_size);
	if((F(1)-mP1.global_randomness[0])*eval_read_tr + mP1.global_randomness[0]*eval_write_tr != mP1.final_eval){
		printf("Error in histograms sumcheck 1\n");
		exit(-1);
	}
	vector<stream_descriptor> fd;fd.push_back(data.read_transcript);
	vector<size_t> fd_cols; fd_cols.push_back(8);
	vector<size_t> fd_size; fd_size.push_back(data.read_transcript.row_size*8);
    
	reset_histograms();
	vector<F> evals_read = prepare_matrix_streaming(fd, fd_cols, fd_size, data.read_transcript.row_size, x, 8);
	fd.clear();fd_cols.clear();fd_size.clear();
	fd.push_back(data.write_transcript);fd_cols.push_back(8);fd_size.push_back(data.read_transcript.row_size*8);
	reset_histograms();
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
    
}

void streaming_forest_sumcheck_leaves_1( histogram_SNARK_data_streaming_forest data, int Attr, F previous_r){
	stream_descriptor compressed_transcript;compressed_transcript.name = "compressed_read_write";
    compressed_transcript.pos = 0;compressed_transcript.size = 2*data.read_transcript.row_size;
    compressed_transcript.compress_vector = data.random_vector;

    //int read_write_fd = open("read_write_compressed",O_RDWR);
	//int read_transcript_fd = open(data.read_transcript.file_name.c_str(),O_RDWR);
	//int write_transcript_fd = open(data.write_transcript.file_name.c_str(),O_RDWR);
	
    vector<F> prev_x;
	
	
	auto t1 = chrono::high_resolution_clock::now();
    printf("Mul Tree input size : %lld\n",2*data.read_transcript.row_size);
	
	// > 2^28-29
	mul_tree_proof_stream mP1;
	if((int)log2(((size_t)2)*data.read_transcript.row_size) >= 29){
		mP1 = prove_multiplication_tree_stream_shallow(compressed_transcript, 2, data.read_transcript.row_size, previous_r,3,prev_x);
	}else{
		mP1 = prove_multiplication_tree_stream(compressed_transcript, 2, data.read_transcript.row_size, previous_r, prev_x);
	}
	
	//mul_tree_proof_stream mP1 = prove_multiplication_tree_stream(compressed_transcript, 2, data.read_transcript.row_size, previous_r, prev_x);
	vector<F> x = mP1.individual_randomness;
	
    reset_stream(compressed_transcript);
    reset_histograms();
	
   
    F eval_read_tr = evaluate_vector_stream(compressed_transcript,x,data.read_transcript.row_size);
	compressed_transcript.pos = data.read_transcript.row_size;
   
    F eval_write_tr = evaluate_vector_stream(compressed_transcript,x,data.write_transcript.row_size);
	if((F(1)-mP1.global_randomness[0])*eval_read_tr + mP1.global_randomness[0]*eval_write_tr != mP1.final_eval){
		printf("Error in histograms sumcheck 1\n");
		exit(-1);
	}
	
	vector<stream_descriptor> fd;fd.push_back(data.read_transcript);
	vector<size_t> fd_cols; fd_cols.push_back(8);
	vector<size_t> fd_size; fd_size.push_back(data.read_transcript.row_size*8);
   
	reset_histograms_forest();
	vector<F> evals_read = prepare_matrix_streaming(fd, fd_cols, fd_size, data.read_transcript.row_size, x, 8);
	
	fd.clear();fd_cols.clear();fd_size.clear();
	fd.push_back(data.write_transcript);fd_cols.push_back(8);fd_size.push_back(data.read_transcript.row_size*8);
	reset_histograms();
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
    
    vector<vector<F>> mul_tree_input(1);
	
	//mul_tree_input[0] = data.compressed_init;
	//mul_tree_input[0] = data.compressed_final;
	mul_tree_proof_stream mP2 = prove_multiplication_tree_stream(data.compressed_final,1,data.compressed_final.size,previous_r,prev_x);
	
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
	//if(mP2.output[0]*mP1.out[1] != mP2.output[1]*mP1.out[0]){
	//	printf("Error in transcript mem\n");
	//	exit(-1);
	//}
	
}


void streaming_sumcheck_leaves_2(histogram_SNARK_data_streaming data, int Attr, F previous_r){

	
    reset_stream(data.read_transcript);
    reset_stream(data.write_transcript);
    reset_stream(data.input_data);
    reset_stream(data.input_aux);
    
	
    reset_histograms();
    
    //int read_transcript_fd = open(data.read_transcript.file_name.c_str(),O_RDWR);
	//int write_transcript_fd = open(data.write_transcript.file_name.c_str(),O_RDWR);
	//int input_fd = open(data.input_data.file_name.c_str(),O_RDWR);
	//int input_aux_fd = open(data.input_aux.file_name.c_str(),O_RDWR);
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
    
	
	vector<F> read_evals = evaluate_vector_stream_batch(data.read_transcript,x_acc,data.read_transcript.col_size*data.read_transcript.row_size);
	reset_histograms();
    
	vector<F> write_evals = evaluate_vector_stream_batch(data.write_transcript,x_acc,data.read_transcript.col_size*data.read_transcript.row_size);
	reset_histograms();
    
	
	vector<F> input_evals = evaluate_vector_stream_batch(data.input_data,x_input_acc,data.input_data.row_size*data.input_data.col_size);
	
	
	vector<F> aux_evals = evaluate_vector_stream_batch(data.input_aux,x_metadata_acc,data.input_aux.row_size*data.input_aux.col_size);
	
	
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

    reset_stream(data.read_transcript);
    reset_stream(data.write_transcript);
    reset_stream(data.input_data);
    reset_stream(data.input_aux);
    
	

	previous_r = chain_hash(chain_hash(chain_hash(chain_hash(x[x.size()-1],aux_evals),input_evals),read_evals),write_evals);

	vector<F> r1 = generate_randomness(5,previous_r);
	vector<F> r2 = generate_randomness(2,r1[r1.size()-1]);
	reset_histograms();
    
	// Note that we do not have to commit to the read/write transcript since we already commit to input/aux
	// we only need to commit to the counter 
	//proof_stream P = generate_2product_sumcheck_proof_stream_beta(data.read_transcript, x_acc, r1,data.read_transcript.col_size*data.read_transcript.row_size, r2[r2.size()-1]);
	//verify_stream_2product_sumcheck(P,  x_acc,r1, P.new_sum);
	
	//reset_histograms();
    //P = generate_2product_sumcheck_proof_stream_beta(data.write_transcript, x_acc, r1,data.read_transcript.col_size*data.read_transcript.row_size, r2[r2.size()-1]);
	//verify_stream_2product_sumcheck(P,  x_acc,r1, P.new_sum);
	
	proof_stream P = generate_2product_sumcheck_proof_stream_beta(data.input_data, x_input_acc, r2,data.input_data.row_size*data.input_data.col_size, r2[r2.size()-1]);
	verify_stream_2product_sumcheck(P,  x_input_acc,r2, P.new_sum);
	
	
	P = generate_2product_sumcheck_proof_stream_beta(data.input_aux, x_metadata_acc, r2, data.input_aux.row_size*data.input_aux.col_size , r2[r2.size()-1]);
	verify_stream_2product_sumcheck(P,  x_metadata_acc,r2, P.new_sum);
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    
}


void streaming_forest_sumcheck_leaves_2( histogram_SNARK_data_streaming_forest data, int Attr, F previous_r){
	reset_stream(data.read_transcript);
    reset_stream(data.write_transcript);
    reset_stream(data.input_data);
    reset_stream(data.input_aux);
    
    reset_histograms_forest();
    
    //int read_transcript_fd = open(data.read_transcript.file_name.c_str(),O_RDWR);
	//int write_transcript_fd = open(data.write_transcript.file_name.c_str(),O_RDWR);
	//int input_fd = open(data.input_data.file_name.c_str(),O_RDWR);
	//int input_aux_fd = open(data.input_aux.file_name.c_str(),O_RDWR);
	
	vector<F> x = generate_randomness((int)log2(data.read_transcript.row_size),F(0));
	//printf(">> %d\n",P.P1.sP3.randomness[0].size() );
	
	
	vector<F> x0_metadata,x1_metadata;


	vector<F> x0_input,x1_input;
	for(int i =0 ; i <  (int)log2(data.input_data.row_size*data.input_data.col_size)-1; i++){
	//for(int i = x.size() - (int)log2(data.input_data.row_size*data.input_data.col_size)+1; i < x.size(); i++){
	//	x0_input.push_back(x[i]);
		x1_input.push_back(x[i]);
	}
	for(int i = 0; i < (int)log2(data.input_data.col_size)-1; i++){
		x0_input.push_back(x[i]);
	//	x1_input.push_back(x[i]);
	}
	for(int i = x.size() + x0_input.size() - (int)log2(data.input_data.size/2); i < x.size(); i++){
		x0_input.push_back(x[i]);
	//	x1_input.push_back(x[i]);
	}
	
	vector<vector<F>> x_input_acc,x_metadata_acc;
	vector<F> x0_readwrite,x1_readwrite,x2_readwrite,x3_readwrite,x4_readwrite;
	x0_input.insert(x0_input.begin(), F(0));
	x1_input.insert(x1_input.begin(), F(1));
	x0_metadata.push_back(F(0));
	x1_metadata.push_back(F(1));
	vector<F> metadata_randomness;
	//for(int i = x.size() - (int)log2(data.input_aux.row_size); i < x.size(); i++){
	//	x0_metadata.push_back(x[i]);
	//	x1_metadata.push_back(x[i]);	
	//	metadata_randomness.push_back(x[i]);
	//}

	
	x_input_acc.push_back(x0_input);x_input_acc.push_back(x1_input);
	
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

	x0_metadata.push_back(x[0]);
	x1_metadata.push_back(x[0]);
	
	
	for(int i = x.size() - (int)log2(data.input_aux.row_size) + 1 ; i < x.size(); i++){
	//for(int i = x.size() - (int)log2(data.input_aux.row_size*data.input_aux.col_size)+1; i < x.size(); i++){
		x0_metadata.push_back(x[i]);
		x1_metadata.push_back(x[i]);
	}
	x_metadata_acc.push_back(x0_metadata);x_metadata_acc.push_back(x1_metadata);

	vector<vector<F>> x_acc;x_acc.push_back(x0_readwrite);x_acc.push_back(x1_readwrite);x_acc.push_back(x2_readwrite);
	x_acc.push_back(x3_readwrite);x_acc.push_back(x4_readwrite);

	auto t1 = chrono::high_resolution_clock::now();


	reset_histograms_forest();
    vector<F> read_evals = evaluate_vector_stream_batch_hardcoded(data.read_transcript,x_acc,data.read_transcript.col_size*data.read_transcript.row_size);
	reset_histograms_forest();
    
	
	
	
	vector<F> write_evals = evaluate_vector_stream_batch_hardcoded(data.write_transcript,x_acc,data.read_transcript.col_size*data.read_transcript.row_size);
	
	reset_histograms_forest();
    
	vector<F> input_evals = evaluate_vector_stream_batch(data.input_data,x_input_acc,data.input_data.row_size*data.input_data.col_size);
	
	

	
	vector<F> aux_evals = evaluate_vector_stream_batch(data.input_aux,x_metadata_acc,data.input_aux.row_size*data.input_aux.col_size);
	
	
	
	if(input_evals[0] != read_evals[1] || input_evals[0] != write_evals[1]){
		printf("Error leaves_sumcheck 2---1\n");
		exit(-1);
	}
	if(input_evals[1] != read_evals[2] || input_evals[1] != write_evals[2]){
		printf("Error leaves_sumcheck 2---2\n");
		//exit(-1);
	}
	// Error will be thrown if attributes are not power of 2
	if(aux_evals[0] != read_evals[0] || aux_evals[0] != write_evals[0]){
		printf("Error leaves_sumcheck 2---3\n");
		//exit(-1);	
	}
	if(aux_evals[1] != read_evals[3] || aux_evals[1] != write_evals[3]){
		printf("Error leaves_sumcheck 2---4\n");
		//exit(-1);	
	}
	if(write_evals[4] - read_evals[4] - F(1) != F(0)){
		printf("Error leaves_sumcheck 2---5\n");
		//exit(-1);
	}

    reset_stream(data.read_transcript);
    reset_stream(data.write_transcript);
    reset_stream(data.input_data);
    reset_stream(data.input_aux);
    
	
	previous_r = chain_hash(chain_hash(chain_hash(chain_hash(x[x.size()-1],aux_evals),input_evals),read_evals),write_evals);

	vector<F> r1 = generate_randomness(5,previous_r);
	vector<F> r2 = generate_randomness(2,r1[r1.size()-1]);
	reset_histograms_forest();

	
    //proof_stream P = generate_2product_sumcheck_proof_stream_beta(data.read_transcript, x_acc, r1,data.read_transcript.col_size*data.read_transcript.row_size, r2[r2.size()-1]);
	//verify_stream_2product_sumcheck(P,x_acc,r1,P.new_sum);
	
	//reset_histograms_forest();
    
	//P = generate_2product_sumcheck_proof_stream_beta(data.write_transcript, x_acc, r1,data.read_transcript.col_size*data.read_transcript.row_size, r2[r2.size()-1]);
	
	//verify_stream_2product_sumcheck(P,x_acc,r1,P.new_sum);
	
	
	proof_stream P = generate_2product_sumcheck_proof_stream_beta(data.input_data, x_input_acc, r2,data.input_data.row_size*data.input_data.col_size, r2[r2.size()-1]);
	
	verify_stream_2product_sumcheck(P,x_input_acc,r2,P.new_sum);
	
	P = generate_2product_sumcheck_proof_stream_beta(data.input_aux, x_metadata_acc, r2, data.input_aux.row_size*data.input_aux.col_size , r2[r2.size()-1]);
	
	verify_stream_2product_sumcheck(P,x_metadata_acc,r2,P.new_sum);
	
	
	auto t2 = chrono::high_resolution_clock::now();
    proving_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    
}



void streaming_gini_sumcheck_1( split_SNARK_streaming_forest data,vector<F> x, int Attr, F final_eval, F previous_r,
	vector<F> &x_dividents, vector<F> &x_divisors, F &divident_eval, F &divisor_eval){
	
	stream_descriptor divisors_quot; divisors_quot.name = "divisors_quot"; divisors_quot.pos = 0; divisors_quot.size  = data.divisors.size;
	
	stream_descriptor cond; cond.name = "cond"; cond.pos = 0; cond.size  = data.divisors.size;
	stream_descriptor cond_inv; cond_inv.name = "cond_inv"; cond_inv.pos = 0; cond_inv.size  = data.divisors.size;

	printf("%d,%d\n",x.size(),divisors_quot.size);
	F eval1 = evaluate_vector_stream(divisors_quot,x,divisors_quot.size);
	F rand = mimc_hash(previous_r,eval1);
	F eval2 = evaluate_vector_stream(data.dividents,x,divisors_quot.size);
	rand = mimc_hash(rand,eval2);
	if(F(1<<Q)*eval2 - eval1 != final_eval){
		printf("I/O Error gini sumcheck1\n");
		exit(-1);
	}

	
	proof_stream tP1 = generate_3product_sumcheck_proof_stream(data.quotients,data.divisors,data.quotients.size,x,rand,SUM);
	verify_stream_3product_sumcheck(tP1, x, eval1);

	reset_stream(data.quotients);reset_stream(data.divisors);


	if(tP1.P.size()>1){
		
		x_divisors = tP1.P[1].randomness[0];
		x_divisors.insert(x_divisors.end(),tP1.P[0].randomness[0].begin(),tP1.P[0].randomness[0].end());
	}else{
		x_divisors = tP1.P[0].randomness[0];
	}
		
	proof_stream tP2 = generate_3product_sumcheck_proof_stream(cond,data.dividents,cond.size,x,tP1.P[0].final_rand,SUM);
	verify_stream_3product_sumcheck(tP2, x, eval2);

	reset_stream(cond);reset_stream(data.dividents);
	
	vector<F> eval_point1;
	F cond_eval1;
	if(tP2.P.size()>1){
		eval_point1 = tP2.P[1].randomness[0];
		cond_eval1 = tP2.P[1].vr[0];
		eval_point1.insert(eval_point1.end(),tP2.P[0].randomness[0].begin(),tP2.P[0].randomness[0].end());
		
	}else{
		eval_point1 = tP2.P[0].randomness[0];
		
		cond_eval1 = tP2.P[0].vr[0];
	}
	x_dividents = eval_point1;
	divident_eval = tP2.vr[1];

	proof_stream tP3 = generate_3product_sumcheck_proof_stream(cond_inv,data.N,cond.size,x,tP2.P[0].final_rand,SUM);
	verify_stream_3product_sumcheck(tP3,x, F_ZERO);

	reset_stream(cond_inv);reset_stream(data.N);
	
	F cond_eval2;
	vector<F> eval_point2;

	if(tP3.P.size()>1){
		eval_point2 = tP3.P[1].randomness[0];
		eval_point2.insert(eval_point2.end(),tP3.P[0].randomness[0].begin(),tP3.P[0].randomness[0].end());
		cond_eval2 = F(1) - tP3.P[1].vr[0];
	}else{
		eval_point2 = tP3.P[0].randomness[0];
		cond_eval2 = F(1) - tP3.P[0].vr[0];
	}

	vector<F> a = generate_randomness(2,tP3.P[0].final_rand);
	
	divisor_eval = tP1.vr[1];
	vector<vector<F>> eval;eval.push_back(eval_point1);eval.push_back(eval_point2);
	proof_stream sP = generate_2product_sumcheck_proof_stream_beta(cond,eval,a,cond.size,a[1]);
	verify_stream_2product_sumcheck(sP,eval,a,sP.new_sum);

	reset_stream(cond);
	vector<F> randomness;

	if(sP.P.size()>1){
		randomness = sP.P[0].randomness[0];
		randomness.insert(randomness.end(),sP.P[1].randomness[0].begin(),sP.P[1].randomness[0].end());
	}else{
		randomness = sP.P[0].randomness[0];
	}
	
	//P.cond_eval3 = P.sP.vr[0];
	//beta1.clear();
	//vector<F> randomness = P.sP.randomness[0];
	
	//precompute_beta(randomness,beta1);
	
	proof_stream tP4 = generate_3product_sumcheck_proof_stream(data.N,data.inverses,data.N.size,randomness,sP.P[0].final_rand,SUM);
	verify_stream_3product_sumcheck(tP4, randomness, tP4.new_sum);

	//if(P.tP4.c_poly[0].eval(F(0)) + P.tP4.c_poly[0].eval(F(1)) != P.cond_eval3){
	//	printf("Error in gini sumcheck1--5\n");
	//	exit(-1);
	//} 
}


void streaming_gini_sumcheck_2( split_SNARK_streaming_forest data, vector<F> x_dividents,vector<F> x_divisors ,F divisors_eval, F dividents_eval, F previous_r){
	
	stream_descriptor square_N; square_N.name = "square_N"; square_N.pos = 0; square_N.size  = data.N.size;
	stream_descriptor pairwise_prod; pairwise_prod.name = "pairwise_prod"; pairwise_prod.pos = 0; pairwise_prod.size  = data.N.size;
	stream_descriptor N_sum; N_sum.name = "N_sum"; N_sum.pos = 0; N_sum.size  = data.N.size;
	stream_descriptor N_1; N_1.name = "gini_input_1"; N_1.pos = 0; N_1.size  = data.N.size;
	stream_descriptor N_0; N_0.name = "gini_input_2"; N_0.pos = 0; N_0.size  = data.N.size;
	

	//F divisors_eval = evaluate_vector(divisors,randomness);
	//F dividents_eval = evaluate_vector(dividents,randomness);
	F square_N_eval = evaluate_vector_stream(square_N,x_dividents,square_N.size);

	F pairwise_prod_eval = evaluate_vector_stream(pairwise_prod,x_dividents,square_N.size);
	F rand = mimc_hash(previous_r,square_N_eval);
	rand = mimc_hash(rand,pairwise_prod_eval);
	if(dividents_eval != square_N_eval - F(2)*pairwise_prod_eval){
		printf("Error in gini sumcheck2--0.5\n");
		exit(-1);
	}

	// Sumcheck for divisors
	proof_stream tP1 = generate_3product_sumcheck_proof_stream(data.N,N_sum,N_sum.size,x_divisors,rand,SUM);
	verify_stream_3product_sumcheck(tP1, x_divisors, divisors_eval);

	reset_stream(data.N);
	vector<F> randomness;
	vector<F> aggr_x1; 
	
	if(tP1.P.size() > 1){
		aggr_x1 = tP1.P[1].randomness[0];
		aggr_x1.insert(aggr_x1.end(),tP1.P[0].randomness[0].begin(),tP1.P[0].randomness[0].end());
	
		for(int i = 1; i < tP1.P[1].randomness[0].size(); i++){
			randomness.push_back(tP1.P[1].randomness[0][i]);
		}
		randomness.insert(randomness.end(),tP1.P[0].randomness[0].begin(),tP1.P[0].randomness[0].end());
	}else{
		for(int i = 1; i < tP1.P[0].randomness[0].size(); i++){
			randomness.push_back(tP1.P[0].randomness[0][i]);
		}
		aggr_x1 = tP1.P[0].randomness[0];
		
	}
	
	
	vector<vector<F>> evals(2);evals[0] = randomness;evals[1] = randomness;
	
	evals[0].insert(evals[0].begin(),F(0));
	evals[1].insert(evals[1].begin(),F(1));
	
	vector<F> batch_eval = evaluate_vector_stream_batch(data.N,evals,data.N.size);
	reset_stream(data.N);
	
	F eval1_N0 = batch_eval[0];
	rand = mimc_hash(tP1.P[0].final_rand,eval1_N0);
	F eval1_N1 = batch_eval[1];
	rand = mimc_hash(rand,eval1_N1);
	F eval1_N = tP1.vr[0];
	if(eval1_N0 + eval1_N1 != tP1.vr[1]){
		printf("Error in gini sumcheck2--1\n");
		exit(-1);
	}



	vector<F> t_x = randomness;

	
	
	vector<F> aggr_x2 = evals[0],aggr_x3 = evals[1];
	// Sumchecks for dividents
	
	proof_stream tP2 = generate_3product_sumcheck_proof_stream(data.N,data.N,data.N.size,x_dividents,rand,SUM);
	verify_stream_3product_sumcheck(tP2,x_dividents, square_N_eval);

	reset_stream(data.N);
	
	vector<F> aggr_x4;
	if(tP2.P.size() > 1){
		aggr_x4 = tP2.P[1].randomness[0];
		aggr_x4.insert(aggr_x4.end(),tP2.P[0].randomness[0].begin(),tP2.P[0].randomness[0].end());
		
	}else{
		aggr_x4 = tP2.P[0].randomness[0];
	}

	F eval2_N = tP2.vr[0];
	
	
	proof_stream tP3 = generate_3product_sumcheck_proof_stream(N_0,N_1,N_1.size,x_dividents,tP2.P[0].final_rand,SUM);
	verify_stream_3product_sumcheck(tP3,x_dividents,pairwise_prod_eval);

	vector<F> _aggr_x1,_aggr_x2;
	if(tP3.P.size() > 1){
		_aggr_x1 = tP3.P[1].randomness[0];
		_aggr_x1.insert(_aggr_x1.end(),tP3.P[0].randomness[0].begin(),tP3.P[0].randomness[0].end());
		_aggr_x2 = _aggr_x1;
		
	
	}else{
		_aggr_x1 = tP3.P[0].randomness[0];
		_aggr_x2 = tP3.P[0].randomness[0];
		
	}
	_aggr_x1.insert(_aggr_x1.begin(),F(0));
	_aggr_x2.insert(_aggr_x2.begin(),F(1));
		

	vector<F> r1 = generate_randomness(4,tP3.P[0].final_rand);

	vector<vector<F>> final_beta_aggr;final_beta_aggr.push_back(aggr_x1);final_beta_aggr.push_back(aggr_x2);
	final_beta_aggr.push_back(aggr_x3);final_beta_aggr.push_back(aggr_x4);
	proof_stream sP1 = generate_2product_sumcheck_proof_stream_beta(data.N,final_beta_aggr,r1,data.N.size,r1[3]);
	verify_stream_2product_sumcheck(sP1,final_beta_aggr,r1,sP1.new_sum);

	reset_stream(data.N);
	
	F s = r1[0]*eval1_N + r1[1]*eval1_N0 + r1[2]*eval1_N1+r1[3]*eval2_N;
	
	vector<F> _aggr_x3,_aggr_x4;
	if(sP1.P.size() > 1){
		//if(eval_poly(sP1.polynomials[0],sP1.c ) != s){
		//	printf("Error in gini sumcheck2--2\n");
		//	exit(-1);
		//}
		_aggr_x3 = sP1.P[1].randomness[0];
		_aggr_x3.insert(_aggr_x3.end(),sP1.P[0].randomness[0].begin(),sP1.P[0].randomness[0].end());
		_aggr_x4 = _aggr_x3;
	
		
	}else{
		//if(s != sP1.P[0].c_poly[0].eval(F(0))+ sP1.P[1].c_poly[0].eval(F(1))){
		//	printf("Error in gini sumcheck2--2\n");
		//	exit(-1);
		//}
		_aggr_x3 = sP1.P[0].randomness[0];
		_aggr_x4 = sP1.P[0].randomness[0];
	
	}
	_aggr_x3.insert(_aggr_x3.begin(),F(0));
	_aggr_x4.insert(_aggr_x4.begin(),F(1));
	
	
	F gini_eval1 = tP3.vr[0];
	F gini_eval2 = tP3.vr[1];
	vector<vector<F>> gini_x(2);gini_x[0] = _aggr_x3;gini_x[1] = _aggr_x4;
	
	vector<F> gini_evals = evaluate_vector_stream_batch(data.gini_inputs,gini_x,data.gini_inputs.size);
	reset_stream(data.gini_inputs);
	
	F gini_eval3 = gini_evals[0];
	F gini_eval4 = gini_evals[1];
	r1 = generate_randomness(4,sP1.P[0].final_rand);
	gini_x.push_back(_aggr_x1);
	gini_x.push_back(_aggr_x2);
	proof_stream P = generate_2product_sumcheck_proof_stream_beta(data.gini_inputs,gini_x,r1,data.gini_inputs.size,r1[3]);
	verify_stream_2product_sumcheck(P,gini_x,r1,P.new_sum);

	
}


void streaming_bagging_2(streaming_bagging_SNARK data, vector<F> x_compressed, F compresssed_eval , F previous_r){
	vector<vector<F>> remainder_x(2); remainder_x[0] = x_compressed;remainder_x[1] = x_compressed;
	
	remainder_x[0].insert(remainder_x[0].begin(),F(0));
	remainder_x[1].insert(remainder_x[1].begin(),F(1));
	vector<F> pair_evals = evaluate_vector_stream_batch(data.pairs,remainder_x,data.pairs.size);
	vector<F> r = data.compressed_pairs.compress_vector;
	//0 : hist
	//1 : remainders
	if(r[2] + pair_evals[0]*r[0] + pair_evals[1]*r[1] != compresssed_eval){
		printf("Error in bagging 1\n");
	}
	F quotients_eval = evaluate_vector_stream(data.randomness_quotient,x_compressed,data.randomness_quotient.size);
	proof_stream P1 = generate_2product_sumcheck_proof_stream(data.randomness,data.s1,data.s1.size,previous_r);

	proof_stream P2 = generate_2product_sumcheck_proof_stream(data.randomness,data.s2,data.s2.size,previous_r);
	
	vector<vector<F>> x_eval;
	x_eval.push_back(x_compressed);
	if(P1.P.size() > 1){
		vector<F> x;
		x  = (P1.P[1].randomness[0]);
		x.insert(x.end(),P1.P[0].randomness[0].begin(),P1.P[0].randomness[0].end());
		x_eval.push_back(x);
		x  = (P2.P[1].randomness[0]);
		x.insert(x.end(),P2.P[0].randomness[0].begin(),P2.P[0].randomness[0].end());
		x_eval.push_back(x);
		
	}else{
		x_eval.push_back(P1.P[0].randomness[0]);
		x_eval.push_back(P2.P[0].randomness[0]);
	}
	
	vector<F> a = generate_randomness(3,x_eval[2][x_eval[2].size()-1]);
	proof_stream P3=  generate_2product_sumcheck_proof_stream_beta(data.randomness,x_eval,a,data.randomness.size,a[2]);
}

void streaming_bagging_1( streaming_bagging_SNARK data, vector<F> &x_compressed, F &compresssed_eval , F previous_r){
	
	vector<F> prev_x;

	vector<F> powers(32*data.powers.size());
	vector<F> final_powers_input(32*data.powers.size());
	vector<F> final_powers(powers.size()/32);
	vector<vector<F>> mul_tree_input;
	vector<vector<F>> final_powers_tree_input;
	
	for(int i = 0; i < data.powers.size(); i++){
		powers[32*i] = data.powers[i];
		for(int j = 1; j < 32; j++){
			powers[32*i + j] = powers[32*i + j-1]*powers[32*i + j-1];
		}
	}
	for(int i = 0; i < data.powers.size(); i++){
		vector<F> temp(32);
		final_powers[i] = F(1);
		
		for(int j =0 ;j < 32; j++){
			final_powers_input[32*i + j] = powers[32*i + j]*data.power_bits[32*i+j];
			temp[j] = (F(1)-data.power_bits[i*32+j]) + powers[i*32+j]*data.power_bits[i*32+j];
			final_powers[i] *= temp[j];
		}
		final_powers_tree_input.push_back(temp);
	
	}


	mul_tree_proof_stream mP1 = prove_multiplication_tree_stream(data.compressed_pairs,1,data.compressed_pairs.size,previous_r,prev_x);
	
	x_compressed = mP1.r;
	compresssed_eval = mP1.final_eval;
	
	mul_tree_input.push_back(final_powers);
	
	
	mul_tree_proof mP2 = prove_multiplication_tree(mul_tree_input,mP1.final_r,prev_x);
	
	vector<F> r = mP2.individual_randomness;
	for(int i = 0; i < mP2.global_randomness.size(); i++){
		r.push_back(mP2.global_randomness[i]);
	}
	F final_powers_eval = evaluate_vector(final_powers,r);
	if(mP2.final_eval != final_powers_eval){
		printf("Error in partition sumcheck 2--1\n");
		exit(-1);
	}

	
	mul_tree_input.clear();
	mul_tree_input = final_powers_tree_input;
	mul_tree_proof mP3 = prove_multiplication_tree(mul_tree_input,mP2.individual_randomness[mP2.individual_randomness.size()-1],mP2.final_r);
	
	r = mP3.individual_randomness;
	for(int i = 0; i < mP3.global_randomness.size(); i++){
		r.push_back(mP3.global_randomness[i]);
	}
	F eval_bits1 = evaluate_vector(data.power_bits,r);
	F final_powers_input_eval = evaluate_vector(final_powers_input,r);
	
	eval_bits1 = eval_bits1;
	final_powers_input_eval = final_powers_input_eval;
	vector<F> eval_bits1_x = r;
	vector<F> final_powers_input_eval_x = r;

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
	verify_3product_sumcheck(tP1,r,tP1.c_poly[0].eval(F(0))+tP1.c_poly[0].eval(F(1)));
	
	if(tP1.c_poly[0].eval(0) + tP1.c_poly[0].eval(1) != final_powers_input_eval){
		printf("Error in partition sumcheck 2--3\n");
		exit(-1);
	}
	F eval_bits2 = tP1.vr[0];
	F eval_powers1 = tP1.vr[1];
	vector<F> eval_powers1_x = tP1.randomness[0];
	// Check power consistency with compressed tree
	eval_powers1 = eval_powers1;
	eval_powers1_x = eval_powers1_x;
	
	// Check power consistency
	F gamma = tP1.final_rand;
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
	sum1 = sum1;
	temp_powers = powers;
	vector<F> temp_powers2 = powers;
	
	proof tP2 = _generate_3product_sumcheck_proof(gamma_vector2,temp_powers,temp_powers2,mimc_hash(gamma,sum1));
	vector<F> t_r;
	verify_3product_sumcheck(tP2,t_r,tP2.c_poly[0].eval(F(0))+tP2.c_poly[0].eval(F(1)));
	
	//F sum1 = tP2.c_poly[0].eval(0) + tP2.c_poly[0].eval(1);
	F eval_powers3 = tP2.vr[1];


	vector<F> eval_powers3_x = tP2.randomness[0];
	temp_powers = powers;
	proof sP3 = generate_2product_sumcheck_proof(gamma_vector1,temp_powers,tP2.final_rand);
	verify_2product_sumcheck(sP3, sP3.q_poly[0].eval(0) +sP3.q_poly[0].eval(1));

	F sum2 = sP3.q_poly[0].eval(0) +sP3.q_poly[0].eval(1); 
	if(sum1 != sum2){
		printf("Error in partition sumcheck 2--5\n");
		exit(-1);
	}
	
	F eval_powers4 = sP3.vr[1];
	vector<F> eval_powers4_x = sP3.randomness[0];
	
	vector<F> aggr_beta(1ULL<<eval_powers1_x.size()),beta1,beta2,beta3,beta4;
	

	precompute_beta(eval_powers1_x,beta1);
	//precompute_beta(eval_powers2_x,beta2);
	precompute_beta(eval_powers3_x,beta3);
	precompute_beta(eval_powers4_x,beta4);

	r = generate_randomness(4,sP3.final_rand);

	for(int i = 0; i < aggr_beta.size(); i++){
		aggr_beta[i] = r[0]*beta1[i]  +r[2]*beta3[i] + r[3]*beta4[i];
	}
	proof sP4 = generate_2product_sumcheck_proof(aggr_beta,powers,r[3]);
	verify_2product_sumcheck(sP4, sP4.q_poly[0].eval(0) +sP4.q_poly[0].eval(1));

	if(sP4.q_poly[0].eval(F(0)) + sP4.q_poly[0].eval(F(1)) != r[0]*eval_powers1  +r[2]*eval_powers3 + r[3]*eval_powers4){
		printf("Error in partition sumcheck 2--6\n");
		exit(-1);	
	}
	F final_rand = sP4.final_rand;

	//vector<F> random_x1 = generate_randomness((int)log2(data.randomness.size)-1,previous_r);
	
	//F eval1 = evaluate_vector_stream(data.randomness,)


}


