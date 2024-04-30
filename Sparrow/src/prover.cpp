#include "prover.h"
#include "config_pc.hpp"
#include "utils.hpp"
#include "witness_stream.h"
#include <bits/stdc++.h>
#include "GKR.h"
#include "Poly_Commit.h"
#include "verifier.h"
using std::cerr;
using std::endl;
using std::max;
using std::min;
extern layeredCircuit C;
extern int Circuits;
extern int MAX_CHUNCK;
#define PHASE_ONE 1
#define PHASE_TWO 2

int naive = 0;
double stream_read_time = 0.0;
Comm pp_recursion;
extern int recursion;

vector<F> beta11,beta12,beta13,beta14;
vector<F> a;
    

void verify_sumcheck(F sum, proof_stream P ){
    
	for(int i = (P.polynomials[0].size() - (1<<P.c)); i < P.polynomials[0].size(); i++){
        sum -= P.polynomials[0][i];
    }
   
    for(int i = 0; i < P.polynomials[1].size(); i++){
        sum -= P.polynomials[1][i];
    }
    if(sum != F(0)){
        printf("Verification Error \n");
        exit(-1);
    }
}

void read_data_phase1(stream_descriptor &fp, int layer, vector<F> &V, vector<F> &H_add,vector<F> &H_mul, int &pos){
    
    clock_t s1,s2;
    s1 = clock();
    vector<F> V_t(C.circuit[layer].size,F_ZERO),H_add_t(C.circuit[layer].size,F_ZERO),H_mul_t(C.circuit[layer].size,F_ZERO);
    int _MAX_CHUNCK;
	if(MAX_CHUNCK == V.size()){
		_MAX_CHUNCK = MAX_CHUNCK;
	}else{
		_MAX_CHUNCK = V.size();
	}

	for(int i = 0; i < _MAX_CHUNCK/V_t.size(); i++){
    
		read_stream(fp,V_t,V_t.size());
        for(int j = 0; j < V_t.size(); j++){
            V[i*V_t.size() + j] = V_t[j];
        }
		if(a.size() == 0){
			read_H(layer+1,H_add_t,H_mul_t,V_t,beta12[pos],F(-1));
		}else{
			read_H(layer+1,H_add_t,H_mul_t,V_t,beta12[pos],beta14[pos]);

		}
        for(int j = 0; j < V_t.size(); j++){
            H_add[i*V_t.size() + j] = H_add_t[j];
            H_mul[i*V_t.size() + j] = H_mul_t[j];
         
            
        }
        pos++;
    }
    s2 = clock();
    stream_read_time += (double)(s2-s1)/(double)(CLOCKS_PER_SEC);
    
   return;
}

void read_data_phase2(stream_descriptor &fp, int layer, vector<F> &V, vector<F> &G_add,vector<F> &G_mul, vector<F> &beta21, vector<F> &beta22, int &pos, F Vr){
    vector<F> V_t(C.circuit[layer].size,F_ZERO),G_add_t(C.circuit[layer].size,F_ZERO),G_mul_t(C.circuit[layer].size,F_ZERO);
    clock_t s1,s2;
    s1 = clock();
    int _MAX_CHUNCK;
	if(MAX_CHUNCK == V.size()){
		_MAX_CHUNCK = MAX_CHUNCK;
	}else{
		_MAX_CHUNCK = V.size();
	}
    for(int i = 0; i < _MAX_CHUNCK/V_t.size(); i++){
       
        read_stream(fp,V_t,V_t.size());
        for(int j = 0; j < V_t.size(); j++){
            V[i*V_t.size() + j] = V_t[j];
        }
		if(a.size()==0){
			read_G(layer+1,G_add_t,G_mul_t,V_t,beta21,beta12[pos],beta22[pos],F(-1),Vr);
        
		}else{
			read_G(layer+1,G_add_t,G_mul_t,V_t,beta21,beta12[pos],beta22[pos],beta14[pos],Vr);
        	
		}
        for(int j = 0; j < V_t.size(); j++){
            G_add[i*V_t.size() + j] = G_add_t[j];
            G_mul[i*V_t.size() + j] = G_mul_t[j];
            
        }
        pos++;
    }
    s2 = clock();
    stream_read_time += (double)(s2-s1)/(double)(CLOCKS_PER_SEC);

}
struct proof _generate_2product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, F previous_r){
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	F rand = previous_r;
	vector<quadratic_poly> p;
	int rounds = int(log2(_v1.size()));
	
	F *v1 = (F *)malloc(_v1.size()*sizeof(F)/2);
	F *v2 = (F *)malloc(_v2.size()*sizeof(F)/2);


	for(int i = 0; i < rounds; i++){
		quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
	
    		quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2;
			int L = 1 << (rounds - 1-i);
			for(int j = 0; j < L; j++){
				if(i== 0){
					l1 = linear_poly(_v1[2*j+1] - _v1[2*j],_v1[2*j]);
					l2 = linear_poly(_v2[2*j+1] - _v2[2*j],_v2[2*j]);
					temp_poly = l1*l2;
					poly = poly + temp_poly;
					v1[j] = _v1[2*j] + rand*(_v1[2*j+1]-_v1[2*j]);
					v2[j] = _v2[2*j] + rand*(_v2[2*j+1]-_v2[2*j]);
					
				}else{
					l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
					l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
					temp_poly = l1*l2;
					poly = poly + temp_poly;
					v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
					v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
				
				}
				
			}
		
		r.push_back(rand);
		
		//vector<F> input;
		rand = mimc_hash(rand,poly.a);
		rand = mimc_hash(rand,poly.b);
		rand = mimc_hash(rand,poly.c);
		
		//input.push_back(rand);
		//input.push_back(poly.a);
		//input.push_back(poly.b);
		//input.push_back(poly.c);
		//vector<vector<F>> temp = mimc_multihash3(input);
		//Pr.w_hashes.push_back(temp);
		//rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		p.push_back(poly);
	}
	rand = mimc_hash(rand,v1[0]);
	rand = mimc_hash(rand,v2[0]);
	
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	Pr.q_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	return Pr;
 }



struct proof _generate_3product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, vector<F> &_v3,F previous_r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(_v1.size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
	F *v1 = _v1.data();
	F *v2 = _v2.data();
	//F *v3 = _v3.data();
	F *v3 = _v3.data();
	for(int i = 0; i < rounds; i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			
			int L = 1 << (rounds -1- i);
			for(int j = 0; j < L; j++){
				if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
					l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
					//q1 = quadratic_poly()
					F coef = v2[2*j+1] - v2[2*j];
					l2 = linear_poly(coef,v2[2*j]);
					coef = v3[2*j+1] - v3[2*j];
					l3 = linear_poly(coef,v3[2*j]);
					temp_poly = l1*l2*l3;
					poly = poly + temp_poly;

				}
				if(v1[2*j+1] == F(0) && v1[2*j] == F(0)){
					v1[j] = F(0);
				}else{
					F v = rand*(v1[2*j+1] - v1[2*j]);
					v1[j] = v1[2*j] + v;//(F(1)-rand)*v1[2*j] + rand*v1[2*j+1];
				}
				if(v2[2*j + 1] == F(0) && v2[2*j] == F(0)){
					v2[j] = F(0);
				}else{
					F v = rand*(v2[2*j+1] - v2[2*j]);
					v2[j] = v2[2*j] + v;
				}
				F v = rand*(v3[2*j+1] - v3[2*j]);
				v3[j] = v3[2*j] + v;

			}

		r.push_back(rand);
		vector<F> input;
		
		//input.push_back(rand);
		//input.push_back(poly.a);
		//input.push_back(poly.b);
		//input.push_back(poly.c);
		//input.push_back(poly.d);
		rand = mimc_hash(rand,poly.a);
		rand = mimc_hash(rand,poly.b);
		rand = mimc_hash(rand,poly.c);
		rand = mimc_hash(rand,poly.d);
		
		//vector<vector<F>> temp = mimc_multihash3(input);
		//Pr.w_hashes.push_back(temp);
		
		//rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		p.push_back(poly);
	}

	rand = mimc_hash(rand,v1[0]);
	rand = mimc_hash(rand,v2[0]);
	//rand = mimc_hash(rand,v3[0]);
	
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v3[0]);

	return Pr;
}


F reduce_proof_size(vector<F> poly, int c, F omega, F old_sum, F r,F previous_r){
	
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


		if(old_sum != F(-1) && old_sum != test_sum){
			printf("Error in verification\n");
			exit(-1);
		}
		
		F new_sum = F(0);
		
		vector<F> L = compute_lagrange_coeff(omega,r,1ULL<<(c+1));
		
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
		proof P1 = _generate_2product_sumcheck_proof(poly,aggr_poly,a[1]);
		KZG_open(poly,P1.randomness[0],pp_recursion);
		F L_eval = evaluate_vector(L, P1.randomness[0]);
		vector<F> beta;precompute_beta(P1.randomness[0],beta);
		a = generate_randomness(2,P1.randomness[0][P1.randomness[0].size()-1]);
		for(int i = 0; i < L.size(); i++){
			aggr_poly[i] = a[0]*pows[i] + a[1]*d[i];
		}
		commit(poly,pp_recursion);
		proof P2 = _generate_3product_sumcheck_proof(d_inv,aggr_poly,beta,a[1]);
		if(P2.c_poly[0].eval(F_ZERO) + P2.c_poly[0].eval(F_ONE) != a[0]*L_eval*A + a[1]){
			printf("Error\n");
		}
		KZG_open(d_inv,P2.randomness[0],pp_recursion);
		
		
		return new_sum;
	
}


proof generate_batch_2product_sumcheck_proof(vector<F> &v1, vector<F> &v2, vector<F> &v3,F previous_r){
	proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(v1.size()));
	vector<quadratic_poly> p;
	F rand = previous_r;
	vector<F> r;
	quadratic_poly temp_qpoly;
	quadratic_poly temp_poly;
	quadratic_poly total;
	quadratic_poly poly;
    
    for(int i = 0; i < rounds; i++){
		total = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2,l3;
    
		int L = 1 << (rounds -1- i);
	    
        for(int j = 0; j < L; j++){
				//printf("OK %d\n",k);			
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
				//q1 = quadratic_poly()
			l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
			l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
            poly = l1*l2+l3;
            total = total+ poly;

			v1[j] = v1[2*j] + rand*(v1[2*j+1] - v1[2*j]); 
			v2[j] = v2[2*j] + rand*(v2[2*j+1] - v2[2*j]); 
			v3[j] = v3[2*j] + rand*(v3[2*j+1] - v3[2*j]); 
								
			
		}
		r.push_back(rand);
		
        //rand.setByCSPRNG();

		rand = mimc_hash(rand,total.a);
		rand = mimc_hash(rand,total.b);
		rand = mimc_hash(rand,total.c);
		

		//rand = mimc_multihash(input);
		p.push_back(total);
	}
	
	Pr.q_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	Pr.vr.push_back(v1[0]);Pr.vr.push_back(v2[0]);
    Pr.vr.push_back(v3[0]);
	
	return Pr;
}

struct proof generate_2product_sumcheck_proof(vector<vector<F>> &v1, vector<F> &v2,vector<F> a, F previous_r){
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	F rand = previous_r;
	vector<quadratic_poly> p;
	int rounds = int(log2(v1[0].size()));
	
	

	for(int i = 0; i < rounds; i++){
		quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2;
			int L = 1 << (rounds - 1-i);
           for(int j = 0; j < L; j++){
				F coef1 = a[0]*(v1[0][2*j+1] - v1[0][2*j]),coef2 = a[0]*v1[0][2*j];
                for(int k = 1; k < a.size(); k++){
                    coef1 += a[k]*(v1[k][2*j+1] - v1[k][2*j]);
                    coef2 += a[k]*(v1[k][2*j]);

                }
				l1 = linear_poly(coef1,coef2);
				l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
					temp_poly = l1*l2;
					poly = poly + temp_poly;
                for(int k = 0; k <  a.size(); k++){
                    
					v1[k][j] = v1[k][2*j] + rand*(v1[k][2*j+1]-v1[k][2*j]);
				
                }
					v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
				
			}
		
        
		r.push_back(rand);
		
		rand = mimc_hash(rand,poly.a);
		rand = mimc_hash(rand,poly.b);
		rand = mimc_hash(rand,poly.c);
		p.push_back(poly);
	}
	rand = mimc_hash(rand,v1[0][0]);
	rand = mimc_hash(rand,v2[0]);
	
    for(int i = 0 ;i < a.size(); i++){
        Pr.vr.push_back(v1[i][0]);
	
    }
	Pr.vr.push_back(v2[0]);
	Pr.q_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	return Pr;
 }


proof_stream generate_2product_sumcheck_proof_stream_beta_local(stream_descriptor fp1, 
                vector<F> &beta21, vector<F> &beta22 , F Vr , size_t size, int PHASE, F previous_r){

    proof_stream P;
    int pos = 0;

    vector<F> v1(size),v2(size),v3(size);
	if(PHASE == PHASE_ONE){
        read_data_phase1(fp1,fp1.layer,v1,v3,v2,pos);
    }else{
        read_data_phase2(fp1,fp1.layer,v1,v3,v2,beta21,beta22,pos,Vr);
        F temp;
        /*
		for(int i = 0; i < v2.size(); i++){
            v2[i] = v2[i]*Vr + v3[i];
            v3[i] = v3[i]*Vr;
        }*/
		

    }

	P.P.push_back(generate_batch_2product_sumcheck_proof(v1,v2,v3,previous_r));
    P.vr.push_back(P.P[0].vr[0]);
    P.vr.push_back(P.P[0].vr[1]);
	P.vr.push_back(P.P[0].vr[2]);
	P.size = size;
    return P;   
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

void verify_2prod(proof P, F sum){
	for(int i = 0; i < P.randomness[0].size(); i++){
		if(P.q_poly[i].eval(F_ZERO) +P.q_poly[i].eval(F_ONE) != sum){
            printf("Error in V %d\n", i);
            exit(-1);
        }
		sum = P.q_poly[i].eval(P.randomness[0][i]);
	}
}

void _verify_proof(proof_stream P, F sum){
	if(MAX_CHUNCK >= P.size){
		if(P.P[0].q_poly[0].eval(F_ZERO) +P.P[0].q_poly[0].eval(F_ONE) != sum){
            printf("Error in V\n");
            exit(-1);
        }
		verify_2prod( P.P[0], sum);
		return;
	}
	
	int total_c = (int)log2(P.size/MAX_CHUNCK);
    int c = 4;
	if(c >= total_c){
        c = total_c;
    }else{
		c = (int)log2(log2(P.size/MAX_CHUNCK)) + 1;
	}
	verify_sumcheck(sum,P);

	vector<F> L = compute_lagrange_coeff(getRootOfUnit(c),P.randomness[0],1ULL<<(c));
	sum = F(0);
	F sum1 = F(0);
	int idx = 0;
	for(int i = 0; i < 1<<c; i++){
		for(int j = i+1; j < 1<<c; j++){
			sum += L[i]*L[j]*P.polynomials[0][idx];
			idx++;
		}
	}
	for(int i = 0; i < 1<<c; i++){
		sum += L[i]*L[i]*P.polynomials[0][idx];
		sum += L[i]*P.polynomials[1][i];
		idx++;
	}
	
	int new_c = total_c -c;
	if(new_c != 0){
		if(new_c <= 4){
		    L = compute_lagrange_coeff(getRootOfUnit(new_c),P.randomness[1],1ULL<<(new_c));
			 for(int i = (P.polynomials[2].size() - (1<<new_c)); i < P.polynomials[2].size(); i++){
				sum -= P.polynomials[2][i];
			}
		
			for(int i = 0; i < P.polynomials[3].size(); i++){
				sum -= P.polynomials[3][i];
			}
			if(sum != F(0)){
				printf("Verification Error \n");
				exit(-1);
			}
			int idx = 0;
			for(int i = 0; i < 1<<new_c; i++){
				for(int j = i+1; j < 1<<new_c; j++){
					sum += L[i]*L[j]*P.polynomials[2][idx];
					idx++;
				}
			}
			for(int i = 0; i < 1<<new_c; i++){
				sum += L[i]*L[i]*P.polynomials[2][idx];
				sum += L[i]*P.polynomials[3][i];
				idx++;
			}

		}else{
			
			L = compute_lagrange_coeff(getRootOfUnit(new_c + 1),P.randomness[1],1ULL<<(new_c+1));
			vector<F> L2 = compute_lagrange_coeff(getRootOfUnit(new_c ),P.randomness[1],1ULL<<(new_c));
			
			
			
			for(int i = 0; i < P.polynomials[2].size()/2; i++){
				sum -= P.polynomials[2][2*i];
				sum -= P.polynomials[3][i];
			}

			if(sum != 0){
				printf("Error in verification phase\n");
			}
			
			
			
			
			F sum1 = F_ZERO;
			for(int i = 0; i < L.size(); i++){
				sum += L[i]*P.polynomials[2][i];
				sum1 += L[i]*P.polynomials[2][i];
			}
			
			for(int i = 0; i < L2.size(); i++){
				sum += L2[i]*P.polynomials[3][i];
				//sum1 += L2[i]*P.polynomials[3][i];
			}

			


		}
	}

	verify_2prod( P.P[0], sum);
	verify_2prod(P.P[1],P._a[0]*P.P[0].vr[0] + P._a[1]*P.P[0].vr[1] + P._a[2]*P.P[0].vr[2]);
			
}

proof_stream generate_2product_sumcheck_proof_stream_beta_naive(stream_descriptor fp1, vector<F> &beta21, vector<F> &beta22 , F Vr , size_t size,
	 int PHASE, F previous_r){
	
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
					if(PHASE == PHASE_ONE){
				
					    read_data_phase1(fp1,fp1.layer,v1,v3,v2,pos);
			
        		    }else{
                		read_data_phase2(fp1,fp1.layer,v1,v3,v2,beta21,beta22,pos,Vr);
                		F temp;
                		/*
						for(int l = 0; l < v2.size(); l++){
                    		v2[l] = v2[l]*Vr + v3[l];
                    		v3[l] = v3[l]*Vr;
                		}*/
						
					}


					for(int k = 0; k < i; k++){
						for(int l = 0; l < MAX_CHUNCK/(1ULL<<(k+1)); l++){
							v1[l] = v1[2*l] + rand_v[k]*(v1[2*l+1]-v1[2*l]);
							v2[l] = v2[2*l] + rand_v[k]*(v2[2*l+1]-v2[2*l]);
							v3[l] = v3[2*l] + rand_v[k]*(v3[2*l+1]-v3[2*l]);
						}
					}
					
					for(int k = 0; k < MAX_CHUNCK/(1<<(i+1)); k++){
						l1 = linear_poly(v1[2*k+1] - v1[2*k],v1[2*k]);
						l2 = linear_poly(v2[2*k+1] - v2[2*k],v2[2*k]);
						l3 = linear_poly(v3[2*k+1] - v3[2*k],v3[2*k]);
						temp_poly = l1*l2 + l3;
						poly = poly + temp_poly;
					}				
				}
				reset_stream(fp1);
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
			if(PHASE == PHASE_ONE){
				
			    read_data_phase1(fp1,fp1.layer,v1,v3,v2,pos);
			
            }else{
                read_data_phase2(fp1,fp1.layer,v1,v3,v2,beta21,beta22,pos,Vr);
                F temp;
                /*
				for(int l = 0; l < v2.size(); l++){
                    v2[l] = v2[l]*Vr + v3[l];
                    v3[l] = v3[l]*Vr;
                }*/
				

            }

			for(int k = 0; k < i; k++){
				for(int l = 0; l < MAX_CHUNCK/(1ULL<<(k+1)); l++){
					v1[l] = v1[2*l] + rand_v[k]*(v1[2*l+1]-v1[2*l]);
					v2[l] = v2[2*l] + rand_v[k]*(v2[2*l+1]-v2[2*l]);
					v3[l] = v3[2*l] + rand_v[k]*(v3[2*l+1]-v3[2*l]);
				}
			}
			for(int k = 0; k < MAX_CHUNCK/(1ULL<<(i)); k++){
				fv1[counter] = v1[k];
				fv2[counter] = v2[k];
				fv3[counter] = v3[k];
				counter++;
			}
		}
		v1 = fv1;
		v2 = fv2;
		v3 = fv3;
		for(; i < rounds; i++){
			quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			
			int L = 1 << (rounds - 1-i);
			for(int j = 0; j < L; j++){
				l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
				l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
				l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
				temp_poly = l1*l2;
				poly = poly + temp_poly;
				v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
				v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);						
				v3[j] = v3[2*j] + rand*(v3[2*j+1]-v3[2*j]);						
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

// NloglogN sumcheck
proof_stream _generate_2product_sumcheck_proof_stream_beta(stream_descriptor fp1, vector<F> &beta21, vector<F> &beta22 , F Vr , size_t size,
	 int PHASE, F previous_r){
	
    
    if(MAX_CHUNCK >= size){
		return generate_2product_sumcheck_proof_stream_beta_local(fp1, 
                beta21, beta22 , Vr , size, PHASE,  previous_r);
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

	vector<F> v1(MAX_CHUNCK),v2(MAX_CHUNCK),v3(MAX_CHUNCK);
	vector<F> temp_v1(degree),temp_v2(degree),temp_v3(degree);
	vector<F> poly(2*degree),l1(2*degree),l2(2*degree),poly_small(degree);

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
    
	
    
    
    int pos;
	
	for(i = 0; i < 2; i++){
	
	    pos = 0;
	    reset_stream(fp1);
		
        for(int j = 0; j < poly.size(); j++){
			poly[j] = F_ZERO;
		}
        for(int j = 0; j < poly_small.size(); j++){
            poly_small[j] = F_ZERO;
        }
        
        for(int j = 0; j < size/MAX_CHUNCK; j++){
            if(PHASE == PHASE_ONE){
				
			    read_data_phase1(fp1,fp1.layer,v1,v3,v2,pos);
			
            }else{
                read_data_phase2(fp1,fp1.layer,v1,v3,v2,beta21,beta22,pos,Vr);
                F temp;
                /*
				for(int l = 0; l < v2.size(); l++){
                    v2[l] = v2[l]*Vr + v3[l];
                    v3[l] = v3[l]*Vr;
                }*/
				

            }

            
            //read_stream(fp1,v1,MAX_CHUNCK);
			//compute_temp_beta(beta1,beta2,a,v2,j);
			
			for(int k = 0; k < i; k++){
				for(int l = 0; l < MAX_CHUNCK/(1ULL<<(c*(k+1))); l++){
					v1[l] = Lv[k][0]*v1[Lv[k].size()*l];
					v2[l] = Lv[k][0]*v2[Lv[k].size()*l];
					v3[l] = Lv[k][0]*v3[Lv[k].size()*l];
                    for(int h = 1; h < Lv[k].size(); h++){
						v1[l] += Lv[k][h]*v1[degree*l + h];
						v2[l] += Lv[k][h]*v2[degree*l + h];
						v3[l] += Lv[k][h]*v3[degree*l + h];
					}
				}
			}
			int current_size = MAX_CHUNCK/(1<<(c*i));
			if(new_c == 0){
				offset = current_size/degree;
				poly_degree = degree; 
			}else{
				offset = current_size/new_degree;
				//printf("Offset : %d\n",offset);
				
				poly_degree = new_degree; 
            
			}
			
			//printf("%d,%d \n",offset,poly_degree);
			for(int k = 0; k < offset; k++){
				for(int l = 0; l < poly_degree; l++){
					temp_v1[l] = v1[poly_degree*k + l];
					temp_v2[l] = v2[poly_degree*k + l];
					temp_v3[l] = v3[poly_degree*k + l];
					
					l1[l + poly_degree] = F_ZERO;
					l2[l+poly_degree] = F_ZERO;
				}

                for(int l = 0; l <  poly_degree; l++){
                    poly_small[l] += temp_v3[l];
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
                   
				   
					
					//fft(temp_v1,new_c,true);
					//fft(temp_v2,new_c,true);
					
				   	my_fft(temp_v1,w,rev,ilen,true);
					my_fft(temp_v2,w,rev,ilen,true);

					for(int l = 0; l < poly_degree; l++){
						l1[l] = temp_v1[l];
						l2[l] = temp_v2[l];
					}
					for(int l = poly_degree; l < 2*poly_degree; l++){
						l1[l] = F_ZERO;
						l2[l] = F_ZERO;
					
					}
					
					//fft(l1,new_c+1,false);
					//fft(l2,new_c+1,false);
					
					my_fft(l1,w_prod,rev_prod,F(1),false);
					my_fft(l2,w_prod,rev_prod,F(1),false);
					for(int l = 0; l < 2*poly_degree; l++){
						poly[l] += l1[l]*l2[l];
					}
				}
				
			}
		}
		
		
		poly_proofs.push_back(poly);
		poly_proofs.push_back(poly_small);
		F r;r.setByCSPRNG();
		rand.push_back(r);
		
		
			
		if(!new_c){

			Lv.push_back(compute_lagrange_coeff(omega,r,degree));
		}else{
		
			F new_omega = getRootOfUnit((int)log2(new_degree));
			
			//printf("%d\n", L.size());
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
			temp_v3.resize(new_degree);
			poly.resize(2*new_degree);
			l1.resize(2*new_degree);
			l2.resize(2*new_degree);
			poly_small.resize(new_degree);
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
    
    
    
    reset_stream(fp1);
		
    // SOME CHANGES
    int final_size = 1;
    for(int i = 0; i < Lv.size(); i++){
       
        final_size *= Lv[i].size();
    }
    final_size = size/final_size;
    
    printf("Iterations : %d \n", i);
	vector<F> final_v1(final_size,F_ZERO),final_v2(final_size,F_ZERO),final_v3(final_size,F_ZERO);
	
    
    counter = 0;
    vector<F> conv;
	compute_convolution(Lv,conv);
    
	pos = 0;
    vector<F> V1,V2;
	for(int j = 0; j < size/MAX_CHUNCK; j++){
		int final_size;
		if(PHASE == PHASE_ONE){
            read_data_phase1(fp1,fp1.layer,v1,v3,v2,pos);
        }else{
            read_data_phase2(fp1,fp1.layer,v1,v3,v2,beta21,beta22,pos,Vr);
                F temp;
                /*
				for(int l = 0;l  < v2.size(); l++){
                    v2[l] = v2[l]*Vr + v3[l];
                    v3[l] = v3[l]*Vr;
                }*/
				

        }
        
        int _c = 0;
        for(int k = 0; k < MAX_CHUNCK/conv.size(); k++){
            for(int l = 0; l < conv.size(); l++){
                final_v1[counter] += conv[l]*v1[k*conv.size() + l];
				
				final_v2[counter] += conv[l]*v2[k*conv.size() + l];
                final_v3[counter] += conv[l]*v3[k*conv.size() + l];
			
            }
            counter++;
        }
        
	}
	
	
    proof P1 = generate_batch_2product_sumcheck_proof(final_v1,final_v2,final_v3,rand[rand.size()-1]);
   	vector<F>().swap(final_v1);
	vector<F>().swap(final_v2);
	vector<F>().swap(final_v3);
	
	P.P.push_back(P1);
   
	reset_stream(fp1);
	
   int conv_size = conv.size();
	
	vector<F> _beta;
    
    precompute_beta(P1.randomness[0],_beta);
    
    
    vector<F> partial_eval1(conv_size,F(0)),partial_eval2(conv_size,F(0)),partial_eval3(conv_size,F(0));
	counter = 0;
	pos = 0;
    for(int i = 0; i < size/MAX_CHUNCK; i++){
		if(PHASE == PHASE_ONE){
            read_data_phase1(fp1,fp1.layer,v1,v3,v2,pos);
        }else{
            read_data_phase2(fp1,fp1.layer,v1,v3,v2,beta21,beta22,pos,Vr);
            /*
			for(int l = 0; l < v2.size(); l++){
                v2[l] = v2[l]*Vr + v3[l];
                v3[l] = v3[l]*Vr;
            }*/
			

        }
        
        for(int j = 0; j < MAX_CHUNCK; j+=conv_size){
			for(int k = 0; k < conv_size; k++){
				partial_eval1[k] += _beta[counter]*v1[j + k];
				partial_eval2[k] += _beta[counter]*v2[j + k];
                partial_eval3[k] += _beta[counter]*v3[j + k];
			}
			counter++;
		}
	}
    
    _beta.clear();
	vector<F> _a = generate_randomness(3,P1.randomness[0][P1.randomness[0].size()-1]);

    P._a = _a;
    
    vector<vector<F>> partial_eval;partial_eval.push_back(partial_eval1);
    partial_eval.push_back(partial_eval2);partial_eval.push_back(partial_eval3);
    proof P2 = generate_2product_sumcheck_proof(partial_eval,conv,_a,_a[2]);

    vector<F>().swap(partial_eval1);
	vector<F>().swap(partial_eval2);
	vector<F>().swap(partial_eval3);
	
	for(int i = 0; i < partial_eval.size(); i++){
		vector<F>().swap(partial_eval[i]);
	}
    //proof P2 = _generate_3product_sumcheck_proof(conv,partial_eval1,beta,rand[rand.size()-1]);
	P.P.push_back(P2);
    if(_a[0]*P1.vr[0] + _a[1]*P1.vr[1] + _a[2]*P1.vr[2] != P2.q_poly[0].eval(F(0))+P2.q_poly[0].eval(F(1))){
		printf(">>Error \n");
		exit(-1);
	}
    
    P.vr.push_back( P2.vr[0]);
    P.vr.push_back(P2.vr[1]);
    P.vr.push_back(P2.vr[2]);
	
    return P;

}




proof_stream generate_2product_sumcheck_proof_stream_beta(stream_descriptor fp1, 
                vector<F> &beta21, vector<F> &beta22 , F Vr , size_t size, int PHASE, F previous_r){
	
    
    if(MAX_CHUNCK >= size){
        generate_2product_sumcheck_proof_stream_beta_local(fp1,  
                beta21, beta22 , Vr , size, PHASE,  previous_r);
	}
    int c = 4;
	if(1<<c > size/MAX_CHUNCK){
        c = (int)log2(size/MAX_CHUNCK);
    }
    printf("Degree : %d\n",1<<c);
    int new_c = 0,offset,poly_degree,new_degree;
	F omega = getRootOfUnit(c);
	int degree = 1<<c;
    proof_stream P;
    F len = F(1<<c);
    F ilen;

    F::inv(ilen, len);

	vector<F> v1(MAX_CHUNCK),v2(MAX_CHUNCK),v3(MAX_CHUNCK);
	vector<F> temp_v1(degree),temp_v2(degree),temp_v3(degree);
	vector<F> poly(2*degree),l1(2*degree),l2(2*degree),poly_small(degree);
    if(c <= 4){
        poly.clear();
        poly.resize(degree*(degree+1)/2);
    }
    vector<vector<F>> poly_proofs;
	vector<vector<F>> Lv;
	vector<F> rand;
    vector<F> v;
	

	vector<u32> rev_prod(2*degree),rev(degree);
    vector<F> w_prod(2*degree);
	vector<F> w(degree);
	rev_prod[0] = 0;
    
	    
	
	prepare_fft_aux(w,rev,w_prod,rev_prod,2*degree);
	

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
    
    
    
    int pos;
    while(true){
        pos = 0;
	    counter = 0;
		reset_stream(fp1);
		
        for(int j = 0; j < poly.size(); j++){
			poly[j] = F_ZERO;
		}
        for(int j = 0; j < poly_small.size(); j++){
            poly_small[j] = F_ZERO;
        }
        
        for(int j = 0; j < size/MAX_CHUNCK; j++){
            if(PHASE == PHASE_ONE){
                read_data_phase1(fp1,fp1.layer,v1,v3,v2,pos);
         
            }else{
                read_data_phase2(fp1,fp1.layer,v1,v3,v2,beta21,beta22,pos,Vr);
                F temp;
                /*
				for(int l = 0; l < v2.size(); l++){
                    v2[l] = v2[l]*Vr + v3[l];
                    v3[l] = v3[l]*Vr;
                }*/
				

            }

            
            //read_stream(fp1,v1,MAX_CHUNCK);
			//compute_temp_beta(beta1,beta2,a,v2,j);
			
			for(int k = 0; k < i; k++){
				for(int l = 0; l < MAX_CHUNCK/(1ULL<<(c*(k+1))); l++){
					v1[l] = Lv[k][0]*v1[Lv[k].size()*l];
					v2[l] = Lv[k][0]*v2[Lv[k].size()*l];
					v3[l] = Lv[k][0]*v3[Lv[k].size()*l];
                    for(int h = 1; h < Lv[k].size(); h++){
						v1[l] += Lv[k][h]*v1[degree*l + h];
						v2[l] += Lv[k][h]*v2[degree*l + h];
						v3[l] += Lv[k][h]*v3[degree*l + h];
					}
				}
			}
			int current_size = MAX_CHUNCK/(1<<(c*i));
			if(new_c == 0){
				offset = current_size/degree;
				poly_degree = degree; 
			}else{
				offset = 1;
				poly_degree = new_degree; 
                //printf("%d\n",current_size);
            }
			//printf("%d,%d \n",offset,poly_degree);
			for(int k = 0; k < offset; k++){
				for(int l = 0; l < poly_degree; l++){
					temp_v1[l] = v1[poly_degree*k + l];
					temp_v2[l] = v2[poly_degree*k + l];
					temp_v3[l] = v3[poly_degree*k + l];
					l1[l + poly_degree] = 0;
					l2[l+poly_degree] = 0;
				}
                for(int l = 0; l <  poly_degree; l++){
                    poly_small[l] += temp_v3[l];
                }
				if(c <= 4 || (new_c <= 4 && new_c != 0)){
                    
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
		poly_proofs.push_back(poly_small);
		F r;r.setByCSPRNG();
		rand.push_back(r);
		if(!new_c){
			Lv.push_back(compute_lagrange_coeff(omega,r,degree));
		}else{
			F new_omega = getRootOfUnit((int)log2(new_degree));
            Lv.push_back(compute_lagrange_coeff(new_omega,r,new_degree));		
		}
		i++;
		
		
       
		if(MAX_CHUNCK/(1<<(c*i)) == 1){
			printf("OK2 \n");
			break;
		}
		if((size/(1<<(c*i))) <= MAX_CHUNCK){
			//printf("OK3 \n");
			break;
		}
        if(MAX_CHUNCK/(1<<(c*i+c)) < 1){
			new_c = (int)log2(MAX_CHUNCK/(1<<(c*i)));
			new_degree = 1<<new_c;
			printf("OK %d,%d\n", MAX_CHUNCK,(1<<(c*i+c)));
            printf("%d, %d\n", new_c,i);
		}
	}


    
    
    P.polynomials = poly_proofs;
    P.c = c;
    P.randomness = rand;
    
    
    
    reset_stream(fp1);
	
    // SOME CHANGES
    int final_size = 1;
    for(int i = 0; i < Lv.size(); i++){
       
        final_size *= Lv[i].size();
    }
    final_size = size/final_size;
    
    printf("Iterations : %d \n", i);
	vector<F> final_v1(final_size,F_ZERO),final_v2(final_size,F_ZERO),final_v3(final_size,F_ZERO);
	
    
    counter = 0;
    vector<F> conv;
	compute_convolution(Lv,conv);
    
    pos = 0;
    vector<F> V1,V2;
	for(int j = 0; j < size/MAX_CHUNCK; j++){
		int final_size;
		if(PHASE == PHASE_ONE){
            read_data_phase1(fp1,fp1.layer,v1,v3,v2,pos);
        }else{
            read_data_phase2(fp1,fp1.layer,v1,v3,v2,beta21,beta22,pos,Vr);
                F temp;
                /*
				for(int l = 0;l  < v2.size(); l++){
                    v2[l] = v2[l]*Vr + v3[l];
                    v3[l] = v3[l]*Vr;
                }*/
				

        }
        
        int _c = 0;
        for(int k = 0; k < MAX_CHUNCK/conv.size(); k++){
            for(int l = 0; l < conv.size(); l++){
                final_v1[counter] += conv[l]*v1[k*conv.size() + l];
			    final_v2[counter] += conv[l]*v2[k*conv.size() + l];
                final_v3[counter] += conv[l]*v3[k*conv.size() + l];
            }
            counter++;
        }
        
	}
    
    
   
    proof P1 = generate_batch_2product_sumcheck_proof(final_v1,final_v2,final_v3,rand[rand.size()-1]);
   P.P.push_back(P1);
   
	reset_stream(fp1);
	
   int conv_size = conv.size();
	
	vector<F> _beta;
    
    precompute_beta(P1.randomness[0],_beta);
    
    
    vector<F> partial_eval1(conv_size,F(0)),partial_eval2(conv_size,F(0)),partial_eval3(conv_size,F(0));
	counter = 0;
	pos = 0;
    for(int i = 0; i < size/MAX_CHUNCK; i++){
		if(PHASE == PHASE_ONE){
            read_data_phase1(fp1,fp1.layer,v1,v3,v2,pos);
        }else{
            read_data_phase2(fp1,fp1.layer,v1,v3,v2,beta21,beta22,pos,Vr);
            /*
			for(int l = 0; l < v2.size(); l++){
                v2[l] = v2[l]*Vr + v3[l];
                v3[l] = v3[l]*Vr;
            }*/
			

        }
        
        for(int j = 0; j < MAX_CHUNCK; j+=conv_size){
			for(int k = 0; k < conv_size; k++){
				partial_eval1[k] += _beta[counter]*v1[j + k];
				partial_eval2[k] += _beta[counter]*v2[j + k];
                partial_eval3[k] += _beta[counter]*v3[j + k];
			}
			counter++;
		}
	}
    
    _beta.clear();
	vector<F> _a = generate_randomness(3,P1.randomness[0][P1.randomness[0].size()-1]);

    P._a = _a;
    
    vector<vector<F>> partial_eval;partial_eval.push_back(partial_eval1);
    partial_eval.push_back(partial_eval2);partial_eval.push_back(partial_eval3);
    proof P2 = generate_2product_sumcheck_proof(partial_eval,conv,_a,_a[2]);

     
    //proof P2 = _generate_3product_sumcheck_proof(conv,partial_eval1,beta,rand[rand.size()-1]);
	P.P.push_back(P2);
    if(_a[0]*P1.vr[0] + _a[1]*P1.vr[1] + _a[2]*P1.vr[2] != P2.q_poly[0].eval(F(0))+P2.q_poly[0].eval(F(1))){
		printf(">>Error \n");
		exit(-1);
	}
    
    P.vr.push_back( P2.vr[0]);
    P.vr.push_back(P2.vr[1]);
    P.vr.push_back(P2.vr[2]);
	
    return P;

}




void prove_circuit(F commitment){
	printf("Depth : %d\n",C.size);
    
	
	stream_descriptor fp;fp.name = "circuit";fp.pos = 0;fp.layer = C.size-1;
    fp.size = Circuits*C.circuit[fp.layer].size;
   
    vector<F> r1_prev = generate_randomness((int)log2(fp.size),commitment);
    vector<F> r2_prev;
	
	printf("Out size : %d\n", fp.size);
    F sum = evaluate_vector_stream(fp,r1_prev,fp.size);
	
	vector<F> V(MAX_CHUNCK);
    vector<F> H_add(MAX_CHUNCK),G_add(MAX_CHUNCK),H_mul(MAX_CHUNCK),G_mul(MAX_CHUNCK);
    vector<F> beta21,beta22,beta23;
    // Start sumchecks
	for(int i = C.size-1; i >= 1; i--){
        printf("Layer : %d \n",i);
        int pos = 0;
        F sum1 = F_ZERO;
        beta11.clear();beta12.clear();beta13.clear();beta14.clear();
        beta21.clear();beta22.clear();beta23.clear();
        vector<F> r2;
        vector<F> r11,r12,r13,r14;
        vector<F> r21,r22,r23;
        for(int j = 0; j < C.circuit[i].bitLength; j++){
            r11.push_back(r1_prev[j]);
        }
        
        for(int j = (C.circuit[i].bitLength); j < r1_prev.size(); j++){
            r12.push_back(r1_prev[j]);
        }
		if(r2_prev.size() != 0){
			 for(int j = 0; j < C.circuit[i].bitLength; j++){
            	r13.push_back(r2_prev[j]);
			}
			
			for(int j = (C.circuit[i].bitLength); j < r2_prev.size(); j++){
				r14.push_back(r2_prev[j]);
			}
			precompute_beta(r13, beta13);
        	precompute_beta(r14, beta14);
        
		}
        
        precompute_beta(r11, beta11);
        precompute_beta(r12, beta12);
        
        vector<F> HA,HM,Vt;
        fp.pos = 0;fp.size = Circuits*C.circuit[i-1].size;fp.layer = i-1;
        proof_stream P1;
		if(naive){
			P1 =  generate_2product_sumcheck_proof_stream_beta_naive(fp, beta21, beta22 ,F_ZERO, fp.size, PHASE_ONE, r1_prev[r1_prev.size()-1]);
        
		}else{
			P1 =  _generate_2product_sumcheck_proof_stream_beta(fp, beta21, beta22 ,F_ZERO, fp.size, PHASE_ONE, r1_prev[r1_prev.size()-1]);
		
		
			verify_stream_2product_sumcheck(P1,sum);

		}
        printf("Phase 1 finished\n");
		
		//_verify_proof(P1, sum);
		
		/*
		if(P1.P.size() > 1){
            verify_sumcheck(sum,P1);
        }else{
            if(P1.P[0].q_poly[0].eval(F_ZERO) +P1.P[0].q_poly[0].eval(F_ONE) != sum){
                printf("Error in V\n");
                exit(-1);
            }
        }*/
		
		
		/*
      
        for(int j = 0; j < fp.size/MAX_CHUNCK; j++){
            read_data_phase1(fp,fp.layer,V,H_add,H_mul,beta11,beta12,pos);
            for(int k = 0; k < V.size(); k++){
                sum1 += V[k]*H_mul[k] + H_add[k];
            }
            Vt.insert(Vt.end(),V.begin(),V.end());
            HA.insert(HA.end(),H_add.begin(),H_add.end());
            HM.insert(HM.end(),H_mul.begin(),H_mul.end());
        
        }
        if(sum1 != sum){
            printf("Error GKR phase 1 %d\n",i);
            exit(-1);
        }
        
        exit(-1);
          
        */
      
        fp.pos = 0;
        if(P1.P.size() > 1){
            r2 = P1.P[1].randomness[0];
            r2.insert(r2.end(),P1.P[0].randomness[0].begin(),P1.P[0].randomness[0].end());
        }else{
			r2 = P1.P[0].randomness[0];
        }
        
        //r2 = generate_randomness((int)log2(Circuits*C.circuit[i-1].size),r1[r1.size()-1]);
        for(int j = 0; j < C.circuit[i-1].bitLength; j++){
            r21.push_back(r2[j]);
        }
        for(int j = C.circuit[i-1].bitLength; j < r2.size(); j++){
            r22.push_back(r2[j]);
        }
        
        precompute_beta(r21,beta21);
        precompute_beta(r22,beta22);
        
		
        F V_sum = P1.vr[0];
        //V_sum = evaluate_vector(Vt,r2);
        //sum = V_sum*evaluate_vector(HM,r2)+evaluate_vector(HA,r2);
        
        sum = V_sum*P1.vr[1]+P1.vr[2];
        
        sum1 = F_ZERO;
        vector<F> Vt2,HA2;
        pos = 0;
        proof_stream P2;
		if(naive){
			P2 = generate_2product_sumcheck_proof_stream_beta_naive(fp,  beta21, beta22 , V_sum,fp.size, PHASE_TWO, r1_prev[r1_prev.size()-1]);
		}else{
			P2 =  _generate_2product_sumcheck_proof_stream_beta(fp,  beta21, beta22 , V_sum,fp.size, PHASE_TWO, r1_prev[r1_prev.size()-1]);
			verify_stream_2product_sumcheck(P2,sum);
		}

		/*
		if(P2.P.size() > 1){
        
		    verify_sumcheck(sum,P2);
        }else{
            if(P2.P[0].q_poly[0].eval(F_ZERO) +P2.P[0].q_poly[0].eval(F_ONE) != sum){
                printf("Error in V\n");
                exit(-1);
            }
        }*/
		
        /*
        for(int j = 0; j < fp.size/MAX_CHUNCK; j++){
            
            read_data_phase2(fp,fp.layer,V,H_add,H_mul,beta21,beta11,beta22,beta12,pos);
            for(int k = 0; k < V.size(); k++){
                sum1 += (V_sum*H_mul[k]+H_add[k])*V[k]+ V_sum*H_add[k];
            }
            Vt2.insert(Vt2.end(),V.begin(),V.end());
            HA2.insert(HA2.end(),H_mul.begin(),H_mul.end());
        }
      
        if(sum1 != sum){
            printf("Error GKR phase 2, %d\n",i);
            exit(-1);
        }
        */
        
		r1_prev = r2;
		
		if(P2.P.size() > 1){
            r2 = P2.P[1].randomness[0];
            r2.insert(r2.end(),P2.P[0].randomness[0].begin(),P2.P[0].randomness[0].end());
        }else{
            r2 = P2.P[0].randomness[0];
        }
        r2_prev = r2;
        a = generate_randomness(2,r2[r2.size()-1]);
		sum = a[0]*V_sum + a[1]*P2.vr[0];
		 printf("Phase 2 finished\n");
		
    }
    printf("Stream Read : %lf \n",stream_read_time);

}
