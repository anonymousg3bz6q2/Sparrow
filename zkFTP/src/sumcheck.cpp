#include "config_pc.hpp"
#include "GKR.h"
#include "mimc.h"
#include "utils.hpp"
#include "sumcheck.h"
#include <chrono>
#include "quantization.h"
#include "pol_verifier.h"

using namespace std::chrono;

extern int threads;
extern int bin_size;
extern double range_proof_verification_time;
extern int range_proof_size;
extern size_t MAX_CHUNCK;
extern int _WRITE;
extern string dir;
 

vector<vector<F>> prepare_matrixes(vector<vector<F>> M1, vector<vector<F>> M2, vector<F> r1, vector<F> r2){
	vector<vector<F>> V(2);
	vector<vector<F>> M = _transpose(M1);

	V[0] = (prepare_matrix(M,r1));

	M = _transpose(M2);
	
	V[1] = (prepare_matrix(M,r2));
	
	return V;

}


struct proof generate_3product_sumcheck_proof_naive(vector<F> v1, vector<F> v2, vector<F> v3, vector<F> r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())),F(0));
	vector<cubic_poly> p;
	for(int i = 0; i < r.size(); i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2,l3;
		
		int L = 1 << (r.size() -1- i);
		for(int j = 0; j < L; j++){
			if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
				l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
				//q1 = quadratic_poly()
				l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
				l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
				temp_poly = l1*l2*l3;
				poly = poly + temp_poly;

			}
			v1[j] = (F(1)-r[i])*v1[2*j] + r[i]*v1[2*j+1];
			if(v2[2*j] == F(0) && v2[2*j+1] == F(0)){
				v2[j] = F(0);
				v3[j] = F(1);
			}else{

				v2[j] = v2[2*j] + r[i]*(v2[2*j+1]-v2[2*j]);
				v3[j] = v3[2*j] + r[i]*(v3[2*j+1]-v3[2*j]);	

			}
		}
		p.push_back(poly);
	}
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v1[0]);

	return Pr;
}

void _generate_3product_sumcheck_proof_folded(F* v1, F* v2, F* v3,F* new_v1,F* new_v2,F* new_v3, cubic_poly &poly,F sum, F rand, int idx, int L ){
	
 	int size = L/threads;
	int pos = idx*size;
	linear_poly l1,l2,l3;
	
	cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
	for(int j = pos; j < pos+size; j++){
		if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			//q1 = quadratic_poly()
			F coef = v2[2*j+1] - v2[2*j];
			l2 = linear_poly(coef,v2[2*j]);
			l3 = linear_poly(-coef,sum - v2[2*j]);
			//l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
			temp_poly = l1*l2*l3;
			poly = poly + temp_poly;
		}
		new_v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
		new_v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
		new_v3[j] = sum - new_v2[j];
	}
}


struct proof generate_3product_sumcheck_proof_folded(vector<F> &_v1, vector<F> &_v2, vector<F> &_v3,F sum,F previous_r){
	
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(_v1.size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;

	// Convert to data arrays
	F *v1 = _v1.data();
	F *v2 = _v2.data();
	F *v3 = _v3.data();


	for(int i = 0; i < rounds; i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		if(threads == 1  || 1 << (rounds - 1-i) <= 1<<14){
			cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			
			int L = 1 << (rounds -1- i);
			for(int j = 0; j < L; j++){
				if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
					l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
					//q1 = quadratic_poly()
					F coef = v2[2*j+1] - v2[2*j];
					
					l2 = linear_poly(coef,v2[2*j]);
					l3 = linear_poly(-coef,sum - v2[2*j]);
					temp_poly = l1*l2*l3;
					poly = poly + temp_poly;

				}
				v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
				v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
				v3[j] = sum - v2[j];
			}
		}else{

			int L = 1 << (rounds -1- i);
			
			F *new_v1 = (F *)malloc(L*sizeof(F));
			F *new_v2 = (F *)malloc(L*sizeof(F));
			F *new_v3 = (F *)malloc(L*sizeof(F));
			
			//vector<F> new_v1(L),new_v2(L),new_v3(L);
			vector<cubic_poly> _poly(threads);
			thread worker[threads];
			for(int j = 0; j < threads; j++){
				_poly[j] = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			}

			for(int j = 0; j < threads; j++){
				//worker[i](_generate_2product_sumcheck,ref(v1),ref(v2),ref(_poly[i]),rand,i,L);
				//worker.push_back( std::async(&_generate_3product_sumcheck_proof_folded,ref(v1),ref(v2),ref(v3),ref(new_v1),ref(new_v2),ref(new_v3),ref(_poly[j]),sum,rand,j,L));
				worker[j] = thread(&_generate_3product_sumcheck_proof_folded,(v1),(v2),(v3),(new_v1),(new_v2),(new_v3),ref(_poly[j]),sum,rand,j,L);
				//worker[j] = thread([&](){_generate_3product_sumcheck_proof_folded((v1),(v2),(v3),(new_v1),(new_v2),(new_v3),(_poly[j]),sum,rand,j,L);});
				//thread th(_generate_3product_sumcheck_proof_folded,ref(v1),ref(v2),ref(v3),ref(new_v1),ref(new_v2),ref(new_v3),ref(_poly[j]),sum,rand,j,L);
				//worker.push_back(move(th));
			}
			for(int j = 0; j < threads; j++){
				worker[j].join();
				poly = poly+ _poly[j];
			}
			//copy(v1.begin(),v1.begin()+new_v1.size(),new_v1.begin());
			//copy(v2.begin(),v2.begin()+new_v2.size(),new_v2.begin());
			//copy(v3.begin(),v3.begin()+new_v3.size(),new_v3.begin());
			
			v1 = new_v1;
			v2 = new_v2;
			v3 = new_v3;

		}
		r.push_back(rand);
		vector<F> input;
		input.push_back(rand);
		input.push_back(poly.a);
		input.push_back(poly.b);
		input.push_back(poly.c);
		input.push_back(poly.d);
		vector<vector<F>> temp = mimc_multihash3(input);
		Pr.w_hashes.push_back(temp);
		rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		p.push_back(poly);
	}
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v1[0]);

	return Pr;
}

void _generate_3product_sumcheck(F* v1,F* v2,F* v3,F* new_v1,F* new_v2, F* new_v3, cubic_poly &poly, F rand, int idx, int L){
	int size = L/threads;
	int pos = idx*size;
	linear_poly l1,l2,l3;
	cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);

	

	for(int j = pos; j < pos+size; j++){
		if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			//q1 = quadratic_poly()
			F coef = v2[2*j+1] - v2[2*j];
			l2 = linear_poly(coef,v2[2*j]);
			l3 = linear_poly(-coef,F(1) - v2[2*j]);
			temp_poly = l1*l2*l3;
			poly = poly + temp_poly;
		}
		new_v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
		if(v2[2*j] == F(0) && v2[2*j+1] == F(0)){
			new_v2[j] = F(0);
			new_v3[j] = F(1);
		}else{
			new_v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
			new_v3[j] = F(1)-new_v2[j];//(1-r[i])*v3[2*j] + r[i]*v3[2*j+1];	

		}
	}
}


struct proof _generate_3product_sumcheck_proof(vector<F> &v1, vector<F> &v2, vector<F> &v3,F previous_r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(v1.size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
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

struct proof _generate_batch_3product_sumcheck_proof(vector<vector<F>> &v1, vector<vector<F>> &v2, vector<F> &v3,vector<F> a,F previous_r){
	struct proof Pr;
	int rounds = int(log2(v1[0].size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
	quadratic_poly temp_qpoly;
	cubic_poly temp_poly;
	cubic_poly total;
	vector<cubic_poly> poly(v1.size());
	vector<int> sizes(v1.size());
	for(int i = 0; i < sizes.size(); i++){
		sizes[i] = v1[i].size();
	}
	vector<F> evaluations(2*v1.size()+1,F(0));
	
	for(int i = 0; i < rounds; i++){
		total = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		for(int k = 0; k < v1.size(); k++){
			poly[k] = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		} 
		vector<linear_poly> l1(v1.size()),l2(v2.size()),l3(v3.size());
		for(int k = 0; k < sizes.size(); k++){
			sizes[k] = sizes[k]/2;
		}	
		int L = 1 << (rounds -1- i);
		for(int j = 0; j < L; j++){
			for(int k = 0; k < v1.size(); k++){
				
				if(sizes[k] == 0 && j == 0){
					if(evaluations[2*k+1] == F(0)){
						evaluations[2*k+1] = v1[k][0];
						evaluations[2*k+2] = v2[k][0];
					}
					l1[k] = linear_poly(F_ZERO - v1[k][0],v1[k][0]);
					l2[k] = linear_poly(F_ZERO - v2[k][0],v2[k][0]);
					temp_poly = l1[k]*l2[k]*l3[0];
					poly[k] = poly[k] + temp_poly;
					v1[k][0] = v1[k][2*j] - rand*(v1[k][2*j]); 
					v2[k][0] = v2[k][2*j] - rand*(v2[k][2*j]); 
					continue;
				}
				
				if(sizes[k] <= j)continue;

				l1[k] = linear_poly(v1[k][2*j+1] - v1[k][2*j],v1[k][2*j]);
				l2[k] = linear_poly(v2[k][2*j+1] - v2[k][2*j],v2[k][2*j]);
				
				if(k == 0){
					l3[k] = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
				}
				temp_poly = l1[k]*l2[k]*l3[0];
				poly[k] = poly[k] + temp_poly;

				v1[k][j] = v1[k][2*j] + rand*(v1[k][2*j+1] - v1[k][2*j]); 
				v2[k][j] = v2[k][2*j] + rand*(v2[k][2*j+1] - v2[k][2*j]); 
				if(k == 0){
					v3[j] = v3[2*j] + rand*(v3[2*j+1] - v3[2*j]); 
				}	
			}
		}
		r.push_back(rand);
		vector<F> input;
		for(int k = 0; k < v1.size(); k++){
			total.a += a[k]*poly[k].a;
			total.b += a[k]*poly[k].b;
			total.c += a[k]*poly[k].c;
			total.d += a[k]*poly[k].d;
		}
		
		rand = mimc_hash(rand,total.a);
		rand = mimc_hash(rand,total.b);
		rand = mimc_hash(rand,total.c);
		rand = mimc_hash(rand,total.d);


		//rand = mimc_multihash(input);
		p.push_back(total);
	}
	for(int k = 0; k < v1.size(); k++){
		rand = mimc_hash(rand,v1[k][0]);
		rand = mimc_hash(rand,v2[k][0]);
		if(k == 0){
			rand = mimc_hash(rand,v3[0]);
		}
	}
	//rand = mimc_hash(rand,v3[0]);
	
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	evaluations[0] = v3[0];
	for(int k = 0; k < v1.size(); k++){
		if(evaluations[2*k+1] == 0){
			evaluations[2*k+1] = v1[k][0];
			evaluations[2*k+2] = v2[k][0];
		}
	}
	for(int k = 0; k < v1.size(); k++){
		if(k == 0){
			Pr.vr.push_back(v3[0]);
		}
		Pr.vr.push_back(v1[k][0]);Pr.vr.push_back(v2[k][0]);
	}
	for(int k = 1; k < evaluations.size(); k++){
		Pr.vr.push_back(evaluations[k]);
	}

	return Pr;
}

struct proof generate_batch_3product_sumcheck_proof(vector<vector<F>> &v1, vector<vector<F>> &v2, vector<vector<F>> &v3,vector<F> a,F previous_r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(v1[0].size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
	quadratic_poly temp_qpoly;
	cubic_poly temp_poly;
	cubic_poly total;
	vector<cubic_poly> poly(v1.size());
	for(int i = 0; i < rounds; i++){
		total = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		for(int k = 0; k < v1.size(); k++){
			poly[k] = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		} 
		vector<linear_poly> l1(v1.size()),l2(v2.size()),l3(v3.size());
			
		int L = 1 << (rounds -1- i);
		for(int j = 0; j < L; j++){
			for(int k = 0; k < v1.size(); k++){
				//printf("OK %d\n",k);			
				l1[k] = linear_poly(v1[k][2*j+1] - v1[k][2*j],v1[k][2*j]);
				//q1 = quadratic_poly()
				l2[k] = linear_poly(v2[k][2*j+1] - v2[k][2*j],v2[k][2*j]);
				if(k < v3.size()){
					l3[k] = linear_poly(v3[k][2*j+1] - v3[k][2*j],v3[k][2*j]);
					temp_poly = l1[k]*l2[k]*l3[k];
					poly[k] = poly[k] + temp_poly;
				}else{
					temp_qpoly = l1[k]*l2[k];
					poly[k].b = poly[k].b + temp_qpoly.a;
					poly[k].c = poly[k].c + temp_qpoly.b;
					poly[k].d = poly[k].d + temp_qpoly.c;
				}
			
				v1[k][j] = v1[k][2*j] + rand*(v1[k][2*j+1] - v1[k][2*j]); 
				v2[k][j] = v2[k][2*j] + rand*(v2[k][2*j+1] - v2[k][2*j]); 
				if(k < v3.size()){
					v3[k][j] = v3[k][2*j] + rand*(v3[k][2*j+1] - v3[k][2*j]); 
				}
				
			}
				
			
		}
		r.push_back(rand);
		vector<F> input;
		for(int k = 0; k < v3.size(); k++){
			total.a += a[k]*poly[k].a;
			total.b += a[k]*poly[k].b;
			total.c += a[k]*poly[k].c;
			total.d += a[k]*poly[k].d;
		}
		for(int k = v3.size(); k < v1.size(); k++){
			total.b += a[k]*poly[k].b;
			total.c += a[k]*poly[k].c;
			total.d += a[k]*poly[k].d;
			
		}
		rand = mimc_hash(rand,total.a);
		rand = mimc_hash(rand,total.b);
		rand = mimc_hash(rand,total.c);
		rand = mimc_hash(rand,total.d);


		//rand = mimc_multihash(input);
		p.push_back(total);
	}
	for(int k = 0; k < v1.size(); k++){
		rand = mimc_hash(rand,v1[k][0]);
		rand = mimc_hash(rand,v2[k][0]);
		if(k < v3.size()){
			rand = mimc_hash(rand,v3[k][0]);
		}
	}
	//rand = mimc_hash(rand,v3[0]);
	
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	for(int k = 0; k < v1.size(); k++){
		Pr.vr.push_back(v1[k][0]);Pr.vr.push_back(v2[k][0]);
		if(k < v3.size()){
			Pr.vr.push_back(v3[k][0]);
		}
	}

	return Pr;
}

struct proof generate_3product_sumcheck_proof(vector<F> &v1, vector<F> &v2, vector<F> &_v3,F previous_r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(v1.size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
	//F *v3 = _v3.data();
	F *v3 = (F *)malloc(v2.size()/2 * sizeof(F));
	for(int i = 0; i < rounds; i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		if(threads == 1  || 1 << (rounds - 1-i) <= 1<<10){
			cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			
			int L = 1 << (rounds -1- i);
			for(int j = 0; j < L; j++){
				if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
					l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
					//q1 = quadratic_poly()
					F coef = v2[2*j+1] - v2[2*j];
					l2 = linear_poly(coef,v2[2*j]);
					l3 = linear_poly(-coef,F(1) - v2[2*j]);
					temp_poly = l1*l2*l3;
					poly = poly + temp_poly;

				}
				v1[j] = (F(1)-rand)*v1[2*j] + rand*v1[2*j+1];
				if(v2[2*j] == F(0) && v2[2*j+1] == F(0)){
					v2[j] = F(0);
					v3[j] = F(1);
				}else{
					v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
					v3[j] = F(1)-v2[j];//(1-r[i])*v3[2*j] + r[i]*v3[2*j+1];	

				}
			}

		}
		r.push_back(rand);
		vector<F> input;
		
		//input.push_back(rand);
		//input.push_back(poly.a);
		//input.push_back(poly.b);
		//input.push_back(poly.c);
		//input.push_back(poly.d);
		//vector<vector<F>> temp = mimc_multihash3(input);
		//Pr.w_hashes.push_back(temp);
		//rand = temp[temp.size()-1][temp[0].size()-1];
		rand = mimc_hash(rand,poly.a);
		rand = mimc_hash(rand,poly.b);
		rand = mimc_hash(rand,poly.c);
		rand = mimc_hash(rand,poly.d);


		//rand = mimc_multihash(input);
		p.push_back(poly);
	}
	rand = mimc_hash(rand,v2[0]);
	rand = mimc_hash(rand,v1[0]);
	//rand = mimc_hash(rand,v3[0]);
	
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = rand;
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v3[0]);
	free(v3);
	
	return Pr;
}

void _generate_norm_sumcheck_proof(F **M,F **temp_M,vector<vector<F>> &_M, vector<F> &beta, quadratic_poly &poly, F rand,int idx, int L,int i ){
	int size = _M.size()/threads;
	int pos = idx*size;
	quadratic_poly temp_poly;
	
	for(int k = pos; k < size+pos; k++){
		temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		for(int j = 0; j < L; j++){
			if(i == 0){
				F diff = _M[k][2*j + 1] - _M[k][2*j];
				temp_poly = temp_poly + quadratic_poly(diff*diff,F(2)*diff*_M[k][2*j],_M[k][2*j]*_M[k][2*j]);
				temp_M[k][j] = _M[k][2*j] + rand*(diff);			
			}else{
				F diff = M[k][2*j + 1] - M[k][2*j];
				temp_poly = temp_poly + quadratic_poly(diff*diff,F(2)*diff*M[k][2*j],M[k][2*j]*M[k][2*j]);
				temp_M[k][j] = M[k][2*j] + rand*(diff);	
			}

		}
		poly = poly +  quadratic_poly(beta[k] * temp_poly.a,beta[k] * temp_poly.b,beta[k] * temp_poly.c);
	}
}


struct proof generate_norm_sumcheck_proof(vector<vector<F>> &_M,vector<F> &beta, F previous_r){
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	F rand = mimc_hash(previous_r,F(0));
	vector<quadratic_poly> p;
	int rounds = int(log2(_M[0].size()));

	F **M = (F **)malloc(_M.size()*sizeof(F*));
	for(int i = 0; i < _M.size(); i++){
		M[i] = (F *)malloc(_M[0].size()*sizeof(F)/2);
	}

	auto ts = high_resolution_clock::now();

	
	for(int i = 0; i < rounds; i++){
		quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2;
		int L = 1 << (rounds - 1-i);
		if(threads == 1 || L < 1<<9){
			for(int k = 0; k < _M.size(); k++){
				temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
				for(int j = 0; j < L; j++){
					if(i == 0){
						F diff = _M[k][2*j + 1] - _M[k][2*j];
						temp_poly = temp_poly + quadratic_poly(diff*diff,F(2)*diff*_M[k][2*j],_M[k][2*j]*_M[k][2*j]);
						M[k][j] = _M[k][2*j] + rand*(diff);
					}else{
						F diff = M[k][2*j + 1] - M[k][2*j];
						temp_poly = temp_poly + quadratic_poly(diff*diff,F(2)*diff*M[k][2*j],M[k][2*j]*M[k][2*j]);
						M[k][j] = M[k][2*j] + rand*(diff);
					}
				}
				poly = poly +  quadratic_poly(beta[k] * temp_poly.a,beta[k] * temp_poly.b,beta[k] * temp_poly.c);
			}
		}else{
			F **temp_M = (F **)malloc(_M.size()*sizeof(F*));
			vector<quadratic_poly> _poly(threads);
			for(int j = 0; j < threads; j++){
				_poly[j] = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			}
			for(int j = 0; j < _M.size(); j++){
				temp_M[j] = (F *)malloc(L*sizeof(F));
			}
			thread worker[threads];
			for(int j = 0; j < threads; j++){
				worker[j] = thread(&_generate_norm_sumcheck_proof,M,temp_M,ref(_M),ref(beta),ref(_poly[j]),rand,j,L,i);
			}
			for(int j = 0; j < threads; j++){
				worker[j].join();
			}
			for(int j = 0; j < threads; j++){
				poly = poly + _poly[j];
			}
			M = temp_M;
			for(int j = 0; j < _M.size(); j++){
				M[j] = temp_M[j];
			}


		}
		

		r.push_back(rand);
		vector<F> input;
		input.push_back(rand);
		input.push_back(poly.a);
		input.push_back(poly.b);
		input.push_back(poly.c);
		vector<vector<F>> temp = mimc_multihash3(input);
		Pr.w_hashes.push_back(temp);
		rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		p.push_back(poly);
	}
	auto te = high_resolution_clock::now();
	auto tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;

	F eval = F(0);
	for(int i = 0; i < beta.size(); i++){
		eval += beta[i]*M[i][0];
	}
	Pr.vr.push_back(eval);
	Pr.vr.push_back(eval);
	Pr.q_poly = p;
	Pr.randomness.push_back(r);
	return Pr;
 }




void _generate_2product_sumcheck(F *v1,vector<F> &_v1, F *v2, vector<F> &_v2,F *new_v1,F *new_v2,quadratic_poly &poly,F rand,int idx,int L,int i){
	
	int size = L/threads;
	
	int pos = idx*size;
	
	linear_poly l1,l2;
	quadratic_poly temp_poly;
	for(int j = pos; j < pos + size; j++){
		if(i == 0){
			l1 = linear_poly(_v1[2*j+1] - _v1[2*j],_v1[2*j]);
			l2 = linear_poly(_v2[2*j+1] - _v2[2*j],_v2[2*j]);
			temp_poly = l1*l2;
			poly = poly + temp_poly;
			new_v1[j] = _v1[2*j] + rand*(_v1[2*j+1]-_v1[2*j]);
			new_v2[j] = _v2[2*j] + rand*(_v2[2*j+1]-_v2[2*j]);
		
		}else{
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
			temp_poly = l1*l2;
			poly = poly + temp_poly;
			new_v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
			new_v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
		}
		
	}
}





struct proof generate_2product_sumcheck_proof_disk(int fp1, int fp2,int size, F previous_r){
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	vector<F> v1(MAX_CHUNCK),v2(MAX_CHUNCK);
	F rand = previous_r;
	vector<quadratic_poly> p;
	vector<F> rand_v;
	int rounds = int(log2(size));
	
	
	if(!_WRITE){
		int i;
		for(i = 0; i < rounds; i++){
			quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2;
			//printf("%d\n",i );
			int L = 1 << (rounds - 1-i);
			if(2*L > MAX_CHUNCK){
				for(int j = 0; j < size/MAX_CHUNCK; j++){
					read_chunk(fp1,v1,MAX_CHUNCK);
					read_chunk(fp2,v2,MAX_CHUNCK);
					

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
				lseek(fp1, 0, SEEK_SET);
				lseek(fp2, 0, SEEK_SET);
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
		vector<F> fv1(MAX_CHUNCK),fv2(MAX_CHUNCK);
		lseek(fp1, 0, SEEK_SET);
		lseek(fp2, 0, SEEK_SET);
				
		int counter = 0;
		for(int j = 0; j < size/MAX_CHUNCK; j++){
			read_chunk(fp1,v1,MAX_CHUNCK);
			read_chunk(fp2,v2,MAX_CHUNCK);
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
			linear_poly l1,l2;
			
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
		Pr.q_poly = p;
		Pr.randomness.push_back(r);
		Pr.final_rand = rand;
		return Pr;
	}else{

		int i;
		for(i = 0; i < rounds; i++){
			string name1 = dir + "temp_buff1_" + to_string(i);
			string name2 = dir + "temp_buff2_" + to_string(i);
			printf("%s \n",name1.c_str());
			FILE *wp1 = fopen(name1.c_str(),"w");
			FILE *wp2 = fopen(name2.c_str(),"w");
		
			
			if(i != 0){
				name1 = dir + "temp_buff1_" + to_string(i-1);
				name2 = dir + "temp_buff2_" + to_string(i-1);
				close(fp1);close(fp2);
				fp1 = open(name1.c_str(),O_RDWR);
				fp2 = open(name2.c_str(),O_RDWR);
			}
			quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2;
			int L = 1 << (rounds - 1-i);
			for(int j = 0; j < size/MAX_CHUNCK; j++){
				read_chunk(fp1,v1,MAX_CHUNCK);
				read_chunk(fp2,v2,MAX_CHUNCK);		
					
				for(int k = 0; k < MAX_CHUNCK/2; k++){
					l1 = linear_poly(v1[2*k+1] - v1[2*k],v1[2*k]);
					l2 = linear_poly(v2[2*k+1] - v2[2*k],v2[2*k]);
					temp_poly = l1*l2;
					poly = poly + temp_poly;
				}
				
			}
			lseek(fp1, 0, SEEK_SET);
			lseek(fp2, 0, SEEK_SET);
			rand_v.push_back(rand);
			r.push_back(rand);
			rand = mimc_hash(rand,poly.a);
			rand = mimc_hash(rand,poly.b);
			rand = mimc_hash(rand,poly.c);
			p.push_back(poly);
			for(int j = 0; j < size/MAX_CHUNCK; j++){
				read_chunk(fp1,v1,MAX_CHUNCK);
				read_chunk(fp2,v2,MAX_CHUNCK);
				for(int k = 0; k < MAX_CHUNCK/2; k++){
					v1[k] = v1[2*k] + rand_v[i]*(v1[2*k+1]-v1[2*k]);
					v2[k] = v2[2*k] + rand_v[i]*(v2[2*k+1]-v2[2*k]);
				}
				write_file(v1,wp1,MAX_CHUNCK/2);		
				write_file(v2,wp2,MAX_CHUNCK/2);			
				fflush(wp1);
				fflush(wp2);
			}
			printf("OK2 %d \n",i);
			size = size/2;
			
			if(size == MAX_CHUNCK){
				break;
			}
			fclose(wp1);fclose(wp2);
		}
		
		i = i+1;
		string name1 = dir + "temp_buff1_" + to_string(i-1);
		string name2 = dir + "temp_buff2_" + to_string(i-1);
		close(fp1);close(fp2);
		fp1 = open(name1.c_str(),O_RDWR);
		fp2 = open(name2.c_str(),O_RDWR);
		read_chunk(fp1,v1,MAX_CHUNCK);
		read_chunk(fp2,v2,MAX_CHUNCK);

		for(; i < rounds; i++){
			quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2;
			
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
		Pr.q_poly = p;
		Pr.randomness.push_back(r);
		Pr.final_rand = rand;
		return Pr;

	}

}


struct proof generate_2product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, F previous_r){
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	F rand = previous_r;
	vector<quadratic_poly> p;
	int rounds = int(log2(_v1.size()));
	
	F *v1 = (F *)malloc(_v1.size()*sizeof(F)/2);
	F *v2 = (F *)malloc(_v2.size()*sizeof(F)/2);


	for(int i = 0; i < rounds; i++){
		quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		if(threads == 1 || (1 << (rounds - 1-i)) <= threads){
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
		}else{
			
			vector<quadratic_poly> _poly(threads);
			thread worker[threads];
			int L = 1 << (rounds - 1-i);
			F *new_v1 = (F *)malloc(L*sizeof(F));
			F *new_v2= (F *)malloc(L*sizeof(F));
			
			for(int j = 0; j < _poly.size(); j++){
				_poly[j] = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
			}
			for(int j = 0; j < threads; j++){
				//worker[i](_generate_2product_sumcheck,ref(v1),ref(v2),ref(_poly[i]),rand,i,L);
				worker[j] = thread(&_generate_2product_sumcheck,v1,ref(_v1),v2,ref(_v2),new_v1,new_v2,ref(_poly[j]),rand,j,L,i);
			}
			for(int j = 0; j < threads; j++){
				worker[j].join();
				poly = poly+ _poly[j];
			}
			v1 = new_v1;
			v2 = new_v2;
				
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
	free(v1);
	free(v2);
	
	return Pr;
 }



struct proof generate_2product_sumcheck_proof_disk_const(int fp1, int fp2,int size, F previous_r){
	int c = 5;
	int i = 0;
	int new_c = 0,offset,poly_degree,new_degree;
	F omega = getRootOfUnit(c);
	F ilen;F::inv(ilen,F(1<<5));
	int degree = 1<<c;
	vector<F> v1(MAX_CHUNCK),v2(MAX_CHUNCK);
	vector<F> temp_v1(degree),temp_v2(degree);
	vector<F> poly(2*degree),l1(2*degree),l2(2*degree);
	vector<vector<F>> Lv;
	vector<F> rand;

	vector<u32> rev(degree),rev_prod(2*degree);
	rev[0] = 0;rev_prod[0] = 0;
    for (u32 i = 1; i < rev.size(); ++i)
        rev[i] = rev[i >> 1] >> 1 | (i & 1) << (c - 1);
	
	for (u32 i = 1; i < rev_prod.size(); ++i){
		rev_prod[i] = rev_prod[i >> 1] >> 1 | (i & 1) << (c );
	}
        
	
	vector<F> w(degree);w[0] = F(1);w[1] = omega;
	for (u32 i = 2; i < w.size(); ++i) w[i] = w[i - 1] * w[1];
	vector<F> w_prod(2*degree); w_prod[0] = F(1); w_prod[1] = getRootOfUnit(c+1);
	for (u32 i = 2; i < w_prod.size(); ++i) w_prod[i] = w_prod[i - 1] * w_prod[1];
	
	F::inv(w[0],w[0]);

	while(true){
		lseek(fp1,0,SEEK_SET);
		lseek(fp2,0,SEEK_SET);
		for(int j = 0; j < 2*degree; j++){
			poly[j] = F(0);
		}
		for(int j = 0; j < size/MAX_CHUNCK; j++){
			read_chunk(fp1,v1,MAX_CHUNCK);
			read_chunk(fp2,v2,MAX_CHUNCK);
		
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
				offset = 1;
				poly_degree = new_degree; 
			}
			//printf("%d,%d \n",offset,poly_degree);
			for(int k = 0; k < offset; k++){
				for(int l = 0; l < poly_degree; l++){
					temp_v1[l] = v1[poly_degree*k + l];
					temp_v2[l] = v2[poly_degree*k + l];
					l1[l + poly_degree] = 0;
					l2[l+poly_degree] = 0;
				}
				if(c <= 4){
					for(int l = 0; l < degree; l++){
						for(int h = 0; h < degree; h++){
							poly[l+h] += temp_v1[l]*temp_v2[h];
						}
					}
				}else{
					my_fft(l1,w,rev,ilen,true);
					my_fft(l2,w,rev,ilen,true);
					for(int l = 0; l < poly_degree; l++){
						l1[l] = temp_v1[l];
						l2[l] = temp_v2[l];
					}
					my_fft(l1,w_prod,rev_prod,ilen,false);
					my_fft(l2,w_prod,rev_prod,ilen,false);
					for(int l = 0; l < 2*poly_degree; l++){
						poly[l] += l1[l]*l2[l];
					}
				}
				
			}
		}
		
		F r;r.setByCSPRNG();
		rand.push_back(r);
		if(!new_c){
			Lv.push_back(compute_lagrange_coeff(omega,r,degree));
		}else{
			F new_omega = getRootOfUnit(new_degree);
			Lv.push_back(compute_lagrange_coeff(new_omega,r,new_degree));		
		}
		i++;
		
			
		if(MAX_CHUNCK/(1<<(c*i+c)) < 1){
			new_c = (int)log2(MAX_CHUNCK/1<<(c*i+c-1));
			new_degree = MAX_CHUNCK/1<<(c*i+c-1);
		
		}
		if(MAX_CHUNCK/(1<<(c*i)) == 1){
		
			break;
		}
		if((size/(1<<(c*i))) <= MAX_CHUNCK){
		
			break;
		}
	}
	
	lseek(fp1,0,SEEK_SET);
	lseek(fp2,0,SEEK_SET);
	
	
	vector<F> final_v1(size/(1<<(c*i))),final_v2(size/(1<<(c*i)));
	
	int counter = 0;
	for(int j = 0; j < size/MAX_CHUNCK; j++){
		int final_size;
		read_chunk(fp1,v1,MAX_CHUNCK);
		read_chunk(fp2,v2,MAX_CHUNCK);	
		for(int k = 0; k < i; k++){
			for(int l = 0; l < MAX_CHUNCK/(1ULL<<(c*k+(int)log2(Lv[k].size()))); l++){
				v1[l] = Lv[k][0]*v1[Lv[k].size()*l];
				v2[l] = Lv[k][0]*v2[Lv[k].size()*l];
				for(int h = 1; h < Lv[k].size(); h++){
					v1[l] += Lv[k][h]*v1[degree*l + h];
					v2[l] += Lv[k][h]*v2[degree*l + h];
				}
			}
			final_size = MAX_CHUNCK/(1ULL<<(c*k+(int)log2(Lv[k].size())));
			if(final_size < 1){
				printf("Error \n");
				exit(-1);
			}
		}
		for(int k = 0; k < final_size; k++){
			final_v1[counter] = v1[k];
			final_v2[counter] = v2[k];
			counter++;
		}
	}
	proof P = generate_2product_sumcheck_proof(final_v1,final_v2,rand[rand.size()-1]);
	
	// Compute convolution
	vector<F> conv;
	compute_convolution(Lv,conv);

	

	lseek(fp1,0,SEEK_SET);
	lseek(fp2,0,SEEK_SET);
	
	int conv_size = conv.size();
	vector<F> beta;precompute_beta(P.randomness[0],beta);
	vector<F> partial_eval1(conv_size,F(0)),partial_eval2(conv_size,F(0)),partial_eval(conv_size);
	counter = 0;
	for(int i = 0; i < size/MAX_CHUNCK; i++){
		read_chunk(fp1,v1,MAX_CHUNCK);
		read_chunk(fp2,v2,MAX_CHUNCK);
		for(int j = 0; j < MAX_CHUNCK; j+=conv_size){
			for(int k = 0; k < conv_size; k++){
				partial_eval1[k] += beta[counter]*v1[j + k];
				partial_eval2[k] += beta[counter]*v2[j + k];
			}
			counter++;
		}
	}
	
	beta.clear();
	F a,b; a.setByCSPRNG();b.setByCSPRNG();
	for(int i = 0; i < partial_eval1.size(); i++){
		partial_eval[i] = a*partial_eval1[i] + b*partial_eval2[i];
	}
	proof P2 = generate_2product_sumcheck_proof(conv,partial_eval,rand[rand.size()-1]);
	if(a*P.vr[0] + b*P.vr[1] != P2.q_poly[0].eval(F(0))+P2.q_poly[0].eval(F(1))){
		printf("Error \n");
		exit(-1);
	}
	return P;
}



struct proof generate_2product_sumcheck_proof_disk_hybrid(int fp1, int fp2,int size, F previous_r){
	

	int M = 8;
	vector<int> _M;
	
	vector<vector<vector<F>>> Acc_Sums;
	vector<vector<F>> P_sum(M);
	F sum = F(0);
	for(int i = 0; i < M; i++){
		P_sum[i].resize(M,F(0));
	}
	struct proof Pr;
	vector<F> v1(MAX_CHUNCK),v2(MAX_CHUNCK);
	F rand = previous_r;
	vector<quadratic_poly> p;
	vector<F> rand_v,r;
	vector<vector<F>> R1,R2;
	int temp_size = size;
	int cluster_size = 1;
	
	int seg = MAX_CHUNCK/M;
	
	

	while(1){
		lseek(fp1, 0, SEEK_SET);
		lseek(fp2, 0, SEEK_SET);
		if((size/MAX_CHUNCK)/(cluster_size*M) == 0){
			M = (size/MAX_CHUNCK)/cluster_size;
		}
		for(int i = 0; i < size/MAX_CHUNCK; i++){
			read_chunk(fp1,v1,MAX_CHUNCK);
			read_chunk(fp2,v2,MAX_CHUNCK);
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
			}/*else{
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
	lseek(fp2, 0, SEEK_SET);
			
	//printf("%d,%d\n",_M.size(),R1.size());
	//for(int i = 0; i < _M.size(); i++){
		//printf("%d\n",_M[i]);
	//}
	vector<F> fv1(MAX_CHUNCK),fv2(MAX_CHUNCK);
	int counter = 0;
	for(int i = 0; i < size/MAX_CHUNCK; i++){
		read_chunk(fp1,v1,MAX_CHUNCK);
		read_chunk(fp2,v2,MAX_CHUNCK);
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
	for(int k = 0; k < R1.size(); k++){
		for(int i = 0; i < _M[k]; i++){
			for(int j = 0; j < _M[k]; j++){
				f_sum += R1[k][i]*R2[k][j]*Acc_Sums[k][i][j];
			}
		}

	}
	/*
	F r_sum = F(0);
	for(int i = 0; i < fv1.size(); i++){
		r_sum += fv1[i]*fv2[i];
	}
	if(f_sum != r_sum){
		printf("Error in sum\n");
	//	exit(-1);
	}
	*/
	proof P = generate_2product_sumcheck_proof(fv1,fv2, F(0));

	r = P.randomness[0];
	vector<F> beta;
	precompute_beta(r,beta);
	vector<F> evals1(size/MAX_CHUNCK,F(0)),evals2(size/MAX_CHUNCK,F(0));
	counter = 0;
	lseek(fp1, 0, SEEK_SET);
	lseek(fp2, 0, SEEK_SET);
	for(int i = 0; i < size/MAX_CHUNCK; i++){
		read_chunk(fp1,v1,MAX_CHUNCK);
		read_chunk(fp2,v2,MAX_CHUNCK);
		for(int j = 0; j < MAX_CHUNCK; j+=size/MAX_CHUNCK){
			for(int k = 0; k < size/MAX_CHUNCK; k++){
				evals1[k] += beta[counter]*v1[k];
				evals2[k] += beta[counter]*v2[k];
			}
			counter++;
		}
		
	}
	
	return P;

}


struct proof prove_norm(vector<vector<F>> &M, vector<F> r, F norm_eval){
	
	vector<F> beta;
	precompute_beta(r,beta);
	proof P  = generate_norm_sumcheck_proof(M,beta, r[0]);
	if(P.q_poly[0].eval(0) + P.q_poly[0].eval(1) != norm_eval){
		printf("Error in norm check\n");
		exit(-1);
	}
	P.type = -1;
	return P;
}


struct proof prove_ifft(vector<F> M){
	F scale;
	F::inv(scale,M.size());
	vector<F> r1 = generate_randomness(int(log2(M.size())),F(0));
	
    vector<F> Fg(M.size());
    phiGInit(Fg,r1.begin(),scale,r1.size(),true);

    struct proof Pr = generate_2product_sumcheck_proof(Fg,M,r1[r1.size()-1]);
	Pr.randomness.push_back(r1);
	Pr.type = MATMUL_PROOF;
	return Pr;

}

struct proof prove_ifft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum){
	F scale;
	F::inv(scale,M[0].size());
	vector<F> r1,r2;
	

	
	for(int i = 0; i < int(log2(M[0].size()))-1; i++){
		r2.push_back(r[i]);
	}
	r2.push_back(r[r.size()-1]);
	for(int i = 0; i < int(log2(M.size())); i++){
		r1.push_back(r[i+int(log2(M[0].size()))-1]);
	}
	vector<F> Fg(M[0].size());
	clock_t start,end;
	start = clock();
	vector<F> arr = prepare_matrix((transpose(M)),r1);
	phiGInit(Fg,r2.begin(),scale,r2.size(),true);

	struct proof Pr = generate_2product_sumcheck_proof(Fg,arr,r[r.size()-1]);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;

	if(previous_sum != Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1)){
		printf("Error in ifft\n");
		exit(-1);
	}
	
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	Pr.type = MATMUL_PROOF;
	return Pr;
}

struct proof prove_fft(vector<F> M){
	M.resize(2*M.size(),F(0));
	vector<F> r1 = generate_randomness(int(log2(M.size())),F(0));
	
	vector<F> Fg1(M.size()); 
	phiGInit(Fg1,r1.begin(),F(1),r1.size(),false);
	
	struct proof Pr = generate_2product_sumcheck_proof(Fg1,M,r1[r1.size()-1]);
	Pr.randomness.push_back(r1);
	Pr.type = MATMUL_PROOF;
	
	return Pr;

}

struct proof prove_fft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum){
	for(int i  = 0; i < M.size(); i++){
		M[i].resize(2*M[i].size(),F(0));
	}
	

	vector<F> r1,r2;
	for(int i = 0; i < int(log2(M[0].size())); i++){
		r2.push_back(r[i]);
	}
	for(int i = 0; i < int(log2(M.size())); i++){
		r1.push_back(r[i+int(log2(M[0].size()))]);
	}
	clock_t start,end;
	start = clock();
	
	vector<F> arr = prepare_matrix((transpose(M)),r1);
	
	vector<F> Fg1(M[0].size()); 
	phiGInit(Fg1,r2.begin(),F(1),r2.size(),false);
	struct proof Pr = generate_2product_sumcheck_proof(Fg1,arr,r[r.size()-1]);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
	
	if(previous_sum != Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1)){
		printf("Error in fft\n");
		exit(-1);
	}
	Pr.randomness.push_back(r1); 
	Pr.randomness.push_back(r2);
	Pr.type = MATMUL_PROOF;
	return Pr;
}

struct proof _prove_matrix2vector(vector<vector<F>> M, vector<F> v, vector<F> r, F previous_sum, F previous_r){
	struct proof Pr;
	
	
	auto ts = high_resolution_clock::now();
	vector<F> V = prepare_matrix(M,r);
	
	//printf("(%d,%d),(%d,%d),(%d,%d)\n",M1.size(),M1[0].size(),M2.size(),M2[0].size(),V[0].size(),V[1].size());
	if(V.size() != 1){
		
		Pr = generate_2product_sumcheck_proof(V,v,previous_r);
		verify_2product_sumcheck(Pr,Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1));
	
		Pr.randomness.push_back(r);
		
		if(previous_sum != (Pr.q_poly[0].eval(0) +Pr.q_poly[0].eval(1)) ){
			//printf("Error in Matrix2vector multiplication\n");
			//exit(-1);
		}
		Pr.type = MATMUL_PROOF;
	}
	auto te = high_resolution_clock::now();
	auto tduration = duration_cast<microseconds>(te - ts);
	//proving_time += tduration.count()/1000000.0;
	return Pr;
}



struct proof _prove_matrix2matrix_transpose(vector<vector<F>> &M1, vector<F> r, F previous_sum){
	struct proof Pr;
	clock_t start,end;
	start = clock();
	
	vector<F> V1 = prepare_matrix(transpose(M1),r);
	
	vector<F> V2 = V1;
	
	//vector<vector<F>> V = prepare_matrixes(M1,M2,r1,r2);
	
	//printf("(%d,%d),(%d,%d),(%d,%d)\n",M1.size(),M1[0].size(),M2.size(),M2[0].size(),V[0].size(),V[1].size());
	
	Pr = generate_2product_sumcheck_proof(V1,V2,r[r.size()-1]);
	verify_2product_sumcheck(Pr,Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1));
	
	Pr.randomness.push_back(r);
	if(previous_sum != (Pr.q_poly[0].eval(0) +Pr.q_poly[0].eval(1)) ){
		printf("Error in Matrix2Matrix multiplication\n");
		exit(-1);
		//printf("Sumcheck Ok, %d\n", V[0].size());
	}
	Pr.type = MATMUL_PROOF;
	end = clock();
	//proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
	return Pr;
}

struct proof _prove_matrix2matrix(vector<vector<F>> M1, vector<vector<F>> M2, vector<F> r, F previous_sum){
	struct proof Pr;
	vector<F> r1(int(log2(M1.size()))); 
	vector<F> r2(int(log2(M2.size())));
	for(int i = 0; i < r2.size(); i++){
		r2[i] = (r[i]);
	}
	for(int i = 0; i < r1.size(); i++){
		r1[i] = (r[i+r2.size()]);
	}
	
	auto ts = high_resolution_clock::now();
	
	
	vector<vector<F>> V = prepare_matrixes(M1,M2,r1,r2);
	

	//printf("(%d,%d),(%d,%d),(%d,%d)\n",M1.size(),M1[0].size(),M2.size(),M2[0].size(),V[0].size(),V[1].size());
	if(V[0].size() != 1){
		Pr = generate_2product_sumcheck_proof(V[0],V[1],r[r.size()-1]);
		verify_2product_sumcheck(Pr,Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1));
	
		Pr.randomness.push_back(r1);
		Pr.randomness.push_back(r2);
		
		if(previous_sum != (Pr.q_poly[0].eval(0) +Pr.q_poly[0].eval(1)) ){
			printf("Error in Matrix2Matrix multiplication\n");
			//exit(-1);
			//printf("Sumcheck Ok, %d\n", V[0].size());
		}
		Pr.type = MATMUL_PROOF;
	}else{
		
		Pr.randomness.push_back(r1);
		Pr.randomness.push_back(r2);
		if(previous_sum != V[0][0]*V[1][0]){
			printf("Error in Matrix2Matrix multiplication\n");
			exit(-1);
		}
		Pr.type = -1;
	}
	auto te = high_resolution_clock::now();
	auto tduration = duration_cast<microseconds>(te - ts);
	//proving_time += tduration.count()/1000000.0;

	return Pr;
}



struct proof prove_matrix2matrix(vector<vector<F>> M1, vector<vector<F>> M2){
	
	vector<F> r1 = generate_randomness(int(log2(M1.size())),F(0));
	vector<F> r2 = generate_randomness(int(log2(M2.size())),F(0));
	
	vector<vector<F>> V = prepare_matrixes(M1,M2,r1,r2);
	struct proof Pr = generate_2product_sumcheck_proof(V[0],V[1],r2[r2.size()-1]);
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	F sum = F(0);
	for(int i = 0; i < V[0].size(); i++){
		sum += V[0][i]*V[1][i];
	}
	if(sum == (Pr.q_poly[0].eval(0) +Pr.q_poly[0].eval(1)) ){
		//printf("Sumcheck Ok, %d\n", V[0].size());
	}
	Pr.type = MATMUL_PROOF;
	return Pr;
}

vector<vector<F>> generate_bit_matrix(vector<F> &bits,int domain){
	vector<vector<F>> M;
	int elements = bits.size()/domain; 
	M.resize(domain);
	for(int i = 0; i < M.size(); i++){
		for(int j = 0; j < elements; j++){
			M[i].push_back(bits[j*domain+i]);
		}
	}
	pad_matrix(M);
	return M;
}





F single_sum(vector<F> &v,vector<F> &beta){
	F sum = F(0);
	
	for(int i = 0; i < v.size(); i++){
		if(v[i] != F(0)){
			sum = sum+beta[i];
		}
	}
	return sum;
}

void _single_sum(vector<F> &individual_sums, vector<vector<F>> &partitions, vector<F> &beta, int idx, int K){
	
	if(threads < K){
		for(int i = idx; i < K; i += threads){
			individual_sums[i] = single_sum(partitions[i],beta);
		}
	}else{
		if(idx < K){
			
			individual_sums[idx] = single_sum(partitions[idx],beta);		
		}

	}
}

F double_sum(vector<F> &v1, vector<F> &v2,vector<F> &beta){
	F sum= F(0);
	
	for(int i = 0; i < v1.size(); i++){
		if(v1[i] == F(1) && v2[i] == F(1)){
			sum = sum+beta[i];
		}
	}
	return sum;
}


void _double_sum(vector<vector<F>> &Partial_sums, vector<vector<F>> &partitions,vector<F> &beta, int idx, int K){
	vector<vector<int>> pos(K*(K-1)/2);
	int counter = 0;
	
	for(int i = 0; i < K; i++){
		for(int j = i+1; j < K; j++){
			pos[counter].push_back(i);
			pos[counter].push_back(j);
			counter++;
		}
	}
	for(int i = idx; i < K*(K-1)/2; i += threads){
		Partial_sums[pos[i][0]][pos[i][1] - pos[i][0]-1] = double_sum(partitions[pos[i][0]],partitions[pos[i][1]],beta);
	}
}

vector<F> compute_all_sums(vector<F> r){
	int size = 1<<r.size();
	vector<F> sums(size,F(0));
	for(int i = 0; i < r.size(); i++){
		vector<F> temp(1<<i);
		for(int j = 0; j < temp.size(); j++){
			temp[j] = sums[j];
		}
		
		for(int j = 0; j < temp.size(); j++){
			sums[j<<1] = temp[j];
			sums[(j<<1)+1] = temp[j] + r[r.size()-i-1];
		}
	}
	return sums;
}

void _fold_bits(vector<vector<F>> &partitions, vector<F> &sums, vector<F> &folded_bits, int idx){
	int size = folded_bits.size()/threads;
	int pos = idx*(folded_bits.size()/threads);
	int num = 0; 
	for(int i = pos; i < pos + size; i++){
		num = 0;
		for(int j = 0; j < partitions.size(); j++){
			if(partitions[j][i] == F(1)){
				num += (1<<j); 
			}
		}

		folded_bits[i] = (sums[num]);
	}
}

vector<F> fold_bits(vector<vector<F>> &partitions, vector<F> &sums){
	vector<F> folded_bits(partitions[0].size());
	int num = 0;
	if(threads == 1){
		for(int i = 0; i < partitions[0].size(); i++){
			num = 0;
			for(int j = 0; j < partitions.size(); j++){
				if(partitions[j][i] == F(1)){
					num += (1<<j); 
				}
			}

			folded_bits[i] = (sums[num]);
		}
	}else{
		thread workers[threads];
		for(int i = 0; i < threads; i++){
			workers[i] = thread(&_fold_bits,ref(partitions),ref(sums),ref(folded_bits),i);
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}
	}
	return folded_bits;
}


void _predicate_sumcheck_phase1(F *v1,vector<F> &_v1,F *v2, vector<F> &_v2,F *v3, vector<F> &_v3,
 									F *v4, vector<F> &_v4, F *new_v1,F *new_v2,F *new_v3,F *new_v4  ,cubic_poly &poly, F rand, int idx, int L, int i){
	int size = L/threads;
	int pos = size*idx;
	cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
	linear_poly l1,l2,l3,l4;

	//printf("%d,%d,%d,%d,%d,%d,%d,%d,%d\n",L,threads,pos,pos+size,idx,_v1.size(),_v2.size(),_v3.size(),_v4.size() );
	for(int j = pos; j < pos+size; j++){
		
		if(i == 0){
			l1 = linear_poly(_v1[2*j+1] - _v1[2*j],_v1[2*j]);
			l2 = linear_poly(_v2[2*j+1] - _v2[2*j],_v2[2*j]);
			l3 = linear_poly(_v3[2*j+1] - _v3[2*j],_v3[2*j]);
			l4 = linear_poly(_v4[2*j+1] - _v4[2*j],_v4[2*j]);
		}else{
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
			l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
			l4 = linear_poly(v4[2*j+1] - v4[2*j],v4[2*j]);		
		}
		temp_poly = (l2-l4*l3)*l1;
		poly = poly + temp_poly;

		
		if(i == 0){
			new_v1[j] = _v1[2*j] + rand*(_v1[2*j+1] - _v1[2*j]);
			new_v2[j] = _v2[2*j] + rand*(_v2[2*j+1] - _v2[2*j]);
			new_v3[j] = _v3[2*j] + rand*(_v3[2*j+1] - _v3[2*j]);
			new_v4[j] = _v4[2*j] + rand*(_v4[2*j+1] - _v4[2*j]);
			
		}else{
			new_v1[j] = v1[2*j] + rand*(v1[2*j+1] - v1[2*j]);
			new_v2[j] = v2[2*j] + rand*(v2[2*j+1] - v2[2*j]);
			new_v3[j] = v3[2*j] + rand*(v3[2*j+1] - v3[2*j]);
			new_v4[j] = v4[2*j] + rand*(v4[2*j+1] - v4[2*j]);
		}
	}
} 


struct proof predicate_sumcheck_phase1(vector<F> &_v1, vector<F> &_v2, vector<F> &_v3, vector<F> &_v4){
	struct proof Pr;
	vector<F> r = generate_randomness(int(log2(_v1.size())),F(0));
	vector<cubic_poly> p;
	
	F *v1 = (F *)malloc(_v1.size()*sizeof(F)/2);
	F *v2 = (F *)malloc(_v2.size()*sizeof(F)/2);
	F *v3 = (F *)malloc(_v3.size()*sizeof(F)/2);
	F *v4 = (F *)malloc(_v4.size()*sizeof(F)/2);
	
	for(int i = 0; i < r.size(); i++){

		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		int L = 1 << (r.size() -1- i);
		if(threads == 1 || L <= 1<<10){

			cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3,l4;
			
			for(int j = 0; j < L; j++){
					if(i == 0){
						l1 = linear_poly(_v1[2*j+1] - _v1[2*j],_v1[2*j]);
						l2 = linear_poly(_v2[2*j+1] - _v2[2*j],_v2[2*j]);
						l3 = linear_poly(_v3[2*j+1] - _v3[2*j],_v3[2*j]);
						l4 = linear_poly(_v4[2*j+1] - _v4[2*j],_v4[2*j]);
					}else{
						l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
						l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
						l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
						l4 = linear_poly(v4[2*j+1] - v4[2*j],v4[2*j]);		
					}
					temp_poly = (l2-l4*l3)*l1;
					poly = poly + temp_poly;

				if(i == 0){
					v1[j] = _v1[2*j] + r[i]*(_v1[2*j+1] - _v1[2*j]);
					v2[j] = _v2[2*j] + r[i]*(_v2[2*j+1] - _v2[2*j]);
					v3[j] = _v3[2*j] + r[i]*(_v3[2*j+1] - _v3[2*j]);
					v4[j] = _v4[2*j] + r[i]*(_v4[2*j+1] - _v4[2*j]);
					
				}else{
					v1[j] = v1[2*j] + r[i]*(v1[2*j+1] - v1[2*j]);
					v2[j] = v2[2*j] + r[i]*(v2[2*j+1] - v2[2*j]);
					v3[j] = v3[2*j] + r[i]*(v3[2*j+1] - v3[2*j]);
					v4[j] = v4[2*j] + r[i]*(v4[2*j+1] - v4[2*j]);

				}
			}
			
		}else{
			vector<cubic_poly> _poly(threads);
			thread worker[threads];
			//vector<F> new_v1(L),new_v2(L);
			

			F *new_v1 = (F *)malloc(L*sizeof(F));
			F *new_v2 = (F *)malloc(L*sizeof(F));
			F *new_v3 = (F *)malloc(L*sizeof(F));
			F *new_v4 = (F *)malloc(L*sizeof(F));
			
			
			for(int j = 0; j < _poly.size(); j++){
				_poly[j] = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			}
			for(int j = 0; j < threads; j++){
				//worker[i](_generate_2product_sumcheck,ref(v1),ref(v2),ref(_poly[i]),rand,i,L);
				worker[j] = thread(&_predicate_sumcheck_phase1,(v1),ref(_v1),(v2),ref(_v2),(v3),ref(_v3),(v4),ref(_v4),new_v1,new_v2,new_v3,new_v4,ref(_poly[j]),r[i],j,L,i);
				//worker.push_back(move(th));
			}
			for(int j = 0; j < threads; j++){
				worker[j].join();
				poly = poly+ _poly[j];
			}
			
			v1 = new_v1;
			v2 = new_v2;
			v3 = new_v3;
			v4 = new_v4;
				
		}
		p.push_back(poly);

	}
	
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v3[0]);
	Pr.vr.push_back(v4[0]);
	
	return Pr;
}

F compute_beta(vector<F> r1, vector<F> r2){
	F prod = F(1);
	for(int i = 0; i < r1.size(); i++){
		prod = prod*((F(1)-r1[i])*(F(1)-r2[i]) + r1[i]*r2[i]);
	}
	return prod;
}

void _prepare_data(vector<F> &beta1,vector<F> &beta2,vector<F> &Hg1,vector<F> &Hg2,vector<int> &input, vector<F> &W, int idx){
	int size = Hg1.size()/threads;
	int pos = idx*size;
	for(int i = pos; i < pos+size; i++){
		Hg1[i] = beta2[input[i]]*W[input[i]];
		Hg2[i] = beta2[input[i]];
	}
}

void prepare_data(vector<F> &beta1,vector<F> &beta2,vector<F> &Hg1,vector<F> &Hg2,vector<int> &input, vector<F> W){
	if(threads > 1){
		thread workers[threads];
		for(int i = 0; i < threads; i++){
			workers[i] = thread(&_prepare_data,ref(beta1),ref(beta2),ref(Hg1),ref(Hg2),ref(input),ref(W),i);
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}

	}else{
		for(int i = 0; i < Hg1.size(); i++){
			Hg1[i] = beta2[input[i]]*W[input[i]];
			Hg2[i] = beta2[input[i]];
		}
	}
}

/*
void lookup_range_proof(vector<int> input, F previous_r , int domain){
	vector<F> W,X;
	char buff[256];
	
	
	for(int i = 0; i < domain; i++){
		W.push_back(F(i));
	}
	for(int i = 0; i < input.size(); i++){
		X.push_back(F(input[i]));
	}
	int bit_size_input = (int)log2(input.size());
	vector<F> r_in,r_dom,r1,r2;
	r_in = generate_randomness(bit_size_input,previous_r);
	r1 = generate_randomness(bit_size_input,r_in[r_in.size()-1]);
	r_dom = generate_randomness(Q,r1[r1.size()-1]);
	r2 = generate_randomness(Q,r_dom[r_dom.size()-1]);
	vector<F> Hg1((input).size()),Hg2(input.size());
	
	auto ts = high_resolution_clock::now();

	vector<F> beta1;
	precompute_beta(r_in,beta1);

	vector<F> beta2;
	precompute_beta(r_dom,beta2);
	
	
	prepare_data(beta1,beta2,Hg1,Hg2,input,W);
	

	
	struct proof P = predicate_sumcheck_phase1(beta1,Hg1,Hg2,X);
	

	range_proof_size += 4*P.c_poly.size()*sizeof(beta1[0]);

	if(P.c_poly[0].eval(0) + P.c_poly[0].eval(1) != F(0)){
		printf("Error\n");
		exit(-1);
	}

	
	r1 = P.randomness[0];
	F X_j = P.vr[3];
	F _b = P.vr[0];
	F Hg2_eval = P.vr[2];
	F last = P.c_poly[P.c_poly.size()-1].eval(P.randomness[0][P.randomness[0].size()-1]);
	

	
	vector<F> temp_beta;
	
	precompute_beta(P.randomness[0],temp_beta);


	vector<F> predicate(W.size(),F(0));
	
	for(int i = 0; i < X.size(); i++){
		predicate[input[i]] = predicate[input[i]] + temp_beta[i];
	}
	

	proof P1 = generate_2product_sumcheck_proof(predicate,beta2,r_dom[0]);
	range_proof_size += (3*P1.q_poly.size() + 3)*sizeof(beta1[0]);
	
	struct proof P2 = generate_3product_sumcheck_proof_naive(predicate,beta2,W, P1.randomness[0]);
	range_proof_size += (4*P2.c_poly.size()+4)*sizeof(beta1[0]);
	

	if(_b*(-X_j*(P1.q_poly[0].eval(0) + P1.q_poly[0].eval(1)) + (P2.c_poly[0].eval(0) + P2.c_poly[0].eval(1))) != last){
		printf("Error in 1st sumcheck\n");
		exit(-1);
	}


	vector<F> ones(predicate.size(),F(1));
	struct proof P3 = generate_2product_sumcheck_proof(predicate,ones,r_dom[0]);
	if(P3.q_poly[0].eval(1) + P3.q_poly[0].eval(0) != F(1)){
		printf("Error 2nd sumcheck\n");
		exit(-1);
	}
	range_proof_size += (3*P3.q_poly.size() + 3)*sizeof(beta1[0]);

	auto te = high_resolution_clock::now();
	auto tduration = duration_cast<microseconds>(te - ts);
	proving_time += tduration.count()/1000000.0;
	printf("%lf\n", tduration.count()/1000000.0);
	
	ts = high_resolution_clock::now();
	for(int i = 0; i < P.c_poly.size(); i++){
		F c = P.c_poly[i].eval(0) + P.c_poly[i].eval(1);
		c = P.c_poly[i].eval(P.randomness[0][i]);
	}
	for(int i = 0; i < P1.q_poly.size(); i++){
		F c = P1.q_poly[i].eval(0) + P1.q_poly[i].eval(1);
		c = P1.q_poly[i].eval(P1.randomness[0][i]);
	}
	
	for(int i = 0; i < P2.c_poly.size(); i++){
		F c = P2.c_poly[i].eval(0) + P2.c_poly[i].eval(1);
		c = P2.c_poly[i].eval(P2.randomness[0][i]);
	}
	
	for(int i = 0; i < P3.q_poly.size(); i++){
		F c = P3.q_poly[i].eval(0) + P3.q_poly[i].eval(1);
		c = P3.q_poly[i].eval(P3.randomness[0][i]);
	}

		
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
	range_proof_verification_time += tduration.count()/1000000.0;

}

*/

struct proof _prove_bit_decomposition_folded(vector<F> bits, vector<F> r1, F previous_sum, int domain){
	//int domain = 256;
	vector<F> powers;
	powers.push_back(F(1));
	for(int i = 1; i < domain; i++){
		powers.push_back(F(2)*powers[i-1]);
	}
	//check_integrity(bits,num,powers);


	vector<vector<F>> M = generate_bit_matrix(bits,domain);
	int K = 8;

	vector<vector<F>> partitions(K);
	vector<vector<F>> Partial_sums(K);
	vector<F> individual_sums(K);
	int counter = 0;
	for(int i = 0; i < K; i++){
		for(int j = 0; j < bits.size()/K; j++){
			partitions[i].push_back(bits[i*bits.size()/K + j]);
		}
	}
	
	auto s = high_resolution_clock::now();
	
	//vector<F> r1 = generate_randomness(int(log2(num.size())));
	auto ts = high_resolution_clock::now();
	
	vector<F> v1 = prepare_matrix((M),r1);
	auto te = high_resolution_clock::now();
	auto tduration = duration_cast<microseconds>(te - ts);
 	//printf("Matrix : %lf\n",tduration.count()/1000000.0);
	

	M.clear();
	struct proof Pr1 = generate_2product_sumcheck_proof(v1,powers,r1[r1.size()-1]);
	verify_2product_sumcheck(Pr1,Pr1.q_poly[0].eval(0) + Pr1.q_poly[0].eval(1));
	
	if(previous_sum != Pr1.q_poly[0].eval(0) + Pr1.q_poly[0].eval(1)){
		printf("Error in bit_decomposition\n");
		exit(-1);
	}
	
	
	
	vector<F> r2 = generate_randomness(int(log2(bits.size()/K)),r1[r1.size()-1]);
	
	ts = high_resolution_clock::now();
	vector<F> beta; 
	precompute_beta(r2,beta);
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
 	//printf("Beta : %lf\n",tduration/1000000.0);
	
	


	
	ts = high_resolution_clock::now();

	if(threads == 1){
		for(int i = 0; i < K; i++){
			individual_sums[i] = single_sum(partitions[i],beta);
		}
		
		for(int i = 0; i < K; i++){
			for(int j = i+1; j < K; j++){
				Partial_sums[i].push_back(double_sum(partitions[i],partitions[j],beta));
				counter++;
			}
		}
	}else{
		thread workers[threads];
		ts = high_resolution_clock::now();
		
		for(int i = 0; i < threads; i++){
			workers[i] = thread(&_single_sum,ref(individual_sums),ref(partitions),ref(beta),i,K);
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}
		te = high_resolution_clock::now();
		tduration = duration_cast<microseconds>(te - ts);
 		//printf("Sums 1: %lf\n",tduration/1000000.0);
		ts = high_resolution_clock::now();
		
		for(int i = 0; i < K; i++){
			Partial_sums[i].resize(K - i - 1);
		}

		for(int i = 0; i < threads; i++){
			workers[i] = thread(&_double_sum,ref(Partial_sums),ref(partitions),ref(beta),i,K);			
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}
	}
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
 	//printf("Sums : %lf\n",tduration/1000000.0);
	
	
	vector<F> r = generate_randomness(K,F(0));
	
	vector<F> sums = compute_all_sums(r);
	
	


	ts = high_resolution_clock::now();
	vector<F> folded_bits = fold_bits(partitions,sums);
	//for(int i = 0; i < folded_bits.size(); i++){
	//	nfolded_bits[i] = (sums[sums.size()-1] - folded_bits[i]);
	//}
	te = high_resolution_clock::now();
	vector<F> nfolded_bits(folded_bits.size());
	tduration = duration_cast<microseconds>(te - ts);
 	//printf("Fold time : %lf\n",tduration/1000000.0);
	
	ts = high_resolution_clock::now();
	struct proof Pr2 = generate_3product_sumcheck_proof_folded(beta,folded_bits,nfolded_bits,sums[sums.size()-1],r2[r2.size()-1]);
	te = high_resolution_clock::now();
	tduration = duration_cast<microseconds>(te - ts);
 	//printf("Sumcheck : %lf\n",tduration/1000000.0);
	
	auto e = high_resolution_clock::now();
	auto duration = duration_cast<microseconds>(e - s);
 
	
	
	//proving_time += duration.count()/1000000.0;
	
	F sum = F(0);
	for(int i = 0; i < K; i++){
		for(int j = i+1; j < K; j++){
			sum += F(2)*r[i]*r[j]*Partial_sums[i][j-i-1];
		}
	}
	sum = F(0) - sum;
	vector<F> mul(K,F(0));
	for(int i = 0; i < K; i++){
		for(int j = 0; j < K; j++){
			if(j != i){
				mul[i] = mul[i]+r[j];
			}
		}
	}
	for(int i = 0; i < K; i++){
		sum += mul[i]*individual_sums[i]*r[i];
	}
	//e = high_resolution_clock::now();
	
	//duration = duration_cast<microseconds>(e - s);
 
	//printf("Bit decomposition : %d, %f\n", bits.size(),duration/1000000.0);
	
	
	if(sum != Pr2.c_poly[0].eval(0) + Pr2.c_poly[0].eval(1)){
		printf("Error\n");
		exit(-1);
	}
	struct proof Pr;
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	Pr.randomness.push_back(Pr1.randomness[0]);
	Pr.randomness.push_back(Pr2.randomness[0]);
	Pr.vr.insert(Pr.vr.end(),Pr1.vr.begin(),Pr1.vr.end());
	Pr.vr.insert(Pr.vr.end(),Pr2.vr.begin(),Pr2.vr.end());
	Pr.q_poly = Pr1.q_poly;
	Pr.c_poly = Pr2.c_poly;
	Pr.type = RANGE_PROOF_OPT;
	Pr.w_hashes.insert(Pr.w_hashes.end(),Pr1.w_hashes.begin(),Pr1.w_hashes.end());
	Pr.w_hashes.insert(Pr.w_hashes.end(),Pr2.w_hashes.begin(),Pr2.w_hashes.end());
	Pr.r = r;
	Pr.Partial_sums = Partial_sums;
	Pr.individual_sums = individual_sums;
	Pr.K = K;
	return Pr;

}

struct proof _prove_binary(vector<F> bits){
	clock_t start,end;
	auto s = high_resolution_clock::now();
	
	vector<F> r2 = generate_randomness(int(log2(bits.size())),F(0));
	vector<F> beta; 
	
	auto st = high_resolution_clock::now();
	precompute_beta(r2,beta);
	auto se = high_resolution_clock::now();
	auto duration = duration_cast<microseconds>(se - st);
	//printf("beta : %f\n",duration.count()/1000000.0);
	
	vector<F> inv_bits;
	
	st = high_resolution_clock::now();
	
	struct proof Pr2 = generate_3product_sumcheck_proof(beta,bits,inv_bits,r2[r2.size()-1]);
	se = high_resolution_clock::now();
	duration = duration_cast<microseconds>(se - st);
	//printf("sumcheck : %f\n",duration.count()/1000000.0);
	
	auto e = high_resolution_clock::now();
 
	// To get the value of duration use the count()
	// member function on the duration object
	
	duration = duration_cast<microseconds>(e - s);
	end = clock();
	//proving_time += duration.count()/1000000.0;
	//printf("Bit decomposition : %d, %f\n", bits.size(),duration.count()/1000000.0);
	struct proof Pr;
	
	Pr.randomness.push_back(r2);
	Pr.randomness.push_back(Pr2.randomness[0]);
	Pr.vr.insert(Pr.vr.end(),Pr2.vr.begin(),Pr2.vr.end());
	Pr.c_poly = Pr2.c_poly;
	Pr.type = RANGE_PROOF;
	Pr.w_hashes.insert(Pr.w_hashes.end(),Pr2.w_hashes.begin(),Pr2.w_hashes.end());
	
	return Pr;
}

vector<proof> _prove_bit_decomposition(vector<F> bits, vector<F> r1, F previous_sum, F previous_r, int domain){
	//int domain = 256;
	vector<F> powers;
	powers.push_back(F(1));
	for(int i = 1; i < domain; i++){
		powers.push_back(F(2)*powers[i-1]);
	}
	pad_vector(powers);
	
	//check_integrity(bits,num,powers);


	clock_t start,end;
			
	start = clock(); 
	vector<vector<F>> M = generate_bit_matrix(bits,domain);
	
	auto s = high_resolution_clock::now();
	
	auto st = high_resolution_clock::now();
	//vector<F> r1 = generate_randomness(int(log2(num.size())));
	vector<F> v1 = prepare_matrix((M),r1);
	auto se = high_resolution_clock::now();
	auto duration = duration_cast<microseconds>(se - st);
	//printf("Matrix : %f\n",duration.count()/1000000.0);
	for(int i = 0; i < M.size(); i++){
		vector<F>().swap(M[i]);
	}
	vector<vector<F>>().swap(M);
	//M.clear();

	struct proof Pr1 = generate_2product_sumcheck_proof(v1,powers,previous_r);
	verify_2product_sumcheck(Pr1,previous_sum);
	if(previous_sum != Pr1.q_poly[0].eval(0) + Pr1.q_poly[0].eval(1)){
		printf("Error in bit_decomposition\n");
		exit(-1);
	}
	vector<F> r2 = generate_randomness(int(log2(bits.size())),Pr1.final_rand);
	vector<F> beta; 
	
	st = high_resolution_clock::now();
	precompute_beta(r2,beta);
	se = high_resolution_clock::now();
	duration = duration_cast<microseconds>(se - st);
	//printf("beta : %f\n",duration.count()/1000000.0);
	
	vector<F> inv_bits;
	
	st = high_resolution_clock::now();
	
	struct proof Pr2 = generate_3product_sumcheck_proof(beta,bits,inv_bits,r2[r2.size()-1]);
	verify_3product_sumcheck(Pr2,r2,0);
	se = high_resolution_clock::now();
	duration = duration_cast<microseconds>(se - st);
	//printf("sumcheck : %f\n",duration.count()/1000000.0);
	
	auto e = high_resolution_clock::now();
 
	// To get the value of duration use the count()
	// member function on the duration object
	
	duration = duration_cast<microseconds>(e - s);
	end = clock();
	//proving_time += duration.count()/1000000.0;
	//printf("Bit decomposition : %d, %f\n", bits.size(),duration.count()/1000000.0);
	vector<proof> Pr(2);
	Pr[0] = Pr1;
	Pr[1] = Pr2;

	return Pr;

}

// takes as input vectors x of equal size and for each 
// vector outputs Prod_i = x[0]*x[1]*x[2]...x[N]
mul_tree_proof prove_multiplication_tree_new(vector<vector<F>> input, F previous_r, vector<F> prev_x){
	int vectors = input.size();
	
	int depth = (int)log2(input[0].size());
	int size = input[0].size();
	for(int i = 0; i < input.size(); i++){
		if(input[i].size() != size){
			printf("Error in mul tree sumcheck, no equal size vectors\n");
			exit(-1);
		}
	}

	if(1<<depth != size){
		depth++;
		size = 1<<depth;
		for(int i = 0; i < input.size(); i++){
			input[i].resize(1<<depth,F(1));
		}

	}

	if(vectors != 1<<((int)log2(vectors))){
		vectors = 1<<((int)log2(vectors)+1);
		int old_vector_size = input.size();
		vector<F> temp_vector(1<<depth,F(0));
		for(int i = 0; i < vectors-old_vector_size; i++){
			input.push_back(temp_vector);
		}
	}
	
	// Initialize total input
	int total_input_size = vectors*size;
	
	//printf("total input %d\n",total_input_size );
	vector<F> total_input(total_input_size);
	int counter = 0;
	for(int j = 0; j < input.size(); j++){
		for(int i = 0; i < input[0].size(); i++){
			total_input[counter] = input[j][i];
			counter++;
		}
	}	
	

	vector<vector<F>> transcript(depth);
	vector<vector<F>> in1(depth),in2(depth);
	for(int i = 0; i < depth; i++){
		transcript[i].resize(total_input_size/(1<<(i+1)));
		in1[i].resize(total_input_size/(1<<(i+1)));
		in2[i].resize(total_input_size/(1<<(i+1)));
	}
	
	counter = 0;
	for(int i = 0; i < total_input_size/2; i++){
		transcript[0][counter] = total_input[2*i]*total_input[2*i+1];
		in1[0][counter] = total_input[2*i];
		in2[0][counter] = total_input[2*i+1];
		counter++;
		
	}
	int len = total_input_size/2;
	for(int i = 1; i < transcript.size(); i++){
		counter = 0;
		for(int j = 0; j < len/2; j++){
			transcript[i][counter] = transcript[i-1][2*j]*transcript[i-1][2*j + 1];
			in1[i][counter] = transcript[i-1][2*j];
			in2[i][counter] = transcript[i-1][2*j + 1];
			counter++;
		}
		
		len = len/2;
	}
	

	//printf("Final prod len : %d\n",transcript[depth-1].size());
	proof P;
	mul_tree_proof Proof;
	Proof.size = size;
	if(transcript[transcript.size()-1].size() == 1){
		Proof.initial_randomness = previous_r;
		vector<F> r;
		previous_r = mimc_hash(previous_r,transcript[transcript.size()-1][0]);
		Proof.output =transcript[transcript.size()-1];

		F sum = transcript[transcript.size()-1][0];
		Proof.out_eval = sum;
		clock_t s,e;
		s = clock();
		for(int i = depth-1; i >= 0; i--){
			vector<F> beta;
			if(r.size() == 0){
				Proof.in1 = in1[i][0];
				Proof.in2 = in2[i][0];
				F num = mimc_hash(previous_r,in1[i][0]);
				previous_r = mimc_hash(num,in2[i][0]);		
				sum = (1-previous_r)*in1[i][0]+(previous_r)*in2[i][0];
				r.push_back(previous_r);	
			}else{
				precompute_beta(r,beta);
				P = _generate_3product_sumcheck_proof(in1[i], in2[i],beta,  previous_r);
				verify_3product_sumcheck(P,r,sum);
				
				Proof.proofs.push_back(P);
				if(sum != P.c_poly[0].eval(F(1)) +  P.c_poly[0].eval(F(0))){
					printf("error %d\n",i );
				}
				r = P.randomness[0];
				
				//previous_r = generate_randomness(1,r[r.size()-1])[0];
				previous_r = P.final_rand;
				//previous_r = mimc_hash(P.final_rand,P.vr[0]);
				//previous_r = mimc_hash(previous_r,P.vr[1]);
				
				sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
				beta.clear();
				r.insert(r.begin(),previous_r);
			}
			//sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
		}
		e = clock();
		
		Proof.final_r = r;
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
		
	}else{
		Proof.initial_randomness = previous_r;
		Proof.output = transcript[depth-1];
		vector<F> r;
		if(prev_x.size() == 0){
			r = generate_randomness((int)log2(transcript[depth-1].size()),previous_r); 	
		}else{
			r = prev_x;
		}
		
		F sum = evaluate_vector(transcript[depth-1],r);
		Proof.out_eval = sum;
		proof P;
		vector<F> beta;
		if(prev_x.size() == 0){
			previous_r = mimc_hash(r[r.size()-1],sum);
		}
		clock_t s,e;
		s = clock();
		precompute_beta(r,beta);
		for(int i = depth-1; i >= 0; i--){
			vector<F> beta;
			precompute_beta(r,beta);
			vector<F> t;
			
			P = _generate_3product_sumcheck_proof(in1[i], in2[i],beta,  previous_r);
			verify_3product_sumcheck(P,r,sum);

			Proof.proofs.push_back(P);
			if(sum != P.c_poly[0].eval(F(1)) +  P.c_poly[0].eval(F(0))){
				printf("error %d\n",i );
			}
			r = P.randomness[0];
			
			previous_r = P.final_rand;
			
			//previous_r = mimc_hash(P.final_rand,P.vr[0]);
			//previous_r = mimc_hash(previous_r,P.vr[1]);
				
			sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
			beta.clear();
			r.insert(r.begin(),previous_r);
		}
		e = clock();
		
		// Correctness verification
		if(evaluate_vector(total_input,r) != sum){
			printf("Error in mul tree final\n");
			exit(-1);
		}
		// Check individual input evaluation
		Proof.final_r = r;
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
		vector<F> partial_eval(input.size());
		for(int i = 0; i < partial_eval.size(); i++){
			partial_eval[i] = evaluate_vector(input[i],individual_randomness);
		}
		Proof.partial_eval = partial_eval;
		if(sum != evaluate_vector(partial_eval,global_randomness)){
			printf("Error in mul tree peval\n");
			exit(-1);
		}

		vector<F> muls(input.size(),F(1));
		for(int i = 0; i < input.size(); i++){
			for(int j = 0; j < input[i].size(); j++){
				muls[i] = muls[i]*input[i][j];
			}
		}
		for(int i = 0; i < transcript[depth-1].size(); i++){
			if(transcript[depth-1][i] != muls[i]){
				printf("Error\n");
				exit(-1);
			}
		}

	}
	
	return Proof;
}


// takes as input vectors x of equal size and for each 
// vector outputs Prod_i = x[0]*x[1]*x[2]...x[N]
mul_tree_proof prove_multiplication_tree(vector<vector<F>> input, F previous_r, vector<F> prev_x){
	int vectors = input.size();
	
	int depth = (int)log2(input[0].size());
	int size = input[0].size();
	for(int i = 0; i < input.size(); i++){
		if(input[i].size() != size){
			printf("Error in mul tree sumcheck, no equal size vectors\n");
			exit(-1);
		}
	}

	if(1<<depth != size){
		depth++;
		size = 1<<depth;
		for(int i = 0; i < input.size(); i++){
			input[i].resize(1<<depth,F(1));
		}

	}

	if(vectors != 1<<((int)log2(vectors))){
		vectors = 1<<((int)log2(vectors)+1);
		int old_vector_size = input.size();
		vector<F> temp_vector(1<<depth,F(0));
		for(int i = 0; i < vectors-old_vector_size; i++){
			input.push_back(temp_vector);
		}
	}
	
	// Initialize total input
	int total_input_size = vectors*size;
	
	
	vector<F> total_input(total_input_size);
	int counter = 0;
	for(int i = 0; i < input[0].size(); i++){
		for(int j = 0; j < input.size(); j++){
			total_input[counter] = input[j][i];
			counter++;
		}
	}	
	

	vector<vector<F>> transcript(depth);
	vector<vector<F>> in1(depth),in2(depth);
	for(int i = 0; i < depth; i++){
		transcript[i].resize(total_input_size/(1<<(i+1)));
		in1[i].resize(total_input_size/(1<<(i+1)));
		in2[i].resize(total_input_size/(1<<(i+1)));
	}
	
	counter = 0;
	for(int i = 0; i < total_input_size/2; i++){
		transcript[0][counter] = total_input[i]*total_input[i+total_input_size/2];
		in1[0][counter] = total_input[i];
		in2[0][counter] = total_input[i+total_input_size/2];
		counter++;
		
	}
	int len = total_input_size/2;
	for(int i = 1; i < transcript.size(); i++){
		counter = 0;
		for(int j = 0; j < len/2; j++){
			transcript[i][counter] = transcript[i-1][j]*transcript[i-1][j+ len/2];
			in1[i][counter] = transcript[i-1][j];
			in2[i][counter] = transcript[i-1][j+ len/2];
			counter++;
		}
		
		len = len/2;
	}
	

	//printf("Final prod len : %d\n",transcript[depth-1].size());
	proof P;
	mul_tree_proof Proof;
	Proof.size = size;
	if(transcript[transcript.size()-1].size() == 1){
		Proof.initial_randomness = previous_r;
		vector<F> r;
		previous_r = mimc_hash(previous_r,transcript[transcript.size()-1][0]);
		Proof.output =transcript[transcript.size()-1];

		F sum = transcript[transcript.size()-1][0];
		Proof.out_eval = sum;
		clock_t s,e;
		s = clock();
		for(int i = depth-1; i >= 0; i--){
			vector<F> beta;
			if(r.size() == 0){
				Proof.in1 = in1[i][0];
				Proof.in2 = in2[i][0];
				F num = mimc_hash(previous_r,in1[i][0]);
				previous_r = mimc_hash(num,in2[i][0]);		
				sum = (1-previous_r)*in1[i][0]+(previous_r)*in2[i][0];
				r.push_back(previous_r);	
			}else{
				precompute_beta(r,beta);
				P = _generate_3product_sumcheck_proof(in1[i], in2[i],beta,  previous_r);
				verify_3product_sumcheck(P,r,sum);
				
				Proof.proofs.push_back(P);
				if(sum != P.c_poly[0].eval(F(1)) +  P.c_poly[0].eval(F(0))){
					printf("error %d\n",i );
				}
				r = P.randomness[0];
				
				//previous_r = generate_randomness(1,r[r.size()-1])[0];
				previous_r = P.final_rand;
				//previous_r = mimc_hash(P.final_rand,P.vr[0]);
				//previous_r = mimc_hash(previous_r,P.vr[1]);
				
				sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
				beta.clear();
				r.push_back(previous_r);
			}
			//sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
		}
		e = clock();
		
		Proof.final_r = r;
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
		
	}else{
		Proof.initial_randomness = previous_r;
		Proof.output = transcript[depth-1];
		vector<F> r;
		if(prev_x.size() == 0){
			r = generate_randomness((int)log2(transcript[depth-1].size()),previous_r); 	
		}else{
			r = prev_x;
		}
		
		F sum = evaluate_vector(transcript[depth-1],r);
		Proof.out_eval = sum;
		proof P;
		vector<F> beta;
		if(prev_x.size() == 0){
			previous_r = mimc_hash(r[r.size()-1],sum);
		}
		clock_t s,e;
		s = clock();
		precompute_beta(r,beta);
		for(int i = depth-1; i >= 0; i--){
			vector<F> beta;
			precompute_beta(r,beta);
			vector<F> t;
			
			P = _generate_3product_sumcheck_proof(in1[i], in2[i],beta,  previous_r);
			verify_3product_sumcheck(P,r,sum);
				
			Proof.proofs.push_back(P);
			if(sum != P.c_poly[0].eval(F(1)) +  P.c_poly[0].eval(F(0))){
				printf("error %d\n",i );
			}
			r = P.randomness[0];
			
			previous_r = P.final_rand;
			
			//previous_r = mimc_hash(P.final_rand,P.vr[0]);
			//previous_r = mimc_hash(previous_r,P.vr[1]);
				
			sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
			beta.clear();
			r.push_back(previous_r);
		}
		e = clock();
		
		// Correctness verification
		if(evaluate_vector(total_input,r) != sum){
			printf("Error in mul tree final\n");
			exit(-1);
		}
		// Check individual input evaluation
		Proof.final_r = r;
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
		vector<F> partial_eval(input.size());
		for(int i = 0; i < partial_eval.size(); i++){
			partial_eval[i] = evaluate_vector(input[i],individual_randomness);
		}
		Proof.partial_eval = partial_eval;
		if(sum != evaluate_vector(partial_eval,global_randomness)){
			printf("Error in mul tree peval\n");
			exit(-1);
		}

		vector<F> muls(input.size(),F(1));
		for(int i = 0; i < input.size(); i++){
			for(int j = 0; j < input[i].size(); j++){
				muls[i] = muls[i]*input[i][j];
			}
		}
		for(int i = 0; i < transcript[depth-1].size(); i++){
			if(transcript[depth-1][i] != muls[i]){
				printf("Error\n");
				exit(-1);
			}
		}

	}
	
	return Proof;
}


// Check consistency of the paritions with the dataset, and with the permuted elements of each partition with the
// real ones
partition_sumcheck1_proof forest_partition_sumcheck_1( vector<vector<F>> data, vector<vector<F>> permuted_data,
 vector<F> compress_vector, int trees , F _c, F previous_r){
	vector<F> prev_x;
	partition_sumcheck1_proof P;
	P.previous_r = previous_r;
	// First ranomdness
	vector<F> randomness = generate_randomness(3,previous_r);
	F a = randomness[0];
	F b = randomness[1];
	F c = randomness[2];

	// Complicated calculations to pad the matrixes
	vector<F> data_vector,perm_data_vector;
	int individual_size = data[0].size()/2;
	int data_attr_size = data[0].size();
	
	int global_size = data.size();
	vector<vector<F>> compressed_data_perm((trees)*global_size);
	vector<vector<F>> compressed_data_input(global_size);
	for(int i = 0; i < global_size; i+= 1){

		compressed_data_input[i].resize(individual_size);
		for(int j = 0; j < trees; j++){
			compressed_data_perm[i*(trees)+j].resize(individual_size);
		}
		
		for(int j = 0; j < individual_size; j++){
			compressed_data_input[i][j] = (a*data[i][2*j]+b*data[i][2*j+1] +c);
		}
		for(int j = 0; j < trees; j++){
			for(int k = 0; k < individual_size; k++){
				compressed_data_perm[i*(trees)+j][k] = a*permuted_data[i*trees+j][2*k]+b*permuted_data[i*trees+j][2*k+1] +c;
			}
		}
		
		data_vector.insert(data_vector.end(),data[i].begin(),data[i].end());
		for(int j = 0; j < trees; j++){
			perm_data_vector.insert(perm_data_vector.end(),permuted_data[i*trees+j].begin(),permuted_data[i*trees+j].end());
		}
	}
	
	
	mul_tree_proof mP = prove_multiplication_tree(compressed_data_input,c,prev_x);
	
	vector<F> r;
	for(int i = 0; i < mP.individual_randomness.size(); i++){
		r.push_back(mP.individual_randomness[i]);
	}
	for(int i = 0; i < mP.global_randomness.size(); i++){
		r.push_back(mP.global_randomness[i]);
	}

	vector<F> r0 = r,r1 = r;
	vector<F> beta;
	r0.insert(r0.begin(),F(0));
	r1.insert(r1.begin(),F(1));
	precompute_beta(r,beta);
	F eval1_data = F(0),eval2_data = F(0);
	for(int i = 0; i < beta.size(); i++){
		eval1_data += beta[i]*data_vector[2*i];
		eval2_data += beta[i]*data_vector[2*i+1];
	}	
	P.eval1_data = eval1_data;
	P.eval2_data = eval2_data;
	F temp_r = mimc_hash(mP.individual_randomness[mP.individual_randomness.size()-1],eval1_data);
	temp_r = mimc_hash(temp_r,eval2_data);
	vector<F> agg_r = generate_randomness(2,temp_r);
	vector<F> aggr_beta(2*beta.size());

	for(int i = 0; i < beta.size(); i++){
		aggr_beta[2*i] = agg_r[0]*beta[i];
		aggr_beta[2*i+1] = agg_r[1]*beta[i];
	}

	if(mP.final_eval != a*eval1_data + b*eval2_data + c){
		printf("Error in partition sumcheck 1--0\n");
		exit(-1);
	}

	proof sP2 = generate_2product_sumcheck_proof(aggr_beta,data_vector,agg_r[1]);
	verify_2product_sumcheck(sP2,sP2.q_poly[0].eval(0) + sP2.q_poly[0].eval(1));
	
	if(sP2.q_poly[0].eval(F(0)) + sP2.q_poly[0].eval(F(1)) != eval1_data*agg_r[0] + eval2_data*agg_r[1]){
		printf("Error in partition sumcheck 1--3\n");
		exit(-1);			
	}
	aggr_beta.clear();r.clear();beta.clear();


	mul_tree_proof mP1 = prove_multiplication_tree(compressed_data_perm,c,prev_x);
	P.mP1 = mP1;

	
	for(int i = 0; i < mP1.individual_randomness.size(); i++){
		r.push_back(mP1.individual_randomness[i]);
	}
	for(int i = 0; i < mP1.global_randomness.size(); i++){
		r.push_back(mP1.global_randomness[i]);
	}
	F final_r = mP1.global_randomness[mP1.global_randomness.size()-1];
	
	r0 = r;r1 = r;
	r0.insert(r0.begin(),F(0));
	r1.insert(r1.begin(),F(1));
	precompute_beta(r,beta);
	F eval1_perm_data= F(0),eval2_perm_data= F(0);
	P.eval1_perm_data_x = r0;
	P.eval2_perm_data_x = r1;
	
	// Generate the randomness for the aggregation to produce a single evaluation point for 
	// data and permuted data
	
	
	for(int i = 0; i < beta.size(); i++){
		eval1_perm_data += beta[i]*perm_data_vector[2*i];
		eval2_perm_data += beta[i]*perm_data_vector[2*i+1];
	}
	P.eval1_perm_data = eval1_perm_data;
	P.eval2_perm_data = eval2_perm_data;
	
	temp_r = mimc_hash(mP1.individual_randomness[mP1.individual_randomness.size()-1],eval1_perm_data);
	temp_r = mimc_hash(temp_r,eval2_perm_data);
	agg_r = generate_randomness(2,temp_r);
	aggr_beta.resize(2*beta.size());

	for(int i = 0; i < beta.size(); i++){
		aggr_beta[2*i] = agg_r[0]*beta[i];
		aggr_beta[2*i+1] = agg_r[1]*beta[i];
	}
	//F eval1_data = evaluate_vector(data_vector,r0),eval2_data = evaluate_vector(data_vector,r1);
	//F eval1_perm_data = evaluate_vector(perm_data_vector,r0), eval2_perm_data = evaluate_vector(perm_data_vector,r1);
	
	
	F eval_data2 = a*eval1_perm_data + b*eval2_perm_data + c;

	if(mP1.final_eval != eval_data2){
		printf("Error in partition sumcheck 1--1\n");
		exit(-1);
	}


	
	proof sP1 = generate_2product_sumcheck_proof(aggr_beta,perm_data_vector,agg_r[1]);
	verify_2product_sumcheck(sP1,sP1.q_poly[0].eval(0) + sP1.q_poly[0].eval(1));
	
	P.sP1 = sP1;
	if(sP1.q_poly[0].eval(F(0)) + sP1.q_poly[0].eval(F(1)) != eval1_perm_data*agg_r[0] + eval2_perm_data*agg_r[1]){
		printf("Error in partition sumcheck 1--2\n");
		exit(-1);			
	}
	
	P.final_rand = P.sP2.final_rand;
	//P.sP4.randomness[0][P.sP4.randomness[0].size()-1];
	return P;
}

// Check consistency of the paritions with the dataset, and with the permuted elements of each partition with the
// real ones
partition_sumcheck1_proof partition_sumcheck_1( vector<vector<F>> data, vector<vector<F>> permuted_data,
 vector<F> compress_vector, F _c, F previous_r){
	vector<F> prev_x;
	partition_sumcheck1_proof P;
	P.previous_r = previous_r;
	// First ranomdness
	vector<F> randomness = generate_randomness(3,previous_r);
	F a = randomness[0];
	F b = randomness[1];
	F c = randomness[2];

	// Complicated calculations to pad the matrixes
	vector<F> data_vector,perm_data_vector;
	int individual_size = data[0].size()/2;
	int data_attr_size = data[0].size();
	
	int global_size = data.size();
	vector<vector<F>> compressed_data(2*global_size);
	for(int i = 0; i < global_size; i++){

		compressed_data[i].resize(individual_size);
		compressed_data[i + global_size].resize(individual_size);
		
		for(int j = 0; j < individual_size; j++){
			compressed_data[i][j] = (a*data[i][2*j]+b*data[i][2*j+1] +c);
			compressed_data[i+global_size][j] = a*permuted_data[i][2*j]+b*permuted_data[i][2*j+1] +c;
		}
		
		data_vector.insert(data_vector.end(),data[i].begin(),data[i].end());
		perm_data_vector.insert(perm_data_vector.end(),permuted_data[i].begin(),permuted_data[i].end());
	}
	
	
	mul_tree_proof mP1 = prove_multiplication_tree(compressed_data,c,prev_x);
	P.mP1 = mP1;

	vector<F> r;
	for(int i = 0; i < mP1.individual_randomness.size(); i++){
		r.push_back(mP1.individual_randomness[i]);
	}
	for(int i = 0; i < mP1.global_randomness.size()-1; i++){
		r.push_back(mP1.global_randomness[i]);
	}
	F final_r = mP1.global_randomness[mP1.global_randomness.size()-1];
	vector<F> r0 = r,r1 = r;
	vector<F> beta;
	r0.insert(r0.begin(),F(0));
	r1.insert(r1.begin(),F(1));
	precompute_beta(r,beta);
	F eval1_data = F(0),eval2_data= F(0),eval1_perm_data= F(0),eval2_perm_data= F(0);
	P.eval1_data_x = r0;
	P.eval2_data_x = r1;
	P.eval1_perm_data_x = r0;
	P.eval2_perm_data_x = r1;
	
	// Generate the randomness for the aggregation to produce a single evaluation point for 
	// data and permuted data
	
	
	for(int i = 0; i < beta.size(); i++){
		eval1_data += beta[i]*data_vector[2*i];
		eval2_data += beta[i]*data_vector[2*i+1];
		eval1_perm_data += beta[i]*perm_data_vector[2*i];
		eval2_perm_data += beta[i]*perm_data_vector[2*i+1];
	}
	P.eval1_data = eval1_data;
	P.eval2_data = eval2_data;
	P.eval1_perm_data = eval1_perm_data;
	P.eval2_perm_data = eval2_perm_data;
	
	F temp_r = mimc_hash(mP1.individual_randomness[mP1.individual_randomness.size()-1],eval1_data);
	temp_r = mimc_hash(temp_r,eval2_data);
	temp_r = mimc_hash(temp_r,eval1_perm_data);
	temp_r = mimc_hash(temp_r,eval2_perm_data);
	vector<F> agg_r = generate_randomness(2,temp_r);
	vector<F> aggr_beta(2*beta.size());

	for(int i = 0; i < beta.size(); i++){
		aggr_beta[2*i] = agg_r[0]*beta[i];
		aggr_beta[2*i+1] = agg_r[1]*beta[i];
	}
	//F eval1_data = evaluate_vector(data_vector,r0),eval2_data = evaluate_vector(data_vector,r1);
	//F eval1_perm_data = evaluate_vector(perm_data_vector,r0), eval2_perm_data = evaluate_vector(perm_data_vector,r1);
	
	
	F eval_data1 = a*eval1_data + b*eval2_data + c;
	F eval_data2 = a*eval1_perm_data + b*eval2_perm_data + c;

	if(mP1.final_eval != (F(1)- final_r)*eval_data1 + final_r*eval_data2){
		printf("Error in partition sumcheck 1--1\n");
		exit(-1);
	}


	vector<F> temp_aggr_beta = aggr_beta;
	
	
	proof sP1 = generate_2product_sumcheck_proof(temp_aggr_beta,perm_data_vector,agg_r[1]);
	verify_2product_sumcheck(sP1,sP1.q_poly[0].eval(0) + sP1.q_poly[0].eval(1));
	
	P.sP1 = sP1;
	if(sP1.q_poly[0].eval(F(0)) + sP1.q_poly[0].eval(F(1)) != eval1_perm_data*agg_r[0] + eval2_perm_data*agg_r[1]){
		printf("Error in partition sumcheck 1--2\n");
		exit(-1);			
	}
	proof sP2 = generate_2product_sumcheck_proof(aggr_beta,data_vector,sP1.final_rand);
	verify_2product_sumcheck(sP2,sP2.q_poly[0].eval(0) + sP2.q_poly[0].eval(1));
	P.sP1 = sP1;
	if(sP2.q_poly[0].eval(F(0)) + sP2.q_poly[0].eval(F(1)) != eval1_data*agg_r[0] + eval2_data*agg_r[1]){
		printf("Error in partition sumcheck 1--3\n");
		exit(-1);			
	}
	P.final_rand = P.sP2.final_rand;
	//P.sP4.randomness[0][P.sP4.randomness[0].size()-1];
	return P;
}


// Check consistency of each path of the tree
partition_sumcheck2_proof forest_partition_sumcheck_2( vector<vector<F>> power_bits, vector<vector<F>> paths, vector<vector<F>> paths_aux,
 vector<vector<vector<F>>> forest, vector<F> tree_compress_vector, int dataset_size , F c, F previous_r){
	
	vector<F> prev_x;
	partition_sumcheck2_proof P;
	vector<vector<F>> final_powers(forest.size());
	vector<F> final_powers_input;
	vector<vector<F>> mul_tree_input;
	vector<vector<F>> final_powers_tree_input;
	int len;
	vector<vector<F>> compressed_tree(forest.size());
	for(int i = 0; i < forest.size(); i++){
		compressed_tree[i].resize(forest[i].size(),F(1));
	}

	vector<vector<F>> compressed_paths(forest.size());
	for(int i = 0; i < forest.size(); i++){
		compressed_paths[i].resize(dataset_size,F(1));
	}
	for(int k = 0; k < forest.size(); k++){
		for(int i = 0; i < forest[k].size(); i++){
			int j;
			for(int j = 0; j < forest[k][i].size(); j++){
				compressed_tree[k][i] += forest[k][i][j]*tree_compress_vector[j];
			}
		}
		pad_vector_with_num(compressed_tree[k],F(1));		
		len = forest[k][0].size()-2;
		for(int i = 0; i < dataset_size; i++){
			int j = 0;

			for(j = 0; j < len; j++){
				compressed_paths[k][i] += paths[k*dataset_size + i][j]*tree_compress_vector[j];
			}
			compressed_paths[k][i] += paths_aux[k*dataset_size + i][0]*tree_compress_vector[j] + paths_aux[k*dataset_size + i][1]*tree_compress_vector[j+1];
		}
	}

	vector<vector<F>> powers(forest.size());
	for(int k = 0; k < forest.size(); k++){
		for(int i = 0; i < compressed_tree[k].size(); i++){
			powers[k].push_back(compressed_tree[k][i]);
			F prev = compressed_tree[k][i];
			for(int j = 1; j < 32; j++){
				powers[k].push_back(prev*prev);
				prev = prev*prev;
			}
		}
		pad_vector(powers[k]);
	}

	// Compute the path exponents
	for(int k = 0; k < forest.size(); k++){
		final_powers[k].resize(powers[k].size()/32);
		for(int i = 0; i < powers[k].size()/32; i++){
			vector<F> temp(32);
			final_powers[k][i] = F(1);
			for(int j = 0; j < 32; j++){
				final_powers_input.push_back(powers[k][i*32+j]*power_bits[k][i*32+j]);
				temp[j] = (F(1)-power_bits[k][i*32+j]) + powers[k][i*32+j]*power_bits[k][i*32+j];
				final_powers[k][i] *= temp[j];
			}
			final_powers_tree_input.push_back(temp);
		}		
	}

	
	//mul_tree_input.push_back(compressed_paths);
	P.mP1 = prove_multiplication_tree(compressed_paths,previous_r,prev_x);
	
	// Prove the correct computation of comressed paths
	for(int i = 0; i < paths.size(); i++){
		paths[i].insert(paths[i].end(),paths_aux[i].begin(),paths_aux[i].end());
		pad_vector(paths[i]);
	}
	vector<F> temp_vector;
	for(int i = 0; i  < len; i++){
		temp_vector.push_back(tree_compress_vector[i]);
	}
	pad_vector(temp_vector);
	temp_vector.push_back(tree_compress_vector[len]);
	temp_vector.push_back(tree_compress_vector[len+1]);
	pad_vector(temp_vector);
	
	P.sP1 = _prove_matrix2vector(_transpose(paths),temp_vector,P.mP1.individual_randomness,P.mP1.final_eval-F(1),P.mP1.individual_randomness[P.mP1.individual_randomness.size()-1]);
	
	
	P.mP2 = prove_multiplication_tree(final_powers,P.sP1.final_rand,prev_x);
	
	for(int i = 0; i < forest.size(); i++){
		if(P.mP2.output[i] != P.mP1.output[i]){
			printf("Error in partition sumcheck 2--1, %d\n",i);
			exit(-1);
		}

	}


	
	P.mP3 = prove_multiplication_tree(final_powers_tree_input,P.mP2.individual_randomness[P.mP2.individual_randomness.size()-1],P.mP2.final_r);
	
	vector<F> r = P.mP3.individual_randomness;r.insert(r.end(),P.mP3.global_randomness.begin(),P.mP3.global_randomness.end());

	F eval_bits1 = evaluate_vector(convert2vector(power_bits),r);
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

	vector<F> v1 = convert2vector(power_bits);
	vector<F> v2 = convert2vector(powers);
	P.tP1 = _generate_3product_sumcheck_proof(v1,v2,beta,rand);
	verify_3product_sumcheck(P.tP1,r,P.tP1.c_poly[0].eval(F(0)) + P.tP1.c_poly[0].eval(F(1)));
	
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


	vector<F> eval_tree_x = generate_randomness((int)log2(compressed_tree.size()) + (int)log2(compressed_tree[0].size()),P.tP1.final_rand);
	vector<F> eval_powers2_x(5,F(0));
	eval_powers2_x.insert(eval_powers2_x.end(),eval_tree_x.begin(),eval_tree_x.end());
	

	v1 = convert2vector(powers);
	F eval_powers2 = evaluate_vector(v1,eval_powers2_x);
	v1.clear();
	v1 = convert2vector(compressed_tree);
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
	P.sP2 = _prove_matrix2vector(_transpose(tree_matrix),tree_compress_vector,eval_tree_x,eval_tree-F(1),rand);
	


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
	vector<F> t_r;
	verify_3product_sumcheck(P.tP2,t_r,P.tP2.c_poly[0].eval(F(0)) + P.tP2.c_poly[0].eval(F(1)));
	
	v2.clear();
	P.eval_powers3 = P.tP2.vr[1];
	P.eval_powers3_x = P.tP2.randomness[0];

	vector<F> eval_powers3_x = P.tP2.randomness[0];
	
	v1 = convert2vector(powers);
	P.sP3 = generate_2product_sumcheck_proof(gamma_vector1,v1,P.tP2.final_rand);
	verify_2product_sumcheck(P.sP3,P.sP3.q_poly[0].eval(0) + P.sP3.q_poly[0].eval(1));
	
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
	verify_2product_sumcheck(P.sP4,P.sP4.q_poly[0].eval(0) + P.sP4.q_poly[0].eval(1));
	
	if(P.sP4.q_poly[0].eval(F(0)) + P.sP4.q_poly[0].eval(F(1)) != r[0]*P.eval_powers1 + r[1]*P.eval_powers2 +r[2]*P.eval_powers3 + r[3]*P.eval_powers4){
		printf("Error in partition sumcheck 2--6\n");
		exit(-1);	
	}
	P.final_rand = P.sP4.final_rand;
	
	return P;


}



// Check consistency of each path of the tree
partition_sumcheck2_proof partition_sumcheck_2(vector<F> compressed_tree, vector<F> compressed_paths, vector<F> powers, vector<F> power_bits,
	vector<vector<F>> paths, vector<vector<F>> tree,vector<F> tree_compress_vector, F c, F previous_r){
	vector<F> prev_x;
	partition_sumcheck2_proof P;
	vector<F> final_powers(powers.size()/32);
	vector<F> final_powers_input;
	vector<vector<F>> mul_tree_input;
	vector<vector<F>> final_powers_tree_input;
	
	// Compute the path exponents
	for(int i = 0; i < powers.size()/32; i++){
		vector<F> temp(32);
		final_powers[i] = F(1);
		for(int j = 0; j < 32; j++){
			final_powers_input.push_back(powers[i*32+j]*power_bits[i*32+j]);
			temp[j] = (F(1)-power_bits[i*32+j]) + powers[i*32+j]*power_bits[i*32+j];
			final_powers[i] *= temp[j];
		}
		final_powers_tree_input.push_back(temp);
	}
	
	
	mul_tree_input.push_back(compressed_paths);
	P.mP1 = prove_multiplication_tree(mul_tree_input,previous_r,prev_x);
	
	// Prove the correct computation of comressed paths
	
	P.sP1 = _prove_matrix2vector(_transpose(paths),tree_compress_vector,P.mP1.individual_randomness,P.mP1.final_eval-F(1),P.mP1.individual_randomness[P.mP1.individual_randomness.size()-1]);
	
	mul_tree_input.clear();

	mul_tree_input.push_back(final_powers);
	P.mP2 = prove_multiplication_tree(mul_tree_input,P.sP1.final_rand,prev_x);
	
	if(P.mP2.output[0] != P.mP1.output[0]){
		printf("Error in partition sumcheck 2--0\n");
		exit(-1);
	}
	vector<F> r = P.mP2.individual_randomness;
	for(int i = 0; i < P.mP2.global_randomness.size(); i++){
		r.push_back(P.mP2.global_randomness[i]);
	}
	F final_powers_eval = evaluate_vector(final_powers,r);
	if(P.mP2.final_eval != final_powers_eval){
		printf("Error in partition sumcheck 2--1\n");
		exit(-1);
	}

	
	mul_tree_input.clear();
	mul_tree_input = final_powers_tree_input;
	P.mP3 = prove_multiplication_tree(mul_tree_input,P.mP2.individual_randomness[P.mP2.individual_randomness.size()-1],P.mP2.final_r);
	
	r = P.mP3.individual_randomness;
	for(int i = 0; i < P.mP3.global_randomness.size(); i++){
		r.push_back(P.mP3.global_randomness[i]);
	}
	F eval_bits1 = evaluate_vector(power_bits,r);
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

	vector<F> temp_powers = powers;
	P.tP1 = _generate_3product_sumcheck_proof(power_bits,temp_powers,beta,rand);
	verify_3product_sumcheck(P.tP1,r,P.tP1.c_poly[0].eval(F(0)) + P.tP1.c_poly[0].eval(F(1)));
	
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


	vector<F> eval_tree_x = generate_randomness((int)log2(compressed_tree.size()),P.tP1.final_rand);
	vector<F> eval_powers2_x(5,F(0));
	eval_powers2_x.insert(eval_powers2_x.end(),eval_tree_x.begin(),eval_tree_x.end());
	
	F eval_powers2 = evaluate_vector(powers,eval_powers2_x);
	F eval_tree = evaluate_vector(compressed_tree,eval_tree_x);
	if(eval_powers2 != eval_tree){
		printf("Error in partition sumcheck 2--4\n");
		exit(-1);
	}

	P.eval_tree_x = eval_tree_x;
	P.eval_powers2_x = eval_powers2_x;
	P.eval_powers2 =eval_powers2; 

	rand = mimc_hash(eval_tree_x[eval_tree_x.size()-1],eval_powers2);

	P.sP2 = _prove_matrix2vector(_transpose(tree),tree_compress_vector,eval_tree_x,eval_tree-F(1),rand);
	
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
	for(int i = 0; i < powers.size()/32; i++){
		gamma_vector1.insert(gamma_vector1.end(),gamma_subvector1.begin(),gamma_subvector1.end());
		gamma_vector2.insert(gamma_vector2.end(),gamma_subvector2.begin(),gamma_subvector2.end());
	}
	F sum1 = F(0);
	for(int i = 0; i < gamma_vector2.size(); i++){
		sum1 += gamma_vector2[i]*powers[i]*powers[i];
	}
	P.sum1 = sum1;
	temp_powers = powers;
	vector<F> temp_powers2 = powers;
	P.tP2 = _generate_3product_sumcheck_proof(gamma_vector2,temp_powers,temp_powers2,mimc_hash(gamma,sum1));
	vector<F> t_r;
	verify_3product_sumcheck(P.tP2,t_r,P.tP2.c_poly[0].eval(F(0)) + P.tP2.c_poly[0].eval(F(1)));
	
	//F sum1 = P.tP2.c_poly[0].eval(0) + P.tP2.c_poly[0].eval(1);
	P.eval_powers3 = P.tP2.vr[1];
	P.eval_powers3_x = P.tP2.randomness[0];

	vector<F> eval_powers3_x = P.tP2.randomness[0];
	temp_powers = powers;
	P.sP3 = generate_2product_sumcheck_proof(gamma_vector1,temp_powers,P.tP2.final_rand);
	verify_2product_sumcheck(P.sP3,P.sP3.q_poly[0].eval(0) + P.sP3.q_poly[0].eval(1));
	
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
	P.sP4 = generate_2product_sumcheck_proof(aggr_beta,powers,r[3]);
	verify_2product_sumcheck(P.sP4,P.sP4.q_poly[0].eval(0) + P.sP4.q_poly[0].eval(1));

	if(P.sP4.q_poly[0].eval(F(0)) + P.sP4.q_poly[0].eval(F(1)) != r[0]*P.eval_powers1 + r[1]*P.eval_powers2 +r[2]*P.eval_powers3 + r[3]*P.eval_powers4){
		printf("Error in partition sumcheck 2--6\n");
		exit(-1);	
	}
	P.final_rand = P.sP4.final_rand;
	return P;


}


partition_sumcheck3_proof forest_partition_sumcheck_3(vector<vector<F>> paths,vector<vector<F>> permuted_data, vector<vector<F>> diff,
	vector<vector<F>> bit_vectors, F previous_r, int forest_size, int dataset_size , int max_depth){
	
	partition_sumcheck3_proof P;
	int depth = max_depth;
	vector<vector<F>> my_diff(forest_size*dataset_size);
	vector<F> comp1(forest_size*dataset_size*depth),comp2(forest_size*dataset_size*depth),comp11(forest_size*dataset_size*depth),comp12(forest_size*dataset_size*depth);
	F two = F(2);
	two.inv(two,two);
	vector<F> partial_prod1,partial_diff,split_values,direction_values,in1,in2;



	for(int i = 0; i < forest_size*dataset_size; i++){
		for(int j = 0; j < depth; j++){
			//if(paths[i][4*j+1]  != permuted_data[i][2*j]){
			//	printf("Error partition sumcheck 3--1: %d,%d\n",i,j);
			//	exit(-1);
			//}
			my_diff[i].push_back(two*(F(1)+paths[i][4*j+2])*paths[i][4*j+2]*(permuted_data[i][2*j+1]-paths[i][4*j]) +(F(1)+paths[i][4*j+2])*(F(1) - paths[i][4*j+2])*(paths[i][4*j]-permuted_data[i][2*j+1]));
			F x1 = permuted_data[i][2*j+1]-paths[i][4*j];
			comp11[i*depth + j] = x1; 
			
			F x2 = F(1)+paths[i][4*j+2];
			comp12[i*depth + j] = x2; 
			comp1[i*depth + j] = x1*x2; 
			F x3 = x1*x2;
			F x4 = -F(1) + (F(1) + two)*paths[i][4*j+2];
			comp2[i*depth + j] = -F(1) + (F(1) + two)*paths[i][4*j+2]; 
			F x = x3*x4;
			
			if(x != my_diff[i][j]){
				printf("Error partition sumcheck 3--2: %d,%d\n",i,j);
				exit(-1);
			}
		}
	}
	
	
	for(int i = 0; i < diff.size(); i++){
		for(int j = 0; j < diff[i].size(); j++){
			if(my_diff[i][j] != diff[i][j]){
				printf("Error %d,%d\n",i,j);
				exit(-1);
			}
		}
	}



	vector<F> diff_vector = convert2vector(diff);
	vector<F> bit_vector = convert2vector(bit_vectors);
	vector<F> paths_vector = convert2vector(paths);
	vector<F> permuted_data_vector = convert2vector(permuted_data);
	
	pad_vector(diff_vector);pad_vector(bit_vector);pad_vector(paths_vector);pad_vector(permuted_data_vector);
	pad_vector(comp1);pad_vector_with_num(comp2,F(-1));pad_vector(comp11);pad_vector_with_num(comp12,F(1));

	P.previous_r = previous_r;
	vector<F> r = generate_randomness((int)log2(diff_vector.size()),previous_r);
	
	F diff_eval = evaluate_vector(diff_vector,r);
	int q = (int)log2(bin_size);
	if(1 << ((int)log2(q)) != q){
		q = 1 << (((int)log2(q))+1);
	}
	P.diff_eval = diff_eval;
	F temp_r = mimc_hash(r[r.size()-1],diff_eval);
	P.diff_eval_x = r;
	P.range_proof = _prove_bit_decomposition(bit_vector,r,diff_eval,temp_r,q);
	
	//F rand = P.range_proof[1].final_rand;
	//P.final_rand = P.range_proof[1].final_rand;

	vector<F> beta1;
	precompute_beta(r,beta1);
	

	
	proof tP1 = _generate_3product_sumcheck_proof(comp1,comp2,beta1,P.range_proof[1].final_rand);
	verify_3product_sumcheck(tP1,r,tP1.c_poly[0].eval(F(0)) + tP1.c_poly[0].eval(F(1)));
	
	if(tP1.c_poly[0].eval(F(0)) + tP1.c_poly[0].eval(F(1)) != diff_eval){
		printf("Error partition sumcheck 3--3\n");
		exit(-1);
	}
	vector<F> path_x1 = tP1.randomness[0];
	path_x1.insert(path_x1.begin(),F(1));
	path_x1.insert(path_x1.begin(),F(0));
	
	if(tP1.vr[1] != -F(1) + (F(1) + two)*evaluate_vector(paths_vector,path_x1)){
		printf("Error partition sumcheck 3--4\n");
		exit(-1);
	}

	beta1.clear();
	precompute_beta(tP1.randomness[0],beta1);

	proof tP2 = _generate_3product_sumcheck_proof(comp11,comp12,beta1,P.range_proof[1].final_rand);
	verify_3product_sumcheck(tP2,r,tP2.c_poly[0].eval(F(0)) + tP2.c_poly[0].eval(F(1)));

	if(tP2.c_poly[0].eval(F(0)) + tP2.c_poly[0].eval(F(1)) != tP1.vr[0]){
		printf("Error partition sumcheck 3--5\n");
		exit(-1);	
	}
	vector<F> path_x2 = tP2.randomness[0],path_x3 = tP2.randomness[0];
	path_x2.insert(path_x2.begin(),F(0));path_x2.insert(path_x2.begin(),F(0));
	path_x3.insert(path_x3.begin(),F(1));path_x3.insert(path_x3.begin(),F(0));
	F path_eval2 = evaluate_vector(paths_vector,path_x2);
	F path_eval3 = evaluate_vector(paths_vector,path_x3);
	if(path_eval3 + F(1) != tP2.vr[1]){
		printf("Error partition sumcheck 3--6\n");
		exit(-1);	
	}
	vector<F> permuted_data_x = tP2.randomness[0];
	permuted_data_x.insert(permuted_data_x.begin(),F(1));
	F permuted_data_eval = evaluate_vector(permuted_data_vector,permuted_data_x);
	
	// NEED TO FIX THAT
	//if(permuted_data_eval - path_eval2 != tP2.vr[0]){
	//	printf("Error partition sumcheck 3--7\n");
	//	exit(-1);	
	//}
	

	return P;
}



partition_sumcheck3_proof partition_sumcheck_3(vector<vector<F>> paths,vector<vector<F>> permuted_data, vector<vector<F>> diff,
	vector<vector<F>> bit_vectors, F previous_r, int max_depth){
	
	partition_sumcheck3_proof P;
	vector<vector<F>> my_diff(paths.size());
	vector<F> comp1(paths.size()*max_depth),comp2(paths.size()*max_depth),comp11(paths.size()*max_depth),comp12(paths.size()*max_depth);
	F two = F(2);
	two.inv(two,two);
	vector<F> partial_prod1,partial_diff,split_values,direction_values,in1,in2;
	int max_depth_bits = (int)log2(max_depth);
	if(1<<max_depth_bits != max_depth){
		max_depth_bits = (max_depth_bits + 1);
	}
	for(int i = 0; i < paths.size(); i++){
		for(int j = 0; j < max_depth; j++){
			if(paths[i][4*j+1]  != permuted_data[i][2*j]){
				printf("Error partition sumcheck 3--1: %d,%d\n",i,j);
				exit(-1);
			}
			my_diff[i].push_back(two*(F(1)+paths[i][4*j+2])*paths[i][4*j+2]*(permuted_data[i][2*j+1]-paths[i][4*j]) + (F(1)+paths[i][4*j+2])*(F(1) - paths[i][4*j+2])*(paths[i][4*j]-permuted_data[i][2*j+1]));
			F x1 = permuted_data[i][2*j+1]-paths[i][4*j];
			comp11[i*max_depth + j] = x1; 
			
			F x2 = F(1)+paths[i][4*j+2];
			comp12[i*max_depth + j] = x2; 
			comp1[i*max_depth + j] = x1*x2; 
			F x3 = x1*x2;
			F x4 = -F(1) + (F(1) + two)*paths[i][4*j+2];
			comp2[i*max_depth + j] = -F(1) + (F(1) + two)*paths[i][4*j+2]; 
			F x = x3*x4;
			
			if(x != my_diff[i][j]){
				printf("Error partition sumcheck 3--2: %d,%d\n",i,j);
				exit(-1);
			}
		}
		
	}

	for(int i = 0; i < diff.size(); i++){
		for(int j = 0; j < diff[i].size(); j++){
			if(my_diff[i][j] != diff[i][j]){
				printf("Error %d,%d\n",i,j);
				exit(-1);
			}
		}
	}

	
	vector<F> diff_vector = convert2vector(diff);
	vector<F> bit_vector = convert2vector(bit_vectors);
	vector<F> paths_vector = convert2vector(paths);
	vector<F> permuted_data_vector = convert2vector(permuted_data);
	
	pad_vector(diff_vector);pad_vector(bit_vector);pad_vector(paths_vector);pad_vector(permuted_data_vector);
	pad_vector(comp1);pad_vector_with_num(comp2,F(-1));pad_vector(comp11);pad_vector_with_num(comp12,F(1));

	P.previous_r = previous_r;
	vector<F> r = generate_randomness((int)log2(diff_vector.size()),previous_r);
	F diff_eval = evaluate_vector(diff_vector,r);
	int q = (int)log2(bin_size);
	if(1 << ((int)log2(q)) != q){
		q = 1 << (((int)log2(q))+1);
	}
	P.diff_eval = diff_eval;
	F temp_r = mimc_hash(r[r.size()-1],diff_eval);
	P.diff_eval_x = r;
	P.range_proof = _prove_bit_decomposition(bit_vector,r,diff_eval,temp_r,q);
	
	//F rand = P.range_proof[1].final_rand;
	//P.final_rand = P.range_proof[1].final_rand;

	vector<F> beta1;
	precompute_beta(r,beta1);
	

	
	proof tP1 = _generate_3product_sumcheck_proof(comp1,comp2,beta1,P.range_proof[1].final_rand);
	verify_3product_sumcheck(tP1,r,tP1.c_poly[0].eval(F(0)) + tP1.c_poly[0].eval(F(1)));

	if(tP1.c_poly[0].eval(F(0)) + tP1.c_poly[0].eval(F(1)) != diff_eval){
		printf("Error partition sumcheck 3--3\n");
		exit(-1);
	}
	vector<F> path_x1 = tP1.randomness[0];
	path_x1.insert(path_x1.begin(),F(1));
	path_x1.insert(path_x1.begin(),F(0));
	
	if(tP1.vr[1] != -F(1) + (F(1) + two)*evaluate_vector(paths_vector,path_x1)){
		printf("Error partition sumcheck 3--4\n");
		exit(-1);
	}

	beta1.clear();
	precompute_beta(tP1.randomness[0],beta1);

	proof tP2 = _generate_3product_sumcheck_proof(comp11,comp12,beta1,P.range_proof[1].final_rand);
	verify_3product_sumcheck(tP2,tP2.randomness[0],tP2.c_poly[0].eval(F(0)) + tP2.c_poly[0].eval(F(1)));

	if(tP2.c_poly[0].eval(F(0)) + tP2.c_poly[0].eval(F(1)) != tP1.vr[0]){
		printf("Error partition sumcheck 3--5\n");
		exit(-1);	
	}
	vector<F> path_x2 = tP2.randomness[0],path_x3 = tP2.randomness[0];
	path_x2.insert(path_x2.begin(),F(0));path_x2.insert(path_x2.begin(),F(0));
	path_x3.insert(path_x3.begin(),F(1));path_x3.insert(path_x3.begin(),F(0));
	F path_eval2 = evaluate_vector(paths_vector,path_x2);
	F path_eval3 = evaluate_vector(paths_vector,path_x3);
	if(path_eval3 + F(1) != tP2.vr[1]){
		printf("Error partition sumcheck 3--6\n");
		exit(-1);	
	}
	vector<F> permuted_data_x = tP2.randomness[0];
	permuted_data_x.insert(permuted_data_x.begin(),F(1));
	F permuted_data_eval = evaluate_vector(permuted_data_vector,permuted_data_x);
	
	// NEED TO FIX THAT
	//if(permuted_data_eval - path_eval2 != tP2.vr[0]){
	//	printf("Error partition sumcheck 3--7\n");
	//	exit(-1);	
	//}
	

	return P;
}


// Check if the read/write tapes are consistent with each other
mul_tree_proof leaves_sumcheck_1(vector<F> &compressed_read,vector<F> &compressed_write, F previous_r){
	vector<vector<F>> mul_tree_input(2);
	vector<F> empty_vector;
	mul_tree_input[0] = compressed_read;
	mul_tree_input[1] = compressed_write;
	return prove_multiplication_tree(mul_tree_input,previous_r,empty_vector);	
}

// Check if the read/write tapes are consistent with the input
leaves_sumcheck_proof leaves_sumcheck_2(vector<F> input,vector<F> input_metadata,vector<F> read_transcript,vector<F> write_transcript,vector<F> eval2_x, 
	vector<F> beta1, vector<F> beta2, F eval1, F eval2, F previous_r){

	leaves_sumcheck_proof P;
	pad_vector(input);
	
	pad_vector(input_metadata);
	pad_vector(read_transcript);
	int old_size = write_transcript.size();
	pad_vector(write_transcript);
	vector<F> sparse_vec(write_transcript.size(),F(0));
	
	for(int i = old_size+4; i < write_transcript.size(); i+=8){
		write_transcript[i] = F(1);
		sparse_vec[i] = F(1);
	}
	
	vector<F> randomness = generate_randomness((int)log2(input.size())-1,previous_r);
	//printf(">> %d\n",P.P1.sP3.randomness[0].size() );
	
	vector<F> x0_metadata,x1_metadata;
	vector<F> x0_input,x1_input;
	vector<F> x0_readwrite,x1_readwrite,x2_readwrite,x3_readwrite,x4_readwrite;
	x0_input.push_back(F(0));
	x1_input.push_back(F(1));
	x0_metadata.push_back(F(0));
	x1_metadata.push_back(F(1));
	vector<F> metadata_randomness;
	for(int i = randomness.size() - (int)log2(input_metadata.size()) + 1; i < randomness.size(); i++){
		x0_metadata.push_back(randomness[i]);
		x1_metadata.push_back(randomness[i]);	
		metadata_randomness.push_back(randomness[i]);
	}
	
	clock_t s,e;
	s = clock();
	
	vector<F> temp_beta,metadata_beta;
	precompute_beta(randomness,temp_beta);
	precompute_beta(metadata_randomness,metadata_beta);
	x0_readwrite.push_back(F(0));x0_readwrite.push_back(F(0));x0_readwrite.push_back(F(0));
	x1_readwrite.push_back(F(1));x1_readwrite.push_back(F(0));x1_readwrite.push_back(F(0));
	x2_readwrite.push_back(F(0));x2_readwrite.push_back(F(1));x2_readwrite.push_back(F(0));
	x3_readwrite.push_back(F(1));x3_readwrite.push_back(F(1));x3_readwrite.push_back(F(0));
	x4_readwrite.push_back(F(0));x4_readwrite.push_back(F(0));x4_readwrite.push_back(F(1));
	for(int i = 0; i < randomness.size(); i++){
		x0_input.push_back(randomness[i]);
		x1_input.push_back(randomness[i]);	
		x0_readwrite.push_back(randomness[i]);
		x1_readwrite.push_back(randomness[i]);
		x2_readwrite.push_back(randomness[i]);
		x3_readwrite.push_back(randomness[i]);
		x4_readwrite.push_back(randomness[i]);
	}
	P.metadata_x.push_back(x0_metadata);
	P.metadata_x.push_back(x1_metadata);
	P.input_x.push_back(x0_input);
	P.input_x.push_back(x1_input);
	P.readwrite_x.push_back(x0_readwrite);
	P.readwrite_x.push_back(x1_readwrite);
	P.readwrite_x.push_back(x2_readwrite);
	P.readwrite_x.push_back(x3_readwrite);
	P.readwrite_x.push_back(x4_readwrite);

	vector<F> aggr_beta(8*temp_beta.size(),F(0)),aggr_beta_read(8*temp_beta.size(),F(0)),aggr_beta_write(8*temp_beta.size(),F(0));
	vector<F> aggr_beta_input(2*temp_beta.size(),F(0));
	vector<F> aggr_beta_metadata(2*metadata_beta.size(),F(0));
	
	
	F y0_input = evaluate_vector(input,x0_input);
	F y0_metadata = evaluate_vector(input_metadata,x0_metadata);
	F y1_input = evaluate_vector(input,x1_input);
	F y1_metadata = evaluate_vector(input_metadata,x1_metadata);
	
	F y0_read = F(0),y1_read = F(0),y2_read = F(0),y3_read = F(0),y4_read = F(0);
	F y0_write = F(0),y1_write = F(0),y2_write = F(0),y3_write = F(0),y4_write = F(0);
	for(int i = 0; i < temp_beta.size(); i++){
		y0_read += read_transcript[8*i]*temp_beta[i];
		y1_read += read_transcript[8*i+1]*temp_beta[i];
		y2_read += read_transcript[8*i+2]*temp_beta[i];
		y3_read += read_transcript[8*i+3]*temp_beta[i];
		y4_read += read_transcript[8*i+4]*temp_beta[i];
		
		y0_write += write_transcript[8*i]*temp_beta[i];
		y1_write += write_transcript[8*i+1]*temp_beta[i];
		y2_write += write_transcript[8*i+2]*temp_beta[i];
		y3_write += write_transcript[8*i+3]*temp_beta[i];
		y4_write += write_transcript[8*i+4]*temp_beta[i];
						
	}
	P.write_evals.push_back(y0_write);P.write_evals.push_back(y1_write);P.write_evals.push_back(y2_write);
	P.write_evals.push_back(y3_write);P.write_evals.push_back(y4_write);
	P.read_evals.push_back(y0_read);P.read_evals.push_back(y1_read);P.read_evals.push_back(y2_read);
	P.read_evals.push_back(y3_read);P.read_evals.push_back(y4_read);
	P.input_evals.push_back(y0_input);P.input_evals.push_back(y1_input);
	P.metadata_evals.push_back(y0_metadata);P.metadata_evals.push_back(y1_metadata);

	previous_r = chain_hash(chain_hash(chain_hash(chain_hash(randomness[randomness.size()-1],P.metadata_evals),P.input_evals),P.read_evals),P.write_evals);

	vector<F> r = generate_randomness(6,previous_r);
	for(int i = 0; i < temp_beta.size(); i++){
		aggr_beta[8*i] = r[0]*temp_beta[i];
		aggr_beta[8*i+1] = r[1]*temp_beta[i];
		aggr_beta[8*i+2] = r[2]*temp_beta[i];
		aggr_beta[8*i+3] = r[3]*temp_beta[i];
		aggr_beta[8*i+4] = r[4]*temp_beta[i];
	}
	for(int i = 0; i < aggr_beta_read.size(); i++){
		aggr_beta_read[i] = aggr_beta[i] + r[5]*beta1[i];
		aggr_beta_write[i] = aggr_beta[i] + r[5]*beta2[i];	
	}
	for(int i = 0; i < temp_beta.size(); i++){
		aggr_beta_input[2*i] = r[0]*temp_beta[i];
		aggr_beta_input[2*i+1] = r[1]*temp_beta[i];
	}
	for(int i = 0; i < metadata_beta.size(); i++){
		aggr_beta_metadata[2*i] = r[0]*metadata_beta[i];
		aggr_beta_metadata[2*i+1] = r[1]*metadata_beta[i];	
	}


	if(y0_input != y1_read || y0_input != y1_write){
		printf("Error leaves_sumcheck 2---1\n");
		exit(-1);
	}
	if(y1_input != y2_read || y1_input != y2_write){
		printf("Error leaves_sumcheck 2---2\n");
		exit(-1);
	}
	// Error will be thrown if attributes are not power of 2
	if(y0_metadata != y0_read || y0_metadata != y0_write){
		printf("Error leaves_sumcheck 2---3\n");
		exit(-1);	
	}
	if(y1_metadata != y3_read || y1_metadata != y3_write){
		printf("Error leaves_sumcheck 2---4\n");
		exit(-1);	
	}
	if(y4_write - y4_read - F(1) != F(0)){
		printf("Error leaves_sumcheck 2---5\n");
		exit(-1);
	}


	//P.sP1 = generate_2product_sumcheck_proof(read_transcript,aggr_beta_read,r[5]);
	//verify_2product_sumcheck(P.sP1,P.sP1.q_poly[0].eval(0) + P.sP1.q_poly[0].eval(1));

	//if(P.sP1.q_poly[0].eval(F(0)) + P.sP1.q_poly[0].eval(F(1)) != r[0]*y0_read + r[1]*y1_read +r[2]*y2_read +r[3]*y3_read +r[4]*y4_read + r[5]*eval1){
	//	printf("Error leaves_sumcheck 2---6\n");
	//	exit(-1);		
	//}
	
	//P.sP2 = generate_2product_sumcheck_proof(write_transcript,aggr_beta_write,P.sP1.final_rand);
	//verify_2product_sumcheck(P.sP2,P.sP2.q_poly[0].eval(0) + P.sP2.q_poly[0].eval(1));
	//P.sparse_vector_eval = evaluate_vector(sparse_vec,eval2_x);
	
	//if(P.sP2.q_poly[0].eval(F(0)) + P.sP2.q_poly[0].eval(F(1)) != r[0]*y0_write + r[1]*y1_write +r[2]*y2_write +r[3]*y3_write +r[4]*y4_write + r[5]*(P.sparse_vector_eval+eval2)){
	//	printf("Error leaves_sumcheck 2---7\n");
	//	exit(-1);		
	//}
	P.sP3 = generate_2product_sumcheck_proof(input,aggr_beta_input,P.sP2.final_rand);
	verify_2product_sumcheck(P.sP3,P.sP3.q_poly[0].eval(0) + P.sP3.q_poly[0].eval(1));
	if(P.sP3.q_poly[0].eval(F(0)) + P.sP3.q_poly[0].eval(F(1)) != r[0]*y0_input + r[1]*y1_input){
		printf("Error leaves_sumcheck 2---8\n");
		exit(-1);		
	}
	P.sP4 = generate_2product_sumcheck_proof(input_metadata,aggr_beta_metadata,P.sP3.final_rand);
	verify_2product_sumcheck(P.sP4,P.sP4.q_poly[0].eval(0) + P.sP4.q_poly[0].eval(1));
	if(P.sP4.q_poly[0].eval(F(0)) + P.sP4.q_poly[0].eval(F(1)) != r[0]*y0_metadata + r[1]*y1_metadata){
		printf("Error leaves_sumcheck 2---9\n");
		exit(-1);		
	}

	e = clock();
	printf("Leaves sumcheck 2 : %lf\n",(float)(e-s)/(float)CLOCKS_PER_SEC);
	P.final_rand = P.sP4.final_rand;	

	return P;
}


// Check if the read/write tapes are consistent with the input
leaves_sumcheck_proof forest_leaves_sumcheck_2(vector<F> input, vector<F> idx,vector<F> &partitions,vector<F> labels, vector<F> &read_transcript,
	vector<F> &write_transcript, vector<F> eval2_x, vector<F> beta1, vector<F> beta2, F eval1, F eval2, int forest_size , F previous_r  ){

	leaves_sumcheck_proof P;
	pad_vector(input);
	

	pad_vector(read_transcript);
	int old_size = write_transcript.size();
	pad_vector(write_transcript);
	vector<F> sparse_vec(write_transcript.size(),F(0));
	
	for(int i = old_size+4; i < write_transcript.size(); i+=8){
		write_transcript[i] = F(1);
		sparse_vec[i] = F(1);
	}
	printf("%d\n",input.size() );
	vector<F> randomness = generate_randomness((int)log2(input.size())-1,previous_r);
	//printf(">> %d\n",P.P1.sP3.randomness[0].size() );
	vector<F> x_partitions,x_labels,x_idx;
	
	vector<F> x0_readwrite,x1_readwrite,x2_readwrite,x3_readwrite,x4_readwrite;
	vector<F> x0_input = randomness,x1_input = randomness;
	x0_input.insert(x0_input.begin(),F(0));
	x1_input.insert(x1_input.begin(),F(1));
	x0_readwrite.push_back(F(0));x0_readwrite.push_back(F(0));x0_readwrite.push_back(F(0));
	x1_readwrite.push_back(F(1));x1_readwrite.push_back(F(0));x1_readwrite.push_back(F(0));
	x2_readwrite.push_back(F(0));x2_readwrite.push_back(F(1));x2_readwrite.push_back(F(0));
	x3_readwrite.push_back(F(1));x3_readwrite.push_back(F(1));x3_readwrite.push_back(F(0));
	x4_readwrite.push_back(F(0));x4_readwrite.push_back(F(0));x4_readwrite.push_back(F(1));
	
	x0_readwrite.insert(x0_readwrite.end(),randomness.begin(),randomness.end());
	x1_readwrite.insert(x1_readwrite.end(),randomness.begin(),randomness.end());
	x2_readwrite.insert(x2_readwrite.end(),randomness.begin(),randomness.end());
	x3_readwrite.insert(x3_readwrite.end(),randomness.begin(),randomness.end());
	x4_readwrite.insert(x4_readwrite.end(),randomness.begin(),randomness.end());
	
	vector<F> transcript_rand = generate_randomness((int)log2(read_transcript.size()) - x1_readwrite.size(),randomness[randomness.size()-1]);
	x0_readwrite.insert(x0_readwrite.end(),transcript_rand.begin(),transcript_rand.end());
	x1_readwrite.insert(x1_readwrite.end(),transcript_rand.begin(),transcript_rand.end());
	x2_readwrite.insert(x2_readwrite.end(),transcript_rand.begin(),transcript_rand.end());
	x3_readwrite.insert(x3_readwrite.end(),transcript_rand.begin(),transcript_rand.end());
	x4_readwrite.insert(x4_readwrite.end(),transcript_rand.begin(),transcript_rand.end());

	for(int i = randomness.size()-(int)log2(labels.size()); i < randomness.size(); i++){
		x_labels.push_back(randomness[i]);
	}
	for(int i = x0_readwrite.size() - (int)log2(partitions.size()); i < x0_readwrite.size(); i++){
		x_partitions.push_back(x0_readwrite[i]);
	}
	x_idx = x_partitions;

	printf("%d\n", x0_readwrite.size());
	F y0_input = evaluate_vector(input,x0_input);
	F y1_input = evaluate_vector(input,x1_input);
	F y_partitions = evaluate_vector(partitions,x_partitions);
	F y_label = evaluate_vector(labels,x_labels);
	F y_idx = evaluate_vector(idx,x_idx);
	F y0_read = F(0),y1_read = F(0),y2_read = F(0),y3_read = F(0),y4_read = F(0);
	F y0_write = F(0),y1_write = F(0),y2_write = F(0),y3_write = F(0),y4_write = F(0);

	vector<F> r = randomness;r.insert(r.end(),transcript_rand.begin(),transcript_rand.end());
	vector<F> input_temp_beta;precompute_beta(randomness,input_temp_beta);
	vector<F> temp_beta;precompute_beta(r,temp_beta);

	for(int i = 0; i < temp_beta.size(); i++){
		y0_read += read_transcript[8*i]*temp_beta[i];
		y1_read += read_transcript[8*i+1]*temp_beta[i];
		y2_read += read_transcript[8*i+2]*temp_beta[i];
		y3_read += read_transcript[8*i+3]*temp_beta[i];
		y4_read += read_transcript[8*i+4]*temp_beta[i];
		
		y0_write += write_transcript[8*i]*temp_beta[i];
		y1_write += write_transcript[8*i+1]*temp_beta[i];
		y2_write += write_transcript[8*i+2]*temp_beta[i];
		y3_write += write_transcript[8*i+3]*temp_beta[i];
		y4_write += write_transcript[8*i+4]*temp_beta[i];
						
	}
	/*
	y0_read = evaluate_vector(read_transcript,x0_readwrite);
	y0_write = evaluate_vector(write_transcript,x0_readwrite);
	y1_read = evaluate_vector(read_transcript,x1_readwrite);
	y2_read = evaluate_vector(read_transcript,x2_readwrite);
	y3_read = evaluate_vector(read_transcript,x3_readwrite);
	y4_read = evaluate_vector(read_transcript,x4_readwrite);
	
	y1_write = evaluate_vector(write_transcript,x1_readwrite);
	y2_write = evaluate_vector(write_transcript,x2_readwrite);
	y3_write = evaluate_vector(write_transcript,x3_readwrite);
	y4_write = evaluate_vector(write_transcript,x4_readwrite);
	*/
	if(y0_input != y1_read || y0_input != y1_write){
		printf("Error leaves_sumcheck 2---1\n");
		//exit(-1);
	}
	if(y1_input != y2_read || y1_input != y2_write){
		printf("Error leaves_sumcheck 2---2\n");
		//exit(-1);
	}
	if(y_partitions != y0_read || y_partitions != y0_write){
		printf("Error leaves_sumcheck 2---3\n");
		//exit(-1);
	}
	if(y_label != y3_read || y_label != y3_write){
		printf("Error leaves_sumcheck 2---4\n");
		//exit(-1);	
	}
	if(y4_write - y4_read - y_idx != F(0)){
		printf("Error leaves_sumcheck 2---5\n");
		//exit(-1);
	}

	P.write_evals.push_back(y0_write);P.write_evals.push_back(y1_write);P.write_evals.push_back(y2_write);
	P.write_evals.push_back(y3_write);P.write_evals.push_back(y4_write);
	P.read_evals.push_back(y0_read);P.read_evals.push_back(y1_read);P.read_evals.push_back(y2_read);
	P.read_evals.push_back(y3_read);P.read_evals.push_back(y4_read);
	P.input_evals.push_back(y0_input);P.input_evals.push_back(y1_input);
	P.metadata_evals.push_back(y_idx);P.metadata_evals.push_back(y_label);P.metadata_evals.push_back(y_partitions);

	previous_r = chain_hash(chain_hash(chain_hash(chain_hash(transcript_rand[transcript_rand.size()-1],P.metadata_evals),P.input_evals),P.read_evals),P.write_evals);

	r = generate_randomness(6,previous_r);
	
	vector<F> aggr_beta(8*temp_beta.size(),F(0));//aggr_beta_read(8*temp_beta.size(),F(0)),aggr_beta_write(8*temp_beta.size(),F(0));
	vector<F> aggr_beta_input(input.size(),F(0));
	for(int i = 0; i < temp_beta.size(); i++){
		aggr_beta[8*i] = r[0]*temp_beta[i];
		aggr_beta[8*i+1] = r[1]*temp_beta[i];
		aggr_beta[8*i+2] = r[2]*temp_beta[i];
		aggr_beta[8*i+3] = r[3]*temp_beta[i];
		aggr_beta[8*i+4] = r[4]*temp_beta[i];
	}
	//for(int i = 0; i < aggr_beta_read.size(); i++){
		//aggr_beta_read[i] = aggr_beta[i] + r[5]*beta1[i];
		//aggr_beta_write[i] = aggr_beta[i] + r[5]*beta2[i];	
	//}
	for(int i = 0; i < input_temp_beta.size(); i++){
		aggr_beta_input[2*i] = r[0]*input_temp_beta[i];
		aggr_beta_input[2*i+1] = r[1]*input_temp_beta[i];
	}

	//P.sP1 = generate_2product_sumcheck_proof(read_transcript,aggr_beta_read,r[5]);
	//verify_2product_sumcheck(P.sP1,P.sP1.q_poly[0].eval(0) + P.sP1.q_poly[0].eval(1));

	//if(P.sP1.q_poly[0].eval(F(0)) + P.sP1.q_poly[0].eval(F(1)) != r[0]*y0_read + r[1]*y1_read +r[2]*y2_read +r[3]*y3_read +r[4]*y4_read + r[5]*eval1){
	//	printf("Error leaves_sumcheck 2---6\n");
	//	exit(-1);		
	//}
	
	//P.sP2 = generate_2product_sumcheck_proof(write_transcript,aggr_beta_write,P.sP1.final_rand);
	//verify_2product_sumcheck(P.sP2,P.sP2.q_poly[0].eval(0) + P.sP2.q_poly[0].eval(1));
	//P.sparse_vector_eval = evaluate_vector(sparse_vec,eval2_x);
	
	//if(P.sP2.q_poly[0].eval(F(0)) + P.sP2.q_poly[0].eval(F(1)) != r[0]*y0_write + r[1]*y1_write +r[2]*y2_write +r[3]*y3_write +r[4]*y4_write + r[5]*(P.sparse_vector_eval+eval2)){
	//	printf("Error leaves_sumcheck 2---7\n");
	//	exit(-1);		
	//}
	P.sP3 = generate_2product_sumcheck_proof(input,aggr_beta_input,P.sP2.final_rand);
	verify_2product_sumcheck(P.sP3,P.sP3.q_poly[0].eval(0) + P.sP3.q_poly[0].eval(1));
	if(P.sP3.q_poly[0].eval(F(0)) + P.sP3.q_poly[0].eval(F(1)) != r[0]*y0_input + r[1]*y1_input){
		printf("Error leaves_sumcheck 2---8\n");
		exit(-1);		
	}
	return P;
}


gini_sumcheck1_proof gini_sumcheck_1(vector<F> &input, F previous_r, vector<F> x, F final_eval , int nodes, int attr, int bin_size){
	vector<F> N(nodes*attr*2*bin_size);
	vector<F> inverses(nodes*attr*2*bin_size);
	vector<F> divisors(nodes*attr*2*bin_size);
	vector<F> dividents(nodes*attr*2*bin_size);
	vector<F> quotients(nodes*attr*2*bin_size);
	vector<F> cond(nodes*attr*2*bin_size),cond_inv(nodes*attr*2*bin_size);
	vector<F> dividents_cond(nodes*attr*2*bin_size);
	vector<F> divisors_quot(nodes*attr*2*bin_size);
	int counter = 0;
	gini_sumcheck1_proof P;
	for(int i = counter; i <counter+ nodes*attr*2*bin_size; i++){
		inverses[i-counter] = input[i];
	}
	counter+= nodes*attr*2*bin_size;
	for(int i = counter; i <counter+ nodes*attr*2*bin_size; i++){
		quotients[i-counter] = input[i];
	}
	counter+= nodes*attr*2*bin_size;
	for(int i = counter; i <counter+ nodes*attr*2*bin_size; i++){
		divisors[i-counter] = input[i];
	}
	counter+= nodes*attr*2*bin_size;
	for(int i = counter; i <counter+ nodes*attr*2*bin_size; i++){
		dividents[i-counter] = input[i];
	}
	counter+= nodes*attr*2*bin_size;
	for(int i = counter; i <counter+ nodes*attr*2*bin_size; i++){
		N[i-counter] = input[i];
	}
	for(int i = 0; i < cond.size(); i++){
		cond[i] = inverses[i]*N[i];
		cond_inv[i] = F(1) - cond[i];
	}
	vector<F> cond2 = cond;
	for(int i = 0; i < dividents_cond.size(); i++){
		dividents_cond[i] = cond[i]*dividents[i];
	}
	for(int i = 0; i < divisors_quot.size(); i++){
		divisors_quot[i] = quotients[i]*divisors[i]; 
	}

	pad_vector(divisors_quot);
	pad_vector(dividents_cond);
	pad_vector(cond);
	pad_vector(cond2);
	cond_inv.resize(cond.size(),F(1));
	pad_vector(quotients);
	pad_vector(N);
	vector<F> N2 = N;
	pad_vector(dividents);
	pad_vector(divisors);
	pad_vector(inverses);
	
	//vector<F> randomness = generate_randomness((int)log2(divisors_quot.size()),F(0));
	
	clock_t s,e;
	s = clock();
	P.previous_r = previous_r;
	P.eval1 = evaluate_vector(divisors_quot,x);
	F rand = mimc_hash(previous_r,P.eval1);
	P.eval2 = evaluate_vector(dividents_cond,x);
	rand = mimc_hash(rand,P.eval2);
	
	if(F(1<<Q)*P.eval2 - P.eval1 != final_eval){
		printf("I/O Error gini sumcheck1\n");
		exit(-1);
	}
	vector<F> beta1,beta2,beta3;
	precompute_beta(x,beta1);
	beta2 = beta1;
	beta3 = beta1;

	P.tP1 = _generate_3product_sumcheck_proof(quotients,divisors,beta1,rand);
	verify_3product_sumcheck(P.tP1,x,P.tP1.c_poly[0].eval(F(0)) + P.tP1.c_poly[0].eval(F(1)));

	if(P.tP1.c_poly[0].eval(F(0)) + P.tP1.c_poly[0].eval(F(1)) != P.eval1){
		printf("Error in gini sumcheck1--1\n");
		exit(-1);
	}
	P.tP2 = _generate_3product_sumcheck_proof(cond,dividents,beta2,P.tP1.final_rand);
	verify_3product_sumcheck(P.tP2,x,P.tP2.c_poly[0].eval(F(0)) + P.tP2.c_poly[0].eval(F(1)));
	if(P.tP2.c_poly[0].eval(F(0)) + P.tP2.c_poly[0].eval(F(1)) != P.eval2){
		printf("Error in gini sumcheck1--2\n");
		exit(-1);
	}
	vector<F> eval_point1 = P.tP2.randomness[0];
	P.cond_eval1 = P.tP2.vr[0];
	P.dividents_eval = eval_point1;

	P.tP3 = _generate_3product_sumcheck_proof(cond_inv,N,beta3,P.tP2.final_rand);
	verify_3product_sumcheck(P.tP3,x,P.tP3.c_poly[0].eval(F(0)) + P.tP3.c_poly[0].eval(F(1)));
	if(P.tP3.c_poly[0].eval(F(0)) + P.tP3.c_poly[0].eval(F(1)) != F(0)){
		printf("Error in gini sumcheck1--3\n");
		exit(-1);
	}
	P.cond_eval2 = F(1) - P.tP3.vr[0];

	vector<F> eval_point2 = P.tP3.randomness[0];
	

	beta1.clear();
	beta2.clear();
	precompute_beta(eval_point1,beta1);
	precompute_beta(eval_point2,beta2);
	
	P.a = generate_randomness(2,P.tP3.final_rand);
	
	
	for(int i = 0; i < beta1.size(); i++){
		beta1[i] = P.a[0]*beta1[i] + P.a[1]*beta2[i];
	}
	
	
	P.sP = generate_2product_sumcheck_proof(cond2,beta1,P.a[1]);
	verify_2product_sumcheck(P.sP,P.sP.q_poly[0].eval(0) + P.sP.q_poly[0].eval(1));

	if(P.sP.q_poly[0].eval(F(0)) + P.sP.q_poly[0].eval(F(1)) != P.a[0]*P.cond_eval1 + P.a[1]*P.cond_eval2){
		printf("Error in gini sumcheck1--4\n");
		exit(-1);
	}

	P.cond_eval3 = P.sP.vr[0];
	beta1.clear();
	vector<F> randomness = P.sP.randomness[0];
	
	precompute_beta(randomness,beta1);
	
	P.tP4 = _generate_3product_sumcheck_proof(N2,inverses,beta1,P.sP.final_rand);
	verify_3product_sumcheck(P.tP4,randomness,P.tP4.c_poly[0].eval(F(0)) + P.tP4.c_poly[0].eval(F(1)));
	if(P.tP4.c_poly[0].eval(F(0)) + P.tP4.c_poly[0].eval(F(1)) != P.cond_eval3){
		printf("Error in gini sumcheck1--5\n");
		exit(-1);
	} 
	e = clock();
	P.final_rand = P.tP4.final_rand; 
	printf("Gini sumcheck 1 : %lf\n",(float)(e-s)/(float)CLOCKS_PER_SEC);
	return P;
}

gini_sumcheck2_proof gini_sumcheck_2(vector<F> &input, F previous_r, vector<F> x_dividents, vector<F> x_divisors, F dividents_eval,F divisors_eval, int nodes, int attr, int bin_size){
	
	vector<F> N(nodes*attr*2*bin_size);
	vector<F> gini_indexes(nodes*attr*4*bin_size);
	vector<F> N0(nodes*attr*bin_size),N1(nodes*attr*bin_size),N_sum(2*nodes*attr*bin_size);
	vector<F> divisors(nodes*attr*2*bin_size),dividents(nodes*attr*2*bin_size);	
	vector<F> square_N(nodes*attr*2*bin_size);
	vector<F> pairwise_prod(nodes*attr*2*bin_size);
	gini_sumcheck2_proof P;
	vector<vector<F>> gini_partitions(2);
	gini_partitions[0].resize(nodes*attr*2*bin_size);
	gini_partitions[1].resize(nodes*attr*2*bin_size);
	
	int counter = 0;
	for(int i = counter; i <counter+ nodes*attr*2*bin_size; i++){
		N[i-counter] = input[i];
	}
	counter += nodes*attr*2*bin_size;
	for(int i = counter; i < counter + nodes*attr*4*bin_size; i++){
		gini_indexes[i - counter] = input[i];
	}
	counter += nodes*attr*4*bin_size;
	for(int i = counter; i < counter + nodes*attr*2*bin_size; i++){
		divisors[i - counter] = input[i];
	}
	counter += nodes*attr*2*bin_size;
	for(int i = counter; i < counter + nodes*attr*2*bin_size; i++){
		dividents[i - counter] = input[i];
	}
	
	for(int i = 0; i < nodes*attr*2*bin_size; i++){
		gini_partitions[0][i] = gini_indexes[2*i];
		gini_partitions[1][i] = gini_indexes[2*i+1];	
	}
	for(int i = 0; i < square_N.size(); i++){
		square_N[i] = N[i]*N[i];
		pairwise_prod[i] = gini_indexes[2*i]*gini_indexes[2*i+1];
	}

	for(int i = 0; i < N0.size(); i++){
		N0[i] = N[2*i];
		N1[i] = N[2*i+1];
		N_sum[2*i] = N0[i]+N1[i];	
		N_sum[2*i+1] = N0[i]+N1[i];	
	}
	//for(int i = 0; i < divisors.size(); i++){
	//	divisors[i] = N[i]*N_sum[i];
	//}

	pad_vector(divisors);
	pad_vector(dividents);
	pad_vector(N);
	pad_vector(N0);
	pad_vector(N1);
	pad_vector(N_sum);
	pad_vector(gini_indexes);
	pad_vector(gini_partitions[0]);
	pad_vector(gini_partitions[1]);
	pad_vector(square_N);
	pad_vector(pairwise_prod);

	//vector<F> randomness = generate_randomness((int)log2(divisors.size()),F(0));

	
	vector<F> beta,beta1,beta2,beta3;
	precompute_beta(x_dividents,beta);

	clock_t s,e;
	s = clock();
	P.previous_r = previous_r; 
	//F divisors_eval = evaluate_vector(divisors,randomness);
	//F dividents_eval = evaluate_vector(dividents,randomness);
	P.square_N_eval = evaluate_vector(square_N,x_dividents);
	P.pairwise_prod_eval = evaluate_vector(pairwise_prod,x_dividents);
	F rand = mimc_hash(previous_r,P.square_N_eval);
	rand = mimc_hash(rand,P.pairwise_prod_eval);
	if(dividents_eval != P.square_N_eval - F(2)*P.pairwise_prod_eval){
		printf("Error in gini sumcheck2--0.5\n");
	}

	// Sumcheck for divisors
	vector<F> N_1 = N;
	precompute_beta(x_divisors,beta1);
	P.tP1 = _generate_3product_sumcheck_proof(N_1,N_sum,beta1,rand);
	verify_3product_sumcheck(P.tP1,x_dividents,P.tP1.c_poly[0].eval(F(0)) + P.tP1.c_poly[0].eval(F(1)));
	
	if(divisors_eval != P.tP1.c_poly[0].eval(F(0))+P.tP1.c_poly[0].eval(F(1))){
		printf("Error in gini sumcheck2--0.75\n");
		exit(-1);
	}
	vector<F> randomness;
	for(int i = 1; i < P.tP1.randomness[0].size(); i++){
		randomness.push_back(P.tP1.randomness[0][i]);
	}
	P.eval1_N0 = evaluate_vector(N0,randomness);
	rand = mimc_hash(P.tP1.final_rand,P.eval1_N0);
	P.eval1_N1 = evaluate_vector(N1,randomness);
	rand = mimc_hash(rand,P.eval1_N1);
	P.eval1_N = P.tP1.vr[0];
	if(P.eval1_N0 + P.eval1_N1 != P.tP1.vr[1]){
		printf("Error in gini sumcheck2--1\n");
		exit(-1);
	}
	vector<F> t_x;
	for(int i = 1; i < P.tP1.randomness[0].size(); i++){
		t_x.push_back(P.tP1.randomness[0][i]);
	}
	vector<F> beta_aggr1,beta_aggr2((1<<P.tP1.randomness[0].size()),F(0)),beta_aggr3((1<<P.tP1.randomness[0].size()),F(0)),temp_beta;
	vector<F> beta_temp;
	precompute_beta(P.tP1.randomness[0],beta_aggr1);
	precompute_beta(t_x,beta_temp);
	for(int i = 0; i < beta_temp.size(); i++){
		beta_aggr2[2*i] = beta_temp[i];
		beta_aggr3[2*i+1] = beta_temp[i];
	}
	// Sumchecks for dividents
	beta2 = beta;
	vector<F> N_2 = N;
	N_1 = N;
	P.tP2 = _generate_3product_sumcheck_proof(N_1,N_2,beta2,rand);
	verify_3product_sumcheck(P.tP2,x_dividents,P.tP2.c_poly[0].eval(F(0)) + P.tP2.c_poly[0].eval(F(1)));
	
	if(P.tP2.c_poly[0].eval(F(0)) + P.tP2.c_poly[0].eval(F(1)) != P.square_N_eval){
		printf("Error in gini sumcheck2--2\n");
		exit(-1);	
	}
	
	P.eval2_N = P.tP2.vr[0];
	vector<F> beta_aggr4;
	precompute_beta(P.tP2.randomness[0],beta_aggr4);

	beta3 = beta;
	P.tP3 = _generate_3product_sumcheck_proof(gini_partitions[0],gini_partitions[1],beta3,P.tP2.final_rand);
	verify_3product_sumcheck(P.tP3,x_dividents,P.tP3.c_poly[0].eval(F(0)) + P.tP3.c_poly[0].eval(F(1)));
	
	if(P.tP3.c_poly[0].eval(F(0)) + P.tP3.c_poly[0].eval(F(1)) != P.pairwise_prod_eval){
		printf("Error in gini sumcheck2--3\n");
		exit(-1);	
	}

	P.r1 = generate_randomness(4,P.tP3.final_rand);
	vector<F> final_beta_aggr(beta_aggr4.size());
	
	for(int i = 0; i < final_beta_aggr.size(); i++){
		final_beta_aggr[i] = P.r1[0]*beta_aggr1[i] + P.r1[1]*beta_aggr2[i] + P.r1[2]*beta_aggr3[i]+P.r1[3]*beta_aggr4[i];
	}
	
	P.gini_eval1 = P.tP3.vr[0];
	P.gini_eval2 = P.tP3.vr[1];
	
	beta_aggr1.clear();
	beta_aggr2.clear();
	temp_beta.clear();
	precompute_beta(P.tP3.randomness[0],temp_beta);
	beta_aggr1.resize(2*temp_beta.size(),F(0));
	beta_aggr2 =  beta_aggr1;
	for(int i = 0; i < temp_beta.size(); i++){
		beta_aggr1[2*i] = temp_beta[i];
		beta_aggr2[2*i+1] = temp_beta[i];
	}
	

	P.sP1 = generate_2product_sumcheck_proof(N,final_beta_aggr,P.r1[3]);
	verify_2product_sumcheck(P.sP1,P.sP1.q_poly[0].eval(0) + P.sP1.q_poly[0].eval(1));
	if(P.sP1.q_poly[0].eval(0) + P.sP1.q_poly[0].eval(1) != P.r1[0]*P.eval1_N + P.r1[1]*P.eval1_N0 + P.r1[2]*P.eval1_N1+P.r1[3]*P.eval2_N){
		printf("Error in gini sumcheck2--4\n");
		exit(-1);			
	}
	// The N evaluation equals to Gini(x,0) + Gini(x,1);
	
	temp_beta.clear();

	vector<F> x1,x2;
	
	precompute_beta(P.sP1.randomness[0],temp_beta);
	beta_aggr3.clear();
	beta_aggr3.resize(2*temp_beta.size(),F(0));
	beta_aggr4 = beta_aggr3;

	for(int i = 0; i < temp_beta.size(); i++){
		beta_aggr3[2*i] = temp_beta[i];
		beta_aggr4[2*i + 1] = temp_beta[i];
	}

	x1.push_back(0);
	x2.push_back(1);
	for(int i = 0; i < P.sP1.randomness[0].size(); i++){
		x1.push_back(P.sP1.randomness[0][i]);
		x2.push_back(P.sP1.randomness[0][i]);	
	}
	P.gini_eval3 = evaluate_vector(gini_indexes,x1);
	P.gini_eval4 = evaluate_vector(gini_indexes,x2);
	
	rand = mimc_hash(P.sP1.final_rand,P.gini_eval3);
	rand = mimc_hash(rand,P.gini_eval4);
	if(P.sP1.vr[0] != P.gini_eval3+P.gini_eval4){
		printf("Error in gini sumcheck2--5\n");
		exit(-1);
	}
	final_beta_aggr.clear();
	final_beta_aggr.resize(beta_aggr1.size());
	P.r2 = generate_randomness(4,rand);
	for(int i = 0; i < final_beta_aggr.size(); i++){
		final_beta_aggr[i] = P.r2[0]*beta_aggr1[i] + P.r2[1]*beta_aggr2[i] + P.r2[2]*beta_aggr3[i]+P.r2[3]*beta_aggr4[i];
	}
	P.sP2 = generate_2product_sumcheck_proof(gini_indexes,final_beta_aggr,P.r2[3]);
	verify_2product_sumcheck(P.sP2,P.sP2.q_poly[0].eval(0) + P.sP2.q_poly[0].eval(1));
	
	if(P.sP2.q_poly[0].eval(0) + P.sP2.q_poly[0].eval(1) != P.r2[0]*P.gini_eval1 + P.r2[1]*P.gini_eval2 + P.r2[2]*P.gini_eval3+P.r2[3]*P.gini_eval4){
		printf("Error in gini sumcheck2--6\n");
		exit(-1);			
	}	
	e = clock();
	printf("Gini sumcheck 2 : %lf\n",(float)(e-s)/(float)CLOCKS_PER_SEC);
	
	return P;
}

struct proof prove_bit_decomposition(vector<F> bits, vector<F> num, int domain){
	//int domain = 256;
	vector<F> powers;
	powers.push_back(F(1));
	for(int i = 1; i < domain; i++){
		powers.push_back(F(2)*powers[i-1]);
	}

	//check_integrity(bits,num,powers);


	clock_t start,end;
			
	start = clock(); 
	vector<vector<F>> M = generate_bit_matrix(bits,domain);
	vector<F> r1 = generate_randomness(int(log2(num.size())),F(0));
	vector<F> v1 = prepare_matrix((M),r1);
	
	struct proof Pr1 = generate_2product_sumcheck_proof(v1,powers,r1[r1.size()-1]);
	verify_2product_sumcheck(Pr1,Pr1.q_poly[0].eval(0) + Pr1.q_poly[0].eval(1));
	
	vector<F> r2 = generate_randomness(int(log2(bits.size())),F(0));
	vector<F> beta; 
	precompute_beta(r2,beta);
	
	vector<F> inv_bits;
	for(int i  = 0; i < bits.size(); i++){
		inv_bits.push_back(F(1) - bits[i]);
	}
	
	struct proof Pr2 = generate_3product_sumcheck_proof(beta,bits,inv_bits,r2[r2.size()-1]);
	
	end = clock();
	

	struct proof Pr;
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	Pr.randomness.push_back(Pr1.randomness[0]);
	Pr.randomness.push_back(Pr2.randomness[0]);
	Pr.vr.insert(Pr.vr.end(),Pr1.vr.begin(),Pr1.vr.end());
	Pr.vr.insert(Pr.vr.end(),Pr2.vr.begin(),Pr2.vr.end());
	Pr.q_poly = Pr1.q_poly;
	Pr.c_poly = Pr2.c_poly;
	Pr.type = RANGE_PROOF;
	return Pr;

}