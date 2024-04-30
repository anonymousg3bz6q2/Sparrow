#include "pol_verifier.h"
#include "GKR.h"


extern int recursion;
extern size_t MAX_CHUNCK;
double verification_time = 0.0;
int proof_len = 0;

extern Comm pp_recursion;

void verify_3product_sumcheck(proof P, vector<F> beta, F sum){
	clock_t t1,t2;
	F a;
	t1 = clock();
	proof_len += sizeof(P.randomness[0][0])*(4*P.randomness[0].size() + 2);
	for(int i = 0; i < P.randomness[0].size(); i++){
		a.setByCSPRNG();a.setByCSPRNG();a.setByCSPRNG();a.setByCSPRNG();a.setByCSPRNG();
		if(P.c_poly[i].eval(F_ZERO) + P.c_poly[i].eval(F_ONE) != sum){
			printf("Error in 3prod verification %d\n",i);
		}
		sum = P.c_poly[i].eval(P.randomness[0][i]);
	}
	F v3 = F(1);

	if(beta.size() != P.randomness[0].size() && beta.size() != 0){
		printf("Error in beta size verification\n");
		exit(-1);
	}
	for(int i = 0; i < beta.size(); i++){
		v3 *= ((beta[i]*P.randomness[0][i]) + ((F_ONE - beta[i])*(F_ONE-P.randomness[0][i])));
	}	
	t2 = clock();
	verification_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;


}

void verify_2product_sumcheck(proof P, F sum){
	clock_t t1,t2;
	t1 = clock();
	F a;
	proof_len += sizeof(P.randomness[0][0])*(3*P.randomness[0].size() + 2);
	for(int i = 0; i < P.randomness[0].size(); i++){
		a.setByCSPRNG();a.setByCSPRNG();a.setByCSPRNG();a.setByCSPRNG();
		if(P.q_poly[i].eval(F_ZERO) + P.q_poly[i].eval(F_ONE) != sum){
			printf("Error in 2prod verification %d \n",i);
		}
		sum =  P.q_poly[i].eval(P.randomness[0][i]);
	}
	t2 = clock();
	verification_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
}

void sum_poly_extended(F sum, vector<F> poly, int c){
	
	for(int i = (poly.size() - (1<<c)); i < poly.size(); i++){
        sum -= poly[i];
    }
	if(sum != F(0)){
        printf("Verification Error \n");
        //exit(-1);
    }
}

void sum_poly(F sum, vector<F> poly, int c){
	for(int i = 0; i < poly.size()/2; i++){
		sum -= poly[2*i];
	}
	if(sum != 0){
		printf("Error in stream sum_poly\n");
	}

}

F evaluate_poly_extended(vector<F> poly, F r, int c){
	vector<F> L = compute_lagrange_coeff(getRootOfUnit(c),r,1ULL<<(c));
	F sum = F(0);
	int idx = 0;
	
	for(int i = 0; i < 1<<c; i++){
		for(int j = i+1; j < 1<<c; j++){
			sum += L[i]*L[j]*poly[idx];
			idx++;
		}
	}
	for(int i = 0; i < 1<<c; i++){
		sum += L[i]*L[i]*poly[idx];
		idx++;
	}
	return sum;
}

F evaluate_poly(vector<F> poly, F r, int c){
	int degree = (int)log2(poly.size());
	vector<F> L = compute_lagrange_coeff(getRootOfUnit(degree),r,1ULL<<(degree));
	F sum = 0;
	for(int i = 0; i < L.size(); i++){
		sum += L[i]*poly[i];
	}
	return sum;
}


void verify_stream_3product_batch(proof_stream P, vector<F> beta, vector<F> a,vector<F> v){
	F sum = 0;
	for(int i = 0 ; i < a.size(); i++){
		sum += a[i]*v[i];
	}
	clock_t t1,t2;
	t1 = clock();

	int total_c = (int)log2(P.size/MAX_CHUNCK);
    int c = 4;
	if(c >= total_c){
        c = total_c;
    }else{
		c = (int)log2(log2(P.size/MAX_CHUNCK)) + 1;
	}
	
	/****=========****/
	proof_len += sizeof(P.polynomials[0][0])*(P.polynomials[0].size());
	/*******/
	sum_poly_extended(sum,P.polynomials[0],c);
	sum = evaluate_poly_extended(P.polynomials[0],P.randomness[0],c);

	int new_c = total_c -c;
	if(new_c != 0){
		if(new_c <= 4){
	
			sum_poly_extended(sum,P.polynomials[1],new_c);
			sum = evaluate_poly_extended(P.polynomials[1],P.randomness[1],new_c);
		}else{
				if(!recursion){
					proof_len += sizeof(P.polynomials[1][0])*(P.polynomials[1].size());
					sum_poly(sum,P.polynomials[1],new_c);
					sum = evaluate_poly(P.polynomials[1],P.randomness[1],new_c);
		
				}else{
					recursion_proof rP = P.RP;
					proof_len += sizeof(pp_recursion.C)*(rP.Proof1.size()+rP.Proof2.size() + 2);
					
					pp_recursion.C  = rP.comm1;
					pp_recursion.Proof = rP.Proof1;
					KZG_verify(rP.P1.randomness[0],rP.P1.vr[0],pp_recursion);
					pp_recursion.C  = rP.comm2;
					pp_recursion.Proof = rP.Proof2;
					KZG_verify(rP.P2.randomness[0],rP.P2.vr[0],pp_recursion);
					verify_2product_sumcheck(rP.P1,rP.sum1);
					verify_3product_sumcheck(rP.P2,rP.P1.randomness[0],rP.sum2);
					sum = rP.sum;
				}

		}
	}

	t2 = clock();
	verification_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;

	verify_3product_sumcheck( P.P[0],P.beta1, sum);
	
	vector<F> V1,V2;
	
	for(int i = 0; i < a.size(); i++){
		V1.push_back(P.P[0].vr[ 1 + 2*i ]);
		V2.push_back(P.P[0].vr[ 1 + 2*i + 1]);
	}

	sum = F(0);
	for(int i = 0; i < V1.size(); i++){
		sum += V1[i]*P.a[i]*P.a[P.a.size()-2];
		sum += V2[i]*P.a[i]*P.a[P.a.size()-1];
	}
	proof_len += sizeof(P.polynomials[0][0])*(2*a.size());
	verify_3product_sumcheck( P.P[1],P.beta2, sum);
}

void verify_stream_3product_sumcheck(proof_stream P, vector<F> beta, F sum){
	if(P.P.size() == 1){
		if(P.P[0].c_poly[0].eval(F_ZERO) +P.P[0].c_poly[0].eval(F_ONE) != sum){
            printf("Error in V\n");
            exit(-1);
        }
		verify_3product_sumcheck( P.P[0],beta, sum);
		return;
	}
		
	clock_t t1,t2;
	t1 = clock();
	int total_c = (int)log2(P.size/MAX_CHUNCK);
    int c = 4;
	if(c >= total_c){
        c = total_c;
    }else{
		c = (int)log2(log2(P.size/MAX_CHUNCK)) + 1;
	}
	/****=========****/
	proof_len += sizeof(P.polynomials[0][0])*(P.polynomials[0].size());
	/*******/
	sum_poly_extended(sum,P.polynomials[0],c);
	sum = evaluate_poly_extended(P.polynomials[0],P.randomness[0],c);

	int new_c = total_c -c;
	if(new_c != 0){
	
		if(new_c <= 4){
	
			sum_poly_extended(sum,P.polynomials[1],new_c);
			sum = evaluate_poly_extended(P.polynomials[1],P.randomness[1],new_c);
		}else{
				if(!recursion){
					proof_len += sizeof(P.polynomials[1][0])*(P.polynomials[1].size());
					sum_poly(sum,P.polynomials[1],new_c);
					sum = evaluate_poly(P.polynomials[1],P.randomness[1],new_c);
		
				}else{
					recursion_proof rP = P.RP;
					proof_len += sizeof(pp_recursion.C)*(rP.Proof1.size()+rP.Proof2.size() + 2);
					
					pp_recursion.C  = rP.comm1;
					pp_recursion.Proof = rP.Proof1;
					KZG_verify(rP.P1.randomness[0],rP.P1.vr[0],pp_recursion);
					pp_recursion.C  = rP.comm2;
					pp_recursion.Proof = rP.Proof2;
					KZG_verify(rP.P2.randomness[0],rP.P2.vr[0],pp_recursion);
					verify_2product_sumcheck(rP.P1,rP.sum1);
					verify_3product_sumcheck(rP.P2,rP.P1.randomness[0],rP.sum2);
					sum = rP.sum;
				}

		}
	}

	t2 = clock();
	verification_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;

	verify_3product_sumcheck( P.P[0],P.beta1, sum);
	sum = P.a[0]*P.P[0].vr[0] + P.a[1]*P.P[0].vr[1];
	verify_3product_sumcheck( P.P[1],P.beta2, sum);
	
}

void verify_stream_2product_sumcheck(proof_stream P, vector<vector<F>> beta, vector<F> a, F sum){
	if( P.P.size() == 1){
		if(P.P[0].q_poly[0].eval(F_ZERO) +P.P[0].q_poly[0].eval(F_ONE) != sum){
            printf("Error in V\n");
            exit(-1);
        }
		verify_2product_sumcheck( P.P[0], sum);
		for(int k = 0; k < beta.size(); k++){
			F v3 = F_ONE;
			for(int i = 0; i < beta.size(); i++){
				v3 *= ((beta[k][i]*P.P[0].randomness[0][i]) + ((F_ONE - beta[k][i])*(F_ONE-P.P[0].randomness[0][i])));
			}
		}
	
		return;
	}
	clock_t t1,t2;
	t1 = clock();

	
	int total_c = (int)log2(P.size/MAX_CHUNCK);
    int c = 4;
	if(c >= total_c){
        c = total_c;
    }else{
		c = (int)log2(log2(P.size/MAX_CHUNCK)) + 1;
	}
	
	sum_poly_extended(sum,P.polynomials[0],c);
	sum = evaluate_poly_extended(P.polynomials[0],P.randomness[0],c);
	
	/****=========****/
	
	proof_len += sizeof(P.polynomials[0][0])*(P.polynomials[0].size());
	
	
	/*******/
	
	int new_c = total_c -c;
	if(new_c != 0){
		if(new_c <= 4){
	
			sum_poly_extended(sum,P.polynomials[1],new_c);
			sum = evaluate_poly_extended(P.polynomials[1],P.randomness[1],new_c);
		}else{
			if(!recursion){
					proof_len += sizeof(P.polynomials[1][0])*(P.polynomials[1].size());
					sum_poly(sum,P.polynomials[1],new_c);
					sum = evaluate_poly(P.polynomials[1],P.randomness[1],new_c);
		
				}else{
						recursion_proof rP = P.RP;
					proof_len += sizeof(pp_recursion.C)*(rP.Proof1.size()+rP.Proof2.size() + 2);
					
					pp_recursion.C  = rP.comm1;
					pp_recursion.Proof = rP.Proof1;
					KZG_verify(rP.P1.randomness[0],rP.P1.vr[0],pp_recursion);
					pp_recursion.C  = rP.comm2;
					pp_recursion.Proof = rP.Proof2;
					KZG_verify(rP.P2.randomness[0],rP.P2.vr[0],pp_recursion);
					verify_2product_sumcheck(rP.P1,rP.sum1);
					verify_3product_sumcheck(rP.P2,rP.P1.randomness[0],rP.sum2);
					sum = rP.sum;
				}
			
		}
	}
	t2 = clock();
	verification_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;

	verify_2product_sumcheck( P.P[0], sum);
	sum = P.a[0]*P.P[0].vr[0] + P.a[1]*P.P[0].vr[1];
	verify_3product_sumcheck( P.P[1],P.beta2, sum);
	vector<F> randomness = P.P[1].randomness[0];
	randomness.insert(randomness.end(),P.P[0].randomness[0].begin(),P.P[0].randomness[0].end());
	t1 = clock();

	for(int k = 0 ; k < beta.size(); k++){
		F v3 = F_ONE;
		for(int i = 0; i < beta.size(); i++){
			v3 *= ((beta[k][i]*P.P[0].randomness[0][i]) + ((F_ONE - beta[k][i])*(F_ONE-P.P[0].randomness[0][i])));
		}
	}
	t2 = clock();
	verification_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;


}