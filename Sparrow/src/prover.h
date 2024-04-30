#pragma once

#include "circuit.h"
#include <vector>
#include <ctime>
#include <algorithm>
#include <memory>
#include "config_pc.hpp"
#include "polynomial.h"
#include "mimc.h"
#include "GKR.h"

using std::unique_ptr;



struct proof{
	int type;
	vector<vector<F>> randomness;
	vector<quadratic_poly> q_poly;
	vector<cubic_poly> c_poly;
	vector<F> output;
	vector<F> vr;
	vector<F> gr;
	vector<F> liu_sum;
	vector<vector<F>> sig;
	vector<vector<F>> final_claims_v;
	F divident,divisor,quotient,remainder;
	// Witnesses to make hash calclulation circuit less deep
	vector<vector<vector<F>>> w_hashes;
	vector<F> r,individual_sums;
	vector<vector<F>> Partial_sums;
	vector<quadratic_poly> q_poly1;
	vector<quadratic_poly> q_poly2;
	F final_rand;
	F final_sum;
	int K;

};

typedef struct proof proof;


struct recursion_proof{
	G1 comm1,comm2;
	F sum,sum1,sum2;
	proof P1,P2;
	vector<G1> Proof1,Proof2;
	vector<F> a1,a2;
};
typedef struct recursion_proof recursion_proof; 

struct proof_stream{
	F sum,new_sum;
    int c,size;
    vector<vector<F>> polynomials;
    recursion_proof RP;
	vector<F> randomness;
	vector<proof> P;
	vector<F> vr;
	vector<F> _a;

};


typedef struct proof_stream proof_stream; 

void prove_circuit(F commitment);