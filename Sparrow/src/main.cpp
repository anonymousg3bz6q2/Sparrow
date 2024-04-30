#include <stdio.h>

//#include <mcl/bn256.hpp>
#include <mcl/bls12_381.hpp>
//#include <mcl/bn.h>

#include <polynomial.h>
#include <math.h>

#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include <time.h>
#include "mimc.h"
#include "utils.hpp"
#include <chrono>
#include <fcntl.h>
#include "witness_stream.h"
#include "GKR.h"
#include "prover.h"
#include "Poly_Commit.h"

int threads = 1,MAX_CHUNCK;
extern layeredCircuit C;
int recursion = 0;
int MAX_CHUNCK_COMM;
extern double verification_time;
extern int _proof_len;
int mod;
vector<unsigned int> preimage;
extern Comm pp_recursion;
vector<unsigned int> SHA;
vector<int> H;
vector<F> V_in;

void init_SHA(){
	for(int i = 0; i < 64; i++){
		SHA.push_back((random()%(1ULL<<32)));
	}
	for(int i = 0; i < 8; i++){
		H.push_back((random()%(1ULL<<32)));
	}
}


int main(int argc, char *argv[]){
	initPairing(mcl::BN_SNARK1);
	init_hash();
    MAX_CHUNCK = 1024*1024*4;
	MAX_CHUNCK_COMM = 1ULL<<20;
	vector<F> data;
	//generate_pp(pp_recursion,15);
	MIPP_Comm pp;
	V_in.resize(1ULL<<10);
	for(int i = 0; i < V_in.size(); i++){
		V_in[i].setByCSPRNG();
	}
	
	mod = (atoi(argv[1]));
	stream_descriptor input_fd;

	if(mod == 1){
		int input = 1ULL<<(atoi(argv[2]));
		int circuits = 1ULL<<(atoi(argv[3]));
		int depth = atoi(argv[4]);
		
		MAX_CHUNCK = 1ULL<<(atoi(argv[5]));
	 	input_fd.pos = 0;input_fd.name = "input";input_fd.size = (circuits*input)/depth;
		test_gkr(data, data, input/depth, circuits, depth);
	}else if(mod == 2){
		init_SHA();
		for(int i = 0; i < 16; i++){
			preimage.push_back(rand()%(1ULL<<32));
		}
		int hashes = atoi(argv[2]);
 		MAX_CHUNCK = 1ULL<<(atoi(argv[3]));
	 	input_fd.pos = 0;input_fd.name = "input";input_fd.size = hashes*(1<<14);
		test_sha256(data, data, hashes);
	
	}else if(mod == 3){
		int N  = 1ULL<<atoi(argv[2]);
		int circuits = 1ULL<<atoi(argv[3]);
		MAX_CHUNCK = 1ULL<<(atoi(argv[4]));
		printf("%d\n",MAX_CHUNCK);
	 	input_fd.pos = 0;input_fd.name = "input";input_fd.size = N*circuits;
		test_multree(data,data, N,circuits, 10);
	}else{
		printf("Invalid circuit\n");
		exit(-1);
	}

	MIPP_gen_stream(pp);
	G1 c;
	clock_t t1,t2;
	
	
	
	//test_m2m(data, data, depth, input/depth, circuits);
    
	//test_gkr(data, data, input/depth, circuits, depth);
	
	
	//stream_descriptor fd;fd.name = "circuit";fd.pos = 0;fd.size = 1ULL<<22;
    //MIPP_Comm(pp_)
    vector<G1> comm;
    F commitment = F(32);
	//MIPP_commit_stream(input_fd,input_fd.size,pp,comm);
	t1 = clock();
	prove_circuit(commitment);
	t2 = clock();
	//MIPP_open_stream(input_fd,input_fd.size,generate_randomness((int)log2(input_fd.size),F(3)),pp,comm);
	printf("GKR Prove time : %lf, V time : %lf , P size : %lf , %d\n", (double)(t2-t1)/(double)(CLOCKS_PER_SEC),verification_time,(double)_proof_len/1024.0,_proof_len);
	printf("PC Prove time : %lf, V time : %lf , P size : %lf\n", pp.prove_time,pp.verification_time,(double)pp.proof_size/1024.0);
	
	
	
		//vector<F> Hg_1,;
	
	return 0;
}
