#ifndef POLY_COMMIT_H
#define POLY_COMMIT_H

#include "config_pc.hpp"
#include "witness_stream.h"

struct Comm{
	vector<G1> pp1,binary_pp1,subvector_pp1,ipp_pp1;
	vector<vector<G1>> pp1_cached;
	vector<G2> pp2,ipp_pp2;
	vector<G1> Proof;
	vector<F> secret;
	vector<vector<G1>> base,binary_base,subvector_base;
	vector<string> base_name;
	string pp_string_name;
	G1 G,C,subvector_C;
	G2 H;
	int fp;
	int bit_size;
};

struct Vesta_Comm{
	vector<struct Comm> comm;
	vector<struct Comm> aux_comm;
	vector<vector<G1>> commitments;
};


struct MIPP_Proof{
	F x,x_inv;
	GT GT_L,GT_R;
	G1 G_L,G_R,Z_L,Z_R;

};
typedef struct MIPP_Proof;


struct MIPP_Comm{
	vector<G1> pp1;
	vector<G2> pp2;
	vector<vector<G1>> precomputed_pp;
	vector<vector<G1>> base;
	vector<vector<G1>> pp1_cached;
	vector<G1> Commitments;
	vector<G1> Proof;
	vector<G2> u;
	vector<G1> w;
	vector<F> r2;
	vector<MIPP_Proof> M_Proof;
	G1 G,C,Agg_C;
	G2 H;
	GT C_T;
	double commit_time,prove_time,verification_time;
	int proof_size;
	int chunck_size;
	int bit_size,commit_bit_size;	
	bool precompute;
	bool bits;
};

struct single_SVL_Proof{
	int nodes_bitsize,bitsize;
	vector<G1> plaintext_proofs;
	GT C1,C2,Cb1,Cb2,Cz1,Cz2,C_debug;
	F c;
	vector<G1> A,Ab;
	vector<G2> B,Bb;
	// Bit proofs 
	GT Cbb1,Cbb2,C_minus,t1,t2;
	F z,r;
	vector<F> y;

};

struct aggregation_proof{
	vector<GT> C_I;
	vector<vector<G2>> H;
	vector<G1> Y;
	GT C_y;
	float proving_time,verification_time,proof_size;
};

typedef struct aggregation_proof;

typedef struct Vesta_Comm;
typedef struct MIPP_Comm;
typedef struct Comm;
typedef struct single_SVL_Proof;
void commit(vector<F> poly,struct Comm &commitment);
void verify(vector<F> x, F y,struct Comm &commitment);
void open(vector<F> poly, vector<F> x, struct Comm &commitment);
void KZG_open_streaming(int fp1,vector<F> x, struct Comm &commitment, size_t size);
void generate_pp(struct Comm &commitment,int bit_size);
void test_MIPP();

void generate_streaming_pp(struct Comm &commitment,int bit_size);


void MIPP_commit(vector<F> &poly, MIPP_Comm &commitment,vector<G1> &commitments);
void MIPP_open(vector<F> &poly,vector<F> x, MIPP_Comm &commitment,vector<G1> commitments);
void MIPP_gen(int bit_size,MIPP_Comm &commitment, bool precompute,bool bits);

void MIPP_verify( F y, MIPP_Comm &commitment);
void MIPP_fold_commit(vector<F> f1, vector<F> bits, MIPP_Comm &commitment);
void MIPP_predicate_commit(vector<int> &mapping, MIPP_Comm &commitment);
void MIPP_predicate_open(vector<int> mapping, vector<F> x, MIPP_Comm &commitment);
void copy_pp(MIPP_Comm &commitment1,MIPP_Comm &commitment2);
vector<vector<G1>> hyperproofs_openall(vector<F> poly,Comm &commitment,int nodes);
void generate_pp_hyperproofs(struct Comm &commitment,int bit_size,int subvector_size);
void Vesta_OpenAll(vector<F> poly, Vesta_Comm &commitment,int level);
void generate_pp_vesta(struct Vesta_Comm &commitment,int bit_size);
void Vesta_Commit(vector<F> poly, Vesta_Comm &commitment, int level);
void VestaOpenAll(vector<F> poly);
void subvector_commit(vector<F> subvector, struct Comm &commitment);
void subvector_open(vector<F> poly, vector<F> x, struct Comm &commitment);
single_SVL_Proof single_SVL_prove(vector<vector<F>> table, vector<vector<G1>> cached_quotients,vector<F> x,int pos,Comm commitment);
vector<vector<G1>> SVL_commit(vector<F> table, Comm &commitment,int nodes);
void single_SVL_verify(single_SVL_Proof Proof,vector<F> x,F y,Comm commitment);
int TIPP(vector<G1> A, vector<G2> B, vector<G1> w, vector<G2> u, GT C1, GT C2, GT P , F s);
int MIPP(vector<G1> A, vector<G2> u,vector<F> b, vector<G1> w, GT T, G1 U,G1 U2);
GT compute_pairing_commitment(vector<G1> &x, vector<G2> &ck);
aggregation_proof Aggregate(vector<vector<G1>> P, vector<G1> w, vector<G2> u, vector<vector<F>> x, vector<F> y, G2 H, int lookups, Comm pp);
void KZG_open(vector<F> poly, vector<F> x, struct Comm &commitment);
void KZG_verify(vector<F> x, F y, struct Comm &commitment);
vector<G1> get_proof(vector<F> f_i, vector<F> x, int pos,vector<vector<int>> &indexes, int M, int N, vector<vector<G1>> cached_quotients, Comm commitment );
G1 compute_G1_commitment( vector<G1> &ck,vector<F> &x);
void MIPP_commit_stream(stream_descriptor fd, int size, MIPP_Comm &commitment, vector<G1> &commitments);
void MIPP_open_stream(stream_descriptor fd, int size,vector<F> x, MIPP_Comm &commitment, vector<G1> commitments);
void MIPP_gen_stream(MIPP_Comm &commitment);
#endif