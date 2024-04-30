#include "config_pc.hpp"
#include "GKR.h"
#include "mimc.h"
#include "utils.hpp"
#include "space_efficient_sumcheck.h"
#include "Poly_Commit.h"

void verify_stream_3product_sumcheck(proof_stream P, vector<F> beta, F sum);
void verify_3product_sumcheck(proof P, vector<F> beta, F sum);
void verify_2product_sumcheck(proof P, F sum);
void verify_stream_2product_sumcheck(proof_stream P, vector<vector<F>> beta, vector<F> a, F sum);
void verify_stream_3product_batch(proof_stream P, vector<F> beta, vector<F> a,vector<F> v);