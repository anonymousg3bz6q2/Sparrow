#include "config_pc.hpp"
#include "mimc.h"
#include "utils.hpp"
#include "prover.h"
#include "Poly_Commit.h"

void verify_stream_3product_sumcheck(proof_stream P, vector<F> beta, F sum);
void verify_3product_sumcheck(proof P, vector<F> beta, F sum);
void verify_2product_sumcheck(proof P, F sum);
void verify_stream_2product_sumcheck(proof_stream P, F sum);