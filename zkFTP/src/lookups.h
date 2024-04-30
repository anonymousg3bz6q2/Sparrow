#pragma once

#include "config_pc.hpp"
#include "sumcheck.h"
#include "utils.hpp"
#include "GKR.h"



lookup_proof lookup_range_proof(vector<F> input,F previous_r ,int range);
lookup_proof lookup_range_proof_streaming( F previous_r, int range);


void test_lookup_commitment_streaming(int range);