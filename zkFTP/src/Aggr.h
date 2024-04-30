#include "config_pc.hpp"


struct FLTrust{
	vector<vector<F>> G,tG;
	vector<F> Prod,Norms,quotients,remainders,relu_bits,most_significant_bits,output,aggr,remainder_bits,quotients_bits,offset;

};

struct FoolsGold{
	vector<vector<F>> G,CS,CS_temp,sqrt_matrix,new_CS;
	vector<F> sqrt,sqrt_left,sqrt_right,sqrt_left_input,sqrt_right_input;
	vector<F> sqrt_left_bits,sqrt_right_bits,CS_remainders,max_1,max_1_difference;
	vector<F> max_1_bits,pardon_div,pardon_remainders,pardon_bits,max_2,max_2_bits;
	vector<F> max_2_difference,CS_remainders_bits,identity_elements;

	vector<F> shifted_max,shifted_max_remainders,max_3_difference,max_3_bits;
	vector<F> normalized_values,normalized_values_remainders,normalized_bits;
	vector<F> log_left,log_right,log_input_2,log_input_1;
	vector<F> shift_bits,logit,output,most_significant_bits,relu_bits;
	vector<F> inv_relu_bits,inv_most_significant_bits,weights,aggr;
 
	F max_val;
};

typedef struct FLTrust;

typedef struct FoolsGold;


FLTrust fltrust(int N, int M);
FoolsGold foolsgold(int N, int M);