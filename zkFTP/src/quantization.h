#pragma once
#include <mcl/bls12_381.hpp>
#include "config_pc.hpp"
#define F Fr
#define Q 22
#define M_exp 8

using namespace mcl::bn;


F quantize(float num);
F exp(F num);
vector<F> shift(F num1, int depth);
F divide(F num1,F num2);
F _divide(F num1,F num2);
F _sqrt(F x);
float dequantize(F num,int depth);
F _shift(F num);
int _shift_int(F num1);
void q_table_init();
F _shift_right(F num);
