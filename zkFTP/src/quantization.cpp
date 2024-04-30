
#include <mcl/bls12_381.hpp>
#include <gmp.h>
#include <math.h>
#include "quantization.h"
#include "utils.hpp"
using namespace mcl::bn;

#define F Fr

#define F_ONE (Fr::one())
#define F_ZERO (Fr(0))
// Qunatization bandwidth (bits of quantized values)
// Exponentiation constant for computing e^x using the formula (1 + x/m)^m
vector<F> q_table;

void q_table_init(){
	for(int i = 0; i < 1ULL<<16; i++){
		q_table.push_back(F(i));
	}
}

F quantize(float num){

	return F((long long int)(num * (1<<Q)));
}

float dequantize(F num,int depth){
	F div = F(1);
	mpz_t num1,num2,num3;
	char buff[257];
	
	for(int i = 0; i < depth-1; i++){
		div = div*F(1<<Q);
	}
	mpz_init(num1);mpz_init(num2);mpz_init(num3);

	int n = num.getStr(buff,257,2);
	long int r_num;
	if(n == 255){
		num = F(-1)*num;
		num.getStr(buff,257,10);
		mpz_set_str(num1,buff,10);
		div.getStr(buff,257,10);
		mpz_set_str(num2,buff,10);
		mpz_fdiv_q(num3,num1,num2);
		r_num = mpz_get_si(num3);
		r_num = -r_num;
	}else{
		num.getStr(buff,257,10);
		mpz_set_str(num1,buff,10);
		div.getStr(buff,257,10);
		mpz_set_str(num2,buff,10);
		mpz_fdiv_q(num3,num1,num2);
		r_num = mpz_get_si(num3);
	}
	mpz_clear(num1);
	mpz_clear(num2);
	mpz_clear(num3);
	return (float)(r_num)/(float)(1<<Q);
}


vector<F> shift(F num1, int depth){
	char buff[257];
	mpz_t dividend,divisor,quotient,remainder;
	vector<F> r;
	mpz_init(dividend);mpz_init(divisor);mpz_init(quotient);mpz_init(remainder);
	F num2 = F(1);
	for(int i = 0; i < depth; i++){
		num2 = num2*F(1<<Q);
	}
	int n = num1.getStr(buff,257,2);
	if(n != 255){
		num1.getStr(buff,257,10);
		mpz_set_str(dividend,buff,10);
		num2.getStr(buff,257,10);
		mpz_set_str(divisor,buff,10);
		mpz_fdiv_q(quotient,dividend,divisor);
		
		mpz_get_str(buff,10,quotient);
		
		F q;
		bool v[1];
		q.setStr(v,buff,0);
		q.getStr(buff,256,10);
		
		//long int tmp = mpz_get_ui(quotient);
		//r.push_back(F(tmp));
		r.push_back(q);
		r.push_back(num2);
		//r.push_back(num1 - F(tmp)*num2);
		r.push_back(num1 - q*num2);
		return r;
	}
	else{
		num1 = F(0) - num1;
		num1.getStr(buff,257,10);
		mpz_set_str(dividend,buff,10);
		num2.getStr(buff,257,10);
		mpz_set_str(divisor,buff,10);
		mpz_fdiv_q(quotient,dividend,divisor);
		F q;
		bool v[1];
		
		mpz_get_str(buff,10,quotient);
		
		q.setStr(v,buff,0);
		
		//long int tmp = mpz_get_ui(quotient);
		
		//r.push_back(F(0) - (F(tmp) + F(1)));
		r.push_back(F(0) - (q + F(1)));
		r.push_back(num2);
		//r.push_back(num2 - (num1 - F(tmp)*num2));
		r.push_back(num2 - (num1 - q*num2));
		return r;
	}

}

F _shift_right(F num){
	/*
	char buff[256],temp_bits[256];
	for(int i = 0; i < 256; i++){
		temp_bits[i] = '0';
	}
	int n = num.getStr(buff,256,2);
	for(int j = n-17; j >= 0; j--){
        temp_bits[j] = buff[j];
		//if(buff[j] == '1'){
        //    temp_bits[n-1 - j] = one;
        //}
	}
	bool v[1];
	num.setStr(v,temp_bits,0);
	return num;
	*/
	return F(42322);
}

int _shift_int(F num1){
	int b1 = get_byte(0, num1);
	int b2 = get_byte(1, num1);
	if(b2*256+b1 >= 1<<16){
		printf("ERROR\n");	
	}
	return b2*256+b1;
}
F _shift(F num1){
	int b1 = get_byte(0, num1);
	int b2 = get_byte(1, num1);
	if(b2*256+b1 >= 1<<16){
		printf("ERROR\n");	
	}
	return q_table[b2*256+b1];
}

F _divide(F num1,F num2){
	char buff[257];
	mpz_t dividend,divisor,quotient;
	
	mpz_init(dividend);mpz_init(divisor);mpz_init(quotient);
	num1.getStr(buff,257,10);
	mpz_set_str(dividend,buff,10);
	num2.getStr(buff,257,10);
	mpz_set_str(divisor,buff,10);
	mpz_fdiv_q(quotient,dividend,divisor);
	
	F q;
	bool v[1];
		
	mpz_get_str(buff,10,quotient);
		
	q.setStr(v,buff,0);
	return q;
}


F divide(F num1,F num2){
	char buff[257];
	mpz_t dividend,divisor,quotient;
	
	mpz_init(dividend);mpz_init(divisor);mpz_init(quotient);

	int n1 = num1.getStr(buff,257,2);
	int n2 = num2.getStr(buff,257,2);
	if(n1 != 255 && n2 != 255 || n1 == 255 && n2 == 255){
		if(n1 == 255){
			num1 = F(-1)*num1;
			num2 = F(-1)*num2;
		}
		num1.getStr(buff,257,10);
		mpz_set_str(dividend,buff,10);
		num2.getStr(buff,257,10);
		mpz_set_str(divisor,buff,10);
		mpz_fdiv_q(quotient,dividend,divisor);
		//long int tmp = mpz_get_ui(quotient);

		F q;
		bool v[1];
		
		mpz_get_str(buff,10,quotient);
		
		q.setStr(v,buff,0);
		return q;
		//return F(tmp);
	}
	else{
		if(n1 == 255){
			num1 = F(-1)*num1;
		}
		else{
			num2 = F(-1)*num2;
		}
		num1.getStr(buff,257,10);
		mpz_set_str(dividend,buff,10);
		num2.getStr(buff,257,10);
		mpz_set_str(divisor,buff,10);
		mpz_fdiv_q(quotient,dividend,divisor);
		//long int tmp = mpz_get_ui(quotient);
		F q;
		bool v[1];
		
		mpz_get_str(buff,10,quotient);
		
		q.setStr(v,buff,0);
		return F(0)-q;

		//return F(-tmp);		
	}
	//return F(0);
}

F _sqrt(F x){
	F sqrt;
	mpz_t x_mpz,sqrt_mpz;
	bool v[1];
	char buff[257];
	mpz_init(x_mpz);
	mpz_init(sqrt_mpz);

	x.getStr(buff,257,10);
	mpz_set_str(x_mpz,buff,10);
	mpz_sqrt(sqrt_mpz,x_mpz);
	mpz_get_str(buff,10,sqrt_mpz);
	sqrt.setStr(v,buff,0);
	return 	sqrt;
}

F exp(F x){
	char buff[257];
	x = divide(x*F(1<<Q),quantize(M_exp));
	x.getStr(buff,257,10);
	F base = quantize(1) + x;
	for(int i = 0; i < (int)log2(M_exp); i++){
		base = base*base;
	}
	return base;
}


