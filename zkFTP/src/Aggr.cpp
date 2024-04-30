#include "config_pc.hpp"
#include "quantization.h"
#include "utils.hpp"
#include "Aggr.h"
#include "math.h"
#include <numeric>
#define LENET 1
#define VGG 2
#define TEST 3
#define AlexNet 4
#define mAlexNet 5


extern unsigned long int mul_counter;

extern int partitions;

bool fake = true;

void init_grad(int N, int M, vector<vector<F>> &G){
	G.resize(N);
	for(int i = 0; i < N; i++){
		vector<float> temp;
		float num = 0.0;
		for(int j = 0; j < M; j++){
			float r = 0.1 + 0.9*(float)rand() / (float)RAND_MAX;
			temp.push_back(r);
			num += r*r;
		}
		for(int j = 0; j < M; j++){
			G[i].push_back(quantize(temp[j]/sqrt(num)));
		}
	}
}

F F_inner_product(vector<F> &v1, vector<F> &v2){
	F sum = F(0);
	for(int i = 0; i < v1.size(); i++){
		sum += v1[i]*v2[i];
	}
	return sum;
}

float float_inner_product(vector<float> &v1, vector<float> &v2){
	float sum = 0.0;
	for(int i = 0; i < v1.size(); i++){
		sum += v1[i]*v2[i];
	}
	return sum;
}

vector<F> inner_product(vector<vector<F>> G, vector<F> tG){
	vector<F> products;
	for(int i = 0; i < G.size(); i++){
		F sum = F(0);
		for(int j = 0; j < G[0].size(); j++){
			sum += G[i][j]*tG[j];
		}
		products.push_back(sum);
	}

	return products;
}

vector<F> norm_test(vector<vector<F>> G){
	vector<F> norms;
	for(int i = 0; i < G.size(); i++){
		F sum = F(0);
		for(int j = 0; j < G[i].size(); j++){
			sum += G[i][j]*G[i][j];
		}
		norms.push_back(sum);
	}
	return norms;
}

void FLTrust_aggregate(FLTrust &data){
	data.aggr = inner_product(_transpose(data.G),data.output);
}

void norm(FLTrust &data, vector<F> norms){
	
	for(int i = 0; i < norms.size(); i++){
		data.quotients.push_back(divide(norms[i],F(1<<Q)));
		data.remainders.push_back(norms[i] - F(1<<Q)*data.quotients[i]);
		data.offset.push_back(F(1<<Q) - data.quotients[i]);
	}
	data.remainder_bits = prepare_bit_vector(data.remainders,Q);
	data.quotients_bits = prepare_bit_vector(data.offset,Q);
}

void relu(FLTrust &data, vector<F> inner_product){
	data.relu_bits = prepare_bit_vector(inner_product,256);
	for(int i = 0; i < inner_product.size(); i++){
		data.most_significant_bits.push_back(data.relu_bits[i*256+254]);
	}
	
	for(int i = 0; i < inner_product.size(); i++){
		data.output.push_back(inner_product[i]*(F(1)-data.most_significant_bits[i]));
	}
}
void relu(FoolsGold &data, vector<F> inner_product){
	data.relu_bits = prepare_bit_vector(inner_product,256);
	for(int i = 0; i < inner_product.size(); i++){
		data.most_significant_bits.push_back(data.relu_bits[i*256+254]);
	}
	
	for(int i = 0; i < inner_product.size(); i++){
		data.output.push_back(inner_product[i]*(F(1)-data.most_significant_bits[i]));
	}
}

FLTrust fltrust(int N, int M){
	FLTrust data;
	vector<vector<F>> G;
	// trusted gradient
	vector<vector<F>> tG;
	init_grad(N,M,G);
	init_grad(1,M,tG);
	data.G = G;
	data.tG = tG;
	data.Prod = inner_product(G,tG[0]);
	data.Norms = norm_test(G);
	relu(data,data.Prod);
	norm(data,data.Norms);
	FLTrust_aggregate(data);
	return data;
}


void generate_input(vector<vector<float>> &G_real, FoolsGold &data){
	if(!fake){

		vector<vector<float>> Temp(G_real.size());
		for(int i = 0; i < G_real.size(); i++){
			Temp[i].resize(G_real[i].size());
		}
		vector<vector<float>> Prod(G_real.size());
		for(int i = 0; i < Prod.size(); i++){
			Prod[i].resize(G_real.size());
		}
		for(int i = 0; i < G_real.size(); i++){
			for(int j = 0; j < G_real[i].size(); j++){
				Temp[i][j] = (float)rand() / (float)RAND_MAX;	
			}
		}
		for(int i = 0; i < G_real.size(); i++){
			for(int j = i; j < G_real.size(); j++){
				Prod[i][j] = float_inner_product(Temp[i],Temp[j]);
				Prod[j][i] = Prod[i][j];
			}
		}
		vector<float> max_vals(G_real.size());
		for(int i = 0; i < max_vals.size(); i++){
			max_vals[i] = 0.0;
			for(int j = 0; j < Prod.size(); j++){
				if(max_vals[i] < Prod[i][j]/(sqrt(Prod[i][i]*sqrt(Prod[j][j])))){
					max_vals[i] = Prod[i][j]/(sqrt(Prod[i][i]*sqrt(Prod[j][j])));
				}
			}	
		}
		vector<int> pos(max_vals.size());
	 	std::iota(pos.begin(),pos.end(),0); //Initializing
	 	sort( pos.begin(),pos.end(), [&](int i,int j){return max_vals[i]<max_vals[j];} );
	 	for(int i = 0; i < G_real.size(); i++){
	 		G_real[i] = Temp[pos[i]];
	 	}

	 	data.G.resize(G_real.size());
	 	for(int i =0 ; i < data.G.size(); i++){
	 		data.G[i].resize(G_real[i].size());
	 		for(int j = 0; j < G_real[i].size(); j++){
	 			data.G[i][j] = quantize(G_real[i][j]);
	 		}
	 	}
	 	data.CS_temp.resize(G_real.size());
	 	for(int i = 0; i < G_real.size(); i++){
	 		data.CS_temp[i].resize(G_real.size());
	 	}
	 	for(int i = 0; i < G_real.size(); i++){
	 		for(int j = i; j < G_real.size(); j++){
	 			data.CS_temp[i][j] = F_inner_product(data.G[i],data.G[j]);
	 			data.CS_temp[j][i] = data.CS_temp[i][j];
	 		}
	 	}
	 }else{
	 	vector<vector<float>> Temp(G_real.size());
	 	for(int i = 0; i < G_real.size(); i++){
			Temp[i].resize(G_real[i].size());
		}
	 	vector<vector<float>> Prod(G_real.size());
		
	 	for(int i = 0; i < Prod.size(); i++){
			Prod[i].resize(G_real.size());
		}

		for(int i = 0; i < G_real.size(); i++){
			for(int j = 0; j < G_real[i].size()-100; j++){
				Temp[i][j] = 0.05 + 0.0008*i;
				//Temp[i][j] = (float)(i+1) / (float)(G_real.size()+1);
			}
			for(int j = G_real[i].size()-100; j < G_real[i].size(); j++){

				Temp[i][j] = (float)rand() / (float)RAND_MAX;
			}
		}

		vector<vector<float>> temp_prod(G_real.size());
		for(int i = 0; i < G_real.size(); i++){
			for(int j = i; j < G_real.size(); j++){
				float sum = 0.0;
				for(int k = G_real[i].size()-100; k < G_real[i].size(); k++){
					sum += Temp[i][k]*Temp[j][k];
				}
				Prod[i][j] = (float)(G_real.size()-100)*Temp[i][0]*Temp[j][0] + sum;//((float)G_real[0].size())*(1.0/((float)(i+1)*(float)(j+1)));
				Prod[j][i] = Prod[i][j];
			}
		}
		
		for(int i = 0; i < G_real.size(); i++){
			temp_prod[i] = Prod[i];
		}
		vector<float> max_vals(G_real.size());
		for(int i = 0; i < max_vals.size(); i++){
			max_vals[i] = 0.0;
			for(int j = 0; j < Prod.size(); j++){
				if(max_vals[i] < Prod[i][j]/(sqrt(Prod[i][i]*sqrt(Prod[j][j])))){
					max_vals[i] = Prod[i][j]/(sqrt(Prod[i][i]*sqrt(Prod[j][j])));
				}
			}
		}
		
		vector<int> pos(max_vals.size());
	 	std::iota(pos.begin(),pos.end(),0); //Initializing
	 	sort( pos.begin(),pos.end(), [&](int i,int j){return max_vals[i]<max_vals[j];} );
	 	

	 	for(int i = 0; i < G_real.size(); i++){
	 		G_real[i] = Temp[pos[i]];
	 	
	 	}
	 	


	 	data.G.resize(G_real.size());
	 	for(int i =0 ; i < data.G.size(); i++){
	 		data.G[i].resize(G_real[i].size());
	 		for(int j = 0; j < G_real[i].size(); j++){
	 			data.G[i][j] = quantize(G_real[i][j]);
	 		}
	 	}
		data.CS_temp.resize(G_real.size());
	 	for(int i = 0; i < G_real.size(); i++){
	 		//printf("%lf\n",0.32*(1-num) + 0.1 + (float)i/2024.0 );
	 		data.CS_temp[i].resize(G_real.size());
	 		for(int j = 0; j < G_real.size(); j++){
	 			F sum = F(0);
				for(int k = G_real[i].size()-100; k < G_real[i].size(); k++){
					sum += data.G[i][k]*data.G[j][k];
				}
	 			//printf("%lf\n", 0.32*(1-num));
	 			data.CS_temp[i][j] = F(G_real.size()-100)*(data.G[i][0])*data.G[j][0] + sum;
	 		}
	 	}
	}
}


F max(vector<F> arr){
	char buff[257];
	F max = F(0);
	for(int i = 0; i < arr.size(); i++){
		int n = (max - arr[i]).getStr(buff,257,2);
		
		if(n == 254){
			max = arr[i];
		}
	}
	return max;
}

F max1(vector<F> arr,int j){
	char buff[257];
	F max = F(0);
	for(int i = 0; i < arr.size(); i++){
		if(i ==j){
			continue;
		}
		int n = (max - arr[i]).getStr(buff,257,2);
		
		if(n == 254){
			max = arr[i];
		}
	}
	return max;
}


vector<F> find_max(vector<vector<F>> M){
	vector<F> v;
	for(int i = 0; i < M.size(); i++){
		v.push_back(max(M[i]));
	}
	return v;
}

vector<F> find_max1(vector<vector<F>> M){
	vector<F> v;
	for(int i = 0; i < M.size(); i++){
		v.push_back(max1(M[i],i));
	}
	return v;	
}

F compute_log(F num,FoolsGold &data){
	F log = F(0);

	num = num - F(1<<Q);
	F temp = num;

	for(int i = 0; i < 8; i++){
		if(i%2 == 0){
			log = log + (data.log_input_2[i]*data.log_input_1[i]*num);
		}
		else{
			log = log - data.log_input_2[i]*data.log_input_1[i]*num;
		}
		num = num*temp;
	}
	return log;
}


void compute_CS(FoolsGold &data){

	for(int i = 0; i <  data.CS_temp.size(); i++){
		data.identity_elements.push_back(data.CS_temp[i][i]);
	}

	char buff[256];
	for(int i = 0; i < data.CS_temp.size(); i++){
		
		data.sqrt.push_back(_sqrt(data.CS_temp[i][i]));
		
		data.sqrt_left.push_back(data.sqrt[i]*data.sqrt[i]);
		data.sqrt_right.push_back((data.sqrt[i]+1)*(data.sqrt[i]+1));
		data.sqrt_left_input.push_back(-data.sqrt_left[i] + data.CS_temp[i][i]);
		data.sqrt_right_input.push_back(data.sqrt_right[i] - data.CS_temp[i][i]);
	
	}
	data.sqrt_left_bits = prepare_bit_vector(data.sqrt_left_input ,2*Q);
	data.sqrt_right_bits = prepare_bit_vector(data.sqrt_right_input ,2*Q);
	data.sqrt_matrix.resize(data.CS_temp.size());
	data.CS.resize(data.CS_temp.size());
	


	for(int i = 0; i < data.CS_temp.size(); i++){
		data.sqrt_matrix[i].resize(data.CS_temp.size());
		data.CS[i].resize(data.CS_temp.size());
	}
	for(int i = 0; i < data.CS_temp.size(); i++){
		for(int j = 0; j < data.CS_temp[i].size(); j++){
			data.sqrt_matrix[i][j] = data.sqrt[i]*data.sqrt[j];
		}
	}


	for(int i = 0; i < data.CS_temp.size(); i++){
		for(int j = 0; j < data.CS_temp[i].size(); j++){
			data.CS[i][j] = divide((1<<Q)*data.CS_temp[i][j],data.sqrt_matrix[i][j]);
			data.CS[i][j].getStr(buff,256,10);
			data.CS_remainders.push_back(F(1<<Q)*data.CS_temp[i][j] - data.CS[i][j]*data.sqrt_matrix[i][j]);
		}
	}
	data.CS_remainders_bits = prepare_bit_vector(data.CS_remainders,4*Q);
	data.max_1 = find_max1(data.CS);
	
	for(int i = 0; i < data.CS.size(); i++){
		for(int j = 0; j < data.CS.size(); j++){
			if(i == j){
				data.max_1_difference.push_back(F(0));	
			}else{

				data.max_1_difference.push_back(data.max_1[i] - data.CS[i][j]);
			}
		}
	}
	data.max_1_bits = prepare_bit_vector(data.max_1_difference,Q);
	
}

void compute_pardon(FoolsGold &data){
	int counter = 0;

	data.new_CS.resize(data.CS.size());

	char buff[256];

	for(int i = 0; i < data.CS.size(); i++){
		for(int j = 0; j <= i; j++){
			data.pardon_div.push_back(F(1));
			data.pardon_remainders.push_back(F(0));
			counter++;
		}
		for(int j = i+1; j < data.CS.size(); j++){
			data.pardon_div.push_back(divide((1<<Q)*data.max_1[i],data.max_1[j]));
			data.pardon_remainders.push_back((1<<Q)*data.max_1[i] - data.pardon_div[counter]*data.max_1[j]);
			data.pardon_remainders[counter].getStr(buff,256,10);
			//printf("%s\n", buff);
			counter++;
		}
	}
	data.pardon_bits = prepare_bit_vector(data.pardon_remainders,Q);
	for(int i = 0; i < data.CS.size(); i++){
		data.new_CS[i].resize(data.CS.size());
		for(int j = 0; j < data.CS.size(); j++){
			data.new_CS[i][j] = data.CS[i][j]*data.pardon_div[i*data.CS.size() + j];
		}
	}

	data.max_2 = find_max(data.new_CS);
	
	for(int i = 0; i < data.CS.size(); i++){
		for(int j = 0; j < data.CS.size(); j++){
			data.max_2_difference.push_back(data.max_2[i] - data.new_CS[i][j]);
		}
	}
	data.max_2_bits = prepare_bit_vector(data.max_2_difference,2*Q);

}

void compute_weights(FoolsGold &data){
	vector<F> arr;
	for(int i = 0; i < data.max_2.size(); i++){
		data.shifted_max.push_back(shift(data.max_2[i],1)[0]);
		data.shifted_max_remainders.push_back(data.max_2[i] - F(1<<Q)*data.shifted_max[i]);
	}

	data.shift_bits = prepare_bit_vector(data.shifted_max_remainders,Q);

	for(int i = 0; i < data.max_2.size(); i++){
		arr.push_back(F(1<<Q) - data.shifted_max[i]);
	}
	data.max_val = max(arr);
	for(int i = 0; i < data.max_2.size(); i++){
		data.max_3_difference.push_back(data.max_val - arr[i]);
	}
	data.max_3_bits = prepare_bit_vector(data.max_3_difference,Q);
	
	for(int i = 0; i < data.max_2.size(); i++){
		data.normalized_values.push_back(divide(F(1<<Q)*arr[i],data.max_val));
		data.normalized_values_remainders.push_back(F(1<<Q)*arr[i] - data.max_val*data.normalized_values[i]);
	}
	data.normalized_bits = prepare_bit_vector(data.normalized_values_remainders,Q);
	for(int i = 0; i < data.max_2.size(); i++){
		data.log_left.push_back(compute_log(data.normalized_values[i],data));
		data.log_right.push_back(compute_log(F(1<<Q)- data.normalized_values[i],data));
	}
	
	for(int i = 0; i < data.max_2.size(); i++){
		data.logit.push_back(data.log_left[i] - data.log_right[i]);
	}
	
	relu(data,data.logit);
	arr.clear();
	for(int i = 0; i < data.output.size(); i++){
		arr.push_back(F(1<<Q) - data.output[i]);
	}
	data.inv_relu_bits = prepare_bit_vector(arr,256);
	for(int i = 0; i < arr.size(); i++){
		data.inv_most_significant_bits.push_back(data.inv_relu_bits[i*256+254]);
	}
	
	for(int i = 0; i <arr.size(); i++){
		data.weights.push_back(F(1<<Q)*data.inv_most_significant_bits[i] + data.output[i]*(F(1)-data.inv_most_significant_bits[i]));
	}

	data.aggr = inner_product(_transpose(data.G),data.weights);

}


FoolsGold foolsgold(int N, int M){
	FoolsGold data;
	vector<vector<float>> G_real(N);
	for(int i = 0; i < N; i++){
		G_real[i].resize(M);
	}

	for(int i = 0; i < 8; i++){
		data.log_input_1.push_back(quantize(1.0/(float)(i+1)));
		data.log_input_2.push_back(F(1));
		for(int j = 0; j < 8-i; j++){
			data.log_input_2[i] = data.log_input_2[i]*F(1<<Q);
		}
	}

	generate_input(G_real,data);
	compute_CS(data);
	compute_pardon(data);
	compute_weights(data);
	return data;	
}