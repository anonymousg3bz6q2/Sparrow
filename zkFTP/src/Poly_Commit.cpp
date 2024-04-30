#include "Poly_Commit.h"
#include "utils.hpp"
#include <math.h>
#include "quantization.h"
#include <map>
#include <unordered_map>
#include <thread>
#include <chrono>


using namespace std::chrono;

extern double proving_time;
extern double verification_time;
extern int comm_size;
extern int threads;
extern size_t MAX_CHUNCK;
double MIPP_verify_time =0.0;

void generate_pp1(vector<G1> &commitment, vector<F> &beta,G1 G, int idx){
	int size = beta.size()/16;
	int pos = idx*size;
	for(int i = pos; i < pos + size; i++){
		commitment[i] = G*beta[i];
	}
}
void generate_pp2(vector<G2> &commitment, vector<F> &beta,G2 G, int idx){
	int size = beta.size()/16;
	int pos = idx*size;
	for(int i = pos; i < pos + size; i++){
		commitment[i] = G*beta[i];
	}
}
vector<F> arr_difference(F x1, F x2, vector<F> &arr){
	vector<F> diff(arr.size()/2);
	if(x1 == F(1) && x2 == F(1)){
		for(int i = 0; i < arr.size()/2; i++){
			diff[i] = arr[2*i + 1] - arr[2*i];
		}
	}else{
		for(int i = 0; i < arr.size()/2; i++){
			diff[i] = x1*(arr[2*i + 1] - arr[2*i]) + arr[2*i];
		}
	}

	//for(int i = 0; i < arr.size()/2; i++){
	//	diff[i] = x1*arr[2*i + 1] - x2*arr[2*i];
	//}
	return diff;
}

vector<F> compute_coefficients(vector<F> &arr){
	
	if(arr.size() == 1){
		vector<F> r(1);
		r[0] = arr[0];
		return r;
	}
	vector<F> l_arr,r_arr;
	vector<F> temp_arr(arr.size()/2);
	for(int i = 0; i < arr.size()/2; i++){
		temp_arr[i] = (arr[i]);
	}
	l_arr = compute_coefficients(temp_arr);
	
	for(int i = 0; i < arr.size()/2; i++){
		temp_arr[i] = (arr[i+arr.size()/2]);
	}
	r_arr = compute_coefficients(temp_arr);
	vector<F> r(2*l_arr.size());
	for(int i = 0; i  < r_arr.size(); i++){
		r[i] = l_arr[i];
	}
	for(int i = 0; i < l_arr.size(); i++){
		r[i+l_arr.size()] = (r_arr[i] - l_arr[i]);
	}
	return r;
}

void MIPP_gen_stream(MIPP_Comm &commitment){
	struct Comm temp_com;
	commitment.bit_size = 2*(int)log2(MAX_CHUNCK);
	//commitment.commit_bit_size = chunck_size;
 	commitment.commit_bit_size = (int)(log2(MAX_CHUNCK));
	generate_pp(temp_com,commitment.commit_bit_size);
	
	commitment.pp1 = temp_com.pp1;
	commitment.pp1_cached = temp_com.pp1_cached;
	commitment.pp2 = temp_com.pp2;
	commitment.base = temp_com.base;
	
	commitment.H = temp_com.H;
	commitment.G = temp_com.G;
	
	commitment.commit_time = 0.0;
	commitment.prove_time = 0.0;
	commitment.verification_time = 0.0;
	commitment.proof_size = 0;
	
	commitment.w.resize(1<<(commitment.bit_size- commitment.commit_bit_size ));
	commitment.u.resize(1<<(commitment.bit_size- commitment.commit_bit_size ));
	thread worker[16];
	vector<F> base;
	for(int i = 0; i < commitment.w.size(); i++){
		base.push_back(F(1+i));
	}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(commitment.w),ref(base),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp2,ref(commitment.u),ref(base),commitment.H,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}

}

vector<vector<F>> find_quontents(vector<F> arr, vector<F> x){
	vector<vector<F>> quotients(x.size());
	
	vector<F> temp;
	for(int i = 0; i < x.size()-1; i++){
		temp = arr_difference(1,1,arr);
		quotients[i] = compute_coefficients(temp);
		arr = arr_difference(x[i],x[i]-F(1),arr);
	}

	vector<F> f = compute_coefficients(arr);

	quotients[x.size()-1].push_back(f[1]);
	
	return quotients;
	/*
	vector<vector<F>> h(x.size());
	for(int i = 0; i < h.size(); i++){
		h[i].resize(arr.size()/(1ULL<<(i+1)));
	}
	vector<F> temp_f = arr;
	for(int i = 0; i < h.size(); i++){
		for(int j = 0; j < h[i].size(); j++){
			h[i][j] = temp_f[j+h[i].size()] - temp_f[j];
		}
		for(int j = 0; j < h[i].size(); j++){
			temp_f[j] = temp_f[j] + h[i][j]*x[h.size()-1-i];
		}
	}
	*/


	//return h;
}




void generate_pp_hyperproofs(struct Comm &commitment,int bit_size,int subvector_size){
	vector<F> random_values;
	//commitment.H = mcl::bn::getG2basePoint();
	char rand[256];
	for(int i = 0; i < 256; i++){
		rand[i] = i+'4';
	}
	
	//commitment.G = mcl::bn::getG1basePoint();
	mcl::bn::hashAndMapToG1(commitment.G,rand,256);

	mcl::bn::hashAndMapToG2(commitment.H,rand,256);
	commitment.bit_size = bit_size;
	for(int i = 0; i < commitment.bit_size; i++){
		F temp;
		temp.setByCSPRNG();
		random_values.push_back(temp);
	}
	commitment.secret = random_values;
	vector<F> betas,betas2;
	precompute_beta(random_values,betas2);
	compute_binary(random_values, betas);

	thread worker[16];
	commitment.pp1.resize(betas.size());
	commitment.binary_pp1.resize(betas.size());
	//for(int i = 0; i < betas.size(); i++){
	//	commitment.pp1[i] = commitment.G*betas[i];
	//}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(commitment.pp1),ref(betas2),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}

	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(commitment.binary_pp1),ref(betas),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}


	vector<G1> temp = commitment.pp1;
	

	commitment.base.resize(random_values.size());
	for(int i = 0; i < random_values.size(); i++){
		for(int j = 0; j < temp.size()/2; j++){
			commitment.base[i].push_back(temp[2*j]+temp[2*j+1]);
			//commitment.base[i].push_back(temp[j]+temp[j+temp.size()]);
		}
		if(commitment.base[i].size() == (1<<subvector_size)){
			commitment.subvector_pp1 = commitment.base[i];
		}
		temp = commitment.base[i];
	}

	temp = commitment.binary_pp1;
	commitment.binary_base.resize(random_values.size());
	for(int i = 0; i < random_values.size(); i++){
		for(int j = 0; j < temp.size()/2; j++){
			commitment.binary_base[i].push_back(temp[2*j]);
		}
		temp = commitment.binary_base[i];
		if(temp.size() < (1<<subvector_size)){
			commitment.subvector_base.push_back(commitment.binary_base[i]);
		}
	}

	for(int i = 0; i < random_values.size(); i++){
		commitment.pp2.push_back(commitment.H * random_values[i]);
	}
	// initialize public parameters for naive inner pairing products
	for(int i = 0; i < random_values.size(); i++){
		commitment.ipp_pp1.push_back(commitment.G*(random_values[i]*(i+10)));
		commitment.ipp_pp2.push_back(commitment.H*(random_values[i]*(i+10)));
	}


}

void generate_streaming_pp(struct Comm &commitment,int bit_size){
	vector<F> random_values;
	//commitment.H = mcl::bn::getG2basePoint();
	char rand[256];
	for(int i = 0; i < 256; i++){
		rand[i] = i+'4';
	}
	
	//commitment.G = mcl::bn::getG1basePoint();
	
	mcl::bn::hashAndMapToG1(commitment.G,"0",1);
	mcl::bn::hashAndMapToG2(commitment.H,rand,256);
	commitment.bit_size = bit_size;
	for(int i = 0; i < commitment.bit_size; i++){
		F temp;
		temp.setByCSPRNG();
		random_values.push_back(temp);
	}
	commitment.secret = random_values;
	vector<F> betas;
	precompute_beta(random_values,betas);
	

	thread worker[16];
	commitment.pp1.resize(betas.size());
	
	//for(int i = 0; i < betas.size(); i++){
	//	commitment.pp1[i] = commitment.G*betas[i];
	//}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(commitment.pp1),ref(betas),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}
	
	vector<G1> temp = commitment.pp1;
	
	
	commitment.base.resize(random_values.size());
	
	for(int i = 0; i < random_values.size(); i++){
		for(int j = 0; j < temp.size()/2; j++){
			commitment.base[i].push_back(temp[2*j]+temp[2*j+1]);
		}

		temp = commitment.base[i];
	}
	
	for(int i = 0; i < random_values.size(); i++){
		commitment.pp2.push_back(commitment.H * random_values[i]);
	}

	// store data 
	vector<int> num(betas.size());
	for(int i = 0; i < betas.size(); i++){
		num[i] = i;
	}
	int K = (1ULL<<bit_size)/MAX_CHUNCK;
	vector<vector<int>> idx(MAX_CHUNCK);
	
	idx[0] = num;
	int curr_arr = 1;
	while(1){
		vector<int> arr_idx(idx[0].size()/2);
		for(int i = 0; i < curr_arr; i++){
			for(int j = idx[i].size()/2; j < idx[i].size(); j++){
				arr_idx[j - idx[i].size()/2] = idx[i][j];
			}
			idx[i+curr_arr] = arr_idx;
			idx[i].resize(idx[i].size()/2);
		}
		curr_arr *= 2;
		if(curr_arr == idx.size()){
			break;
		}
	}
	int counter = 0;
	vector<int> pos((1ULL<<(bit_size-1)));
	for(int i = 0; i < idx[0].size(); i++){
		for(int j = 0; j < idx.size()/2; j++){
			pos[counter] = idx[2*j][i];
			counter++;
		}
	}

	vector<vector<G1>> pp(random_values.size());
	for(int i = 0; i < commitment.base.size(); i++){
		pp[i].resize(commitment.base[i].size());
		for(int j = 0; j < commitment.base[i].size(); j++){
			pp[i][j] = commitment.base[i][pos[j]];
		}
		for(int j = 0; j < commitment.base[i].size()/2; j++){
			pos[j] = pos[2*j];
		}
	}

	//int num = rand();
	
	FILE *fp;
	string s = to_string(0);
	commitment.pp_string_name = s;
	fp = fopen(commitment.pp_string_name.c_str(),"w");
	write_pp(commitment.pp1,fp);
	fclose(fp);
	
	for(int i = 0; i < commitment.base.size(); i++){
		s = to_string(i+1);
		commitment.base_name.push_back(s);
		fp = fopen(commitment.base_name[i].c_str(),"w");
		write_pp(pp[i],fp);
		fclose(fp);
	}
	//for(int )
}

void generate_pp(struct Comm &commitment,int bit_size){
	vector<F> random_values;
	//commitment.H = mcl::bn::getG2basePoint();
	char rand[256];
	for(int i = 0; i < 256; i++){
		rand[i] = i+'4';
	}
	
	//commitment.G = mcl::bn::getG1basePoint();
	
	mcl::bn::hashAndMapToG1(commitment.G,"0",1);
	mcl::bn::hashAndMapToG2(commitment.H,rand,256);
	commitment.bit_size = bit_size;
	for(int i = 0; i < commitment.bit_size; i++){
		F temp;
		temp.setByCSPRNG();
		random_values.push_back(temp);
	}
	commitment.secret = random_values;
	vector<F> betas,betas2;
	precompute_beta(random_values,betas2);
	compute_binary(random_values, betas);

	thread worker[16];
	commitment.pp1.resize(betas.size());
	commitment.pp1_cached.resize(bit_size);
	//for(int i = 0; i < betas.size(); i++){
	//	commitment.pp1[i] = commitment.G*betas[i];
	//}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(commitment.pp1),ref(betas2),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}
	
	//commitment.pp1_cached[bit_size -1] = commitment.pp1;
	for(int i = bit_size-2; i >= 0; i--){
		if(i == bit_size -2){
			for(int j = 0; j < commitment.pp1.size()/2; j++){
			//	commitment.pp1_cached[i].push_back(commitment.pp1[2*j] + commitment.pp1[2*j+1]);				
			}	
		}
		else{
			for(int j = 0; j < commitment.pp1_cached[i+1].size()/2; j++){
			//	commitment.pp1_cached[i].push_back(commitment.pp1_cached[i+1][2*j] + commitment.pp1_cached[i+1][2*j+1]);	
			}
		}
	}

	
	vector<G1> temp(betas2.size());
	
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(temp),ref(betas),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}

	commitment.base.resize(random_values.size());
	for(int i = 0; i < random_values.size(); i++){
		for(int j = 0; j < temp.size()/2; j++){
		//	commitment.base[i].push_back(temp[2*j]+temp[2*j+1]);
			commitment.base[i].push_back(temp[2*j]);
		}
		temp = commitment.base[i];
	}
	
	int idx = 1;
	for(int i = 0; i < random_values.size(); i++){
		commitment.pp2.push_back(commitment.H * betas[idx]);
		idx = idx*2;
	}
}

void generate_pp_vesta(struct Vesta_Comm &commitment,int bit_size){
	int levels = 1;
	int bit = bit_size;
	vector<int> bits,hbits;
	bits.push_back(bit_size);
	hbits.push_back(bit_size-16);
	while(true){
		if(bit == 8){
			bits.push_back(bit);
			hbits.push_back(bit);
			break;
		}
		if(bit > 16){
			bits.push_back(16);
			hbits.push_back(8);
			bit = 8;
		}
		else{
			bits.push_back(bit);
			hbits.push_back(bit/2);
			bit = bit/2;
		}
	}

	commitment.comm.resize(bits.size());
	commitment.aux_comm.resize(bits.size());
	for(int i = 0; i < commitment.comm.size(); i++){
		generate_pp(commitment.comm[i],bits[i]);
	}

	for(int i = 0; i < commitment.comm.size(); i++){
		generate_pp_hyperproofs(commitment.aux_comm[i],hbits[i],1);
	}
	commitment.commitments.resize(bits.size());
}

void commit(vector<F> poly, struct Comm &commitment){
	clock_t start,end;
	if(poly.size() > commitment.pp1.size()){
		printf("Error in KZG size\n");
		exit(-1);
	}
	if(poly.size() == commitment.pp1.size()){
		start = clock();
		G1::mulVec(commitment.C, commitment.pp1.data(), poly.data(), poly.size());
		end = clock();
	}else{
		int bit_size = (int)log2(poly.size());
		start = clock();
		G1::mulVec(commitment.C, commitment.pp1_cached[bit_size-1].data(), poly.data(), poly.size());
		end = clock();
	}
	//printf("Commit time : %lf, size : %d\n",(float)(end-start)/(float)CLOCKS_PER_SEC,poly.size() );
}


void MIPP_commit_stream_bits(stream_descriptor fd, unsigned long long int size, MIPP_Comm &commitment, vector<G1> &commitments){
	auto s = high_resolution_clock::now();

	//printf("%d,%d\n",size,  1<<(commitment.bit_size - commitment.commit_bit_size));
	if(MAX_CHUNCK >= size){
		vector<F> buff(size);
		read_stream(fd,buff,size);
		if(MAX_CHUNCK == size){
			commitment.Commitments.push_back(compute_G1_commitment(commitment.pp1,buff));
		}else{
			commitment.Commitments.push_back(compute_G1_commitment(commitment.pp1_cached[(int)log2(size)-1],buff));
		}
		/*
		int log_size = (int)log2(size);
		int kzg_commit_size = log_size/2 + 3;
		int pairing_size = log_size - kzg_commit_size;
		vector<F> poly(1ULL<<kzg_commit_size);
		for(int i  =0; i < (1ULL<<pairing_size); i++){
			for(int j = 0; j < (1ULL<<kzg_commit_size); j++){
				poly[j] = buff[i*(1ULL<<kzg_commit_size) + j];
			}
			commitment.Commitments.push_back(compute_G1_commitment(commitment.pp1_cached[kzg_commit_size-1],buff));
		}*/
		 
		
	}else{
		printf("OK\n");
		vector<F> buff(MAX_CHUNCK);
		for(int i = 0; i < size/MAX_CHUNCK; i++){
			read_stream(fd,buff,MAX_CHUNCK);
			G1 comm = commitment.G*F(1);
			for(int j = 0; j < MAX_CHUNCK/2; j++){
				comm = commitment.pp1[j] + comm;
			}
			commitment.Commitments.push_back(comm);
		}
	}
	
	
	commitment.C_T = compute_pairing_commitment(commitment.Commitments,commitment.u);
	comm_size += sizeof(commitment.C_T);
	
	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	
	//proving_time += d.count()/1000000.0;
	commitment.prove_time += d.count()/1000000.0;
	printf("%lf\n",commitment.prove_time);
	commitments = commitment.Commitments;
		
}


void MIPP_commit_stream_multree(stream_descriptor fd, vector<size_t> sizes,int distance, MIPP_Comm &commitment, vector<vector<G1>> &commitments, vector<GT> &C){
	clock_t s = clock();
	//auto s = high_resolution_clock::now();
	vector<vector<F>> v(sizes.size()-1);
    vector<vector<F>> v1(sizes.size()-1);
    vector<int> idx(sizes.size()-1,0),counter(sizes.size()-1,0);
    vector<F> sum(sizes.size()-1,0);
    
    for(int i = 0; i < v.size(); i++){
        v[i].resize(MAX_CHUNCK/(1<<(distance*i)));
        v1[i].resize(MAX_CHUNCK);
    }
    
	for(int i = 0; i < sizes[0]/MAX_CHUNCK; i++){
        read_stream_batch(fd,v,MAX_CHUNCK,distance);
        for(int j = 0; j < v.size(); j++){
            if(idx[j] == MAX_CHUNCK) idx[j] = 0;
            for(int k = 0; k < v[j].size(); k++){
                v1[j][idx[j]] = v[j][k];
                idx[j]++;
            }
        }
        for(int j = 0; j < v.size(); j++){
            if(idx[j] != MAX_CHUNCK) continue;
            commitments[j].push_back(compute_G1_commitment(commitment.pp1,v1[j]));
        }
    }

	
	for(int i = 0; i < sizes.size()-1; i++){
		C.push_back(compute_pairing_commitment(commitments[i],commitment.u));	
	}	
	
	comm_size += sizeof(C[0])*C.size();
	
	clock_t e = clock();
	//auto e = high_resolution_clock::now();
	//auto d = duration_cast<microseconds>(e - s);
	
	commitment.prove_time += (double)(e-s)/(double)CLOCKS_PER_SEC;// d.count()/1000000.0;
	printf(">>%lf\n",commitment.prove_time);
}

	

void MIPP_commit_stream(stream_descriptor fd, size_t size, MIPP_Comm &commitment, vector<G1> &commitments){
	auto s = high_resolution_clock::now();

	//printf("%d,%d\n",size,  1<<(commitment.bit_size - commitment.commit_bit_size));
	if(MAX_CHUNCK >= size){
		vector<F> buff(size);
		read_stream(fd,buff,size);
		if(MAX_CHUNCK == size){
			commitment.Commitments.push_back(compute_G1_commitment(commitment.pp1,buff));
		}else{
			commitment.Commitments.push_back(compute_G1_commitment(commitment.pp1_cached[(int)log2(size)-1],buff));
		}
		/*
		int log_size = (int)log2(size);
		int kzg_commit_size = log_size/2 + 3;
		int pairing_size = log_size - kzg_commit_size;
		vector<F> poly(1ULL<<kzg_commit_size);
		for(int i  =0; i < (1ULL<<pairing_size); i++){
			for(int j = 0; j < (1ULL<<kzg_commit_size); j++){
				poly[j] = buff[i*(1ULL<<kzg_commit_size) + j];
			}
			commitment.Commitments.push_back(compute_G1_commitment(commitment.pp1_cached[kzg_commit_size-1],buff));
		}*/
		 
		
	}else{
	
		vector<F> buff(MAX_CHUNCK);
		for(int i = 0; i < size/MAX_CHUNCK; i++){
			read_stream(fd,buff,MAX_CHUNCK);
	
			commitment.Commitments.push_back(compute_G1_commitment(commitment.pp1,buff));
		}
	}
	
	
	commitment.C_T = compute_pairing_commitment(commitment.Commitments,commitment.u);
	comm_size += sizeof(commitment.C_T);
	
	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	
	//proving_time += d.count()/1000000.0;
	commitment.prove_time += d.count()/1000000.0;
	printf("%lf\n",commitment.prove_time);
	commitments = commitment.Commitments;
		
}



void MIPP_commit(vector<F> &poly, MIPP_Comm &commitment, vector<G1> &commitments){
	auto s = high_resolution_clock::now();
	commitment.Commitments.clear();
	pad_vector(poly);

	if(poly.size() <= (1ULL<<commitment.commit_bit_size)){
		int size = (int)log2(poly.size());
		if(poly.size() == (1ULL<<commitment.commit_bit_size)){
			commitment.Commitments.push_back(compute_G1_commitment(commitment.pp1,poly));
		}else{
			printf("%d,%d,%d\n",size,commitment.pp1_cached[size-1].size(),poly.size());
			commitment.Commitments.push_back(compute_G1_commitment(commitment.pp1_cached[size-1],poly));
		}
		auto e = high_resolution_clock::now();
		auto d = duration_cast<microseconds>(e - s);
		//proving_time += d.count()/1000000.0;
		commitment.prove_time += d.count()/1000000.0;
		commitments = commitment.Commitments;
	
		return;
		
	}
	int log_size = (int)log2(poly.size());
	int commit_size = 1<<(commitment.commit_bit_size);
	//printf("%d,%d\n",size,  1<<(commitment.bit_size - commitment.commit_bit_size));
	vector<F> arr(commit_size);
	//printf("Comms : %d, size : %d\n",1<<(commitment.bit_size - commitment.commit_bit_size),size );
	for(int i = 0; i < 1<<(log_size - commitment.commit_bit_size); i++){
		for(int j = 0; j < commit_size; j++){
			arr[j] = poly[i*commit_size + j];
		}
		commitment.Commitments.push_back(compute_G1_commitment(commitment.pp1,arr));
	}
	printf("%d\n",commitment.Commitments.size());
	commitment.C_T = compute_pairing_commitment(commitment.Commitments,commitment.u);
	comm_size += sizeof(commitment.C_T);
	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	//proving_time += d.count()/1000000.0;
	commitment.prove_time += d.count()/1000000.0;
	commitments = commitment.Commitments;	
	
}


void MIPP_open(vector<F> &poly,vector<F> x, MIPP_Comm &commitment, vector<G1> commitments){
	pad_vector(poly);
	printf(">> %d\n",poly.size());
	int log_size = (int)log2(poly.size());
	
	vector<F> r1,r2;
	for(int i = 0; i < log_size - commitment.commit_bit_size; i++){
		r1.push_back(x[i + commitment.commit_bit_size]);
	}
	for(int i = log_size - commitment.commit_bit_size; i < log_size; i++){
		r2.push_back(x[i - (log_size - commitment.commit_bit_size)]);
	}
	auto s = high_resolution_clock::now();

	if(poly.size() <= 1ULL<<commitment.commit_bit_size){
		vector<vector<F>> quotients = find_quontents(poly,x);	
		commitment.Proof.clear();
		G1 P;
		int offset = commitment.commit_bit_size - x.size();
		printf("%d\n",offset);
		for(int i = 0; i < x.size(); i++){
		
			G1::mulVec(P, commitment.base[i+offset].data(),quotients[i].data(), quotients[i].size());	
			commitment.Proof.push_back(P);
		}
		printf("OK\n");
		auto e = high_resolution_clock::now();
		auto d = duration_cast<microseconds>(e - s);
		//proving_time += d.count()/1000000.0;
		
		MIPP_verify(evaluate_vector(poly,x),commitment);
		printf("OK\n");
		commitment.prove_time += d.count()/1000000.0;
		commitment.proof_size += (r2.size()+1)*sizeof(P);
		commitment.verification_time += MIPP_verify_time;
		MIPP_verify_time = 0.0;
		return;
	}
	vector<F> aggr_poly(1 << commitment.commit_bit_size,F(0));
	
	vector<F> betas;
	precompute_beta(r1,betas);
	int size = 1<<(commitment.commit_bit_size);
	// Aggregate polynomials
	for(int i = 0; i < 1<<(log_size - commitment.commit_bit_size); i++){
		for(int j = 0; j < size; j++){
			aggr_poly[j] += betas[i]*poly[i*size + j];
		}
	}
	
	// Prepare commitments for MIPP
	G1 Agg_C = compute_G1_commitment(commitments,betas);
	G1 P = compute_G1_commitment(commitment.w,betas);
	MIPP_verify_time = 0.0;
	int mipp_proof_size = MIPP(commitments,commitment.u,betas,commitment.w,commitment.C_T,P,Agg_C);
	commitment.Agg_C = Agg_C;
	commitment.r2 = r2;
	// Open aggregated polynomial

	vector<vector<F>> quotients = find_quontents(aggr_poly,r2);
	
	for(int i = 0; i < r2.size(); i++){
		G1 P;
		P = compute_G1_commitment(commitment.base[i],quotients[i]);
		//G1::mulVec(P, commitment.base[i].data(),quotients[i].data(), quotients[i].size());	
		commitment.Proof.push_back(P);
	}


	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	//proving_time += d.count()/1000000.0;
	MIPP_verify(evaluate_vector(aggr_poly,r2),commitment);
	commitment.prove_time += d.count()/1000000.0;
	commitment.proof_size += (r2.size()+1)*sizeof(P) + sizeof(commitment.C_T) + mipp_proof_size;
	commitment.verification_time += MIPP_verify_time;
	MIPP_verify_time  = 0.0;


}

void MIPP_verify( F y, MIPP_Comm &commitment){
	
	GT check_P,Pairing_prod;
	vector<G2> diff;
	vector<G1> proofs;
	
	auto s = high_resolution_clock::now();

	for(int i = 0; i < commitment.r2.size(); i++){
		proofs.push_back(commitment.Proof[i]);
		diff.push_back(commitment.pp2[i] + commitment.H*(F(0)-commitment.r2[i]));
	}
	diff.push_back(commitment.H);
	proofs.push_back(commitment.Agg_C*(F(-1))+commitment.G*y);
	mcl::bn::millerLoopVec(Pairing_prod,proofs.data(),diff.data(),commitment.r2.size()+1);
	
	comm_size += proofs.size()*sizeof(commitment.G);
	
	finalExp(Pairing_prod,Pairing_prod);
	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	commitment.verification_time +=2.0*d.count()/1000000.0;
	if((Pairing_prod).isOne() != 1){
		//printf("Error in open\n");
		//exit(-1);
	}

}

void MIPP_open_stream_multree(stream_descriptor fd, vector<size_t> sizes, int distance,vector<F> x, MIPP_Comm &commitment, vector<vector<G1>> commitments){
	vector<F> r1,r2;
	vector<F> aggr_poly;
	vector<G1> aggr_comm(commitments[0].size());
	auto s = high_resolution_clock::now();
	vector<F> betas;

		
	int log_size = (int)log2(sizes[0]);
	for(int i = 0; i < log_size - commitment.commit_bit_size; i++){
		r1.push_back(x[i + commitment.commit_bit_size]);
	}
	for(int i = log_size - commitment.commit_bit_size; i < log_size; i++){
		r2.push_back(x[i - (log_size - commitment.commit_bit_size)]);
	}
	aggr_poly.resize(1 << commitment.commit_bit_size,F(0));
	
	vector<F> a = generate_randomness(commitments.size(),x[x.size()-1]);	
	vector<G1> buffG(commitments.size());
	int counter = 0;
	for(int i = 0; i < commitments[0].size(); i++){
		for(int k = 0; k < commitments.size(); k++){
			if(commitments.size() > i){
				buffG[k] = commitments[k][i];
				counter++;
			}
		}
		G1::mulVec(aggr_comm[i], buffG.data(),a.data(), counter);
		counter= 0;
	}
		
	precompute_beta(r1,betas);
	
	vector<vector<F>> v(commitments.size());
    vector<vector<F>> v1(commitments.size());
    vector<int> idx(commitments.size(),0);
    vector<F> sum(commitments.size(),0);
    
    for(int i = 0; i < v.size(); i++){
        v[i].resize(MAX_CHUNCK/(1<<(distance*i)));
        v1[i].resize(MAX_CHUNCK);
    }
    vector<int> counters(v.size(),0);
	
	
	for(int i = 0; i < sizes[0]/MAX_CHUNCK; i++){
        read_stream_batch(fd,v,MAX_CHUNCK,distance);
        
        for(int j = 0; j < v.size(); j++){
            if(idx[j] == MAX_CHUNCK) idx[j] = 0;
            for(int k = 0; k < v[j].size(); k++){
                v1[j][idx[j]] = v[j][k];
                idx[j]++;
            }
        }
        for(int j = 0; j < v.size(); j++){
            if(idx[j] != MAX_CHUNCK) continue;
			for(int k = 0; k < MAX_CHUNCK; k++){
				aggr_poly[k] += a[j]*betas[counters[j]]*v1[j][k];
			}
			counters[j]++;
		}
    }
	F y = evaluate_vector(aggr_poly,r2);
	
	// Prepare commitments for MIPP
	
	G1 Agg_C = compute_G1_commitment(aggr_comm,betas);
	
	vector<G1> w(betas.size());
	vector<G2> u(betas.size());
	
	for(int i = 0;i< betas.size(); i++){
		
		w[i] = commitment.w[i];
		u[i] = commitment.u[i];

	}
	
	G1 P = compute_G1_commitment(w,betas);
	MIPP_verify_time = 0.0;
	
	
	int mipp_proof_size = MIPP(aggr_comm,u,betas,w,commitment.C_T,P,Agg_C);
	commitment.Agg_C = Agg_C;
	commitment.r2 = r2;
	// Open aggregated polynomial
	
	
	vector<vector<F>> quotients = find_quontents(aggr_poly,r2);
	

	
	commitment.Proof.clear();
	if(aggr_poly.size() == 1ULL<<commitment.commit_bit_size){

	
		for(int i = 0; i < r2.size(); i++){
			G1 P;
			G1::mulVec(P, commitment.base[i].data(),quotients[i].data(), quotients[i].size());	
			commitment.Proof.push_back(P);
		}
	}else{
		int offset = commitment.commit_bit_size - (int)log2(aggr_poly.size());
		for(int i = 0; i < r2.size(); i++){
			G1 P;
			G1::mulVec(P, commitment.base[i+offset].data(),quotients[i].data(), quotients[i].size());	
			commitment.Proof.push_back(P);
		}
	}
	
	
	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	printf(">%lf\n", 2*d.count()/1000000.0);
		
	//proving_time += d.count()/1000000.0;
	MIPP_verify(y,commitment);
	commitment.prove_time += 2*d.count()/1000000.0;
	commitment.proof_size += (r2.size()+1)*sizeof(P) + sizeof(commitment.C_T) + mipp_proof_size;
	commitment.verification_time += MIPP_verify_time;
	MIPP_verify_time = 0.0;

}

void MIPP_open_stream(stream_descriptor fd, unsigned long long int size,vector<F> x, MIPP_Comm &commitment, vector<G1> commitments){
	vector<F> r1,r2;
	vector<F> aggr_poly;
	auto s = high_resolution_clock::now();
	vector<F> betas;

	if(size > MAX_CHUNCK){
		
		int log_size = (int)log2(size);
		
		for(int i = 0; i < log_size - commitment.commit_bit_size; i++){
			r1.push_back(x[i + commitment.commit_bit_size]);
		}
		for(int i = log_size - commitment.commit_bit_size; i < log_size; i++){
			r2.push_back(x[i - (log_size - commitment.commit_bit_size)]);
		}
		aggr_poly.resize(1 << commitment.commit_bit_size,F(0));
		
		
		
		precompute_beta(r1,betas);
		vector<F> buff(MAX_CHUNCK);
		for(int i = 0; i < size/MAX_CHUNCK; i++){
			read_stream(fd,buff,MAX_CHUNCK);
			for(int j = 0; j < MAX_CHUNCK; j++){
				aggr_poly[j] += betas[i]*buff[j];
			}
		}
	}else{
		
		/*
		int log_size = (int)log2(size);
		int kzg_commit_size = log_size/2+3;
		int pairing_size = log_size - kzg_commit_size;
		for(int i = 0; i < pairing_size; i++){
			r1.push_back(x[i + kzg_commit_size]);
		}
		for(int i = log_size - kzg_commit_size; i < log_size; i++){
			r2.push_back(x[i - (log_size - kzg_commit_size)]);
		}
		aggr_poly.resize(1 << kzg_commit_size,F_ZERO);
		
		precompute_beta(r1,betas);
		*/
		vector<F> buff(size);
		read_stream(fd,buff,size);
		vector<vector<F>> quotients = find_quontents(buff,x);
	

		int offset = (int)log2(MAX_CHUNCK) - (int)log2(buff.size());
		commitment.Proof.clear();
		G1 P;
		
			for(int i = 0; i < x.size(); i++){
				G1::mulVec(P, commitment.base[i + offset].data(),quotients[i].data(), quotients[i].size());	
				commitment.Proof.push_back(P);
			}
		
		auto e = high_resolution_clock::now();
		auto d = duration_cast<microseconds>(e - s);
		MIPP_verify(evaluate_vector(buff,x),commitment);
		printf(">%lf\n", d.count()/1000000.0);
		//proving_time += d.count()/1000000.0;
		commitment.prove_time += d.count()/1000000.0;
		commitment.proof_size += (x.size()+1)*sizeof(P);// + sizeof(commitment.C_T) + mipp_proof_size;
		commitment.verification_time += MIPP_verify_time;
		MIPP_verify_time = 0.0;
		return;
		/*
		for(int i = 0; i < 1ULL<<pairing_size; i++){
			
			for(int j = 0; j < 1ULL<<kzg_commit_size; j++){
				aggr_poly[j] += betas[i]*buff[i*(1ULL<<kzg_commit_size) + j];
			}
		}*/
		
		
	}
	
	F y = evaluate_vector(aggr_poly,r2);
	
	// Prepare commitments for MIPP
	
	G1 Agg_C = compute_G1_commitment(commitments,betas);
	
	vector<G1> w(betas.size());
	vector<G2> u(betas.size());
	
	for(int i = 0;i< betas.size(); i++){
		
		w[i] = commitment.w[i];
		u[i] = commitment.u[i];

	}
	
	G1 P = compute_G1_commitment(w,betas);
	MIPP_verify_time = 0.0;
	
	
	int mipp_proof_size = MIPP(commitments,u,betas,w,commitment.C_T,P,Agg_C);
	commitment.Agg_C = Agg_C;
	commitment.r2 = r2;
	// Open aggregated polynomial
	
	
	vector<vector<F>> quotients = find_quontents(aggr_poly,r2);
	

	
	commitment.Proof.clear();
	if(aggr_poly.size() == 1ULL<<commitment.commit_bit_size){

	
		for(int i = 0; i < r2.size(); i++){
			G1 P;
			G1::mulVec(P, commitment.base[i].data(),quotients[i].data(), quotients[i].size());	
			commitment.Proof.push_back(P);
		}
	}else{
		int offset = commitment.commit_bit_size - (int)log2(aggr_poly.size());
		for(int i = 0; i < r2.size(); i++){
			G1 P;
			G1::mulVec(P, commitment.base[i+offset].data(),quotients[i].data(), quotients[i].size());	
			commitment.Proof.push_back(P);
		}
	}
	/*
	for(int i = 0; i < r2.size(); i++){
		P = compute_G1_commitment(commitment.base[i],quotients[i]);
		//G1::mulVec(P, commitment.base[i].data(),quotients[i].data(), quotients[i].size());	
		commitment.Proof.push_back(P);
	}*/
	

	
	
	auto e = high_resolution_clock::now();
	auto d = duration_cast<microseconds>(e - s);
	printf(">%lf\n", d.count()/1000000.0);
		
	//proving_time += d.count()/1000000.0;
	MIPP_verify(y,commitment);
	commitment.prove_time += d.count()/1000000.0;
	commitment.proof_size += (r2.size()+1)*sizeof(P) + sizeof(commitment.C_T) + mipp_proof_size;
	commitment.verification_time += MIPP_verify_time;
	MIPP_verify_time = 0.0;

}


void subvector_commit(vector<F> subvector, struct Comm &commitment){
	clock_t start,end;
	start = clock();
	G1::mulVec(commitment.subvector_C, commitment.subvector_pp1.data(), subvector.data(), subvector.size());
	end = clock();
	printf("Subvector Commit : %lf, size : %d\n",(float)(end-start)/(float)CLOCKS_PER_SEC,subvector.size() );

}


void KZG_open_streaming(int fp1,vector<F> x, struct Comm &commitment, size_t size){
	vector<F> v1(MAX_CHUNCK);
	vector<F> fv(size/MAX_CHUNCK);
	vector<G1> P(x.size());
	int tree_depth = (int)log2(MAX_CHUNCK);
	vector<G1> pp;
	G1 C_t;

	for(int i = 0; i < P.size(); i++){
		P[i] = commitment.G*F(0);
	}

	for(int i = 0; i < size/MAX_CHUNCK; i++){
		read_chunk(fp1,v1,MAX_CHUNCK);
		for(int j = 0; j < tree_depth; j++){
			vector<F> arr(MAX_CHUNCK/(2<<(j+1)));
			pp.resize(MAX_CHUNCK/(2<<(j+1)));
			read_pp(commitment.fp,pp,pp.size());
			for(int k = 0; k < MAX_CHUNCK/(2<<(j+1)); k++){
				arr[k] = v1[2*k+1] - v1[2*k];	
				v1[k] = v1[2*k] + arr[k]*x[x.size()-1-j];
			}
			
			G1::mulVec(C_t,pp.data(),arr.data(),arr.size());
			P[j] = P[j]+C_t;
		}
		fv[i] = v1[0];
	}

	for(int i = tree_depth; i < x.size(); i++){
		pp.resize(fv.size()/(2<<(i+1)));
		read_pp(commitment.fp,pp,pp.size());
			
		vector<F> arr(fv.size()/(2<<(i+1)));
		
		for(int k = 0; k < arr.size(); k++){
			arr[k] = fv[2*k + 1] - fv[2*k];
			fv[k] = fv[2*k] + arr[k]*x[x.size()-1-i];
		}
		G1::mulVec(P[i],pp.data(),arr.data(),arr.size());
	}


}


void KZG_open(vector<F> poly, vector<F> x, struct Comm &commitment){
	clock_t start,end;
	start = clock();
	vector<vector<F>> quotients = find_quontents(poly,x);
	
		
	commitment.Proof.clear();
	if(poly.size() == commitment.pp1.size()){
		for(int i = 0; i < x.size(); i++){
			G1 P;
			G1::mulVec(P, commitment.base[i].data(),quotients[i].data(), quotients[i].size());	
			commitment.Proof.push_back(P);
		}
	}else{
		int offset = (int)log2(commitment.pp1.size()) - (int)log2(poly.size());
		for(int i = 0; i < x.size(); i++){
			G1 P;
			G1::mulVec(P, commitment.base[i+offset].data(),quotients[i].data(), quotients[i].size());	
			commitment.Proof.push_back(P);
		}
	}
	
	end = clock();
	//proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
	//printf("Open time : %lf, size : %d\n",(float)(end-start)/(float)CLOCKS_PER_SEC,poly.size() );

}

void subvector_open(vector<F> poly, vector<F> x, struct Comm &commitment){
	clock_t start,end;
	start = clock();
	vector<vector<F>> quotients = find_quontents(poly,x);
	for(int i = 0; i < x.size(); i++){
		G1 P;
		G1::mulVec(P, commitment.subvector_base[i].data(),quotients[i].data(), quotients[i].size());	
		commitment.Proof.push_back(P);
	}
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;

}

void KZG_verify(vector<F> x, F y, struct Comm &commitment){
	
	GT check_P,Pairing_prod;
	vector<G2> diff;
	vector<G1> proofs;
	G1 test = commitment.G*y;
	GT r;
	int pp_bit_size = (int)log2(commitment.pp1.size());
	if(pp_bit_size == x.size()){
		for(int i = 0; i < commitment.Proof.size(); i++){
			//test = test + commitment.Proof[i]*commitment.secret[i];
			
			proofs.push_back(commitment.Proof[i]);
			diff.push_back(commitment.pp2[i] + commitment.H*(F(0)-x[i]));
			//diff.push_back(commitment.pp2[x.size()-1-i] + commitment.H*(F(0)-x[x.size()-1-i]));
		}
		test = test + commitment.C*(F(-1));
		diff.push_back(commitment.H);
		proofs.push_back(commitment.C*(F(-1))+commitment.G*y);
	}else{
		int bit_size = x.size();
		for(int i = 0; i < commitment.Proof.size(); i++){
			//test = test + commitment.Proof[i]*commitment.secret[i];
			
			proofs.push_back(commitment.Proof[i]);
			diff.push_back(commitment.pp2[pp_bit_size - bit_size+ i] + commitment.H*(F(0)-x[i]));
			//diff.push_back(commitment.pp2[x.size()-1-i] + commitment.H*(F(0)-x[x.size()-1-i]));
		}
		test = test + commitment.C*(F(-1));
		diff.push_back(commitment.H);
		proofs.push_back(commitment.C*(F(-1))+commitment.G*y);
	}
	
	mcl::bn::millerLoopVec(Pairing_prod,proofs.data(),diff.data(),x.size()+1);
	
	finalExp(Pairing_prod,Pairing_prod);

	if((Pairing_prod).isOne() != 1){
		//printf("Error in open\n");
		//exit(-1);
	}
}

void _compute_GT_commitment(vector<G1> &x, vector<G2> &y,GT &res, int idx){
	int size = x.size()/threads;
	int pos = idx*size;
	G1 *g = (G1 *)malloc(size*sizeof(G1));
	G2 *p = (G2 *)malloc(size*sizeof(G2));
	
	for(int i = 0; i < size; i++){
		g[i] = x[pos+i];
		p[i] = y[pos+i];
	}
	mcl::bn::millerLoopVec(res, g,p, size);
}


GT compute_pairing_commitment(vector<G1> &x, vector<G2> &ck){
	GT res;
	
	
	if(threads == 1 || x.size() <= 4*threads){
		
		mcl::bn::millerLoopVec(res,x.data(),ck.data(),x.size());
	}else{
		

		GT _res[threads];
		thread workers[threads];
		for(int i = 0; i < threads; i++){
			workers[i] =  thread(&_compute_GT_commitment,ref(x),ref(ck),ref(_res[i]),i);
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}
		res = _res[0];
		for(int i = 1; i < threads; i++){
			res = res + _res[i];
		}
	
	}
	return res;
}

void _compute_G1_commitment(vector<G1> &ck, vector<F> &x,G1 &res, int idx){
	int size = ck.size()/threads;
	int pos = idx*size;
	G1 *g = (G1 *)malloc(size*sizeof(G1));
	F *p = (F *)malloc(size*sizeof(F));
	for(int i = 0; i < size; i++){
		g[i] = ck[pos+i];
		p[i] = x[pos+i];
	}
	G1::mulVec(res, g,p, size);
}

G1 compute_G1_commitment( vector<G1> &ck,vector<F> &x){
	G1 res;
	if(threads == 1 || x.size() <= 4*threads){
		G1::mulVec(res, ck.data(),x.data(), x.size());
	}else{
		
		G1 _res[threads];
		thread workers[threads];
		for(int i = 0; i < threads; i++){
			workers[i] =  thread(&_compute_G1_commitment,ref(ck),ref(x),ref(_res[i]),i);
		}
		for(int i = 0; i < threads; i++){
			workers[i].join();
		}
		res = _res[0];
		for(int i = 1; i < threads; i++){
			res = res + _res[i];
		}

	}
	return res;	
}


void _base_compute(vector<G1> &A,vector<G1> &A_L,vector<G1> &A_R,vector<G2> &u,vector<G2> &u_l,vector<G2> &u_r,vector<F> &b,vector<F> &B_L,vector<F> &B_R,vector<G1> &w,vector<G1> &w_l,vector<G1> &w_r, F x, F x_inv,int idx){
	int size = A.size()/threads;
	int pos = idx*size;
	for(int j = pos; j < pos+size; j++){
		A[j] = (A_L[j] + A_R[j]*x);
		u[j] = (u_l[j] + u_r[j]*x_inv);
		b[j] = (B_L[j] + B_R[j]*x_inv);
		w[j] = (w_l[j] + w_r[j]*x);
	}
}

int TIPP(vector<G1> A, vector<G2> B, vector<G1> w, vector<G2> u, GT C1, GT C2, GT P , F s){
	int iter = (int)log2(A.size());
	// rescale A
	F scale = F(1);
	for(int i = 0; i < A.size(); i++){
		A[i] = A[i]*scale;
		scale *= s;
	}
	int proof_size = 0;
	// run GIPA
	F x,x_inv;
	
	for(int i = 0; i < iter; i++){
		vector<G1> A_L(A.size()/2),A_R(A.size()/2);
		vector<G2> B_L(A.size()/2),B_R(A.size()/2);
		vector<G2> u_l(A.size()/2),u_r(A.size()/2);
		vector<G1> w_l(A.size()/2),w_r(A.size()/2);
		for(int j = 0; j < A.size()/2; j++){
			A_L[j] = A[j];
			A_R[j] = A[j+A.size()/2];
			B_L[j] = B[j];
			B_R[j] = B[j+A.size()/2];
			u_l[j] = u[j];
			u_r[j] = u[j+A.size()/2];
			w_l[j] = w[j];
			w_r[j] = w[j+A.size()/2];
		}
		GT Z_L = compute_pairing_commitment(A_R,B_L);
		GT Z_R = compute_pairing_commitment(A_L,B_R);
		GT C_1L = compute_pairing_commitment(A_R,u_l);
		GT C_1R = compute_pairing_commitment(A_L,u_r);
		GT C_2L = compute_pairing_commitment(w_r,B_L);
		GT C_2R = compute_pairing_commitment(w_l,B_R);
		proof_size += 4*sizeof(Z_L);
		x.setByCSPRNG();
		x_inv.inv(x_inv,x);
		A.resize(A_L.size());
		u.resize(A_L.size());
		B.resize(A_L.size());
		w.resize(A_L.size());
		for(int j = 0; j < A_L.size(); j++){
			A[j] = (A_L[j] + A_R[j]*x);
			u[j] = (u_l[j] + u_r[j]*x_inv);
			B[j] = (B_L[j] + B_R[j]*x_inv);
			w[j] = (w_l[j] + w_r[j]*x);
		}
		clock_t s,e;
		s = clock();

		C_1L = C_1L;
		C_1R = C_1R;
		C_2L = C_2L;
		C_2R = C_2R;
		
		C_1L.pow(C_1L,C_1L,x);
		C_1R.pow(C_1R,C_1R,x_inv);

		C_2L.pow(C_2L,C_2L,x);
		C_2R.pow(C_2R,C_2R,x_inv);
		C1 = C_1L + C1+ C_1R;
		C2 = C_2L + C2+ C_2R;	

		e = clock();
		
		MIPP_verify_time += (double)(e-s)/(double)CLOCKS_PER_SEC;
	}
	return proof_size;
}

aggregation_proof Aggregate(vector<vector<G1>> P, vector<G1> w, vector<G2> u, vector<vector<F>> x, vector<F> y, G2 H, int lookups, Comm pp){
	// Aggregate proofs
	// commit phase
	aggregation_proof Pr; 
	int poly_degree = (int)(x[0].size());
	vector<vector<G1>> C_Q(P[0].size());
	vector<vector<G1>> C_Q_rescale(lookups);
	vector<vector<G2>> C_I(lookups);
	vector<G1> Y(P.size());
	vector<GT> Proof_commitments(P[0].size()); 
	vector<GT> index_commitments(lookups);
	vector<GT> Pairing_prod(lookups);
	vector<GT> Prod1(P[0].size());
	Pr.proof_size = 0;
	Pr.verification_time = 0;
	Pr.proving_time = 0;
	for(int i = 0; i <poly_degree; i++){
		C_Q[i].resize(P.size());
		for(int j = 0; j < P.size(); j++){
			C_Q[i][j] = P[j][i];
		}
	}
	
	

	clock_t start,end;
	start = clock();
	
	for(int i = 0; i < Y.size(); i++){
		Y[i] = pp.G*(y[i]);
	}
	for(int i = poly_degree - lookups; i < poly_degree; i++){
		C_I[i - (poly_degree - lookups)].resize(P.size());
		for(int j = 0; j < P.size(); j++){
			C_I[i - (poly_degree - lookups)][j] = pp.H*(-x[j][i]);
		}
	}
	
	for(int i = 0; i < P[0].size(); i++){
		Proof_commitments[i] = compute_pairing_commitment(C_Q[i],u);
	}
	for(int i = 0; i < C_I.size(); i++){
		index_commitments[i] = compute_pairing_commitment(w,C_I[i]);
	}
	GT C_y = compute_pairing_commitment(Y,u);
	
	F s;s.setByCSPRNG();
	vector<F> pow;
	F scale = F(1);
	for(int i = 0; i < P.size(); i++){
		pow.push_back(scale);
		scale *= F_ONE;
	}
	vector<G1> Q_G1com(P[0].size());
	for(int i = 0; i < P[0].size(); i++){
		Q_G1com[i] = compute_G1_commitment(C_Q[i],pow);
		if(i >= poly_degree - lookups){
			C_Q_rescale[i- (poly_degree - lookups)].resize(P.size());
			for(int j = 0; j < P.size(); j++){
				C_Q_rescale[i - (poly_degree - lookups)][j] = C_Q[i][j]*pow[j];
			}
			Pairing_prod[i - (poly_degree - lookups)] = compute_pairing_commitment(C_Q_rescale[i - (poly_degree - lookups)],C_I[i-(poly_degree - lookups)]);
		}	
	}
	
	vector<F> rand(P[0].size()),rand_2;
	for(int i = 0; i < rand.size(); i++){
		rand[i].setByCSPRNG();
		if(i >= poly_degree - lookups){
			rand_2.push_back(rand[i]);
		}
	}

	// Batch the statements into one
	vector<G1> aggregated_G1_TIPP(P.size()),aggregated_G1_MIPP(P.size());
	vector<G1> buff(rand.size()),buff_2(lookups);
	vector<G2> buff_3(lookups);
	for(int i = 0 ; i< aggregated_G1_TIPP.size(); i++){
		for(int k = 0; k < rand.size(); k++){
			buff[k] = P[i][k];
		}
		aggregated_G1_MIPP[i] = compute_G1_commitment(buff,rand);
		
		for(int k = 0; k < lookups; k++){
			buff_2[k] = C_Q_rescale[k][i];
		}
		//aggregated_G1_TIPP[i] = compute_G1_commitment(buff_2,rand_2);
	}
	end = clock();
	
	Pr.proving_time = (double)(end-start)/(double)(CLOCKS_PER_SEC);


	

	start = clock();
	for(int i = 0; i < lookups; i++){
		TIPP(C_Q_rescale[i],C_I[i],w,u,Proof_commitments[i+(poly_degree-lookups)],index_commitments[i],Pairing_prod[i],s);
	}
	Proof_commitments[0].pow(Proof_commitments[0],Proof_commitments[0],rand[0]);
	GT aggr_comm = Proof_commitments[0];
	G1 U;
	G2 h1;
	for(int i = 1; i < Proof_commitments.size(); i++){
		Proof_commitments[i].pow(Proof_commitments[i],Proof_commitments[i],rand[i]);
		aggr_comm = aggr_comm*Proof_commitments[i];
		
	}
	Pr.proof_size += MIPP(aggregated_G1_MIPP,u,pow,w,aggr_comm,U,U);
	end = clock();
	
	Pr.proving_time += (double)(end-start)/(double)(CLOCKS_PER_SEC);
	Pr.verification_time= MIPP_verify_time;
	MIPP_verify_time = 0.0;
	Pr.C_I = index_commitments;

	Pr.C_y = C_y;
	Pr.H = C_I;
	Pr.Y = Y;

	return Pr;
}

int MIPP(vector<G1> A, vector<G2> u,vector<F> b, vector<G1> w, GT T, G1 U,G1 U2){
		vector<MIPP_Proof> Proof;
	
	int iter = (int)log2(A.size());
	comm_size = 0;
	for(int i = 0; i < iter; i++){
		MIPP_Proof P;
		vector<G1> A_L(A.size()/2),A_R(A.size()/2);
		vector<F> B_L(A.size()/2),B_R(A.size()/2);
		vector<G2> u_l(A.size()/2),u_r(A.size()/2);
		vector<G1> w_l(A.size()/2),w_r(A.size()/2);
		for(int j = 0; j < A.size()/2; j++){
			A_L[j] = A[j];
			A_R[j] = A[j+A.size()/2];
			B_L[j] = b[j];
			B_R[j] = b[j+A.size()/2];
			u_l[j] = u[j];
			u_r[j] = u[j+A.size()/2];
			w_l[j] = w[j];
			w_r[j] = w[j+A.size()/2];
		}
		// Send to the verifier
		P.Z_L = compute_G1_commitment(A_R,B_L);
		P.Z_R = compute_G1_commitment(A_L,B_R);
		
		P.G_L = compute_G1_commitment(w_r,B_L);
		P.G_R = compute_G1_commitment(w_l,B_R);
		P.GT_L = compute_pairing_commitment(A_L,u_r);
		P.GT_R = compute_pairing_commitment(A_R,u_l);
		comm_size += 2*sizeof(P.GT_L);
		comm_size += 4*sizeof(P.G_L);

		clock_t s,e;
		s = clock();
		F x,x_inv;
		x.setByCSPRNG();
		x_inv.inv(x_inv,x); 
		
		GT t1,t2;
		t1.pow(P.GT_L,P.GT_L,x_inv);
		
		t2.pow(P.GT_R,P.GT_R,x);
		t1 = t1*T*t2;
		G1 v1,v2;
		v1 = P.G_L*x;
		v2 = P.G_R*x_inv;
		v1 = v1+v2+U;
		v1 = P.G_L*x;
		v2 = P.G_R*x_inv;
		v1 = v1+v2+U;
		e = clock();
		
		MIPP_verify_time += (double)(e-s)/(double)CLOCKS_PER_SEC;

		P.x = x;
		P.x_inv = x_inv;
		Proof.push_back(P);
		if(x_inv*x != F(1)){
			printf("Error \n");
			exit(-1);
		}
		// Reduce vectors
		A.resize(A_L.size());
		u.resize(A_L.size());
		b.resize(A_L.size());
		w.resize(A_L.size());
		if(threads == 1 || A_L.size() <= threads){
			for(int j = 0; j < A_L.size(); j++){
				A[j] = (A_L[j] + A_R[j]*x);
				u[j] = (u_l[j] + u_r[j]*x_inv);
				b[j] = (B_L[j] + B_R[j]*x_inv);
				w[j] = (w_l[j] + w_r[j]*x);
			}			
		}else{
			thread workers[threads];
			for(int j = 0; j < threads; j++){
				workers[j] = thread(&_base_compute,ref(A),ref(A_L),ref(A_R),ref(u),ref(u_l),ref(u_r),ref(b),ref(B_L),ref(B_R),ref(w),ref(w_l),ref(w_r),x,x_inv,j);
			}
			for(int j = 0; j < threads; j++){
				workers[j].join();
			}

		}
	}
	return comm_size;
}


void test_MIPP(){
	int size = 1024*16;
	vector<G1> ck1,A;
	vector<F> B;
	vector<G2> ck2;
	char rand[256];
	G2 h;
	mcl::bn::hashAndMapToG2(h,rand,256);
	G1 g = mcl::bn::getG1basePoint();

	for(int i = 0; i < size; i++){
		F num;
		num.setByCSPRNG();
		B.push_back(num);
		ck1.push_back(g*num);
		A.push_back(g*(num+num));
		ck2.push_back(h*num); 
	}
	MIPP(A,ck2,B,ck1,compute_pairing_commitment(A,ck2),compute_G1_commitment(ck1,B),compute_G1_commitment(A,B));

}

void copy_pp(MIPP_Comm &commitment1,MIPP_Comm &commitment2){
	commitment2.bit_size = commitment1.bit_size;
	commitment2.commit_bit_size = commitment1.commit_bit_size;
	commitment2.pp1 = commitment1.pp1;
	commitment2.pp2 =commitment1.pp2;
	commitment2.base = commitment1.base;
	commitment2.precompute = commitment1.precompute;
	commitment2.H = commitment1.H ;
	commitment2.G = commitment1.G ;
	commitment2.bits = commitment1.bits ;
	commitment2.w = commitment1.w;
	commitment2.u = commitment1.u;
	commitment2.precomputed_pp = commitment1.precomputed_pp;
}

void MIPP_gen(int bit_size,MIPP_Comm &commitment, bool precompute,bool bits){
	struct Comm temp_com;
	commitment.bit_size = bit_size;
	if(!bits){

		if(commitment.bit_size%2 == 0){
			commitment.commit_bit_size = commitment.bit_size/2 + 2 ;
		}else{
			commitment.commit_bit_size = (commitment.bit_size+1)/2 + 2;
		}
	}else{
		if(commitment.bit_size%2 == 0){
			commitment.commit_bit_size = commitment.bit_size/2 + 4;
		}else{
			commitment.commit_bit_size = (commitment.bit_size+1)/2 + 4;
		}
	}

	if(precompute && bits){
		commitment.commit_bit_size = commitment.bit_size;
	}
	generate_pp(temp_com,commitment.commit_bit_size);
	
	commitment.pp1 = temp_com.pp1;
	commitment.pp2 = temp_com.pp2;
	commitment.base = temp_com.base;
	commitment.precompute = precompute;
	commitment.H = temp_com.H;
	commitment.G = temp_com.G;
	commitment.bits = bits;
	commitment.pp1_cached = temp_com.pp1_cached;

	commitment.w.resize(1<<(commitment.bit_size- commitment.commit_bit_size ));
	commitment.u.resize(1<<(commitment.bit_size- commitment.commit_bit_size ));
	thread worker[16];
	vector<F> base;
	for(int i = 0; i < commitment.w.size(); i++){
		base.push_back(F(1+i));
	}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp1,ref(commitment.w),ref(base),commitment.G,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}
	for(int i = 0; i < 16; i++){
		worker[i] = thread(&generate_pp2,ref(commitment.u),ref(base),commitment.H,i);
	}
	for(int i = 0; i < 16; i++){
		worker[i].join();
	}
	//for(int i = 0; i < 1<<(commitment.bit_size- commitment.commit_bit_size ); i++){
	//	commitment.w.push_back(commitment.G*F(1+i));
	//	commitment.u.push_back(commitment.H*F(1+i));
	//}

	if(precompute && bits == false){
		vector<vector<G1>> precomputed_pp(255);
		if(Q == 16){
			precomputed_pp.resize(510);
		}
		precomputed_pp[0] = commitment.pp1;
		for(int i = 1; i < 255; i++){
			for(int j = 0; j < precomputed_pp[i-1].size(); j++){
				precomputed_pp[i].push_back(precomputed_pp[i-1][j] + precomputed_pp[0][j]);
			}
		}
		if(Q == 16){
			for(int i = 255; i < 510; i++){
				for(int j = 0; j < precomputed_pp[0].size(); j++){
					precomputed_pp[i].push_back(precomputed_pp[i-1][j] + precomputed_pp[254][j]);
				}
			}
		}
		commitment.precomputed_pp = precomputed_pp;
	}


}


void MIPP_fold_commit(vector<F> f1, vector<F> bits, MIPP_Comm &commitment){
	clock_t start,end;
	start = clock();
	int size = 1<<(commitment.commit_bit_size);
	

	for(int i = 0; i < 1<< (commitment.bit_size - commitment.commit_bit_size); i++){
		vector<F> exp;
		unordered_map<F,int> table;
		int counter = 0;
		vector<F> arr(size);
		vector<F> elements;
		G1 C;
		for(int j = 0; j < size; j++){
			arr[j] = f1[i*size + j];
		}
	
		for(int j = 0; j < size; j++){
			if(f1[j] == F(0) || bits[i*size + j] == F(0)) continue;
			if(table.find(f1[j]) == table.end()){
				table[f1[j]] = counter++;
				elements.push_back(f1[j]);
			}
		}
		vector<G1> bases;
		for(int i = 0; i < elements.size(); i++){
			bases.push_back(commitment.G*F(0));
		}
	
		for(int j = 0; j < size; j++){
			if(f1[j] == F(0) || bits[i*size + j] == F(0)) continue;
	
			int idx = table[f1[j]];
			bases[idx] = bases[idx] + commitment.pp1[j];
			
		}
	
		commitment.Commitments.push_back(compute_G1_commitment(bases,elements));
	}
	//commitment.C_T = compute_pairing_commitment(commitment.Commitments,commitment.u);
	end = clock();
	printf("%lf\n", (float)(end-start)/(float)CLOCKS_PER_SEC);
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
}


void _MIPP_predicate_commit(vector<int> &mapping, MIPP_Comm &commitment, vector<G1> &commitments,int threads , int idx){
	int L = (1<<(commitment.bit_size - commitment.commit_bit_size))/threads;
	int pos = L*idx;
	int size = 1<<(commitment.commit_bit_size-8);
	vector<int> arr(size);
	for(int i = pos; i < pos + L; i++){
		G1 C = commitment.G*F(0);
		for(int j = 0; j  < size; j++){
			arr[j] = mapping[i*size + j];
		}
		for(int j = 0; j < size; j++){
			C = C + commitment.pp1[256*j + arr[j]];
		}
		commitments.push_back(C);
	}
}




void _aggregate(vector<F> &aggr_poly,vector<F> &betas,vector<F> &poly,int L,int L2, int idx){
	int size = L/threads;
	int pos = size*idx;
	for(int i = 0; i < L2; i++){
		for(int j = pos; j < pos + size; j++){
			aggr_poly[j] += betas[i]*poly[i*L+j];
		}
	}
}






// Return indexes from cached quotients
vector<vector<int>> get_path(int pos,int nodes_bit){
	int new_pos = 0;
	vector<vector<int>> indexes(2);
	for(int i = nodes_bit-1; i >= 0; i--){
		if(pos%2 == 1){
			new_pos += 1<<i;	
		}
	 	pos = pos / 2;
	}
	

	int temp_pos = new_pos;
	indexes[0].resize(nodes_bit);
	for(int i = nodes_bit-1; i >= 0; i--){
		indexes[0][i] = 0;
		if(temp_pos&1 == 1){
			indexes[0][i] = 1;
		}
		temp_pos = temp_pos >> 1;
	}
	
	indexes[1].resize(nodes_bit);
	indexes[1][nodes_bit-1] = new_pos/2;
	for(int i = nodes_bit-2; i >= 0; i--){
		indexes[1][i] = indexes[1][i+1]/2;
	}
	return indexes;
}

vector<vector<G1>> SVL_commit(vector<F> table,Comm &commitment,int nodes){
	commit(table,commitment);
	return hyperproofs_openall(table,commitment,nodes);

}

vector<G1> get_proof(vector<F> f_i, vector<F> x, int pos,vector<vector<int>> &indexes, int M, int N, vector<vector<G1>> &cached_quotients, Comm &commitment ){
	vector<G1> P;
	int bitsize = (int)log2(M*N);
	int nodes_bitsize = (int)log2(M);
	subvector_open(f_i,x,commitment);
	indexes = get_path(pos,nodes_bitsize);

	P.insert(P.begin(),commitment.Proof.begin(),commitment.Proof.end());
	for(int i = 0; i < nodes_bitsize; i++){
		P.push_back(cached_quotients[i][indexes[1][i]]);
	}
	commitment.Proof.clear();
	return P;
}

single_SVL_Proof single_SVL_prove(vector<vector<F>> table, vector<vector<G1>> &cached_quotients,vector<F> x,int pos,Comm &commitment){
	int bitsize = (int)log2(table.size()*table[0].size());
	int nodes_bitsize = (int)log2(table.size());
	vector<F> path = table[pos];
	
	subvector_open(path,x,commitment);
	
	vector<G1> C_q(nodes_bitsize);
	vector<G2> C_h(nodes_bitsize);
	vector<G2> pp2(nodes_bitsize);
	vector<G1> pp1(nodes_bitsize);
	vector<vector<int>> indexes = get_path(pos,nodes_bitsize);
	for(int i = 0; i < nodes_bitsize; i++){
		C_q[i] = cached_quotients[i][indexes[1][i]];
		C_h[i] = commitment.pp2[i] - commitment.H*(F(indexes[0][i]));
		pp1[i] = commitment.ipp_pp1[i];
		pp2[i] = commitment.ipp_pp2[i];
	}


	GT C_debug;
	//mcl::bn::millerLoopVec(C_debug,C_q.data(),C_h.data(),nodes_bitsize);
	
	
	// Commit to the quotients and evaluations
	GT C1;
	mcl::bn::millerLoopVec(C1,C_q.data(),pp2.data(),nodes_bitsize);
	GT C2;
	mcl::bn::millerLoopVec(C2,pp1.data(),C_h.data(),nodes_bitsize);
	// Select and commit blinding factors
	vector<G1> b1(nodes_bitsize);
	vector<G2> b2(nodes_bitsize);
	for(int i = 0; i < nodes_bitsize; i++){
		F num;
		num.setByCSPRNG();
		b1[i] = commitment.G*num;
		num.setByCSPRNG();
		b2[i] = commitment.H*num;
	}
	GT Cb1;
	mcl::bn::millerLoopVec(Cb1,b1.data(),pp2.data(),nodes_bitsize);
	GT Cb2;
	mcl::bn::millerLoopVec(Cb2,pp1.data(),b2.data(),nodes_bitsize);
	GT Cz2;
	mcl::bn::millerLoopVec(Cz2,b1.data(),b2.data(),nodes_bitsize);
	GT Cz1,Cz1a,Cz1b;
	mcl::bn::millerLoopVec(Cz1a,b1.data(),C_h.data(),nodes_bitsize);
	mcl::bn::millerLoopVec(Cz1b,C_q.data(),b2.data(),nodes_bitsize);
	Cz1 = Cz1a*Cz1b;
	F c;
	c.setByCSPRNG();
	vector<G1> A;
	vector<G2> B;
	for(int i = 0; i < nodes_bitsize; i++){
		A.push_back(C_q[i]+b1[i]*c);
		B.push_back(C_h[i]+b2[i]*c);
	}


	vector<F> bb1(nodes_bitsize),bb2(nodes_bitsize),y(nodes_bitsize);
	vector<G1> Gbb1(nodes_bitsize),Gminus(nodes_bitsize);
	vector<G2> Gbb2(nodes_bitsize);
	GT Cbb1,Cbb2,C_minus;
	F z;
	for(int i = 0; i <nodes_bitsize; i++){
		y[i].setByCSPRNG();
		bb1[i].setByCSPRNG();
		bb2[i].setByCSPRNG();
		Gbb1[i] = commitment.G*bb1[i];
		Gbb2[i] = commitment.H*bb2[i];
		Gminus[i] = commitment.G*(F(indexes[0][i]-1));
	}
	z.setByCSPRNG();
	mcl::bn::millerLoopVec(Cbb1,Gbb1.data(),pp2.data(),nodes_bitsize);
	mcl::bn::millerLoopVec(Cbb2,pp1.data(),Gbb2.data(),nodes_bitsize);
	mcl::bn::millerLoopVec(C_minus,Gminus.data(),pp2.data(),nodes_bitsize);

	GT t1,t2;
	vector<G1> t1G;
	vector<G2> t1H;
	for(int i = 0; i < nodes_bitsize; i++){
		t1G.push_back((Gminus[i]+commitment.G*z)*y[i]);
		t1H.push_back(Gbb2[i]);
	}
	for(int i = 0; i < nodes_bitsize; i++){
		t1G.push_back(Gbb1[i]);
		t1H.push_back((commitment.H*F(indexes[0][i]) - commitment.H*z)*y[i]);
	}
	
	mcl::bn::millerLoopVec(t1,t1G.data(),t1H.data(),t1G.size());
	mcl::bn::millerLoopVec(t2,Gbb1.data(),Gbb2.data(),Gbb1.size());

	F r;
	r.setByCSPRNG();
	vector<G1> Ab;
	vector<G2> Bb;
	for(int i = 0; i < bitsize; i++){
		Ab.push_back(Gminus[i] + (Gbb1[i]*r));
		Bb.push_back(commitment.H*F(indexes[0][i]) + Gbb2[i]*r);	
	}

	//verification_time += d.count()/1000000.0;



	single_SVL_Proof Proof;
	Proof.nodes_bitsize = nodes_bitsize;
	Proof.bitsize = bitsize;
	Proof.plaintext_proofs = commitment.Proof;
	Proof.C1 = C1;
	Proof.C2 = C2;
	Proof.Cb1 = Cb1;
	Proof.Cb2 = Cb2;
	Proof.Cz1 = Cz1;
	Proof.Cz2 = Cz2;
	Proof.C_debug = C_debug;
	Proof.c = c;
	Proof.A = A;
	Proof.B = B;
	// Bit proofs
	Proof.Cbb1 = Cbb1;
	Proof.Cbb2 = Cbb2;
	Proof.C_minus = C_minus;
	Proof.t1 = t1;
	Proof.t2 = t2;
	Proof.r = r;
	Proof.z = z;
	Proof.y = y;
	Proof.Ab = Ab;
	Proof.Bb = Bb;


	return Proof;
}

void single_SVL_verify(single_SVL_Proof Proof,vector<F> x,F y,Comm &commitment){
	int nodes_bitsize = Proof.nodes_bitsize;
	vector<G1> C_q;
	vector<G2> C_h;

	for(int i = 0; i < Proof.plaintext_proofs.size(); i++){
		C_q.push_back(Proof.plaintext_proofs[i]);
		C_h.push_back(commitment.pp2[i+nodes_bitsize] - commitment.H*(x[i]));
	}
	printf("Proofs : %d\n", Proof.plaintext_proofs.size());

	C_q.push_back(commitment.G*(y)- commitment.C);//res*F(-1);
	C_h.push_back(commitment.H);
	GT C_T;
	mcl::bn::millerLoopVec(C_T,C_q.data(),C_h.data(),C_q.size());
	F c = Proof.c;
	/*
	GT check1,check2,C_prod;
	mcl::bn::millerLoopVec(check1,Proof.A.data(),commitment.ipp_pp2.data(),Proof.A.size());
	mcl::bn::millerLoopVec(check2,commitment.ipp_pp1.data(),Proof.B.data(),Proof.B.size());
	mcl::bn::millerLoopVec(C_prod,Proof.A.data(),Proof.B.data(),Proof.B.size());
	

	Proof.Cb1.pow(Proof.Cb1,Proof.Cb1,-c);
	Proof.C1.pow(Proof.C1,Proof.C1,F(-1));
	check1 = check1*Proof.Cb1*Proof.C1;
	Proof.Cb2.pow(Proof.Cb2,Proof.Cb2,-c);
	Proof.C2.pow(Proof.C2,Proof.C2,F(-1));
	check2 = check2*Proof.Cb2*Proof.C2;
	

	finalExp(check1,check1);
	finalExp(check2,check2);
	
	Proof.C_debug = C_T*Proof.C_debug;
	finalExp(Proof.C_debug,Proof.C_debug);
	

	Proof.Cz1.pow(Proof.Cz1,Proof.Cz1,c);
	Proof.Cz2.pow(Proof.Cz2,Proof.Cz2,c*c);
	C_prod.pow(C_prod,C_prod,-F(1));
	C_T.pow(C_T,C_T,-F(1));
	
	C_prod = C_prod*C_T*Proof.Cz1*Proof.Cz2;
	
	finalExp(C_prod,C_prod);

	
	if((check1).isOne() != 1){
		printf("Error in open\n");
		exit(-1);
	}
	if((check2).isOne() != 1){
		printf("Error in open\n");
		exit(-1);		
	}
	if(C_prod.isOne()!=1){
		printf("Error in open C_prod\n");
		exit(-1);
	}

	C_q.clear();
	C_h.clear();
	GT C_bits;
	for(int i = 0; i < nodes_bitsize; i++){
		C_q.push_back(commitment.ipp_pp1[i]);
		C_h.push_back(commitment.pp2[i]);
	}
	mcl::bn::millerLoopVec(C_bits,C_q.data(),C_h.data(),C_h.size());
	C_bits = Proof.C2*C_bits;

	vector<G1> Ab_new;
	vector<G2> Bb_new;
	for(int i = 0; i < Proof.Ab.size(); i++){
		Ab_new.push_back(Proof.Ab[i]*Proof.y[i] + commitment.G*(Proof.z));
		Bb_new.push_back(Proof.Bb[i] - commitment.H*Proof.z);
	}

	mcl::bn::millerLoopVec(check1,Proof.Ab.data(),commitment.ipp_pp2.data(),Proof.Ab.size());
	mcl::bn::millerLoopVec(check2,commitment.ipp_pp1.data(),Proof.Bb.data(),Proof.B.size());
	check1.inv(check1,check1);
	check2.inv(check2,check2);
	Proof.Cbb2.pow(Proof.Cbb2,Proof.Cbb2,Proof.r);
	Proof.Cbb1.pow(Proof.Cbb1,Proof.Cbb1,Proof.r);
	check2 = check2*Proof.Cbb2*C_bits;
	check1 = check1*Proof.Cbb1*Proof.C_minus;
	//mcl::bn::millerLoopVec(C_prod,Proof.A.data(),Proof.B.data(),Proof.B.size());
	finalExp(check1,check1);
	finalExp(check2,check2);
	if(check1.isOne() != 1 ){
		//printf("Error in binary check 1\n");
	}
	if(check2.isOne() != 1){
		//printf("Error in binary check 2\n");		
	}

	GT final_product,C_r;
	mcl::bn::millerLoopVec(final_product,Ab_new.data(),Bb_new.data(),Proof.B.size());
	vector<G1> g_final;
	vector<G2> h_final;
	for(int i = 0; i < nodes_bitsize; i++){
		g_final.push_back(commitment.G*Proof.y[i]);
		h_final.push_back(commitment.H);
	}
	mcl::bn::millerLoopVec(C_r,g_final.data(),h_final.data(),g_final.size());
	final_product.inv(final_product,final_product);
	Proof.t1.pow(Proof.t1,Proof.t1,Proof.r);
	Proof.t2.pow(Proof.t2,Proof.t2,Proof.r*Proof.r);
	C_r.pow(C_r,C_r,Proof.z -Proof.z*Proof.z );
	final_product = final_product*Proof.t1*Proof.t2*C_r;
	if(final_product.isOne() != 1){
		//printf("Error in binary check 3\n");		
	}
	*/
		
	
}


void compute_proofs(vector<F> &poly,Comm &commitment,vector<vector<G1>> &proof_tree, int level, int nodes){
	if(level == nodes){
		G1 P;
		//printf("%d,%d,%d,%d\n",level,commitment.base[level].size(),commitment.base[level-1].size(),commitment.subvector_pp1.size() );
		
		G1::mulVec(P, commitment.base[level-1].data(),poly.data(), poly.size());	
		proof_tree[level].push_back(P);
		//printf(">> %d\n",proof_tree[level].size() );
		return;
	}
	vector<F> poly1(poly.size()/2),poly2(poly.size()/2);
	vector<F> quotient(poly.size()/2);
	for(int i = 0; i < poly.size()/2; i++){
		poly1[i] = poly[2*i];
		poly2[i] = poly[2*i + 1];
		//poly1[i] = poly[i];
		//poly2[i] = poly[i + poly.size()/2];
		quotient[i] = poly2[i] - poly1[i];
	}
	G1 P;
	//printf("%d,%d,%d\n",level,commitment.base[level].size(),quotient.size() );
	G1::mulVec(P, commitment.base[level].data(),quotient.data(), quotient.size());	
	
	proof_tree[level].push_back(P);

	compute_proofs(poly1,commitment,proof_tree,level+1,nodes);
	compute_proofs(poly2,commitment,proof_tree,level+1,nodes);
}


vector<vector<G1>> hyperproofs_openall(vector<F> poly,Comm &commitment, int nodes){
	
	vector<vector<G1>> proof_tree((int)log2(nodes) + 1);
	//printf("Preprocessing Starts\n");
	clock_t start,end;
	start = clock();
	compute_proofs(poly,commitment,proof_tree,0,(int)log2(nodes));	
	end = clock();

	//printf("Preprocessing time : %lf\n",(float)(end-start)/(float)CLOCKS_PER_SEC );
	return proof_tree;

}
