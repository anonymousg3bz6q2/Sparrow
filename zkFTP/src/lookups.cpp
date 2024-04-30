#include "lookups.h"
#include "mimc.h"
#include "utils.hpp"
#include "witness_stream.h"
#include "space_efficient_sumcheck.h"
#include "Poly_Commit.h"
vector<vector<F>> lookup_read,lookup_write;
vector<vector<vector<F>>> output,mem_init;

int seg_bitsize = 8;
vector<long long int> lookup_input;
int domain;
int	quantization_level;
extern stream_descriptor lookup_stream;
extern size_t MAX_CHUNCK;
extern MIPP_Comm pp;
extern int _commitment_test;
// Memory consistency check : Read/Write_transcript [address, counter]. 
// Compress memories with linear combination
// + Perform mul tree for read_transcript write_transcript
// + Perform mul tree for input/output transcript
lookup_proof mem_consistency(vector<vector<vector<F>>> output_transcript,vector<vector<vector<F>>> input_transcript,
	vector<vector<vector<F>>> read_transcript,vector<vector<vector<F>>> write_transcript, vector<vector<F>> indexes, F previous_r){

	vector<vector<F>> compressed_read(read_transcript.size()),compressed_write(write_transcript.size());
	vector<vector<F>> compressed_input(input_transcript.size()),compressed_output(output_transcript.size());
	vector<F> read_idx(read_transcript.size()*read_transcript[0].size()),write_idx(read_transcript.size()*read_transcript[0].size()),read_counter(read_transcript.size()*read_transcript[0].size()),write_counter(read_transcript.size()*read_transcript[0].size());
	vector<F> read_product,input_product,out_product,write_product;
	vector<F> prev_x;
	lookup_proof P;
	P.previous_r = previous_r;
	F a,b,c;
	a = mimc_hash(previous_r,F(0));
	b = mimc_hash(a,F(1));
	c = mimc_hash(b,F(2));
	F rand = c;
	int counter = 0;
	
	for(int i = 0; i < read_transcript.size(); i++){
		compressed_read[i].resize(read_transcript[0].size());
		compressed_write[i].resize(write_transcript[0].size());
		F mul1 = F(1),mul2 = F(1);
		for(int j = 0; j < read_transcript[0].size(); j++){
			compressed_read[i][j] = read_transcript[i][j][0]*a+read_transcript[i][j][1]*b + c;
			compressed_write[i][j] = write_transcript[i][j][0]*a + write_transcript[i][j][1]*b + c;
			
			read_idx[counter] = read_transcript[i][j][0];
			write_idx[counter] = write_transcript[i][j][0];
			read_counter[counter] = read_transcript[i][j][1];
			write_counter[counter] = write_transcript[i][j][1];
			counter++;

			mul1 = compressed_read[i][j]*mul1;
			mul2 = compressed_write[i][j]*mul2;
		}
		read_product.push_back(mul1);
		write_product.push_back(mul2);
	}
	
	for(int i = 0; i < compressed_output.size(); i++){
		compressed_input[i].resize(input_transcript[0].size());
		compressed_output[i].resize(output_transcript[0].size());
		F mul1 = F(1),mul2 = F(1);
		for(int j = 0; j < input_transcript[0].size(); j++){
			compressed_input[i][j] = input_transcript[i][j][0]*a + input_transcript[i][j][1]*b + c;
			compressed_output[i][j] = output_transcript[i][j][0]*a + output_transcript[i][j][1]*b + c;
			mul1 = compressed_input[i][j]*mul1;
			mul2 = compressed_output[i][j]*mul2;
		}
		input_product.push_back(mul1);
		out_product.push_back(mul2);
	}
	for(int i = 0; i < out_product.size(); i++){
		if(input_product[i]*write_product[i] != out_product[i]*read_product[i]){
			printf("Error\n");
			exit(-1);
		}
	}

	vector<vector<F>> input;

	for(int i = 0; i < compressed_read.size(); i++){
		input.push_back(compressed_read[i]);
	}
	for(int i = 0; i < compressed_write.size(); i++){
		input.push_back(compressed_write[i]);
	}
	
	P.mul_out1 = read_product;
	for(int i = 0; i < out_product.size(); i++){
		P.mul_out1.push_back(write_product[i]); 
	}
	
	rand = chain_hash(rand,P.mul_out1);

	vector<F> r = generate_randomness((int)log2(P.mul_out1.size()),rand);
	
	F sum = evaluate_vector(P.mul_out1,r);
	P.sum1 = sum; 
	rand = mimc_hash(rand,sum);
	P.mP1 = prove_multiplication_tree(input,rand,r);	
	
	P.read_eval_x = P.mP1.individual_randomness;
	P.write_eval_x = P.mP1.individual_randomness;
	for(int i = 0; i < P.mP1.global_randomness.size()-1; i++){
		P.read_eval_x.push_back(P.mP1.global_randomness[i]);
		P.write_eval_x.push_back(P.mP1.global_randomness[i]);
	}
	
	P.read_eval = evaluate_vector(convert2vector(compressed_read),P.read_eval_x);
	P.write_eval = evaluate_vector(convert2vector(compressed_write),P.write_eval_x);
	
	rand = mimc_hash(P.mP1.final_r[P.mP1.final_r.size()-1],P.read_eval);
	rand = mimc_hash(rand,P.write_eval);

	if(P.read_eval + P.mP1.global_randomness[P.mP1.global_randomness.size()-1]*(P.write_eval-P.read_eval) != P.mP1.final_eval){
		printf("lookup error 1\n");
		exit(-1);
	}
	

	input.clear();
	for(int i = 0; i < compressed_input.size(); i++){
		input.push_back(compressed_input[i]);
	}
	for(int i = 0; i < compressed_input.size(); i++){
		input.push_back(compressed_output[i]);
	}
	
	P.mul_out2 = input_product;
	for(int i = 0; i < out_product.size(); i++){
		P.mul_out2.push_back(out_product[i]); 
	}

	rand = chain_hash(rand,P.mul_out2);

	r = generate_randomness((int)log2(P.mul_out2.size()),rand);
	
	sum = evaluate_vector(P.mul_out2,r);
	P.sum2 = sum; 
	rand = mimc_hash(rand,sum);
	

	P.mP2 = prove_multiplication_tree(input,rand,r);
	
	
	clock_t s,e;
	s = clock();
	P.read_eval1 = evaluate_vector(read_idx,P.read_eval_x);
	rand = mimc_hash(P.mP2.final_r[P.mP2.final_r.size()-1],P.read_eval1);
	P.read_eval2 = evaluate_vector(read_counter,P.read_eval_x);
	rand = mimc_hash(rand,P.read_eval2);
	P.write_eval1 = evaluate_vector(write_idx,P.read_eval_x);
	rand = mimc_hash(rand,P.write_eval1);
	P.write_eval2 = evaluate_vector(write_counter,P.read_eval_x);
	rand = mimc_hash(rand,P.write_eval2);
	
	vector<F> segment_eval(indexes.size());

	vector<F> x1;
	for(int i = 0; i < (int)log2(indexes[0].size()); i++){
		x1.push_back(P.read_eval_x[i]);
	}
	
	for(int i = 0; i < indexes.size(); i++){
		segment_eval[i] = evaluate_vector(indexes[i],x1);
	}
	P.x1 = x1;
	P.indexes_eval = segment_eval;
	
	rand = chain_hash(rand,P.indexes_eval);

	vector<F> x2((int)log2(segment_eval.size()));
	for(int i =0; i < x2.size() ; i++){
		x2[x2.size()-1-i] = P.read_eval_x[P.read_eval_x.size()-1-i];
	}
	F idx_eval = evaluate_vector(segment_eval,x2);


	e = clock();
	
	if((P.read_eval != c+P.read_eval1*a+P.read_eval2*b)||(P.write_eval != c+P.write_eval1*a+P.write_eval2*b)){
		printf("Lookup error 1 \n");
		exit(-1);
	}
	if(P.read_eval1 - P.write_eval1 != 0){
		printf("Lookup error 2\n");
		exit(-1);
	}
	if( P.write_eval2-P.read_eval2 != F(1)){
		printf("Lookup error 3\n");
		exit(-1);
	}
	if(idx_eval != P.read_eval1){
		printf("Lookup error 4\n");
		exit(-1);
	}
	P.final_rand = rand;
	return P;
}


void gen_indexes(vector<F> input,int range, vector<vector<int>> &_indexes){

	char buff[range];
	char buff2[256];

	for(int i = 0; i < input.size(); i++){
		input[i].getStr(buff2,256,2);
		//cout << buff2 << endl;
		
		input[i].getStr(buff,range,10);
		
		unsigned long int num = stol(buff);
		for(int j = 0; j < range/seg_bitsize; j++){
			_indexes[j][i] = num%(1<<seg_bitsize);
			num = (num-_indexes[j][i])/(1<<seg_bitsize);
		}
		if(num != 0){
			printf("Error in lookup prepare phase, increase range\n");
			cout << buff2 << endl;
			exit(-1);
		}
	}
}


void prepare_lookup_range_proof(int segments,int elements,  vector<vector<int>> idx,vector<vector<vector<F>>> &input_transcript,
	vector<vector<vector<F>>> &output_transcript,vector<vector<vector<F>>> &read_transcript,vector<vector<vector<F>>> &write_transcript){
	input_transcript.resize(segments);
	output_transcript.resize(segments);
	read_transcript.resize(segments);
	write_transcript.resize(segments);

	for(int i = 0; i < segments; i++){
		input_transcript[i].resize(256);
		output_transcript[i].resize(256);
		for(int j = 0; j < 256; j++){
			input_transcript[i][j].push_back(F(j));
			input_transcript[i][j].push_back(F(0));
			output_transcript[i][j].push_back(F(j));
			output_transcript[i][j].push_back(F(0));
		}
	}
	for(int i = 0; i < segments; i++){
		read_transcript[i].resize(elements);
		write_transcript[i].resize(elements);
		for(int j = 0; j < elements; j++){
			if(F(idx[i][j]) != output_transcript[i][idx[i][j]][0]){
				printf("Error\n");
				exit(-1);
			}
			read_transcript[i][j].push_back(output_transcript[i][idx[i][j]][0]);
			read_transcript[i][j].push_back(output_transcript[i][idx[i][j]][1]);
			write_transcript[i][j].push_back(output_transcript[i][idx[i][j]][0]);
			write_transcript[i][j].push_back(output_transcript[i][idx[i][j]][1] + F(1));
			output_transcript[i][idx[i][j]][1] += F(1);
		}
	}

}



void commit_lookup_streaming( int segments, vector<vector<G1>> &commitments){
	// note that we only need to commit to either the read tape or the write one, as one derives the other
	stream_descriptor lookup_read_fd;
	vector<G1> C;
	lookup_read_fd.name = "read_table";
	lookup_read_fd.size = 2*lookup_stream.size*segments;
	lookup_read_fd.pos = 0;
	lookup_read.clear();
	lookup_write.clear();
	mem_init.clear();
	output.clear();
	lookup_read.resize(segments);
	lookup_write.resize(segments);
	mem_init.resize(segments);
	output.resize(segments);
	for(int i = 0; i < segments; i++){
		lookup_read[i].resize(256);
		lookup_write[i].resize(256);
		mem_init[i].resize(256);
		output[i].resize(256);

		for(int j = 0; j < 256; j++){
			lookup_read[i][j] = F(0);
			lookup_write[i][j] = F(0);
			mem_init[i][j].push_back(F(j));
			mem_init[i][j].push_back(F(0));
			output[i][j].push_back(F(j));
			output[i][j].push_back(F(0));
		}
	}
	if(domain < 128){
		compute_lookup_output();
	}else{
		compute_lookup_output_field();	
	}
	
	
	MIPP_commit_stream(lookup_read_fd,lookup_read_fd.size,pp,C);
	
	commitments.push_back(C);
	vector<F> out_vec;
	for(int i = 0; i < output.size(); i++){
		for(int j = 0; j < output[i].size(); j++){
			out_vec.insert(out_vec.end(),output[i][j].begin(),output[i][j].end());
		}
	}
	
	// commit
	MIPP_commit(out_vec,pp,C);
	commitments.push_back(C);
}


void open_lookup_streaming( int segments,  vector<vector<G1>> commitments){
	// note that we only need to commit to either the read tape or the write one, as one derives the other
	stream_descriptor lookup_read_fd;
	
	lookup_read_fd.name = "read_table";
	lookup_read_fd.size = 2*lookup_stream.size*segments;
	lookup_read_fd.pos = 0;
	lookup_stream.pos = 0;
	lookup_read.clear();
	lookup_write.clear();
	mem_init.clear();
	output.clear();
	lookup_read.resize(segments);
	lookup_write.resize(segments);
	mem_init.resize(segments);
	output.resize(segments);
	for(int i = 0; i < segments; i++){
		lookup_read[i].resize(256);
		lookup_write[i].resize(256);
		mem_init[i].resize(256);
		output[i].resize(256);

		for(int j = 0; j < 256; j++){
			lookup_read[i][j] = F(0);
			lookup_write[i][j] = F(0);
			mem_init[i][j].push_back(F(j));
			mem_init[i][j].push_back(F(0));
			output[i][j].push_back(F(j));
			output[i][j].push_back(F(0));
		}
	}
	if(domain < 128){
		compute_lookup_output();
	}else{
		compute_lookup_output_field();	
	}
	if(domain < 128){
		compute_lookup_output();
	}else{
		compute_lookup_output_field();	
	}

	MIPP_open_stream(lookup_read_fd,lookup_read_fd.size,generate_randomness((int)log2(lookup_read_fd.size),F(321)),pp,commitments[0]);

	vector<F> out_vec;
	for(int i = 0; i < output.size(); i++){
		for(int j = 0; j < output[i].size(); j++){
			out_vec.insert(out_vec.end(),output[i][j].begin(),output[i][j].end());
		}
	}
	
	// commit
	MIPP_open(out_vec,generate_randomness((int)log2(out_vec.size()),F(321)),pp,commitments[1]);
}

lookup_proof lookup_range_proof_streaming( F previous_r, int range){
	lookup_proof P;
	int log_size = (int)log2(lookup_stream.size);
	vector<F> prev_x;
	domain = range;
	quantization_level = 8;
	
	int segments = range/seg_bitsize;
	P.previous_r = previous_r;
	F a,b,c;
	a = mimc_hash(previous_r,F(0));
	b = mimc_hash(a,F(1));
	c = mimc_hash(b,F(2));
	F rand = c;

	lookup_read.clear();
	lookup_write.clear();
	mem_init.clear();
	output.clear();
	lookup_read.resize(segments);
	lookup_write.resize(segments);
	mem_init.resize(segments);
	output.resize(segments);
	for(int i = 0; i < segments; i++){
		lookup_read[i].resize(256);
		lookup_write[i].resize(256);
		mem_init[i].resize(256);
		output[i].resize(256);

		for(int j = 0; j < 256; j++){
			lookup_read[i][j] = F(0);
			lookup_write[i][j] = F(0);
			mem_init[i][j].push_back(F(j));
			mem_init[i][j].push_back(F(0));
			output[i][j].push_back(F(j));
			output[i][j].push_back(F(0));
		}
	}
	if(domain < 128){
		compute_lookup_output();
	}else{
		compute_lookup_output_field();	
	}
	
	vector<vector<F>> compressed_input(mem_init.size()),compressed_output(output.size());
	vector<F> input_product,out_product;
	for(int i = 0; i < compressed_output.size(); i++){
		compressed_input[i].resize(mem_init[0].size());
		compressed_output[i].resize(output[0].size());
		F mul1 = F(1),mul2 = F(1);
		for(int j = 0; j < mem_init[0].size(); j++){
			compressed_input[i][j] = mem_init[i][j][0]*a + mem_init[i][j][1]*b + c;
			compressed_output[i][j] = output[i][j][0]*a + output[i][j][1]*b + c;
			mul1 = compressed_input[i][j]*mul1;
			mul2 = compressed_output[i][j]*mul2;
		}
		input_product.push_back(mul1);
		out_product.push_back(mul2);
	}

	stream_descriptor compressed_readwrite;compressed_readwrite.pos = 0;
	compressed_readwrite.name = "compressed_lookup_read_write";
	compressed_readwrite.size = lookup_stream.size*segments;
	compressed_readwrite.compress_vector.push_back(F(0));
	compressed_readwrite.compress_vector.push_back(b);
	compressed_readwrite.compress_vector.push_back(c);

	vector<F> _a  = compressed_readwrite.compress_vector;
	stream_descriptor lookup_read_fd,lookup_write_fd;lookup_read_fd.pos = 0;lookup_write_fd.pos = 0;
	lookup_read_fd.name = "read_table";lookup_write_fd.name = "write_table";
	lookup_read_fd.size = 2*lookup_stream.size*segments;lookup_write_fd.size = 2*lookup_stream.size*segments;
	

	
	mul_tree_proof_stream mP1 = prove_multiplication_tree_stream(compressed_readwrite,segments*2,lookup_stream.size, c,prev_x);
	printf("OK\n");
	compressed_readwrite.pos = 0;

	//F eval1 = evaluate_vector_stream(compressed_readwrite,mP1.r,2*compressed_readwrite.size);
	
	stream_descriptor read_fd,write_fd;read_fd.pos = 0;write_fd.pos = 0;
	read_fd.name = "compressed_lookup_read";write_fd.name = "compressed_lookup_write";
	read_fd.size = lookup_stream.size*segments;write_fd.size = lookup_stream.size*segments;
	read_fd.compress_vector = compressed_readwrite.compress_vector;
	write_fd.compress_vector = compressed_readwrite.compress_vector;
	
	
	

	
	P.read_eval_x = mP1.individual_randomness;
	P.write_eval_x = mP1.individual_randomness;
	for(int i = 0; i < mP1.global_randomness.size()-1; i++){
		P.read_eval_x.push_back(mP1.global_randomness[i]);
		P.write_eval_x.push_back(mP1.global_randomness[i]);
	}
	
	
	P.read_eval = evaluate_vector_stream(read_fd,P.read_eval_x,read_fd.size);
	
	
	P.write_eval = evaluate_vector_stream(write_fd,P.write_eval_x,write_fd.size);
	
	rand = mimc_hash(rand,P.read_eval);
	rand = mimc_hash(rand,P.write_eval);

	//if(P.read_eval + mP1.r[0]*(P.write_eval-P.read_eval) != mP1.final_eval){
	if(P.read_eval + mP1.global_randomness[mP1.global_randomness.size()-1]*(P.write_eval-P.read_eval) != mP1.final_eval){
		printf("lookup error 1\n");
		//exit(-1);
	}
	
	
	
	vector<vector<F>> table_input;
	
	for(int i = 0; i < compressed_input.size(); i++){
		table_input.push_back(compressed_input[i]);
	}
	for(int i = 0; i < compressed_input.size(); i++){
		table_input.push_back(compressed_output[i]);
	}
	
	P.mul_out2 = input_product;
	for(int i = 0; i < out_product.size(); i++){
		P.mul_out2.push_back(out_product[i]); 
	}

	rand = chain_hash(rand,P.mul_out2);

	vector<F> r = generate_randomness((int)log2(P.mul_out2.size()),rand);
	
	F sum = evaluate_vector(P.mul_out2,r);
	P.sum2 = sum; 
	rand = mimc_hash(rand,sum);
	

	P.mP2 = prove_multiplication_tree(table_input,rand,r);
	
	

	vector<F> eval_read,eval_write;
	vector<vector<F>> eval_read_x(2),eval_write_x(2);
	eval_read_x[0].push_back(F(0));eval_read_x[0].insert(eval_read_x[0].end(), P.read_eval_x.begin(), P.read_eval_x.end());
	eval_read_x[1].push_back(F(1));eval_read_x[1].insert(eval_read_x[1].end(), P.read_eval_x.begin(), P.read_eval_x.end());
	
	eval_write_x[0].push_back(F(0));eval_write_x[0].insert(eval_write_x[0].end(), P.read_eval_x.begin(), P.read_eval_x.end());
	eval_write_x[1].push_back(F(1));eval_write_x[1].insert(eval_write_x[1].end(), P.read_eval_x.begin(), P.read_eval_x.end());
	
	
	eval_write = evaluate_vector_stream_batch(lookup_write_fd,eval_read_x,lookup_write_fd.size);



	eval_read  = evaluate_vector_stream_batch(lookup_read_fd,eval_read_x,lookup_read_fd.size);
	
	
	if((P.read_eval != _a[2]+eval_read[0]*_a[0]+eval_read[1]*_a[1]) || (P.write_eval != c+eval_write[0]*a+eval_write[1]*b)){
		//printf("Lookup error 1 \n");
		//exit(-1);
	}
	if(eval_read[0] - eval_write[0] != 0){
		printf("Lookup error 2\n");
		//exit(-1);
	}
	if( -eval_read[1]+eval_write[1] != F(1)){
		printf("Lookup error 3\n");
		//exit(-1);
	}
	
	stream_descriptor indexes;indexes.name = "indexes";indexes.size = segments*lookup_stream.size;
	indexes.pos = 0;
	// compute indexes
	vector<F> input_x,idx_eval;
	for(int i = 0; i < (int)log2(lookup_stream.size); i++){
		input_x.push_back(P.read_eval_x[i]); 
	}
	P.input_x = input_x;
	for(int i = 0; i < segments; i++){
		if(MAX_CHUNCK >= lookup_stream.size){
			vector<F> buff(lookup_stream.size);
			read_stream(indexes,buff,buff.size());
			idx_eval.push_back(evaluate_vector(buff,input_x));
			buff.clear();
		}else{
			idx_eval.push_back(evaluate_vector_stream(indexes,input_x,lookup_stream.size));
			indexes.pos += lookup_stream.size;
		}
	}
	P.final_eval = 0;
	F pow = F_ONE;
	for(int i = 0; i < segments; i++){
		P.final_eval += pow*idx_eval[i];
		pow *= F(256);
	}
	
	return P;
	
}



void commit_lookup( int segments, vector<vector<vector<F>>> read_table, vector<vector<G1>> &commitments){
	// note that we only need to commit to either the read tape or the write one, as one derives the other
	vector<G1> C;
	vector<F> poly;
	for(int i = 0 ; i <  read_table.size(); i++){
		for(int j = 0; j < read_table[i].size(); j++){
			poly.insert(poly.end(),read_table[i][j].begin(),read_table[i][j].end());
		}
	}
		output.clear();
	output.resize(segments);
	for(int i = 0; i < segments; i++){
		output[i].resize(256);
		for(int j = 0; j < 256; j++){
			output[i][j].push_back(F(j));
			output[i][j].push_back(F(0));
		}
	}

	
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	vector<F> out_vec;
	for(int i = 0; i < output.size(); i++){
		for(int j = 0; j < output[i].size(); j++){
			out_vec.insert(out_vec.end(),output[i][j].begin(),output[i][j].end());
		}
	}
	
	// commit
	MIPP_commit(out_vec,pp,C);
	commitments.push_back(C);
}


void open_lookup( int segments, vector<vector<vector<F>>> read_table, vector<vector<G1>> commitments){
	// note that we only need to commit to either the read tape or the write one, as one derives the other
		vector<F> poly;
	for(int i = 0 ; i <  read_table.size(); i++){
		for(int j = 0; j < read_table[i].size(); j++){
			poly.insert(poly.end(),read_table[i][j].begin(),read_table[i][j].end());
		}
	}
	output.clear();
	output.resize(segments);
	for(int i = 0; i < segments; i++){
		output[i].resize(256);
		for(int j = 0; j < 256; j++){
			output[i][j].push_back(F(j));
			output[i][j].push_back(F(0));
		}
	}

	
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[0]);
	vector<F> out_vec;
	for(int i = 0; i < output.size(); i++){
		for(int j = 0; j < output[i].size(); j++){
			out_vec.insert(out_vec.end(),output[i][j].begin(),output[i][j].end());
		}
	}
	// commit
	MIPP_open(out_vec,generate_randomness((int)log2(out_vec.size()),F(321)),pp,commitments[1]);
}

void test_lookup_commitment_streaming(int range){
	int log_size = (int)log2(lookup_stream.size);
	vector<F> prev_x;
	domain = range;
	quantization_level = 8;
	
	int segments = range/seg_bitsize;
	vector<vector<G1>> commitments;
	printf("lookup commit\n");
	commit_lookup_streaming(segments,commitments);
	printf("lookup open\n");
	open_lookup_streaming(seg_bitsize,commitments);
	printf("Exit\n");
}


lookup_proof lookup_range_proof(vector<F> input, F previous_r, int range){
	int log_size = (int)log2(input.size());
	if(1ULL<<log_size != input.size()){
		log_size++;
		input.resize(1<<log_size,F(0));
	}

	int segments = range/seg_bitsize;
	vector<vector<int>> _indexes(segments);
	vector<vector<F>> indexes(segments);
	vector<vector<vector<F>>> input_transcript,output_transcript,read_transcript,write_transcript;
	
	for(int i = 0; i < _indexes.size(); i++){
		_indexes[i].resize(input.size());
		indexes[i].resize(input.size());
	}
	
	gen_indexes(input,range,_indexes);
	for(int i = 0 ; i < _indexes.size(); i++){
		for(int j = 0; j < _indexes[i].size(); j++){
			indexes[i][j] = F(_indexes[i][j]);
		}
	}

	for(int i = 0; i < input.size(); i++){
		F sum = F(0);
		for(int j = 0; j < segments; j++){
			sum += F(1ULL<<(j*8))*indexes[j][i];
		}
		if(sum != input[i]){
			printf("Error %d\n",i );
			char buff[128];
			input[i].getStr(buff,128,10);
			printf("%s\n", buff);
			exit(-1);
		}
	}
	prepare_lookup_range_proof(segments,input.size(),_indexes,input_transcript,output_transcript,read_transcript,write_transcript);

	if(_commitment_test){
		vector<vector<G1>> commitment;
		commit_lookup(segments,read_transcript,commitment);
		open_lookup(segments,read_transcript,commitment);
		lookup_proof P;
		return P;
	}

	lookup_proof P = mem_consistency(output_transcript,input_transcript,read_transcript,write_transcript,indexes,previous_r);
	
	F sum = F(0);
	for(int i = 0; i < segments; i++){
		sum += P.indexes_eval[i]*F(1ULL<<(i*8)); 
	}

	if(evaluate_vector(input,P.x1) != sum){
		printf("Error final lookup\n");
		exit(-1);
	}
	P.final_eval = sum;
	return P;
}