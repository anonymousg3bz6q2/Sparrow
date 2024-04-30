#include "witness_stream.h"
#include "Inference.h"
#include "utils.hpp"
#include "quantization.h"
extern Dataset D_train;
extern vector<vector<Node>> _tree;
extern vector<vector<vector<Node>>> _forest;
extern vector<vector<F>> tree;
extern vector<vector<vector<F>>> forest;
extern vector<vector<vector<vector<int>>>> histograms;
extern vector<vector<vector<int>>> node_histogram;
extern vector<vector<vector<vector<int>>>> histograms_forest;
vector<vector<int>> witness_hist,out_hist;
extern vector<vector<F>> lookup_read,lookup_write;
extern vector<vector<vector<F>>> output;
extern vector<F> table;
// Input for SNARK that proves split 
extern vector<unsigned long long int> gini_input;
int gini_input_pos = -1;

extern int total_nodes;
extern int attr;
extern int domain;
extern int quantization_level;
extern int max_depth;
extern int bin_size;
extern vector<long long int> lookup_input;
extern vector<vector<unsigned long long int>> best_gini;
extern stream_descriptor lookup_stream;

extern F one,zero;

// initialize to seed
F prev_rand,A_,B_;
F seed;
vector<int> discrete_table;
double inference_time = 0.0;
double stream_access_time = 0.0;



void get_lookup_stream_field(vector<F> &v, int size){
    if(lookup_stream.name == "randomness_quotient"){
        if(lookup_stream.pos == 0){
            prev_rand = seed;
        }
        if(lookup_stream.pos%lookup_stream.size == 0){
            prev_rand = seed;
        }


        F prev;
        F divisor = F(1ULL<<16);
        for(int i = 0; i < size; i++){
            prev = A_*prev_rand + B_;
            v[i] =_shift_right(prev);
            //v[i] = _divide(prev,divisor);
            prev_rand = prev;
        }
        
    }else{
        printf("No lookup stream\n");
        exit(-1);
    }
    lookup_stream.pos += size;

}
int get_lookup_stream(vector<int> &v, int size){
    int split_size = (forest[0].size()-1)*D_train.data.size()*4*bin_size;
    
    if(lookup_stream.name == "remainders"){
        unsigned long long int _N1,_N2,mul1,mul2;
        unsigned long long int divisor,divident,quotient;

        int pos = (2*lookup_stream.pos )%split_size;
        if(pos == 0) {
            compute_ginis(2*lookup_stream.pos/split_size);
        }
       
        for(int i = 0; i < size/2; i++){
            if(pos + 4*i == split_size) [[unlikely]]{
                pos -= split_size;
                compute_ginis((2*lookup_stream.pos+4*i)/split_size);
            }
            
            _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
            _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
            //_N1 = gini_input[2*lookup_stream.pos + 4*i] + gini_input[2*lookup_stream.pos + 4*i+1];
            //_N2 = gini_input[2*lookup_stream.pos + 4*i+2] + gini_input[2*lookup_stream.pos + 4*i+3];
            if(_N1 == 0 && _N2 == 0){
                v[2*i] = v[2*i+1]= 0;
                continue;
            }

            if(_N1 != 0 && _N2 != 0){
                mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                //mul1 = gini_input[2*lookup_stream.pos + 4*i]*gini_input[2*lookup_stream.pos + 4*i+1];
                //mul2 = gini_input[2*lookup_stream.pos + 4*i+2] * gini_input[2*lookup_stream.pos + 4*i+3];
                divisor = _N1*(_N1+_N2);
                divident = _N1*_N1- 2*mul1;
                quotient = ((1ULL<<Q)*divident)/divisor;
                v[2*i] = ((1ULL<<Q))*(divident) - (quotient*divisor);
                divisor = _N2*(_N1+_N2);
                divident = _N2*_N2- 2*mul2;
                quotient = ((1ULL<<Q)*divident)/divisor;
                v[2*i+1] = ((1ULL<<Q))*(divident) - (quotient*divisor);
            }else if(_N1 == 0){
                v[2*i] = 0;
                mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                //mul2 = gini_input[2*lookup_stream.pos + 4*i+2] * gini_input[2*lookup_stream.pos + 4*i+3];
                divisor = _N2*(_N1+_N2);
                divident = _N2*_N2- 2*mul2;
                quotient = ((1ULL<<Q)*divident)/divisor;
                
                v[2*i+1] = ((1ULL<<Q))*(divident) - (quotient*divisor); 
            }else{
                mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                //mul1 = gini_input[2*lookup_stream.pos + 4*i]*gini_input[2*lookup_stream.pos + 4*i+1];
                divisor = _N1*(_N1+_N2);
                divident = _N1*_N1- 2*mul1;
                quotient = ((1ULL<<Q)*divident)/divisor;
                v[2*i] = ((1ULL<<Q))*(divident) - (quotient*divisor);
                v[2*i+1] = 0; 
            }
        }
    }
    else if(lookup_stream.name == "sub_ginis"){
        unsigned long long int _N1,_N2,mul1,mul2,divisor,divident;
        unsigned long long int q1,q2;
        int _pos,row,col;
        //printf("%d,%d,%d\n",lookup_stream.pos,size,lookup_stream.size);
        if(lookup_stream.pos >= lookup_stream.size){
            printf("ERROR\n");
            exit(-1);
        }
        int pos = (4*lookup_stream.pos )%split_size;
        if(pos == 0) {
            compute_ginis(4*lookup_stream.pos/split_size);
        }
        for(int i = 0; i < size; i++){
            if(pos + 4*i == split_size) [[unlikely]]{
                pos -= split_size;
                compute_ginis((4*lookup_stream.pos+4*i)/split_size);
            }

            //_N1 = gini_input[4*lookup_stream.pos + 4*i] + gini_input[4*lookup_stream.pos + 4*i+1];
            //_N2 = gini_input[4*lookup_stream.pos + 4*i+2] + gini_input[4*lookup_stream.pos + 4*i+3];
            _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
            _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
            
            _pos = i+ lookup_stream.pos; 
            _pos = (_pos - (_pos%bin_size))/bin_size;
            row = (_pos - (_pos%attr))/attr;
            col = _pos%attr;
            if(_N1 == 0 && _N2 == 0){
                v[i] = 0;

                continue;
            }

            if(_N1 != 0 && _N2 != 0){
                //mul1 = gini_input[4*lookup_stream.pos + 4*i]*gini_input[4*lookup_stream.pos + 4*i+1];
                //mul2 = gini_input[4*lookup_stream.pos + 4*i+2] * gini_input[4*lookup_stream.pos + 4*i+3];
                mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                divisor = _N1*(_N1+_N2);
                divident = _N1*_N1- 2*mul1;
                q1 = ((1ULL<<Q)*divident)/divisor;
                divisor = _N2*(_N1+_N2);
                divident = _N2*_N2- 2*mul2;
                q2 = ((1ULL<<Q)*divident)/divisor;

                v[i] = (1ULL<<Q) - q1-q2 - best_gini[row][col];
            }
            else if(_N1 == 0 ){
                mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                //mul2 = gini_input[4*lookup_stream.pos + 4*i+2] * gini_input[4*lookup_stream.pos + 4*i+3];
                divisor = _N2*(_N1+_N2);
                divident = _N2*_N2- 2*mul2;
               v[i] = (1ULL<<Q) - (((1ULL<<Q)*divident)/divisor) - best_gini[row][col];
                //printf(">> v: %d,%d,%d,%d,%d,%d\n",v[i],4*lookup_stream.pos,gini_input[4*lookup_stream.pos + 4*i+2],gini_input[4*lookup_stream.pos + 4*i+3],row,col);
            }else{
                //mul1 = gini_input[4*lookup_stream.pos + 4*i]*gini_input[4*lookup_stream.pos + 4*i+1];
                mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                divisor = _N1*(_N1+_N2);
                divident = _N1*_N1- 2*mul1;
                v[i] = (1ULL<<Q) - (((1ULL<<Q)*divident)/divisor) - best_gini[row][col];
                
            }         
        }
    }
    else{
        printf("Lookup stream not implemented yet\n");
        exit(-1);
    }
    lookup_stream.pos += size;
    
    return lookup_stream.pos;
}

void compute_lookup_output_field(){
    int segments = domain/quantization_level;
    vector<F> buff(1024);
    char bytes[32];
    for(int i = 0; i < segments; i++){
        for(int j = 0; j < lookup_stream.size/1024; j++){
            get_lookup_stream_field(buff,1024);
            for(int k = 0; k < 1024; k++){
                //int idx = (lookup_input[j]/(1ULL<<(quantization_level*(i))))%(1ULL<<quantization_level);
                int  idx = get_byte(i,buff[k]);
               output[i][idx][1] += 1;
            }
        }
        lookup_stream.pos = 0;
    }
 
}

void compute_lookup_output(){
    int segments = domain/quantization_level;
    vector<int> buff(1024);
    for(int i = 0; i < segments; i++){
        for(int j = 0; j < lookup_stream.size/1024; j++){
            get_lookup_stream(buff,1024);
            for(int k = 0; k < 1024; k++){
                //int idx = (lookup_input[j]/(1ULL<<(quantization_level*(i))))%(1ULL<<quantization_level);
                int idx = (buff[k]/(1ULL<<(quantization_level*(i))))%(1ULL<<quantization_level);
                output[i][idx][1] += 1;
            }
        }
        lookup_stream.pos = 0;
    }
 
}

int get_witness_split(stream_descriptor &fd, vector<F> &v, int size){
    int split_size = (forest[0].size()-1)*D_train.data.size()*4*bin_size;
   
    if(attr == 0 || total_nodes == 0 || bin_size == 0){
        printf("Did not initialized attr/total_nodes/bins ,%d,%d,%d\n",attr ,total_nodes ,bin_size);
        exit(-1);
    }
    if(best_gini.size() == 0){
        printf("Error in arr size stream\n");
    }
   
    if(fd.name == "N"){
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size/2; i++){
                v[2*i] = zero;
                v[2*i+1] = zero;
            }
        }else{
            int pos = (2*fd.pos)%split_size;
            if(pos == 0 || gini_input_pos != 2*fd.pos/split_size) {
                compute_ginis(2*fd.pos/split_size);
            }
            for(int i = 0; i < size/2; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((2*fd.pos+4*i)/split_size);
                }
                //v[2*i] = F(gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1]);
                //v[2*i+1] = F(gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3]);
                v[2*i] = F(gini_input[pos + 4*i] + gini_input[pos + 4*i+1]);
                v[2*i+1] = F(gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3]);
            }
        }        
        
    }else if(fd.name  == "gini_input"){
        if(fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (fd.pos)%split_size;
            if(pos == 0 || gini_input_pos != fd.pos/split_size) {
                compute_ginis(fd.pos/split_size);
            }
            for(int i = 0; i <size; i++){
                if(pos + i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((fd.pos+i)/split_size);
                }
                v[i] = F(gini_input[pos + i]);
                //v[i] = F(gini_input[fd.pos + i]);
            }
        }
        
    }
    else if(fd.name == "gini_input_1" || fd.name == "gini_input_2"){
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (2*fd.pos)%split_size;
            if(pos == 0 || gini_input_pos != 2*fd.pos/split_size) {
                compute_ginis(2*fd.pos/split_size);
            }
            int cond = (fd.name == "gini_input_1");
            for(int i = 0; i < size; i++){
                if(pos + 2*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((2*fd.pos+2*i)/split_size);
                }
                if(cond){
                    //v[i] = F(gini_input[2*fd.pos + 2*i]);
                    v[i] = F(gini_input[pos + 2*i]);
                }else{
                    //v[i] = F(gini_input[2*fd.pos + 2*i+1]); 
                    v[i] = F(gini_input[pos + 2*i+1]); 
                }
            }
        }
        
    }
    else if(fd.name == "N_sum"){
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (2*fd.pos)%split_size;
            if(pos == 0 || gini_input_pos != 2*fd.pos/split_size) {
                compute_ginis(2*fd.pos/split_size);
            }

            for(int i = 0; i < size/2; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((2*fd.pos+4*i)/split_size);
                }
                //v[2*i] = F(gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1] + gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3]);
                //v[2*i+1] = v[2*i];
                v[2*i] = F(gini_input[pos+ 4*i] + gini_input[pos + 4*i+1] + gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3]);
                v[2*i+1] = v[2*i];

            }
        }
        
    }
    else if(fd.name == "pairwise_prod"){
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (2*fd.pos)%split_size;
            if(pos == 0 || gini_input_pos != 2*fd.pos/split_size) {
                compute_ginis(2*fd.pos/split_size);
            }

            for(int i = 0; i < size; i++){
                if(pos + 2*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((2*fd.pos+2*i)/split_size);
                }

                v[i] = F(gini_input[pos + 2*i]*gini_input[pos + 2*i+1]);
                //v[i] = F(gini_input[2*fd.pos + 2*i]*gini_input[2*fd.pos + 2*i+1]);
            }
        }
        
    }
    else if(fd.name == "square_N"){
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (2*fd.pos)%split_size;
            if(pos == 0 || gini_input_pos != 2*fd.pos/split_size) {
                compute_ginis(2*fd.pos/split_size);
            }

            for(int i = 0; i < size/2; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((2*fd.pos+4*i)/split_size);
                }
                v[2*i] = F((gini_input[pos + 4*i] + gini_input[pos + 4*i+1])*(gini_input[pos + 4*i] + gini_input[pos + 4*i+1]));
                v[2*i+1] = F((gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3])*(gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3]));
                //v[2*i] = F((gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1])*(gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1]));
                //v[2*i+1] = F((gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3])*(gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3]));
            }
        }
        
    }
    else if(fd.name == "divisors"){
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (2*fd.pos)%split_size;
            if(pos == 0 || gini_input_pos != 2*fd.pos/split_size) {
                compute_ginis(2*fd.pos/split_size);
            }
            unsigned long long int _N1,_N2;
            for(int i = 0; i < size/2; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((2*fd.pos+4*i)/split_size);
                }
                _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
                _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
                v[2*i] = F(_N1*(_N1+_N2));
                v[2*i+1] = F(_N2*(_N1+_N2));
            

                //_N1 = gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1];
                //_N2 = gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3];
                //v[2*i] = F(_N1*(_N1+_N2));
                //v[2*i+1] = F(_N2*(_N1+_N2));
            }
        }
    }
    else if(fd.name == "dividents"){
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (2*fd.pos)%split_size;
            if(pos == 0 || gini_input_pos != 2*fd.pos/split_size) {
                compute_ginis(2*fd.pos/split_size);
            }

            unsigned  long long int _N1,_N2,mul1,mul2;
            for(int i = 0; i < size/2; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                     
                    pos -= split_size;
                    compute_ginis((2*fd.pos+4*i)/split_size);
                }
                _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
                _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
                mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                //_N1 = gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1];
                //_N2 = gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3];
                //mul1 = gini_input[2*fd.pos + 4*i]*gini_input[2*fd.pos + 4*i+1];
                //mul2 = gini_input[2*fd.pos + 4*i+2] * gini_input[2*fd.pos + 4*i+3];
                v[2*i] = F(_N1*_N1- 2*mul1);
                v[2*i+1] = F(_N2*_N2 - 2*mul2);
            }
        }
    }
    else if(fd.name == "quotients"){
        unsigned long long int _N1,_N2,mul1,mul2;
        unsigned long long int divisor,divident;
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (2*fd.pos)%split_size;
            if(pos == 0 || gini_input_pos != 2*fd.pos/split_size) {
                compute_ginis(2*fd.pos/split_size);
            }


            for(int i = 0; i < size/2; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((2*fd.pos+4*i)/split_size);
                }
                
                //_N1 = gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1];
                //_N2 = gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3];
                _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
                _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
                if(_N1 == 0 && _N2 == 0){
                    v[2*i] = v[2*i+1]= zero;
                    continue;
                
                }
                
                if(_N1 != 0 && _N2 != 0){
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    //mul1 = gini_input[2*fd.pos + 4*i]*gini_input[2*fd.pos + 4*i+1];
                    //mul2 = gini_input[2*fd.pos + 4*i+2] * gini_input[2*fd.pos + 4*i+3];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    v[2*i] = F(((1ULL<<Q)*divident)/divisor);
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    v[2*i+1] = F(((1ULL<<Q)*divident)/divisor);
                }
                else if(_N1 == 0 ){
                    //mul2 = gini_input[2*fd.pos + 4*i+2] * gini_input[2*fd.pos + 4*i+3];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    v[2*i+1] = F(((1ULL<<Q)*divident)/divisor);
                    v[2*i] = zero;
                }else{
                    //mul1 = gini_input[2*fd.pos + 4*i]*gini_input[2*fd.pos + 4*i+1];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    v[2*i] = F(((1ULL<<Q)*divident)/divisor);
                    v[2*i+1] = zero;
                    
                }
            }
        }
    }
    else if(fd.name == "remainders"){
        unsigned long long int _N1,_N2,mul1,mul2;
        unsigned long long int divisor,divident,quotient;
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
                
            int pos = (2*fd.pos)%split_size;
            if(pos == 0 || gini_input_pos != 2*fd.pos/split_size) {
                compute_ginis(2*fd.pos/split_size);
            }
            
            for(int i = 0; i < size/2; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((2*fd.pos+4*i)/split_size);
                }

                _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
                _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
                
                //_N1 = gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1];
                //_N2 = gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3];
                if(_N1 == 0 && _N2 == 0){
                    v[2*i] = v[2*i+1]= zero;
                    continue;
                }

                if(_N1 != 0 && _N2 != 0){
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    //mul1 = gini_input[2*fd.pos + 4*i]*gini_input[2*fd.pos + 4*i+1];
                    //mul2 = gini_input[2*fd.pos + 4*i+2] * gini_input[2*fd.pos + 4*i+3];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    quotient = ((1ULL<<Q)*divident)/divisor;
                    v[2*i] = F((1ULL<<Q))*F(divident) - F(quotient*divisor);
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    quotient = ((1ULL<<Q)*divident)/divisor;
                    v[2*i+1] = F((1ULL<<Q))*F(divident) - F(quotient*divisor);
                }else if(_N1 == 0){
                    v[2*i] = zero;
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    //mul2 = gini_input[2*fd.pos + 4*i+2] * gini_input[2*fd.pos + 4*i+3];
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    quotient = ((1ULL<<Q)*divident)/divisor;
                    
                    v[2*i+1] = F((1ULL<<Q))*F(divident) - F(quotient*divisor); 
                }else{
                    //mul1 = gini_input[2*fd.pos + 4*i]*gini_input[2*fd.pos + 4*i+1];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    quotient = ((1ULL<<Q)*divident)/divisor;
                    v[2*i] = F((1ULL<<Q))*F(divident) - F(quotient*divisor);
                    v[2*i+1] = zero; 
               }
            }
        }
    }else if(fd.name == "remainders_bits"){
        unsigned long long int _N1,_N2,mul1,mul2;
        unsigned long long int divisor,divident,quotient;
        vector<F> arr(size);
       
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < 64*size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (2*fd.pos)%split_size;
            if(pos == 0 || gini_input_pos != 2*fd.pos/split_size) {
                compute_ginis(2*fd.pos/split_size);
            }

            for(int i = 0; i < size/2; i++){
               // printf("%d,%d\n",2*i,size);
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((2*fd.pos+4*i)/split_size);
                }
                _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
                _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
                
                //_N1 = gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1];
                //_N2 = gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3];
                if(_N1 == 0 && _N2 == 0){
                    arr[2*i] = arr[2*i+1]= zero;
                    continue;
                }

                if(_N1 != 0 && _N2 != 0){
                    //mul1 = gini_input[2*fd.pos + 4*i]*gini_input[2*fd.pos + 4*i+1];
                    //mul2 = gini_input[2*fd.pos + 4*i+2] * gini_input[2*fd.pos + 4*i+3];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    
                    quotient = ((1ULL<<Q)*divident)/divisor;
                    if((1ULL<<Q)*divident < quotient*divisor){
                        printf("Error\n");
                        exit(-1);
                    }
                    arr[2*i] = F((1ULL<<Q))*F(divident) - F(quotient*divisor);
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    quotient = ((1ULL<<Q)*divident)/divisor;
                    arr[2*i+1] = F((1ULL<<Q))*F(divident) - F(quotient*divisor);
                    
                }else if(_N1 == 0){
                    arr[2*i] = zero;
                    //mul2 = gini_input[2*fd.pos + 4*i+2] * gini_input[2*fd.pos + 4*i+3];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    quotient = ((1ULL<<Q)*divident)/divisor;

                    arr[2*i+1] = F((1ULL<<Q))*F(divident) - F(quotient*divisor); 
                    if((1ULL<<Q)*divident < quotient*divisor){
                        printf("Error\n");
                        exit(-1);
                    }
                    //printf("%lld,%lld,%lld\n",divident,(1ULL<<Q)*divident,(1ULL<<Q)*divident - quotient*divisor);
                
                }else{
                    //mul1 = gini_input[2*fd.pos + 4*i]*gini_input[2*fd.pos + 4*i+1];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    quotient = ((1ULL<<Q)*divident)/divisor;
                    arr[2*i] = F((1ULL<<Q))*F(divident) - F(quotient*divisor);
                    if((1ULL<<Q)*divident < quotient*divisor){
                        printf("Error\n");
                        exit(-1);
                    }
                    arr[2*i+1] = zero; 
                }
            }
            v = prepare_bit_vector(arr,64);

        }
    }
    else if(fd.name == "inverses"){
        unsigned long long int _N1,_N2;
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (2*fd.pos)%split_size;
            if(pos == 0) {
                compute_ginis(2*fd.pos/split_size);
            }

            for(int i = 0; i < size/2; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((2*fd.pos+4*i)/split_size);
                }
                //_N1 = gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1];
                //_N2 = gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3];
                _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
                _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
                if(_N1 == 0 && _N2 == 0){
                    v[2*i] = v[2*i+1]= zero;
                    continue;
                }

                if(_N1 != 0 && _N2 != 0){
                    v[2*i].inv(v[2*i],F(_N1));
                    v[2*i+1].inv(v[2*i+1],F(_N2));                
                }else if(_N1 == 0){
                    v[2*i] = zero;
                    v[2*i+1].inv(v[2*i+1],F(_N2));                
                }else{
                    v[2*i].inv(v[2*i],F(_N1));
                    v[2*i+1] = zero;
                }            
            }
        }
    }
    else if(fd.name == "cond" || fd.name == "cond_inv"){
        unsigned long long int _N1,_N2;
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int cond = fd.name == "cond";
            int pos = (2*fd.pos)%split_size;
            if(pos == 0) {
                compute_ginis(2*fd.pos/split_size);
            }

            for(int i = 0; i < size/2; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((2*fd.pos+4*i)/split_size);
                }
                
                _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
                _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
                //_N1 = gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1];
                //_N2 = gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3];
                if(_N1 == 0 && _N2 == 0){
                    if(cond){
                        v[2*i] = v[2*i+1]= zero;                
                    }else{
                        v[2*i] = v[2*i+1]= one;
                    }
                    continue;
                }

                if(_N1 != 0 && _N2 != 0){
                    if(cond){
                        v[2*i] = one; //.inv(v[2*i],F(_N1));
                        v[2*i+1] = one;//.inv(v[2*i+1],F(_N2));                
                    }else{
                        v[2*i] = zero; //.inv(v[2*i],F(_N1));
                        v[2*i+1] = zero;//.inv(v[2*i+1],F(_N2));                

                    }
                    
                }else if(_N1 == 0){
                    if(cond){
                        v[2*i] = zero;
                        v[2*i+1] = one;//.inv(v[2*i+1],F(_N2));                
                    }else{
                        v[2*i] = one;
                        v[2*i+1] = zero;//.inv(v[2*i+1],F(_N2));                
                    }
                }else{
                    if(cond){
                            v[2*i] = one;
                            v[2*i+1] = zero;//.inv(v[2*i+1],F(_N2));                
                        }else{
                            v[2*i] = zero;
                            v[2*i+1] = one;//.inv(v[2*i+1],F(_N2));                
                        }
                    }            
            }
        }    
    }
    else if(fd.name == "divisors_quot"){
        unsigned long long int _N1,_N2,mul1,mul2;
        unsigned long long int divisor,divident,quotient;
        if(2*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (2*fd.pos)%split_size;
            if(pos == 0) {
                compute_ginis(2*fd.pos/split_size);
            }

            for(int i = 0; i < size/2; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    
                    compute_ginis((2*fd.pos+4*i)/split_size);
                }
                _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
                _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
                
                //_N1 = gini_input[2*fd.pos + 4*i] + gini_input[2*fd.pos + 4*i+1];
                //_N2 = gini_input[2*fd.pos + 4*i+2] + gini_input[2*fd.pos + 4*i+3];
                if(_N1 == 0 && _N2 == 0){
                    v[2*i] = v[2*i+1]= zero;
                    continue;
                
                }
                
                if(_N1 != 0 && _N2 != 0){
                    //mul1 = gini_input[2*fd.pos + 4*i]*gini_input[2*fd.pos + 4*i+1];
                    //mul2 = gini_input[2*fd.pos + 4*i+2] * gini_input[2*fd.pos + 4*i+3];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    v[2*i] = F(((1ULL<<Q)*divident)/divisor)*F(divisor);
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    v[2*i+1] = F(((1ULL<<Q)*divident)/divisor)*F(divisor);
                }
                else if(_N1 == 0 ){
                    //mul2 = gini_input[2*fd.pos + 4*i+2] * gini_input[2*fd.pos + 4*i+3];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    
                    v[2*i+1] = F((((1ULL<<Q)*divident)/divisor)*divisor);
                    v[2*i] = zero;
                }else{
                    //mul1 = gini_input[2*fd.pos + 4*i]*gini_input[2*fd.pos + 4*i+1];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    v[2*i] = F((((1ULL<<Q)*divident)/divisor)*divisor);
                    v[2*i+1] = zero;
                    
                }
            }
        }
    }
    else if(fd.name == "ginis"){
        unsigned long long int _N1,_N2,mul1,mul2,divisor,divident;
        unsigned long long int q1,q2;
        
        if(4*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int pos = (4*fd.pos)%split_size;
            if(pos == 0) {
                compute_ginis(4*fd.pos/split_size);
            }

            for(int i = 0; i < size; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((4*fd.pos+4*i)/split_size);
                }
                
                //_N1 = gini_input[4*fd.pos + 4*i] + gini_input[4*fd.pos + 4*i+1];
                //_N2 = gini_input[4*fd.pos + 4*i+2] + gini_input[4*fd.pos + 4*i+3];
                _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
                _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];

                if(_N1 == 0 && _N2 == 0){
                    v[i] = zero;
                    continue;
                }

                if(_N1 != 0 && _N2 != 0){
                    //mul1 = gini_input[4*fd.pos + 4*i]*gini_input[4*fd.pos + 4*i+1];
                    //mul2 = gini_input[4*fd.pos + 4*i+2] * gini_input[4*fd.pos + 4*i+3];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    q1 = ((1ULL<<Q)*divident)/divisor;
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    q2 = ((1ULL<<Q)*divident)/divisor;

                    v[i] = F((1ULL<<Q) - q1-q2);
                }
                else if(_N1 == 0 ){
                    //mul2 = gini_input[4*fd.pos + 4*i+2] * gini_input[4*fd.pos + 4*i+3];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    v[i] = F((1ULL<<Q) - (((1ULL<<Q)*divident)/divisor));
                }else{
                    //mul1 = gini_input[4*fd.pos + 4*i]*gini_input[4*fd.pos + 4*i+1];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    v[i] = F((1ULL<<Q) - ((1ULL<<Q)*divident)/divisor);
                    
                }         
            }
        }
    
    }else if(fd.name == "sub_ginis"){
        unsigned long long int _N1,_N2,mul1,mul2,divisor,divident;
        unsigned long long int q1,q2;
        if(4*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < size; i++){
                v[i] = zero;
            }
        }else{
            int _pos,row,col;
            int pos = (4*fd.pos)%split_size;
            if(pos == 0) {
                compute_ginis(4*fd.pos/split_size);
            }

            for(int i = 0; i < size; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((4*fd.pos+4*i)/split_size);
                }
                //_N1 = gini_input[4*fd.pos + 4*i] + gini_input[4*fd.pos + 4*i+1];
                //_N2 = gini_input[4*fd.pos + 4*i+2] + gini_input[4*fd.pos + 4*i+3];
                _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
                _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
                
                _pos = i+ fd.pos; 
                _pos = (_pos - (_pos%bin_size))/bin_size;
                row = (_pos - (_pos%attr))/attr;
                col = _pos%attr;
                if(_N1 == 0 && _N2 == 0){
                    v[i] = zero;
                    continue;
                }

                if(_N1 != 0 && _N2 != 0){
                    //mul1 = gini_input[4*fd.pos + 4*i]*gini_input[4*fd.pos + 4*i+1];
                    //mul2 = gini_input[4*fd.pos + 4*i+2] * gini_input[4*fd.pos + 4*i+3];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    q1 = ((1ULL<<Q)*divident)/divisor;
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    q2 = ((1ULL<<Q)*divident)/divisor;

                    v[i] = F((1ULL<<Q) - q1-q2 - best_gini[row][col]);
                }
                else if(_N1 == 0 ){
                    //mul2 = gini_input[4*fd.pos + 4*i+2] * gini_input[4*fd.pos + 4*i+3];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    v[i] = F((1ULL<<Q) - (((1ULL<<Q)*divident)/divisor) - best_gini[row][col]);
                }else{
                    //mul1 = gini_input[4*fd.pos + 4*i]*gini_input[4*fd.pos + 4*i+1];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    v[i] = F((1ULL<<Q) - (((1ULL<<Q)*divident)/divisor) - best_gini[row][col]);
                    
                }         
            }
        }
    }else if(fd.name == "sub_ginis_bits"){
        unsigned long long int _N1,_N2,mul1,mul2,divisor,divident;
        unsigned long long int q1,q2;
        int _pos,row,col;
        vector<F> arr(size);
            
        if(4*fd.pos >= forest.size()*split_size){
            for(int i = 0; i  < 32*size; i++){
                v[i] = zero;
            }
        }else{
            //F *arr = (F *)malloc(sizeof(F)*size/4);
            int pos = (4*fd.pos)%split_size;
            if(pos == 0) {
                compute_ginis(4*fd.pos/split_size);
            }

            for(int i = 0; i < size; i++){
                if(pos + 4*i == split_size) [[unlikely]]{
                    pos -= split_size;
                    compute_ginis((4*fd.pos+4*i)/split_size);
                }
                _N1 = gini_input[pos + 4*i] + gini_input[pos + 4*i+1];
                _N2 = gini_input[pos + 4*i+2] + gini_input[pos + 4*i+3];
                
                //_N1 = gini_input[4*fd.pos + 4*i] + gini_input[4*fd.pos + 4*i+1];
                //_N2 = gini_input[4*fd.pos + 4*i+2] + gini_input[4*fd.pos + 4*i+3];
                //_pos = i+ fd.pos; 
                
                _pos = i+ fd.pos; 
                _pos = (_pos - (_pos%bin_size))/bin_size;
                row = (_pos - (_pos%attr))/attr;
                col = _pos%attr;
                if(_N1 == 0 && _N2 == 0){
                    arr[i] = zero;
                    continue;
                }

                if(_N1 != 0 && _N2 != 0){
                    //mul1 = gini_input[4*fd.pos + 4*i]*gini_input[4*fd.pos + 4*i+1];
                    //mul2 = gini_input[4*fd.pos + 4*i+2] * gini_input[4*fd.pos + 4*i+3];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    q1 = ((1ULL<<Q)*divident)/divisor;
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    q2 = ((1ULL<<Q)*divident)/divisor;
                    arr[i] = F((1ULL<<Q) - q1-q2 - best_gini[row][col]);
                }
                else if(_N1 == 0 ){
                    //mul2 = gini_input[4*fd.pos + 4*i+2] * gini_input[4*fd.pos + 4*i+3];
                    mul2 = gini_input[pos + 4*i+2] * gini_input[pos + 4*i+3];
                    divisor = _N2*(_N1+_N2);
                    divident = _N2*_N2- 2*mul2;
                    arr[i] = F((1ULL<<Q) - (((1ULL<<Q)*divident)/divisor) - best_gini[row][col]);
                }else{
                    //mul1 = gini_input[4*fd.pos + 4*i]*gini_input[4*fd.pos + 4*i+1];
                    mul1 = gini_input[pos + 4*i]*gini_input[pos + 4*i+1];
                    divisor = _N1*(_N1+_N2);
                    divident = _N1*_N1- 2*mul1;
                    arr[i] = F((1ULL<<Q) - (((1ULL<<Q)*divident)/divisor) - best_gini[row][col]);
                    
                }         
            }
            v = prepare_bit_vector(arr,32);
        }
        
    }
    else{
        printf("Invalid stream for split SNARK\n");
    }
    
    fd.pos += size;

    return fd.pos;
}

void get_powers(vector<F> &powers_table, int instances, int trees){
    prev_rand = seed;
    F prev;
    int idx;
    F divisor = F(1<<16);
    for(int i = 0; i < instances*trees; i++){
        prev = A_*prev_rand + B_;
        idx = _shift_int(prev);
        //idx = (prev - divisor*_divide(prev,divisor)).getInt64();
        
        prev_rand = prev;
        powers_table[idx] += one;
    }

}

int get_witness_bagging(stream_descriptor &fd, vector<F> &v, int size){
    if(fd.name == "randomness"){
        if(fd.pos == 0){
            prev_rand = seed;
        }

        for(int i = 0; i < size; i++){
            v[i] = A_*prev_rand + B_;
            prev_rand = v[i];
        }
    }else if(fd.name == "randomness_remainder"){
        if(fd.pos == 0){
            prev_rand = seed;
        }
        F prev;
        F divisor = F(1ULL<<16);
        for(int i = 0; i < size; i++){
            prev = A_*prev_rand + B_;
            v[i] = _shift(prev);//prev - F(1<<Q)*_divide(prev,divisor);
            prev_rand = prev;
        }
    }
    else if(fd.name == "randomness_quotient"){
        if(fd.pos == 0){
            prev_rand = seed;
        }

        F prev;
        F divisor = F(1ULL<<16);
        for(int i = 0; i < size; i++){
            prev = A_*prev_rand + B_;
            v[i] = _divide(prev,divisor);
            prev_rand = prev;
        }
    }else if(fd.name == "quotient_bits"){
        if(fd.pos == 0){
            prev_rand = seed;
        }

        F prev;
        F divisor = F(1ULL<<16);
        vector<F> buff(size);
        for(int i = 0; i < size; i++){
            prev = A_*prev_rand + B_;
            buff[i] = _shift_right(prev);
            prev_rand = prev;
        }
        v = prepare_bit_vector(buff, 256);
    }
    else if(fd.name == "pairs"){
        if(fd.pos == 0){
            prev_rand = seed;
        }
        F prev;
        F divisor = F(1ULL<<16);
        int idx;
        
        for(int i = 0; i < size/2; i++){
            prev = A_*prev_rand + B_;
            //idx = (prev - divisor*_divide(prev,divisor)).getInt64();
            idx = _shift_int(prev);//(prev - divisor*_divide(prev,divisor)).getInt64();
            prev_rand = prev;
            v[2*i] = discrete_table[idx];
            v[2*i+1] = idx; 
        }
    }else if(fd.name == "s1"){
        F s = fd.compress_vector[1];
        if(fd.pos == 0){
           
            s = fd.compress_vector[0];
            fd.compress_vector[1] = zero; 
        }
        for(int i = 0; i < size; i++){
            v[i] = fd.compress_vector[1];
            if(fd.pos == 0 && i == 0){
                fd.compress_vector[1] = s;
            }else{
                fd.compress_vector[1] = fd.compress_vector[1]*s;
            }
        }
    }else if(fd.name == "s2"){
        F s = fd.compress_vector[1];
        if(fd.pos == 0){
           
            s = fd.compress_vector[0];
            fd.compress_vector[1] = s; 
        }
        for(int i = 0; i < size; i++){
            v[i] = fd.compress_vector[1];
            if(fd.pos + i == fd.size - 1){
            
                v[i] = F(0);
            }else{
                fd.compress_vector[1] = fd.compress_vector[1]*s;
            }
        }
        
    }



    fd.pos += size;
    return fd.pos;
}



int get_witness_lookup(stream_descriptor &fd, vector<F> &v, int size){
    if(fd.name == "indexes"){
        if(fd.pos >= fd.size){
            printf("RESETTING STREAM forest\n");
            fd.pos = 0;
        }
        if(fd.pos == 0){
            lookup_stream.pos = 0;
        }
        if(fd.pos % lookup_stream.size ==0){
            lookup_stream.pos = 0;
        }
     
        //int segment = fd.pos/lookup_input.size();
        int segment = fd.pos/lookup_stream.size;
        vector<int> buff;
        vector<F> buff_field;
        if(domain < 128){
            if(size > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

            }else{
                buff.resize(size);
                get_lookup_stream(buff,size);

            }
        }else{
            if(size > lookup_stream.size){
                buff_field.resize(lookup_stream.size);
                get_lookup_stream_field(buff_field,lookup_stream.size);

            }else{
                buff_field.resize(size);
                get_lookup_stream_field(buff_field,size);

            }
        }
        
        
        
        for(int i =0; i < size; i++){
            if(i%lookup_stream.size == 0){
                segment = (fd.pos+i)/lookup_stream.size;
            }
           
            //int idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
            int idx;
           
                if(domain < 128){
                    idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
                }else{
                    idx = get_byte(segment,buff_field[(i)%lookup_stream.size]);
                    
                }
            //v[i] = F(idx);
            v[i] = table[(idx)];
        }
        fd.pos += size;
    }
    else if(fd.name == "read_table"){
        if(fd.pos >= fd.size){
            printf("RESETTING STREAM forest\n");
            fd.pos = 0;
        }
        if(fd.pos == 0){
            lookup_stream.pos = 0;
            for(int i = 0; i < lookup_read.size(); i++){
                for(int j = 0; j < lookup_read[i].size(); j++){
                    lookup_read[i][j] = zero;
                }
            }
        }
        if(fd.pos % lookup_stream.size ==0){
            lookup_stream.pos = 0;
        }
     
        //int segment = fd.pos/lookup_input.size();
        int segment = fd.pos/lookup_stream.size;
        vector<int> buff;
        vector<F> buff_field;

        if(domain < 128){
            if(size/2 > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

            }else{
                buff.resize(size/2);
                get_lookup_stream(buff,size/2);

            }
        }else{
            if(size/2 > lookup_stream.size){
                buff_field.resize(lookup_stream.size);
                get_lookup_stream_field(buff_field,lookup_stream.size);

            }else{
                buff_field.resize(size/2);
                get_lookup_stream_field(buff_field,size/2);

            }
        }
        /*
            if(size/2 > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

            }else{
                buff.resize(size/2);
                get_lookup_stream(buff,size/2);
                

            }
        */
        for(int i = 0; i < size/2; i++){
            if(i%lookup_stream.size == 0){
                    segment = (fd.pos+i)/lookup_stream.size;
                }
            
            //int idx = (lookup_input[(fd.pos+i)%lookup_input.size()]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
            //int idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
            int idx;
                char bytes[32];
                if(domain < 128){
                    idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
                }else{
                  idx = get_byte(segment,buff_field[(i)%lookup_stream.size]);
                    
                }
            //v[2*i] = F(idx);
            v[2*i] = table[(idx)];
            v[2*i+1] = lookup_read[segment][idx];
            lookup_read[segment][idx] += 1;
        }
        fd.pos += size/2;
    }
    else if(fd.name == "write_table"){
       
        if(fd.pos >= fd.size){
            printf("RESETTING STREAM forest\n");
            fd.pos = 0;
        }
        if(fd.pos == 0){
            lookup_stream.pos = 0;
            for(int i = 0; i < lookup_write.size(); i++){
                for(int j = 0; j < lookup_write[i].size(); j++){
                    lookup_write[i][j] = zero;
                }
            }
        }
        if(fd.pos % lookup_stream.size ==0){
            lookup_stream.pos = 0;
        }
     
        
        //int segment = fd.pos/lookup_input.size();
        int segment = fd.pos/lookup_stream.size;
           
        vector<int> buff;
        vector<F> buff_field;

        if(domain < 128){
            if(size/2 > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

            }else{
                buff.resize(size/2);
                get_lookup_stream(buff,size/2);

            }
        }else{
            if(size/2 > lookup_stream.size){
                buff_field.resize(lookup_stream.size);
                get_lookup_stream_field(buff_field,lookup_stream.size);

            }else{
                buff_field.resize(size/2);
                get_lookup_stream_field(buff_field,size/2);

            }
        }
        /*
            if(size/2 > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

            }else{
                
                buff.resize(size/2);
                get_lookup_stream(buff,size/2);
             
            }
        */    
        for(int i = 0; i < size/2; i++){
            if(i%lookup_stream.size == 0){
                    segment = (fd.pos+i)/lookup_stream.size;
                }
            
            //int idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
            int idx;
             if(domain < 128){
                    idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
                }else{
                 idx = get_byte(segment,buff_field[(i)%lookup_stream.size]);
                    
                }
            //v[2*i] = F(idx);
            v[2*i] = table[idx];
            v[2*i+1] = lookup_write[segment][idx] + one;
            lookup_write[segment][idx] += one;
        }
        fd.pos += size/2;
    }else if(fd.name == "compressed_lookup_read"){
        if(fd.pos >= fd.size){
            printf("RESETTING STREAM forest\n");
            fd.pos = 0;
        }
        if(fd.pos == 0){
            lookup_stream.pos = 0;
            for(int i = 0; i < lookup_read.size(); i++){
                for(int j = 0; j < lookup_read[i].size(); j++){
                    lookup_read[i][j] = zero;
                }
            }
        }
        if(fd.pos % lookup_stream.size ==0){
            lookup_stream.pos = 0;
        }
     

        //int segment = fd.pos/lookup_input.size();
        int segment = fd.pos/lookup_stream.size;
        vector<int> buff;
        vector<F> buff_field;
        if(domain < 128){
            if(size > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

            }else{
                buff.resize(size);
                get_lookup_stream(buff,size);

            }
        }else{
            if(size > lookup_stream.size){
                buff_field.resize(lookup_stream.size);
                get_lookup_stream_field(buff_field,lookup_stream.size);

            }else{
                buff_field.resize(size);
                get_lookup_stream_field(buff_field,size);

            }
        }
        /*
        
            if(size > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

            }else{
                buff.resize(size);
                get_lookup_stream(buff,size);

            }      
        */
        for(int i = 0; i < size; i++){
            if(i%lookup_stream.size == 0){
                segment = (fd.pos+i)/lookup_stream.size;
            }
            //int idx = (lookup_input[(fd.pos + i)%lookup_input.size()]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
            int idx;
            char bytes[32];
            if(domain < 128){
                idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
            }else{
                idx = get_byte(segment,buff_field[(i)%lookup_stream.size]);
                    
            }
            //v[i] = fd.compress_vector[0]*F(idx) + fd.compress_vector[1]*F(lookup_read[segment][idx]) + fd.compress_vector[2];
            v[i] = fd.compress_vector[0]*table[(idx)] + fd.compress_vector[1]*F(lookup_read[segment][idx]) + fd.compress_vector[2];
            lookup_read[segment][idx] += one;
        }
        fd.pos += size;
    }else if(fd.name == "compressed_lookup_write"){
        
        if(fd.pos >= fd.size){
            printf("RESETTING STREAM forest\n");
            fd.pos = 0;
        }
        if(fd.pos == 0){
            lookup_stream.pos = 0;
            for(int i = 0; i < lookup_write.size(); i++){
                for(int j = 0; j < lookup_write[i].size(); j++){
                    lookup_write[i][j] = zero;
                }
            }
        }
        if(fd.pos % lookup_stream.size ==0){
            lookup_stream.pos = 0;
        }
     
        //int segment = fd.pos/lookup_input.size();
        int segment = fd.pos/lookup_stream.size;
        vector<int> buff;
        vector<F> buff_field;
        if(domain < 128){
            if(size > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

            }else{
                buff.resize(size);
                get_lookup_stream(buff,size);

            }
        }else{
            if(size > lookup_stream.size){
                buff_field.resize(lookup_stream.size);
                get_lookup_stream_field(buff_field,lookup_stream.size);

            }else{
                buff_field.resize(size);
                get_lookup_stream_field(buff_field,size);

            }
        }
        /*
        if(size > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

        }else{
            buff.resize(size);
            get_lookup_stream(buff,size);

        }*/
        
        
        
        for(int i =0; i < size; i++){
            if(i%lookup_stream.size == 0){
                    segment = (fd.pos+i)/lookup_stream.size;
                }
            //int idx = (lookup_input[(fd.pos + i)%lookup_input.size()]>>quantization_level*(segment))%(1ULL<<quantization_level);
           // int idx = (buff[(i)%lookup_stream.size]>>quantization_level*(segment))%(1ULL<<quantization_level);
            int idx;
            char bytes[32];
            if(domain < 128){
                idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
            }else{
                idx = get_byte(segment,buff_field[(i)%lookup_stream.size]);
            }
            
            v[i] = fd.compress_vector[0]*table[(idx)] + fd.compress_vector[1]*(lookup_write[segment][idx] + 1) + fd.compress_vector[2];
            lookup_write[segment][idx] += one;
        }
        fd.pos += size;
    }else if(fd.name == "compressed_lookup_read_write"){
        
        if(fd.pos >= 2*fd.size){
            printf("RESETTING STREAM forest\n");
            fd.pos = 0;
        }
        if(fd.pos == 0){
            
            lookup_stream.pos = 0;
            for(int i = 0; i < lookup_read.size(); i++){
                for(int j = 0; j < lookup_read[i].size(); j++){
                    lookup_read[i][j] = zero;
                }
            }
            for(int i = 0; i < lookup_write.size(); i++){
                for(int j = 0; j < lookup_write[i].size(); j++){
                    lookup_write[i][j] = zero;
                }
            }
        }
        if(fd.pos == fd.size){
            lookup_stream.pos = 0;
        }
        if(fd.pos % lookup_stream.size ==0){
            lookup_stream.pos = 0;
        }
        
        if(size > fd.size){
            
            //exit(-1);
            int segment = fd.pos/lookup_stream.size;
                       
            vector<int> buff;
             vector<F> buff_field;
            if(domain < 128){
                if(size > lookup_stream.size){
                    buff.resize(lookup_stream.size);
                    get_lookup_stream(buff,lookup_stream.size);

                }else{
                    buff.resize(size);
                    get_lookup_stream(buff,size);

                }
            }else{
                if(size > lookup_stream.size){
                    buff_field.resize(lookup_stream.size);
                    get_lookup_stream_field(buff_field,lookup_stream.size);

                }else{
                    buff_field.resize(size);
                    get_lookup_stream_field(buff_field,size);

                }
            }

        /*
            if(size > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

            }else{
                buff.resize(size);
                get_lookup_stream(buff,size);

            }
        */
            
            for(int i = 0; i <  fd.size; i++){
                if(i%lookup_stream.size == 0){
                    segment = (fd.pos+i)/lookup_stream.size;
                }
                int idx;
                
                if(domain < 128){
                    idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
                }else{
                    idx = get_byte(segment,buff_field[(i)%lookup_stream.size]);
                }
                v[i] = fd.compress_vector[0]*table[(idx)] + fd.compress_vector[1]*(lookup_read[segment][idx]) + fd.compress_vector[2];
                
                //v[i] = fd.compress_vector[0]*F(idx) + fd.compress_vector[1]*F(lookup_read[segment][idx]) + fd.compress_vector[2];
                lookup_read[segment][idx] += one;
            }
          
            for(int i = 0; i < fd.size; i++){
                if(i%lookup_stream.size == 0){
                    segment = (fd.pos+i)/lookup_stream.size;
                }
                //int idx = (lookup_input[(fd.pos + i)%lookup_input.size()]>>quantization_level*(segment))%(1ULL<<quantization_level);
                //int idx = (buff[(i)%lookup_stream.size]>>quantization_level*(segment))%(1ULL<<quantization_level);
                int idx;
                
                if(domain < 128){
                    idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
                }else{
                    idx = get_byte(segment,buff_field[(i)%lookup_stream.size]);
                }
                v[i + fd.size] = fd.compress_vector[0]*table[(idx)] + fd.compress_vector[1]*(lookup_write[segment][idx] + 1) + fd.compress_vector[2];
                
                //v[i + fd.size] = fd.compress_vector[0]*F(idx) + fd.compress_vector[1]*F(lookup_write[segment][idx] + 1) + fd.compress_vector[2];
                
                lookup_write[segment][idx] += one;
            } 
           
               
        }
        else if(fd.pos < fd.size){
            
            //int segment = fd.pos/lookup_input.size();
            int segment = fd.pos/lookup_stream.size;
                       
            vector<int> buff;
             vector<F> buff_field;
            if(domain < 128){
                if(size > lookup_stream.size){
                    buff.resize(lookup_stream.size);
                    get_lookup_stream(buff,lookup_stream.size);

                }else{
                    buff.resize(size);
                    get_lookup_stream(buff,size);

                }
            }else{
                if(size > lookup_stream.size){
                    buff_field.resize(lookup_stream.size);
                    get_lookup_stream_field(buff_field,lookup_stream.size);

                }else{
                    buff_field.resize(size);
                    get_lookup_stream_field(buff_field,size);

                }
            }
            /*
            if(size > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

            }else{
                buff.resize(size);
                get_lookup_stream(buff,size);

            }*/
            
            
            for(int i = 0; i <  size; i++){
                if(i%lookup_stream.size == 0){
                    segment = (fd.pos+i)/lookup_stream.size;
                }

                //int idx = (lookup_input[(fd.pos + i)%lookup_input.size()]>>quantization_level*(segment))%(1ULL<<quantization_level);
                //int idx = (buff[(i)%lookup_stream.size]>>quantization_level*(segment))%(1ULL<<quantization_level);
                int idx;
                char bytes[32];
                if(domain < 128){
                    idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
                }else{
                    idx = get_byte(segment,buff_field[(i)%lookup_stream.size]);
                        
                }
                //v[i] = fd.compress_vector[0]*F(idx) + fd.compress_vector[1]*F(lookup_read[segment][idx]) + fd.compress_vector[2];
                
                v[i] = fd.compress_vector[0]*table[(idx)] + fd.compress_vector[1]*(lookup_read[segment][idx]) + fd.compress_vector[2];
                lookup_read[segment][idx] += one;
            }
        

        }
        else{
            if(fd.pos % lookup_stream.size ==0){
                lookup_stream.pos = 0;
            }
     
            //int segment = fd.pos/lookup_input.size();
            int segment = (fd.pos-fd.size)/lookup_stream.size;
            
            
            vector<int> buff;
             vector<F> buff_field;
            if(domain < 128){
                if(size > lookup_stream.size){
                    buff.resize(lookup_stream.size);
                    get_lookup_stream(buff,lookup_stream.size);

                }else{
                    buff.resize(size);
                    get_lookup_stream(buff,size);

                }
            }else{
                if(size > lookup_stream.size){
                    buff_field.resize(lookup_stream.size);
                    get_lookup_stream_field(buff_field,lookup_stream.size);

                }else{
                    buff_field.resize(size);
                    get_lookup_stream_field(buff_field,size);

                }
            }
            /*
            if(size > lookup_stream.size){
                buff.resize(lookup_stream.size);
                get_lookup_stream(buff,lookup_stream.size);

            }else{
                buff.resize(size);
                get_lookup_stream(buff,size);

            }*/
            
      
            for(int i = 0; i < size; i++){
                if(i%lookup_stream.size == 0){
                    segment = (fd.pos+i- fd.size)/lookup_stream.size;
                }
                
                
                //int idx = (lookup_input[(fd.pos + i)%lookup_input.size()]>>quantization_level*(segment))%(1ULL<<quantization_level);
                //int idx = (buff[(i)%lookup_stream.size]>>quantization_level*(segment))%(1ULL<<quantization_level);
                int idx;
                
                if(domain < 128){
                    idx = (buff[(i)%lookup_stream.size]/(1ULL<<(quantization_level*(segment))))%(1ULL<<quantization_level);
                }else{
                    idx = get_byte(segment,buff_field[(i)%lookup_stream.size]);
                }
                
             
                v[i] = fd.compress_vector[0]*table[(idx)] + fd.compress_vector[1]*F(lookup_write[segment][idx] + 1) + fd.compress_vector[2];
                //v[i] = fd.compress_vector[0]*F(idx) + fd.compress_vector[1]*F(lookup_write[segment][idx] + 1) + fd.compress_vector[2];
                
                lookup_write[segment][idx] += 1;
            }
        
        }
        fd.pos += size;
    }else{
        printf("Error, lookup stream not implemented\n");
        exit(-1);
    }
    return fd.pos;
}


int get_witness_hist(stream_descriptor &fd, vector<F> &v, int size){
    
    int stream_size = 0;
    
    if(fd.name == "final_hist")stream_size = forest.size()*forest[0].size()*2*bin_size*D_train.data.size();
    else if(fd.name == "node_hist")stream_size = forest.size()*(forest[0].size()-1)*2*bin_size*D_train.data.size();
    else if(fd.name == "witness_hist")stream_size = forest.size()*(2*forest[0].size()-2)*2*bin_size*D_train.data.size();
    else if(fd.name == "out_hist")stream_size = forest.size()*(2*forest[0].size()-2)*bin_size*D_train.data.size();

    int hist_size = stream_size/forest.size();
    
    
    if(fd.pos >= stream_size){
        for(int i = 0; i < size; i++){
            v[i] = zero;
        }
        fd.pos += size;
        return size;
    }
    
    int counter = 0;
            
    int pos_counter = 0;
    int data_read = 0;
    while(true){
          
        if(fd.pos%hist_size == 0){
    
            if(fd.name == "final_hist")compute_histogram(fd.pos/hist_size);
            else if(fd.name == "node_hist")compute_node_histogram(fd.pos/hist_size);
            else if(fd.name == "witness_hist")compute_witness_hist(fd.pos/hist_size);
            else if(fd.name == "out_hist")compute_out_hist(fd.pos/hist_size);

        }
        if(fd.name == "final_hist"){
            for(int i = 0; i < histograms.size(); i++){
                for(int j = 0; j < histograms[0].size(); j++){
                    for(int l = 0; l < histograms[0][0][0].size(); l++){
                        if(pos_counter < fd.pos%hist_size){
                            pos_counter++;
                            continue;
                        }
                        if(counter == size){
                            fd.pos += data_read;
                            return size;
                        }
                        v[counter] =  histograms[i][j][0][l];
                        v[counter+1] = histograms[i][j][1][l];
                        counter+=2;
                        data_read+=2;    
                    }
                }
            }
        }else if(fd.name == "node_hist"){
            for(int i = 0; i < node_histogram.size(); i++){
                for(int j = 0; j < node_histogram[0].size(); j++){
                    for(int l = 0; l < node_histogram[0][0].size(); l++){
                        if(pos_counter < fd.pos%hist_size){
                            pos_counter++;
                            continue;
                        }
                        if(counter == size){
                            fd.pos += data_read;
                            return 0;
                        }
                        v[counter] =  node_histogram[i][j][l];
                        counter++;
                        data_read++;    
                    }
                }
            }
        }else{
            int rows,cols;
           
            if(fd.name == "witness_hist"){
                rows = witness_hist.size();
                cols = witness_hist[0].size();
            }else{
                rows = out_hist.size();
                cols = out_hist[0].size();
            }
           
            for(int i = 0; i < rows; i++){
                for(int j = 0; j < cols; j++){
                    if(pos_counter < fd.pos%hist_size){
                        pos_counter++;
                        continue;
                    }
                    if(counter == size){
                        fd.pos += data_read;
                        return 0;
                    }
                    if(fd.name == "witness_hist")v[counter] =  witness_hist[i][j];
                    else v[counter] = out_hist[i][j];
                    
                    counter++;
                    data_read++;    
                }
            }
        }
        fd.pos += data_read;
        data_read = 0;
        if(fd.pos == stream_size){
            break;
        }
    }
    if(counter < size){
     
        for(int i = counter; i < size; i++){
            v[i] = zero;
            fd.pos++;
        }
    }           
    return size;
}

int get_witness_forest_int(stream_descriptor &fd, vector<int> &v, int size){

    
   
    int offset = 0; 
    Tree_Inference_Data inference_data;
    
    
    v.clear();
   
    if(fd.pos >= _forest.size()*D_train.data[0].size() && fd.name != "read_write_transcript"){
        printf("RESETTING STREAM forest\n");
        fd.pos = 0;
    }
    if((fd.pos == _forest.size()*D_train.data[0].size() || fd.pos == 0) && (fd.name == "read_write_transcript" ||fd.name == "read_transcript"||fd.name == "write_transcript" || fd.name == "histogram_counter") ){
        offset = fd.pos;
        //printf("Clearning histograms %d\n",fd.pos);

        reset_histograms_forest();
        //printf("OK\n");
        //reset_histograms();
    }
    if((fd.pos > _forest.size()*D_train.data[0].size()) && fd.name == "read_write_transcript"){
        offset = _forest.size()*D_train.data[0].size();
    }
    if(fd.pos >= 2*_forest.size()*D_train.data[0].size()){
        printf("Resetting read/write\n");
        fd.pos = 0;
    }
    int pos_init = fd.pos;
    
    
    //printf("%s\n",fd.name.c_str());
    
    vector<int> buff(8,0);
    vector<int> x(D_train.data.size());

    vector<F> permuted_input(2*D_train.data.size()),diff(_forest[0][0].size()-1),input(2*D_train.data.size());
    vector<F> path(4*(_forest[0][0].size()-1)),aux(2);
    vector<F> bits;
        
        //printf("%d,%d \n ",fd.pos,fd.pos+size-1);
        for(int i = fd.pos-offset; i < fd.pos + size-offset; i++){
            //printf("_+DSAASD\n");
            
            int y;
            int instance = i/_forest.size();
            
            if(i == _forest.size()*D_train.data[0].size()){
                int r = i - fd.pos;
                //printf("Return : %d,%d\n",fd.pos, i - fd.pos);
                fd.pos += (i-fd.pos);
                return r;
            }
            for(int k = 0; k <D_train.data.size(); k++){
                x[k] =  D_train.data[k][instance];
            }
            y = D_train.label[instance];
                
            if(fd.name == "read_write_transcript"){
                instance = i%D_train.data[0].size();
                int tree_id = i/D_train.data[0].size();
                // previously : tree_id = i%_forest.size()
                
                if(instance == 0)reset_histograms_forest();    
                
                int pos = get_pos(_forest[tree_id], x,y);
                if(fd.pos < forest.size()*D_train.data[0].size()){
                    for(int j = 0; j < D_train.data.size(); j++){
                        buff[0] = (pos);
                        buff[1] = (j);
                        buff[2] = (D_train.data[j][instance]);
                        buff[3] = (y);
                        buff[4] = histograms_forest[pos][j][y][D_train.data[j][instance]];
                        histograms_forest[pos][j][y][D_train.data[j][instance]]++;
                        v.insert(v.end(),buff.begin(),buff.end());
                    }
                }else{
                    for(int j = 0; j < D_train.data.size(); j++){
                        buff[0] = (pos);
                        buff[1] = (j);
                        buff[2] = (D_train.data[j][instance]);
                        buff[3] = (y);
                        buff[4] = histograms_forest[pos][j][y][D_train.data[j][instance]] + 1;
                        histograms_forest[pos][j][y][D_train.data[j][instance]]++;
                        v.insert(v.end(),buff.begin(),buff.end());
                    }    
                }
            }
            else{
                printf("Error, stream not implemented yet %s\n",fd.name.c_str());
                exit(-1);
            }
            
        }
    
    
    
    fd.pos += size;
    return size;

}

int get_witness_forest(stream_descriptor &fd, vector<F> &v, int size){

    
   
    int offset = 0; 
    Tree_Inference_Data inference_data;
    
    if(fd.name == "final_hist" || fd.name == "node_hist" || fd.name == "witness_hist" || fd.name == "out_hist"){
       return get_witness_hist(fd,v,size);
    }
    v.clear();
   
    if(fd.pos >= _forest.size()*D_train.data[0].size() && fd.name != "read_write_transcript"){
        printf("RESETTING STREAM forest\n");
        fd.pos = 0;
    }
    if((fd.pos == _forest.size()*D_train.data[0].size() || fd.pos == 0) && (fd.name == "read_write_transcript" ||fd.name == "read_transcript"||fd.name == "write_transcript" || fd.name == "histogram_counter") ){
        offset = fd.pos;
        //printf("Clearning histograms %d\n",fd.pos);

        reset_histograms_forest();
        //printf("OK\n");
        //reset_histograms();
    }
    if((fd.pos > _forest.size()*D_train.data[0].size()) && fd.name == "read_write_transcript"){
        offset = _forest.size()*D_train.data[0].size();
    }
    if(fd.pos >= 2*_forest.size()*D_train.data[0].size()){
        printf("Resetting read/write\n");
        fd.pos = 0;
    }
    int pos_init = fd.pos;
    vector<int> x;
    if(fd.name == "diff" || fd.name == "bit_vector"){
        
        vector<F> temp_v;
        while(true){
            x.clear();
            int y;
		    for(int k =0; k < D_train.data.size(); k++){
			    x.push_back(D_train.data[k][fd.pos]);
		    }
            for(int j = fd.tree_pos; j < forest.size(); j++){
                clock_t t1,t2;
                t1 = clock();
                inference_data = Tree_Inference(_forest[j],x,y);
                t2 = clock();
                inference_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
                if(fd.name == "diff"){
                    temp_v = inference_data.diff;
                }else{
                    temp_v = inference_data.bit_vector;
                }
                if(v.size() + temp_v.size() < size){
                    if(fd.pos_j != 0){
                        for(int i = fd.pos_j; i < temp_v.size(); i++){
                            v.push_back(temp_v[i]);
                        }
                    }else{
                        v.insert(v.end(),temp_v.begin(),temp_v.end());
                    }
                }else{
                    for(int i = 0; i < temp_v.size(); i++){
                        v.push_back(temp_v[i]);
                        if(v.size() == size){
                            fd.pos_j = i;
                            fd.tree_pos = j;
                            return size;
                        }
                    }
                }
                if(fd.pos == D_train.data[0].size()-1){
                    return fd.pos - pos_init +1;
                }
                fd.pos_j = 0;
            }
            fd.pos++;
            fd.tree_pos = 0;
            
        }
    }
    //printf("%s\n",fd.name.c_str());
    else if(fd.name == "path_transpose" || fd.name == "path_aux_transpose"){
        int y;
        vector<F> path(4*(_forest[0][0].size()-1)),aux(2);
        for(int i = fd.pos; i < fd.pos + size; i++){
            x.clear();    
            if(i >= _forest.size()*D_train.data[0].size()){
                int r = i - fd.pos;
                fd.pos += (i-fd.pos);
                return r;
            }
            y = D_train.label[i%D_train.data[0].size()];
            for(int k = 0; k < D_train.data.size(); k++){
			    x.push_back(D_train.data[k][i%D_train.data[0].size()]);
		    }
            
            
            //inference_data = Tree_Inference(_forest[i/D_train.data[0].size()],x,y);
            
            
            if(fd.name == "path_transpose"){
                get_path(path,_forest[i/D_train.data[0].size()],x,y);
                //pad_vector(inference_data.path);
                //v.insert(v.end(),inference_data.path.begin(),inference_data.path.end());
                pad_vector(path);
                v.insert(v.end(),path.begin(),path.end());
                path.resize(4*(_forest[0][0].size()-1));
            }else if(fd.name == "path_aux_transpose"){
                get_aux(aux,_forest[i/D_train.data[0].size()],x,y);
                //v.insert(v.end(),inference_data.paths_aux.begin(),inference_data.paths_aux.end());
                v.push_back(aux[0]);
                v.push_back(aux[1]);
                
            }
        
        }
    }
    else if(fd.name == "input"){
        vector<F> input(2*D_train.type.size());
        for(int i = fd.pos-offset; i < fd.pos + size-offset; i++){
            x.clear();
            int y;
            if(i == D_train.data[0].size()){
                int r = i - fd.pos;
                //printf("Return : %d,%d\n",fd.pos, i - fd.pos);
                fd.pos += (i-fd.pos);
                return r;
            }
            for(int k = 0; k < D_train.type.size(); k++){
                x.push_back(D_train.data[k][i]);
            }
                
            inference_data = Tree_Inference(_forest[0],x,y);
            for(int k = 0; k < input.size()/2; k++){
                //input[2*k] = F(k);
                //input[2*k+1] = F(x[k]);
                input[2*k] = table[(k)];
                input[2*k+1] = table[(x[k])];
            }
            
            //v.insert(v.end(),input.begin(),input.end());
        
            //pad_vector(inference_data.input);
            v.insert(v.end(),inference_data.input.begin(),inference_data.input.end());
        }
    }
    else{
        vector<F> buff(8,zero);
        vector<int> x(D_train.data.size());

        vector<F> permuted_input(2*D_train.data.size()),diff(_forest[0][0].size()-1),input(2*D_train.data.size());
        vector<F> path(4*(_forest[0][0].size()-1)),aux(2);
        vector<F> bits;
        
        //printf("%d,%d \n ",fd.pos,fd.pos+size-1);
        for(int i = fd.pos-offset; i < fd.pos + size-offset; i++){
            //printf("_+DSAASD\n");
            
            int y;
            int instance = i/_forest.size();
            
            if(i == _forest.size()*D_train.data[0].size()){
                int r = i - fd.pos;
                //printf("Return : %d,%d\n",fd.pos, i - fd.pos);
                fd.pos += (i-fd.pos);
                return r;
            }
            for(int k = 0; k <D_train.data.size(); k++){
                x[k] =  D_train.data[k][instance];
            }
            y = D_train.label[instance];
            
                
            //inference_data = Tree_Inference(_forest[i%_forest.size()],x,y);
            
                
            if(fd.name == "permuted_input"){
                
                get_permuted_input(permuted_input,_forest[i%_forest.size()], x,y);
                 v.insert(v.end(),permuted_input.begin(),permuted_input.end());
               
                //pad_vector(inference_data.permuted_input);
                //v.insert(v.end(),inference_data.permuted_input.begin(),inference_data.permuted_input.end());
            }
            else if(fd.name == "input"){
                
                //pad_vector(inference_data.input);
                for(int k = 0; k < input.size()/2; k++){
                    //input[2*k] = F(k);
                    //input[2*k+1] = F(x[k]);
                    input[2*k] = table[(k)];
                    input[2*k+1] = table[(x[k])];
                }

                v.insert(v.end(),input.begin(),input.end());
           
                //v.insert(v.end(),inference_data.input.begin(),inference_data.input.end());
            }
            else if(fd.name == "path"){
                get_path(path, _forest[i%_forest.size()], x,y);
                pad_vector(path);
                v.insert(v.end(),path.begin(),path.end());
                path.resize(4*(_forest[i%_forest.size()][0].size()-1));
            }
            else if(fd.name == "path_aux"){
                get_aux(aux, _forest[i%_forest.size()], x,y);
                v.push_back(aux[0]);
                v.push_back(aux[1]);
                
            }
            else if(fd.name == "bit_vector"){
                get_bits(bits, _forest[i%_forest.size()], x,y);
                v.insert(v.end(),bits.begin(),bits.end());
                bits.clear();  
            }
            else if(fd.name == "diff"){
                get_diff(diff,_forest[i%_forest.size()], x,y);
                v.insert(v.end(),diff.begin(),diff.end());
            }
            else if(fd.name == "input_aux"){
                instance = i%D_train.data[0].size();
                int tree_id = i/D_train.data[0].size();
                // previously : tree_id = i%_forest.size()
                v.push_back(get_pos(_forest[tree_id], x,y));
                v.push_back(y);
            }else if(fd.name == "histogram_counter"){
                instance = i%D_train.data[0].size();
                int tree_id = i/D_train.data[0].size();
                // previously : tree_id = i%_forest.size()
                if(instance == 0)reset_histograms_forest();    
                int pos = get_pos(_forest[tree_id], x,y);
                for(int j = 0; j < D_train.data.size(); j++){
                    v.push_back(F(histograms_forest[pos][j][y][D_train.data[j][instance]]));
                    histograms_forest[pos][j][y][D_train.data[j][instance]]++;
                }
            }
            else if(fd.name == "read_transcript"){
                instance = i%D_train.data[0].size();
                int tree_id = i/D_train.data[0].size();
                // previously : tree_id = i%_forest.size()
                if(instance == 0)reset_histograms_forest();    
                
                int pos = get_pos(_forest[tree_id], x,y);
                for(int j = 0; j < D_train.data.size(); j++){
                    buff[0] = table[(pos)];
                    buff[1] = table[(j)];
                    buff[2] = table[(D_train.data[j][instance])];
                    buff[3] = table[(y)];
                    buff[4] = F(histograms_forest[pos][j][y][D_train.data[j][instance]]);
                    histograms_forest[pos][j][y][D_train.data[j][instance]]++;
                    v.insert(v.end(),buff.begin(),buff.end());
                }
            }else if(fd.name == "write_transcript"){
                instance =i%D_train.data[0].size();
                int tree_id = i/D_train.data[0].size();
                // previously : tree_id = i%_forest.size()
                if(instance == 0)reset_histograms_forest();    
               
                int pos = get_pos(_forest[tree_id], x,y);
                for(int j = 0; j < D_train.data.size(); j++){
                    buff[0] = table[(pos)];
                    buff[1] = table[(j)];
                    buff[2] = table[(D_train.data[j][instance])];
                    buff[3] = table[(y)];
                    buff[4] = F(histograms_forest[pos][j][y][D_train.data[j][instance]] + 1);
                    histograms_forest[pos][j][y][D_train.data[j][instance]]++;
                    v.insert(v.end(),buff.begin(),buff.end());
                }    
            }else if(fd.name == "read_write_transcript"){
                instance = i%D_train.data[0].size();
                int tree_id = i/D_train.data[0].size();
                // previously : tree_id = i%_forest.size()
                if(instance == 0)reset_histograms_forest();    
               
                int pos = get_pos(_forest[tree_id], x,y);
                if(fd.pos < forest.size()*D_train.data[0].size()){
                    for(int j = 0; j < D_train.data.size(); j++){
                        buff[0] = table[(pos)];
                        buff[1] = table[(j)];
                        buff[2] = table[(D_train.data[j][instance])];
                        buff[3] = table[(y)];
                        buff[4] = F(histograms_forest[pos][j][y][D_train.data[j][instance]]);
                        histograms_forest[pos][j][y][D_train.data[j][instance]]++;
                        v.insert(v.end(),buff.begin(),buff.end());
                    }
                }else{
                    for(int j = 0; j < D_train.data.size(); j++){
                        buff[0] = table[(pos)];
                        buff[1] = table[(j)];
                        buff[2] = table[(D_train.data[j][instance])];
                        buff[3] = table[(y)];
                        buff[4] = F(histograms_forest[pos][j][y][D_train.data[j][instance]] + 1);
                        histograms_forest[pos][j][y][D_train.data[j][instance]]++;
                        v.insert(v.end(),buff.begin(),buff.end());
                    }    
                }
            }
            else{
                printf("Error, stream not implemented yet %s\n",fd.name.c_str());
                exit(-1);
            }
            
        }
    
    }
    
    fd.pos += size;
    return size;

}

int get_witness_tree(stream_descriptor &fd, vector<F> &v, int size){
    v.clear();
    int offset = 0;
    Tree_Inference_Data inference_data;
    if(fd.pos >= D_train.data[0].size() && fd.name != "read_write_transcript"){
        printf("RESETTING STREAM\n");
        fd.pos = 0;
    }
    if((fd.pos == D_train.data[0].size() || fd.pos == 0) && (fd.name == "read_write_transcript" ||fd.name == "read_transcript"||fd.name == "write_transcript" || fd.name == "histogram_counter") ){
        offset = fd.pos;
        //printf("Clearning histograms %d\n",fd.pos);
        reset_histograms();
    }
    if((fd.pos > D_train.data[0].size()) && fd.name == "read_write_transcript"){
        offset = D_train.data[0].size();
    }
    if(fd.pos >= 2*D_train.data[0].size()){
        printf("Resetting read/write\n");
        fd.pos = 0;
    }
    int pos_init = fd.pos;
    vector<int> x;
    if(fd.name == "diff" || fd.name == "bit_vector"){
        vector<F> temp_v;
        while(true){
            x.clear();
            int y;
		    for(int k = 0; k < D_train.type.size(); k++){
			    x.push_back(D_train.data[k][fd.pos]);
		    }
            clock_t t1,t2;
                t1 = clock();
                
            inference_data = Tree_Inference(_tree,x,y);
                            t2 = clock();
                inference_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;

            if(fd.name == "diff"){
                temp_v = inference_data.diff;
            }else{
                temp_v = inference_data.bit_vector;
            }
            if(v.size() + temp_v.size() < size){
                if(fd.pos_j != 0){
                    for(int i = fd.pos_j; i < temp_v.size(); i++){
                        v.push_back(temp_v[i]);
                    }
                }else{
                    v.insert(v.end(),temp_v.begin(),temp_v.end());
                }
            }else{
                for(int i = 0; i < temp_v.size(); i++){
                    v.push_back(temp_v[i]);
                    if(v.size() == size){
                        fd.pos_j = i;
                        return size;
                    }
                }
            }
            if(fd.pos == D_train.data[0].size()-1){
                return fd.pos - pos_init +1;
            }
            fd.pos++;
            fd.pos_j = 0;
            
        }
    }
    vector<F> buff(8,zero);
    
    vector<F> permuted_input(2*D_train.data.size()),diff(_tree[0].size()-1),input(2*D_train.data.size());
    vector<F> path(4*(_tree[0].size()-1)),aux(2);
    vector<F> bits;
    //printf("%d,%d \n ",fd.pos,fd.pos+size-1);
	
    for(int i = fd.pos-offset; i < fd.pos + size-offset; i++){
		x.clear();
        int y;
		if(i == D_train.data[0].size()){
            int r = i - fd.pos;
            //printf("Return : %d,%d\n",fd.pos, i - fd.pos);
            fd.pos += (i-fd.pos);
            return r;
        }
        for(int k = 0; k < D_train.type.size(); k++){
			x.push_back(D_train.data[k][i]);
		}
		y = D_train.label[i];
        
        //inference_data = Tree_Inference(_tree,x,y);
        
        
        if(fd.name == "permuted_input"){
            get_permuted_input(permuted_input,_tree,x,y);
            //pad_vector(inference_data.permuted_input);
            //v.insert(v.end(),inference_data.permuted_input.begin(),inference_data.permuted_input.end());
            v.insert(v.end(),permuted_input.begin(),permuted_input.end());
        
        }
        else if(fd.name == "input"){
            //pad_vector(inference_data.input);
            for(int k = 0; k < input.size()/2; k++){
                //input[2*k] = F(k);
                //input[2*k+1] = F(x[k]);
                input[2*k] = table[(k)];
                input[2*k+1] = table[(x[k])];
            }
            //v.insert(v.end(),inference_data.input.begin(),inference_data.input.end());
            v.insert(v.end(),input.begin(),input.end());
        }
        else if(fd.name == "path"){

            //pad_vector(inference_data.path);
		    get_path(path, _tree, x,y);
            pad_vector(path);
            //v.insert(v.end(),inference_data.path.begin(),inference_data.path.end());
            v.insert(v.end(),path.begin(),path.end());
            path.resize(4*(_tree[0].size()-1));
        }
        else if(fd.name == "path_aux"){
            get_aux(aux, _tree, x,y);
            v.push_back(aux[0]);
            v.push_back(aux[1]);
            //v.insert(v.end(),inference_data.paths_aux.begin(),inference_data.paths_aux.end());
        }
        else if(fd.name == "bit_vector"){
            get_bits(bits,_tree, x,y);
            //v.insert(v.end(),inference_data.bit_vector.begin(),inference_data.bit_vector.end());
            v.insert(v.end(),bits.begin(),bits.end());
            bits.clear();
        }
        else if(fd.name == "diff"){
            //v.insert(v.end(),inference_data.diff.begin(),inference_data.diff.end());
            get_diff(diff,_tree, x,y);
            v.insert(v.end(),diff.begin(),diff.end());
            
        }
        else if(fd.name == "input_aux"){
            v.push_back(get_pos(_tree,x,y));
            v.push_back(y);
        }else if(fd.name == "histogram_counter"){
                int pos = get_pos(_tree,x,y);
              for(int j = 0; j < D_train.data.size(); j++){
                    //buff[0] = F(pos);
                    //buff[1] = F(j);
                    //buff[2] = F(D_train.data[j][instance]);
                    //buff[3] = (y);
                    //buff[4] = F(histograms_forest[i%_forest.size()][pos][j][y][D_train.data[j][instance]]);
                    v.push_back(F(histograms[pos][j][y][D_train.data[j][i]]));
                    histograms[pos][j][y][D_train.data[j][i]]++;
                    
                    //v.insert(v.end(),buff.begin(),buff.end());
                }
            }
        else if(fd.name == "read_transcript"){
            int pos = get_pos(_tree,x,y);
            for(int j = 0; j < D_train.data.size(); j++){
                //buff[0] = F(pos);
                //buff[1] = F(j);
                //buff[2] = F(D_train.data[j][i]);
                //buff[3] = (y);
                //buff[4] = F(histograms[pos][j][y][D_train.data[j][i]]);
                buff[0] = table[(pos)];
                buff[1] = table[(j)];
                buff[2] = table[(D_train.data[j][i])];
                buff[3] = table[(y)];
                buff[4] = F(histograms[pos][j][y][D_train.data[j][i]]);
                
                
                histograms[pos][j][y][D_train.data[j][i]]++;
                v.insert(v.end(),buff.begin(),buff.end());
            }
        }else if(fd.name == "write_transcript"){
            int pos = get_pos(_tree,x,y);
            
            for(int j = 0; j < D_train.data.size(); j++){
                //buff[0] = F(pos);
                //buff[1] = F(j);
                //buff[2] = F(D_train.data[j][i]);
                //buff[3] = (y);
                //buff[4] = F(histograms[pos][j][y][D_train.data[j][i]] + 1);
                buff[0] = table[(pos)];
                buff[1] = table[(j)];
                buff[2] = table[(D_train.data[j][i])];
                buff[3] = table[(y)];         
                buff[4] = F(histograms[pos][j][y][D_train.data[j][i]] + 1);
                histograms[pos][j][y][D_train.data[j][i]]++;
                v.insert(v.end(),buff.begin(),buff.end());
            }    
        }else if(fd.name == "read_write_transcript"){
             int pos = get_pos(_tree,x,y);
           
            if(fd.pos < D_train.data[0].size()){
                for(int j = 0; j < D_train.data.size(); j++){
                    //buff[0] = F(pos);
                    //buff[1] = F(j);
                    //buff[2] = F(D_train.data[j][i]);
                    //buff[3] = (y);
                    //buff[4] = F(histograms[pos][j][y][D_train.data[j][i]]);
                    buff[0] = table[(pos)];
                    buff[1] = table[(j)];
                    buff[2] = table[(D_train.data[j][i])];
                    buff[3] = table[(y)];         
                    buff[4] = F(histograms[pos][j][y][D_train.data[j][i]]);
                    histograms[pos][j][y][D_train.data[j][i]]++;
                    v.insert(v.end(),buff.begin(),buff.end());
                }
            }else{
                for(int j = 0; j < D_train.data.size(); j++){
                    //buff[0] = F(pos);
                    //buff[1] = F(j);
                    //buff[2] = F(D_train.data[j][i]);
                    //buff[3] = (y);
                    //buff[4] = F(histograms[pos][j][y][D_train.data[j][i]] + 1);
                    buff[0] = table[(pos)];
                    buff[1] = table[(j)];
                    buff[2] = table[(D_train.data[j][i])];
                    buff[3] = table[(y)];         
                    buff[4] = F(histograms[pos][j][y][D_train.data[j][i]]+1);
                    histograms[pos][j][y][D_train.data[j][i]]++;
                    v.insert(v.end(),buff.begin(),buff.end());
                }    
            }
        }
        else{
            printf("Tree training  : Error, stream not implemented yet %s\n", fd.name.c_str());
            exit(-1);
        }
    }
    fd.pos += size;
    return size;
}

int get_witness(stream_descriptor &fd ,vector<F> &v,int size){
    if(_tree.size() != 0){
        
        return get_witness_tree(fd,v,size);
    }else{
        
        return get_witness_forest(fd,v,size);
    }
}


void get_final_hist_forest(vector<vector<F>> &final_histogram){
   
    vector<vector<vector<vector<int>>>> _histograms;
    
    for(int l = 0; l < final_histogram.size(); l++){
        _histograms.clear();
        _histograms.resize(forest[l].size());
        for(int i = 0; i < forest[l].size(); i++){
            _histograms[i].resize(D_train.data.size());
            for(int j = 0; j < D_train.data.size(); j++){
                _histograms[i][j].resize(2);
                _histograms[i][j][0].resize(bin_size,0);
                _histograms[i][j][1].resize(bin_size,0);
            }
        }
    
        vector<int> x;
        Tree_Inference_Data inference_data;
        for(int i = 0; i < D_train.data[0].size(); i++){
            x.clear();
            int y;
            for(int k = 0; k < D_train.type.size(); k++){
                x.push_back(D_train.data[k][i]);
            }
            y = D_train.label[i];
            clock_t t1,t2;
                t1 = clock();
                
            inference_data = Tree_Inference(_forest[l],x,y);
                            t2 = clock();
                inference_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;

            for(int j = 0; j < D_train.data.size(); j++){
                _histograms[inference_data.pos][j][y][D_train.data[j][i]]+=1;
            }
        }

        for(int i = 0; i < forest[l].size(); i++){
            for(int j = 0; j < D_train.data.size(); j++){
                for(int k = 0; k < bin_size; k++){
                    //final_histogram[l][i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][0] = F(i);
                    //final_histogram[l][i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][1] = F(j);
                    //final_histogram[l][i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][2] = F(k);
                    //final_histogram[l][i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][3] = F(0);
                    final_histogram[l][i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k] = F(_histograms[i][j][0][k]);

                    //final_histogram[l][i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][0] = F(i);
                    //final_histogram[l][i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][1] = F(j);
                    //final_histogram[l][i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][2] = F(k);
                    //final_histogram[l][i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][3] = F(1);
                    final_histogram[l][i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1] = F(_histograms[i][j][1][k]);
                }
            }
        }   

    }

}

void get_final_hist(vector<vector<F>> &final_histogram){
   
    vector<vector<vector<vector<F>>>> _histograms(tree.size());
    for(int i = 0; i < tree.size(); i++){
        _histograms[i].resize(D_train.data.size());
        for(int j = 0; j < D_train.data.size(); j++){
            _histograms[i][j].resize(2);
            _histograms[i][j][0].resize(bin_size,0);
            _histograms[i][j][1].resize(bin_size,0);
        }
    }
   
    vector<int> x;
    Tree_Inference_Data inference_data;
    for(int i = 0; i < D_train.data[0].size(); i++){
        x.clear();
        int y;
		for(int k = 0; k < D_train.type.size(); k++){
			x.push_back(D_train.data[k][i]);
		}
		y = D_train.label[i];
        clock_t t1,t2;
                t1 = clock();
                
		inference_data = Tree_Inference(_tree,x,y);
                    t2 = clock();
                inference_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;

        for(int j = 0; j < D_train.data.size(); j++){
            _histograms[inference_data.pos][j][y][D_train.data[j][i]]+=one;
        }
    }
    
    for(int i = 0; i < tree.size(); i++){
        for(int j = 0; j < D_train.data.size(); j++){
            for(int k = 0; k < bin_size; k++){
                final_histogram[i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][0] = F(i);
				final_histogram[i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][1] = F(j);
				final_histogram[i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][2] = F(k);
				final_histogram[i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][3] = F(0);
				final_histogram[i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][4] = _histograms[i][j][0][k];

				final_histogram[i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][0] = F(i);
				final_histogram[i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][1] = F(j);
				final_histogram[i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][2] = F(k);
				final_histogram[i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][3] = F(1);
				final_histogram[i*(D_train.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][4] = _histograms[i][j][1][k];
            }
        }
    }
}

int get_compressed_data(stream_descriptor &fd ,vector<F> &v,int size){
        
    if(fd.name == "compressed_path"){
        stream_descriptor fd2,fd3;
        fd2.pos = fd.pos;fd3.pos = fd.pos;
        if(_tree.size() != 0){
            fd2.name = "path";
            fd3.name = "path_aux";
        
        }else{
            
            fd2.name = "path_transpose";
            fd3.name = "path_aux_transpose";
        }
        vector<F> v_temp,v_temp_aux;
        vector<F> compress_vector = fd.compress_vector;
        
        
        int counter = 0;
        for(int i = 0; i < size; i+=(512/(compress_vector.size()-2))){
            counter += (512/(compress_vector.size()-2));
            get_witness(fd2,v_temp,512/(compress_vector.size()-2));
            //printf("%d\n", fd2.pos);
            get_witness(fd3,v_temp_aux,512/(compress_vector.size()-2));
            //printf("%d\n", fd3.pos);
            for(int j = 0; j < 512/(compress_vector.size()-2); j++){
                v[i + j] = one;
                for(int k = 0; k < compress_vector.size()-2; k++){
                    v[i + j] += compress_vector[k]*v_temp[j*(compress_vector.size()-2) + k];
                }
                v[i+j] += compress_vector[compress_vector.size()-2]*v_temp_aux[2*j] + 
                            compress_vector[compress_vector.size()-1]*v_temp_aux[2*j+1]; 
                
            }
            v_temp.clear();
            v_temp_aux.clear();
        }
        fd.pos += size;
   
    }else if(fd.name == "compressed_input"){
        stream_descriptor fd2;
        
        if(size == 2*D_train.data.size()*D_train.data[0].size()){
            fd2.pos = fd.pos/D_train.data.size();
            fd2.name = "input";
            vector<F> temp_v,compress_vector = fd.compress_vector;
                
            get_witness(fd2,temp_v,size/(2*D_train.data.size()));
            for(int i = 0; i < size/2; i++){
                v[i] = temp_v[2*i]*compress_vector[0] + temp_v[2*i+1]*compress_vector[1] + compress_vector[2];     
            }
            fd2.pos = 0;
            fd2.name = "permuted_input";
            temp_v.clear();
            get_witness(fd2,temp_v,size/(2*D_train.data.size()));
            for(int i = 0; i < size/2; i++){
                v[i+size/2] = temp_v[2*i]*compress_vector[0] + temp_v[2*i+1]*compress_vector[1] + compress_vector[2];     
            }   

        }else{
            if(fd.pos < D_train.data.size()*D_train.data[0].size()){
                fd2.pos = fd.pos/D_train.data.size();
                fd2.name = "input";
                vector<F> temp_v,compress_vector = fd.compress_vector;
                get_witness(fd2,temp_v,size/D_train.data.size());
                for(int i = 0; i < size; i++){
                    v[i] = temp_v[2*i]*compress_vector[0] + temp_v[2*i+1]*compress_vector[1] + compress_vector[2];     
                }
            }else{
                fd2.pos = (fd.pos-D_train.data.size()*D_train.data[0].size())/D_train.data.size();
                fd2.name = "permuted_input";
                vector<F> temp_v,compress_vector = fd.compress_vector;
                get_witness(fd2,temp_v,size/D_train.data.size());
                for(int i = 0; i < size; i++){
                    v[i] = temp_v[2*i]*compress_vector[0] + temp_v[2*i+1]*compress_vector[1] + compress_vector[2];     
                }
            }
        }
        
        fd.pos += size;
    }else if(fd.name == "compressed_input_forest"){
        stream_descriptor fd2;
        
        fd2.pos = fd.pos/D_train.data.size();
        fd2.name = "input";
        vector<F> temp_v,compress_vector = fd.compress_vector;
        
                
        get_witness(fd2,temp_v,size/(D_train.data.size()));
        
        for(int i = 0; i < size; i++){
            v[i] = temp_v[2*i]*compress_vector[0] + temp_v[2*i+1]*compress_vector[1] + compress_vector[2];     
        }
        fd.pos += size;
    
    }else if(fd.name == "compressed_pairs"){
        stream_descriptor fd2;
        
        fd2.pos = fd.pos*2;
        fd2.name = "pairs";
        vector<F> temp_v(2*size),compress_vector = fd.compress_vector;
        
                
        get_witness_bagging(fd2,temp_v,2*size);
        
        for(int i = 0; i < size; i++){
            v[i] = temp_v[2*i]*compress_vector[0] + temp_v[2*i+1]*compress_vector[1] + compress_vector[2];     
        }
        fd.pos += size;
    
    }
    else if(fd.name == "compressed_perm_forest"){
        stream_descriptor fd2;
        
        fd2.pos = fd.pos/D_train.data.size();
        fd2.name = "permuted_input";
        vector<F> temp_v,compress_vector = fd.compress_vector;
                
        get_witness(fd2,temp_v,size/(D_train.data.size()));
        for(int i = 0; i < size; i++){
            v[i] = temp_v[2*i]*compress_vector[0] + temp_v[2*i+1]*compress_vector[1] + compress_vector[2];     
        }
        fd.pos += size;
    }
    else if(fd.name == "compressed_read_write"){
        stream_descriptor fd2;

        fd2.pos = fd.pos/(D_train.data.size());
        fd2.name = "read_write_transcript";
        vector<int> temp_v;
        vector<F> cache1,cache2,cache3,cache4,compress_vector = fd.compress_vector;
        
        for(int i = 0; i < 128; i++)cache1.push_back(F(i)*fd.compress_vector[0]);
        for(int i = 0; i < D_train.data.size(); i++)cache2.push_back(F(i)*fd.compress_vector[1]);
        for(int i = 0; i < bin_size; i++)cache3.push_back(F(i)*fd.compress_vector[2]);
        for(int i = 0; i < 2; i++)cache4.push_back(F(i)*fd.compress_vector[3]);
        
        
        for(int j = 0; j < 8; j++){
            
            get_witness_forest_int(fd2,temp_v,size/(8*D_train.data.size()));
            for(int i = 0; i < size/8; i++){
                v[j*(size/8) + i] = one + cache1[temp_v[i*8]]+cache2[temp_v[i*8+1]]+cache3[temp_v[i*8+2]]+cache4[temp_v[i*8+3]] + F(temp_v[i*8+4])*compress_vector[4];
                //for(int k = 0; k < 5; k++){
                //    v[j*(size/8) + i] += temp_v[i*8 + k]*compress_vector[k];
                //}
                //v[i] = temp_v[2*i]*compress_vector[0] + temp_v[2*i+1]*compress_vector[1] + compress_vector[2];     
            }
        }
        
        fd.pos += size;
    }else if(fd.name == "compressed_final_hist"){
        
        int stream_size = forest.size()*forest[0].size()*2*bin_size*D_train.data.size();
        int hist_size = stream_size/forest.size();
        
        if(fd.pos >= stream_size){
            for(int i = 0; i < size; i++){
                v[i] = one;
            }
            fd.pos += size;
            return 0;
        }
            
        int counter = 0;
            
        vector<F> cache1,cache2,cache3;
        for(int i = 0; i < forest[0].size(); i++)cache1.push_back(F(i)*fd.compress_vector[0]);
        for(int i = 0; i < D_train.data.size(); i++)cache2.push_back(F(i)*fd.compress_vector[1]);
        for(int i = 0; i < bin_size; i++)cache3.push_back(F(i)*fd.compress_vector[2]);
        // Yet another example of cursed/cancerous code sorryy
        int flag = 0;
        int pos_counter = 0;
        int data_read = 0;
        while(true){
          
            if(fd.pos%hist_size == 0){
                compute_histogram(fd.pos/hist_size);
            }
            
            for(int i = 0; i < histograms.size(); i++){
                for(int j = 0; j < histograms[0].size(); j++){
                    for(int l = 0; l < histograms[0][0][0].size(); l++){
                        if(pos_counter < fd.pos%hist_size){
                            pos_counter++;
                            continue;
                        }
                        if(counter == size){
                            fd.pos += data_read;
                            //exit(-1);
                            return 0;
                        }
                            
                        v[counter] = cache1[i] + cache2[j] + cache3[l] + histograms[i][j][0][l]*fd.compress_vector[4] + one;
                                
                        v[counter+1] = cache1[i] + cache2[j] + cache3[l] + fd.compress_vector[3] +  
                            histograms[i][j][1][l]*fd.compress_vector[4] + one;
                        counter+=2;
                        data_read+=2;
                    }
                }
            }
            fd.pos += data_read;
            data_read = 0;
            if(flag)break;
            if(fd.pos == stream_size)break;
        }
        if(counter < size){
            for(int i = counter; i < size; i++){
                v[i] = one;
                fd.pos++;
            }
        }
        
           
    }
    else{
        printf("Invalid stream, exiting \n");
        exit(-1);
    }
    return 0;
}


void generate_inference_layers(stream_descriptor &fd ,vector<F> &v,int size){
    stream_descriptor fd2,fd3;
    F two = one + F(2);
    if(fd.name == "inference_layer1" ||fd.name == "inference_layer3"){
        fd2.pos = fd.pos;fd2.name = "permuted_input";
        fd3.pos = fd.pos; fd3.name = "path";
        vector<F> perm,path;
        int counter = 0;
        int N = 0;
        //printf("%d \n", fd.pos);
        if(fd.pos >= D_train.data[0].size()){
            for(int i = 0; i < size; i++){
                v[i] = zero;
            }
            return;
        }
        while(true){
            N = get_witness(fd2,perm,64);
            get_witness(fd3,path,64);
            
            int col_size = path.size()/N;
            for(int i = 0; i < N; i++){
                for(int j = fd.pos_j; j < max_depth; j++){
                    if(fd.name == "inference_layer1"){
                        v[counter] = perm[i*2*D_train.data.size() + 2*j + 1] - path[i*col_size + 4*j];
                    }else if(fd.name == "inference_layer3"){
                        v[counter] =  ( one + path[i*col_size + 4*j + 2])*(perm[i*2*D_train.data.size() + 2*j + 1] - path[i*col_size + 4*j]);
                    }
                    counter++;
                    if(counter == size){
                        fd.pos += i;
                        fd.pos_j = j+1;//+1;
                        return;
                    }
                }
                fd.pos_j = 0;
            }
            fd.pos += N;
            if(N < 64 || fd2.pos == D_train.data[0].size()){
                break;
            }
        }

        //printf("EOF %d ,%d,%d\n", counter,fd.pos,N);
        for(int i = counter; i < size; i++){
            v[i] = zero;
        }
    }
    else if(fd.name == "inference_layer2" || fd.name == "inference_layer4"){
        fd2.pos = fd.pos;fd2.name = "path";
        vector<F> perm,path;
        int counter = 0;
        int N = 0;
        if(fd.pos >= D_train.data[0].size()){
            for(int i = 0; i < size; i++){
                if(fd.name == "inference_layer2"){
                    v[i] =  one;
                }else if(fd.name == "inference_layer4"){
                    v[i] = -one;
                }
            }
            return;
        }
        while(true){
            N = get_witness(fd2,path,64);
            int col_size = path.size()/N;
           
            for(int i = 0; i < N; i++){
                for(int j = fd.pos_j; j < max_depth; j++){
                    if(fd.name == "inference_layer2"){
                        v[counter] =  one + path[i*col_size + 4*j + 2];
                    }else if(fd.name == "inference_layer4"){
                        v[counter] = -one + two*path[i*col_size + 4*j + 2];
                    }
                    counter++;
                    if(counter == size){
                        fd.pos += i;
                        fd.pos_j = j+1;
                        return;
                    }
                }
                fd.pos_j = 0;
            }
            fd.pos += N;
            if(N < 64 || fd2.pos == D_train.data[0].size()){
                break;
            }
            
        }
        
        for(int i = counter; i < size; i++){
            if(fd.name == "inference_layer2"){
                v[i] =  one;
            }else if(fd.name == "inference_layer4"){
                v[i] = -one;
            } 
          
        } 
        //printf("EOF %d \n", counter);
           
    }else{
        printf("Invalid stream %s\n",fd.name.c_str());
        exit(-1);
    }

}

int get_test_data(stream_descriptor &fd, vector<F> &v, int size){
    if(fd.pos >= fd.size){
        return -1;
    }
    F prod = one;
    for(int i = 0; i  < 4;i++){
        prod *= F(3323213);
    }
    int counter = 0;
    for(int i = fd.pos; i < fd.pos + size; i++){
        v[counter] = prod*F(i)*F(i) + one;
        counter++;
    }
    fd.pos += size;
    return 0;
}

void reset_stream(stream_descriptor &fd){
    fd.pos = 0; fd.pos_j = 0;fd.input_pos = 0;fd.input_pos_j = 0;
}


void read_stream_batch(stream_descriptor &fd, vector<vector<F>> &v, int size,int distance){
    
    if(fd.name == "test"){
        for(int i = 0; i < v.size(); i++){
            for(int j = 0; j < v[i].size(); j++){
                v[i][j] = F(1024*i + (j)%4);
            }
        }
    }
    else if(fd.name == "mul_tree"){
        stream_descriptor input_fd;
        input_fd.pos = fd.input_pos;input_fd.size = fd.input_size;
        input_fd.pos_j = fd.input_pos_j; input_fd.data_size = fd.input_data_size;
        input_fd.name = fd.input_name;
        input_fd.compress_vector = fd.compress_vector;
        //printf("%d\n",input_fd.compress_vector.size());
        generate_mul_tree_batch(input_fd,v,size,fd.layer,distance);
        fd.input_pos = input_fd.pos;
    }    
}

void read_stream(stream_descriptor &fd, vector<F> &v, int size){
        
    clock_t t1,t2;
    t1 = clock();
    if(fd.name == "permuted_input" || fd.name == "input"){
        int read_size = size/(2*D_train.data.size());
        get_witness(fd,v,read_size);
    }else if(fd.name == "path" || fd.name == "path_transpose" ){
        int read_size = size/(fd.col_size);
        get_witness(fd,v,read_size);
    }else if(fd.name == "path_aux" || fd.name == "input_aux" || fd.name == "path_aux_transpose"){
        int read_size = size/2;
        get_witness(fd,v,read_size);
    }else if(fd.name == "bit_vector" || fd.name == "diff"){
        if(fd.pos >= D_train.data[0].size()){
            for(int i = 0; i < size; i++){
                v[i] = zero;
            }           
        }
        int status = get_witness(fd,v,size);
      
        if(status == -1){
      
            for(int i = v.size(); i < size; i++){
                v.push_back(zero);
            }
      
            
        }
        if(v.size() < size){
      
            v.resize(size,zero);
        }
    }else if(fd.name == "final_hist" || fd.name == "node_hist" || fd.name == "witness_hist" || fd.name == "out_hist"){
        get_witness(fd,v,size);    
    }else if(fd.name == "compressed_input" || fd.name == "compressed_path" || fd.name == "compressed_read_write" || 
    fd.name == "compressed_input_forest" || fd.name == "compressed_perm_forest" || fd.name == "compressed_pairs" || fd.name == "compressed_final_hist"){
        get_compressed_data(fd,v,size);
    }else if(fd.name == "inference_layer1" || fd.name == "inference_layer2" || fd.name == "inference_layer3" ||
    fd.name == "inference_layer4"){
        generate_inference_layers(fd,v,size);
    }else if(fd.name == "histogram_counter"){
        int read_size = size/D_train.data.size();
        get_witness(fd,v,read_size);
    }
    else if(fd.name == "read_transcript" || fd.name == "write_transcript" || fd.name == "read_write_transcript"){
        int read_size = size/(8*D_train.data.size()); 
        get_witness(fd,v,read_size);
    }else if(fd.name == "read_table" || fd.name == "write_table" || fd.name == "write_table" || fd.name == "compressed_lookup_read" 
    || fd.name == "compressed_lookup_write" || fd.name == "compressed_lookup_read_write" || fd.name == "indexes"){
        int read_size = size;
        get_witness_lookup(fd,v,read_size);
    }
    else if(fd.name == "divisors" || fd.name == "N" || fd.name == "dividents" || fd.name == "quotients" || fd.name == "remainders" ||
    fd.name == "inverses" || fd.name == "ginis" || fd.name == "gini_input_1" || fd.name == "gini_input_2" || fd.name == "N_sum" || fd.name == "pairwise_prod" || fd.name == "square_N"
    || fd.name == "cond" || fd.name == "cond_inv" || fd.name == "divisors_quot" || fd.name == "sub_ginis" || fd.name == "gini_input"){
        get_witness_split(fd,v,size);
    }else if(fd.name == "sub_ginis_bits"){
        get_witness_split(fd,v,size/32);
    }else if(fd.name == "remainders_bits"){
        get_witness_split(fd,v,size/64);
    }
    else if(fd.name == "quotient_bits"){
        get_witness_bagging(fd,v,size/256);
    }

    else if(fd.name == "randomness" || fd.name == "pairs" || fd.name == "randomness_remainder" || fd.name == "randomness_quotient"
    || fd.name == "s1" || fd.name == "s2"){
        get_witness_bagging(fd,v,size);
    }
    else if(fd.name == "mul_tree"){
        stream_descriptor input_fd;
        input_fd.pos = fd.input_pos;input_fd.size = fd.input_size;
        input_fd.pos_j = fd.input_pos_j; input_fd.data_size = fd.input_data_size;
        input_fd.name = fd.input_name;
        input_fd.compress_vector = fd.compress_vector;
        //printf("%d\n",input_fd.compress_vector.size());
        generate_mul_tree(input_fd,v,size,fd.layer);
        fd.input_pos = input_fd.pos;
    }else if(fd.name == "test"|| fd.name == "test2"){
        get_test_data(fd,v,size);
    }else if(fd.name == "test_inv"|| fd.name == "test2_inv"){
        get_test_data(fd,v,size);
        for(int i = 0; i < v.size(); i++){
            v[i].inv(v[i],v[i]);
        }
    }else if(fd.name == "sumcheck_test"){
        F num = F(1232113)*F(2122)*F(3123);
        for(int i = 0; i < v.size(); i++){
            v[i] = num + i;
        }
    }
    else{
        printf("Invalid stream\n");
        exit(-1);
    }
    t2 = clock();
    stream_access_time += (float)(t2-t1)/(float)CLOCKS_PER_SEC;
}

int get_chunk(stream_descriptor &fd, vector<F> &v, int size){
    //printf("%s\n",fd.name.c_str());
    if(fd.name == "compressed_input" || fd.name == "compressed_path" || fd.name == "compressed_read_write" ||
     fd.name == "compressed_input_forest" || fd.name == "compressed_perm_forest" || fd.name  == "compressed_pairs" || fd.name == "compressed_final_hist"){
        return get_compressed_data(fd,v,size);
    }else if(fd.name == "compressed_lookup_read" 
    || fd.name == "compressed_lookup_write" || fd.name == "compressed_lookup_read_write"){
        return get_witness_lookup(fd,v,size);
    }else if(fd.name == "sub_ginis"){
        return get_witness_split(fd, v, size);
    }
    else if(fd.name == "test"){
        return get_test_data(fd,v,size);
    }else{
        printf("Invalid stream for multiplication \n");
        exit(-1);
    }
    return -1;
}


void generate_mul_tree_batch(stream_descriptor &fd, vector<vector<F>> &v, int size, int layer, int distance){
    int counter = 0;
    int _seg = 1ULL<<(layer+1);
    vector<F> temp_v(size);
    while(true){
        if(get_chunk(fd,temp_v,size) == -1){
            printf("EOF\n");
            break;
        }
        for(int i = 0; i < size/(_seg); i++){
            v[0][counter] = one;
            for(int j = 0; j < _seg; j++){
                v[0][counter] *= temp_v[i*(_seg) + j];
            }
            counter++;
        }
        
        if(counter == size){
            //printf("OK\n");
            break;
        }
    }
    
    //printf("%d\n",distance);
    int offset = 1<<distance;
    
    //printf("%d,%d,%d\n",offset,v[0].size(),offset*v[1].size());
    for(int i = 1; i < v.size(); i++){
        for(int j = 0; j < v[i].size(); j++){
            v[i][j] = one;
            for(int k = 0; k < offset; k++){
                v[i][j] *= v[i-1][offset*j + k];
            }
        } 
    }
}


void generate_mul_tree(stream_descriptor &fd , vector<F> &v ,int &size,int layer){
    int _seg = 1ULL<<(layer+1);
    if(layer+1 <= (int)log2(size)){
        int counter = 0;
        vector<F> temp_v(size);
        while(true){
            if(get_chunk(fd,temp_v,size) == -1){
                printf("EOF\n");
                return;
            }
            for(int i = 0; i < size/(_seg); i++){
                v[counter] = one;
                for(int j = 0; j < _seg; j++){
                    v[counter] *= temp_v[i*(_seg) + j];
                }
                counter++;
            }
            if(counter == size){
                //printf("OK\n");
                return;
            }
        }
    }else{
        int counter = 0;
        //size = fd.size/size;
        vector<F> temp_v(size);
        while(true){
            if(get_chunk(fd,temp_v,size) == -1){
                size = counter;
                return;
            }
            v[counter] = one;
            for(int i = 0; i < size; i++){
                v[counter] *= temp_v[i];
            }
            counter++;
        }
    }
}

void generate_mul_tree_parallel(stream_descriptor &fd , vector<F> &v ,int &size, int max_depth,int layer){
    if(layer > max_depth){
        printf("Error, choose smaller depth\n");
        exit(-1);
    }
    

    int counter = 0;
    vector<F> temp_v(size);
    int offset = 1ULL<<(layer+1);
    while(true){
        if(get_chunk(fd,temp_v,size) == -1){
            printf("EOF\n");
            return;
        }
        for(int i = 0; i < size/offset; i++){
            v[counter] = one;
            for(int j = 0; j < offset; j++){
                v[counter] *= temp_v[i*offset + j];
            }
            counter++;
        }
        if(counter == size){
            //printf("OK\n");
            return;
        }
    }
}

