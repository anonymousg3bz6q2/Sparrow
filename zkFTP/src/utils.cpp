//
// Created by 69029 on 6/23/2021.
//


#include "utils.hpp"
#include "config_pc.hpp"
#include "GKR.h"
#include "mimc.h"
#include <errno.h> 
#include "witness_stream.h"
#include "Inference.h"
#include <chrono>
using namespace std::chrono;

extern double proving_time;
extern unsigned long int mul_counter;
extern int threads;
extern size_t MAX_CHUNCK;
extern size_t data_read;
extern double serialization_time;
extern double read_time;
extern double clear_cache_time;
extern vector<vector<vector<Node>>> _forest;
extern vector<vector<vector<vector<int>>>> histograms;
extern vector<vector<vector<vector<int>>>> histograms_forest;
extern vector<vector<vector<int>>> node_histogram;
extern vector<vector<vector<vector<int>>>> histograms_forest;
extern vector<vector<vector<F>>> forest;
extern vector<vector<int>> witness_hist,out_hist;
extern vector<unsigned long long int> gini_input;
extern int gini_input_pos;
extern int bin_size;
extern vector<vector<F>> tree;
extern vector<vector<vector<F>>> forest;
extern Dataset D_train;
extern F one,zero;
vector<F> powers_two;
extern int total_nodes;
extern int attr;
extern int domain;
extern int quantization_level;
extern int max_depth;
extern int bin_size;


void compute_histogram(int idx){
    if(histograms.size() == 0){
        histograms.resize(forest[idx].size());
        for(int i = 0; i < forest[idx].size(); i++){
            histograms[i].resize(D_train.data.size());
            for(int j = 0; j < D_train.data.size(); j++){
                histograms[i][j].resize(2);
                histograms[i][j][0].resize(bin_size,0);
                histograms[i][j][1].resize(bin_size,0);
            }
        }
    }
    for(int i = 0; i < forest[idx].size(); i++){
		//histograms[i].resize(D_train.data.size());
		for(int j = 0; j < D_train.data.size(); j++){
            for(int k = 0; k < histograms[i][j].size(); k++){
                for(int l = 0; l < histograms[i][j][k].size(); l++){
                    histograms[i][j][k][l] = 0;
                }
            }
		}
	}
    vector<int> x(D_train.type.size());
    for(int i = 0; i < D_train.data[0].size(); i++){
        x.clear();
        int y;
		for(int k = 0; k < D_train.type.size(); k++){
			x[k] = (D_train.data[k][i]);
		}
		y = D_train.label[i];
        
        int pos = get_pos(_forest[idx],x,y);
        for(int j = 0; j < D_train.data.size(); j++){
            histograms[pos][j][y][D_train.data[j][i]]++; 
        }
    }    
}

void add_histograms(vector<vector<int>> &hist1, vector<vector<int>> &hist2){
	vector<vector<int>> hist(hist1.size());
	for(int i = 0; i < hist.size(); i++){
		hist[i].resize(hist1[0].size());
		for(int j = 0; j < hist[i].size(); j++){
			hist[i][j] = hist1[i][j] + hist2[i][j];
		}
	}
	node_histogram.push_back(hist);
}

void compute_node_histogram(int idx){
    node_histogram.clear();
    compute_histogram(idx);
    vector<vector<vector<int>>> buff;
    vector<int> node_coeff;
    vector<vector<int>> leaf_matrix(max_depth+1);
    vector<vector<int>> leaf_index_matrix(max_depth+1);
    vector<vector<int>> leaf_coeff_int(forest[idx].size());
    vector<vector<Node>> tree = _forest[idx];

    for(int i = 0; i <= max_depth; i++){
        leaf_matrix[i].resize(1<<i,-1);
        leaf_index_matrix[i].resize(1<<i,-1);
    }
    for(int i = 0; i < forest[idx].size(); i++){
        leaf_coeff_int[i].resize(2);
        leaf_coeff_int[i][0] = (tree[i][tree[i].size()-1].h);
		leaf_coeff_int[i][1] = (tree[i][tree[i].size()-1].pos);
			
        leaf_matrix[leaf_coeff_int[i][0]][leaf_coeff_int[i][1]] = 2;
		leaf_index_matrix[leaf_coeff_int[i][0]][leaf_coeff_int[i][1]] = i;

    }
    vector<vector<int>> node_index_matrix(leaf_index_matrix.size());
	for(int i = 0; i < node_index_matrix.size(); i++){
		node_index_matrix[i].resize(leaf_index_matrix[i].size(),-1);
	}

    buff.resize(histograms.size());
    for(int i = 0; i < histograms.size(); i++){
        buff[i].resize(histograms[i].size());
        for(int j = 0; j < buff[i].size(); j++){
            buff[i][j].resize(2*bin_size);
            for(int k = 0; k < histograms[i][j][0].size(); k++){
                buff[i][j][2*k] = histograms[i][j][0][k];
                buff[i][j][2*k+1] = histograms[i][j][1][k];
            }
        }
    }

    vector<vector<int>> hist1,hist2;
	for(int i = leaf_matrix.size()-1; i > 0; i--){
		for(int j = 0; j < leaf_matrix[i].size(); j+=2){
			if(leaf_matrix[i][j] != -1){
				leaf_matrix[i-1][j/2] = 1;
				node_coeff.push_back((i-1));
				node_coeff.push_back((j/2));
					
				node_index_matrix[i-1][j/2] = node_coeff.size()/2-1; 
            	if(leaf_index_matrix[i][j] != -1){
					hist1 = buff[leaf_index_matrix[i][j]];
				}else{
					hist1 = node_histogram[node_index_matrix[i][j]];
				}
				if(leaf_index_matrix[i][j+1] != -1){
					hist2 = buff[leaf_index_matrix[i][j+1]];		
				}else{
					hist2 = node_histogram[node_index_matrix[i][j+1]];				
				}
				add_histograms(hist1,hist2);
			}
		}
	}
}


vector<vector<int>> serialize_hist(int idx){
    vector<vector<int>> buff(histograms[idx].size());
    for(int i = 0; i < buff.size(); i++){
        buff[i].resize(2*bin_size);
        for(int j = 0; j  < bin_size; j++){
            buff[i][2*j] = histograms[idx][i][0][j];
            buff[i][2*j+1] = histograms[idx][i][1][j];
        }
    }
    return buff;
}

void compute_witness_hist(int idx){
    
    
    witness_hist.clear();
    vector<F> witness_coeff;
    vector<vector<int>> leaf_matrix(max_depth+1);
    vector<vector<int>> leaf_index_matrix(max_depth+1);
    vector<vector<int>> leaf_coeff_int(forest[idx].size());
    vector<vector<Node>> tree = _forest[idx];
    vector<vector<int>> H;
    vector<int> node_coeff;
    vector<int> H_v;
	compute_node_histogram(idx);
    for(int i = 0; i <= max_depth; i++){
        leaf_matrix[i].resize(1<<i,-1);
        leaf_index_matrix[i].resize(1<<i,-1);
    }
    for(int i = 0; i < forest[idx].size(); i++){
        leaf_coeff_int[i].resize(2);
        leaf_coeff_int[i][0] = (tree[i][tree[i].size()-1].h);
		leaf_coeff_int[i][1] = (tree[i][tree[i].size()-1].pos);
			
        leaf_matrix[leaf_coeff_int[i][0]][leaf_coeff_int[i][1]] = 2;
		leaf_index_matrix[leaf_coeff_int[i][0]][leaf_coeff_int[i][1]] = i;

    }
    vector<vector<int>> node_index_matrix(leaf_index_matrix.size());
	for(int i = 0; i < node_index_matrix.size(); i++){
		node_index_matrix[i].resize(leaf_index_matrix[i].size(),-1);
	}
    

    for(int i = leaf_matrix.size()-1; i > 0; i--){
		for(int j = 0; j < leaf_matrix[i].size(); j+=2){
			if(leaf_matrix[i][j] != -1){
				leaf_matrix[i-1][j/2] = 1;
				node_coeff.push_back((i-1));
				node_coeff.push_back((j/2));
					
				node_index_matrix[i-1][j/2] = node_coeff.size()/2-1; 
			}
		}
	}
    for(int i = leaf_matrix.size()-1; i > 0; i--){
		for(int j = 0; j < leaf_matrix[i].size(); j+=2){
			
			if(leaf_matrix[i][j] != -1){
				H_v.clear();
					
             	if(leaf_index_matrix[i][j] != -1){
					H = serialize_hist(leaf_index_matrix[i][j]);//histograms[leaf_index_matrix[i][j]];
				}else{
                	H = node_histogram[node_index_matrix[i][j]];
				}
				for(int k = 0; k < H.size(); k++){
					H_v.insert(H_v.end(),H[k].begin(),H[k].end());
				}
				witness_hist.push_back(H_v);
				H_v.clear();
				if(leaf_index_matrix[i][j+1] != -1){
					H = serialize_hist(leaf_index_matrix[i][j+1]);
				}else{
                	
					H = node_histogram[node_index_matrix[i][j+1]];
				}
				for(int k = 0; k < H.size(); k++){
					H_v.insert(H_v.end(),H[k].begin(),H[k].end());
				}
				
				witness_hist.push_back(H_v);
			}
		}
	}
    for(int i = 0; i < H.size(); i++){
       vector<int>().swap(H[i]);
    }
    vector<vector<int>>().swap(H);
    vector<int>().swap(H_v);
    
}

void compute_out_hist(int idx){
    out_hist.clear();
    
    		
    compute_witness_hist(idx);
    
    out_hist.resize(witness_hist.size()/2);	
	vector<int> hist_aggr;
	for(int i = 0; i < out_hist.size(); i++){
		//vector<int> hist_aggr;
	    hist_aggr.clear();

		hist_aggr.resize(witness_hist[i].size());
        for(int j = 0; j < hist_aggr.size(); j++){
			hist_aggr[j] = witness_hist[2*i][j] + witness_hist[2*i+1][j];
		}
		out_hist[i] = hist_aggr;
    }
    vector<int>().swap(hist_aggr);
			
}

void compute_ginis(int idx){
    int nodes = forest[0].size() -1;
    if(idx >= forest.size()){
        gini_input.clear();
        gini_input.resize(nodes*attr*4*bin_size,0);
        return;        
    }
    compute_node_histogram(idx);
    gini_input.clear();
    gini_input.resize(nodes*attr*4*bin_size);
    vector<vector<vector<unsigned long long int>>> sums(nodes);
	
    for(int i = 0; i < nodes; i++){
		sums[i].resize(attr);
		for(int j = 0; j < attr; j++){
			sums[i][j].resize(2,0);
			for(int k = 0; k < node_histogram[i][j].size(); k+=2){
				sums[i][j][0] += node_histogram[i][j][k];
				sums[i][j][1] += node_histogram[i][j][k+1];
			}
		}
	}

    for(int i = 0; i < nodes; i++){
		for(int j = 0; j < attr; j++){
			gini_input[ i*attr*4*bin_size + j*4*bin_size] = node_histogram[i][j][0];
			gini_input[ i*attr*4*bin_size + j*4*bin_size+1] = node_histogram[i][j][1];
			gini_input[ i*attr*4*bin_size + j*4*bin_size+2] = sums[i][j][0] - node_histogram[ i][j][0];
			gini_input[ i*attr*4*bin_size + j*4*bin_size+3] = sums[i][j][1] - node_histogram[ i][j][1];
				
            for(int k = 1; k < bin_size; k++){
				//gini_input[ i*attr*4*bin_size + j*4*bin_size+2*k] = node_histogram[i][j][0];
				//gini_input[ i*attr*4*bin_size + j*4*bin_size+1+2*k+1] = node_histogram[ i][j][1];
				//gini_input[ i*attr*4*bin_size + j*4*bin_size+2+2*k+2] = sums[i][j][0] - node_histogram[ i][j][0];
				//gini_input[ i*attr*4*bin_size + j*4*bin_size+3+2*k+3] = sums[i][j][1] - node_histogram[ i][j][1];
                
                gini_input[i*attr*4*bin_size + j*4*bin_size + 4*k] = node_histogram[i][j][2*k] + gini_input[i*attr*4*bin_size + j*4*bin_size + 4*(k-1)];
				gini_input[i*attr*4*bin_size + j*4*bin_size + 4*k+1] = node_histogram[i][j][2*k+1] + gini_input[i*attr*4*bin_size + j*4*bin_size + 4*(k-1) + 1];
				gini_input[i*attr*4*bin_size + j*4*bin_size + 4*k+2] = gini_input[i*attr*4*bin_size + j*4*bin_size + 4*(k-1) + 2] - node_histogram[i][j][2*k];
				gini_input[i*attr*4*bin_size + j*4*bin_size + 4*k+3] = gini_input[i*attr*4*bin_size + j*4*bin_size + 4*(k-1) + 3] - node_histogram[i][j][2*k+1];				
			
			}
		}
	}
    gini_input_pos = idx;
}

void compute_compressed_histograms(vector<vector<F>> &compressed_leaf_hist,vector<vector<F>> &compressed_node,vector<vector<F>> &compressed_witness,
vector<vector<F>> &compressed_out,vector<F> compress_vector){
    
    compressed_leaf_hist.resize(forest.size());
    compressed_node.resize(forest.size());
    compressed_witness.resize(forest.size());
    compressed_out.resize(forest.size());
    

    for(int i = 0; i < forest.size(); i++){
        compute_histogram(i);
        compressed_leaf_hist[i].resize(histograms.size(),F(0));
        for(int j = 0; j < histograms.size(); j++){
            int counter = 0;
            for(int k = 0; k < histograms[j].size(); k++){
                for(int l = 0; l < bin_size; l++){
                    compressed_leaf_hist[i][j] += compress_vector[counter]*histograms[j][k][0][l];
                    counter++;
                    compressed_leaf_hist[i][j] += compress_vector[counter]*histograms[j][k][1][l];
                    counter++;
                }
            }
        }
    }
    for(int i = 0; i < forest.size(); i++){
        compute_node_histogram(i);
        compressed_node[i].resize(node_histogram.size(),F(0));
        for(int j = 0; j < node_histogram.size(); j++){
            int counter = 0;
            for(int k = 0; k < node_histogram[j].size(); k++){
                for(int l = 0; l < node_histogram[j][k].size(); l++){
                    compressed_leaf_hist[i][j] += compress_vector[counter]*node_histogram[j][k][l];
                    counter++;
                }
            }
        }
    }
    for(int i = 0; i < forest.size(); i++){
        compute_witness_hist(i);
        compressed_witness[i].resize(witness_hist.size(),F(0));
        for(int j = 0; j < witness_hist.size(); j++){
            for(int k = 0; k < witness_hist[j].size(); k++){
                compressed_witness[i][j] += compress_vector[k]*witness_hist[j][k];
            }
        }
    }

    for(int i = 0; i < forest.size(); i++){
        compute_out_hist(i);
        compressed_out[i].resize(witness_hist.size()/2,F(0));
        for(int j = 0; j < witness_hist.size()/2; j++){
            for(int k = 0; k < witness_hist[j].size(); k++){
                compressed_out[i][j] += compress_vector[k]*out_hist[j][k];
			}
        }
    }

}

void reset_histograms_forest(){
    histograms_forest.clear();
    histograms_forest.resize(forest[0].size());
	for(int i = 0; i < forest[0].size(); i++){
        histograms_forest[i].resize(D_train.data.size());
        for(int l = 0; l < histograms_forest[i].size(); l++){
            histograms_forest[i][l].resize(2);
            histograms_forest[i][l][0].resize(bin_size,0);
            histograms_forest[i][l][1].resize(bin_size,0);
		    //for(int j = 0; j < D_train.data.size(); j++){
            //    histograms_forest[i][l][j].resize(2);
            //    histograms_forest[i][l][j][0].resize(bin_size,0);
            //    histograms_forest[i][l][j][1].resize(bin_size,0);
		    //}  
        }
	}
}

void reset_histograms(){
    histograms.clear();
    
    
    histograms.resize(tree.size());
	for(int i = 0; i < tree.size(); i++){
		histograms[i].resize(D_train.data.size());
		for(int j = 0; j < D_train.data.size(); j++){
			histograms[i][j].resize(2);
			histograms[i][j][0].resize(bin_size,0);
			histograms[i][j][1].resize(bin_size,0);
		}
	}
}

size_t normalize_number(size_t num){
	if(1<<((int)log2(num)) != num){
		return 1<<(((int)log2(num)) +1);
	}
	return num;
}

F chain_hash_verify(F previous_r, vector<F> values, vector<F> &x, vector<F> &y){
    for(int i  = 0; i < values.size(); i++){
        x.push_back(previous_r);
        x.push_back(values[i]);
        previous_r = mimc_hash(previous_r,values[i]);
        y.push_back(previous_r);
    }
    return previous_r;
}


F chain_hash(F previous_r, vector<F> values){
    for(int i  = 0; i < values.size(); i++){
        previous_r = mimc_hash(previous_r,values[i]);
    }
    return previous_r;
}



void write_file_bytes(vector<F> arr, int no_bytes, FILE *fp){
    fseek(fp,0,SEEK_END);
    
    int maxSize = arr[0].maxSize;
    if(no_bytes == 4){
        int *buff = (int *)malloc(arr.size()*sizeof(int));
        for(int i = 0; i < arr.size(); i++){
            buff[i] = (int)arr[i].v_[0]; 
        }
        fwrite(buff,1,no_bytes*arr.size(),fp);
        free(buff);

    }else{
        uint8_t *buff = (uint8_t *)malloc(arr.size()*sizeof(uint8_t));
        for(int i = 0; i < arr.size(); i++){
            buff[i] = (uint8_t)arr[i].v_[0];    
        }
        fwrite(buff,1,no_bytes*arr.size(),fp);
        free(buff);
    }
}



void write_file(vector<F> arr, FILE *fp, int size){
    fseek(fp,0,SEEK_END);

    if(size == 0){
        size = arr.size();
    }    

    int maxSize = arr[0].maxSize;
   
    long long int *buff = (long long int *)malloc(size*maxSize*sizeof(long long int));
    for(int i = 0; i < size; i++){
        for(int j = 0; j < maxSize; j++){
            buff[i*maxSize + j] = arr[i].v_[j];
        }
    }
    fwrite(buff,1,32*size,fp);
    free(buff);
}


void write_pp(vector<G1> pp, FILE *fp){
    char element[32];
    char *buff = (char *)malloc(32*pp.size());

    for(int i = 0; i < pp.size(); i++){
        pp[i].serialize(element,32);
        for(int j = 0; j < 32; j++){
            buff[32*i + j] = element[j];
        }
    }

    fwrite(buff,1,32*pp.size(),fp);
    free(buff);

}

void read_pp(int fp, vector<G1> &pp, int segment_size){
    uint8_t *buff;
    uint8_t element[32];
    buff = (uint8_t *)malloc(pp.size()*32);
    size_t to_read = (unsigned long int)32*(unsigned long int)segment_size;
    size_t counter = 0;
    size_t size;
    while(to_read != 0){
        size = read(fp,buff+counter,to_read);
        if(size == -1){
            printf("Error opening file: %s\n", strerror(errno)); 
        }
        to_read -= size;
        counter += size;
    }
    for(int i = 0; i < segment_size; i++){
        pp[i].deserialize(buff+i*32,32);
    }
    free(buff);
}

void read_chunk_bytes(int fp,vector<F> &arr, int no_bytes, int segment_size){
    //uint8_t *buff;
    //uint8_t element[32];
    //buff = (uint8_t *)malloc(arr.size()*32);
    int maxSize = arr[0].maxSize;
    
    if(no_bytes == 4){

        int *buff = (int *)malloc(arr.size()*sizeof(int));

        /*
        Total : 44.230626
Deserialize : 1.749431
Scan : 18.637066
Op time : 23.844129 
Clear Cache : 519.228755
        auto s = chrono::high_resolution_clock::now();
        system("sudo hdparm -A 0 /dev/sda >/dev/null 2>&1");
        system("echo 3 | sudo tee /proc/sys/vm/drop_caches >/dev/null 2>&1");
        auto e = chrono::high_resolution_clock::now();
        clear_cache_time += chrono::duration_cast<chrono::nanoseconds>(e - s).count()*(1e-9);
        */
        //printf("OK %lf\n",clear_cache_time);

        auto t1 = chrono::high_resolution_clock::now();
        size_t to_read = (unsigned long int)no_bytes*(unsigned long int)segment_size;
        size_t counter = 0;
        size_t size;
        data_read += to_read;
        while(to_read != 0){
            size = read(fp,buff+counter,to_read);
            if(size == -1 || size == 0){
                printf("Error opening file: %s\n", strerror(errno));
                exit(-1); 
            }
            to_read -= size;
            counter += size;
        }
        auto t2 = chrono::high_resolution_clock::now();
        
        read_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
        //printf("Read time : %lf\n",read_time);
        if(counter < (unsigned long int)no_bytes*(unsigned long int)segment_size){
            printf("%lld,%lld\n",size,(unsigned long int)no_bytes*(unsigned long int)segment_size );
            printf("Error in read\n");
            exit(-1);
        }
        

        F num;
        bool v[1];
        
        t1 = chrono::high_resolution_clock::now();

        for(int i = 0; i < segment_size; i++){
            arr[i].v_[0] = buff[i];
            //arr[i].deserialize(buff+i*32,32);
            //arr[i] = F(0);
        }
        t2 = chrono::high_resolution_clock::now();
        

        serialization_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
        free(buff);
    }else{
        uint8_t *buff = (uint8_t *)malloc(arr.size()*sizeof(uint8_t));

        //time_t t1,t2;

        //auto t1 = chrono::high_resolution_clock::now();
        //system("sudo hdparm -A 0 /dev/sda >/dev/null 2>&1");
        //system("echo 3 | sudo tee /proc/sys/vm/drop_caches >/dev/null 2>&1");
        //auto t2 = chrono::high_resolution_clock::now();
        //clear_cache_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
        //printf("OK %lf\n",clear_cache_time);

        auto t1 = chrono::high_resolution_clock::now();
        size_t to_read = (unsigned long int)no_bytes*(unsigned long int)segment_size;
        size_t counter = 0;
        size_t size;
        data_read += to_read;
        while(to_read != 0){
            size = read(fp,buff+counter,to_read);
            if(size == -1){
                printf("Error opening file: %s\n", strerror(errno)); 
            }
            to_read -= size;
            counter += size;
        }
        auto t2 = chrono::high_resolution_clock::now();
        
        read_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
        //printf("Read time : %lf\n",read_time);
        if(counter < (unsigned long int)no_bytes*(unsigned long int)segment_size){
            printf("%lld,%lld\n",size,(unsigned long int)no_bytes*(unsigned long int)segment_size );
            printf("Error in read\n");
            exit(-1);
        }
        

        F num;
        bool v[1];
        
        t1 = chrono::high_resolution_clock::now();

        for(int i = 0; i < segment_size; i++){
            arr[i].v_[0] = buff[i];
            //arr[i].deserialize(buff+i*32,32);
            //arr[i] = F(0);
        }
        t2 = chrono::high_resolution_clock::now();
        

        serialization_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
        free(buff);
    }
}


void read_chunk(int fp,vector<F> &arr, int segment_size){
    //uint8_t *buff;
    //uint8_t element[32];
    //buff = (uint8_t *)malloc(arr.size()*32);
    int maxSize = arr[0].maxSize;
    long long int *buff = (long long int *)malloc(arr.size()*maxSize*sizeof(long long int));

    //time_t t1,t2;
    /*
    auto _t1 = chrono::high_resolution_clock::now();
    system("sudo hdparm -A 0 /dev/sda >/dev/null 2>&1");
    system("echo 3 | sudo tee /proc/sys/vm/drop_caches >/dev/null 2>&1");
    auto _t2 = chrono::high_resolution_clock::now();
    clear_cache_time += chrono::duration_cast<chrono::nanoseconds>(_t2 - _t1).count()*(1e-9);
    */
    
   
   

    auto t1 = chrono::high_resolution_clock::now();
    size_t to_read = (unsigned long int)32*(unsigned long int)segment_size;
    size_t counter = 0;
    size_t size;
    data_read += to_read;
    while(to_read != 0){
        size = read(fp,buff+counter,to_read);
        if(size == -1){
            printf("Error opening file: %s\n", strerror(errno));
            exit(-1); 
        }

        to_read -= size;
        counter += size;
    }
    auto t2 = chrono::high_resolution_clock::now();
    
    read_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    //printf("Read time : %lf\n",read_time);
    if(counter < (unsigned long int)32*(unsigned long int)segment_size){
        printf("%lld,%lld\n",size,(unsigned long int)32*(unsigned long int)segment_size );
        printf("Error in read\n");
        exit(-1);
    }
    

    F num;
    bool v[1];
    
    t1 = chrono::high_resolution_clock::now();

    for(int i = 0; i < segment_size; i++){
        for(int j = 0; j < maxSize; j++){
            arr[i].v_[j] = buff[i*maxSize + j];
        }
        //arr[i].deserialize(buff+i*32,32);
        //arr[i] = F(0);
    }
    t2 = chrono::high_resolution_clock::now();
    

    serialization_time += chrono::duration_cast<chrono::nanoseconds>(t2 - t1).count()*(1e-9);
    free(buff);
    
}

vector<F> generate_randomness_verify(int size, F seed,vector<F> &x,vector<F> &y){
    vector<F> r;
    
    F num = seed;
    for(int i = 0; i < size; i++){
        if(i > 0){
            x.push_back(num);
            x.push_back(F(i));
            num = mimc_hash(num,F(i));
            y.push_back(num);
        }else{
            x.push_back(seed);
            x.push_back(F(i));
            num = mimc_hash(seed,F(0));
            y.push_back(num);
        }
        r.push_back(num);
    }
    /*
    for(int i = 0; i < size; i++){
        F num = F(0);
        num.setByCSPRNG();
        r.push_back(num);
    }
    */
    return r;
}


vector<F> generate_randomness(int size, F seed){
    vector<F> r;
    
    F num = seed;
    for(int i = 0; i < size; i++){
        if(i > 0){
            num = mimc_hash(num,F(i));
        }else{
            num = mimc_hash(seed,F(0));
        }
        r.push_back(num);
    }
    /*
    for(int i = 0; i < size; i++){
        F num = F(0);
        num.setByCSPRNG();
        r.push_back(num);
    }
    */
    return r;
}


float proof_size(vector<struct proof> P){
    int counter = 0;
    for(int i = 0; i < P.size(); i++){
        if(P[i].type== 1){
            for(int j = 1; j < P[i].randomness.size(); j++){
                counter += P[i].randomness[j].size();
            }
        }else if(P[i].type == 2){
            counter += P[i].randomness[0].size();
            counter += P[i].randomness[1].size();
        }else if(P[i].type == 3){
            counter += P[i].randomness[0].size();
        }
        counter += P[i].q_poly.size()*3;
        counter += P[i].c_poly.size()*4;
        counter += P[i].vr.size();
        counter += P[i].gr.size();
        counter += P[i].liu_sum.size();
        for(int j = 0; j < P[i].sig.size(); j++){
            counter += P[i].sig[j].size();
        }
        for(int j = 0; j  < P[i].final_claims_v.size(); j++){
            counter += P[i].final_claims_v[j].size();
        }
    }
    return (float)(counter*32)/1024.0;
}



void initHalfTable(vector<F> &beta_f, vector<F> &beta_s, const vector<F>::const_iterator &r, const F &init, u64 first_half, u64 second_half) {
    beta_f.at(0) = init;
    beta_s.at(0) = F_ONE;

    for (u32 i = 0; i < first_half; ++i) {
        for (u32 j = 0; j < (1ULL << i); ++j) {
            auto tmp = beta_f.at(j) * r[i];
            beta_f.at(j | (1ULL << i)) = tmp;
            beta_f.at(j) = beta_f[j] - tmp;
        }
    }

    for (u32 i = 0; i < second_half; ++i) {
        for (u32 j = 0; j < (1ULL << i); ++j) {
            auto tmp = beta_s[j] * r[(i + first_half)];
            beta_s[j | (1ULL << i)] = tmp;
            beta_s[j] = beta_s[j] - tmp;
        }
    }
}

void initBetaTable(vector<F> &beta_g, u8 gLength, const vector<F>::const_iterator &r, const F &init) {
    if (gLength == -1) return;

    static vector<F> beta_f, beta_s;
    int first_half = gLength >> 1, second_half = gLength - first_half;
    u32 mask_fhalf = (1ULL << first_half) - 1;

    assert(beta_g.size() >= 1ULL << gLength);
    myResize(beta_f, 1ULL << first_half);
    myResize(beta_s, 1ULL << second_half);
    if (init != F_ZERO) {
        initHalfTable(beta_f, beta_s, r, init, first_half, second_half);
        for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g.at(i) = beta_f.at(i & mask_fhalf) * beta_s.at(i >> first_half);
    } else for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g.at(i) = F_ZERO;

    
}

void initBetaTable(vector<F> &beta_g, int gLength, const vector<F>::const_iterator &r_0,
                   const vector<F>::const_iterator &r_1, const F &alpha, const F &beta) {
    static vector<F> beta_f, beta_s;
    int first_half = gLength >> 1, second_half = gLength - first_half;
    u32 mask_fhalf = (1ULL << first_half) - 1;
    assert(beta_g.size() >= 1ULL << gLength);
    myResize(beta_f, 1ULL << first_half);
    myResize(beta_s, 1ULL << second_half);
    if (beta != F_ZERO) {
        initHalfTable(beta_f, beta_s, r_1, beta, first_half, second_half);
        for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g[i] = beta_f[i & mask_fhalf] * beta_s[i >> first_half];
    } else for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g[i] = F_ZERO;

    if (alpha == F_ZERO) return;
    initHalfTable(beta_f, beta_s, r_0, alpha, first_half, second_half);
    assert(beta_g.size() >= 1ULL << gLength);
    for (u32 i = 0; i < (1ULL << gLength); ++i)
        beta_g[i] = beta_g[i] + beta_f[i & mask_fhalf] * beta_s[i >> first_half];
}

F getRootOfUnit(int n) {
    F res = -F_ONE;
    if (!n) return F_ONE;
    while (--n) {
        bool b = F::squareRoot(res, res);
        assert(b);
    }
    return res;
}

vector<F> convert2vector(vector<vector<F>> &M){
    vector<F> V;
    for(int i = 0; i < M.size(); i++){
        for(int j = 0; j < M[i].size(); j++){
            V.push_back(M[i][j]);
        }
    }
    return V;
}

vector<F> tensor2vector(vector<vector<vector<vector<F>>>> M){
    vector<F> V;

    for(int i = 0; i < M.size(); i++){
        for(int j = 0; j < M[i].size(); j++){
            for(int k = 0; k < M[i][j].size(); k++){
                for(int l = 0; l < M[i][j][k].size(); l++){
                    V.push_back(M[i][j][k][l]);
                }
            }
        }
    }
    return V;
}
void _precompute_beta(F *B, F *temp_B,F rand, vector<F> &beta, int idx, int L){
    int size = L/threads;
    int pos = idx*size;
    if(beta.size()/2 == L){
        for(int j = pos; j < pos+size; j++){
            int num = j<<1;
            F temp = rand*temp_B[j];
            beta[num] = temp_B[j] - temp;
            beta[num+1] = temp;
            
        }
    }else{
        for(int j = pos; j < pos+size; j++){
            int num = j<<1;
            F temp = rand*temp_B[j];
            B[num] = temp_B[j] - temp;
            B[num+1] = temp;
            
        }

    }
}


void compute_binary(vector<F> r, vector<F> &B){
    B.resize(1<<r.size());
    int num;
    for(int i = 0; i < 1<<r.size(); i++){
        num = i;
        B[i] = F(1);
        for(int j = 0; j < r.size(); j++){
            if(num & 1 == 1){
                B[i] = B[i]*r[j];
            }
            //else{
            //    B[i] = B[i]*(F(1)-r[j]);
            //}
            num = num >> 1;
        }

    }
}


void compute_convolution(vector<vector<F>> Lv, vector<F> &B){
    int conv_size = 1;
	for(int i = 0; i < Lv.size(); i++){
		conv_size = conv_size*Lv[i].size();
		//printf("%d ", Lv[i].size());
	}
    F *_B = (F *)malloc((1)*sizeof(F));
    _B[0] = F(1);
    
	//printf("\n");
    B.resize(conv_size);
    int size = 1;
    for(int i = Lv.size()-1; i >= 0; i--){
        size *= Lv[i].size();
        F *temp_B = (F *)malloc(size*sizeof(F));
        if(i == 0){
            for(int j = 0; j < conv_size/Lv[i].size(); j++){
                for(int k = 0; k < Lv[i].size(); k++){
                    B[j* Lv[i].size() + k] = _B[j]*Lv[i][k];
                }
            }
        }else{
            for(int j = 0; j < size/Lv[i].size(); j++){
                for(int k = 0; k < Lv[i].size(); k++){
                    temp_B[j* Lv[i].size() + k] = _B[j]*Lv[i][k];
                }
            }
        }
        _B = temp_B;
    }
}

void precompute_beta(vector<F> r,vector<F> &B){
    
    B.resize(1<<r.size());
    F *_B = (F *)malloc((1)*sizeof(F));
    B[0] = F(1);
    _B[0] = F(1);
    
    
    for(int i = 0; i < r.size(); i++){
        
        F *temp_B = (F *)malloc((1<<(i+1))*sizeof(F));
        
        //vector<F> temp_B(1<<i);
        //for(int j = 0; j < (1<<i); j++){
        //    temp_B[j] = (_B[j]);
        //}
        if(threads == 1 || 1<<10 >= 1<<i){
            
            if(B.size()/2 == 1<<i){
                for(int j = 0; j < (1<<i); j++){
                    int num = j<<1;
                    //printf("%d\n",num);
                    F temp = r[r.size() - 1 -i]*_B[j];
                    B[num] = _B[j] - temp;
                    B[num+1] = temp;
                
                }
            }else{
                
                for(int j = 0; j < (1<<i); j++){
                    int num = j<<1;
                    //printf("%d\n",num);
                    F temp = r[r.size() - 1 -i]*_B[j];
                    temp_B[num] = _B[j] - temp;
                    temp_B[num+1] = temp;
                    
                    /*
                    B[num] = (1-r[r.size() - 1 -i])*temp_B[j];
                    B[num+1] = r[r.size() - 1 -i]*temp_B[j];
                    */
                }
            }
        }else{
            thread workers[threads];
            for(int j = 0; j < threads; j++){
                workers[j] = thread(&_precompute_beta,temp_B,_B,r[r.size() - 1 -i],ref(B),j,1<<i);
            }
            for(int j = 0; j < threads; j++){
                workers[j].join();
            }
        }
        free(_B);
        _B = temp_B;
    }
    free(_B);
    //return B;
}
void write_data(vector<F> data,char *filename){
    FILE *f;
    char buff[257];
    f = fopen(filename,"w+");
    
    for(int i= 0; i < data.size(); i++){
        data[i].getStr(buff,257,10);
        fprintf(f, "%s\n",buff);
    }
    fclose(f);
    
}

vector<vector<vector<vector<F>>>> vector2tensor(vector<F> v,vector<vector<vector<vector<F>>>> M,int w_pad){
    int N = M[0].size();
    int w = M[0][0].size();
    vector<vector<vector<vector<F>>>> M_new(M.size());
    for(int i = 0; i < M.size(); i++){
        M_new[i].resize(M[i].size());
        for(int j = 0; j < M[i].size(); j++){
            M_new[i][j].resize(w_pad);
            for(int k = 0; k < w_pad; k++){
                M_new[i][j][k].resize(w_pad);
                for(int l = 0; l < w_pad; l++){
                    M_new[i][j][k][l] = v[i*N*w*w + j*w*w + k*w + l];
                    //V.push_back(M[i][j][k][l]);
                }
            }
        }
    }
    return M_new;
}

vector<vector<F>> convert2matrix(vector<F> arr, int d1, int d2){
    vector<vector<F>> U(d1);
    for(int i = 0; i < d1; i++){
        U[i].resize(d2);
        for(int j = 0; j < d2; j++){
            U[i][j] = arr[i*d2+j];
        }
    }
    return U;
}


vector<vector<F>> &transpose(vector<vector<F>> &M){
    vector<vector<F>> M_t(M[0].size());
    for(int i = 0; i < M[0].size(); i++){
        M_t[i].resize(M.size());
        for(int j = 0; j < M.size(); j++){
            M_t[i][j] = M[j][i];
        }
    }
    return M_t;
}

vector<vector<F>> _transpose(vector<vector<F>> &M){
    vector<vector<F>> M_t(M[0].size());
    for(int i = 0; i < M[0].size(); i++){
        M_t[i].resize(M.size());
        for(int j = 0; j < M.size(); j++){
            M_t[i][j] = M[j][i];
        }
    }
    return M_t;
}


vector<vector<F>> rotate(vector<vector<F>> M){
    vector<vector<F>> M_r(M.size());
    for(int i = 0; i < M.size(); i++){
        M_r[i].resize(M[i].size());
        for(int j = 0; j < M[i].size(); j++){
            M_r[i][j] = M[M.size()-1-i][M[i].size()-1-j];
        }
    }
    return M_r;
}


int get_byte(int pos, F num){
    int b = 8*pos,e = (pos+1)*8;
    char _buff[256];
    int n = num.getStr(_buff,256,2);
    char buff[n];
    for(int i = 0; i < n; i++){
        buff[i] = _buff[n-i-1];
    }
    if(n < b){
        return 0;
    }
    int sum = 0;
    int pow = 1;
    for(int i = b; i < e; i++){
        if(i == n){
            return sum;
        }
        if(buff[i] == '1'){
            sum += pow;
        }
        pow *= 2;
    }
    return sum;
}

vector<F> prepare_bit_vector(vector<F> num, int domain){
    vector<F> bits;
    char buff[257];
    for(int i = 0; i < num.size(); i++){
        vector<F> temp_bits;
        for(int j = 0; j < domain; j++){
            temp_bits.push_back(zero);
        }
        int n = num[i].getStr(buff,257,2);
        if(domain > n-1){
            for(int j = n-1; j >= 0; j--){
                if(buff[j] == '1'){
                    temp_bits[n-1 - j] = one;
                }
            }
        }//else{
        //    printf("Select larger domain %d\n",n);
        //    exit(-1);
        //}
        for(int j = 0; j < domain; j++){
            bits.push_back(temp_bits[j]);
        }
    }
    return bits;
}

vector<F> compute_lagrange_coeff(F omega, F r, int degree){
	vector<F> pows;
	vector<F> L1(degree);
	F A; A.pow(A,r,F(degree));
	A = A-F(1);

	pows.push_back(F(1));
	for(int i = 1; i < degree; i++){
		F num = pows[i-1]*omega;
		if(num == F(1)){
			break;
		}
		pows.push_back(num);
	}
	for(int i = 0; i < pows.size(); i++){
		F temp = F(degree)*(r-pows[i]);
		temp.inv(temp,temp);
		L1[i] = temp*A*pows[i];
	}	
	return L1;
}

void my_fft(vector<F> &arr, vector<F> &w, vector<u32> &rev, F ilen,  bool flag){
    u32 len = arr.size();
    if(!flag){
        //if (flag) F::inv(w[1], w[1]);
        for (u32 i = 0; i < len; ++i)
            if (rev[i] < i) std::swap(arr[i], arr[rev[i]]);
  
        F u,v;
        for (u32 i = 2; i <= len; i <<= 1){
            for (u32 j = 0; j < len; j += i)
                for (u32 k = 0; k < (i >> 1); ++k) {
                    u = arr[j + k];
                    v = arr[j + k + (i >> 1)] * w[len / i * k];
                    arr[j + k] = u + v;
                    arr[j + k + (i >> 1)] = u - v;
                }
        }

    }else{
        F u,v;
        for (u32 i = 0; i < len; ++i)
            if (rev[i] < i) std::swap(arr[i], arr[rev[i]]);
      
    for (u32 i = 2; i <= len; i <<= 1)
        for (u32 j = 0; j < len; j += i)
            for (u32 k = 0; k < (i >> 1); ++k) {
                    u = arr[j + k];
                    v = arr[j + k + (i >> 1)] * w[len / i * k];
                    arr[j + k] = u + v;
                    arr[j + k + (i >> 1)] = u - v;
                
            }
    
        if(flag){
            for (u32 i = 0; i < len; ++i){
                arr[i] = arr[i] * ilen;
            }
        }
       
    }
        
    
    
    /*
    F u,v;    
    for (u32 i = 2; i <= len; i <<= 1)
        for (u32 j = 0; j < len; j += i)
            for (u32 k = 0; k < (i >> 1); ++k) {
                if(i == 2){
                    arr[j + k + (i >> 1)] = arr[j+k];
                }else{
                    u = arr[j + k];
                    v = arr[j + k + (i >> 1)] * w[len / i * k];
                    arr[j + k] = u + v;
                    arr[j + k + (i >> 1)] = u - v;
                }
            }
    
    for (u32 i = 0; i < len; ++i){
        arr[i] = arr[i] * ilen;
    }*/
    
    
    

}


void fft(vector<F> &arr, int logn, bool flag) {
//    cerr << "fft: " << endl;
//    for (auto x: arr) cerr << x << ' ';
//    cerr << endl;
    static std::vector<u32> rev;
    static std::vector<F> w;

    u32 len = 1ULL << logn;
    assert(arr.size() == len);

    rev.resize(len);
    w.resize(len);

    rev[0] = 0;
    for (u32 i = 1; i < len; ++i)
        rev[i] = rev[i >> 1] >> 1 | (i & 1) << (logn - 1);

    w[0] = F_ONE;
    w[1] = getRootOfUnit(logn);
   
    if (flag) F::inv(w[1], w[1]);
    for (u32 i = 2; i < len; ++i) w[i] = w[i - 1] * w[1];
    
    for (u32 i = 0; i < len; ++i)
        if (rev[i] < i) std::swap(arr[i], arr[rev[i]]);

    F u,v;
   
    for (u32 i = 2; i <= len; i <<= 1){
        for (u32 j = 0; j < len; j += i)
            for (u32 k = 0; k < (i >> 1); ++k) {
                u = arr[j + k];
                v = arr[j + k + (i >> 1)] * w[len / i * k];
                arr[j + k] = u + v;
                arr[j + k + (i >> 1)] = u - v;
            }
    }
 
    
    if (flag) {
        F ilen;
        F::inv(ilen, len);
        for (u32 i = 0; i < len; ++i){
            arr[i] = arr[i] * ilen;
        }
    }
}


void phiPowInit(vector<F> &phi_mul, int n, bool isIFFT) {
    u32 N = 1ULL << n;
    F phi = getRootOfUnit(n);
    if (isIFFT) F::inv(phi, phi);
    phi_mul[0] = F_ONE;
    for (u32 i = 1; i < N; ++i) phi_mul[i] = phi_mul[i - 1] * phi;
}

void phiGInit(vector<F> &phi_g, const vector<F>::const_iterator &rx, const F &scale, int n, bool isIFFT) {
    vector<F> phi_mul(1 << n);
    phiPowInit(phi_mul, n, isIFFT);

    if (isIFFT) {
//        cerr << "==" << endl;
//        cerr << "gLength: " << n << endl;
//        for (int i = 0; i < n - 1; ++i) {
//            cerr << rx[i];
//            cerr << endl;
//        }
        phi_g[0] = phi_g[1] = scale;
        for (int i = 2; i <= n; ++i)
            for (u32 b = 0; b < (1ULL << (i - 1)); ++b) {
                u32 l = b, r = b ^ (1ULL << (i - 1));
                int m = n - i;
                F tmp1 = F_ONE - rx[m], tmp2 = rx[m] * phi_mul[b << m];
                phi_g[r] = phi_g[l] * (tmp1 - tmp2);
                phi_g[l] = phi_g[l] * (tmp1 + tmp2);
            }
    } else {
//        cerr << "==" << endl;
//        cerr << "gLength: " << n << endl;
//        for (int i = 0; i < n; ++i) {
//            cerr << rx[i];
//            cerr << endl;
//        }
        phi_g[0] = scale;
        /*
        
        for(int i = 0; i < n; i++){
            for(int j = 1ULL << (i+1)-1; j >= 0; j--){
                phi_g[j] = phi_g[j%(1ULL << i)]*(F(1)-rx[i] + rx[i]*phi_mul[j]);
            }
        }
        */

        for (int i = 1; i < n; ++i){
            for (u32 b = 0; b < (1ULL << (i - 1)); ++b) {
                u32 l = b, r = b ^ (1ULL << (i - 1));
                int m = n - i;
                
                F tmp1 = F_ONE - rx[m], tmp2 = rx[m] * phi_mul[b << m];
                //printf("%d,%d\n",r,l );
                phi_g[r] = phi_g[l] * (tmp1 - tmp2);
                phi_g[l] = phi_g[l] * (tmp1 + tmp2);
            }

        }
        for (u32 b = 0; b < (1ULL << (n - 1)); ++b) {
            u32 l = b;

            F tmp1 = F_ONE - rx[0], tmp2 = rx[0] * phi_mul[b];
            phi_g[l] = phi_g[l] * (tmp1 + tmp2);
            
        }
        
    }
}

void _prepare_matrix1(vector<vector<F>> &M,F rand, int idx, int n, int L){
    int size = n/threads;
    int pos = idx*size;
   
    for(int i = pos; i < pos + size; i++){
        for(int j = 0; j < L; j++){
            M[i][j] = M[i][2*j] + rand*(M[i][2*j+1]-M[i][2*j]);
        }
    }
}
void _prepare_matrix2(F** M,F **temp_M, F rand, int idx, int n, int L){
    int size = L/threads;
    int pos = idx*size;
    

    for(int i = 0; i < n; i++){
        for(int j = pos; j < pos + size ; j++){
            temp_M[i][j] = M[i][2*j] + rand*(M[i][2*j+1]-M[i][2*j]);
        }
    }
}

void cp(vector<vector<F>> &M1,vector<vector<F>> &M2){
    M1 = ref(M2);
}


void pad_matrix(vector<vector<F>> &M){
    int h = 1<<(int)log2(M[0].size());
    if(h != M[0].size()){
        h = h*2;
        for(int i = 0; i < M.size(); i++){
            M[i].resize(h,F(0));
        }
    }

    if((1<<(int)log2(M.size())) != M.size()){
        int s = M.size();
        int e = 1<<(int)(log2(M.size())+1);
        vector<F> new_row(h,F(0));
        for(int i = s; i < e; i++){
            M.push_back(new_row);
        }
    }
}

void pad_matrix_with_num(vector<vector<F>> &M, F num){
    int h = 1<<(int)log2(M[0].size());
    if(h != M[0].size()){
        h = h*2;
        for(int i = 0; i < M.size(); i++){
            M[i].resize(h,num);
        }
    }

    if((1<<(int)log2(M.size())) != M.size()){
        int s = M.size();
        int e = 1<<(int)(log2(M.size())+1);
        vector<F> new_row(h,num);
        for(int i = s; i < e; i++){
            M.push_back(new_row);
        }
    }
}

void pad_file_with(FILE *fd, F num, size_t size){
    
    if(1ULL<<((int)log2(size)) == size){
        return;
    }    
    size_t pad_size = (1ULL<<((int)log2(size)+1)) - size;
    vector<F> v(MAX_CHUNCK,num);
    for(int i = 0; i < pad_size/MAX_CHUNCK; i++){
        write_file(v,fd);
    }
    v.clear();
    v.resize(pad_size%MAX_CHUNCK,num);
    write_file(v,fd);
}

void pad_vector(vector<F> &V){
    int h = 1<<(int)log2(V.size());
    if(h != V.size()){
        h = h*2;
        V.resize(h,F(0));
    }
}

void pad_vector_with_num(vector<F> &V,F num){
    int h = 1<<(int)log2(V.size());
    if(h != V.size()){
        h = h*2;
        V.resize(h,num);
    }
}



vector<F> prepare_matrix(vector<vector<F>> &M, vector<F> r){
    vector<F> V;
    int n = M.size();
    int offset = M[0].size()/2;
    //printf(">> %d,%d,%d\n",n, M[0].size(),r.size() );
   
     if(threads == 1){
        for(int k = 0; k < r.size(); k++){
            for(int i = 0; i < n; i++){
                for(int j = 0; j < offset; j++){
                    M[i][j] = M[i][2*j] + r[k]*(M[i][2*j+1]-M[i][2*j]);
                }
            }
            offset = offset/2;
        }
    }
    else if(n >= threads){

        for(int k = 0; k < r.size(); k++){
            if(n*offset > 1<<16){
        
                thread workers[threads];
                for(int i = 0; i < threads; i++){
                    workers[i] = thread(&_prepare_matrix1,ref(M),r[k],i,n,offset);
                }
                for(int i = 0; i < threads; i++){
                    workers[i].join();
                }
            }else{
                for(int i = 0; i < n; i++){
                    for(int j = 0; j < offset; j++){
                        M[i][j] = M[i][2*j] + r[k]*(M[i][2*j+1]-M[i][2*j]);
                    }
                }
            }
            offset = offset/2;
        }
    }else{
        F** temp = (F **)malloc(n*sizeof(F *));
        for(int i = 0; i < n; i++){
            temp[i] = M[i].data();
        }
        
        for(int k = 0; k < r.size(); k++){
            if(n*offset > 1<<16){
                F **temp_M;
                temp_M = (F **)malloc(n*sizeof(F*));
                for(int i = 0; i < n; i++){
                    temp_M[i] = (F *)malloc(offset*sizeof(F));
                }
                
                thread workers[threads];
                auto ts = high_resolution_clock::now();
                for(int i = 0; i < threads; i++){
                    workers[i] = thread(&_prepare_matrix2,ref(temp),ref(temp_M),r[k],i,n,offset);
                }
                for(int i = 0; i < threads; i++){
                    workers[i].join();
                }
                offset = offset/2;
                
                auto te = high_resolution_clock::now();
                auto tduration = duration_cast<microseconds>(te - ts);
                
                ts = high_resolution_clock::now();
                
                for(int i = 0; i < n; i++){
                    temp[i] = temp_M[i];
                }

                te = high_resolution_clock::now();
                tduration = duration_cast<microseconds>(te - ts);
                
            }else{
                for(int i = 0; i < n; i++){
                    for(int j = 0; j < offset; j++){
                        temp[i][j] = temp[i][2*j] + r[k]*(temp[i][2*j+1]-temp[i][2*j]);
                    }
                }   
            }
        }
        for(int i = 0; i < n; i++){
            V.push_back(temp[i][0]);
        }
        return V;
    }
    for(int i = 0; i < n; i++){
        V.push_back(M[i][0]);
    }
    return V;
}

F evaluate_matrix(vector<vector<F>> M, vector<F> r1, vector<F> r2){
    vector<F> v = prepare_matrix(transpose(M),r1);
    for(int i = 0; i < r2.size(); i++){
        int L = 1 << (r2.size() - 1 - i);

        for(int j = 0; j < L; j++){
            v[j] = (1-r2[i])*v[2*j] + r2[i]*v[2*j+1];
        }
    }
    return v[0];
}

F evaluate_vector(vector<F> v,vector<F> r){
    if(r.size() > (int)log2(v.size())){
        vector<F> temp_r;
        for(int i = 0; i < (int)log2(v.size()); i++){
            temp_r.push_back(r[r.size()-(int)log2(v.size())+ i]);
        }
        r = temp_r;
    }
    for(int i = 0; i < r.size(); i++){
        int L = 1 << (r.size() - 1 - i);
        for(int j = 0; j < L; j++){
            v[j] = (1-r[i])*v[2*j] + r[i]*v[2*j+1];
        }
    }
    return v[0];    
}

vector<F> evaluate_vector_stream_batch_hardcoded(stream_descriptor fp,vector<vector<F>> r, size_t size){
    int _MAX_CHUNCK = MAX_CHUNCK;
    if(_MAX_CHUNCK > size){
        _MAX_CHUNCK = size;
    }

    
    
    int depth = (int)log2(size) - (int)log2(_MAX_CHUNCK);
    vector<vector<F>> x1(r.size()),x2(r.size());
    
    for(int i = 3; i < (int)log2(_MAX_CHUNCK); i++){
        for(int j = 0; j < x1.size(); j++){
            x1[j].push_back(r[j][i]);
        }
    }
    
    for(int i = (int)log2(_MAX_CHUNCK); i < r[0].size(); i++){
        for(int j = 0; j < x2.size(); j++){
            x2[j].push_back(r[j][i]);
        }
    } 

    vector<vector<F>> temp_sum(x1.size());
    for(int i = 0; i < x1.size(); i++){
        temp_sum[i].resize(depth,F(0));
    }
    if(x2[0].size() != depth){
        printf("Different depth\n");
        exit(-1);
    }
    vector<F> v1(_MAX_CHUNCK);
    vector<vector<F>> v2(r.size());
    for(int i = 0; i < v2.size(); i++){
        v2[i].resize(size/_MAX_CHUNCK,F(0));
    }
    vector<F> final_eval(x1.size());
    
    
    vector<vector<F>> B(x1.size());
    for(int i = 0; i < x1.size(); i++){
        precompute_beta(x1[i],B[i]);
    }
    
    for(int i = 0; i < size/_MAX_CHUNCK; i++){
      
        read_stream(fp,v1,_MAX_CHUNCK);
      
        for(int k = 0; k < x1.size(); k++){
            for(int j = 0; j < _MAX_CHUNCK/8; j++){
                v2[k][i] += v1[8*j + k]*B[k][j];
            }
        }
    }
    if(x2[0].size() == 0){
        for(int i = 0; i < x1.size(); i++){
            final_eval[i] = v2[i][0];// evaluate_vector(v2[i],x2[i]);
        }    
    }else{
        for(int i = 0; i < x1.size(); i++){
            final_eval[i] = evaluate_vector(v2[i],x2[i]);
        }
    }
    v1.clear();
    for(int i = 0; i <v2.size(); i++){
        v2[i].clear();
    }
    
    return final_eval;    
}

vector<F> evaluate_vector_stream_batch(stream_descriptor fp,vector<vector<F>> r, size_t size){
    int _MAX_CHUNCK = MAX_CHUNCK;
    if(_MAX_CHUNCK > size){
        _MAX_CHUNCK = size;
    }

    
    
    int depth = (int)log2(size) - (int)log2(_MAX_CHUNCK);
    vector<vector<F>> x1(r.size()),x2(r.size());
    
    for(int i = 0; i < (int)log2(_MAX_CHUNCK); i++){
        for(int j = 0; j < x1.size(); j++){
            x1[j].push_back(r[j][i]);
        }
    }
    
    for(int i = (int)log2(_MAX_CHUNCK); i < r[0].size(); i++){
        for(int j = 0; j < x2.size(); j++){
            x2[j].push_back(r[j][i]);
        }
    } 

    vector<vector<F>> temp_sum(x1.size());
    for(int i = 0; i < x1.size(); i++){
        temp_sum[i].resize(depth,F(0));
    }
    if(x2[0].size() != depth){
        printf("Different depth\n");
        exit(-1);
    }
    vector<F> v1(_MAX_CHUNCK);
    vector<vector<F>> v2(r.size());
    for(int i = 0; i < v2.size(); i++){
        v2[i].resize(size/_MAX_CHUNCK,F(0));
    }
    vector<F> final_eval(x1.size());
    
    for(int i = 0; i < size/_MAX_CHUNCK; i++){
        read_stream(fp,v1,_MAX_CHUNCK);
    
        for(int k = 0; k < x1.size(); k++){
            v2[k][i] = evaluate_vector(v1,x1[k]);
            /*
            F eval1 = evaluate_vector(v1,x1[k]);
            for(int j = 0; j < temp_sum[k].size(); j++){
                if(temp_sum[k][j] == F(0)){
                    temp_sum[k][j] = eval1;
                    
                    break;
                }else{
                    eval1 = temp_sum[k][j]*(F(1) - x2[k][j]) + eval1*x2[k][j];
                    temp_sum[k][j] = F(0);
                }
            }*/
            
            //final_eval[k] = eval1;
        }
    }
    if(x2[0].size() == 0){
        for(int i = 0; i < x1.size(); i++){
            final_eval[i] = v2[i][0];// evaluate_vector(v2[i],x2[i]);
        }    
    }else{
        for(int i = 0; i < x1.size(); i++){
            final_eval[i] = evaluate_vector(v2[i],x2[i]);
        }
    }
    v1.clear();
    for(int i = 0; i <v2.size(); i++){
        v2[i].clear();
    }
    
    return final_eval;    
}

vector<F> evaluate_multree(stream_descriptor fp, vector<F> r, vector<size_t> sizes, int distance){
    vector<vector<F>> v(sizes.size());
    vector<vector<F>> v1(sizes.size());
    vector<int> idx(sizes.size(),0),counter(sizes.size(),0);
    vector<F> sum(sizes.size(),0);
    
    for(int i = 0; i < v.size(); i++){
        v[i].resize(MAX_CHUNCK/(1<<(distance*i)));
        v1[i].resize(MAX_CHUNCK);
    }
    vector<F> r1,r2;
    vector<F> beta1,beta2;
    for(int i = 0; i < (int)log2(MAX_CHUNCK); i++){
        r1.push_back(r[i]);
    }
    for(int j = (int)(log2(MAX_CHUNCK)); j < r.size(); j++){
        r2.push_back(r[j]);
    }
    precompute_beta(r1,beta1);
    precompute_beta(r2,beta2);
    
    for(int i = 0; i < sizes[0]/MAX_CHUNCK; i++){
        read_stream_batch(fp,v,MAX_CHUNCK,distance);
        
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
                sum[j] += v1[j][k]*beta1[k]*beta2[counter[j]];
            }
            counter[j]++;
            
        }
    }
    
    vector<F> prod(sizes.size(),F(1));
    for(int i = 1; i < prod.size(); i++){
        
        for(int j = 0; j < (int)log2(sizes[0]/sizes[i]); j++){
            prod[i] *= (F(1) - r[r.size() -1-j]);
        }
    }
    for(int i = 0; i < prod.size(); i++){
        F::inv(prod[i],prod[i]);
        sum.push_back(sum[i]*prod[i]);
    }
    
    return sum;
}


F evaluate_vector_stream(stream_descriptor fp, vector<F> r, size_t size){
    int _MAX_CHUNCK = MAX_CHUNCK;
    if(_MAX_CHUNCK > size){
        _MAX_CHUNCK = size;
    }
    int depth = (int)log2(size) - (int)log2(_MAX_CHUNCK);
    vector<F> x1,x2;
    for(int i = 0; i < (int)log2(_MAX_CHUNCK); i++){
        x1.push_back(r[i]);
    }
    for(int i = (int)log2(_MAX_CHUNCK); i < r.size(); i++){
        x2.push_back(r[i]);
    } 

    vector<F> temp_sum(depth,F(0));
    vector<F> v1(_MAX_CHUNCK),v2(size/_MAX_CHUNCK);
    F final_eval;
    for(int i = 0; i < size/_MAX_CHUNCK; i++){
        read_stream(fp,v1,_MAX_CHUNCK);
        /*
        for(int j = 0; j < temp_sum.size(); j++){
            if(temp_sum[j] == F(0)){
                temp_sum[j] = eval1;
                break;
            }else{
                eval1 = temp_sum[j]*(F(1) - x2[j]) + eval1*x2[j];
                temp_sum[j] = F(0);
            }
        }
        final_eval = eval1;*/
        v2[i] =  evaluate_vector(v1,x1);
        //F eval1 = evaluate_vector(v1,x1);
        
    }
    F y =evaluate_vector(v2,x2);
    v2.clear();
    v1.clear();
    return y;    
}




vector<vector<F>> generate_tables(){
    int N = 4;
    int no_tables = 5;
    vector<vector<F>> tables(no_tables);
    vector<int> max_num;
    int exponent = 0,last_exponent = 1;
    float num = 0;
    
    for(int i = 0; i < tables.size(); i++){
        for(int j = 0; j < 1<<N; j++){
            exponent = exponent + last_exponent; 
            F num;
            num.setByCSPRNG();
            tables[i].push_back(num);
            //tables[i].push_back(quantize(exp(-dequantize(exponent,1))));
        }
        last_exponent = exponent;
        exponent = 0;
    }
    
    //printf("%f,%f\n",dequantize(prod,level),exp(-0.1) );
    return tables;
}


vector<F> get_predicates(int size){
    vector<F> poly;
    for(int i = 0; i < 1<<size; i++){
        poly.push_back(F(rand()%2));
    }
    return poly;
}

vector<F> get_poly(int size){
    vector<F> poly;

    for(int i = 0; i < 1<<size; i++){
        F num;
        num.setByCSPRNG();
        poly.push_back(num);
    }
    return poly;
}

vector<F> lookup_prod(vector<vector<F>> tables, F num){
    char buff[256];
    num = F(0)-num;
    int n = num.getStr(buff,256,2);
    int counter = 0;
    int level = 0;
    F prod = F(1);
    vector<vector<F>> monomials(tables.size());
    for(int i = 0; i < tables.size(); i++){
        monomials[i].resize(4);
        for(int j = 0; j < 4; j++){
            monomials[i][j] = F(0);
        }
    }
    for(int i = 0; i < tables.size(); i++){
        int idx = 0;

        for(int j = 0; j < (int)log2(tables[i].size()); j++){
            if(buff[n - counter - 1] == '1'){
                idx += 1<<j;
                monomials[i][j] = F(1);
            }
            

            counter+=1;
            if(counter == n){
                break;
            }

        }
        if(counter == n){
            prod *= tables[i][idx];
            level = i+1;
            break;
        }
        level = i+1;
        prod *= tables[i][idx];
    }
    if(level < tables.size()){
    
        for(int i = level; i <tables.size(); i++){
            prod *= tables[i][0];
        }
    }
    vector<F> r;
    F prod_2 = F(1);
    for(int i = 0; i < monomials.size(); i++){
        r.push_back( evaluate_vector(tables[i],monomials[i]));
    }


    return r;
}

F lookup(vector<vector<F>> tables, F num){
    char buff[256];
    num = F(0)-num;
    int n = num.getStr(buff,256,2);
    int counter = 0;
    int level = 0;
    F prod = F(1);
    vector<vector<F>> monomials(tables.size());
    for(int i = 0; i < tables.size(); i++){
        monomials[i].resize(4);
        for(int j = 0; j < 4; j++){
            monomials[i][j] = F(0);
        }
    }
    for(int i = 0; i < tables.size(); i++){
        int idx = 0;

        for(int j = 0; j < (int)log2(tables[i].size()); j++){
            if(buff[n - counter - 1] == '1'){
                idx += 1<<j;
                monomials[i][j] = F(1);
            }
            

            counter+=1;
            if(counter == n){
                break;
            }

        }
        if(counter == n){
            prod *= tables[i][idx];
            level = i+1;
            break;
        }
        level = i+1;
        prod *= tables[i][idx];
    }
    if(level < tables.size()){
    
        for(int i = level; i <tables.size(); i++){
            prod *= tables[i][0];
        }
    }

    F prod_2 = F(1);
    for(int i = 0; i < monomials.size(); i++){
        prod_2 *= evaluate_vector(tables[i],monomials[i]);
    }

    prod_2.getStr(buff,256,10);
    //printf("%s\n",buff );

    return prod;
}
