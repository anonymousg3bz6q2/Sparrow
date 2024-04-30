#pragma once
#include "config_pc.hpp"
#include "BuildTree.h"

struct stream_descriptor{
    size_t pos,pos_j = 0;
    size_t data_size,row_size,col_size,size,layer,tree_pos;
    vector<F> compress_vector;
    string name;    
    vector<vector<F>> tree;
    vector<vector<Node>> _tree;
    size_t input_pos,input_pos_j,input_data_size,input_size;
    string input_name;
};

typedef struct stream_descriptor stream_descriptor;


int get_witness(stream_descriptor &fd ,vector<F> &v,int size);
int get_compressed_data(stream_descriptor &fd ,vector<F> &v,int size);
void generate_inference_layers(stream_descriptor &fd ,vector<F> &v,int size);
void generate_mul_tree(stream_descriptor &fd , vector<F> &v ,int &size,int layer);
void generate_mul_tree_batch(stream_descriptor &fd, vector<vector<F>> &v, int size, int layer, int distance);
void read_stream(stream_descriptor &fd, vector<F> &v, int size);
void reset_stream(stream_descriptor &fd);
void generate_mul_tree_parallel(stream_descriptor &fd , vector<F> &v ,int &size, int max_depth,int layer);
void get_final_hist(vector<vector<F>> &final_histogram);
void get_final_hist_forest(vector<vector<F>> &final_histogram);
void compute_lookup_output();
void compute_lookup_output_field();
void read_stream_batch(stream_descriptor &fd, vector<vector<F>> &v, int size, int distance);
void get_powers(vector<F> &powers_table, int instances, int trees);
void compute_histogram(int idx);
void compute_node_histogram(int idx);
void compute_compressed_histograms(vector<vector<F>> &compressed_leaf_hist,vector<vector<F>> &compressed_node,vector<vector<F>> &compressed_witness,
vector<vector<F>> &compressed_out,vector<F> compress_vector);