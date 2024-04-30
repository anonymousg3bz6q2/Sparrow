#pragma once
#include "config_pc.hpp"
#include "circuit.h"


struct stream_descriptor{
    size_t pos,pos_j = 0;
    size_t data_size,row_size,col_size,size,layer,tree_pos;
    string name;    
    size_t input_pos,input_pos_j,input_data_size,input_size;
    string input_name;
};

typedef struct stream_descriptor stream_descriptor;

void read_layer(int circuit_num, int layer , vector<F> &V);
void read_H( int layer , vector<F> &H_add,vector<F> &H_mul, vector<F> &V, F beta_h1, F beta_h2 );
void read_G( int layer , vector<F> &G_add,vector<F> &G_mul, vector<F> &V, vector<F> &beta_g1,F beta_h1,
 F beta_g2,F beta_h2,F Vr);
 
void read_stream(stream_descriptor &fd, vector<F> &v, int size);

void reset_stream(stream_descriptor &fp);