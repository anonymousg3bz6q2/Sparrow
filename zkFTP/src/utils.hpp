//
// Created by 69029 on 6/23/2021.
//

#pragma once

#include "config_pc.hpp"
#include "witness_stream.h"

extern double proving_time;

void reset_histograms_forest();
void reset_histograms();
void compute_histogram(int idx);
void compute_node_histogram(int idx);
void compute_witness_hist(int idx);
void compute_out_hist(int idx);
void compute_ginis(int idx);
void compute_compressed_histograms(vector<vector<F>> &compressed_leaf_hist,vector<vector<F>> &compressed_node,vector<vector<F>> &compressed_witness,
vector<vector<F>> &compressed_out,vector<F> compress_vector);
void write_file(vector<F> arr, FILE *fp, int size =0);
vector<F> compute_lagrange_coeff(F omega, F r, int degree);
void write_file_bytes(vector<F> arr, int no_bytes, FILE *fp);
void read_chunk_bytes(int fp,vector<F> &arr, int no_bytes, int segment_size);
void write_pp(vector<G1> pp, FILE *fp);
F evaluate_vector_stream(stream_descriptor fp,vector<F> r, size_t size);
vector<F> evaluate_vector_stream_batch_hardcoded(stream_descriptor fp,vector<vector<F>> r, size_t size);
vector<F> evaluate_vector_stream_batch(stream_descriptor fp,vector<vector<F>> r, size_t size);
void read_pp(int fp, vector<G1> &pp, int segment_size);
void read_chunk(int fp,vector<F> &arr, int segment_size);
void pad_file_with(FILE *fd, F num, size_t size);
void pad_vector(vector<F> &V);
void pad_vector_with_num(vector<F> &V,F num);
void pad_matrix(vector<vector<F>> &M);
void pad_matrix_with_num(vector<vector<F>> &V,F num);
F chain_hash(F previous_r, vector<F> values);
F chain_hash_verify(F previous_r, vector<F> values, vector<F> &x, vector<F> &y);
vector<F> generate_randomness_verify(int size, F seed,vector<F> &x,vector<F> &y);
vector<F> generate_randomness(int size, F seed);
float proof_size(vector<struct proof> P);
vector<vector<F>> generate_tables();
vector<F> lookup_prod(vector<vector<F>> tables, F num);
vector<F> get_poly(int size);
vector<F> evaluate_multree(stream_descriptor fp, vector<F> r, vector<size_t> sizes, int distance);
size_t normalize_number(size_t num);
void precompute_beta(vector<F> r, vector<F> &beta);
void compute_convolution(vector<vector<F>> Lv, vector<F> &B);
vector<F> get_predicates(int size);
F lookup(vector<vector<F>> tables, F num);
F evaluate_matrix(vector<vector<F>> M, vector<F> r1, vector<F> r2);
F evaluate_vector(vector<F> v,vector<F> r);
vector<F> prepare_matrix(vector<vector<F>> &M, vector<F> r);
vector<F> convert2vector(vector<vector<F>> &M);
void write_data(vector<F> data,char *filename);
vector<F> tensor2vector(vector<vector<vector<vector<F>>>> M);
vector<vector<vector<vector<F>>>> vector2tensor(vector<F> v,vector<vector<vector<vector<F>>>> M,int w);
vector<vector<F>> &transpose(vector<vector<F>> &M);
vector<vector<F>> _transpose(vector<vector<F>> &M);
void compute_binary(vector<F> r, vector<F> &B);
vector<vector<F>> convert2matrix(vector<F> arr, int d1, int d2);
vector<F> prepare_bit_vector(vector<F> num, int domain);
int get_byte(int pos, F num);
vector<vector<F>> rotate(vector<vector<F>> M);
void initBetaTable(vector<F> &beta_g, u8 gLength, const vector<F>::const_iterator &r, const F &init);

void
initBetaTable(vector<F> &beta_g, int gLength, const vector<F>::const_iterator &r_0,
              const vector<F>::const_iterator &r_1, const F &alpha, const F &beta);

void my_fft(vector<F> &arr, vector<F> &w, vector<u32> &rev, F ilen, bool flag);
void fft(vector<F> &arr, int logn, bool flag);
F getRootOfUnit(int n);
void phiGInit(vector<F> &phi_g, const vector<F>::const_iterator &rx, const F &scale, int n, bool isIFFT);
template <class T>
void myResize(vector<T> &vec, u64 sz) {
    if (vec.size() < sz) vec.resize(sz);
}





