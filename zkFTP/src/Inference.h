#include "config_pc.hpp"
#include "BuildTree.h"

struct Tree_Inference_Data{
	vector<F> path;
	vector<F> paths_aux;
	vector<F> input;
	vector<F> permuted_input;
	vector<F> bit_vector;
	vector<F> diff;
	int pos;
};

typedef struct Tree_Inference_Data;


Tree_Inference_Data Tree_Inference(vector<vector<Node>> &tree, vector<int> x,int y);
void test_accuracy(Dataset D_test, vector<vector<Node>> tree);

void get_permuted_input(vector<F> &buff,vector<vector<Node>> &tree, vector<int> &x,int y);
void get_path(vector<F> &path, vector<vector<Node>> &tree, vector<int> &x,int y);
void get_aux(vector<F> &aux, vector<vector<Node>> &tree, vector<int> &x,int y);
void get_diff(vector<F> &diff, vector<vector<Node>> &tree, vector<int> &x,int y);
void get_bits(vector<F> &bit_vector, vector<vector<Node>> &tree, vector<int> &x,int y);
int get_pos( vector<vector<Node>> &tree, vector<int> &x,int y);
void init_table();