#include "BuildTree.h"
#include "config_pc.hpp"
#include "Inference.h"
#include <math.h>
#include "utils.hpp"

extern int correct_prediction;
extern int bin_size;
vector<F> table;

F one,zero,minus_one;

void init_table(){
	one = F(1);zero = F(0);minus_one = F(-1);
	for(int i = 0; i < (1ULL<<8); i++){
		table.push_back(F(i));
	}
}

int get_pos(vector<vector<Node>> &tree, vector<int> &x,int y){
	int pos = 0;
	int size = (int)log2(tree.size())-1;
	int idx = 0;
	
	
	for(int i = 0; i <tree.size(); i++){
		for(int j = 0; j < tree[i].size(); j++){
			int attr = tree[i][j].attr;
			if(tree[i][j].direction < 0){
				return i;
			}
			if(x[attr] > tree[i][j].split_value && tree[i][j].direction == 0){
				break;
			}
			if(x[attr] <= tree[i][j].split_value && tree[i][j].direction == 1){
				break;
			}
		}
	
	}

	return -1;
	
	return pos;
}


int find_path(vector<vector<Node>> &tree, vector<int> &x, vector<int> &indexes,int y){
	int pos = 0;
	int size = (int)log2(tree.size())-1;
	int idx = 0;
	
	
	for(int i = 0; i <tree.size(); i++){
		for(int j = 0; j < tree[i].size(); j++){
			int attr = tree[i][j].attr;
			if(tree[i][j].direction < 0){
				for(int k = 0; k < tree[i].size()-1; k++){
					indexes.push_back(tree[i][k].attr);
				}
				if(y == tree[i][j].classification){
					correct_prediction++;
				}
				return i;
			}
			if(x[attr] > tree[i][j].split_value && tree[i][j].direction == 0){
				break;
			}
			if(x[attr] <= tree[i][j].split_value && tree[i][j].direction == 1){
				break;
			}
		}
	
	}

	return -1;
	
	return pos;
}

void get_permuted_input(vector<F> &buff,vector<vector<Node>> &tree, vector<int> &x,int y){
	vector<int> indexes;
	int pos = find_path(tree,x,indexes,y);
	Tree_Inference_Data Data;
	vector<int> inactive_indexes(x.size());
	for(int i = 0; i < x.size(); i++){
		inactive_indexes[i] = i;
	}
	for(int i = 0; i < indexes.size(); i++){
		inactive_indexes.erase(std::remove(inactive_indexes.begin(), inactive_indexes.end(), indexes[i]), inactive_indexes.end());
	}
	for(int i = 0; i < indexes.size(); i++){
		//buff[2*i] = F(indexes[i]);
		//buff[2*i+1] = F(x[indexes[i]]);
		buff[2*i] = table[(indexes[i])];
		buff[2*i+1] = table[(x[indexes[i]])];
	}
	
	for(int i = 0; i <inactive_indexes.size(); i++){
		//buff[2*indexes.size() + 2*i] = F(inactive_indexes[i]);
		//buff[2*indexes.size() + 2*i+1] = F(x[inactive_indexes[i]]);
		buff[2*indexes.size() + 2*i] = table[(inactive_indexes[i])];
		buff[2*indexes.size() + 2*i+1] = table[(x[inactive_indexes[i]])];
	}	
}

void get_path(vector<F> &path, vector<vector<Node>> &tree, vector<int> &x,int y){
	int pos = get_pos(tree,x,y);
	for(int i = 0; i < tree[pos].size()-1; i++){
		//path[4*i] = (F(tree[pos][i].split_value));
		//path[4*i+1]  = (F(tree[pos][i].attr));
		//path[4*i +2] = (F(tree[pos][i].direction));
		//path[4*i + 3] = (F_ZERO);
		path[4*i] = table[((tree[pos][i].split_value))];
		path[4*i+1]  = table[(tree[pos][i].attr)];
		if(tree[pos][i].direction < 0){
			path[4*i +2] = minus_one;
		}else{
			path[4*i +2] = table[(tree[pos][i].direction)];
		}
		path[4*i + 3] = table[0];
	
	}
}

void get_aux(vector<F> &aux, vector<vector<Node>> &tree, vector<int> &x,int y){
	int pos = get_pos(tree,x,y);
	//aux[0] = F(pos);
	//aux[1] = F(tree[pos][tree[pos].size()-1].classification);
	aux[0] = table[(pos)];
	aux[1] = table[(tree[pos][tree[pos].size()-1].classification)];
}

void get_diff(vector<F> &diff, vector<vector<Node>> &tree, vector<int> &x,int y){
	vector<int> indexes;
	int pos = find_path(tree,x,indexes,y);
	Tree_Inference_Data Data;
	
	if(pos == -1){
		printf("Error inference\n");
		exit(-1);
	}
	vector<int> inactive_indexes(x.size());
	for(int i = 0; i < x.size(); i++){
		inactive_indexes[i] = i;
	}
	for(int i = 0; i < indexes.size(); i++){
		inactive_indexes.erase(std::remove(inactive_indexes.begin(), inactive_indexes.end(), indexes[i]), inactive_indexes.end());
	}
	
	//vector<vector<int>> path = tree[pos];
	
	vector<int> path;
	vector<int> permuted_input;
	vector<int> _diff(tree[pos].size()-1);
	
	for(int i = 0; i < indexes.size(); i++){
		permuted_input.push_back((indexes[i]));
		permuted_input.push_back((x[indexes[i]]));
	
	}
	
	for(int i = 0; i <inactive_indexes.size(); i++){
		permuted_input.push_back((inactive_indexes[i]));
		permuted_input.push_back((x[inactive_indexes[i]]));
	}

	for(int i = 0; i < tree[pos].size()-1; i++){
		path.push_back((tree[pos][i].split_value));
		path.push_back((tree[pos][i].attr));
		path.push_back((tree[pos][i].direction));
		path.push_back((0));
	}
	
	
	for(int i = 0; i < tree[pos].size()-1; i++){
		if(path[4*i+2] == 1){
			_diff[i] = permuted_input[2*i+1]-path[4*i];
		}else if(path[4*i+2] == 0){
			_diff[i] = path[4*i] - permuted_input[2*i+1];
		}else{
			_diff[i] = 0;
		}
	}
	for(int i = 0; i < _diff.size(); i++){
		//diff[i] = F(_diff[i]);
		if(_diff[i] < 0){
			printf("Error in diff\n");
			exit(-1);
		}
		diff[i] = table[(_diff[i])];
		
	}
}

void get_bits(vector<F> &bit_vector, vector<vector<Node>> &tree, vector<int> &x,int y){
	vector<int> indexes;
	int pos = find_path(tree,x,indexes,y);
	Tree_Inference_Data Data;
	
	if(pos == -1){
		printf("Error inference\n");
		exit(-1);
	}
	vector<int> inactive_indexes(x.size());
	for(int i = 0; i < x.size(); i++){
		inactive_indexes[i] = i;
	}
	for(int i = 0; i < indexes.size(); i++){
		inactive_indexes.erase(std::remove(inactive_indexes.begin(), inactive_indexes.end(), indexes[i]), inactive_indexes.end());
	}
	
	//vector<vector<int>> path = tree[pos];
	
	vector<int> path;
	vector<int> permuted_input;
	vector<int> _diff(tree[pos].size()-1);
	//vector<int> diff(tree[pos].size()-1);
	for(int i = 0; i < indexes.size(); i++){
		permuted_input.push_back((indexes[i]));
		permuted_input.push_back((x[indexes[i]]));
	
	}
	
	for(int i = 0; i <inactive_indexes.size(); i++){
		permuted_input.push_back((inactive_indexes[i]));
		permuted_input.push_back((x[inactive_indexes[i]]));
	}

	for(int i = 0; i < tree[pos].size()-1; i++){
		path.push_back((tree[pos][i].split_value));
		path.push_back((tree[pos][i].attr));
		path.push_back((tree[pos][i].direction));
		path.push_back((0));
	}
	
	
	for(int i = 0; i < tree[pos].size()-1; i++){
		if(path[4*i+2] == 1){
			_diff[i] = permuted_input[2*i+1]-path[4*i];
		}else if(path[4*i+2] == 0){
			_diff[i] = path[4*i] - permuted_input[2*i+1];
		}else{
			_diff[i] = 0;
		}
	}

	
	/*
	for(int i = 0; i < _diff.size(); i++){
		//diff[i] = F(_diff[i]);
		if(diff[i] < 0){
			printf("Negative diff\n");
			exit(-1);
		}
		diff[i] = table[(_diff[i])];
	}
	*/
	int q = ((int)log2(bin_size));
	if(1 << ((int)log2(q)) != q){
		q = 1 << ((int)log2(q)+1);
	}
	bit_vector.resize(q*_diff.size());
	for(int i = 0; i < _diff.size(); i++){
		for(int j = 0; j < q; j++){
			if(_diff[i]&1 == 1){
				bit_vector[i*q + j] = one;
			}else{
				bit_vector[i*q + j] = zero;
			}
			_diff[i] = _diff[i]>>1;
		}
	}
	
	//bit_vector = prepare_bit_vector(diff,q);

}

void test_accuracy(Dataset D_test, vector<vector<Node>> tree){
	for(int i = 0; i < D_test.data[0].size(); i++){
		vector<int> x;
		vector<int> indexes;
		for(int j = 0; j < D_test.data.size(); j++){
			x.push_back(D_test.data[j][i]);
		}
		find_path(tree,x,indexes,D_test.label[i]);
	}
	printf("Accuracy : %lf \n", (float)correct_prediction/(float)D_test.data[0].size());
}

Tree_Inference_Data Tree_Inference(vector<vector<Node>> &tree, vector<int> x,int y){
	vector<int> indexes;
	int pos = find_path(tree,x,indexes,y);
	Tree_Inference_Data Data;
	
	if(pos == -1){
		printf("Error inference\n");
		exit(-1);
	}
	vector<int> inactive_indexes(x.size());
	for(int i = 0; i < x.size(); i++){
		inactive_indexes[i] = i;
	}
	for(int i = 0; i < indexes.size(); i++){
		inactive_indexes.erase(std::remove(inactive_indexes.begin(), inactive_indexes.end(), indexes[i]), inactive_indexes.end());
	}
	
	//vector<vector<int>> path = tree[pos];
	
	vector<F> path;
	vector<F> input;
	vector<F> permuted_input;

	for(int i = 0; i < x.size(); i++){
		input.push_back(F(i));
		input.push_back(F(x[i]));		
	}
	for(int i = 0; i < indexes.size(); i++){
		permuted_input.push_back(F(indexes[i]));
		permuted_input.push_back(F(x[indexes[i]]));
	
	}
	
	for(int i = 0; i <inactive_indexes.size(); i++){
		permuted_input.push_back(F(inactive_indexes[i]));
		permuted_input.push_back(F(x[inactive_indexes[i]]));
	}

	for(int i = 0; i < tree[pos].size()-1; i++){
		path.push_back(F(tree[pos][i].split_value));
		path.push_back(F(tree[pos][i].attr));
		path.push_back(F(tree[pos][i].direction));
		path.push_back(F(0));
	}
	//for(int i = 0; i < inactive_indexes.size(); i++){
	//	path.push_back(F(0));
	//	path.push_back(inactive_indexes[i]);
	//	path.push_back(F(-1));
	//}
	Data.paths_aux.push_back(F(pos));
	Data.paths_aux.push_back(F(tree[pos][tree[pos].size()-1].classification));
	

	vector<F> diff(tree[pos].size()-1);
	vector<F> diff_bits;
	
	for(int i = 0; i < tree[pos].size()-1; i++){
		if(path[4*i+2] == F(1)){
			diff[i] = permuted_input[2*i+1]-path[4*i];
		}else if(path[4*i+2] == F(0)){
			diff[i] = path[4*i] - permuted_input[2*i+1];
		}else{
			diff[i] = 0;
		}
	}
	int q = ((int)log2(bin_size));
	if(1 << ((int)log2(q)) != q){
		q = 1 << ((int)log2(q)+1);
	}
	vector<F> bit_vector = prepare_bit_vector(diff,q);

	Data.input = input;
	Data.permuted_input = permuted_input;
	Data.path = path;
	Data.bit_vector = bit_vector;
	Data.diff  = diff;
	Data.pos = pos;
	return Data;

	/*
	for(int i = 0; i < indexes.size(); i++){
		diff[i] = path[i][0] - x[indexes[i]];
		if((diff[i] < 0 && path[i][2] == 0) || (diff[i] >= 0 && path[i][2] == 1)){
			printf("Error\n");
			printf("%d,%d,%d\n",pos,indexes.size(),i );
	
			for(int j = 0; j < indexes.size(); j++){
				printf("%d ",x[indexes[j]] );
			}
			printf("\n");
			for(int j = 0; j < indexes.size(); j++){
				printf("%d,%d / ",path[j][0],diff[j] );
			}
			printf("\n");
			exit(-1);
		}
	}
	*/

}