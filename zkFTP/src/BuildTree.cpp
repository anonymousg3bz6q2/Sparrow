#include "BuildTree.h"
#include "config_pc.hpp"
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <sstream>
#include <bits/stdc++.h>
#include <chrono>
#include "Inference.h"
#include "utils.hpp"
#include "GKR.h"
#include "sumcheck.h"
#include "quantization.h"
#include "lookups.h"
#include "mimc.h"
#include "Poly_Commit.h"

#define NUMERICAL 1 
#define CATEGORICAL 2
using namespace chrono;


int r_counter = 0,counter = 0;
extern int bin_size;
int attr_num;
extern MIPP_Comm pp;
extern vector<G1> input_commit;
vector<vector<G1>> cached_commitments;
extern int _commitment_test;
extern float total_p,total_v,total_s;

void LoadDummyDataset_inference(int test_instances, Dataset &D_train,Dataset &D_test){
	vector<string> row;
	vector<vector<string>> content;
	string line,word;
	Dataset D;
	fstream file("/home/christodoulos/datasets/Many_attributes.csv", ios::in);
	if(file.is_open()){
		while(getline(file, line)){
			row.clear();
 		
			stringstream str(line);
 
			while(getline(str, word, ','))
				row.push_back(word);
			content.push_back(row);
		}
		/*
		for(int i=0;i<content.size();i++)
		{
			for(int j=0;j<content[i].size();j++){
				cout<<content[i][j]<<" ";
			}
			cout<<"\n";
		}
		*/
	}
	D.type.resize(content[0].size()-1);
	for(int i = 0; i < D.type.size(); i++){
		D.type[i] = NUMERICAL;
	}
	attr_num = D.type.size();
	bin_size = 128;
	for(int i = 0; i < D.type.size(); i++){

		vector<float> buff(content.size()-1);
		vector<int> col(content.size()-1);

		for(int j = 1; j < content.size(); j++){
			buff[j-1] = stof(content[j][i]);
		}
		float max = *max_element(buff.begin(),buff.end());
		float min = *min_element(buff.begin(),buff.end());
		float dom = (max - min)/(float)(bin_size);
			
		for(int j = 0; j < col.size(); j++){
			col[j] = (int)((buff[j]-min)/dom);
			if(col[j] >= bin_size){
				col[j]--;
			}
		}
		D.data.push_back(col);		
	}
	D.label.resize(content.size()-1);
	for(int i = 1; i < content.size(); i++){
		D.label[i-1] = stoi(content[i][content[0].size()-1].c_str());
	}
	for(int i = 0; i < D.type.size(); i++){
		D.remaining_attr.push_back(i);
	}

	int training_data = D.label.size() - test_instances;


	D_train.type = D.type;
	D_train.remaining_attr = D.remaining_attr;
	D_test.type = D.type;
	D_test.remaining_attr = D.remaining_attr;
	for(int i = 0; i < training_data; i++){
		D_train.data.resize(D.type.size());
		for(int j = 0; j < D.type.size(); j++){
			D_train.data[j].push_back(D.data[j][i]);
		}
		
		D_train.label.push_back(D.label[i]);
		D_train.indexes.push_back(i);
	}

	for(int i = training_data; i < D.data[0].size(); i++){
		D_test.data.resize(D.type.size());
		for(int j = 0; j < D.type.size(); j++){
			D_test.data[j].push_back(D.data[j][i]);
		}
		
		D_test.label.push_back(D.label[i]);
	}
}
void LoadDummyDataset2(int test_instances,int instances, int attributes , Dataset &D_train,Dataset &D_test){
	vector<string> row;
	vector<vector<string>> content;
	string line,word;
	Dataset D;
	
	string name = "dummy_dataset";
	name = name + to_string(instances);
	name = name + "_" + to_string(attributes);
	name = name + ".csv";
	printf("%s\n",name.c_str() ); 
	fstream file(name.c_str(), ios::in);
	if(file.is_open()){
		while(getline(file, line)){
			row.clear();
 		
			stringstream str(line);
 
			while(getline(str, word, ','))
				row.push_back(word);
			content.push_back(row);
		}
	}
	printf("Read dataset\n");
	sleep(10);
	D.type.resize(content[0].size()-1);
	for(int i = 0; i < D.type.size(); i++){
		D.type[i] = NUMERICAL;
	}
	attr_num = D.type.size();
	bin_size = 128;
	vector<float> buff(content.size()-1);
	vector<int> col(content.size()-1);
	for(int i = 0; i < D.type.size(); i++){

		
		for(int j = 1; j < content.size(); j++){
			buff[j-1] = stof(content[j][i]);
		}
		float max = *max_element(buff.begin(),buff.end());
		float min = *min_element(buff.begin(),buff.end());
		float dom = (max - min)/(float)(bin_size);
			
		for(int j = 0; j < col.size(); j++){
			col[j] = (int)((buff[j]-min)/dom);
			if(col[j] >= bin_size){
				col[j]--;
			}
		}
		D.data.push_back(col);		
	}

	D.label.resize(content.size()-1);
	for(int i = 1; i < content.size(); i++){
		D.label[i-1] = stoi(content[i][content[0].size()-1].c_str());
	}
	for(int i = 0; i < D.type.size(); i++){
		D.remaining_attr.push_back(i);
	}

	int training_data = D.label.size() - test_instances;


	D_train.type = D.type;
	D_train.remaining_attr = D.remaining_attr;
	D_test.type = D.type;
	D_test.remaining_attr = D.remaining_attr;
	for(int i = 0; i < training_data; i++){
		D_train.data.resize(D.type.size());
		for(int j = 0; j < D.type.size(); j++){
			D_train.data[j].push_back(D.data[j][i]);
		}
		
		D_train.label.push_back(D.label[i]);
		D_train.indexes.push_back(i);
	}

	for(int i = training_data; i < D.data[0].size(); i++){
		D_test.data.resize(D.type.size());
		for(int j = 0; j < D.type.size(); j++){
			D_test.data[j].push_back(D.data[j][i]);
		}
		
		D_test.label.push_back(D.label[i]);
	}
}


void LoadDummyDataset(int test_instances,int instances, int attributes , Dataset &D_train,Dataset &D_test){
	
	string line,word;
	Dataset D;
	
	string name = "dummy_dataset";
	name = name + to_string(instances);
	name = name + "_" + to_string(attributes);
	name = name + ".csv";
	printf("%s\n",name.c_str() ); 
	fstream file(name.c_str(), ios::in);
			
	vector<string> row;
	vector<vector<string>> content;
	
	vector<float> buff(attributes);
	vector<int> col(attributes);
	
	bin_size = 128;
	int i = 0;
	if(file.is_open()){
		while(getline(file, line)){
			row.clear();
			stringstream str(line);
			if(i != 0){
				while(getline(str, word, ','))
				row.push_back(word);
			//content.push_back(row);
			
			for(int j = 0; j < row.size()-1; j++){
				buff[j] = stof(row[j]);

				//printf("%lf\n",buff[j]);
			}
			
			float max = *max_element(buff.begin(),buff.end());
			float min = *min_element(buff.begin(),buff.end());
			
			
			float dom = (max - min)/(float)(bin_size);
			
			for(int j = 0; j < col.size(); j++){
				col[j] = (int)((buff[j]-min)/dom);
				if(col[j] >= bin_size){
					col[j]--;
				}
						
			}
			D.data.push_back(col);		
			D.label.push_back(stoi(row[col.size()].c_str()));
			
			}else{
				i++;
			}
			row.clear();
		}
	}
	
	
	D.type.resize(attributes);
	for(int i = 0; i < D.type.size(); i++){
		D.type[i] = NUMERICAL;
	}
	attr_num = D.type.size();
	
	
	
	//D.label.resize(content.size()-1);
	//for(int i = 1; i < content.size(); i++){
		//D.label[i-1] = stoi(content[i][content[0].size()-1].c_str());
	//}
	for(int i = 0; i < D.type.size(); i++){
		D.remaining_attr.push_back(i);
	}

	int training_data = D.label.size() - test_instances;

	printf("%d,%d,%d\n",D.data.size(),D.data[0].size(),test_instances);
	D_train.type = D.type;
	D_train.remaining_attr = D.remaining_attr;
	D_test.type = D.type;
	D_test.remaining_attr = D.remaining_attr;
	D_train.data.resize(D.type.size());
	printf("%d\n",training_data);
	for(int i = 0; i < training_data; i++){
		for(int j = 0; j < D.type.size(); j++){
			D_train.data[j].push_back(D.data[i][j]);
		}
		
		D_train.label.push_back(D.label[i]);
		D_train.indexes.push_back(i);
	}

	for(int i = training_data; i < D.data[0].size(); i++){
		D_test.data.resize(D.type.size());
		for(int j = 0; j < D.type.size(); j++){
			D_test.data[j].push_back(D.data[j][i]);
		}
		
		D_test.label.push_back(D.label[i]);
	}
}


void LoadIrisDataset(Dataset &D_train,Dataset &D_test){
	vector<string> row;
	vector<vector<string>> content;
	string line,word;
	Dataset D;
	fstream file("/home/christodoulos/datasets/Iris.csv", ios::in);
	if(file.is_open()){
		while(getline(file, line)){
			row.clear();
 		
			stringstream str(line);
 
			while(getline(str, word, ','))
				row.push_back(word);
			content.push_back(row);
		}
		/*
		for(int i=0;i<content.size();i++)
		{
			for(int j=0;j<content[i].size();j++){
				cout<<content[i][j]<<" ";
			}
			cout<<"\n";
		}
		*/
	}
	D.type.resize(content[0].size()-2);
	for(int i = 0; i < D.type.size(); i++){
		D.type[i] = NUMERICAL;
	}
	attr_num = D.type.size();
	bin_size = 256;
	for(int i = 0; i < D.type.size(); i++){

		vector<float> buff(content.size()-1);
		vector<int> col(content.size()-1);

		for(int j = 1; j < content.size(); j++){
			buff[j-1] = stof(content[j][i+1]);
		}
		float max = *max_element(buff.begin(),buff.end());
		float min = *min_element(buff.begin(),buff.end());
		float dom = (max - min)/(float)bin_size;
		for(int j = 0; j < col.size(); j++){
			col[j] = (int)((buff[j]-min)/dom);
		}
		D.data.push_back(col);
		
	}
	D.label.resize(content.size()-1);
	for(int i = 1; i < content.size(); i++){
		D.label[i-1] = stoi(content[i][content[0].size()-1].c_str());
	}
	for(int i = 0; i < D.type.size(); i++){
		D.remaining_attr.push_back(i);
	}



	D_train.type = D.type;
	D_train.remaining_attr = D.remaining_attr;
	D_test.type = D.type;
	D_test.remaining_attr = D.remaining_attr;

	vector<int> train_idx,test_idx;

	for(int i = 0; i < 150; i++){
		if(i % 5 != 0){
			train_idx.push_back(i);
		}else{
			test_idx.push_back(i);
		}
	}

	for(int i = 0; i < train_idx.size(); i++){
		D_train.data.resize(D.type.size());
		for(int j = 0; j < D.type.size(); j++){
			D_train.data[j].push_back(D.data[j][train_idx[i]]);
		}
		
		D_train.label.push_back(D.label[train_idx[i]]);
		D_train.indexes.push_back(i);
	}

	for(int i = 0; i < test_idx.size(); i++){
		D_test.data.resize(D.type.size());
		for(int j = 0; j < D.type.size(); j++){
			D_test.data[j].push_back(D.data[j][test_idx[i]]);
		}
		
		D_test.label.push_back(D.label[test_idx[i]]);
	}
}

void LoadDiabetesDataset(Dataset &D_train,Dataset &D_test, int test_instances, string fname){
	vector<string> row;
	vector<vector<string>> content;
	string line,word;
	Dataset D;
	fstream file(fname, ios::in);
	if(file.is_open()){
		while(getline(file, line)){
			row.clear();
 		
			stringstream str(line);
 
			while(getline(str, word, ','))
				row.push_back(word);
			content.push_back(row);
		}
		/*
		for(int i=0;i<content.size();i++)
		{
			for(int j=0;j<content[i].size();j++){
				cout<<content[i][j]<<" ";
			}
			cout<<"\n";
		}
		*/
	}
	D.type.resize(content[0].size()-2);
	for(int i = 0; i < D.type.size(); i++){
		D.type[i] = NUMERICAL;
	}
	attr_num = D.type.size();
	bin_size = 128;
	for(int i = 0; i < D.type.size(); i++){

		if(i >= 5 && i < 7){
			vector<float> buff(content.size()-1);
			vector<int> col(content.size()-1);

			for(int j = 1; j < content.size(); j++){
				buff[j-1] = stof(content[j][i+1]);
			}
			float max = *max_element(buff.begin(),buff.end());
			float min = *min_element(buff.begin(),buff.end());
			float dom = (max - min)/(float)bin_size;
			for(int j = 0; j < col.size(); j++){
				col[j] = (int)((buff[j]-min)/dom);
				if(col[j] >= bin_size){
					col[j] = bin_size-1;
				}

			}
			D.data.push_back(col);
		}else{
			vector<int> buff(content.size()-1);

			for(int j = 1; j < content.size(); j++){
				buff[j-1] = stoi(content[j][i+1].c_str());
			}
			int max = *max_element(buff.begin(),buff.end());
			int min = *min_element(buff.begin(),buff.end());
			
			float dom = (float)(max-min)/(float)bin_size;
			if(dom < 1.0){
				D.data.push_back(buff);
			}else{
				for(int j = 0; j < content.size()-1; j++){
					buff[j] = (int)((buff[j]-min)/dom);
					if(buff[j] >= bin_size){
						buff[j] = bin_size-1;
					}
				}
				D.data.push_back(buff);
			}
		}
	}
	D.label.resize(content.size()-1);
	for(int i = 1; i < content.size(); i++){
		D.label[i-1] = stoi(content[i][content[0].size()-1].c_str());
	}
	for(int i = 0; i < D.type.size(); i++){
		D.remaining_attr.push_back(i);
	}

	int training_data = D.label.size() - test_instances;


	D_train.type = D.type;
	D_train.remaining_attr = D.remaining_attr;
	D_test.type = D.type;
	D_test.remaining_attr = D.remaining_attr;
	for(int i = 0; i < training_data; i++){
		D_train.data.resize(D.type.size());
		for(int j = 0; j < D.type.size(); j++){
			D_train.data[j].push_back(D.data[j][i]);
		}
		
		D_train.label.push_back(D.label[i]);
		D_train.indexes.push_back(i);
	}

	for(int i = training_data; i < D.data[0].size(); i++){
		D_test.data.resize(D.type.size());
		for(int j = 0; j < D.type.size(); j++){
			D_test.data[j].push_back(D.data[j][i]);
		}
		
		D_test.label.push_back(D.label[i]);
	}

}

// The smaller the better
float compute_gini(vector<int> histogram){
	float G1,G2; 
	int N1 = histogram[0] + histogram[1]; 
	int N2 = histogram[2] + histogram[3];
	//printf("%d,%d\n",N1,N2 );
	float p11 = (float)histogram[0]/(float)(N1),p12 = (float)histogram[1]/(float)(N1);
	float p21 = (float)histogram[2]/(float)(N2), p22 = (float)histogram[3]/(float)(N2);
	
	if(N1 == 0){
		G2 = 1.0 - ((float)histogram[2]/(float)(N2))*((float)histogram[2]/(float)(N2)) - ((float)histogram[3]/(float)(N2))*((float)histogram[3]/(float)(N2));
		return G2;	
	}
	if(N2 == 0){
		G1 = 1.0 - ((float)histogram[0]/(float)(N1))*((float)histogram[0]/(float)(N1)) - ((float)histogram[1]/(float)(N1))*((float)histogram[1]/(float)(N1));
		return G1;		
	}
	//G1 = -p11*log2(p11) - p12*log2(p12);
	//G2 = -p21*log2(p21) - p22*log2(p22);

	G1 = 1.0 - ((float)histogram[0]/(float)(N1))*((float)histogram[0]/(float)(N1)) - ((float)histogram[1]/(float)(N1))*((float)histogram[1]/(float)(N1));
	G2 = 1.0 - ((float)histogram[2]/(float)(N2))*((float)histogram[2]/(float)(N2)) - ((float)histogram[3]/(float)(N2))*((float)histogram[3]/(float)(N2));
	return ((float)N1/(float)(N1+N2))*G1 + ((float)N2/(float)(N1+N2))*G2;
}


vector<vector<int>> compute_histograms(vector<vector<int>> histogram, int type){
	vector<vector<int>> histograms(histogram[0].size());
	//printf("%d\n",histograms.size() );
	if(type == NUMERICAL){
		histograms[0].resize(4);
		histograms[0][0] = histogram[0][0];
		histograms[0][1] = histogram[1][0];

		int rest_zero = 0;
		int rest_ones = 0;
		for(int i = 1; i < histogram[0].size(); i++){
			rest_zero += histogram[0][i];
			rest_ones += histogram[1][i];
		}
		histograms[0][2] = rest_zero;
		histograms[0][3] = rest_ones;

		int num = rest_zero+rest_ones+histogram[0][0]+histogram[1][0];
		
		for(int i = 1; i < histograms.size(); i++){
			histograms[i].resize(4);
			histograms[i][0] = histograms[i-1][0] + histogram[0][i];
			histograms[i][1] = histograms[i-1][1] + histogram[1][i];
			rest_zero -= histogram[0][i];
			rest_ones -= histogram[1][i];
			histograms[i][2] = rest_zero;
			histograms[i][3] = rest_ones;
			if(num != (histograms[i][2]+histograms[i][3]+histograms[i][0]+histograms[i][1])){
				printf("ERROR\n");
				exit(-1);
			}

		}
	}
	return histograms;
}


float Best_split(vector<vector<int>> histogram, int type, int &split_pos){
	vector<vector<int>> histograms = compute_histograms(histogram,type);
	float best_gini = 10000.0;
	
	if(type == NUMERICAL){
		for(int i = 0; i < histograms.size(); i++){

			float gini = compute_gini(histograms[i]);
			//printf("split : %lf, pos: %d, hist : %d,%d,%d,%d : %d\n", gini,i, histograms[i][0],histograms[i][1],histograms[i][2],histograms[i][3], histograms[i][0]+histograms[i][1]+histograms[i][2]+histograms[i][3]  );
			if(gini < best_gini){
				//printf("Best split : %lf, pos: %d, hist : %d,%d,%d,%d : %d\n", gini,i, histograms[i][0],histograms[i][1],histograms[i][2],histograms[i][3], histograms[i][0]+histograms[i][1]+histograms[i][2]+histograms[i][3]  );
				
				best_gini = gini;
				split_pos = i;
			}
		}
	}else{
		exit(-1);
	}
	//printf("==============\n");
	//printf("==============\n");

	return best_gini;	
}


float FindSplit(Dataset D, int &value, int &feature, vector<float> &Ginis){
	float best_gini = 10000.0;
	int split_value;
	//printf("Size : %d,%d\n",D.data.size(),D.data[0].size() );
	for(int i = 0; i < D.data.size(); i++){
		vector<vector<int>> histogram_table(2);
		//printf("ok %d,%d\n",D.label.size(),D.data[i].size());
		
		if(D.type[i] == NUMERICAL){
			//histogram_table[0].clear();
			//histogram_table[1].clear();
			histogram_table[0].resize(bin_size,0);
			histogram_table[1].resize(bin_size,0);
			
			for(int j = 0; j < D.data[i].size(); j++){
				//printf("%d\n",D.data[i][j] );
				if(D.data[i][j] >= bin_size){
					printf("%d\n",D.data[i][j] );
					printf(">Error\n");
					exit(-1);
				}
				histogram_table[D.label[j]][D.data[i][j]]++;

			}
			
		}
		else{
			exit(1);
		}
		float gini = Best_split(histogram_table,D.type[i],split_value);
		
		if(gini == 10000.0){
			printf("%d\n",split_value );
			exit(1);
		}
		Ginis.push_back(gini);
		if(gini < best_gini){
			best_gini = gini;			
			value = split_value;
			feature = i;
			//printf("Best : %lf,%d,%d\n", best_gini,split_value,D.remaining_attr[i]);
		}
	}
	//printf("ok\n");
	//printf("Best : %lf, %d,%d\n",best_gini,value,feature );
	if(best_gini == 10000.0){
		return -1.0;
	}
	return best_gini;
}


void dataset_union(Dataset &D1,Dataset &D2,Dataset &D){
	D.type = D1.type;
	D.remaining_attr = D1.remaining_attr;
	D.data = D1.data;
	for(int i = 0; i < D2.data.size(); i++){
		for(int j = 0; j < D2.data[0].size(); j++){
			D.data[i].push_back(D2.data[i][j]);
		}
	}
	D.label = D1.label;
	D.label.insert(D.label.begin(),D2.label.begin(),D2.label.end());

}

void sample(Dataset &D, Dataset &sample_dataset, int sample_size){
	if(D.data[0].size() <= sample_size){
		sample_dataset = D;
		return;
	}
	vector<int> idx(D.data[0].size());
	for(int i = 0; i < idx.size(); i++){
		idx[i] = i;
	}
	//srand(time(0));
	uint64_t millisec = duration_cast<milliseconds>(system_clock::now().time_since_epoch()).count();
	

	shuffle(idx.begin(),idx.end(),default_random_engine(millisec));

	sample_dataset.type = D.type;
	sample_dataset.remaining_attr = D.remaining_attr;
	sample_dataset.data.resize(D.data.size());
	for(int i = 0; i < sample_size; i++){
		for(int j = 0; j < D.data.size(); j++){
			sample_dataset.data[j].push_back(D.data[j][idx[i]]);
		}
		sample_dataset.label.push_back(D.label[idx[i]]);
	}

}

void partition_dataset(Dataset &D, Dataset &D1, Dataset &D2, int split_val, int feature){
	
	for(int i = 0; i < D.type.size(); i++){
		if(i == feature)continue;

		D1.type.push_back(D.type[i]);
		D1.remaining_attr.push_back(D.remaining_attr[i]);
		D2.type.push_back(D.type[i]);
		D2.remaining_attr.push_back(D.remaining_attr[i]);
		
	}
	D1.data.resize(D1.type.size());
	D2.data.resize(D1.type.size());
	if(D.type[feature] == NUMERICAL){
		for(int i = 0; i < D.data[0].size(); i++){
			if(D.data[feature][i] <= split_val){
				int counter = 0;
				for(int j = 0; j < D.data.size(); j++){
					if(j == feature)continue;
					D1.data[counter].push_back(D.data[j][i]);
					counter++;	
				}
				D1.label.push_back(D.label[i]);
				D1.indexes.push_back(D.indexes[i]);
			}else{
				int counter = 0;
				for(int j = 0; j < D.data.size(); j++){
					if(j == feature)continue;
					D2.data[counter].push_back(D.data[j][i]);
					counter++;
				}
				D2.label.push_back(D.label[i]);
				D2.indexes.push_back(D.indexes[i]);
			}
		}
	}
	
}


int _BuildTree(Dataset D, vector<Dataset> &Partitions, int max_depth, int depth,int father_pos, int direction, vector<vector<Node>> &tree, vector<vector<Node>> &expanded_tree, vector<Node> arr){
	Node new_node;
	Dataset D1,D2;
	
	

	int best_split_feature,best_split_value;
	
	int positive = 0;
	
	for(int i = 0; i < D.label.size(); i++){
		positive += D.label[i];
	}
	//printf("Purity : %lf \n", (float)positive/(float)D.label.size());
	
	if((float)positive/(float)D.label.size() <= 0.1 || (float)positive/(float)D.label.size() >= 0.9){
		counter++;
		new_node.split_value = -1;
		new_node.attr = -1;
		new_node.h = depth;
		new_node.pos = 2*father_pos+direction;
		new_node.direction = -1;
		//printf("Size : %d\n",D.data[0].size() );
		
		if((float)positive/(float)D.label.size() <= 0.1){
			new_node.classification = 0;
		}else{
			new_node.classification = 1;
		}
		//printf("RETURN\n");
		tree[depth].push_back(new_node);
		arr.push_back(new_node);
		expanded_tree.push_back(arr);
		Partitions.push_back(D);
		
		return 1;
	}
	if(max_depth == depth){
		r_counter++;
		//printf("@Size : %d\n",D.data[0].size() );
		new_node.split_value = -1;
		new_node.attr = -1;
		new_node.h = depth;
		new_node.pos = 2*father_pos+direction;
		new_node.direction = -1;
		
		if((float)positive/(float)D.label.size() <= 0.5){
			new_node.classification = 0;
		}else{
			new_node.classification = 1;
		}
		//printf("RETURN\n");
		tree[depth].push_back(new_node);

		arr.push_back(new_node);
		expanded_tree.push_back(arr);
		Partitions.push_back(D);
		//printf("MAX depth\n");
		return 1;
	}
	vector<float> Ginis;
	float gini = FindSplit(D,best_split_value,best_split_feature,Ginis);
	partition_dataset(D,D1,D2,best_split_value,best_split_feature);
	//printf("%d,%d\n",D1.data[0].size(),D2.data[0].size() );
	new_node.split_value = best_split_value;
	new_node.attr = D.remaining_attr[best_split_feature];
	new_node.h = depth;
	new_node.pos = 2*father_pos+direction;
	new_node.direction = 0;
	tree[depth].push_back(new_node);
	arr.push_back(new_node);
	int ch1 = _BuildTree(D1,Partitions,max_depth,depth+1,2*father_pos+direction,0,tree,expanded_tree,arr);
	arr[arr.size()-1].direction = 1;
	int ch2 = _BuildTree(D2,Partitions,max_depth,depth+1,2*father_pos+direction,1,tree,expanded_tree,arr);

	Dataset sD;
	int error = 0;
	for(int j = 0; j < 5; j++){
		sample(D,sD,500*(ch1+ch2));
		//printf("%d\n",D.data[0].size());
		int new_split,new_feature;
		vector<float> sampleGinis;
		FindSplit(sD,new_split,new_feature,sampleGinis);
		if(best_split_feature - new_feature != 0){
			error++;
			//printf("=======ERROR in Pos : %d,%d | Old split : %d,%d| New : %d,%d | %d\n",depth,2*father_pos+direction,best_split_value,best_split_feature,new_split,new_feature ,D.data[0].size() );
			//for(int i = 0; i < Ginis.size(); i++){
			//	printf("%lf,%lf\n",Ginis[i],sampleGinis[i] );
			//}
		}
	}
	//printf("======ERROR COUNTER : %lf,%d,%d\n",(float)error/5.0, ch1+ch2,D.data[0].size() );
	
	
	return ch1+ch2;
	//printf("Pos : %d,%d | Old split : %d,%d| New : %d,%d\n",depth,2*father_pos+direction,best_split_value,best_split_feature,new_split,new_feature );

}



vector<int> find_inactive_attributes(vector<Node> arr){
	vector<int> inactive_attributes;
	for(int i = 0; i < attr_num; i++){
		inactive_attributes.push_back(i);
	}
	for(int i = 0; i < arr.size()-1; i++){
		inactive_attributes.erase(std::remove(inactive_attributes.begin(), inactive_attributes.end(), arr[i].attr), inactive_attributes.end());
	}
	
	return inactive_attributes;
}



// Gini based tree
vector<vector<Node>> BuildTree(Dataset D, vector<Dataset> &Partitions, int max_depth){
	int best_split_value,best_split_feature;
	vector<vector<Node>> tree(max_depth+1);
	vector<vector<Node>> expanded_tree;
	vector<Node> arr;
	vector<Dataset> temp_partitions;
	_BuildTree(D,Partitions,max_depth,0,0,0,tree,expanded_tree,arr);

	/*	
	for(int i = 0; i < temp_partitions.size(); i++){
		Dataset temp_D;
		temp_D.data.resize(D.type.size());
		temp_D.
		for(int j = 0; j < temp_partitions[i].indexes.size(); j++){
			temp_D.type = D.type;
			temp_D.remaining_attr = D.remaining_attr;
			for(int k = 0; k < D.type.size(); k++){
				temp_D.data[k].push_back(temp_partitions[i].data[k][j]);
			}
			temp_D.label
		}
	}
	*/
	
	//printf("Max level : %d, %d\n", r_counter,counter);
	//printf("TREE : \n");
	int nodes = 0;
	
	for(int i = 0; i < max_depth; i++){
		for(int j = 0; j < tree[i].size(); j++){
	//		printf("(%d,%d,%d,%d),",tree[i][j].h,tree[i][j].pos,tree[i][j].attr,tree[i][j].split_value );
		}
		nodes += tree[i].size();
	//	printf("\n");
	}
	//printf("%d,%d\n",nodes,expanded_tree.size());

	int final_depth = 0;
	for(int i = 0; i < expanded_tree.size(); i++){
		
		if((expanded_tree[i].size()-1) > final_depth){
			final_depth = expanded_tree[i].size()-1;
		}
	}
	
	for(int i = 0; i < expanded_tree.size(); i++){
		if(expanded_tree[i].size() - 1 == final_depth){
			expanded_tree[i][expanded_tree[i].size() - 1].direction = -1;
			continue;
		}
		
		vector<int> inactive_attributes = find_inactive_attributes(expanded_tree[i]);
		expanded_tree[i][expanded_tree[i].size()-1].split_value = 0;
		expanded_tree[i][expanded_tree[i].size()-1].attr = inactive_attributes[0];
		int label = expanded_tree[i][expanded_tree[i].size()-1].classification;
		int h =  expanded_tree[i][expanded_tree[i].size()-1].h;
		int pos =  expanded_tree[i][expanded_tree[i].size()-1].pos;
		
		int size = expanded_tree[i].size();
		for(int j = 1; j < final_depth-size+2; j++){
			Node node;
			node.split_value = 0;
			node.attr = inactive_attributes[j];
			node.direction = -1;
			node.classification = label;
			node.h = h;
			node.pos = pos;
			expanded_tree[i].push_back(node);
		}
		
	}
	return expanded_tree;
}


void commit_partitions(partition_SNARK_data data, vector<vector<F>> tree, vector<vector<G1>> &commitments){
	vector<G1> C;
	vector<F> poly = convert2vector(data.permuted_data);
	MIPP_commit(poly,pp,C);
	
	commitments.push_back(C);
	poly = convert2vector(data.input_data);
	MIPP_commit(poly,pp,C);
	input_commit = C;
	commitments.push_back(C);
	
	poly = convert2vector(data.paths);
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	
	poly = convert2vector(data.paths_aux);
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	
	poly = convert2vector(data.diff_data);
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	
	poly = convert2vector(data.bit_vectors);
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);

	
	vector<F> forest_poly;
	for(int i = 0; i < tree.size(); i++){
		forest_poly.insert(forest_poly.end(),tree[i].begin(),tree[i].end());
	}

	MIPP_commit(forest_poly,pp,C);
	commitments.push_back(C);
	MIPP_commit(data.power_bits,pp,C);
	commitments.push_back(C);
	
}


void commit_histograms_leaves(histogram_SNARK_data data , vector<vector<G1>> &commitments){
	vector<G1> C;
	vector<F> poly;
	for(int i = 0; i < data.read_transcript.size(); i++){
		poly.insert(poly.end(),data.read_transcript[i].begin(),data.read_transcript[i].end());
	}

	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	//MIPP_commit_stream(data.write_transcript,data.write_transcript.size,pp,C);
	//commitments.push_back(C);

	// commit final histograms
	vector<F> hist_poly;
	for(int i = 0; i < data.final_memory.size(); i++){
		hist_poly.insert(hist_poly.end(), data.final_memory[i].begin(),data.final_memory[i].end());
	}
	MIPP_commit(hist_poly,pp,C);
	commitments.push_back(C);
	hist_poly.clear();
}

void open_histograms_leaves(histogram_SNARK_data data , vector<vector<G1>> &commitments){
	vector<G1> C;
	vector<F> poly;
	for(int i = 0; i < data.read_transcript.size(); i++){
		poly.insert(poly.end(),data.read_transcript[i].begin(),data.read_transcript[i].end());
	}
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[0]);
	
	poly = convert2vector(data.input_data);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,input_commit);
	//MIPP_open_stream(data.write_transcript,data.write_transcript.size,generate_randomness((int)log2(data.write_transcript.size),F(321)),pp,commitments[0]);
	
	vector<F> hist_poly;
	for(int i = 0; i < data.final_memory.size(); i++){
		hist_poly.insert(hist_poly.end(), data.final_memory[i].begin(),data.final_memory[i].end());
	}
	
	MIPP_open(hist_poly,generate_randomness((int)log2(hist_poly.size()),F(321)),pp,commitments[1]);
	
	hist_poly.clear();
	
}


void commit_histograms_nodes(nodes_histogram_SNARK_data data , vector<vector<G1>> &commitments){
	vector<G1> C;
	vector<F> poly;
	for(int i = 0; i < data.node_histograms.size(); i++){
		for(int j = 0; j < data.node_histograms[i].size(); j++){
			poly.insert(poly.end(), data.node_histograms[i][j].begin(),data.node_histograms[i][j].end());
		}
	}
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	//vector<vector<int>> node_index_matrix,leaf_index_matrix,leaf_matrix;
	poly.clear();
	for(int i = 0; i < data.node_index_matrix.size(); i++){
		for(int j = 0; j < data.node_index_matrix[i].size(); j++){
			poly.push_back(F(data.node_index_matrix[i][j]));
		}
	}
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	poly.clear();
	for(int i = 0; i < data.leaf_index_matrix.size(); i++){
		for(int j = 0; j < data.leaf_index_matrix[i].size(); j++){
			poly.push_back(F(data.leaf_index_matrix[i][j]));
		}
	}
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	poly.clear();
	for(int i = 0; i < data.leaf_matrix.size(); i++){
		for(int j = 0; j < data.leaf_matrix[i].size(); j++){
			poly.push_back(F(data.leaf_matrix[i][j]));
		}
	}
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	poly = data.node_coeff;
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	poly = data.leaf_coeff;
	MIPP_commit(poly,pp,C);
	commitments.push_back(C);
	
}


void open_histograms_nodes(nodes_histogram_SNARK_data data , vector<vector<G1>> &commitments){
	vector<F> poly;
	for(int i = 0; i < data.node_histograms.size(); i++){
		for(int j = 0; j < data.node_histograms[i].size(); j++){
			poly.insert(poly.end(), data.node_histograms[i][j].begin(),data.node_histograms[i][j].end());
		}
	}
	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[0]);
	
	//vector<vector<int>> node_index_matrix,leaf_index_matrix,leaf_matrix;
	poly.clear();
	for(int i = 0; i < data.node_index_matrix.size(); i++){
		for(int j = 0; j < data.node_index_matrix[i].size(); j++){
			poly.push_back(F(data.node_index_matrix[i][j]));
		}
	}
	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[1]);
	poly.clear();
	for(int i = 0; i < data.leaf_index_matrix.size(); i++){
		for(int j = 0; j < data.leaf_index_matrix[i].size(); j++){
			poly.push_back(F(data.leaf_index_matrix[i][j]));
		}
	}
	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[2]);
	poly.clear();
	for(int i = 0; i < data.leaf_matrix.size(); i++){
		for(int j = 0; j < data.leaf_matrix[i].size(); j++){
			poly.push_back(F(data.leaf_matrix[i][j]));
		}
	}
	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[3]);
	poly = data.node_coeff;
	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[4]);
	poly = data.leaf_coeff;

	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[5]);
		
}

void open_partitions(partition_SNARK_data data,vector<vector<F>> tree , vector<vector<G1>> commitments){
	
	vector<F> poly = convert2vector(data.permuted_data);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[0]);
	poly = convert2vector(data.input_data);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[1]);
	poly = convert2vector(data.paths);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[2]);
	poly = convert2vector(data.paths_aux);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[3]);
	poly = convert2vector(data.diff_data);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[4]);
	poly = convert2vector(data.bit_vectors);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(321)),pp,commitments[5]);
	
	vector<F> forest_poly;
	for(int i = 0; i < tree.size(); i++){
		forest_poly.insert(forest_poly.end(),tree[i].begin(),tree[i].end());
	}
	
	MIPP_open(forest_poly,generate_randomness((int)log2(forest_poly.size()),F(321)),pp,commitments[6]);
	vector<F> bits = data.power_bits;
	
	MIPP_open(bits,generate_randomness((int)log2(bits.size()),F(321)),pp,commitments[7]);
	printf("P : %lf, V : %lf, L : %lf\n",pp.prove_time,pp.verification_time,(double)pp.proof_size/1024.0);
	pp.prove_time = 0.0;
	pp.verification_time = 0.0;
	pp.proof_size =0;
}




// Assume the following vetors: [inputs],[permuted_inputs],[individual paths],[paths],[frequency],[bits]
// We need two permutation checks: 1) Between [inputs] and [permuted_inputs]/ 2) [individual paths],[paths],[frequency]
// Apply inference proof using [permuted_inputs],[individual paths],[bits]
// Check path consistency : The difference between the previous and the current pos of [individual paths] will be >=0 

partition_SNARK_proof prove_correct_partitions(partition_SNARK_data data, Dataset &D, vector<vector<F>> Tree,int max_depth){
	partition_SNARK_proof P;
	vector<F> randomness = generate_randomness(10,F(0));
	
	// Permutation checks 
	// Use Matrix-vector multiplication to compress dataset and individual paths
	clock_t t2,t1;
	t1 = clock();
	printf("Data size : %d,%d\n",data.input_data.size(),data.input_data[0].size() );
	pad_matrix(data.input_data);
	
	vector<F> compressed_tree(Tree.size(),F(0));
	vector<F> compressed_paths(D.data[0].size(),F(0));
		
	F commitment;commitment.setByCSPRNG();
	P.commitment = commitment;
	vector<F> compress_vector = generate_randomness(D.data.size()+1,commitment);
	P.compress_vector = compress_vector;
	vector<F> tree_compress_vector = generate_randomness(4*max_depth+2,compress_vector[compress_vector.size()-1]);
	P.tree_compress_vector = tree_compress_vector;
	F c = mimc_hash(tree_compress_vector[tree_compress_vector.size()-1],F(1));

	F check1= F(1),check2 = F(1);

	for(int i = 0; i < Tree.size(); i++){
		for(int j = 0; j < Tree[i].size(); j++){
			compressed_tree[i] += Tree[i][j]*tree_compress_vector[j];
		}
		compressed_tree[i] += F(1);
		
	}
	for(int i = 0; i < data.paths.size(); i++){
		int j = 0;
		for(j = 0; j < data.paths[i].size(); j++){
			compressed_paths[i] += data.paths[i][j]*tree_compress_vector[j];
		}
		compressed_paths[i] += data.paths_aux[i][0]*tree_compress_vector[j] + data.paths_aux[i][1]*tree_compress_vector[j+1];
		compressed_paths[i]+=F(1);
	}
	
	pad_vector_with_num(compressed_paths,F(1));
	pad_vector_with_num(compressed_tree,F(1));
	

	vector<F> gkr_data;
	
	
	pad_vector(compress_vector);
	
	P.P1 = partition_sumcheck_1(data.input_data,data.permuted_data,compress_vector,c,c);


	vector<F> powers;
	for(int i = 0; i < compressed_tree.size(); i++){
		powers.push_back(compressed_tree[i]);
		F prev = compressed_tree[i];
		for(int j = 1; j < 32; j++){
			powers.push_back(prev*prev);
			prev = prev*prev;
		}
	}


	vector<vector<F>> paths = data.paths;
	for(int i = 0; i < paths.size(); i++){
		paths[i].push_back(data.paths_aux[i][0]);
		paths[i].push_back(data.paths_aux[i][1]);			
	}
	vector<vector<F>> tree = Tree; 
	pad_matrix(tree);
	pad_matrix(paths);
	pad_vector(tree_compress_vector);
	
	P.P2 = partition_sumcheck_2(compressed_tree, compressed_paths, powers, data.power_bits, paths, tree, tree_compress_vector,c,P.P1.final_rand);
	
	P.P3 = partition_sumcheck_3(data.paths, data.permuted_data, data.diff_data,data.bit_vectors,P.P2.final_rand,max_depth);
	
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	// Phase 2: Batch inference

	//P.final_rand = P.GKR_proof1.final_rand;
	// check path consistency
	//_prove_binary(data.path_diff);
	return P;
}




histogram_SNARK_proof prove_histograms(histogram_SNARK_data data, int Attr, F previous_r){
	histogram_SNARK_proof P;
	
	F commitments;commitments.setByCSPRNG();
	P.commitments = commitments;
	P.previous_r = previous_r;
	F rand = mimc_hash(previous_r,commitments);

	clock_t t1,t2;
	t1 = clock();

	vector<F> random_vector = generate_randomness(8,rand);
	previous_r = random_vector[random_vector.size()-1];
	vector<F> compressed_final(data.memory_init.size(),F(0)),compressed_init(data.memory_init.size(),F(0));
	vector<F> compressed_write( data.write_transcript.size(),F(0));
	vector<F> compressed_read(data.write_transcript.size(),F(0));
	vector<F> compressed_write_tr(data.write_transcript.size(),F(0));
	vector<F> compressed_read_tr(data.write_transcript.size(),F(0));
	vector<F> compressed_final_mem(data.memory_init.size(),F(0));
	
	for(int i = 0; i < data.memory_init.size(); i++){
		for(int j = 0; j < 5; j++){
			compressed_init[i] += data.memory_init[i][j]*random_vector[j];
			compressed_final[i] += data.final_memory[i][j]*random_vector[j];
		}
		compressed_init[i]+= F(1);
		compressed_final[i]+= F(1);
		
	}
	for(int i = 0; i < data.read_transcript.size(); i++){
		for(int j = 0; j < 5; j++){
			compressed_write[i] += random_vector[j]*data.write_transcript[i][j];
			compressed_read[i] += random_vector[j]*data.read_transcript[i][j];
		}
		compressed_write[i]+=F(1);
		compressed_read[i]+=F(1);
	}

	F check1 = F(1),check2 = F(1);
	for(int i = 0; i < compressed_write.size(); i++){
		check2 = check2*compressed_read[i];
		check1 = check1*compressed_write[i];
	}

	vector<F> read_data,write_data,input_data,input_metadata;
	for(int i = 0; i < data.read_transcript.size(); i++){
		read_data.insert(read_data.end(),data.read_transcript[i].begin(),data.read_transcript[i].end());
	}

	for(int i = 0; i < data.write_transcript.size(); i++){
		write_data.insert(write_data.end(),data.write_transcript[i].begin(),data.write_transcript[i].end());		
	}
	for(int i = 0; i < data.input_data.size(); i++){
		for(int j = 0; j < 2*Attr; j++){
			input_data.push_back(data.input_data[i][j]);
		}
		for(int j = 2*Attr; j < data.input_data[i].size(); j++){
			input_metadata.push_back(data.input_data[i][j]);
		}
	}
	
	//gkr_data.insert(gkr_data.end(),compressed_read.begin(),compressed_read.end());
	//gkr_data.insert(gkr_data.end(),compressed_write.begin(),compressed_write.end());
	
	P.mP1 = leaves_sumcheck_1(compressed_read,compressed_write,previous_r);
	
	vector<vector<F>> padded_read_transcript = data.read_transcript;
	vector<vector<F>> padded_write_transcript = data.write_transcript;
	vector<vector<F>> padded_histograms = data.final_memory;
	pad_matrix(padded_read_transcript);
	pad_matrix(padded_write_transcript);
	pad_vector(random_vector);

	if((F(1)-P.mP1.global_randomness[0])*P.mP1.partial_eval[0] + P.mP1.global_randomness[0]*P.mP1.partial_eval[1] != P.mP1.final_eval){
		printf("Error\n");
		exit(-1);
	}

	rand = mimc_hash(P.mP1.individual_randomness[P.mP1.individual_randomness.size()-1],P.mP1.partial_eval[0]);
	rand = mimc_hash(rand,P.mP1.partial_eval[1]);

	P.sP1 = _prove_matrix2vector(_transpose(padded_read_transcript),random_vector,P.mP1.individual_randomness,P.mP1.partial_eval[0]-F(1),rand);
	
	P.sP2 = _prove_matrix2vector(_transpose(padded_write_transcript),random_vector,P.mP1.individual_randomness,P.mP1.partial_eval[1]-F(1),P.sP1.final_rand);
	

	P.mP2 = leaves_sumcheck_1(compressed_init,compressed_final,P.sP2.final_rand);
	if(P.mP1.output[0]*P.mP2.output[1] != P.mP2.output[0]*P.mP1.output[1]){
		printf("Error in histogram proof 1\n");
		exit(-1);
	}
	rand = mimc_hash(P.mP2.final_r[P.mP2.final_r.size()-1],P.mP2.partial_eval[1]);
	pad_matrix(padded_histograms);
	P.sP3 = _prove_matrix2vector(_transpose(padded_histograms),random_vector,P.mP2.individual_randomness,P.mP2.partial_eval[1]-F(1),rand);	



	
	vector<F> r1,r2,beta1,beta2;

	r1 = P.sP1.randomness[0];
	for(int i = 0; i < P.mP1.individual_randomness.size(); i++){
		r1.push_back(P.mP1.individual_randomness[i]);
	}

	r2 = P.sP2.randomness[0];
	for(int i = 0; i < P.mP1.individual_randomness.size(); i++){
		r2.push_back(P.mP1.individual_randomness[i]);
	}
	precompute_beta(r1,beta1);
	precompute_beta(r2,beta2);

	P.P1 = leaves_sumcheck_2(input_data,input_metadata,read_data,write_data,r2,beta1,beta2,P.sP1.vr[0],P.sP2.vr[0],P.sP3.final_rand);
	P.final_rand = P.P1.final_rand;
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	return P;

}

void add_histograms(vector<vector<vector<F>>> &node_histograms, vector<vector<F>> hist1, vector<vector<F>> hist2){
	vector<vector<F>> hist(hist1.size());
	for(int i = 0; i < hist.size(); i++){
		hist[i].resize(hist1[0].size());
		for(int j = 0; j < hist[i].size(); j++){
			hist[i][j] = hist1[i][j] + hist2[i][j];
		}
	}
	node_histograms.push_back(hist);
}


void compute_compressed_hist(vector<F> &compressed_hist, vector<vector<vector<F>>> Hist, vector<F> compress_vector){
	int counter;
	for(int i = 0; i < compressed_hist.size(); i++){
		counter = 0;
		for(int j = 0; j < Hist[i].size(); j++){
			for(int k = 0; k < Hist[i][j].size(); k++){
				compressed_hist[i] += compress_vector[counter]*Hist[i][j][k];
				counter++;
			}
		}
	}
}

vector<vector<F>> padded_hist(vector<vector<vector<F>>> Hist){
	vector<vector<F>> matrix;
	for(int i = 0; i < Hist.size(); i++){
		vector<F> vec;
		for(int j = 0; j < Hist[i].size(); j++){
			vec.insert(vec.end(),Hist[i][j].begin(),Hist[i][j].end());
		}
		matrix.push_back(vec);
	}
	pad_matrix(matrix);
	return _transpose(matrix);
}


void serialize(vector<vector<vector<F>>> &data, vector<F> &serialized_data){
	for(int i = 0; i < data.size(); i++){
		for(int j = 0; j < data[i].size(); j++){
			serialized_data.insert(serialized_data.end(),data[i][j].begin(),data[i][j].end());
		}
	}
}


// make a circuit that takes as input the 1) leaf coefficients, the leaf histograms,
// the 2) node coefficients, the node histograms
// 3) a non-determenistic witness containing children histograms with their coefficients 
nodes_histogram_SNARK_proof prove_node_histograms(nodes_histogram_SNARK_data data, F previous_r){
	vector<vector<F>> witness_hist;
	vector<F> witness_coeff;
	vector<F> randomness(1);
	nodes_histogram_SNARK_proof P;

	if(_commitment_test){
		vector<vector<G1>> commitments;
		commit_histograms_nodes(data,commitments);
		open_histograms_nodes(data,commitments);
		total_p += pp.prove_time;
		total_v += pp.verification_time;
		total_s += (double)pp.proof_size/1024.0;

		pp.prove_time = 0.0;
		pp.verification_time = 0.0;
		pp.proof_size =0;

		return P;
	}
	clock_t t1,t2;
	t1 = clock();
	
	
	for(int i = data.leaf_matrix.size()-1; i > 0; i--){
		for(int j = 0; j < data.leaf_matrix[i].size(); j+=2){
			
			if(data.leaf_matrix[i][j] != -1){
				vector<vector<F>> H;
				vector<F> H_v;
				
				witness_coeff.push_back(F(i));
				witness_coeff.push_back(F(j));
				witness_coeff.push_back(F(i));
				witness_coeff.push_back(F(j+1));
				
				if(data.leaf_index_matrix[i][j] != -1){
					H = data.leaf_histograms[data.leaf_index_matrix[i][j]];
				}else{
					H = data.node_histograms[data.node_index_matrix[i][j]];
				}
				for(int k = 0; k < H.size(); k++){
					H_v.insert(H_v.end(),H[k].begin(),H[k].end());
				}
				witness_hist.push_back(H_v);
				H_v.clear();
				if(data.leaf_index_matrix[i][j+1] != -1){
					H = data.leaf_histograms[data.leaf_index_matrix[i][j+1]];
				}else{
					H = data.node_histograms[data.node_index_matrix[i][j+1]];
				}
				for(int k = 0; k < H.size(); k++){
					H_v.insert(H_v.end(),H[k].begin(),H[k].end());
				}
				
				witness_hist.push_back(H_v);
			}
		}
	}
	
	F two_inv = F(2);
	two_inv.inv(two_inv,two_inv);
	vector<vector<F>> out_hist(witness_hist.size()/2);	
	
	for(int i = 0; i < out_hist.size(); i++){
		vector<F> hist_aggr(witness_hist[i].size());
		
		for(int j = 0; j < hist_aggr.size(); j++){
			hist_aggr[j] = witness_hist[2*i][j] + witness_hist[2*i+1][j];
		}
		out_hist[i] = hist_aggr;
	}

	int witness_size = witness_hist[0].size();
	if(1ULL<<((int)log2(witness_size)) != witness_hist[0].size()){
		witness_size = 1ULL<<((int)log2(witness_size)+1);
	}


	P.commitment.setByCSPRNG();P.previous_r = previous_r;
	F rand = mimc_hash(previous_r,P.commitment);
	
	P.r = generate_randomness((int)log2(witness_size),rand);
	vector<F> compress_vector;
	precompute_beta(P.r,compress_vector);
	vector<F> compressed_leaf_hist(data.leaf_histograms.size(),F(0)),compressed_node_hist(data.node_histograms.size(),F(0));
	vector<F> compressed_witness(witness_hist.size(),F(0)),compressed_out(witness_hist.size()/2,F(0));
	compute_compressed_hist(compressed_leaf_hist,data.leaf_histograms,compress_vector);
	compute_compressed_hist(compressed_node_hist,data.node_histograms,compress_vector);
	
	for(int i = 0; i < witness_hist.size()/2; i++){
		for(int j = 0; j < witness_hist[i].size(); j++){
			compressed_witness[2*i] += compress_vector[j]*witness_hist[2*i][j];
			compressed_witness[2*i+1] += compress_vector[j]*witness_hist[2*i+1][j];
			compressed_out[i] += compress_vector[j]*out_hist[i][j];
		}
	}

	vector<F> gkr_data;

	F a = mimc_hash(P.r[P.r.size()-1],F(0));
	F b = mimc_hash(a,F(1));
	F c = mimc_hash(b,F(2));
	F r = mimc_hash(c,F(3));
	rand = mimc_hash(r,F(0));

	pad_vector(data.leaf_coeff);
	pad_vector(data.node_coeff);
	pad_vector(witness_coeff);
	pad_vector(compressed_leaf_hist);
	pad_vector(compressed_node_hist);
	pad_vector(compressed_out);
	pad_vector(compressed_witness);
	
	gkr_data.insert(gkr_data.end(),witness_coeff.begin(),witness_coeff.end());
	gkr_data.insert(gkr_data.end(),data.node_coeff.begin(),data.node_coeff.end());
	gkr_data.insert(gkr_data.end(),data.leaf_coeff.begin(),data.leaf_coeff.end());
	gkr_data.insert(gkr_data.end(),compressed_witness.begin(),compressed_witness.end());
	gkr_data.insert(gkr_data.end(),compressed_node_hist.begin(),compressed_node_hist.end());
	gkr_data.insert(gkr_data.end(),compressed_out.begin(),compressed_out.end());
	gkr_data.insert(gkr_data.end(),compressed_leaf_hist.begin(),compressed_leaf_hist.end());

	gkr_data.push_back(a);
	gkr_data.push_back(b);
	gkr_data.push_back(c);
	gkr_data.push_back(r);
	gkr_data.push_back(two_inv);
	gkr_data.push_back(F(1));
	
	// Compute arr1 = a*leaf_coef[2*i]+b*leaf_coef[2*i+1] + c*compressed_leaf_hist[i] -c
	
	// Prove consistency of compressed histograms and tree coefficients
	randomness[0] = rand;
	P.GKR_proof1 = node_histogram_consistency(gkr_data,randomness,data.leaf_histograms.size(),data.node_histograms.size());
	vector<F> x_leaf,x_node,x_witness,x_compressed_leaf,x_compressed_node,x_compressed_witness,x_compressed_out;
	vector<F> x = P.GKR_proof1.randomness[P.GKR_proof1.randomness.size()-1];
	if(P.GKR_proof1.q_poly[0].eval(0) + P.GKR_proof1.q_poly[0].eval(1) != F(0)){
		printf("Error in nodes histograms 1\n");
		exit(-1);
	}

	for(int i = 0; i < (int)log2(witness_coeff.size()); i++){x_witness.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(data.node_coeff.size()); i++){x_node.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(data.leaf_coeff.size()); i++){x_leaf.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(compressed_witness.size()); i++){x_compressed_witness.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(compressed_node_hist.size()); i++){x_compressed_node.push_back(x[i]);}
	for(int i = 0 ;i < (int)log2(compressed_leaf_hist.size()); i++){x_compressed_leaf.push_back(x[i]);}

	P.wit_eval = evaluate_vector(witness_coeff,x_witness);
	P.node_eval = evaluate_vector(data.node_coeff,x_node);
	P.leaf_eval = evaluate_vector(data.leaf_coeff,x_leaf);
	P.comp_wit_eval = evaluate_vector(compressed_witness,x_compressed_witness);
	P.comp_node_eval = evaluate_vector(compressed_node_hist,x_compressed_node);
	P.comp_out_eval = evaluate_vector(compressed_out,x_compressed_node);
	P.comp_leaf_eval = evaluate_vector(compressed_leaf_hist,x_compressed_leaf);
	printf("Compress vector : %d\n",compress_vector.size() );
	// Prove that the histograms compressed correctly
	
	rand = mimc_hash(P.GKR_proof1.final_rand,P.wit_eval);
	rand = mimc_hash(rand,P.node_eval);
	rand = mimc_hash(rand,P.leaf_eval);
	rand = mimc_hash(rand,P.comp_wit_eval);
	rand = mimc_hash(rand,P.comp_node_eval);
	rand = mimc_hash(rand,P.comp_out_eval);
	rand = mimc_hash(rand,P.comp_leaf_eval);


	int wit_row_size = witness_hist[0].size();
	pad_matrix(witness_hist);
	

	
	pad_matrix(out_hist);

	
	P.sP1 = _prove_matrix2vector(_transpose(witness_hist),compress_vector,x_compressed_witness,P.comp_wit_eval,rand);
	P.sP2 = _prove_matrix2vector(_transpose(out_hist),compress_vector,x_compressed_node,P.comp_out_eval,P.sP1.final_rand);
	int leaves = data.leaf_histograms.size();
	int nodes = data.node_histograms.size();
	P.sP3 = _prove_matrix2vector(padded_hist(data.leaf_histograms),compress_vector,x_compressed_leaf,P.comp_leaf_eval,P.sP2.final_rand);
	P.sP4 = _prove_matrix2vector(padded_hist(data.node_histograms),compress_vector,x_compressed_node,P.comp_node_eval,P.sP3.final_rand);
	

	//prove_compression(data,witness_hist,out_hist,compressed_leaf_hist,compressed_node_hist,compressed_witness,compressed_out,compress_vector);
	// Prove that the out histograms computed correctly
	gkr_data.clear();
	for(int i = 0; i < witness_hist.size(); i++){
		gkr_data.insert(gkr_data.end(),witness_hist[i].begin(),witness_hist[i].end());
	}
	
	randomness.clear();
	randomness = P.sP2.randomness[0];
	randomness.insert(randomness.end(),x_compressed_node.begin(),x_compressed_node.end());
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	
	P.GKR_proof2 = prove_node_sum(gkr_data,randomness,P.sP4.final_rand,witness_hist[0].size(),witness_hist.size(),nodes);
	vector<F> out_hist_vec = convert2vector(out_hist);
	

	if(P.GKR_proof2.q_poly[0].eval(0) + P.GKR_proof2.q_poly[0].eval(1) != P.sP2.vr[0]){
		printf("Error in nodes histograms 2\n" );
		exit(-1);
	}
	P.final_rand = P.GKR_proof2.final_rand;
	// need to reduce witness_hist
	
	return P;
}

void commit_split_data(split_SNARK_data data){
	
	vector<G1> C;
	
	
	vector<F> poly;
	serialize(data.gini_inputs,poly);
	pad_vector(poly);
	MIPP_commit(poly,pp,C);

	cached_commitments.push_back(C);
	poly.clear();
	serialize(data.quotients,poly);
	MIPP_commit(poly,pp,C);
	cached_commitments.push_back(C);
	poly.clear();
	serialize(data.quotients,poly);
	MIPP_commit(poly,pp,C);
	cached_commitments.push_back(C);
	poly.clear();
	serialize(data.quotients,poly);
	MIPP_commit(poly,pp,C);
	cached_commitments.push_back(C);

	
}

void open_split_data(split_SNARK_data data){
	vector<G1> C;
	
	
	vector<F> poly;
	serialize(data.gini_inputs,poly);
	pad_vector(poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(31)),pp,cached_commitments[0]);
	poly.clear();
	serialize(data.quotients,poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(31)),pp,cached_commitments[1]);
	poly.clear();
	serialize(data.quotients,poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(31)),pp,cached_commitments[2]);
	poly.clear();
	serialize(data.quotients,poly);
	MIPP_open(poly,generate_randomness((int)log2(poly.size()),F(31)),pp,cached_commitments[3]);
}
split_SNARK_proof prove_split(split_SNARK_data data, F previous_r){
	

	vector<F> gkr_data;
	vector<F> range_proof_vector;
	vector<vector<vector<F>>> subtracted_ginis(data.nodes);
	vector<F> prev_x;
	F commitments; commitments.setByCSPRNG();
	split_SNARK_proof P;
	

	P.previous_r = previous_r;
	P.commitment = commitments;
	F rand = mimc_hash(previous_r,commitments);
	// Check the correctness of best splits
	clock_t t1,t2;
	t1 = clock();
	// Check if the best gini contents are the maximum elelemts
	
	for(int i = 0; i < data.ginis.size(); i++){
		subtracted_ginis[i].resize(data.attr);
		for(int j = 0; j < data.ginis[i].size(); j++){
			subtracted_ginis[i][j].resize(bin_size);
			for(int k = 0; k < data.ginis[i][j].size(); k++){
				subtracted_ginis[i][j][k] = data.ginis[i][j][k] - data.best_gini[i][j];// +F(1);
				char buff[256];
				if(subtracted_ginis[i][j][k].getStr(buff,256,2) > 128){
					printf("Error : %d,%d,%d\n",i,j,k );
				}
			}
		}
	}

	//exit(-1);
	serialize(subtracted_ginis,range_proof_vector);
	if(_commitment_test){
		printf("Commit forest\n");
		commit_split_data(data);
		printf("Open forest\n");
		open_split_data(data);		
		printf("Finis\n");
		commitments.clear();
		lookup_range_proof(range_proof_vector,rand, 32);
		serialize(data.remainders,range_proof_vector);
		pad_vector(range_proof_vector);
		lookup_range_proof(range_proof_vector,rand, 64);
		total_p += pp.prove_time;
		total_v += pp.verification_time;
		total_s += (double)pp.proof_size/1024.0;

		pp.prove_time = 0.0;
		pp.verification_time = 0.0;
		pp.proof_size =0;

		return P;
	}
	vector<F> r = generate_randomness((int)log2(range_proof_vector.size()),F(32));
	printf("OK\n");
	_prove_bit_decomposition(prepare_bit_vector(range_proof_vector,32),r,evaluate_vector(range_proof_vector,r),rand,32);
	//P.lP1 = lookup_range_proof(range_proof_vector,rand, 32);
	vector<F>().swap(range_proof_vector);
	//range_proof_vector.clear();
	serialize(data.ginis,range_proof_vector);
	pad_vector(range_proof_vector);
	vector<F> x1 =generate_randomness((int)log2(range_proof_vector.size()),F(232));
	P.ginis_eval1 = evaluate_vector(range_proof_vector,x1);
	range_proof_vector.clear();

	vector<F> temp = convert2vector(data.best_gini);
	pad_vector(temp);
	P.best_gini_eval1 =  evaluate_vector(temp,x1);
	rand = mimc_hash(rand,P.best_gini_eval1);

	//if(P.lP1.final_eval != -P.best_gini_eval1 + P.ginis_eval1){
	//	printf("Error in split 1\n");
	//	exit(-1);
	//}

	// Check if the maximum elements belong to ginis
	vector<vector<F>> trees;
	for(int i = 0; i < data.nodes; i++){
		for(int j = 0; j < data.attr; j++){
			trees.push_back(subtracted_ginis[i][j]);
		}
	}
	
	P.mP1 = prove_multiplication_tree(trees,rand,prev_x);
	
	vector<F> x = P.mP1.individual_randomness;
	rand = P.mP1.individual_randomness[P.mP1.individual_randomness.size()-1];
	for(int i = 0; i < P.mP1.global_randomness.size(); i++){
		x.push_back(P.mP1.global_randomness[i]);
	}
	serialize(data.ginis,range_proof_vector);
	pad_vector(range_proof_vector);
	P.ginis_eval2 = evaluate_vector(range_proof_vector,x);
	range_proof_vector.clear();
	temp = convert2vector(data.best_gini);
	pad_vector(temp);
	P.best_gini_eval2 =  evaluate_vector(temp,x);
	rand = mimc_hash(rand,P.ginis_eval2);
	rand = mimc_hash(rand,P.best_gini_eval2);
	if(P.mP1.final_eval != P.ginis_eval2- P.best_gini_eval2){
		printf("Error in split 2\n");
	}


	// Check the correctness of the division.
	// First check that the remainders are in the correct domain
	range_proof_vector.clear();
	serialize(data.remainders,range_proof_vector);
	pad_vector(range_proof_vector);
	
	r = generate_randomness((int)log2(range_proof_vector.size()),F(3432));
	F final_eval = evaluate_vector(range_proof_vector,r);
	_prove_bit_decomposition(prepare_bit_vector(range_proof_vector,64),r,final_eval,rand,64);
	
	//P.lP2 = lookup_range_proof(range_proof_vector,rand, 64);

	// Then check the the correct computation of remainders
	
	// Cut it in two parts for efficiency 
	serialize(data.inverses,gkr_data);
	serialize(data.quotients,gkr_data);
	serialize(data.divisors,gkr_data);
	serialize(data.dividents,gkr_data);
	serialize(data.N,gkr_data);
	//gkr_data.push_back(F(1));
	// First part
	//prove_gini_check_phase1(gkr_data, randomness, data.nodes, data.attr, bin_size);
	
	// Give input the lookup evaluation point
	P.P1 = gini_sumcheck_1(gkr_data, F(3234),r, final_eval, data.nodes, data.attr, bin_size);
	// get evaluations of quoteints 


	gkr_data.clear();
	serialize(data.N,gkr_data);
	serialize(data.gini_inputs,gkr_data);
	serialize(data.divisors,gkr_data);
	serialize(data.dividents,gkr_data);

	P.P2 = gini_sumcheck_2(gkr_data,P.P1.final_rand,P.P1.tP2.randomness[0],P.P1.tP1.randomness[0],P.P1.tP2.vr[1],P.P1.tP1.vr[1], data.nodes, data.attr, bin_size);


	gkr_data.clear();
	serialize(data.sums,gkr_data);
	serialize(data.gini_inputs,gkr_data);
	serialize(data.node_histograms,gkr_data);
	
	// Second part
	vector<F> randomness(1);
	randomness[0] = P.P2.sP2.final_rand;
	t2 = clock();
	proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
	P.GKR_proof1 = prove_gini_check_phase2(gkr_data, randomness, data.nodes, data.attr, bin_size);
	if(P.GKR_proof1.q_poly[0].eval(F(0)) + P.GKR_proof1.q_poly[0].eval(F(1)) != F(0)){
		printf("Error in split 3\n");
		//exit(-1);
	}
	return P;
}

split_SNARK_data get_split_transcript(vector<vector<vector<F>>> node_histograms){
	printf("\n======= SPLIT Proof =======\n");
	split_SNARK_data data;
	int nodes = node_histograms.size();
	int attr = node_histograms[0].size();
	vector<vector<vector<F>>> gini_inputs(nodes);
	vector<vector<vector<F>>> sums(nodes);
	vector<vector<vector<float>>> fginis(nodes);
	vector<vector<vector<F>>> N(nodes),dividents(nodes),divisors(nodes),quotients(nodes),inverses(nodes);
	// For debug purposes
	vector<vector<vector<F>>> remainders(nodes);
	vector<vector<F>> best_gini(nodes);
	vector<vector<float>> _best_gini(nodes);
	vector<vector<int>> _best_pos(nodes);

	for(int i = 0; i < nodes; i++){
		divisors[i].resize(attr);
		dividents[i].resize(attr);
		quotients[i].resize(attr);
		inverses[i].resize(attr);
		remainders[i].resize(attr);
		fginis[i].resize(attr);
		_best_gini[i].resize(attr);
		best_gini[i].resize(attr);
		_best_pos[i].resize(attr);
		N[i].resize(attr);
		for(int j = 0; j < attr; j++){
			dividents[i][j].resize(2*bin_size);
			divisors[i][j].resize(2*bin_size);
			quotients[i][j].resize(2*bin_size);
			inverses[i][j].resize(2*bin_size);
			remainders[i][j].resize(2*bin_size);
			N[i][j].resize(2*bin_size);
			fginis[i][j].resize(bin_size);
		}
	}

	

	for(int i = 0; i < nodes; i++){
		sums[i].resize(attr);
		
		for(int j = 0; j < attr; j++){
			sums[i][j].resize(2,F(0));
			for(int k = 0; k < node_histograms[i][j].size(); k+=2){
				sums[i][j][0] += node_histograms[i][j][k];
				sums[i][j][1] += node_histograms[i][j][k+1];
			}
		}
	}
	for(int i = 0; i < nodes; i++){
		gini_inputs[i].resize(attr);
		for(int j = 0; j < attr; j++){
			gini_inputs[i][j].resize(4*(bin_size));
			gini_inputs[i][j][0] = node_histograms[i][j][0];
			gini_inputs[i][j][1] = node_histograms[i][j][1];
			gini_inputs[i][j][2] = sums[i][j][0] - node_histograms[i][j][0];
			gini_inputs[i][j][3] = sums[i][j][1] - node_histograms[i][j][1];
			for(int k = 1; k < bin_size; k++){
				gini_inputs[i][j][4*k] = node_histograms[i][j][2*k] + gini_inputs[i][j][4*(k-1)];
				gini_inputs[i][j][4*k+1] = node_histograms[i][j][2*k+1] + gini_inputs[i][j][4*(k-1)+1];
				gini_inputs[i][j][4*k+2] = gini_inputs[i][j][4*(k-1)+2] - node_histograms[i][j][2*k];
				gini_inputs[i][j][4*k+3] = gini_inputs[i][j][4*(k-1)+3] - node_histograms[i][j][2*k+1];
			
			}

		}
	}

	for(int i = 0; i < nodes; i++){
		fginis[i].resize(attr);
		for(int j = 0; j < attr; j++){
			fginis[i][j].resize(bin_size);
			float min1 = 100,min2 = 100;
			int idx1,idx2;
			for(int k = 0; k < bin_size; k++){
				// Compute 
				char num_str[64];
				int N11,N10,N21,N20;
				gini_inputs[i][j][4*k].getStr(num_str,64,10);
				N11 = stoi(num_str);
				gini_inputs[i][j][4*k+1].getStr(num_str,64,10);
				N10 = stoi(num_str);
				gini_inputs[i][j][4*k+2].getStr(num_str,64,10);
				N21 = stoi(num_str);
				gini_inputs[i][j][4*k+3].getStr(num_str,64,10);
				N20 = stoi(num_str);
				float N1 = (float)(N10+N11);
				float N2 = (float)(N20+N21);

				float _G1 = ((float)N11/(float)N1)*((float)N11/(float)N1) + ((float)N10/(float)N1)*((float)N10/(float)N1);
				//float _G1 = ((float)N11*N11+(float)N10*N10)/(float)((N11+N10)*(N11+N10));
				float _G2 = ((float)N21/(float)N2)*((float)N21/(float)N2) + ((float)N20/(float)N2)*((float)N20/(float)N2);
				//float _G2 = ((float)N21*N21+(float)N20*N20)/(float)((N21+N20)*(N21+N20));
				if(N1 && N2){
					fginis[i][j][k] = 1 - _G1*N1/(N2+N1) - _G2*N2/(N1+N2);
					if(fginis[i][j][k] > 1.0){
						printf("Error\n");
						printf("%d,%d,%d,%d,%lf,%lf,%lf,%lf\n",N10,N11,N20,N21,N1,N2,_G1,_G2 );
						exit(-1);
					}
				}else if(N1 == 0){
					fginis[i][j][k] = 1.0 - _G2;					
				}else{
					fginis[i][j][k] = 1.0 - _G1;						
				}

				F _N1 = (gini_inputs[i][j][4*k]+gini_inputs[i][j][4*k+1]);
				F _N2 = (gini_inputs[i][j][4*k+2]+gini_inputs[i][j][4*k+3]);
				N[i][j][2*k] = _N1;
				N[i][j][2*k+1] = _N2;
				divisors[i][j][2*k] = _N1*(_N1+_N2);
				divisors[i][j][2*k+1] = _N2*(_N1+_N2);
				dividents[i][j][2*k] = (_N1*_N1 - F(2)*gini_inputs[i][j][4*k]*gini_inputs[i][j][4*k+1]);  
				dividents[i][j][2*k+1] = (_N2*_N2 - F(2)*gini_inputs[i][j][4*k+2]*gini_inputs[i][j][4*k+3]);
				float d1 = 0.0,d2 = 0.0;
				if(_N1 != F(0) && _N2 != F(0)){
					d1 = dequantize(divide(F(1<<Q)*dividents[i][j][2*k],divisors[i][j][2*k]),1);
					d2 = dequantize(divide(F(1<<Q)*dividents[i][j][2*k+1],divisors[i][j][2*k+1]),1);
					quotients[i][j][2*k] = divide(F(1<<Q)*dividents[i][j][2*k],divisors[i][j][2*k]);
					quotients[i][j][2*k+1] = divide(F(1<<Q)*dividents[i][j][2*k+1],divisors[i][j][2*k+1]);
					inverses[i][j][2*k].inv(inverses[i][j][2*k],_N1);
					
					inverses[i][j][2*k+1].inv(inverses[i][j][2*k+1],_N2);
					remainders[i][j][2*k] = F(1<<Q)*dividents[i][j][2*k] - divisors[i][j][2*k]*quotients[i][j][2*k];
					remainders[i][j][2*k+1] = F(1<<Q)*dividents[i][j][2*k+1] - divisors[i][j][2*k+1]*quotients[i][j][2*k+1];
				
				}
				else if(_N1 == F(0)){
					d2 = dequantize(divide(F(1<<Q)*dividents[i][j][2*k+1],divisors[i][j][2*k+1]),1);					
					quotients[i][j][2*k] = F(0);
					quotients[i][j][2*k+1] = divide(F(1<<Q)*dividents[i][j][2*k+1],divisors[i][j][2*k+1]);
					inverses[i][j][2*k] = F(0);
					inverses[i][j][2*k+1].inv(inverses[i][j][2*k+1],_N2);
					remainders[i][j][2*k] = F(0);
					remainders[i][j][2*k+1] = F(1<<Q)*dividents[i][j][2*k+1] - divisors[i][j][2*k+1]*quotients[i][j][2*k+1];
				}
				else{
					d1 = dequantize(divide(F(1<<Q)*dividents[i][j][2*k],divisors[i][j][2*k]),1);
					quotients[i][j][2*k] = divide(F(1<<Q)*dividents[i][j][2*k],divisors[i][j][2*k]);
					quotients[i][j][2*k+1] = F(0);							
					inverses[i][j][2*k].inv(inverses[i][j][2*k],_N1);
					inverses[i][j][2*k+1] = F(0);
					remainders[i][j][2*k] = F(1<<Q)*dividents[i][j][2*k] - divisors[i][j][2*k]*quotients[i][j][2*k];
					remainders[i][j][2*k+1] = F(0);
				}

				if(fginis[i][j][k] - 1 + d1 +d2 > 0.0001){
					printf("Error %lf,%lf\n", fginis[i][j][k],1-d1-d2);
					exit(-1);
				}
				if(min1 - fginis[i][j][k] > 0){
					//printf("Ok, %.16lf,%.16lf,%d,%d,%d,%d\n",fginis[i][j][k],min1,((double)min1 - (double)fginis[i][j][k]) > 0.0,i,j,k);
					min1 = fginis[i][j][k];
					idx1 = k;
				
					best_gini[i][j] = F(1<<Q) - quotients[i][j][2*k] - quotients[i][j][2*k+1];
					idx2 = k;
					
				}
				//if(min2 > 1 - d1 - d2){
				//	min2 =  1 - d1 - d2;
				//	best_gini[i][j] = F(1<<Q) - quotients[i][j][2*k] - quotients[i][j][2*k+1];
				//	idx2 = k;
				//	printf(">>Ok %lf,%d,%d,%d\n",min2,i,j,k);
				//}
				//printf("%lf\n", 1 - _G1*N1/(N2+N1) - _G2*N2/(N1+N2));
			}
			if(idx1 != idx2){
				
				printf("Error in split value, increase quantization\n");
				exit(-1);
			}
			//printf("%d\n",min2 );

			_best_gini[i][j] = min1;
			_best_pos[i][j] = idx1;
		}
	}
	
	
	vector<vector<vector<F>>> ginis(nodes);
	for(int i = 0; i < nodes; i++){
		ginis[i].resize(attr);
		for(int j = 0; j < attr; j++){
			ginis[i][j].resize(bin_size);
			for(int k = 0; k < bin_size; k++){
				ginis[i][j][k] = F(1<<Q)- quotients[i][j][2*k] - quotients[i][j][2*k+1]; 
			}
		}
	}
	

	data.nodes = nodes;
	data.attr = attr;
	data.gini_inputs = gini_inputs;
	data.sums = sums;
	data.node_histograms = node_histograms;
	data.inverses = inverses;
	data.quotients = quotients;
	data.remainders = remainders;
	data.divisors = divisors;
	data.dividents = dividents;
	data.N = N;
	data.best_gini = best_gini;
	data.ginis = ginis;
	return data;
}

// Get histograms, the tree matrix and output the histogram of each node
nodes_histogram_SNARK_data get_node_histograms_transcript(vector<vector<F>> _histograms, vector<vector<int>> leaf_index_matrix, vector<vector<int>> leaf_matrix,int attr,vector<vector<F>> _leaf_coeff,int leaves){
	nodes_histogram_SNARK_data data;
	vector<F> node_coeff;
	vector<F> leaf_coeff;
	printf("\n======= Node Histograms Proof =======\n");
	

	for(int i = 0; i < _leaf_coeff.size(); i++){
		for(int j = 0; j < _leaf_coeff[i].size(); j++){
			leaf_coeff.push_back(_leaf_coeff[i][j]);
		}
	}
	// re-organize histograms
	// [node,attr,data]
	vector<vector<vector<F>>> histograms(leaves);
	vector<vector<vector<F>>> node_histograms;
	for(int i = 0; i < histograms.size(); i++){
		histograms[i].resize(attr);
		for(int j = 0; j < attr; j++){
			histograms[i][j].resize(bin_size*2);
			for(int k = 0; k < bin_size; k++){
				histograms[i][j][2*k] = _histograms[i*(attr*bin_size*2) + j*(2*bin_size) + 2*k][4];
				histograms[i][j][2*k+1] = _histograms[i*(attr*bin_size*2) + j*(2*bin_size) + 2*k+1][4];
			}
		}
	}
	
	vector<vector<int>> node_index_matrix(leaf_index_matrix.size());
	for(int i = 0; i < node_index_matrix.size(); i++){
		node_index_matrix[i].resize(leaf_index_matrix[i].size(),-1);
	}

 	for(int i = leaf_matrix.size()-1; i > 0; i--){
		for(int j = 0; j < leaf_matrix[i].size(); j+=2){
			if(leaf_matrix[i][j] != -1){
				vector<int> temp_coeff;
				node_coeff.push_back(F(i-1));
				node_coeff.push_back(F(j/2));
				leaf_matrix[i-1][j/2] = 1;
				
				node_index_matrix[i-1][j/2] = node_coeff.size()/2-1; 
				vector<vector<F>> hist1,hist2;
				if(leaf_index_matrix[i][j] != -1){
					hist1 = histograms[leaf_index_matrix[i][j]];
				}else{
					hist1 = node_histograms[node_index_matrix[i][j]];
				}
				if(leaf_index_matrix[i][j+1] != -1){
					hist2 = histograms[leaf_index_matrix[i][j+1]];		
				}else{
					hist2 = node_histograms[node_index_matrix[i][j+1]];				
				}
				add_histograms(node_histograms,hist1,hist2);
			}
		}
	}

	data.node_histograms = node_histograms;
	data.leaf_histograms = histograms;

	data.node_index_matrix = node_index_matrix;
	data.leaf_index_matrix = leaf_index_matrix;

	data.leaf_matrix = leaf_matrix;
	data.node_coeff = node_coeff;
	data.leaf_coeff = leaf_coeff;
	return data;
}


histogram_SNARK_data get_histograms_transcript(Dataset &D, vector<int> data_partitions, vector<int> label, vector<vector<Node>> Tree, int Attr){
	histogram_SNARK_data transcript;
	// Histograms :  Partitions x Attributes x [class * |C|]
	vector<vector<F>> read_transcript(D.data.size()*D.data[0].size()),write_transcript(D.data.size()*D.data[0].size());
	vector<vector<F>> memory_init(Tree.size()*D.data.size()*2*bin_size);
	vector<vector<F>> final_memory(Tree.size()*D.data.size()*2*bin_size);
	printf("\n======= Leaves Histograms Proof =======\n");
	
	printf("Memory size : %d\n",memory_init.size());
	vector<vector<vector<vector<F>>>> histograms(Tree.size());
	
	for(int i = 0; i < Tree.size(); i++){
		for(int j = 0; j < D.data.size(); j++){
			for(int k = 0; k < bin_size; k++){
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k].resize(8,F(0));
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1].resize(8,F(0));
				
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][0] = F(i);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][1] = F(j);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][2] = F(k);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][3] = F(0);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][4] = F(0);

				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][0] = F(i);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][1] = F(j);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][2] = F(k);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][3] = F(1);
				memory_init[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][4] = F(0);

			}
		}
	}

	for(int i = 0; i < histograms.size(); i++){
		histograms[i].resize(D.data.size());
		for(int j = 0; j < D.data.size(); j++){
			histograms[i][j].resize(2);
			for(int k = 0; k < 2; k++){
				histograms[i][j][k].resize(bin_size,F(0));

			}
		}
	}
	for(int i = 0; i < data_partitions.size(); i++){
		int partition = data_partitions[i];
		
		for(int j = 0; j < Attr; j++){
			read_transcript[i*Attr + j].resize(8,F(0));
			write_transcript[i*Attr + j].resize(8,F(0));
			read_transcript[i*Attr + j][0] = F(partition);
			read_transcript[i*Attr + j][1] = F(j);
			read_transcript[i*Attr + j][2] = F(D.data[j][i]);
			read_transcript[i*Attr + j][3] = label[i];
			read_transcript[i*Attr + j][4] = histograms[partition][j][label[i]][D.data[j][i]];
			write_transcript[i*Attr + j][0] = F(partition);
			write_transcript[i*Attr + j][1] = F(j);
			write_transcript[i*Attr + j][2] = F(D.data[j][i]);
			write_transcript[i*Attr + j][3] = label[i];
			write_transcript[i*Attr + j][4] = histograms[partition][j][label[i]][D.data[j][i]] + F(1);
			histograms[partition][j][label[i]][D.data[j][i]] += F(1);
		}
	}
	
	for(int i = 0; i < Tree.size(); i++){
		for(int j = 0; j < D.data.size(); j++){
			for(int k = 0; k < bin_size; k++){
				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k].resize(8,F(0));
				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1].resize(8,F(0));
				
				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][0] = F(i);
				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][1] = F(j);
				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][2] = F(k);
				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][3] = F(0);
				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k][4] = histograms[i][j][0][k];

				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][0] = F(i);
				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][1] = F(j);
				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][2] = F(k);
				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][3] = F(1);
				final_memory[i*(D.data.size()*bin_size*2) + j*(2*bin_size) + 2*k+1][4] = histograms[i][j][1][k];
			}
		}
	}
	transcript.read_transcript = read_transcript;
	transcript.final_memory = final_memory;
	transcript.memory_init = memory_init;
	transcript.write_transcript = write_transcript;
	return transcript;
}



partition_SNARK_data get_partitions_transcript(Dataset D, vector<Dataset> Partitions, vector<vector<Node>> Tree){
	Tree_Inference_Data inference_data;
	partition_SNARK_data data;


	vector<vector<F>> input_data;
	vector<int> data_partitions;
	vector<int> label;
	vector<vector<F>> permuted_data;
	vector<vector<F>> paths,paths_aux;
	vector<vector<F>> bit_vectors;
	vector<vector<F>> diff_data;
	vector<F> path_diff;

	int check = 0;
	

	for(int i = 0; i < D.data[0].size(); i++){
		vector<int> x;
		int y;
		for(int k = 0; k < D.type.size(); k++){
			x.push_back(D.data[k][i]);
		}
		y = D.label[i];
		label.push_back(y);
		inference_data = Tree_Inference(Tree,x,y);
		inference_data.input.push_back(F(inference_data.pos));
		inference_data.input.push_back(F(y));
		inference_data.permuted_input.push_back(F(inference_data.pos));
		inference_data.permuted_input.push_back(F(y));
		
		input_data.push_back(inference_data.input);
		permuted_data.push_back(inference_data.permuted_input);
		paths.push_back(inference_data.path);
		paths_aux.push_back(inference_data.paths_aux);
		bit_vectors.push_back(inference_data.bit_vector);
		diff_data.push_back(inference_data.diff);	
		data_partitions.push_back(inference_data.pos);
	}

	for(int i = 0; i < Partitions.size(); i++){
		data.powers.push_back(F(Partitions[i].indexes.size()));
		data.int_pows.push_back(Partitions[i].indexes.size());
	}
	
	data.power_bits = prepare_bit_vector(data.powers,32);
	pad_vector(data.power_bits);
	//pad_matrix(input_data);
	pad_matrix(permuted_data);
	data.input_data =input_data;

	data.permuted_data = permuted_data;
	data.paths = paths;
	data.paths_aux = paths_aux;
	data.bit_vectors = bit_vectors;
	data.diff_data = diff_data;
	data.path_diff = path_diff;
	data.data_partitions = data_partitions;
	data.label = label;
	return data;
}