
#include "GKR.h"
#include "pol_verifier.h"
#include "VerifyTree.h"

using namespace std;
using std::max;
#define Clients 2
#define Len 8
extern int partitions;

vector<DAG_gate *> in_circuit_dag;
vector<vector<DAG_gate *>> ip_circuit_dag;

const int repeat = 1;

FILE *ins_file, *wit_file;

using std::cerr;
using std::endl;


struct gkr_proof_metadata{
    vector<vector<vector<int>>> q_poly;
    vector<vector<int>> random;
    vector<vector<vector<vector<int>>>> q_hashes;
    vector<vector<int>> v,sig,final_claims_v;
    int sum;
};


struct range_proof_metadata{
    vector<vector<int>> q_poly,c_poly;
    vector<vector<vector<int>>> q_hashes,c_hashes;
    vector<int> inputs1,inputs2,v1,v2;
    int sum;
 };


struct m2m_proof_metadata{
    vector<vector<int>> coef;
    vector<vector<vector<int>>> q_hashes;
    vector<int> inputs;

    int v1,v2,sum;
};



int arr_len = 1024*16;
int N = 16;
int algorithm = 666;
int clients = 512+1;//512+1;
int K = 254;
long long int numbers = 1024*1024;
int mod;


layeredCircuit DAG_to_layered() {
     layeredCircuit c;
     vector<u64> in_deg(in_circuit_dag.size());          // in degree
    vector<int> lyr_id(in_circuit_dag.size());          // the layer of each gate
    vector<u64> id_in_lyr(in_circuit_dag.size());       // the corresponding id within the layer
    vector<vector<u64>> edges(in_circuit_dag.size());   // the edges in the DAG

    // Topologically sorting
    queue<u64> q;
    for (u64 i = 0; i < in_circuit_dag.size(); ++i) {

        auto &g = *in_circuit_dag[i];
        if (g.input0.first == 'V') {
            ++in_deg[i];
            edges[g.input0.second].push_back(i);
        }
        if (g.input1.first == 'V') {
            ++in_deg[i];
            edges[g.input1.second].push_back(i);
        }
        if (g.ty == Input) {
            lyr_id[i] = 0;
            q.push(i);
        }
    }

    int max_lyr_id = 0;
    while (!q.empty()) {

        u64 u = q.front();
        q.pop();
        max_lyr_id = max(lyr_id[u], max_lyr_id);
        for (auto v: edges[u])
            if (!(--in_deg[v])) {
                q.push(v);
                lyr_id[v] = max(lyr_id[v], lyr_id[u] + 1);
            }
    }

    // build the circuit
    c.circuit.resize(max_lyr_id + 1);
    c.size = max_lyr_id + 1;
    for (u64 i = 0; i < in_circuit_dag.size(); ++i)
        id_in_lyr[i] = c.circuit[lyr_id[i]].size++;

    for (int i = 0; i < c.size; ++i)
        c.circuit[i].gates.resize(c.circuit[i].size);

    for (u64 i = 0; i < in_circuit_dag.size(); ++i) {
        int lg = lyr_id[i];
        u64 gid = id_in_lyr[i];
        auto &g = *in_circuit_dag[i];
        auto ty = g.ty, nty = ty;
        u64 in0 = g.input0.second;
        u64 in1 = g.input1.second;
        bool is_assert = g.is_assert;
        u64 u, v;
        F cst;

        switch (ty) {
            case Mul: case Add: case Xor:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) swap(u, v), swap(in0, in1);
                c.circuit[lg].gates[gid] = gate(ty, lyr_id[in1], u, v, F_ZERO, is_assert);
                break;
            case AddMul:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) swap(u, v), swap(in0, in1);
                c.circuit[lg].gates[gid] = gate(ty, lyr_id[in1], u, v, F_ZERO, is_assert,0);
                for(int k = 0; k < ip_circuit_dag[i].size()-1; k++){
                    auto &g_new = *ip_circuit_dag[i][k];
                    u64 i0 = g_new.input0.second;
                    u64 i1 = g_new.input1.second;
                    u = id_in_lyr[i0];
                    v = id_in_lyr[i1];
                    if (lyr_id[in0] < lg - 1) swap(u, v), swap(in0, in1);
                    c.circuit[lg].gates[gid].push_elements(u,v);
                }
                break;
            case Sub:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) {
                    nty = AntiSub;
                    swap(u, v);
                    swap(in0, in1);
                }
                c.circuit[lg].gates[gid] = gate(nty, lyr_id[in1], u, v, F_ZERO, is_assert);
            break;
            case Naab:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) {
                    nty = AntiNaab;
                    swap(u, v);
                    swap(in0, in1);
                }
                c.circuit[lg].gates[gid] = gate(nty, lyr_id[in1], u, v, F_ZERO, is_assert);
            break;
            case Mulc: case Addc:
                u = id_in_lyr[in0];
                cst = F(in1);
                c.circuit[lg].gates[gid] = gate(ty, -1, u, 0, cst, is_assert);
            break;
            case Not: case Copy:
                u = id_in_lyr[in0];
                cst = F(in1);
                c.circuit[lg].gates[gid] = gate(ty, -1, u, 0, cst, is_assert);
            case Input:
                u = in0;
                c.circuit[lg].gates[gid] = gate(ty, -1, u, 0, F_ZERO, is_assert);
        }
    }
    // repeat the layer except the input for ${repeat} times
    for (int i = 1; i < c.size; ++i) {
        for (int j = 1; j < repeat; ++j)
            for (u64 k = 0; k < c.circuit[i].size; ++k) {
                auto &g = c.circuit[i].gates[k];
                c.circuit[i].gates.push_back(c.circuit[i].gates[k]);
                if (g.ty != Input && i > 1) g.u += j * c.circuit[i].size;
                if (g.ty == Add ||
                    g.ty == Mul ||
                    g.ty == Xor ||
                    g.ty == AddMul ||
                    g.ty == Sub ||
                    g.ty == AntiSub ||
                    g.ty == Naab ||
                    g.ty == AntiNaab)
                    g.v += j * c.circuit[i].size;
            }
        c.circuit[i].size *= repeat;
    }

    for (int i = 0; i <= max_lyr_id; ++i) {
        c.circuit[i].bitLength = (int) log2(c.circuit[i].size);
        if ((1ULL << c.circuit[i].bitLength) < c.circuit[i].size) ++c.circuit[i].bitLength;
    }
    return c;
}

#define REL 1

extern layeredCircuit DAG_to_layered();

void parse_single_inference_phase1(ifstream &circuit_in, long long int *in, int Attr);
void parse_single_inference_phase2(ifstream &circuit_in, long long int *in, int Attr, int max_depth);
void parse_permutation_check(ifstream &circuit_in, long long int *in, int Attr);
void parse_permutation_check_partitions(ifstream &circuit_in, long long int *in, int N,int Attr);
void parse_permutation_check_partitions_data(ifstream &circuit_in, long long int *in, int N,int nodes, int Attr);
void parse_permutation_check_partitions_tree(ifstream &circuit_in, long long int *in, int N, int nodes);
void parse_batch_inference(ifstream &circuit_in, long long int *in, int diff_size, int Attr, int max_depth, int N,int path_col,int perm_col);
void parse_path_consistency(ifstream &circuit_in, long long int *in, int Attr, int max_depth, int N);
void parse_histogram_check(ifstream &circuit_in, long long int *in, int N,int Attr,int compressed_size);
void parse_check_coordinates(ifstream &circuit_in, long long int *in, int leaves, int nodes);
void parse_check_coordinates_forest(ifstream &circuit_in, long long int *in, int leaves, int nodes, int trees);
void parse_node_sum(ifstream &circuit_in, long long int *in, int hist_size, int leaves, int nodes);
void parse_gini_check1(ifstream &circuit_in, long long int *in, int nodes, int attr, int bin_size); 
void parse_gini_check2(ifstream &circuit_in, long long int *in, int nodes, int attr, int bin_size); 
void parse_range_lookup(ifstream &circuit_in, long long int *in, int segments, int elements);
void parse_proof_recursion(ifstream &circuit_in, long long int *in,vector<partition_indexes> P1,vector<histogram_indexes> P2 ,vector<node_histogram_indexes> P3, vector<split_indexes> P4, int input_size);
void parse_test_circuit(ifstream &circuit_in, long long int *in, int N, int layers);
void parse_prepare_coeff(ifstream &circuit_in, long long int *in, int degree);
void inference_parse(ifstream &circuit_in, long long int *in, int Attr, int max_depth, int trees);

void parse_test_circuit(ifstream &circuit_in, long long int *in, int N, int layers);
void parse_test_circuit2(ifstream &circuit_in, long long int *in, int N, int layers);

void test_gkr(vector<F> data, vector<F> randomness, int N, int M, int layers){
    
     layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_test_circuit2(circuit_in, in, N*M/layers, layers);

    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
   
    
    
    //prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    //verifier v(&p, c);
    //ip_circuit_dag.clear();
    //struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    //return Pr;    

}

struct proof inference_proof(vector<F> data, vector<F> randomness,  int Attr, int max_depth, int trees){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    inference_parse(circuit_in, in, Attr,  max_depth, trees);

    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;
}

struct proof prepare_coeff(vector<F> data, vector<F> randomness, int N){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_prepare_coeff(circuit_in, in, N);

    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;
}

struct proof prove_test_circuit(vector<F> data, vector<F> randomness, int N, int layers){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_test_circuit(circuit_in, in, N, layers);

    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;    

}

struct proof prove_recursion(vector<F> data, vector<F> randomness, vector<partition_indexes> P1,vector<histogram_indexes> P2 ,vector<node_histogram_indexes> P3, vector<split_indexes> P4, int input_size){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_proof_recursion(circuit_in, in, P1,P2,P3,P4, input_size);

    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;    

}

struct proof range_lookup(vector<F> data, vector<F> randomness, int segments, int elements){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_range_lookup(circuit_in, in, segments, elements);

    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;    

}

struct proof prove_gini_check_phase1(vector<F> data, vector<F> randomness, int nodes, int attr, int bin_size){
     layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_gini_check1(circuit_in, in, nodes, attr,  bin_size);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;
}

struct proof prove_gini_check_phase2(vector<F> data, vector<F> randomness, int nodes, int attr, int bin_size){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_gini_check2(circuit_in, in, nodes, attr,  bin_size);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;    

}


struct proof prove_node_sum(vector<F> data, vector<F> randomness, F rand, int hist_size, int leaves, int nodes){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_node_sum(circuit_in, in, hist_size, leaves, nodes);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,rand);
    return Pr;    

}

struct proof node_histogram_consistency_forest(vector<F> data, vector<F> randomness, int leaves, int nodes, int trees){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_check_coordinates_forest(circuit_in, in,leaves, nodes, trees);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;
}

struct proof node_histogram_consistency(vector<F> data, vector<F> randomness, int leaves, int nodes){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_check_coordinates(circuit_in, in,leaves, nodes);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;
}

struct proof histogram_check(vector<F> data, vector<F> randomness, int N, int Attr, int compressed_size){
     layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_histogram_check(circuit_in, in, N, Attr, compressed_size);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;
}


struct proof path_consistency(vector<F> data, vector<F> randomness, int Attr, int max_depth, int N){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_path_consistency(circuit_in, in, Attr, max_depth, N);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;
}

struct proof batch_inference(vector<F> data, vector<F> randomness,F previous_r,  int diff_size, int Attr, int max_depth, int N,int path_col,int perm_col){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_batch_inference(circuit_in, in, diff_size, Attr, max_depth, N,path_col,perm_col);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,previous_r);
    return Pr;
}

struct proof single_inference_phase1(vector<F> data, vector<F> randomness, int Attr){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_single_inference_phase1(circuit_in,in,Attr);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;
}
struct proof single_inference_phase2(vector<F> data, vector<F> randomness, int Attr, int max_depth){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_single_inference_phase2(circuit_in,in,Attr,max_depth);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;
}

struct proof permutation_check_partitions_tree(vector<F> data, vector<F> randomness, int N, int nodes){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_permutation_check_partitions_tree(circuit_in, in, N, nodes);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;

}


struct proof permutation_check_partitions_data(vector<F> data, vector<F> randomness, int N, int nodes,int Attr){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_permutation_check_partitions_data(circuit_in, in, N,nodes,Attr);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;

}

struct proof permutation_check_partitions_input(vector<F> data, vector<F> randomness, int N, int Attr){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_permutation_check_partitions(circuit_in, in, N,Attr);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;

}

struct proof permutation_check(vector<F> data, vector<F> randomness, int Attr){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_permutation_check(circuit_in,in,Attr);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    return Pr;
}



struct proof generate_GKR_proof(char *circuit_name, char *input_file,vector<F> data,vector<F> randomness, bool debug) {
    //16798108731015832284940804142231733909889187121439069848933715426072753864723
    layeredCircuit c;

    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in(circuit_name);
    in_circuit_dag.clear();

    
    c = DAG_to_layered();
    //fclose(stdin);
    //F::init();
    c.subsetInit();
    prover p(c,input_file,data,debug);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);

    return Pr;
    //fprintf(stdout, "mult counter %d, add counter %d\n", F::multCounter, F::addCounter);
    

    //return 0;
}

regex add_gate("P V[0-9]+ = V[0-9]+ \\+ V[0-9]+ E");
regex mult_gate("P V[0-9]+ = V[0-9]+ \\* V[0-9]+ E");
regex add_mul_gate("P V[0-9]+ = V[0-9]+ ip V[0-9]+ E");
regex input_gate("P V[0-9]+ = I[0-9]+ E");
regex output_gate("P O[0-9]+ = V[0-9]+ E");
regex xor_gate("P V[0-9]+ = V[0-9]+ XOR V[0-9]+ E");
regex minus_gate("P V[0-9]+ = V[0-9]+ minus V[0-9]+ E");
regex naab_gate("P V[0-9]+ = V[0-9]+ NAAB V[0-9]+ E");
regex not_gate("P V[0-9]+ = V[0-9]+ NOT V[0-9]+ E");


smatch base_match;

DAG_gate *buildGate(gateType ty, u64 tgt, u64 src0, u64 src1 = -1, bool has_constant = true);
DAG_gate *buildInput(u64 tgt, u64 src0);
void setAssertion(u64 tgt);

long long int Z;
long long int C;


void add(int x,int y,int &counter){
    buildGate(Add, counter, x,y, false);
    counter+=1;
}


int sum_tree(vector<int> leaves,int &counter){
    vector<int> vec;
    for(int i = 0; i < leaves.size(); i+=2){
        if(i+1 >= leaves.size()){
            vec.push_back(leaves[i]);
        }
        else{
            add(leaves[i],leaves[i+1],counter);
            vec.push_back(counter-1);
        }
    }
    if(vec.size()==1){
        return vec[0];
    }
    else{
        return sum_tree(vec,counter);
    }
} 


void mul(int x,int y,int &counter){
    buildGate(Mul, counter, x,y, false);
    counter+=1;
}

void sub(int x,int y,int &counter){
    buildGate(Sub,counter,x,y,false);
    counter+=1;
}

void ip(vector<int> x, vector<int> y, int &counter){
    for(int i = 0; i < x.size(); i++){
       
         buildGate(AddMul,counter,x[i],y[i],false);
    }
    counter+=1;
}

int add_tree(vector<int> leaves,int &counter){
    vector<int> vec;
    for(int i = 0; i < leaves.size(); i+=2){
        if(i+1 >= leaves.size()){
            vec.push_back(leaves[i]);
        }
        else{
            add(leaves[i],leaves[i+1],counter);
            vec.push_back(counter-1);
        }
    }
    if(vec.size()==1){
        return vec[0];
    }
    else{
        return add_tree(vec,counter);
    }
} 


int mul_tree(vector<int> leaves,int &counter){
    vector<int> vec;
    for(int i = 0; i < leaves.size(); i+=2){
        if(i+1 >= leaves.size()){
            vec.push_back(leaves[i]);
        }
        else{
            mul(leaves[i],leaves[i+1],counter);
            vec.push_back(counter-1);
        }
    }
    if(vec.size()==1){
        return vec[0];
    }
    else{
        return mul_tree(vec,counter);
    }
} 

void hash_circuit_segmented(int hash_input,int k,vector<int> C,int seg, int &counter){
    int iters;
    if(seg == 0){
        add(hash_input,k,counter);
        
        int out = counter-1;
        mul(out,out,counter);
        
        mul(out,counter-1,counter);
        
        int hash_input = counter-1;
        //iters = 9;
        iters = 160/partitions-1;
        for(int i = 0; i < iters; i++){
            add(hash_input,k,counter);
            add(counter-1,C[i+seg],counter);
            out = counter-1;
            mul(out,out,counter);
            mul(out,counter-1,counter);
            hash_input = counter-1;

        }
    }
    else{
        //iters = 10;
        iters = 160/partitions - 1;
        for(int i = 0; i < iters; i++){
            add(hash_input,k,counter);
            add(counter-1,C[i+seg-1],counter);
            int out = counter-1;
            mul(out,out,counter);
            mul(out,counter-1,counter);
            int hash_input = counter-1;

        }
    }

    if(iters + seg == 160){
            add(hash_input,k,counter);
            add(counter-1,C[iters + seg-1],counter);
            int out = counter-1;
            mul(out,out,counter);
            mul(out,counter-1,counter);
            int hash_input = counter-1;
            add(hash_input,k,counter);
     }
}

void multihash_segmented(vector<vector<int>> hashes, vector<int> hash_input, vector<int> C, int zero, int &counter){
    for(int i = 0; i < hashes.size(); i++){

        for(int j = 0; j < hashes[i].size() -1; j++){
            if(j == 0){
                if(i == 0){
                    hash_circuit_segmented(hash_input[i],zero,C,(160/partitions)*j,counter);
                }else{
                    hash_circuit_segmented(hash_input[i],hashes[i-1][hashes[i-1].size()-1],C,(160/partitions)*j,counter);
                    
                }
            }
            else{
                if(i == 0){
                    hash_circuit_segmented(hashes[i][j-1],zero,C,(160/partitions)*j,counter);
                }else{
                    hash_circuit_segmented(hashes[i][j-1],hashes[i-1][hashes[i-1].size()-1],C,(160/partitions)*j,counter);
                }
                if(j == hashes[i].size()-2){
                    if(i == 0){
                        add(counter-1,zero,counter);
                    }else{
                        add(counter-1,hashes[i-1][hashes[i-1].size()-1],counter);
                    }
                    sub(hash_input[i],hashes[i][j+1],counter);
                    add(counter-1,counter-2,counter);
                    //sub(counter-1,hashes[i][j+1],counter);
                }
            }
        }
    }
}


int eval_quadratic_poly(vector<int> coef, int x, int &counter){
    mul(x,x,counter);
    mul(counter-1,coef[0],counter);
    mul(x,coef[1],counter);
    add(counter-1,coef[2],counter);
    add(counter-1,counter-3,counter);
    return counter-1;
}

void eval_cubic_poly(vector<int> coef, int x, int &counter){
    mul(x,x,counter);
    int sqr = counter-1;
    mul(x,sqr,counter);
    int cube = counter-1;
    mul(x,coef[2],counter);
    add(counter-1,coef[3],counter);
    int _sum = counter-1;
    mul(sqr,coef[1],counter);
    add(counter-1,_sum,counter);
    _sum = counter-1;
    mul(cube,coef[0],counter);
    add(counter-1,_sum,counter);

}

void beta_computation(vector<int> r1, vector<int> r2, int one, int &counter){
    vector<int> temp;

    for(int i = 0; i < r1.size(); i++){
        add(r1[i],r2[i],counter);
        sub(one,counter-1,counter);
        
        mul(r1[i],r2[i],counter);
        add(counter-1,counter-1,counter);
        
        add(counter-1,counter-3,counter);
        temp.push_back(counter-1);
    }
    mul_tree(temp,counter);
}



int poly_eval(vector<int> coeff, vector<int> x, int &counter){
    
    for(int i = 0; i < x.size(); i++){
        int L = 1 << (x.size() - 1 - i);
        for(int j = 0; j < L; j++){
            sub(coeff[2*j+1],coeff[2*j],counter);
            mul(counter-1,x[i],counter);
            add(coeff[2*j],counter-1,counter);
            coeff[j] = counter-1;
        }
    }
    return coeff[0];
}

void verify_3sumcheck(vector<vector<int>> coef, vector<int> randomness, vector<int> init_randomness, int v1, int v2, int sum, int one,int &counter){
    int prev_sum = sum;
    for(int i = 0; i < coef.size(); i++){
        add(coef[i][0],coef[i][1],counter);
        add(coef[i][2],coef[i][3],counter);
        add(counter-1,counter-2,counter);
        add(counter-1,coef[i][3],counter);
        sub(counter-1,prev_sum,counter);
        eval_cubic_poly(coef[i],randomness[i],counter);
        prev_sum = (counter-1);
    }
    
    if(init_randomness.size()!=0){
        beta_computation(init_randomness,randomness,one,counter);
        int beta = counter-1; 
        mul(beta,v1,counter);
        mul(counter-1,v2,counter);
        sub(prev_sum,counter-1,counter);
    }
    else{
        mul(v1,v2,counter);
        mul(v2,counter-1,counter);
        sub(prev_sum,counter-1,counter);
    }
}

int mul_tree_verification_circuit(MulTree_indexes P, int one, int &counter){
    int sum;
    if(P.first_r.size() == 0){
        mul(P.in[0],P.in[1],counter);
        sub(P.initial_sum,counter-1,counter);
        sub(one,P.randomness[0][0],counter);
        mul(counter-1,P.in[0],counter);
        mul(P.randomness[0][0],P.in[1],counter);
        add(counter-1,counter-2,counter);
        sum = counter-1;
        for(int i = 0; i < P.polynomials.size(); i++){
            verify_3sumcheck(P.polynomials[i],P.randomness[i+1],P.randomness[i],P.vr[2*i],P.vr[2*i+1],sum,one,counter);
            sub(one,P.rand[i],counter);
            mul(counter-1,P.vr[2*i],counter);
            mul(P.rand[i],P.vr[2*i+1],counter);
            add(counter-1,counter-2,counter);
            sum = counter-1; 
        }
    }else{
        vector<int> previous_r = P.first_r;
        sum = P.initial_sum;
        
        for(int i = 0; i < P.polynomials.size(); i++){
            verify_3sumcheck(P.polynomials[i],P.randomness[i],previous_r,P.vr[2*i],P.vr[2*i+1],sum,one,counter);
            sub(one,P.rand[i],counter);
            mul(counter-1,P.vr[2*i],counter);
            mul(P.rand[i],P.vr[2*i+1],counter);
            add(counter-1,counter-2,counter);
            sum = counter-1; 
            previous_r = P.randomness[i];
        }
    }
    return sum;
}


int verify_2sumcheck(sumcheck2Prod P,int one, int &counter){
    int previous = P.sum;
    for(int i = 0; i < P.polynomials.size(); i++){
        add(P.polynomials[i][0],P.polynomials[i][1],counter);
        add(P.polynomials[i][2],P.polynomials[i][2],counter);
        add(counter-1,counter-2,counter);
        sub(counter-1,previous,counter);
        previous = eval_quadratic_poly(P.polynomials[i],P.randomness[i],counter);
    }
    if(P.vr.size() != 0){
        mul(P.vr[0],P.vr[1],counter);
        sub(counter-1,previous,counter);
    }

    return previous;
}

void verify_gkr(gkr_proof_indexes P, int one, int &counter){
    int sum = P.sum;
    int idx = 0;
    for(int i = 0; i < P.layers; i++){
        P.sumcheck[idx].sum = sum;
        sum = verify_2sumcheck(P.sumcheck[idx],one,counter);
        idx++;
        P.sumcheck[idx].sum = sum;
        verify_2sumcheck(P.sumcheck[idx],one,counter);
        idx++;
        P.sumcheck[idx].sum = P.sums[i];
        sum = verify_2sumcheck(P.sumcheck[idx],one,counter);
        mul(P.vr[i],P.gr[i],counter);
        sub(sum,counter-1,counter);
        sum = P.vr[i];
        idx++;
    }
}

void verify_sumcheck(vector<vector<int>> coef, vector<int> inputs, int v1, int v2, int sum, int &counter){
    int previous = sum;
    for(int i = 0;i  < coef.size(); i++){
        add(coef[i][0],coef[i][1],counter);
        add(coef[i][2],coef[i][2],counter);
        add(counter-1,counter-2,counter);
        sub(counter-1,previous,counter);
        eval_quadratic_poly(coef[i],inputs[i],counter);
    }
    if(v1 != -1){
        mul(v1,v2,counter);
        sub(counter-1,previous,counter);
    }
}


void parse_test_circuit2(ifstream &circuit_in, long long int *in, int N, int layers){
    vector<int> input(N);
    int counter = 0;
    for(int i = 0; i < N; i++){
        buildInput(counter, 0);
        input[i] = counter;
        counter++;
    }
    printf("%lld\n",N);
    vector<int> layer;
    int layer_id = 0;
    for(int l = 0; l < layers; l++){
        for(int i = 0; i < N; i++){
            if(rand()%2 == 0){
                mul(input[(2*i)%N],input[(2*i+1)%N],counter);
            }else{
                add(input[(2*i)%N],input[(2*i+1)%N],counter);
            }
            layer.push_back(counter-1);
        }
        input = layer;
        layer.clear();
        //layer_id++;
        //if(layers == layer_id) break;
    }
    
    
}
int Liu_sum(vector<int> sig, vector<int> final_claims_v, int &counter){
    vector<int> tree;
    for(int i = 0; i < sig.size(); i+=2){
        if(i+1 >= sig.size()){
            mul(final_claims_v[i],sig[i],counter);
            tree.push_back(counter-1);
        }
        else{
            mul(final_claims_v[i+1],sig[i+1],counter);
            mul(final_claims_v[i],sig[i],counter);
            add(counter-1,counter-2,counter);
            tree.push_back(counter-1);
        }
    }
    if(final_claims_v.size() == 1){
        return tree[0];
    }
    else{
        return sum_tree(tree,counter);
    }
}




void parse_single_inference_phase1(ifstream &circuit_in, long long int *in, int Attr){
    vector<int> path(3*Attr+1);
    vector<int> bits(256*Attr);
    int counter = 0;

    for(int i = 0; i < path.size(); i++){
        buildInput(counter, 0);
        path[i] = counter;
        counter++;
    }
    for(int i = 0; i < bits.size(); i++){
        buildInput(counter, 0);
        bits[i] = counter;
        counter++;   
    }
    int one;
    buildInput(counter, 0);
    one = counter;
    counter++;   

    for(int i = 0; i < Attr; i++){
        sub(bits[256*i + 253],path[3*i+2],counter);
        add(one,path[3*i + 2],counter);
        mul(counter-1,counter-2,counter);
    }

}

void parse_range_lookup(ifstream &circuit_in, long long int *in, int segments, int elements){
    vector<vector<int>> indexes(segments);
    vector<vector<vector<int>>> write_transcript(segments),read_transcript(segments);
    vector<vector<vector<int>>> input_transcript(segments),output_transcript(segments);
    int counter = 0;
    for(int i = 0; i < segments; i++){
        indexes[i].resize(elements);
        for(int j = 0; j < elements; j++){
            buildInput(counter, 0);
            indexes[i][j] = (counter);
            counter++;
        }
    }
    for(int i = 0; i < segments; i++){
        write_transcript[i].resize(elements);
        for(int j = 0 ; j < elements; j++){
            buildInput(counter, 0);
            write_transcript[i][j].push_back(counter);
            counter++;
            buildInput(counter, 0);
            write_transcript[i][j].push_back(counter);
            counter++;
        }
    }
    for(int i = 0; i < segments; i++){
        read_transcript[i].resize(elements);
        for(int j = 0 ; j < elements; j++){
            buildInput(counter, 0);
            read_transcript[i][j].push_back(counter);
            counter++;
            buildInput(counter, 0);
            read_transcript[i][j].push_back(counter);
            counter++;
        }
    }
    for(int i = 0; i < segments; i++){
        input_transcript[i].resize(256);
        for(int j = 0 ; j < 256; j++){
            buildInput(counter, 0);
            input_transcript[i][j].push_back(counter);
            counter++;
            buildInput(counter, 0);
            input_transcript[i][j].push_back(counter);
            counter++;
        }
    }
    for(int i = 0; i < segments; i++){
        output_transcript[i].resize(256);
        for(int j = 0 ; j < 256; j++){
            buildInput(counter, 0);
            output_transcript[i][j].push_back(counter);
            counter++;
            buildInput(counter, 0);
            output_transcript[i][j].push_back(counter);
            counter++;
        }
    }

    buildInput(counter, 0);
    int a = counter;
    counter++;


    buildInput(counter, 0);
    int b = counter;
    counter++;

    for(int i = 0; i < segments; i++){
        for(int j = 0; j < elements; j++){
            sub(indexes[i][j],read_transcript[i][j][0],counter);
            sub(indexes[i][j],write_transcript[i][j][0],counter);
            sub(write_transcript[i][j][1],read_transcript[i][j][1],counter);
        }
    }
    vector<vector<int>> perm1(segments),perm2(segments);
    for(int i = 0; i < segments; i++){
        perm1[i].resize(elements+256);
        perm2[i].resize(elements+256);
    }
    int pos = 0;
    for(int i = 0; i < segments; i++){
        for(int j = 0; j < elements; j++){
            //mul(a,read_transcript[i][j][0],counter);
            //mul(b,read_transcript[i][j][1],counter);
            //add(counter-1,counter-2,counter);
            //perm1[i][pos] = counter-1;
            //mul(a,write_transcript[i][j][0],counter);
            //mul(b,write_transcript[i][j][1],counter);
            //perm2[i][pos] = counter-1;
            perm1[i][pos] = read_transcript[i][j][0];
            perm2[i][pos] = write_transcript[i][j][0];

            pos++;
        }
        pos = 0;
    }

    pos = elements;
    for(int i = 0; i < segments; i++){
        for(int j = 0; j < 256; j++){
            //mul(a,output_transcript[i][j][0],counter);
            //mul(b,output_transcript[i][j][1],counter);
            //add(counter-1,counter-2,counter);
            //perm1[i][pos] = counter-1;
            //mul(a,input_transcript[i][j][0],counter);
            //mul(b,input_transcript[i][j][1],counter);
            //perm2[i][pos] = counter-1;
            perm1[i][pos] = input_transcript[i][j][0];
            perm2[i][pos] = output_transcript[i][j][0];
            
            pos++;
        }
        pos = elements;
    }
    for(int i  = 0; i < segments; i++){
        //mul_tree(perm1[i],counter);
        //mul_tree(perm2[i],counter);
    }

}

void parse_gini_check1(ifstream &circuit_in, long long int *in, int nodes, int attr, int bin_size){
    vector<vector<vector<int>>> inverses(nodes),quotients(nodes),divisors(nodes),dividents(nodes),N(nodes);
    int counter = 0;
    for(int i = 0; i < nodes; i++){
        inverses[i].resize(attr);
        for(int j = 0; j < attr; j++){
            inverses[i][j].resize(2*bin_size);
            for(int k = 0; k < 2*bin_size; k++){
                buildInput(counter, 0);
                inverses[i][j][k] = counter;
                counter++; 
            }
        }
    }
    for(int i = 0; i < nodes; i++){
        quotients[i].resize(attr);
        for(int j = 0; j < attr; j++){
            quotients[i][j].resize(2*bin_size);
            for(int k = 0; k < 2*bin_size; k++){
                buildInput(counter, 0);
                quotients[i][j][k] = counter;
                counter++; 
            }
        }
    }
    for(int i = 0; i < nodes; i++){
        divisors[i].resize(attr);
        for(int j = 0; j < attr; j++){
            divisors[i][j].resize(2*bin_size);
            for(int k = 0; k < 2*bin_size; k++){
                buildInput(counter, 0);
                divisors[i][j][k] = counter;
                counter++; 
            }
        }
    }
    for(int i = 0; i < nodes; i++){
        dividents[i].resize(attr);
        for(int j = 0; j < attr; j++){
            dividents[i][j].resize(2*bin_size);
            for(int k = 0; k < 2*bin_size; k++){
                buildInput(counter, 0);
                dividents[i][j][k] = counter;
                counter++; 
            }
        }
    }
    for(int i = 0; i < nodes; i++){
        N[i].resize(attr);
        for(int j = 0; j < attr; j++){
            N[i][j].resize(2*bin_size);
            for(int k = 0; k < 2*bin_size; k++){
                buildInput(counter, 0);
                N[i][j][k] = counter;
                counter++; 
            }
        }
    }
    buildInput(counter, 0);
    int one = counter;
    counter++;
    
    for(int i = 0; i  < nodes; i++){
        
        for(int j = 0; j < attr; j++){
            
            for(int k = 0; k < bin_size; k++){   
                
                mul(inverses[i][j][2*k],N[i][j][2*k],counter);
                int cond1 = counter-1;
                sub(one,counter-1,counter);
                mul(N[i][j][2*k],counter-1,counter);
                
                mul(inverses[i][j][2*k+1],N[i][j][2*k+1],counter);
                int cond2 = counter-1;
                sub(one,counter-1,counter);
                mul(N[i][j][2*k+1],counter-1,counter);
                
                mul(dividents[i][j][2*k],cond1,counter);
                
                mul(quotients[i][j][2*k],divisors[i][j][2*k],counter);
                sub(counter-1,counter-2,counter);
                
                mul(dividents[i][j][2*k+1],cond2,counter);
                
                mul(quotients[i][j][2*k+1],divisors[i][j][2*k+1],counter);
                sub(counter-1,counter-2,counter);
            }
        }
    }


}


void parse_gini_check2(ifstream &circuit_in, long long int *in, int nodes, int attr, int bin_size){
    vector<vector<vector<int>>> sums(nodes),gini_inputs(nodes),histograms(nodes);
    vector<vector<vector<int>>> N(nodes);
    int counter = 0;

    
    for(int i = 0; i < nodes; i++){
        sums[i].resize(attr);
        for(int j = 0; j < attr; j++){
            buildInput(counter, 0);
            sums[i][j].push_back(counter);
            counter++;
            buildInput(counter, 0);
            sums[i][j].push_back(counter);
            counter++;
        }
    }
    for(int i = 0; i < nodes; i++){
        gini_inputs[i].resize(attr);
        for(int j = 0; j < attr; j++){
            gini_inputs[i][j].resize(4*bin_size);
            for(int k = 0; k < 4*bin_size; k++){
                buildInput(counter, 0);
                gini_inputs[i][j][k] = counter;
                counter++;
            }
        }
    }
    for(int i = 0; i < nodes; i++){
        histograms[i].resize(attr);
        for(int j = 0; j < attr; j++){
            histograms[i][j].resize(2*bin_size);
            for(int k = 0; k < 2*bin_size; k++){
                buildInput(counter, 0);
                histograms[i][j][k] = counter;
                counter++;
            }
        }
    }



    for(int i = 0; i < nodes; i++){
        for(int j = 0; j < attr; j++){
            sub(histograms[i][j][0],gini_inputs[i][j][0],counter);
            sub(histograms[i][j][1],gini_inputs[i][j][1],counter);
            

            sub(sums[i][j][0],histograms[i][j][0],counter);
            sub(gini_inputs[i][j][2],counter-1,counter);
            sub(sums[i][j][1],histograms[i][j][1],counter);
            sub(gini_inputs[i][j][3],counter-1,counter);
            for(int k = 1; k < bin_size; k++){
                
                add(histograms[i][j][2*k],gini_inputs[i][j][4*(k-1)],counter);
                sub(counter-1,gini_inputs[i][j][4*k],counter);
                
                add(histograms[i][j][2*k+1],gini_inputs[i][j][4*(k-1)+1],counter);
                sub(counter-1,gini_inputs[i][j][4*k+1],counter);
                
                sub(gini_inputs[i][j][4*(k-1) + 2],histograms[i][j][2*k],counter);
                sub(gini_inputs[i][j][4*k+2],counter-1,counter);
                
                sub(gini_inputs[i][j][4*(k-1) + 3],histograms[i][j][2*k+1],counter);
                sub(gini_inputs[i][j][4*k+3],counter-1,counter);

            }
        }
    }
    
    
    //vector<vector<vector<int>>> divisors(nodes),dividents(nodes);
    // Compute necessary data for the gini computation
    
    //for(int i = 0; i  < nodes; i++){
    //    divisors[i].resize(attr);
    //    dividents[i].resize(attr);
        
    //    for(int j = 0; j < attr; j++){
    //        divisors[i][j].resize(2*bin_size);
    //        dividents[i][j].resize(2*bin_size);
            
    //        for(int k = 0; k < bin_size; k++){
                // N0 = N00+N01
                //add(gini_inputs[i][j][4*k],gini_inputs[i][j][4*k+1],counter);
                //int N0 = counter-1;
                // N0_square = N0*N0
    //            mul(N[i][j][2*k],N[i][j][2*k],counter);
    //            int N0_square = counter-1;

                // N1 = N10+N11
                //add(gini_inputs[i][j][4*k+2],gini_inputs[i][j][4*k+3],counter);
                //int N1 = counter-1;
                // N1_square = N1*N1
    //            mul(N[i][j][2*k+1],N[i][j][2*k+1],counter);
    //            int N1_square = counter-1;

                // N = N1+N0
    //            add(N[i][j][2*k],N[i][j][2*k+1],counter);
    //            int _N = counter-1;

    //            mul(N[i][j][2*k],_N,counter);
    //            add(counter-1,zero,counter);

                //add(zero,counter-1,counter);
    //            divisors[i][j][2*k] = counter-1;
    //            mul(N[i][j][2*k+1],_N,counter);
    //            add(counter-1,zero,counter);
                //add(zero,counter-1,counter);
    //            divisors[i][j][2*k+1] = counter-1;

    //            mul(gini_inputs[i][j][4*k],gini_inputs[i][j][4*k+1],counter);
   //             add(counter-1,counter-1,counter);
    //            sub(N0_square,counter-1,counter);
    //            dividents[i][j][2*k] = counter-1;
    //            mul(gini_inputs[i][j][4*k+2],gini_inputs[i][j][4*k+3],counter);
    //            add(counter-1,counter-1,counter);
    //            sub(N1_square,counter-1,counter);
    //            dividents[i][j][2*k+1] = counter-1;
                
                /*
                mul(inverses[i][j][2*k],N0,counter);
                int cond1 = counter-1;
                sub(one,counter-1,counter);
                mul(N0,counter-1,counter);
                
                mul(inverses[i][j][2*k+1],N1,counter);
                int cond2 = counter-1;
                sub(one,counter-1,counter);
                mul(N1,counter-1,counter);
                */
                //mul(dividents[i][j][2*k],cond1,counter);
                
                //mul(quotients[i][j][2*k],divisors[i][j][2*k],counter);
                //sub(counter-1,counter-2,counter);
                //sub(divisors[i][j][2*k],counter-1,counter);

                //mul(dividents[i][j][2*k+1],cond2,counter);
                
                //mul(quotients[i][j][2*k+1],divisors[i][j][2*k+1],counter);
                //sub(counter-1,counter-2,counter);
                //sub(divisors[i][j][2*k+1],counter-1,counter);
    //        }
    //    }
    //}

}

void parse_check_coordinates_forest(ifstream &circuit_in, long long int *in, int leaves, int nodes, int trees){
    int leaf_size = 2*leaves;
    if(1ULL << ((int)log2(2*leaves)) != 2*leaves){
        leaf_size = 1ULL << ((int)log2(2*leaves)+1);
    }
    int nodes_size = 2*nodes;
    if(1ULL << ((int)log2(2*nodes)) != 2*nodes){
        nodes_size = 1ULL << ((int)log2(2*nodes)+1);
    }
    int witness_size = 2*(leaves+nodes-1);
    if(1ULL << ((int)log2(witness_size)) != witness_size){
        witness_size = 1ULL << ((int)log2(witness_size)+1);
    }

   
    vector<vector<int>> leaf_coord(trees),node_coord(trees);
    vector<vector<int>> witness_coord(trees);
    int counter = 0;
    for(int k = 0; k < trees; k++){
        witness_coord[k].resize(witness_size);
        for(int i = 0; i < witness_coord[k].size(); i++){
            buildInput(counter, 0);
            witness_coord[k][i] = counter;
            counter++;    
        }
    }
    for(int k = 0; k < trees; k++){
        node_coord[k].resize(nodes_size);
        for(int i = 0; i < node_coord[k].size(); i++){
            buildInput(counter, 0);
            node_coord[k][i] = counter;
            counter++;    
        }
    }

    for(int k = 0; k < trees; k++){
        leaf_coord[k].resize(leaf_size);
        for(int i = 0; i < leaf_coord[k].size(); i++){
            buildInput(counter, 0);
            leaf_coord[k][i] = counter;
            counter++;   
        }
    }
    
    int nodes2_size = nodes;
    if(1ULL << ((int)log2(nodes2_size)) != nodes2_size){
        nodes2_size = 1ULL << ((int)log2(nodes2_size)+1);
    }
    int com_witness_size = leaves+nodes-1;
    if(1ULL << ((int)log2(com_witness_size)) != com_witness_size){
        com_witness_size = 1ULL << ((int)log2(com_witness_size)+1);
    }
    int comp_leaves = leaves;
    if(1ULL << ((int)log2(comp_leaves)) != comp_leaves){
        comp_leaves = 1ULL << ((int)log2(comp_leaves)+1);
    }
    vector<vector<int>> compressed_leaf_hist(trees),compressed_node_hist(trees);
    vector<vector<int>> compressed_witness_hist(trees),compressed_out_hist(trees);
    
    for(int k = 0; k < trees; k++){
        compressed_witness_hist[k].resize(com_witness_size);
        for(int i = 0; i < compressed_witness_hist[k].size(); i++){
            buildInput(counter, 0);
            compressed_witness_hist[k][i] = counter;
            counter++;    
        }
    }
    
    
    for(int k = 0; k < trees; k++){
        compressed_node_hist[k].resize(nodes2_size);
        for(int i = 0; i < compressed_node_hist[k].size(); i++){
            buildInput(counter, 0);
            compressed_node_hist[k][i] = counter;
            counter++;
        }
    }
    for(int k = 0; k < trees; k++){
        compressed_out_hist[k].resize(nodes2_size);
        for(int i = 0; i < compressed_out_hist[k].size(); i++){
            buildInput(counter, 0);
            compressed_out_hist[k][i] = counter;
            counter++;    
        }
    }

    for(int k = 0; k < trees; k++){
        compressed_leaf_hist[k].resize(comp_leaves);
        for(int i = 0; i < compressed_leaf_hist[k].size(); i++){
            buildInput(counter, 0);
            compressed_leaf_hist[k][i] = counter;
            counter++;   
        }
    }
    buildInput(counter, 0);
    int a = counter;
    counter++;
    buildInput(counter, 0);
    int b = counter;
    counter++;
    buildInput(counter, 0);
    int c = counter;
    counter++;
    buildInput(counter,0);
    int r = counter;
    counter++;
    buildInput(counter, 0);
    int two_inv = counter;
    counter++;
    buildInput(counter, 0);
    int one = counter;
    counter++;

    
    vector<int> out_coord(2*nodes);
    vector<int> compressed_leaf(leaves),compressed_node(nodes-1),compressed_witness(leaves+nodes-1),compressed_out(nodes);
    for(int k = 0; k < trees; k++ ){
        for(int i = 0; i < leaves; i++){
            mul(leaf_coord[k][2*i],a,counter);
            mul(leaf_coord[k][2*i+1],b,counter);
            add(counter-1,counter-2,counter);
            mul(compressed_leaf_hist[k][i],r,counter);
            add(counter-1,counter-2,counter);
            sub(counter-1,c,counter);   
            
            compressed_leaf[i] = counter-1;
        }

        for(int i = 0; i < nodes-1; i++){
            mul(node_coord[k][2*i],a,counter);
            mul(node_coord[k][2*i+1],b,counter);
            add(counter-1,counter-2,counter);
            mul(compressed_node_hist[k][i],r,counter);
            add(counter-1,counter-2,counter);
            sub(counter-1,c,counter);   
            compressed_node[i] = counter-1;
        }

        int root;
        mul(node_coord[k][2*(nodes-1)],a,counter);
        mul(node_coord[k][2*(nodes-1)+1],b,counter);
        add(counter-1,counter-2,counter);
        mul(compressed_node_hist[k][nodes-1],r,counter);
        add(counter-1,counter-2,counter);
        sub(counter-1,c,counter);   
        root = counter-1;

        for(int i = 0; i < nodes+leaves-1; i++){
            mul(witness_coord[k][2*i],a,counter);
            mul(witness_coord[k][2*i+1],b,counter);
            add(counter-1,counter-2,counter);
            mul(compressed_witness_hist[k][i],r,counter);
            add(counter-1,counter-2,counter);
            sub(counter-1,c,counter);   
            compressed_witness[i] = counter-1;
        }
        
        for(int i = 0; i < (nodes+leaves-1)/2; i++){
            sub(witness_coord[k][4*i],one,counter);
            mul(witness_coord[k][4*i+1],two_inv,counter);
            out_coord[2*i] = counter-2;
            out_coord[2*i+1] = counter-1;
        }
        for(int i = 0; i < nodes; i++){
            mul(out_coord[2*i],a,counter);
            mul(out_coord[2*i+1],b,counter);
            add(counter-1,counter-2,counter);
            mul(compressed_out_hist[k][i],r,counter);
            add(counter-1,counter-2,counter);
            
            sub(counter-1,c,counter);   
            compressed_out[i] = counter-1;
        }
        
        mul_tree(compressed_witness,counter);
        int wit_prod = counter-1;

        mul_tree(compressed_leaf,counter);
        int leaf_prod = counter-1;

        mul_tree(compressed_node,counter);
        mul(counter-1,root,counter);
        int val1 = counter-1;
        mul(counter-2,leaf_prod,counter);
        int val2 = counter-1;

        mul_tree(compressed_out,counter);
        
        sub(counter-1,val1,counter);
        sub(wit_prod,val2,counter);
    }
    
    /*
    */
}


void parse_check_coordinates(ifstream &circuit_in, long long int *in, int leaves, int nodes){
    int leaf_size = 2*leaves;
    if(1ULL << ((int)log2(2*leaves)) != 2*leaves){
        leaf_size = 1ULL << ((int)log2(2*leaves)+1);
    }
    int nodes_size = 2*nodes;
    if(1ULL << ((int)log2(2*nodes)) != 2*nodes){
        nodes_size = 1ULL << ((int)log2(2*nodes)+1);
    }
    int witness_size = 2*(leaves+nodes-1);
    if(1ULL << ((int)log2(witness_size)) != witness_size){
        witness_size = 1ULL << ((int)log2(witness_size)+1);
    }
    vector<int> leaf_coord(leaf_size),node_coord(nodes_size);
    vector<int> witness_coord(witness_size);
    int counter = 0;
    for(int i = 0; i < witness_coord.size(); i++){
        buildInput(counter, 0);
        witness_coord[i] = counter;
        counter++;    
    }
    for(int i = 0; i < node_coord.size(); i++){
        buildInput(counter, 0);
        node_coord[i] = counter;
        counter++;    
    }
    for(int i = 0; i < leaf_coord.size(); i++){
        buildInput(counter, 0);
        leaf_coord[i] = counter;
        counter++;   
    }
    int nodes2_size = nodes;
    if(1ULL << ((int)log2(nodes2_size)) != nodes2_size){
        nodes2_size = 1ULL << ((int)log2(nodes2_size)+1);
    }
    int com_witness_size = leaves+nodes-1;
    if(1ULL << ((int)log2(com_witness_size)) != com_witness_size){
        com_witness_size = 1ULL << ((int)log2(com_witness_size)+1);
    }
    int comp_leaves = leaves;
    if(1ULL << ((int)log2(comp_leaves)) != comp_leaves){
        comp_leaves = 1ULL << ((int)log2(comp_leaves)+1);
    }
    vector<int> compressed_leaf_hist(comp_leaves),compressed_node_hist(nodes2_size);
    vector<int> compressed_witness_hist(com_witness_size),compressed_out_hist(nodes2_size);
    

    for(int i = 0; i < compressed_witness_hist.size(); i++){
        buildInput(counter, 0);
        compressed_witness_hist[i] = counter;
        counter++;    
    }
    for(int i = 0; i < compressed_node_hist.size(); i++){
        buildInput(counter, 0);
        compressed_node_hist[i] = counter;
        counter++;
    }
    
    for(int i = 0; i < compressed_out_hist.size(); i++){
        buildInput(counter, 0);
        compressed_out_hist[i] = counter;
        counter++;    
    }
    for(int i = 0; i < compressed_leaf_hist.size(); i++){
        buildInput(counter, 0);
        compressed_leaf_hist[i] = counter;
        counter++;   
    }

    buildInput(counter, 0);
    int a = counter;
    counter++;
    buildInput(counter, 0);
    int b = counter;
    counter++;
    buildInput(counter, 0);
    int c = counter;
    counter++;
    buildInput(counter,0);
    int r = counter;
    counter++;
    buildInput(counter, 0);
    int two_inv = counter;
    counter++;
    buildInput(counter, 0);
    int one = counter;
    counter++;
    
    vector<int> out_coord(2*nodes);
    vector<int> compressed_leaf(leaves),compressed_node(nodes-1),compressed_witness(leaves+nodes-1),compressed_out(nodes);
    for(int i = 0; i < leaves; i++){
        mul(leaf_coord[2*i],a,counter);
        mul(leaf_coord[2*i+1],b,counter);
        add(counter-1,counter-2,counter);
        mul(compressed_leaf_hist[i],r,counter);
        add(counter-1,counter-2,counter);
        sub(counter-1,c,counter);   
        
        compressed_leaf[i] = counter-1;
    }

    for(int i = 0; i < nodes-1; i++){
        mul(node_coord[2*i],a,counter);
        mul(node_coord[2*i+1],b,counter);
        add(counter-1,counter-2,counter);
        mul(compressed_node_hist[i],r,counter);
        add(counter-1,counter-2,counter);
        sub(counter-1,c,counter);   
        compressed_node[i] = counter-1;
    }

    int root;
    mul(node_coord[2*(nodes-1)],a,counter);
    mul(node_coord[2*(nodes-1)+1],b,counter);
    add(counter-1,counter-2,counter);
    mul(compressed_node_hist[nodes-1],r,counter);
    add(counter-1,counter-2,counter);
    sub(counter-1,c,counter);   
    root = counter-1;

    for(int i = 0; i < nodes+leaves-1; i++){
        mul(witness_coord[2*i],a,counter);
        mul(witness_coord[2*i+1],b,counter);
        add(counter-1,counter-2,counter);
        mul(compressed_witness_hist[i],r,counter);
        add(counter-1,counter-2,counter);
        sub(counter-1,c,counter);   
        compressed_witness[i] = counter-1;
    }
    
    for(int i = 0; i < (nodes+leaves-1)/2; i++){
        sub(witness_coord[4*i],one,counter);
        mul(witness_coord[4*i+1],two_inv,counter);
        out_coord[2*i] = counter-2;
        out_coord[2*i+1] = counter-1;
    }
    for(int i = 0; i < nodes; i++){
        mul(out_coord[2*i],a,counter);
        mul(out_coord[2*i+1],b,counter);
        add(counter-1,counter-2,counter);
        mul(compressed_out_hist[i],r,counter);
        add(counter-1,counter-2,counter);
        
        sub(counter-1,c,counter);   
        compressed_out[i] = counter-1;
    }
    
    mul_tree(compressed_witness,counter);
    int wit_prod = counter-1;

    mul_tree(compressed_leaf,counter);
    int leaf_prod = counter-1;

    mul_tree(compressed_node,counter);
    mul(counter-1,root,counter);
    int val1 = counter-1;
    mul(counter-2,leaf_prod,counter);
    int val2 = counter-1;

    mul_tree(compressed_out,counter);
    
    sub(counter-1,val1,counter);
    sub(wit_prod,val2,counter);
    /*
    */
}

void parse_node_sum(ifstream &circuit_in, long long int *in, int hist_size, int leaves, int nodes){
    int padded_hist_size = hist_size;
    if(1ULL<<((int)log2(padded_hist_size)) != padded_hist_size){
        padded_hist_size = 1ULL<<((int)log2(padded_hist_size)+1);
    }



    vector<int> witness(leaves*padded_hist_size);
    int counter = 0;
    
    for(int i = 0; i < witness.size(); i++){
        buildInput(counter, 0);
        witness[i] = counter;
        counter++;   
    }
    
    for(int i = 0; i < leaves; i+=2){
        for(int j = 0; j < padded_hist_size; j++){
            add(witness[i*padded_hist_size + j],witness[(i+1)*(padded_hist_size) +j],counter);
        }
    }

}

void parse_histogram_check(ifstream &circuit_in, long long int *in, int N,int Attr,int compressed_size){
    vector<int> read_transcript(Attr*N*8),write_transcript(Attr*N*8);
    vector<int> input(N*(2*Attr+2));
    vector<int> compressed_read(compressed_size),compressed_write(compressed_size);
    int counter = 0;
    for(int i = 0; i < read_transcript.size(); i++){
        buildInput(counter, 0);
        read_transcript[i] = counter;
        counter++;
    }
    for(int i = 0; i < write_transcript.size(); i++){
        buildInput(counter, 0);
        write_transcript[i] = counter;
        counter++;
    }
    for(int i = 0; i < input.size(); i++){
        buildInput(counter, 0);
        input[i] = counter;
        counter++;
    }
    /*
    for(int i = 0; i < compressed_read.size(); i++){
        buildInput(counter, 0);
        compressed_read[i] = counter;
        counter++;
    }
    for(int i = 0; i < compressed_write.size(); i++){
        buildInput(counter, 0);
        compressed_write[i] = counter;
        counter++;
    }
    */
    buildInput(counter, 0);
    int c = counter;
    counter++;
    
    for(int i = 0; i < N; i++){
        int input_offset = (2*Attr+2);
        int mem_offset = 8*(Attr);
        
        for(int j = 0; j < Attr; j++){
            sub(input[i*input_offset + 2*j],read_transcript[i*mem_offset + 8*j+1],counter);
            sub(input[i*input_offset + 2*j+1],read_transcript[i*mem_offset + 8*j+2],counter);
            sub(input[i*input_offset + 2*Attr],read_transcript[i*mem_offset + 8*j],counter);
            sub(input[i*input_offset + 2*Attr+1],read_transcript[i*mem_offset + 8*j+3],counter);
            sub(input[i*input_offset + 2*j],write_transcript[i*mem_offset + 8*j+1],counter);
            sub(input[i*input_offset + 2*j+1],write_transcript[i*mem_offset + 8*j+2],counter);
            sub(input[i*input_offset + 2*Attr],write_transcript[i*mem_offset + 8*j],counter);
            sub(input[i*input_offset + 2*Attr+1],write_transcript[i*mem_offset + 8*j+3],counter);
            sub(write_transcript[i*mem_offset + 8*j+4],read_transcript[i*mem_offset + 8*j+4],counter);

        }
    }
    /*
    int check1,check2;
    mul_tree(compressed_read,counter);
    check1 = counter-1;
    mul_tree(compressed_write,counter);
    check2 = counter-1;
    sub(check1,check1,counter);
    */
}


void parse_path_consistency(ifstream &circuit_in, long long int *in, int Attr, int max_depth, int N){
    vector<int> path(N*(3*max_depth+2));
    vector<int> perm_input(N*(2*Attr+2));
    int counter = 0;
    for(int i = 0; i < path.size(); i++){
        buildInput(counter, 0);
        path[i] = counter;
        counter++;
    }
    for(int i = 0; i < perm_input.size(); i++){
        buildInput(counter, 0);
        perm_input[i] = counter;
        counter++;   
    }
    buildInput(counter, 0);
    int zero = counter;
    counter++;
    
    for(int i = 0; i < N; i++){
        sub(path[i*(3*max_depth+2)],perm_input[i*(2*Attr+2) + 2*Attr],counter);
    }

    add(path[0],zero,counter);
    for(int i = 1; i < N; i++){
        sub(path[(i)*(3*max_depth+2)],path[(i-1)*(3*max_depth+2)],counter);
    }
    
}


void parse_batch_inference(ifstream &circuit_in, long long int *in, int diff_size, int Attr, int max_depth, int N, int path_col,int perm_col){
    vector<vector<int>> path(N);//*path_col);
    vector<vector<int>> perm_input(N);//*perm_col);
    int counter = 0;
    printf("(%d,%d),(%d,%d)\n",N,path_col,N,perm_col);
    for(int i = 0; i < path.size(); i++){
        path[i].resize(path_col);
        for(int j = 0; j < path_col; j++){
            buildInput(counter, 0);
            path[i][j] = counter;
            counter++;
        }
    }
    for(int i = 0; i < perm_input.size(); i++){
        perm_input[i].resize(perm_col);
        for(int j = 0; j < perm_col; j++){
            buildInput(counter, 0);
            perm_input[i][j] = counter;
            counter++;   
        }
    }
    buildInput(counter, 0);
    int one = counter;
    counter++;
    buildInput(counter,0);
    int two_inv = counter;
    counter++;
    buildInput(counter,0);
    int zero = counter;
    counter++;
    
    for(int j = 0; j < diff_size; j++){
        for(int i = 0; i < max_depth; i++){
            // If path == 1 
            sub(perm_input[j][2*i+1],path[j][3*i+1],counter);
            add(one,path[j][3*i+2+1],counter);
            mul(counter-1,counter-2,counter);
            mul(two_inv,path[j][3*i+2+1],counter);
            sub(counter-1,one,counter);
            mul(counter-3,counter-1,counter);
        }
    }
    
    for(int j = 0; j < diff_size; j++){        
        for(int i = 0; i < max_depth; i++){
            sub(path[j][3*i+1+1],perm_input[j][2*i],counter);
        }
    }
    for(int i = 0; i < N; i++){
        sub(path[i][0],perm_input[i][2*Attr],counter);
    }
    add(path[0][0],zero,counter);
    for(int i = 1; i < N; i++){
        sub(path[(i)][0],path[(i-1)][0],counter);
    }
}

void inference_parse(ifstream &circuit_in, long long int *in, int Attr, int max_depth, int trees){
    vector<int> path(4*max_depth*trees);
    vector<int> perm_input(2*Attr*trees);
    int counter = 0;
    for(int i = 0; i < path.size(); i++){
        buildInput(counter, 0);
        path[i] = counter;
        counter++;
    }
    for(int i = 0; i < perm_input.size(); i++){
        buildInput(counter, 0);
        perm_input[i] = counter;
        counter++;       
    }
    buildInput(counter, 0);
    int one = counter;
    counter++;
    buildInput(counter,0);
    int two_inv = counter;
    counter++;
    for(int i = 0; i < trees*max_depth; i++){
        // If path == 1 
        sub(perm_input[2*i+1],path[4*i],counter);
        mul(counter-1,path[4*i+2],counter);
        add(path[4*i+2],one,counter);
        mul(counter-1,two_inv,counter);
        mul(counter-1,counter-3,counter);
        int temp = counter-1;
        
        sub(path[4*i],perm_input[2*i+1],counter);
        sub(one,path[4*i+2],counter);
        mul(counter-1,counter-2,counter);
        add(path[4*i+2],one,counter);
        mul(counter-1,counter-2,counter);
        add(counter-1,temp,counter);
    }
    for(int i = 0; i < trees*max_depth; i++){
        sub(path[4*i+1],perm_input[2*i],counter);
    }
}

void parse_single_inference_phase2(ifstream &circuit_in, long long int *in, int Attr, int max_depth){
    vector<int> path(3*max_depth+2);
    vector<int> perm_input(2*Attr);
    
    int counter = 0;

    for(int i = 0; i < path.size(); i++){
        buildInput(counter, 0);
        path[i] = counter;
        counter++;
    }
    for(int i = 0; i < perm_input.size(); i++){
        buildInput(counter, 0);
        perm_input[i] = counter;
        counter++;   
    }
    buildInput(counter, 0);
    int one = counter;
    counter++;
    buildInput(counter,0);
    int two_inv = counter;
    counter++;
    
    for(int i = 0; i < max_depth; i++){
        // If path == 1 
        sub(perm_input[2*i+1],path[3*i+1],counter);
        mul(counter-1,path[3*i+2+1],counter);
        add(path[3*i+2+1],one,counter);
        mul(counter-1,two_inv,counter);
        mul(counter-1,counter-3,counter);
        int temp = counter-1;
        
        sub(path[3*i+1],perm_input[2*i+1],counter);
        sub(one,path[3*i+2+1],counter);
        mul(counter-1,counter-2,counter);
        add(path[3*i+2+1],one,counter);
        mul(counter-1,counter-2,counter);
        add(counter-1,temp,counter);
    }
    for(int i = 0; i < max_depth; i++){
        sub(path[3*i+1+1],perm_input[2*i],counter);
    }
}

void parse_permutation_check_partitions(ifstream &circuit_in, long long int *in, int N,int Attr){
    vector<int> input(N*(2*Attr+2)),perm_input(N*(2*Attr+2));
    int counter = 0;
    for(int i = 0; i < input.size(); i++){
        buildInput(counter, 0);
        input[i] = counter;
        counter++;
    }
    for(int i = 0; i < perm_input.size(); i++){
        buildInput(counter, 0);
        perm_input[i] = counter;
        counter++;   
    }
    

    buildInput(counter, 0);
    int a = counter;
    counter++;
    buildInput(counter, 0);
    int b = counter;
    counter++;
    buildInput(counter, 0);
    int c = counter;
    counter++;

   
}

void parse_permutation_check_partitions_data(ifstream &circuit_in, long long int *in, int N,int nodes,int Attr){
    vector<int> input(N*(2*Attr+2)),perm_input(N*(2*Attr+2));
    
    //vector<int> compressed_input(N),compressed_perm_input(N);
    
    // parse tree permutation checks
    vector<int> compressed_path(N),compressed_tree(nodes);
    vector<int> powers(25*nodes);
    vector<int> power_bits(32*nodes);

    int counter = 0;
    for(int i = 0; i < input.size(); i++){
        buildInput(counter, 0);
        input[i] = counter;
        counter++;
    }
    for(int i = 0; i < perm_input.size(); i++){
        buildInput(counter, 0);
        perm_input[i] = counter;
        counter++;   
    }
    /*
    for(int i = 0; i < N; i++){
        buildInput(counter, 0);
        compressed_input[i] = counter;
        counter++;
    }
    for(int i = 0; i < N; i++){
        buildInput(counter, 0);
        compressed_perm_input[i] = counter;
        counter++;   
    }
    */
    /// Permutation checks
    for(int i = 0; i < N; i++){
        buildInput(counter, 0);
        compressed_path[i] = counter;
        counter++;
    }
    for(int i = 0; i < nodes; i++){
        buildInput(counter, 0);
        compressed_tree[i] = counter;
        counter++;   
    }
    for(int i = 0; i < powers.size(); i++){
        buildInput(counter, 0);
        powers[i] = counter;
        counter++;
    }
    for(int i = 0; i < 32*nodes; i++){
        buildInput(counter, 0);
        power_bits[i] = counter;
        counter++;
    }


    buildInput(counter, 0);
    int a = counter;
    counter++;
    buildInput(counter, 0);
    int b = counter;
    counter++;
    buildInput(counter, 0);
    int c = counter;
    counter++;

    buildInput(counter, 0);
    int one = counter;
    counter++;

    // Data check
    /*
    vector<int> check1_vector(N),check2_vector(N);
    for(int i = 0; i < N; i++){
        sub(compressed_input[i],c,counter);
        check1_vector[i] = counter-1;
    }
    for(int i = 0; i < N; i++){
        sub(compressed_perm_input[i],c,counter);
        check2_vector[i] = counter-1;
    }
    mul_tree(check2_vector,counter);
    int final_check1 = counter-1;
    mul_tree(check2_vector,counter);
    int final_check2 = counter-1;
    sub(final_check1,final_check2,counter);
    */
    // tree check
    vector<int> final_powers(nodes);
    for(int i = 0; i < nodes; i++){
        vector<int> temp;
        for(int j = 0; j < 25; j++){
            sub(one,power_bits[i*32 + j],counter);
            mul(powers[i*25+j],power_bits[i*32+j],counter);
            add(counter-1,counter-2,counter);
            temp.push_back(counter-1);
        }
        mul_tree(temp,counter);
        final_powers[i] = counter-1;
    }
    // check correctness of powers
    for(int i = 0; i < nodes; i++){
        sub(compressed_tree[i],c,counter);
        sub(counter-1,powers[25*i],counter);
    }
    // check power consistency
    
    for(int i = 0; i < nodes; i++){
        for(int j = 0; j < 24; j++){
            mul(powers[25*i + j],powers[25*i + j],counter);
            sub(counter-1,powers[25*i + j+1],counter);
        }
    }
    
    mul_tree(final_powers,counter);
    int check1 = counter-1;
    mul_tree(compressed_path,counter);
    sub(counter-1,check1,counter);
    /*
    vector<int> compressed_input_check(Attr+2);   
    vector<int> compressed_perm_input_check(Attr+2);   
    vector<int> new_input(N),new_perm_input(N);
    
    for(int i = 0; i < N; i++){
        for(int j = 0; j < Attr; j++){
            mul(a,input[i*(2*Attr+2) + 2*j],counter);
            mul(b,input[i*(2*Attr+2) + 2*j+1],counter);
            add(counter-1,counter-2,counter);
            sub(counter-1,c,counter);
            compressed_input_check[j] = counter-1;
        }
        sub(input[i*(2*Attr+2) + 2*Attr],c,counter);
        compressed_input_check[Attr] = counter-1;
        sub(input[i*(2*Attr+2) + 2*Attr+1],c,counter);
        compressed_input_check[Attr+1] = counter-1;
        mul_tree(compressed_input_check,counter);
        new_input[i] = counter-1;
    }
    for(int i = 0; i < N; i++){
        for(int j = 0; j < Attr; j++){
            mul(a,perm_input[i*(2*Attr+2) + 2*j],counter);
            mul(b,perm_input[i*(2*Attr+2) + 2*j+1],counter);
            add(counter-1,counter-2,counter);
            sub(counter-1,c,counter);
            compressed_perm_input_check[j] = counter-1;
        }
        sub(perm_input[i*(2*Attr+2) + 2*Attr],c,counter);
        compressed_perm_input_check[Attr] = counter-1;
        sub(perm_input[i*(2*Attr+2) + 2*Attr+1],c,counter);
        compressed_perm_input_check[Attr+1] = counter-1;
        mul_tree(compressed_perm_input_check,counter);
        new_perm_input[i] = counter-1;    
    }
    for(int i = 0; i < N; i++){
        sub(new_input[i],new_perm_input[i],counter);
    }
    */
}

void parse_permutation_check_partitions_tree(ifstream &circuit_in, long long int *in, int N, int nodes){
    vector<int> compressed_path(N),compressed_tree(nodes);
    vector<int> powers(25*nodes);
    vector<int> power_bits(32*nodes);
    
    int counter = 0;

    for(int i = 0; i < N; i++){
        buildInput(counter, 0);
        compressed_path[i] = counter;
        counter++;
    }
    for(int i = 0; i < nodes; i++){
        buildInput(counter, 0);
        compressed_tree[i] = counter;
        counter++;   
    }
    for(int i = 0; i < powers.size(); i++){
        buildInput(counter, 0);
        powers[i] = counter;
        counter++;
    }
    for(int i = 0; i < 32*nodes; i++){
        buildInput(counter, 0);
        power_bits[i] = counter;
        counter++;
    }
    buildInput(counter, 0);
    int one = counter;
    counter++;
    
    buildInput(counter, 0);
    int c = counter;
    counter++;
    

    vector<int> final_powers(nodes);
    for(int i = 0; i < nodes; i++){
        vector<int> temp;
        for(int j = 0; j < 25; j++){
            sub(one,power_bits[i*32 + j],counter);
            mul(powers[i*25+j],power_bits[i*32+j],counter);
            add(counter-1,counter-2,counter);
            temp.push_back(counter-1);
        }
        mul_tree(temp,counter);
        final_powers[i] = counter-1;
    }
    // check correctness of powers
    for(int i = 0; i < nodes; i++){
        sub(compressed_tree[i],c,counter);
        sub(counter-1,powers[25*i],counter);
    }
    // check power consistency
    
    for(int i = 0; i < nodes; i++){
        for(int j = 0; j < 24; j++){
            mul(powers[25*i + j],powers[25*i + j],counter);
            sub(counter-1,powers[25*i + j+1],counter);
        }
    }
    
    mul_tree(final_powers,counter);
    int check1 = counter-1;
    mul_tree(compressed_path,counter);
    sub(counter-1,check1,counter);


}

void parse_permutation_check(ifstream &circuit_in, long long int *in, int Attr){
    //vector<int> path(3*Attr+1);
    vector<int> input(2*Attr),perm_input(2*Attr);
    vector<int> compressed_input(Attr),compressed_perm_input(Attr);

    int counter = 0;
    //for(int i = 0; i < path.size(); i++){
    //    buildInput(counter, 0);
    //    path[i] = counter;
    //    counter++;
    //}
    for(int i = 0; i < input.size(); i++){
        buildInput(counter, 0);
        input[i] = counter;
        counter++;
    }
    for(int i = 0; i < perm_input.size(); i++){
        buildInput(counter, 0);
        perm_input[i] = counter;
        counter++;   
    }
    
    int a,b;
    buildInput(counter, 0);
    a = counter;
    counter++;   
    buildInput(counter, 0);
    b = counter;
    counter++;
    for(int i = 0; i < Attr; i++){
        mul(a,input[2*i],counter);
        mul(b,input[2*i+1],counter);
        add(counter-1,counter-2,counter);
        compressed_input[i] = counter-1;
    }
    for(int i = 0; i < Attr; i++){
        mul(a,perm_input[2*i],counter);
        mul(b,perm_input[2*i+1],counter);
        add(counter-1,counter-2,counter);
        compressed_perm_input[i] = counter-1;
    }
    mul_tree(compressed_input,counter);
    int val1 = counter-1;
    mul_tree(compressed_perm_input,counter);
    int val2 = counter-1;
    sub(val1,val2,counter);
}

// Returns the final sum
int verify_lookup(lookup_proof_indexes P, vector<int> powers, int one, int &counter){
    P.mul_proofs[0].first_r = P.r1;
    int final_sum = mul_tree_verification_circuit(P.mul_proofs[0],one,counter);
    sub(P.write_eval,P.read_eval,counter);
    mul(counter-1,P.mul_proofs[0].global_randomness[P.mul_proofs[0].global_randomness.size()-1],counter);
    add(P.read_eval,counter-1,counter);
    sub(final_sum,counter-1,counter);
    P.mul_proofs[1].first_r = P.r2;
    final_sum = mul_tree_verification_circuit(P.mul_proofs[1],one,counter);
    
    mul(P.a,P.read_eval1,counter);
    mul(P.b,P.read_eval2,counter);
    add(counter-2,counter-1,counter);
    add(counter-1,P.c,counter);
    sub(P.read_eval,counter-1,counter);

    mul(P.a,P.write_eval1,counter);
    mul(P.b,P.write_eval2,counter);
    add(counter-2,counter-1,counter);
    add(counter-1,P.c,counter);
    sub(P.write_eval,counter-1,counter);
    sub(P.write_eval1,P.read_eval1,counter);
    sub(P.write_eval2,P.read_eval2,counter);
    
    vector<int> temp_prod;
    for(int i = 0; i < P.indexes_eval.size(); i++){
        mul(P.indexes_eval[i],powers[i],counter);
        temp_prod.push_back(counter-1);
    }
    add_tree(temp_prod,counter);
    return counter-1;
}

void parse_proof_recursion(ifstream &circuit_in, long long int *in, vector<partition_indexes> P1,vector<histogram_indexes> P2 ,vector<node_histogram_indexes> P3, vector<split_indexes> P4, int input_size){
    vector<int> proof(input_size);
    int counter = 0;
    for(int i = 0; i < input_size; i++){
        buildInput(counter, 0);
        proof[i] = counter;
        counter++;   
    }
    int one = counter;
    buildInput(counter, 0);
    counter++;
    int zero = counter;
    buildInput(counter, 0);
    counter++;
    int two =  counter;
    buildInput(counter, 0);
    counter++;
    vector<int> powers(8);
    for(int i = 0; i < 8; i++){
        powers[i] = counter;
        buildInput(counter, 0);
        counter++;
    }

    

    for(int j = 0; j < P1.size(); j++){

        int final_sum;
        vector<int> prev_rand;
       
        mul_tree_verification_circuit(P1[j].mul_proofs[0], one, counter);
        
        mul(P1[j].aggr_r[0],P1[j].eval1_perm_data,counter);
        mul(P1[j].aggr_r[1],P1[j].eval2_perm_data,counter);
        add(counter-1,counter-2,counter);
        P1[j].sumcheck2Prod_proofs[0].sum = counter-1;
        verify_2sumcheck(P1[j].sumcheck2Prod_proofs[0],one,counter);
        final_sum = mul_tree_verification_circuit(P1[j].mul_proofs[1], one, counter);
        int size = P1[j].mul_proofs[1].randomness.size()-1;
        int x = P1[j].mul_proofs[1].randomness[size][P1[j].mul_proofs[1].randomness[size].size()-1];

        sub(P1[j].eval_perm_input,P1[j].eval_input,counter);
        mul(x,counter-1,counter);
        sub(final_sum,P1[j].eval_input,counter);
        add(counter-1,counter-2,counter);

        sub(P1[j].eval_input,P1[j]._c,counter);
        P1[j].sumcheck2Prod_proofs[1].sum = counter-1;
        verify_2sumcheck(P1[j].sumcheck2Prod_proofs[1],one,counter);
        mul(P1[j].aggr_r[0],P1[j].eval1_data,counter);
        mul(P1[j].aggr_r[1],P1[j].eval2_data,counter);  
        add(counter-1,counter-2,counter);
        mul(P1[j].aggr_r[2],P1[j].eval3_data,counter);  
        add(counter-1,counter-2,counter);
        P1[j].sumcheck2Prod_proofs[2].sum = counter-1;
        verify_2sumcheck(P1[j].sumcheck2Prod_proofs[2],one,counter);
        sub(P1[j].eval_perm_input,P1[j]._c,counter);
        P1[j].sumcheck2Prod_proofs[3].sum = counter-1;
        verify_2sumcheck(P1[j].sumcheck2Prod_proofs[3],one,counter);
        
        final_sum = mul_tree_verification_circuit(P1[j].mul_proofs[2], one, counter);

        sub(final_sum,one,counter);
        P1[j].sumcheck2Prod_proofs[4].sum = counter-1;
        verify_2sumcheck(P1[j].sumcheck2Prod_proofs[4],one,counter);
        final_sum = mul_tree_verification_circuit(P1[j].mul_proofs[3], one, counter);
        sub(P1[j].mul_proofs[2].initial_sum,P1[j].mul_proofs[3].initial_sum,counter);
        
        P1[j].mul_proofs[4].initial_sum = final_sum;
      
        final_sum = mul_tree_verification_circuit(P1[j].mul_proofs[4], one, counter);
      
        sub(P1[j].final_powers_input_eval,P1[j].eval_bits1,counter);
        add(one,counter-1,counter);
        sub(final_sum,counter-1,counter);
        
        prev_rand = P1[j].mul_proofs[4].individual_randomness;
        for(int i = 0; i< P1[j].mul_proofs[4].global_randomness.size(); i++){
            prev_rand.push_back(P1[j].mul_proofs[4].global_randomness[i]);
        }
        verify_3sumcheck(P1[j].sumcheck3Prod_proofs[0].polynomials, P1[j].sumcheck3Prod_proofs[0].randomness, prev_rand, P1[j].sumcheck3Prod_proofs[0].vr[0], P1[j].sumcheck3Prod_proofs[0].vr[1], P1[j].final_powers_input_eval,  one,counter);

        sub(P1[j].eval_powers2,one,counter);
        P1[j].sumcheck2Prod_proofs[5].sum = counter-1;
        verify_2sumcheck(P1[j].sumcheck2Prod_proofs[5],one,counter);

        prev_rand.clear();
        verify_3sumcheck(P1[j].sumcheck3Prod_proofs[1].polynomials, P1[j].sumcheck3Prod_proofs[1].randomness, prev_rand, P1[j].sumcheck3Prod_proofs[1].vr[0], P1[j].sumcheck3Prod_proofs[1].vr[1], P1[j].sum1,  one,counter);
        P1[j].sumcheck2Prod_proofs[6].sum = P1[j].sum1;
        verify_2sumcheck(P1[j].sumcheck2Prod_proofs[6],one,counter);
        
        mul(P1[j].r2[0],P1[j].sumcheck3Prod_proofs[0].vr[1],counter);
        mul(P1[j].r2[1],P1[j].eval_powers2,counter);
        add(counter-1,counter-2,counter);
        mul(P1[j].r2[2],P1[j].sumcheck3Prod_proofs[1].vr[1],counter);
        mul(P1[j].r2[3],P1[j].sumcheck2Prod_proofs[6].vr[1],counter);
        add(counter-1,counter-2,counter);
        add(counter-1,counter-4,counter);
        P1[j].sumcheck2Prod_proofs[7].sum = counter-1;
        verify_2sumcheck(P1[j].sumcheck2Prod_proofs[7],one,counter);
        P1[j].sumcheck2Prod_proofs[8].sum = P1[j].diff_eval;
        verify_2sumcheck(P1[j].sumcheck2Prod_proofs[8],one,counter);
        verify_3sumcheck(P1[j].sumcheck3Prod_proofs[2].polynomials, P1[j].sumcheck3Prod_proofs[2].randomness, P1[j].range_proof_rand, P1[j].sumcheck3Prod_proofs[2].vr[0], P1[j].sumcheck3Prod_proofs[2].vr[1], zero,  one,counter);

        P1[j].GKR.sum = P1[j].diff_eval;
        verify_gkr(P1[j].GKR,one,counter);

        /*
        */
        ////////////////// HISTOGRAM PROOF
        final_sum = mul_tree_verification_circuit(P2[j].mul_proofs[0], one, counter);
        sub(P2[j].peval2,P2[j].peval1,counter);
        mul(P2[j].mul_proofs[0].global_randomness[0],counter-1,counter);
        add(P2[j].peval1,counter-1,counter);
        sub(final_sum,counter-1,counter);

        sub(P2[j].peval1,one,counter);
        P2[j].sumcheck2Prod_proofs[0].sum = counter-1;
        verify_2sumcheck(P2[j].sumcheck2Prod_proofs[0],one,counter);
        sub(P2[j].peval2,one,counter);
        P2[j].sumcheck2Prod_proofs[1].sum = counter-1;
        verify_2sumcheck(P2[j].sumcheck2Prod_proofs[1],one,counter);
        mul_tree_verification_circuit(P2[j].mul_proofs[1], one, counter);
        sub(P2[j].peval3,one,counter);
        P2[j].sumcheck2Prod_proofs[2].sum = counter-1;
        verify_2sumcheck(P2[j].sumcheck2Prod_proofs[2],one,counter);
        sub(P2[j].input_evals[0],P2[j].read_evals[1],counter);    
        sub(P2[j].input_evals[0],P2[j].write_evals[1],counter);    
        sub(P2[j].input_evals[1],P2[j].read_evals[2],counter);    
        sub(P2[j].input_evals[1],P2[j].write_evals[2],counter);    
        sub(P2[j].metadata_evals[0],P2[j].read_evals[0],counter);    
        sub(P2[j].metadata_evals[0],P2[j].write_evals[0],counter);    
        sub(P2[j].metadata_evals[1],P2[j].read_evals[3],counter);    
        sub(P2[j].metadata_evals[1],P2[j].write_evals[3],counter);    
        sub(P2[j].write_evals[4],P2[j].read_evals[4],counter);
        sub(counter-1,one,counter);
       
        mul(P2[j].r[0],P2[j].read_evals[0],counter);
        mul(P2[j].r[1],P2[j].read_evals[1],counter);
        add(counter-1,counter-2,counter);
        mul(P2[j].r[2],P2[j].read_evals[2],counter);
        mul(P2[j].r[3],P2[j].read_evals[3],counter);
        add(counter-1,counter-2,counter);
        add(counter-1,counter-4,counter);
        mul(P2[j].r[4],P2[j].read_evals[4],counter);
        add(counter-1,counter-2,counter);
        P2[j].sumcheck2Prod_proofs[3].sum = counter-1;
        mul(P2[j].r[0],P2[j].write_evals[0],counter);
        mul(P2[j].r[1],P2[j].write_evals[1],counter);
        add(counter-1,counter-2,counter);
        mul(P2[j].r[2],P2[j].write_evals[2],counter);
        mul(P2[j].r[3],P2[j].write_evals[3],counter);
        add(counter-1,counter-2,counter);
        add(counter-1,counter-4,counter);
        mul(P2[j].r[4],P2[j].write_evals[4],counter);
        add(counter-1,counter-2,counter);
        P2[j].sumcheck2Prod_proofs[4].sum = counter-1;
        mul(P2[j].r[0],P2[j].input_evals[0],counter);
        mul(P2[j].r[1],P2[j].input_evals[1],counter);
        add(counter-1,counter-2,counter);
        P2[j].sumcheck2Prod_proofs[5].sum = counter-1;
        mul(P2[j].r[0],P2[j].metadata_evals[0],counter);
        mul(P2[j].r[1],P2[j].metadata_evals[1],counter);
        add(counter-1,counter-2,counter);
        P2[j].sumcheck2Prod_proofs[6].sum = counter-1;
        verify_2sumcheck(P2[j].sumcheck2Prod_proofs[3],one,counter);
        verify_2sumcheck(P2[j].sumcheck2Prod_proofs[4],one,counter);
        verify_2sumcheck(P2[j].sumcheck2Prod_proofs[5],one,counter);
        verify_2sumcheck(P2[j].sumcheck2Prod_proofs[6],one,counter);
        /*
        */
        /********************************************/
        ////////////////// Nodes Histogram PROOF
     
        P3[j].GKR1.sum = zero;
        verify_gkr(P3[j].GKR1,one,counter);

        P3[j].sumcheck2Prod_proofs[0].sum = P3[j].comp_wit_eval;
        P3[j].sumcheck2Prod_proofs[1].sum = P3[j].comp_out_eval;
        P3[j].sumcheck2Prod_proofs[2].sum = P3[j].comp_leaf_eval;
        P3[j].sumcheck2Prod_proofs[3].sum = P3[j].comp_node_eval;
        verify_2sumcheck(P3[j].sumcheck2Prod_proofs[0],one,counter);
        verify_2sumcheck(P3[j].sumcheck2Prod_proofs[1],one,counter);
        verify_2sumcheck(P3[j].sumcheck2Prod_proofs[2],one,counter);
        verify_2sumcheck(P3[j].sumcheck2Prod_proofs[3],one,counter);
        P3[j].GKR2.sum = P3[j].sumcheck2Prod_proofs[1].vr[0];
        verify_gkr(P3[j].GKR2,one,counter);
     

        /********************************************/

        ////////////////// SPLIT PROOF
        final_sum = verify_lookup(P4[j].lookup_indexes[0],powers,one,counter);
        sub(P4[j].ginis_eval1,P4[j].best_gini_eval1,counter);
        sub(final_sum,counter-1,counter);
        final_sum = mul_tree_verification_circuit(P4[j].mul_proof,one,counter);
        sub(P4[j].ginis_eval2,P4[j].best_gini_eval2,counter);
        sub(final_sum,counter-1,counter);
        final_sum = verify_lookup(P4[j].lookup_indexes[1],powers,one,counter);
        mul(powers[1],P4[j].dividents_cond_eval,counter);
        sub(counter-1,P4[j].divisors_quot_eval,counter);
        sub(counter-1,final_sum,counter);

        verify_3sumcheck(P4[j].sumcheck3Prod_proofs[0].polynomials, P4[j].sumcheck3Prod_proofs[0].randomness, P4[j].lookup_indexes[1].x1, P4[j].sumcheck3Prod_proofs[0].vr[0], P4[j].sumcheck3Prod_proofs[0].vr[1], P4[j].divisors_quot_eval,  one,counter);
        verify_3sumcheck(P4[j].sumcheck3Prod_proofs[1].polynomials, P4[j].sumcheck3Prod_proofs[1].randomness, P4[j].lookup_indexes[1].x1, P4[j].sumcheck3Prod_proofs[1].vr[0], P4[j].sumcheck3Prod_proofs[1].vr[1], P4[j].dividents_cond_eval,  one,counter);
        verify_3sumcheck(P4[j].sumcheck3Prod_proofs[2].polynomials, P4[j].sumcheck3Prod_proofs[2].randomness, P4[j].lookup_indexes[1].x1, P4[j].sumcheck3Prod_proofs[2].vr[0], P4[j].sumcheck3Prod_proofs[2].vr[1], zero,  one,counter);
        sub(one,P4[j].sumcheck3Prod_proofs[2].vr[1],counter);
        int cond2_eval = counter-1;
        int cond1_eval = P4[j].sumcheck3Prod_proofs[1].vr[0];
        mul(cond1_eval,P4[j].a[0],counter);
        mul(cond2_eval,P4[j].a[1],counter);
        add(counter-1,counter-2,counter);
        P4[j].sumcheck2Prod_proofs[0].sum = counter-1;
        int t = verify_2sumcheck(P4[j].sumcheck2Prod_proofs[0],one,counter);
        
        
        
        verify_3sumcheck(P4[j].sumcheck3Prod_proofs[3].polynomials, P4[j].sumcheck3Prod_proofs[3].randomness, P4[j].sumcheck2Prod_proofs[0].randomness, P4[j].sumcheck3Prod_proofs[3].vr[0], P4[j].sumcheck3Prod_proofs[3].vr[1], P4[j].sumcheck2Prod_proofs[0].vr[0],  one,counter);
        


        mul(two,P4[j].pairwise_prod_eval,counter);
        sub(P4[j].sumcheck3Prod_proofs[1].vr[1],P4[j].square_N_eval,counter);
        sub(counter-1,counter-2,counter);

        verify_3sumcheck(P4[j].sumcheck3Prod_proofs[4].polynomials, P4[j].sumcheck3Prod_proofs[4].randomness,P4[j].sumcheck3Prod_proofs[0].randomness, P4[j].sumcheck3Prod_proofs[4].vr[0], P4[j].sumcheck3Prod_proofs[4].vr[1], P4[j].sumcheck3Prod_proofs[0].vr[1],  one,counter);
        verify_3sumcheck(P4[j].sumcheck3Prod_proofs[5].polynomials, P4[j].sumcheck3Prod_proofs[5].randomness,P4[j].sumcheck3Prod_proofs[1].randomness, P4[j].sumcheck3Prod_proofs[4].vr[0], P4[j].sumcheck3Prod_proofs[4].vr[1], P4[j].square_N_eval,  one,counter);
        verify_3sumcheck(P4[j].sumcheck3Prod_proofs[6].polynomials, P4[j].sumcheck3Prod_proofs[6].randomness,P4[j].sumcheck3Prod_proofs[1].randomness, P4[j].sumcheck3Prod_proofs[6].vr[0], P4[j].sumcheck3Prod_proofs[6].vr[1], P4[j].pairwise_prod_eval,  one,counter);
        mul(P4[j].r1[0],P4[j].sumcheck3Prod_proofs[4].vr[0],counter);
        mul(P4[j].r1[1],P4[j].eval1_N0,counter);
        add(counter-1,counter-2,counter);
        mul(P4[j].r1[2],P4[j].eval1_N1,counter);
        mul(P4[j].r1[3],P4[j].sumcheck3Prod_proofs[5].vr[1],counter);
        add(counter-1,counter-2,counter);
        add(counter-1,counter-4,counter);
        P4[j].sumcheck2Prod_proofs[1].sum = counter-1;
        verify_2sumcheck(P4[j].sumcheck2Prod_proofs[1],one,counter);
        
        mul(P4[j].r2[0],P4[j].sumcheck3Prod_proofs[6].vr[0],counter);
        mul(P4[j].r2[1],P4[j].sumcheck3Prod_proofs[6].vr[1],counter);
        add(counter-1,counter-2,counter);
        mul(P4[j].r2[2],P4[j].gini_eval3,counter);
        mul(P4[j].r2[3],P4[j].gini_eval4,counter);
        add(counter-1,counter-2,counter);
        add(counter-1,counter-4,counter);
        P4[j].sumcheck2Prod_proofs[2].sum = counter-1;
        verify_2sumcheck(P4[j].sumcheck2Prod_proofs[2],one,counter);   
        P4[j].GKR.sum = zero;
        verify_gkr(P4[j].GKR,one,counter);
        /*
        */
    }
 
 
}


void parse_prepare_coeff(ifstream &circuit_in, long long int *in, int degree){
    vector<int> L(degree);
    int counter = 0;
    for(int i = 0; i < N; i++){
        buildInput(counter, 0);
        L[i] = counter;
        counter++;
    }
    for(int i = 0; i < L.size(); i++){
        for(int j = i+1; j < L.size(); j++){
            mul(L[i],L[j],counter);
        }
    }
    for(int i = 0; i < L.size(); i++){
        mul(L[i],L[i],counter);
    }
}

void parse_test_circuit(ifstream &circuit_in, long long int *in, int N, int layers){
    vector<int> input(N);
    int counter = 0;
    for(int i = 0; i < N; i++){
        buildInput(counter, 0);
        input[i] = counter;
        counter++;
    }
    vector<int> layer;
    int layer_id = 0;
    while(N != 4){
        for(int i = 0; i < N/2; i++){
            if(rand()%2 == 0){
                mul(input[2*i],input[2*i+1],counter);
            }else{
                add(input[2*i],input[2*i+1],counter);
            }
            layer.push_back(counter-1);
        }
        input = layer;
        layer.clear();
        layer_id++;
        if(layers == layer_id) break;
        N = N/2;
    }
   
    
}


void parse(ifstream &circuit_in, long long int *in) {
    string source_line;
    i64 tgt, src0, src1;
    
    while (getline(circuit_in, source_line)) {
        if (std::regex_match(source_line, base_match, add_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld + V%lld E", &tgt, &src0, &src1);
            buildGate(Add, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, mult_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld * V%lld E", &tgt, &src0, &src1);
            buildGate(Mul, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, input_gate)) {
            sscanf(source_line.c_str(), "P V%lld = I%lld E", &tgt, &src0);
            buildInput(tgt, 0);
        } else if (std::regex_match(source_line, base_match, output_gate)) {
            sscanf(source_line.c_str(), "P O%lld = V%lld E", &tgt, &src0);
        } else if (std::regex_match(source_line, base_match, xor_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld XOR V%lld E", &tgt, &src0, &src1);
            buildGate(Xor, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, add_mul_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld ip V%lld E", &tgt, &src0, &src1);
            buildGate(AddMul, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, naab_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld NAAB V%lld E", &tgt, &src0, &src1);
            buildGate(Naab, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, minus_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld minus V%lld E", &tgt, &src0, &src1);
            buildGate(Sub, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, not_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld NOT V%lld E", &tgt, &src0, &src1);
            buildGate(Not, tgt, src0, 0, true);
        } else {
            assert(false);
        }
    }
    //free(in);
}

DAG_gate *buildGate(gateType ty, u64 tgt, u64 src0, u64 src1, bool has_constant) {
//  fprintf(stderr, "buildGate: tgt: %d, src0: %d, src1: %d, has_const: %d\n", tgt, src0, src1, (int) has_constant);
    DAG_gate *g = new DAG_gate();
    vector<DAG_gate *> v; 
    g->is_assert = false;
    g->ty = ty;
    g->input0 = make_pair((int)'V', src0);
    g->input1 = make_pair(has_constant ? (int)'S' : 'V', src1);
    if (tgt >= in_circuit_dag.size()){

        in_circuit_dag.resize(tgt + 1, nullptr);
    }
    if (tgt >= ip_circuit_dag.size()) {
        ip_circuit_dag.resize(tgt + 1,v);
    }
    in_circuit_dag[tgt] = g;
    if(ty == AddMul){
        ip_circuit_dag[tgt].resize(ip_circuit_dag[tgt].size() + 1,nullptr);
        ip_circuit_dag[tgt][ip_circuit_dag[tgt].size()-1] = g;
    }
    return g;
}

DAG_gate *buildInput(u64 tgt, u64 src0) {
//  fprintf(stderr, "buildInput: tgt: %d, src0: %d\n", tgt, src0);
    DAG_gate *g = new DAG_gate();
    vector<DAG_gate *> v;
    g->is_assert = false;
    g->ty = Input;
    g->input0 = make_pair((int)'S', src0);
    g->input1 = make_pair((int)'N', 0);
    if (tgt >= in_circuit_dag.size()) in_circuit_dag.resize(tgt + 1, nullptr);
    if (tgt >= in_circuit_dag.size()) ip_circuit_dag.resize(tgt + 1, v);
    
    in_circuit_dag[tgt] = g;
    return g;
}

void setAssertion(u64 tgt) {
    assert(tgt < in_circuit_dag.size());
    in_circuit_dag[tgt]->is_assert = true;
}