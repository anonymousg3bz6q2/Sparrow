
#include "GKR.h"
#include "circuit.h"

using namespace std;
using std::max;
#define Clients 2
#define Len 8
extern int partitions;

vector<DAG_gate *> in_circuit_dag;
vector<vector<DAG_gate *>> ip_circuit_dag;

using std::cerr;
using std::endl;

const int repeat = 1;
layeredCircuit C;
int Circuits;

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
        for (auto v: edges[u]){
          
            if (!(--in_deg[v])) {
                q.push(v);
                lyr_id[v] = max(lyr_id[v], lyr_id[u] + 1);
            }
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

int count_size(layer i_layer){
    int size = 0;
    for(int j = 0; j < i_layer.size; j++){
        auto &g = i_layer.gates[j];
        if(g.ty == AddMul){
            size += g.counter;
        }
        else{
            size += 1;
        }
    }
    return size;
}
void subsetInit() {
    for (int i = 0; i < C.size; ++i) {
        C.circuit[i].dadBitLength.resize(i, -1);
        C.circuit[i].dadSize.resize(i, 0);
        C.circuit[i].dadId.resize(i);
        C.circuit[i].maxDadBitLength = -1;
        C.circuit[i].maxDadSize = 0;
    }

    vector<vector<int>> visited_idx(C.size);  // whether the i-th layer, j-th gate has been visited in the current layer
    vector<vector<u64>> subset_idx(C.size);   // the subset index of the i-th layer, j-th gate
    for (int i = 0; i < C.size; ++i) {
        //Changed
        visited_idx[i].resize(count_size(C.circuit[i]));
        subset_idx[i].resize(count_size(C.circuit[i]));
    }
    
    for (int i = C.size - 1; i > 0; --i) {
        for (u64 j = C.circuit[i].size - 1; j < C.circuit[i].size; --j) {
            auto &g = C.circuit[i].gates[j];
            int l = g.l;
            if(g.ty == AddMul){
                for(int k = 0; k < g.vector_v.size(); k++){
                    u64 v = g.vector_v.at(k);
                    if (!(~l)) continue;
                    if (visited_idx[l][v] != i) {
                        visited_idx[l][v] = i;
                        subset_idx[l][v] = C.circuit[i].dadSize[l]++;
                        C.circuit[i].dadId[l].push_back(v);
                    }
                    g.lv_push(subset_idx[l][v]);
                }
            }
            else{

                u64 v = g.v;
                if (!(~l)) continue;
                if (visited_idx[l][v] != i) {
                    visited_idx[l][v] = i;
                    subset_idx[l][v] = C.circuit[i].dadSize[l]++;
                    C.circuit[i].dadId[l].push_back(v);
                }
                g.lv = subset_idx[l][v];
            }
        }

        for (int j = 0; j < i; ++j) {
            C.circuit[i].dadBitLength[j] = (int) log2(C.circuit[i].dadSize[j]);
            if ((1ULL << C.circuit[i].dadBitLength[j]) < C.circuit[i].dadSize[j])
                ++C.circuit[i].dadBitLength[j];
            C.circuit[i].maxDadSize = max(C.circuit[i].dadSize[j], C.circuit[i].maxDadSize);
            C.circuit[i].maxDadBitLength = max(C.circuit[i].dadBitLength[j], C.circuit[i].maxDadBitLength);
        }
    }
}


void parse_test_circuit(ifstream &circuit_in, long long int *in, int N, int layers);
void parse_test_circuit2(ifstream &circuit_in, long long int *in, int N, int layers);
void parse_m2m(ifstream &circuit_in, long long int *in, int col_size,int row_size, int layers);
void parse_sha256(ifstream &circuit_in,long long int *in, int instances);


void test_sha256(vector<F> data, vector<F> randomness, int hashes){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    
    Circuits = hashes;
    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_sha256(circuit_in, in, 0);

    C = DAG_to_layered();
    
    subsetInit();
}


void test_m2m(vector<F> data, vector<F> randomness, int cols, int rows, int circuits){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    
    Circuits = circuits;
    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_m2m(circuit_in, in, cols,rows, 0);

    C = DAG_to_layered();
    
    subsetInit();
    
}

void test_multree(vector<F> data, vector<F> randomness, int N, int M, int layers){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    
    Circuits = M;
    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_test_circuit(circuit_in, in, N, layers);

    C = DAG_to_layered();
    
    subsetInit();
    
}

void test_gkr(vector<F> data, vector<F> randomness, int N, int M, int layers){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    
    Circuits = M;
    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_test_circuit2(circuit_in, in, N, layers);

    C = DAG_to_layered();
    
    subsetInit();
    //prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    //verifier v(&p, c);
    //ip_circuit_dag.clear();
    //struct proof Pr = v.verify(randomness,randomness[randomness.size()-1]);
    //return Pr;    

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

void _xor_gate(int x,int y,int &counter){
    buildGate(Xor,counter,x,y,false);
    counter+=1;
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

void func1(vector<int> pow, vector<int> a, vector<int> b, vector<int> c,int zero_2, int &counter){
    vector<int> prod;
    for(int i = 0; i < a.size(); i++){
        mul(a[i],b[i],counter);
        int a_b = counter-1;
        mul(a[i],c[i],counter);
        int a_c = counter-1;
        mul(b[i],c[i],counter);
        int b_c = counter-1;
        _xor_gate(a_b,a_c,counter);
        add(zero_2,b_c,counter);
        _xor_gate(counter-1,counter-2,counter);
        //XOR(a_b,a_c,counter);
        //XOR(counter-1,b_c,counter);
        prod.push_back(counter-1);
        //mul(pow[i],counter-1,counter);
        //prod.push_back(counter-1);
    }
    ip(prod,pow,counter);
    
    //add_tree(prod,counter);
}

void func2(vector<int> pow, vector<int> e, vector<int> f, vector<int> g, int one,int zero,int zero_2, int &counter){
    vector<int> prod;
    for(int i = 0; i < e.size(); i++){
        mul(e[i],f[i],counter);
        add(zero_2,counter-1,counter);
        sub(one,e[i],counter);
        add(zero,g[i],counter);
        mul(counter-1,counter-2,counter);
        _xor_gate(counter-1,counter-4,counter);
        //XOR(counter-1,counter-3,counter);
        
        //mul(pow[i],counter-1,counter);
        prod.push_back(counter-1);
    }
    ip(prod,pow,counter);
    //add_tree(prod,counter);
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


void parse_m2m(ifstream &circuit_in, long long int *in, int col_size,int row_size, int layers){
    vector<vector<int>> input(row_size);
    
    int counter = 0;
    
    vector<int> out(row_size/2);
    
    for(int i = 0; i < row_size; i++){
        input[i].resize(col_size);
        for(int j = 0; j < col_size; j++){
            buildInput(counter, 0);
            input[i][j] = counter;
            counter++;
        }
    }
    
    for(int i = 0; i < row_size; i+=2){
        ip(input[i],input[i+1],counter);
        out[i/2] = counter-1;
    
    }
    for(int i = 0; i < out.size()/2; i++){
    
        mul(out[2*i],out[2*i+1],counter);
    }

}


void rotate_right(vector<int> pow, vector<int> w1, vector<int> w2, vector<int> w3, int r1,int r2,int r3,int zero, int &counter){
    vector<int> w1_r,w2_r,w3_r;
    for(int i = r1; i < w1.size(); i++){
        w1_r.push_back(w1[i]);
    }
    for(int i = 0; i < r1; i++){
        w1_r.push_back(w1[i]);
    }
    for(int i = r2; i < w2.size(); i++){
        w2_r.push_back(w2[i]);
    }
    for(int i = 0; i < r2; i++){
        w2_r.push_back(w2[i]);
    }
    for(int i = r3; i < w3.size(); i++){
        w3_r.push_back(w3[i]);
    }
    for(int i = 0; i < r3; i++){
        w3_r.push_back(w3[i]);
    }
     vector<int> xored_word;
    int num;
    for(int i = 0; i < w3_r.size(); i++){
        _xor_gate(w3_r[i],w1_r[i],counter);
        add(zero,w2_r[i],counter);
        _xor_gate(counter-1,counter-2,counter);
        //XOR(w3_r[i],w1_r[i],counter);
        //XOR(counter-1,w2_r[i],counter);
        num = counter;
        xored_word.push_back(num-1);
    }
    vector<int> prod;
    ip(xored_word,pow,counter);
    /*
    for(int i = 0; i < w1_r.size(); i++){
        mul(xored_word[i],pow[i],counter);
        num = counter;
        prod.push_back(counter-1);
    }
    add_tree(prod,counter);*/
    
}

void xor_shift(vector<int> pow,vector<int> w1,vector<int> w2,vector<int> w3,int rotate1,int rotate2,int shift3,int zero,int zero_2,int zero_3,int &counter){
    vector<int> w1_r,w2_r,w3_s;
    for(int i = rotate1; i < w1.size(); i++){
        w1_r.push_back(w1[i]);
    }
    for(int i = 0; i < rotate1; i++){
        w1_r.push_back(w1[i]);
    }
    for(int i = rotate2; i < w2.size(); i++){
        w2_r.push_back(w2[i]);
    }
    for(int i = 0; i < rotate2; i++){
        w2_r.push_back(w2[i]);
    }
    for(int i = shift3; i < w3.size(); i++){
        w3_s.push_back(w3[i]);
    }
    vector<int> xored_word;
    int num;
    
    // Depth: 2
    for(int i = 0; i < w3_s.size(); i++){
        _xor_gate(w3_s[i],w1_r[i],counter);
        add(zero,w2_r[i],counter);
        _xor_gate(counter-1,counter-2,counter);
        //XOR(w3_s[i],w1_r[i],counter);
        //XOR(counter-1,w2_r[i],counter);
        num = counter;
        xored_word.push_back(num-1);
    }
    for(int i = w3_s.size(); i < w1_r.size(); i++){
        _xor_gate(w2_r[i],w1_r[i],counter);
        add(zero_2,counter-1,counter);
        
        //add(zero_3,counter-1,counter);
        //XOR(w2_r[i],w1_r[i],counter);
        num = counter;
        xored_word.push_back(num-1);    
    }
    //vector<int> prod;
    //for(int i = 0; i < w1_r.size(); i++){
    //    mul(xored_word[i],pow[i],counter);
    //    num = counter;
    //    prod.push_back(num-1);
    //}
    //add_tree(prod,counter);
    ip(xored_word,pow,counter);
}


void parse_sha256(ifstream &circuit_in,long long int *in, int instances){
    vector<int> words;
    
    words.resize(64);
    vector<int> quotients;
    quotients.resize(64);
    
    vector<vector<int>> words_bits;
    words_bits.resize(64);
    
    vector<int> pows(32);
    vector<int> SHA(64);
    vector<int> a(65),b(65),c(65),d(65),e(65),f(65),g(65),h(65);
    vector<int> a_q(64),e_q(64);
    vector<vector<int>> a_bits(64),b_bits(64),c_bits(64),e_bits(64),f_bits(64),g_bits(64);
    int one;
        
    int counter = 0;
   
    for(int i = 0; i < 64; i++){
        buildInput(counter, 0);
        SHA[i] = counter;
        counter++;
    }
    for(int i = 0; i < 32; i++){
        buildInput(counter,0);
        pows[i] = counter;
        counter++;
    }
    
    for(int i = 0; i < 64; i++){
        buildInput(counter, 0);
        words[i] = counter;
        counter++;
    }
        
    for(int i = 0; i < 64; i++){
        buildInput(counter, 0);
        quotients[i] = counter;
        counter++;
    }
        
        for(int i = 0; i < a.size(); i++){
            buildInput(counter,0);
            a[i] = counter;
            counter++;
            buildInput(counter,0);
            b[i] = counter;
            counter++;
            buildInput(counter,0);
            c[i] = counter;
            counter++;
            buildInput(counter,0);
            d[i] = counter;
            counter++;
            buildInput(counter,0);
            e[i] = counter;
            counter++;
            buildInput(counter,0);
            f[i] = counter;
            counter++;
            buildInput(counter,0);
            g[i] = counter;
            counter++;
            buildInput(counter,0);
            h[i] = counter;
            counter++;
        }
        for(int i = 0; i < a_q.size(); i++){
            buildInput(counter,0);
            a_q[i] = counter;
            counter++;
            buildInput(counter,0);
            e_q[i] = counter;
            counter++;
            
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter, 0);
                words_bits[i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                a_bits[i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                b_bits[i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                c_bits[i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                e_bits[i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                f_bits[i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                g_bits[i].push_back(counter);
                counter++;
            }
        }
    
    buildInput(counter,0);
    one = counter;
    counter++;
    
    buildInput(counter,0);
    int zero = counter;
    counter++;
    
    for(int i = 0; i < 1174; i++){
        buildInput(counter,0);
        counter++;
    }


    printf("%d\n",counter);
    
    
    int two_power32;
    mul(pows[1],pows[31],counter);
    two_power32 = counter-1;
    
    
    vector<int> updated_word(64);
    add(zero,zero,counter);
    int zero_2 = counter-1;
    add(zero_2,zero_2,counter);
    int zero_3 = counter-1;
    add(zero_3,zero_3,counter);
    int zero_4 = counter-1;
    
    vector<int> pows_3(pows.size());
    vector<int> pows_4(pows.size());
    for(int i = 0; i < pows.size(); i++){
        add(zero,pows[i],counter);
        pows_3[i] = counter-1;
    }
    for(int i = 0; i < pows.size(); i++){
        add(pows_3[i],zero_2,counter);
        pows_3[i] = counter-1;
    }
    for(int i = 0; i < pows.size(); i++){
        add(pows_3[i],zero_3,counter);
        pows_4[i] = counter-1;
    }
    
    // First phase. Compute the words 
    for(int i = 16; i < 64; i++){
        // Depth : 4
        xor_shift(pows_3,words_bits[i-15],words_bits[i-15],words_bits[i-15],7,18,3,zero,zero_2,zero_3,counter);
        int num1 = counter-1;
        xor_shift(pows_3,words_bits[i-2],words_bits[i-2],words_bits[i-2],17,19,10,zero,zero_2,zero_3,counter);
        int num2 = counter-1;
        
        // Depth 5
        add(num1,num2,counter);
        int temp1 = counter-1;

        add(words[i-16],words[i-7],counter);
        add(counter-1,zero_2,counter);
        add(counter-1,zero_3,counter);
        int temp2 = counter-1;
        //add(counter-1,counter-2,counter);
        updated_word[i] = counter-1;
        
        add(quotients[i],zero,counter);
        mul(counter-1,two_power32,counter);
        
        add(words[i],zero,counter);
        add(counter-1,zero_2,counter);

        add(counter-1,counter-3,counter);
        
        sub(temp2,counter-1,counter);
        //add(counter-1,zero_4,counter);

        add(temp1,counter-1,counter);
        
    }
    for(int i = 0; i <  64; i++){
        rotate_right(pows_3, a_bits[i], a_bits[i], a_bits[i], 2,13,22,zero, counter);
        add(counter-1,zero_4,counter);
        int s0 = counter-1;
        
        func1(pows_4,a_bits[i],b_bits[i],c_bits[i],zero_2,counter);
        int maj = counter-1;
        add(maj,s0,counter);
        int t2 = counter-1;
            
        rotate_right(pows_3, e_bits[i], e_bits[i], e_bits[i], 6,11,25,zero, counter);
        int s1 = counter-1;
        func2(pows_4,e_bits[i],f_bits[i],g_bits[i],one,zero,zero_2,counter);
        int ch = counter-1;
        
        
        add(h[i],words[i],counter);
        
        add(SHA[i],zero,counter);
        add(counter-1,counter-2,counter);
        add(counter-1,zero_3,counter);
        add(s1,counter-1,counter);

        add(counter-1,ch,counter);
        
        int t1 = counter-1;

        add(t1,t2,counter);
        /*
        int _a = counter-1;
        mul(a_q[i],two_power32,counter);
        add(counter-1,a[i+1],counter);
        sub(counter-1,_a,counter);
            
        add(t1,d[i],counter);
        int _e = counter-1;
        mul(e_q[i],two_power32,counter);
        add(counter-1,e[i+1],counter);
        sub(counter-1,_e,counter);
        */
        sub(h[i+1],g[i],counter);
        sub(g[i+1],f[i],counter);
        sub(f[i+1],e[i],counter);

        sub(d[i+1],c[i],counter);
        sub(c[i+1],b[i],counter);
        sub(b[i+1],a[i],counter);
        
    }
    for(int i = 0; i < a_bits.size(); i++){
        for(int j = 0; j < a_bits[i].size(); j++){
            add(a_bits[i][j],zero,counter);
            sub(one,a_bits[i][j],counter);
            mul(counter-1,counter-2,counter);

            add(b_bits[i][j],zero,counter);
            sub(one,b_bits[i][j],counter);
            mul(counter-1,counter-2,counter);

            add(g_bits[i][j],zero,counter);
            sub(one,g_bits[i][j],counter);
            mul(counter-1,counter-2,counter);

                add(c_bits[i][j],zero,counter);
            sub(one,c_bits[i][j],counter);
            mul(counter-1,counter-2,counter);

            add(e_bits[i][j],zero,counter);
            sub(one,e_bits[i][j],counter);
            mul(counter-1,counter-2,counter);

            add(f_bits[i][j],zero,counter);
            sub(one,f_bits[i][j],counter);
            mul(counter-1,counter-2,counter);


        }
    }
    for(int i = 0; i < 14270; i++){
        add(zero,zero,counter);

    }
    for(int i = 0; i < 4879; i++){
        add(zero_2,zero_2,counter);

    }
    for(int i =0 ; i <3679; i++){
        add(zero_3,zero_3,counter);
    }
    for(int i = 0; i < 160; i++){
        add(zero_4,zero_4,counter);
    }
    
    int zero_5 = counter-1;
    for(int i = 0; i < 256 - 176; i++){
        add(zero_5,zero_5,counter);
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
    while(N != 0){
        for(int i = 0; i < N/2; i++){
            mul(input[2*i],input[2*i+1],counter);
            layer.push_back(counter-1);
        }
        input = layer;
        printf("%d\n",input.size());
        layer.clear();
        layer_id++;
        if(layers == layer_id) break;
        N = N/2;
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
        layer_id++;
        if(layers == layer_id) break;
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