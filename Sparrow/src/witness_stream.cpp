
#include "witness_stream.h"

extern layeredCircuit C;

extern vector<F> beta11,beta12,beta13,beta14;
extern vector<F> a;
extern int mod;
extern vector<unsigned int> preimage;
extern vector<unsigned int> SHA;
extern vector<int> H;
extern vector<F> V_in;


vector<unsigned int> rotate(vector<unsigned int> bits, int shift){
	vector<unsigned int> new_bits;
 	for(int i = shift; i < bits.size(); i++){
        new_bits.push_back(bits[i]);
    }
    for(int i = 0; i < shift; i++){
        new_bits.push_back(bits[i]);
    }
	return new_bits;
}

vector<unsigned int> shift(vector<unsigned int> bits, int shift){
	vector<unsigned int> new_bits;
	for(int i = shift; i < bits.size(); i++){
		new_bits.push_back(bits[i]);
	}
	for(int i = 0; i < bits.size()-shift; i++){
		new_bits.push_back((0));
	}
	return new_bits;
}

vector<unsigned int> prepare_bit_vector(unsigned int word, int range){
    vector<unsigned int> bits(range,0);
    for(int i = 0; i < range; i++){
        if(word&1){
            bits[i] = 1;
        }
        word = word>>1;
    }
    return bits;
}

vector<F> get_sha_witness(vector<unsigned int> words){
	vector<F> gkr_input;
	vector<unsigned long int> pow(32);pow[0] = 1;pow[1] = 2;
	for(int i = 2; i < 32; i++){
		pow[i] = pow[i-1]*pow[1];
	}
	vector<F> new_words(48);
	vector<vector<unsigned int>> words_bits(64);
	vector<F> buff;
	for(int i = 0; i < 16; i++){
		words_bits[i] = prepare_bit_vector(words[i], 32);
	}
	vector<F> quotients;

	for(int i = 0;i < 16; i++){
		quotients.push_back(F_ZERO);
	}
	for(int i = 16; i < 64; i++){
		unsigned long long int temp_word1 = 0,temp_word2 = 0;
		vector<unsigned int> w1 = rotate(words_bits[i-15],7);
		vector<unsigned int> w2 = rotate(words_bits[i-15],18);
		vector<unsigned int> w3 = shift(words_bits[i-15],3);
		for(int j = 0; j < 32; j++){
			unsigned long long int _t = w1[j]+w2[j] - 2*w1[j]*w2[j];
			temp_word1 = temp_word1 + pow[j]*(w3[j] + _t - 2*w3[j]*_t);
		}
		
		w1 = rotate(words_bits[i-2],17);
		w2 = rotate(words_bits[i-2],19);
		w3 = shift(words_bits[i-2],10);
		for(int j = 0; j < 32; j++){
			unsigned long long int _t = w1[j]+w2[j] - 2*w1[j]*w2[j];
			temp_word2 = temp_word2 + pow[j]*(w3[j] + _t - 2*w3[j]*_t);
		}
		unsigned long long int temp_word = temp_word1 + temp_word2 + words[i - 16] + words[i-7];
		quotients.push_back(temp_word/((unsigned long long)1ULL<<32));
		words.push_back(temp_word%((unsigned long long)1ULL<<32));
		
		//printf("OK %d,%d,%d,%lld,%lld\n",i,buff.size(),words.size(),1ULL<<32, words[i].toint128());
		words_bits[i] = prepare_bit_vector(words[i], 32);
		if(words_bits[i].size() != 32){
			printf("Error in witness 0\n");
			exit(-1);
		}
	}

	
	vector<unsigned int> a(65),b(65),c(65),d(65),e(65),f(65),g(65),h(65);
    a[0] = H[0];b[0] = H[1];c[0] = H[2];d[0] = H[3];
	e[0] = H[4];f[0] = H[5];g[0] = H[6];h[0] = H[7];
	vector<vector<unsigned int>> a_bits(64),b_bits(64),c_bits(64),e_bits(64),f_bits(64),g_bits(64);
    vector<unsigned long long int> a_q,e_q;

    for(int i = 0; i < 64; i++){
		
        a_bits[i] = prepare_bit_vector(a[i],32);
		
        unsigned long long int s0 = 0;
		vector<unsigned int> w1 = rotate(a_bits[i],2);
		vector<unsigned int> w2 = rotate(a_bits[i],13);
		vector<unsigned int> w3 = rotate(a_bits[i],22);
		
		for(int j = 0; j < 32; j++){
			unsigned long long int _t = w1[j]+w2[j] - 2*w1[j]*w2[j];
			s0 = s0+ pow[j]*(w3[j] + _t - 2*w3[j]*_t);
		}
		buff.push_back(b[i]);
		b_bits[i] = prepare_bit_vector(b[i],32);
		buff.clear();
		buff.push_back(c[i]);
		c_bits[i] = prepare_bit_vector(c[i],32);
		buff.clear();	
		if(a_bits[i].size() != 32 || b_bits[i].size() != 32 || c_bits[i].size() != 32){
			printf("Error in witness 1\n");
			exit(-1);
		}
		unsigned long long int maj = 0;
		for(int j = 0; j < 32; j++){
			unsigned long long int _t = a_bits[i][j]*b_bits[i][j] + b_bits[i][j]*c_bits[i][j] - 2*a_bits[i][j]*b_bits[i][j]*b_bits[i][j]*c_bits[i][j];
			maj = maj + pow[j]*(c_bits[i][j]*a_bits[i][j] + _t - 2*c_bits[i][j]*a_bits[i][j]*_t);
		}
		unsigned long long int t2 = maj + s0;
		
        e_bits[i] = prepare_bit_vector(e[i],32);
		
        f_bits[i] = prepare_bit_vector(f[i],32);
		
        g_bits[i] = prepare_bit_vector(g[i],32);
		
        if(e_bits[i].size() != 32 || f_bits[i].size() != 32 || g_bits[i].size() != 32){
			printf("Error in witness 1\n");
			exit(-1);
		}
		w1 = rotate(e_bits[i],6);
		w2 = rotate(e_bits[i],11);
		w3 = rotate(e_bits[i],25);
		unsigned long long int s1 = 0;
		for(int j = 0; j < 32; j++){
			unsigned long long int _t = w1[j]+w2[j] - 2*w1[j]*w2[j];
			s1 = s1 + pow[j]*(w3[j] + _t - 2*w3[j]*_t);
		}
		unsigned long long int ch = (0);
		for(int j = 0; j < 32; j++){
			ch = ch+ pow[j]*(e_bits[i][j]*f_bits[i][j] + (1-e_bits[i][j])*g_bits[i][i] - 2*e_bits[i][j]*f_bits[i][j]* (1-e_bits[i][j])*g_bits[i][i]);
		}
		long long int t1 = ch + s1 + words[i] + h[i] + SHA[i];
		a_q.push_back((t1+t2)/(1ULL<<32));
		a[i+1] = (t1+t2)%((1ULL<<32));
		//printf("%lld , %lld\n",a_q[i].toint128()),(t1+t2 - a_q[i]*(1ULL<<32) - a[i+1]);
		e_q.push_back((t1 + d[i])/(1ULL<<32));
		e[i+1] = (t1 + d[i])%(1ULL<<32);
		h[i+1] = g[i];
		g[i+1] = f[i];
		f[i+1] = e[i];
		d[i+1] = c[i];
		c[i+1] = b[i];
		b[i+1] = a[i];
	}
	


	gkr_input.insert(gkr_input.end(),words.begin(),words.end());
	gkr_input.insert(gkr_input.end(),quotients.begin(),quotients.end());
	//gkr_input.insert(gkr_input.end(),pow.begin(),pow.end());
	
	for(int i = 0; i < a.size(); i++){
		gkr_input.push_back(a[i]);
		gkr_input.push_back(b[i]);
		gkr_input.push_back(c[i]);
		gkr_input.push_back(d[i]);
		gkr_input.push_back(e[i]);
		gkr_input.push_back(f[i]);
		gkr_input.push_back(g[i]);
		gkr_input.push_back(h[i]);
	}
	for(int i = 0; i < a_q.size(); i++){
		gkr_input.push_back(a_q[i]);
		gkr_input.push_back(e_q[i]);
	}
    for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),words_bits[i].begin(),words_bits[i].end());
	}

	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),a_bits[i].begin(),a_bits[i].end());
	}
	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),b_bits[i].begin(),b_bits[i].end());
	}
	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),c_bits[i].begin(),c_bits[i].end());
	}
	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),e_bits[i].begin(),e_bits[i].end());
	}
	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),f_bits[i].begin(),f_bits[i].end());
	}
	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),g_bits[i].begin(),g_bits[i].end());
	}
    gkr_input.push_back(1);
    F zero = F(0);
    gkr_input.resize(1ULL<<14,zero);
	//gkr_input.push_back(F(1));
	return gkr_input;
}



void reset_stream(stream_descriptor &fp){
    fp.pos = 0;
}

void read_layer(int circuit_num, int layer , vector<F> &V){
     if(C.size < layer){
        printf("Wrong layer \n");
        exit(-1);
    }
    
    vector<vector<F>> circuitValue; 
    circuitValue.resize(C.size + 1);
    //Change the size of the input layer
    if(mod == 1 || mod == 3){
        F a = F(311322);
        circuitValue[0].resize(1ULL << C.circuit[0].bitLength, F_ZERO);
        for(int i = 0; i < circuitValue[0].size(); i++){
           circuitValue[0][i] = a;
        }
    }else{
        circuitValue[0] = get_sha_witness(preimage);
    }
    
    for (u64 g = 0; g < C.circuit[0].size; ++g)
    {
        // make sure the gates are of type input
        auto info = C.circuit[0].gates[g];
        assert(info.ty == gateType::Input);
        //printf("%llu , %llu\n",g,C.circuit[0].gates[g].u );
        circuitValue[0][g] = (g+1)  + C.circuit[0].size*circuit_num;
        //printf("%llu\n",circuitValue[0][g].toint128());
    }
    if(layer == 0){
        for(int i = 0; i < circuitValue[0].size(); i++){
            V[i] = circuitValue[0][i];
        }
        return;
    }
    //fclose(f);
    
    std::vector<std::pair<int, F> > ret;
    
    for (int i = 1; i < layer+1; ++i)
    {   
        circuitValue[i].resize(C.circuit[i].size);
        for (u64 g = 0; g < C.circuit[i].size; ++g){
            // check info of each gate and compute the output
            auto info = C.circuit[i].gates[g];
            gateType ty = info.ty;
            int l = info.l;
            
            
            
            u64 u = info.u;
            u64 v = info.v;
            
            
            if(l != i-1){
                printf("ERROR the circuit is not layered, %d %d\n",l,i);
                exit(-1);
            }
            int counter = info.counter;
            F *x, *y;
            switch (ty) {
                case gateType::Add:
                    circuitValue[i][g] = circuitValue[i - 1][u] + circuitValue[l][v];
                break;
                case gateType::Sub:
                    circuitValue[i][g] = circuitValue[i - 1][u] - circuitValue[l][v];
                    break;
                case gateType::Mul:
                    circuitValue[i][g] =  circuitValue[i - 1][u] * circuitValue[l][v];
                    break;
                case gateType::AntiSub:
                    circuitValue[i][g] = -circuitValue[i - 1][u] + circuitValue[l][v];
                    break;
                case gateType::AddMul:
                    circuitValue[i][g] = F(0);
                    for(int k = 0; k < counter; k++){
                        circuitValue[i][g] = circuitValue[i][g] + circuitValue[i-1][info.vector_u.at(k)]*circuitValue[l][info.vector_v.at(k)];
                        //printf("%lld \n", circuitValue[i-1][info.vector_u.at(k)].toint128());
                    }
                    break;
                case gateType::Naab:
                    circuitValue[i][g] = circuitValue[l][v] - circuitValue[i - 1][u] * circuitValue[l][v];
                break;
                case gateType::AntiNaab:
                    circuitValue[i][g] = circuitValue[i - 1][u] - circuitValue[i - 1][u] * circuitValue[l][v];
                break;
                case gateType::Addc:
                    circuitValue[i][g] = circuitValue[i - 1][u] + info.c;
                break;
                case gateType::Mulc:
                    circuitValue[i][g] = circuitValue[i - 1][u] * info.c;
                break;
                case gateType::Copy:
                    circuitValue[i][g] = circuitValue[i - 1][u];
                break;
                case gateType::Not:
                    circuitValue[i][g] = F_ONE - circuitValue[i - 1][u];
                break;
                case gateType::Xor:
                    x = &circuitValue[i - 1][u];
                    y = &circuitValue[l][v];
                    circuitValue[i][g] = *x + *y - F(2) * (*x) * (*y);
                break;
                default:
                    assert(false);
            }
        }
    }

    for(int i = 0; i < circuitValue[layer].size(); i++){
        V[i] = circuitValue[layer][i];
    }
        
}

void read_H( int layer , vector<F> &H_add,vector<F> &H_mul, vector<F> &V, F beta_h1, F beta_h2 ){
    
    for(int i = 0; i < H_add.size(); i++){
        H_add[i] = F_ZERO;
        H_mul[i] = F_ZERO;
    }
    int counter1 = 0;
    for (u64 g = 0; g < C.circuit[layer].size; ++g) {
        // take each current gate 
        auto info = C.circuit[layer].gates[g];
        gateType ty = info.ty;
        int l = info.l;
        u64 u = info.u;
        u64 v = info.v;
        u64 lv = info.lv;
        int counter = info.counter;
        F tmp;
        if(a.size() == 0){
            tmp = beta11[g]*beta_h1;
        }else{
            tmp = a[0]*beta11[g]*beta_h1 + a[1]*beta13[g]*beta_h2;
        }
        
        //tmp *= beta_h2;
        switch (ty) {
            case gateType::Add:
                
                H_add[u] +=  V[v] * tmp; 
                // That is add()V(i-1)(x)
                H_mul[u] += tmp;
                break;
            case gateType::Sub:
                H_add[u] -=  V[v] * tmp;
                H_mul[u] += tmp;
                break;
            case gateType::Mul:
                //printf("%d,%d\n",u,v);
                H_mul[u] += V[v] * tmp;
                break;
            case gateType::AntiSub:
                H_add[u] = H_add[u] + V[v] * tmp;
                H_mul[u] = H_mul[u] - tmp;
                break;
            case gateType::AddMul:
                //tmp_mult[info.vector_u.at(0)] = F(0);
                for(int k = 0; k < counter; k++){
                    H_mul[info.vector_u.at(k)] = H_mul[info.vector_u.at(k)]  + V[info.vector_v.at(k)]*tmp;
                }
                break;
            case gateType::Naab:
                H_add[u] = H_add[u] + tmp * V[v];
                H_mul[u] = H_mul[u] - (V[v] * tmp);
                break;
            case gateType::AntiNaab:
                H_mul[u] = H_mul[u] + (tmp - (V[v] * tmp));
                break;
            case gateType::Addc:
                H_add[u] = H_add[u] + info.c * tmp;
                H_mul[u] = H_mul[u] + tmp;
                break;
            case gateType::Mulc:
                H_mul[u] = H_mul[u] + info.c * tmp;
                break;
            case gateType::Copy:
                H_mul[u] += tmp;
                break;
            case gateType::Not:
                H_add[u] = H_add[u] + tmp;
                H_mul[u] = H_mul[u] - tmp;
                break;
            case gateType::Xor:
                H_add[u] = H_add[u] + tmp * V[v];
                H_mul[u] = H_mul[u] + tmp * (F_ONE - (V[v] + V[v]));
                break;
            default:
                assert(false);
        }
    }
}

void read_G( int layer , vector<F> &G_add,vector<F> &G_mul, vector<F> &V, vector<F> &beta_g1,F beta_h1,
 F beta_g2,F beta_h2, F V_u){

     for(int i = 0; i < G_add.size(); i++){
        G_add[i] = F_ZERO;
        G_mul[i] = F_ZERO;
    }
     for (u64 g = 0; g < C.circuit[layer].size; ++g)
    {
        auto info = C.circuit[layer].gates[g];
        gateType ty = info.ty;
        
        u64 u = info.u;
        u64 v = info.v;
        int counter = info.counter;
        // Create the bookkeeping table for the second phase
        // Note that this time tmp is not G[g], but G[g]*U[u]
        // Because add() and mul() contain x which has become 
        // u so there must be an identity function for x too
        F tmp;
        if(a.size() == 0){
            tmp = beta11[g]*beta_h1*beta_g2*beta_g1[u];
        }else{
            tmp = (a[0]*beta11[g]*beta_h1 + a[1]*beta13[g]*beta_h2)*beta_g2*beta_g1[u];
        }

        //F tmp = beta_g1[u] * beta_h1[g]*beta_g2*beta_h2;
        
        //printf("%d,%d,%d\n",g,u,v);
        switch (ty) {
            case gateType::Add:
                G_mul[v] += tmp;
                G_add[v] += tmp * V_u;
                break;
            case gateType::Sub:
                G_add[v] +=  tmp * V_u;
                G_mul[v] -=  tmp;
                break;
            case gateType::Mul:
                G_mul[v] += tmp*V_u;
                break;
            case gateType::AddMul:
                //multArray[l][info.vector_lv.at(0)]= F(0);
                for(int k = 0; k < counter; k++){
                    //printf("u : %d, v : %d\n", info.vector_u.at(k),info.vector_lv.at(k));
                    F tmp_add_mull;// = beta_g[g] * beta_u[info.vector_u.at(k)];
                    if(a.size() == 0){
                        tmp_add_mull = beta11[g]*beta_h1*beta_g2*beta_g1[info.vector_u.at(k)];
                    }else{
                        tmp_add_mull = (a[0]*beta11[g]*beta_h1 + a[1]*beta13[g]*beta_h2)*beta_g2*beta_g1[info.vector_u.at(k)];
                    }
                    G_mul[info.vector_v.at(k)] +=  tmp_add_mull*V_u ;
                }
                break;
            case gateType::Not:
                G_add[0] = G_add[0] + tmp * (F_ONE - V_u);
                break;
            case gateType::Xor:
                
                G_add[v] = G_add[v] + tmp * V_u;
                G_mul[v] = G_mul[v] + tmp * (F_ONE - (V_u + V_u));
                break;
            default:
                assert(false);
        }
    }

}



void read_stream(stream_descriptor &fd, vector<F> &v, int size){
    
    if(fd.name == "circuit"){
        int current_pos = fd.pos/C.circuit[fd.layer].size;
        vector<F> V(C.circuit[fd.layer].size);
        
        for(int i = 0; i < size/C.circuit[fd.layer].size; i++){
            read_layer(current_pos, fd.layer , V);
            current_pos++;
            fd.pos += V.size();
            for(int j = 0; j < V.size(); j++){
                v[i*V.size() + j] = V[j];
            }
           
        }
    }
    else if(fd.name == "input"){
        if(mod == 1 || mod == 3){
            for(int i =0 ; i < size; i++){
                v[i] = V_in[i%1024];
            }
        }else{
            vector<F> buff;
            int counter = 0;
            for(int i = 0; i < size/C.circuit[0].size; i++){
                buff = get_sha_witness(preimage);
                for(int j = 0; j < buff.size(); j++){
                    v[counter++] = buff[j];
                }
            }
        }
        
    }
}