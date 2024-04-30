#include "circuit.h"
#include "config_pc.hpp"
#include <algorithm>
#include "immintrin.h"

using std::max;



void randomize(int layerNum, int eachLayer)
{
    layeredCircuit c;
    int gateSize = 1 << eachLayer;
    c.circuit.resize(layerNum);
    c.size = layerNum;
    c.circuit[0].bitLength = eachLayer;
    c.circuit[0].size = gateSize;
    c.circuit[0].gates.resize(gateSize);
    for (int i = 0; i < gateSize; ++i)
    {
        c.circuit[0].gates[i] = gate(gateType::Input, 0, random(), 0, F_ZERO, false);
    }
    for (int i = 1; i < layerNum; ++i)
    {
        c.circuit[i].bitLength = eachLayer;
        c.circuit[i].size = gateSize;
        c.circuit[i].gates.resize(gateSize);
        for (int j = 0; j < gateSize; ++j)
        {
            c.circuit[i].gates[j] = gate((random() & 1) == 0 ? gateType::Add : gateType::Mul, random() % i, random() % gateSize, random() % gateSize, F_ZERO, false);
        }
    }
//    return c;
}

