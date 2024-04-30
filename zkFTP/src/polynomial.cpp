#include <iostream>
#include "polynomial.h"

quintuple_poly::quintuple_poly() { a.clear(); b.clear(); c.clear(); d.clear(); e.clear(); f.clear();}
quintuple_poly::quintuple_poly(const F &aa, const F &bb, const F &cc, const F &dd, const F &ee, const F &ff) {
    a = aa;
    b = bb;
    c = cc;
    d = dd;
    e = ee;
    f = ff;
}

quintuple_poly quintuple_poly::operator + (const quintuple_poly &x) const {
    return quintuple_poly(a + x.a, b + x.b, c + x.c, d + x.d, e + x.e, f + x.f);
}

F quintuple_poly::eval(const F &x) const {
    return (((((a * x) + b) * x + c) * x + d) * x + e) * x + f;
}

void quintuple_poly::clear() {
    a.clear(); b.clear(); c.clear(); d.clear(); e.clear(); f.clear();
}

quadruple_poly::quadruple_poly() {a.clear(); b.clear(); c.clear(); d.clear(); e.clear();}
quadruple_poly::quadruple_poly(const F &aa, const F &bb, const F &cc, const F &dd, const F &ee) {
    a = aa;
    b = bb;
    c = cc;
    d = dd;
    e = ee;
}

quadruple_poly quadruple_poly::operator + (const quadruple_poly &x) const {
    return quadruple_poly(a + x.a, b + x.b, c + x.c, d + x.d, e + x.e);
}

F quadruple_poly::eval(const F &x) const {
    return ((((a * x) + b) * x + c) * x + d) * x + e;
}

void quadruple_poly::clear() {
    a.clear(); b.clear(); c.clear(); d.clear(); e.clear();
}

cubic_poly::cubic_poly() {a.clear(); b.clear(); c.clear(); d.clear();}
cubic_poly::cubic_poly(const F &aa, const F &bb, const F &cc, const F &dd) {
    a = aa;
    b = bb;
    c = cc;
    d = dd;
}


cubic_poly cubic_poly::operator + (const cubic_poly &x) const {
    return cubic_poly(a + x.a, b + x.b, c + x.c, d + x.d);
}

cubic_poly quadratic_poly::operator - (const cubic_poly &x) const {
    return cubic_poly(x.a , x.b - a, x.c - b, x.d - c);
}

F cubic_poly::eval(const F &x) const {
    return (((a * x) + b) * x + c) * x + d;
}

quadratic_poly::quadratic_poly() {a.clear(); b.clear(); c.clear();}
quadratic_poly::quadratic_poly(const F &aa, const F &bb, const F &cc) {
    a = aa;
    b = bb;
    c = cc;
}

quadratic_poly quadratic_poly::operator + (const quadratic_poly &x) const {
    return quadratic_poly(a + x.a, b + x.b, c + x.c);
}

quadratic_poly quadratic_poly::operator+(const linear_poly &x) const {
    return quadratic_poly(a, b + x.a, c + x.b);
}

quadratic_poly linear_poly::operator-(const quadratic_poly &x) const {
    return quadratic_poly(-x.a, a - x.b, b - x.c);
}


cubic_poly quadratic_poly::operator * (const linear_poly &x) const {
    return cubic_poly(a * x.a, a * x.b + b * x.a, b * x.b + c * x.a, c * x.b);
}

cubic_poly cubic_poly::operator * (const F &x) const {
    return cubic_poly(a * x, b * x, c * x, d * x);
}

void cubic_poly::clear() {
    a.clear(); b.clear(); c.clear(); d.clear();
}

quadratic_poly quadratic_poly::operator*(const F &x) const {
    return quadratic_poly(a * x, b * x, c * x);
}

F quadratic_poly::eval(const F &x) const {
    return ((a * x) + b) * x + c;
}

void quadratic_poly::clear() {
    a.clear(); b.clear(); c.clear();
}

linear_poly::linear_poly() {a.clear(); b.clear();}
linear_poly::linear_poly(const F &aa, const F &bb) {
    a = aa;
    b = bb;
}
linear_poly::linear_poly(const F &x) {
    a.clear();
    b = x;
}

linear_poly linear_poly::operator + (const linear_poly &x) const {
    return linear_poly(a + x.a, b + x.b);
}

quadratic_poly linear_poly::operator * (const linear_poly &x) const {
    return quadratic_poly(a * x.a, a * x.b + b * x.a, b * x.b);
}

linear_poly linear_poly::operator*(const F &x) const {
    return linear_poly(a * x, b * x);
}

F linear_poly::eval(const F &x) const {
    return a * x + b;
}

void linear_poly::clear() {
    a.clear(); b.clear();
}

vector<F> mul_poly(vector<F> line,vector<F> poly){
    vector<F> product(poly.size()+1,F(0));
    for(int i = 0; i < poly.size(); i++){
        product[i] = poly[i]*line[0];
    }
    for(int i = 0; i < poly.size(); i++){
        product[i+1] += poly[i]*line[1];
    }
    return product;
}

vector<F> negate_poly(vector<F> poly){
    poly[0] = F(1)- poly[0];
    
    for(int i = 1; i < poly.size(); i++){
        poly[i] = F(0) - poly[i];
    }
    
    return poly;
}

vector<F> add_poly(vector<F> poly1, vector<F> poly2){
    for(int i = 0; i < poly1.size(); i++){
        poly1[i] += poly2[i];
    }
    
    return poly1;
}


// Computes the restriction of the polynomial to the given line
vector<F> reduce_poly(vector<vector<F>> line, vector<F> poly){
    vector<vector<F>> polynomials(poly.size());
    for(int i = 0; i < polynomials.size(); i++){
        polynomials[i].push_back(poly[i]);
    }
    for(int i = 0; i < line.size(); i++){
        int L = 1<<(line.size() - 1 - i);
        for(int j = 0; j < L; j++){

            polynomials[j] = add_poly(mul_poly(negate_poly(line[i]),polynomials[2*j]),mul_poly(line[i],polynomials[2*j+1]));
        }
    }
    return polynomials[0];
}


F univariate_eval(vector<F> poly, F x){
    F y = poly[poly.size()-1];
    for(int i = poly.size()-2; i >= 0; i--){
        y = y*x + poly[i]; 
    }
    return y;
}


