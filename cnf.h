#ifndef CNF_H

#define CNF_H

//#include <endian.h>
#include <iostream>
#include <new>
#include <ostream>
#include <vector>
#include "ast.h"

/*! \class Literal
 *  \brief Brief class description
 *
 *  Detailed description
 */
class Literal {
public:
    Literal () {is_idl=true;}
    Literal(size_t a,size_t b,int k) {this->a=a;this->b=b;this->k=k;is_idl=true;}//under common circumstances, a-b<=k, if "distinct": a=k is denoted as pre=a, pos=-1, key=k; a!=b is denoted as pre=a, pos=b, key=-1
    Literal(size_t a, size_t b){this->a=a;this->b=b;is_idl=true;}
    Literal(int k){this->k=k;is_idl=false;}
    Literal(size_t a,int k){this->a=a;this->k=k;is_idl=false;}
    Literal(bool tf){this->true_false=(tf)?1:-1;this->is_idl=false;}
    void invert(){size_t tmp=a;a=b;b=tmp; k=-1-k;}
    void invertAB(){size_t tmp=a;a=b;b=tmp;}
    void invert_bool(){k=-k;}
    void inver_true_false(){true_false*=-1;}
    void invert_lit(){//change itself, and void
        if(this->is_idl){this->invert();}
        else if(this->true_false==0){this->invert_bool();}
        else{this->inver_true_false();}
    }
    friend Literal neg(Literal l){//return a neg lit
        l.invert_lit();
        return l;
    }
    friend bool operator==(const Literal lit1, const Literal lit2) {
        if(lit1.is_idl&&lit2.is_idl&&(lit1.a==lit2.a)&&(lit1.b==lit2.b)&&(lit1.k==lit2.k)){return true;}
        if(!lit1.is_idl&&!lit2.is_idl&&lit1.k==lit2.k){return true;}
        if(lit1.true_false!=0&&lit2.true_false!=0&&lit1.true_false==lit2.true_false){return true;}
        return false;
     }
    friend bool is_opp(Literal lit1,Literal lit2){
        return  lit1==neg(lit2);
    }
public:
  size_t  a; /*!< Member description */
  size_t b;
  int  k;
  bool is_idl=true;
    int true_false=0;//1 means true, -1 means false
};

using Clause = std::vector<Literal>;
using Formular = std::vector<Clause>;

class cnfUtility {
public:
  cnfUtility() : var_num(0) {}
    int new_variable() { syntaxTree::symbol_table.index("new_var"+std::to_string(new_var_num++)); return var_num++; }
  Literal tran_and(Literal a, Literal b, Formular &formular);
  Literal tran_or(Literal a, Literal b, Formular &formular);

public:
  int var_num;
    int new_var_num=0;
};

#endif /* end of include guard: CNF_H */
