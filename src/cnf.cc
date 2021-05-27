#include "cnf.h"

Literal cnfUtility::tran_and(Literal a, Literal b, Formular &formular) {
    if (a.true_false == 1) {
      return b;
    }
    if (b.true_false==1) {
      return a;
    }
    if (a.true_false == -1 || b.true_false == -1) {
      return Literal(false);
    }
    if(a==b){return a;}
    if(is_opp(a,b)){return Literal(false);}
  // a*b=o <==> (a + o')( b + o')(a'+b'+o)
  Literal o(new_variable());
  Clause clause;

  clause.reserve(2);
  clause.push_back(a);
  clause.push_back(neg(o));
  formular.push_back(std::move(clause));

  clause.clear();
  clause.reserve(2);
  clause.push_back(b);
  clause.push_back(neg(o));
  formular.push_back(std::move(clause));

  clause.clear();
  clause.reserve(3);
  clause.push_back(neg(a));
  clause.push_back(neg(b));
  clause.push_back(o);
  formular.push_back(std::move(clause));

  return o;
}

Literal cnfUtility::tran_or(Literal a, Literal b, Formular &formular) {
    if (a.true_false == -1) {
      return b;
    }
    if (b.true_false == -1) {
      return a;
    }
    if (a.true_false == 1 || b.true_false == 1) {
      return Literal(true);
    }
    if(a==b){return a;}
    if(is_opp(a,b)){return Literal(false);}

  // a+b=c <==> (a' + c)( b' + c)(a + b + c')
  Literal o(new_variable());
  Clause clause;

  clause.reserve(2);
  clause.push_back(neg(a));
  clause.push_back(o);
  formular.push_back(std::move(clause));

  clause.clear();
  clause.reserve(2);
  clause.push_back(neg(b));
  clause.push_back(o);
  formular.push_back(std::move(clause));

  clause.clear();
  clause.reserve(3);
  clause.push_back(a);
  clause.push_back(b);
  clause.push_back(neg(o));
  formular.push_back(std::move(clause));

  return o;
}
