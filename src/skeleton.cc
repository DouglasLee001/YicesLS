#include "skeleton.h"
#include "ast.h"
#include "parser.h"
#include "cnf.h"
#include <cassert>
#include<string>
#include<queue>
//#include <endian.h>

namespace skeleton {

bool Skeleton::transform(syntaxTree::Ast &ast, size_t index) {
  const syntaxTree::Node &ast_node = ast[index];
  switch (ast_node.label()) {
  case LIST:
    return transform(ast, ast_node.left_child())&&transform(ast, ast_node.right_child());
    break;
  case ASSERT:
    return set_to(ast, ast_node.left_child());
    break;
      case DECLARE_FUN:{
          syntaxTree::symbol_table.set_sym_is_idl(ast[ast_node.left_child()].ref(), ast[ast_node.right_child()].label());
      }
          break;
  default:
    break;
  }
    return true;
}

// top level
bool Skeleton::set_to(syntaxTree::Ast &ast, size_t index) {
    size_t node_idx=index;
    bool flag_first=false;
    bool after_and=false;
    //if there is an AND after the first AND/OR or there is ite, tseitin should be applied
    std::queue<size_t> que;
    que.push(node_idx);
    while(!que.empty()){
        node_idx=que.front();
        que.pop();
        if(flag_first&&ast[node_idx].label()==AND){after_and=true;break;}
        if(ast[node_idx].label()==ITE||ast[node_idx].label()==IMPLY){after_and=true;break;}
        if(flag_first==false&&(ast[node_idx].label()==OR||ast[node_idx].label()==AND)){flag_first=true;}
        if(ast[node_idx].left_child()!=0&&ast[node_idx].label()!=EQUAL){que.push(ast[node_idx].left_child());}
        if(ast[node_idx].right_child()!=0&&ast[node_idx].label()!=EQUAL){que.push(ast[node_idx].right_child());}
    }
    if(after_and){
        return false;
//        let_set(ast, index);
//        convert_term_tseitin(ast, index, true);
    }
    else{convert_term(ast, index,true);return true;}
}

void Skeleton::let_set(syntaxTree::Ast &ast, size_t index){
    const syntaxTree::Node &ast_node = ast[index];
    switch (ast_node.label()) {
        case LETTERM:{
            if(let2term.find( ast[ast_node.left_child()].ref())==let2term.end())
                let2term[ast[ast_node.left_child()].ref()]=ast_node.right_child();
            if(let2lit.find(ast[ast_node.left_child()].ref())==let2lit.end()){
                Literal l=convert_term_tseitin(ast, ast_node.right_child(), true);
                let2lit[ast[ast_node.left_child()].ref()]=l;
            }
        }
            break;
        case LETLIST:{
            let_set(ast, ast_node.left_child());
            if(ast_node.right_child()!=0){let_set(ast, ast_node.right_child());}
        }
            break;
        case LET:{
            let_set(ast, ast_node.left_child());
            let_set(ast, ast_node.right_child());
        }
            break;
        default:
            top_level_set_to(ast, index, true, true);
            break;
    }
}
void Skeleton::top_level_set_to(syntaxTree::Ast &ast, size_t index, bool value,bool isAnd){
    const syntaxTree::Node &ast_node = ast[index];
    if(ast_node.label()==LET){let_set(ast, index);return;}
      else if (ast_node.label() == AND && value) {
          const syntaxTree::Node &left_node = ast[ast_node.left_child()];
          top_level_set_to(ast, left_node.left_child(), value,true);
          top_level_set_to(ast, left_node.right_child(), value,true);
          return;
      }
      else if (ast_node.label() == OR && !value) {
          const syntaxTree::Node &left_node = ast[ast_node.left_child()];
          top_level_set_to(ast, left_node.left_child(), value,false);
          top_level_set_to(ast, left_node.right_child(), value,false);
          return;
      }
    else if(ast_node.label()==ANDORLIST&&((isAnd&&value)||(!isAnd&&!value))){
        top_level_set_to(ast, ast_node.left_child(), value, isAnd);
        top_level_set_to(ast, ast_node.right_child(), value, isAnd);
        return;
    }
    else if(ast_node.label()==NOT){
        top_level_set_to(ast, ast_node.left_child(), !value, isAnd);
        return;
    }
    else if(ast_node.label()==EQUAL){
        if(ast[ast_node.right_child()].label()==TRUE_TOK){
            top_level_set_to(ast, ast_node.left_child(), value, isAnd);return;}
        else if(ast[ast_node.right_child()].label()==FALSE_TOK){
            top_level_set_to(ast, ast_node.left_child(), !value, isAnd);return;}
    }
    
    Literal lit;
    if(ast_node.label()==REPRESENT){lit=let2lit[ast_node.ref()];}
    else{lit= convert_term_tseitin(ast, index,isAnd);}
      formular_.push_back(Clause());
      if (!value) {lit.invert_lit();}
      formular_.back().push_back(lit);
}

size_t Skeleton::plus_right(syntaxTree::Ast &ast,size_t index){
    const syntaxTree::Node &ast_node=ast[index];
    if(ast_node.label()==MUL){return ast[ast_node.right_child()].ref();}
    else {return plus_right(ast, let2term[ast_node.ref()]);}//Represent
}
void Skeleton::set_a_b_k(syntaxTree::Ast &ast,size_t index,size_t &a,bool &is_plus,size_t &b,int &k){
    const syntaxTree::Node &ast_node = ast[index];
    switch (ast_node.label()) {
        case REPRESENT:
            set_a_b_k(ast, let2term[ast_node.ref()], a, is_plus, b, k);
            break;
        case NUMERAL:
            k=std::atoi(syntaxTree::symbol_table.str(ast_node.ref()).c_str());
            break;
        case PLUS:{
            is_plus=true;
            if(ast[ast_node.left_child()].label()==SYMBOL){a=ast[ast_node.left_child()].ref();}
            else{k=std::atoi(syntaxTree::symbol_table.str(ast[ast_node.left_child()].ref()).c_str());}
            if(ast[ast_node.right_child()].label()==SYMBOL){b=ast[ast_node.right_child()].ref();}
            else if(ast[ast_node.right_child()].label()==NUMERAL){k=std::atoi(syntaxTree::symbol_table.str(ast[ast_node.right_child()].ref()).c_str());}
            else {is_plus=false;b=plus_right(ast, ast_node.right_child());}
        }
            break;
        case MINUS:{
            is_plus=false;
            a=ast[ast_node.left_child()].ref();
            b=ast[ast_node.right_child()].ref();
        }
            break;
        case SYMBOL:{
            a=ast_node.ref();
        }
            break;
        default:
            break;
    }
    
}

void Skeleton::convert_term(syntaxTree::Ast &ast, size_t index,bool isAnd) {
  const syntaxTree::Node &ast_node = ast[index];
    size_t left_a,left_b,right_a,right_b;
    int left_k,right_k;
    bool left_is_plus,right_is_plus;
    left_a=left_b=right_a=right_b=-1;
    left_k=right_k=0;

  switch (ast_node.label()) {
      case LET:
      {
          convert_term(ast, ast_node.left_child(), isAnd);
          convert_term(ast, ast_node.right_child(), isAnd);
      }
          break;
    case LETTERM:
            {
                if(let2term.find( ast[ast_node.left_child()].ref())==let2term.end())
                    let2term[ast[ast_node.left_child()].ref()]=ast_node.right_child();
            }
            break;
    case LETLIST:
    {
        convert_term(ast, ast_node.left_child(),isAnd);
        convert_term(ast, ast_node.right_child(),isAnd);
    }
        break;
      case ANDORLIST:
      {
          convert_term(ast, ast_node.left_child(),isAnd);
          convert_term(ast, ast_node.right_child(),isAnd);
      }
          break;
      case AND:{
          convert_term(ast, ast_node.left_child(),true);
      }
    break;
      case OR:{
          if(isAnd){formular_.push_back(Clause());}
          convert_term(ast, ast_node.left_child(),false);
      }
    break;
      case NOT:{
          convert_term(ast, ast_node.left_child(),isAnd);
          if(ast[ast_node.left_child()].label()!=EQUAL)
              formular_.back().back().invert_lit();
          else{
              formular_.back().back().invert();
              formular_.back()[formular_.back().size()-2].invert();
          }
      }
    break;
      case MINUS:
      {
          if(isAnd){
              Clause c;
              formular_.push_back(c);
          }
          size_t left=ast[ast_node.left_child()].ref();
          size_t right=ast[ast_node.right_child()].ref();
          Literal lit (left,right);
          formular_.back().push_back(lit);
      }
          break;
      case PLUS:{
          if(isAnd){
              Clause c;
              formular_.push_back(c);
          }
          size_t left=ast[ast_node.left_child()].ref();
          size_t right=plus_right(ast, ast_node.right_child());
          Literal lit (left,right);
          formular_.back().push_back(lit);
      }
          break;
      case GE:{//la(+/-)lb+lk >= ra(+/-)rb+rk  here cannot reach MINUS
          set_a_b_k(ast, ast_node.left_child(), left_a, left_is_plus, left_b, left_k);
          set_a_b_k(ast, ast_node.right_child(), right_a, right_is_plus, right_b, right_k);
          size_t A,B;//A-B<=K
          A=B=0;
          int K=0;
          if(isAnd){formular_.push_back(Clause());}
          K+=(left_k-right_k);
          if(left_a!=-1){B=left_a;}
          if(left_b!=-1){
              if(left_is_plus){B=left_b;}
              else{A=left_b;}
          }
          if(right_a!=-1){A=right_a;}
          if(right_b!=-1){
              if(right_is_plus){A=right_b;}
              else{B=right_b;}
          }
          if(A==B){
              if(K>=0){formular_.back().push_back(Literal(true));}
              else{formular_.back().push_back(Literal(false));}
          }
          else
          formular_.back().push_back(Literal(A,B,K));
      }
          break;
      case LE:{//la(+/-)lb+lk <= ra(+/-)rb+rk
          if(isAnd){formular_.push_back(Clause());}
          set_a_b_k(ast, ast_node.left_child(), left_a, left_is_plus, left_b, left_k);
          set_a_b_k(ast, ast_node.right_child(), right_a, right_is_plus, right_b, right_k);
          size_t A,B;//A-B<=K
          A=B=0;
          int K=0;
          K+=(right_k-left_k);
          if(left_a!=-1){A=left_a;}
          if(left_b!=-1){
              if(left_is_plus){A=left_b;}
              else{B=left_b;}
          }
          if(right_a!=-1){B=right_a;}
          if(right_b!=-1){
              if(right_is_plus){B=right_b;}
              else{A=right_b;}
          }
          if(A==B){
              if(K>=0){formular_.back().push_back(Literal(true));}
              else{formular_.back().push_back(Literal(false));}
          }
          else
          formular_.back().push_back(Literal(A,B,K));
      }
          break;
      case LARGE:{//la(+/-)lb+lk > ra(+/-)rb+rk-->la(+/-)lb+lk-1 >= ra(+/-)rb+rk
          if(isAnd){formular_.push_back(Clause());}
          set_a_b_k(ast, ast_node.left_child(), left_a, left_is_plus, left_b, left_k);
          set_a_b_k(ast, ast_node.right_child(), right_a, right_is_plus, right_b, right_k);
          size_t A,B;//A-B<=K
          A=B=0;
          int K=-1;
          K+=(left_k-right_k);
          if(left_a!=-1){B=left_a;}
          if(left_b!=-1){
              if(left_is_plus){B=left_b;}
              else{A=left_b;}
          }
          if(right_a!=-1){A=right_a;}
          if(right_b!=-1){
              if(right_is_plus){A=right_b;}
              else{B=right_b;}
          }
          if(A==B){
              if(K>=0){formular_.back().push_back(Literal(true));}
              else{formular_.back().push_back(Literal(false));}
          }
          else
          formular_.back().push_back(Literal(A,B,K));
      }
          break;
      case SMALL:{//la(+/-)lb+lk < ra(+/-)rb+rk-->la(+/-)lb+lk <= ra(+/-)rb+rk-1
          if(isAnd){formular_.push_back(Clause());}
          set_a_b_k(ast, ast_node.left_child(), left_a, left_is_plus, left_b, left_k);
          set_a_b_k(ast, ast_node.right_child(), right_a, right_is_plus, right_b, right_k);
          size_t A,B;//A-B<=K
          A=B=0;
          int K=-1;
          K+=(right_k-left_k);
          if(left_a!=-1){A=left_a;}
          if(left_b!=-1){
              if(left_is_plus){A=left_b;}
              else{B=left_b;}
          }
          if(right_a!=-1){B=right_a;}
          if(right_b!=-1){
              if(right_is_plus){B=right_b;}
              else{A=right_b;}
          }
          if(A==B){
              if(K>=0){formular_.back().push_back(Literal(true));}
              else{formular_.back().push_back(Literal(false));}
          }
          else
          formular_.back().push_back(Literal(A,B,K));
      }
          break;
      case EQUAL:{
          if(isAnd){
              Clause c;
              formular_.push_back(c);
          }
          if(ast[ast_node.right_child()].label()==SYMBOL&&syntaxTree::symbol_table.get_sym_is_idl(ast[ast_node.right_child()].ref())){//a==b (idl var) if
              size_t left=ast[ast_node.left_child()].ref();
              size_t right=ast[ast_node.right_child()].ref();
              Literal l1(left,right,0);
              Literal l2(right,left,0);
              formular_.back().push_back(l1);
              formular_.back().push_back(l2);
          }
          else if(ast[ast_node.right_child()].label()==NUMERAL){//a-b==k
              int key=std::atoi(syntaxTree::symbol_table.str(ast[ast_node.right_child()].ref()).c_str());
              convert_term(ast, ast_node.left_child(), isAnd);
              convert_term(ast, ast_node.left_child(), false);
              formular_.back()[formular_.back().size()-2].invertAB();
              formular_.back()[formular_.back().size()-2].k=-key;
              formular_.back().back().k=key;
          }
          else if(ast[ast_node.right_child()].label()==TRUE_TOK)
              formular_.back().push_back(Literal(ast[ast_node.left_child()].ref(),1));
          else if(ast[ast_node.right_child()].label()==FALSE_TOK)
              formular_.back().push_back(Literal(ast[ast_node.left_child()].ref(),-1));
          else{//a==(or/and/not lits)
              size_t cur_formular_size=formular_.size();
              Literal left_l((int)ast[ast_node.left_child()].ref());
              if(ast[ast_node.right_child()].label()!=AND){//or/not/>=
//                  if(ast[ast_node.right_child()].label()!=OR)
                  formular_.push_back(Clause());
                  convert_term(ast, ast_node.right_child(), false);
                  size_t or_size=formular_.back().size();
                  formular_.back().push_back(neg(left_l));
                  for(int i=0;i<or_size;i++){
                      formular_.push_back(Clause());
                      formular_.back().push_back(neg(formular_[cur_formular_size][i]));
                      formular_.back().push_back(left_l);
                  }
              }
              else{//and a=(and b c)-->-aVb ^ -aVc ^ -bV-cVa
                  convert_term(ast, ast_node.right_child(), true);
                  size_t new_formular_size=formular_.size();
                  formular_.push_back(Clause());
                  for(;cur_formular_size<new_formular_size;cur_formular_size++){
                      formular_[cur_formular_size].push_back(neg(left_l));
                      formular_.back().push_back(neg(formular_[cur_formular_size][0]));
                  }
                  formular_.back().push_back(left_l);
              }
          }
      }
          break;
      case SYMBOL:{//the original bool var
          if(isAnd){formular_.push_back(Clause());}
          formular_.back().push_back(Literal(ast_node.ref(),1));
      }
          break;
      case IMPLY:{
          if(ast[ast_node.right_child()].label()!=EQUAL){//a=>(lit)
              convert_term(ast, ast_node.left_child(), isAnd);
              formular_.back().back().invert_lit();
              convert_term(ast, ast_node.right_child(), false);
          }
          else{//a=>(= b c) the right side is an idl lit
              convert_term(ast, ast_node.right_child(), true);
              if(formular_.back()[0].is_idl){//the right side is an idl lit, then the result is in one clause
                  Clause c=formular_.back();
                  formular_.pop_back();
                  convert_term(ast, ast_node.left_child(), isAnd);
                  formular_.back().back().invert_lit();
                  formular_.back().push_back(c[0]);
                  convert_term(ast, ast_node.left_child(), isAnd);
                  formular_.back().back().invert_lit();
                  formular_.back().push_back(c[1]);
              }
              else{// the right side is a bool lit,
                  convert_term(ast, ast_node.left_child(), true);
                  Clause c=formular_.back();
                  formular_.pop_back();
                  size_t old_size=formular_.size();
                  formular_[old_size-1].push_back(neg(c[0]));
                  formular_[old_size-2].push_back(neg(c[0]));
              }
          }
      }
          break;
      case REPRESENT:
      {
          convert_term(ast, let2term[ast_node.ref()], isAnd);
      }
          break;
    // theory term
  default:
    break;
  }
}

Literal Skeleton::convert_term_tseitin(syntaxTree::Ast &ast, size_t index,bool isAnd){
    const syntaxTree::Node &ast_node = ast[index];
    size_t left_a,left_b,right_a,right_b;
    int left_k,right_k;
    bool left_is_plus,right_is_plus;
    left_a=left_b=right_a=right_b=-1;
    left_k=right_k=0;
    Literal l;
    switch (ast_node.label()) {
//        case LET:{
//            convert_term_tseitin(ast, ast_node.left_child(), isAnd);
//            convert_term_tseitin(ast, ast_node.right_child(), isAnd);
//            return l;
//        }
//            break;
//      case LETTERM:{
//                  if(let2term.find( ast[ast_node.left_child()].ref())==let2term.end())
//                  {let2term[ast[ast_node.left_child()].ref()]=ast_node.right_child();}
//                  return l;
//              }
//              break;
//      case LETLIST:{
//          convert_term_tseitin(ast, ast_node.left_child(),isAnd);
//          convert_term_tseitin(ast, ast_node.right_child(),isAnd);
//          return l;
//      }
//          break;
        case ANDORLIST:{
            Literal l1=convert_term_tseitin(ast, ast_node.left_child(),isAnd);
            Literal l2=convert_term_tseitin(ast, ast_node.right_child(),isAnd);
            if(isAnd){return cnf_utility.tran_and(l1, l2, formular_);}
            else{return  cnf_utility.tran_or(l1, l2, formular_);}
        }
            break;
        case TRUE_TOK:{return Literal(true);}
            break;
        case FALSE_TOK:{return Literal(false);}
            break;
        case AND:{return convert_term_tseitin(ast, ast_node.left_child(),true);}
      break;
        case OR:{return convert_term_tseitin(ast, ast_node.left_child(),false);}
      break;
        case NOT:{
            l=convert_term_tseitin(ast, ast_node.left_child(),isAnd);
            if(l.is_idl){l.invert();}
            else{l.invert_bool();}
            return l;
        }
      break;
        case MINUS:{
            size_t left=ast[ast_node.left_child()].ref();
            size_t right=ast[ast_node.right_child()].ref();
            return Literal(left,right);
        }
            break;
        case GE:{//la(+/-)lb+lk >= ra(+/-)rb+rk
            set_a_b_k(ast, ast_node.left_child(), left_a, left_is_plus, left_b, left_k);
            set_a_b_k(ast, ast_node.right_child(), right_a, right_is_plus, right_b, right_k);
            size_t A,B;//A-B<=K
            A=B=0;
            int K=0;
            K+=(left_k-right_k);
            if(left_a!=-1){B=left_a;}
            if(left_b!=-1){
                if(left_is_plus){B=left_b;}
                else{A=left_b;}
            }
            if(right_a!=-1){A=right_a;}
            if(right_b!=-1){
                if(right_is_plus){A=right_b;}
                else{B=right_b;}
            }
            if(A==B){
                if(K>=0){return Literal(true);}
                else{return Literal(false);}
            }
            else
            return Literal(A,B,K);
        }
            break;
        case LE:{//la(+/-)lb+lk <= ra(+/-)rb+rk
            if(isAnd){formular_.push_back(Clause());}
            set_a_b_k(ast, ast_node.left_child(), left_a, left_is_plus, left_b, left_k);
            set_a_b_k(ast, ast_node.right_child(), right_a, right_is_plus, right_b, right_k);
            size_t A,B;//A-B<=K
            A=B=0;
            int K=0;
            K+=(right_k-left_k);
            if(left_a!=-1){A=left_a;}
            if(left_b!=-1){
                if(left_is_plus){A=left_b;}
                else{B=left_b;}
            }
            if(right_a!=-1){B=right_a;}
            if(right_b!=-1){
                if(right_is_plus){B=right_b;}
                else{A=right_b;}
            }
            if(A==B){
                if(K>=0){return Literal(true);}
                else{return Literal(false);}
            }
            else
            return Literal(A,B,K);
        }
            break;
        case LARGE:{//la(+/-)lb+lk > ra(+/-)rb+rk-->la(+/-)lb+lk-1 >= ra(+/-)rb+rk
            if(isAnd){formular_.push_back(Clause());}
            set_a_b_k(ast, ast_node.left_child(), left_a, left_is_plus, left_b, left_k);
            set_a_b_k(ast, ast_node.right_child(), right_a, right_is_plus, right_b, right_k);
            size_t A,B;//A-B<=K
            A=B=0;
            int K=-1;
            K+=(left_k-right_k);
            if(left_a!=-1){B=left_a;}
            if(left_b!=-1){
                if(left_is_plus){B=left_b;}
                else{A=left_b;}
            }
            if(right_a!=-1){A=right_a;}
            if(right_b!=-1){
                if(right_is_plus){A=right_b;}
                else{B=right_b;}
            }
            if(A==B){
                if(K>=0){return Literal(true);}
                else{return Literal(false);}
            }
            else
            return Literal(A,B,K);
        }
            break;
        case SMALL:{//la(+/-)lb+lk < ra(+/-)rb+rk-->la(+/-)lb+lk <= ra(+/-)rb+rk-1
            if(isAnd){formular_.push_back(Clause());}
            set_a_b_k(ast, ast_node.left_child(), left_a, left_is_plus, left_b, left_k);
            set_a_b_k(ast, ast_node.right_child(), right_a, right_is_plus, right_b, right_k);
            size_t A,B;//A-B<=K
            A=B=0;
            int K=-1;
            K+=(right_k-left_k);
            if(left_a!=-1){A=left_a;}
            if(left_b!=-1){
                if(left_is_plus){A=left_b;}
                else{B=left_b;}
            }
            if(right_a!=-1){B=right_a;}
            if(right_b!=-1){
                if(right_is_plus){B=right_b;}
                else{A=right_b;}
            }
            if(A==B){
                if(K>=0){return Literal(true);}
                else{return Literal(false);}
            }
            else
            return Literal(A,B,K);
        }
            break;
        case EQUAL:{
            Literal l1,l2;
            if(ast[ast_node.right_child()].label()==SYMBOL&&syntaxTree::symbol_table.get_sym_is_idl(ast[ast_node.right_child()].ref())){//a==b-->a-b<=0^b-a<=0
                size_t left=ast[ast_node.left_child()].ref();
                size_t right=ast[ast_node.right_child()].ref();
                l1=Literal(left,right,0);
                l2=Literal(right,left,0);
            }
            else if(ast[ast_node.right_child()].label()==NUMERAL){//a-b==k-->a-b<=k^b-a<=-k
                int key=std::atoi(syntaxTree::symbol_table.str(ast[ast_node.right_child()].ref()).c_str());
                l1=convert_term_tseitin(ast, ast_node.left_child(), isAnd);
                l2=convert_term_tseitin(ast, ast_node.left_child(), false);
                l2.invertAB();
                l2.k=-key;
                l1.k=key;
            }
            else if(ast[ast_node.right_child()].label()==TRUE_TOK)
                return convert_term_tseitin(ast, ast_node.left_child(), isAnd);
            else if(ast[ast_node.right_child()].label()==FALSE_TOK)
                return neg(convert_term_tseitin(ast, ast_node.left_child(), isAnd));
            else{//bool lit== bool lit
                Literal l_left=convert_term_tseitin(ast, ast_node.left_child(), false);
                Literal l_right=convert_term_tseitin(ast, ast_node.right_child(), false);
                l1=cnf_utility.tran_or(neg(l_left), l_right, formular_);
                l2=cnf_utility.tran_or(l_left, neg(l_right), formular_);
            }
            return cnf_utility.tran_and(l1,l2,formular_);
        }
            break;
        case ITE:{//ite a b c-->(-aVb)^(aVc)
            l=convert_term_tseitin(ast, ast_node.left_child(), isAnd);
            const syntaxTree::Node &ast_node_right = ast[ast_node.right_child()];
            Literal b=convert_term_tseitin(ast, ast_node_right.left_child(), isAnd);
            Literal c=convert_term_tseitin(ast, ast_node_right.right_child(), isAnd);
            Literal l1=cnf_utility.tran_or(neg(l), b, formular_);
            Literal l2=cnf_utility.tran_or(l, c, formular_);
            return cnf_utility.tran_and(l1, l2, formular_);
        }
            break;
        case SYMBOL:{return Literal((int)ast_node.ref());}
            break;
        case IMPLY:{
            Literal l1=convert_term_tseitin(ast, ast_node.left_child(), isAnd);
            Literal l2=convert_term_tseitin(ast, ast_node.right_child(), isAnd);
            return cnf_utility.tran_or(neg(l1), l2,formular_);
        }
            break;
        case REPRESENT:{
//            return convert_term_tseitin(ast, let2term[ast_node.ref()], isAnd);
            return  let2lit[ast_node.ref()];
        }
            break;
      // theory term
    default:
            return l;
      break;
    }
}

} // namespace skeleton
