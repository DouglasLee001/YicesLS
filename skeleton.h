#ifndef SKELETON_H

#define SKELETON_H

#include "ast.h"
#include "cnf.h"
//#include <endian.h>
#include <vector>
#include<string>

namespace skeleton {

/*! \class Node
 *  \brief Brief class description
 *
 *  Detailed description
 */
class Node {
public:
  void set_ast_index(size_t i) { ast_index_ = i; }
  void set_literal(Literal lit) { lit_ = lit; }

private:
  Literal lit_; /*!< Member description */
  size_t ast_index_;
};

/*! \class TheoryNode
 *  \brief Brief class description
 *
 *  Detailed description
 */
class TheoryNode {
public:
  TheoryNode(Literal l, const syntaxTree::Node &nd) : lit_(l), ast_node_(nd) {}

  const syntaxTree::Node &ast_node() { return ast_node_; }
  Literal lit() { return lit_; }

protected:
  Literal lit_; /*!< Member description */
  const syntaxTree::Node &ast_node_;
};

/*! \class Skeleton
 *  \brief Brief class description
 *
 *  Detailed description
 */
class Skeleton {
public:
    Skeleton() {cnf_utility.var_num=syntaxTree::symbol_table.sym_size();}
  bool transform(syntaxTree::Ast &ast, size_t index);
  void convert_term(syntaxTree::Ast &ast, size_t index,bool isAnd);
    Literal convert_term_tseitin(syntaxTree::Ast &ast, size_t index,bool isAnd);
    void set_a_b_k(syntaxTree::Ast &ast,size_t index,size_t &a,bool &is_plus,size_t &b,int &k);
    void top_level_set_to(syntaxTree::Ast &ast, size_t index, bool value,bool isAnd);
    void let_set(syntaxTree::Ast &ast, size_t index);
    size_t plus_right(syntaxTree::Ast &ast,size_t index);

  bool set_to(syntaxTree::Ast &ast, size_t index);

  void print_formular() {
    std::cout << "Printing formular" << std::endl;
      Clause clause=formular_[0];
    for (auto &clause : formular_) {
      for (auto l : clause) {
          if(l.true_false==-1)std::cout<<"false\n";
          else if(l.true_false==1)std::cout<<"true\n";
          else{
              if(l.is_idl)
                    std::cout<<syntaxTree::symbol_table.str(l.a)<<'-'<<syntaxTree::symbol_table.str(l.b)<<"<="<<l.k<<std::endl;
              else{
                  if(l.k<0){std::cout<<"-";}
                  std::cout<<syntaxTree::symbol_table.str(abs(l.k))<<"\n";
                  }
          }
      }
      std::cout << std::endl;
    }
  }

  void print_theory(syntaxTree::Ast &ast) {
    std::cout << "Printing theory" << std::endl;
      for (int i=0;i<ast.node_size();i++) {
//      syntaxTree::ast.output(std::cout, nd.ast_node());
//          ast.output(std::cout, ast[i]);
          ast[i].output(std::cout);
          std::cout<<std::endl<<i<<" "<<ast[i].left_child()<<" "<<ast[i].right_child()<<std::endl<<std::endl;
    }
  }

//  Literal ref2lit(const size_t ref) {
//    Literal lit;
//    if (ref2lit_.find(ref) != ref2lit_.end()) {
//      lit = ref2lit_[ref];
//    } else {
//      lit = cnf_utility.new_variable();
//      ref2lit_[ref] = lit;
//    }
//    return lit;
//  }

public:
  Formular formular_;
  std::map<size_t, Literal> ref2lit_; /*!< from symbol_table ref to lit */
    std:: map<size_t,size_t> let2term;//ref to term num
    std::map<size_t,Literal> let2lit;//represent to present a lit 
    cnfUtility cnf_utility;
    bool  is_distinct=false;
//  cnfUtility cnf_utility;
};

} // namespace skeleton

#endif /* end of include guard: SKELETON_H */
