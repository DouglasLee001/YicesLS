#ifndef AST_H

#define AST_H

#include <cassert>
#include <cstddef>
#include <iostream>
#include <map>
#include <ostream>
#include <string>
#include <vector>
#include "parser.h"

#define verbose 0

namespace syntaxTree {

/*! \class SymbolTable
 *  \brief Brief class description
 *
 *  Detailed description
 */
class SymbolTable {
public:
  size_t index(const std::string &str) {
    if (symbol_index_.find(str) == symbol_index_.end()) {
      symbol_index_[str] = symbol_table_.size();
      symbol_table_.push_back(str);
      return symbol_table_.size() - 1;
    } else {
      return symbol_index_[str];
    }
  }
    void set_sym_is_idl(size_t ref,int label){is_idl_vec_[ref]=(label==INT)?true:false;}
    bool get_sym_is_idl(size_t ref){return is_idl_vec_[ref];}
    int sym_size(){return (int)symbol_table_.size();}
  const std::string &str(const size_t index) const {
    assert(index < symbol_table_.size());
    return symbol_table_[index];
  }

private:
  std::vector<std::string> symbol_table_; /*!< Member description */
  std::map<std::string, size_t> symbol_index_;
    std::map<size_t, bool> is_idl_vec_;
};

extern SymbolTable symbol_table;

/*! \class Node
 *  \brief Brief class description
 *
 *  Detailed description
 */
class Node {
public:
  Node() : label_(0), left_child_(0), right_child_(0) {}

  Node(int l) : label_(l), left_child_(0), right_child_(0) {}

  Node(int l, const std::string &str)
      : label_(l), left_child_(0), right_child_(0),
        ref_(symbol_table.index(str)) {}

  Node(int l, std::size_t c1) : label_(l), left_child_(c1), right_child_(0) {}

  Node(int l, size_t c1, size_t c2)
      : label_(l), left_child_(c1), right_child_(c2) {}

  bool is_empty() { return label_ == 0; }

  int label() const { return label_; }
  size_t left_child() const { return left_child_; }
  size_t right_child() const { return right_child_; }
  size_t ref() const { return ref_; }

  void output(std::ostream &out) const;

private:
  int label_;
  size_t left_child_, right_child_;
  size_t ref_; /*!< additional string reference */
};

/*! \class Ast
 *  \brief Brief class description
 *
 *  Detailed description
 */
class Ast {
public:
    bool is_validation=false;
  /* make dummy 0 node */
  Ast() { node_vec_.push_back(Node()); }

  size_t new_node() {
    if (verbose == 3) {
      std::cout << "new_node: "
                << "empty" << std::endl;
    }
    node_vec_.push_back(Node());
    return node_vec_.size() - 1;
  }

  size_t new_node(int label) {
    if (verbose == 3) {
      std::cout << "new_node: " << label << std::endl;
    }
    node_vec_.push_back(Node(label));
    return node_vec_.size() - 1;
  }

  size_t new_node(int label, const std::string &str) {
    if (verbose == 3) {
      std::cout << "new_node: " << label << '\t' << str << std::endl;
    }
    node_vec_.push_back(Node(label, str));
    return node_vec_.size() - 1;
  }

  size_t new_node(int label, size_t c1, size_t c2) {
    if (verbose == 3) {
      std::cout << "new_node: " << label << "\tc1: " << c1 << "\tc2: " << c2
                << std::endl;
    }
    node_vec_.push_back(Node(label, c1, c2));
    return node_vec_.size() - 1;
  }

  size_t new_node(int label, size_t c1) {
    if (verbose == 3) {
      std::cout << "new_node: " << label << '\t' << c1 << std::endl;
    }
    node_vec_.push_back(Node(label, c1));
    return node_vec_.size() - 1;
  }

  size_t node_size() { return node_vec_.size(); }

  bool check_sat() const {
    if (verbose == 3) {
      std::cout << "checking" << std::endl;
    }
    return true;
  }
    void get_model(){is_validation=true;}

  const size_t root_index() const { return node_vec_.size() - 1; }

  const Node &operator[](size_t index) const { return node_vec_[index]; }

  const Node &root() const { return node_vec_[root_index()]; }

  void output(std::ostream &out) const;

  void output(std::ostream &out, const Node &nd) const;
  
    void print_tree();

private:
  std::vector<Node> node_vec_; /*!< Member description */
};

extern Ast ast;

} // namespace syntaxTree

#endif /* end of include guard: AST_H */
