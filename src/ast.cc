#include "ast.h"
#include "parser.h"
#include <ostream>

namespace syntaxTree {

SymbolTable symbol_table;
Ast ast;

void Node::output(std::ostream &out) const {
  switch (label()) {
  case EOF:
    break;
  case LPAREN:
    out << "(";
    break;
  case RPAREN:
    out << ")";
    break;
  case LBRACKET:
    out << "[";
    break;
  case RBRACKET:
    out << "]";
    break;
  case SET_LOGIC:
    out << "set-logic";
    break;
  case ASSERT:
    out << "assert";
    break;
  case CHECK_SAT:
    out << "check-sat";
    break;
  case DECLARE_FUN:
    out << "declare_fun";
    break;
  case EXIT:
    out << "exit";
    break;
  case GET_ASSIGNMENT:
    out << "get-assignment";
    break;
  case NUMERAL:
    out << symbol_table.str(ref());
    break;
  case BOOL:
    out << "BOOL";
    break;
  case SYMBOL:
    out << symbol_table.str(ref());
    break;
  case NOT:
    out << "NOT";
    break;
  case AND:
    out << "AND";
    break;
  case EQUAL:
    out << "=";
    break;
  case OR:
    out << "or";
    break;
  case INT:
    out<<"INT";
     break;
  case PLUS:
    out<<"PLUS";
    break;
  case MUL:
    out<<"MUL";
    break;
  case ANDORLIST:
    out<<"ANDORLIST";break;
      case LIST:
          out<<"LIST";break;
      case MINUS :
          out<<"MINUS";break;
      case LETLIST:
          out<<"LETLIST";break;
      case LETTERM:
          out<<"LETTERM";break;
      case LET:
          out<<"LET";break;
      case GE:
          out<<">=";break;
      case LE:
          out<<"<=";break;
      case LARGE:
          out<<">";break;
      case SMALL:
          out<<"<";break;
      case TRUE_TOK:
          out<<"TRUE";break;
      case FALSE_TOK:
          out<<"FALSE";break;
      case ITE:
          out<<"ITE";break;
      case ITELIST:
          out<<"ITELIST";break;
      case REPRESENT:
    out << symbol_table.str(ref());
          break;

    
  default:
    out << "?";
  }
}

void Ast::output(std::ostream &out) const { output(out, root()); }

void Ast::output(std::ostream &out, const Node &nd) const {
  static int level = 0;
  level++;

  const Node &lc = node_vec_[nd.left_child()];
  const Node &rc = node_vec_[nd.right_child()];

  if (nd.label() == LIST) {
    output(out, lc);
    output(out, rc);
  } else {

    static int first_out_level = -1;
    if (first_out_level == -1) {
      first_out_level = level;
    }

    if (nd.left_child() != 0 && nd.right_child() != 0) {
      out << "[";
      nd.output(out);
      out << " ";
      output(out, lc);
      out << " ";
      output(out, rc);
      out << "]";
    } else if (nd.left_child() != 0) {
      nd.output(out);
      out << " ";
      output(out, lc);
    } else if (nd.right_child() != 0) {
      nd.output(out);
      out << " ";
      output(out, rc);
    } else {
      nd.output(out);
    }

    if (level == first_out_level) {
      out << std::endl;
      first_out_level = -1;
    }
  }
  level--;
}

void Ast::print_tree(){
    for(size_t i=0;i<node_vec_.size();i++){
        std::cout<<i<<' '<<' '<<node_vec_[i].left_child()<<' '<<node_vec_[i].right_child()<<' '<<"lable:"<<' '<<node_vec_[i].label()<<' ';
        ast[i].output(std::cout);
        std::cout<<std::endl;
    }
}
} // namespace syntaxTree
