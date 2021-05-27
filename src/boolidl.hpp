//
//  boolidl.hpp
//  parser
//
//  Created by DouglasLee on 2020/9/24.
//  Copyright © 2020 DouglasLee. All rights reserved.
//

#ifndef boolidl_hpp
#define boolidl_hpp

#include <cstdio>
#include <chrono>
#include <string.h>
#include "ast.h"
#include "parser.h"
#include "skeleton.h"
#include "Array.h"
#include<stack>
#include<random>
using namespace std;
bool parse_file(const std::string &file);
using skeleton::Skeleton;
using syntaxTree::ast;

namespace boolidl {
//if is_idl_lit: _vars[prevar_idx]-_vars[posvar_idx]<=key
//else: if key>0: _vars[prevar_idx] else: neg(_vars[prevar_idx)
struct lit{
    uint64_t    prevar_idx;
    uint64_t    posvar_idx;
    int     key;
    uint64_t    clause_idx;
    bool is_idl_lit;
};

struct variable{
    vector<lit>         literals;
    //idl vars in same clause
    vector<uint64_t>    neighbor_var_idxs_idl;
    //bool vars in same clause
    vector<uint64_t>    neighbor_var_idxs_bool;
    //vars in same lit
    vector<uint64_t>    neighbor_var_idxs_in_lit;
    vector<uint64_t>    clause_idxs;
//    uint64_t last_move_step;
    bool                is_delete=false;
    int score;// if it is a bool var, then the score is calculated beforehand
    string  var_name;
    bool is_idl;
    int up_bool=0;//the bool value of variables deleted(1 true -1 false)
};

struct clause{
    vector<lit>         literals;
    vector<lit>         idl_literals;
    vector<lit>         bool_literals;
    vector<uint64_t>    var_idxs;
    // int64_t sum_delta;
    uint64_t    sat_count;
    uint64_t    weight;
    bool        is_hard=true;
    //the lit with smallest delta
    lit         watch_lit;
    //the last true lit in a falsified clause
    lit         last_true_lit;
    int    min_delta;
    bool is_delete=false;
};

vector<clause>          _clauses;
stack<clause>           _reconstruct_stack;
inline bool        cmp_clause_weight(int a,int b){return _clauses[a].weight>_clauses[b].weight;}
class bool_ls_solver{
public:
    //basic informations and controls
    string                  _inst_file;
    vector<variable>        _vars;
    vector<variable>        _resolution_vars;
    uint64_t                _num_vars;
    uint64_t                _num_bool_vars;
    uint64_t                _num_idl_vars;
    uint64_t                _num_lits;
    uint64_t                _num_clauses;
    uint64_t                _max_lit_num_in_clause=0;
    uint64_t                _additional_len;
    int                     _random_seed;
    mt19937                 mt;
    map<int64_t,uint64_t>   sym2var;
    map<int,uint64_t>       sym2bool_var;
    double                  _cutoff;
    int64_t                _average_k_value;
    uint64_t                     smooth_probability;
    uint64_t               fix_0_var_idx;//the var is fixed to 0
    uint64_t                _lit_in_unsast_clause_num;
    uint64_t                _bool_lit_in_unsat_clause_num;
    //tabulist[2*var] and [2*var+1] means that var are forbidden to move forward or backward until then, for bool vars, only tabulist[2*var] counts
    vector<uint64_t>        tabulist;
    vector<int>             CClist;//CClist[2*var]==1 and [2*var+1]==1 means that var is allowed to move forward or backward, for bool vars, only CClist[2*var] counts
    vector<uint64_t>        last_move;
    vector<int>        operation_vec;
    vector<int>         operation_vec_idl;
    vector<int>         operation_vec_bool;
    vector<bool>         operation_is_last_true_vec;//for Novelty
    int                     h_inc;
    int                    CCmode=-1;//-1 means tabu; 0 means allowing the neighbor in clause; 1 means allowing the neighbor in lit (especially for idl); 2 means allowing opposite direction of neighbor in lit
    bool                    is_validation=false;
    uint64_t                softclause_weight_threshold;
    bool            second_choice=false;

    // tmp information :: -> users should not use them
    int64_t min_delta_lit_length;
    //the var has existed in the min_delta_list for [i] times
    vector<int64_t> exist_time;


    //data structure
//    vector<uint64_t> _unsat_clauses;
    vector<uint64_t> _unsat_soft_clauses;
    vector<uint64_t> _unsat_hard_clauses;
//    vector<uint64_t> _index_in_unsat_clauses;
    vector<int64_t> _index_in_unsat_soft_clauses;
    vector<int64_t> _index_in_unsat_hard_clauses;
    //critical changing value
    vector<int>     _forward_critical_value;
    vector<int>     _backward_critical_value;
    // the clause with one sat number, and contains more than one lits
    Array   *sat_num_one_clauses;
    //the idl_var and bool_var vector
    vector<uint64_t> idl_var_vec;
    vector<uint64_t> bool_var_vec;
    //to avoid choosing the same bool var
    vector<bool>    is_chosen_bool_var;


    //solution information
    vector<int> _solution;
    vector<int> _best_solution;
    uint64_t        _best_found_hard_cost;
    uint64_t        _best_found_hard_cost_this_restart;
    uint64_t        _best_found_soft_cost;
    double          _best_cost_time;
    uint64_t        _step;
    uint64_t        _max_step;
    uint64_t        _max_tries;


    
    // data structure for clause weighting
    uint64_t    _swt_threshold;
    float       _swt_p;//w=w*p+ave_w*(1-p)
    uint64_t    total_clause_weight;
    
    //time
    chrono::steady_clock::time_point start;

    bool_ls_solver();
    bool    parse_arguments(const int argc, char ** const argv);
    bool    build_instance(string inst);
    void    up_bool_vars();
    bool    local_search();
    void    print_solution(bool detailed);
    void    make_space();
    void    build_neighbor_clausenum();
    inline  int64_t get_cost();
    void    print_formula();
    inline  uint64_t    transfer_sym_to_var(int64_t sym);
    inline  uint64_t    transfer_sym_to_bool_var(int sym);
    inline  uint64_t    transfer_to_reduced_var(int v_idx);
    inline  uint64_t    transfer_to_reduced_bool_var(int v_idx);
    inline  int     lit_delta(lit &l);   // should save in structure(lit)
    int     calculate_cscore(int score,int subscore);
    void    clear_prev_data();
    double  TimeElapsed();
    void    transfer_smt2();


    //main functions
    void        initialize();
    void        initialize_variable_datas();
    void        initialize_clause_datas();
    void        random_walk_all();
    void        random_walk_all_bool();
    int64_t     pick_critical_move(int64_t & direction);
    int64_t     pick_critical_move_bool(int64_t & direction);
    void     swap_from_small_weight_clause();
    void        critical_move(uint64_t var_idx,uint64_t direction);
    void        update_clause_weight();
    void        update_clause_weight_critical();
    void        smooth_clause_weight();
    void        smooth_clause_weight_critical();
    
    //restart construction
    
    Array           *unsat_clause_with_assigned_var;//unsat clause with at least one assigned var
    vector<int>     var_is_assigned;//0 means the var is not assigned
    vector<int>     construct_unsat;//0 means the clause is unsat
    void            construct_slution_score();//construct the solution based on score
    uint64_t        pick_construct_idx(int &best_value);
    void            construct_move(int var_idx,int value);
    int             construct_score(int var_idx,int value);
    vector<int>     restart_unsat_num_in_unsat_clause;
    //resolution
    void            resolution();
    bool            is_equal(lit &l1,lit & l2);
    bool            is_neg(lit &l1,lit &l2);
    //unit prop
    void            unit_prop();
    void            reduce_clause();//reduce the deleted clauses and vars
    //functions for basic operations
    inline void sat_a_clause(uint64_t the_clause);
    inline void unsat_a_clause(uint64_t the_clause);
    bool        update_best_solutioin();
    void        hash_opt(int operation,int &var_idx,int &operation_direction,int &critical_value);
    void        modifyCC(uint64_t var_idx,uint64_t direction);
    //calculate the score and subscore of a critical operation
   void         critical_score_subscore(uint64_t var_idx,int change_value);
    int         critical_score(uint64_t var_idx,int change_value,int &safety);//only calculate the score
    int         critical_subscore(uint64_t var_idx,int change_value);//only calculate the subscore
    // add swap operation from a random sat_num==1 clause
    void        add_swap_operation(int &operation_idx);
    
    bool        check_solution();
    bool        check_best_solution();

    
};
}

#endif /* boolidl_hpp */
