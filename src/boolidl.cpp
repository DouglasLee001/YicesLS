//
//  boolidl.cpp
//  parser
//
//  Created by DouglasLee on 2020/9/24.
//  Copyright © 2020 DouglasLee. All rights reserved.
//

#include "boolidl.hpp"
#include <fstream>
#include <iostream>
#include <stack>
#include <algorithm>
#include <cstdlib>
#include<exception>
#include<time.h>
#include<signal.h>
#include<unistd.h>
#include<sys/types.h>
using namespace boolidl;

bool_ls_solver::bool_ls_solver(){
    _additional_len=10;
    _max_tries=1;
    _max_step=UINT64_MAX;
    _swt_p=0.7;
    _swt_threshold=50;
    smooth_probability=3;
}

/***parse parameters*****************/
bool     bool_ls_solver::parse_arguments(int argc, char ** argv)
{
    bool flag_inst = false;
    for (int i=1; i<argc; i++)
    {
        if(strcmp(argv[i],"-inst")==0)
        {
            i++;
            if(i>=argc) return false;
            _inst_file = argv[i];
            flag_inst = true;
            continue;
        }
        else if(strcmp(argv[i],"-seed")==0)
        {
            i++;
            if(i>=argc) return false;
            sscanf(argv[i], "%d", &_random_seed);
            continue;
        }
        else if(strcmp(argv[i],"-t")==0)
        {
            i++;
            if(i>=argc) return false;
            sscanf(argv[i], "%lf", &_cutoff);
            continue;
        }
        else if(strcmp(argv[i], "-CCmode")==0){
            if(++i>=argc) return false;
            sscanf(argv[i], "%d", &CCmode);
            continue;
        }
        else if(strcmp(argv[i], "-validation")==0){
            if(++i>=argc) return false;
            if(strcmp("true", argv[i])==0){is_validation=true;}
            continue;
        }
    }
    if (flag_inst) return true;
    else return false;
}

uint64_t bool_ls_solver::transfer_sym_to_var(int64_t sym){
    if(sym2var.find(sym)==sym2var.end()){
        sym2var[sym]=_resolution_vars.size();
        variable var;
        var.is_idl=true;
        var.var_name=syntaxTree::symbol_table.str(sym);
        _resolution_vars.push_back(var);
        idl_var_vec.push_back(_resolution_vars.size()-1);
        return _resolution_vars.size()-1;
    }
    else return sym2var[sym];
}

uint64_t bool_ls_solver::transfer_sym_to_bool_var(int sym){
    int sym_abs=abs(sym);
    if(sym2bool_var.find(sym_abs)==sym2bool_var.end()){
        sym2bool_var[sym_abs]=_resolution_vars.size();
        variable var;
        var.is_idl=false;
        var.clause_idxs.reserve(64);
        var.var_name=syntaxTree::symbol_table.str(sym_abs);
        _resolution_vars.push_back(var);
        bool_var_vec.push_back(_resolution_vars.size()-1);
        return _resolution_vars.size()-1;
    }
    else return sym2bool_var[sym_abs];
}

uint64_t bool_ls_solver::transfer_to_reduced_var(int v_idx){
    if(sym2var.find(v_idx)==sym2var.end()){
        sym2var[v_idx]=_vars.size();
        variable var;
        var.is_idl=true;
        var.var_name=_resolution_vars[v_idx].var_name;
        _vars.push_back(var);
        idl_var_vec.push_back(_vars.size()-1);
        return _vars.size()-1;
    }
    else return sym2var[v_idx];
}
uint64_t bool_ls_solver::transfer_to_reduced_bool_var(int v_idx){
    if(sym2bool_var.find(v_idx)==sym2bool_var.end()){
        sym2bool_var[v_idx]=_vars.size();
        variable var;
        var.is_idl=false;
        var.var_name=_resolution_vars[v_idx].var_name;
        _vars.push_back(var);
        bool_var_vec.push_back(_vars.size()-1);
        return _vars.size()-1;
    }
    else return sym2bool_var[v_idx];
}

void bool_ls_solver::make_space(){
    _solution.resize(_num_vars+_additional_len);
    _best_solution.resize(_num_vars+_additional_len);
    _index_in_unsat_hard_clauses.resize(_num_clauses+_additional_len,-1);
    _index_in_unsat_soft_clauses.resize(_num_clauses+_additional_len,-1);
    exist_time.resize(_num_vars);
    tabulist.resize(2*_num_vars+_additional_len);
    CClist.resize(2*_num_vars+_additional_len);
    _forward_critical_value.resize(_num_vars+_additional_len);
    _backward_critical_value.resize(_num_vars+_additional_len);
    operation_vec.resize(_num_lits*2+_additional_len);
    operation_vec_idl.resize(_num_lits*2+_additional_len);
    operation_vec_bool.resize(_num_lits*2+_additional_len);
    operation_is_last_true_vec.resize(_num_lits*2+_additional_len);
    var_is_assigned.resize(_num_vars);
    unsat_clause_with_assigned_var=new Array((int)_num_clauses);
    construct_unsat.resize(_num_clauses);
    last_move.resize(_num_vars*2+_additional_len);
    sat_num_one_clauses=new Array((int)_num_clauses);
    is_chosen_bool_var.resize(_num_vars+_additional_len,false);
}


/// build neighbor_var_idxs for each var
void bool_ls_solver::build_neighbor_clausenum(){
    uint64_t    j;
    uint64_t v, c;
    vector<char> neighbor_flag(_num_vars+_additional_len);
    vector<int64_t> clause_flag(_num_clauses+_additional_len);
    vector<int64_t> neighbor_in_lit_flag(_num_vars+_additional_len);
    for (j=0; j<neighbor_flag.size(); ++j ) {neighbor_flag[j] = 0;}
    for (j=0; j<neighbor_flag.size(); ++j ) {neighbor_in_lit_flag[j] = 0;}
    for (j=0;j<clause_flag.size();++j){clause_flag[j]=0;}
    for (v=0; v < _num_vars; ++v)
    {
        variable * vp = &(_vars[v]);
        for (lit lv : vp->literals)
        {
            if(lv.is_idl_lit){
            if(!neighbor_in_lit_flag[lv.prevar_idx]&&lv.prevar_idx!=v){
                neighbor_in_lit_flag[lv.prevar_idx]=1;
                vp->neighbor_var_idxs_in_lit.push_back(lv.prevar_idx);
            }
            if(!neighbor_in_lit_flag[lv.posvar_idx]&&lv.posvar_idx!=v){
                neighbor_in_lit_flag[lv.posvar_idx]=1;
                vp->neighbor_var_idxs_in_lit.push_back(lv.posvar_idx);
            }
            }
            c = lv.clause_idx;
            if (!clause_flag[c])
            {
                clause_flag[c] = 1;
                vp->clause_idxs.push_back(c);
                for (lit lc : _clauses[c].literals){
                    if(lc.is_idl_lit){//idl lit
                        if (!neighbor_flag[lc.prevar_idx] && lc.prevar_idx!=v){
                            neighbor_flag[lc.prevar_idx] = 1;
                            vp->neighbor_var_idxs_idl.push_back(lc.prevar_idx);
                        }
                        if (!neighbor_flag[lc.posvar_idx] && lc.posvar_idx!=v){
                            neighbor_flag[lc.posvar_idx] = 1;
                            vp->neighbor_var_idxs_idl.push_back(lc.posvar_idx);
                        }
                    }
                    else if (!neighbor_flag[lc.prevar_idx] && lc.prevar_idx!=v){//bool lit
                        neighbor_flag[lc.prevar_idx]=1;
                        vp->neighbor_var_idxs_bool.push_back(lc.prevar_idx);
                    }
                }
            }
        }
        for (uint64_t j:vp->neighbor_var_idxs_idl) {neighbor_flag[j] = 0;}
        for (uint64_t j:vp->neighbor_var_idxs_bool) {neighbor_flag[j]=0;}
        for (uint64_t j:vp->neighbor_var_idxs_in_lit) {neighbor_in_lit_flag[j] = 0;}
        for (j=0; j<vp->clause_idxs.size(); ++j) {clause_flag[vp->clause_idxs[j]] = 0;}
        for (j=0;j<vp->clause_idxs.size();++j){
            _clauses[vp->clause_idxs[j]].var_idxs.push_back(v);
        }
    }
}

bool bool_ls_solver::build_instance(string inst){
    parse_file(inst);
    Skeleton skeleton;
    _average_k_value=0;
    _num_lits=0;
    int num_idl_lit=0;
    h_inc=1;
    softclause_weight_threshold=1;
    is_validation=is_validation||ast.is_validation;
    if(!skeleton.transform(ast, ast.root_index()))return false;
//    skeleton.print_formular();
    for (auto &cl : skeleton.formular_) {
        if(cl.size()==0)
            continue;
        clause cur_clause;
        uint64_t last_clause_index=_clauses.size();
        bool exist_true=false;
        for (auto l : cl) {
            _num_lits++;
            lit curlit;
            if(l.is_idl){
                num_idl_lit++;
            curlit.is_idl_lit=true;
            uint64_t pre=transfer_sym_to_var(l.a);
            uint64_t pos=transfer_sym_to_var(l.b);
            curlit.prevar_idx=pre;
            curlit.posvar_idx=pos;
            curlit.key=l.k;
            _average_k_value+=abs(curlit.key);
            }
            else if(l.true_false==0){
                curlit.is_idl_lit=false;
                uint64_t bool_var_idx=transfer_sym_to_bool_var((int)l.a);
                curlit.prevar_idx=bool_var_idx;
                curlit.key=l.k;
                _resolution_vars[bool_var_idx].clause_idxs.push_back((int)last_clause_index);
            }
            else if(l.true_false==-1){continue;}// if there exists a false in a clause, pass it
            else if(l.true_false==1){exist_true=true;break;}//if there exists a true in a clause, the clause should not be added
            cur_clause.literals.push_back(curlit);
            cur_clause.is_hard=true;
            cur_clause.weight=1;
        }
        if(!exist_true){_clauses.push_back(cur_clause);}
    }
    if(sym2var.find(0)!=sym2var.end()){fix_0_var_idx=sym2var[0];}
    _num_clauses=_clauses.size();
//    uint64_t origin_num_clause=_num_clauses;
//    uint64_t origin_num_bool_var=bool_var_vec.size();
    unit_prop();
        resolution();
        unit_prop();
        reduce_clause();
//    print_formula();
//    cout<<"*********\n";
//    cout<<"origin clause num: "<<origin_num_clause<<endl;
//    cout<<"origin bool var:"<<origin_num_bool_var<<endl<<"new bool var:"<<bool_var_vec.size()<<endl;
    _num_clauses=_clauses.size();
    _num_vars=_vars.size();
    _num_bool_vars=bool_var_vec.size();
    _num_idl_vars=idl_var_vec.size();
    total_clause_weight=_num_clauses;
    make_space();
    build_neighbor_clausenum();
    if(num_idl_lit>0){_average_k_value/=num_idl_lit;}
    if(_average_k_value<1)_average_k_value=1;
    _best_found_hard_cost=_num_clauses;
    _best_found_soft_cost=0;
    return true;
}

void bool_ls_solver::reduce_clause(){
    sym2var.clear();
    int ave_lit_num=0;
    sym2bool_var.clear();
    bool_var_vec.clear();
    idl_var_vec.clear();
    _vars.reserve(_resolution_vars.size());
    int i,reduced_clause_num;
    i=0;reduced_clause_num=0;
    for(;i<_num_clauses;i++){if(!_clauses[i].is_delete){_clauses[reduced_clause_num++]=_clauses[i];}}
    _clauses.resize(reduced_clause_num);
    for(i=0;i<reduced_clause_num;i++){
        _clauses[i].weight=1;
        for(int k=0;k<_clauses[i].literals.size();k++){
            lit *l=&(_clauses[i].literals[k]);
            l->clause_idx=i;
            if(l->is_idl_lit){
                l->prevar_idx=transfer_to_reduced_var((int)l->prevar_idx);
                l->posvar_idx=transfer_to_reduced_var((int)l->posvar_idx);
                _vars[l->prevar_idx].literals.push_back(*l);
                _vars[l->posvar_idx].literals.push_back(*l);
                _clauses[i].idl_literals.push_back(*l);
            }
            else{
                l->prevar_idx=transfer_to_reduced_bool_var((int)l->prevar_idx);
                _vars[l->prevar_idx].literals.push_back(*l);
                _clauses[i].bool_literals.push_back(*l);
            }
            if(_clauses[i].literals.size()>_max_lit_num_in_clause){_max_lit_num_in_clause=_clauses[i].literals.size();}
        }
        ave_lit_num+=_clauses[i].literals.size();
    }
    _vars.resize(_vars.size());
//    cout<<_max_lit_num_in_clause<<endl<<ave_lit_num/(int)reduced_clause_num<<endl;
    int idl_max_lit=0;
    int idl_ave_lit=0;
    int bool_max_lit=0;
    int bool_ave_lit=0;
    for(uint64_t idl_var:idl_var_vec){
        int lit_size=(int)_vars[idl_var].literals.size();
        idl_ave_lit+=lit_size;
        if(lit_size>idl_max_lit)idl_max_lit=lit_size;
    }
    for(uint64_t bool_var:bool_var_vec){
        int lit_size=(int)_vars[bool_var].literals.size();
        bool_ave_lit+=lit_size;
        if(lit_size>bool_max_lit)bool_max_lit=lit_size;
    }
    if(bool_var_vec.size()==0)bool_ave_lit=0;
    else bool_ave_lit/=(int)bool_var_vec.size();
//    cout<<idl_max_lit<<endl<<idl_ave_lit/(int)idl_var_vec.size()<<endl<<bool_max_lit<<endl<<bool_ave_lit<<endl<<bool_var_vec.size()<<endl<<idl_var_vec.size()<<endl<<_clauses.size()<<endl;
}
//resolution
void bool_ls_solver::resolution(){
    vector<uint64_t> pos_clauses(10*_num_clauses);
    vector<uint64_t> neg_clauses(10*_num_clauses);
    int pos_clause_size,neg_clause_size;
    bool is_improve=true;
    while(is_improve){
        is_improve=false;
    for(uint64_t bool_var_idx:bool_var_vec){
        if(_resolution_vars[bool_var_idx].is_delete)continue;
        pos_clause_size=0;neg_clause_size=0;
        for(int i=0;i<_resolution_vars[bool_var_idx].clause_idxs.size();i++){
            uint64_t clause_idx=_resolution_vars[bool_var_idx].clause_idxs[i];
            if(_clauses[clause_idx].is_delete)continue;
            for(lit l:_clauses[clause_idx].literals){
                if(l.prevar_idx==bool_var_idx){
                    if(l.key>0){pos_clauses[pos_clause_size++]=clause_idx;}
                    else{neg_clauses[neg_clause_size++]=clause_idx;}
                    break;
                }
            }
        }//determine the pos_clause and neg_clause
        int tautology_num=0;
        for(int i=0;i<pos_clause_size;i++){//pos clause X neg clause
            uint64_t pos_clause_idx=pos_clauses[i];
            for(int j=0;j<neg_clause_size;j++){
                uint64_t neg_clause_idx=neg_clauses[j];
                for(int k=0;k<_clauses[neg_clause_idx].literals.size();k++){
                    lit l=_clauses[neg_clause_idx].literals[k];
                    if(l.prevar_idx!=bool_var_idx){//the bool_var for resolution is not considered
                        for(uint64_t x=0;x<_clauses[pos_clause_idx].literals.size();x++){
                            if(is_neg(l, _clauses[pos_clause_idx].literals[x])){
                                tautology_num++;
                                break;
                            }//if there exists (aVb)^(-aV-b), the new clause is tautology
                        }
                    }
                }
            }
        }
        if((pos_clause_size*neg_clause_size-tautology_num)>(pos_clause_size+neg_clause_size)){continue;}//if deleting the var can cause 2 times clauses, then skip it
        for(uint64_t clause_idx:_resolution_vars[bool_var_idx].clause_idxs){//delete the clauses of bool_var
            _clauses[clause_idx].is_delete=true;
            for(lit l:_clauses[clause_idx].literals){//delete the clause from corresponding bool var
                if(!l.is_idl_lit&&l.prevar_idx!=bool_var_idx){
                    uint64_t delete_idx=0;
                    for(;delete_idx<_resolution_vars[l.prevar_idx].clause_idxs.size();delete_idx++){
                        if(_resolution_vars[l.prevar_idx].clause_idxs[delete_idx]==clause_idx){
                            _resolution_vars[l.prevar_idx].clause_idxs[delete_idx]=_resolution_vars[l.prevar_idx].clause_idxs.back();
                            _resolution_vars[l.prevar_idx].clause_idxs.pop_back();
                            break;
                        }
                    }
                }
            }
        }
        is_improve=true;
        _resolution_vars[bool_var_idx].is_delete=true;
        if(pos_clause_size==0){_resolution_vars[bool_var_idx].up_bool=-1;}//if it is a false pure lit, the var is set to false
        if(neg_clause_size==0){_resolution_vars[bool_var_idx].up_bool=1;}//if it is a true pure lit, the var is set to true
        if(pos_clause_size==0||neg_clause_size==0)continue;//pos or neg clause is empty, meaning the clauses are SAT when assigned to true or false, then cannot resolute, just delete the clause
        for(int i=0;i<pos_clause_size;i++){//pos clause X neg clause
            uint64_t pos_clause_idx=pos_clauses[i];
            for(int j=0;j<neg_clause_size;j++){
                uint64_t neg_clause_idx=neg_clauses[j];
                clause new_clause;
                uint64_t pos_lit_size=_clauses[pos_clause_idx].literals.size();
                uint64_t neg_lit_size=_clauses[neg_clause_idx].literals.size();
                new_clause.literals.reserve(pos_lit_size+neg_lit_size);
                bool is_tautology=false;
                for(int k=0;k<pos_lit_size;k++){
                    lit l=_clauses[pos_clause_idx].literals[k];
                    if(l.prevar_idx!=bool_var_idx){new_clause.literals.push_back(l);}
                }//add the lits in pos clause to new clause
                for(int k=0;k<neg_lit_size;k++){
                    lit l=_clauses[neg_clause_idx].literals[k];
                    if(l.prevar_idx!=bool_var_idx){
                        bool is_existed_lit=false;
                        for(uint64_t i=0;i<pos_lit_size-1;i++){
                            if(is_equal(l, new_clause.literals[i])){is_existed_lit=true;break;}// if the lit has existed, then it will not be added
                            if(is_neg(l, new_clause.literals[i])){is_tautology=true;break;}//if there exists (aVb)^(-aV-b), the new clause is tautology
                        }
                        if(is_tautology){break;}
                        if(!is_existed_lit){new_clause.literals.push_back(l);}
                    }
                }
                if(!is_tautology){//add new clause, and modify the clause of corresponding bool var
                    for(lit l:new_clause.literals){
                        if(!l.is_idl_lit){
                            _resolution_vars[l.prevar_idx].clause_idxs.push_back((int)_num_clauses);
                        }
                    }
                    _clauses.push_back(new_clause);
                    _num_clauses++;
                }
            }
        }
        for(int i=0;i<pos_clause_size;i++){
            clause pos_cl=_clauses[pos_clauses[i]];
            for(int j=0;j<pos_cl.literals.size();j++){
                if(pos_cl.literals[j].prevar_idx==bool_var_idx){
                    lit tmp=pos_cl.literals[j];
                    pos_cl.literals[j]=pos_cl.literals[0];
                    pos_cl.literals[0]=tmp;
                    break;
                }
            }
            _reconstruct_stack.push(pos_cl);
        }
        for(int i=0;i<neg_clause_size;i++){
            clause neg_cl=_clauses[neg_clauses[i]];
            for(int j=0;j<neg_cl.literals.size();j++){
                if(neg_cl.literals[j].prevar_idx==bool_var_idx){
                    lit tmp=neg_cl.literals[j];
                    neg_cl.literals[j]=neg_cl.literals[0];
                    neg_cl.literals[0]=tmp;
                    break;
                }
            }
            _reconstruct_stack.push(neg_cl);
        }
    }
    }
}
void bool_ls_solver::up_bool_vars(){//reconstruct the solution by pop the stack
    for(int i=0;i<_resolution_vars.size();i++){if(!_resolution_vars[i].is_idl&&_resolution_vars[i].up_bool==0){_resolution_vars[i].up_bool=-1;}}//set all origin bool var as false
    while(!_reconstruct_stack.empty()){
        clause cl=_reconstruct_stack.top();
        _reconstruct_stack.pop();
        bool sat_flag=false;
        for(lit l:cl.literals){
            if(l.is_idl_lit){
                if(sym2var.find(l.prevar_idx)==sym2var.end()||sym2var.find(l.posvar_idx)==sym2var.end()){sat_flag=true;break;}
                else if(_best_solution[sym2var[l.prevar_idx]]-_best_solution[sym2var[l.posvar_idx]]<=l.key){sat_flag=true;break;}
            }
            else{
                if(sym2bool_var.find((int)l.prevar_idx)==sym2bool_var.end()){
                    if((l.key>0&&_resolution_vars[l.prevar_idx].up_bool>0)||(l.key<0&&_resolution_vars[l.prevar_idx].up_bool<0)){sat_flag=true;break;}}
                else if((_best_solution[sym2bool_var[(int)l.prevar_idx]]>0&&l.key>0)||(_best_solution[sym2bool_var[(int)l.prevar_idx]]<0&&l.key<0)){sat_flag=true;break;}
            }
        }
        if(sat_flag==false){_resolution_vars[cl.literals[0].prevar_idx].up_bool=1;}//if the clause is false, flip the var
    }
}

void bool_ls_solver::unit_prop(){
    stack<uint64_t> unit_clause;//the var_idx in the unit clause
    for(uint64_t clause_idx=0;clause_idx<_num_clauses;clause_idx++){//the unit clause is the undeleted clause containing only one bool var
        if(!_clauses[clause_idx].is_delete&&_clauses[clause_idx].literals.size()==1&&!_clauses[clause_idx].literals[0].is_idl_lit){unit_clause.push(clause_idx);}
    }
    while(!unit_clause.empty()){
        uint64_t unit_clause_idx=unit_clause.top();
        unit_clause.pop();
        if(_clauses[unit_clause_idx].is_delete){continue;}
        int is_pos_lit=_clauses[unit_clause_idx].literals[0].key;
        uint64_t unit_var=_clauses[unit_clause_idx].literals[0].prevar_idx;
        _resolution_vars[unit_var].up_bool=is_pos_lit;//set the solution of a boolean var as its unit propogation value
        _resolution_vars[unit_var].is_delete=true;
        for(uint64_t cl_idx:_resolution_vars[unit_var].clause_idxs){
            clause *cl=&(_clauses[cl_idx]);
            if(cl->is_delete)continue;
            for(uint64_t lit_idx=0;lit_idx<cl->literals.size();lit_idx++){
                lit l=cl->literals[lit_idx];
                if(!l.is_idl_lit&&l.prevar_idx==unit_var){
                    if((is_pos_lit>0&&l.key>0)||(is_pos_lit<0&&l.key<0)){
                        cl->is_delete=true;
                        for(lit l:cl->literals){//delete the clause from corresponding bool var
                            if(!l.is_idl_lit&&l.prevar_idx!=unit_var){
                                for(uint64_t delete_idx=0;delete_idx<_resolution_vars[l.prevar_idx].clause_idxs.size();delete_idx++){
                                    if(_resolution_vars[l.prevar_idx].clause_idxs[delete_idx]==cl_idx){
                                        _resolution_vars[l.prevar_idx].clause_idxs[delete_idx]=_resolution_vars[l.prevar_idx].clause_idxs.back();
                                        _resolution_vars[l.prevar_idx].clause_idxs.pop_back();
                                        break;
                                    }
                                }
                            }
                        }
                    }//if there exist same lit, the clause is already set true
                    else{//else delete the lit
                        cl->literals[lit_idx]=cl->literals.back();
                        cl->literals.pop_back();
                        if(cl->literals.size()==1&&!cl->literals[0].is_idl_lit){unit_clause.push(cl_idx);}//if after deleting, it becomes unit clause
                    }
                    break;
                }
            }
        }
    }
}

void bool_ls_solver::print_formula(){
    int i=0;
    for(clause & cl :_clauses){
        cout<<i++<<endl;
        for(lit & l: cl.literals){
            if(l.is_idl_lit)
            cout<<_vars[l.prevar_idx].var_name<<'-'<<_vars[l.posvar_idx].var_name<<"<="<<l.key<<endl;
            else{
                if(l.key<0)cout<<"-";
                cout<<_vars[l.prevar_idx].var_name<<endl;
                }
        }
        cout<<endl;
    }
}

void bool_ls_solver::clear_prev_data(){
    for(uint64_t v:bool_var_vec){_vars[v].score=0;}
}

/************initialization**************/

void bool_ls_solver::initialize_variable_datas(){
    
    //last move step
    for(uint64_t i=0;i<_num_vars;i++){last_move[2*i]=last_move[2*i+1]=0;}
    //tabulist
    for(uint64_t i=0;i<_num_vars;i++){tabulist[2*i]=tabulist[2*i+1]=0;}
    //CClist
    for (uint64_t i=0;i<_num_vars;i++){CClist[2*i]=CClist[2*i+1]=1;}
}

void bool_ls_solver::initialize_clause_datas(){
    _lit_in_unsast_clause_num=0;
    _bool_lit_in_unsat_clause_num=0;
    for(uint64_t c=0;c<_num_clauses;c++){
        _clauses[c].sat_count=0;
        _clauses[c].weight=1;
        _clauses[c].min_delta=INT32_MAX;
        _clauses[c].last_true_lit.prevar_idx=-1;
        for(lit l:_clauses[c].literals){
            int delta=lit_delta(l);
            if(delta<=0){
                _clauses[c].sat_count++;
                delta=0;
            }
            if(delta<_clauses[c].min_delta){
                _clauses[c].min_delta=delta;
                _clauses[c].watch_lit=l;
            }
        }
        if(_clauses[c].sat_count==0){
            unsat_a_clause(c);
            _lit_in_unsast_clause_num+=_clauses[c].literals.size();
            _bool_lit_in_unsat_clause_num+=_clauses[c].bool_literals.size();
            for(lit &bl:_clauses[c].bool_literals){_vars[bl.prevar_idx].score++;}
        }
        else{sat_a_clause(c);}
        if(_clauses[c].sat_count==1){sat_num_one_clauses->insert_element((int)c);
            if(!_clauses[c].watch_lit.is_idl_lit){_vars[_clauses[c].watch_lit.prevar_idx].score--;}}
        else{sat_num_one_clauses->delete_element((int)c);}
    }
    total_clause_weight=_num_clauses;
}

void bool_ls_solver::initialize(){
    clear_prev_data();
    construct_slution_score();
    initialize_clause_datas();
    initialize_variable_datas();
    _best_found_hard_cost_this_restart=_unsat_hard_clauses.size();
    update_best_solutioin();
}

/**********restart construction***********/


void bool_ls_solver::construct_slution_score(){
    fill(var_is_assigned.begin(), var_is_assigned.end(), 0);
    fill(construct_unsat.begin(), construct_unsat.end(), 0);
    unsat_clause_with_assigned_var->clear();
    uint64_t var_idx=idl_var_vec[mt()%idl_var_vec.size()];//first choose an idl var, assign it to 0
    int     best_value=0;
    var_is_assigned[var_idx]=1;
    _solution[var_idx]=best_value;
    for(uint64_t i: _vars[var_idx].clause_idxs){unsat_clause_with_assigned_var->insert_element(int (i));}
    for(int i=1;i<_num_vars;i++){
        var_idx=pick_construct_idx(best_value);
        construct_move((int)var_idx, best_value);
    }
}

uint64_t bool_ls_solver::pick_construct_idx(int &best_value){
    int best_score,score,cnt,value,direction,var_idx;
    uint64_t    best_var_idx=0;
    best_score=INT32_MIN;
    best_value=0;
    int operation_idx=0;
    for(int i=0;i<unsat_clause_with_assigned_var->size();i++){
        clause *cl=&(_clauses[unsat_clause_with_assigned_var->element_at(i)]);
        for(lit l:cl->literals){
            if(l.is_idl_lit){
            //one var is assigned while the other is not
            if(var_is_assigned[l.prevar_idx]==0&&var_is_assigned[l.posvar_idx]==1){
                var_idx=(int)l.prevar_idx;
                value=l.key+_solution[l.posvar_idx];
                operation_vec[operation_idx++]=value*(int)_num_vars+var_idx;
            }
            if(var_is_assigned[l.posvar_idx]==0&&var_is_assigned[l.prevar_idx]==1){
                var_idx=(int)l.posvar_idx;
                value=-l.key+_solution[l.prevar_idx];
                operation_vec[operation_idx++]=value*(int)_num_vars+var_idx;
            }
            }
            else if(var_is_assigned[l.prevar_idx]==0){
                value=(l.key>0)?1:-1;
                var_idx=(int)l.prevar_idx;
                operation_vec[operation_idx++]=value*(int)_num_vars+var_idx;
            }
        }
    }
    shuffle(operation_vec.begin(), operation_vec.begin()+operation_idx, mt);
    cnt=min(45,operation_idx);
    for(int i=0;i<cnt;i++){
        hash_opt(operation_vec[i], var_idx, direction, value);
        score=construct_score(var_idx, value);
        if(score>best_score){
            best_score=score;
            best_var_idx=var_idx;
            best_value=value;
        }
    }
    //if there is no operation, choose a random unassigned var and assign it randomly
    if(cnt==0){
        int i=0;
        for(;i<_num_vars;i++){if(var_is_assigned[i]==0){best_var_idx=i; break;}}
        if(_vars[i].is_idl){best_value=mt()%_average_k_value;}
        else{best_value=(mt()%2==0)?1:-1;}
    }
    return best_var_idx;
}

int bool_ls_solver::construct_score(int var_idx, int value){
    int score=0;
    variable *var=&(_vars[var_idx]);
    if(var->is_idl){
    uint64_t last_sat_clause_idx=UINT64_MAX;
    for(uint64_t i=0;i<var->literals.size();i++){
        lit l=var->literals[i];
        // the clause is sat
        if(l.clause_idx==last_sat_clause_idx||construct_unsat[l.clause_idx]==1){
            last_sat_clause_idx=l.clause_idx;
            continue;
        }
        if( ((int)l.posvar_idx==var_idx&&var_is_assigned[l.prevar_idx]==1&&(value>=(_solution[l.prevar_idx]-l.key)))||
            ((int)l.prevar_idx==var_idx&&var_is_assigned[l.posvar_idx]==1&&(value<=(_solution[l.posvar_idx]+l.key))) ){
            // score++;
           score+=_clauses[l.clause_idx].weight;
            last_sat_clause_idx=l.clause_idx;
        }
    }
    }
    else{
        for(uint64_t i=0;i<var->literals.size();i++){
            lit l=var->literals[i];
            if(construct_unsat[l.clause_idx]==1) {continue;}
            else if((l.key>0&&value>0)||(l.key<0&&value<0)) {score+=_clauses[l.clause_idx].weight;}
        }
    }
    return score;
}

//set solution[var_idx] to value
void bool_ls_solver::construct_move(int var_idx, int value){
    variable *var=&(_vars[var_idx]);
    if(var->is_idl){
    uint64_t last_sat_clause_idx=UINT64_MAX;
    for(uint64_t i=0;i<var->literals.size();i++){
        lit l=var->literals[i];
        // the clause is sat
        if(l.clause_idx==last_sat_clause_idx||construct_unsat[l.clause_idx]==1){
            last_sat_clause_idx=l.clause_idx;
            continue;
        }
        if( ((int)l.posvar_idx==var_idx&&var_is_assigned[l.prevar_idx]==1&&(value>=(_solution[l.prevar_idx]-l.key)))||
            ((int)l.prevar_idx==var_idx&&var_is_assigned[l.posvar_idx]==1&&(value<=(_solution[l.posvar_idx]+l.key))) ){
            construct_unsat[l.clause_idx]=1;
            last_sat_clause_idx=l.clause_idx;
        }
    }
    }
    else{
        for(uint64_t i=0;i<var->literals.size();i++){
            lit l=var->literals[i];
            if((l.key>0&&value>0)||(l.key<0&&value<0)){construct_unsat[l.clause_idx]=1;}
        }
    }
    for(uint64_t clause_idx:_vars[var_idx].clause_idxs){
        if(construct_unsat[clause_idx]==0){unsat_clause_with_assigned_var->insert_element((int)clause_idx);}
        else{unsat_clause_with_assigned_var->delete_element((int)clause_idx);}
    }
    _solution[var_idx]=value;
    var_is_assigned[var_idx]=1;
}
/**********sat or unsat a clause***********/
void bool_ls_solver::unsat_a_clause(uint64_t the_clause){
    if(_clauses[the_clause].is_hard==true&&_index_in_unsat_hard_clauses[the_clause]==-1){
        _index_in_unsat_hard_clauses[the_clause]=_unsat_hard_clauses.size();
        _unsat_hard_clauses.push_back(the_clause);
    }
    else if(_clauses[the_clause].is_hard==false&&_index_in_unsat_soft_clauses[the_clause]==-1){
        _index_in_unsat_soft_clauses[the_clause]=_unsat_soft_clauses.size();
        _unsat_soft_clauses.push_back(the_clause);
    }
}

void bool_ls_solver::sat_a_clause(uint64_t the_clause){
    uint64_t index,last_item;
    //use the position of the clause to store the last unsat clause in stack
    if(_clauses[the_clause].is_hard==true&&_index_in_unsat_hard_clauses[the_clause]!=-1){
        last_item = _unsat_hard_clauses.back();
        _unsat_hard_clauses.pop_back();
        index = _index_in_unsat_hard_clauses[the_clause];
        _index_in_unsat_hard_clauses[the_clause]=-1;
        if(last_item!=the_clause){
            _unsat_hard_clauses[index] = last_item;
            _index_in_unsat_hard_clauses[last_item] = index;
            }
        }
    else if(_clauses[the_clause].is_hard==false&&_index_in_unsat_soft_clauses[the_clause]!=-1){
        last_item = _unsat_soft_clauses.back();
        _unsat_soft_clauses.pop_back();
        index = _index_in_unsat_soft_clauses[the_clause];
        _index_in_unsat_soft_clauses[last_item]=-1;
        if(last_item!=the_clause){
            _unsat_soft_clauses[index] = last_item;
            _index_in_unsat_soft_clauses[last_item] = index;
            }
        }
}

/**********calculate the delta of a lit***********/
int bool_ls_solver::lit_delta(lit& l){
    if(l.is_idl_lit)
    return _solution[l.prevar_idx]-_solution[l.posvar_idx]-l.key;
    else{
        if((_solution[l.prevar_idx]>0&&l.key>0)||(_solution[l.prevar_idx]<0&&l.key<0))return 0;
        else return 1;// 1 or average_k
    }
}

/**********lit equal or neg***********/
bool bool_ls_solver::is_equal(lit &l1, lit &l2){
    if(l1.is_idl_lit&&l2.is_idl_lit){return l1.prevar_idx==l2.prevar_idx&&l1.posvar_idx==l2.posvar_idx&&l2.posvar_idx&&l1.key==l2.key;}
    else if(!l1.is_idl_lit&&!l2.is_idl_lit){return (l1.prevar_idx==l2.prevar_idx)&&((l1.key>0&&l2.key>0)||(l1.key<0&&l2.key<0));}
    return false;
}
bool bool_ls_solver::is_neg(lit &l1, lit &l2){
    if(l1.is_idl_lit&&l2.is_idl_lit){return l1.prevar_idx==l2.posvar_idx&&l1.posvar_idx==l2.prevar_idx&&(l1.key==(-1-l2.key));}
    else if(!l1.is_idl_lit&&!l2.is_idl_lit){return (l1.prevar_idx==l2.prevar_idx)&&((l1.key>0&&l2.key<0)||(l1.key<0&&l2.key>0));}
    return false;
}

int bool_ls_solver::calculate_cscore(int score, int subscore){
    return score-subscore/_average_k_value;
}

/**********modify the CClist***********/
void bool_ls_solver::modifyCC(uint64_t var_idx, uint64_t direction){
    uint64_t opposite_direction=(direction+1)%2;
    variable * vp = &(_vars[var_idx]);
    if(vp->is_idl){CClist[2*var_idx+opposite_direction]=0;}
    else{CClist[2*var_idx]=0;}
    for(uint64_t v:vp->neighbor_var_idxs_bool){CClist[2*v]++;}// allow the bool clause neighbor
    if(!vp->is_idl){for(uint64_t v:vp->neighbor_var_idxs_idl){CClist[2*v]++;CClist[2*v+1]++;}}//the bool var, allow the idl clause neighbor
    else{
        if(CCmode==0){for(uint64_t v:_vars[var_idx].neighbor_var_idxs_idl){CClist[2*v]++;CClist[2*v+1]++;}}
        //the idl var with CCmode 0, allow the idl clause neighbor
        else if(CCmode==1){for(uint64_t v:_vars[var_idx].neighbor_var_idxs_in_lit){CClist[2*v]++;CClist[2*v+1]++;}}
        //the idl var with CCmode 1, allow the idl lit neighbor
        else if(CCmode==2){for(uint64_t v:_vars[var_idx].neighbor_var_idxs_in_lit){CClist[2*v+opposite_direction]++;}}
        //the idl var with CCmode 2 allow the opposite direction of idl lit neighbor
    }
}
/**********calculate score and subscore of critical operation***********/

void bool_ls_solver::critical_score_subscore(uint64_t var_idx,int change_value){
    int delta_old,delta_new;
    variable *var=&(_vars[var_idx]);
    //number of make_lits in a clause
    int make_break_in_clause=0;
    lit watch_lit;
    //the future min delta containing var
    int new_future_min_delta=INT32_MAX;
    if(var->is_idl){
    for(uint64_t i=0;i<var->literals.size();i++){
        lit l=var->literals[i];
        delta_old=lit_delta(l);
        if(var_idx==l.prevar_idx) delta_new=delta_old+change_value;
        else    delta_new=delta_old-change_value;
        if(delta_old<=0&&delta_new>0) make_break_in_clause--;
        else if(delta_old>0&&delta_new<=0) make_break_in_clause++;
        if(delta_new<new_future_min_delta){
            new_future_min_delta=delta_new;
            watch_lit=l;
        }
        //enter a new clause or the last literal
        if((i!=(var->literals.size()-1)&&l.clause_idx!=var->literals[i+1].clause_idx)||i==(var->literals.size()-1)){
            clause *cp=&(_clauses[l.clause_idx]);
            if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) {
                cp->last_true_lit=cp->watch_lit;
                unsat_a_clause(l.clause_idx);
                _lit_in_unsast_clause_num+=cp->literals.size();
                _bool_lit_in_unsat_clause_num+=cp->bool_literals.size();
            }
            else if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) {
                sat_a_clause(l.clause_idx);
                _lit_in_unsast_clause_num-=cp->literals.size();
                _bool_lit_in_unsat_clause_num-=cp->bool_literals.size();
            }
            lit origin_watch_lit=cp->watch_lit;
            uint64_t origin_sat_count=cp->sat_count;
            cp->sat_count+=make_break_in_clause;
            if(cp->sat_count==1){sat_num_one_clauses->insert_element((int)l.clause_idx);}
            else{sat_num_one_clauses->delete_element((int)l.clause_idx);}
            new_future_min_delta=max(0,new_future_min_delta);
            //if new_future_min_delta<=cp->min_delta, then min_delta and watch needs updating if var is changed
            if(new_future_min_delta<=cp->min_delta){
                cp->min_delta=new_future_min_delta;
                cp->watch_lit=watch_lit;
            }
            else if(cp->watch_lit.prevar_idx==var_idx||cp->watch_lit.posvar_idx==var_idx){
                    for(lit lc:cp->literals){
                        if(lc.prevar_idx!=var_idx&&lc.posvar_idx!=var_idx&&(max(0,lit_delta(lc))<new_future_min_delta)){
                            new_future_min_delta=max(0,lit_delta(lc));
                            watch_lit=lc;
                        }
                    }
                    cp->min_delta=new_future_min_delta;
                    cp->watch_lit=watch_lit;
                }//if new_future_min_delta>cp->min_delta and var_idx belongs to the watch_lit
            if(_num_bool_vars>0){
            if(make_break_in_clause>0){
                if(origin_sat_count==0){for(lit &bl:cp->bool_literals){_vars[bl.prevar_idx].score-=cp->weight;}}
                else if(origin_sat_count==1&&!origin_watch_lit.is_idl_lit){_vars[origin_watch_lit.prevar_idx].score+=cp->weight;}
            }
            if(make_break_in_clause<0){
                if(cp->sat_count==0){for(lit &bl:cp->bool_literals){_vars[bl.prevar_idx].score+=cp->weight;}}
                else if(cp->sat_count==1&&!cp->watch_lit.is_idl_lit){_vars[cp->watch_lit.prevar_idx].score-=cp->weight;}
            }
            }
            new_future_min_delta=INT32_MAX;
            make_break_in_clause=0;
        }
    }
    }
    else{
        for(uint64_t i=0;i<var->literals.size();i++){
            lit l=var->literals[i];
            if(lit_delta(l)==0){//true to false
                make_break_in_clause=-1;
                new_future_min_delta=1;//TODO::average_k
            }
            else{//false to true
                make_break_in_clause=1;
                new_future_min_delta=0;
            }
            watch_lit=l;
            clause *cp=&(_clauses[l.clause_idx]);
            if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) {
                cp->last_true_lit=cp->watch_lit;
                unsat_a_clause(l.clause_idx);
                _lit_in_unsast_clause_num+=cp->literals.size();
                _bool_lit_in_unsat_clause_num+=cp->bool_literals.size();
            }
            else if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) {
                sat_a_clause(l.clause_idx);
                _lit_in_unsast_clause_num-=cp->literals.size();
                _bool_lit_in_unsat_clause_num-=cp->bool_literals.size();
            }
            lit origin_watch_lit=cp->watch_lit;
            uint64_t origin_sat_count=cp->sat_count;
            cp->sat_count+=make_break_in_clause;
            if(cp->sat_count==1){sat_num_one_clauses->insert_element((int)l.clause_idx);}
            else{sat_num_one_clauses->delete_element((int)l.clause_idx);}
            if(new_future_min_delta<=cp->min_delta){
                cp->min_delta=new_future_min_delta;
                cp->watch_lit=watch_lit;
            }
            else if(cp->watch_lit.prevar_idx==var_idx){
                    for(lit lc:cp->literals){
                        if(lc.prevar_idx!=var_idx&&(max(0,lit_delta(lc))<new_future_min_delta)){
                            new_future_min_delta=max(0,lit_delta(lc));
                            watch_lit=lc;
                        }
                    }
                    cp->min_delta=new_future_min_delta;
                    cp->watch_lit=watch_lit;
                }
            if(_num_bool_vars>0){
            if(make_break_in_clause>0){
                if(origin_sat_count==0){for(lit &bl:cp->bool_literals){_vars[bl.prevar_idx].score-=cp->weight;}}
                else if(origin_sat_count==1&&!origin_watch_lit.is_idl_lit){_vars[origin_watch_lit.prevar_idx].score+=cp->weight;}
            }
            else if(make_break_in_clause<0){
                if(cp->sat_count==0){for(lit &bl:cp->bool_literals){_vars[bl.prevar_idx].score+=cp->weight;}}
                else if(cp->sat_count==1&&!cp->watch_lit.is_idl_lit){_vars[cp->watch_lit.prevar_idx].score-=cp->weight;}
            }
            }
        }
    }
}
int bool_ls_solver::critical_score(uint64_t var_idx, int change_value,int &safety){
    int critical_score=0;
    safety=0;
    int delta_old,delta_new;
    variable *var=&(_vars[var_idx]);
    //number of make_lits in a clause
    int make_break_in_clause=0;
    if(var->is_idl){
    for(uint64_t i=0;i<var->literals.size();i++){
        lit l=var->literals[i];
        delta_old=lit_delta(l);
        if(var_idx==l.prevar_idx) delta_new=delta_old+change_value;
        else    delta_new=delta_old-change_value;
        if(delta_old<=0&&delta_new>0) make_break_in_clause--;
        else if(delta_old>0&&delta_new<=0) make_break_in_clause++;
        //enter a new clause or the last literal
        if((i!=(var->literals.size()-1)&&l.clause_idx!=var->literals[i+1].clause_idx)||i==(var->literals.size()-1)){
            clause *cp=&(_clauses[l.clause_idx]);
            if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) critical_score+=cp->weight;
            else if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) critical_score-=cp->weight;
            if(cp->sat_count<=1&&cp->sat_count+make_break_in_clause>1){safety++;}
            else if(cp->sat_count>1&&cp->sat_count+make_break_in_clause<=1){safety--;}
            make_break_in_clause=0;
        }
    }
    }
    //if the var is a bool_var, then flip it
    else{
        for(uint64_t i=0;i<var->literals.size();i++){
            lit l=var->literals[i];
            if(lit_delta(l)>0){make_break_in_clause=1;}//false to true
            else{make_break_in_clause=-1;}//true to false
            clause *cp=&(_clauses[l.clause_idx]);
            if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) critical_score+=cp->weight;
            else if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) critical_score-=cp->weight;
            if(cp->sat_count<=1&&cp->sat_count+make_break_in_clause>1){safety++;}
            else if(cp->sat_count>1&&cp->sat_count+make_break_in_clause<=1){safety--;}
        }
    }
    return critical_score;
}

int bool_ls_solver::critical_subscore(uint64_t var_idx,int change_value){
    int critical_subscore=0;
    int delta_old,delta_new;
    variable *var=&(_vars[var_idx]);
    //the future min delta containing var
    int new_future_min_delta=INT32_MAX;
    if(var->is_idl){
    for(uint64_t i=0;i<var->literals.size();i++){
        lit l=var->literals[i];
        delta_old=lit_delta(l);
        if(var_idx==l.prevar_idx) delta_new=delta_old+change_value;
        else    delta_new=delta_old-change_value;
        if(delta_new<new_future_min_delta){new_future_min_delta=delta_new;}
        //enter a new clause or the last literal
        if((i!=(var->literals.size()-1)&&l.clause_idx!=var->literals[i+1].clause_idx)||i==(var->literals.size()-1)){
            clause *cp=&(_clauses[l.clause_idx]);
            new_future_min_delta=max(0,new_future_min_delta);
            if(new_future_min_delta<=cp->min_delta){
                critical_subscore+=(new_future_min_delta-cp->min_delta)*cp->weight;
            }
            else{
                //if new_future_min_delta>cp->min_delta and var_idx belongs to the watch_lit
                if(cp->watch_lit.prevar_idx==var_idx||cp->watch_lit.posvar_idx==var_idx){
                    for(lit lc:cp->literals){
                        if(lc.prevar_idx!=var_idx&&lc.posvar_idx!=var_idx&&(max(0,lit_delta(lc))<new_future_min_delta)){
                            new_future_min_delta=max(0,lit_delta(lc));
                        }
                    }
                    critical_subscore+=(new_future_min_delta-cp->min_delta)*cp->weight;
                }
            }
            new_future_min_delta=INT32_MAX;
        }
    }
    }
    else{
        for(uint64_t i=0;i<var->literals.size();i++){
            lit l=var->literals[i];
            if(lit_delta(l)==0){new_future_min_delta=1;}//TODO::average_k
            else{new_future_min_delta=0;}
            clause *cp=&(_clauses[l.clause_idx]);
            if(new_future_min_delta<=cp->min_delta){critical_subscore+=(new_future_min_delta-cp->min_delta)*cp->weight;}
            else if(cp->watch_lit.prevar_idx==var_idx){
                for(lit lc :cp->literals){
                    if(lc.prevar_idx!=var_idx&&(max(0,lit_delta(lc))<new_future_min_delta)){new_future_min_delta=max(0,lit_delta(lc));}
                }
                critical_subscore+=(new_future_min_delta-cp->min_delta)*cp->weight;
            }
        }
    }
    return critical_subscore;
}

/**********make move***********/

void bool_ls_solver::critical_move(uint64_t var_idx,uint64_t direction){
    if(_vars[var_idx].is_idl){
        int change_value=(direction==0)?(_forward_critical_value[var_idx]):(-_backward_critical_value[var_idx]);
        critical_score_subscore(var_idx, change_value);
        _solution[var_idx]+=change_value;
    }
    else{
        int origin_score=_vars[var_idx].score;
        critical_score_subscore(var_idx, 0);
        _solution[var_idx]*=-1;
        _vars[var_idx].score=-origin_score;
    }
    //step
    if(_vars[var_idx].is_idl){
        last_move[2*var_idx+direction]=_step;
        tabulist[var_idx*2+(direction+1)%2]=_step+3+mt()%10;
        if(CCmode!=-1){modifyCC(var_idx,direction);}
    }
    else{
        last_move[2*var_idx]=_step;
        tabulist[var_idx*2]=_step+3+mt()%10;
        if(CCmode!=-1){modifyCC(var_idx, direction);}
    }
}uint64_t pick_bool=0;
uint64_t pick_idl=0;
uint64_t walk_bool=0;
uint64_t walk_idl=0;
void bool_ls_solver::swap_from_small_weight_clause(){
    uint64_t min_weight=UINT64_MAX;
    uint64_t min_weight_clause_idx=0;
    for(int i=0;i<45;i++){
        int clause_idx=sat_num_one_clauses->rand_element();
        if(_clauses[clause_idx].weight<min_weight){
            min_weight=_clauses[clause_idx].weight;
            min_weight_clause_idx=clause_idx;
        }
    }
    clause *cl=&(_clauses[min_weight_clause_idx]);
    for(lit l:cl->literals){
        if(l.prevar_idx!=cl->watch_lit.prevar_idx||l.posvar_idx!=cl->watch_lit.posvar_idx||l.key!=cl->watch_lit.key){
            int delta=lit_delta(l);
            int safety;
            if(l.is_idl_lit){
            if(critical_score(l.prevar_idx, -delta, safety)>critical_score(l.posvar_idx, delta, safety)){
                _backward_critical_value[l.prevar_idx]=delta;
                critical_move(l.prevar_idx, 1);
            }
            else{
                _forward_critical_value[l.posvar_idx]=delta;
                critical_move(l.posvar_idx, 0);
            }
            }
            else{critical_move(l.prevar_idx, 0);}
            break;
        }
    }
}


/**********pick move***********/
//pick the  smallest critical move by BMS
int64_t bool_ls_solver::pick_critical_move(int64_t &direction){
    int best_score,score,best_var_idx,cnt,operation;
    int best_value=0;
    int best_safety=INT32_MIN;
    bool BMS=false;
    best_score=0;
    best_var_idx=-1;
    uint64_t best_last_move=UINT64_MAX;
    int        operation_idx=0;
    //determine the critical value
    for(uint64_t c:_unsat_hard_clauses){
        clause *cl=&(_clauses[c]);
        for(lit l:cl->idl_literals){
            int delta=lit_delta(l);
           if(_step>tabulist[2*l.posvar_idx]&&CClist[2*l.posvar_idx]>0){
//           if((_step>tabulist[2*l.posvar_idx]&&CCmode==-1)||(CClist[2*l.posvar_idx]>0&&CCmode>=0)){
               operation_vec[operation_idx++]=(delta)*(int)_num_vars+(int)l.posvar_idx;
           }
            if(_step>tabulist[2*l.prevar_idx+1]&&CClist[2*l.prevar_idx+1]>0){
//           if((_step>tabulist[2*l.prevar_idx+1]&&CCmode==-1)||(CClist[2*l.prevar_idx+1]>0&&CCmode>=0)){
               operation_vec[operation_idx++]=(-delta)*(int)_num_vars+(int)l.prevar_idx;
           }
        }
    }
    //go through the forward and backward move of vars, evaluate their score, pick the untabued best one
    if(operation_idx>45){BMS=true;cnt=45;}
    else{BMS=false;cnt=operation_idx;}
    for(int i=0;i<cnt;i++){
        if(BMS){
            int idx=mt()%(operation_idx-i);
            int tmp=operation_vec[operation_idx-i-1];
            operation=operation_vec[idx];
            operation_vec[idx]=tmp;
        }
        else{operation=operation_vec[i];}
//        operation=operation_vec[i];
        int var_idx,operation_direction,critical_value,safety;
        hash_opt(operation, var_idx, operation_direction, critical_value);
            score=critical_score(var_idx, critical_value,safety);
        uint64_t last_move_step=last_move[2*var_idx+(operation_direction+1)%2];
        if(score>best_score||(score==best_score&&safety>best_safety)||(score==best_score&&safety==best_safety&&last_move_step<best_last_move)){
                best_safety=safety;
                best_score=score;
                best_var_idx=var_idx;
                direction=operation_direction;
                best_last_move=last_move_step;
                best_value=critical_value;
            }
    }
    //if there is untabu decreasing move
    if(best_var_idx!=-1){
        if(best_value>0){_forward_critical_value[best_var_idx]=best_value;}
        else{_backward_critical_value[best_var_idx]=-best_value;}
        return best_var_idx;}
    //TODO:aspiration
    //choose from swap operations if there is no decreasing unsat critical
    operation_idx=0;
  for(int i=0;operation_idx<45&&i<100;i++){add_swap_operation(operation_idx);}
//    while (operation_idx<45) {add_swap_operation(operation_idx);}
    for(int i=0;i<operation_idx;i++){
        operation=operation_vec[i];
        int var_idx,operation_direction,critical_value,safety;
        hash_opt(operation, var_idx, operation_direction, critical_value);
            score=critical_score(var_idx, critical_value,safety);
//            if(score>best_score||(score==best_score&&last_move[2*var_idx+(operation_direction+1)%2]<best_last_move)){
        uint64_t last_move_step=(_vars[var_idx].is_idl)?last_move[2*var_idx+(operation_direction+1)%2]:last_move[2*var_idx];
        if(score>best_score||(score==best_score&&safety>best_safety)||(score==best_score&&safety==best_safety&&last_move_step<best_last_move)){
                best_safety=safety;
                best_score=score;
                best_var_idx=var_idx;
                direction=operation_direction;
                best_last_move=last_move_step;
                best_value=critical_value;
            }
    }
    if(best_var_idx!=-1){
        if(best_value>0){_forward_critical_value[best_var_idx]=best_value;}
        else{_backward_critical_value[best_var_idx]=-best_value;}
        return best_var_idx;}
    //update weight
    if(mt()%10000>smooth_probability){update_clause_weight_critical();}
    else {smooth_clause_weight_critical();}
    random_walk_all();
    walk_idl++;
    return best_var_idx;
}

int64_t bool_ls_solver::pick_critical_move_bool(int64_t & direction){
    int best_score,score,best_var_idx,cnt,operation;
    int best_value=0;
    int best_safety=INT32_MIN;
    bool BMS=false;
    best_score=1;
    best_var_idx=-1;
    uint64_t best_last_move=UINT64_MAX;
    int        operation_idx=0;
//    int        operation_idx_out_cc=0;
    for(uint64_t c:_unsat_hard_clauses){
        clause *cl=&(_clauses[c]);
        for(lit l:cl->bool_literals){
            if(is_chosen_bool_var[l.prevar_idx])continue;
            if(_step>tabulist[2*l.prevar_idx]&&CClist[2*l.prevar_idx]>0) {
//            if((_step>tabulist[2*l.prevar_idx]&&CCmode==-1)||(CClist[2*l.prevar_idx]>0&&CCmode>=0)) {
                operation_vec[operation_idx++]=(int)l.prevar_idx;
                is_chosen_bool_var[l.prevar_idx]=true;
            }
//            else{
//                operation_vec_bool[operation_idx_out_cc++]=(int)l.prevar_idx;
//                is_chosen_bool_var[l.prevar_idx]=true;
//            }
        }
    }
    for(int i=0;i<operation_idx;i++){is_chosen_bool_var[operation_vec[i]]=false;}// recover chosen_bool_var
//    for(int i=0;i<operation_idx_out_cc;i++){is_chosen_bool_var[operation_vec_bool[i]]=false;}
    if(operation_idx>45){BMS=true;cnt=45;}
    else{BMS=false;cnt=operation_idx;}
    for(int i=0;i<cnt;i++){
        if(BMS){
            int idx=mt()%(operation_idx-i);
            int tmp=operation_vec[operation_idx-i-1];
            operation=operation_vec[idx];
            operation_vec[idx]=tmp;
        }
        else{operation=operation_vec[i];}
//        operation=operation_vec[i];
        int var_idx,operation_direction,critical_value,safety;
        hash_opt(operation, var_idx, operation_direction, critical_value);
//            score=critical_score(var_idx, critical_value,safety);
        score=_vars[var_idx].score;
        safety=0;
        uint64_t last_move_step=last_move[2*var_idx];
        if(score>best_score||(score==best_score&&safety>best_safety)||(score==best_score&&safety==best_safety&&last_move_step<best_last_move)){
                best_safety=safety;
                best_score=score;
                best_var_idx=var_idx;
                best_last_move=last_move_step;
                best_value=critical_value;
            }
    }
    //if there is untabu decreasing move
    if(best_var_idx!=-1){return best_var_idx;}
//    //choose one from the out_cc
//    best_score=(int)total_clause_weight/_num_clauses;
//    if(operation_idx_out_cc>45){BMS=true;cnt=45;}
//    else{BMS=false;cnt=operation_idx_out_cc;}
//    for(int i=0;i<cnt;i++){
//        if(BMS){
//            int idx=mt()%(operation_idx_out_cc-i);
//            int tmp=operation_vec_bool[operation_idx_out_cc-i-1];
//            operation=operation_vec_bool[idx];
//            operation_vec_bool[idx]=tmp;
//        }
//        else{operation=operation_vec_bool[i];}
//        int var_idx,operation_direction,critical_value,safety;
//        hash_opt(operation, var_idx, operation_direction, critical_value);
//            score=critical_score(var_idx, critical_value,safety);
//        uint64_t last_move_step=last_move[2*var_idx];
//        if(score>best_score||(score==best_score&&safety>best_safety)||(score==best_score&&safety==best_safety&&last_move_step<best_last_move)){
//            best_safety=safety;
//            best_score=score;
//            best_var_idx=var_idx;
//            best_last_move=last_move_step;
//        }
//    }
//    if(best_var_idx!=-1){return  best_var_idx;}
    //update weight
    if(mt()%10000>smooth_probability){update_clause_weight_critical();}
    else {smooth_clause_weight_critical();}
    random_walk_all();
    walk_bool++;
    return best_var_idx;
}

void bool_ls_solver::hash_opt(int operation,int &var_idx,int &operation_direction,int &critical_value){
    if(operation>0){
        var_idx=operation%(int)_num_vars;
        operation_direction=0;
        critical_value=operation/(int)_num_vars;
    }
    else{
        operation_direction=1;
        var_idx=(operation%(int)_num_vars+(int)_num_vars);
        if(var_idx==(int)_num_vars)var_idx=0;
        critical_value=(operation-var_idx)/(int)_num_vars;
    }
}
//a bool var with score>0 is from a falsified clause, no need to select from sat_num_one_clause, so the swap operation is dedicated for idl var
void bool_ls_solver::add_swap_operation(int &operation_idx){
    int c=sat_num_one_clauses->element_at(mt()%sat_num_one_clauses->size());
    clause *cl=&(_clauses[c]);
    for(lit l:cl->idl_literals){
        if(l.prevar_idx!=cl->watch_lit.prevar_idx||l.posvar_idx!=cl->watch_lit.posvar_idx||l.key!=cl->watch_lit.key){
            int delta=lit_delta(l);
            operation_vec[operation_idx++]=(delta)*(int)_num_vars+(int)l.posvar_idx;
            operation_vec[operation_idx++]=(-delta)*(int)_num_vars+(int)l.prevar_idx;
        }
    }
}

/**********random walk***********/
void bool_ls_solver::random_walk_all(){
    uint64_t c;
    uint64_t best_operation_idx_idl,best_operation_idx_bool;
    //best is the best operation of all, second is the best of non-last-true
    best_operation_idx_idl=best_operation_idx_bool=0;
    uint64_t        operation_idx_idl=0;
    uint64_t        operation_idx_bool=0;
    for(int i=0;i<3&&operation_idx_idl+operation_idx_bool<5;i++){
        c=_unsat_hard_clauses[mt()%_unsat_hard_clauses.size()];
        clause *cp=&(_clauses[c]);
        for(lit l:cp->idl_literals){
            int delta=lit_delta(l);
            operation_vec_idl[operation_idx_idl++]=(-delta)*(int)_num_vars+(int)l.prevar_idx;
            operation_vec_idl[operation_idx_idl++]=(delta)*(int)_num_vars+(int)l.posvar_idx;
        }
        for(lit l:cp->bool_literals){
            if(is_chosen_bool_var[l.prevar_idx]){continue;}
            operation_vec_bool[operation_idx_bool++]=(int)l.prevar_idx;
            is_chosen_bool_var[l.prevar_idx]=true;
        }
    }
    for(int i=0;i<operation_idx_bool;i++){is_chosen_bool_var[operation_vec_bool[i]]=false;}
    int subscore,score,var_idx,operation_direction,critical_value,safety_bool;
    int best_subscore_idl=INT32_MAX;
    int best_score_bool=INT32_MIN;
    int best_safety_bool=INT32_MIN;
    uint64_t best_last_move_idl=UINT64_MAX;
    uint64_t best_last_move_bool=UINT64_MAX;
    for(uint64_t i=0;i<operation_idx_idl;i++){
        hash_opt(operation_vec_idl[i], var_idx, operation_direction, critical_value);
        subscore=critical_subscore(var_idx, critical_value);
        uint64_t last_move_step=last_move[2*var_idx+(operation_direction+1)%2];
        if(subscore<best_subscore_idl||(subscore==best_subscore_idl&&last_move_step<best_last_move_idl)){
            best_subscore_idl=subscore;
            best_last_move_idl=last_move_step;
            best_operation_idx_idl=i;
        }
    }
    for(uint64_t i=0;i<operation_idx_bool;i++){
        hash_opt(operation_vec_idl[i], var_idx, operation_direction, critical_value);
//        score=critical_score(var_idx, critical_value, safety_bool);
        score=_vars[var_idx].score;
        safety_bool=0;
        uint64_t last_move_step=last_move[2*var_idx];
        if(score>best_score_bool||(score==best_score_bool&&safety_bool>best_safety_bool)||(score==best_score_bool&&safety_bool==best_safety_bool&&last_move_step<best_last_move_bool)){
            best_score_bool=score;
            best_safety_bool=safety_bool;
            best_last_move_bool=last_move_step;
            best_operation_idx_bool=i;
        }
    }
    if(operation_idx_bool==0||(operation_idx_idl>0&&operation_idx_bool>0&&mt()%_num_vars<_num_idl_vars)){
        hash_opt(operation_vec_idl[best_operation_idx_idl], var_idx, operation_direction, critical_value);
        if(critical_value>0){_forward_critical_value[var_idx]=critical_value;}
        else{_backward_critical_value[var_idx]=-critical_value;}
    }
    else{
        hash_opt(operation_vec_bool[best_operation_idx_bool], var_idx, operation_direction, critical_value);
    }
    critical_move(var_idx, operation_direction);
}
/**********update solution***********/
bool bool_ls_solver::update_best_solutioin(){
    bool improve=false;
    if(_unsat_hard_clauses.size()<_best_found_hard_cost_this_restart){
        improve=true;
        _best_found_hard_cost_this_restart=_unsat_hard_clauses.size();
//        cout<<"best_found_hard_cost_this_turn:"<<_best_found_hard_cost_this_restart<<endl;
    }
    if((_unsat_hard_clauses.size()<_best_found_hard_cost)||(_unsat_hard_clauses.size()==0&&_unsat_soft_clauses.size()<_best_found_soft_cost)){
        improve=true;
        _best_cost_time=TimeElapsed();
        _best_found_hard_cost=_unsat_hard_clauses.size();
//        cout<<"best_found_hard_cost"<<_best_found_hard_cost<<endl<<"best_found_soft_cost:"<<_best_found_soft_cost<<" best_step:"<<_step<<" time"<<_best_cost_time<<endl<<endl;
        _best_solution=_solution;
    }
    if(_unsat_hard_clauses.size()==0&&_unsat_soft_clauses.size()<_best_found_soft_cost){
        _best_found_soft_cost=_unsat_soft_clauses.size();
    }
    return improve;
}

bool bool_ls_solver::local_search(){
    int64_t flipv;
    int64_t direction;//0 means moving forward while 1 means moving backward
    uint64_t no_improve_cnt=0;
    start = chrono::steady_clock::now();
    initialize();
    for(_step=1;_step<_max_step;_step++){
        if(0==_unsat_hard_clauses.size()){return true;}
        if(_step%1000==0&&(TimeElapsed()>_cutoff)){break;}
        if(no_improve_cnt>500000){initialize();no_improve_cnt=0;}
        if(mt()%100<99||sat_num_one_clauses->size()==0){//only when 1% probabilty and |sat_num_one_clauses| is more than 1, do the swap from small weight
//        if(mt()%100<99){
            if(mt()%_lit_in_unsast_clause_num<_bool_lit_in_unsat_clause_num){flipv=pick_critical_move_bool(direction);}
            else{flipv=pick_critical_move(direction);}
        if(flipv!=-1){
            if(_vars[flipv].is_idl){pick_idl++;}
            else{pick_bool++;}
            critical_move(flipv, direction);}
        }
        else{swap_from_small_weight_clause();}
        if(update_best_solutioin()) no_improve_cnt=0;
        else                        no_improve_cnt++;
    }
    return false;
}

double bool_ls_solver::TimeElapsed(){
    chrono::steady_clock::time_point finish = chrono::steady_clock::now();
    chrono::duration<double> duration = finish - start;
    return duration.count();
}

void bool_ls_solver::print_solution(bool detailed){
    if(detailed){
        up_bool_vars();
        for(int i=0;i<_resolution_vars.size();i++){
            cout<<"(define-fun "<<_resolution_vars[i].var_name<<" () ";
            if(_resolution_vars[i].is_idl){
                if(sym2var.find(i)==sym2var.end())cout<<"Int\n0)\n";
                else{cout<<"Int\n"<<_best_solution[sym2var[i]]<<")\n";}
            }
            else{
                if(sym2bool_var.find(i)==sym2bool_var.end()){
                    cout<<"Bool\n";
                    cout<<(_resolution_vars[i].up_bool>0?"true":"false")<<")\n";
                }
                else{cout<<"Bool\n"<<(_best_solution[sym2bool_var[i]]>0?"true":"false")<<")\n";}
            }
        }
    }
    else{
        cout<<_best_found_hard_cost<<endl<<_best_cost_time<<endl;
    }
}


/**********clause weighting***********/
void bool_ls_solver::update_clause_weight(){
    clause *cp;
    for(uint64_t c:_unsat_soft_clauses){
        cp=&(_clauses[c]);
        if(cp->weight>softclause_weight_threshold)
            continue;
        cp->weight++;
    }
    for(uint64_t c:_unsat_hard_clauses){
        cp=&(_clauses[c]);
        cp->weight+=h_inc;
    }
    total_clause_weight+=_unsat_soft_clauses.size();
    total_clause_weight+=h_inc*_unsat_hard_clauses.size();
    if(total_clause_weight>_swt_threshold*_num_clauses)
        smooth_clause_weight();
}

//only add clause weight
void bool_ls_solver::update_clause_weight_critical(){
    clause *cp;
    for(uint64_t c:_unsat_soft_clauses){
        cp=&(_clauses[c]);
        if(cp->weight>softclause_weight_threshold)
            continue;
        cp->weight++;
    }
    for(uint64_t c:_unsat_hard_clauses){
        cp=&(_clauses[c]);
        cp->weight+=h_inc;
        for(lit &l:cp->bool_literals){_vars[l.prevar_idx].score+=h_inc;}
    }
    total_clause_weight+=_unsat_soft_clauses.size();
    total_clause_weight+=h_inc*_unsat_hard_clauses.size();
}

void bool_ls_solver::smooth_clause_weight(){
    clause *cp;
    uint64_t scale_ave_weight=total_clause_weight/_num_clauses*(1-_swt_p);
    total_clause_weight=0;
    for(uint64_t c=0;c<_num_clauses;c++){
        cp=&(_clauses[c]);
        cp->weight=cp->weight*_swt_p+scale_ave_weight;
        if(cp->weight<1){cp->weight=1;}
        total_clause_weight+=cp->weight;
    }
}


//only minus the weight of clauses, score and subscore are not updated
void bool_ls_solver::smooth_clause_weight_critical(){
    clause *cp;
    int weight_delta;
    for(uint64_t c=0;c<_num_clauses;c++){
       if(_clauses[c].weight>1&&_index_in_unsat_hard_clauses[c]==-1&&_index_in_unsat_soft_clauses[c]==-1){
            cp=&(_clauses[c]);
            weight_delta=(cp->is_hard)?h_inc:1;
            cp->weight-=weight_delta;
            total_clause_weight-=weight_delta;
           if(cp->sat_count==1&&!cp->watch_lit.is_idl_lit){_vars[cp->watch_lit.prevar_idx].score+=weight_delta;}
        }
    }
}
int64_t bool_ls_solver::get_cost(){
    if(_unsat_hard_clauses.size()==0)
        return _unsat_soft_clauses.size();
    else
        return -1;
}


void bool_ls_solver::transfer_smt2(){
    cout<<"(set-logic QF_IDL)\n";
    for(uint64_t i=0;i<_num_vars;i++){
        cout<<"(declare-fun "<<_vars[i].var_name<<" () Int)"<<endl;
    }
    for(uint64_t i=0;i<_num_clauses;i++){
        cout<<"(assert-soft ";
        cout<<"(or ";
        for(lit l:_clauses[i].literals){
            uint64_t pre=l.prevar_idx;
            uint64_t pos=l.posvar_idx;
            int64_t  key=l.key;
            cout<<"(<= (- "<<_vars[pre].var_name<<" "<<_vars[pos].var_name<<") ";
            if(key<0){
                cout<<"(- "<<-key<<")";
            }
            else
                cout<<key;
            cout<<") ";
        }
        cout<<") :weight 1 :id goal)\n";
    }
    cout<<"(minimize goal)\n(check-sat)\n(get-objectives)\n(exit)\n";
}
/********checker*********/
bool bool_ls_solver::check_solution(){
    clause *cp;
    uint64_t unsat_hard_num=0;
    uint64_t unsat_soft_num=0;
    for(uint64_t i=0;i<_num_clauses;i++){
        bool unsat_flag=false;
        uint64_t sat_count=0;
        cp=&(_clauses[i]);
        for(lit l: cp->literals){
            int preval=_solution[l.prevar_idx];
            int posval=_solution[l.posvar_idx];
            if((l.is_idl_lit&&preval-posval<=l.key)||(!l.is_idl_lit&&preval*l.key>0)){
                unsat_flag=true;
                sat_count++;
            }
        }
        if(sat_count!=_clauses[i].sat_count){
            cout<<"sat_count wrong!"<<endl;
        }
        if(!unsat_flag){
            if(cp->is_hard) unsat_hard_num++;
            else unsat_soft_num++;
        }
    }
    if(unsat_hard_num==_unsat_hard_clauses.size())
        cout<<"right solution\n";
    else
        cout<<"wrong solution\n";
    return unsat_hard_num==_unsat_hard_clauses.size();
}

bool bool_ls_solver::check_best_solution(){
    clause *cp;
    uint64_t unsat_hard_num=0;
    uint64_t unsat_soft_num=0;
    for(uint64_t i=0;i<_num_clauses;i++){
        bool unsat_flag=false;
        uint64_t sat_count=0;
        cp=&(_clauses[i]);
        for(lit l: cp->literals){
            int preval=_best_solution[l.prevar_idx];
            if(l.is_idl_lit){
            int posval=_best_solution[l.posvar_idx];
            if(preval-posval<=l.key){
                unsat_flag=true;
                sat_count++;
            }
            }
            else if((preval>0&&l.key>0)||(preval<0&&l.key<0)){
                unsat_flag=true;
                sat_count++;
            }
        }

        if(!unsat_flag){
            if(cp->is_hard) unsat_hard_num++;
            else unsat_soft_num++;
        }
    }
    if(unsat_hard_num==_best_found_hard_cost)
        cout<<"right solution\n";
    else
        cout<<"wrong solution\n";
    return unsat_hard_num==_best_found_hard_cost;
}

void test(bool_ls_solver& ls){
    return;
}

void sigalarm_handler(int){printf("unknown\n");exit(0);}
int main(int argc, char *argv[]) {
    signal(SIGALRM, sigalarm_handler);
    signal(SIGINT,sigalarm_handler);
    bool_ls_solver toyidl;
    toyidl.parse_arguments(argc, argv);
    alarm(toyidl._cutoff);
    toyidl.mt.seed(toyidl._random_seed);
    srand(toyidl._random_seed);
    string cmd="./yices-smt2 --timeout=";
    if(!toyidl.build_instance(toyidl._inst_file)||toyidl._num_vars==0){
        system((cmd+"1200 "+toyidl._inst_file).data());
        return 1;
    }
    if(toyidl.is_validation){
        if(toyidl._num_clauses>0){toyidl.local_search();}
        if(toyidl._best_found_hard_cost==0){cout<<"sat\n";
            toyidl.print_solution(true);
            return 0;}
    }
    FILE *fp;
    fp=popen((cmd+"100 "+toyidl._inst_file).data(), "r");//100s yices
    char res[50]="unknown\n";
    fgets(res, 50, fp);
    if(strcmp(res, "unknown\n")){
        printf("%s", res);
        while (fgets(res,50,fp)!= NULL)cout<<res;
        return 0;
    }
    toyidl._cutoff-=700;
    if(toyidl._num_clauses>0){toyidl.local_search();}
    if(toyidl._best_found_hard_cost==0){cout<<"sat\n";return 0;}
    system((cmd+"600 "+toyidl._inst_file).data());
//    toyidl.print_formula();
  return 0;
}
