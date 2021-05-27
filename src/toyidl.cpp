//
//  toyidl.cpp
//  parser
//
//  Created by DouglasLee on 2020/9/24.
//  Copyright © 2020 DouglasLee. All rights reserved.
//

#include "toyidl.hpp"
#include <fstream>
#include <iostream>
#include <algorithm>
using namespace TOYIDL;

ls_solver::ls_solver(){
    _additional_len=10;
    _max_tries=1;
    _max_step=UINT64_MAX;
    _swt_p=0.7;
    _swt_threshold=50;
    smooth_probability=3;
}

/***parse parameters*****************/
bool     ls_solver::parse_arguments(int argc, char ** argv)
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
    }
    if (flag_inst) return true;
    else return false;
}

uint64_t ls_solver::transfer_sym_to_var(int64_t sym){
    if(sym2var.find(sym)==sym2var.end()){
        sym2var[sym]=_vars.size();
        variable var;
        var.is_idl=true;
        var.var_name=syntaxTree::symbol_table.str(sym);
        _vars.push_back(var);
        idl_var_vec.push_back(_vars.size()-1);
        return _vars.size()-1;
    }
    else return sym2var[sym];
}

uint64_t ls_solver::transfer_sym_to_bool_var(int sym){
    int sym_abs=abs(sym);
    if(sym2bool_var.find(sym_abs)==sym2bool_var.end()){
        sym2bool_var[sym_abs]=_vars.size();
        variable var;
        var.is_idl=false;
//        var.var_name=to_string(sym_abs);
        var.var_name=syntaxTree::symbol_table.str(sym_abs);
        _vars.push_back(var);
        bool_var_vec.push_back(_vars.size()-1);
        return _vars.size()-1;
    }
    else return sym2bool_var[sym_abs];
}

void ls_solver::make_space(){
    _solution.resize(_num_vars+_additional_len);
    _best_solution.resize(_num_vars+_additional_len);
    _index_in_unsat_hard_clauses.resize(_num_clauses+_additional_len,-1);
    _index_in_unsat_soft_clauses.resize(_num_clauses+_additional_len,-1);
    exist_time.resize(_num_vars);
    tabulist.resize(2*_num_vars+_additional_len);
    CClist.resize(2*_num_vars+_additional_len);
    _forward_critical_value.resize(_num_vars+_additional_len);
    _backward_critical_value.resize(_num_vars+_additional_len);
    _forward_critical_set.resize(_num_vars+_additional_len);
    _backward_critical_set.resize(_num_vars+_additional_len);
    operation_vec.resize(_num_lits*2+_additional_len);
    operation_is_last_true_vec.resize(_num_lits*2+_additional_len);
    var_is_assigned.resize(_num_vars);
    unsat_clause_with_assigned_var=new Array((int)_num_clauses);
    construct_unsat.resize(_num_clauses);
    last_move.resize(_num_vars*2+_additional_len);
    sat_num_one_clauses=new Array((int)_num_clauses);
}


/// build neighbor_var_idxs for each var
void ls_solver::build_neighbor_clausenum(){
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

void ls_solver::build_instance(string inst){
    parse_file(inst);
    Skeleton skeleton;
    _average_k_value=0;
    _num_lits=0;
    int num_idl_lit=0;
    h_inc=1;
    softclause_weight_threshold=1;
    skeleton.transform(ast, ast.root_index());
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
            curlit.clause_idx=last_clause_index;
            _vars[pre].literals.push_back(curlit);
            _vars[pos].literals.push_back(curlit);
            }
            else if(l.true_false==0){
                curlit.is_idl_lit=false;
                uint64_t bool_var_idx=transfer_sym_to_bool_var(l.k);
                curlit.prevar_idx=bool_var_idx;
                curlit.key=l.k;
                curlit.clause_idx=last_clause_index;
                _vars[bool_var_idx].literals.push_back(curlit);
            }
            else if(l.true_false==-1){continue;}// if there exists a false in a clause, pass it
            else if(l.true_false==1){exist_true=true;break;}//if there exists a true in a clause, the clause should not be added
            cur_clause.literals.push_back(curlit);
            cur_clause.is_hard=true;
            cur_clause.weight=1;
        }
        if(!exist_true){_clauses.push_back(cur_clause);}
        if(cur_clause.literals.size()>_max_lit_num_in_clause){_max_lit_num_in_clause=cur_clause.literals.size();}
    }
    if(sym2var.find(0)!=sym2var.end()){fix_0_var_idx=sym2var[0];}
    _num_clauses=_clauses.size();
    _num_vars=_vars.size();
    total_clause_weight=_num_clauses;
    make_space();
    build_neighbor_clausenum();
    _average_k_value/=num_idl_lit;
    if(_average_k_value<1)_average_k_value=1;
    _best_found_hard_cost=_num_clauses;
    _best_found_soft_cost=0;
}

void ls_solver::print_formula(){
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

void ls_solver::clear_prev_data(){
    
}

/************initialization**************/

void ls_solver::initialize_variable_datas(){
    
    //last move step
    for(uint64_t i=0;i<_num_vars;i++){last_move[2*i]=last_move[2*i+1]=0;}
    //tabulist
    if(CCmode==-1){for(uint64_t i=0;i<_num_vars;i++){tabulist[2*i]=tabulist[2*i+1]=0;}}
    //CClist
    else{for (uint64_t i=0;i<_num_vars;i++){CClist[2*i]=CClist[2*i+1]=1;}}
}

void ls_solver::initialize_clause_datas(){
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
        if(_clauses[c].sat_count==0){unsat_a_clause(c);}
        else{sat_a_clause(c);}
        if(_clauses[c].sat_count==1){sat_num_one_clauses->insert_element((int)c);}
        else{sat_num_one_clauses->delete_element((int)c);}
    }
    total_clause_weight=_num_clauses;
}

void ls_solver::initialize(){
    clear_prev_data();
    construct_slution_score();
    initialize_clause_datas();
    initialize_variable_datas();
    _best_found_hard_cost_this_restart=_unsat_hard_clauses.size();
    update_best_solutioin();
}

/**********restart construction***********/


void ls_solver::construct_slution_score(){
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

uint64_t ls_solver::pick_construct_idx(int &best_value){
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

int ls_solver::construct_score(int var_idx, int value){
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
void ls_solver::construct_move(int var_idx, int value){
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
void ls_solver::unsat_a_clause(uint64_t the_clause){
    if(_clauses[the_clause].is_hard==true&&_index_in_unsat_hard_clauses[the_clause]==-1){
        _index_in_unsat_hard_clauses[the_clause]=_unsat_hard_clauses.size();
        _unsat_hard_clauses.push_back(the_clause);
    }
    else if(_clauses[the_clause].is_hard==false&&_index_in_unsat_soft_clauses[the_clause]==-1){
        _index_in_unsat_soft_clauses[the_clause]=_unsat_soft_clauses.size();
        _unsat_soft_clauses.push_back(the_clause);
    }
}

void ls_solver::sat_a_clause(uint64_t the_clause){
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
int ls_solver::lit_delta(lit& l){
    if(l.is_idl_lit)
    return _solution[l.prevar_idx]-_solution[l.posvar_idx]-l.key;
    else{
        if((_solution[l.prevar_idx]>0&&l.key>0)||(_solution[l.prevar_idx]<0&&l.key<0))return 0;
        else return 1;// 1 or average_k
    }
}

int ls_solver::calculate_cscore(int score, int subscore){
    return score-subscore/_average_k_value;
}

/**********modify the CClist***********/
void ls_solver::modifyCC(uint64_t var_idx, uint64_t direction){
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

void ls_solver::critical_score_subscore(uint64_t var_idx,int change_value){
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
            if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) {cp->last_true_lit=cp->watch_lit;unsat_a_clause(l.clause_idx);}
            else if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) {sat_a_clause(l.clause_idx);}
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
            if(cp->sat_count>0&&cp->sat_count+make_break_in_clause==0) {cp->last_true_lit=cp->watch_lit;unsat_a_clause(l.clause_idx);}
            else if(cp->sat_count==0&&cp->sat_count+make_break_in_clause>0) {sat_a_clause(l.clause_idx);}
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
        }
    }
}
int ls_solver::critical_score(uint64_t var_idx, int change_value,int &safety){
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

int ls_solver::critical_subscore(uint64_t var_idx,int change_value){
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

void ls_solver::critical_move(uint64_t var_idx,uint64_t direction){
    if(_vars[var_idx].is_idl){
        int change_value=(direction==0)?(_forward_critical_value[var_idx]):(-_backward_critical_value[var_idx]);
        critical_score_subscore(var_idx, change_value);
        _solution[var_idx]+=change_value;
    }
    else{
        critical_score_subscore(var_idx, 0);
        _solution[var_idx]*=-1;
    }
    //step
    if(_vars[var_idx].is_idl){
        if(CCmode==-1){
            last_move[2*var_idx+direction]=_step;
            tabulist[var_idx*2+(direction+1)%2]=_step+3+mt()%10;
        }
        else{modifyCC(var_idx,direction);}
    }
    else{
        if(CCmode==-1){
            last_move[2*var_idx]=_step;
            tabulist[var_idx*2]=_step+3+mt()%10;
        }
        else{modifyCC(var_idx, direction);}
    }
}
void ls_solver::swap_from_small_weight_clause(){
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
int64_t ls_solver::pick_critical_move(int64_t &direction){
    int best_score,score,best_var_idx,cnt,operation;
    int best_value=0;
    int best_safety=INT32_MIN;
    bool BMS=false;
    best_score=0;
    best_var_idx=-1;
    uint64_t best_last_move=UINT64_MAX;
    fill(_forward_critical_set.begin(),_forward_critical_set.end(),0);
    fill(_backward_critical_set.begin(),_backward_critical_set.end(),0);
    int        operation_idx=0;
    //determine the critical value
    for(uint64_t c:_unsat_hard_clauses){
        clause *cl=&(_clauses[c]);
        for(lit l:cl->literals){
            if(l.is_idl_lit){
            int delta=lit_delta(l);
           if((_step>tabulist[2*l.posvar_idx]&&CCmode==-1)||(CClist[2*l.posvar_idx]>0&&CCmode>=0)){
               operation_vec[operation_idx++]=(delta)*(int)_num_vars+(int)l.posvar_idx;
           }
           if((_step>tabulist[2*l.prevar_idx+1]&&CCmode==-1)||(CClist[2*l.prevar_idx+1]>0&&CCmode>=0)){
               operation_vec[operation_idx++]=(-delta)*(int)_num_vars+(int)l.prevar_idx;
           }
            }
            else if((_step>tabulist[2*l.prevar_idx]&&CCmode==-1)||(CClist[2*l.prevar_idx]>0&&CCmode>=0)) {operation_vec[operation_idx++]=(int)l.prevar_idx;}
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
    return best_var_idx;
}

void ls_solver::hash_opt(int operation,int &var_idx,int &operation_direction,int &critical_value){
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

void ls_solver::add_swap_operation(int &operation_idx){
    int c=sat_num_one_clauses->element_at(mt()%sat_num_one_clauses->size());
    clause *cl=&(_clauses[c]);
    for(lit l:cl->literals){
        if(l.prevar_idx!=cl->watch_lit.prevar_idx||l.posvar_idx!=cl->watch_lit.posvar_idx||l.key!=cl->watch_lit.key){
            if(l.is_idl_lit){
            int delta=lit_delta(l);
            operation_vec[operation_idx++]=(delta)*(int)_num_vars+(int)l.posvar_idx;
            operation_vec[operation_idx++]=(-delta)*(int)_num_vars+(int)l.prevar_idx;
            }
            else{operation_vec[operation_idx++]=(int)l.prevar_idx;}
        }
    }
}

/**********random walk***********/
void ls_solver::random_walk_all(){
    uint64_t c;
    uint64_t best_operation_idx,second_operation_idx;
    //best is the best operation of all, second is the best of non-last-true
    best_operation_idx=second_operation_idx=0;
    uint64_t        operation_idx=0;
    while(operation_idx<5){
        c=_unsat_hard_clauses[mt()%_unsat_hard_clauses.size()];
    clause *cp=&(_clauses[c]);
    for(lit l:cp->literals){
        if(l.is_idl_lit){
        int delta=lit_delta(l);
        int opt_pre=(-delta)*(int)_num_vars+(int)l.prevar_idx;
        int opt_pos=(delta)*(int)_num_vars+(int)l.posvar_idx;
        bool is_last_true=(l.prevar_idx==cp->last_true_lit.prevar_idx&&l.posvar_idx==cp->last_true_lit.posvar_idx&&l.key==cp->last_true_lit.key);
        operation_is_last_true_vec[operation_idx]=is_last_true;
        operation_vec[operation_idx++]=opt_pre;
        operation_is_last_true_vec[operation_idx]=is_last_true;
        operation_vec[operation_idx++]=opt_pos;
        }
        else{
            operation_is_last_true_vec[operation_idx]=(l.prevar_idx==cp->last_true_lit.prevar_idx&&l.posvar_idx==cp->last_true_lit.posvar_idx&&l.key==cp->last_true_lit.key);
            operation_vec[operation_idx]=(int)l.prevar_idx;
        }
    }
    }
    int subscore,second_subscore,best_subscore,var_idx,operation_direction,critical_value;
    best_subscore=INT32_MAX;
    second_subscore=INT32_MAX;
    uint64_t best_last_move=UINT64_MAX;
    uint64_t second_last_move=UINT64_MAX;
    for(uint64_t i=0;i<operation_idx;i++){
        hash_opt(operation_vec[i], var_idx, operation_direction, critical_value);
        subscore=critical_subscore(var_idx, critical_value);
        uint64_t last_move_step=(_vars[var_idx].is_idl)?last_move[2*var_idx+(operation_direction+1)%2]:last_move[2*var_idx];
        if(subscore<best_subscore||(subscore==best_subscore&&last_move_step<best_last_move)){
            best_subscore=subscore;
            best_last_move=last_move_step;
            best_operation_idx=i;
        }
        if(!operation_is_last_true_vec[i]&&(subscore<second_subscore||(subscore==second_subscore&&last_move_step<second_last_move))){
            second_subscore=subscore;
            second_last_move=last_move_step;
            second_operation_idx=i;
        }
    }
    if(!operation_is_last_true_vec[best_operation_idx]||(operation_is_last_true_vec[best_operation_idx]&&mt()%100>0)){
        hash_opt(operation_vec[best_operation_idx], var_idx, operation_direction, critical_value);
    }
    else{hash_opt(operation_vec[second_operation_idx], var_idx, operation_direction, critical_value);}
    if(critical_value>0){_forward_critical_value[var_idx]=critical_value;}
    else{_backward_critical_value[var_idx]=-critical_value;}
    critical_move(var_idx, operation_direction);
}
/**********update solution***********/
bool ls_solver::update_best_solutioin(){
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

bool ls_solver::local_search(){
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
        flipv=pick_critical_move(direction);
        if(flipv!=-1){critical_move(flipv, direction);}
        }
        else{swap_from_small_weight_clause();}
        if(update_best_solutioin()) no_improve_cnt=0;
        else                        no_improve_cnt++;
    }
    return false;
}

double ls_solver::TimeElapsed(){
    chrono::steady_clock::time_point finish = chrono::steady_clock::now();
    chrono::duration<double> duration = finish - start;
    return duration.count();
}

void ls_solver::print_solution(bool detailed){
    if(detailed){
        for(uint64_t i=0;i<_num_vars;i++){
            cout<<_vars[i].var_name<<' '<<_solution[i]<<endl;
        }
        cout<<"min_unsat_hard:"<<_best_found_hard_cost<<"min_unsat_soft: "<<_best_found_soft_cost<<" time:"<<_best_cost_time<<endl;
    }
    else{
        cout<<_best_found_hard_cost<<endl<<_best_cost_time<<endl;
    }
}


/**********clause weighting***********/
void ls_solver::update_clause_weight(){
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
void ls_solver::update_clause_weight_critical(){
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
}

void ls_solver::smooth_clause_weight(){
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
void ls_solver::smooth_clause_weight_critical(){
    clause *cp;
    int weight_delta;
    for(uint64_t c=0;c<_num_clauses;c++){
       if(_clauses[c].weight>1&&_index_in_unsat_hard_clauses[c]==-1&&_index_in_unsat_soft_clauses[c]==-1){
            cp=&(_clauses[c]);
            weight_delta=(cp->is_hard)?h_inc:1;
            cp->weight-=weight_delta;
            total_clause_weight-=weight_delta;
        }
    }
}
int64_t ls_solver::get_cost(){
    if(_unsat_hard_clauses.size()==0)
        return _unsat_soft_clauses.size();
    else
        return -1;
}


void ls_solver::transfer_smt2(){
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
bool ls_solver::check_solution(){
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
            if(preval-posval<=l.key){
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

bool ls_solver::check_best_solution(){
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

void test(ls_solver& ls){
    return;
}

int main1(int argc, char *argv[]) {
    ls_solver toyidl;
    toyidl.parse_arguments(argc, argv);
    toyidl.mt.seed(toyidl._random_seed);
    srand(toyidl._random_seed);
    toyidl.build_instance(toyidl._inst_file);
//    toyidl.transfer_smt2();
//    toyidl.print_formula();
//    toyidl.initialize();
//    cout<<toyidl._num_vars<<' '<<toyidl._num_clauses<<endl;
//    test(toyidl);
    toyidl.local_search();
    toyidl.print_solution(false);
    toyidl.check_best_solution();
//    toyidl.print_formula();
  return 0;
}
