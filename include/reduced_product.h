#pragma once
#include "invariant.h"
#include "rp/reduced_product.hpp"
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>

namespace invfinder {
// Native Z3 adapter for the range/flat reduced-product synthesis core.
// The original Z3 context must outlive this object and all returned expressions.
class ReducedProductInvariant {
    transitionSystem trans_;
    rp::Problem problem_;
    std::vector<z3::expr> ranges_, flats_;
    z3::expr_vector rename_from_, rename_to_;
    bool ran_ = false;
    rp::Result result_;

    std::string serialize(z3::expr e) const {
        return e.substitute(rename_from_, rename_to_).to_string();
    }
    z3::expr prime(z3::expr e) const {
        return e.substitute(trans_.get_ori_consts(), trans_.get_bar_consts());
    }
    void add(const std::string& label, const z3::expr& e, bool flat) {
        if(ran_) throw std::logic_error("Cannot add rows after synthesis");
        if(!e.is_bv() || &e.ctx()!=&trans_.ctx)
            throw std::invalid_argument("Rows must be BV expressions in the transition context");
        rp::Row row{label,e.get_sort().bv_size(),serialize(e),serialize(prime(e))};
        (flat?problem_.flats:problem_.ranges).push_back(std::move(row));
        (flat?flats_:ranges_).push_back(e);
    }
public:
    explicit ReducedProductInvariant(transitionSystem trans)
        :trans_(std::move(trans)),rename_from_(trans_.ctx),rename_to_(trans_.ctx) {
        for(std::size_t i=0;i<trans_.vars.size();++i){
            const unsigned w=trans_.vars[i].get_sort().bv_size();
            const std::string x="rp_state_x"+std::to_string(i),xp="rp_state_n"+std::to_string(i);
            problem_.variables.push_back({x,xp,w});
            rename_from_.push_back(trans_.vars[i]);rename_to_.push_back(trans_.ctx.bv_const(x.c_str(),w));
            rename_from_.push_back(trans_.vars_bar[i]);rename_to_.push_back(trans_.ctx.bv_const(xp.c_str(),w));
        }
        problem_.pre=serialize(trans_.pre);problem_.transition=serialize(trans_.trans);
    }
    void add_range(const std::string& label,const z3::expr& row){add(label,row,false);}
    void add_flat(const std::string& label,const z3::expr& row){add(label,row,true);}

    // Reuse existing InvFinder row construction for interval/zones/octagon/polyhedra.
    // New flat factors have true flat-constant semantics, unlike interval bounds on
    // a remainder expression. Selecting several components preserves their conjunction.
    void add_domain(const std::string& domain){
        if(ran_) throw std::logic_error("Cannot add domains after synthesis");
        if(domain=="knownbits"){
            for(std::size_t i=0;i<trans_.vars.size();++i)
                for(unsigned b=0;b<trans_.vars[i].get_sort().bv_size();++b)
                    add_flat("knownbits_"+std::to_string(i)+"_"+std::to_string(b),trans_.vars[i].extract(b,b));
        }else if(domain=="signed"){
            for(std::size_t i=0;i<trans_.vars.size();++i){
                const auto& x=trans_.vars[i];unsigned w=x.get_sort().bv_size();
                rp::Integer sign=rp::Integer(1)<<(w-1);
                auto mask=trans_.ctx.bv_val(sign.convert_to<std::string>().c_str(),w);
                add_range("signed_"+std::to_string(i),x^mask);
            }
        }else if(domain.rfind("congruence:",0)==0){
            const auto digits=domain.substr(11);
            if(digits.empty() || digits.find_first_not_of("0123456789")!=std::string::npos)
                throw std::invalid_argument("Congruence modulus must be a decimal integer");
            rp::Integer m=0;
            for(char digit:digits) m=m*10+(digit-'0');
            if(m<2)throw std::invalid_argument("Congruence modulus must be >= 2");
            for(std::size_t i=0;i<trans_.vars.size();++i){
                const auto& x=trans_.vars[i];unsigned w=x.get_sort().bv_size();
                if(m>=(rp::Integer(1)<<w))throw std::invalid_argument("Modulus must fit the variable width");
                add_flat(domain+"_"+std::to_string(i),z3::urem(x,trans_.ctx.bv_val(m.convert_to<std::string>().c_str(),w)));
            }
        }else{
            UBVInvariant original(trans_,domain);
            for(std::size_t i=0;i<original.var.size();++i)
                add_range(domain+"_"+std::to_string(i),original.var[i]);
        }
    }
    void add_product(const std::string& product){
        if(product.empty() || product.back()=='+')
            throw std::invalid_argument("Empty product component");
        std::stringstream in(product);std::string domain;std::set<std::string> seen;
        while(std::getline(in,domain,'+')){
            if(domain.empty()||!seen.insert(domain).second)throw std::invalid_argument("Empty or duplicate product component");
            add_domain(domain);
        }
    }
    const rp::Result& run(const rp::Options& options={}){
        if(ran_)throw std::logic_error("Create a fresh reduced-product engine for each run");
        result_=rp::synthesize(problem_,options);ran_=true;return result_;
    }
    const rp::Problem& problem() const{return problem_;}
    const rp::Result& result() const{
        if(!ran_)throw std::logic_error("Synthesis has not run");
        return result_;
    }
    z3::expr get_inv_with_var(const std::vector<z3::expr>& vars) const{
        if(!ran_||vars.size()!=trans_.vars.size())throw std::invalid_argument("Run first and provide matching state arity");
        auto& ctx=trans_.ctx;if(result_.invariant.bottom)return ctx.bool_val(false);
        z3::expr_vector from(ctx),to(ctx);
        for(std::size_t i=0;i<vars.size();++i){
            if(&vars[i].ctx()!=&ctx || !vars[i].is_bv()||vars[i].get_sort().bv_size()!=trans_.vars[i].get_sort().bv_size())
                throw std::invalid_argument("Substitution variable sort mismatch");
            from.push_back(trans_.vars[i]);to.push_back(vars[i]);
        }
        z3::expr inv=ctx.bool_val(true);const auto& a=result_.invariant;
        for(std::size_t i=0;i<ranges_.size();++i){
            auto row=ranges_[i];row=row.substitute(from,to);unsigned w=row.get_sort().bv_size();
            inv=inv&&z3::ule(ctx.bv_val(a.lower[i].convert_to<std::string>().c_str(),w),row)
                   &&z3::ule(row,ctx.bv_val(a.upper[i].convert_to<std::string>().c_str(),w));
        }
        for(std::size_t i=0;i<flats_.size();++i)if(a.enabled[i]){
            auto row=flats_[i];row=row.substitute(from,to);
            inv=inv&&(row==ctx.bv_val(a.constants[i].convert_to<std::string>().c_str(),row.get_sort().bv_size()));
        }
        return inv.simplify();
    }
};
} // namespace invfinder
