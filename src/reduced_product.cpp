#include "rp/reduced_product.hpp"
#include <z3.h>
#include <algorithm>
#include <chrono>
#include <cctype>
#include <cmath>
#include <fstream>
#include <filesystem>
#include <limits>
#include <memory>
#include <regex>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>

namespace invfinder::rp {
namespace {
using Clock = std::chrono::steady_clock;
std::string dec(const Integer& x) { return x.convert_to<std::string>(); }
Integer maxval(unsigned w) { return (Integer(1) << w) - 1; }
unsigned parse_width(const std::string& text) {
    if (text.empty() || !std::all_of(text.begin(), text.end(),
        [](unsigned char c) { return c >= '0' && c <= '9'; }))
        throw std::invalid_argument("Width must be a decimal integer in [1,4096]");
    std::size_t used=0;
    const auto w=std::stoul(text, &used);
    if (used!=text.size() || w<1 || w>4096)
        throw std::invalid_argument("Width must be a decimal integer in [1,4096]");
    return static_cast<unsigned>(w);
}
std::string bv(const Integer& x, unsigned w) {
    if (x < 0 || x > maxval(w)) throw std::invalid_argument("BV numeral out of range");
    return "(_ bv" + dec(x) + " " + std::to_string(w) + ")";
}
std::string app(const std::string& op, const std::vector<std::string>& terms) {
    if (terms.empty()) return op == "and" ? "true" : "false";
    if (terms.size() == 1) return terms[0];
    std::string r = "(" + op;
    for (const auto& t : terms) r += " " + t;
    return r + ")";
}
std::string bin(const std::string& op, const std::string& a, const std::string& b) {
    return "(" + op + " " + a + " " + b + ")";
}
std::string neg(const std::string& x) { return "(not " + x + ")"; }
std::string assertion(const std::string& x) { return "(assert " + x + ")\n"; }
std::string sort(unsigned w) { return "(_ BitVec " + std::to_string(w) + ")"; }
std::string name(char k, std::size_t i) { return "rp_internal_" + std::string(1,k) + std::to_string(i); }
std::string decl(const std::string& n, const std::string& s) {
    return "(declare-const " + n + " " + s + ")\n";
}
// Token-level hygiene also enforces that a next-state row really is the
// same observation after simultaneous state-variable renaming. SMT validates
// operator sorts subsequently. Quoted symbols are retained as indivisible tokens.
std::vector<std::string> tokens(const std::string& text) {
    std::vector<std::string> out;
    for (std::size_t i=0;i<text.size();) {
        unsigned char c=text[i];
        if(std::isspace(c)){++i;continue;}
        if(c=='('||c==')'){out.emplace_back(1,static_cast<char>(c));++i;continue;}
        if(c==';'||c=='"')throw std::invalid_argument("Only BV/Boolean terms without comments or strings are accepted");
        std::size_t j=i;
        if(c=='|'){
            j=text.find('|',i+1);
            if(j==std::string::npos)throw std::invalid_argument("Unterminated quoted symbol");
            ++j;
        }else while(j<text.size()&&!std::isspace(static_cast<unsigned char>(text[j]))&&text[j]!='('&&text[j]!=')')++j;
        out.push_back(text.substr(i,j-i));i=j;
    }
    int depth=0;bool done=false;
    for(const auto& t:out){
        if(done)throw std::invalid_argument("Expected exactly one SMT term");
        if(t=="(")++depth;
        else if(t==")"){if(--depth<0)throw std::invalid_argument("Unbalanced SMT term");if(depth==0)done=true;}
        else if(depth==0)done=true;
        if(t.rfind("rp_internal_",0)==0)throw std::invalid_argument("Reserved internal symbol in input term");
    }
    if(out.empty()||depth)throw std::invalid_argument("Empty or unbalanced SMT term");
    return out;
}
std::string parameters(const Problem& p) {
    std::string s;
    for (std::size_t i = 0; i < p.ranges.size(); ++i) {
        s += decl(name('l',i), sort(p.ranges[i].width));
        s += decl(name('u',i), sort(p.ranges[i].width));
    }
    for (std::size_t i = 0; i < p.flats.size(); ++i) s += decl(name('e',i), "Bool");
    return s;
}
std::string states(const Problem& p) {
    std::string s;
    for (const auto& v : p.variables) s += decl(v.current,sort(v.width)) + decl(v.next,sort(v.width));
    return s;
}
std::string forall_state(const Problem& p, const std::string& f, bool both) {
    if (p.variables.empty()) return f;
    std::string s = "(forall (";
    for (const auto& v : p.variables) {
        s += "(" + v.current + " " + sort(v.width) + ")";
        if (both) s += "(" + v.next + " " + sort(v.width) + ")";
    }
    return s + ") " + f + ")";
}
void check_shape(const Problem& p, const Element& a) {
    if (a.bottom) return;
    if (a.lower.size()!=p.ranges.size() || a.upper.size()!=p.ranges.size() ||
        a.enabled.size()!=p.flats.size() || a.constants.size()!=p.flats.size())
        throw std::invalid_argument("Abstract-element shape mismatch");
}
std::string gamma(const Problem& p, const Element& a, bool next, bool symbolic) {
    if (a.bottom && !symbolic) return "false";
    check_shape(p,a);
    std::vector<std::string> cs;
    for (std::size_t i=0; i<p.ranges.size(); ++i) {
        const auto& r=p.ranges[i]; const auto& f=next?r.next:r.current;
        if (symbolic || a.lower[i]!=0)
            cs.push_back(bin("bvule",symbolic?name('l',i):bv(a.lower[i],r.width),f));
        if (symbolic || a.upper[i]!=maxval(r.width))
            cs.push_back(bin("bvule",f,symbolic?name('u',i):bv(a.upper[i],r.width)));
    }
    for (std::size_t i=0; i<p.flats.size(); ++i) {
        const auto& r=p.flats[i];
        auto fact=bin("=",next?r.next:r.current,bv(a.constants[i],r.width));
        if (symbolic) cs.push_back(bin("=>",name('e',i),fact));
        else if (a.enabled[i]) cs.push_back(fact);
    }
    return app("and",cs);
}
std::string wellformed(const Problem& p) {
    std::vector<std::string> cs;
    for(std::size_t i=0;i<p.ranges.size();++i) cs.push_back(bin("bvule",name('l',i),name('u',i)));
    return app("and",cs);
}
std::string inductive(const Problem& p,const Element& anchor) {
    const auto g=gamma(p,anchor,false,true), gp=gamma(p,anchor,true,true);
    return app("and",{forall_state(p,bin("=>",p.pre,g),false),
        forall_state(p,bin("=>",app("and",{g,p.transition}),gp),true)});
}
std::string below(const Problem& p,const Element& a) {
    std::vector<std::string> cs;
    for(std::size_t i=0;i<p.ranges.size();++i) {
        cs.push_back(bin("bvule",bv(a.lower[i],p.ranges[i].width),name('l',i)));
        cs.push_back(bin("bvule",name('u',i),bv(a.upper[i],p.ranges[i].width)));
    }
    for(std::size_t i=0;i<p.flats.size();++i) if(a.enabled[i]) cs.push_back(name('e',i));
    return app("and",cs);
}
std::string strict(const Problem& p,const Element& a) {
    std::vector<std::string> cs;
    for(std::size_t i=0;i<p.ranges.size();++i) {
        cs.push_back(bin("bvult",bv(a.lower[i],p.ranges[i].width),name('l',i)));
        cs.push_back(bin("bvult",name('u',i),bv(a.upper[i],p.ranges[i].width)));
    }
    for(std::size_t i=0;i<p.flats.size();++i) if(!a.enabled[i]) cs.push_back(name('e',i));
    return app("or",cs);
}
std::string json_string(const std::string& s) {
    std::string r="\"";
    for(unsigned char c:s) {
        if(c=='"'||c=='\\') {r+='\\';r+=static_cast<char>(c);}
        else if(c=='\n')r+="\\n";else if(c=='\t')r+="\\t";else if(c=='\r')r+="\\r";
        else if(c<32){ const char* h="0123456789abcdef";r+="\\u00";r+=h[c>>4];r+=h[c&15];}
        else r+=static_cast<char>(c);
    }
    return r+'"';
}
// Owns a context with non-reference-counted ASTs; models and solvers retain refs.
// Each engine has its own contexts: no process-global timeout or solver settings.
class Solver {
    Z3_context c_; Z3_solver s_; Z3_model m_=nullptr;
    void error() const {
        const auto e=Z3_get_error_code(c_);
        if(e) throw std::runtime_error(std::string("Z3: ")+Z3_get_error_msg(c_,e));
    }
    static void no_abort(Z3_context,Z3_error_code) {}
public:
    Solver() {
        auto cfg=Z3_mk_config(); Z3_set_param_value(cfg,"model","true");
        c_=Z3_mk_context(cfg);Z3_del_config(cfg); Z3_set_error_handler(c_,no_abort);
        s_=Z3_mk_solver(c_);Z3_solver_inc_ref(c_,s_);
        auto p=Z3_mk_params(c_);Z3_params_inc_ref(c_,p);
        Z3_params_set_bool(c_,p,Z3_mk_string_symbol(c_,"mbqi"),true);
        Z3_params_set_bool(c_,p,Z3_mk_string_symbol(c_,"ematching"),false);
        Z3_solver_set_params(c_,s_,p);Z3_params_dec_ref(c_,p);error();
    }
    ~Solver(){if(m_)Z3_model_dec_ref(c_,m_);Z3_solver_dec_ref(c_,s_);Z3_del_context(c_);}
    Solver(const Solver&)=delete;Solver& operator=(const Solver&)=delete;
    void add(const std::string& text){Z3_solver_from_string(c_,s_,text.c_str());error();}
    void push(){Z3_solver_push(c_,s_);error();}
    void pop(){Z3_solver_pop(c_,s_,1);error();}
    int check(unsigned milliseconds){
        if(m_){Z3_model_dec_ref(c_,m_);m_=nullptr;}
        auto p=Z3_mk_params(c_);Z3_params_inc_ref(c_,p);
        Z3_params_set_uint(c_,p,Z3_mk_string_symbol(c_,"timeout"),milliseconds);
        Z3_solver_set_params(c_,s_,p);Z3_params_dec_ref(c_,p);error();
        auto r=Z3_solver_check(c_,s_);error();
        if(r==Z3_L_TRUE){m_=Z3_solver_get_model(c_,s_);Z3_model_inc_ref(c_,m_);}
        return static_cast<int>(r);
    }
    std::string reason()const{return Z3_solver_get_reason_unknown(c_,s_);}
    Integer value(const std::string& n,unsigned w){
        if(!m_)throw std::logic_error("Model requested without SAT");
        auto a=Z3_mk_const(c_,Z3_mk_string_symbol(c_,n.c_str()),Z3_mk_bv_sort(c_,w));
        Z3_ast v=nullptr;
        if(!Z3_model_eval(c_,m_,a,true,&v))throw std::runtime_error("Z3 model evaluation failed");
        error(); const char* str=Z3_get_numeral_string(c_,v);error();
        return Integer(std::string(str));
    }
    bool flag(const std::string& n){
        auto a=Z3_mk_const(c_,Z3_mk_string_symbol(c_,n.c_str()),Z3_mk_bool_sort(c_));
        Z3_ast v=nullptr;
        if(!m_||!Z3_model_eval(c_,m_,a,true,&v))throw std::runtime_error("Z3 Boolean evaluation failed");
        error();auto b=Z3_get_bool_value(c_,v);error();
        if(b==Z3_L_UNDEF)throw std::runtime_error("Incomplete Boolean model");
        return b==Z3_L_TRUE;
    }
};
struct Scope { Solver& solver; explicit Scope(Solver& s):solver(s){s.push();} ~Scope(){solver.pop();} };
struct Interrupted { std::string reason; };
struct Features {
    std::vector<Integer> ranges,flats;
    bool operator==(const Features& o)const{return ranges==o.ranges&&flats==o.flats;}
};
struct Edge {Features source,target;};
struct Cut {enum Kind {LOWER,UPPER,FLAT} kind;std::size_t i;Integer value;};
class Engine {
    const Problem& p;const Options& o;Result result;Clock::time_point start=Clock::now();
    Element low;std::vector<Integer> cap,floor;std::vector<bool> blocked;
    std::vector<Features> positives;std::vector<Edge> edges;
    std::vector<std::string> learned;std::unique_ptr<Solver> candidate_solver;
    std::size_t committed=0;
    int check(Solver& s,std::uint64_t& category){
        if(o.max_solver_calls>=0&&result.stats.calls()>=static_cast<std::uint64_t>(o.max_solver_calls))
            throw Interrupted{"solver-call budget"};
        unsigned ms=0;
        if(o.timeout_seconds>=0){
            const auto left=o.timeout_seconds-std::chrono::duration<double>(Clock::now()-start).count();
            if(left<=0)throw Interrupted{"timeout"};
            ms=static_cast<unsigned>(std::min(std::ceil(left*1000.0),
                   static_cast<double>(std::numeric_limits<unsigned>::max())));
            ms=std::max(1u,ms);
        }
        ++category;const auto r=s.check(ms);
        if(r==0)throw Interrupted{"solver UNKNOWN: "+s.reason()};
        return r;
    }
    std::string observations(bool both)const{
        std::string s;
        for(std::size_t i=0;i<p.ranges.size();++i){
            const auto&r=p.ranges[i];s+=decl(name('r',i),sort(r.width));
            s+=assertion(bin("=",name('r',i),r.current));
            if(both){s+=decl(name('s',i),sort(r.width));s+=assertion(bin("=",name('s',i),r.next));}
        }
        for(std::size_t i=0;i<p.flats.size();++i){
            const auto&r=p.flats[i];s+=decl(name('f',i),sort(r.width));
            s+=assertion(bin("=",name('f',i),r.current));
            if(both){s+=decl(name('g',i),sort(r.width));s+=assertion(bin("=",name('g',i),r.next));}
        }
        return s;
    }
    Features features(Solver& s,bool next=false)const{
        Features f;
        for(std::size_t i=0;i<p.ranges.size();++i)f.ranges.push_back(s.value(name(next?'s':'r',i),p.ranges[i].width));
        for(std::size_t i=0;i<p.flats.size();++i)f.flats.push_back(s.value(name(next?'g':'f',i),p.flats[i].width));
        return f;
    }
    Element model(Solver& s)const{
        Element a=result.invariant;
        for(std::size_t i=0;i<p.ranges.size();++i){
            a.lower[i]=s.value(name('l',i),p.ranges[i].width);
            a.upper[i]=s.value(name('u',i),p.ranges[i].width);
        }
        for(std::size_t i=0;i<p.flats.size();++i)a.enabled[i]=s.flag(name('e',i));
        return a;
    }
    std::string member(const Features& s)const{
        std::vector<std::string> cs;
        for(std::size_t i=0;i<p.ranges.size();++i){
            const auto x=bv(s.ranges[i],p.ranges[i].width);
            cs.push_back(bin("bvule",name('l',i),x));cs.push_back(bin("bvule",x,name('u',i)));
        }
        for(std::size_t i=0;i<p.flats.size();++i)
            if(s.flats[i]!=result.invariant.constants[i])cs.push_back(neg(name('e',i)));
        return app("and",cs);
    }
    bool contains(const Element& a,const Features& s)const{
        for(std::size_t i=0;i<p.ranges.size();++i)
            if(s.ranges[i]<a.lower[i]||s.ranges[i]>a.upper[i])return false;
        for(std::size_t i=0;i<p.flats.size();++i)
            if(a.enabled[i]&&s.flats[i]!=a.constants[i])return false;
        return true;
    }
    void update_limits(){
        for(std::size_t i=0;i<p.ranges.size();++i){cap[i]=std::min(cap[i],low.lower[i]);floor[i]=std::max(floor[i],low.upper[i]);}
        for(std::size_t i=0;i<p.flats.size();++i)if(!low.enabled[i])blocked[i]=true;
    }
    bool join_positive(const Features& s,bool promotion){
        if(std::find(positives.begin(),positives.end(),s)!=positives.end())return false;
        positives.push_back(s);learned.push_back(member(s));++result.stats.positive_samples;
        if(promotion)++result.stats.promoted_targets;
        bool changed=false;
        for(std::size_t i=0;i<p.ranges.size();++i){
            if(s.ranges[i]<low.lower[i]){low.lower[i]=s.ranges[i];changed=true;}
            if(s.ranges[i]>low.upper[i]){low.upper[i]=s.ranges[i];changed=true;}
        }
        for(std::size_t i=0;i<p.flats.size();++i)
            if(low.enabled[i]&&s.flats[i]!=low.constants[i]){low.enabled[i]=false;changed=true;}
        if(changed)++result.stats.envelope_updates;
        update_limits();return changed;
    }
    void close_envelope(){
        if(!o.promotion)return;
        bool changed;
        do {changed=false;
            for(const auto& e:edges)
                if(contains(low,e.source)&&!contains(low,e.target))
                    changed=join_positive(e.target,true)||changed;
        }while(changed);
    }
    std::string limits()const{
        std::vector<std::string> cs;
        for(std::size_t i=0;i<p.ranges.size();++i){
            cs.push_back(bin("bvule",name('l',i),bv(cap[i],p.ranges[i].width)));
            cs.push_back(bin("bvule",bv(floor[i],p.ranges[i].width),name('u',i)));
        }
        for(std::size_t i=0;i<p.flats.size();++i)if(blocked[i])cs.push_back(neg(name('e',i)));
        return app("and",cs);
    }
    std::string cut_parameters(const Cut& c)const{
        if(c.kind==Cut::FLAT)return name('e',c.i);
        const auto v=bv(c.value,p.ranges[c.i].width);
        return c.kind==Cut::LOWER?bin("bvule",v,name('l',c.i)):bin("bvule",name('u',c.i),v);
    }
    std::string cut_states(const Cut& c)const{
        if(c.kind==Cut::FLAT)return bin("=",p.flats[c.i].current,bv(result.invariant.constants[c.i],p.flats[c.i].width));
        const auto v=bv(c.value,p.ranges[c.i].width);
        return c.kind==Cut::LOWER?bin("bvule",v,p.ranges[c.i].current):bin("bvule",p.ranges[c.i].current,v);
    }
    void apply_cut(const Cut& c){
        if(c.kind==Cut::LOWER)result.invariant.lower[c.i]=c.value;
        else if(c.kind==Cut::UPPER)result.invariant.upper[c.i]=c.value;
        else result.invariant.enabled[c.i]=true;
    }
    // Returns no counterexample only after two UNSAT verification checks.
    // A failed consecution creates an implication, never an unconditional sample.
    bool verify(const Element& a,bool learn){
        Solver init;init.add(states(p)+observations(false)+assertion(app("and",{p.pre,neg(gamma(p,a,false,false))})));
        if(check(init,result.stats.verifier)==1){
            if(learn){join_positive(features(init),false);close_envelope();}
            return false;
        }
        Solver step;step.add(states(p)+observations(true)+assertion(app("and",{gamma(p,a,false,false),p.transition,neg(gamma(p,a,true,false))})));
        if(check(step,result.stats.verifier)==1){
            if(learn){
                Edge e{features(step),features(step,true)};
                const bool duplicate=std::any_of(edges.begin(),edges.end(),[&](const Edge& old){return old.source==e.source&&old.target==e.target;});
                if(duplicate)throw std::runtime_error("Previously learned implication violated by a candidate");
                learned.push_back(bin("=>",member(e.source),member(e.target)));
                edges.push_back(std::move(e));++result.stats.implication_samples;close_envelope();
            }
            return false;
        }
        return true;
    }
    void commit_learned(){
        while(committed<learned.size())candidate_solver->add(assertion(learned[committed++]));
    }
    bool quantified(const Cut& c){
        Scope scope(*candidate_solver);
        candidate_solver->add(assertion(app("and",{below(p,result.invariant),limits(),cut_parameters(c)})));
        if(check(*candidate_solver,result.stats.quantified)==-1)return false;
        auto a=model(*candidate_solver);
        if(!verify(a,false))throw std::runtime_error("Quantified SAT model failed independent validation");
        result.invariant=std::move(a);++result.stats.accepted_candidates;return true;
    }
    bool cegis(const Cut& c){
        commit_learned();
        bool success=false;
        {Scope scope(*candidate_solver);
            candidate_solver->add(assertion(app("and",{below(p,result.invariant),limits(),cut_parameters(c)})));
            std::size_t local=committed;
            for(;;){
                if(o.max_candidates>=0&&result.stats.candidate>=static_cast<std::uint64_t>(o.max_candidates))
                    throw Interrupted{"candidate budget"};
                if(check(*candidate_solver,result.stats.candidate)==-1)break;
                auto a=model(*candidate_solver);
                if(verify(a,true)){
                    result.invariant=std::move(a);++result.stats.accepted_candidates;success=true;break;
                }
                while(local<learned.size())candidate_solver->add(assertion(learned[local++]));
                candidate_solver->add(assertion(limits()));
            }
        }
        commit_learned();return success;
    }
    void attempt(const Cut& c){
        ++result.stats.proposals;
        if(o.reduction){
            Solver red;red.add(states(p)+assertion(app("and",{gamma(p,result.invariant,false,false),neg(cut_states(c))})));
            if(check(red,result.stats.reduction)==-1){apply_cut(c);++result.stats.reduction_hits;return;}
        }
        bool success=o.method=="quantified"?quantified(c):cegis(c);
        if(!success){
            if(c.kind==Cut::LOWER)cap[c.i]=std::min(cap[c.i],Integer(c.value-1));
            else if(c.kind==Cut::UPPER)floor[c.i]=std::max(floor[c.i],Integer(c.value+1));
            else blocked[c.i]=true;
        }
    }
    void search_flats(){
        for(std::size_t i=0;i<p.flats.size();++i)
            if(!result.invariant.enabled[i]&&!blocked[i])attempt({Cut::FLAT,i,0});
    }
    void search_ranges(){
        for(std::size_t i=0;i<p.ranges.size();++i){
            while(result.invariant.lower[i]<cap[i]){
                Integer mid=(result.invariant.lower[i]+cap[i]+1)/2;attempt({Cut::LOWER,i,mid});
            }
            while(floor[i]<result.invariant.upper[i]){
                Integer mid=(floor[i]+result.invariant.upper[i])/2;attempt({Cut::UPPER,i,mid});
            }
        }
    }
    void certify(){
        Solver s;s.add(states(p)+parameters(p)+assertion(app("and",{
            wellformed(p),inductive(p,result.invariant),below(p,result.invariant),strict(p,result.invariant)})));
        if(check(s,result.stats.certificate)!=-1)throw std::runtime_error("Bestness certificate failed: a strictly smaller inductive tuple exists");
        result.bestness_certified=true;
    }
public:
    Engine(const Problem& p_,const Options& o_):p(p_),o(o_){
        result.invariant.lower.assign(p.ranges.size(),0);
        for(const auto& r:p.ranges)result.invariant.upper.push_back(maxval(r.width));
        result.invariant.enabled.assign(p.flats.size(),false);result.invariant.constants.assign(p.flats.size(),0);
    }
    Result run(){
        try{
            Solver initial;initial.add(states(p)+observations(false)+assertion(p.pre));
            if(check(initial,result.stats.initial)==-1){
                result.invariant.bottom=true;result.complete=true;result.bestness_certified=true;
                result.reason="empty initial set";
            }else{
                const auto anchor=features(initial);result.invariant.constants=anchor.flats;
                low=result.invariant;low.lower=low.upper=anchor.ranges;
                low.enabled.assign(p.flats.size(),true);
                cap=floor=anchor.ranges;blocked.assign(p.flats.size(),false);
                positives.push_back(anchor);learned.push_back(member(anchor));result.stats.positive_samples=1;
                candidate_solver=std::make_unique<Solver>();
                candidate_solver->add(states(p)+parameters(p)+assertion(wellformed(p)));
                if(o.method=="quantified")candidate_solver->add(assertion(inductive(p,result.invariant)));
                if(o.flat_first){search_flats();search_ranges();}else{search_ranges();search_flats();}
                // Publication is already sound. These final checks independently
                // validate the assembled result, including semantic-only updates.
                if(!verify(result.invariant,false))throw std::runtime_error("Final invariant failed validation");
                if(o.certify_best)certify();
                result.complete=true;result.reason="all parameter decisions resolved";
            }
        }catch(const Interrupted& e){result.reason=e.reason;}
        result.stats.seconds=std::chrono::duration<double>(Clock::now()-start).count();
        return result;
    }
};
} // namespace
void Problem::validate()const{
    if(pre.empty()||transition.empty())throw std::invalid_argument("Both pre and transition are required");
    const std::regex identifier("[A-Za-z_][A-Za-z_0-9]*");std::set<std::string> names;
    for(const auto& v:variables){
        if(!v.width||v.width>4096)throw std::invalid_argument("State width must be in [1,4096]");
        for(const auto& n:{v.current,v.next})
            if(!std::regex_match(n,identifier)||n.rfind("rp_internal_",0)==0||!names.insert(n).second)
                throw std::invalid_argument("State names must be distinct, simple SMT identifiers, and not rp_internal_*");
    }
    const auto pre_tokens=tokens(pre);tokens(transition);
    for(const auto& v:variables)
        if(std::find(pre_tokens.begin(),pre_tokens.end(),v.next)!=pre_tokens.end())
            throw std::invalid_argument("Precondition may not reference next-state variables");
    std::set<std::string> labels;
    for(const auto* rows:{&ranges,&flats})for(const auto& r:*rows){
        if(!r.width||r.width>4096||r.current.empty()||r.next.empty()||!labels.insert(r.label).second)
            throw std::invalid_argument("Invalid row width/expression or duplicate row label");
        auto current_tokens=tokens(r.current);const auto next_tokens=tokens(r.next);
        for(auto& token:current_tokens){
            for(const auto& v:variables)
                if(token==v.next)throw std::invalid_argument("Current row references next-state variable");
            for(const auto& v:variables)if(token==v.current){token=v.next;break;}
        }
        if(current_tokens!=next_tokens)
            throw std::invalid_argument("Next row must be the current row under state-variable renaming");
    }
}
std::uint64_t Statistics::calls()const{return initial+quantified+candidate+verifier+reduction+certificate;}
Result synthesize(const Problem& p,const Options& o){
    p.validate();
    if(o.method!="cegis"&&o.method!="quantified")throw std::invalid_argument("Method must be cegis or quantified");
    if(!std::isfinite(o.timeout_seconds)||o.max_candidates< -1||o.max_solver_calls< -1)
        throw std::invalid_argument("Invalid budget");
    return Engine(p,o).run();
}
std::string formula(const Problem& p,const Element& a,bool next){return gamma(p,a,next,false);}
std::string solver_version(){return Z3_get_full_version();}
Problem read_problem(const std::string& path){
    std::ifstream in(path);if(!in)throw std::runtime_error("Cannot open "+path);
    Problem p;std::string line;unsigned n=0;bool have_pre=false,have_trans=false;
    while(std::getline(in,line)){++n;if(!line.empty()&&line.back()=='\r')line.pop_back();
        if(line.empty()||line[0]=='#'||line=="RP1")continue;
        std::vector<std::string> f;std::stringstream s(line);std::string token;
        while(std::getline(s,token,'\t'))f.push_back(token);
        try{
            if(f.size()==4&&f[0]=="var")p.variables.push_back({f[1],f[2],parse_width(f[3])});
            else if(f.size()==2&&f[0]=="pre"&&!have_pre){p.pre=f[1];have_pre=true;}
            else if(f.size()==2&&f[0]=="trans"&&!have_trans){p.transition=f[1];have_trans=true;}
            else if(f.size()==5&&(f[0]=="range"||f[0]=="flat")){
                Row r{f[1],parse_width(f[2]),f[3],f[4]};
                (f[0]=="range"?p.ranges:p.flats).push_back(std::move(r));
            }else throw std::invalid_argument("invalid fields");
        }catch(const std::exception& e){throw std::runtime_error(path+":"+std::to_string(n)+": "+e.what());}
    }
    p.validate();return p;
}
std::string result_json(const Problem& p,const Result& r){
    std::ostringstream s;const auto b=[](bool v){return v?"true":"false";};
    s<<"{\n  \"complete\": "<<b(r.complete)<<", \"sound\": "<<b(r.sound)
     <<", \"bestness_certified\": "<<b(r.bestness_certified)<<", \"bottom\": "<<b(r.invariant.bottom)
     <<",\n  \"reason\": "<<json_string(r.reason)<<", \"z3\": "<<json_string(solver_version())<<",\n  \"ranges\": [";
    for(std::size_t i=0;i<p.ranges.size();++i){if(i)s<<',';s<<"{\"label\":"<<json_string(p.ranges[i].label)
        <<",\"lower\":"<<json_string(dec(r.invariant.lower[i]))<<",\"upper\":"<<json_string(dec(r.invariant.upper[i]))<<'}';}
    s<<"],\n  \"flats\": [";
    for(std::size_t i=0;i<p.flats.size();++i){if(i)s<<',';s<<"{\"label\":"<<json_string(p.flats[i].label)
        <<",\"enabled\":"<<b(r.invariant.enabled[i])<<",\"constant\":"<<json_string(dec(r.invariant.constants[i]))<<'}';}
    s<<"],\n  \"formula\": "<<json_string(formula(p,r.invariant))<<",\n  \"stats\": {";
#define FIELD(x) s<<"\"" #x "\":"<<r.stats.x<<','
    FIELD(initial);FIELD(quantified);FIELD(candidate);FIELD(verifier);FIELD(reduction);FIELD(certificate);
    FIELD(proposals);FIELD(reduction_hits);FIELD(positive_samples);FIELD(implication_samples);
    FIELD(promoted_targets);FIELD(envelope_updates);FIELD(accepted_candidates);
#undef FIELD
    s<<"\"total_calls\":"<<r.stats.calls()<<",\"seconds\":"<<r.stats.seconds<<"}\n}\n";return s.str();
}
void write_certificates(const Problem& p,const Result& r,const std::string& prefix){
    // A reused prefix must not leave a stale bestness obligation from a prior
    // completed run when the current run is incomplete.
    if (!r.complete && !r.invariant.bottom) {
        std::error_code ec;
        std::filesystem::remove(prefix+".best.smt2",ec);
        if (ec) throw std::runtime_error("Cannot remove stale bestness obligation: "+ec.message());
    }
    auto write=[&](const std::string& suffix,const std::string& content){
        std::ofstream out(prefix+suffix);if(!out)throw std::runtime_error("Cannot write certificate file");
        out<<"; Expected UNSAT. A replayable obligation, not a serialized proof object.\n"<<content<<"(check-sat)\n";
        if(!out)throw std::runtime_error("Certificate file write failed");
    };
    write(".init.smt2",states(p)+assertion(app("and",{p.pre,neg(formula(p,r.invariant))})));
    write(".step.smt2",states(p)+assertion(app("and",{formula(p,r.invariant),p.transition,neg(formula(p,r.invariant,true))})));
    if(r.invariant.bottom)write(".best.smt2",states(p)+assertion(p.pre));
    else if(r.complete)write(".best.smt2",states(p)+parameters(p)+assertion(app("and",{
        wellformed(p),inductive(p,r.invariant),below(p,r.invariant),strict(p,r.invariant)})));
}
} // namespace invfinder::rp
