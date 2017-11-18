/***************************************************************************************[Solver.cc]
abcdSAT -- Copyright (c) 2016, Jingchao Chen, Donghua University   

abcdSAT sources are obtained by modifying Glucose (see below Glucose copyrights). Permissions and copyrights of
abcdSAT are exactly the same as Glucose.

----------------------------------------------------------
Glucose -- Copyright (c) 2009, Gilles Audemard, Laurent Simon
				CRIL - Univ. Artois, France
				LRI  - Univ. Paris Sud, France
 
Glucose sources are based on MiniSat (see below MiniSat copyrights). Permissions and copyrights of
Glucose are exactly the same as Minisat on which it is based on. (see below).

---------------

Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <math.h>

#include "mtl/Sort.h"
#include "core/Solver.h"
#include "core/Constants.h"
#include "core/D_Constants.h"

#include "utils/System.h"

#define  SELECT_WIDTH  9    

int mod_k=4;
unsigned int all_conflicts=0;
unsigned int unsatCnt=0;
unsigned int unsat9Cnt=0;
int priorBegin[150];
int priorNum=0;
int outvars=0;
  
int cancel_subsolve=0;
extern int size30;

extern int **Bclauses;
extern int nBlocked2;
extern int BCDfalses;
extern int nClausesB;
int  *varRange=0;

int UnitPropSimplify(PPS *pps,bool multi_probe);
int SimplifySAT(PPS *pps);
void extend_solution(PPS *pps);
void XOR_Preprocess(PPS *pps, int way);
void check(int sol[],Stack<int> *clause);
void SortLiteral(Stack<int> * clause);
void sortClause(PPS *pps,int **clsPtr);
void release_pps (PPS * pps);

Stack<int> * doubleClause=0;
int  doubleClauseCnt=0;

using namespace abcdSAT;

extern FILE*   certifiedOutput;
extern bool    certifiedUNSAT;  

Solver* mainSolver=0;
int    drupNum=0;
int    treeDepth=0;
int    treeExtLit[30];
int    treeAuxLit[30]; //auxiliary  z=x^y
int    auxVar;

extern int * ite2ext;

inline int GetextLit (int ilit) 
{
  if(ilit < 0) return -ite2ext[-ilit];
  return ite2ext[ilit];
}

inline void  printreeExtLit()
{
   if(treeDepth<=0) return;
   int k=treeDepth-1;
   if(treeAuxLit[k]==0){
        if(k==0) treeAuxLit[k]=treeExtLit[k];
        else{ //auxiliary var replace z=x^y^.....
             auxVar++;
             fprintf(certifiedOutput, "%i ", auxVar);
             for (int i = 0; i < treeDepth; i++){// z V -x V -y.....
                  fprintf(certifiedOutput, "%i ", treeExtLit[i]);
             }
             fprintf(certifiedOutput, "0\n");
             for (int i = 0; i < treeDepth; i++){// -z V x
                  fprintf(certifiedOutput, "%i %i 0\n", -auxVar, -treeExtLit[i]);
             }
             treeAuxLit[k]=-auxVar;
        }
   }
   fprintf(certifiedOutput, "%i ", treeAuxLit[k]);
}

inline void  printDrupUnit(Lit p, int needExtV)
{
      printreeExtLit();
      int lit=toIntLit(p);
      if(needExtV){
              if(lit < 0) lit = -ite2ext[-lit];
              else        lit =  ite2ext[lit];
      }
      fprintf(certifiedOutput, "%i 0\n", lit);
}

inline void  printDrupLits(const vec<Lit>& ps, int deleteflag, int needExtV)
{     int i;

      if(deleteflag){
           fprintf(certifiedOutput, "d ");
      }
      printreeExtLit();
      int changext=0;
      if(ite2ext && needExtV) changext=1;
      for (i = 0; i < ps.size(); i++){
           int lit=toIntLit(ps[i]);
           if(changext) lit=GetextLit(lit);
           fprintf(certifiedOutput, "%i ", lit);
      }   
      fprintf(certifiedOutput, "0\n");
}

inline void  printDrupClause(Clause & c, int deleteflag, int needExtV)
{     int i;
      if(deleteflag){
           fprintf(certifiedOutput, "d ");
      }
      printreeExtLit();
   
      int changext=0;
      if(ite2ext && needExtV) changext=1;
      for (i = 0; i < c.size(); i++){
           int lit=toIntLit(c[i]);
           if(changext) lit=GetextLit(lit);
           fprintf(certifiedOutput, "%i ", lit);
      }
      fprintf(certifiedOutput, "0\n");
}

//         clause_type=CNF_CLS / CNF_C_B; 
void add_2type_clause(vec<int> & lits, int clause_type)
{   
    if(doubleClause==0){
         doubleClause = new Stack<int>;
         doubleClauseCnt=0;
    }
    int k=lits.size();
    doubleClause->push(((k+1)<<FLAGBIT) | clause_type);
    for (int i = 0; i < k; i++) doubleClause->push(lits[i]);
    doubleClauseCnt++;
}

bool isConflict(int *clause,int len)
{  int i;

   if(len<=0) return false;
     
   vec<Lit> lits;
   lits.clear();
   CRef confl = CRef_Undef;
   int fconf=0;
   for (i=0; i<len; i++){
        int lit=clause[i];
	Lit p=(lit > 0) ? ~mkLit(lit-1)   : mkLit(-lit-1);
        if ( mainSolver->value(p) == l_True) {
               continue;
        }

        lits.push(~p);
        if ( mainSolver->value(p) == l_False){
               fconf=1;
               break;
        }
  
        mainSolver->newDecisionLevel();
        mainSolver->uncheckedEnqueue(p);
       
        confl = mainSolver->propagate();
        if (confl != CRef_Undef) break;
   }
   mainSolver->cancelUntil(0);
   if (confl != CRef_Undef || fconf){
         int ys=0;
         if(lits.size() > 1) {
                 mainSolver->simpAddClause(lits);
                 ys=1;
         }
         else {
              if(lits.size() == 1 && mainSolver->value(lits[0]) == l_Undef ){
                // mainSolver->unitPropagation(lits[0]);//bug 2016/9/28  9dlx_..._345.cnf
                 mainSolver->addClause_(lits);
                 if(certifiedUNSAT)  printDrupLits(lits, 0, mainSolver->needExtVar);
                 ys=1;
              }
         }
         if(ys) return true;
   }
   return false;
}

bool hasBincls(int lit1, int lit2, vec<int> & lits)
{
   lits.clear();
   Lit p=(lit1 > 0) ? mkLit(lit1-1)   : ~mkLit(-lit1-1);
   Lit q=(lit2 > 0) ? mkLit(lit2-1)   : ~mkLit(-lit2-1);
   bool has=mainSolver->hasBin(p,q);
   if(has) return true;
   int clause[2];
   clause[0]=lit1; clause[1]=lit2;
   if(isConflict(clause,2)) {
         lits.push(lit1);
         lits.push(lit2);
   }
   return false;
}

vec<Lit> priorityLit;

int load_glueclause(Solver* solver, PPS *pps);

//=================================================================================================
// Options:

static const char* _cat = "CORE";
static const char* _cr = "CORE -- RESTART";
static const char* _cred = "CORE -- REDUCE";
static const char* _cm = "CORE -- MINIMIZE";



static DoubleOption opt_K                 (_cr, "K",           "The constant used to force restart",            0.8,     DoubleRange(0, false, 1, false));           
static DoubleOption opt_R                 (_cr, "R",           "The constant used to block restart",            1.4,     DoubleRange(1, false, 5, false));           
static IntOption     opt_size_lbd_queue     (_cr, "szLBDQueue",      "The size of moving average for LBD (restarts)", 50, IntRange(10, INT32_MAX));
static IntOption     opt_size_trail_queue     (_cr, "szTrailQueue",      "The size of moving average for trail (block restarts)", 5000, IntRange(10, INT32_MAX));

static IntOption     opt_first_reduce_db     (_cred, "firstReduceDB",      "The number of conflicts before the first reduce DB", 2000, IntRange(0, INT32_MAX));
static IntOption     opt_inc_reduce_db     (_cred, "incReduceDB",      "Increment for reduce DB", 300, IntRange(0, INT32_MAX));
static IntOption     opt_spec_inc_reduce_db     (_cred, "specialIncReduceDB",      "Special increment for reduce DB", 1000, IntRange(0, INT32_MAX));
static IntOption    opt_lb_lbd_frozen_clause      (_cred, "minLBDFrozenClause",        "Protect clauses if their LBD decrease and is lower than (for one turn)", 30, IntRange(0, INT32_MAX));

static IntOption     opt_lb_size_minimzing_clause     (_cm, "minSizeMinimizingClause",      "The min size required to minimize clause", 30, IntRange(3, INT32_MAX));
static IntOption     opt_lb_lbd_minimzing_clause     (_cm, "minLBDMinimizingClause",      "The min LBD required to minimize clause", 6, IntRange(3, INT32_MAX));


static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.8,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);

static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));

//=================================================================================================
// Constructor/Destructor:

void Solver :: mainAddClause(const vec<Lit>& lits)
{
     CRef cr = ca.alloc(lits, true);
     ca[cr].setLBD(0x7fffffff);
     learnts.push(cr);
     attachClause(cr);
}
/*
bool Solver :: mainDelClause(const vec<Lit>& lits)
{  int i,j;

   for (i = learnts.size()-1; i>=0; i--){
         Clause& c = ca[learnts[i]];
         if(c.size() != lits.size()) continue;
         for(j=0; j < c.size(); j++){
            int lit=toIntLit(c[j]);
            if(litMark[lit]==0) goto nextc;
         }
         removeClause(learnts[i]);
         for (; i < learnts.size()-1; i++) learnts[i] = learnts[i+1];
         learnts.shrink(1);
         checkGarbage();
         return true;
 nextc:  ;
    }
    for (i=0; i<lits.size(); i++) printf("%d ", toIntLit(lits[i]));
    return false;
}
*/

Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
    , K              (opt_K)
    , R              (opt_R)
    , sizeLBDQueue   (opt_size_lbd_queue)
    , sizeTrailQueue   (opt_size_trail_queue)
    , firstReduceDB  (opt_first_reduce_db)
    , incReduceDB    (opt_inc_reduce_db)
    , specialIncReduceDB    (opt_spec_inc_reduce_db)
    , lbLBDFrozenClause (opt_lb_lbd_frozen_clause)
    , lbSizeMinimizingClause (opt_lb_size_minimzing_clause)
    , lbLBDMinimizingClause (opt_lb_lbd_minimzing_clause)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
 
    // Statistics: (formerly in 'SolverStats')
    //
  ,  nbRemovedClauses(0),nbReducedClauses(0), nbDL2(0),nbBin(0),nbUn(0) , nbReduceDB(0)
    , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0),nbstopsrestarts(0),nbstopsrestartssame(0),lastblockatrestart(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
    , curRestart(1)

  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches            (WatcherDeleted(ca))
  , watchesBin            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (VarOrderLt(activity))
  , progress_estimate  (0)
  , remove_satisfied   (true)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)

{   MYFLAG=0;
    g_pps=(struct PPS *) calloc (1, sizeof (PPS));
    recursiveDepth=0;
    conflict_limit=-1;
    completesolve=0;
    originVars=0;
    equhead=equlink=0;
    dummyVar=0;
    hbrsum=equsum=unitsum=probeSum=0;
    varRange=0;
    longcls=0;
    probe_unsat=0;
    BCD_conf=500000;
    maxDepth=0;
    subformuleClause=0;
    needExtVar=0;
}

Solver::~Solver()
{
   ClearClause(clauses, 0);
   ClearClause(learnts, 0);

   if(probe_unsat==0) garbageCollect();
   if(g_pps->unit) free(g_pps->unit);
  
   if(equhead) free(equhead);
   if(equlink) free(equlink);
   equhead = equlink=0;
   if(dummyVar) free(dummyVar);
   dummyVar=0;
   delete g_pps;
}

void Solver:: ClearUnit()
{
     if(treeDepth<2) return;
     for(int i=trail.size()-1; i>=init_trailsize; i--){
            vec<Lit> ps;
            ps.clear();
            ps.push(trail[i]);
            printDrupLits(ps, 1, needExtVar);
     }
     trail.clear();
}         

CRef Solver::unitPropagation(Lit p)
{
     int oldts=trail.size();
     uncheckedEnqueue(p);
     CRef confl = propagate();
     if(decisionLevel()==0){
         if (certifiedUNSAT){
              if(confl != CRef_Undef){
                  printDrupUnit(trail[oldts], needExtVar);
                  trail.shrink(trail.size() - oldts);
                  return confl;
              }
              for(int i=oldts; i<trail.size(); i++) printDrupUnit(trail[i], needExtVar);
         }
   }
   return confl;
}

bool Solver :: is_conflict(vec<Lit> & lits)
{  
   cancelUntil(0);
   int i;
   for (i=0; i<lits.size(); i++){
        Lit p = ~lits[i];
        if ( value(p) == l_True) continue;
        if ( value(p) == l_False) break;
  
        newDecisionLevel();
        uncheckedEnqueue(p);
        CRef confl = propagate();
        if (confl != CRef_Undef) break;
   }
   cancelUntil(0);
   if(i<lits.size()) return true;
   return false;
}

//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    watchesBin  .init(mkLit(v, false));
    watchesBin  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    //activity .push(0);
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    permDiff  .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    return v;
}


bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);

    if(subformuleClause==0 || (subformuleClause==2 && nClauses()>400000)){
        vec<Lit>    os;
        os.clear();
        Lit p; int i, j,flag=0;

        if(certifiedUNSAT) {
             for (i = 0; i < ps.size(); i++) {
                   os.push(ps[i]);
                   if (value(ps[i]) == l_False) flag = 1;
             }
        }

        for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
            if (value(ps[i]) == l_True || ps[i] == ~p) return true;
            else if (value(ps[i]) != l_False && ps[i] != p)
                 ps[j++] = p = ps[i];
           ps.shrink(i - j);

       if (flag && certifiedUNSAT) {
             printDrupLits(ps, 0, 0);
             if(subformuleClause==0) printDrupLits(os, 1, 0);
       } 
    }

    if (ps.size() == 0) return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    if(c.size()==2) {
      watchesBin[~c[0]].push(Watcher(cr, c[1]));
      watchesBin[~c[1]].push(Watcher(cr, c[0]));
    } else {
      watches[~c[0]].push(Watcher(cr, c[1]));
      watches[~c[1]].push(Watcher(cr, c[0]));
    }
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }




void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    
    assert(c.size() > 1);
    if(c.size()==2) {
      if (strict){
        remove(watchesBin[~c[0]], Watcher(cr, c[1]));
        remove(watchesBin[~c[1]], Watcher(cr, c[0]));
      }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watchesBin.smudge(~c[0]);
        watchesBin.smudge(~c[1]);
      }
    } else {
      if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
      }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
      }
    }
    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr) {
  
  Clause& c = ca[cr];
  detachClause(cr);
  // Don't leave pointers to free'd memory!
  if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
  c.mark(1); 
  ca.free(cr);
}

bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++){
        if (value(c[i]) == l_True) return true;
    }
  
    return false; 
}


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
           if(maxDepth < trail.size()-trail_lim[0]) maxDepth=trail.size()-trail_lim[0];
           for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:

extern int *extVarRank,numVarRk;

Lit Solver::pickBranchLit()
{
    Var next = var_Undef;
     
    int clevel=decisionLevel();

    if(clevel < 6 && numVarRk>0){
          double MaxAct=0;
          for(int i=0; i<numVarRk && i<100; i++){
             int v=extVarRank[i]-1;
             if (decision[v] && value(v) == l_Undef){
                   if(activity[v]>MaxAct){
                          MaxAct=activity[v];
                          next=v;
                   }
             }
          }
          if(next != var_Undef) goto found;
    }
  
    if(clevel>0 && clevel < 4){
          if(varRange){
   //          conflicts > 6000000 
              if( (int)conflicts >= BCD_conf || recursiveDepth>0) goto nofound;
              Lit lit=trail[trail_lim[0]];
              int v = var(lit);
              if(varRange[v]==0 || v >= originVars) goto nofound;
              int ed = varRange[v];
              double maxAct=-10000;
              int vec[20];
              for (int i = varRange[v]+1; i >=ed-5; i--){//-5, -10
                        int *plit = Bclauses[i];
                        int j=0;
                        while(*plit){
                            int cv=ABS(*plit)-1;
                            if(value(cv) == l_Undef){
                                if(decision[cv] && j<20) vec[j++]=cv;  
                            }
                            else {
                                if(value(cv) == l_True) { if(*plit>0) goto nexti;}
                                else   if(*plit<0) goto nexti;
                            }
                            plit++;
                        }
            //
                        for(j--; j>=0; j--){
                              if(activity[vec[j]]>maxAct){
                                   next=vec[j];
                                   maxAct=activity[next];
                              }
                        }
                        nexti: ;
              }
              if(next != var_Undef ) goto found;
      //       next = var_Undef;
         }
    }
//
nofound:
   if (next == var_Undef){
        if (order_heap.empty()) return lit_Undef;
        else next = order_heap.removeMin();
    }
   
   // Activity based decision:
    while (value(next) != l_Undef || !decision[next])
        if (order_heap.empty()) return lit_Undef;
        else next = order_heap.removeMin();

found:
    if(bitVecNo>=0){
           if(clevel<12){
          // if(conflicts > 200000 && clevel<12 || clevel<8){ 
                   polarity[next]=(bitVecNo>>(clevel% mod_k)) & 1;
           }
     }
     return mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel,unsigned int &lbd)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

	// Special case for binary clauses
	// The first one has to be SAT
	if( p != lit_Undef && c.size()==2 && value(c[0])==l_False) {
	  
	  assert(value(c[1])==l_True);
	  Lit tmp = c[0];
	  c[0] =  c[1], c[1] = tmp;
	}
	
       if (c.learnt())
            claBumpActivity(c);

#ifdef DYNAMICNBLEVEL		    
       // DYNAMIC NBLEVEL trick (see competition'09 companion paper)
       if(c.learnt()  && c.lbd()>2) { 
	 MYFLAG++;
	 unsigned  int nblevels =0;
	 for(int i=0;i<c.size();i++) {
	   int l = level(var(c[i]));
	//   if (l!=0 && permDiff[l] != MYFLAG) {//new idea
	   if (permDiff[l] != MYFLAG) {
	     permDiff[l] = MYFLAG;
	     nblevels++;
	   }
	   
	   
	 }
	 if(nblevels+1<c.lbd() ) { // improve the LBD
	   if(c.lbd()<=lbLBDFrozenClause) {
	     c.setCanBeDel(false); 
	   }
	   // seems to be interesting : keep it for the next round
	   c.setLBD(nblevels); // Update it
	 }
       }
#endif
       

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel()) {
                    pathC++;
#ifdef UPDATEVARACTIVITY
		    // UPDATEVARACTIVITY trick (see competition'09 companion paper)
		    if((reason(var(q))!= CRef_Undef)  && ca[reason(var(q))].learnt()) 
		      lastDecisionLevel.push(q);
#endif

		} else {
                    out_learnt.push(q);
		}
	    }
        }
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();


    /* ***************************************
      Minimisation with binary clauses of the asserting clause
      First of all : we look for small clauses
      Then, we reduce clauses with small LBD.
      Otherwise, this can be useless
     */
    if(out_learnt.size()<=lbSizeMinimizingClause) {
      // Find the LBD measure                                                                                                         
      lbd = 0;
      MYFLAG++;
      for(int i=0;i<out_learnt.size();i++) {

	int l = level(var(out_learnt[i]));
	if (permDiff[l] != MYFLAG) {
	  permDiff[l] = MYFLAG;
	  lbd++;
	}
      }


      if(lbd<=lbLBDMinimizingClause){
      MYFLAG++;
      
      for(int i = 1;i<out_learnt.size();i++) {
	permDiff[var(out_learnt[i])] = MYFLAG;
      }

      vec<Watcher>&  wbin  = watchesBin[p];
      int nb = 0;
      for(int k = 0;k<wbin.size();k++) {
	Lit imp = wbin[k].blocker;
	if(permDiff[var(imp)]==MYFLAG && value(imp)==l_True) {
	//	  printClause(out_learnt);
        //	  printClause(*(wbin[k].clause));
	  nb++;
	  permDiff[var(imp)]= MYFLAG-1;
	}
      }
      int l = out_learnt.size()-1;
      if(nb>0) {
	nbReducedClauses++;
	for(int i = 1;i<out_learnt.size()-nb;i++) {
	  if(permDiff[var(out_learnt[i])]!=MYFLAG) {
	    Lit p = out_learnt[l];
	    out_learnt[l] = out_learnt[i];
	    out_learnt[i] = p;
	    l--;i--;
	  }
	}
	
	//    printClause(out_learnt);
	out_learnt.shrink(nb);
      }
    }
    }
    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }


  // Find the LBD measure 
  lbd = 0;
  MYFLAG++;
  for(int i=0;i<out_learnt.size();i++) {
    
    int l = level(var(out_learnt[i]));
    if (permDiff[l] != MYFLAG) {
//    if (l!=0 && permDiff[l] != MYFLAG) {//new idea
      permDiff[l] = MYFLAG;
      lbd++;
    }
  }


  
#ifdef UPDATEVARACTIVITY
  // UPDATEVARACTIVITY trick (see competition'09 companion paper)
  if(lastDecisionLevel.size()>0) {
    for(int i = 0;i<lastDecisionLevel.size();i++) {
      if(ca[reason(var(lastDecisionLevel[i]))].lbd()<lbd)
	varBumpActivity(var(lastDecisionLevel[i]));
    }
    lastDecisionLevel.clear();
  } 
#endif	    



    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause& c = ca[reason(var(analyze_stack.last()))]; analyze_stack.pop();
	if(c.size()==2 && value(c[0])==l_False) {
	  assert(value(c[1])==l_True);
	  Lit tmp = c[0];
	  c[0] =  c[1], c[1] = tmp;
	}

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
		//                for (int j = 1; j < c.size(); j++) Minisat (glucose 2.0) loop 
		// Bug in case of assumptions due to special data structures for Binary.
		// Many thanks to Sam Bayless (sbayless@cs.ubc.ca) for discover this bug.
		for (int j = ((c.size()==2) ? 0:1); j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }  

            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();
    watchesBin.cleanAll();
    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

	
	    // First, Propagate binary clauses 
	vec<Watcher>&  wbin  = watchesBin[p];
	
	for(int k = 0;k<wbin.size();k++) {
	  
	  Lit imp = wbin[k].blocker;
	  
	  if(value(imp) == l_False) {
	    return wbin[k].cref;
	  }
	  
	  if(value(imp) == l_Undef) {
	    uncheckedEnqueue(imp,wbin[k].cref);
	  }
	}
    


        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
	      
	      *j++ = w; continue; }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else {
                uncheckedEnqueue(first, cr);
	    }
        NextClause:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;
    
    return confl;
}

void Solver::deepropagate(vec<int> & deep, vec<int> & prvPos, Lit q)
{
    newDecisionLevel();
    uncheckedEnqueue(q);

    watches.cleanAll();
    watchesBin.cleanAll();
    int dhead=0;
    deep.push(0);
    prvPos.push(-1);
    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];   
        int          depth = deep[dhead++]+1;
      	vec<Watcher>&  wbin  = watchesBin[p];
	for(int k = 0;k<wbin.size();k++) {
	  Lit imp = wbin[k].blocker;
	  if(value(imp) == l_Undef) {
	    uncheckedEnqueue(imp,wbin[k].cref);
            deep.push(depth);
            prvPos.push(qhead-1);
	  }
	}
    
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *end;
        for (i = (Watcher*)ws, end = i + ws.size();  i != end; i++){
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            int j=0;    
            Lit lit;
            for (int k = 0; k < c.size(); k++){
                  if(value(c[k]) == l_True) goto NextClause;
                  if(value(c[k]) == l_False) continue;
                  if(j) goto NextClause;
                  j++;
                  lit=c[k];
            }
            if(j){
                  uncheckedEnqueue(lit, cr);
                  deep.push(depth);
                  prvPos.push(qhead-1);
	    }
            NextClause:;
        }
    }
}

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
 
    // Main criteria... Like in MiniSat we keep all binary clauses
    if(ca[x].size()> 2 && ca[y].size()==2) return 1;
    
    if(ca[y].size()>2 && ca[x].size()==2) return 0;
    if(ca[x].size()==2 && ca[y].size()==2) return 0;
    
    // Second one  based on literal block distance
    if(ca[x].lbd()> ca[y].lbd()) return 1;
    if(ca[x].lbd()< ca[y].lbd()) return 0;    
    
    
    // Finally we can use old activity or size, we choose the last one
        return ca[x].activity() < ca[y].activity();
    }    
};

void Solver::reduceDB()
{
  int     i, j;
  if(learnts.size() < 30) return;
  nbReduceDB++;
  int fixV=BCD_conf? 1 : 5;
  if(BCD_delay) fixV=20;
  int limit = learnts.size() / 2;
  int unFix=nUnfixedVars();
  if(conflicts>300000 && unFix>1200 && (nVars()>unFix+fixV) && nClauses() < 30*unFix){
     //printf("c find_k reduceDB \n");
     int range=0;
     for (i = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
       if (c.canBeDel() || locked(c)) range++;
     }
     range=3*range/5+limit/2+limit/6;
     find_k_th(learnts, range, reduceDB_lt(ca));
   }
   else  sort(learnts, reduceDB_lt(ca));

  // We have a lot of "good" clauses, it is difficult to compare them. Keep more !
  if(ca[learnts[learnts.size() / RATIOREMOVECLAUSES]].lbd()<=3) nbclausesbeforereduce +=specialIncReduceDB; 
  // Useless :-)
  if(ca[learnts.last()].lbd()<=5)  nbclausesbeforereduce +=specialIncReduceDB; 
  
  // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
  // Keep clauses which seem to be usefull (their lbd was reduce during this sequence)
  for (i = j = 0; i < learnts.size(); i++){
    Clause& c = ca[learnts[i]];
    if (c.lbd()>2 && c.size() > 2 && c.canBeDel() &&  !locked(c) && (i < limit)) {
         removeClause(learnts[i]);
         if(certifiedUNSAT) printDrupClause(c, 1, needExtVar);
         nbRemovedClauses++;
    }
    else {
      if(!c.canBeDel()) limit++; //we keep c, so we can delete an other clause
      c.setCanBeDel(true);       // At the next step, c can be delete
      learnts[j++] = learnts[i];
    }
  }
  learnts.shrink(i - j);
  checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs,int delFlag)
{  int i, j;

   if(certifiedUNSAT && delFlag) delFlag=1;
   else delFlag=0;

   for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (c.size()>=2 && satisfied(c)){  // A bug if we remove size ==2, We need to correct it, but later.
                 if(delFlag)  printDrupClause(c, 1, needExtVar);
                 removeClause(cs[i]);
        }
        else    cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}

void Solver::rebuildOrderHeap()
{
    if(conflicts>500 && equhead && nFreeVars()>1200 && (recursiveDepth || nFreeVars()>20000)){
      for (int i =0; i < nVars(); i++) {
         int exv=i+1;
         if(equhead[exv]==0 || equhead[exv]==exv) continue;
         activity[i]=0;
      }            
    }
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef){
             if(equhead && recursiveDepth && nFreeVars()>1200){
                int exv=v+1;
                if(equhead[exv] && equhead[exv]!=exv) continue;
             }
             vs.push(v);
             if(conflicts>50000 || recursiveDepth){
               Lit p = mkLit(v);//new idea
               int pos=watchesBin[p].size();
               int neg=watchesBin[~p].size();
               activity[v] += (pos+1)*(neg+1)/100.0;
            }
        }

   int sz=vs.size();
   int k;
   if(maxDepth){
          k= recursiveDepth? 2:3;
          k=k*maxDepth;
          if(sz<1200 && k<sz/2)  k=sz/2;
          if(k<250) k=250;
          if(k>sz)  k=sz;
    }
    else   k=sz;
    maxDepth=0;
    if(k < sz) find_k_th((Var *)vs, vs.size(), k, VarOrderLt(activity));
    order_heap.build(vs,k);
}



/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

   if (!ok || propagate() != CRef_Undef)
        return ok = false;

   if (nAssigns() == simpDB_assigns || (simpDB_props > 0)) return true;
   
 // Remove satisfied clauses:
   removeSatisfied(learnts,1);
   
   if (remove_satisfied){        // Can be turned off.
          static int pre_conf=0;
          if((nVars() < 500000 || longcls<300000) && (conflicts>200000 || recursiveDepth>3) && (nClauses()<300000 || ((int)conflicts-pre_conf)>120000)){
                  pre_conf=(int)conflicts;
                  lbool ret=probe();
                  if(ret == l_False){
                       probe_unsat=1;
                       return ok = false;
                  }
          }
          else {
             int delflag=0;
             if(certifiedUNSAT && subformuleClause==0) delflag=1;
             removeSatisfied(clauses, delflag);
          }
    }
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
   // int         backtrack_level;
   // unsigned int nblevels;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    bool blocked=false;
    uint64_t old_conf=conflicts;
    starts++;
    for (;;){
        //int oldts=trail.size();
        CRef confl = propagate();
nexta:
        if (confl != CRef_Undef){
             conflictC++;
 	     conflicts++; 
         
	  if(conflicts%5000==0 && var_decay<0.95) var_decay += 0.01;
 	  if (verbosity > 0 && conflicts%verbEveryConflicts==0 && (recursiveDepth==0 || conflicts%40000==0)){ 
            printf("c | %g ", cpuTime());//dec_vars
	    if(conflicts) printf(" LBD=%d ", int(sumLBD / conflicts));

            printf("%8d  %7d  %5d  %7d | %7d %8d %8d | %5d %8d   %6d %8d | %6.3f %% |\n", 
		   (int)starts,(int)nbstopsrestarts, (int)(conflicts/starts), (int)conflicts, 
		   (int)nVars() - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
		   (int)nbReduceDB, nLearnts(), (int)nbDL2,(int)nbRemovedClauses, progressEstimate()*100);
	  }
	  if (decisionLevel() == 0) return l_False;
	  
	  trailQueue.push(trail.size());
          if(conflicts-old_conf <2000){
             if( conflicts>LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid()  && trail.size()>R*trailQueue.getavg()) {
	      lbdQueue.fastclear();
	      nbstopsrestarts++;
	      if(!blocked) {lastblockatrestart=starts;nbstopsrestartssame++;blocked=true;}
	     }
           }
           int min_back;
           unsigned int min_nblevels;
           vec<Lit> best_learnt;
           analyze(confl, best_learnt, min_back, min_nblevels);
           cancelUntil(min_back);

           if (certifiedUNSAT) {
               if(best_learnt.size() != 1) printDrupLits(best_learnt, 0, needExtVar);
           }
      
           if (best_learnt.size() == 1){
                    confl = unitPropagation(best_learnt[0]);
                    lbdQueue.push(min_nblevels);
	            sumLBD += min_nblevels;
                    nbUn++;
                    goto nexta;
           }
           else{
                    CRef cr = ca.alloc(best_learnt, true);
        	    
                    ca[cr].setLBD(0x7fffffff);
                
                    if(min_nblevels<=2) nbDL2++; // stats
        	    if(ca[cr].size()==2) {nbBin++;} // stats
              
                    learnts.push(cr);
                    attachClause(cr);
                    claBumpActivity(ca[cr]);
                    uncheckedEnqueue(best_learnt[0], cr);
            }
            varDecayActivity();
            claDecayActivity();
           
            lbdQueue.push(min_nblevels);
	    sumLBD += min_nblevels;
   
        }else{
	  // Our dynamic restart, see the SAT09 competition compagnion paper 
          if(nof_conflicts != -1){
                 if(conflicts > (unsigned)nof_conflicts){
                          cancelUntil(0);
                          return l_Undef;
                  }
          } 

	  if ((conflicts - old_conf > 20000) ||
	      ( lbdQueue.isvalid() && ((lbdQueue.getavg()*K) > (sumLBD / conflicts)))) {
	    lbdQueue.fastclear();
	    progress_estimate = progressEstimate();
	    cancelUntil(0);
	    return l_Undef; }

           // Simplify the set of problem clauses:
	  if (decisionLevel() == 0 && !simplify()) {
	    return l_False;
	  }

          // Perform clause database reduction !
	    if((unsigned)conflicts>= curRestart* (unsigned)nbclausesbeforereduce) 
	      {
	
		assert(learnts.size()>0);
		curRestart = (conflicts/ nbclausesbeforereduce)+1;
		reduceDB();
		nbclausesbeforereduce += incReduceDB;
	      }
//
            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                decisions++;
               // New variable decision:
                next = pickBranchLit();
                if (next == lit_Undef){
	          // Model found:
		   Solver * solver=this;
	           extend_subsolution(solver);
		   return l_True;
		}
            }
          // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

lbool Solver :: singleSolve()
{       recursiveDepth=1000;

        printf("c singleSolve \n");

        for(int j=priorBegin[1], k=priorBegin[2]-1; j<=k; j++,k--){
               for(int i=0; i<2; i++){
                    Lit p=priorityLit[j]; 
                    if(i==0) p=priorityLit[j];
                    else     p = ~priorityLit[k];
                    if(value(var(p)) != l_Undef) continue;
                    Solver* subsolver;
                    lbool ret=run_subsolver(subsolver, p,-1,1);
                    if(ret==l_True) {
                         copyAssign(subsolver);
                         delete subsolver;
                         return l_True;
                    }
                    delete subsolver;
                    if(ret != l_False ) return l_Undef;
                    uncheckedEnqueue(~p);
                    if( propagate() != CRef_Undef ) return l_False;
              }
       }
       recursiveDepth=0;
       return l_Undef;
}

lbool Solver::solve_()
{
    if (verbosity > 0) printf("c :solve_ ...\n");
   
    auxVar=outvars=originVars=nVars();
    longcls=nClauses(); 
   
    if(nClauses() >= 800000 || originVars<=800 || originVars>=10000){
      longcls=longClauses();
    }
    if(nClauses() > 4000000 && longcls < 300000){
          if(probe() == l_False) return l_False;
    }

    int bincls=nClauses()-longcls;
    oldVars=nVars();
    
    if(10000 < originVars && originVars < 20000 && nClauses() < 180000) detect_longImp();
       
    rebuildOrderHeap();
    model.clear();
    conflict.clear();
    if (!ok) return l_False;
 
   lbdQueue.initSize(sizeLBDQueue);
    trailQueue.initSize(sizeTrailQueue);
    sumLBD = 0;
    solves++;
    lbool   status        = l_Undef;
    nbclausesbeforereduce = firstReduceDB;
    verbEveryConflicts=10000;
    if(verbosity > 0 && recursiveDepth==0) {
      printf("c ========================================[ MAGIC CONSTANTS ]==============================================\n");
      printf("c | Constants are supposed to work well together :-)                                                      |\n");
      printf("c | however, if you find better choices, please let us known...                                           |\n");
      printf("c |-------------------------------------------------------------------------------------------------------|\n");
    printf("c |                                |                                |                                     |\n"); 
    printf("c | - Restarts:                    | - Reduce Clause DB:            | - Minimize Asserting:               |\n");
    printf("c |   * LBD Queue    : %6d      |   * First     : %6d         |    * size < %3d                     |\n",lbdQueue.maxSize(),firstReduceDB,lbSizeMinimizingClause);
    printf("c |   * Trail  Queue : %6d      |   * Inc       : %6d         |    * lbd  < %3d                     |\n",trailQueue.maxSize(),incReduceDB,lbLBDMinimizingClause);
    printf("c |   * K            : %6.2f      |   * Special   : %6d         |                                     |\n",K,specialIncReduceDB);
    printf("c |   * R            : %6.2f      |   * Protected :  (lbd)< %2d     |                                     |\n",R,lbLBDFrozenClause);
    printf("c |                                |                                |                                     |\n"); 
printf("c ==================================[ Search Statistics (every %6d conflicts) ]=========================\n",verbEveryConflicts);
      printf("c |                                                                                                       |\n"); 

      printf("c |          RESTARTS           |          ORIGINAL         |              LEARNT              | Progress |\n");
      printf("c |       NB   Blocked  Avg Cfc |    Vars  Clauses Literals |   Red   Learnts    LBD2  Removed |          |\n");
      printf("c =========================================================================================================\n");
    }
    // Search:
    if(priorNum > 80) status = singleSolve();
    else priorNum=0;
   
    if(verbosity>0)  printf("c old_Var#=%d cls#=%d longcls#=%d bincls=%d \n",originVars,nClauses(),longcls,bincls);
   
     int ct=originVars>210000? 120000 :10000;
     bool Thisolver= priorNum || (nClauses() > 1500000) || (originVars>100000 && longcls<10000) || 
           (originVars>50000 && originVars<250000 && nClauses()*2>=3*originVars && longcls>50000 &&
            nClauses()<2*originVars+ct && nClauses()>originVars) ;
    bitVecNo=-1;

    if(status == l_Undef && originVars < 700) {
         int saveCheck=certifiedUNSAT;
         certifiedUNSAT=0;
         status = Lit3find();
         certifiedUNSAT=saveCheck;
    }
    if(status == l_Undef && Thisolver && originVars < 1400000 && nClauses() < 5000000){
         if(nClauses() > 2*originVars && originVars > 100000){
              fast_bcd();
              BCD_conf=30000;
          }
    }
    BCD_delay=0;
    while (status == l_Undef){
         int climit=-1;
         if(originVars>100000 && longcls<10000) bitVecNo++;
         else{
            if(conflicts > 2000000 || conflicts > 300000 && originVars > 1000000) bitVecNo=-1;
            else  bitVecNo++;
         }
         status = search(climit); // the parameter is useless in glucose, kept to allow modifications
         if (!withinBudget()) break;
         if(longcls < 1800000 && int(sumLBD / conflicts) < 5 && bincls>800000) goto midsol; 
         if(Thisolver || originVars > 550000) continue;
midsol: 
         if(originVars>33000 && conflicts < 50000) continue;
         if(verbosity > 0) printf("c mid_simplify and sub_solve conflicts=%d \n",(int)conflicts);
         if(status == l_Undef){
             if(varRange){
                  free(varRange);
                  varRange=0;
                  BCD_conf=500000;
             }
             midsimp_solve(1);//preprocess;
             int rc=midsimp_solve(0);
             if(rc==UNSAT) return l_False;
             if(rc==SAT) status=l_True;
         }
         Thisolver=true;
         bincls=0;
     }

    if (status == l_True){
        // Extend & copy model:
        if(verbosity > 0) printf("c solution found by first solver \n");
       
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
        verify();
        solveEqu(equhead,model);
        return status;
    } else if (status == l_False && conflict.size() == 0) ok = false;

    cancelUntil(0);
    return status;
}

lbool Solver::solve2_()
{
    if(recursiveDepth<3) printf("c Depth=%d \n",recursiveDepth);
  
    originVars=nVars();
    size30=0;
    if(ite2ext == 0) needExtVar=0;
    if(originVars>3200 &&  originVars<3600) XorMark();
   
    BCDfalses=1000;
    BCD_conf=0;
    int mp= (originVars<10000)? 30: 21; 
    if(recursiveDepth==0 && numVarRk<30 && nClauses()< mp*originVars){
         if(originVars > 1600 && originVars < 15000)  BCD_conf=6000001;
         else                                         BCD_conf=500001;
    }

    BCD_delay=0;
    if(BCD_conf){
          if(originVars<4400 || originVars>4700 || nClauses()< 14*originVars){
                fast_bcd();
          }
          else BCD_delay=1;
    }

    model.clear();
    conflict.clear();
    if (!ok) return l_False;
 
    lbdQueue.initSize(sizeLBDQueue);

    trailQueue.initSize(sizeTrailQueue);
    sumLBD = 0;
    
    solves++;
    
    lbool   status        = l_Undef;
    nbclausesbeforereduce = firstReduceDB;
    verbEveryConflicts=10000;
   
    if(certifiedUNSAT == 0 && needExtVar) verbosity=1;
    if(recursiveDepth > 100) verbosity=0;
    bitVecNo=-1;
   
    if(verbosity > 0) printf("c D=%d hard#=%d unsat#=%d unsat9#=%d \n",recursiveDepth,all_conflicts,unsatCnt, unsat9Cnt);
   
    int force=0;
    if(2*unsatCnt>5*unsat9Cnt && recursiveDepth>=9 || recursiveDepth >=11){
          completesolve=1;
          force=1;
    }
    if(certifiedUNSAT && recursiveDepth>=10) completesolve=1;
   
    int sLBD=0;
    int oldfreeVars=nUnfixedVars();
    bitVecNo=-1;
    while (status == l_Undef){
         int climit=conflict_limit;
         if(recursiveDepth==0){
            if((size30>6 && size30 <20) || outvars<500) bitVecNo=-1;
            else{
              if(BCDfalses>30){
                 if(conflicts > 3000000) bitVecNo=-1;
                 else  {          //     bitVecNo++;
                    if(conflicts || outvars>1500) bitVecNo++;
                 }
               }
            }
         }
         else{
             if(recursiveDepth<=9 && conflicts < 30000) bitVecNo++;
             else bitVecNo=-1;

             if(completesolve==1){
                   if(recursiveDepth < 11){
                        if(nVars() < 1400 && progressEstimate()>0.081 && (force || recursiveDepth !=9)) climit=-1;
                        else climit=force ? 600000:50000;
                   }
                   else  climit=-1;
             }
             if(completesolve==0 || cancel_subsolve){
                  if(recursiveDepth < 11) climit=500;
                  else climit=10000;
             }
             if(recursiveDepth > 100) climit=-1;
         }
         if(climit != -1) {
                 if(conflicts >= (unsigned) climit) goto done; 
         }
         status = search(climit);
         if (!withinBudget()) break;
         
         if(BCD_conf>500001){
            if(conflicts>5000 && conflicts<300000 & sumLBD < 6*conflicts && sLBD==0) sLBD=int(sumLBD/conflicts);
            if(conflicts>300000 && sumLBD < 8*conflicts && (sLBD==0 || int(sumLBD/conflicts) <= sLBD)){
                BCD_conf=500001;
            }
         }
         if(BCD_conf){
              if(nClauses()>20*originVars && sumLBD < 10*conflicts && conflicts<1500000) continue;
         }   
//       
         if(recursiveDepth > 1900){
               if(conflicts > 20000){
                   if(status == l_Undef) return l_Undef;
               } 
               continue;
         }   
         if(recursiveDepth > 100){
               if(conflicts > 1500000){
                   if(status == l_Undef) return l_Undef;
               } 
               continue;
         }   
         if(recursiveDepth == 0){

              if(conflicts>200000) {
                    if((oldfreeVars==nUnfixedVars() && sumLBD /7 < conflicts && oldfreeVars<2000) ||
                      40*nUnfixedVars() < outvars || nClauses()>600000 || ((hbrsum>110000 || progressEstimate()>0.011) && conflicts<300000)){

                          if(varRange){
                                free(varRange);
                                if(verbosity > 0) printf("c cancel BCD pick var \n");
                          }
                          varRange=0;
                    } 
              }

              if(nVars() < 1400 && ((nVars()>=nUnfixedVars()+2 && conflicts<1500000) ||conflicts<500000)) continue;
              if(nVars() > 2500 && conflicts<6000000) continue;
              int aLBD=sumLBD/conflicts;
              if(aLBD > 16 || nVars() > 10000 || outvars<500) continue;
              if(nVars() > 1500){
                  if(sumLBD /13 < conflicts){
                         if(conflicts<500000) continue;
                         if(outvars>3000 && conflicts<2000000) continue;
                  }
                    if(conflicts>7000000 || conflicts>3000000 && (aLBD<=10 || nVars() > 3500 && aLBD<=11)) {
                      cancel_subsolve=1; continue;
                  }
               }
         }
         if(status==l_False){
               if(recursiveDepth <= 9) unsat9Cnt++;
               break;
         }

         if(recursiveDepth >= 11 && conflicts > 10000){
               if(all_conflicts> unsatCnt+1200) cancel_subsolve=1;
               if(conflicts > 2500000) cancel_subsolve=1;
        }

        if(recursiveDepth == 0 && cancel_subsolve) continue;
       
        if(completesolve==0){
             if(recursiveDepth==0 && conflicts >= 100000 || recursiveDepth>0 && conflicts >= (unsigned)climit){//9
                if(status == l_Undef) {
                       status=subsolve();
                       if(recursiveDepth==0 && status == l_Undef){
                             completesolve=1;
                             if(!cancel_subsolve) status=subsolve();
                       }
                 }
                 if(recursiveDepth) break;
                 cancel_subsolve=1;
                 continue;
             }
             if(conflicts >= (unsigned)climit) goto done;
             continue;
        }
        if(recursiveDepth >=11 || climit==-1){//13
              if(conflicts < 2500000) continue;
              cancel_subsolve=1;
        }
        if(cancel_subsolve) goto done;
        if(conflicts >= (unsigned)climit){
               if(status == l_Undef)  status=subsolve();
        }
     }

    if (verbosity > 0 && recursiveDepth==0)
      printf("c =========================================================================================================\n");
      if(conflicts > 2500000){
            if(recursiveDepth > 9) cancel_subsolve=1;
      }
      else{
             if(conflicts > 650000) all_conflicts += 60;//100
             else if(conflicts > 230000){
                       int m=conflicts/65000; 
                       all_conflicts += (m*m);
                   }
                   else all_conflicts += ((int)conflicts/80000);
      }
done:
    if (status == l_Undef){
         // buildEquClause();
          cancel_subsolve = 1;
          cancelUntil(0);
          return l_Undef;
    }
    if (status == l_True){
        // Extend & copy model:
        if(verbosity > 0) printf("c solution found depth=%d \n",recursiveDepth);

        solveEqu(equhead,assigns);
        if(recursiveDepth) return status;
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
        return status;
    }

    if(conflict.size() == 0) ok = false;
 
    unsatCnt++;
    return l_False;
}
  
//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("c Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    watchesBin.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
            vec<Watcher>& ws2 = watchesBin[p];
            for (int j = 0; j < ws2.size(); j++)
                ca.reloc(ws2[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

//------------------------------------------------------------------------------

extern float * size_diff;

lbool Solver::dumpClause(vec<CRef>& cs,Solver* fromSolver,Solver* toSolver,int sizelimit) 
{    int i,j;
     vec<Lit> lits;
     for (i =0; i < cs.size(); i++){
                Clause & c = fromSolver->ca[cs[i]];
 		int sz=c.size();
           	if(sz > 6 && sizelimit==2) continue;
		lits.clear();
		for (j = 0; j < sz; j++) {
                        Lit lit=c[j];
			if (toSolver->value(lit) == l_True) break;
   			if (toSolver->value(lit) == l_False) continue;
                        lits.push(lit);	
		}
                if(j<sz) continue;
            	if(sizelimit==2 && lits.size() > 2) continue;
 //add clause   
                if(lits.size()==0) return l_False;
                if(lits.size() == 1){
                       toSolver->uncheckedEnqueue(lits[0]);
                       if(toSolver->propagate() != CRef_Undef ) return l_False;
                }
                else{
                    CRef cr = toSolver->ca.alloc(lits, false);
                    toSolver->clauses.push(cr);
                    toSolver->attachClause(cr);
                }
      }
      return l_Undef;
}

CRef Solver::trypropagate(Lit p)//new idea
{
    newDecisionLevel();
    uncheckedEnqueue(p);
    return propagate();
}    

double *fweight;

inline double Solver::dynamicWeight()
{   double w=0.01;
    for (int c = trail.size()-1; c >= trail_lim[0]; c--) w+=fweight[trail[c].x];
    cancelUntil(0);
    return w;
}

void Solver::LitWeight(vec<CRef>& cs) 
{
   int size=2*nVars()+2;
   fweight=(double *) malloc(sizeof(double) *(size));
   int i, j;
   for( i = 0; i <size; i++ ) fweight[i]=0;
   for (i = 0; i < cs.size(); i++){
            Clause& c = ca[cs[i]];
 	    int sz=c.size()-1;
   	    if(sz>80) continue; 
            for (j = 0; j <= sz; j++) fweight[c[j].x]+=size_diff[sz];
    }
}

lbool Solver :: run_subsolver(Solver* & newsolver, Lit plit, int conf_limit,int fullsolve)
{
        int nV=nVars();
        newsolver=new Solver();

        newsolver->subformuleClause=1;
        newsolver->needExtVar = needExtVar;

        while (nV > newsolver->nVars()) newsolver->newVar();
        newsolver->recursiveDepth=recursiveDepth+1;
       
        for(int i=0; i<nV; i++){
	      if(assigns[i] != l_Undef){
		       Lit lt = (assigns[i] == l_True) ? mkLit(i) : ~mkLit(i);
                       newsolver->uncheckedEnqueue(lt);
               }
        }
      
        if(certifiedUNSAT){
            int lit=toIntLit(plit);
            if(needExtVar) lit=GetextLit (lit);
            treeAuxLit[treeDepth]=0;
            treeExtLit[treeDepth]=-lit;
            treeDepth++;
        } 

        if(value(var(plit)) == l_Undef){
               newsolver->uncheckedEnqueue(plit);
        }
        lbool ret=dumpClause(clauses, this, newsolver, 10000000);
        if(ret == l_False) goto run_end;
        ret=dumpClause(learnts, this, newsolver, 2);
        if(ret == l_False) goto run_end;
        
        if(newsolver->propagate() != CRef_Undef ){
              ret=l_False;
run_end:
              newsolver->init_trailsize=newsolver->trail.size();
              goto run_end2;
        }     
        newsolver->conflict_limit=conf_limit;
        newsolver->completesolve=fullsolve;

        newsolver->init_trailsize=newsolver->trail.size();

        ret=newsolver->solveNoAssump();
run_end2:
        if(certifiedUNSAT){
              if(ret == l_False && treeDepth){
                     vec<Lit> ps;
                     ps.clear();
                     printDrupLits(ps, 0, needExtVar);
                     if( treeDepth>3 ){
                            newsolver->ClearClause(newsolver->learnts, 1);
                            newsolver->ClearUnit();
                     }
              }
              treeDepth--;
        }
        return ret;
}      

void Solver :: ClearClause(vec<CRef>& cs,int deleteflag)
{
    if(certifiedUNSAT && deleteflag && subformuleClause) deleteflag=1;
    else deleteflag=0;
    for (int i = 0; i < cs.size(); i++){
            removeClause(cs[i]);
            if(deleteflag)  printDrupClause(ca[cs[i]], 1, needExtVar);
    }
    cs.clear();
}

int Solver::Out_oneClause(Solver* solver,vec<CRef>& cs,Stack<int> * outClause, int lenLimit,int clause_type) 
{       int i,j,num=0;
	for (i =0; i < cs.size(); i++){
                Clause & c = solver->ca[cs[i]];
 		int sz=c.size();
	   	if(lenLimit==2 && sz>6) continue;
		int k=0;
		for (j = 0; j < sz; j++) {
			if (solver->value(c[j]) == l_True) break;
			if (solver->value(c[j]) == l_False) continue;
			k++;
		}
		if(j<sz) continue;
         	if(lenLimit==2 && k>2) continue;
		outClause->push(((k+1)<<FLAGBIT) | clause_type);
          	for (j = 0; j < sz; j++) {
			Lit p=c[j];
                        if (solver->value(p) == l_False) continue;
	                outClause->push(toIntLit(p));
         	}
                num++;
        }
        return num;
}

int Solver :: Output_All_Clause(Solver* solver)
{   int clause_type;
    if(g_pps->clause==0) {
            clause_type=CNF_CLS; 
            g_pps->clause=new Stack<int>;
    }
    else clause_type=CNF_C_B; 

    int Numclause = Out_oneClause(solver,solver->clauses, g_pps->clause, 1000000, clause_type);
    Numclause += Out_oneClause(solver,solver->learnts, g_pps->clause, 2,       clause_type);
    return Numclause;
}

lbool Solver::dumpClause(Solver* fromSolver, Solver* toSolver)
{
     for(int i=0; i<nVars(); i++){
	    if(toSolver->assigns[i] != l_Undef) continue;
	    if(fromSolver->assigns[i] != l_Undef){
		       Lit lit = (fromSolver->assigns[i] == l_True) ? mkLit(i) : ~mkLit(i);
                       toSolver->uncheckedEnqueue(lit);
            }
      }
  
     lbool ret=dumpClause(fromSolver->clauses, fromSolver, toSolver, 10000000);

     if(ret == l_False) return l_False; 
     return dumpClause(fromSolver->learnts, fromSolver, toSolver, 2);
}      

void Solver::copyAssign(Solver* fromSolver)
{
    for(int i=0; i<nVars(); i++){
	    if(assigns[i] != l_Undef) continue;
	    assigns[i]=fromSolver->assigns[i];
    }    
}

inline void Solver :: simpAddClause(const vec<Lit>& lits)
{
     if(certifiedUNSAT) printDrupLits(lits, 0, needExtVar);
     CRef cr = ca.alloc(lits, false);
     clauses.push(cr);
     attachClause(cr);
}

void Solver :: XorMark()
{   
     g_pps->numVar=nVars();
     OutputClause(g_pps->clause, (int *)0, g_pps->numClause,0);

     int way=2;
     XOR_Preprocess(g_pps,way);
     release_pps (g_pps);
}

lbool Solver :: subsolve()
{       cancelUntil(0);
        g_pps->numVar=nVars();
	OutputClause(g_pps->clause, (int *)0, g_pps->numClause,0);

        int way=1;
        XOR_Preprocess(g_pps,way);

        int Mvar0;
        int rc0=findmaxVar(Mvar0);
        release_pps (g_pps);
        if(rc0 == UNSAT) return l_False;
      
        lbool ret;
        int mvar;
        double maxWeight,diff; //bug
        if( Mvar0 >=0 ){
             mvar=Mvar0;
             goto done;
        }
retry:	
        ret=l_Undef;
        mvar=-1;
        maxWeight=-1;
        LitWeight(clauses);
        for(int i=0; i<numVarRk; i++){
	      int var=extVarRank[i]-1;
	      if(assigns[var] != l_Undef) continue;
         
              Lit p0=~mkLit(var);
              Lit p1=mkLit(var);
              CRef confl0=trypropagate(p0);
              double w0=dynamicWeight();
              CRef confl1=trypropagate(p1);
              double w1=dynamicWeight();
              if (confl0 != CRef_Undef){
                    if (confl1 != CRef_Undef) {ret=l_False; break;}
                    if(value(p1) != l_Undef) continue; 
                    unitPropagation(p1);
                    continue;
              }
              if (confl1 != CRef_Undef){
                    if(value(p0) != l_Undef) continue; 
                    unitPropagation(p0);
                    continue;
              }
              diff=w0*w1;
              if(maxWeight < diff && i<15 || mvar==-1){//15
                     maxWeight = diff;
                     mvar=var;
              }
              if(i>30) break;
        }
        free(fweight); 
        if(ret==l_False) return l_False;
        if(mvar==-1) return l_True;
done:
        if(assigns[mvar] != l_Undef) goto retry;
        
        Solver* subsolver2;
        lbool ret2=run_subsolver(subsolver2, mkLit(mvar),-1,completesolve);
        if(ret2==l_True){
               copyAssign(subsolver2);
               delete subsolver2;
               return l_True;
        }
        delete subsolver2;
        if(ret2==l_Undef){
               cancel_subsolve=1;
               return l_Undef;
        }

        Solver* subsolver1;
        lbool ret1=run_subsolver(subsolver1, ~mkLit(mvar),-1,completesolve);
        if(ret1==l_True) {
                copyAssign(subsolver1);
                delete subsolver1;
                return l_True;
        }
        delete subsolver1;
        if(ret1==l_Undef){
               cancel_subsolve=1;
               return l_Undef;
        }
        return l_False;
}

void Solver::Out_removeClause(vec<CRef>& cs,Stack<int> * & outClause, int & numCls,int lenLimit,int Del) //new idea
{       int i,j,m=0;
	for (i =0; i < cs.size(); i++){
                Clause & c = ca[cs[i]];
 		int sz=c.size();
		int k=0;
		for (j = 0; j < sz; j++) {
			if (value(c[j]) == l_True) break;
			if(g_pps->unit){
                             int vv=var(c[j])+1;
		             if((vv+1)==g_pps->unit[vv]) break;
                        }
			if (value(c[j]) == l_False) continue;
			k++;
		}
		if(j<sz){
			 if(Del) removeClause(cs[i]);
			 continue;
		}
         	if(lenLimit==2 && k>2){
                        if(Del) cs[m++] = cs[i];
  			continue;
		}
		outClause->push(((k+1)<<FLAGBIT) | CNF_CLS);
          	for (j = 0; j < sz; j++) {
			Lit p=c[j];
                        if (value(p) == l_False) continue;
	                outClause->push(toIntLit(p));
         	}
	        if(Del) removeClause(cs[i]);
                numCls++;
	}
        if(Del) cs.shrink(i - m);
}

void Solver :: OutputClause(Stack<int> * & clauseCNF, int *solution, int & numCls,int Del)
{
    if(clauseCNF) delete clauseCNF;
    cancelUntil(0);
	
    if(solution){
       	 for (int i = nVars()-1; i >=0 ; i--){
		 if(solution[i+1]) continue;
		 if (assigns[i] != l_Undef){
                        if(assigns[i]==l_True) solution[i+1]=i+1;
			else                   solution[i+1]=-(i+1);
		 }
	 }
    }

    clauseCNF=new Stack<int>; 
    numCls=0;

    Out_removeClause(clauses, clauseCNF, numCls,10000000,Del); //new idea
    Out_removeClause(learnts, clauseCNF, numCls,2,Del);
}

void extend_unit_solution(Solver * solver)
{    int i;

     if(solver->g_pps->unit==0) solver->g_pps->unit=(int *) calloc (solver->originVars+1, sizeof (int));
     int *unit=solver->g_pps->unit;
     for (i = 0; i <solver->originVars; i++){
	   if(unit[i+1]){
		   if(unit[i+1]==i+2) unit[i+1]=0; //bug x=y ^ x=0 ^ y=0
		   continue;
	    }
	    if (solver->assigns[i] != l_Undef){
                  if(solver->assigns[i]==l_True) unit[i+1]=i+1;
		  else unit[i+1]=-(i+1);
	     }
      }
      extend_solution(solver->g_pps);
}

void Solver:: extend_subsolution( Solver * sub_solver)
{
         int i, nV=originVars;
	 int *unit;
	 if(sub_solver){
		 extend_unit_solution(sub_solver);
                 unit=sub_solver->g_pps->unit;
	 }
	 else unit=g_pps->unit;
	 for (i = 1; i <= nV; i++){
	      if(unit[i]==i) assigns[i-1]=l_True;
              if(unit[i]==-i) assigns[i-1]=l_False;
	 }
}

//------------------------------------------------------
typedef struct SPF SPF;
SPF * s_init (void);
void s_release (SPF *);
int s_maxVar (SPF *);
void s_add (SPF *, int lit);
int s_ideref (SPF * spf, int elit);

void onlymidSimplify (SPF * spf); 
int midprep_solve (SPF * spf);

int Solver :: midsimp_solve(int isPreprocess)
{    int i,j;

     cancelUntil(0);
     mainSolver=this;
     SPF * simp_solver = s_init ();
     vec<int> lits;
     for (i =0; i < clauses.size(); i++){
           Clause & c = ca[clauses[i]];
 	   int sz=c.size();
	   for (j = 0; j < sz; j++) {
		if (value(c[j]) == l_True) break;
		if (value(c[j]) == l_False) continue;
	   } 
	   if(j<sz) continue;
           lits.clear();
           for (j = 0; j < sz; j++) {
		Lit p=c[j];
                if (value(p) == l_False) continue;
                int lit=toIntLit(p);
                s_add (simp_solver, lit);
                lits.push(lit);
	   }
           if(!isPreprocess) add_2type_clause(lits,CNF_CLS);
           s_add(simp_solver, 0); //close a clause 
      }

     for (i =0; i < learnts.size(); i++){
           Clause & c = ca[learnts[i]];
 	   int sz=c.size();
           int k=0;
	   for (j = 0; j < sz; j++) {
		if (value(c[j]) == l_True) break;
		if (value(c[j]) == l_False) continue;
                k++;
	   } 
	   if(j<sz || k!=2) continue;
           lits.clear();
           for (j = 0; j < sz; j++) {
		Lit p=c[j];
                if (value(p) == l_False) continue;
                int lit=toIntLit(p);
                s_add (simp_solver, lit);
                lits.push(lit);
	   }
           if(!isPreprocess) add_2type_clause(lits,CNF_CLS);
           s_add(simp_solver, 0); 
      }

      if(isPreprocess){
              onlymidSimplify (simp_solver);
              s_release (simp_solver);
              return _UNKNOWN;
      }

      int res = midprep_solve(simp_solver);
//result:
      if(res==10) {
             int  maxvar = s_maxVar (simp_solver);
             for (i = 1; i <= maxvar; i++) {
                 if(assigns[i-1]!=l_Undef) continue;
	         int lit = (s_ideref (simp_solver, i) > 0) ? i : -i;
	         if(lit==i) assigns[i-1]=l_True;
                 else       assigns[i-1]=l_False;
             }
             s_release (simp_solver);
             return SAT;
      }
      s_release (simp_solver);
      if(res==0) return _UNKNOWN;
      return UNSAT;//res=20
}

//--------------------------------------------------------
//look both by an iterative uint propagation
int Solver :: IterativeUnitPropagation(int lit0, int * Queue, float *diff,int *unit,int *pre_unit)
{   int i,ForcedLit=0;
    int lt,var,sp,sp1;
    int rc=_UNKNOWN;
    PPS *pps = g_pps;
    Stack<int> * clause=pps->clause;
    Stack<int> * occCls=pps->occCls;
    Queue[0]=unit[ABS(lit0)]=lit0;
    Lit pp0 = mkLit(ABS(lit0)-1);

    sp1=0; sp=1;*diff=1;
    while(sp1<sp){
	    lt=Queue[sp1++];
	    int numocc = occCls[-lt];
	    for (i = 0; i < numocc; i++) {
		 int cpos=occCls[-lt][i];
                 int len=(*clause)[cpos];
		 int mark=len & MARKBIT;
                 if(mark!=CNF_CLS) continue;
	   	 len=len>>FLAGBIT;
 		 int *clsp=&(*clause)[cpos];
		 int *lits=clsp+1;
                 clsp+=len;
		 int m=0;
                 for (; lits<clsp; lits++){
			 var=ABS(*lits); 
			 if(unit[var]==*lits) goto nextC;
                      
                         int iVar=var-1;
                         if(assigns[iVar] != l_Undef){
                                if( (*lits > 0) && (assigns[iVar] == l_True)) goto nextC;  
                                if( (*lits < 0) && (assigns[iVar] == l_False)) goto nextC;  
                                continue;
			 }
                         
                         if(unit[var]==0) {m++; ForcedLit=*lits;}
		  }
		  if(m==0) {rc=UNSAT; goto ret;}; //conflict
		  if(m==1) {
                          int fvar=ABS(ForcedLit);
			  Queue[sp++]=unit[fvar]=ForcedLit;
                         
                           if(pre_unit){
                               if(unit[fvar]==pre_unit[fvar]){
	                          int iVar=fvar-1;
                                  if(assigns[iVar] != l_Undef) continue;
                  	          Lit ulit=(unit[fvar] > 0) ? mkLit(iVar) : ~mkLit(iVar);
                                 // uncheckedEnqueue(ulit);
                                 // CRef confl = propagate();
                                 if(!addbinclause(pp0,  ulit)) continue;
                                 if(!addbinclause(~pp0, ulit)) continue;
                                 CRef confl = unitPropagation(ulit);
                                 if (confl != CRef_Undef) {Queue[sp]=0; return UNSAT;} 
                             }
                          }
                        
		  }
		  else{
			 if(m<100) (*diff)+=size_diff[m];
		  }
nextC:          ;
		}
      }
ret:
//     for(i=0; i<sp; i++) unit[ABS(Queue[i])]=0;
     Queue[sp]=0;
     return rc;
}

void setDoubleDataIndex(PPS *pps, bool add_delcls);
void clear_unit(int *Queue,int *unit)
{    
     for(int i=0; Queue[i]; i++) unit[ABS(Queue[i])]=0;
}

int Solver :: findmaxVar(int & Mvar)
{   	
    setDoubleDataIndex(g_pps,false);
    if(g_pps->unit){
           free(g_pps->unit);
           g_pps->unit=0;
    } 
    int *Queue0=(int *)calloc (4*g_pps->numVar+4, sizeof (int));
    int *Queue1=Queue0 + g_pps->numVar+1;
    int *unit0=Queue1 + g_pps->numVar+1;
    int *unit1=unit0 + g_pps->numVar+1;
    float diff1,diff2;
    double maxW=-1,diff; //bug float 2017.7.4
    double df[101];
    Mvar=-1;
    for(int i=0; i<numVarRk && i < 100; i++){
 	     int eVar=extVarRank[i];
	     if(assigns[eVar-1] != l_Undef) continue;
             int rc1=IterativeUnitPropagation(eVar,  Queue0, &diff1, unit0, (int *)0);
	     int rc2=IterativeUnitPropagation(-eVar, Queue1, &diff2, unit1, unit0);
             clear_unit(Queue0,unit0);
             clear_unit(Queue1,unit1);
             CRef confl = CRef_Undef;
             if(rc1==UNSAT){
		  Lit p = ~mkLit(eVar-1); // ~eVar
                  confl = unitPropagation(p);
                  if(rc2==UNSAT) {
                        free(Queue0); 
                        return UNSAT;
                  }
             }
	     else{
        	  if(rc2==UNSAT){
                       Lit p = mkLit(eVar-1); // eVar
                       if(value(p) == l_Undef){
                          confl = unitPropagation(p);
                      }
                  }
             }
             if (confl != CRef_Undef) {
                     free(Queue0); 
                     return UNSAT;
             }
             if(rc1==UNSAT || rc2==UNSAT) continue;
	     diff=df[i]=diff1*diff2;
	     if(diff>maxW){
		       maxW=diff;
		       Mvar=eVar;
	      }
	}
        if(Mvar>0 && assigns[Mvar-1] != l_Undef) {
      //  if(Mvar>0 && nVars() <= 2500 && assigns[Mvar-1] != l_Undef) {
             maxW=-1; Mvar=-1;
	     for(int i=0; i<numVarRk && i < 100; i++){
                  int eV=extVarRank[i];
	          if(assigns[eV-1] != l_Undef) continue;
                  if(df[i]>maxW){ maxW=df[i]; Mvar=eV;}
             }
        }
	Mvar--;
        free(Queue0);
	return _UNKNOWN;
}

void Solver :: verify()
{
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            printf("c {");
            for (int j = 0; j < c.size(); j++){
               if(sign(c[j])) printf("-");
               printf("%d", var(c[j])+1);
               if(value(c[i]) == l_True) printf(":1 ");
               else printf(":0 ");
            }
            printf(" }\n");
            exit(0);
        }
   
    if (verbosity > 0) printf("c verified by abcdSAT \n");
}

// a bin clasue exists?
bool Solver::hasBin(Lit p, Lit q)
{
    vec<Watcher>&  wbin  = watchesBin[~p];
    for(int k = 0;k<wbin.size();k++) {
	  Lit imp = wbin[k].blocker;
	  if( imp == q) return true;
    }
    return false;
}	  

inline void Solver::setmark(vec<int> & liftlit)
{   liftlit.clear();
    for (int c = trail.size()-1; c >= trail_lim[0]; c--) {
            int lit=toInt(trail[c]);
            mark[lit]=1;
            liftlit.push(lit);
    }
    cancelUntil(0);
}

inline void Solver::clearmark(vec<int> & liftlit)
{
     for (int i =0; i < liftlit.size(); i++) mark[liftlit[i]]=0;
}

lbool Solver:: addequ(Lit p, Lit q)
{ 
    if(var(p) < var(q)){
         Lit t=p;  p=q;  q=t;
    }
    int pl=toIntLit(p);
    int ql=toIntLit(q);
 
    if(pl == ql)  return l_Undef;
    if(pl == -ql) return l_False;

    touchVar.push(var(p));
    touchVar.push(var(q));
 
    if(pl<0){ pl=-pl; ql=-ql; }
    int qv=ABS(ql);
    if(equhead[pl] == equhead[qv]){
        if(equhead[pl] == 0){
           equhead[pl]=ql; equhead[qv]=qv;
           equlink[qv]=pl;
           equsum++;
           return l_Undef;
        }
        if(ql < 0) return l_False;
        return l_Undef;
    }
    if(equhead[pl] == -equhead[qv]){
        if(ql < 0) return l_Undef;
        return l_False;
    }
    equsum++;
    if(equhead[pl] == 0 && equhead[qv]){
        if(ql < 0) equhead[pl]=-equhead[qv];
        else equhead[pl]=equhead[qv];
        int h=ABS(equhead[pl]);
        int t = equlink[h];
        equlink[h]=pl;
        equlink[pl]=t;
        return l_Undef;
    }
    if(equhead[pl] && equhead[qv]==0){
        if(ql < 0) equhead[qv]=-equhead[pl];
        else equhead[qv]=equhead[pl];
        int h=ABS(equhead[qv]);
        int t = equlink[h];
        equlink[h]=qv;
        equlink[qv]=t;
        return l_Undef;
    }
//merge
    int x=equhead[pl];
    int y=equhead[qv];
    if(ql < 0) y=-y;
    int next=ABS(y);
    while(1){
         if(equhead[next]==y) equhead[next]=x;
         else  equhead[next]=-x;
         if(equlink[next]==0) break;
         next=equlink[next];
    }    
    int xh=ABS(x);
    int t=equlink[xh];
    equlink[xh]=ABS(y);
    equlink[next]=t;
    return l_Undef;
}

void Solver:: buildEquClause()
{   vec<Lit> lits;
    if(equhead==0) return;
 
    if(dummyVar == 0)  dummyVar = (char * ) calloc (nVars()+1, sizeof(char));
    
    for (int i=1; i <= nVars(); i++){
         if(equhead[i]==0 || equhead[i]==i || dummyVar[i]) continue;
         Lit p=mkLit(i-1);
         int lit=equhead[i];
         dummyVar[i]=1;
         Lit q = (lit>0) ? mkLit(lit-1) : ~mkLit(-lit-1);
         if( !hasBin(p, ~q) ) {
                lits.clear();
                lits.push(p);
                lits.push(~q);
                if(certifiedUNSAT) printDrupLits(lits, 0, needExtVar);
                else   simpAddClause(lits);
         }
         if(!hasBin(~p, q) ) {
                lits.clear();
                lits.push(~p);
                lits.push(q);
                if(certifiedUNSAT) printDrupLits(lits, 0, needExtVar);
                else   simpAddClause(lits);
         }
    }
}


void Solver:: solveEqu(int *equRepr, vec<lbool> & Amodel)
{   
   if(equRepr==0) return;
   if (verbosity > 0) printf("c solve Equ Vn=%d \n",originVars);
   for (int i=1; i <= originVars; i++){
         if(equRepr[i]==0 || equRepr[i]==i) continue;
         int v=equRepr[i];
         v=ABS(v)-1;
         Amodel[i-1] = l_False;
         if (Amodel[v] == l_Undef) Amodel[v] = l_True;
         if (Amodel[v] == l_True){
                   if(equRepr[i] > 0) Amodel[i-1] = l_True;
         }
         else      if(equRepr[i] < 0) Amodel[i-1] = l_True;
    }
}

//hyper bin resol
lbool Solver:: simpleprobehbr (Clause & c)
{   vec<int> ostack;
    vec<Lit> lits;
    ostack.clear();
    CRef confl= CRef_Undef;
    int sum=0,cnt=0;
    int maxcount=0;
    lbool ret=l_Undef;

    for (int i =0; i < 3; i++){
        Lit lit=c[i];
        vec<Watcher>&  bin  = watchesBin[lit];
        if(bin.size()) cnt++;
    }
    if(cnt <= 1) goto done;
    for (int i =0; i < 3; i++){
        Lit lit=c[i];
        int litint=toInt(lit);
        sum += litint;
        vec<Watcher>&  bin  = watchesBin[lit];
        for(int k = 0;k<bin.size();k++) {
	      Lit other = bin[k].blocker;
              int oint = toInt(other);
              if(mark[oint]) continue;
              int nother = oint^1;
              if(mark[nother]) {//unit
                    if(value(lit) != l_Undef) goto done;
                   // uncheckedEnqueue(~lit);
                   // confl=propagate();
                    confl = unitPropagation(~lit);
                    goto done;
              }
              count[oint]++;
              if(maxcount < count[oint]) maxcount = count[oint];
              litsum[oint] += litint;
              mark[oint] =1;
              ostack.push(oint);
       }
       for(int k = 0;k<bin.size();k++) {
 	    Lit other = bin[k].blocker;
            mark[toInt(other)]= 0;
       }
   }
   if(maxcount < 2 ) goto done;
   for (int i =0; i < ostack.size(); i++){
           int oint=ostack[i];
           if(count[oint]<=1) continue;
           Lit other = toLit(oint);
           if(count[oint]==3){//unit
                  if(value(other) != l_Undef) continue; //bug 2016.3.9
                  //uncheckedEnqueue(other);
                 // confl=propagate();
                  confl = unitPropagation(other);
                  if (confl != CRef_Undef) goto done;
                  continue;
           }
           int litint = sum - litsum[oint];
           Lit lit = toLit(litint);
           if(other == lit) {//unit
                  if(value(other) != l_Undef) continue; 
              //    uncheckedEnqueue(other);
               //   confl=propagate();
                  confl = unitPropagation(other);
                  if (confl != CRef_Undef) goto done;
                  continue;
           }
           if(other == (~lit)) continue;
           if(hasBin(other, lit)) continue;

           hbrsum++;
           lits.clear();
           lits.push(other);
           lits.push(lit);

           simpAddClause(lits); //add <other, lit>
         
           if(hasBin(~other, ~lit)){//other=~lit
                   ret=addequ(other, ~lit);
                   if(ret == l_False){
                         if(certifiedUNSAT) printDrupUnit(other,needExtVar);
                         goto done;
                   }
           }
           else{
                   touchVar.push(var(other));
                   touchVar.push(var(lit));
           }               
  }              
done:
  for (int i =0; i < ostack.size(); i++){
        int oint=ostack[i];
        count[oint]=litsum[oint]=0;
        mark[oint]=0;
  }     
  if (confl != CRef_Undef) return l_False;
  return ret;
}

lbool Solver::removeEqVar(vec<CRef>& cls, bool learntflag)
{
    vec<Lit> newCls;
    int i, j,k,n;

    lbool ret=l_Undef;
  
    for (i = j = 0; i < cls.size(); i++){
        if(ret!=l_Undef){
            cls[j++] = cls[i];
            continue;
        }
      
        Clause& c = ca[cls[i]];
        newCls.clear();

        int T=0;
        int del=0;
        for (k = 0; k < c.size(); k++){
             Lit p=c[k];
             if (value(p) == l_True) {
                    del=T=1; 
                    break;
             }
             if (value(p) == l_False){
                     del=1; 
                     continue;
             }
             int v = var(p)+1;
             Lit q;
             if(equhead[v]==0 || equhead[v]==v) q=p;
             else{ int lit;
                 if(sign(p)) lit = -equhead[v];
                 else        lit = equhead[v];
                 q = (lit>0) ? mkLit(lit-1) : ~mkLit(-lit-1);
                 del=1;
            }
             if(del){
                for(n=newCls.size()-1; n>=0; n--){
                   if( q  == newCls[n]) break;
                   if( ~q == newCls[n]) {T=1; break;}
                }
             }
             else n=-1;
             if(T) break;
             if(n<0) newCls.push(q);
        }

       if(del==0){
            cls[j++] = cls[i];
            continue;
       }
       if(T){
           removeClause(cls[i]);
           continue;
       }
       if(newCls.size()<3){
          for (k = 0; k < newCls.size(); k++) touchMark[var(newCls[k])]=1;
       }
       if(newCls.size()==0){
              cls[j++] = cls[i];
              ret=l_False;
              continue;
       }
       if(newCls.size()==1){
              cls[j++] = cls[i];
              if( unitPropagation(newCls[0]) != CRef_Undef ) ret=l_False;
              unitsum++;
              continue;
       }
       if(certifiedUNSAT) printDrupLits(newCls, 0, needExtVar);
       removeClause(cls[i]);
       if(certifiedUNSAT && learntflag) printDrupClause(c, 1, needExtVar);
       CRef cr = ca.alloc(newCls, learntflag);
       attachClause(cr);
       cls[j++] = cr;
    }
    cls.shrink(i - j);
    checkGarbage();
    return ret; 
}

bool Solver:: addbinclause(Lit p, Lit q)
{
      if(hasBin(p,q)) return true;
      vec<Lit> ps;
      ps.clear();
      ps.push(p);
      ps.push(q);
      if(is_conflict(ps)){
           if(certifiedUNSAT) printDrupLits(ps, 0, needExtVar);
           CRef cr = ca.alloc(ps, false);
           clauses.push(cr);
           attachClause(cr);
           return true;
      }
      return false;
}

bool Solver:: out_binclause(Lit p, Lit q)
{
      if(hasBin(p,q)) return true;
      vec<Lit> ps;
      ps.clear();
      ps.push(p);
      ps.push(q);
      if(is_conflict(ps)){
           if(certifiedUNSAT) printDrupLits(ps, 0, needExtVar);
           return true;
      }
      return false;
}

lbool Solver::probeaux()
{    
     int old_equsum = equsum;
     for (int i = 0; i<clauses.size() && i<400000; i++){
           Clause & c = ca[clauses[i]];
 	   int sz=c.size();
           if(sz!=3) continue;
	   int tcnt=0;
           for (int j = 0; j < sz; j++) {
                tcnt += touchMark[var(c[j])];
                if(value(c[j]) != l_Undef) goto next;
           }
           if(tcnt < 2) continue;
           if(simpleprobehbr (c) == l_False) return l_False;
next:      ;
     }
//lift
    vec<int> liftlit;
    vec<int> unit;
    int liftcnt;
    if(probeSum) liftcnt = nVars()/2;
    else liftcnt=10000;

    for(int vv=0; vv<nVars() && liftcnt > 0; vv++){
	     if(touchMark[vv]==0) continue;
             if(assigns[vv] != l_Undef) continue;
             if(equhead[vv+1] && ABS(equhead[vv+1]) <= vv) continue;

            Lit p = mkLit(vv);
            int pos=watchesBin[p].size();
            int neg=watchesBin[~p].size();

            if(pos==0 || neg==0) continue;
            liftcnt--;
            if(pos < neg) p=~p;
            CRef confl=trypropagate(p);
            if (confl != CRef_Undef){
                    cancelUntil(0);
                    if(value(p) != l_Undef) continue; 
                    confl=unitPropagation(~p);
                    if (confl != CRef_Undef) return l_False;
                    unitsum++;
                    continue;
            }
            setmark(liftlit);
            confl=trypropagate(~p);
            if (confl != CRef_Undef){
                    cancelUntil(0);
                    clearmark(liftlit);
                    if(value(p) != l_Undef) continue;
                    unitPropagation(p);
                    unitsum++;
                    continue;
            }
            unit.clear();
            vec<Lit> eqLit;
            eqLit.clear();
            for (int c = trail.size()-1; c > trail_lim[0]; c--) {//not contain p
                 int lit=toInt(trail[c]);
                 if(mark[lit]) unit.push(lit);
                 else{
                      if(mark[lit^1]) {//equ p=~lit
                          Lit q = ~trail[c];//~toLit(lit); 
                          eqLit.push(q);
                          unit.push(lit);
                       }
                 }
             }
            clearmark(liftlit);
            cancelUntil(0);
//p=q
             for (int i =0; i< eqLit.size(); i++) {
                     Lit q=eqLit[i];
                     if(certifiedUNSAT){
                     //        if(!addbinclause(p,  ~q)) continue;
                             if(!out_binclause(p,  ~q)) continue;
                             if(!out_binclause(~p, q) )  continue;
                     }
                     lbool ret=addequ(p,q);
                      if(ret == l_False){
                            if(certifiedUNSAT) printDrupUnit(p,needExtVar);
                            return l_False;
                      }
            }
//unit  
            for (int i =0; i < unit.size(); i++){
                  int lit=unit[i];
              	  Lit uLit=toLit(lit);
	          if(value(uLit) != l_Undef) continue;
                  if(!addbinclause(p,  uLit)) continue;
                  if(!addbinclause(~p, uLit)) continue;
                  confl=unitPropagation(uLit);
                  if (confl != CRef_Undef) return l_False;
                  unitsum++;
            }
   }
  
   for (int i =0; i < nVars(); i++) {
         touchMark[i]=0;
//new idea
         int exv=i+1;
         if(equhead[exv]==0 || equhead[exv]==exv) continue;
         decision[i]=1;
   }
  
   for (int i =0; i < touchVar.size(); i++) touchMark[touchVar[i]]=1;
  
   if(certifiedUNSAT && treeDepth>3) return l_Undef;

   if(old_equsum != equsum){
        if(certifiedUNSAT) buildEquClause();
         lbool ret=removeEqVar(clauses, false);
         if(ret == l_False) return l_False;
         ret=removeEqVar(learnts, true);
         return ret;
   }
   return l_Undef;
}

lbool Solver::probe()
{    
     lbool ret=l_Undef;
     count = (int* ) calloc (2*nVars()+1, sizeof(int));
     litsum = (int* ) calloc (2*nVars()+1, sizeof(int));
     mark = (char * ) calloc (2*nVars()+1, sizeof(char));
     if(equhead == 0) equhead = (int * ) calloc (nVars()+1, sizeof(int));
     if(equlink == 0) equlink = (int * ) calloc (nVars()+1, sizeof(int));
     touchMark = (char *) malloc(sizeof(char) * (nVars()+1));

     for (int i =0; i < nVars(); i++)  touchMark[i]=1;
     int nC=nClauses();
     nC += (nC/2);
     int m=0;
     if(hbrsum > 1000 && conflicts>5000000 || (recursiveDepth && conflicts>300000)) goto noprobe;
     while(hbrsum<nC){
          m++;
          touchVar.clear();
          int oldhbr=hbrsum;
          int oldequ=equsum;
          int olduni=unitsum;
          ret=probeaux();
          if(ret == l_False) break;
          if(recursiveDepth || probeSum>3 || conflicts>100000 && m>25000) break;        
          if(oldhbr==hbrsum && oldequ==equsum && olduni==unitsum) break;
      }
noprobe:
     if(verbosity>0) printf("c hyper bin resol#=%d equ#=%d uni#=%d \n",  hbrsum,equsum,unitsum);
    
     touchVar.clear();
     free(count);
     free(litsum);
     free(mark);
     free(touchMark);

     probeSum++;
     return ret;
}

void Solver:: detect_longImp()
{   vec<int> deep;
    vec<int> prvPos;
    cancelUntil(0);
    int inVars=nVars();
    mark = (char * ) calloc (inVars, sizeof(char));
    priorNum=0;
    for(int vv=0; vv<inVars; vv++){
	    if(assigns[vv] != l_Undef) continue;
	    if(mark[vv]) continue;
            Lit p = mkLit(vv);
            int pos=watchesBin[p].size();
            int neg=watchesBin[~p].size();
            if(pos && neg) continue;
            if(neg) p=~p;
            deep.clear();
            prvPos.clear();
            deepropagate(deep,prvPos,p);
            int dp=trail.size()-trail_lim[0]-1;
            if(deep[dp]>100){
               Lit prv=trail.last();
               int begin=priorityLit.size();
               if(priorNum<100) priorBegin[priorNum++]=begin; 

               priorityLit.push(prv);
               mark[var(prv)]=1;
               for (int c =trail.size()-1; ; ) {
                    c=prvPos[c-trail_lim[0]];
                    Lit q=trail[c];
                    priorityLit.push(q);
                    mark[var(q)]=1;
                    if(c <= trail_lim[0]) break;
               }
               priorBegin[priorNum]=priorityLit.size();
               for (int i= begin, j=priorityLit.size()-1; i<j; i++,j--) {
                    Lit q=priorityLit[i];
                    priorityLit[i]=priorityLit[j];
                    priorityLit[j]=q;
                }
            }
            cancelUntil(0);
     }

     free(mark);
     mark=0;
}

// local search
lbool Solver:: Lit3find()
{   int i,j,k; 
    int tsize[50][2];

    recursiveDepth=2000;

    mark = (char *) malloc(sizeof(char)*nVars());
    for (i = 0; i < nVars(); i++) mark[i]=2;
    for (i = 0; i < clauses.size(); i++){
          Clause & c = ca[clauses[i]];
          if(c.size()>2) continue;
          for (j = 0; j < c.size(); j++) mark[var(c[j])]=sign(c[j]);
    }
    for (i = 0; i < nVars(); i++) if(mark[i]==2) return l_Undef; 

    CRef confl;
    int n,m,s1,s2,s;
    for (i = 2; i < 27; i++){
          if((i>6 && i<19) || (i>20 && i<26)) continue;
          if(value(i) != l_Undef) continue;
          mark[i]=1-mark[i];
          confl=trypropagate(mkLit(i,mark[i]));
          if (confl != CRef_Undef) goto nexti;
          for (j = 19; j < 72; j++){
              if(j<=i || (j>=20 && j<=25) || j>=30 && j<50 || j>=55 && j<69) continue;
              if(value(j) != l_Undef) continue;
              mark[j]=1-mark[j];
              confl=trypropagate(mkLit(j,mark[j]));
              if (confl != CRef_Undef) goto nextj;
              for (k = 46; k < 78; k++){
                    if(k<=j || (k>=60 && k<=70)) continue;
                    if(value(k) != l_Undef) continue;
                    mark[k]=1-mark[k];
                    confl=trypropagate(mkLit(k,mark[k]));
                    if (confl != CRef_Undef) goto nextk;
                    s=0;
                    for (m = 51; m < 84; m++){
                        if(m<=k || (m>=54 && m<=72)) continue;
                        if(value(m) != l_Undef) continue;
                        mark[m]=1-mark[m];
                        confl=trypropagate(mkLit(m,mark[m]));
                        if (confl != CRef_Undef) goto nextm;
                   
                        for(n=s; n>=1; n--){
                           if(trail.size()<=tsize[n-1][0]) break;
                           tsize[n][0]=tsize[n-1][0];
                           tsize[n][1]=tsize[n-1][1];
                        }
                        tsize[n][0]=trail.size();
                        tsize[n][1]=m;
                        s++;
                     nextm:
                        cancelUntil(3);
                        mark[m]=1-mark[m];
                    }
                     
                    if(s>=15){s1=s-4; s2=6;}
                    else{
                          s1=s/2+2;
                          if(s1>=s) s1=s-1;
                          s2=s/2-2;
                          if(s2<0) s2=0;
                          if(s>=5 && s<=8){s1=s-1; s2=2;}
                    }
                    for (s--; s>=0; s--){
                         m=tsize[s][1];
                         mark[m]=1-mark[m];
                         Lit p=mkLit(m,mark[m]);
                         trypropagate(p);
                           Solver* subsolver;
                           lbool ret=run_subsolver(subsolver, p,-1,1);
                           if(ret==l_True) {
                              copyAssign(subsolver);
                              delete subsolver;
                              return l_True;
                           }
                           delete subsolver;

                         cancelUntil(3);
                         mark[m]=1-mark[m];
                    }
              nextk:
                    cancelUntil(2);
                    mark[k]=1-mark[k];
               }
          nextj:
               cancelUntil(1);
               mark[j]=1-mark[j];
          }
nexti:   
          cancelUntil(0);
          mark[i]=1-mark[i];
    }
    free(mark);
    mark=0;
    recursiveDepth=0;
    return l_Undef; 
}

extern int nVarsB;
extern int sumLit;
void MixBCD(int pure_mode); 

void Solver :: varOrderbyClause()
{  
   int rng=5;
   for (Var v = 0; v < originVars; v++) varRange[v]=0;    
   for (int i = 0; i < nClausesB-5; i++){
      if(Bclauses[i][2]==0) continue;
      int *plit = Bclauses[i];
      int v=ABS(*plit)-1;
      if(varRange[v]==0){
          varRange[v]=i;
          if(varRange[v]<rng) varRange[v]=rng;
      }
   }
   for (int i = 0; i < nClausesB-5; i++){
      if(Bclauses[i][2]) continue;
      int *plit = Bclauses[i];
      int v=ABS(*plit)-1;
      if(varRange[v]==0){
          varRange[v]=i;
          if(varRange[v]<rng) varRange[v]=rng;
      }
   }
}

int Solver :: longClauses()
{  int cnt=0;
   for (int i = clauses.size()-1; i >= 0; i--){
      Clause& c = ca[clauses[i]];
      if(c.size()>2) cnt++;
   }
   return cnt;
}
 
void Solver :: fast_bcd()
{  
   nVarsB = nVars();
   if( nVarsB < 60 || varRange) return;
   nClausesB=clauses.size();
   sumLit=0;   
   for (int i = 0; i < nClausesB; i++){
      Clause& c = ca[clauses[i]];
      sumLit += c.size() + 1;
   }
   Bclauses = (int**) malloc(sizeof(int*) * (nClausesB+1));
   Bclauses[0] = (int*) malloc (sizeof(int)*sumLit);
   int j; 
   for (int i = 0; i < nClausesB; i++){
      Clause& c = ca[clauses[i]];
      for (j = 0; j < c.size(); j++){
           Bclauses[i][j] = toIntLit(c[j]);
      }
      Bclauses[i][j]=0;
      Bclauses[i+1] = Bclauses[i] +j+1;
  }
  MixBCD(0);

  varRange = (int* )calloc (nVars(), sizeof(int));
  varOrderbyClause();
}


