/***************************************************************************************[mid_simp_solver.cc]
abcdSAT -- intermediate simplification:lift, probe, block,distill,eliminate, 
            hyper binary resolve, hidden tautology etc  
***************************************************************************************/
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <core/D_Constants.h>
#include "core/Constants.h"
#include "core/Solver.h"

typedef struct SPF SPF;
int * ite2ext=0;
int drup_add=0;

using namespace abcdSAT;

void add_2type_clause(vec<int> & lits,int clause_type);
bool isConflict(int *clause,int len);

static int lit_sign (int lit) { return (lit < 0) ? -1 : 1; }
//------------------------------------------------------
typedef struct Opt {
  char shrt;
  const char * lng, * descrp;
  int val, min, max;
} Opt;

typedef struct Opts {
  Opt block;
  Opt blkclslim;
  Opt blkmaxeff;
  Opt blkmineff;
  Opt blkreleff;
  Opt blkocclim;

  Opt dstmaxeff;
  Opt dstmineff;
  Opt dstreleff;

  Opt elim;
  Opt elmclslim;
  Opt elmhte;
  Opt elmhtelim;
  Opt elmaxeff;
  Opt elmineff;
  Opt elmreleff;
  Opt elmreslim;
  Opt elmocclim;
  Opt elmnostr;

  Opt hlamaxlim;
  Opt hlaliminc;
  Opt hlaminlim;
  
  Opt hte;
  Opt htered;
  Opt htemaxeff;
  Opt htemineff;
  Opt htereleff;
  Opt lhbr;

  Opt lftmaxeff;
  Opt lftmineff;
  Opt lftreleff;

  Opt probe;
  Opt prbmaxeff;
  Opt prbmineff;
  Opt prbreleff;

  Opt seed;
  Opt smallvevars;
  Opt smallve;
  Opt randecint;
 
  Opt syncint;
  Opt termint;

  Opt trdmineff;
  Opt trdmaxeff;
  Opt trdreleff;

  Opt unhdextstamp;
  Opt unhdmaxeff;
  Opt unhdmineff;
  Opt unhdreleff;
  Opt unhdlnpr;
  Opt unhdroundlim;
  Opt unhdhbr;
} Opts;

typedef struct Stats 
{ int64_t prgss;
  struct { int64_t simp;} props, visits;
  struct { size_t current, max; } bytes;
  struct { int current, sum;} fixed, equiv;
  struct { int64_t res;} blk;
  struct { struct { int64_t steps; } hla,all;} hte;
  struct { int64_t steps;} trd;
  struct { int64_t steps; } unhd;
  struct {int count; int64_t steps;} elm;
} Stats;

typedef struct Del { int cur, rem; } Del;

typedef struct Limits {
  int hla;
  int64_t randec;
  struct { int pen;} dst;
  struct { int pen; int64_t steps;} trd, unhd;
  struct { int excess,pen; int64_t steps;} elm;
  struct { int pen;} prb, lft;
  struct { int pen; int64_t steps; } hte;
  struct { int64_t steps;} term, sync;
} Limits;

typedef struct Stk { int * start, * top, * end; } Stk;
typedef signed char Val;
typedef struct HTS { int offset; int count;}  HTS;
typedef struct DVar { HTS hts[2]; } DVar;
typedef struct TD { int level, dom; int rsn[2]; } TD;

typedef enum Tag {
  FREEVAR = 0,
  FIXEDVAR = 1,
  EQUIVAR = 2,
  ELIMVAR = 3,

  DECISION = 0,
  UNITCS = 1,
  IRRCS = 1,
  BINCS = 2,
  TRNCS = 3,
  LRGCS = 4,
  MASKCS = 7,

  REDCS = 8,
  RMSHFT = 4,
} Tag;

typedef struct AVar {
  int pos;
  Tag type : 4;
  int mark, trail;
} AVar;

typedef struct Ext {
  unsigned equiv:1, blocking:2, eliminated:1;
  int val:2, repr, etrailpos;
} Ext;

typedef struct DF { int discovered, finished; } DF;
typedef struct EVar { int occ[2], score, pos; } EVar;
typedef struct Conf { int lit, rsn[2]; } Conf;
typedef struct Lir { Stk lits; } Lir;
typedef struct DFPR { int discovered, finished, parent, root; } DFPR;
typedef struct DFOPF { int observed, pushed, flag; } DFOPF;

typedef enum Wrag {
  PREFIX = 0,
  BEFORE = 1,
  AFTER = 2,
  POSTFIX = 3,
} Wrag;

typedef struct Work {
  Wrag wrag : 2;
  int lit : 30;
  int other : 30;
  unsigned red : 1;
  unsigned removed : 1;
} Work;

typedef struct Wtk { Work * start, * top, * end; } Wtk;

typedef struct DFL {
  int discovered, finished;
  union { int lit, sign; };
} DFL;

typedef struct RNG { unsigned z, w; } RNG;
#define MAXLDFW		31	
struct SPF {
  Opts opts;
  Ext * ext; int maxext; size_t szext;
  DVar * dvars; AVar * avars; Val * vals;  EVar * evars;
  int nvars, szvars, * i2e, * repr;
  Stk clause, dsched, esched, extend, sortstk, resolvent;
  Stk irr; int mt; Lir red[2];
  struct { struct { Stk bin, trn; } red, irr; } dis;
  struct { int pivot, negcls, necls, neglidx;
    Stk lits, next, csigs, lsigs, sizes, occs, noccs, mark, m2i; } elm;
  Stk trail, etrail, frames, saved, clv; 
  TD * drail; int szdrail;
  Stk wchs; int freewchs[MAXLDFW], nfreewchs;
  int next, flushed, level;
  struct { struct { DF * dfs; int ndfs, szdfs; } pos, neg; } df;
  Conf conf; Stk seen;
  RNG rng;
  char decomposing, measureagility, probing, distilling, lifting;
  char simp, eliminating, simplifying, blocking, unhiding;
  char dense, propred, igntrn;
  int ignlidx, ignlits[3];
  Limits limits;
  Stats stats;
  struct { int (*fun)(void*); void * state; int done; } term;
  struct {
    struct { void (*fun)(void*,int); void * state; } produce, consumed;
    struct { void(*fun)(void*,int**,int**); void*state; } consume;
  } units;
  struct {
    struct { int * (*fun)(void*); void * state; } lock;
    struct { void (*fun)(void*,int,int); void * state; } unlock;
  } eqs;
};

#define REMOVED		INT_MAX
#define NOTALIT		((INT_MAX >> RMSHFT))
#define MAXVAR		((INT_MAX >> RMSHFT) - 2)
#define MAXREDLIDX	((1 << 27) - 2)
#define MAXIRRLIDX	((1 << (31 - RMSHFT)) - 2)
#define FALSECNF	(1ll<<32)
#define TRUECNF		0ll
#define FUNVAR		11
#define FUNQUADS	(1<<(FUNVAR - 6))
#define MINPEN		0
#define MAXPEN		4

int s_maxVar (SPF * spf) {  return spf->maxext; }

static Ext * s_elit2ext (SPF * spf, int elit) {
  int idx = abs (elit);
  return spf->ext + idx;
}

extern Stack<int> * doubleClause;
extern int  doubleClauseCnt;
int getextLit (int ilit) 
{
  return ite2ext[abs(ilit)] * lit_sign (ilit);
}

int getintvar (SPF * spf, int eidx) 
{
    Ext * ext = s_elit2ext (spf, eidx);
    return ext->repr;
}

int s_import (SPF * spf, int elit);
void s_initsetup (SPF * spf); 
int s_lift (SPF * spf);
int s_unhide (SPF * spf);
int s_eliminate (SPF * spf);
int s_probe (SPF * spf);
int s_erepr (SPF * spf, int elit);
int * s_hts2wchs (SPF * spf, HTS * hts);
HTS * s_hts (SPF * spf, int lit);
int s_cval (SPF * spf, int litorval);
void s_iassume (SPF * spf, int lit);
void s_clearMap (SPF * spf); 
int abcd_solve(SPF * spf);

bool addClause_abcdSAT(SPF * spf, int *clause, int len, Solver* solver)
{  
   vec<Lit> lits;
   lits.clear();
   for (int i=0; i<len; i++){
        int elit=clause[i];
        int ilit=s_import (spf, elit);
        Lit p=(ilit > 0) ? mkLit(ilit-1)  : ~mkLit(-ilit-1);
        lits.push(p);
   }
   return solver->addClause_(lits); 
}

extern bool  certifiedUNSAT;  

void delRepeatClause(int **clsPtr)
{  
    for(int i=0; i < doubleClauseCnt; i++){
           int *pcls1=clsPtr[i];
           int len1=*pcls1;
	   int mark1=len1 & MARKBIT;
	   if(mark1==DELETED) continue;
           len1=len1>>FLAGBIT;
        
           for(int j=i+1; j < doubleClauseCnt; j++){
                 int *pcls2=clsPtr[j];
                 int len2=*pcls2;
	         int mark2=len2 & MARKBIT;
	         if(mark2==DELETED) continue;
                 len2=len2>>FLAGBIT;
                 if(mark1 != mark2 || len1 != len2) break;
                 for (int k=1; k<len1; k++)  if(pcls1[k] != pcls2[k]) goto nextC;
                 *pcls2=(len2<<FLAGBIT) | DELETED;
           }
      nextC: ;
    }
    int k=0;
    for(int i=0; i < doubleClauseCnt; i++){
           int *pcls1=clsPtr[i];
           int len1=*pcls1;
	   int mark1=len1 & MARKBIT;
	   if(mark1==DELETED) continue;
           clsPtr[k++]=clsPtr[i];
    }
    if(!certifiedUNSAT) printf("c old doubleCls#=%d \n",doubleClauseCnt);
    doubleClauseCnt=k;
    if(!certifiedUNSAT) printf("c new doubleCls#=%d \n",doubleClauseCnt);
}

bool extractNewClause(SPF * spf, int **clsPtr,Solver* solver)
{   int j,newcls=0;
    int oldcls, nocls;
    bool ret;
    do{
       oldcls=newcls;
       nocls=0;
       for(int i=0; i < doubleClauseCnt; i++){
           int *pcls=clsPtr[i];
           int len1=*pcls;
	   int mark1=len1 & MARKBIT;
	   if(mark1==CNF_CLS || mark1==DELETED) continue;
           len1=len1>>FLAGBIT;
           int share=0;
	   for(j=i-1; j < i+2; j++){
                if(j<0 || j==i || j>=doubleClauseCnt) continue;
                int *pcls2=clsPtr[j];
                int len2=*pcls2;
        	int mark2=len2 & MARKBIT;
                if(mark2 != CNF_CLS) continue;
	        len2 = len2>>FLAGBIT;
                if(len1 != len2) continue;
                int k;
                for (k=1; k<len1; k++)  if(pcls2[k] != pcls[k]) break;
                if(k < len1 ) continue;
                share=1;break;
           }
           if(share){ // A=B;
                 *pcls=(len1<<FLAGBIT) | DELETED;
                 ret=addClause_abcdSAT(spf, pcls+1, len1-1, solver);
                 if(!ret) return false;
           }
           else {
               ret=isConflict(pcls+1,len1-1);
               if(ret){
                    *pcls=(len1<<FLAGBIT) | DELETED;
                     newcls++;
                     ret=addClause_abcdSAT(spf, pcls+1, len1-1, solver);
                     if(!ret) return false;
               }
               else nocls++;
           }
       }
   } while(newcls!=oldcls && nocls);
   if(nocls) return false;
   return true;
}

void extractBClause(SPF * spf)
{  
     if(doubleClause==0) return;
  
     int *pcls=doubleClause->begin();
     int *pend=doubleClause->end();
     while(pcls < pend){
         int len=*pcls;
	 int *lits=pcls+1;
	 len=len>>FLAGBIT;
         pcls+=len;
         isConflict(lits,len-1);
     }
     delete doubleClause;
     doubleClause=0;
     doubleClauseCnt=0;
}

void SortLiteral(Stack<int> * clause);
void sortClause(Stack<int> *clause,int **clsPos);
bool hasBincls(int lit1, int lit2, vec<int> & lits);

void onlymidSimplify (SPF * spf) 
{
  s_initsetup (spf);
  s_clearMap (spf);
  drup_add=1;
  while(1){
      if (!s_lift (spf)) break;
      if (!s_eliminate (spf)) break;
      if (!s_unhide (spf)) break;
      s_probe (spf);
      break;
   }
   drup_add=0;
   vec<int> lits;
   for(int eVar=1; eVar<=spf->maxext; eVar++){
       int eqV = s_erepr (spf, eVar);
       if(eqV==eVar) continue;
       int lit1=eqV;
       int lit2=-eVar;
       for(int j=0; j<2; j++){
            if(j){lit1=-lit1; lit2=-lit2;}
              if(hasBincls(lit1,lit2,lits)){} 
              else {
                  if(lits.size()==2) add_2type_clause(lits,CNF_C_B);
              }
       }
   }
   extractBClause(spf);
}

int abcd_solve(SPF * spf)
{   
    int idx, sign, lit, blit, tag, other, other2;
    const int * p, * w, * eow, * c, * top;
    HTS * hts;
    int clscnt=0;
    vec<int> lits;
    ite2ext=spf->i2e;

    for(int eVar=1; eVar<=spf->maxext; eVar++){
           int eqV = s_erepr (spf, eVar);
           if(eqV==eVar) {
                 int ilit=getintvar(spf,eVar);
                 if(ilit<=1){
                       if(ilit>=-1) continue;
                       return 0;
                 }
                 if(getextLit(ilit) != eVar) return 0;
                 continue;
           }
           int lit1=eqV;
           int lit2=-eVar;
           for(int j=0; j<2; j++){
              if(j){lit1=-lit1; lit2=-lit2;}
              if(!hasBincls(lit1,lit2,lits)) {
                   if(lits.size()==2) add_2type_clause(lits,CNF_C_B);
                   else return 0;
              }
           }
    }

   for (idx = 2; idx < spf->nvars; idx++)
      for (sign = -1; sign <= 1; sign += 2) {
        lit = sign * idx;
        hts = s_hts (spf, lit);
        w = s_hts2wchs (spf, hts);
        eow = w + hts->count;
        for (p = w; p < eow; p++) {
	    blit = *p;
	    tag = blit & MASKCS;
            if (tag == TRNCS || tag == LRGCS) p++;
	    if (tag == BINCS) {
	          other = blit >> RMSHFT;
	          if (abs (other) < idx) continue;
	          other2 = 0;
	     } else if (tag == TRNCS) {
	          other = blit >> RMSHFT;
	          if (abs (other) < idx) continue;
	          other2 = *p;
	          if (abs (other2) < idx) continue;
	    } else continue;

            lits.clear();
            lits.push(getextLit(lit));
            lits.push(getextLit(other));
            if (tag == TRNCS) lits.push(getextLit(other2));
            add_2type_clause(lits,CNF_C_B);
            clscnt++;
        }
     }

     top = spf->irr.top;
     for (c = spf->irr.start; c < top; c = p + 1) {
          p = c;
          if (*p >= NOTALIT) continue;
          lits.clear();
          while (*p) {
              lit=*p++;
              lits.push(getextLit(lit));
          }
          add_2type_clause(lits,CNF_C_B);
          clscnt++;
     }

     if(doubleClause==0) return 0;
//
     SortLiteral(doubleClause);
     int **clsPos=(int **) malloc(sizeof(int *)*(doubleClauseCnt));
     sortClause(doubleClause, clsPos);

     Solver* solver=new Solver();
     while (spf->nvars-1 > solver->nVars()) solver->newVar();

     solver->subformuleClause=1;
   
     delRepeatClause(clsPos);
     bool ret=extractNewClause(spf, clsPos, solver);
     free(clsPos);
     delete doubleClause;
     doubleClause=0;
     if(ret==false) return 0;
    
     vec<Lit> ulit;
     ulit.clear();
     ulit.push(mkLit(0));
     solver->addClause(ulit);

    vec<Lit> dummy;
    solver->needExtVar=1;
    lbool rc = solver->solveLimited2(dummy);
    if(rc==l_True || rc==l_Undef) {
          for (idx = 2; idx < spf->nvars; idx++){
                  if(s_cval (spf, idx)) continue;
                  if (solver->model[idx-1] != l_Undef){
                      int lit;
                      if(solver->model[idx-1]==l_True) lit=idx;
		      else lit=-idx; 
                      s_iassume (spf, lit);
	          }
            }
            delete solver;
            if(rc==l_Undef) return 0;
            return 10;//SAT
    }
    delete solver;
    if(rc==l_False) return 20;//UNSAT;
    return 0;
}
//-----------------------------------------------------------------------

#define SWAP2(A,B) do { typeof(A) TMP = (A); (A) = (B); (B) = TMP; } while (0)

#define NEW(P,N) \
  do { (P) = (typeof(P))s_malloc (spf, (N) * sizeof *(P)); } while (0)

#define DEL(P,N) \
  do { s_free (spf, (P), (N) * sizeof *(P)); (P) = 0; } while (0)

#define RSZ(P,O,N,T) \
  do { (P) = (T)s_realloc (spf, (P), (O)*sizeof*(P), (N)*sizeof*(P)); } while (0)

#define CLN(P,N) \
  do { memset ((P), 0, (N) * sizeof *(P)); } while (0)
#define CLRPTR(P) \
  do { memset ((P), 0, sizeof *(P)); } while (0)
#define CLR(P) \
  do { memset (&(P), 0, sizeof (P)); } while (0)

//----------------------------------
#define SWAP(TYPE,A,B) \
do { TYPE TMP = (A); (A) = (B); (B) = TMP; } while (0)

#define ISORTLIM 10

#define CMPSWAP(TYPE,CMP,P,Q) \
do { if (CMP (&(P), &(Q)) > 0) SWAP (TYPE, P, Q); } while(0)

#define QPART(TYPE,CMP,A,L,R) \
do { \
  TYPE PIVOT; \
  int J = (R); \
  I = (L) - 1; \
  PIVOT = (A)[J]; \
  for (;;) { \
    while (CMP (&(A)[++I], &PIVOT) < 0) \
      ; \
    while (CMP (&PIVOT, &(A)[--J]) < 0) \
      if (J == (L)) break; \
    if (I >= J) break; \
    SWAP (TYPE, (A)[I], (A)[J]); \
  } \
  SWAP (TYPE, (A)[I], (A)[R]); \
} while(0)

#define QSORT(TYPE,CMP,A,N) \
do { \
  int L = 0, R = (N) - 1, M, LL, RR, I; \
  assert (s_mtstk (&spf->sortstk)); \
  if (R - L <= ISORTLIM) break; \
  for (;;) { \
    M = (L + R) / 2; \
    SWAP (TYPE, (A)[M], (A)[R - 1]); \
    CMPSWAP (TYPE, CMP, (A)[L], (A)[R - 1]); \
    CMPSWAP (TYPE, CMP, (A)[L], (A)[R]); \
    CMPSWAP (TYPE, CMP, (A)[R - 1], (A)[R]); \
    QPART (TYPE, CMP, (A), L + 1, R - 1); \
    if (I - L < R - I) { LL = I + 1; RR = R; R = I - 1; } \
    else { LL = L; RR = I - 1; L = I + 1; } \
    if (R - L > ISORTLIM) { \
      assert (RR - LL > ISORTLIM); \
      s_pushstk (spf, &spf->sortstk, LL); \
      s_pushstk (spf, &spf->sortstk, RR); \
    } else if (RR - LL > ISORTLIM) L = LL, R = RR; \
    else if (!s_mtstk (&spf->sortstk)) { \
      R = s_popstk (&spf->sortstk); \
      L = s_popstk (&spf->sortstk); \
    } else break; \
  } \
} while (0)

#define ISORT(TYPE,CMP,A,N) \
do { \
  TYPE PIVOT; \
  int L = 0, R = (N) - 1, I, J; \
  for (I = R; I > L; I--) \
    CMPSWAP (TYPE, CMP, (A)[I - 1], (A)[I]); \
  for (I = L + 2; I <= R; I++) { \
    J = I; \
    PIVOT = (A)[I]; \
    while (CMP (&PIVOT, &(A)[J - 1]) < 0) { \
      (A)[J] = (A)[J - 1]; \
      J--; \
    } \
    (A)[J] = PIVOT; \
  } \
} while (0)

#define SORT(TYPE,A,N,CMP) \
do { \
  TYPE * AA = (A); \
  int NN = (N); \
  QSORT (TYPE, CMP, AA, NN); \
  ISORT (TYPE, CMP, AA, NN); \
} while (0)

#define SORT3(A,N,CMP) \
   SORT(typeof(*(A)),A,N,CMP)

typedef int64_t Cnf;
typedef uint64_t Fun[FUNQUADS];

#define LT(n) n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n

static const char s_floorldtab[256] =
{
// 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
  -1, 0, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3,
  LT(4), LT(5), LT(5), LT(6), LT(6), LT(6), LT(6),
  LT(7), LT(7), LT(7), LT(7), LT(7), LT(7), LT(7), LT(7)
};

static const uint64_t s_basevar2funtab[6] = {
  0xaaaaaaaaaaaaaaaaull, 0xccccccccccccccccull, 0xf0f0f0f0f0f0f0f0ull,
  0xff00ff00ff00ff00ull, 0xffff0000ffff0000ull, 0xffffffff00000000ull,
};

static int s_floorld (int n) {
  if (n < (1<<8)) return s_floorldtab[n];
  if (n < (1<<16)) return 8 + s_floorldtab[n>>8];
  if (n < (1<<24)) return 16 + s_floorldtab[n>>16];
  return 24 + s_floorldtab[n>>24];
}

static int s_ispow2 (int n) { return !(n & (n - 1));}

static int s_ceilld (int n) {
  int res = s_floorld (n);
  if (!s_ispow2 (n)) res++;
  return res;
}

static void fatalExit (const char * msg, ...) {
  printf ("c *** internal error %s in '%s': ", msg, __FILE__);
  exit (0);
}

static void s_inc (SPF * spf, size_t bytes) {
  spf->stats.bytes.current += bytes;
  if (spf->stats.bytes.max < spf->stats.bytes.current) {
    spf->stats.bytes.max = spf->stats.bytes.current; // maximum allocated 
  }
}

static void s_dec (SPF * spf, size_t bytes) {  spf->stats.bytes.current -= bytes;}

static void * s_malloc (SPF * spf, size_t bytes) {
  void * res;
  if (!bytes) return 0;
  res = malloc (bytes);
  if (!res) fatalExit ("out of memory allocating %ld bytes", bytes);
  s_inc (spf, bytes);
  memset (res, 0, bytes);
  return res;
}

static void s_free (SPF * spf, void * ptr, size_t bytes) {
  if (!ptr) { assert (!bytes); return; }
  s_dec (spf, bytes);
  free (ptr);
}

static void * s_realloc (SPF * spf, void * ptr, size_t old, size_t newsz) {
  void * res;
  if (!ptr) return s_malloc (spf, newsz);
  if (!newsz) { s_free (spf, ptr, old); return 0; }
  s_dec (spf, old);
  res = realloc (ptr, newsz);
  if (!res) fatalExit ("out of memory reallocating %ld to %ld bytes", old, newsz);
  s_inc (spf, newsz);
  if (newsz > old) memset ((char *)res + old, 0, newsz - old);
  return res;
}

static int s_fullstk (Stk * s) { return s->top == s->end; }
static int s_mtstk (Stk * s) { return s->top == s->start; }
static size_t s_cntstk (Stk * s) { return s->top - s->start; }
static size_t s_szstk (Stk * s) { return s->end - s->start; }

static int s_peek (Stk * s, int pos) {  return s->start[pos];}
static void s_poke (Stk * s, int pos, int val) {  s->start[pos] = val;}

static void s_enlstk (SPF * spf, Stk * s) {
  size_t old_size = s_szstk (s);
  size_t new_size = old_size ? 2 * old_size : 1;
  size_t count = s_cntstk (s);
  RSZ (s->start, old_size, new_size,int *);
  s->top = s->start + count;
  s->end = s->start + new_size;
}

static void s_relstk (SPF * spf, Stk * s) {
  DEL (s->start, s_szstk (s));
  s->start = s->top = s->end = 0;
}

static void s_shrstk (SPF * spf, Stk * s, int new_size) {
  size_t old_size, count = s_cntstk (s);
  if (new_size > 0) {
    old_size = s_szstk (s);
    RSZ (s->start, old_size, new_size,int *);
    s->top = s->start + count;
    s->end = s->start + new_size;
  } else s_relstk (spf, s);
}

static void s_fitstk (SPF * spf, Stk * s) {  s_shrstk (spf, s, s_cntstk (s));}

static void s_pushstk (SPF * spf, Stk * s, int elem) {
  if (s_fullstk (s)) s_enlstk (spf, s);
  *s->top++ = elem;
}

static int s_popstk (Stk * s) { return *--s->top; }
static int s_topstk (Stk * s) { return s->top[-1]; }
static void s_rststk (Stk * s, int newsz) {  s->top = s->start + newsz;}
static void s_clnstk (Stk * s) { s_rststk (s, 0); }

static unsigned s_rand (SPF * spf) {
  unsigned res;
  spf->rng.z = 36969 * (spf->rng.z & 65535) + (spf->rng.z >> 16);
  spf->rng.w = 18000 * (spf->rng.w & 65535) + (spf->rng.w >> 16);
  res = (spf->rng.z << 16) + spf->rng.w;
  return res;
}

#define OPT(SHRT,LNG,VAL,MIN,MAX,DESCRP) \
do { \
  Opt * opt = &spf->opts.LNG; \
  opt->shrt = SHRT; \
  opt->lng = #LNG; \
  opt->val = VAL; \
  assert (MIN <= VAL); \
  opt->min = MIN; \
  assert (VAL <= MAX); \
  opt->max = MAX; \
  opt->descrp = DESCRP; \
} while (0)

SPF * s_init (void) {
  const int K = 1000, M = K*K, I = INT_MAX;
  SPF * spf;
  int i;

  drup_add=0;
  spf = (SPF *)malloc (sizeof *spf);
  CLRPTR (spf);

  for (i = 0; i < MAXLDFW; i++) spf->freewchs[i] = INT_MAX;
 
  s_pushstk (spf, &spf->wchs, INT_MAX);
  s_pushstk (spf, &spf->wchs, INT_MAX);

  spf->measureagility = 1;
  spf->propred = 1;
  spf->ignlidx = -1;

  OPT(0,block,1,0,1,"enable initial blocked clause elimination");
  OPT(0,blkclslim,2000,3,I,"max blocked clause size");
  OPT(0,blkmaxeff,80*M,0,I,"max effort in blocked clause elimination");
  OPT(0,blkmineff,3*M,0,I,"min effort in blocked clause elimination");
  OPT(0,blkreleff,30,0,K,"rel effort in blocked clause elimination");
  OPT(0,blkocclim,2000,3,I,"max occurrences in blocked clause elimination");

  OPT(0,dstmaxeff,60*M,0,I,"max effort in distilling");
  OPT(0,dstmineff,600*K,0,I,"min effort in distilling");
  OPT(0,dstreleff,15,0,K,"rel effort in distilling");
 
  OPT(0,elim,1,0,1,"enable eliminiation");
  
  OPT(0,elmhte,1,0,1,"enabled hte during elimination");
  OPT(0,elmhtelim,2000,0,I,"hte during elimination resolvent limit");
  OPT(0,elmclslim,1000,3,I,"max antecendent size in elimination");
  OPT(0,elmaxeff,600*M,0,I,"max effort in eliminiation");
  OPT(0,elmineff,15*M,0,I,"min effort in eliminiation");
  OPT(0,elmreleff,200,0,10*K,"rel effort in elimination");
  OPT(0,elmocclim,1000,3,I,"max occurences in elimination");
  OPT(0,elmnostr,0,0,I,"number of elimination rounds before strengthening");
  OPT(0,elmreslim,2000,2,I,"max resolvent size in elimination");
    
  OPT(0,hlaliminc,5,1,I/4,"hidden literal addition limit increment");
  OPT(0,hlaminlim,5,1,I/2,"hidden literal addition min limit");
  OPT(0,hlamaxlim,10000,1,I/2,"hidden literal addition max limit");
  OPT(0,hte,1,0,1,"enable hte & hlr removal");
  OPT(0,htered,1,0,1,"enable hte & hlr in redundant/learned clauses");
  OPT(0,htemaxeff,100*M,0,I,"max effort in hidden tautology elimination");
  OPT(0,htemineff,M,0,I,"min effort in hidden tautology elimination");
  OPT(0,htereleff,40,0,10*K,"rel effort in hidden tautology elimination");
  OPT(0,lhbr,1,0,1, "enable lazy hyber binary reasoning");
   
  OPT(0,lftmaxeff,40*M,0,I,"max effort in lifting");
  OPT(0,lftmineff,400*K,0,I,"min effort in lifting");
  OPT(0,lftreleff,20,0,10*K,"rel effort in lifting");

  OPT(0,probe,1,0,1,"enable probing");
  OPT(0,prbmaxeff,40*M,0,I,"max effort in probing");
  OPT(0,prbmineff,400*K,0,I,"min effort in probing");
  OPT(0,prbreleff,20,0,10*K,"rel effort in probing");

  OPT(0,seed,0,0,I,"random number generator seed");
  OPT(0,smallve,1,0,1,"enable small number variables elimination");
  OPT(0,smallvevars,FUNVAR,4,FUNVAR,  "variables in small number variables elimination");
  OPT(0,randecint,1000,2,I/2,"random decision interval");
 
  OPT(0,syncint,111111,0,M,"unit synchronization interval");
  OPT(0,termint,122222,0,M,"termination check interval");
 
  OPT(0,trdmaxeff,60*M,0,I,"max effort in transitive reduction");
  OPT(0,trdmineff,600*K,0,I,"min effort in transitive reduction");
  OPT(0,trdreleff,6,0,10*K,"rel effort in transitive reduction");
 
  OPT(0,unhdextstamp,1,0,1,"used extended stamping features");
  OPT(0,unhdhbr,0,0,1,"enable unhiding hidden binary resolution");
  OPT(0,unhdmaxeff,100*M,0,I,"max effort in unhiding");
  OPT(0,unhdmineff,1*M,0,I,"min effort in unhiding");
  OPT(0,unhdreleff,30,0,10*K,"rel effort in unhiding");
  OPT(0,unhdlnpr,3,0,I,"unhide no progress round limit");
  OPT(0,unhdroundlim,5,0,100,"unhide round limit");

  return spf;
}

static unsigned s_gcd (unsigned a, unsigned b) {
  unsigned tmp;
  if (a < b) SWAP2 (a, b);
  while (b) tmp = b, b = a % b, a = tmp;
  return a;
}

static void s_rszvars (SPF * spf, int new_size) {
  int old_size = spf->szvars;
  RSZ (spf->vals, old_size, new_size, Val *);
  RSZ (spf->i2e, old_size, new_size, int *);
  RSZ (spf->dvars, old_size, new_size, DVar *);
  RSZ (spf->avars, old_size, new_size, AVar *);
  spf->szvars = new_size;
}

static void s_enlvars (SPF * spf) {
  size_t old_size, new_size;
  old_size = spf->szvars;
  new_size = old_size ? 2 * old_size : 4;
  s_rszvars (spf, new_size);
}

static void s_redvars (SPF * spf) {
  size_t old_size, new_size;
  old_size = spf->szvars;
  new_size = spf->nvars;
  if (new_size == old_size) return;// reducing variables from %ld to %ld", old_size, new_size
  s_rszvars (spf, new_size);
}

static int s_max (int a, int b) { return a > b ? a : b; }
static DVar * s_dvar (SPF * spf, int lit) {  return spf->dvars + abs (lit);}
static AVar * s_avar (SPF * spf, int lit) {  return spf->avars + abs (lit);}

static int * s_dpos (SPF * spf, int lit) {
  AVar * av;
  int * res;
  av = s_avar (spf, lit);
  res = &av->pos;
  return res;
}

static int s_dcmp (SPF * spf, int l, int k) {
    return 0;
 // AVar * av = s_avar (spf, l);
 // AVar * bv = s_avar (spf, k);
//  int res;
  //if ((res = (bv->part - av->part))) return res;
 // return res;
}

static void s_dup (SPF * spf, int lit) {
  int child = lit, parent, cpos, ppos, * p, * cposptr, * pposptr;
  Stk * s = &spf->dsched;
  p = s->start;
  cposptr = s_dpos (spf, child);
  cpos = *cposptr;
  while (cpos > 0) {
    ppos = (cpos - 1)/2;
    parent = p[ppos];
    if (s_dcmp (spf, parent, lit) >= 0) break;
    pposptr = s_dpos (spf, parent);
    p[cpos] = parent;
    *pposptr = cpos;//parent, "down from %d", ppos);
    cpos = ppos;
    child = parent;
  }
  if (*cposptr == cpos) return;
  *cposptr = cpos;
  p[cpos] = lit;//lit, "up from %d", ppos);
}

static void s_ddown (SPF * spf, int lit) {
  int parent = lit, child, right, ppos, cpos;
  int * p, * pposptr, * cposptr, size;
  Stk * s = &spf->dsched;
  size = s_cntstk (s);
  p = s->start;
  pposptr = s_dpos (spf, parent);
  ppos = *pposptr;
  for (;;) {
    cpos = 2*ppos + 1;
    if (cpos >= size) break;
    child = p[cpos];
    if (cpos + 1 < size) {
      right = p[cpos + 1];
      if (s_dcmp (spf, child, right) < 0) cpos++, child = right;
    }
    if (s_dcmp (spf, child, lit) <= 0) break;
    cposptr = s_dpos (spf, child);
    p[ppos] = child;
    *cposptr = ppos; //child, "up from %d", cpos);
    ppos = cpos;
    parent = child;
  }
  if (*pposptr == ppos) return;
  *pposptr = ppos;
  p[ppos] = lit;//lit, "down from %d", cpos);
}

static void s_dsched (SPF * spf, int lit) {
  int * p = s_dpos (spf, lit);
  Stk * s = &spf->dsched;
  *p = s_cntstk (s);
  s_pushstk (spf, s, lit);
  s_dup (spf, lit);
  s_ddown (spf, lit); //lit, "pushed");
}

static Val s_val (SPF * spf, int lit) {
  int idx = abs (lit);
  Val res;
  res = spf->vals[idx];
  if (lit < 0) res = -res;
  return res;
}

static int s_trail (SPF * spf, int lit) { return s_avar (spf, lit)->trail; }

static TD * s_td (SPF * spf, int lit) {
  int pos = s_trail (spf, lit);
  return spf->drail + pos;
}

static int s_evel (SPF * spf, int lit) { return s_td (spf, lit)->level; }

static void s_dreschedule (SPF * spf) {
  Stk * s = &spf->dsched;
  int idx, i, pos, cnt = s_cntstk (s);
  AVar * av;
  //rescheduling %d variables", cnt);
  pos = 0;
  s->top = s->start;
  for (i = 0; i < cnt; i++) {
    idx = s->start[i];
    av = s_avar (spf, idx);
    if (av->type != FREEVAR) { av->pos = -1; continue; }
    s->start[pos] = idx;
    av->pos = pos++;
    s->top++;
    s_dup (spf, idx);
    s_ddown (spf, idx);
  }//new schedule with %d variables", s_cntstk (s));
  s_fitstk (spf, s);
}

static int s_newvar (SPF * spf) {
  int res;
  AVar * av;
  DVar * dv;
  if (spf->nvars == spf->szvars) s_enlvars (spf);
  if (spf->nvars) res = spf->nvars++;
  else res = 2, spf->nvars = 3;
  assert (res < spf->szvars);
  if (res > MAXVAR) fatalExit ("more than %d variables", MAXVAR - 1);
  dv = spf->dvars + res;
  CLRPTR (dv);
  av = spf->avars + res;
  CLRPTR (av);
  av->pos = -1;
  s_dsched (spf, res);
  return res;
}

int s_erepr (SPF * spf, int elit) {
  int res, next;
  Ext * ext;
  res = elit;
  for (;;) {
    ext = s_elit2ext (spf, res);
    if (!ext->equiv) break;
    next = ext->repr;
    if (res < 0) next = -next;
    res = next;
  }
  return res;
}

static void s_adjext (SPF * spf, int eidx) {
  size_t old, newsz;
  old = spf->szext;
  newsz = old ? 2*old : 2;
  while ((size_t)eidx >= newsz) newsz *= 2;
  //enlarging external variables from %ld to %ld", old, newsz);
  RSZ (spf->ext, old, newsz,Ext *);
  spf->szext = newsz;
}

int s_import (SPF * spf, int elit) {
  int res, repr, eidx = abs (elit);
  Ext * ext;
  if ((size_t)eidx >= spf->szext) s_adjext (spf, eidx);
  if (eidx > spf->maxext) spf->maxext = eidx;
  repr = s_erepr (spf, elit);
  ext = s_elit2ext (spf, repr);
  res = ext->repr;
  if (!res) {
    res = s_newvar (spf);
    ext->repr = res;
    ext->etrailpos = -1;
    spf->i2e[res] = eidx;//mapping external variable %d to %d", eidx, res);
  }
  if (repr < 0) res = -res;//importing %d as %d", elit, res);
  return res;
}

static int * s_idx2lits (SPF * spf, int red, int lidx) {
  Stk * s;
  if (red) s = &spf->red[0].lits;
  else s = &spf->irr;
  return s->start + lidx;
}

static int s_isfree (SPF * spf, int lit) {
  return s_avar (spf, lit)->type == FREEVAR;
}

static int s_iselim (SPF * spf, int lit) {
  return s_avar (spf, lit)->type == ELIMVAR;
}

static int s_export (SPF * spf, int ilit) {
  assert (2 <= abs (ilit) && abs (ilit) < spf->nvars);
  return spf->i2e[abs (ilit)] * lit_sign (ilit);
}

static int * s_rsn (SPF * spf, int lit) { return s_td (spf, lit)->rsn; }

static int s_dom (SPF * spf, int lit) {
  int res = s_td (spf, lit)->dom;
  if (s_val (spf, lit) < 0) res = -res;
  return res;
}

HTS * s_hts (SPF * spf, int lit) {
  return s_dvar (spf, lit)->hts + (lit < 0);
}

int * s_hts2wchs (SPF * spf, HTS * hts) {
  int * res = spf->wchs.start + hts->offset;
  return res;
}

static void s_assign (SPF * spf, int lit, int r0, int r1) {
  AVar * av = s_avar (spf, lit);
  int idx, phase, tag;
  TD * td;
  av->trail = s_cntstk (&spf->trail);
  if (av->trail >= spf->szdrail) {
    int newszdrail = spf->szdrail ? 2*spf->szdrail : 1;
    RSZ (spf->drail, spf->szdrail, newszdrail, TD *);
    spf->szdrail = newszdrail;
  }
  td = s_td (spf, lit);
  tag = r0 & MASKCS;
  if (tag == BINCS) {
    td->dom = -s_dom (spf, (r0 >> RMSHFT));// literal %d dominated by %d, lit, td->dom
  } else td->dom = lit;

  idx = abs (lit);
  phase = lit_sign (lit);
  spf->vals[idx] = phase;
  td->level = spf->level;
  if (!spf->level) {
    if (av->type == EQUIVAR) {// spf->stats.equiv.current--;
    } else av->type = FIXEDVAR;
    td->rsn[0] = UNITCS | (lit << RMSHFT);
    td->rsn[1] = 0;
    if (spf->units.produce.fun)  {
   //try to export internal unit %d external %d\n, spf->tid, lit, s_export (spf, lit));
      spf->units.produce.fun (spf->units.produce.state, s_export (spf, lit));
   //exporting internal unit %d external %d\n,    spf->tid, lit, s_export (spf, lit));
    }
  } else {
    td->rsn[0] = r0;
    td->rsn[1] = r1;
  }
  s_pushstk (spf, &spf->trail, lit);
  __builtin_prefetch (s_hts2wchs (spf, s_hts (spf, -lit)));
}

static void s_f2rce (SPF * spf, int lit, int other, int red) {
  s_assign (spf, lit, ((other << RMSHFT) | BINCS | red), 0);
}

static void s_f3rce (SPF * spf, int lit, int other, int other2, int red) {
  s_assign (spf, lit, ((other << RMSHFT) | TRNCS | red), other2);
}

static void s_flrce (SPF * spf, int lit, int red, int lidx) {
  s_assign (spf, lit, red | LRGCS, lidx);
}

static void s_unassign (SPF * spf, int lit) {
  int idx = abs (lit);
  AVar * av = s_avar (spf, lit);
  spf->vals[idx] = 0;
  if (av->pos < 0) s_dsched (spf, idx);
}

static void s_backtrack (SPF * spf, int level) {
  int lit;
  while (!s_mtstk (&spf->trail)) {
    lit = s_topstk (&spf->trail);
    if (s_evel (spf, lit) <= level) break;
    s_unassign (spf, lit);
    spf->trail.top--;
  }
  spf->level = level;
  spf->conf.lit = 0;
  spf->conf.rsn[0] = spf->conf.rsn[1] = 0;
  spf->next = s_cntstk (&spf->trail);
}

static int s_marked (SPF * spf, int lit) {
  int res = s_avar (spf, lit)->mark;
  if (lit < 0) res = -res;
  return res;
}

static void s_unit (SPF * spf, int lit) {  s_assign (spf, lit, (lit << RMSHFT) | UNITCS, 0);}
static void s_mark (SPF * spf, int lit) {  s_avar (spf, lit)->mark = lit_sign (lit);}
static void s_unmark (SPF * spf, int lit) { s_avar (spf, lit)->mark = 0; }

int s_cval (SPF * spf, int litorval) {
  if (litorval == 1 || litorval == -1) return litorval;
  return s_val (spf, litorval);
}

static int s_simpcls (SPF * spf) {
  int * p, * q = spf->clause.start, lit, tmp, mark;
  for (p = spf->clause.start; (lit = *p); p++) {
    tmp = s_cval (spf, lit);
    if (tmp == 1)  break;//literal %d satisfies clauses, lit
    if (tmp == -1) continue; //removing false literal %d, lit
    mark = s_marked (spf, lit);
    if (mark > 0)  continue; //removing duplicated literal %d", lit
    if (mark < 0)  break;//literals %d and %d occur both", -lit, lit
    *q++ = lit;
    s_mark (spf, lit);
  }
  *q = 0;
  spf->clause.top = q + 1;
  while (q > spf->clause.start) s_unmark (spf, *--q);
//  if (lit) LOG (2, "simplified clause is trivial");
//  else LOGCLS (2, spf->clause.start, "simplified clause");
  return lit;
}

static void s_orderclsaux (SPF * spf, int * start) {
  int * p, max = 0, level, lit;
  for (p = start; (lit = *p); p++) {
    if (!s_val (spf, lit)) continue;
    level = s_evel (spf, lit);
    if (level <= max) continue;
    max = level;
    *p = start[0];
    start[0] = lit;
  }
}

static void s_ordercls (SPF * spf) {
  s_orderclsaux (spf, spf->clause.start);
 // LOG (3, "head literal %d", spf->clause.start[0]);
  s_orderclsaux (spf, spf->clause.start  + 1);
//  LOG (3, "tail literal %d", spf->clause.start[1]);
 // LOGCLS (3, spf->clause.start, "ordered clause");
}

static void s_freewch (SPF * spf, int oldoffset, int oldhcount) {
  int ldoldhcount = s_ceilld (oldhcount);
  spf->wchs.start[oldoffset] = spf->freewchs[ldoldhcount];
  spf->freewchs[ldoldhcount] = oldoffset;
  spf->nfreewchs++;
  //saving watch stack at %d of size %d on free list %d",oldoffset, oldhcount, ldoldhcount
}

static void s_shrinkhts (SPF * spf, HTS * hts, int newcount) {
  int * p, i, oldcount = hts->count;
  assert (newcount <= oldcount);
  if (newcount == oldcount) return;
  p = s_hts2wchs (spf, hts);
  for (i = newcount; i < oldcount; i++) p[i] = 0;
  hts->count = newcount;
  if (newcount) return;
  s_freewch (spf, hts->offset, oldcount);
  hts->offset = 0;
}

static long s_enlwchs (SPF * spf, HTS * hts) {
  int oldhcount = hts->count, oldoffset = hts->offset, newoffset;
  int oldwcount, newwcount, oldwsize, newwsize, i, j;
  int newhcount = oldhcount ? 2*oldhcount : 1;
  int * oldwstart, * newwstart, * start;
  int ldnewhcount = s_floorld (newhcount);
  long res = 0;

  newhcount = (1<<ldnewhcount);
  assert (newhcount > oldhcount);
  // increasing watch stack at %d from %d to %d,  oldoffset, oldhcount, newhcount

  newoffset = spf->freewchs[ldnewhcount];
  start = spf->wchs.start;
  if (newoffset != INT_MAX) {
    spf->freewchs[ldnewhcount] = start[newoffset];
    start[newoffset] = 0;
    assert (spf->nfreewchs > 0);
    spf->nfreewchs--;    //reusing free watch stack at %d of size %d",newoffset, (1 << ldnewhcount));
  } else {
    assert (spf->wchs.start[hts->offset]);
    assert (spf->wchs.top[-1] == INT_MAX);

    oldwcount = s_cntstk (&spf->wchs);
    newwcount = oldwcount + newhcount;
    oldwsize = s_szstk (&spf->wchs);
    newwsize = oldwsize;
   
    while (newwsize < newwcount) newwsize *= 2;
    if (newwsize > oldwsize) {
      newwstart = oldwstart = spf->wchs.start;
      RSZ (newwstart, oldwsize, newwsize, int *);
      //resized global watcher stack from %d to %d", oldwsize, newwsize
      res = newwstart - oldwstart;
      if (res) {//moved global watcher stack by %ld", res);
	start = spf->wchs.start = newwstart;
      }
      spf->wchs.end = start + newwsize;
    }
    spf->wchs.top = start + newwcount;
    spf->wchs.top[-1] = INT_MAX;
    newoffset = oldwcount - 1;
    //new watch stack of size %d at end of global watcher stack at %d,newhcount, newoffset);
  }
  j = newoffset;
  for (i = oldoffset; i < oldoffset + oldhcount; i++) {
    start[j++] = start[i];
    start[i] = 0;
  }
  while (j < newoffset + newhcount) start[j++] = 0;
  hts->offset = newoffset;
  if (oldhcount > 0) s_freewch (spf, oldoffset, oldhcount);
  return res;
}

static long s_pushwch (SPF * spf, HTS * hts, int wch) {
  long res = 0;
  int * wchs = s_hts2wchs (spf, hts);
  if (wchs[hts->count]) {
    res = s_enlwchs (spf, hts);
    wchs = s_hts2wchs (spf, hts);
  }
  wchs[hts->count++] = wch;
  return res;
}

static long s_wchbin (SPF * spf, int lit, int other, int red) {
  HTS * hts = s_hts (spf, lit);
  int cs = ((other << RMSHFT) | BINCS | red);
  long res = s_pushwch (spf, hts, cs);
  // new %s binary watch %d blit %d", s_red2str (red), lit, other
  return res;
}

static void s_wchtrn (SPF * spf, int a, int b, int c, int red) {
  HTS * hts = s_hts (spf, a);
  int cs = ((b << RMSHFT) | TRNCS | red);
  s_pushwch (spf, hts, cs);
  s_pushwch (spf, hts, c);
  //new %s ternary watch %d blits %d %d", s_red2str (red), a, b, c
}

static long s_wchlrg (SPF * spf, int lit, int other, int red, int lidx) {
  HTS * hts = s_hts (spf, lit);
  int blit = ((other << RMSHFT) | LRGCS | red);
  long res = 0;
  res += s_pushwch (spf, hts, blit);
  res += s_pushwch (spf, hts, lidx);
  return res;
}

static EVar * s_evar (SPF * spf, int lit) {
  int idx = abs (lit);
  return spf->evars + idx;
}

static int * s_epos (SPF * spf, int lit) {
  EVar * ev;
  int * res;
  ev = s_evar (spf, lit);
  res = &ev->pos;
  return res;
}

static int s_escore (SPF * spf, int lit) {
  EVar * ev;
  int res;
  ev = s_evar (spf, lit);
  res = ev->score;
  return res;
}

static int s_ecmp (SPF * spf, int s, int l, int t, int k) {
  if (s > t) return -1;
  if (s < t) return 1;
  return k - l;
}

static void s_eup (SPF * spf, int lit) {
  int child = lit, parent, cpos, ppos, * p, * cposptr, * pposptr;
  Stk * s = &spf->esched;
  int lscr, pscr;
  p = s->start;
  lscr = s_escore (spf, child);
  cposptr = s_epos (spf, child);
  cpos = *cposptr;
  while (cpos > 0) {
    ppos = (cpos - 1)/2;
    parent = p[ppos];
    pscr = s_escore (spf, parent);
    if (s_ecmp (spf, pscr, parent, lscr, lit) >= 0) break;
    pposptr = s_epos (spf, parent);
    p[cpos] = parent;
    *pposptr = cpos;//parent, "down from %d", ppos);
    cpos = ppos;
    child = parent;
  }
  if (*cposptr == cpos) return;
  *cposptr = cpos;
  p[cpos] = lit;//lit, "up from %d", ppos);
}

static void s_edown (SPF * spf, int lit) {
  int parent = lit, child, right, ppos, cpos;
  int * p, * pposptr, * cposptr, size;
  int lscr, cscr, rscr;
  Stk * s = &spf->esched;
  size = s_cntstk (s);
  p = s->start;
  lscr = s_escore (spf, parent);
  pposptr = s_epos (spf, parent);
  ppos = *pposptr;
  for (;;) {
    cpos = 2*ppos + 1;
    if (cpos >= size) break;
    child = p[cpos];
    cscr = s_escore (spf, child);
    if (cpos + 1 < size) {
      right = p[cpos + 1];
      rscr = s_escore (spf, right);
      if (s_ecmp (spf, cscr, child, rscr, right) < 0)
        cpos++, child = right, cscr = rscr;
    }
    if (s_ecmp (spf, cscr, child, lscr, lit) <= 0) break;
    cposptr = s_epos (spf, child);
    p[ppos] = child;
    *cposptr = ppos;
    //child, "up from %d", cpos);
    ppos = cpos;
    parent = child;
  }
  if (*pposptr == ppos) return;
  *pposptr = ppos;
  p[ppos] = lit;
//lit, "down from %d", cpos);
}

static void s_esched (SPF * spf, int lit) {
  int * p;
  Stk * s;
  if (!s_isfree (spf, lit)) return;
  p = s_epos (spf, lit);
  s = &spf->esched;
  if (*p >= 0) return;
  *p = s_cntstk (s);
  s_pushstk (spf, s, lit);
  s_eup (spf, lit);
  s_edown (spf, lit);
  //lit, "pushed");
}

static void s_eschedall (SPF * spf) {
  int lit;
  for (lit = 2; lit < spf->nvars; lit++) s_esched (spf, lit);
}

static int s_ecalc (SPF * spf, EVar * ev) {
  int res = ev->score, o0 = ev->occ[0], o1 = ev->occ[1];
  if (!o0 || !o1) ev->score = 0;
  else ev->score = o0 + o1;
  return res;
}

static void s_incocc (SPF * spf, int lit) {
  int idx = abs (lit), old, sign = (lit < 0);
  EVar * ev = s_evar (spf, lit);
  assert (s_isfree (spf, lit));
  ev->occ[sign] += 1;
  old = s_ecalc (spf, ev);
//inc occ of %d gives escore[%d] = %d with occs %d %d",lit, idx, ev->score, ev->occ[0], ev->occ[1], ev->score);
  if (ev->pos < 0) {
    if (spf->elm.pivot != idx) s_esched (spf, idx);
  } else if (old < ev->score) s_edown (spf, idx);
}

static int s_isact (int act) { return NOTALIT <= act && act < REMOVED-1; }

static void s_addcls (SPF * spf, int red) {
  int size, lit, other, other2, * p, lidx, blit;
  Lir * lir;
  Stk * w;

  if(drup_add){
         vec<int> lits;
         lits.clear();
         for (p = spf->clause.start; (other2 = *p); p++) lits.push(s_export(spf,other2));
         add_2type_clause(lits, CNF_C_B);
  }
 
  size = s_cntstk (&spf->clause) - 1;
  if (!size) {// empty clause;
    spf->mt = 1;
    return;
  }
  lit = spf->clause.start[0];
  if (size == 1) {
    s_unit (spf, lit);
    return;
  }
  other = spf->clause.start[1];
  if (size == 2) {
    s_wchbin (spf, lit, other, red);
    s_wchbin (spf, other, lit, red);
    if (red) {
      if (s_val (spf, lit) < 0) s_f2rce (spf, other, lit, REDCS);
      if (s_val (spf, other) < 0) s_f2rce (spf, lit, other, REDCS);
    } else if (spf->dense) {
      s_incocc (spf, lit);
      s_incocc (spf, other);
    }
    return;
  }
  s_ordercls (spf);
  lit = spf->clause.start[0];
  other = spf->clause.start[1];
  if (size == 3) {
    other2 = spf->clause.start[2];
    s_wchtrn (spf, lit, other, other2, red);
    s_wchtrn (spf, other, lit, other2, red);
    s_wchtrn (spf, other2, lit, other, red);
    if (red) {
      if (s_val (spf, lit) < 0 && s_val (spf, other) < 0)
	s_f3rce (spf, other2, lit, other, REDCS);
      if (s_val (spf, lit) < 0 && s_val (spf, other2) < 0)
	s_f3rce (spf, other, lit, other2, REDCS);
      if (s_val (spf, other) < 0 && s_val (spf, other2) < 0)
	s_f3rce (spf, lit, other, other2, REDCS);
    } else if (spf->dense) {
      s_incocc (spf, lit);
      s_incocc (spf, other);
      s_incocc (spf, other2);
    }
    return;
  }
  if (red) {
      lir = spf->red;
      w = &lir->lits;
      lidx = s_cntstk (w) + 1;
      if (lidx > MAXREDLIDX) fatalExit ("number of redundant large clause literals exhausted");
      s_pushstk (spf, w, NOTALIT);// not a lit
  }
  else {
      w = &spf->irr;
      lidx = s_cntstk (w);
      if (lidx <= 0 && !s_mtstk (w)) fatalExit ("number of irredundant large clause literals exhausted");
  }
  
  for (p = spf->clause.start; (other2 = *p); p++) s_pushstk (spf, w, other2);
  s_pushstk (spf, w, 0);

  if ((!red && !spf->dense) || red) {
    (void) s_wchlrg (spf, lit, other, red, lidx);
    (void) s_wchlrg (spf, other, lit, red, lidx);
  }
  if (!red && spf->dense) {
    if (lidx > MAXIRRLIDX)  fatalExit ("number of irredundant large clause literals exhausted");
    blit = (lidx << RMSHFT) | IRRCS;
    for (p = spf->clause.start; (other2 = *p); p++) {
        s_incocc (spf, other2);
        s_pushwch (spf, s_hts (spf, other2), blit);
    }
  }
}

static void s_iadd (SPF * spf, int ilit) {
  s_pushstk (spf, &spf->clause, ilit);
  if (ilit) return;
  if (!s_simpcls (spf)) s_addcls (spf, 0);
  s_clnstk (&spf->clause);
}

void s_add (SPF * spf, int elit) {
  int ilit;
  if (spf->level > 0) s_backtrack (spf, 0);
  if (elit) ilit = s_import (spf, elit);
  else ilit = 0;
  s_iadd (spf, ilit);
}

static void s_bonflict (SPF * spf, int lit, int blit) {
  spf->conf.lit = lit;
  spf->conf.rsn[0] = blit;
// inconsistent %s binary clause %d %d",   s_red2str (blit & REDCS), lit, (blit >> RMSHFT));
}

static void s_tonflict (SPF * spf, int lit, int blit, int other2) {
  spf->conf.lit = lit;
  spf->conf.rsn[0] = blit;
  spf->conf.rsn[1] = other2;
}

static void s_onflict (SPF * spf, int check, int lit, int red, int lidx) {
  spf->conf.lit = lit;
  spf->conf.rsn[0] = red | LRGCS;
  spf->conf.rsn[1] = lidx;
}

static void s_rmtwch (SPF * spf, int lit, int other1, int other2, int red) {
  int * p, blit, other, blit1, blit2, * w, * eow, tag;
  HTS * hts;
  //removing %s ternary watch %d blits %d %d,s_red2str (red), lit, other1, other2);
  hts = s_hts (spf, lit);
  p = w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  blit1 = (other1 << RMSHFT) | red | TRNCS;
  blit2 = (other2 << RMSHFT) | red | TRNCS;
  for (;;) {
    if (p == eow) return;
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == BINCS) continue;
    if (tag == IRRCS) { assert (spf->dense); continue; }
    other = *p++;
    if (blit == blit1 && other == other2) break;
    if (blit == blit2 && other == other1) break;
  }
  while (p < eow) p[-2] = p[0], p++;
  s_shrinkhts (spf, hts, p - w - 2);
}

static int s_ca (SPF * spf, int a, int b) {
  int c, res, prev, r0, tag, * rsn;
  AVar * av;
  res = 0;
  for (c = a; c; c = -prev) {
    assert (s_val (spf, c) > 0);
    av = s_avar (spf, c);
    assert (!av->mark);
    av->mark = 1;
    rsn = s_rsn (spf, c);
    r0 = rsn[0];
    tag = r0 & MASKCS;
    if (tag != BINCS) break;
    prev = r0 >> RMSHFT;
  }
  for (res = b; res; res = -prev) {
    av = s_avar (spf, res);
    if (av->mark) break;
    rsn = s_rsn (spf, res);
    r0 = rsn[0];
    tag = r0 & MASKCS;
    if (tag != BINCS) { res = 0; break; }
    prev = r0 >> RMSHFT;
  }
  for (c = a; c; c = -prev) {
    av = s_avar (spf, c);
    av->mark = 0;
    rsn = s_rsn (spf, c);
    r0 = rsn[0];
    tag = r0 & MASKCS;
    if (tag != BINCS) break;
    prev = r0 >> RMSHFT;
  }//least common ancestor of %d and %d is %d", a, b, res);
  return res;
}

static void s_rmlwch (SPF * spf, int lit, int red, int lidx) {
  int blit, tag, * p, * q, * w, * eow, ored, olidx;
  HTS * hts;
 
  hts = s_hts (spf, lit);
  p = w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  for (;;) {
    if (p == eow) return;
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == BINCS) continue;
    if (tag == IRRCS) { assert (spf->dense); continue; }
    olidx = *p++;
    if (tag == TRNCS) continue;
    ored = blit & REDCS;
    if (ored != red) continue;
    if (olidx == lidx) break;
  }
  for (q = p; q < eow; q++)
    q[-2] = q[0];

  s_shrinkhts (spf, hts, q - w - 2);
}

static int s_hbred (SPF * spf, int subsumed, int red) {
  int res = subsumed ? red : REDCS;// hyber binary learned clause 
  return res;
}

static void s_prop (SPF * spf, int lit) {
  int tag, val, val2, lidx, * c, * l, tmp, igd, dom, hbred, subsumed, unit;
  int * p, * q, * eos, blit, other, other2, other3, red, prev, i0, i1, i2;
  int visits;
  long delta;
  HTS * hts;
  // propagating lit over ternary and large clauses 
  hts = s_hts (spf, -lit);
  if (!hts->offset) return;
  q = s_hts2wchs (spf, hts);
  eos = q + hts->count;
  visits = 0;
  igd = 0;
  for (p = q; p < eos; p++) {
    visits++;
    blit = *p;
    tag = blit & MASKCS;
    if (tag == IRRCS) {
      assert (spf->dense);
      *q++ = blit;
      lidx = blit >> RMSHFT;
      c = s_idx2lits (spf, 0, lidx);
      unit = 0;
      for (l = c; (other = *l); l++) {
	val = s_val (spf, other);
	if (val > 0) break;
	if (val < 0) continue;
	if (unit) break;
	unit = other;
      }
      if (other) continue;
      if (unit) { s_flrce (spf, unit, 0, lidx); continue; }
      s_onflict (spf, 1, -lit, 0, lidx);
      p++;
      break;
    }
    red = blit & REDCS;
    other = (blit >> RMSHFT);
    val = s_val (spf, other);
    if (tag == BINCS) {
      *q++ = blit;
      if (val > 0) continue;
      if (red) {
	if (!spf->propred) continue;
	if (s_iselim (spf, other)) continue;
      }
      if (val < 0) {
	s_bonflict (spf, -lit, blit);
	p++;
	break;
      }
      s_f2rce (spf, other, -lit, red);
    } else if (tag == TRNCS) {
      *q++ = blit;
      other2 = *++p;
      *q++ = other2;
      if (val > 0) continue;
      if (red) {
	if (!spf->propred) continue;
	if (s_iselim (spf, other)) continue;
      }
      val2 = s_val (spf, other2);
      if (val2 > 0) continue;
      if (!val && !val2) continue;
      if (red && s_iselim (spf, other2)) continue;
      if (spf->igntrn && !igd) {
	i0 = spf->ignlits[0], i1 = spf->ignlits[1], i2 = spf->ignlits[2];
	if (i0 == -lit) {
	  if (i1 == other) { if (i2 == other2) { igd = 1; continue; } }
	  else if (i2 == other) { if (i1 == other2) { igd = 1; continue; } }
	} else if (i1 == -lit) {
	  if (i0 == other) { if (i2 == other2) { igd = 1; continue; } }
	  else if (i2 == other) { if (i0 == other2) { igd = 1; continue; } }
	} else if (i2 == -lit) {
	  if (i0 == other) { if (i1 == other2) { igd = 1; continue; } }
	  else if (i1 == other) { if (i0 == other2) { igd = 1; continue; } }
	}
      }
      if (val < 0 && val2 < 0) {
	s_tonflict (spf, -lit, blit, other2);
	p++;
	break;
      }
      if (!val) { tmp = other2; other2 = other; other = tmp; }
      if (spf->opts.lhbr.val && spf->level >= 1) {
	if (s_evel (spf, other) < 1) dom = lit;
	else {
	  dom = s_dom (spf, lit);
	  if (s_dom (spf, -other) != dom) goto NO_HBR_JUST_F3RCE;
	  dom = s_ca (spf, lit, -other);
	}
	subsumed = (dom == lit || dom == -other);
	if (subsumed && spf->distilling) goto NO_HBR_JUST_F3RCE;
	hbred = s_hbred (spf, subsumed, red);
 	//hyper binary resolved %s clause %d %d,s_red2str (hbred), -dom, other2;
	if (subsumed) {//subsumes %s ternary clause %d %d %d",s_red2str (red), -lit, other, other2);
	  s_rmtwch (spf, other2, other, -lit, red);
	  s_rmtwch (spf, other, other2, -lit, red);
	}
	delta = 0;
	if (dom == lit) { 
        //replace %s ternary watch %d blits %d %d with binary %d blit %d s_red2str(red,-lit,other,other2,-lit,-dom
	  blit = (other2 << RMSHFT) | BINCS | hbred;
	  q[-2] = blit;
	  q--;
	} else {
	  if (dom == -other) {
	   //removing %s ternary watch %d blits %d %d, s_red2str (red), -lit, other, other2);
	    q -= 2;
	  } 
          delta += s_wchbin (spf, -dom, other2, hbred);
	}
	delta += s_wchbin (spf, other2, -dom, hbred);
	if (delta) p += delta, q += delta, eos += delta;
	s_f2rce (spf, other2, -dom, hbred);
      } else {
NO_HBR_JUST_F3RCE:
       s_f3rce (spf, other2, -lit, other, red);
      }
    } else {
      if (val > 0) goto COPYL;
      if (red && !spf->propred) goto COPYL;
      lidx = p[1];
      if (lidx == spf->ignlidx) goto COPYL;
      c = s_idx2lits (spf, red, lidx);
      other2 = c[0];
      if (other2 == -lit) other2 = c[0] = c[1], c[1] = -lit;
      if (other2 != other) {
	other = other2;
	val = s_val (spf, other);
	blit = red;
	blit |= LRGCS;
	blit |= other2 << RMSHFT;
	if (val > 0) goto COPYL;
      }
      if (red && s_iselim (spf, other)) goto COPYL;
      val2 = INT_MAX;
      prev = -lit;
      for (l = c + 2; (other2 = *l); l++) {
	*l = prev;
	val2 = s_val (spf, other2);
	if (val2 >= 0) break;
	if (red && s_iselim (spf, other2)) break;
	prev = other2;
      }
     if (other2 && val2 >= 0) {
	c[1] = other2;
	assert (other == c[0]);
	delta = s_wchlrg (spf, other2, other, red, lidx);
	if (delta) p += delta, q += delta, eos += delta;
	p++;
	continue;
      }
      while (l > c + 2) {
	other3 = *--l;
	*l = prev;
	prev = other3;
      }
      if (other2 && val2 < 0) goto COPYL;
      if (val < 0) {
	s_onflict (spf, 1, -lit, red, lidx);
	break;
      }
      if (spf->opts.lhbr.val && spf->level >= 1) {
	dom = 0;
	for (l = c; (other2 = *l); l++) {
	  if (other2 == other) continue;
	  if (!s_evel (spf, other2)) continue;
	  assert (s_val (spf, other2) < 0);
	  if (!dom) dom = s_dom (spf, other);
	  if (dom != s_dom (spf, other2)) goto NO_HBR_JUST_FLRCE;
	}
	//dominator %d for %s clause", dom, s_red2str (red));
	dom = lit;
	for (l = c; (other2 = *l); l++) {
	  if (other2 == other) continue;
	  assert (s_val (spf, other2) < 0);
	  if (other2 == -lit) continue;
	  if (s_evel (spf, other2) < 1) continue;
	  if (dom == -other2) continue;
	  dom = s_ca (spf, dom, -other2);
	}
	//closest dominator %d", dom);
	subsumed = 0;
	for (l = c; !subsumed && (other2 = *l); l++)
	  subsumed = (dom == -other2);
	if (subsumed && spf->distilling) goto NO_HBR_JUST_FLRCE;
	hbred = s_hbred (spf, subsumed, red);// hyper binary resolved %s clause %d %d,

	if (subsumed) {//	subsumes %s large clause
	  s_rmlwch (spf, other, red, lidx);
	  if (red) { c[-1] = REMOVED; }
	  for (l = c; *l; l++) *l = REMOVED;
	  *l = REMOVED;
	}
	delta = 0;
	if (dom == lit) {// replacing %s large watch %d with binary watch %d blit %d
	  blit = (other << RMSHFT) | BINCS | hbred;
	  *q++ = blit, p++;
	} else {
	  if (subsumed) {// removing %s large watch %d", s_red2str (red), -lit
	    p++;
	  } else {// "%s binary clause %d %d becomes reasons for %d instead of %s large clause
	  }
	  delta += s_wchbin (spf, -dom, other, hbred);
	}
	delta += s_wchbin (spf, other, -dom, hbred);
        if (delta) p += delta, q += delta, eos += delta;
	s_f2rce (spf, other, -dom, hbred);
	if (subsumed) continue;
      } else {
NO_HBR_JUST_FLRCE:
	s_flrce (spf, other, red, lidx);
      }
COPYL:
      *q++ = blit;
      *q++ = *++p;
    }
  }
  while (p < eos) *q++ = *p++;
  s_shrinkhts (spf, hts, hts->count - (p - q));
}

static void s_prop2 (SPF * spf, int lit) {
  int other, blit, tag, val, red, visits;
  const int * p, * w, * eow;
  HTS * hts;
  // propagating %d over binary clauses,lit
  visits = 0;
  hts = s_hts (spf, -lit);
  w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    visits++;
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag != BINCS) continue;
    red = blit & REDCS;
    if (red && !spf->propred) continue;
    other = blit >> RMSHFT;
    val = s_val (spf, other);
    if (val > 0) continue;
    if (val < 0) { s_bonflict (spf, -lit, blit); break; }
    s_f2rce (spf, other, -lit, red);
  }
  spf->stats.visits.simp += visits;
}

static int s_bcp (SPF * spf) {
  int lit, cnt, next2 = spf->next, count = 0;
  while (!spf->conf.lit) {
    cnt = s_cntstk (&spf->trail);
    if (next2 < cnt) {
      lit = s_peek (&spf->trail, next2++);
      s_prop2 (spf, lit);
      continue;
    }
    if (spf->next >= cnt) break;
    lit = s_peek (&spf->trail, spf->next++);
    count++;
    s_prop (spf, lit);
  }
  spf->stats.props.simp += count;
  return !spf->conf.lit;
}

static int s_decision (SPF * spf, int lit) {
  int * rsn = s_rsn (spf, lit);
  int tag = rsn[0] & MASKCS;
  return tag == DECISION;
}

static void s_fitlir (SPF * spf, Lir * lir) {
  s_fitstk (spf, &lir->lits);
}

static void s_rmbwch (SPF * spf, int lit, int other, int red) {
  int * p, blit, blit1, * w, * eow, tag;
  HTS * hts;
  //removing %s binary watch %d blit %d, s_red2str (red), lit, other);
  hts = s_hts (spf, lit);
  p = w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  blit1 = (other << RMSHFT) | red | BINCS;
  for (;;) {
    if (p == eow) return;
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) { p++; continue; }
    if (tag == IRRCS) continue;
    //tag == BINCS
    if (blit == blit1) break;
  }
  while (p < eow) p[-1] = p[0], p++;
  s_shrinkhts (spf, hts, p - w - 1);
}

static int s_popesched (SPF * spf) {
  Stk * s = &spf->esched;
  int res, last, cnt, * p;
  EVar * ev;
  res = *s->start;
  //res, "popped");
  ev = s_evar (spf, res);
  ev->pos = -1;
  last = s_popstk (s);
  cnt = s_cntstk (s);
  if (!cnt) { assert (last == res); return res; }
  p = s_epos (spf, last);
  *p = 0;
  *s->start = last;
  s_edown (spf, last);
  return res;
}

static void s_decocc (SPF * spf, int lit) {
  int idx = abs (lit), old, sign = (lit < 0);
  EVar * ev = s_evar (spf, lit);
  if (!s_isfree (spf, lit)) return;
  ev->occ[sign] -= 1;
  old = s_ecalc (spf, ev);
  //dec occ of %d gives escore[%d] = %d with occs %d %d", lit, idx, ev->score, ev->occ[0], ev->occ[1], ev->score);
  if (ev->pos < 0) {
    if (spf->elm.pivot != idx) s_esched (spf, idx);
  } else if (old > ev->score) s_eup (spf, idx);
}

static void s_rmbcls (SPF * spf, int a, int b, int red) {
  s_rmbwch (spf, a, b, red);
  s_rmbwch (spf, b, a, red);  //removed %s binary clause %d %d", s_red2str (red), a, b);
  if (!red && spf->dense) s_decocc (spf, a), s_decocc (spf, b);
}

static void s_rmtcls (SPF * spf, int a, int b, int c, int red) {
  s_rmtwch (spf, a, b, c, red);
  s_rmtwch (spf, b, a, c, red);
  s_rmtwch (spf, c, a, b, red);  //removed %s ternary clause %d %d %d", s_red2str (red), a, b, c);
  if (!red && spf->dense)  s_decocc (spf, a), s_decocc (spf, b), s_decocc (spf, c);
}

static void s_rmlocc (SPF * spf, int lit, int lidx) {
  int search, blit, tag, * p, * q, * w, * eow;
  HTS * hts;

  hts = s_hts (spf, lit);
  search = (lidx << RMSHFT) | IRRCS;
  p = w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  do {
    assert (p < eow);
    blit = *p++;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
  } while (blit != search);
  for (q = p ; q < eow; q++)
    q[-1] =q[0];
  s_shrinkhts (spf, hts, q - w - 1);
}

static void s_rmlcls (SPF * spf, int lidx, int red) {
  int * c, * p, lit;
  c = s_idx2lits (spf, red, lidx);
  if (red || (!red && !spf->dense)) {
    s_rmlwch (spf, c[0], red, lidx);
    s_rmlwch (spf, c[1], red, lidx);
  }
  if (!red && spf->dense) {
    for (p = c; (lit = *p); p++) {
      s_rmlocc (spf, lit, lidx);
      s_decocc (spf, lit);
    }
  }
  if (red) { c[-1] = REMOVED; }
  for (p = c; *p; p++) *p = REMOVED;
  *p = REMOVED;
}

static void s_popnunmarkstk (SPF * spf, Stk * stk) {
  while (!s_mtstk (stk))
    s_avar (spf, s_popstk (stk))->mark = 0;
}

static int s_str (SPF * spf) {
  if (!spf->opts.elim.val) return 1;
  if (spf->stats.elm.count < spf->opts.elmnostr.val) return 0;
  if (spf->stats.elm.count > spf->opts.elmnostr.val) return 1;
  if (spf->eliminating) return 0;
  return 1;
}

static void s_dis (SPF * spf) {
  int blit, nblit, tag, red, * p, * q, * eow, * w;
  int idx, sign, lit, other, other2;
  Stk bins, trns;
  Val val, val2;
  HTS * hts;
  CLR (bins); CLR (trns);
  for (idx = 2; idx < spf->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = idx * sign;
      hts = s_hts (spf, lit);
      if (!hts->offset) continue;
      val = s_val (spf, lit);
      if (val || s_iselim (spf, lit))
	{ s_shrinkhts (spf, hts, 0); continue; }
      w = s_hts2wchs (spf, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	if (tag == IRRCS) continue;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	other = blit >> RMSHFT;
	val = s_val (spf, other);
	if (val > 0) continue;
	if (s_iselim (spf, other)) continue;
	if (tag == BINCS) {
	  assert (!val);
	  s_pushstk (spf, &bins, blit);
	  continue;
	}
	other2 = *p;
	val2 = s_val (spf, other2);
	if (val2 > 0) continue;
	if (s_iselim (spf, other2)) continue;
	if (val < 0) {
	  assert (val < 0 && !val2);
	  nblit = red | (other2<<RMSHFT) | BINCS;
	  s_pushstk (spf, &bins, nblit);
	  continue;
	}
	if (val2 < 0) {
	  assert (!val && val2 < 0);
	  nblit = red | (other<<RMSHFT) | BINCS;
	  s_pushstk (spf, &bins, nblit);
	  continue;
	}
	s_pushstk (spf, &trns, blit);
	s_pushstk (spf, &trns, other2);
      }
      q = w;
      for (p = bins.start; p != bins.top; p++) *q++ = *p;
      for (p = trns.start; p != trns.top; p++) *q++ = *p;
      s_shrinkhts (spf, hts, q - w);
      s_clnstk (&bins);
      s_clnstk (&trns);
    }
  s_relstk (spf, &bins);
  s_relstk (spf, &trns);
}

static void s_connaux (SPF * spf, int glue) {
  int lit, satisfied, lidx, size, red, act;
  const int * p, * c, * start, * top;
  int * q, * d;
  Stk * stk;
  Lir * lir;
  Val val;
  if (glue >= 0) {
    red = REDCS;
    lir = spf->red;
    stk = &lir->lits;
  } else red = 0, stk = &spf->irr;
  c = start = q = stk->start;
  top = stk->top;
  while (c < top) {
    act = *c;
    if (act == REMOVED) {
      for (p = c + 1; p < top && *p == REMOVED; p++) ;
      c = p;
      continue;
    }
    if (s_isact (act)) *q++ = *c++; else act = -1;
    p = c;
    d = q;
    satisfied = 0;
    while (assert (p < top), (lit = *p++)) {
      if (satisfied) continue;
      val = s_val (spf, lit);
      if (s_iselim (spf, lit)) assert (spf->eliminating), satisfied = 1;
      else if (val > 0) satisfied = 1;
      else if (!val) *q++ = lit;
    }
    if (satisfied || p == c + 1) {
      q = d - (act >= 0);
    } else if (!(size = q - d)) {
      q = d - (act >= 0);
      if (!spf->mt) {// empty clause during connection garbage collection phase
	spf->mt = 1;
      }
    } else if (size == 1) {
      q = d - (act >= 0);// unit during garbage collection
      s_unit (spf, d[0]);
    } else if (size == 2) {
      q = d - (act >= 0);
      s_wchbin (spf, d[0], d[1], red);
      s_wchbin (spf, d[1], d[0], red);
    } else if (size == 3) {
      q = d - (act >= 0);
      s_wchtrn (spf, d[0], d[1], d[2], red);
      s_wchtrn (spf, d[1], d[0], d[2], red);
      s_wchtrn (spf, d[2], d[0], d[1], red);
    } else {
      *q++ = 0;
      lidx = d  - start;
      (void) s_wchlrg (spf, d[0], d[1], red, lidx);
      (void) s_wchlrg (spf, d[1], d[0], red, lidx);
    }
    c = p;
  }
  stk->top = q;
}

static void s_con (SPF * spf) {
  for (int glue = -1; glue <=0; glue++) s_connaux (spf, glue);
}

static int s_ulit (int lit) { return 2*abs (lit) + (lit < 0); }

static int s_ilit (int ulit) {
  int res = ulit/2;
  if (ulit & 1) res = -res;
  return res;
}

static int s_maplit (int * map, int lit) {
  return map [ abs (lit) ] * lit_sign (lit);
}

static void s_mapstk (SPF * spf, int * map, Stk * lits) {
  int * p, * eol;
  eol = lits->top;
  for (p = lits->start; p < eol; p++)
    *p = s_maplit (map, *p);
}

static void s_mapglue (SPF * spf, int * map, Stk * lits) {
  int * p, * eol;
  eol = lits->top;
  for (p = lits->start; p < eol; p++)
    if (!s_isact (*p)) *p = s_maplit (map, *p);
}

static void s_maplits (SPF * spf, int * map) {
  s_mapstk (spf, map, &spf->irr);
  s_mapglue (spf, map, &spf->red[0].lits);
}

static void s_mapvars (SPF * spf, int * map, int nvars) {
  int i, oldnvars = spf->nvars;
  DVar * dvars;
  AVar * avars;
  Val * vals;
  int * i2e;

  if (nvars > 2) assert (nvars <= oldnvars);
  else nvars = 0;

  NEW (vals, nvars);
  for (i = 2; i < oldnvars; i++)
    if (s_isfree (spf, i))
      vals[map[i]] = spf->vals[i];
  DEL (spf->vals, spf->szvars);
  spf->vals = vals;

  NEW (i2e, nvars);
  for (i = 2; i < oldnvars; i++)
    if (s_isfree (spf, i))
      i2e[map[i]] = spf->i2e[i];
  DEL (spf->i2e, spf->szvars);
  spf->i2e = i2e;

  NEW (dvars, nvars);
  for (i = 2; i < oldnvars; i++)
    if (s_isfree (spf, i))
      dvars[map[i]] = spf->dvars[i];
  DEL (spf->dvars, spf->szvars);
  spf->dvars = dvars;

  NEW (avars, nvars);
  for (i = 2; i < oldnvars; i++)
    if (s_isfree (spf, i))
      avars[map[i]] = spf->avars[i];
  DEL (spf->avars, spf->szvars);
  spf->avars = avars;

  spf->nvars = spf->szvars = nvars;
  spf->stats.fixed.current = 0;
}

static void s_maphts (SPF * spf, int * map) {
  int idx, sign, lit, * w, *eow, * p, other, other2, blit, tag, red;
  int newblit, newother, newother2;
  HTS * hts;
  for (idx = 2; idx < spf->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = s_hts (spf, lit);
      if (!hts->count) continue;
      w = s_hts2wchs (spf, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	assert (tag == BINCS || tag == TRNCS || tag == LRGCS);
	red = blit & REDCS;
	other = blit >> RMSHFT;
	newother = s_maplit (map, other);
	newblit = (newother << RMSHFT) | tag | red;
	*p = newblit;
	if (tag == BINCS) continue;
	other2 = *++p;
	if (tag == LRGCS) continue;
	assert (tag == TRNCS);
	newother2 = s_maplit (map, other2);
	*p = newother2;
      }
    }
}

static void s_maptrail (SPF * spf, int * map) {
  int * p, * q, src, dst;
  for (p = spf->trail.start; p < spf->trail.top; p++)
    if (s_evel (spf, *p) > 0) break;
  for (q = spf->trail.start; p < spf->trail.top; p++) {
    src = *p;
    dst = s_maplit (map, src);
    *q++ = dst;
  }
  spf->trail.top = q;
  spf->flushed = spf->next = s_cntstk (&spf->trail);
}

static int s_ptrjmp (int * repr, int max, int start) {
  int next, idx, res, sgn, tmp;
  next = start;
  do {
    res = next;
    idx = abs (res);
    sgn = lit_sign (res);
    next = repr[idx];
    next *= sgn;
  } while (next);
  tmp = start;
  while (tmp != res) {
    idx = abs (tmp), sgn = lit_sign (tmp);
    next = repr[idx] * sgn;
    repr[idx] = sgn * res;
    tmp = next;
  }
  return res;
}

static int s_irepr (SPF * spf, int lit) 
{
  return s_ptrjmp (spf->repr, spf->nvars - 1, lit);
}

static void s_mapext (SPF * spf, int * map) { //mapping external to internal;
  int eidx, ilit, mlit;
  Ext * ext;
  for (eidx = 1; eidx <= spf->maxext; eidx++) {
    ext = spf->ext + eidx;
    if (ext->equiv) continue;
    ilit = ext->repr;
    mlit = s_maplit (map, ilit);
    ext->repr = mlit;
  }
}

static void s_map (SPF * spf) {
  int idx, ridx, size, dst, count, * map, oldnvars, repr;
  AVar * av, * rv;;
  Val val;
  size = 0;
  for (idx = 2; idx < spf->nvars; idx++) {
    av = s_avar (spf, idx);
    if (av->type == ELIMVAR) continue;
    if (av->type != FREEVAR) continue;
    size++;
  }
  // mapping %d remaining variables, size
  oldnvars = spf->nvars;
  NEW (map, s_max (oldnvars, 2));
  map[0] = 0, map[1] = 1;
  count = 0;
  dst = 2;
  for (idx = 2; idx < spf->nvars; idx++) {
    if (map[idx]) continue;
    av = s_avar (spf, idx);
    if (av->type == FREEVAR) {
      if (map[idx]) continue;//mapping free %d to %d", idx, count + 2);
      map[idx] = count + 2;
      count++;
    } else if (av->type == EQUIVAR) {
      repr = s_irepr (spf, idx);
      ridx = abs (repr);
      if (ridx < idx) {
	//assert (map[ridx]);
      } else if (!map[ridx]) {
	rv = s_avar (spf, repr);
	if (rv->type == FREEVAR) {
	  map[ridx] = count + 2;
	  count++;
	} else {
	  assert (s_avar (spf, repr)->type == FIXEDVAR);
	  val = spf->vals[ridx];//mapping assigned representative %d to %d", ridx, val);
	}
      }
      dst = s_maplit (map, repr);//mapping equivalent %d to %d", idx, dst);
      map[idx] = dst;
    } else if (av->type == FIXEDVAR) {
      val = spf->vals[idx];//mapping assigned %d to %d", idx, (int) val);
      map[idx] = val;
    } else map[idx] = 0;
  }
  s_maptrail (spf, map);
  s_mapvars (spf, map, size + 2);
  s_maplits (spf, map);
  s_mapstk (spf, map, &spf->dsched);
  s_mapext (spf, map);
  s_maphts (spf, map);
  DEL (map, s_max (oldnvars, 2));
  if (spf->repr) DEL (spf->repr, oldnvars);
  s_dreschedule (spf);
}

static int s_fixedoreq (SPF * spf) {  return spf->stats.fixed.sum + spf->stats.equiv.sum;}
static void s_fitlirs (SPF * spf) {    s_fitlir (spf, spf->red);}

void s_clearMap (SPF * spf) 
{  if (!spf->eliminating && !spf->blocking && s_fixedoreq (spf) == 0) return;
   if (spf->level > 0) s_backtrack (spf, 0);
   for (;;) {
     s_dis (spf);
     s_con (spf);
     if (!spf->mt && (unsigned)spf->next == s_cntstk (&spf->trail)) break;
     if (!s_bcp (spf)) {// empty clause after propagating garbage collection unit
         spf->mt = 1;
         break;
      }
  }
  s_dreschedule (spf);
  s_map (spf);
  s_fitlirs (spf);
}

void s_iassume (SPF * spf, int lit) {
  spf->level++;
  s_assign (spf, lit, DECISION, 0);
}

static void s_dcpdis (SPF * spf) {
  int idx, sign, lit, tag, blit, red, other, other2, i;
  const int * w, * p, * eow;
  Val val;
  HTS * hts;
  Stk * s;
  assert (s_mtstk (&spf->dis.irr.bin));
  assert (s_mtstk (&spf->dis.irr.trn));
  assert (s_mtstk (&spf->dis.red.bin));
  assert (s_mtstk (&spf->dis.red.trn));
  for (idx = 2; idx < spf->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = s_hts (spf, lit);
      if (!hts->offset) continue;
      w = s_hts2wchs (spf, hts);
      eow = w + hts->count;
      hts->count = hts->offset = 0;
      val = s_val (spf, lit);
      if (val > 0) continue;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	val = s_val (spf, other);
	if (val > 0) continue;
	red = blit & REDCS;
	if (red && !s_isfree (spf, other)) continue;
	if (tag == BINCS) {
	  s = red ? &spf->dis.red.bin : &spf->dis.irr.bin;
	} else {// (tag == TRNCS);
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	  val = s_val (spf, other2);
	  if (val > 0) continue;
	  if (red && !s_isfree (spf, other2)) continue;
	  s = red ? &spf->dis.red.trn : &spf->dis.irr.trn;
	  s_pushstk (spf, s, other2);
	}
	s_pushstk (spf, s, other);
	s_pushstk (spf, s, lit);
	s_pushstk (spf, s, 0);
      }
    }
  s_rststk (&spf->wchs, 2);
  spf->wchs.top[-1] = INT_MAX;
  for (i = 0; i < MAXLDFW; i++) spf->freewchs[i] = INT_MAX;
  spf->nfreewchs = 0;
}

static void s_dcpclnstk (SPF * spf, int red, Stk * s) {
  int oldsz, newsz, lit, mark, satisfied, repr, act;
  const int * p, * c, * eos = s->top;
  int * start, * q, * r, * d;
  Stk * t;
  Val val;
  q = start = s->start;
  for (c = q; c < eos; c = p + 1) {
    act = *c;
    if (act == REMOVED) {
      for (p = c + 1; p < eos && *p == REMOVED; p++)
	;
      assert (p >= eos || *p < NOTALIT || s_isact (*p));
      p--;
      continue;
    }
    if (s_isact (act)) *q++ = *c++; else act = -1;
    d = q;
    satisfied = 0;
    for (p = c; assert (p < eos), (lit = *p); p++) {
      assert (lit < NOTALIT);
      if (satisfied) continue;
      repr = s_irepr (spf, lit);
      val = s_val (spf, repr);
      if (val > 0) { satisfied = 1; continue; }
      if (val < 0) continue;
      mark = s_marked (spf, repr);
      if (mark < 0) { satisfied = 1; continue; }
      if (mark > 0) continue;
      s_mark (spf, repr);
      *q++ = repr;
    }
    oldsz = p - c;
    for (r = d; r < q; r++) s_unmark (spf, *r);
    if (satisfied || !oldsz) { q = d - (act >= 0); continue; }
    newsz = q - d;
    if (newsz >= 4) {
      assert (act < 0 || d[-1] == act);
      *q++ = 0;
    } else if (!newsz) {  //found empty clause while cleaning decompostion");
      spf->mt = 1;
      q = d - (act >= 0);
    } else if (newsz == 1) {//new unit %d while cleaning decomposition", d[0]);
      s_unit (spf, d[0]);
      q = d - (act >= 0);
    } else if (newsz == 2) {
      t = red ? &spf->dis.red.bin : &spf->dis.irr.bin;
      if (s != t) {
	s_pushstk (spf, t, d[0]);
	s_pushstk (spf, t, d[1]);
	s_pushstk (spf, t, 0);
	q = d - (act >= 0);
      } else *q++ = 0;
    } else {
      assert (newsz == 3);
      t = red ? &spf->dis.red.trn : &spf->dis.irr.trn;
      if (s != t) {
	s_pushstk (spf, t, d[0]);
	s_pushstk (spf, t, d[1]);
	s_pushstk (spf, t, d[2]);
	s_pushstk (spf, t, 0);
	q = d - (act >= 0);
      } else *q++ = 0;
    }
  }
  s->top = q;
}

static void s_dcpconnaux (SPF * spf, int red, int glue, Stk * s) {
  int * start = s->start, * q, * d, lit, size, lidx, act;
  const int * p, * c, * eos = s->top;
  q = start;
  for (c = q; c < eos; c = p + 1) {
    if (s_isact (act = *c)) *q++ = *c++; else act = -1;
    d = q;
    for (p = c; (lit = *p); p++) {
      assert (!spf->repr[abs (lit)]);
      assert (!spf->vals[abs (lit)]);
      *q++ = lit;
    }
    size = q - d;
    if (size == 2) {
      q = d - (act >= 0);
      s_wchbin (spf, d[0], d[1], red);
      s_wchbin (spf, d[1], d[0], red);
    } else if (size == 3) {
      q = d - (act >= 0);
      s_wchtrn (spf, d[0], d[1], d[2], red);
      s_wchtrn (spf, d[1], d[0], d[2], red);
      s_wchtrn (spf, d[2], d[0], d[1], red);
    } else {
      assert (size > 3);
      *q++ = 0;
      lidx = d - start;
      (void) s_wchlrg (spf, d[0], d[1], red, lidx);
      (void) s_wchlrg (spf, d[1], d[0], red, lidx);
    }
  }
  s->top = q;
}

static void s_dcpcon (SPF * spf) {
  Lir * lir;
  s_dcpconnaux (spf, 0, 0, &spf->dis.irr.bin);
  s_dcpconnaux (spf, REDCS, 0, &spf->dis.red.bin);
  s_dcpconnaux (spf, 0, 0, &spf->dis.irr.trn);
  s_dcpconnaux (spf, REDCS, 0, &spf->dis.red.trn);
  s_relstk (spf, &spf->dis.irr.bin);
  s_relstk (spf, &spf->dis.irr.trn);
  s_relstk (spf, &spf->dis.red.bin);
  s_relstk (spf, &spf->dis.red.trn);
  s_dcpconnaux (spf, 0, 0, &spf->irr);
  lir = spf->red;
  s_dcpconnaux (spf, REDCS, 0, &lir->lits);
}

static void s_dcpcln (SPF * spf) {
  int old;
  Lir * lir;
  do {
    old = spf->stats.fixed.current;
    s_dcpclnstk (spf, 0, &spf->irr);
    s_dcpclnstk (spf, 0, &spf->dis.irr.bin);
    s_dcpclnstk (spf, 0, &spf->dis.irr.trn);
    s_dcpclnstk (spf, REDCS, &spf->dis.red.bin);
    s_dcpclnstk (spf, REDCS, &spf->dis.red.trn);
    lir = spf->red;
    s_dcpclnstk (spf, REDCS, &lir->lits);
  } while (old < spf->stats.fixed.current);
}

static void s_emerge (SPF * spf, int ilit0, int ilit1) {
  int elit0 = spf->i2e[abs (ilit0)] * lit_sign (ilit0);
  int elit1 = spf->i2e[abs (ilit1)] * lit_sign (ilit1);
  int repr0 = s_erepr (spf, elit0);
  int repr1 = s_erepr (spf, elit1);
  Ext * ext0 = s_elit2ext (spf, repr0);
  if (repr0 < 0) repr0 *= -1, repr1 *= -1;
  ext0->equiv = 1;
  ext0->repr = repr1;//merging external literals %d and %d", repr0, repr1);
 }

static void s_imerge (SPF * spf, int lit, int repr) {
  int idx = abs (lit);
  AVar * av = s_avar (spf, idx);
  if (lit < 0) repr = -repr;
  av->type = EQUIVAR;
  spf->repr[idx] = repr;
  spf->stats.prgss++;
  spf->stats.equiv.sum++;
  s_emerge (spf, idx, repr);
}

static int s_cmprepr (SPF * spf, int a, int b) 
{ int res;
  if ((res = (abs (a) - abs (b)))) return res;
  return a - b;
}

static int s_tarjan (SPF * spf) {
  int * dfsimap, * mindfsimap, idx, oidx, sign, lit, blit, tag, other;
  int dfsi, mindfsi, ulit, uother, tmp, repr, res, sgn, frozen;
  const int * p, * w, * eow;
  Stk stk, component;
  AVar * av;
  HTS * hts;
  if (!spf->nvars) return 1;
 
  dfsi = 0;
  NEW (dfsimap, 2*spf->nvars);//,int *);
  NEW (mindfsimap, 2*spf->nvars);//,int *);
  NEW (spf->repr, spf->nvars);//,int *);
  CLR (stk); CLR (component);
  res = 1;
  for (idx = 2; idx < spf->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      ulit = s_ulit (lit);
      tmp = dfsimap[ulit];
      if (tmp) continue;
      s_pushstk (spf, &stk, lit);
      while (!s_mtstk (&stk)) {
	lit = s_popstk (&stk);
	if (lit) {
	  ulit = s_ulit (lit);
	  if (dfsimap[ulit]) continue;
	  dfsimap[ulit] = mindfsimap[ulit] = ++dfsi;
	  s_pushstk (spf, &component, lit);
	  s_pushstk (spf, &stk, lit);
	  s_pushstk (spf, &stk, 0);
	  hts = s_hts (spf, -lit);
	  if (!hts->offset) continue;
	  w = s_hts2wchs (spf, hts);
	  eow = w + hts->count;
	  for (p = w; p < eow; p++) {
	    blit = *p;
	    tag = blit & MASKCS;
	    if (tag != BINCS) { p++; continue; }
	    other = blit >> RMSHFT;
	    uother = s_ulit (other);
	    tmp = dfsimap[uother];
	    if (tmp) continue;
	    s_pushstk (spf, &stk, other);
	  }
	} else {
	  lit = s_popstk (&stk);
	  ulit = s_ulit (lit);
	  mindfsi = dfsimap[ulit];
	  hts = s_hts (spf, -lit);
	  w = s_hts2wchs (spf, hts);
	  eow = w + hts->count;
	  for (p = w; p < eow; p++) {
	    blit = *p;
	    tag = blit & MASKCS;
	    if (tag != BINCS) { p++; continue; }
	    other = blit >> RMSHFT;
	    uother = s_ulit (other);
	    tmp = mindfsimap[uother];
	    if (tmp >= mindfsi) continue;
	    mindfsi = tmp;
	  }
	  if (mindfsi == dfsimap[ulit]) {
	    repr = lit;
	    for (p = component.top - 1; (other = *p) != lit; p--) {
	      if (s_cmprepr (spf, other, repr) < 0) repr = other;
	    }
	    while ((other = s_popstk (&component)) != lit) {
	      mindfsimap[s_ulit (other)] = INT_MAX;
	      if (other == repr) continue;
	      if (other == -repr) {//empty clause since repr[%d] = %d", repr, other);
		spf->mt = 1; res = 0; goto DONE;
	      }
	      sgn = lit_sign (other);
	      oidx = abs (other);
	      tmp = spf->repr[oidx];
	      if (tmp == sgn * repr) continue;//"repr[%d] = %d", oidx, sgn * repr);
	      if (tmp) {//empty clause since repr[%d] = %d and repr[%d] = %d",oidx, tmp, oidx, sgn * repr);
		spf->mt = 1; res = 0; goto DONE;
	      } else {
		av = s_avar (spf, oidx);
		assert (sgn*oidx == other);
		if (av->type == FREEVAR) s_imerge (spf, other, repr);
		else assert (av->type == FIXEDVAR);
	      }
	    }
	    mindfsimap[s_ulit (lit)] = INT_MAX;
	    if (frozen) {
	     //equivalence class of %d is frozen", repr);
	    }
	  } else mindfsimap[ulit] = mindfsi;
	}
      }
    }
  }
DONE:
  s_relstk (spf, &stk);
  s_relstk (spf, &component);
  DEL (mindfsimap, 2*spf->nvars);
  DEL (dfsimap, 2*spf->nvars);
  if (!res) DEL (spf->repr, spf->nvars);
  return res;
}

static int64_t s_steps (SPF * spf) {
  int64_t steps = spf->stats.props.simp;
  steps += spf->stats.trd.steps;
  steps += spf->stats.unhd.steps;
  steps += spf->stats.elm.steps;
  return steps;
}

static int s_terminate (SPF * spf) {
  int64_t steps;
  int res;
  if (!spf->term.fun) return 0;
  if (spf->term.done) return 1;
  steps = s_steps (spf);
  if (steps < spf->limits.term.steps) return 0;
  res = spf->term.fun (spf->term.state);
  if (res) spf->term.done = res;
  else spf->limits.term.steps = steps + spf->opts.termint.val;
  return  res;
}

static int s_syncunits (SPF * spf) {
  int * units, * eou, * p, elit, erepr, ilit, res, count = 0;
  void (*produce)(void*, int);
  int64_t steps;
  Ext * ext;
  Val val;
  if (!spf->units.consume.fun) return 1;
  steps = s_steps (spf);
  if (steps < spf->limits.sync.steps) return 1;
  spf->limits.sync.steps = steps + spf->opts.syncint.val;
  spf->units.consume.fun (spf->units.consume.state, &units, &eou);
  if (units == eou) return 1;
  produce = spf->units.produce.fun;
  spf->units.produce.fun = 0;
  for (p = units; !spf->mt && p < eou; p++) {
    elit = *p;
    erepr = s_erepr (spf, elit);
    ext = s_elit2ext (spf, erepr);
    ilit = ext->repr;
    if (!ilit) continue;
    if (erepr < 0) ilit = -ilit;
    if (ilit == 1) continue;
    if (ilit == -1) val = -1;
    else {
      val = s_val (spf, ilit);
      if (val && s_evel (spf, ilit)) val = 0;
    }
    if (val == 1) continue;
    if (val == -1) {//mismatching synchronized external unit %d", elit);
      if (spf->level > 0) s_backtrack (spf, 0);
      spf->mt = 1;
    } else if (!s_isfree (spf, ilit)) continue;
    else {
      if (spf->level > 0) s_backtrack (spf, 0);
      s_unit (spf, ilit);//importing internal unit %d external %d,spf->tid, ilit, elit);
      count++;
    }
  }
  spf->units.produce.fun = produce;
  if (spf->units.consumed.fun) 
    spf->units.consumed.fun (spf->units.consumed.state, count);
  if (spf->mt) return 0;
  if (!count) return 1;
  if (spf->distilling) { assert (!spf->propred); spf->propred = 1; }
  res = s_bcp (spf);
  if (spf->distilling) { assert (spf->propred); spf->propred = 0; }
  if(!res && !spf->mt) spf->mt = 1;
  return res;
}

static int s_prbpull (SPF * spf, int lit, int probe) {
  AVar * av;
  av = s_avar (spf, lit);
  if (av->mark) return 0;
  if (!s_evel (spf, lit)) return 0;
  av->mark = 1;
  s_pushstk (spf, &spf->seen, -lit);//pulled in literal %d during probing analysis", -lit);
  return 1;
}

static int s_prbana (SPF * spf, int probe) {
  int open, lit, r0, r1, tag, red, other, res, * p, * rsn;
  res = open = 0;
  lit = spf->conf.lit;
  r0 = spf->conf.rsn[0], r1 = spf->conf.rsn[1];
  open = s_prbpull (spf, lit, probe);
  //starting probing analysis with reason of literal %d", lit);
  for (;;) {
    tag = r0 & MASKCS;
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      if (s_prbpull (spf, other, probe)) open++;
      if (tag == TRNCS && s_prbpull (spf, r1, probe)) open++;
    } else {
      red = r0 & REDCS;
      p = s_idx2lits (spf, red, r1);
      while ((other = *p++)) open += s_prbpull (spf, other, probe);
    }//open %d antecedents in probing analysis", open-1);
    while (!s_marked (spf, lit = s_popstk (&spf->trail)))
      s_unassign (spf, lit);
    s_unassign (spf, lit);
    if (!--open) { res = lit; break; }
    //analyzing reason of literal %d in probing analysis next", lit);
    rsn = s_rsn (spf, lit);
    r0 = rsn[0], r1 = rsn[1];
  }
//  if (res == probe) probing analysis returns the probe %d as 1st UIP");
//  else probing analysis returns different 1st UIP %d and not probe %d",res, probe);
  s_popnunmarkstk (spf, &spf->seen);
  return res;
}

int s_ideref (SPF * spf, int elit) {
  int ilit, res, repr;
  Ext * ext;
  if (abs (elit) > spf->maxext) return -1;
  repr = s_erepr (spf, elit);
  ext = s_elit2ext (spf, repr);
  res = ext->val;
  if (!res) {
    ilit = ext->repr;
    res = ilit ? s_cval (spf, ilit) : 0;
  }
  if (repr < 0) res = -res;
  return res;
}

int s_probe (SPF * spf) {
  int lit, root, units, lifted, ok, old, first, dom;
  int nprobes, probed, changed, success = 0; 
  int idx;
  Stk probes, lift, saved;
  unsigned pos, delta;
  const int * p;
  int64_t limit;
  Val val;

  if (!spf->nvars) return 1;
  if (!spf->opts.probe.val) return 1;
  
  spf->simp = 1;
  if (spf->level > 0) s_backtrack (spf, 0);
  spf->measureagility = 0;
  spf->probing = 1;

  CLR (lift); CLR (probes); CLR (saved);
  for (idx = 2; idx < spf->nvars; idx++) {
    if (!s_isfree (spf, idx)) continue;// new probe %d, idx
    s_pushstk (spf, &probes, idx);
  }
  nprobes = s_cntstk (&probes);

  lifted = units = 0;
  probed = 0;

  if (!nprobes) goto DONE;
  pos = s_rand (spf) % nprobes;
  delta = s_rand (spf) % nprobes;
  if (!delta) delta++;
  while (s_gcd (delta, nprobes) > 1)
    if (++delta == (unsigned)nprobes) delta = 1;//probing start %u delta %u mod %u", pos, delta, nprobes
  limit = spf->opts.prbmaxeff.val/10;
  if (limit < spf->opts.prbmineff.val) limit = spf->opts.prbmineff.val;
  if (limit > spf->opts.prbmaxeff.val) limit = spf->opts.prbmaxeff.val;
  // probing with penalty %d", spf->limits.prb.pen
  if (spf->limits.prb.pen < 0) limit <<= -spf->limits.prb.pen;
  if (spf->limits.prb.pen > 0) limit >>= spf->limits.prb.pen;
  // probing with up to %lld propagations,limit
  limit += spf->stats.visits.simp;
  changed = first = 0;
  for (;;) {
    if (spf->stats.visits.simp >= limit) break;
    if (s_terminate (spf)) break;
    if (!s_syncunits (spf)) break;
    assert (pos < (unsigned) nprobes);
    root = probes.start[pos];
    if (root == first) {
       if (changed) changed = 0; else break;
    }
    if (!first) first = root;
    pos += delta;
    if (pos >= (unsigned) nprobes) pos -= nprobes;
    if (s_val (spf, root)) continue;
    probed++;
    s_clnstk (&lift);
    s_clnstk (&saved);// next probe %d positive phase, root
    //-------------------------spf->level==0
    s_iassume (spf, root);
    old = s_cntstk (&spf->trail);
    ok = s_bcp (spf);
    dom = 0;
    if (ok) {
      s_clnstk (&saved);
      for (p = spf->trail.start + old; p < spf->trail.top; p++)
	s_pushstk (spf, &saved, *p);
    } else dom = s_prbana (spf, root);
    s_backtrack (spf, 0);
    if (!ok) {// failed literal %d on probing, dom, root
      s_pushstk (spf, &lift, -dom);
      goto MERGE;
    }// next probe %d negative phase, -root
    //---------------------------------------
    s_iassume (spf, -root);
    ok = s_bcp (spf);
    if (ok) {
      for (p = saved.start; p < saved.top; p++) {
	lit = *p;
	val = s_val (spf, lit);
	if (val <= 0) continue;
	lifted++;
	s_pushstk (spf, &lift, lit);// lifted lit
      }
    } else dom = s_prbana (spf, -root);
    s_backtrack (spf, 0);
   //------------------------------------------------
    if (!ok) {// failed literal %d on probing %d, dom, -root
      s_pushstk (spf, &lift, -dom);
    }
MERGE:
    while (!s_mtstk (&lift)) {
      lit = s_popstk (&lift);
      val = s_val (spf, lit);
      if (val > 0) continue;
      if (val < 0) goto EMPTY;
      s_unit (spf, lit);
      success = changed = 1;
      units++;
      if (s_bcp (spf)) continue;
EMPTY:
      spf->mt = 1;// empty clause after propagating lifted and failed literals
      goto DONE;
    }
  }
DONE:
  s_relstk (spf, &lift);
  s_relstk (spf, &probes);
  s_relstk (spf, &saved);
  spf->measureagility = 1;
  spf->probing = 0;
  spf->simp = 0;
  if (success && spf->limits.prb.pen > MINPEN) spf->limits.prb.pen--;
  if (!success && spf->limits.prb.pen < MAXPEN) spf->limits.prb.pen++;
  return !spf->mt;
}

static int s_small (SPF * spf) {
  int maxirrlidx = s_cntstk (&spf->irr);
  if (maxirrlidx > MAXIRRLIDX) return 0;
  return  1;
}

static void s_dense (SPF * spf) {
  int lit, lidx, idx, other, other2, blit, sign, tag, red;
  const int * start, * top, * c, * p, * eow;
  int * q, * w;
  EVar * ev;
  HTS * hts;
 
  other2 = 0;
  NEW (spf->evars, spf->nvars);
  for (idx = 2; idx < spf->nvars; idx++) {
    ev = spf->evars + idx;
    ev->pos = -1;
  }
  for (idx = 2; idx < spf->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = s_hts (spf, lit);
      if (!hts->count) continue;
      q = w = s_hts2wchs (spf, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	*q++ = blit;
	assert (tag != LRGCS);
	if (tag == TRNCS) *q++ = *p;
	if (red) continue;
	other = blit >> RMSHFT;
	if (abs (other) < idx) continue;
	if (tag == TRNCS) {
	  other2 = *p;
	  if (abs (other2) < idx) continue;
	}
	s_incocc (spf, lit);
	s_incocc (spf, other);
	if (tag == BINCS) continue;
	assert (tag == TRNCS);
	s_incocc (spf, other2);
      }
      s_shrinkhts (spf, hts, q - w);
    }
    // counted %d occurrences in small irredundant clauses
  start = spf->irr.start;
  top = spf->irr.top;
  for (c = start; c < top; c = p + 1) {
    p = c;
    if (*c >= NOTALIT) continue;
    lidx = c - start;
    assert (lidx < MAXIRRLIDX);
    blit = (lidx << RMSHFT) | IRRCS;
    for (; (lit = *p); p++) {
      hts = s_hts (spf, lit);
      s_pushwch (spf, hts, blit);
      s_incocc (spf, lit);
    }
  }
  for (idx = 2; idx < spf->nvars; idx++) {
    ev = s_evar (spf, idx);
    if (ev->pos >= 0) continue;
    s_esched (spf, idx);
  }
  spf->dense = 1;
}

static void s_sparse (SPF * spf) {
  int idx, sign, lit, count, blit, tag;
  int * w, *p, * eow, * q;
  HTS * hts;
  count = 0;
  for (idx = 2; idx < spf->nvars; idx++)
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = s_hts (spf, lit);
      if (!hts->count) continue;
      w = s_hts2wchs (spf, hts);
      eow = w + hts->count;
      for (p = q = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == IRRCS) { count++; continue; }
	*q++ = blit;
	if (tag == BINCS) continue;
	assert (tag == LRGCS || tag == TRNCS);
	*q++ = *++p;
      }
      s_shrinkhts (spf, hts, q - w);
    }
  DEL (spf->evars, spf->nvars);
  s_relstk (spf, &spf->esched); //removed %d full irredundant occurrences", count);
  spf->dense = 0;
}

static int s_m2i (SPF * spf, int mlit) {
  int res, midx = abs (mlit);
  assert (0 < midx);
  res = s_peek (&spf->elm.m2i, midx);
  if (mlit < 0) res = -res;
  return res;
}

static int s_i2m (SPF * spf, int ilit) {
  AVar * av = s_avar (spf, ilit);
  int res = av->mark;
  if (!res) {
    res = s_cntstk (&spf->seen) + 1;
    av->mark = res;
    s_pushstk (spf, &spf->seen, abs (ilit));
    s_pushstk (spf, &spf->elm.lsigs, 0);
    s_pushstk (spf, &spf->elm.lsigs, 0);
    s_pushstk (spf, &spf->elm.noccs, 0);
    s_pushstk (spf, &spf->elm.noccs, 0);
    s_pushstk (spf, &spf->elm.mark, 0);
    s_pushstk (spf, &spf->elm.mark, 0);
    s_pushstk (spf, &spf->elm.occs, 0);
    s_pushstk (spf, &spf->elm.occs, 0);
    s_pushstk (spf, &spf->elm.m2i, abs (ilit));
    //mapped internal variable %d to marked variable %d", abs (ilit), res);
  }
  if (ilit < 0) res = -res;
  return res;
}

static unsigned s_sig (int lit) {
  unsigned ulit = s_ulit (lit), res;
  ulit -= 2;
  res = (1u << (ulit & 31));
  return res;
}

static void s_addecl (SPF * spf, const int * c) {
  int ilit, mlit, umlit, size = 0, next, prev;
  unsigned csig = 0;
  const int * p;
  Val val;// copying irredundant clause
  spf->stats.elm.steps++;
  size = 0;
  for (p = c; (ilit = *p); p++) {
    val = s_val (spf, ilit);
    if (val < 0) continue;
    size++;
    if (abs (ilit) == spf->elm.pivot) continue;
    mlit = s_i2m (spf, ilit);
    assert (abs (mlit) != 1);
    csig |= s_sig (mlit);
  }
  next = s_cntstk (&spf->elm.lits);
  for (p = c; (ilit = *p); p++) {
    val = s_val (spf, ilit);
    if (val < 0) continue;
    mlit = s_i2m (spf, ilit);
    s_pushstk (spf, &spf->elm.lits, mlit);
    umlit = s_ulit (mlit);
    prev = s_peek (&spf->elm.occs, umlit);
    s_pushstk (spf, &spf->elm.next, prev);
    s_poke (&spf->elm.occs, umlit, next++);
    s_pushstk (spf, &spf->elm.csigs, csig);
    s_pushstk (spf, &spf->elm.sizes, size);
    spf->elm.noccs.start[umlit]++;
    spf->elm.lsigs.start[umlit] |= csig;
  }
  s_pushstk (spf, &spf->elm.lits, 0);
  s_pushstk (spf, &spf->elm.next, 0);
  s_pushstk (spf, &spf->elm.csigs, 0);
  s_pushstk (spf, &spf->elm.sizes, 0);
  spf->elm.necls++;
 //spf->elm.lits.start + lidx, "copied and mapped clause");
}

static int s_ecls (SPF * spf, int lit) {
  int blit, tag, red, other, lidx, count;
  const int * p, * w, * eow, * c;
  int d[4];
  HTS * hts;
  //copying irredundant clauses with %d", lit);
  count = 0;
  hts = s_hts (spf, lit);
  if (!hts->count) return 0;
  w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (red) continue;
    if (tag == BINCS || tag == TRNCS) {
      d[0] = lit;
      other = blit >> RMSHFT;
      d[1] = other;
      if (tag == TRNCS) d[2] = *p, d[3] = 0;
      else d[2] = 0;
      c = d;
    } else {//tag == IRRCS);
      lidx = (tag == IRRCS) ? (blit >> RMSHFT) : *p;
      c = s_idx2lits (spf, 0, lidx);
    }
    s_addecl (spf, c);
    count++;
  }
  return count;
}

static void s_rstecls (SPF * spf)  {
  s_clnstk (&spf->elm.lits);
  s_clnstk (&spf->elm.next);
  s_clnstk (&spf->elm.csigs);
  s_clnstk (&spf->elm.lsigs);
  s_clnstk (&spf->elm.sizes);
  s_clnstk (&spf->elm.occs);
  s_clnstk (&spf->elm.noccs);
  s_clnstk (&spf->elm.mark);
  s_clnstk (&spf->elm.m2i);
  s_popnunmarkstk (spf, &spf->seen);
  spf->elm.pivot = 0;
}

static void s_relecls (SPF * spf)  {
  s_relstk (spf, &spf->elm.lits);
  s_relstk (spf, &spf->elm.next);
  s_relstk (spf, &spf->elm.csigs);
  s_relstk (spf, &spf->elm.lsigs);
  s_relstk (spf, &spf->elm.sizes);
  s_relstk (spf, &spf->elm.occs);
  s_relstk (spf, &spf->elm.noccs);
  s_relstk (spf, &spf->elm.mark);
  s_relstk (spf, &spf->elm.m2i);
  s_relstk (spf, &spf->clv);
}

static int spf2manyoccs4elm (SPF * spf, int lit) {
  return s_hts (spf, lit)->count > spf->opts.elmocclim.val;
}

static int s_chkoccs4elmlit (SPF * spf, int lit) {
  int blit, tag, red, other, other2, lidx, size;
  const int * p, * w, * eow, * c, * l;
  HTS * hts;
  hts = s_hts (spf, lit);
  w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (red) continue;
    if (tag == BINCS || tag == TRNCS) {
      other = blit >> RMSHFT;
      if (spf2manyoccs4elm (spf, other)) return 0;
      if (tag == TRNCS) {
	other2 = *p;
	if (spf2manyoccs4elm (spf, other2)) return 0;
      }
    } else {//(tag == IRRCS);
      lidx = blit >> RMSHFT;
      c = s_idx2lits (spf, 0, lidx);
      size = 0;
      for (l = c; (other = *l); l++) {
	if (spf2manyoccs4elm (spf, other)) return 0;
	if (++size > spf->opts.elmclslim.val) return 0;
      }
    }
  }
  return 1;
}

static int s_chkoccs4elm (SPF * spf, int idx) {
  if (spf2manyoccs4elm (spf, idx)) return 0;
  if (spf2manyoccs4elm (spf, -idx)) return 0;
  if (!s_chkoccs4elmlit (spf, idx)) return 0;
  return s_chkoccs4elmlit (spf, -idx);
}

static void s_initecls (SPF * spf, int idx) {
  int clauses;
  spf->elm.pivot = idx;
  s_pushstk (spf, &spf->elm.mark, 0);
  s_pushstk (spf, &spf->elm.mark, 0);
  s_pushstk (spf, &spf->elm.occs, 0);
  s_pushstk (spf, &spf->elm.occs, 0);
  s_pushstk (spf, &spf->elm.noccs, 0);
  s_pushstk (spf, &spf->elm.noccs, 0);
  s_pushstk (spf, &spf->elm.lsigs, 0);
  s_pushstk (spf, &spf->elm.lsigs, 0);
  s_pushstk (spf, &spf->elm.m2i, 0);
  (void) s_i2m (spf, idx);
  s_pushstk (spf, &spf->elm.lits, 0);
  s_pushstk (spf, &spf->elm.next, 0);
  s_pushstk (spf, &spf->elm.csigs, 0);
  s_pushstk (spf, &spf->elm.sizes, 0);
  spf->elm.necls = 0;
  clauses = s_ecls (spf, idx);
  spf->elm.negcls = spf->elm.necls;
  spf->elm.neglidx = s_cntstk (&spf->elm.lits);
  clauses += s_ecls (spf, -idx);
  //found %d variables in %d clauses with %d or %d",s_cntstk (&spf->seen), clauses, idx, -idx);
}

static void s_elrmcls (SPF * spf, int lit, int * c, int clidx) {
  int lidx, i, other, ulit, * lits, * csigs, blit, tag, red, other2;//, size;
  int * p, * eow, * w, count;
  HTS * hts;
  lits = spf->elm.lits.start;
  csigs = spf->elm.csigs.start;
  assert (lits < c && c < spf->elm.lits.top - 1);
  lidx = c - lits;
  //removing clause
  for (i = lidx; (other = lits[i]); i++) {
    lits[i] = REMOVED;
    csigs[i] = 0;
    ulit = s_ulit (other);
    spf->elm.noccs.start[ulit] -= 1;
  }

  hts = s_hts (spf, lit);
  w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  blit = tag = count = 0;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    if (count == clidx) break;
    count++;
  }
  if (tag == BINCS) {
    other = blit >> RMSHFT;
    s_rmbcls (spf, lit, other, 0);
  } else if (tag == TRNCS) {
    other = blit >> RMSHFT;
    other2 = *p;
    s_rmtcls (spf, lit, other, other2, 0);
  } else {
    lidx = (tag == IRRCS) ? (blit >> RMSHFT) : *p;
    s_rmlcls (spf, lidx, 0);
  }
}

static int s_backsub (SPF * spf, int * c, int str) {
  int * start = spf->elm.lits.start, * p, * q, marked = 0, res, * d;
  int lit, ulit, occ, next, osize, other, uolit, size, plit, phase, clidx;
  unsigned ocsig, lsig, csig = 0;

  //backward check for clause, backward %s check for mapped clause", mode);
  phase = (c - start) >= spf->elm.neglidx;
  for (p = c; (lit = *p); p++)
    if (abs (lit) != 1)
      csig |= s_sig (lit);
  size = p - c;
  res = 0;

  if (str) phase = !phase;
  lit = phase ? -1 : 1;

  ulit = s_ulit (lit);
  occ = s_peek (&spf->elm.noccs, ulit);
  if (!str && occ <= 1) return 0;
  if (str && !occ) return 0;
  lsig = s_peek (&spf->elm.lsigs, ulit);
  if ((csig & ~lsig)) return 0;
  for (next = s_peek (&spf->elm.occs, ulit);
       !res && next;
       next = s_peek (&spf->elm.next, next)) {
      if (next == p - start) continue;
      if (phase != (next >= spf->elm.neglidx)) continue;
      plit = s_peek (&spf->elm.lits, next);
      if (plit >= NOTALIT) continue;
      osize = s_peek (&spf->elm.sizes, next);
      if (osize > size) continue;
      ocsig = s_peek (&spf->elm.csigs, next);
      if ((ocsig & ~csig)) continue;
      if (!marked) {
	for (q = c; (other = *q); q++) {
	  if (str && abs (other) == 1) other = -other;
	  uolit = s_ulit (other);
	  s_poke (&spf->elm.mark, uolit, 1);
	}
	marked = 1;
      }
      d = spf->elm.lits.start + next;
      if (c <= d && d < c + size) continue;
      spf->stats.elm.steps++;
      while (d[-1]) d--;
      // backward %s check with clause, mode
      res = 1;
      for (q = d; res && (other = *q); q++) {
	uolit = s_ulit (other);
	res = s_peek (&spf->elm.mark, uolit);
      }
      if (!res || !str || osize < size) continue;
      //strengthening by double self-subsuming resolution");
      clidx = 0;
      q = spf->elm.lits.start + spf->elm.neglidx;
      while (q < d) {
	other = *q++;
	if (other >= NOTALIT) { while (*q++) ; continue; }
	if (!other) clidx++;
      }
      // strengthened and subsumed original irredundant clause");
      // strengthened and subsumed mapped irredundant clause");
      s_elrmcls (spf, -spf->elm.pivot, d, clidx);
  }
  if (marked) {
    for (p = c; (lit = *p); p++) {
      if (str && abs (lit) == 1) lit = -lit;
      ulit = s_ulit (lit);
      assert (s_peek (&spf->elm.mark, ulit));
      s_poke (&spf->elm.mark, ulit, 0);
    }
  }
  return res;
}

static void s_elmsub (SPF * spf) {
  int clidx, count, subsumed, pivot, * c;
  count = clidx = subsumed = 0;
  pivot = spf->elm.pivot;
  for (c = spf->elm.lits.start + 1;
       c < spf->elm.lits.top &&
         spf->limits.elm.steps > spf->stats.elm.steps;
       c++) {
    if (count++ == spf->elm.negcls) clidx = 0, pivot = -pivot;
    if (s_backsub (spf, c, 0)) {
      subsumed++;
      //subsumed original irredundant clause, subsumed mapped irredundant clause
      s_elrmcls (spf, pivot, c, clidx);
    } else clidx++;
    while (*c) c++;
  }
  //subsumed %d clauses containing %d or %d,subsumed, spf->elm.pivot, -spf->elm.pivot);
}

static int s_elmstr (SPF * spf) {
  int clidx, count, strengthened, pivot, * c, * p, mlit, ilit, res;
  int size;
  count = clidx = strengthened = 0;
  pivot = spf->elm.pivot;
  res = 0;
  // strengthening with pivot 
  for (c = spf->elm.lits.start + 1;
       c < spf->elm.lits.top &&
         spf->limits.elm.steps > spf->stats.elm.steps;
       c++) {
    if (count++ == spf->elm.negcls) {
      clidx = 0, pivot = -pivot;//strengthening with pivot %d, pivot
    }
    if (*c == REMOVED) {
      while (*c) { assert (*c == REMOVED); c++; }
      continue;
    }
    if (s_backsub (spf, c, 1)) {
      strengthened++;
      //strengthening original irredundant clause,strengthening mapped irredundant clause");
      size = 0;
      for (p = c; (mlit = *p); p++) {
	ilit = s_m2i (spf, *p);
	if (ilit == pivot) { //found = 1;
        continue; }
	s_pushstk (spf, &spf->clause, ilit);
	size++;
      }
      s_pushstk (spf, &spf->clause, 0); //static strengthened irredundant clause
      s_elrmcls (spf, pivot, c, clidx);
      s_addcls (spf, 0);
      s_clnstk (&spf->clause);
      if (size == 1) { res = 1; break; }
    } else clidx++;
    while (*c) c++;
  }
 //strengthened %d clauses containing %d or %d,strengthened, spf->elm.pivot, -spf->elm.pivot);
  return res;
}

static void s_flushlit (SPF * spf, int lit) {
  int blit, tag, red, other, other2, lidx, count;
  const int * p, * w, * eow;
  int * c, * q;
  HTS * hts;
  hts = s_hts (spf, lit);
  if (!hts->count) return;
  //flushing positive occurrences of %d", lit);
  w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  count = 0;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    red = blit & REDCS;
    other = blit >> RMSHFT;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (!red && tag == LRGCS) continue;
    if (tag == BINCS) {
      s_rmbwch (spf, other, lit, red);
      if (red==0) s_decocc (spf, other);
      //flushed %s binary clause %d %d", s_red2str (red), lit, other);
      count++;
    } else if (tag == TRNCS) {
      other2 = *p;
      s_rmtwch (spf, other2, lit, other, red);
      s_rmtwch (spf, other, lit, other2, red);
      if (red==0) s_decocc (spf, other), s_decocc (spf, other2);
      //flushed %s ternary clause %d %d %d",s_red2str (red), lit, other, other2);
      count++;
    } else {
      lidx = (tag == IRRCS) ? other : *p;
      c = s_idx2lits (spf, red, lidx);//flushed irredundant large clause");
      for (q = c; (other = *q); q++) {
	*q = REMOVED;
	if (red) continue;
	s_decocc (spf, other);
	if (other == lit) continue;
	s_rmlocc (spf, other, lidx);
      }
      *q = REMOVED;
      count++;
    }
  }
  s_shrinkhts (spf, hts, 0);//flushed %d clauses in which %d occurs", count, lit);
}

static int s_flush (SPF * spf) {
  int lit;
  if (spf->mt) return 0;
  if ((unsigned)spf->flushed == s_cntstk (&spf->trail)) return 1;
  if (!s_bcp (spf)) { spf->mt = 1; return 0; }
  if (!s_syncunits (spf)) return 0;
  while  ((unsigned)spf->flushed < s_cntstk (&spf->trail)) {
    lit = s_peek (&spf->trail, spf->flushed++);
    s_flushlit (spf, lit);
  }
  return 1;
}

static void s_epush (SPF * spf, int ilit) {
  int elit = ilit ? s_export (spf, ilit) : 0;
  s_pushstk (spf, &spf->extend, elit); //pushing external %d internal %d, elit, ilit
}

static void s_elmfrelit (SPF * spf, int mpivot,
			  int * sop, int * eop, int * son, int * eon,
			  int bintoo) {
  int ipivot = mpivot * spf->elm.pivot, clidx, ilit, tmp, cover, maxcover;
  int * c, * d, * p, * q, lit, nontrivial, idx, sgn, clen, reslen;
  int size;
  //blocked clause elimination and forced resolution of clauses with %d",ipivot);
  clidx = 0;
  s_evar (spf, ipivot);
  cover = s_peek (&spf->elm.noccs, s_ulit (-mpivot));
  for (c = sop; c < eop; c = p + 1) {
    if (*c == REMOVED) { for (p = c + 1; *p; p++) ; continue; }
    maxcover = 0;
    for (p = c; (lit = *p); p++) {
      if (lit == mpivot) continue;
      assert (lit != -mpivot);
      maxcover += s_peek (&spf->elm.noccs, s_ulit (-lit));
    }
    if (maxcover < cover - 1) { clidx++; continue; }
    for (p = c; (lit = *p); p++) {
      if (lit == mpivot) continue;
      assert (lit != -mpivot);
      idx = abs (lit);
      assert (!s_peek (&spf->elm.mark, idx));
      sgn = lit_sign (lit);
      s_poke (&spf->elm.mark, idx, sgn);
    }
    nontrivial = 0;
    clen = p - c;
    for (d = son; !nontrivial && d < eon; d = q + 1) {
      if (*d == REMOVED) { for (q = d + 1; *q; q++) ; continue; }
      spf->stats.elm.steps++;
      //c,d: trying forced resolution 1st 2nd antecedent
      reslen = clen - 1;
      for (q = d; (lit = *q); q++) {
	if (lit == -mpivot) continue;
        assert (lit != mpivot);
	idx = abs (lit), sgn = lit_sign (lit);
	tmp = s_peek (&spf->elm.mark, idx);
	if (tmp == -sgn) break;
	if (tmp != sgn) reslen++;
      }
      if (lit) {
	while (*++q) ;
        //try forced resolution ends with trivial resolvent
      } else {
	//non trivial resolvent in blocked clause elimination
	nontrivial = INT_MAX;
      }
    }
    for (p = c; (lit = *p); p++) {
      if (lit == mpivot) continue;
      idx = abs (lit);
      s_poke (&spf->elm.mark, idx, 0);
    }
    size = p - c;
    if (!nontrivial && (bintoo || size > 2)) { //blocked on %d clause, ipivot);
      s_epush (spf, 0);
      s_epush (spf, ipivot);
      for (p = c; (lit = *p); p++) {
	if (lit == mpivot) continue;
	ilit = s_m2i (spf, lit);
	s_epush (spf, ilit);
      }
      s_elrmcls (spf, ipivot, c, clidx);
      continue;
    }
    clidx++;
    if (spf->limits.elm.steps <= spf->stats.elm.steps) {//maximum number of steps in elmination exhausted
      return;
    }
  }
}

static void s_elmfre (SPF * spf, int bintoo) {
  int * sop, * eop, * son, * eon;
  sop = spf->elm.lits.start + 1;
  eop = son = spf->elm.lits.start + spf->elm.neglidx;
  eon = spf->elm.lits.top;
  s_elmfrelit (spf, 1, sop, eop, son, eon, bintoo);
  s_elmfrelit (spf, -1, son, eon, sop, eop, bintoo);
}

static int s_forcedvechk (SPF * spf, int idx) {
  EVar * v = s_evar (spf, idx);
  int pos = v->occ[0], neg = v->occ[1];
  int newpn, old;
  if (pos >= (1<<15)) return 0;
  if (neg >= (1<<15)) return 0;
  old = pos + neg;
  newpn = pos * neg;
  return newpn <= old + spf->limits.elm.excess;
}

static void s_eliminated (SPF * spf, int pivot) {
  AVar * av;
  int elit;
  Ext * e;
  av = s_avar (spf, pivot);
  av->type = ELIMVAR;
  s_flushlit (spf, pivot);
  s_flushlit (spf, -pivot);// eliminated pivot
  elit = s_export (spf, pivot);
  e = s_elit2ext (spf, elit);
  e->eliminated = 1;
}

static void s_epusheliminated (SPF * spf, int idx) {
  const int * p, * w, * eow, * c, * l;
  int pivot, blit, tag, red, lit;
  EVar * ev = s_evar (spf, idx);
  HTS * hts0;
  pivot = (ev->occ[0] <= ev->occ[1]) ? idx : -idx;
  hts0 = s_hts (spf, pivot);
  w = s_hts2wchs (spf, hts0);
  eow = w + hts0->count;// keeping clauses with pivot for extending assignment
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    s_epush (spf, 0);
    s_epush (spf, pivot);
    if (tag == BINCS || tag == TRNCS) {
      s_epush (spf, blit >> RMSHFT);
      if (tag == TRNCS)
	s_epush (spf, *p);
    } else {
      assert (tag == IRRCS);
      c = s_idx2lits (spf, 0, blit >> RMSHFT);
      for (l = c; (lit = *l); l++)
	if (lit != pivot)
	  s_epush (spf, lit);
    }
  }
  s_epush (spf, 0);
  s_epush (spf, -pivot);
  s_eliminated (spf, pivot);
}

static void s_forcedve (SPF * spf, int idx) {
  const int * p0, * p1, * w0, * w1, * eow0, * eow1, * c0, * c1, * l0, * l1;
  int pivot, dummy0[4], dummy1[4], blit0, blit1, tag0, tag1, red0, red1;
  long deltairr, deltawchs;
  HTS * hts0, * hts1;
  int * wchs, * irr;
  int lit0, lit1;
  int unit = 0;
  EVar * ev;
  Val val;
  if (spf->elm.pivot) s_rstecls (spf);// forced variable elimination of idx
  ev = s_evar (spf, idx);
  pivot = (ev->occ[0] <= ev->occ[1]) ? idx : -idx;
  hts0 = s_hts (spf, pivot);
  hts1 = s_hts (spf, -pivot);
  w0 = s_hts2wchs (spf, hts0);
  w1 = s_hts2wchs (spf, hts1);
  eow0 = w0 + hts0->count;
  eow1 = w1 + hts1->count;
  dummy0[0] = pivot;
  dummy1[0] = -pivot;
  for (p0 = w0; !unit && p0 < eow0; p0++) {
    blit0 = *p0;
    tag0 = blit0 & MASKCS;
    if (tag0 == TRNCS || tag0 == LRGCS) p0++;
    red0 = blit0 & REDCS;
    if (red0) continue;
    if (tag0 == BINCS) {
      dummy0[1] = blit0 >> RMSHFT;
      dummy0[2] = 0;
      c0 = dummy0;
    } else if (tag0 == TRNCS) {
      dummy0[1] = blit0 >> RMSHFT;
      dummy0[2] = *p0;
      dummy0[3] = 0;
      c0 = dummy0;
    } else {
      assert (tag0 == IRRCS);
      c0 = s_idx2lits (spf, 0, blit0 >> RMSHFT);
    }
    for (l0 = c0; (lit0 = *l0); l0++) {
      assert (!s_marked (spf, lit0));
      s_mark (spf, lit0);
    }
    for (p1 = w1; !unit && p1 < eow1; p1++) {
      blit1 = *p1;
      tag1 = blit1 & MASKCS;
      if (tag1 == TRNCS || tag1 == LRGCS) p1++;
      red1 = blit1 & REDCS;
      if (red1) continue;
      if (tag1 == BINCS) {
	dummy1[1] = blit1 >> RMSHFT;
	dummy1[2] = 0;
	c1 = dummy1;
      } else if (tag1 == TRNCS) {
	dummy1[1] = blit1 >> RMSHFT;
	dummy1[2] = *p1;
	dummy1[3] = 0;
	c1 = dummy1;
      } else {
	assert (tag1 == IRRCS);
	c1 = s_idx2lits (spf, 0, blit1 >> RMSHFT);
      }
      spf->stats.elm.steps++;
      for (l1 = c1; (lit1 = *l1); l1++)
	if (lit1 != -pivot && s_marked (spf, lit1) < 0) break;
      if (lit1) continue;
      //c0, c1: resolving forced variable elimination 1st 2nd antecedent
      for (l0 = c0; (lit0 = *l0); l0++) {
	if (lit0 == pivot) continue;
	val = s_val (spf, lit0);
	assert (val <= 0);
	if (val < 0) continue;
	s_pushstk (spf, &spf->clause, lit0);
      }
      for (l1 = c1; (lit1 = *l1); l1++) {
	if (lit1 == -pivot) continue;
	val = s_val (spf, lit1);
	assert (val <= 0);
	if (val < 0) continue;
	if (s_marked (spf, lit1)) continue;
	s_pushstk (spf, &spf->clause, lit1);
      }
      s_pushstk (spf, &spf->clause, 0);
      //forced variable elimination resolvent");
      if (s_cntstk (&spf->clause) >= 3) {
	wchs = spf->wchs.start;
	irr = spf->irr.start;
	s_addcls (spf, 0);
	deltawchs = spf->wchs.start - wchs;
	if (deltawchs) {
	  p0 += deltawchs, w0 += deltawchs, eow0 += deltawchs;
	  p1 += deltawchs, w1 += deltawchs, eow1 += deltawchs;
	}
	deltairr = spf->irr.start - irr;
	if (deltairr && tag0 == IRRCS) c0 += deltairr;
	s_clnstk (&spf->clause);
      } else {
	assert (s_cntstk (&spf->clause) == 2);
	s_unit (spf, spf->clause.start[0]);
	s_clnstk (&spf->clause);
	unit = 1;
      }
    }
    for (l0 = c0; (lit0 = *l0); l0++) {
      assert (s_marked (spf, lit0));
      s_unmark (spf, lit0);
    }
  }
  if (unit) return;
  s_epusheliminated (spf, pivot);
}

static int s_unhimpl (const DFPR * dfpr, int a, int b) {
  int u = s_ulit (a), v = s_ulit (b), c, d, f, g;
  c = dfpr[u].discovered; if (!c) return 0;
  d = dfpr[v].discovered; if (!d) return 0;
  f = dfpr[u].finished, g = dfpr[v].finished;
  return c < d && g < f;
}

static int s_unhimplies2 (const DFPR * dfpr, int a, int b) {
  return s_unhimpl (dfpr, a, b) || s_unhimpl (dfpr, -b, -a);
}

static int s_unhimplincl (const DFPR * dfpr, int a, int b) {
  int u = s_ulit (a), v = s_ulit (b), c, d, f, g;
  c = dfpr[u].discovered; if (!c) return 0;
  d = dfpr[v].discovered; if (!d) return 0;
  f = dfpr[u].finished, g = dfpr[v].finished;
  return c <= d && g <= f;
}

static int s_unhimplies2incl (const DFPR * dfpr, int a, int b) {
  return s_unhimplincl (dfpr, a, b) || s_unhimplincl (dfpr, -b, -a);
}

#define ENLDF(POSNEG) \
do { \
  int OLDSIZE = spf->df.POSNEG.szdfs; \
  int NEWSIZE = OLDSIZE ? 2*OLDSIZE : 1; \
  RSZ (spf->df.POSNEG.dfs, OLDSIZE, NEWSIZE, struct DF *); \
  spf->df.POSNEG.szdfs = NEWSIZE; \
} while (0)

#define PUSHDF(POSNEG,LIT) \
do { \
  unsigned ULIT = s_ulit (LIT); \
  int discovered = dfpr[ULIT].discovered; \
  DF * DF; \
  if (!discovered) break; \
  if (spf->df.POSNEG.ndfs == spf->df.POSNEG.szdfs) ENLDF (POSNEG); \
  DF = spf->df.POSNEG.dfs + spf->df.POSNEG.ndfs++; \
  DF->discovered = discovered; \
  DF->finished = dfpr[ULIT].finished; \
} while (0)

static int s_cmpdf (const DF * a, const DF * b) {
  return a->discovered - b->discovered;
}

static int s_uhte (SPF * spf, const DFPR * dfpr, Stk * s) {
  int size = s_cntstk (s), i, p, n, lit;
  if (size <= 2 || size > spf->opts.elmhtelim.val) return 0;
  spf->df.pos.ndfs = spf->df.neg.ndfs = 0;
  for (i = 0; i < size; i++) {
    lit = s->start[i];
    PUSHDF (pos, lit);
    PUSHDF (neg, -lit);
  }
  if (!spf->df.pos.ndfs || !spf->df.neg.ndfs) return 0;
  SORT3 (spf->df.pos.dfs, spf->df.pos.ndfs, s_cmpdf);
  SORT3 (spf->df.neg.dfs, spf->df.neg.ndfs, s_cmpdf);
  p = n = 0;
  for (;;) {
    if (spf->df.neg.dfs[n].discovered > spf->df.pos.dfs[p].discovered) {
      if (++p == spf->df.pos.ndfs) return 0;
    } else if (spf->df.neg.dfs[n].finished < spf->df.pos.dfs[p].finished) {
      if (++n == spf->df.neg.ndfs) return 0;
    } else return 1;
  }
}

static int s_tryforcedve (SPF * spf, int idx) {
  if (spf->limits.elm.steps <= spf->stats.elm.steps) return 1;
  if (!s_forcedvechk (spf, idx)) return 0;
  s_forcedve (spf, idx);
  return 1;
}

static int s_trylargeve (SPF * spf, DFPR * dfpr) {
  const int * c, * d, * sop, * eop, * son, * eon, * p, * q, * start, * end;
  int lit, idx, sgn, tmp, ip, mp, ilit, npocc, nnocc, limit, count, occ, i;
  int clen, dlen, reslen, maxreslen;
  EVar * ev;
  Val val;
  ip = spf->elm.pivot;
  sop = spf->elm.lits.start + 1;
  eop = son = spf->elm.lits.start + spf->elm.neglidx;
  eon = spf->elm.lits.top;
  npocc = s_peek (&spf->elm.noccs, s_ulit (1));
  nnocc = s_peek (&spf->elm.noccs, s_ulit (-1));
  limit = npocc + nnocc;
  count = 0;
  for (i = 0; i <= 1; i++) {
    start = i ? son : sop;
    end = i ? eon : eop;
    for (c = start; c < end; c++) {
      if (*c == REMOVED) { while (*c) c++; continue; }
      while ((lit = *c)) {
	ilit = s_m2i (spf, lit);
	ev = s_evar (spf, ilit);
	sgn = lit_sign (ilit);
	occ = ev->occ[sgn];
	if (occ > spf->opts.elmocclim.val) return 0; //number of occurrences of %d larger than limit, ilit
	c++;
      }
      count++;
    }
  }
  limit += spf->limits.elm.excess;
  // try clause distribution for %d with limit %d ip, limit
  maxreslen = 0;
  for (c = sop; c < eop && limit >= 0; c = p + 1) {
    if (*c == REMOVED) { for (p = c + 1; *p; p++) ; continue; }
    assert (s_mtstk (&spf->resolvent));
    clen = 0;
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      assert (lit != -1);
      idx = abs (lit);
      assert (!s_peek (&spf->elm.mark, idx));
      sgn = lit_sign (lit);
      s_poke (&spf->elm.mark, idx, sgn);
      ilit = s_m2i (spf, lit);
      s_pushstk (spf, &spf->resolvent, ilit);
      clen++;
    }
    for (d = son; limit >= 0 && d < eon; d = q + 1) {
      if (*d == REMOVED) { for (q = d + 1; *q; q++) ; continue; }
      spf->stats.elm.steps++;
      dlen = 0;
      reslen = clen;
      for (q = d; (lit = *q); q++) {
	if (lit == -1) continue;
	dlen++;
	assert (lit != 1);
	idx = abs (lit), sgn = lit_sign (lit);
	tmp = s_peek (&spf->elm.mark, idx);
	if (tmp == -sgn) break;
	if (tmp == sgn) continue;
	ilit = s_m2i (spf, lit);
	s_pushstk (spf, &spf->resolvent, ilit);
	reslen++;
      }
      assert (reslen == s_cntstk (&spf->resolvent));
      if (!lit && reslen == 1) {//trying resolution ends with unit clause");
	lit = s_peek (&spf->resolvent, 0);
	limit += s_evar (spf, lit)->occ[lit < 0];
      } else if (lit) {
	while (*++q) ;
        //try resolution ends with trivial resolvent");
      } else if (dfpr && (reslen > 2 || clen > 1 || dlen > 1) &&
                 s_uhte (spf, dfpr, &spf->resolvent)) {
        //trying resolution ends with hidden tautology");
      } else {
        limit--;
        //try resolution with non trivial resolvent remaining %d",limit);
	if (reslen > maxreslen) maxreslen = reslen;
      }
      assert (!*q);
      s_rststk (&spf->resolvent, clen);
    }
    s_clnstk (&spf->resolvent);
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      idx = abs (lit);
      s_poke (&spf->elm.mark, idx, 0);
    }
    if (spf->limits.elm.steps <= spf->stats.elm.steps) return 0;//maximum number of steps in elmination exhausted
    if (maxreslen > spf->opts.elmreslim.val) return 0; //maximum resolvent size in elimination reached
  }
  if (limit < 0) return 0; // resolving away %d would increase number of clauses;
 
  s_flushlit (spf, ip);
  s_flushlit (spf, -ip);
  if (npocc < nnocc) start = sop, end = eop, mp = 1;
  else start = son, end = eon, ip = -ip, mp = -1;
  // will save clauses with %d for extending assignment, ip
  for (c = start; c < end; c = p + 1) {
    if (*c == REMOVED) { for (p = c + 1; *p; p++) ; continue; }
    s_epush (spf, 0);
    s_epush (spf, ip);
    for (p = c; (lit = *p); p++)  {
      if (lit == mp) continue;
      ilit = s_m2i (spf, lit);
      s_epush (spf, ilit);
    }
  }
  s_epush (spf, 0);
  s_epush (spf, -ip);
  for (c = sop; c < eop; c = p + 1) {
    if (*c == REMOVED) { for (p = c + 1; *p; p++) ; continue; }
    clen = 0;
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      idx = abs (lit);
      sgn = lit_sign (lit);
      s_poke (&spf->elm.mark, idx, sgn);
      ilit = s_m2i (spf, lit);
      s_pushstk (spf, &spf->resolvent, ilit);
      clen++;
    }
    for (d = son; limit >= 0 && d < eon; d = q + 1) {
      if (*d == REMOVED) { for (q = d + 1; *q; q++) ; continue; }
      spf->stats.elm.steps++;
      dlen = 0;
      reslen = clen;
      for (q = d; (lit = *q); q++) {
	if (lit == -1) continue;
	dlen++;
	idx = abs (lit), sgn = lit_sign (lit);
	tmp = s_peek (&spf->elm.mark, idx);
	if (tmp == sgn) continue;
	if (tmp == -sgn) break;
	ilit = s_m2i (spf, lit);
	val = s_val (spf, ilit);
	if (val < 0) continue;
	if (val > 0) break;
	s_pushstk (spf, &spf->clause, ilit);
	ilit = s_m2i (spf, lit);
	s_pushstk (spf, &spf->resolvent, ilit);
	reslen++;
      }
      assert (reslen == s_cntstk (&spf->resolvent));
      if (!lit && reslen == 1) {
	goto RESOLVE;
      } if (lit) {
	while (*++q) ;
      } else if (dfpr && 
                 (reslen > 2 || clen > 1 || dlen > 1) &&
                 s_uhte (spf, dfpr, &spf->resolvent)) {
//	spf->stats.elm.htes++;
      } else {
RESOLVE:
	//c,d:  resolving variable elimination 1st 2nd antecedent
	for (p = c; (lit = *p); p++) {
	  if (lit == 1) continue;
	  ilit = s_m2i (spf, lit);
	  val = s_val (spf, ilit);
	  if (val < 0) continue;
	  if (val > 0) break;
	  s_pushstk (spf, &spf->clause, ilit);
	}
	if (!lit) {
	  s_pushstk (spf, &spf->clause, 0);// variable elimination resolvent
	  s_addcls (spf, 0);
	}
      }
      s_clnstk (&spf->clause);
      s_rststk (&spf->resolvent, clen);
    }
    s_clnstk (&spf->resolvent);
    for (p = c; (lit = *p); p++) {
      if (lit == 1) continue;
      idx = abs (lit);
      s_poke (&spf->elm.mark, idx, 0);
    }
  }
  s_eliminated (spf, spf->elm.pivot);
  return 1;
}

static void s_elimlitaux (SPF * spf, DFPR * dfpr, int idx) {
  s_elmsub (spf);
  if (s_str (spf) && s_elmstr (spf)) return;
  if (s_tryforcedve (spf, idx)) return;
  s_elmfre (spf, !dfpr);
  if (s_tryforcedve (spf, idx)) return;
  s_trylargeve (spf, dfpr);
}

static int s_s2m (SPF * spf, int ilit) {
  AVar * av = s_avar (spf, ilit);
  int res = av->mark;
  if (!res) {
    res = s_cntstk (&spf->seen) + 1;
    if (res > spf->opts.smallvevars.val + 1) return 0;
    av->mark = res;
    assert (s_cntstk (&spf->seen) == s_cntstk (&spf->elm.m2i) - 1);
    s_pushstk (spf, &spf->seen, abs (ilit));
    s_pushstk (spf, &spf->elm.m2i, abs (ilit));// mapped internal variable %d to marked variable %d", ilit res
  }
  if (ilit < 0) res = -res;
  return res;
}

static void s_var2funaux (int v, Fun res, int negate) {
  uint64_t tmp;
  int i, j, p;
  if (v < 6) {
    tmp = s_basevar2funtab[v];
    if (negate) tmp = ~tmp;
    for (i = 0; i < FUNQUADS; i++)
      res[i] = tmp;
  } else {
    tmp = negate ? ~0ull : 0ull;
    p = 1 << (v - 6);
    j = 0;
    for (i = 0; i < FUNQUADS; i++) {
      res[i] = tmp;
      if (++j < p) continue;
      tmp = ~tmp;
      j = 0;
    }
  }
}

static void s_var2fun (int v, Fun res) {  s_var2funaux (v, res, 0);}

static void s_negvar2fun (int v, Fun res) {  s_var2funaux (v, res, 1);}

static void s_funcpy (Fun dst, const Fun src) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    dst[i] = src[i];
}

static void s_falsefun (Fun res) {
  int i;
  for (i = 0; i < FUNQUADS; i++)   res[i] = 0ll;
}

static void s_truefun (Fun res) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    res[i] = (unsigned long long)(~0ll);
}

static int s_isfalsefun (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (f[i] != 0ll) return 0;
  return 1;
}

static int s_istruefun (const Fun f) {
  int i;
  for (i = 0; i < FUNQUADS; i++){
     //  if (f[i] != ~0ll) return 0;
       if (f[i] != (unsigned long long)(~0ll)) return 0;//new idea ???
  }
  return 1;
}

static void s_orfun (Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++) a[i] |= b[i];
}

static void s_ornegfun (Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++) a[i] |= ~b[i];
}

static void s_or3fun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)  a[i] = b[i] | c[i];
}

static void s_or3negfun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)  a[i] = b[i] | ~c[i];
}

static void s_andornegfun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)    a[i] &= b[i] | ~c[i];
}

static void s_andfun (Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++)    a[i] &= b[i];
}

static void s_and3fun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)    a[i] = b[i] & c[i];
}

static void s_and3negfun (Fun a, const Fun b, const Fun c) {
  int i;
  for (i = 0; i < FUNQUADS; i++)    a[i] = b[i] & ~c[i];
}

static void s_srfun (Fun a, int shift) {
  uint64_t rest, tmp;
  int i, j, q, b, l;
  b = shift & 63;
  q = shift >> 6;
  j = 0;
  i = j + q;
  l = 64 - b;
  while (j < FUNQUADS) {
    if (i < FUNQUADS) {
      tmp = a[i] >> b;
      rest = (b && i+1 < FUNQUADS) ? (a[i+1] << l) : 0ull;
      a[j] = rest | tmp;
    } else a[j] = 0ull;
    i++, j++;
  }
}

static void s_slfun (Fun a, int shift) {
  uint64_t rest, tmp;
  int i, j, q, b, l;
  b = shift & 63;
  q = shift >> 6;
  j = FUNQUADS - 1;
  i = j - q;
  l = 64 - b;
  while (j >= 0) {
    if (i >= 0) {
      tmp = a[i] << b;
      rest = (b && i > 0) ? (a[i-1] >> l) : 0ll;
      a[j] = rest | tmp;
    } else a[j] = 0ll;
    i--, j--;
  }
}

static void s_s2fun (int mlit, Fun res) {
  int midx = abs (mlit), sidx = midx - 2;
  if (mlit < 0) s_negvar2fun (sidx, res);
  else s_var2fun (sidx, res);
}

static int s_initsmallve (SPF * spf, int lit, Fun res) {
  int blit, tag, red, other, other2, lidx, mlit;
  const int * p, * w, * eow, * c, * q;
  Fun cls, tmp;
  HTS * hts;
  Val val;
  //initializing small variable eliminiation for %d", lit);
  mlit = s_s2m (spf, lit);
  hts = s_hts (spf, lit);
  s_truefun (res);
  if (!hts->count) goto DONE;
  w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    s_falsefun (cls);
    if (tag == BINCS || tag == TRNCS) {
      other = blit >> RMSHFT;
      val = s_val (spf, other);
      assert (val <= 0);
      if (!val) {
	mlit = s_s2m (spf, other);
	if (!mlit) return 0;
	s_s2fun (mlit, tmp);
	s_orfun (cls, tmp);
      }
      if (tag == TRNCS) {
        other2 = *p;
	val = s_val (spf, other2);
	assert (val <= 0);
	if (!val) {
	  mlit = s_s2m (spf, other2);
	  if (!mlit) return 0;
	  s_s2fun (mlit, tmp);
	  s_orfun (cls, tmp);
	}
      }
    } else {      //tag == IRRCS);
      lidx = blit >> RMSHFT;
      c = s_idx2lits (spf, 0, lidx);
      for (q = c; (other = *q); q++) {
	if (other == lit) continue;
	val = s_val (spf, other);
	if (!val) {
	  mlit = s_s2m (spf, other);
	  if (!mlit) return 0;
	  s_s2fun (mlit, tmp);
	  s_orfun (cls, tmp);
	}
      }
    }
    s_andfun (res, cls);
    spf->stats.elm.steps++;
  }
DONE:
  return 1;
}

static void s_resetsmallve (SPF * spf) {
  s_clnstk (&spf->elm.m2i);
  s_clnstk (&spf->clv);
  s_popnunmarkstk (spf, &spf->seen);
}

static void s_smallevalcls (unsigned cls, Fun res) {
  Fun tmp;
  int v;
  s_falsefun (res);
  for (v = 0; v < FUNVAR; v++) {
    if (cls & (1 << (2*v + 1))) {
      s_var2fun (v, tmp);
      s_ornegfun (res, tmp);
    } else if (cls & (1 << (2*v))) {
      s_var2fun (v, tmp);
      s_orfun (res, tmp);
    }
  }
}

static Cnf s_pos2cnf (int pos) { assert (pos >=0 ); return pos; }
static Cnf s_size2cnf (int s) { assert (s >=0 ); return ((Cnf)s) << 32; }
static int s_cnf2pos (Cnf cnf) { return cnf & 0xfffffll; }
static int s_cnf2size (Cnf cnf) { return cnf >> 32; }

static Cnf s_cnf (int pos, int size) {
  return s_pos2cnf (pos) | s_size2cnf (size);
}

static void s_smallevalcnf (SPF * spf, Cnf cnf, Fun res) {
  Fun tmp;
  int i, n, p, cls;
  p = s_cnf2pos (cnf);
  n = s_cnf2size (cnf);
  s_truefun (res);
  for (i = 0; i < n; i++) {
    cls = s_peek (&spf->clv, p + i);
    s_smallevalcls (cls, tmp);
    s_andfun (res, tmp);
  }
}

static void s_negcofactorfun (const Fun f, int v, Fun res) {
  Fun mask, masked;
  s_var2fun (v, mask);
  s_and3negfun (masked, f, mask);
  s_funcpy (res, masked);
  s_slfun (masked, (1 << v));
  s_orfun (res, masked);
}

static void s_poscofactorfun (const Fun f, int v, Fun res) {
  Fun mask, masked;
  s_var2fun (v, mask);
  s_and3fun (masked, f, mask);
  s_funcpy (res, masked);
  s_srfun (masked, (1 << v));
  s_orfun (res, masked);
}

static int s_eqfun (const Fun a, const Fun b) {
  int i;
  for (i = 0; i < FUNQUADS; i++)
    if (a[i] != b[i]) return 0;
  return 1;
}

static int s_smalltopvar (const Fun f, int min) {
  Fun p, n;
  int v;
  for (v = min; v < FUNVAR; v++) {
    s_poscofactorfun (f, v, p);
    s_negcofactorfun (f, v, n);
    if (!s_eqfun (p, n)) return v;
  }
  return v;
}

static Cnf s_smalladdlit2cnf (SPF * spf, Cnf cnf, int lit) {
  int p, m, q, n, i, cls;
  Cnf res;
  p = s_cnf2pos (cnf);
  m = s_cnf2size (cnf);
  q = s_cntstk (&spf->clv);
  for (i = 0; i < m; i++) {
    cls = s_peek (&spf->clv, p + i);
    assert (!(cls & lit));
    cls |= lit;
    s_pushstk (spf, &spf->clv, cls);
  }
  n = s_cntstk (&spf->clv) - q;
  res = s_cnf (q, n);
  return res;
}

static Cnf s_smallipos (SPF * spf, const Fun U, const Fun L, int min) {
  Fun U0, U1, L0, L1, Unew, ftmp;
  Cnf c0, c1, cstar, ctmp, res;
  int x, y, z;
  if (s_istruefun (U)) return TRUECNF;
  if (s_isfalsefun (L)) return FALSECNF;
  y = s_smalltopvar (U, min);
  z = s_smalltopvar (L, min);
  x = (y < z) ? y : z;
  s_negcofactorfun (U, x, U0); s_poscofactorfun (U, x, U1);
  s_negcofactorfun (L, x, L0); s_poscofactorfun (L, x, L1);
  s_or3negfun (ftmp, U0, L1);
  c0 = s_smallipos (spf, ftmp, L0, min+1);
  s_or3negfun (ftmp, U1, L0);
  c1 = s_smallipos (spf, ftmp, L1, min+1);
  s_smallevalcnf (spf, c0, ftmp);
  s_or3negfun (Unew, U0, ftmp);
  s_smallevalcnf (spf, c1, ftmp);
  s_andornegfun (Unew, U1, ftmp);
  s_or3fun (ftmp, L0, L1);
  cstar = s_smallipos (spf, Unew, ftmp, min+1);
  assert (cstar != FALSECNF);
  ctmp = s_smalladdlit2cnf (spf, c1, (1 << (2*x + 1)));
  res = s_cnf2pos (ctmp);
  ctmp = s_smalladdlit2cnf (spf, c0, (1 << (2*x)));
  if (res == TRUECNF) res = s_cnf2pos (ctmp);
  ctmp = s_smalladdlit2cnf (spf, cstar, 0);
  if (res == TRUECNF) res = s_cnf2pos (ctmp);
  res |= s_size2cnf (s_cntstk (&spf->clv) - res);
  return res;
}

static void s_smallve (SPF * spf, Cnf cnf) {
  int * soc = spf->clv.start + s_cnf2pos (cnf);
  int * eoc = soc + s_cnf2size (cnf);
  int * p, cls, v, lit, trivial;
  Val val;
  for (p = soc; !spf->mt && p < eoc; p++) {
    cls = *p;
    trivial = 0;
    for (v = 0; v < FUNVAR; v++) {
      if (cls & (1 << (2*v + 1))) lit = -s_m2i (spf, v+2);
      else if (cls & (1 << (2*v))) lit = s_m2i (spf, v+2);
      else continue;
      val = s_val (spf, lit);
      if (val < 0) continue;
      if (val > 0) trivial = 1;
      s_pushstk (spf, &spf->clause, lit);
    }
    if (!trivial) {
      spf->stats.elm.steps++;
      s_pushstk (spf, &spf->clause, 0);//small elimination resolvent
      s_addcls (spf, 0);
    }
    s_clnstk (&spf->clause);
  }
}

static int s_smallisunitcls (SPF * spf, int cls) {
  int fidx, fsign, flit, mlit, ilit;
  ilit = 0;
  for (fidx = 0; fidx < FUNVAR; fidx++)
    for (fsign = 0; fsign <= 1; fsign++) {
      flit = 1<<(2*fidx + fsign);
      if (!(cls & flit)) continue;
      if (ilit) return 0;
      mlit = (fidx + 2) * (fsign ? -1 : 1);
      ilit = s_m2i (spf, mlit);
    }
  return ilit;
}

static int s_smallcnfunits (SPF * spf, Cnf cnf) {
  int p, m, i, res, cls, ilit;
  p = s_cnf2pos (cnf);
  m = s_cnf2size (cnf);
  res = 0;
  for (i = 0; i < m; i++) {
    cls = s_peek (&spf->clv, p + i);
    ilit = s_smallisunitcls (spf, cls);
    if (!ilit) continue;
    s_unit (spf, ilit);
    res++;
  }
  return res;
}

static int s_trysmallve (SPF * spf, int idx) {
  int res = 0, newsz, old, units;
  Fun pos, neg, fun;
  EVar * ev;
  Cnf cnf;
  s_pushstk (spf, &spf->elm.m2i, 0);
  s_pushstk (spf, &spf->clv, 0);
  if (s_initsmallve (spf, idx, pos) && s_initsmallve (spf, -idx, neg)) {
    s_or3fun (fun, pos, neg);
    cnf = s_smallipos (spf, fun, fun, 0);
    newsz = s_cnf2size (cnf);
    units = s_smallcnfunits (spf, cnf);
    newsz -= units;
    ev = s_evar (spf, idx);
    old = ev->occ[0] + ev->occ[1];
    //small elimination of %d replaces "%d old with %d new clauses and %d units",idx, old, newsz, units);
    if (newsz <= old + spf->limits.elm.excess) {//small elimination of %d removes %d clauses, idx, old - newsz
      s_smallve (spf, cnf);
      s_epusheliminated (spf, idx);
      res = 1;
    } else {      //small elimination of %d would add %d clauses", idx, newsz - old);
      if (units > 0) res = 1;
    }
  } //too many variables for small elimination
  s_resetsmallve (spf);
  return res;
}

static void s_elimlit (SPF * spf, DFPR * dfpr, int idx) {
  if (!s_isfree (spf, idx)) return;
  if (!s_chkoccs4elm (spf, idx)) return;
  // trying to eliminate idx
  if (!dfpr &&
      s_str (spf) &&
      spf->opts.smallve.val &&
      s_trysmallve (spf, idx)) return;
  if (s_tryforcedve (spf, idx)) return;
  s_initecls (spf, idx);
  s_elimlitaux (spf, dfpr, idx);
  if (spf->elm.pivot) s_rstecls (spf);
}

static int s_blockcls (SPF * spf, int lit) {
  int blit, tag, red, other, other2, lidx, val, count, size;
  const int * p, * w, * eow, * c, *l;
  HTS * hts;
  hts = s_hts (spf, lit);
  hts = s_hts (spf, lit);
  if (!hts->count) return 1;
  w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  count = 0;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    count++;
    spf->stats.blk.res++;
    if (tag == BINCS || tag == TRNCS) {
      other = blit >> RMSHFT;
      val = s_marked (spf, other);
      if (val < 0) continue;
      if (tag == TRNCS) {
	other2 = *p;
	val = s_marked (spf, other2);
	if (val < 0) continue;
      }
    } else {  //tag == IRRCS);
      lidx = blit >> RMSHFT;
      c = s_idx2lits (spf, 0, lidx);
      size = 0;
      for (l = c; (other = *l); l++) {
	val = s_marked (spf, other);
	if (++size > spf->opts.blkclslim.val) return 0;
	if (val < 0) break;
      }
      if (other) continue;
    }
    return 0;
  }
  //resolved %d trivial resolvents on %d", count, lit);
  return 1;
}

static void s_pushnmarkseen (SPF * spf, int lit) {
  s_pushstk (spf, &spf->seen, lit);
  s_mark (spf, lit);
}

static int spf2manyoccs4blk (SPF * spf, int lit) {
  return s_hts (spf, lit)->count > spf->opts.blkocclim.val;
}

static void s_blocking (SPF * spf, int ilit) {
  int elit = s_export (spf, ilit), sgnbit = (1 << (elit < 0));
  Ext * ext = s_elit2ext (spf, elit);
  if (ext->blocking & sgnbit) return;
  ext->blocking |= sgnbit;
  //marking external %d internal %d as blocking", elit, ilit
}

static int s_blocklit (SPF * spf, int lit, Stk * stk) {
  int blit, tag, red, blocked, other, other2, lidx, count, size;
  int * p, * w, * eow, * c, * l;
  HTS * hts;
  if (s_val (spf, lit)) return 0;
  hts = s_hts (spf, lit);
  if (!hts->count) return 0;
  if (spf2manyoccs4blk (spf, lit)) return 0;
  w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  count = 0;
  for (p = w; p < eow; p++) {
    blit = *p;
    tag = blit & MASKCS;
    blocked = 0;
    if (tag == TRNCS || tag == LRGCS) p++;
    red = blit & REDCS;
    if (red) continue;
    assert (s_mtstk (&spf->seen));
    if (tag == BINCS || tag == TRNCS) {
      other = blit >> RMSHFT;
      if (spf2manyoccs4blk (spf, other)) continue;
      s_pushnmarkseen (spf, other);
      if (tag == TRNCS) {
	other2 = *p;
        if (spf2manyoccs4blk (spf, other2)) goto CONTINUE;
	s_pushnmarkseen (spf, other2);
      }
    } else {
      //(tag == IRRCS);
      lidx = blit >> RMSHFT;
      c = s_idx2lits (spf, 0, lidx);
      size = 0;
      for (l = c; (other = *l); l++) {
	if (other == lit) continue;
        if (spf2manyoccs4blk (spf, other)) goto CONTINUE;
	if (++size > spf->opts.blkclslim.val) goto CONTINUE;
	s_pushnmarkseen (spf, other);
      }
    }
    blocked = s_blockcls (spf, -lit);
CONTINUE:
    s_popnunmarkstk (spf, &spf->seen);
    if (!blocked) continue;
    if (tag == BINCS) {
      other = blit >> RMSHFT;
      s_pushstk (spf, stk+2, other);
    } else if (tag == TRNCS) {
      other = blit >> RMSHFT;
      s_pushstk (spf, stk+3, other);
      other2 = *p;
      s_pushstk (spf, stk+3, other2);
    } else {
      assert (tag == IRRCS);
      lidx = blit >> RMSHFT;
      s_pushstk (spf, stk+4, lidx);
    }
  }
  while (!s_mtstk (stk+2)) {
    count++;
    other = s_popstk (stk+2);
    //blocked binary clause %d %d on %d", lit, other, lit);
    s_rmbcls (spf, lit, other, 0);
    s_epush (spf, 0);
    s_epush (spf, lit);
    s_epush (spf, other);
  }
  while (!s_mtstk (stk+3)) {
    count++;
    other2 = s_popstk (stk+3);
    other = s_popstk (stk+3);
    //blocked ternary clause %d %d %d on %d", lit, other, other2, lit);
    s_rmtcls (spf, lit, other, other2, 0);
    s_epush (spf, 0);
    s_epush (spf, lit);
    s_epush (spf, other);
    s_epush (spf, other2);
  }
  while (!s_mtstk (stk+4)) {
    lidx = s_popstk (stk+4);
    count++;
    c = s_idx2lits (spf, 0, lidx);//blocked on %d large clause, lit
    s_epush (spf, 0);
    s_epush (spf, lit);
    for (l = c; (other = *l); l++)
      if (other != lit) s_epush (spf, other);
    s_rmlcls (spf, lidx, 0);
  }//found %d blocked clauses with %d, count, lit
  s_blocking (spf, lit);
  return count;
}

static void s_signedmark (SPF * spf, int lit) {
  AVar * av = s_avar (spf, lit);
  int bit = 1 << ((lit < 0) ? 1 : 2);
  if (av->mark & bit) return;
  av->mark |= bit;
}

static void s_signedmarknpushseen (SPF * spf, int lit) {
  s_signedmark (spf, lit);
  s_pushstk (spf, &spf->seen, lit);
}

static int s_signedmarked (SPF * spf, int lit) {
  AVar * av = s_avar (spf, lit);
  int bit = 1 << ((lit < 0) ? 1 : 2);
  return av->mark & bit;
}

static int s_hla (SPF * spf, int start) {
  int next, blit, tag, other, red, lit, tmp;
  const int * p, * w, * eow;
  HTS * hts;
  s_signedmarknpushseen (spf, start);
  next = 0;
  //starting hidden literal addition from %d", start);
  while ((unsigned)next < s_cntstk (&spf->seen)) {
    lit = s_peek (&spf->seen, next++);
    hts = s_hts (spf, lit);
    if (!hts->count) continue;
    w = s_hts2wchs (spf, hts);
    eow = w + hts->count;
    for (p = w; p < eow; p++) {
      spf->stats.hte.hla.steps++;
      spf->stats.hte.all.steps++;
      blit = *p;
      tag = blit & MASKCS;
      if (tag == TRNCS || tag == LRGCS) p++;
      if (tag != BINCS) continue;
      red = blit & REDCS;
      if (red) continue;
      other = -(blit >> RMSHFT);
      if (s_signedmarked (spf, other)) continue;
      if (s_signedmarked (spf, -other)) {
	// failed literal %d in hidden tautology elimination, -start
	s_unit (spf, start);
	tmp = s_flush (spf);
	if (!tmp && !spf->mt) spf->mt = 1;
	return 0;
      }
      // added hidden literal %d, other
      s_signedmarknpushseen (spf, other);
      if (s_cntstk (&spf->seen) > (unsigned)spf->limits.hla) return 1;
    }
  }
  return 1;
}

static void s_addhtebincls (SPF * spf, int a, int b, int red) {
  if (a == -b) return;
  if (s_val (spf, a) > 0) return;
  if (s_val (spf, b) > 0) return;
  if (!s_val (spf, a)) s_pushstk (spf, &spf->clause, a);
  if (!s_val (spf, b)) s_pushstk (spf, &spf->clause, b);
  s_pushstk (spf, &spf->clause, 0);  // hte binary clause
  s_addcls (spf, red);
  s_clnstk (&spf->clause);
}

static void s_hte (SPF * spf) {
  int idx, sign, lit, blit, tag, red, other, other2, lidx, witness;
  int first, pos, delta, nlits, changed, success;
  struct { Stk trn, lrg; int count; } taut, rem;
  int64_t limit, oldprgss = spf->stats.prgss;
  const int * p, * w, * eow, * c, * l;
  HTS * hts;
  assert (spf->dense);
  nlits = 2*(spf->nvars - 2);
  if (nlits <= 0) return;
  
  CLR (taut.trn); CLR (taut.lrg);
  CLR (rem.trn); CLR (rem.lrg);
  taut.count = rem.count = 0;
  first = 0;
  pos = s_rand (spf) % nlits;
  delta = s_rand (spf) % nlits;
  if (!delta) delta++;
  while (s_gcd (delta, nlits) > 1)
    if (++delta == nlits) delta = 1;
  // hte start %u delta %u mod %u", pos, delta, nlits
  limit = spf->opts.htemaxeff.val/10;
  if (limit < spf->opts.htemineff.val) limit = spf->opts.htemineff.val;
  if (limit > spf->opts.htemaxeff.val) limit = spf->opts.htemaxeff.val;
  // hte penalty %d", spf->limits.hte.pen
  if (spf->limits.hte.pen < 0) limit <<= -spf->limits.hte.pen;
  if (spf->limits.hte.pen > 0) limit >>= spf->limits.hte.pen;
  // hte search steps limit %lld", limit
  limit += spf->stats.hte.all.steps;
  changed = 0;
  while (!spf->mt) {
    if (spf->stats.hte.all.steps >= limit) break;
    if (s_terminate (spf)) break;
    if (!s_syncunits (spf)) break;
    sign = (pos & 1) ? -1 : 1;
    idx = pos/2 + 2;
    assert (2 <= idx && idx < spf->nvars);
    lit = sign * idx;
    if (s_val (spf, lit)) goto CONTINUE;
    if (!s_hla (spf, lit)) { changed = 1; goto CONTINUE; }
    hts = s_hts (spf, lit);
    w = s_hts2wchs (spf, hts);
    eow = w + hts->count;
    for (p = w; p < eow && spf->stats.hte.all.steps < limit; p++) {
      spf->stats.hte.all.steps++;
      blit = *p;
      tag = blit & MASKCS;				
      //(tag != LRGCS);
      if (tag == TRNCS) p++;
      if (tag == BINCS) continue;
      red = blit & REDCS;
      if (red && !spf->opts.htered.val) continue;
      assert (!red || tag == TRNCS);			
      if (tag == TRNCS) {
	other = blit >> RMSHFT;
	other2 = *p;
	if (s_signedmarked (spf, -other)) {
	  s_pushstk (spf, &taut.trn, red);
	  s_pushstk (spf, &taut.trn, other);
	  s_pushstk (spf, &taut.trn, other2);
	  s_pushstk (spf, &taut.trn, other);
	} else if (s_signedmarked (spf, -other2)) {
	  s_pushstk (spf, &taut.trn, red);
	  s_pushstk (spf, &taut.trn, other);
	  s_pushstk (spf, &taut.trn, other2);
	  s_pushstk (spf, &taut.trn, other2);
	} else if (s_str (spf) && s_signedmarked (spf, other)) {
	  s_pushstk (spf, &rem.trn, red);
	  s_pushstk (spf, &rem.trn, other);
	  s_pushstk (spf, &rem.trn, other2);
	  s_pushstk (spf, &rem.trn, other);
	} else if (s_str (spf) && s_signedmarked (spf, other2)) {
	  s_pushstk (spf, &rem.trn, red);
	  s_pushstk (spf, &rem.trn, other);
	  s_pushstk (spf, &rem.trn, other2);
	  s_pushstk (spf, &rem.trn, other2);
	}
      } else {	//tag == IRRCS);
	lidx = blit >> RMSHFT;
	c = s_idx2lits (spf, 0, lidx);
	for (l = c; (other = *l); l++) {
	  if (other == lit) continue;
	  if (s_signedmarked (spf, -other)) {
	    s_pushstk (spf, &taut.lrg, lidx);
	    s_pushstk (spf, &taut.lrg, other);
	    break;
	  }
	  if (s_str (spf) && s_signedmarked (spf, other)) {
	    s_pushstk (spf, &rem.lrg, lidx);
	    s_pushstk (spf, &rem.lrg, other);
	     break;
	  }
	}
      }
    }
    while (!s_mtstk (&taut.lrg)) {
      witness = s_popstk (&taut.lrg);
      lidx = s_popstk (&taut.lrg);
      //s_idx2lits (spf, 0, lidx), "hidden tautology on %d and %d irredundant large clause", lit, witness
      s_rmlcls (spf, lidx, 0);
      spf->stats.prgss++;
      taut.count++;
    }
    while (!s_mtstk (&taut.trn)) {
      witness = s_popstk (&taut.trn);
      other2 = s_popstk (&taut.trn);
      other = s_popstk (&taut.trn);
      red = s_popstk (&taut.trn);
      // hidden tautology on %d and %d %s ternary clause %d %d %d", lit, witness, s_red2str (red), lit, other, other2);
      s_rmtcls (spf, lit, other, other2, red);
      spf->stats.prgss++;
      taut.count++;
    }
    while (!s_mtstk (&rem.lrg)) {
      witness = s_popstk (&rem.lrg);
      lidx = s_popstk (&rem.lrg);
      //s_idx2lits (spf, 0, lidx),hidden literal removal of %d on %d in irredundant large clause",witness, lit);
      spf->stats.prgss++;
      rem.count++;
      c = s_idx2lits (spf, 0, lidx);
      for (l = c; (other = *l); l++)
	if (other == witness) ; 
	else if (s_val (spf, other) > 0) break;
	else if (!s_val (spf, other)) s_pushstk (spf, &spf->clause, other);
      if (!other) {
           s_pushstk (spf, &spf->clause, 0);
	   s_rmlcls (spf, lidx, 0);
	   s_addcls (spf, 0);
      }
      s_clnstk (&spf->clause);
    }
    while (!s_mtstk (&rem.trn)) {
      witness = s_popstk (&rem.trn);
      other2 = s_popstk (&rem.trn);
      other = s_popstk (&rem.trn);
      red = s_popstk (&rem.trn);
      //  hidden literal removal of %d on %d in %s ternary clause %d %d %d 
      spf->stats.prgss++;
      rem.count++;
      s_rmtcls (spf, lit, other, other2, red);
      s_addhtebincls (spf, lit, (other==witness) ? other2 : other, red);
      changed = 1;
    }
CONTINUE:
    s_popnunmarkstk (spf, &spf->seen);
    if (first == lit) {
      if (!changed) break;
      changed = 0;
    }
    if (!first) first = lit;
    pos += delta;
    if (pos >= nlits) pos -= nlits;
  }
  s_relstk (spf, &taut.trn);
  s_relstk (spf, &taut.lrg);
  s_relstk (spf, &rem.trn);
  s_relstk (spf, &rem.lrg);
  spf->limits.hla += spf->opts.hlaliminc.val;
  if (spf->limits.hla > spf->opts.hlamaxlim.val)
    spf->limits.hla = spf->opts.hlamaxlim.val;
  success = oldprgss < spf->stats.prgss;
  if (success && spf->limits.hte.pen > MINPEN) spf->limits.hte.pen--;
  if (!success && spf->limits.hte.pen < MAXPEN) spf->limits.hte.pen++;
}

static void s_block (SPF * spf) {
  Stk blocked[5];
  int idx, count;
  int64_t limit;
 
  spf->blocking = 1;
  count = 0;
  memset (blocked, 0, sizeof blocked);
  limit = spf->opts.blkmaxeff.val/10;
  if (limit < spf->opts.blkmineff.val) limit = spf->opts.blkmineff.val;
  if (limit > spf->opts.blkmaxeff.val) limit = spf->opts.blkmaxeff.val;
  //blocking resolution steps limit %lld, limit
  limit += spf->stats.blk.res;
  while (!s_terminate (spf) &&  spf->stats.blk.res < limit && !s_mtstk (&spf->esched)) {
    idx = s_popesched (spf);
    spf->elm.pivot = idx;
    count += s_blocklit (spf, idx, blocked);
    count += s_blocklit (spf, -idx, blocked);
  }
  s_relstk (spf, blocked+2);
  s_relstk (spf, blocked+3);
  s_relstk (spf, blocked+4);
  spf->elm.pivot = 0;  //blocked clause elimination
  spf->blocking = 0;
  s_eschedall (spf);
}

static DFPR * s_stampall (SPF *, int);

int s_eliminate (SPF * spf) {
  int res = 1, idx, oldnvars, skip;
  int flushed, success; 
  int64_t limit, oldprgss;
  DFPR * dfpr;
  oldnvars = spf->nvars;
  skip = (!oldnvars || !s_small (spf));
  if (skip) goto DONE;
  if (spf->mt || spf->nvars <= 2) goto DONE;
  spf->stats.elm.count++;
   
  spf->eliminating = 1;  spf->simp = 1;
  s_clearMap (spf);
  if (spf->level > 0) s_backtrack (spf, 0);
  
  s_dense (spf);
  if (spf->opts.hte.val) { s_hte (spf); res = !spf->mt; }
  if (res && spf->opts.block.val) s_block (spf);
                             // current elimination excess
  limit = spf->opts.elmaxeff.val/10;
  if (limit < spf->opts.elmineff.val) limit = spf->opts.elmineff.val;
  if (limit > spf->opts.elmaxeff.val) limit = spf->opts.elmaxeff.val;
                     // elimination penalty
  if (spf->limits.elm.pen < 0) limit <<= -spf->limits.elm.pen;
  if (spf->limits.elm.pen > 0) limit >>= spf->limits.elm.pen;
                      // elimination up to subsumption checks / resolutions
  spf->limits.elm.steps = spf->stats.elm.steps + limit;

  oldprgss = spf->stats.prgss;
  if (res &&   (res = s_flush (spf)) &&  spf->opts.elmhte.val && !s_str (spf)) {
    dfpr = s_stampall (spf, 1);
    res = s_flush (spf);
  } else dfpr = 0;
  flushed = 0;
  while (res &&	 !s_terminate (spf) && !(flushed = s_mtstk (&spf->esched)) &&
	 spf->limits.elm.steps > spf->stats.elm.steps) {
    idx = s_popesched (spf);
    s_elimlit (spf, dfpr, idx);
    res = s_flush (spf);
  }
  if (dfpr) DEL (dfpr, 2*spf->nvars);
  s_relecls (spf);
  s_sparse (spf);
  if (res) { s_clearMap (spf); if (spf->mt) res = 0; } else assert (spf->mt);

  success = oldprgss < spf->stats.prgss;
  if (success && spf->limits.elm.pen > MINPEN) spf->limits.elm.pen--;
  if (!success && spf->limits.elm.pen < MAXPEN) spf->limits.elm.pen++;
  spf->eliminating = 0;  spf->simp = 0;
DONE:
  return res;
}

static int s_elitblockingoreliminated (SPF * spf, int elit) {
  Ext * ext = s_elit2ext (spf, elit);
  return ext->blocking || ext->eliminated;
}

static int s_synceqs (SPF * spf) {
  int * ereprs, emax = spf->maxext;
  int elit1, erepr1, elit2, erepr2;
  int ilit1, irepr1, ilit2, irepr2;
  int consumed = 0, produced = 0;
  if (!spf->nvars) return 1;
  if (!spf->eqs.lock.fun) return 1;
  ereprs = spf->eqs.lock.fun (spf->eqs.lock.state);
  produced = consumed = 0;
  for (elit1 = 1; elit1 <= emax; elit1++) {
    if (s_elitblockingoreliminated (spf, elit1)) continue;
    elit2 = s_ptrjmp (ereprs, emax, elit1);
    if (elit2 == elit1) continue;
    if (s_elitblockingoreliminated (spf, elit2)) continue;
    erepr1 = s_erepr (spf, elit1);
    if (s_elitblockingoreliminated (spf, erepr1)) continue;
    erepr2 = s_erepr (spf, elit2);
    if (s_elitblockingoreliminated (spf, erepr2)) continue;
    if (erepr1 == erepr2) continue;
    if (erepr1 == -erepr2) {
INCONSISTENT:
      //inconsistent external equivalence %d %d", elit1, elit2);
      spf->mt = 1;
      goto DONE;
    }
    ilit1 = s_import (spf, elit1);
    ilit2 = s_import (spf, elit2);
    if (ilit1 == ilit2) continue;
    if (ilit1 == -ilit2) goto INCONSISTENT;
    if (abs (ilit1) <= 1) continue;
    if (abs (ilit2) <= 1) continue;
    irepr1 = s_irepr (spf, ilit1);
    irepr2 = s_irepr (spf, ilit2);
    if (irepr1 == irepr2) continue;
    if (irepr1 == -irepr2) goto INCONSISTENT;
    if (abs (irepr1) <= 1) continue;
    if (abs (irepr2) <= 1) continue;
    //importing external equivalence %d %d as internal %d %d",elit1, elit2, irepr1, irepr2);
    if (!s_isfree (spf, irepr1)) continue;
    if (!s_isfree (spf, irepr2)) continue;
    consumed++;
    s_imerge (spf, irepr1, irepr2);
  }// consumed %d equivalences", consumed);
  for (elit1 = 1; elit1 <= emax; elit1++) {
    elit2 = s_erepr (spf, elit1);
    if (elit1 == elit2) continue;
    erepr1 = s_ptrjmp (ereprs, emax, elit1);
    erepr2 = s_ptrjmp (ereprs, emax, elit2);
    if (erepr1 == erepr2) continue;
    //exporting external equivalence %d %d", erepr1, erepr2);
    produced++;
    ereprs[abs (erepr1)] = (erepr1 < 0) ? -erepr2 : erepr2;
  }// produced %d equivalences, produced
DONE:
  if (spf->eqs.unlock.fun) 
    spf->eqs.unlock.fun (spf->eqs.unlock.state, consumed, produced);
  return !spf->mt;
}

static int s_decomp (SPF * spf) {
  int res = 1;
  if (!s_small (spf)) goto NEXT;
  spf->decomposing = 1;
  spf->simp = 1;
  if (spf->level > 0) s_backtrack (spf, 0);
  res = 0;
  if (!s_bcp (spf)) goto DONE;
  s_clearMap (spf);
  if (spf->mt) goto DONE;
  if (!s_tarjan (spf)) goto DONE;
  if (!s_synceqs (spf)) goto DONE;

  s_dcpdis (spf);
  s_dcpcln (spf);
  s_dcpcon (spf);
  s_fitlirs (spf);
  s_dreschedule (spf);
  s_map (spf);
  if (spf->mt) goto DONE;
  if (!s_bcp (spf)) goto DONE;
  s_clearMap (spf);
  if (spf->mt) goto DONE;
  s_dreschedule (spf);
  res = 1;
DONE:
  spf->decomposing = 0;  spf->simp = 0;
NEXT:
  return res;
}

static int s_randomprobe (SPF * spf, Stk * outer) {
  unsigned pos, mod;
  int res;
  mod = s_cntstk (outer);
  if (!mod) return 0;
  pos = s_rand (spf) % mod;
  res = s_peek (outer, pos);
  if (s_val (spf, res)) return 0;
  assert (res == abs (res));
  return res;
}

static int s_innerprobe (SPF * spf, int old,  Stk * outer, Stk * tmp) {
  int i, lit, blit, tag, other, other2, res;
  const int * w, * eow, * p;
  HTS * hts;
  assert (old < s_cntstk (&spf->trail));
  assert (s_mtstk (tmp));
  for (i = old; (unsigned)i < s_cntstk (&spf->trail); i++) {
    lit = s_peek (&spf->trail, i);
    hts = s_hts (spf, -lit);
    w = s_hts2wchs (spf, hts);
    eow = w + hts->count;
    for (p = w; p < eow; p++) {
      blit = *p;
      tag = blit & MASKCS;
      if (tag == TRNCS || tag == LRGCS) p++;
      if (tag == BINCS || tag == LRGCS) continue;
      assert (tag == TRNCS);
      other = blit >> RMSHFT;
      if (s_val (spf, other) > 0) continue;
      other2 = *p;
      if (s_val (spf, other2) > 0) continue;
      assert (!s_val (spf, other));
      assert (!s_val (spf, other2));
      other = abs (other);
      if (!s_marked (spf, other)) {
	s_mark (spf, other);
	s_pushstk (spf, tmp, other);
	//potential inner probe %d for %d", other, lit);
      }
      other2 = abs (other2);
      if (!s_marked (spf, other2)) {
	s_mark (spf, other2);
	s_pushstk (spf, tmp, other2);
	//potential inner probe %d for %d", other2, lit);
      }
    }
  }//found %d inner probes in ternary clauses", s_cntstk (tmp));
  res = s_randomprobe (spf, tmp);
  s_popnunmarkstk (spf, tmp);
  if (!res) res = s_randomprobe (spf, outer);
  return res;
}

static void s_cleanrepr (SPF * spf, Stk * represented, int * repr) {
  int idx;
  while (!s_mtstk (represented)) {
    idx = s_popstk (represented);
    repr[idx] = 0;
  }
}

static void s_addliftbincls (SPF * spf, int a, int b) {
  s_pushstk (spf, &spf->clause, a);
  s_pushstk (spf, &spf->clause, b);
  s_pushstk (spf, &spf->clause, 0); // lifted binary clause, a, b
  s_addcls (spf, REDCS);
  s_clnstk (&spf->clause);
}

static int s_iftaux (SPF * spf) {
  int i, idx, lit, * reprs[3], first, outer, inner, changed, branch;
  int ok, oldouter, dom, repr, other;
  int lit1, lit2, repr1, repr2, orepr1, orepr2;
  Stk probes, represented[2], saved, tmp;
  unsigned pos, delta, mod;
  Val val, val1, val2;
  int64_t limit;
  NEW (spf->repr, spf->nvars);
  limit = spf->opts.lftmaxeff.val/10;
  if (limit < spf->opts.lftmineff.val) limit = spf->opts.lftmineff.val;
  if (limit > spf->opts.lftmaxeff.val) limit = spf->opts.lftmaxeff.val;
  // lifting with penalty %d", spf->limits.lft.pen);
  if (spf->limits.lft.pen < 0) limit <<= -spf->limits.lft.pen;
  if (spf->limits.lft.pen > 0) limit >>= spf->limits.lft.pen;
  //lifting with up to %lld propagations", (long long) limit);
  limit += spf->stats.visits.simp;
  CLR (probes); CLR (saved); CLR (tmp);
  CLR (represented[0]); CLR (represented[1]);
  NEW (reprs[0], spf->nvars);
  NEW (reprs[1], spf->nvars);
  NEW (reprs[2], spf->nvars);
  for (idx = 2; idx < spf->nvars; idx++) {
    if (!s_isfree (spf, idx)) continue;
    s_pushstk (spf, &probes, idx);
  }
  mod = s_cntstk (&probes);
  if (!(mod)) goto DONE;

  pos = s_rand (spf)  % mod;
  delta = s_rand (spf) % mod;
  if (!delta) delta++;
  while (s_gcd (delta, mod) > 1)
    if (++delta == mod) delta = 1;
  //lifting start %u delta %u mod %u", pos, delta, mod
  changed = first = 0;
  while (!spf->mt) {
    if (spf->stats.visits.simp >= limit) break;
    if (s_terminate (spf)) break;
    if (!s_syncunits (spf)) break;
    assert (pos < (unsigned) mod);
    outer = probes.start[pos];
    if (outer == first) { if (changed) changed = 0; else break; }
    if (!first) first = outer;
    pos += delta;
    if (pos >= mod) pos -= mod;
    if (s_val (spf, outer)) continue;
    //1st outer branch %d during lifting, outer
    oldouter = s_cntstk (&spf->trail);
 //------------------------- 
    s_iassume (spf, outer);
    ok = s_bcp (spf);
    if (!ok) {
FIRST_OUTER_BRANCH_FAILED:
      dom = s_prbana (spf, outer);
      //1st outer branch failed literal %d during lifting, outer
      s_backtrack (spf, 0);
//--------------------------------------
      s_unit (spf, -dom);
      if (s_bcp (spf)) continue;  // empty clause after propagating outer probe during lifting
      spf->mt = 1;
      break;
    }
    inner = s_innerprobe (spf, oldouter, &probes, &tmp);
    if (!inner) {
FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE:
      //no inner probe for 1st outer probe %d", outer
      for (i = oldouter; (unsigned)i < s_cntstk (&spf->trail); i++) {
	lit = s_peek (&spf->trail, i);
	idx = abs (lit);
	reprs[0][idx] = lit_sign (lit);
	s_pushstk (spf, &represented[0], idx);
      }
      goto END_OF_FIRST_OUTER_BRANCH;
    }   //1st inner branch %d in outer 1st branch %d", inner, outer
    s_iassume (spf, inner);
    ok = s_bcp (spf);
    if (!ok) {//1st inner branch failed literal %d on 1st outer branch %d,inner, outer
      s_backtrack (spf, 1);
      s_addliftbincls (spf, -inner, -outer);
      ok = s_bcp (spf);
      if (ok) goto FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE;
      //conflict after propagating negation of 1st inner branch
      goto FIRST_OUTER_BRANCH_FAILED;
    }
    s_clnstk (&saved);
    for (i = oldouter; (unsigned)i < s_cntstk (&spf->trail); i++)
      s_pushstk (spf, &saved, s_peek (&spf->trail, i));
   //saved %d assignments of 1st inner branch %d in 1st outer branch, s_cntstk (&saved), inner, outer
    s_backtrack (spf, 1);
    //2nd inner branch %d in 1st outer branch %d", -inner, outer
    s_iassume (spf, -inner);
    ok = s_bcp (spf);
    if (!ok) {// 2nd inner branch failed literal %d on 1st outer branch %d,-inner, outer
      s_backtrack (spf, 1);
      s_addliftbincls (spf, inner, -outer);
      ok = s_bcp (spf);
      if (ok) goto FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE;
      // conflict after propagating negation of 2nd inner branch
      goto FIRST_OUTER_BRANCH_FAILED;
    } 
    while (!s_mtstk (&saved)) {
      lit = s_popstk (&saved);
      idx = abs (lit);
      val1 = lit_sign (lit);
      val2 = s_val (spf, idx);
      if (val1 == val2) {
	reprs[0][idx] = val1;
	s_pushstk (spf, &represented[0], idx);
      } else if (lit != inner && val1 == -val2) {
	assert (lit != -inner);
	repr = s_ptrjmp (reprs[0], spf->nvars-1, inner);
	other = s_ptrjmp (reprs[0], spf->nvars-1, lit);
	if (s_cmprepr (spf, other, repr) < 0) SWAP2 (repr, other);
	if (other < 0) other = -other, repr = -repr;
	assert (!reprs[0][other]);
	reprs[0][other] = repr;
	s_pushstk (spf, &represented[0], other);
      } else assert (lit == inner || !val2);
    }
    s_backtrack (spf, 1);
END_OF_FIRST_OUTER_BRANCH:
    s_backtrack (spf, 0);
    // 2nd outer branch %d during lifting, -outer
    s_iassume (spf, -outer);
    ok = s_bcp (spf);
    if (!ok) {
SECOND_OUTER_BRANCH_FAILED:
      dom = s_prbana (spf, -outer);
   //2nd branch outer failed literal %d during lifting, -outer
      s_backtrack (spf, 0);
      s_unit (spf, -dom);
      if (s_bcp (spf)) goto CONTINUE;
      spf->mt = 1;
      goto CONTINUE;
    }
    if (!inner || s_val (spf, inner)) 
      inner = s_innerprobe (spf, oldouter, &probes, &tmp);
    if (!inner) {
SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE:
      //no inner probe for 2nd outer branch %d", -outer
      for (i = oldouter; (unsigned)i < s_cntstk (&spf->trail); i++) {
	lit = s_peek (&spf->trail, i);
	idx = abs (lit);
	reprs[1][idx] = lit_sign (lit);
	s_pushstk (spf, &represented[1], idx);
      }
      goto END_OF_SECOND_BRANCH;
    }
    //1st inner branch %d in outer 2nd branch %d", inner, -outer
    s_iassume (spf, inner);
    ok = s_bcp (spf);
    if (!ok) {//1st inner branch failed literal %d on 2nd outer branch %d", inner, -outer
      s_backtrack (spf, 1);
      s_addliftbincls (spf, -inner, outer);
      ok = s_bcp (spf);
      if (ok) goto SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE;
      // conflict after propagating negation of 1st inner branch
      goto SECOND_OUTER_BRANCH_FAILED;
    }
    s_clnstk (&saved);
    for (i = oldouter; (unsigned)i < s_cntstk (&spf->trail); i++)
      s_pushstk (spf, &saved, s_peek (&spf->trail, i));
    //saved %d assignments of 1st inner branch %d in 2nd outer branch %d",s_cntstk (&saved), inner, -outer
    s_backtrack (spf, 1);
    // 2nd inner branch %d in 2nd outer branch %d", -inner, -outer
    s_iassume (spf, -inner);
    ok = s_bcp (spf);
    if (!ok) {// 2nd inner branch failed literal %d on 2nd outer branch %d", -inner, -outer
      s_backtrack (spf, 1);
      s_addliftbincls (spf, inner, outer);
      ok = s_bcp (spf);
      if (ok) goto SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE;
      //conflict after propagating negation of 2nd inner branch
      goto SECOND_OUTER_BRANCH_FAILED;
    }
    while (!s_mtstk (&saved)) {
      lit = s_popstk (&saved);
      idx = abs (lit);
      val1 = lit_sign (lit);
      val2 = s_val (spf, idx);
      if (val1 == val2) {
	reprs[1][idx] = val1;
	s_pushstk (spf, &represented[1], idx);
      } else if (lit != inner && val1 == -val2) {
	repr = s_ptrjmp (reprs[1], spf->nvars-1, inner);
	other = s_ptrjmp (reprs[1], spf->nvars-1, lit);
	if (s_cmprepr (spf, other, repr) < 0) SWAP2 (repr, other);
	if (other < 0) other = -other, repr = -repr;
	reprs[1][other] = repr;
	s_pushstk (spf, &represented[1], other);
      } 
    }
    s_backtrack (spf, 1);
END_OF_SECOND_BRANCH:
    s_backtrack (spf, 0);
    for (branch = 0; branch <= 1; branch++) {
      for (i = 0; (unsigned)i < s_cntstk (&represented[branch]); i++) {
	lit1 = s_peek (&represented[branch], i);
	lit2 = reprs[branch][lit1];
	if (abs (lit2) == 1) {
	  val = s_val (spf, lit1);
	  if (val) continue;
	  repr1 = s_ptrjmp (reprs[!branch], spf->nvars-1, lit1);
	  if (repr1 != lit2) continue;
	  //common constant equivalence : %d = %d  (branch %d, lit1, lit2, branch);
	  s_unit (spf, lit2*lit1);
	} else {
	  repr1 = s_ptrjmp (reprs[2], spf->nvars-1, lit1);
	  repr2 = s_ptrjmp (reprs[2], spf->nvars-1, lit2);
	  if (repr1 == repr2) continue;
	  orepr1 = s_ptrjmp (reprs[!branch], spf->nvars-1, lit1);
	  orepr2 = s_ptrjmp (reprs[!branch], spf->nvars-1, lit2);
	  if (orepr1 != orepr2) continue;
	  if (s_cmprepr (spf, repr2, repr1) < 0) SWAP2 (repr1, repr2);
	  if (repr2 < 0) repr2 = -repr2, repr1 = -repr1;
	  //common equivalence candidate
	  reprs[2][repr2] = repr1;
	}
      }
    }
    s_bcp (spf);
CONTINUE:
    s_backtrack (spf, 0);
    s_cleanrepr (spf, &represented[0], reprs[0]);
    s_cleanrepr (spf, &represented[1], reprs[1]);
  }
  if (!spf->mt) {
    for (idx = 2; idx < spf->nvars; idx++)
      (void) s_ptrjmp (reprs[2], spf->nvars-1, idx);
    for (idx = 2; idx < spf->nvars; idx++) {
      repr = s_ptrjmp (reprs[2], spf->nvars-1, idx);
      val = s_val (spf, idx);
      if (!val) continue;
      if (repr == -val) {//inconsistent assigned members of equivalence classe
	spf->mt = 1;
	goto DONE;
      }
      if (repr < 0) repr = -repr, val = -val;
      if (repr == 1) { assert (val == 1); continue; }
      reprs[2][repr] = val;
    }
    for (idx = 2; idx < spf->nvars; idx++) {
      repr = s_ptrjmp (reprs[2], spf->nvars-1, idx);
      if (repr == idx) continue;
      if (abs (repr) == 1) continue;
      //real common equivalence : %d = %d", idx, repr
      s_imerge (spf, idx, repr);
    }
  }
DONE:
  DEL (reprs[0], spf->nvars);
  DEL (reprs[1], spf->nvars);
  DEL (reprs[2], spf->nvars);
  s_relstk (spf, &probes);
  s_relstk (spf, &represented[0]);
  s_relstk (spf, &represented[1]);
  s_relstk (spf, &saved);
  s_relstk (spf, &tmp);
  if (spf->mt) DEL (spf->repr, spf->nvars);
  return !spf->mt;
}

int s_lift (SPF * spf) {
  int64_t oldprgss = spf->stats.prgss;
  int success;
  if (!s_small (spf)) goto NEXT;
  spf->lifting = 1;  spf->simp = 1;
  if (spf->level > 0) s_backtrack (spf, 0);
  if (!s_bcp (spf)) goto DONE;
  s_clearMap (spf);
  if (spf->mt) goto DONE;
  if (!s_iftaux (spf)) { assert (spf->mt); goto DONE; }
  if (!s_synceqs (spf)) { assert (spf->mt); goto DONE; }
  s_dcpdis (spf);
  s_dcpcln (spf);
  s_dcpcon (spf);
  s_fitlirs (spf);
  s_dreschedule (spf);
  s_map (spf);
  if (spf->mt) goto DONE;
  if (!s_bcp (spf)) goto DONE;
  s_clearMap (spf);
  if (spf->mt) goto DONE;
  s_dreschedule (spf);
  success = (spf->stats.prgss > oldprgss);
  if (success && spf->limits.lft.pen > MINPEN) spf->limits.lft.pen--;
  if (!success && spf->limits.lft.pen < MAXPEN) spf->limits.lft.pen++;
DONE:
  spf->lifting = 0;  spf->simp = 0;
NEXT:
  return !spf->mt;
}

static void s_dstpull (SPF * spf, int lit) {//distillation
  AVar * av;
  av = s_avar (spf, lit);
  if (av->mark) return;
  if (!s_evel (spf, lit)) return;
  av->mark = 1;
  if (s_decision (spf, lit)) {
    s_pushstk (spf, &spf->clause, lit);//added lit to learned clause
  } else {
    s_pushstk (spf, &spf->seen, -lit);
  }
}

static int s_dstanalit (SPF * spf, int lit) {
  int r0, r1, antecedents, other, next, tag, * p, * rsn;
  AVar * av;
  antecedents = 1;
  av = s_avar (spf, lit);
  rsn = s_rsn (spf, lit);
  r0 = rsn[0], r1 = rsn[1];
  // lit, r0, r1,starting literal distillation analysis for %d with", lit);
  //added %d to learned clause", lit);
  s_pushstk (spf, &spf->clause, lit);
  av->mark = 1;
  next = 0;
  for (;;) {
    tag = r0 & MASKCS;
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      s_dstpull (spf, other);
      if (tag == TRNCS) s_dstpull (spf, r1);
    } else {
      assert (tag == LRGCS);
      for (p = s_idx2lits (spf, (r0 & REDCS), r1); (other = *p); p++)
	if (other != lit) s_dstpull (spf, *p);
    }
    if ((unsigned)next == s_cntstk (&spf->seen)) break;
    lit = s_peek (&spf->seen, next++);
    av = s_avar (spf, lit);
    rsn = s_rsn (spf, lit);
    r0 = rsn[0], r1 = rsn[1];
    //lit, r0, r1, "literal distillation analysis of");
    antecedents++;
  }
  s_popnunmarkstk (spf, &spf->seen);
  //literal distillation analysis used %d antecedents", antecedents);
  return antecedents;
}

static int s_dstanaconf (SPF * spf) {
  int lit, r0, r1, unit, other, next, tag, * p, * rsn;
 
  lit = spf->conf.lit, r0 = spf->conf.rsn[0], r1 = spf->conf.rsn[1];
  //lit, r0, r1,starting conflict distillation analysis for %d with", lit);
  s_dstpull (spf, lit);
  next = 0;
  for (;;) {
    tag = r0 & MASKCS;
    if (tag == BINCS || tag == TRNCS) {
      other = r0 >> RMSHFT;
      s_dstpull (spf, other);
      if (tag == TRNCS) s_dstpull (spf, r1);
    } else {//tag == LRGCS
      for (p = s_idx2lits (spf, (r0 & REDCS), r1); (other = *p); p++)
	if (other != lit) s_dstpull (spf, *p);
    }
    if ((unsigned)next == s_cntstk (&spf->seen)) break;
    lit = s_peek (&spf->seen, next++);
    rsn = s_rsn (spf, lit);
    r0 = rsn[0], r1 = rsn[1];
    //lit, r0, r1, "conflict distillation analysis of");
  }
  unit = (s_cntstk (&spf->clause) == 1) ? spf->clause.start[0] : 0;
  s_popnunmarkstk (spf, &spf->seen);
  s_popnunmarkstk (spf, &spf->clause);
  return unit;
}

static int s_distill (SPF * spf) {
  int lidx, i, * clauses, lit, distilled, size, count, nlrg, ntrn, idx,sign;
  int * c, * p, * q, satisfied, res, newsize, antecedents, * start, * trn;
  int blit, tag, red, other, other2, ok, success;
  int64_t limit, oldprgss = spf->stats.prgss;
  unsigned first, pos, delta, mod, last;
  int * w, * eow;
  HTS * hts;
  Val val;
  
  spf->distilling = 1;
  spf->simp = 1;
  res = 1;
  nlrg = 0;
  for (c = spf->irr.start; c < spf->irr.top; c = p) {
    p = c;
    lit = *p++;
    if (lit == REMOVED) continue;
    while (*p++) assert (p < spf->irr.top);
    nlrg++;
  }
 // if (nlrg) LOG (1, "distilling %d large clauses", nlrg);
 // else LOG (1, "could not find any large irredundant clause to distill");
  ntrn = 0;
  for (idx = 2; idx < spf->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = s_hts (spf, lit);
      if (!hts->count) continue;
      w = s_hts2wchs (spf, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	other = blit >> RMSHFT;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag != TRNCS) continue;
	if (red) continue;
	if (abs (other) < idx) continue;
	other2 = *p;
	if (abs (other2) < idx) continue;
	ntrn++;
      }
    }
  }
 // if (ntrn) LOG (1, "distilling %d ternary clauses", ntrn);
 // else LOG (1, "could not find any ternary irredundant clause to distill");
  mod = nlrg + ntrn;
  if (!mod) { //there are no irredundant clauses to distill");
    goto NEXT;
  }
  NEW (trn, 3*ntrn*sizeof *trn);//, int *);
  i = 0;
  for (idx = 2; idx < spf->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = s_hts (spf, lit);
      if (!hts->count) continue;
      w = s_hts2wchs (spf, hts);
      eow = w + hts->count;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	red = blit & REDCS;
	other = blit >> RMSHFT;
	if (tag == TRNCS || tag == LRGCS) p++;
	if (tag != TRNCS) continue;
	if (red) continue;
	if (abs (other) < idx) continue;
	other2 = *p;
	if (abs (other2) < idx) continue;
	trn[i++] = lit;
	trn[i++] = other;
	trn[i++] = other2;
      }
    }
  }
  if (spf->level > 0) s_backtrack (spf, 0);
  spf->measureagility = spf->propred = 0;
  pos = s_rand (spf) % mod;
  delta = s_rand (spf) % mod;
  if (!delta) delta++;
  while (s_gcd (delta, mod) > 1)
    if (++delta == mod) delta = 1;
  //distilling start %u delta %u mod %u", pos, delta, mod);
  limit = spf->opts.dstmaxeff.val/10;
  if (limit < spf->opts.dstmineff.val) limit = spf->opts.dstmineff.val;
  if (limit > spf->opts.dstmaxeff.val) limit = spf->opts.dstmaxeff.val;
  //distilling with penalty %d", spf->limits.dst.pen);
  if (spf->limits.dst.pen < 0) limit <<= -spf->limits.dst.pen;
  if (spf->limits.dst.pen > 0) limit >>= spf->limits.dst.pen;
  //distilling with up to %lld propagations", limit);
  limit += spf->stats.visits.simp;
  NEW (clauses, mod);
  i = 0;
  start = spf->irr.start;
  for (c = start; c < spf->irr.top; c = p) {
    p = c;
    lit = *p++;
    if (lit == REMOVED) continue;
    while (*p++) assert (p < spf->irr.top);
    clauses[i++] = c - start;
  }
  first = mod;
  success = count = distilled = 0;
  while (spf->stats.visits.simp < limit && !s_terminate (spf)) {
    if (!(res = s_syncunits (spf))) { assert (spf->mt); goto DONE; }
    count++;
    if (pos < (unsigned)nlrg) {
      lidx = clauses[pos];
      c = start + lidx;
      if (*c == REMOVED) goto CONTINUE;
      // distilling large %d clause, lidx
      satisfied = (s_val (spf, c[0]) > 0 || s_val (spf, c[1]) > 0);
      q = c + 2;
      for (p = q; (lit = *p); p++) {
	if (satisfied) continue;
	val = s_val (spf, lit);
	if (val < 0) continue;
	if (val > 0) { satisfied = lit; continue; }
	*q++ = lit;
      }
      if (!satisfied) assert (!s_val (spf, c[0]) && !s_val (spf, c[1]));
      size = q - c;
      *q++ = 0;
      while (q <= p) *q++ = REMOVED;
      if (satisfied || size <= 3) {
	s_rmlwch (spf, c[0], 0, lidx);
	s_rmlwch (spf, c[1], 0, lidx);
      }
      if (satisfied) {//distilled large %d clause already %d satisfied,lidx, satisfied
      } else if (size == 2) {//found new binary clause distilling large %d clause, lidx
	s_wchbin (spf, c[0], c[1], 0);
	s_wchbin (spf, c[1], c[0], 0);
      } else if (size == 3) {//found new ternary clause distilling large %d clause", lidx
	s_wchtrn (spf, c[0], c[1], c[2], 0);
	s_wchtrn (spf, c[1], c[0], c[2], 0);
	s_wchtrn (spf, c[2], c[0], c[1], 0);
      } else assert (size > 3);
      if (satisfied || size <= 3) {
	while (p >= c) *p-- = REMOVED;
	goto CONTINUE;
      }
      distilled++;
      spf->ignlidx = lidx;
      ok = 1;
      val = 0;
      for (p = c; (lit = *p); p++) {
	val = s_val (spf, lit);
	if (val) break;
	s_iassume (spf, -lit);
	ok = s_bcp (spf);
	if (!ok) break;
      }
      spf->ignlidx = -1;
      if (ok || !lit) s_backtrack (spf, 0);
      if (!lit) goto CONTINUE;
      s_rmlwch (spf, c[0], 0, lidx);
      s_rmlwch (spf, c[1], 0, lidx);
      if (val < 0) {
	spf->stats.prgss++;
	success++;
	//removing literal %d in distilled large %d clause,lit, lidx
	for (p = c; (*p != lit); p++) ;
	for (q = p++; (lit = *p); p++) *q++ = lit;
	*q++ = 0;
	*q = REMOVED;
	if (size == 4) goto LRG2TRN; else goto LRG2LRG;
      } else if (val > 0) {
	newsize = p - c + 1;
	assert (2 <= newsize && newsize <= size);
	if (newsize == size) goto LRGRED;
	antecedents = s_dstanalit (spf, lit);
	if (antecedents > 1) {
	  p = q = c;
	  while (q < c + newsize) {
	    lit = *q++;
	    if (s_marked (spf, lit)) *p++ = lit;
	  }
	  p--;
	  newsize = p - c + 1;
	  assert (2 <= newsize && newsize <= size);
	}
	s_popnunmarkstk (spf, &spf->clause);
	if (antecedents == 1) goto LRGRED;
	spf->stats.prgss++;	//shortening distilled large %d clause by %d literals,idx, size - newsize
	*++p = 0;
	while (*++p) *p = REMOVED;
	*p = REMOVED;
	if (newsize == 2) {
//LRG2BIN:
	  //distilled large %d clause becomes binary clause %d %d",lidx, c[0], c[1]
	  s_wchbin (spf, c[0], c[1], 0);
	  s_wchbin (spf, c[1], c[0], 0);
	  c[0] = c[1] = c[2] = REMOVED;
	} else if (newsize == 3) {
LRG2TRN:
	 //distilled large %d clause becomes ternary clause %d %d %d, lidx, c[0], c[1], c[2]
	  s_wchtrn (spf, c[0], c[1], c[2], 0);
	  s_wchtrn (spf, c[1], c[0], c[2], 0);
	  s_wchtrn (spf, c[2], c[0], c[1], 0);
	  c[0] = c[1] = c[2] = c[3] = REMOVED;
	  assert (c[4] == REMOVED);
	} else {
LRG2LRG:
	  (void) s_wchlrg (spf, c[1], c[0], 0, lidx);
	  (void) s_wchlrg (spf, c[0], c[1], 0, lidx);//distilled %d clause remains large clause, lidx
	}
      } else if (p == c) {
	lit = s_dstanaconf (spf);
	s_backtrack (spf, 0);
LRGFAILED:
	spf->stats.prgss++;
	//failed literal %d during distilling large %d clause,-lit, lidx
	s_unit (spf, lit);
	spf->propred = 1;
	res = s_bcp (spf);
	spf->propred = 0;
	if (!res) { assert (!spf->mt); spf->mt = 1; goto DONE; }
	goto LRGREM;
      } else {
	lit = s_dstanaconf (spf);
	s_backtrack (spf, 0);
	if (lit) goto LRGFAILED;
LRGRED:	//redundant distilled large %d clause, lidx
	spf->stats.prgss++;
LRGREM:
	for (p = c; *p; p++) *p = REMOVED;
	*p = REMOVED;
      }
    } else {
      lidx = pos - nlrg;
      c = trn + 3*lidx;
      if (*c == REMOVED) goto CONTINUE;
      //distilling ternary clause %d %d %d", c[0], c[1], c[2]
      for (i = 0; i < 3; i++) {
	if (s_val (spf, c[i]) <= 0) continue;
//	distilled ternary clause %d %d %d already satisfied by %d c[0], c[1], c[2], c[i]
	goto TRNREM;
      }
      for (i = 0; i < 3; i++) {
	val = s_val (spf, c[i]);
	if (!val) continue;
	if (i != 2) SWAP2 (c[i], c[2]);
	//removing false %d from distilled ternary clause %d %d %d,c[i], c[0], c[1], c[2]
	goto TRN2BIN;
      }
      distilled++;
      for (i = 0; i < 3; i++) spf->ignlits[i] = c[i];
      spf->igntrn = 1;
      ok = 1;
      val = 0;
      lit = 0;
      for (i = 0; i < 3; i++) {
	lit = c[i];
	val = s_val (spf, lit);
	if (val) break;
	s_iassume (spf, -lit);
	ok = s_bcp (spf);
	if (!ok) break;
      }
      if (val || i == 3) s_backtrack (spf, 0);
      spf->igntrn = 0;
      if (i == 3) goto CONTINUE;
      if (val < 0) {
	spf->stats.prgss++;
	if (i != 2) SWAP2 (c[i], c[2]);
TRN2BIN:
	//distilled ternary clause becomes binary clause %d %d", c[0], c[1]
	s_wchbin (spf, c[0], c[1], 0);
	s_wchbin (spf, c[1], c[0], 0);
	goto TRNREM;
      } else if (val > 0) {
	if (i == 2) goto TRNRED;
	antecedents = s_dstanalit (spf, lit);
	s_popnunmarkstk (spf, &spf->clause);
	if (antecedents == 1) goto TRNRED;
	spf->stats.prgss++;
	goto TRN2BIN;
      } else if (i == 0) {
	lit = s_dstanaconf (spf);
	s_backtrack (spf, 0);
TRNFAILED:
        spf->stats.prgss++;//failed literal %d during distilling ternary clause, -lit
	s_unit (spf, lit);
	spf->propred = 1;
	res = s_bcp (spf);
	spf->propred = 0;
	if (!res) { assert (!spf->mt); spf->mt = 1; goto DONE; }
	else goto TRNREM;
      } else {
	lit = s_dstanaconf (spf);
	s_backtrack (spf, 0);
	if (lit) goto TRNFAILED;
TRNRED:	//redundant distilled ternary clause %d %d %d,c[0], c[1], c[2];
	spf->stats.prgss++;
TRNREM:
	s_rmtwch (spf, c[0], c[1], c[2], 0);
	s_rmtwch (spf, c[1], c[0], c[2], 0);
	s_rmtwch (spf, c[2], c[0], c[1], 0);
	*c = REMOVED;
      }
    }
CONTINUE:
    last = pos;
    pos += delta;
    if (pos >= mod) pos -= mod;
    if (pos == first) { assert (count == mod); break; }
    if (mod == 1) break;
    if (first == mod) first = last;
  }
DONE:
  DEL (trn, 3*ntrn*sizeof *trn);
  DEL (clauses, mod);
  s_fitstk (spf, &spf->irr);
  spf->measureagility = spf->propred = 1;
  success = oldprgss < spf->stats.prgss;
  if (success && spf->limits.dst.pen > MINPEN) spf->limits.dst.pen--;
  if (!success && spf->limits.dst.pen < MAXPEN) spf->limits.dst.pen++;
  //ssuccessfully distilled %d clauses, success ? "" : "un", distilled
NEXT:
  spf->distilling = 0;
  spf->simp = 0;
  return res;
}

static int s_trdbin (SPF * spf, int start, int target, int irr) {
  int lit, next, blit, tag, red, other, * p, * w, * eow, res, ign, val;
  HTS * hts;
  //trying transitive reduction of %s binary clause %d %d", s_red2str (irr^REDCS), start, target
  s_pushnmarkseen (spf, -start);
  next = 0;
  res = 0;
  ign = 1;
  while ((unsigned)next < s_cntstk (&spf->seen)) {
    lit = s_peek (&spf->seen, next++);
    spf->stats.trd.steps++;
    //transitive reduction search step %d", lit);
    val = s_val (spf, lit);
    if (val) continue;
    hts = s_hts (spf, -lit);
    if (!hts->count) continue;
    w = s_hts2wchs (spf, hts);
    eow = w + hts->count;
    for (p = w; p < eow; p++) {
      blit = *p;
      tag = blit & MASKCS;
      if (tag == LRGCS || tag == TRNCS) p++;
      if (tag != BINCS) continue;
      red = blit & REDCS;
      if (irr && red) continue;
      other = blit >> RMSHFT;
      if (other == start) continue;
      if (other == target) {
	if (lit == -start && ign) { ign = 0; continue; }
	//transitive path closed with %s binary clause %d %d",s_red2str (red), -lit, other);
	res = 1;
	goto DONE;
      }
      val = s_marked (spf, other);
      if (val > 0) continue;
      if (val < 0) {  //failed literal %d in transitive reduction, -start
	s_unit (spf, start);
	val = s_bcp (spf);
	if (!val && !spf->mt) spf->mt = 1;
	res = -1;
	goto DONE;
      }
      s_pushnmarkseen (spf, other);
      //transitive reduction follows %s binary clause %d %d,s_red2str (red), -lit, other
    }
  }
DONE:
  s_popnunmarkstk (spf, &spf->seen);
  return res;
}

static void s_trdlit (SPF * spf, int start) {
  int target, * w, * p, * eow, blit, tag, red, val;
  HTS * hts;
  val = s_val (spf, start);
  if (val) return;
  //transitive reduction of binary clauses with %d", start
  hts = s_hts (spf, start);
  if (!hts->count) return;
  w = s_hts2wchs (spf, hts);
  eow = w + hts->count;
  for (p = w;
       p < eow && (spf->stats.trd.steps < spf->limits.trd.steps);
       p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == TRNCS || tag == LRGCS) p++;
    if (tag != BINCS) continue;
    target = blit >> RMSHFT;
    if (abs (start) > abs (target)) continue;
    red = blit & REDCS;
    val = s_trdbin (spf, start, target, red^REDCS);
    if (!val) continue;
    if (val < 0) break;
    //removing transitive redundant %s binary clause %d %d, s_red2str (red), start, target);
    spf->stats.prgss++;
    s_rmbwch (spf, start, target, red);
    s_rmbwch (spf, target, start, red);
    if (red) break;
    break;
  }
}

static int s_transitive_reduction (SPF * spf) {
  unsigned pos, delta, mod, ulit, first, last;
  int64_t limit, oldprgss = spf->stats.prgss;;
  int lit, count, success;
  if (spf->nvars <= 2) return 1;
  if (spf->level > 0) s_backtrack (spf, 0);
  mod = 2*(spf->nvars - 2);
  pos = s_rand (spf) % mod;
  delta = s_rand (spf) % mod;
  if (!delta) delta++;
  while (s_gcd (delta, mod) > 1)
    if (++delta == mod) delta = 1;
  //transitive reduction start %u delta %u mod %u", pos, delta, mod);
  limit = spf->opts.trdmaxeff.val/10;
  if (limit < spf->opts.trdmineff.val) limit = spf->opts.trdmineff.val;
  if (limit > spf->opts.trdmaxeff.val) limit = spf->opts.trdmaxeff.val;
  //transitive reduction penalty %d", spf->limits.trd.pen);
  if (spf->limits.trd.pen < 0) limit <<= -spf->limits.trd.pen;
  if (spf->limits.trd.pen > 0) limit >>= spf->limits.trd.pen;
  //transitive reduction with up to %lld search steps", limit);
  spf->limits.trd.steps = spf->stats.trd.steps + limit;
  first = mod;
  count = 0;
  while (spf->stats.trd.steps < spf->limits.trd.steps) {
    if (s_terminate (spf)) break;
    if (!s_syncunits (spf)) break;
    ulit = pos + 4;
    lit = s_ilit (ulit);
    s_trdlit (spf, lit);
    count++;
    if (spf->mt) break;
    last = pos;
    pos += delta;
    if (pos >= mod) pos -= mod;
    if (pos == first) { assert (count == mod); break; }
    if (mod == 1) break;
    if (first == mod) first = last;
  }
  success = oldprgss < spf->stats.prgss;
  if (success && spf->limits.trd.pen > MINPEN) spf->limits.trd.pen--;
  if (!success && spf->limits.trd.pen < MAXPEN) spf->limits.trd.pen++;
  return !spf->mt;
}

static int s_unhdhasbins (SPF * spf, const DFPR * dfpr,int lit, int irronly) {
  int blit, tag, other, val, red, ulit;
  const int * p, * w, * eos;
  HTS * hts;
  hts = s_hts (spf, lit);
  w = s_hts2wchs (spf, hts);
  eos = w + hts->count;
  for (p = w; p < eos; p++) {
    blit = *p;
    tag = blit & MASKCS;
    if (tag == IRRCS) continue;
    if (tag == TRNCS || tag == LRGCS) { p++; continue; }
    red = blit & REDCS;
    if (irronly && red) continue;
    other = blit >> RMSHFT;
    val = s_val (spf, other);
    assert (val >= 0);
    if (val > 0) continue;
    ulit = s_ulit (other);
    if (!dfpr[ulit].discovered) return 1;
  }
  return 0;
}

static int s_unhdisroot (SPF * spf, int lit, DFPR * dfpr, int irronly) {
  int res = !s_unhdhasbins (spf, dfpr, lit, irronly);
  return res;
}

static int s_mtwtk (Wtk * wtk) { return wtk->top == wtk->start; }
static int s_fullwtk (Wtk * wtk) { return wtk->top == wtk->end; }
static int s_sizewtk (Wtk * wtk) { return wtk->end - wtk->start; }
static int s_cntwtk (Wtk * wtk) { return wtk->top - wtk->start; }
static void s_relwtk (SPF * spf, Wtk * wtk) {
  DEL (wtk->start, s_sizewtk (wtk));
  memset (wtk, 0, sizeof *wtk);
}

static void s_enlwtk (SPF * spf, Wtk * wtk) {
  int oldsize = s_sizewtk (wtk);
  int newsize = oldsize ? 2*oldsize : 1;
  int count = s_cntwtk (wtk);
  RSZ (wtk->start, oldsize, newsize, Work *);
  wtk->top = wtk->start + count;
  wtk->end = wtk->start + newsize;
}

static void s_pushwtk (SPF * spf, Wtk * wtk, Wrag wrag, int lit, int other, int red) {
  Work w;
  if (s_fullwtk (wtk)) s_enlwtk (spf, wtk);
  w.wrag = wrag;
  w.other = other;
  w.red = red ? 1 : 0;
  w.removed = 0;
  w.lit = lit;
  *wtk->top++ = w;
}

#define s_popwtk(WTK,WRAG,LIT,OTHER,RED,REMOVED) \
do { \
  assert (!s_mtwtk (WTK)); \
  (WTK)->top--; \
  (WRAG) = (WTK)->top->wrag; \
  (LIT) = (WTK)->top->lit; \
  (OTHER) = (WTK)->top->other; \
  (RED) = (WTK)->top->red ? REDCS : 0; \
  (REMOVED) = (WTK)->top->removed; \
} while (0)

static int s_stamp (SPF * spf, int root,
                     DFPR * dfpr, DFOPF * dfopf,
		     Wtk * work, Stk * units, Stk * sccs, Stk * trds,
		     int * visitedptr, int stamp, int irronly) {
  int uroot, lit, ulit, blit, tag, red, other, failed, uother, unotother;
  int observed, discovered, pos, undiscovered;
  unsigned start, end, mod, i, j, sccsize;
  const int * p, * w, * eos;
  int startstamp;
  const Work * r;
  int removed;
  HTS * hts;
  Wrag wrag;
  if (s_val (spf, root)) return stamp;
  uroot =  s_ulit (root);
  if (dfpr[uroot].discovered) return stamp;
  //stamping dfs %s %d %s",(s_unhdisroot (spf, root, dfpr, irronly) ? "root" : "start"), root,
  //     irronly ? "only over irredundant clauses" :"also over redundant clauses");
  startstamp = 0;
  s_pushwtk (spf, work, PREFIX, root, 0, 0);
  while (!s_mtwtk (work)) {
    spf->stats.unhd.steps++;
    s_popwtk (work, wrag, lit, other, red, removed);
    if (removed) continue;
    if (wrag == PREFIX) {
      ulit = s_ulit (lit);
      if (dfpr[ulit].discovered) {
	dfopf[ulit].observed = stamp;//stamping %d observed %d", lit, stamp);
	continue;
      }
      dfpr[ulit].discovered = ++stamp;
      dfopf[ulit].observed = stamp;//stamping %d observed %d", lit, stamp);
      *visitedptr += 1;
      if (!startstamp) {
	startstamp = stamp;//root %d with stamp %d", lit, startstamp);
	dfpr[ulit].root = lit;//stamping %d root %d", lit, lit);
	//stamping %d parent %d", lit, 0);
      }//stamping %d discovered %d", lit, stamp);
      s_pushwtk (spf, work, POSTFIX, lit, 0, 0);
      dfopf[ulit].pushed = s_cntwtk (work);
      dfopf[ulit].flag = 1;
      s_pushstk (spf, sccs, lit);
      hts = s_hts (spf, -lit);
      w = s_hts2wchs (spf, hts);
      eos = w + hts->count;
      for (undiscovered = 0; undiscovered <= 1 ; undiscovered++) {
	start = s_cntwtk (work);
	for (p = w; p < eos; p++) {
	  blit = *p;
	  tag = blit & MASKCS;
	  if (tag == IRRCS) continue;
	  if (tag == TRNCS || tag == LRGCS) { p++; continue; }
	  red = blit & REDCS;
	  if (irronly && red) continue;
	  other = blit >> RMSHFT;
	  if (s_val (spf, other)) continue;
	  uother = s_ulit (other);
	  if (undiscovered != !dfpr[ulit].discovered) continue;
	 // COVER (s_signedmarked (spf, other) > 0);
	  if (s_signedmarked (spf, other) > 0) {//stamping skips duplicated edge %d %d", lit, other);
	    continue;
	  }
	  s_signedmark (spf, other);
	  s_pushwtk (spf, work, BEFORE, lit, other, red);
	}
	end = s_cntwtk (work);
	for (r = work->start + start; r < work->top; r++) 
	  s_unmark (spf, r->other);
	mod = (end - start);
	if (mod <= 1) continue;
	for (i = start; i < end - 1;  i++) {
	  assert (1 < mod && mod == (end - i));
	  j = s_rand (spf) % mod--;
	  if (!j) continue;
	  j = i + j;
	  SWAP2 (work->start[i], work->start[j]);
	}
      }
    } else if (wrag == BEFORE) {// before recursive call,stamping edge %d %d before recursion", lit, other);
      s_pushwtk (spf, work, AFTER, lit, other, red);
      ulit = s_ulit (lit);
      uother = s_ulit (other);
      unotother = s_ulit (-other);
      if (spf->opts.unhdextstamp.val && (irronly || red) &&
	  dfopf[uother].observed > dfpr[ulit].discovered) {//transitive edge %d %d during stamping", lit, other);
	spf->stats.prgss++;
	s_rmbcls (spf, -lit, other, red);
	if ((pos = dfopf[unotother].pushed) >= 0) {
	  while (pos  < s_cntwtk (work)) {
	    if (work->start[pos].lit != -other) break;
	    if (work->start[pos].other == -lit) {//removing edge %d %d from DFS stack", -other, -lit);
	      work->start[pos].removed = 1;
	    }
	    pos++;
	  }
	}
	work->top--;
	continue;
      }
      observed = dfopf[unotother].observed;
      if (spf->opts.unhdextstamp.val && startstamp <= observed) {//stamping failing edge %d %d, lit, other
	for (failed = lit;
	     dfpr[s_ulit (failed)].discovered > observed;
	     failed = dfpr[s_ulit (failed)].parent);
	//stamping failed literal %d", failed
	s_pushstk (spf, units, -failed);
	if (dfpr[unotother].discovered && !dfpr[unotother].finished) {
//stamping skips edge %d %d after failed literal %d",lit, other, failed
	  work->top--;
	  continue;
	}
      }
      if (!dfpr[uother].discovered) {
	dfpr[uother].parent = lit;//stamping %d parent %d", other, lit
	dfpr[uother].root = root;//stamping %d root %d", other, root
	s_pushwtk (spf, work, PREFIX, other, 0, 0);
      }
    } else if (wrag == AFTER) {	// after recursive call. stamping edge %d %d after recursion, lit, other
      uother = s_ulit (other);
      ulit = s_ulit (lit);
      if (spf->opts.unhdextstamp.val && !dfpr[uother].finished &&
          dfpr[uother].discovered < dfpr[ulit].discovered) {//stamping back edge %d %d", lit, other
	dfpr[ulit].discovered = dfpr[uother].discovered;
//stamping %d reduced discovered to %d",lit, dfpr[ulit].discovered);
	if (dfopf[ulit].flag) {// stamping %d as being part of a non-trivial SCC", lit
	  dfopf[ulit].flag = 0;
	}
      }
      dfopf[uother].observed = stamp;//stamping %d observed %d", other, stamp
    } else {//stamping postfix %d", lit
      ulit = s_ulit (lit);
      if (dfopf[ulit].flag) {
	stamp++;
	sccsize = 0;
	discovered = dfpr[ulit].discovered;
	do {
	  other = s_popstk (sccs);
	  uother = s_ulit (other);
	  dfopf[uother].pushed = -1;
	  dfopf[uother].flag = 0;
	  dfpr[uother].discovered = discovered;
	  dfpr[uother].finished = stamp;
//stamping %d interval %d %d parent %d root %d",other, dfpr[uother].discovered, dfpr[uother].finished,
	      // dfpr[uother].parent, dfpr[uother].root);
	  sccsize++;
	} while (other != lit);
    //    if (sccsize > 1) {//stamping non trivial SCC of size %d", sccsize
	//  spf->stats.unhd.stamp.sccs++;
	//}
      } 
    }
  }
  return stamp;
}

static int s_unhlca (SPF * spf, const DFPR * dfpr, int a, int b) {
  const DFPR * c, * d;
  int u, v, p;
  if (a == b) return a;
  u = s_ulit (a), v = s_ulit (b);
  c = dfpr + u, d = dfpr + v;
  if (c->discovered <= d->discovered) {
    p = a;
  } else {
    assert (c->discovered > d->discovered);
    p = b;
    SWAP2 (c, d);
  }
  for (;;) {
    if (d->finished <= c->finished) break;
    p = c->parent;
    if (!p) break;
    u = s_ulit (p);
    c = dfpr + u;
  }  //unhiding least common ancestor of %d and %d is %d", a, b, p
  return p;
}

static int s_unhidefailed (SPF * spf, const DFPR * dfpr) {
  int idx, sign, lit, unit, nfailed = 0;
  for (idx = 2; idx < spf->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      if (s_terminate (spf)) return 0;
      if (!s_syncunits (spf)) return 0;
      spf->stats.unhd.steps++;
      lit = sign * idx;
      if (s_val (spf, lit)) continue;
      if (!dfpr[s_ulit (lit)].discovered) continue;
      if (s_unhimplincl (dfpr, lit, -lit)) {
	unit = -lit;//	unhiding %d implies %d", lit, -lit
      } else if (s_unhimplincl (dfpr, -lit, lit)) {
	unit = lit;//unhiding %d implies %d", -lit, lit
      } else continue;
      //unhiding failed literal %d", -unit
      s_unit (spf, unit);
      nfailed++;
      if (s_bcp (spf)) continue; //empty clause after propagating unhidden failed literal
      spf->mt = 1;
      return 0;
    }
  } //unhiding %d failed literals in this round, nfailed
  return 1;
}

static int s_unhroot (const DFPR * dfpr, int lit) {  return dfpr[s_ulit (lit)].root;}

static int s_unhidebintrn (SPF * spf, const DFPR * dfpr, int irronly) {
  int idx, sign, lit, blit, tag, red, other, other2, unit, root, lca;
  int nbinred, ntrnred, nbinunits, ntrnunits, ntrnstr, ntrnhbrs;
  const int * p, * eow;
  int ulit, uother;
  int * w , * q;
  long delta;
  HTS * hts;
  nbinred = ntrnred = nbinunits = ntrnunits = ntrnstr = ntrnhbrs = 0;
  for (idx = 2; idx < spf->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      if (s_terminate (spf)) return 0;
      if (!s_syncunits (spf)) return 0;
      spf->stats.unhd.steps++;
      lit = sign * idx;
      if (s_val (spf, lit)) continue;
      ulit = s_ulit (lit);
      if (!dfpr[ulit].discovered) continue;
      hts = s_hts (spf, lit);
      w = s_hts2wchs (spf, hts);
      eow = w + hts->count;
      q = w;
      for (p = w; p < eow; p++) {
	blit = *p;
	*q++ = blit;
	tag = blit & MASKCS;
	if (tag == TRNCS || tag == LRGCS) *q++ = *++p;
	if (tag == LRGCS) continue;
	red = blit & REDCS;
	other = blit >> RMSHFT;
	if (s_val (spf, other)) continue;
	uother = s_ulit (other);
	if (tag == BINCS) {
	  if (s_unhimplies2 (dfpr, other, lit)) {
	    //unhiding removal of literal %d with implication %d %d from binary clause %d %d,other,other,lit,lit,other
	    nbinunits++;
            unit = lit;
UNIT:
	    s_unit (spf, unit);
	    p++;
	    while (p < eow) *q++ = *p++;
	    s_shrinkhts (spf, hts, hts->count - (p - q));
	    if (s_bcp (spf)) goto NEXTIDX;//empty clause after propagating unhidden lifted unit
	    spf->mt = 1;
	    return 0;
	  } else if ((root = s_unhroot (dfpr, -lit)) &&
	             !s_val (spf, root) &&
	             root == s_unhroot (dfpr, -other)) {
	    //negated literals in binary clause %d %d implied by %d",lit, other, root
	    lca = s_unhlca (spf, dfpr, -lit, -other);
	    unit = -lca;
	    goto UNIT;
	  } else if (!irronly && !red) continue;
	  else {
	    if (dfpr[uother].parent == -lit) continue;
	    if (dfpr[ulit].parent == -other) continue;
	    if (!s_unhimplies2 (dfpr, -lit, other)) continue;
    //unhiding tautological binary clause %d %d", lit, other
	    spf->stats.prgss++;
	    nbinred++;
	    s_rmbwch (spf, other, lit, red);
	   //removed %s binary clause %d %d, s_red2str (red), lit, other);
	    q--;
	  }
	} else {
	  other2 = *p;
	  if (s_val (spf, other2)) continue;
	  if (s_unhimplies2incl (dfpr, other, lit) &&
	      s_unhimplies2incl (dfpr, other2, lit)) {
	 //unhiding removal of literals %d and %d with implications
	//%d %d and %d %d from ternary clause %d %d %d, other, other2, other, lit, other2, lit,lit, other, other2);
	    ntrnunits++;
	    unit = lit;
	    goto UNIT;
	  } else if ((root = s_unhroot (dfpr, -lit)) &&
	             !s_val (spf, root) &&
	             root == s_unhroot (dfpr, -other) &&
	             root == s_unhroot (dfpr, -other2)) {
	   //negation of literals in ternary clauses %d %d %d implied by %d", lit, other, other2, root);
	    lca = s_unhlca (spf, dfpr, -lit, -other);
	    lca = s_unhlca (spf, dfpr, lca, -other2);
	    unit = -lca;
	    goto UNIT;
	  } else if ((red || irronly) &&  (s_unhimplies2incl (dfpr, -lit, other) ||
	              s_unhimplies2incl (dfpr, -lit, other2))) {
	   //unhiding tautological ternary clause %d %d %d, lit, other, other2
	    spf->stats.prgss++;
	    ntrnred++;
	    s_rmtwch (spf, other, lit, other2, red);
	    s_rmtwch (spf, other2, lit, other, red);
	    //removed %s ternary clause %d %d %d, s_red2str (red), lit, other, other2);
	    q -= 2;
	  } else if (s_str (spf) && 
	             s_unhimplies2incl (dfpr, other2, lit)) {
TRNSTR://unhiding removal of literal %d with implication %d %d from ternary clause %d %d %d,
//	 other2, other2, lit, lit, other, other2);
	    spf->stats.prgss++;
	    ntrnstr++;
	    s_rmtwch (spf, other, lit, other2, red);
	    s_rmtwch (spf, other2, lit, other, red);
	   //removed %s ternary clause %d %d %d, s_red2str (red), lit, other, other2);
	    delta = s_wchbin (spf, other, lit, red);
	    if (delta) { p += delta, q += delta, eow += delta, w += delta; }
	    (--q)[-1] = red | BINCS | (other << RMSHFT);
	    continue;
	  } else if (s_str (spf) && s_unhimplies2incl (dfpr, other, lit)) {
	    SWAP2 (other, other2);
	    goto TRNSTR;
	  } else if (spf->opts.unhdhbr.val &&
	             (root = s_unhroot (dfpr, -lit)) &&
	             !s_val (spf, root)) {
	    if (root == s_unhroot (dfpr, -other2)) {
	      lca = s_unhlca (spf, dfpr, -lit, -other2);
	    } else if (root == s_unhroot (dfpr, -other)) {
	      lca = s_unhlca (spf, dfpr, -lit, -other);
	      SWAP2 (other, other2);
	    } else if (s_unhimplies2incl (dfpr, root, -other2)) lca = root;
	    else if (s_unhimplies2incl (dfpr, root, -other)) {
	      lca = root;
	      SWAP2 (other, other2);
	    } else continue;
	    if (!lca) continue;
	    if (abs (lca) == abs (lit)) continue;
	    if (abs (lca) == abs (other)) continue;
	    if (abs (lca) == abs (other2)) continue;
	    if (s_unhimplies2incl (dfpr, lca, other)) continue;
	   //negations of literals %d %d in ternary clause %d %d %d
	  // implied by %d", lit, other2, lit, other, other2, lca);
	    spf->stats.prgss++;
            ntrnhbrs++; //unhidden hyper binary resolved clause %d %d",-lca,other
	    delta = s_wchbin (spf, -lca, other, REDCS);
	    if (delta) { p += delta, q += delta, eow += delta, w += delta; }
	    delta = s_wchbin (spf, other, -lca, REDCS);
	    if (delta) { p += delta, q += delta, eow += delta, w += delta; }
	  }
	}
      }
      s_shrinkhts (spf, hts, hts->count - (p - q));
    }
NEXTIDX:
    ;
  }
  return 1;
}

static int s_cmpdfl (const DFL * a, const DFL * b) {  return a->discovered - b->discovered;}

static int s_unhideglue (SPF * spf, const DFPR * dfpr, int glue, int irronly) {
  DFL * dfl, * eodfl, * d, * e; int szdfl, posdfl, negdfl, ndfl, res;
  int oldsize, newsize, hastobesatisfied, satisfied, tautological;
  int watched, lit, ulit, val, sign, nonfalse, root, lca, unit;
  int ntaut = 0, nstr = 0, nunits = 0, lidx;
  int * p, * q, * c, * eoc, red;
  int lca1, lca2, root1, root2;
  Stk * lits;
  Lir * lir;

  if (glue < 0) {
    lir = 0;
    lits = &spf->irr;
    red = 0;
  } else {
    lir = spf->red;
    lits = &lir->lits;
    red = REDCS;
  }
  res = 1;
  dfl = 0; szdfl = 0;
 
  for (c = lits->start; !spf->mt && c < lits->top; c = eoc + 1) {
    if (s_terminate (spf) || !s_syncunits (spf)) { res = 0; break; }
    if ((lit = *(eoc = c)) >= NOTALIT) continue;
    spf->stats.unhd.steps++;
    lidx = c - lits->start;
    watched = 1;
    while (*eoc) eoc++;
    oldsize = eoc - c;

    unit = hastobesatisfied = satisfied = tautological = ndfl = 0;
    q = c;
    nonfalse = posdfl = negdfl = 0;
    for (p = c; p < eoc; p++) {
      lit = *p;
      val = s_val (spf, lit);
      if (val > 0) {
	satisfied = 1;
	q = c + 2;
	break;
      }
      if (val < 0) {
	if (p < c + 2) {
	  *q++ = lit;		// watched, so have to keep it
	  hastobesatisfied = 1;	// for assertion checking only
	}
	continue;
      }
      *q++ = lit;
      nonfalse++;
      if (dfpr[s_ulit (lit)].discovered) posdfl++;	// count pos in BIG
      if (dfpr[s_ulit (-lit)].discovered) negdfl++;	// count neg in BIG
    }
    *(eoc = q) = 0;
    ndfl = posdfl + negdfl;	// number of literals in BIG
    if (hastobesatisfied) assert (satisfied);
    if (satisfied || ndfl < 2) goto NEXT;
//FAILED: find root implying all negated literals
    if (nonfalse != negdfl) goto HTE;	// not enough complement lits in BIG
    root = s_unhroot (dfpr, -*c);
    if (s_val (spf, root)) goto HTE;
    for (p = c + 1; p < eoc && s_unhroot (dfpr, -*p) == root; p++)
      ;
    if (p < eoc) goto HTE;		// at least two roots
    // unhiding failed literal through large %s clause",type
    // unhiding that all negations are implied by root %d", root
    lca = -*c;
    for (p = c + 1; p < eoc; p++)
      lca = s_unhlca (spf, dfpr, -*p, lca);
    // unhiding failed large %s clause implied by LCA %d", type, lca
    unit = -lca;
    goto NEXT;
HTE:
    if (glue < 0 && !irronly) goto STRNEG; // skip tautology checking if redundant clauses used and
					   // we work on irredundant clauses
    if (posdfl < 2 || negdfl < 2) goto STRNEG;
    if (ndfl > szdfl) { RSZ (dfl, szdfl, ndfl,DFL*); szdfl = ndfl; }
    ndfl = 0;
    // copy all literals and their complements to 'dfl'
    for (p = c; p < eoc; p++) {
      for (sign = -1; sign <= 1; sign += 2) {
	lit = *p;
	ulit = s_ulit (sign * lit);
	if (!dfpr[ulit].discovered) continue;	// not in BIG so skip
	assert (ndfl < szdfl);
	dfl[ndfl].discovered = dfpr[ulit].discovered;
	dfl[ndfl].finished = dfpr[ulit].finished;
	dfl[ndfl].sign = sign;
	ndfl++;
      }
    }
    spf->stats.unhd.steps += 6;			// rough guess
    SORT3 (dfl, ndfl, s_cmpdfl);
    eodfl = dfl + ndfl;

    for (d = dfl; d < eodfl - 1; d++)
      if (d->sign < 0) break;			// get first negative pos
    while (d < eodfl - 1) {
      for (e = d + 1; e < eodfl && e->finished < d->finished; e++) {
	if (e->sign < 0) continue;		// get next positive pos
	// unhiding with implication %d %d tautological %s clause -d->lit4logging, e->lit4logging, type);
	ntaut++;
	spf->stats.prgss++;
	tautological = 1;
	goto NEXT;
      }
      for (d = e; d < eodfl && d->sign > 0; d++)
	;
    }
STRNEG:
    if (!s_str (spf)) goto HBR;
    if (negdfl < 2) goto STRPOS;
    if (negdfl > szdfl) { RSZ (dfl, szdfl, negdfl,DFL*); szdfl = negdfl; }
    spf->stats.unhd.steps++;
    ndfl = 0;
    // copy complement literals to 'dfl'
    for (p = c; p < eoc; p++) {
      lit = *p;
      ulit = s_ulit (-lit);			
      if (!dfpr[ulit].discovered) continue;
      dfl[ndfl].discovered = dfpr[ulit].discovered;	
      dfl[ndfl].finished = dfpr[ulit].finished;		
      dfl[ndfl].lit = lit;			
      ndfl++;
    }
    if (ndfl < 2) goto STRPOS;
    spf->stats.unhd.steps += 3;			
    SORT3 (dfl, ndfl, s_cmpdfl);
    eodfl = dfl + ndfl;
    for (d = dfl; d < eodfl - 1; d = e) {
      for (e = d + 1; e < eodfl && d->finished >= e->finished; e++) {
	lit = e->lit;
	//unhiding removal of literal %d with implication %d %d from large %s clause",lit, -d->lit, -e->lit, type);
	e->lit = 0;
	nstr++;
	spf->stats.prgss++;
	if (!watched) continue;
	if (lit != c[0] && lit != c[1]) continue;
	s_rmlwch (spf, c[0], red, lidx);
	s_rmlwch (spf, c[1], red, lidx);
	watched = 0;
      }
    }
    q = c;
    if (watched) q += 2;			
    for (p = q; p < eoc; p++) {
      lit = *p;
      ulit = s_ulit (-lit);			
      if (dfpr[ulit].discovered) continue;
      *q++ = lit;
    }
    // copy from 'dfl' unremoved BIG literals back to clause
    for (d = dfl; d < eodfl; d++) {
      lit = d->lit;
      if (!lit) continue;
      if (watched && lit == c[0]) continue;
      if (watched && lit == c[1]) continue;
      *q++ = lit;
    }
    *(eoc = q) = 0;
STRPOS:
    if (posdfl < 2) goto HBR;
    if (posdfl > szdfl) { RSZ (dfl, szdfl, posdfl,DFL*); szdfl = posdfl; }
    ndfl = 0;
    // copy original literals to 'dfl' but sort reverse wrt 'discovered'
    for (p = c; p < eoc; p++) {
      lit = *p;
      ulit = s_ulit (lit);			
      if (!dfpr[ulit].discovered) continue;
      assert (ndfl < szdfl);
      dfl[ndfl].discovered = -dfpr[ulit].discovered;	
      dfl[ndfl].finished = -dfpr[ulit].finished;		
      dfl[ndfl].lit = lit;
      ndfl++;
    }
    if (ndfl < 2) goto NEXT;
    spf->stats.unhd.steps += 3;			
    SORT3 (dfl, ndfl, s_cmpdfl);
    eodfl = dfl + ndfl;
    for (d = dfl; d < eodfl - 1; d = e) {
      for (e = d + 1; e < eodfl && d->finished >= e->finished; e++) {
	lit = e->lit;
	//unhiding removal of literal %d with implication %d %d from large %s clause,lit, e->lit, d->lit, type);
	e->lit = 0;
	nstr++;
	spf->stats.prgss++;
	if (!watched) continue;
	if (lit != c[0] && lit != c[1]) continue;
	s_rmlwch (spf, c[0], red, lidx);
	s_rmlwch (spf, c[1], red, lidx);
	watched = 0;
      }
    }
    q = c;
    if (watched) q += 2;
    for (p = q; p < eoc; p++) {
      lit = *p;
      ulit = s_ulit (lit);			
      if (dfpr[ulit].discovered) continue;
      *q++ = lit;
    }
    for (d = dfl; d < eodfl; d++) {
      lit = d->lit;
      if (!lit) continue;
      if (watched && lit == c[0]) continue;
      if (watched && lit == c[1]) continue;
      *q++ = lit;
    }
    *(eoc = q) = 0;
HBR:
    if (!spf->opts.unhdhbr.val) goto NEXT;
    if (eoc - c < 3) goto NEXT;
    root1 = root2 = lca1 = lca2 = 0;
    for (p = c; (lit = *p); p++) {
      root = s_unhroot (dfpr, -lit);
      if (!root) root = -lit;
      if (!root1) { root1 = root; continue; }
      if (root1 == root) continue;
      if (!root2) { root2 = root; continue; }
      if (root2 == root) continue;
      if (s_unhimplies2incl (dfpr, root1, -lit)) { lca1 = root1; continue; }
      if (s_unhimplies2incl (dfpr, root2, -lit)) { lca2 = root2; continue; }
      goto NEXT;			// else more than two roots ...
    }
    if (!root2) goto NEXT;
    if (root1 == -root2) goto NEXT;
    if (s_unhimplies2incl (dfpr, root1, -root2)) goto NEXT;
    //root hyper binary resolution %d %d of %s clause,-root1, -root2, type);
    if (!lca1 && !lca2) {
      for (p = c; (lit = *p); p++) {
	root = s_unhroot (dfpr, -lit);
	if (root) {
	  if (root == root1)
	    lca1 = lca1 ? s_unhlca (spf, dfpr, lca1, -lit) : -lit;
	  if (root == root2)
	    lca2 = lca2 ? s_unhlca (spf, dfpr, lca2, -lit) : -lit;
	} else {
	  assert (!lca2);
	  if (lca1) lca2 = -lit; else lca1 = -lit;
	}
      }
    } else {
      if (!lca1) lca1 = root1;
      if (!lca2) lca2 = root2;
    }
    if (lca1 == -lca2) goto NEXT;
    if (s_unhimplies2incl (dfpr, lca1, -lca2)) goto NEXT;
    //lca hyper binary resolution %d %d of %s clause",-lca1, -lca2, type);
    s_wchbin (spf, -lca1, -lca2, REDCS);
    s_wchbin (spf, -lca2, -lca1, REDCS);
NEXT:
    newsize = eoc - c;
    if (newsize <= 3 || satisfied || tautological) {
      if (watched) {
	s_rmlwch (spf, c[0], red, lidx);
	s_rmlwch (spf, c[1], red, lidx);
      }
    }
    for (p = c + oldsize; p > eoc; p--) *p = REMOVED;
    if (satisfied || tautological) {
      while (p >= c) *p-- = REMOVED;
      if (red) { c[-1] = REMOVED; }
      eoc = c + oldsize;
      continue;
    }

    if (red && newsize <= 3) { c[-1] = REMOVED; }
    if (newsize > 3 && !watched) {
      (void) s_wchlrg (spf, c[0], c[1], red, lidx);
      (void) s_wchlrg (spf, c[1], c[0], red, lidx);
    } else if (newsize == 3) {//large %s clause became ternary", type);
      s_wchtrn (spf, c[0], c[1], c[2], red);
      s_wchtrn (spf, c[1], c[0], c[2], red);
      s_wchtrn (spf, c[2], c[0], c[1], red);
      c[0] = c[1] = c[2] = *eoc = REMOVED;
    } else if (newsize == 2) {//large %s clause became binary", type);
      s_wchbin (spf, c[0], c[1], red);
      s_wchbin (spf, c[1], c[0], red);
      c[0] = c[1] = *eoc = REMOVED;
    } else if (newsize == 1) {  //large %s clause became unit", type);
      unit = c[0];		// even works if unit already set
      c[0] = *eoc = REMOVED;
      nunits++;
    }
    if (!unit) continue;
    s_unit (spf, unit);
    if (s_bcp (spf)) continue;
    spf->mt = 1;    //unhiding large clause produces empty clause
    res = 0;
  }
  if (dfl) DEL (dfl, szdfl);
  return res;
}

static void s_fixlrgwchs (SPF * spf) {
  int idx, sign, lit, blit, tag, red, lidx, fixed;
  const int * p, * eow, * c;
  int * q, * w;
  HTS * hts;
  fixed = 0;
  for (idx = 2; idx < spf->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      hts = s_hts (spf, lit);
      w = s_hts2wchs (spf, hts);
      eow = w + hts->count;
      q = w;
      for (p = w; p < eow; p++) {
	blit = *p;
	tag = blit & MASKCS;
	if (tag == BINCS) { *q++ = blit; continue; }
	lidx = *++p;
	if (tag == TRNCS) { *q++ = blit; *q++ = lidx; continue; }
	//tag == LRGCS
	red = blit & REDCS;
	c = s_idx2lits (spf, red, lidx);
	if (*c >= NOTALIT) { fixed++; continue; }
	*q++ = blit;
	*q++ = lidx;
      }
      s_shrinkhts (spf, hts, hts->count - (p - q));
    }
  }
  //if (fixed) LOG (1, "fixed %d large watches", fixed);
}

static int s_unhidelrg (SPF * spf, const DFPR * dfpr, int irronly) {
  int glue, res = 1;
  for (glue = -1; res && glue < 1; glue++)
    res = s_unhideglue (spf, dfpr, glue, irronly);
  s_fixlrgwchs (spf);
  return res;
}

static void s_rmbindup (SPF * spf) {
  int idx, sign, lit, blit, tag, red, other, round, redrem, irrem;
  int * w, * eow, * p, * q;
  HTS * hts;
  redrem = irrem = 0;
  for (idx = 2; idx < spf->nvars; idx++) {
    for (sign = -1; sign <= 1; sign += 2) {
      lit = sign * idx;
      assert (s_mtstk (&spf->seen));
      for (round = 0; round < 2; round++) {
	hts = s_hts (spf, lit);
	w = s_hts2wchs (spf, hts);
	eow = w + hts->count;
	q = w;
	for (p = w; p < eow; p++) {
	  blit = *p;
	  tag = blit & MASKCS;
	  if (tag != BINCS) *q++ = blit;
	  if (tag== LRGCS || tag == TRNCS) *q++ = *++p;
	  if (tag != BINCS) continue;
	  red = blit & REDCS;
	  other = blit >> RMSHFT;
	  if (s_signedmarked (spf, other)) {
	    if (round && !red) goto ONLYCOPY;
	    if (red) redrem++; else irrem++;
	    if (abs (lit) > abs (other)) {
	      //removing duplicated %s binary clause %d %d and 2nd watch %d,s_red2str (red), lit, other, other);
	      if (!red && spf->dense) 
		s_decocc (spf, lit), s_decocc (spf, other);
	    }
	   //removing 1st watch %d of duplicated %s binary clause %d %d,other, s_red2str (red), other, lit);
	  } else {
	    if ((!round && !red) || (round && red))
	      s_signedmarknpushseen (spf, other);
ONLYCOPY:
	    *q++ = blit;
	  }
	}
	s_shrinkhts (spf, hts, hts->count - (p - q));
      }
      s_popnunmarkstk (spf, &spf->seen);
    }
  }
}

static DFPR * s_stampall (SPF * spf, int irronly) {
  int roots, searches, noimpls, unassigned, visited;
  unsigned pos, delta, mod, ulit, first, last, count;
  int root, stamp, rootsonly, lit;
  Stk units, sccs, trds;
  DFOPF * dfopf, * q;
  DFPR * dfpr;
  Wtk work;
  Val val;
  if (spf->nvars <= 2) return 0;
  s_rmbindup (spf);
  NEW (dfpr, 2*spf->nvars);
  NEW (dfopf, 2*spf->nvars);
  CLR (work); CLR (sccs); CLR (trds); CLR (units);
  for (q = dfopf; q < dfopf + 2*spf->nvars; q++) q->pushed = -1;
  searches = roots = noimpls = unassigned = stamp = visited = 0;
  for (rootsonly = 1; rootsonly >= 0; rootsonly--) {
    count = 0;
    first = mod = 2*(spf->nvars - 2);
    pos = s_rand (spf) % mod;
    delta = s_rand (spf) % mod;
    if (!delta) delta++;
    while (s_gcd (delta, mod) > 1)
      if (++delta == mod) delta = 1;
   //unhiding %s round start %u delta %u mod %u,(rootsonly ? "roots-only": "non-root"), pos, delta, mod);
    for (;;) {
      if (s_terminate (spf)) { searches = 0; goto DONE; }
      if (!s_syncunits (spf)) { assert (spf->mt); goto DONE; }
      ulit = pos + 4;
      root = s_ilit (ulit);
      spf->stats.unhd.steps++;
      count++;
      if (s_val (spf, root)) goto CONTINUE;
      if (rootsonly) unassigned++;
      if (dfpr[s_ulit (root)].discovered) goto CONTINUE;
      if (rootsonly &&
	  !s_unhdisroot (spf, root, dfpr, irronly)) goto CONTINUE;
      if (!s_unhdhasbins (spf, dfpr, -root, irronly)) {
	if (rootsonly) noimpls++; goto CONTINUE;
      }
      if (rootsonly) roots++;
      searches++;
      stamp = s_stamp (spf, root, dfpr, dfopf,
			&work, &units, &sccs, &trds, &visited,
			stamp, irronly);
      while (!s_mtstk (&units)) {
	lit = s_popstk (&units);
	val = s_val (spf, lit);
	if (val > 0) continue;
	if (val < 0) {//unhidding stamp unit %d already false", lit);
	  spf->mt = 1;
	  goto DONE;
	}
	s_unit (spf, lit);
	if (!s_bcp (spf)) {//propagating unhidden stamp unit %d failed", lit);
	  spf->mt = 1;
	  goto DONE;
	}
      }
CONTINUE:
      last = pos;
      pos += delta;
      if (pos >= mod) pos -= mod;
      if (pos == first) { assert (count == mod); break; }
      if (mod == 1) break;
      if (first == mod) first = last;
    }
  }
DONE:
  if (!searches || spf->mt) { DEL (dfpr, 2*spf->nvars); dfpr = 0; }
  s_relwtk (spf, &work);
  s_relstk (spf, &units);
  s_relstk (spf, &sccs);
  s_relstk (spf, &trds);
  DEL (dfopf, 2*spf->nvars);
  return dfpr;
}

int s_unhide (SPF * spf) {
  int64_t limit, oldprgss = spf->stats.prgss, roundprgss = 0;
  int irronly, round, maxrounds, noprgssrounds, success;

  DFPR * dfpr = 0;
  if (spf->nvars <= 2) return 1;
  int unhd_count=1; 
  spf->unhiding = 1;
  
  irronly = unhd_count & 1;
  if (spf->level > 0) s_backtrack (spf, 0);
  limit = spf->opts.unhdmaxeff.val/10;
  maxrounds = spf->opts.unhdroundlim.val;
  if (unhd_count == 1) maxrounds *= 4;
  if (unhd_count == 2) maxrounds *= 2;
  if (limit < spf->opts.unhdmineff.val) limit = spf->opts.unhdmineff.val;
  if (limit > spf->opts.unhdmaxeff.val) limit = spf->opts.unhdmaxeff.val;
  if (spf->limits.unhd.pen < 0) limit <<= -spf->limits.unhd.pen;
  if (spf->limits.unhd.pen > 0) limit >>= spf->limits.unhd.pen;
  // unhiding with up to %lld search steps, limit
  spf->limits.unhd.steps = spf->stats.unhd.steps + limit;
  noprgssrounds = round = 0;
  while (!spf->mt) {
    if (round >= maxrounds) break;
    if (round > 0) {
      if (roundprgss == spf->stats.prgss) {
	if (noprgssrounds++ == spf->opts.unhdlnpr.val) {//too many non progress unhiding rounds");
	  break;
	}
      }
    }
    round++;
    roundprgss = spf->stats.prgss;
    s_clearMap (spf);
    if (!spf->nvars || spf->mt) break;
    dfpr = s_stampall (spf, irronly);
    if (!dfpr) break;
    if (!s_unhidefailed (spf, dfpr)) break;
    if (!s_unhidebintrn (spf, dfpr, irronly)) break;
    if (!s_unhidelrg (spf, dfpr, irronly)) break;
    if (spf->stats.unhd.steps >= limit) break;
    irronly = !irronly;
    DEL (dfpr, 2*spf->nvars);
  }
  if (dfpr) DEL (dfpr, 2*spf->nvars);

  success = (oldprgss < spf->stats.prgss);
  if (success && spf->limits.unhd.pen > MINPEN) spf->limits.unhd.pen--;
  if (!success && spf->limits.unhd.pen < MAXPEN) spf->limits.unhd.pen++;
  return !spf->mt;
}

static int s_simpaux (SPF * spf) 
{
  if (!s_distill (spf)) return 0;
  if (!s_decomp (spf)) return 0;
  if (!s_transitive_reduction (spf)) return 0;
  s_clearMap (spf);
  return 1;
}

static int simplify_abcdsolve(SPF * spf) 
{
  if (s_bcp (spf)==0) return 0;//unsat->unknown
  if (!s_simpaux (spf)) return 0;//unsat->unknown
  return abcd_solve(spf);
}

static void s_setup (SPF * spf) 
{
  spf->limits.term.steps = -1;
  spf->limits.hla = spf->opts.hlaminlim.val;

  spf->rng.w = (unsigned) spf->opts.seed.val;
  spf->rng.z = ~spf->rng.w;
  spf->rng.w <<= 1;
  spf->rng.z <<= 1;
  spf->rng.w += 1;
  spf->rng.z += 1;
  spf->rng.w *= 2019164533u, spf->rng.z *= 1000632769u;

  spf->limits.randec += spf->opts.randecint.val/2;
  spf->limits.randec += s_rand (spf) % spf->opts.randecint.val;
}

void s_initsetup (SPF * spf) 
{
  s_setup (spf);
  s_redvars (spf);
  s_fitstk (spf, &spf->irr);
  s_fitstk (spf, &spf->dsched);
}

static void s_eassign (SPF * spf, int lit) {
  Ext * ext = s_elit2ext (spf, lit);
  int pos;
  ext->val = lit_sign (lit);
  if ((pos = ext->etrailpos) >= 0) {
    assert (abs (spf->etrail.start[pos]) == abs (lit));
    spf->etrail.start[pos] = lit;
  } else {
    ext->etrailpos = s_cntstk (&spf->etrail);
    s_pushstk (spf, &spf->etrail, lit);
  }
}

static void s_eunassign (SPF * spf, int lit) {
  Ext * ext = s_elit2ext (spf, lit);
  ext->etrailpos = -1;
  ext->val = 0;
}

static void s_extend (SPF * spf) 
{
  printf("c spf extend \n");
  int * p, lit, next, satisfied, val, * start = spf->extend.start;
  
  while (!s_mtstk (&spf->etrail)) s_eunassign (spf, s_popstk (&spf->etrail));
  p = spf->extend.top;
  while (p > start) {
    satisfied = 0;
    next = 0;
    do {
      lit = next;
      next = *--p;
      if (!lit || satisfied) continue;
      val = s_ideref (spf, lit);
      if (val > 0) satisfied = 1;
    } while (next);
    if (satisfied) continue;
    s_eassign (spf, lit);
  }
}

//new idea
int midprep_solve (SPF * spf)
{ s_initsetup (spf);
  int res = simplify_abcdsolve (spf);
  if (res == 10) s_extend (spf); //SATISFIED;  res = 20  UNSATISFIED res = 0 UNKNOWN;
  return res;
}

void s_release (SPF * spf) {
  DEL (spf->avars, spf->szvars);
  DEL (spf->dvars, spf->szvars);
  DEL (spf->vals, spf->szvars);
  DEL (spf->i2e, spf->szvars);
  DEL (spf->ext, spf->szext);
  DEL (spf->df.pos.dfs, spf->df.pos.szdfs);
  DEL (spf->df.neg.dfs, spf->df.neg.szdfs);
  s_relstk (spf, &spf->wchs);
  s_relstk (spf, &spf->resolvent);
  s_relstk (spf, &spf->extend);
  s_relstk (spf, &spf->clause);
  s_relstk (spf, &spf->dsched);
  s_relstk (spf, &spf->irr);
  
  s_relstk (spf, &spf->red[0].lits);

  s_relstk (spf, &spf->trail);
  s_relstk (spf, &spf->etrail);
  s_relstk (spf, &spf->frames);
  s_relstk (spf, &spf->saved);
  s_relstk (spf, &spf->seen);
  s_relstk (spf, &spf->sortstk);
  DEL (spf->drail, spf->szdrail);
  free (spf);
}

