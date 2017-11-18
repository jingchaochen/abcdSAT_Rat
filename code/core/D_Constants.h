
#ifndef D_CONSTANTS_DEFINED 
#define D_CONSTANTS_DEFINED 

#define ABS(x) ((x)>0?(x):(-x))
#define Swap(a,b) { int t; t=a; a=b; b=t;}
#define lit2posLit(x) ((x)>0?(2 * x):(2 * (- (x)) + 1))
#define posLit2lit(x) (((x) & 1)? (- (x/2)) : (x/2))

#define CLRPTR(P) \
  do { memset ((P), 0, sizeof *(P)); } while (0)

#define QXCONST		11
#define QXBASE		25
#define CONST_EQ    10

#ifdef _MSC_VER
#define LLONG_MAX   0x7fffffff
#else
  #ifndef LLONG_MAX
     #define LLONG_MAX   0x7fffffffffffffffLL
  #endif
#endif

#define MAXCLAUSE 20000000	    // maximum possible number of clauses
#define INIT_RANDOM_SEED 91648253 //a random seed
#define SAT         10
#define UNSAT       20
#define _UNKNOWN     0
#define CONST_EQ    10
#define DELFLAG    0x7fffffff


#define CNF_CLS    0
#define XOR_CLS    1
#define DELETED    2
#define FROZE      3
#define CNF_C_B    4

#define FLAGBIT    3
#define MARKBIT    7
    
#define EQV_TYPE   0
#define ALIAS_TYPE 1

#ifdef _MSC_VER
typedef __int64  int64;
#define i64d "I64d"
#else
typedef long long int64;
#define i64d "lld"
#endif

#endif
