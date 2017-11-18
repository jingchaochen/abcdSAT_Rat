/*
Fast Blocked Clause Decomposition
*/

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/times.h>
#include <string.h>
#include <limits.h>
#include <float.h>
#include <getopt.h>
#include <signal.h>

#define ABS(x) ((x)>0?(x):(-x))

extern bool  certifiedUNSAT;  

int nVarsB,nClausesB;
int BCDfalses=1000;

int nBlocked2;      // number of the first blocked clauses
int *label,*clauseScore;
void flipClause(int *clause);
int *clauseMem;
int **Bclauses;

int **lookup;      //  clause No. where each literal occurs, lookup[lit][j]:  the j'th clause of literal lit or -lit  
int *occurrences;   // number each literal occurs
int *lookup_mem;
int sumLit;
int *value;
int retouchNum=0;
//BCD ------------------------------------------------------------------------
int *marks,*next, last, start, *touched,*stack;
int nBlocked1,nBlocked,nMoved, nRemoved, nRank;
int maxCsize;
int size30;
   
inline void addClauseIdx (int index) {
  int *clause = Bclauses[ index ];
  while (*clause) { int lit = *(clause++); lookup[ lit ][ occurrences[ lit ]++ ] = index; }
}

struct clauserank {
    int score;
    int clsNo;
} clsRank[80];

void removeBlocked_addcandidate (int index, int cut)
{   if(nClausesB <= nRemoved) return;
    int* clause = Bclauses[index];
    int & nClauses=nClausesB;
    while (*clause) {
           int j,lit  = *(clause++);
           for (j = 0; j < occurrences[ lit ]; ++j)
	      if (lookup[ lit ][ j ] == index){
	           lookup[ lit ][ j-- ] = lookup[ lit ][ --occurrences[ lit ] ];
                   break;
              }

           if(occurrences[lit]>1 && (nClauses>800000 || (nVarsB>900 && cut>0))) continue;
     
           for (j = 0; j < occurrences[ -lit ]; ++j){
              int cls = lookup[ -lit ][ j ];
	      if (touched[cls]== 0) {
                 touched[ cls ] = 1;
                 if (last == -1) start = cls;
                 else            next[ last ] = cls;
                 last = cls;
                 next[ last ] = last;
             }
          }
    }
}

void simple_bce(int cut)
{  int i,j;
   int ** & clauses=Bclauses;
   int *clause,first;
   i = start;
  while (1) {
      if (touched[ i ] == 0) goto next_i;
      clause = clauses[ i ];
      touched[ i ] = 0;
      while (*clause) { int lit = *(clause++); marks[ -lit ] = i; }

      clause = clauses[ i ];
      first = *clause;
      while (*clause) {
        int lit  = *(clause++);
        if(cut > 0){
              if (occurrences[-lit]>1) continue;
        }
        int flag = 1;
        for (j = 0; j < occurrences[ -lit ]; ++j) {
          int count  = 0;
	  int *check = clauses[ lookup[ -lit ][ j ] ];
	  while (*check) {
	    if (marks[ *(check++) ] == i) count++;
            if (count == 2) goto next_check;
          }
          flag = 0; break;
          next_check:;
        }
        if (flag) { // found a blocked clause, update data-structures
	  label   [ i ]      = 1;
          clauses  [ i ][ 0 ] = lit;
          clause   [-1 ]      = first;
          stack[ nBlocked++ ] = i;
          nRemoved++;
          if(nClausesB <= nRemoved) return;
          removeBlocked_addcandidate (i,cut);
          break;
        }
      }
    next_i:;
    if (next[ i ] == i) break;
    i = next[ i ];
  }
}

void find_k_largest(int *st, int n, int k)
{
     if(k>=n-1) return;
    int pivot=clauseScore[st[n/2]];
     int i=0, j=n-1;
     while(i<=j){
         while(i<=j && clauseScore[st[i]]>pivot) i++;
         while(i<=j && clauseScore[st[j]]<pivot) j--;
         if(i>j) break;
         int t=st[i];
         st[i]=st[j];
         st[j]=t;
         i++; j--;
     }
     if(i>=k) find_k_largest(st, i, k);
     else find_k_largest(st+i, n-i, k-i);
}

void re_touch()
{ int i;
  for (i = 0; i < nClausesB; ++i) {
         if(label[i]) continue;
         if (last == -1) start = i;
         else            next[last]= i;
         last = i;
         touched[i] = 1;
  }
  next[last] = last;
}

void LessInterfere_BCD1(int cut)
{   int i,j,bce=0;
    int theta;
    int ** & clauses=Bclauses;
    int & nClauses=nClausesB;
    theta=nClauses/100; 
   
    if(nClauses <= 200000) theta=18;
    else if(nClauses <= 800000) theta=nClauses/2300; 

    int *CNoStack = (int*) malloc(sizeof(int)*200001);
    int CNoSum=0;
    for (i = 0; i < nClauses; ++i) clauseScore[i]=0;
    
    int alpha=40*theta;
    if(alpha < 5000) alpha=5000;
    if(alpha>10000 && maxCsize >20) alpha=10000;
    int noneqSz = 1;//(maxCsize != minCsize);
    int cnt, min_occ; 
BCE:
   if(last != -1){
      if(bce==0 && nClauses <2000000) simple_bce(-1);
      else  simple_bce(cut);
   }
   last=-1;
   bce++;
   if (nClauses == nRemoved) {
           free(CNoStack);
           return;
   }
//DECOMPOSITION
    int decision = -1;

    for(i=0; i<theta && i<CNoSum; i++){
      if (label[CNoStack[i]]) continue; 
      decision=CNoStack[i];
      goto REMOVE;
    }

    if(nClauses>700000){
            cnt=20000;
            if(nClauses>2000000) cnt=2000;
      }
    else{
         cnt=nClauses/2;
         if(cnt<10000) cnt=nClauses;  
    }
    min_occ = 10000000;
    for (i = 0; i < CNoSum; ++i) clauseScore[CNoStack[i]]=0;
    CNoSum=0;
    for (i=0; i < nClauses; ++i) {
      if (label[ i ]) continue; 
      int *clause = clauses[i];
      while (*clause) {
          int lit=*clause;
          marks[ -lit ] = i;
          if (occurrences[ -lit ] < min_occ) min_occ = occurrences[ -lit ];
          clause++; 
       }
       cnt--;
       if(cnt==0) break;
     }
  
     cnt=0;
     for (i = 0; i < nClauses && (cnt<alpha || CNoSum < theta); ++i) {
        if (label[i]) continue; // clause is already in one of the sets;
        int *clause = clauses[ i ];
        while (*clause) {
          int lit = *clause;   
          int m = occurrences[-lit];
          if (m == min_occ) {
             cnt++;
             int cond=noneqSz && ((m>20 && nRemoved > nClauses/2) || nClauses<10000);
             for (j = 0; j < m; ++j) {
                 int cls = lookup[ -lit ][ j ];
                 if(cond){
                      int count = 0;
                      int *check = clauses[ cls ];
	              while (*check)  if (marks[ *(check++) ] == i) count++;
	              if (count == 1) goto addscore;
                 }
                 else{ //new idea
addscore:
                        if(clauseScore[cls]) clauseScore[cls]++;
                         else{
                             if(CNoSum<200000){
                               CNoStack[CNoSum++]=cls;
                               clauseScore[cls]=1;
                          }
                      }                           
                 }
              }
           }
           clause++;
        }
     }
//
     if(CNoSum==0) {
            if(retouchNum < 20){
                re_touch();
                cut=-2;
                retouchNum++;
                goto BCE;
            }
            for (i = 0; i < nClauses; ++i) if (label[i]==0) break;
            if(i>=nClauses) return;
            decision = i;   
      }
      else{
         find_k_largest(CNoStack,CNoSum,theta);
         decision = CNoStack[0];
      }
REMOVE:;
      if (decision >= 0) {
          label[ decision ] = 2;
          nRemoved++;  nMoved++;
          removeBlocked_addcandidate (decision,cut);
          goto BCE;
      }
}

void LessInterfere_BCD2(int cut)
{   int min_occ,i,j,bce=0;
    int & nClauses=nClausesB;
    int ** & clauses=Bclauses;
    int theta;
    if(nClauses < 6*nVarsB) theta=14;
    else theta=18; 
  
    int *CNoStack = (int*) malloc(sizeof(int)*100001);
    int CNoSum=0;
    for (i = 0; i < nClauses; ++i) clauseScore[i]=0;

BCE:
   if(last != -1) simple_bce(cut);
   last=-1;
   bce++;
   if (nClauses == nRemoved) {
         free(CNoStack);
         return;
   }
//DECOMPOSITION
    int decision = -1;
    for(i=0; i<nRank; i++){
      if (label[clsRank[i].clsNo]) continue; 
      decision=clsRank[i].clsNo;
      goto REMOVE;
    }
    nRank=0;

    min_occ = 1000000;
     for (i = 0; i < CNoSum; ++i) clauseScore[CNoStack[i]]=0;
     CNoSum=0;
  
     for (i = -nVarsB; i <= nVarsB; ++i){
       if (occurrences[i]==0) continue;
       if (occurrences[i] < min_occ) min_occ = occurrences[i];
    }   
    for (i = 0; i < nClauses; ++i) {
      if (label[ i ]) continue; 
      int lit, *clause = clauses[ i ];
      while ((lit=*clause)) {
          marks[-lit ] = i;
          clause++; 
      }
      clause=clauses[ i ];
      while (*clause) {
          int lit = *clause;   
          int m = occurrences[ -lit ];
          if (m == min_occ) {
             for (j = 0; j < m; ++j) {
                 int cls = lookup[ -lit ][ j ];
                      if(clauseScore[cls]) clauseScore[cls]++;
                      else{
                             if(CNoSum<100000){
                               CNoStack[CNoSum++]=cls;
                               clauseScore[cls]=1;
                            }
                      }             
                 int k;
                 for(k=nRank-1; k >= 0; k--){
           	      if(clauseScore[ cls ] < clsRank[k].score) break; 
                      clsRank[k+1]=clsRank[k];
                 }
                 k++;
                 clsRank[k].score=clauseScore[cls];
                 clsRank[k].clsNo=cls;
                 if(nRank < theta) nRank++;
              }
           }
           clause++;
      }
    }
    if(nRank==0){
        if(retouchNum < 20){
            re_touch();
            retouchNum++;
            goto BCE;
         }
         for (i = 0; i < nClauses; ++i) if (label[i]==0) break;
         if(i>=nClauses) return;
         decision = i;   
    }
    else  decision = clsRank[0].clsNo;
REMOVE:;
      last = -1;
      if (decision >= 0) {
          label[decision ] = 2;
          nRemoved++;  nMoved++;
          removeBlocked_addcandidate (decision,cut);
          goto BCE;
      }
}

void flipClause(int *clause)
{
    int *first=clause;
    while (*clause) {
      int var=ABS(*clause);
      if (value[var] == (*clause > 0)) return;
      clause++;
    }
    clause--;
    while (clause >= first) {
      int lit=*clause--;
      if (value[ABS(lit) ] == 2){// any
                 value[ABS(lit)] = (lit > 0);
                 return;
      }
    }
    value[ ABS(*first) ] = (*first > 0);
}

int countfalseClause()
{
  int i, nfalse=0;
  for (i = 0; i < nClausesB; i++) {
    int *clause = Bclauses[i];
    while (*clause) {
       if (value[ ABS(*clause) ] == ( *clause >0 )) goto next_clause;
         clause++; 
    }
    nfalse++;
    next_clause:;
  }
  return nfalse;
}
 
void lookup_Mem()
{
     int doubleVars = 2*nVarsB;
     occurrences = (int*) malloc(sizeof(int) * (doubleVars + 1));
     lookup = (int**) malloc(sizeof(int*) * (doubleVars + 1));

     occurrences += nVarsB;
     lookup  +=  nVarsB;
 
     int i;
     for (i = -nVarsB; i <= nVarsB; i++) occurrences[i] =0;
     int *litp = Bclauses[0];
     for (i = 0; i <  sumLit; i++) occurrences[*litp++]++;	
     occurrences[0]=0;
	
     lookup_mem   = (int*) malloc (sizeof(int) * (sumLit+doubleVars+1));
     int loc= 0;
     for (i = -nVarsB; i <= nVarsB; ++i) { 
         lookup[ i ] = lookup_mem + loc;
         loc += occurrences[ i ]+1; // end at 0
     }
}

void moveBlockable()
{    int i,j;
     int & nClauses=nClausesB;
     int ** & clauses=Bclauses;

     for (i = -nVarsB; i <= nVarsB; ++i) occurrences[ i ] = 0;
     for (i = 0; i < nClauses; ++i) if (label[ i ] == 1) addClauseIdx(i);
     int bked=0;
     for (i = 0; i < nClauses; ++i) 
          if (label[ i ] == 2) {
             int *clause = clauses[ i ];
             while (*clause) { int lit = *(clause++); marks[ -lit ] = i; }

             clause = clauses[ i ];
             int first = *clause;//bug
             while (*clause) {
                 int flag = 1;
                 int lit  = *(clause++);
                 for (j = 0; j < occurrences[ -lit ]; ++j) {
                      int count  = 0;
                      int cls = lookup[ -lit ][ j ];
                      if (label[ cls] != 1) continue;
	              int *check = clauses[ cls ];
	              while (*check) {
	                 if (marks[ *(check++) ] == i) count++;
                         if (count == 2) goto next_check_pure;
                      }
                      flag = 0;
                      break;//new idea
                      next_check_pure:;
                  }
                  if (flag) {
	             label   [ i ]       = 1;
                     clauses [ i ][ 0 ] = lit;//bug
                     clause   [-1 ]     = first;
                     stack[ nBlocked++ ] = i;
                     addClauseIdx(i);
                     bked++;
                     goto next_clause_pure;
                  }
             }
             next_clause_pure:;
       }
      // printf("c  blockable # =%d \n",bked);
}

int longcls=0;
void LessInterfere_BCD()
{    retouchNum=0;
     if(nClausesB > 1000000 || longcls > 500000) LessInterfere_BCD1(-1);
     else                   LessInterfere_BCD2(0);
}

void MixBCD(int pure_mode) 
{
  if(!certifiedUNSAT) printf("c MIX BCD var#=%d  clause#=%d \n", nVarsB, nClausesB);
 
  lookup_Mem();

  stack       = (int* ) malloc (sizeof(int ) * ( nClausesB ));
  touched     = (int* ) malloc (sizeof(int ) * ( nClausesB ));
  next        = (int* ) malloc (sizeof(int ) * ( nClausesB ));
  clauseScore = (int* ) malloc (sizeof(int ) * ( nClausesB ));
  label       = (int* ) malloc (sizeof(int ) * ( nClausesB ));
  marks       = (int* ) malloc (sizeof(int ) * (2*nVarsB+1)); 
  marks       += nVarsB;

  value=(int* ) malloc (sizeof(int ) * (nVarsB+1)); 

  int i,k;
  for (i = -nVarsB; i <= nVarsB; ++i) { 
        occurrences[ i ] = 0; 
        marks[ i ] = -1; 
  }
  maxCsize=longcls=size30=0;
  for (i = 0; i < nClausesB; ++i) {
    next    [ i ] = i + 1;
    label   [ i ] = 0;  // 1: blocked 2:moved 0:any 
    
    int *clause = Bclauses[i];
    int sz=0;
    while (*clause) {sz++; clause++;}
    if(sz>maxCsize) maxCsize=sz;
    if(sz>=28 && sz<50) size30++;
    if(sz>2) longcls++;
    addClauseIdx(i);
    touched[ i ] = 1; 
  }
  last = nClausesB - 1;
  next[last] = last;
  nMoved = nRemoved = nRank = start = nBlocked = 0;

  LessInterfere_BCD();
  nBlocked1=nBlocked;
  moveBlockable();

  double percent = (nBlocked * 100.0) / nClausesB;
  if(!certifiedUNSAT) printf("c [MixBCD] BLOCKED %i OUT OF %i CLAUSES %i%%, %i REMAIN %i%%\n",
          nBlocked, nClausesB, (int) percent, nClausesB - nBlocked, 100 - (int) percent );

  int **newclauses = (int**) malloc(sizeof(int*) * (nClausesB + 1));
  int begin=0;//new idea
  nBlocked2=begin;

//first part
  for (i = nBlocked1 - 1; i >= 0; --i) newclauses[nBlocked2++]=Bclauses[stack[i]];
//second part
  for (i = nBlocked1; i < nBlocked ; i++) newclauses[nBlocked2++]=Bclauses[stack[i]];
 
  for (i = 1;     i <= nVarsB; ++i) value[i] = 0;//any
  for (i = begin; i < nBlocked2; i++) flipClause(newclauses[i]);
 
//  printModel();
// second blocked set -------------------------------------------------------------
  for (i = -nVarsB; i <= nVarsB; ++i) { 
        occurrences[ i ] = 0; 
        marks[ i ] = -1; 
  }
 
  last = -1;
  for (i = 0; i < nClausesB; ++i) {
     if(label[ i ] == 2){
         if (last == -1) start = i;
         else            next[last]= i;
         last = i;
         label[ i ] = 0;
         addClauseIdx(i);
         touched[ i ] = 1; 
     }
     else  touched[ i ]= 0; 
  }

  if( last == -1) goto end;

  next[ last ] = last;
  nRemoved = nBlocked;
  nMoved = nRank = 0;
//
  LessInterfere_BCD();
  
  percent = (nBlocked * 100.0) / nClausesB;
  if(!certifiedUNSAT) printf("c second BLOCKED %i OUT OF %i CLAUSES %i%%, %i REMAIN %i%%\n",
          nBlocked, nClausesB, (int) percent, nClausesB - nBlocked, 100 - (int) percent );

  k = nBlocked2; 
  for (i = nBlocked - 1; i >= nBlocked2-begin; --i) newclauses[k++]=Bclauses[stack[i]];

  if(k-begin < nClausesB){
        for (i = 0; i < nClausesB; ++i) 
              if(label[ i ] == 2) newclauses[k++]=Bclauses[i];
        nClausesB = k-begin;
  } 

  if(!certifiedUNSAT) printf("c clauses#=%d \n",nClausesB);

  for (i = nBlocked2; i < nClausesB+begin; i++ ) flipClause(newclauses[i]);

//  printModel();
  BCDfalses=countfalseClause(); 
//  printf("c A false clause %d maxCsize=%d size30=%d \n", BCDfalses,maxCsize,size30);

  for (i = begin; i < nBlocked2; i++) flipClause(newclauses[i]);

  BCDfalses=countfalseClause(); 
//  printf("c B false clause %d \n", BCDfalses);
   
end:
  free(Bclauses);
  Bclauses = newclauses;

  free(stack);
  free(touched);
  free(next);
  free(clauseScore);
  free(label);
  marks -= nVarsB;
  free(marks);
  free(value);

  occurrences -= nVarsB;
  free(occurrences);

  lookup  -=  nVarsB;
  free(lookup);
  free(lookup_mem);
  return;
}
//BCD end--------------------------------------------------------------------------

