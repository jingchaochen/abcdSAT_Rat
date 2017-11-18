/*
 preprocessor for abcdSAT -- Copyright (c) 2016, Jingchao Chen
*/
#include <cassert>
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <time.h>
#include "core/D_Constants.h"
#include "core/Stack_PPS.h"

#define Swap(a,b) { int t; t=a; a=b; b=t;}

void getclausePos(PPS *pps);
int BinarySimplify(PPS *pps);
int SimplifySAT(PPS *pps);
void forwardsubsume(PPS *pps);
int XOR_varElimination(PPS *pps);
int subsumeDelete(PPS *pps, int *delvar);
int subsumptionResolution(PPS *pps, int vi, int & deletedVnum,bool & NewUnit, int delta);
void save_eqv(PPS *pps);

void check(int sol[],Stack<int> *clause);

void sortColumn(Stack<int> * & clause, int j_th, int numvar);
void sortClause(Stack<int> * & clause, int numcolumn,int & numClauses, int numvar, int delrepeat);

void release_occCls(PPS *pps) 
{
	if(pps->occCls){
	     for(int i = 1; i <= pps->numVar; i++) {
	       pps->occCls[i].release();
	       pps->occCls[-i].release();
	     }
	     pps->occCls-=pps->numVar;
	     free(pps->occCls);
             pps->occCls = 0;
	}
	if(pps->occBoth){
        for(int i = 1; i <= pps->numVar; i++) pps->occBoth[i].release();
	    free(pps->occBoth);
            pps->occBoth=0;
	}
}

void clear_occCls(PPS *pps)
{ 
    if(pps->occCls){
	for(int i = 1; i <= pps->numVar; i++) {
	       pps->occCls[i].shrink(0);
	       pps->occCls[-i].shrink(0);
	}
    }
    else{
	int Itemsize = 2*(pps->numVar + 1); 
        pps->occCls = (Stack<int> *) calloc (Itemsize, sizeof (*(pps->occCls)));
	pps->occCls+=pps->numVar;
     }
}

void free_mem(int * & ptr)
{
	if(ptr) free(ptr);
	ptr=0;
}

void free_stack(Stack<int> * & ptr)
{
    if(ptr) {
	delete ptr;
	ptr=0;
    }
}

void release_pps (PPS * pps)
{
    if(pps==0) return;
    release_occCls(pps);
    free_stack(pps->clause);
    free_stack(pps->clausePos);
//    free_stack(pps->trigonXORequ);
//    free_stack(pps->sameReplace);
    free_mem(pps->unit);
    free_mem(pps->seen);
    free_mem(pps->outEquAtom);
    if(pps->numXOR){
		pps->numVar=0;
		free(pps->Leq[0]);
		free(pps->Leq);
    }
}

void release_free_pps (PPS * & pps)
{
    if(pps==0) return;
    release_pps (pps);
    free(pps);
    pps=0;
}

void SetClausePtr(int **clauseP,int *newPointer,int cntClauses);
inline int equ_lit(int var, PPS *pps)
{   
	if(pps->outEquAtom==0) return pps->unit[var];
	int eqv=ABS(pps->outEquAtom[var]);
	if(eqv==0 || eqv==var) return pps->unit[var];
	if(pps->unit[eqv]==0) return pps->unit[var];
	if(pps->outEquAtom[var]<0) eqv=-pps->unit[eqv];
	else eqv=pps->unit[eqv];
	if(eqv<0) return -var;
	return var;
}

void extend_solution(PPS *pps) 
{
  int *start = pps->extend.begin();
  int *p=pps->extend.end();
  int satisfied,lit,next;

  p=pps->extend.end();
  while (p > start) {
          p--;
	  lit=*p;
	  if(lit!=0){ // bug x=y   x=0, y=0 2011/12/16
		  int vv=ABS(lit); 
		  if(pps->unit[vv]==0) pps->unit[vv]=-lit;
	  }
  }
  p=pps->extend.end();
  while (p > start) {
    satisfied = 0;
    next = 0;
    do {
      lit = next;
      next = *--p;
      if (!lit || satisfied) continue;
      int var=ABS(lit);
      pps->unit[var]=equ_lit(var, pps);
	  if (pps->unit[var]==lit) satisfied = 1;
    } while (next);
    if (satisfied) continue;
	pps->unit[ABS(lit)]=lit;
  }
}

void setDoubleDataIndex(PPS *pps,bool add_delcls)
{
	 clear_occCls(pps);
         int *pcls=pps->clause->begin();
	 int *pend=pps->clause->end();
  	 int clsNum=0;
	 pps->numXOR=0;
	 while(pcls < pend){
         int len=*pcls;
		 int mark=len & MARKBIT;
		 len=len>>FLAGBIT;
		 int *lits=pcls+1;
                 pcls+=len;
	         if(!add_delcls && (mark==DELETED || mark==FROZE)) continue; //remove;
		 if(mark==XOR_CLS) pps->numXOR++;
		 else clsNum++;
		 int pos=(pcls-pps->clause->begin())-len;
		 for (; lits<pcls; lits++) {
			 pps->occCls[*lits].push(pos);
			 if(mark==XOR_CLS) pps->occCls[-(*lits)].push(pos);
		 }
	 }
	 pps->numClause=clsNum;
}

void set_CNF_occ(PPS *pps)
{
     clear_occCls(pps);
     int *pcls=pps->clause->begin();
     int *pend=pps->clause->end();
     pps->numClause=0;
     while(pcls < pend){
          int len=*pcls;
	  int mark=len & MARKBIT;
	  len=len>>FLAGBIT;
	  int *lits=pcls+1;
          pcls+=len;
	  if(mark!=CNF_CLS) continue;
	  pps->numClause++;
	  int pos=(pcls-pps->clause->begin())-len;
	 for (; lits<pcls; lits++) pps->occCls[*lits].push(pos);
     }
}

void setSingleDataIndex(PPS *pps)
{
    release_occCls(pps); 
    pps->occBoth = (Stack<int> *) calloc (pps->numVar + 1, sizeof (*(pps->occBoth)));
    int *pcls=pps->clause->begin();
	int *pend=pps->clause->end();
  	int clsNum=0;
	while(pcls < pend){
         int len=*pcls;
		 int mark=len & MARKBIT;
		 len=len>>FLAGBIT;
		 int *lits=pcls+1;
                 pcls+=len;
	         if(mark==DELETED) continue; //remove;
		 clsNum++;
		 int pos=(pcls-pps->clause->begin())-len;
		 for (; lits<pcls; lits++) pps->occBoth[ABS(*lits)].push(pos);
	}
	pps->numClause=clsNum;
}

int getBinClsNum(PPS *pps,int * & binNum)
{
	int *pcls=pps->clause->begin();
	int *pend=pps->clause->end();
	binNum=(int *)calloc(2*pps->numVar+2,sizeof(int));
  	binNum+=pps->numVar;
        int binNo=0;
	while(pcls < pend){
            int len=*pcls;
            len=len>>FLAGBIT;
	    int *lits=pcls+1;
            pcls+=len;
            if(len!=3) continue;
		    binNum[lits[0]]++;
		    binNum[lits[1]]++;
	            binNo++;
	}
    return binNo;
}

int checkUnitClause(PPS *pps,int cpos,int & change)
{
    int lit,size,var,k,rc;
    int aCNF[20];
    Stack<int> *clsSAT=pps->clause;
    int *seen=pps->seen;
    int *unit=pps->unit;

    size=0; change=0;
    int len=(*clsSAT)[cpos];
    len=len>>FLAGBIT;
    int *lits=&(*clsSAT)[cpos];
    int *nextcls=lits+len;
    for(lits++; lits<nextcls; lits++){
	   lit=*lits; var=ABS(lit);
           if(unit[var]!=0) {
	        if(unit[var]!=lit) continue;
  		rc=SAT; 
                goto ret;
	   }
   	   if(seen[var]==0) {
        	if(size>=10) continue;
	     	aCNF[size++]=lit;
		seen[var]=lit;
	   }
	   else{
		 if(seen[var]==-lit){
  		        rc=SAT; goto ret;
		 }
	   }
	}
	rc=_UNKNOWN;
ret:	
	for(k=0; k<size; k++) seen[ABS(aCNF[k])]=0;
	if(rc==SAT) return SAT;
//unit cluase found
    if(size==1){
         unit[ABS(aCNF[0])]=aCNF[0];
	 change=1;
     }
     if(size==0) return UNSAT;
     return SAT;
}


int breakEquivalentLoop(PPS *pps)
{    int i,cur,sign,next1;
     int numatom=pps->numVar;
     int *outEquAtom=pps->outEquAtom;
     int *unit=pps->unit;

     for(i=1; i<=numatom; i++) {
		if(ABS(outEquAtom[i])<=i) continue;
		cur=i;
		sign=1;
		do{ 
			next1=outEquAtom[cur];
			outEquAtom[cur]=sign*i;
			if(unit[cur]!=0){
				int lit=unit[i];
				unit[i]=(outEquAtom[cur]<0 && unit[cur]<0) || (outEquAtom[cur]>0 && unit[cur]>0)? i:-i;
				if(lit==-unit[i]) return UNSAT;
			}
			if(next1<0) {cur=-next1; sign=-sign;}
			else cur=next1;
		} while(cur!=outEquAtom[cur]);
	}

	for(i=1; i<=numatom; i++) {
		next1=ABS(outEquAtom[i]);
		if(outEquAtom[next1]==next1 || next1==0) continue;
		sign=outEquAtom[i]<0 ? -1: 1;
		outEquAtom[i]=sign*outEquAtom[next1];
	}
	return SAT;
}

//delete some cluases
/*
int deletegarbage(PPS *pps, Stack<int>* & clauseOut, int & numOut,int limLen);
int deletegarbage(PPS *pps, int & change)
{
  int rc=deletegarbage(pps, newNum,0x7fffffff);
  if(rc==UNSAT) return rc;
  change=(newNum!=pps->numClause);
  return rc;
}
*/
//outEquAtom=EquLink
int deletegarbage(PPS *pps)
{
	int lit,var,newsz;
	int j,k,True;
    int *EquLink=pps->outEquAtom;

	if(pps->seen==0) pps->seen=(int *)calloc(pps->numVar+1,sizeof(int));
    int *seen=pps->seen;
    int *unit=pps->unit;
loop:		
 	int numOut=0;
	Stack<int> *clauseOut=new Stack<int>; 
    Stack<int> *clauseIn=pps->clause;
	int *pcls=clauseIn->begin();
	int *pend=clauseIn->end();
	bool unitchange=false; //bug 2011/9/25
	while(pcls < pend){ //map ext var to internal var
         int len=*pcls;
		 int mark= len & MARKBIT;
		 len=len>>FLAGBIT;
		 int *lits=pcls;
         pcls+=len;
         if(mark==DELETED) continue;
		 True=0;
		 int initp=clauseOut->nowpos();
		 clauseOut->push(0);
 		 for(k=1; k<len; k++){
			lit=lits[k];
    		if(EquLink!=0){
		    	int lit1=EquLink[ABS(lit)];
			    if(lit1!=0)	lit=(lit<0)?-lit1:lit1;
			}
			var=ABS(lit);
			if(unit[var]){
				 if(unit[var]!=lit) continue;
				 True++;
				 if(mark!=XOR_CLS) break;
			}

			if(seen[var]==0) {
				seen[var]=lit; 
				clauseOut->push(lit);
			}
			else {
				if(seen[var]==-lit) {True++; if(mark!=XOR_CLS) break;}
				if(mark==XOR_CLS) {
					seen[var]=0;
					int newp=clauseOut->nowpos();
					int m=initp+1;
			    	for(j=initp+1; j<newp; j++) {
						int lit2=(*clauseOut)[j]; 
						if(ABS(lit2)==var) continue;
						(*clauseOut)[m++]=lit2;
					}
				    clauseOut->shrink(m);
				}
			}
			
		 }
		
		 int newp=clauseOut->nowpos();
		 for(j=initp+1; j<newp; j++) {lit=(*clauseOut)[j]; seen[ABS(lit)]=0;}
		 newsz=newp-initp;
       	 if(mark==XOR_CLS) {
			 True=True%2;
			 if(newsz>1 && True){
				 lit=(*clauseOut)[initp+1];
				 (*clauseOut)[initp+1]=-lit;
				 True=0;
			 }
		 }
		 if(True) {
		 	 clauseOut->shrink(initp);
		     continue;
		 }
		 if(newsz==1){
			printf("c proprocessing binary CNF conflict \n");
			delete clauseOut;
			return UNSAT;
		}
		
		if(newsz==2){
			lit=(*clauseOut)[initp+1];
			unit[ABS(lit)]=lit;
			clauseOut->shrink(initp);
			unitchange=true;
			continue;
		}
		(*clauseOut)[initp]= (newsz << FLAGBIT) | mark;
		numOut++;
	 }
     delete pps->clause;
     pps->clause=clauseOut;
     pps->numClause=numOut;
	 if(unitchange) goto loop;
	 return _UNKNOWN;
}
//delete some cluases
void deleteClause(PPS *pps)
{
	int k;
	Stack<int> *NewClause=new Stack<int>; 
 	int newNum=0;
	int *pcls=pps->clause->begin();
	int *pend=pps->clause->end();
	while(pcls < pend){
               int len=*pcls;
		int mark= len & MARKBIT;
		len=len>>FLAGBIT;
		int *lits=pcls;
                pcls+=len;
		if(mark==DELETED) continue;
               	for(k=0; k<len; k++) NewClause->push(lits[k]);
		newNum++;
	 }
         delete pps->clause;
	 pps->clause=NewClause;
 	 pps->numClause=newNum;
}

void mergeTwoEqu(PPS *pps, int lit1, int lit2)
{
    int v1,v2;
	v1=ABS(lit1); v2=ABS(lit2);
	if(v1>v2){
		Swap(v1,v2);
        Swap(lit1,lit2);
  	}
   	if(lit2<0) lit1=-lit1;
   	pps->outEquAtom[v1]=0;
	pps->outEquAtom[v2]=lit1;
}

inline int find(PPS *pps,int vv, int lit)
{
	int lit1=pps->outEquAtom[vv];
    while(lit1){
    	lit=(lit<0)?-lit1:lit1;
	    vv=ABS(lit);
		lit1=pps->outEquAtom[vv];
		if(ABS(lit1)==vv){
			pps->outEquAtom[vv]=0;
			break;
		}
	}
	return lit;
}

inline int find_lit(PPS *pps,int lit)
{
     return find(pps,lit/2,  posLit2lit(lit));
}

void mergeAllEqu(PPS *pps)
{
	for(int i=pps->numVar; i>=2; i--){
         if(pps->outEquAtom[i]==0) continue;
		 int other=find(pps, i,i);
    	 mergeTwoEqu(pps, other, i);
    }
}

int mergeTwoEunit(PPS *pps,int lit1, int lit2)
{
    int v1,v2;
	v1=ABS(lit1); v2=ABS(lit2);
	if(v1>v2){
		Swap(v1,v2);
        Swap(lit1,lit2);
  	}
   	if(lit2<0) lit1=-lit1;
	int *unit=pps->unit;
    if(unit[v2]){// bug 2010.9.19
         if(unit[v2]<0) lit1=-lit1;
		 if(unit[v1]==-lit1) return UNSAT;
         unit[v1]=lit1;
		 return SAT;
	}
	pps->outEquAtom[v1]=0;
	pps->outEquAtom[v2]=lit1;
	return SAT;
}

inline int find1(PPS *pps,int lit)
{   int vv=ABS(lit);
    int *outEquAtom=pps->outEquAtom;
	int lit1=outEquAtom[vv];
    while(lit1){
    	lit=(lit<0)?-lit1:lit1;
	    int vv=ABS(lit);
	    lit1=outEquAtom[vv];
		if(ABS(lit1)==vv){
			outEquAtom[vv]=0;
			break;
		}
	}
	return lit;
}

//binary equivalent resoning
int BinaryEquReason(PPS *pps)
{   
    sortClause(pps->clause,4,pps->numClause,pps->numVar,0); //??no duplicate
  	int *unit=pps->unit;
	int *pcls=pps->clause->begin();
	int *pend=pps->clause->end();
	while(pcls < pend){
            int len1=*pcls;
		    len1=len1>>FLAGBIT;
		    int *lits1=pcls+1;
            pcls+=len1;
            if(pcls >= pend) break;
			int len2=*pcls;
		    len2=len2>>FLAGBIT;
		    int *lits2=pcls+1;
            if(len1!=3 || len2!=3) continue; //bug 5/23/2011
			int lit1=*lits1; 
			int lit2=lits1[1];
		   	if(-lit1==*lits2){
			    if(-lit2==lits2[1]){    //lit1==-lit2;
			// printf("<CNF %d = %d> ", lit1,-lit2);
			   	    int a=find1(pps,lit1);
				    int b=find1(pps,(-lit2));
			        if(a == b) continue;
	                if(a == -b) return UNSAT;
				     int rc=mergeTwoEunit(pps,a,b);
				     if(rc==UNSAT) return UNSAT;
				}
			    if(lit2==lits2[1]){    //A v B  AND -A V B ==> B
			  // printf("\n +-A=%d B=%d ==> B ",lit1,lit2);
			    	int vv=ABS(lit2);
			    	if(unit[vv]==-lit2)	return UNSAT;
				    unit[vv]=lit2;
				}
			}
            else{
			   if(lit1==*lits2){
			      if(-lit2==lits2[1]){    //A v B  AND A V -B ==> A
			    //  printf("\n A=%d +-B=%d ==> A ",lit1,lit2); printf("\n A v B  & -A V B ==> B ");
				     int vv=ABS(lit1);
				     if(unit[vv]==-lit1) return UNSAT;
				     unit[ABS(lit1)]=lit1;
				  }
			   }
			}
    }
    mergeAllEqu(pps);
//delete some cluases
    int rc=deletegarbage(pps);
	return rc;
}

int BinarySimplify(PPS *pps)
{
	 int i,sum;
         int loop,change,rc;
    
	 if(pps->seen==0) pps->seen=(int *)calloc(pps->numVar+1,sizeof(int));
  	 if(pps->outEquAtom==0) pps->outEquAtom=(int *)calloc(pps->numVar+1,sizeof(int));
	
	 sum=0;
	 do{
	      loop=0;
              int *pcls=pps->clause->begin();
	      int *pend=pps->clause->end();
  	      while(pcls < pend){
                    int len=*pcls;
		    int mark=len & MARKBIT;
		    len=len>>FLAGBIT;
		    pcls+=len;
	            if(mark==DELETED) continue; //remove;
		    int pos=(pcls-pps->clause->begin())-len;
	            rc=checkUnitClause(pps,pos,change);
		    if(rc==UNSAT){
                        //  printf("c  exit unsat! \n");
                          return UNSAT;
                     }
		    if(change) loop=1;
		 }
		 sum++;
       } while (loop==1);
  
       sum=0;
       int oldnum;
       do{
		 sum++;
		 oldnum=pps->numClause;
		 if(BinaryEquReason(pps)==UNSAT) return UNSAT;
                // printf("c BinaryEquReason loop #=%d numClauses=%d \n", sum,pps->numClause);
		 if((pps->numClause>500000 && sum>10) || sum>40) break;
	 } while(oldnum!=pps->numClause);

	 for(i=1; i<=pps->numVar; i++) { //SAT_dat.k50
		 if(pps->unit[i]==0) continue;
		 if(pps->outEquAtom[i]==0) continue;
		 int other=find1(pps,i);
		 if(other==i) continue;	
		 if(pps->unit[i]<0) other=-other;
		 int vv=ABS(other);
                 if(pps->unit[vv]==-other) {
		//	 printf("c bin equ i=%d pps->unit[%d]=%d UNSAT\n",i,vv,pps->unit[vv]);
			 return UNSAT;
		 }
		 pps->unit[vv]=other;
	 }

	 save_eqv(pps); 
	 return _UNKNOWN;     	 
}

int SimplifySAT(PPS *pps)
{
     int rc;
     rc=BinarySimplify(pps);
//     printf("c BinarySimplify numclause=%d rc=%d \n",pps->numClause,rc);
     if(rc==UNSAT) return UNSAT;

     if(pps->numClause<10000000) forwardsubsume(pps);
     setDoubleDataIndex(pps,false);
     if(pps->numClause<6000000 || pps->numVar<100000){
	   rc=XOR_varElimination(pps);
	   if(rc==UNSAT) return UNSAT;
     
	   rc=subsumeDelete(pps, (int *)0);
	   if(rc==UNSAT) return UNSAT;
      }
      if(pps->numClause<5000000){
	     int delrepeat=1;
             sortClause(pps->clause,4,pps->numClause,pps->numVar,delrepeat);
      }
  //    printf("\nc Delete repeated  numClauses=%d \n",pps->numClause);
      return rc;
}

extern int CNF_space;
//extend space for subsumption Resolution by clause distribution
int subsumeDelete(PPS *pps, int *bigNum)
{    
     int *unit=pps->unit;
     bool NewUnit;
     int deletedVnum=0;
     for(int i=0; i<10 || NewUnit; i++){
		  NewUnit=false;
		  int preNum=deletedVnum;
	      Stack<int> *occCls=pps->occCls; 
		  for(int vi=1; vi<=pps->numVar; vi++){
			   if(unit[vi]) continue;//unit[vi]!=vi+1
		       int numOccur=occCls[vi]+occCls[-vi]; 
		       if(numOccur<=0) continue;
			   else{//12
		             if(numOccur<12 && occCls[vi]>0 && occCls[-vi]>0) {
	                   bool NewUnit1;
					   int rc=subsumptionResolution(pps, vi, deletedVnum,NewUnit1,0);
			           if(rc==UNSAT) return rc;
					   if(NewUnit1) NewUnit=NewUnit1; 
				   }
			   }
		  }
		  if(preNum!=deletedVnum || NewUnit) {
		   	  int rc=deletegarbage(pps);
			  if(rc==UNSAT) return rc;
		 }
		 setDoubleDataIndex(pps,false);
		 if(preNum==deletedVnum) break;
	 }
	// printf("c subsumeDelete deletedVnum=%d \n",deletedVnum);
	 return _UNKNOWN;
}

void SortLiteral(Stack<int> * clause)
{    
	 int *pcls=clause->begin();
	 int *pend=clause->end();
	 while(pcls < pend){
            int len=*pcls;
	    len=len>>FLAGBIT;
	    int *lit0=pcls+1;
	    int *lits=pcls+2;
            pcls+=len;
            for(; lits<pcls; lits++) {
		int *pw;
		for(pw=lits; pw>lit0 && ABS(*(pw-1)) > ABS(*pw); pw--){
		    Swap(*(pw-1),*pw);
		}
	    }
         }
}

void sortClause(Stack<int> * & clause, int numcolumn,int & numClauses, int numvar, int delrepeat)
{  
	// -x -> 2(-x)+1, x -> 2x
	if(delrepeat){
		 int *pcls=clause->begin();
	     int *pend=clause->end();
	     while(pcls < pend){
            int len=*pcls;
		    len=len>>FLAGBIT;
		    int *lits=pcls+1;
            pcls+=len;
            for (; lits<pcls; lits++) *lits=lit2posLit(*lits);
		 }
	}
//sort literals in each row    
   	SortLiteral(clause);
//Sort 4 columns
    if(numcolumn>2){
		sortColumn(clause,3,numvar);
		sortColumn(clause,2,numvar);
  	}
	sortColumn(clause,1,numvar);
	sortColumn(clause,0,numvar);
//remove repeated clauses
	if(delrepeat){
	     int *pcls1=clause->begin();
	     int *pend=clause->end();
	     int *pcls2;
	     for(; pcls1 < pend; pcls1=pcls2){
                    int len1=*pcls1;
		    int mark=len1 & MARKBIT;
		    len1=len1>>FLAGBIT;
		    pcls2=pcls1+len1;
                    if(mark!=CNF_CLS) continue;
		    if(pcls2>= pend) break;
			int len2=*pcls2;
		    mark=len2 & MARKBIT;
            if(mark!=CNF_CLS) continue;
		    len2=len2>>FLAGBIT;
		    if(len1!=len2) continue;
            int j;
			for (j=1; j<len1; j++){
				if(pcls1[j]!=pcls2[j]) break;
			}
			if(j>=len1){
				*pcls1=(len1<<FLAGBIT) | DELETED; ////repeated clauses
			}
		 }
// 2x -> x,   2x+1 ->-x
         Stack<int> * newclause=new Stack<int>;
   	     int *pcls=clause->begin();
	     numClauses=0;
		 while(pcls < pend){
            int len=*pcls;
		    int mark=len & MARKBIT;
            len=len>>FLAGBIT;
		    int *lits=pcls;
            pcls+=len;
            if(mark==DELETED) continue;
			numClauses++;
			newclause->push(*lits);
			for (lits++; lits<pcls; lits++) {
				int lit=posLit2lit(*lits);
	         	newclause->push(lit);
			}
		 }
		 delete clause;
		 clause=newclause;
	}
}


void sortClause2(Stack<int> * & clause, int numvar)
{  
	sortColumn(clause,3,numvar);
    sortColumn(clause,2,numvar);
	sortColumn(clause,1,numvar);
	sortColumn(clause,0,numvar);
}

void SortLiteral2(Stack<int> * & clause, int changeNo)
{  
	 int *pcls=clause->begin();
	 int *pend=clause->end();
	 while(pcls < pend){
            int len=*pcls;
		    len=len>>FLAGBIT;
		    int *lits=pcls+1;
            pcls+=len;
        	if(len<3) continue; //size=1
			if(len>3){
			    if(changeNo==1) {Swap(lits[1],lits[2]);}
        	    if(changeNo==2) {Swap(lits[0],lits[2]);}
			}
	        if(lits[0]>lits[1]) Swap(lits[0],lits[1]);
	 }
}

void clslit2poslit(Stack<int> * clauseCNF)
{
	int *pcls=clauseCNF->begin();
	int *pend=clauseCNF->end();
	while(pcls < pend){
         int len=*pcls;
		 len=len>>FLAGBIT;
		 int *lits=pcls+1;
         pcls+=len;
         for (; lits<pcls; lits++) *lits=lit2posLit(*lits);
	}
}

void poslit2clslit(Stack<int> * clauseCNF)
{
	int *pcls=clauseCNF->begin();
	int *pend=clauseCNF->end();
	while(pcls < pend){
        int len=*pcls;
		len=len>>FLAGBIT;
		int *lits=pcls+1;
        pcls+=len;
        for (; lits<pcls; lits++) *lits=posLit2lit(*lits);
	}
}
/*
void printclause(Stack<int> *clsSAT, int pos)
{
  int len=(*clsSAT)[pos];
	  len=len>>FLAGBIT;
	  printf("\n");
      for(int i=1; i<len; i++) printf("%d ",(*clsSAT)[pos+i]);
}
*/

void forwardsubsume(PPS *pps)
{
	int i,j,k;
	bool deleteCli;
    if(pps->numClause<10) return;
	// -x -> 2(-x)+1, x -> 2x
   
    Stack<int> * clauseCNF=pps->clause;
    clslit2poslit(clauseCNF);
	
	int *Seen =(int *) calloc (2*pps->numVar+2, sizeof (int));
	for(i=0; i<3; i++){
       deleteCli=false;
//sort literals in each row    
	   SortLiteral2(clauseCNF,i);
	   sortClause2(clauseCNF,pps->numVar);
       pps->clause=clauseCNF;
	   getclausePos(pps);
       Stack<int> * clausePos=pps->clausePos;
      
	   for(j =1; j < pps->numClause; j++) {
		   int h=j-1;
		   int hPos= (*clausePos)[h];
           int hLen=(*clauseCNF)[hPos];
           if((hLen & MARKBIT)==DELETED) continue;
		   hLen=hLen>>FLAGBIT;
		   int size=hLen-1;
		   if(size!=2) {//backward subsume
			   if(size>=8) continue;
			   int lit=(*clauseCNF)[hPos+1];
			   int m;
		       for(m=1; m<size; m++) Seen[(*clauseCNF)[hPos+1+m]]=1;
			   for(int k=h-1; k>=0 && k>j-30; k--){
			        int kPos= (*clausePos)[k];
                    int lenK=(*clauseCNF)[kPos];
                    if((lenK & MARKBIT)==DELETED) continue;
		            lenK=lenK>>FLAGBIT;
		  	        int size2=lenK-1;
				    if(size2>=size) continue;
			    	if(lit!=(*clauseCNF)[kPos+1]) break;
			   		for(m=1; m<size2; m++){
						 int lit2=(*clauseCNF)[kPos+1+m];
						 if(Seen[lit2]==0) break;
					}
		            if(m>=size2){
						 (*clauseCNF)[hPos]=(hLen<<FLAGBIT) | DELETED; // //delete
						// Clit1[h][0]=0; // //delete
						 deleteCli=true;
						 break;
					 }
			   }
		       for(m=1; m<size; m++) Seen[(*clauseCNF)[hPos+1+m]]=0;
        	   continue;
		   }
		  
		   int jPos= (*clausePos)[j];
           int jLen=(*clauseCNF)[jPos];
           if((jLen & MARKBIT)==DELETED) continue;
		   jLen=jLen>>FLAGBIT;
		   if(jLen<3) continue;
		  
		   if((*clauseCNF)[jPos+1]==(*clauseCNF)[hPos+1] && (*clauseCNF)[jPos+2]==(*clauseCNF)[hPos+2]) {
               (*clauseCNF)[jPos]=(jLen<<FLAGBIT) | DELETED; // //delete
			   deleteCli=true;
			   for(k=j+1; k<pps->numClause && k<j+5; k++){
		             int kPos= (*clausePos)[k];
                     int kLen=(*clauseCNF)[kPos];
                     if((kLen & MARKBIT)==DELETED) continue;
		             kLen=kLen>>FLAGBIT;
		             if(kLen<3) continue;
		             if((*clauseCNF)[kPos+1]==(*clauseCNF)[hPos+1] && (*clauseCNF)[kPos+2]==(*clauseCNF)[hPos+2]) {
			              (*clauseCNF)[kPos]=(kLen<<FLAGBIT) | DELETED; // //delete
				   }
			   }
		   }
	   }
	   if(deleteCli) {
		   deleteClause(pps);
		   clauseCNF=pps->clause;
	   }
	}
    free(Seen);
	poslit2clslit(clauseCNF);
	pps->clause=clauseCNF;
}

// x=a^b <=> {x, -a,-b}{-x, a}{-x,b}
void ANDgate(int vi, int andclsPos[4],Stack<int> *occCls,Stack<int> *clsSAT)
{   int ab;
    int i,j,k;
	int occ=occCls[vi];
   	ab=0;
    for(i=0; i<occ; i++){ // x==a^b
   	    int posA=occCls[vi][i];
    	andclsPos[0]=posA;
	    int len=(*clsSAT)[posA];
		len=len>>FLAGBIT;
		if(len!=4) continue; //3
		k=1;
        int *clsp=&(*clsSAT)[posA];
		int *lits=clsp+1;
        clsp+=len;
		for (; lits<clsp; lits++){
			  if(*lits==vi) continue;
			  int vb=-(*lits);
	          int occb=occCls[-vi];
	          for(j=0; j<occb; j++){
		          int posB=occCls[-vi][j];
                  int lenB=(*clsSAT)[posB];
		          if( (lenB & MARKBIT)==DELETED) continue;// bug 2011/9/24
			      lenB=lenB>>FLAGBIT;
		          if(lenB!=3) continue; //2
		   	      if((*clsSAT)[posB+1]==vb || (*clsSAT)[posB+2]==vb) {
					   if(ab!=vb) {
						   ab=vb; andclsPos[k++]=posB; //bug 2011/9/24
						   if(k==3) {
							  // printf("c Acls=%d   Bcls=%d Bcls=%d \n",andclsPos[0],andclsPos[1],andclsPos[2]);// Niklas E.en and Armin Biere
			                  // for(int m=0; m<3; m++) printclause(clsSAT, andclsPos[m]);
							   return;
						   }
					   }
				  }
			  }
		}
	}
	andclsPos[0]=-1; //??? bug
}

//flat200-100
int subsumptionResolution(PPS *pps, int vi, int & deletedVnum,bool & NewUnit, int delta)
{
	int i,j,m,pos,neg,k,k1,pi;
    int andclsPos[5];
    int posA,posB,nextbegin;
    
	int *seen=pps->seen;
	Stack<int> * clsSAT=pps->clause;
	pos=pps->occCls[vi];
    neg=pps->occCls[-vi];
	if(delta<=1){
		if(pos+neg<8) delta=0;
	    else delta=1;
    }
	else delta=-delta;
  
	NewUnit=false;
//	printf("\n\ntry del vi=%d u[%d]=%d ",vi, vi,unit[ABS(vi)]);
    if(pps->unit[ABS(vi)]) return _UNKNOWN;
 
//	if(vi==63211) return _UNKNOWN;
		 
	andclsPos[0]=-1;
	if(pos+neg<8){
		ANDgate(vi,andclsPos,pps->occCls,clsSAT);
		if(andclsPos[0]==-1) {
			vi=-vi;
			ANDgate(vi,andclsPos,pps->occCls,clsSAT);
			pos=pps->occCls[vi];
	        neg=pps->occCls[-vi];
		}
	}

	int origsize=clsSAT->nowpos();
	int Newsize=origsize;
	int clsB_size,lenB;
	int newCNFs=0,end=0;
    int *unit=pps->unit;

	for(i=0; i<pos; i++){
		  posA=pps->occCls[vi][i];
		  int len=(*clsSAT)[posA];
		  if( (len & MARKBIT)==DELETED) continue;
		  len=len>>FLAGBIT;
		  int clsbegin=clsSAT->nowpos();
		  clsSAT->push(0);
		 // printf("\nA: ");
		  for (pi=posA+1; pi<posA+len; pi++){
			  int alit=(*clsSAT)[pi];
			  int vv=ABS(alit);
		//	  printf("%d ", alit);
			  if(unit[vv]){
				  if(unit[vv]==alit) goto clearSeen;
			  }
			  else if(alit!=vi) {clsSAT->push(alit); seen[vv]=alit;}
		  }
		 // printf("\n");
		  k1=clsSAT->nowpos()-clsbegin-1;
		  //if(k1<=0) goto clearSeen; //bug 2011/9/24    
		  for(j=0; j<neg; j++){ // G(x)={x,-a -b} G'={-x,a) V {-x,b},  S= G(x) V G(-x) V R(x) V R(-x) => S"= G(x)*R(-x) V G(-x)*R(x)
   	           posB=pps->occCls[-vi][j];
			   if(andclsPos[0]>=0){// S''=R*G' v R'*G
				   //if(vi==63211) printf("c and-gate subsumption \n");// Niklas E.en and Armin Biere
				   if(andclsPos[0]!=posA) { // R(x)*G(-x)
					   if(andclsPos[1]!=posB && andclsPos[2]!=posB) {
						  // printf(" R*R' ");
						   continue;
					   }
				   }
				   else{ // G(x)*R(-x)
					   if(andclsPos[1]==posB || andclsPos[2]==posB) {
						   //printf(" G*G' ");
						   continue;
					   }
				   }
			   }
		       lenB=(*clsSAT)[posB];
       		   if( (lenB & MARKBIT)==DELETED) continue;
			   lenB=lenB>>FLAGBIT;
	           clsB_size=clsSAT->nowpos();
			 //  printf(" clsB_size=%d ",clsB_size);
			   //printf("\nB: ");
			   for (pi=posB+1; pi<posB+lenB; pi++){
			       int blit=(*clsSAT)[pi];
		  	     //  printf("u[%d]=%d ", blit,unit[ABS(blit)]);
			 	   if(blit==-vi) continue;
                   int vv=ABS(blit);
			       if(unit[vv]){
					   if(unit[vv]==blit) goto nextj;
					   continue;
				   }
				   if(seen[vv]==-blit) goto nextj;
				   if(seen[vv]==0) clsSAT->push(blit);
			   }
		       nextbegin=clsSAT->nowpos();
		       k=nextbegin-clsbegin;
			   if(k==1) {// bug 2011/9/24
	        	           clsSAT->shrink(origsize);
				   return UNSAT;
			   }
			   if(k==2){
				   NewUnit=true;
				   int lit=(*clsSAT)[clsbegin+1];
				   unit[ABS(lit)]=lit;
				 //  printf(" unit[%d]=%d ",ABS(lit),unit[ABS(lit)]);
				   end=1; 
				   goto clearSeen;
			   }
		       newCNFs++;
			   if(newCNFs>pos+neg-delta){ end=1; goto clearSeen; }
	           Newsize=nextbegin;
		       (*clsSAT)[clsbegin]=(k<<FLAGBIT) | CNF_CLS;//len
			   clsSAT->push(0);
			   for(m=1; m<=k1; m++) {
				   int clit=(*clsSAT)[clsbegin+m];
				   clsSAT->push(clit); // move A-type CNF to next
			   }
			   clsbegin=nextbegin;
			   continue;
nextj:          
			   clsSAT->shrink(clsB_size);
			}
clearSeen:
		 clsSAT->shrink(Newsize);
         for (pi=posA+1; pi<posA+len; pi++){
			  int alit=(*clsSAT)[pi];
			  seen[ABS(alit)]=0;
		 }
		 if(end){
			 clsSAT->shrink(origsize);
		     return _UNKNOWN;
		 }
	}
	if(newCNFs<=pos+neg-delta){//set delete mark
    	clsSAT->shrink(Newsize);
		int pivot;
		if(pps->occCls[vi]<pps->occCls[-vi]) pivot=vi;
		else pivot=-vi;
		int occN=pps->occCls[pivot];
		for(i=0; i<occN; i++){
				posA=pps->occCls[pivot][i];
		        int len=(*clsSAT)[posA];
                if( (len & MARKBIT)==DELETED) continue;
			    pps->extend.push(0);
                pps->extend.push(pivot);
	     	    len=len>>FLAGBIT;
	
				//if(ABS(vi)==1453816) printf("\n pi=%d:", pivot);
	 	
				for(int i=posA+1; i<posA+len; i++){
					int lit=(*clsSAT)[i];
					if(pivot!=lit) pps->extend.push(lit);
					//else printf("*");
				}
		}
		
	//
		for(m=0; m<2; m++){
			int vv;
			if(m) vv=vi;
			else vv=-vi;
			
			int occM=pps->occCls[vv];
			for(i=0; i<occM; i++){
				posA=pps->occCls[vv][i];
		        int len=(*clsSAT)[posA];
		  	    len=len>>FLAGBIT;
	            (*clsSAT)[posA]=(len<<FLAGBIT) | DELETED;
				for(int i=posA+1; i<posA+len; i++){
					int lit=(*clsSAT)[i];
					if(vv!=lit){
						pps->occCls[lit].shrink(0);// ??? bug 3 2011
					    pps->occCls[-lit].shrink(0);
					}
				}
			}
		}
		deletedVnum++;
	}
	else{
	     clsSAT->shrink(origsize);
	}
	return _UNKNOWN;
}	

int XOR_varElimination(PPS *pps)
{
    int pos,neg;
    int i,j,clsCnt,k,deletedVnum,preNum;
    int alpha,beta;
    int posB,sz,*litB;
    if(pps->seen==0) pps->seen=(int *)calloc(pps->numVar+1,sizeof(int));
   	if(pps->numClause>150000 && pps->numClause<1000000){ alpha=4; beta=4;}
	else {alpha=2; beta=3;}
    int *seen=pps->seen;
	deletedVnum=0;
	while(1){
     	preNum=deletedVnum;
		int ipos=0;
	    Stack<int> * clsSAT=pps->clause;
        Stack<int> * occCls=pps->occCls;
        int endpos=clsSAT->nowpos();
    	clsCnt=0;
		while(ipos < endpos){
			int len=(*clsSAT)[ipos];
			int mark=len & MARKBIT;
		    len=len>>FLAGBIT;
		    ipos+=len;
			if(mark==DELETED) continue;
			clsCnt++;
	        if(len>21) continue;
		    int MinOcc=1000000;
            int lit=0;  
			for(i=ipos-len+1; i<ipos; i++) {
		       int clit=(*clsSAT)[i];
		       if(occCls[clit]<=0 || occCls[-clit]<=0) continue;
			   int occN=occCls[clit]+occCls[-clit];
			   if(occN<MinOcc) {lit=clit; MinOcc=occN;}
			}
            if(MinOcc>40 || MinOcc<=2) continue;
         	for(i=ipos-len+1; i<ipos; i++) {
		       int clit=(*clsSAT)[i];
		       seen[ABS(clit)]=clit;
			}
			int occN=occCls[-lit];
			int num2=0;
			for(j=0; j<occN; j++){
   	             int posB=occCls[-lit][j];
				 int sz=(*clsSAT)[posB];
				 sz=sz>>FLAGBIT;
		   		 if(sz>64) { num2=100; break;}
				 int *litB=&(*clsSAT)[posB+1];
                 k=0;
			   	 for(sz=sz-2; sz>=0; sz--){
					   int lt=litB[sz];
				 	   if(seen[ABS(lt)]==-lt) k++;
				 }
		         if(k<2) num2++;
			}
		    for(i=ipos-len+1; i<ipos; i++) {
		       int clit=(*clsSAT)[i];
		       seen[ABS(clit)]=0;
			}
			if(num2>2) goto No_delete;
			posB=occCls[-lit][0];
			sz=(*clsSAT)[posB];
			sz=sz>>FLAGBIT;// bug 2011/9/23 
	        litB=&(*clsSAT)[posB+1];
            for(j=sz-2; j>=0; j--) {
			seen[ABS(litB[j])]=litB[j];
			}
            occN=occCls[lit];
			for(j=0; j<occN; j++){
   	              int posA=occCls[lit][j];
				  int szA=(*clsSAT)[posA];
				  szA=szA>>FLAGBIT;
		   		  if(szA>64) { num2=10000; break;}
				  k=0;
			      int *litA=&(*clsSAT)[posA+1];
                  for(szA=szA-2; szA>=0; szA--){
					   int lt=litA[szA];
				 	   if(seen[ABS(lt)]==-lt) k++;
				  }
		          if(k<2) num2++;
			}
		    for(j=sz-2; j>=0; j--) seen[ABS(litB[j])]=0;
            if(num2>beta) goto No_delete;
	        pos=occCls[lit];
            neg=occCls[-lit];
	        num2=0;
			int i;
			for(i=0; i<pos; i++){
   	            int posA=occCls[lit][i];
   		        int sz=(*clsSAT)[posA];
				sz=sz>>FLAGBIT;
		   		int *litA=&(*clsSAT)[posA+1];
                int *pcls=litA+sz-1;
				for(; litA<pcls; litA++) seen[ABS(*litA)]=*litA;
   	            for(j=0; j<neg; j++){
   	                posB=occCls[-lit][j];
			        k=0;
			        int sz2=(*clsSAT)[posB];
				    sz2=sz2>>FLAGBIT;
	                int *litB=&(*clsSAT)[posB+1];
                    int *pclsB=litB+sz2-1;
					for(; litB<pclsB; litB++) if(seen[ABS(*litB)]==-(*litB)) k++;
					if(k<2) num2++;
                }
			  	litA=&(*clsSAT)[posA+1];
              	for(; litA<pcls; litA++) seen[ABS(*litA)]=0;
			}
			if(num2/alpha>pos+neg) goto No_delete; //2
			{
				bool NewUnit;
	    	    int rc=subsumptionResolution(pps, lit, deletedVnum,NewUnit,num2);
	  		    if(rc==UNSAT) return UNSAT;
			    if(NewUnit) preNum=-1;
			}
	No_delete:
			;
		}
	    if(preNum!=deletedVnum) {
	  		  int rc=deletegarbage(pps); //bug 2011/9/25
	  		  if(rc==UNSAT) return UNSAT;
	    }
       	setDoubleDataIndex(pps,false);
        if(clsCnt>=pps->numClause || preNum==deletedVnum) break;
	}
//	printf("c XOR_varElimination deleted var#=%d clauses#=%d \n", deletedVnum,pps->numClause);
    return _UNKNOWN;
}

void sortColumn(Stack<int> * & clause, int j_th, int numVar)
{    int i,j,k,lit,sum;
     int *cluaseLen;
	 
	 int maxLit=2*numVar+2;
	 cluaseLen=(int *) malloc(sizeof(int)*(maxLit));
     for(i = 0; i < maxLit; i++) cluaseLen[i] = 0;
   
	 int *pcls=clause->begin();
	 int *pend=clause->end();
	 int stacksize=pend-pcls;
  	 while(pcls < pend){
            int len=*pcls;
		    len=len>>FLAGBIT;
		    int *lits=pcls+1;
            pcls+=len;
		    if (j_th >= len-1) lit=0;
            else lit=ABS(lits[j_th]);
		    cluaseLen[lit]+=len;
	 }
     Stack<int> * clause2=new Stack<int>;
     clause2->memalloc (stacksize);
	 sum=0;
     for(i = 0; i < maxLit;i++) {
 		 j=cluaseLen[i];  cluaseLen[i]=sum;   sum+=j;
     }
//copy
	 pcls=clause->begin();
	 while(pcls < pend){
            int len=*pcls;
		    int *lits=pcls;
            len=len>>FLAGBIT;
		    pcls+=len;
	 	    if (j_th >= len-1) lit=0;
            else lit=ABS(lits[j_th+1]);
		    k=cluaseLen[lit];
	        for (; lits<pcls; lits++) (*clause2)[k++]=*lits;
           	cluaseLen[lit]=k;
	 }
	 delete clause;
	 clause=clause2;
	 free(cluaseLen);
}	 

Stack<int> *occCNF;
int occCNFcmp( const void *ptrA, const void *ptrB )
{
    int LitA=*(int *)ptrA;
	int numA=occCNF[LitA]+occCNF[-LitA];
	int LitB=*(int *)ptrB;
	int numB=occCNF[LitB]+occCNF[-LitB];
	if(numA>numB) return 1;
        if(numA<numB) return -1;
	return 0;
}

void getclausePos(PPS *pps)
{
	if(pps->clausePos) delete pps->clausePos;
	pps->clausePos = new Stack<int>;
	Stack<int> * clausepos=pps->clausePos;
        pps->numClause=0;
        Stack<int> *clauseCNF=pps->clause;
	int *pcls;
	int *pend=clauseCNF->end();
        int len;
   	for(pcls=clauseCNF->begin(); pcls < pend; pcls+=len){
                 len=*pcls;
		 int mark=len & MARKBIT;
		 len=len>>FLAGBIT;
       	         if( mark==DELETED) continue; //remove;
		 pps->numClause++;
                 int pos=pcls-clauseCNF->begin();
		 clausepos->push(pos);
	}    
}

void save_eqv(PPS *pps)
{
    if(pps->outEquAtom){
       for(int i=pps->numVar; i>=1; i--){
	      int vv=pps->outEquAtom[i];
	      if(vv==0 || vv==i) continue;
              pps->extend.push(0);
 	      pps->extend.push(i);
	      pps->extend.push(-vv);
	 }
	   free(pps->outEquAtom);
	   pps->outEquAtom=0;
	}
}
#include "core/Solver.h"
using namespace abcdSAT;

int load_glueclause(Solver* solver, PPS *pps)
{   
    bool ret;
    vec<Lit> lits;
    int numatom=pps->numVar;
    while (numatom > solver->nVars()) solver->newVar();
    int *fixedvar=pps->unit;
    free_mem(pps->seen);
    int *Seen=(int *) calloc (solver->nVars()+1, sizeof (int));
    int i=0;
//CNF clause   
    int *pcls=pps->clause->begin();
    int *pend=pps->clause->end();
    while(pcls < pend){
         int len=*pcls;
	 int mark=len & MARKBIT;
	 len=len>>FLAGBIT;
	 int *litp=pcls+1;
         pcls+=len;
	 if(mark==DELETED) continue;
	 if(mark==CNF_CLS){
		 lits.clear();
		 for (; litp<pcls; litp++){
	                int lit=*litp;
		        int vv=ABS(lit);
			if(fixedvar[vv]==0 || fixedvar[vv]==vv+1) {
           			Seen[vv]=1;
				lits.push( (lit > 0) ? mkLit(lit-1) : ~mkLit(-lit-1) );	
			}
			else {
			       if(fixedvar[vv]==lit) goto nextCNF;
			}
		 }
          	 ret=solver->addClause(lits); //close a clause
		 if(ret==false) return UNSAT;
	 }
nextCNF:
	 ;
     }
     for(i=1; i<=numatom; i++){
	    if(solver->assigns[i-1] != l_Undef) continue;
	    if(fixedvar[i]) continue;
	    if(Seen[i]) continue;
       	    fixedvar[i]=i+1;		// 0 occurrence
     }
     release_occCls(pps);
     free(Seen);
     return _UNKNOWN;
}
//---------------------------------------------------------------
// x's'1' is odd, return true 
bool parity (unsigned x)
{ bool res = false; while (x) res = !res, x &= x-1; 
    return res; 
}
// l1 (+) l2 (+) l3 (+) l4 +...+ln=1
void get_2_9_equivalence(PPS *pps)
{   unsigned int i,j,k,m,n,cNo,one,pw2;
    int *matchCli,match[512];
        
    getclausePos(pps);
    Stack<int> * clauseCNF=pps->clause;
    Stack<int> * clausePos=pps->clausePos;
    int numClauses=pps->numClause;
    matchCli=(int *) malloc(sizeof(int)*2020);
    i=0; 
    while (i < (unsigned int)numClauses){
           int iPos=(*clausePos)[i];
	   int len=(*clauseCNF)[iPos];
	   if((len & MARKBIT)==DELETED) {i++; continue;} 
	   len=len>>FLAGBIT;
	   unsigned int size1=len-1;
	   if(size1<2 || size1>9) { i++; continue; }
	   pw2=1;
           for(j=0;j<size1; j++) pw2=2*pw2;
           for(j=0;j<pw2; j++) match[j]=0;
	   cNo=n=0;
           iPos++;
	   for(j=i+1; j < (unsigned int)numClauses; j++){
    	         int jPos=(*clausePos)[j];
		 int jLen=(*clauseCNF)[jPos];
		 jLen=jLen>>FLAGBIT;
		 if(jLen!=len) break;
		 m=0;one=0;
		 jPos++;
		 for(k=0; k<size1; k++){
			 m=2*m;
		         if((*clauseCNF)[iPos+k]==-(*clauseCNF)[jPos+k]){
                                 m++;
                                 one++;
                                 continue;
                         }
			 if((*clauseCNF)[iPos+k]!=(*clauseCNF)[jPos+k]) break;
		 }
		 if(k<size1) break;
		 if(one%2) continue;
                 matchCli[cNo++]=j;
		 if(cNo >= 2000) break;
                 if(!match[m] && m) {n++; match[m]=1;}
	   }
	   if((pw2/2-1)==n && cNo<2000){
	         (*clauseCNF)[iPos-1]=(len<<FLAGBIT) | XOR_CLS; // xor clause; 
		 for(k=0;k<cNo;k++) {
		        int kPos=(*clausePos)[matchCli[k]];
			(*clauseCNF)[kPos]=(len<<FLAGBIT) | FROZE; //  freeze clause; 
		 }
	    }
	    i=j;
     }
     free(matchCli);
}

void get_XOR_equivalent(PPS *pps)
{
     int delrepeat=0;
     sortClause(pps->clause,4,pps->numClause,pps->numVar,delrepeat); //??no duplicate
     get_2_9_equivalence(pps);
}

int *XorFrq=0;
int *CNFfrq;
int XORcmp( const void *ptrA, const void *ptrB)
{
    int *litsA=*(int **)ptrA;
    int *litsB=*(int **)ptrB;
    
    int sumA=0;
    int lenA=(*litsA) >> FLAGBIT;
    for(int k=1; k<lenA; k++) sumA += XorFrq[ABS(litsA[k])];
  
    int sumB=0;
    int lenB=(*litsB)>>FLAGBIT;
    for(int k=1; k<lenB; k++) sumB += XorFrq[ABS(litsB[k])];
 
    if(lenA > lenB) return 1;
    if(lenA < lenB) return -1;
    if((lenB-1)*sumA < (lenA-1)*sumB) return 1;
    if((lenB-1)*sumA > (lenA-1)*sumB) return -1;
    return 0;
}

int clsCmp( const void *ptrA, const void *ptrB)
{
    int *litsA=*(int **)ptrA;
    int *litsB=*(int **)ptrB;
    
    int lenA=(*litsA) >> FLAGBIT;
    int lenB=(*litsB)>>FLAGBIT;
    if(lenA < lenB) return -1;
    if(lenA > lenB) return 1;
    
    for(int k=1; k<lenA; k++){
        if(litsA[k] < litsB[k]) return -1;
        if(litsA[k] > litsB[k]) return 1;
    }
    return 0;
}

int vfrqcmp( const void *ptrA, const void *ptrB)
{
    int varA=*(int *)ptrA;
    int varB=*(int *)ptrB;
         if(XorFrq[varA] < 4 && XorFrq[varB] < 4 ) goto cnfCmp;
         if(XorFrq[varA] < XorFrq[varB]) return 1;
         if(XorFrq[varA] > XorFrq[varB]) return -1;
cnfCmp:  
         if(CNFfrq[varA] < CNFfrq[varB]) return 1;
         if(CNFfrq[varA] > CNFfrq[varB]) return -1;

//  }
    return 0;
}

int xorfrqcmp( const void *ptrA, const void *ptrB)
{
     int varA=*(int *)ptrA;
     int varB=*(int *)ptrB;
     return XorFrq[varB]-XorFrq[varA];
}

void Adp_SymPSort(void *a, int n, int es, int (*cmp)(const void *,const void *));
int *extVarRank=0,numVarRk=0;
void rank_by_XOR_freq(PPS *pps, int way)
{  
     int numXor=0;
     int **XorPos=0;
     if(way==0) XorPos=(int **) malloc(sizeof(int *)*(pps->numClause/2));
     XorFrq=(int *) calloc(pps->numVar+1, sizeof(int));
     CNFfrq=(int *) calloc(pps->numVar+3, sizeof(int));
    
     int *pcls=pps->clause->begin();
     int *pend=pps->clause->end();
     while(pcls < pend){
         int len=*pcls;
	 int mark=len & MARKBIT;
	 int *lits=pcls;
	 len=len>>FLAGBIT;
         pcls+=len;
         if(mark==DELETED) continue;
         if(mark==XOR_CLS){
               if(way==0) XorPos[numXor++]=lits;
               for(int k=1; k<len; k++) XorFrq[ABS(lits[k])]++;
         }
         else{
               for(int k=1; k<len; k++) CNFfrq[ABS(lits[k])]++;
         }
         *lits=(len<<FLAGBIT) | CNF_CLS;
    }
  //  printf("c clause Xor#=%d \n",numXor);
    if(extVarRank==0) extVarRank=(int *) calloc(pps->numVar+50, sizeof(int));     
    int i;
    if(way){
           for(i=0; i < pps->numVar; i++) extVarRank[i]=i+1;
           numVarRk=pps->numVar;
           if(way==1) Adp_SymPSort((void *)extVarRank, pps->numVar, sizeof(int), vfrqcmp);
           else {
               Adp_SymPSort((void *)extVarRank, pps->numVar, sizeof(int), xorfrqcmp);
               for(i=0; i < pps->numVar; i++) {
              //   printf(" %d ",XorFrq[extVarRank[i]]);
                 if(XorFrq[extVarRank[i]]<3) break;
               }
               numVarRk=i;
          }
    }
    else{
          numVarRk=0;
          if(numXor >1 ){
              Adp_SymPSort((void *)XorPos, numXor, sizeof(int *), XORcmp);
              int *Seen=(int *) calloc(pps->numVar+1, sizeof(int));     
              for(int i=0; i < numXor; i++){
                 int *lits=XorPos[i];
                 int  len=(*lits) >> FLAGBIT;
                 for(int k=1; k<len; k++){ 
                    if(Seen[ABS(lits[k])]==0){
                        Seen[ABS(lits[k])]=1;
                       extVarRank[numVarRk++]=ABS(lits[k]);
                     }
                  }
              }
              free(Seen);
           }
     }
     if(XorPos) free(XorPos);
     free(XorFrq);
     free(CNFfrq);
}

void sortClause(PPS *pps,int **clsPos)
{  
     int *pcls=pps->clause->begin();
     int *pend=pps->clause->end();
     int clsNum=0;
     while(pcls < pend){
         int len=*pcls;
	 int mark=len & MARKBIT;
	 int *lits=pcls;
	 len=len>>FLAGBIT;
         pcls+=len;
         if(mark!=DELETED) clsPos[clsNum++]=lits;
     }
     Adp_SymPSort((void *)clsPos, clsNum, sizeof(int *), clsCmp);
}

void sortClause(Stack<int> *clause,int **clsPos)
{  
     int *pcls=clause->begin();
     int *pend=clause->end();
     int clsNum=0;
     while(pcls < pend){
         int len=*pcls;
	 int mark=len & MARKBIT;
	 int *lits=pcls;
	 len=len>>FLAGBIT;
         pcls+=len;
         if(mark!=DELETED) clsPos[clsNum++]=lits;
     }
     Adp_SymPSort((void *)clsPos, clsNum, sizeof(int *), clsCmp);
}

void XOR_Preprocess(PPS *pps,int way)
{
    get_XOR_equivalent(pps);
    rank_by_XOR_freq(pps,way);
  //  printf("c Varxor#=%d \n",numVarRk);
}
/*
void check(int sol[],Stack<int> *clause)
{
     int len,sum,i=0;
     int *pcls=clause->begin();
     int *pend=clause->end();
     while(pcls < pend){
         len=*pcls;
	 int mark=len & MARKBIT;
	 len=len>>FLAGBIT;
	 int *lits=pcls+1;
    	 pcls+=len;
         if(mark==DELETED) continue; 
         sum=0; i++;
         for (; lits<pcls; lits++) if(sol) if(sol[ABS(*lits)]==*lits) sum+=1;
         if(sol && (mark==CNF_CLS && sum==0 || mark==XOR_CLS && sum%2!=1)) {
		  printf ("s UNKNOWN \nc error i=%d sum=%d \nc ",i,sum);
		  int *lits=pcls+1-len;
		  for (; lits<pcls; lits++) printf("%d[%d] ",*lits,sol[ABS(*lits)]);
		  return;
                 // exit(0);
  	  }
   }
   printf("c verified \n");
}
*/

//-------------------------------------------------
void dumpCNFk(Stack<int> *clause)
{
     int *pcls=clause->begin();
     int *pend=clause->end();
     int i=0;
     while(pcls < pend){
         int len=*pcls;
	 int mark=len & MARKBIT;
	 len=len>>FLAGBIT;
	 int *lits=pcls+1;
    	 pcls+=len;
         if(mark != CNF_CLS) continue;
   	 printf("\n%d:",i++);
         for (; lits<pcls; lits++) printf("%d ",*lits);
    }
}

void CNFgarbageCollection(PPS *pps)
{   
    if (pps->garbage < 200000) return;

    clear_occCls(pps);
    int *pcls=pps->clause->begin();
    int *pend=pps->clause->end();
    int *newcls=pps->clause->begin();
    while(pcls < pend){
         int len=*pcls;
	 int mark=len & MARKBIT;
	 len=len>>FLAGBIT;
	 int *litp=pcls;
         pcls+=len;
	 if(mark==CNF_CLS){
		for (; litp<pcls; litp++) *newcls++ = *litp; 
         }
    }
    int size=newcls-pps->clause->begin();
    pps->clause->memalloc(size);
    set_CNF_occ(pps);
    pps->garbage=0;
}

