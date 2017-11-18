// Copyright (c) 2010, Jingchao Chen, Donghua University,China.  All rights reserved.

#ifndef CircleSat_h_INCLUDED
#define CircleSat_h_INCLUDED

#include <cassert>
#include <cstring>
#include <stdio.h>
//#include <cstdio>

//format string for printing large integers
#ifdef _MSC_VER
typedef __int64  int64;
typedef __int64 longlong;
#define i64d "I64d"
#else
typedef long long int64;
typedef long long longlong;
#define i64d "lld"
#endif


typedef int ** intpp;
typedef int * intp;

class Mem2 {
public:
  typedef void * (*NewFun)(void *, size_t);
  typedef void (*DeleteFun)(void *, void*, size_t);
  typedef void * (*ResizeFun)(void *, void *, size_t, size_t);
//private:
  size_t cur, max;
  void * emgr; NewFun newfun; DeleteFun deletefun; ResizeFun resizefun;
  void operator += (size_t b) { if ((cur += b) > max) max = cur; }
  void operator -= (size_t b) { assert (cur >= b); cur -= b; }
public:
  Mem2 () : cur(0), max(0), emgr(0), newfun(0), deletefun(0), resizefun(0) { }
  void set (void * e, NewFun n, DeleteFun d, ResizeFun r) {
    assert (e && n && d && r);
    emgr = e; newfun = n; deletefun = d; resizefun = r;
  }
  operator size_t () const { return cur; }
  size_t getCurrent () const { return cur; }
  size_t getMax () const { return max; }
  void * allocate (size_t bytes) {
    size_t mb = bytes >> 20;
    void * res;
    res = newfun ? newfun (emgr, bytes) : malloc (bytes);
    if (!res) {
		printf("c out of memory allocating %d MB\n", (int)mb);
		exit(0);
	}
    *this += bytes;
    return res;
  }
  void * callocate (size_t bytes) {
    void * res = allocate (bytes);
    memset (res, 0, bytes);
    return res;
  }
  void * reallocate (void * ptr, size_t old_bytes, size_t new_bytes) {
    size_t mb = new_bytes >> 20;
    *this -= old_bytes;
    void * res  = resizefun ? resizefun (emgr, ptr, old_bytes, new_bytes) :
                              realloc (ptr, new_bytes);
	if (!res){
		printf("c out of memory allocating %d MB\n", (int)mb);
		exit(0);
	}
    *this += new_bytes;
    return res;
  }
  void * recallocate (void * ptr, size_t o, size_t n) {
    char * res = (char*) reallocate (ptr, o, n);
    if (n > o) memset (res + o, 0, n - o);
    return (void*) res;
  }
  void deallocate (void * ptr, size_t bytes) {
    *this -= bytes;
    if (deletefun) deletefun (emgr, ptr, bytes); 
    else free (ptr);
  }
};

template<class T> 
class Stack {
  T * a, * t, * e;
  int size () const { return e - a; }
public:
  int nowpos () const { return t - a; }
  size_t bytes () const { return size () * sizeof (T); }
  void memalloc (int size){
        size_t b = size * sizeof (T);
        a = (T*) realloc (a, b);
        t = a + size;
        e = a + size;
  }
private:
  void enlarge (Mem2 & m) {
    assert (t == e);
    size_t ob = bytes ();
    int o = size ();
    int s = o ? 2 * o : 2;
    size_t nb = s * sizeof (T);
//	a = (T*) m.reallocate (a, ob, nb);
	T *new_a =(T*)m.allocate(nb);
        if(ob){
	    memcpy(new_a, a,ob);  // DOS bug ???
	    m.deallocate (a, ob);
        }
	a=new_a;
	t = a + o;
        e = a + s;
  }
  void enlarge (){
	assert (t == e);
        int o = size ();
        int s;
	if(o>400000) s=o+o/2; 
	else s = o ? 2 * o : 2;
        size_t b = s * sizeof (T);
	a = (T*) realloc (a, b);
	t = a + o;
        e = a + s;
  }
public:
  Stack () : a (0), t (0), e (0) { }
  ~Stack () { free (a); }
  operator int () const { return t - a; }
  void push (Mem2 & m, const T & d) { if (t == e) enlarge (m); *t++ = d; }
  void push (const T & d) { if (t == e) enlarge (); *t++ = d; }
  const T & pop () { assert (a < t); return *--t; }
  const T & top () { assert (a < t); return t[-1]; }
  T & operator [] (int i) { assert (i < *this); return a[i]; }
  void shrink (int m = 0) { assert (m <= *this); t = a + m; }
 // void shrink (T * nt) { assert (a <= nt); assert (nt <= t); t = nt; }
  void release (Mem2 & m) { m.deallocate (a, bytes ()); a = t = e = 0; }
  void release () { free (a); a = t = e = 0; }
  const T * begin () const { return a; }
  const T * end () const { return t; }
  const T * iaddr(int i) const { return a+i;}
  T * begin () { return a; }
  T * end () { return t; }
  void remove (const T & d) {
	assert (t > a);
        T prev = *--t;
        if (prev == d) return;
  	T * p = t;
        for (;;) {
          assert (p > a);
          T next = *--p;
          *p = prev;
          if (next == d) return;
          prev = next;
        }
  }
  bool contains (const T & d) const {
    for (const T * p = begin (); p < end (); p++) if (*p == d) return true;
    return false;
  }
};

//preprocesss struct 
struct PPS {
   Stack<int> * clause;
   Stack<int> * clausePos;
   Stack<int> * occCls; //  
   Stack<int> * occBoth; //  
   int  numVar;                // the number of atoms 
   int  numClause;             //current number of clauses
   unsigned int garbage;
//   Stack<int> *trigonXORequ;   //trigonometric XOR equation
//   Stack<int> *sameReplace;   // x <=> a+b, replace a+b with x
   Stack<int> extend;
   int *outEquAtom;
   int *unit;	 // atom which occurs in unit clause
   int *seen;

   int  numXOR;  // the number of active XOR clauses
   int **Leq;    //  literals for each active XOR clause
};

#endif
