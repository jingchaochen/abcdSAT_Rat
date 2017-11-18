
#ifndef BoundedQueue_h
#define BoundedQueue_h

#include "mtl/Vec.h"

//=================================================================================================

namespace abcdSAT {

template <class T>
class bqueue {
    vec<T>  elems;
    int     first;
	int		last;
	unsigned long long sumofqueue;
	int     maxsize;
	int     queuesize; // Number of current elements (must be < maxsize !)
	bool expComputed;
	double exp,value;
public:
 bqueue(void) : first(0), last(0), sumofqueue(0), maxsize(0), queuesize(0),expComputed(false) { } 
	
	void initSize(int size) {growTo(size);exp = 2.0/(size+1);} // Init size of bounded size queue
	
	void push(T x) {
	  expComputed = false;
		if (queuesize==maxsize) {
			assert(last==first); // The queue is full, next value to enter will replace oldest one
			sumofqueue -= elems[last];
			if ((++last) == maxsize) last = 0;
		} else 
			queuesize++;
		sumofqueue += x;
		elems[first] = x;
		if ((++first) == maxsize) {first = 0;last = 0;}
	}

	T peek() { assert(queuesize>0); return elems[last]; }
	void pop() {sumofqueue-=elems[last]; queuesize--; if ((++last) == maxsize) last = 0;}
	
	unsigned long long getsum() const {return sumofqueue;}
	unsigned int getavg() const {return (unsigned int)(sumofqueue/((unsigned long long)queuesize));}
	int maxSize() const {return maxsize;}
	double getavgDouble() const {
	  double tmp = 0;
	  for(int i=0;i<elems.size();i++) {
	    tmp+=elems[i];
	  }
	  return tmp/elems.size();
	}
	int isvalid() const {return (queuesize==maxsize);}
	
	void growTo(int size) {
		elems.growTo(size); 
		first=0; maxsize=size; queuesize = 0;last = 0;
		for(int i=0;i<size;i++) elems[i]=0; 
	}
	
	double getAvgExp() {
	  if(expComputed) return value;
	  double a=exp;
	  value = elems[first];
	  for(int i  = first;i<maxsize;i++) {
	    value+=a*((double)elems[i]);
	    a=a*exp;
	  }
	  for(int i  = 0;i<last;i++) {
	    value+=a*((double)elems[i]);
	    a=a*exp;
	  }
	  value = value*(1-exp)/(1-a);
	  expComputed = true;
	  return value;
	  

	}
	void fastclear() {first = 0; last = 0; queuesize=0; sumofqueue=0;} // to be called after restarts... Discard the queue
	
    int  size(void)    { return queuesize; }

    void clear(bool dealloc = false)   { elems.clear(dealloc); first = 0; maxsize=0; queuesize=0;sumofqueue=0;}


};
}
//=================================================================================================

#endif
