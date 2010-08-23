/* ======================================================================
   mulknap.c,  David Pisinger                     feb 1998 
   ====================================================================== */

/* This is the MULKNAP algorithm for solving the multiple knapsack 
 * problem. The algorithm is described in 
 *
 *   D.Pisinger
 *   "An exact algoirthm for large multiple knapsack problems",
 *   accepted for publication, European Journal of Operational 
 *   Research (1998)
 *
 * Copyright (c) D.Pisinger 1998.
 * The code may only be used for academic or non-commercial purposes.
 *
 * Further details on the project can also be found in
 *
 *   D.Pisinger
 *   "Algorithms for knapsack problems"
 *   Report 95/1, DIKU, University of Copenhagen
 *   Universitetsparken 1
 *   DK-2100 Copenhagen
 *
 * The code has been tested on a hp9000/735, and conforms with the
 * ANSI-C standard apart from some of the timing routines (which may
 * be removed).
 *  
 * Errors and questions are refered to:
 *   David Pisinger, associate professor
 *   DIKU, University of Copenhagen,
 *   Universitetsparken 1,
 *   DK-2100 Copenhagen.
 *   e-mail: pisinger@diku.dk
 *   fax: +45 35 32 14 01
 */

/* Added some testing and Ruby interface, Lou Vanek, 2/6/2006 */

/* ======================================================================
   definitions
   ====================================================================== */
// Ruby
#include "ruby.h"

// SATisfiability 
#ifdef __cplusplus
#include <cstdlib>

//#include <set>
//#include <vector>
//#include <dirent.h>
//#include "SAT.h"
#endif

// mulknap
#define MAXN          300   /* only reverse sort if n <= MAXN */
#define MAXCAP      30000   /* only tighten if capacity is up to MAXCAP */
#define MAXSTATES 5000000   /* max number of states in dyn prog for KP */
#define SSSTATES  1000000   /* max number of states in dyn prog for SSP */

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <stdarg.h>
#include <string.h>
#include <math.h>
#include <signal.h>

#ifdef __cplusplus
#include <stdexcept>
using namespace std;
#endif



/* ======================================================================
   macros
   ====================================================================== */

#define SYNC            5      /* when to switch to linear scan in bins */
#define SORTSTACK     200      /* size of stack for sorting */
#define MINMED        100      /* find exact median if larger size */
#define XITEMS         50      /* tighten constraints when less items */

#define TRUE  1                /* boolean values */
#define FALSE 0

#define LEFT  1                /* expansion of core in given direction */
#define RIGHT 2

#define PARTIATE 1             /* should sort routine partition or sort */
#define SORTALL  2

#define MORE     0             /* four states used in reducewgtset */
#define LAST     1
#define ALLENUM  2
#define FILLED   3

#define MAXV  (8*sizeof(long)) /* number of bits in a long integer */
#define PMAX  1                /* profit of worlds most efficient item  */
#define WMAX  0                /* weight of worlds most efficient item  */
#define PMIN  0                /* profit of worlds least efficient item */
#define WMIN  1                /* weight of worlds least efficient item */

#define FDET(a1, a2, b1, b2)   ((a1) * (ftype) (b2) - (a2) * (ftype) (b1))
#define DET(a1, a2, b1, b2)    ((a1) * (ptype) (b2) - (a2) * (ptype) (b1))
#define SWAP(a, b)   { register item t; t = *(a); *(a) = *(b); *(b) = t; }
#define SIZE(a)                ((int) (((a)->lset+1)-(a)->fset))

#ifdef __cplusplus
#define CHK_DIV_BY_0(denominator,msg) if (denominator==0) {     \
    char buf[1024];                                             \
    sprintf(buf,"Divide by zero. %s",(msg ? msg : ""));         \
    throw std::runtime_error(buf);                              \
  }
#else
#define CHK_DIV_BY_0(denominator,msg) if (denominator==0) {     \
    char buf[1024];                                             \
    sprintf(buf,"Divide by zero. %s",(msg ? msg : ""));         \
    rb_raise(rb_eArgError, buf);                                \
  }
#endif

#ifdef __cplusplus
#define CHK_RANGE_GREATERTHAN_0(tgt,msg) if (tgt<1) {                   \
    char buf[1024];                                                     \
    sprintf(buf,"Range error (must be greater than 0). %s",(msg ? msg : "")); \
    throw std::runtime_error(buf);                                      \
  }
#else
#define CHK_RANGE_GREATERTHAN_0(tgt,msg) if (tgt<1) {                   \
    char buf[1024];                                                     \
    sprintf(buf,"Range error (must be greater than 0). %s",(msg ? msg : "")); \
    rb_raise(rb_eArgError, buf);                                        \
  }
#endif














#define BFSIZ 1023

static char buf[BFSIZ + 1] = {0};
static int ptr = 0;


static void bin_prnt_byte(unsigned char x)
{
  int n;
  for(n=0; n<8; n++) {
    printf ( "%c", (x & (1<<n)) ? '1' : '0' );
    if (n==3)
      printf(" "); /* insert a space between nibbles */
  }
}


static int hexdump( char *src, int sz, FILE *fp, int dump_binary/*= 0*/ )
{
  int line;
  unsigned char c[4];

  if ( !fp )
    return( -1 );

  if ( sz < 1 ) {
    fprintf( fp, "HEX DUMP: dump size %d\n\n", sz );
    return( -2 );
  }

  line = ( sz / 4 ) + 1;

  while ( line ) {
    int i;
    for (i = 0; i < 4; i++ )
      c[i] = ( sz > 0 ) ? src[i] : 0;
    fprintf(fp, 
            "  %02.2x %02.2x %02.2x %02.2x",
            c[0],c[1],c[2],c[3]
            );

    if (dump_binary) {
      fprintf( fp, "   " );
      for (i = 0; i < 4; i++ ) {
        bin_prnt_byte(c[i]);
        fprintf( fp, " " );
      }

      fprintf( fp, "  " );
    }
    for (i = 0; i < 4; i++ )
      c[i] = ( sz > 0 && src[i] > 31 ) ? src[i] : '.';
    fprintf( fp, "       %c%c%c%c",
             c[0],c[1],c[2],c[3]);

    /* REDISPLAY THE 4 BYTES AS INT */
    fprintf( fp, "       %d", *((int *)src) );

    fprintf( fp, "\n" );
    sz  -= 4;
    src += 4;
    line--;
  } // while

  fprintf( fp, "\n" );
  return( 0 );
} /* hexdump */


/************** SALLOC *****************/
/* ALLOCATE A TEMPORARY BLANK-FILLED STRING IN THE RING */
/* RETURN THE ADDRESS TO THE STRING */
static char *salloc(int n)
// n;  /* NUMBER OF CHARACTERS (NOT COUNTING TRAILING NULL) */
{
  char *bf;

  /* FIND THE ADDRESS FOR A NEW BUFFER WITHIN buf (buf IS A CIRCULAR BUFFER) */
  if((ptr + n) > BFSIZ) 
    ptr = 0;
  bf = buf + ptr;
  ptr += (n + 1);

  /* CLEAR THE BUFFER AND END IT WITH ZERO */
  memset(bf,' ',n);
  bf[n] = 0;

  return(bf);
} /* salloc */


/*************** FMT *******************/
/* RETURN POINTER TO FORMATTED STRING */
/* CALLED AS fmt(format,arg0,arg1,...) */
char *fmt(char *fmt, ...)
{
  va_list args;
  char *f;
  char *t;

  /* ASSUME MAX SIZE IS 256 */
  t = salloc(256);

  /* FORMAT THE ARGUMENTS INTO THE BUFFER */
  va_start(args, fmt);
  //f = va_arg(args,char *);
  vsprintf(t,fmt,args);
  va_end(args);

  return t;
} /* fmt */



/* if round_up == 0: return int in range [0..max-1]
 * if round_up == 1: return int in range [1..max]
 */
int random_int(int max, 
               int round_up 
#ifdef __cplusplus
               = 1 // 0: round down 1: round up
#endif
               )
{
  double frac = (round_up+rand())/((double)RAND_MAX);
  frac  = max * frac;
  return (int) ( round_up ? ceil(frac) : floor(frac) );
}



//#define DUMP_ITEM(i) fprintf(stderr,"ITEM:  p: %hi w: %hi x: %hi y: %hi a: %hi\n",i->p,i->w,(short)i->x,(short)i->y,(short)i->a);





/* ======================================================================
   type declarations
   ====================================================================== */

typedef int           mk_boolean; /* logical variable         */
typedef long          ntype;   /* number of states         */
typedef long         itype;   /* item profits and weights */
typedef long          stype;   /* sum of profit or weight  */
typedef float         ftype;   /* product type (sufficient precision) */
typedef double        ptype;   /* product type (sufficient precision) */
typedef signed char   mtype;   /* number of knapsacks      */
typedef unsigned long btype;   /* binary solution vector   */

typedef int (*funcptr) (const void *, const void *);

/* item record */
typedef struct irec {
  itype    p;     /* profit */
  itype    w;     /* weight */
  mtype    x;     /* optimal solution variable */
  mtype    y;     /* current solution */
  mtype    a;     /* consider only after a */
  int     *xp;    /* pointer to solution variable */
} item;

typedef struct { /* i-stack */
  item     *f;
  item     *l;
} interval;

/* state in dynamic programming */
typedef struct pv {
  stype    psum;
  stype    wsum;
  btype    vect;
} dpstate;

/* partial weight vector */
typedef struct {
  stype    wsum;  /* weight sum */
  item     *mod;  /* modified vector */
} wstate;

/* set of partial vectors */
typedef struct pset {
  ntype       size; /* set size */
  dpstate    *fset; /* first element in set */
  dpstate    *lset; /* last element in set */
  dpstate    *set1; /* first element in array */
  dpstate    *setm; /* last element in array */
} partset;

/* set of partial weight vectors */
typedef struct {
  ntype    size;  /* set size */
  wstate   *fset; /* first element in set */
  wstate   *lset; /* last element in set */
} wgtset;

/* tightening record */
typedef struct {
  stype    c;     /* capacity of knapsack */
  stype    wsmall;/* current weight sum, small items */
  stype    wbig;  /* current weight sum, big items */
} trec;

/* all problem information */
typedef struct {
  int      type;         /* type of problem           */
  itype    range;        /* data range                */
  mtype    m;            /* number of knapsacks       */
  ntype    n;            /* number of items           */
  mk_boolean  sim;          /* similar capacities        */
  stype    *cap;         /* all capacities */
  item     *fitem;       /* first item in problem     */
  item     *litem;       /* last item in problem      */

  /* information corresponding to Multiple Knapsack Problem */
  item     *h;           /* index of enumeration      */
  item     *maxh;        /* largest depth in tree     */
  stype    csum;         /* sum of all initial capacities */
  stype    psum;         /* profit sum fixed items    */
  stype    wsum;         /* weight sum fixed items    */
  itype    brp;          /* profit of break item      */
  itype    brw;          /* weight of break item      */
  stype    psumb2;       /* profit sum break item     */
  stype    wsumb2;       /* weight sum break item     */
  stype    z1;           /* current lower bound       */

  /* information corresponding to Subset-sum Problem */
  mtype    k;            /* knapsack to be considered */
  item     *fitem2;      /* first item restricted problem */
  item     *litem2;      /* last item restricted problem */
  item     *s2;          /* s+1 is first item enumme. */
  item     *t2;          /* t-1 is last item enummer. */
  item     *b2;          /* break item for smallest c */
  stype    wsuma2;       /* weight sum of all items   */
  stype    wsumbw2;      /* weight sum up to b        */
  stype   *wcap;        /* cap info of each knapsack */
  wgtset   da;           /* set of partial vectors    */
  wgtset   db;           /* set of partial vectors    */
  mk_boolean  finish2;      /* did we reach optimum      */
  stype    psum2;        /* solution profit sum       */
  stype    wsum2;        /* solution weight sum       */

  /* information corresponding to 0-1 Knapsack Problem */
  item     *ftouch;
  item     *ltouch;
  item     *s;
  item     *t;
  item     *b;
  item     *fpart;
  item     *lpart;
  stype    wfpart;
  item     *fsort;
  item     *lsort;
  stype    wfsort;
  stype    c;
  stype    cstar;
  stype    wstar;        /* weight sum corresponding to zstar */
  stype    z;
  stype    lb;           /* lower bound on problem. vector y is not changed */
  stype    zstar;        /* optimal solution value */
  stype    zwsum;
  itype    ps, ws, pt, wt;

  btype    vno;          /* current vector number   */
  item *   vitem[MAXV];  /* current last MAXV items */
  item *   ovitem[MAXV]; /* optimal set of items    */
  btype    ovect;        /* optimal solution vector */

  stype    dantzig;
  stype    ub;
  stype    psumb;
  stype    wsumb;
  mk_boolean  firsttime;
  mk_boolean  welldef;
  partset  d;                 /* set of partial vectors */
  interval *intv1, *intv2;
  interval *intv1b, *intv2b;

  /* repeatedly used arrays */
  dpstate  *kpstates;
  wstate   *sstatesa1;
  wstate   *sstatesa2;
  wstate   *sstatesb1;
  wstate   *sstatesb2;
  interval *interv;

  /* debug information */
  long curred;            /* number of currently reduced */
} state;


/* ======================================================================
   debug variables
   ====================================================================== */

long iterates;          /* iterations in branch-and-bound */
long tightened;         /* max tightening */
long reduced;           /* max numer of reduced */
long gub;               /* global upper bound */
long tottime;           /* computing time in milliseconds */
long coresize;          /* max number of variables considered in b&b */


/* **********************************************************************
**********************************************************************
Small procedures
**********************************************************************
********************************************************************** */


/* ======================================================================
   forward declarations
   ====================================================================== */


static void minknap(state *a, item *fitem, stype c, stype z);


/* ======================================================================
   debug routines
   ====================================================================== */

static void error(char *str, ...)
{
  va_list args;

  va_start(args, str);
  vprintf(str, args); printf("\n");
  va_end(args);
  exit(-1);
}


/* ======================================================================
   timing routines
   ====================================================================== */

/* These timing routines are written for HP-UNIX, but should be portable
 * with minor changes. The timing function "times" should be portable, but
 * since it returns the number of clock-ticks used by the process, one must
 * convert them to seconds. The function "sysconf" returns the number of
 * clock-ticks per second when given the argument _SC_CLK_TCK, but apparently
 * there is no convention on what _SC_CLK_TCK should be (HP-UNIX is using
 * the value 2, while digital UNIX has value 3). The constant is defined
 * in <unistd.h>, but only if _POSIX_SOURCE is defined.
 */

#ifdef false
#define _POSIX_SOURCE         /* to read <unistd.h> on digital UNIX */
#define _INCLUDE_POSIX_SOURCE /* to read <unistd.h> on HP-UX */
#include <unistd.h>           /* define the constant _SC_CLK_TCK */
#include <sys/times.h>        /* timing routines */

static void give_time(long *time)
{ /* return the number of milliseconds used */
  struct tms timeend;
  double t1;

  times(&timeend);
  t1 = (double) (timeend.tms_utime) / sysconf(_SC_CLK_TCK);
  *time = (long)(t1 * 1000);
}
#endif

/* ======================================================================
   palloc
   ====================================================================== */

static void pfree(void *p)
{ 
  /* semi-own free routine which makes additional test */
  if (p == NULL) 
    error("freeing null");
  free(p);
}


static void *palloc(long size, long no)
{ 
  /* semi-own alloc routine which makes additional test */
  long *p;

  size *= no;

  if (size == 0) 
    size = 1;

  if (size != (size_t) size) 
    error("Alloc too big %ld", size);

  p = (long *)malloc(size);
  if (p == NULL) 
    error("no memory size %ld", size);
  return p;
}


/* ======================================================================
   findvect
   ====================================================================== */

static dpstate *findvect(stype ws1, dpstate *f1, dpstate *l1)
{
  /* find vector i, so that i->wsum <= ws < (i+1)->wsum */
  register dpstate *f, *l, *m;
  register stype ws;

  /* a set should always have at least one vector */
  f = f1; 
  l = l1; 
  ws = ws1;
  if (f->wsum >  ws) 
    return NULL; 

  if (l->wsum <= ws) 
    return l;

  while (l - f > SYNC) {
    m = f + (l - f) / 2;
    if (m->wsum > ws) 
      l = m-1; 
    else 
      f = m;
  }

  while (l->wsum > ws) 
    l--;

  return l;
}


/* ======================================================================
   push/pop
   ====================================================================== */

static void push(state *a, int side, item *f, item *l)
{
  interval *pos;

  if (l+1 == f) 
    return;

  switch (side) {
  case LEFT : pos = a->intv1; 
    (a->intv1)++; 
    break;

  case RIGHT: pos = a->intv2; 
    (a->intv2)--; 
    break;
  }

  if (a->intv1 == a->intv2) 
    error("interval stack full");

  pos->f = f; 
  pos->l = l;
}

static void pop(state *a, int side, item **f, item **l)
{
  interval *pos;

  switch (side) {
  case LEFT : if (a->intv1 == a->intv1b) 
      error("pop left");
    (a->intv1)--; 
    pos = a->intv1; 
    break;

  case RIGHT: if (a->intv2 == a->intv2b) 
      error("pop right");
    (a->intv2)++; 
    pos = a->intv2; 
    break;
  }

  *f = pos->f; 
  *l = pos->l;
}


/* **********************************************************************
**********************************************************************
Subset-sum Problem
**********************************************************************
********************************************************************** */


/* ======================================================================
   weightsort
   ====================================================================== */
// sort weights in decreasing order
static void weightsort(item *f, item *l)
{
  register itype mw;
  register item *i, *j, *m;
  int d;

  d = l - f + 1;

  if (d > 1) {
    m = f + d / 2;
    if (f->w < m->w) 
      SWAP(f, m);

    if (d > 2) {
      if (m->w < l->w) { 
        SWAP(m, l); 
        if (f->w < m->w) 
          SWAP(f, m); 
      }
    }
  }

  if (d > 3) {
    mw = m->w; 
    i  = f; 
    j  = l; 

    for (;;) {

      do i++; 
      while (i->w > mw);

      do j--; 
      while (j->w < mw);

      if (i > j) 
        break;

      SWAP(i, j);
    }

    weightsort( f, i -1 ); 
    weightsort( i, l    );
  }
}


/* ======================================================================
   compress
   ====================================================================== */

static item *compress(item *f, item *l, mtype y)
{
  register item *i, *j, *m;
  register mtype y1;

  /* compress items in table such that ordering is respected */
  y1 = y;
  j = l + 1;
  m = f - 1;

  for (i = l; i != m; i--) {
    if (i->y != y1) {
      j--;
      if (i != j) 
        SWAP(i, j);
    }
  }

  return j-1;
}


/* ======================================================================
   freeitems
   ====================================================================== */

static item *freeitems(state *a, stype *psumfree, item *f, item *l, mtype y)
{
  register item *i, *j, *m;
  register stype ps, ws;
  register mtype y1;

  y1 = y+1; 
  ps = 0; 
  ws = 0;
  j = f - 1;
  m = l + 1;

  for (i = f; i != m; i++) {
    if (i->y == -y1) { 
      i->y = 1; 
      ps += i->p; 
      ws += i->w; 
      continue; 
    } 
    if ((i->y < 0) || (i->a > y1)) { 
      j++; 
      SWAP(i, j);  
      continue; 
    }
    i->y = 0;
  }

  a->psum2 -= ps;
  a->wsum2 -= ws;
  *psumfree = ps;    /* lower bound for KP */
  return j + 1;
}


/* ====================================================================== 
   defitems
   ====================================================================== */

static item *defitems(state *a, item *f, item *l, mtype y)
{
  register item *i, *j, *m;
  register mtype y1;
  register stype ps, ws;

  y1 = y; 
  ps = 0; 
  ws = 0;
  j = f - 1;
  m = l + 1;

  for (i = f; i != m; i++) {
    if (i->y == 1) { 
      ps += i->p; 
      ws += i->w; 
      i->y = y1;
      j++; 
      if (i != j) 
        SWAP(i, j); 
    }
  }

  a->psum2 += ps;
  a->wsum2 += ws;
  return j + 1;
}


/* ======================================================================
   wmultiply
   ====================================================================== */

static void wadd(state *a, item *t)
{
  register wstate *i, *j, *k;
  register stype c, w, iw, jw, kw;
  register item *mod;
  wstate *r;
  
  /* initialize limits */
  if (2*a->db.size + 1 > SSSTATES) 
    error("no space in wadd");

  r = (a->db.fset == a->sstatesb1 ? a->sstatesb2 : a->sstatesb1);
  i = a->db.fset;
  j = a->db.fset;
  k = r;
  w = t->w;
  c = a->wcap[a->k];
  mod = t;

  /* add large state at end, and copy first state */
  (a->db.lset+1)->wsum = c + 1;
  *k = *i; i++;

  /* now merge sets: i, j indices to each set, k index to merged set */
  iw = i->wsum; 
  jw = j->wsum + w; 
  kw = k->wsum;
  
  for (;;) {
    if (iw <= jw) {
      if (iw > c) 
        break;
      k++; 
      kw = iw; 
      *k = *i; 
      i++; 
      iw = i->wsum; 
    } else {
      if (jw != kw) { 
        k++; 
        kw = k->wsum = jw; 
        k->mod = mod; 
      }
      j++; 
      jw = j->wsum + w;
    }
  } // for

  /* save limits */
  a->db.fset = r;
  a->db.lset = k;
  a->db.size = SIZE(&(a->db));
} // wadd


static void wsub(state *a, item *s)
{
  register wstate *i, *j, *k;
  register stype c, w, iw, jw, kw;
  register item *mod;
  wstate *r;

  /* initialize limits */
  if (2*a->da.size + 1 > SSSTATES) 
    error("no space in wsub");

  r = (a->da.fset == a->sstatesa1 ? a->sstatesa2 : a->sstatesa1);
  i = a->da.fset;
  j = a->da.fset;
  k = r;
  w = s->w;
  c = a->wcap[a->k] - (a->wsuma2 - a->wsumbw2); 
  if (c < 0) 
    c = 0; /* never subtract more than can be added */
  mod = s;

  /* add small state at end, and copy first state */
  (a->da.lset+1)->wsum = c-1;
  *k = *i; i++;

  /* now merge sets: i, j indices to each set, k index to merged set */
  iw = i->wsum; 
  jw = j->wsum - w; 
  kw = k->wsum;
	  
  for (;;) {
    if (iw >= jw) {
      if (iw < c) 
        break;
      k++; 
      kw = iw; 
      *k = *i; 
      i++; 
      iw = i->wsum;
    } else {
      if (jw != kw) { 
        k++; 
        kw = k->wsum = jw; 
        k->mod = mod; 
      }
      j++; 
      jw = j->wsum - w;
    }
  } // for

  /* save limits */
  a->da.fset = r;
  a->da.lset = k;
  a->da.size = SIZE(&(a->da));
} // wsub


/* ======================================================================
   definesolution2
   ====================================================================== */

static void definesolution2(state *a, wstate *i1, wstate *j1)
{
  register item *i, *m, *l;
  register wstate *j, *k;
  register stype ps, ws, w0, c;
  mtype y, m1;

  m1 = a->k+1;
  y = -m1; ps = 0;
  c = a->wcap[a->k];

  /* first take items up to b2 */
  m = a->b2;

  for (i = a->fitem2; i != m; i++) {
    if (m1 >= i->a) { 
      i->y = y; 
      ps += i->p; 
    }
  }

  /* backtrack set da */
  ws = i1->wsum;
  w0 = a->wsumbw2;

  for (j = i1; ws != w0; j--) {
    if (j->wsum == ws) { 
      i = j->mod; 
      i->y = 1; 
      ws += i->w; 
      ps -= i->p; 
    }
  }

  /* backtrack set db */
  ws = j1->wsum;

  for (j = j1; ws != 0; j--) {
    if (j->wsum == ws) { 
      i = j->mod; 
      i->y = y; 
      ws -= i->w; 
      ps += i->p; 
    }
  }

  /* sum totals */
  ws = i1->wsum + j1->wsum;
  a->psum2  += ps;
  a->wsum2  += ws;
  a->wsuma2 -= ws;

  /* find new fitem */
  a->fitem2 = compress( a->fitem2, a->t2-1, y ) + 1;
}


/* ======================================================================
   reducewgtset
   ====================================================================== */

static void reducewgtset(state *a, mk_boolean update)
{
  register wstate *i, *j, *k, *l;
  register stype ws, iw, kw, c, maxw;
  wstate *i1, *k1;
  int com;

  /* check if knapsack a->k is filled */
  c = a->wcap[a->k];

  i = a->da.fset; 
  j = a->da.lset+1;
  k = a->db.fset; 
  l = a->db.lset+1;

  maxw = -1; 
  l->wsum = c+1; 
  kw = k->wsum; 

  for ( ; i != j; i++) {
    iw = i->wsum; 
    ws = iw + kw;

    while (ws <= c) {
      if (ws > maxw) { 
        maxw = ws; 
        i1 = i; 
        k1 = k; 
      }
      k++; 
      kw = k->wsum; 
      ws = iw + kw;
    } // while
  } // for

  /* now see if improved (optimal) solution */
  com = MORE;
  if ((update) && (a->k == a->m-1) && (a->wsuma2 <= c)) 
    com = LAST;
  if ((a->s2 < a->fitem2) && (a->t2 > a->litem2))       
    com = ALLENUM;
  if (maxw == c)                                        
    com = FILLED;

  if (com != MORE) {
    if (update) 
      definesolution2(a, i1, k1);
    a->wcap[a->k] = maxw;
    a->finish2    = TRUE;
  }
} // reducewgtset


/* ======================================================================
   findwbreak
   ====================================================================== */

static void findwbreak(state *a, mtype m, mk_boolean update)
{
  register item *i, *j;
  register stype c, c1;
  stype wsum;
  wstate *k;

  /* find break item for the current knapsack */
  c = c1 = a->wcap[a->k];
  j = a->litem2 + 1;

  for (i = a->fitem2 ; i != j; i++) {
    if (m >= i->a) { 
      if (i->w > c) 
        break; 
      else 
        c -= i->w; 
    }
  }

  wsum = c1 - c;

  /* initialize limits */
  a->b2      = i;
  a->s2      = i-1;
  a->t2      = i;
  a->wsumbw2 = wsum;

  /* initialize table of partial vectors */
  a->da.size = 1;
  a->da.fset = a->sstatesa1;
  a->da.lset = a->da.fset;

  a->db.size = 1;
  a->db.fset = a->sstatesb1;
  a->db.lset = a->db.fset;

  /* initialize first partial vector */
  k = a->da.fset; 
  k->wsum = wsum; 
  k->mod = NULL;

  k = a->db.fset; 
  k->wsum = 0;    
  k->mod = NULL;
}


/* ======================================================================
   partition
   ====================================================================== */

static void partition(state *a, mk_boolean update)
{
  stype c;
  mtype m;
  item *i;

  c = a->wcap[a->k];
  m = a->k + 1;

  if (c > 0) {
    a->finish2 = FALSE;
    findwbreak(a, m, update);

    for (;;) {
      reducewgtset(a, update);
      if (a->finish2) 
        break;

      i = a->t2;
      if (i <= a->litem2) {
        if (m >= i->a) 
          wadd(a,i);
        a->t2++;
      }

      i = a->s2;
      if (i >= a->fitem2) {
        if (m >= i->a) 
          wsub(a,i);
        a->s2--;
      }
    } // for

  } // if
}


/* ======================================================================
   subset_sum
   ====================================================================== */

static void subset_sum(state *a, mk_boolean update, stype *c)
{
  stype wsum, tight, lb;
  mtype k;
  ntype n;

  wsum = 0;

  for (k = 0; k != a->m; k++) 
    wsum += c[k];

  /* initialize */
  tight     = 0;
  a->wsum2  = 0;
  a->psum2  = 0;
  a->wsuma2 = 2*a->csum+1;
  a->fitem2 = a->h+1;
  a->litem2 = a->litem;
 
  /* copy capacities */
  a->wcap = (stype *)palloc(a->m, sizeof(stype));
  memcpy(a->wcap, c, a->m * sizeof(stype));

  /* prepare items */
  if (update) {
    a->litem2 = compress(a->fitem2, a->litem2, 1);
    a->psum2  = a->psum;
    a->wsuma2 = a->wstar;
    n         = a->litem2 - a->fitem2 + 1;
    if (n <= MAXN) 
      weightsort(/*a,*/ a->fitem2, a->litem2);
  }

  /* now fill the knapsacks */
  for (k = 0; k != a->m; k++) {
    if ((c[k] <= MAXCAP) || (update)) { 
      a->k = k; 
      partition(a, update); 
    }
  }

  for (k = 0; k != a->m; k++) {
    if (update) {
      if ((a->wcap[k] < c[k]) && (a->wsuma2 > 0)) {
        /* solve 0-1 Knapsack Problem by freeing variables, sum, define */
        a->fitem2 = freeitems(a, &lb, a->h+1, a->litem, k);
        minknap(a, a->fitem2, c[k], lb);
        a->fitem2 = defitems(a, a->fitem2, a->litem, -(k+1));
      }
    } else {
      tight    += c[k] - a->wcap[k];
      a->wsum2 += a->wcap[k];
      c[k]      = a->wcap[k];
    } // else
  } // for

  if (!update) {
    if (tight > tightened) 
      tightened = tight;
  } // if

  pfree(a->wcap);
} // subset_sum


/* **********************************************************************
**********************************************************************
0-1 Knapsack Problem
**********************************************************************
********************************************************************** */


/* ======================================================================
   improvesolution
   ====================================================================== */

static void improvesolution(state *a, dpstate *v)
{
  if (v->wsum > a->c) 
    error("wrong improvesoluton");
  if (v->psum < a->z) 
    error("not improved solution");

  a->z      = v->psum;
  a->zwsum  = v->wsum;
  a->ovect  = v->vect;
  memcpy(a->ovitem, a->vitem, sizeof(item *) * MAXV);
}


/* ======================================================================
   definesolution
   ====================================================================== */

static void definesolution(state *a)
{
  register item *i, *m;
  item     *f, *l;
  stype     psum, wsum;
  btype     j, k;

  if (a->firsttime) {
    if (a->z == a->lb) { 
      a->welldef = TRUE; 
      return; 
    } 
    a->zstar = a->z;
    a->wstar = a->zwsum;

    m = a->b;

    for (i = a->h+1; i != m; i++) 
      i->y = 1;

    m = a->litem + 1;

    for (i = a->b; i != m; i++) 
      i->y = 0;

    a->firsttime = FALSE;
  }

  psum = a->z;
  wsum = a->zwsum;
  f    = a->fsort - 1;
  l    = a->lsort + 1;

  for (j = 0; j < MAXV; j++) {
    k = a->ovect & ((btype) 1 << j);
    i = a->ovitem[j]; 
    if (i == NULL) 
      continue;

    if (i->y == 1) {
      if (i > f) 
        f = i;
      if (k) { 
        psum += i->p; 
        wsum += i->w; 
        i->y = 0; 
      }
    } else {
      if (i < l) 
        l = i;
      if (k) { 
        psum -= i->p; 
        wsum -= i->w; 
        i->y = 1; 
      }
    }
  }

  a->welldef = (psum == a->psumb) && (wsum == a->wsumb);

  /* prepare for next round */
  if (!a->welldef) {
    a->fsort = f + 1;
    a->lsort = l - 1;
    a->intv1 = a->intv1b;
    a->intv2 = a->intv2b;

    a->c  = wsum;
    a->z  = psum - 1;
    a->ub = psum;
  }
}


/* ======================================================================
   partsort
   ====================================================================== */

static void partsort(state *a, item *f, item *l, stype ws, int what)
{
  register itype   mp, mw;
  register item   *i, *j, *m;
  register stype   wi;
  int              d;

  d = l - f + 1;

  if (d > 1) {
    m = f + d / 2;
    if (FDET(f->p, f->w, m->p, m->w) < 0) 
      SWAP(f, m);
    if (d > 2) {
      if (FDET(m->p, m->w, l->p, l->w) < 0) {
        SWAP(m, l);
        if (FDET(f->p, f->w, m->p, m->w) < 0) 
          SWAP(f, m);
      }
    }
  }

  if (d > 3) {
    mp = m->p; 
    mw = m->w; 
    i = f; 
    j = l; 
    wi = ws;

    for (;;) {

      do { wi += i->w; i++; } 
      while (FDET(i->p, i->w, mp, mw) > 0);

      do { j--; } 
      while (FDET(j->p, j->w, mp, mw) < 0);

      if (i > j) 
        break;

      SWAP(i, j);
    }

    if (wi <= a->cstar) {
      if (what ==  SORTALL) 
        partsort(a, f, i-1, ws, what);

      if (what == PARTIATE) 
        push(a, LEFT, f, i-1);
      partsort(a, i, l, wi, what);
    } else {
      if (what ==  SORTALL) 
        partsort(a, i, l, wi, what);
      if (what == PARTIATE) 
        push(a, RIGHT, i,  l);
      partsort(a, f, i-1, ws, what);
    }
  }

  if ((d <= 3) || (what == SORTALL)) {
    a->fpart  = f;
    a->lpart  = l;
    a->wfpart = ws;
  }
}


/* ======================================================================
   haschance
   ====================================================================== */

static mk_boolean haschance(state *a, item *i, int side)
{
  register dpstate *j, *m;
  register ptype p, w, r;
  stype pp, ww;

  if (a->d.size == 0) 
    return FALSE;

  if (side == RIGHT) {
    if (a->d.fset->wsum <= a->c - i->w) 
      return TRUE;
    p  = a->ps; 
    w  = a->ws; 
    pp = i->p - a->z - 1; 
    ww = i->w - a->c;
    r = -DET(pp, ww, p, w);

    m = a->d.lset + 1;

    for (j = a->d.fset; j != m; j++) {
      if (DET(j->psum, j->wsum, p, w) >= r) 
        return TRUE;
    }

  } else {
    if (a->d.lset->wsum > a->c + i->w) 
      return TRUE;
    p = a->pt; 
    w = a->wt; 
    pp = -i->p - a->z - 1; 
    ww = -i->w - a->c;
    r = -DET(pp, ww, p, w);

    m = a->d.fset - 1;

    for (j = a->d.lset; j != m; j--) {
      if (DET(j->psum, j->wsum, p, w) >= r) 
        return TRUE;
    }

  } // else

  return FALSE;
}


/* ======================================================================
   multiply
   ====================================================================== */

static void multiply(state *a, item *h, int side)
{
  register dpstate *i, *j, *k, *m;
  register itype    p, w;
  register btype    mask0, mask1;
  dpstate          *r1, *rm;

  if (a->d.size == 0) 
    return;
  if (side == RIGHT) { 
    p = h->p; 
    w = h->w; 
  } else { 
    p = -h->p; 
    w = -h->w; 
  }
  if (2*a->d.size + 2 > MAXSTATES) 
    error("no space in multiply");

  /* keep track on solution vector */
  a->vno++;
  if (a->vno == MAXV) 
    a->vno = 0;
  mask1 = ((btype) 1 << a->vno);
  mask0 = ~mask1;
  a->vitem[a->vno] = h;

  /* initialize limits */
  r1 = a->d.fset; 
  rm = a->d.lset; 
  k = a->d.set1; 
  m = rm + 1;
  k->psum = -1;
  k->wsum = r1->wsum + abs(p) + 1;
  m->wsum = rm->wsum + abs(w) + 1;

  i = r1;
  j = r1;

  for ( ; (i != m) || (j != m) ; ) {
    if (i->wsum <= j->wsum + w) {
      if (i->psum > k->psum) {
        if (i->wsum > k->wsum) 
          k++;
        k->psum = i->psum; 
        k->wsum = i->wsum;
        k->vect = i->vect & mask0;
      }
      i++;
    } else {
      if (j->psum + p > k->psum) {
        if (j->wsum + w > k->wsum) 
          k++;
        k->psum = j->psum + p; 
        k->wsum = j->wsum + w;
        k->vect = j->vect | mask1;
      }
      j++;
    }
  } // for

  a->d.fset = a->d.set1;
  a->d.lset = k;
  a->d.size = a->d.lset - a->d.fset + 1;
}


/* =========================================================================
   simpreduce
   ========================================================================= */

static void simpreduce(int side, item **f, item **l, state *a)
{
  register item *i, *j, *k;
  register ptype pb, wb;
  register ptype q, r;

  if (a->d.size == 0) { 
    *f = *l+1; 
    return; 
  }
  if (*l < *f) 
    return;

  pb = a->b->p; 
  wb = a->b->w;
  q = DET(a->z+1-a->psumb, a->c-a->wsumb, pb, wb);
  r = -DET(a->z+1-a->psumb, a->c-a->wsumb, pb, wb);
  i = *f; 
  j = *l;
  if (side == LEFT) {
    k = a->fsort - 1;

    while (i <= j) {
      if (DET(j->p, j->w, pb, wb) > r) {
        SWAP(i, j); i++;       /* not feasible */
      } else {
        SWAP(j, k); 
        j--; 
        k--;  /* feasible */
      }
    } // while

    *l = a->fsort - 1; 
    *f = k + 1;
  } else {
    k = a->lsort + 1;

    while (i <= j) {
      if (DET(i->p, i->w, pb, wb) < q) {
        SWAP(i, j); 
        j--;      /* not feasible */
      } else {
        SWAP(i, k); 
        i++; 
        k++;  /* feasible */
      }
    } // while

    *f = a->lsort + 1; 
    *l = k - 1;
  }
}


/* ======================================================================
   reduceset
   ====================================================================== */

static void reduceset(state *a)
{
  register dpstate *i, *m, *k;
  register ptype    ps, ws, pt, wt, r;
  stype             z, c;
  dpstate          *r1, *rm, *v;
  item             *f, *l;

  if (a->d.size == 0) 
    return;

  /* initialize limits */
  r1 = a->d.fset;
  rm = a->d.lset;

  v  = findvect(a->c, r1, rm);
  if (v == NULL) {
    v = r1 - 1; /* all excess weight */
  } else {
    if ((v->psum == a->z) && (v->wsum < a->zwsum)) 
      improvesolution(a, v);
    if (v->psum > a->z) 
      improvesolution(a, v);
  }
  c  = a->c;
  z  = a->z + 1;
  k  = a->d.setm;

  /* expand core, and choose ps, ws */
  if (a->s < a->fsort) {
    if (a->intv1 == a->intv1b) {
      ps = PMAX; 
      ws = WMAX;
    } else {
      pop(a, LEFT, &f, &l);
      if (f < a->ftouch) 
        a->ftouch = f;
      ps = f->p; 
      ws = f->w; /* default: choose item at random */
      simpreduce(LEFT, &f, &l, a);
      if (f <= l) {
        partsort(a, f, l, 0, SORTALL); 
        a->fsort = f;
        ps = a->s->p; 
        ws = a->s->w;
      }
    }
  } else {
    ps = a->s->p; 
    ws = a->s->w;
  }

  /* expand core, and choose pt, wt */
  if (a->t > a->lsort) {
    if (a->intv2 == a->intv2b) {
      pt = PMIN; 
      wt = WMIN;
    } else {
      pop(a, RIGHT, &f, &l);
      if (l > a->ltouch) 
        a->ltouch = l;
      pt = l->p; 
      wt = l->w; /* default: choose item at random */
      simpreduce(RIGHT, &f, &l, a);
      if (f <= l) {
        partsort(a, f, l, 0, SORTALL); 
        a->lsort = l;
        pt = a->t->p; 
        wt = a->t->w;
      }
    }
  } else {
    pt = a->t->p; 
    wt = a->t->w;
  }

  /* now do the reduction */
  r = DET(z, c, ps, ws);

  m = v;

  for (i = rm; i != m; i--) {
    if (DET(i->psum, i->wsum, ps, ws) >= r) {
      k--; 
      *k = *i;
    }
  }

  r = DET(z, c, pt, wt);

  m = r1 - 1;

  for (i = v; i != m; i--) {
    if (DET(i->psum, i->wsum, pt, wt) >= r) {
      k--; 
      *k = *i;
    }
  }

  a->ps = (short)ps; 
  a->ws = (short)ws;
  a->pt = (short)pt; 
  a->wt = (short)wt;
  a->d.fset = k;
  a->d.lset = a->d.setm - 1; /* reserve one record for multiplication */
  a->d.size = a->d.lset - a->d.fset + 1;
}


/* ======================================================================
   initfirst
   ====================================================================== */

static void initfirst(state *a, stype ps, stype ws)
{
  dpstate *k;

  a->d.size  = 1;
  a->d.set1  = a->kpstates;
  a->d.setm  = a->d.set1 + MAXSTATES - 1;
  a->d.fset  = a->d.set1;
  a->d.lset  = a->d.set1;

  k = a->d.fset;
  k->psum   = ps;
  k->wsum   = ws;
  k->vect   = 0;
}


/* ======================================================================
   initvect
   ====================================================================== */

static void initvect(state *a)
{
  register btype i;

  for (i = 0; i < MAXV; i++) 
    a->vitem[i] = NULL;

  a->vno = MAXV-1;
}


/* ======================================================================
   findbreak
   ====================================================================== */

static int findbreak(state *a)
{
  register item *i, *m;
  register stype psum, wsum, c;

  psum = 0; 
  wsum = 0; 
  c = a->cstar;

  i = a->h + 1;
  m = a->litem + 1;

  for ( ;; i++ ) {
    if (i == m) {
      break;
    }
    if (wsum + i->w > c) {
      break;
    }
    psum += i->p; 
    wsum += i->w;
  }

  a->fsort   = a->fpart;
  a->lsort   = a->lpart;
  a->ftouch  = a->fpart;
  a->ltouch  = a->lpart;
  a->b       = i;
  a->psumb   = psum;
  a->wsumb   = wsum;
  if (i == m ) {
    a->dantzig = psum;
  }
  else {
    CHK_DIV_BY_0(i->w,"findbreak")
      a->dantzig = psum + ((c - wsum) * (stype) i->p) / i->w;
  }
  if (gub == 0) 
    gub = a->dantzig;

  /* find greedy solution */

  m = a->litem + 1;

  for (i = a->b; i != m; i++) {
    if (wsum + i->w <= c) { 
      psum += i->p; 
      wsum += i->w; 
    }
  }

  if (psum > a->lb) {
    m = a->b;

    for (i = a->h+1; i != m; i++) 
      i->y = 1;

    m = a->litem + 1;
    wsum = a->wsumb;

    for (i = a->b; i != m; i++) {
      i->y = 0; 
      if (wsum + i->w <= c) { 
        wsum += i->w; 
        i->y = 1; 
      }
    }

    a->lb    = psum;
    a->z     = psum;
    a->zstar = psum;
    a->wstar = wsum;
  } else {
    a->z     = a->lb;
    a->zstar = a->lb;
    a->wstar = a->cstar;
  } 
  a->c = a->cstar;
}


/* ======================================================================
   minknap
   ====================================================================== */

static void minknap(state *a, item *fitem, stype c, stype lb)
{
  interval  *inttab;
  item      *h;

  h = a->h; 
  a->h = fitem-1;  

  a->cstar = c;
  a->lb    = lb;
  inttab   = a->interv;
  a->intv1 = a->intv1b = &inttab[0];
  a->intv2 = a->intv2b = &inttab[SORTSTACK - 1];
  a->fsort = a->litem; 
  a->lsort = a->h+1;
  partsort(a, a->h+1, a->litem, 0, PARTIATE);
  findbreak(a);

  a->ub = a->dantzig;
  a->firsttime = TRUE;

  for (;;) {
    a->s = a->b-1;
    a->t = a->b;
    initfirst(a, a->psumb, a->wsumb);
    initvect(a);
    reduceset(a);

    while ((a->d.size > 0) && (a->z != a->ub)) {
      if (a->t <= a->lsort) {
        if (haschance(a, a->t, RIGHT)) 
          multiply(a, a->t, RIGHT);
        (a->t)++;
      }
      reduceset(a);

      if (a->s >= a->fsort) {
        if (haschance(a, a->s, LEFT)) 
          multiply(a, a->s, LEFT);
        (a->s)--;
      }
      reduceset(a);
    } // while

    definesolution(a);
    if (a->welldef) 
      break;
  } // for

  a->h = h;
}


/* **********************************************************************
**********************************************************************
Multiple Knapsack Problem
**********************************************************************
********************************************************************** */


/* ======================================================================
   findbest
   ====================================================================== */

static void findbest(state *a, stype *c, item **k1, mtype *i1)
{
  register item *j, *k, *m;
  mtype i;

  *k1 = NULL; 
  *i1 = 0; 
  if (a->h == a->litem) 
    return;

  for (i = 0; i < a->m; i++) {
    if (c[i] > 0) {
      /* remove items, not allowed for this knapsack */
      m = a->litem + 1;

      for (j = k = a->h+1; j != m; j++) {
        if (j->a > i+1) { 
          SWAP(j, k); 
          k++; 
        }
      }

      /* solve the knapsack problem */
      minknap(a, k, c[i], 0);

      /* find most efficient item */
      m = a->litem + 1;

      for (j = k; j != m; j++) 
        if (j->y == 1) 
          break;

      if (j != m) {
        k = j;

        for (j = k+1; j != m; j++) {
          if (j->y == 1) {
            if (DET(j->p, j->w, k->p, k->w) > 0) 
              k = j;
          }
        }

        if (k->a > i+1) 
          error("bad choice");
        *k1 = k; *i1 = i;
        return;
      } // if
    } // if
  } // for

  /* no items fit into any knapsacks */
}


/* ======================================================================
   copysolution
   ====================================================================== */

static void copysolution(state *a)
{
  register item *k, *l;

  a->z1 = a->psum2;
  l = a->litem + 1;

  for (k = a->fitem; k != l; k++) {
    if (k->y < 0) 
      k->x = -k->y; 
    else 
      k->x = 0;
  } // for

}


/* ======================================================================
   reduceitems
   ====================================================================== */

static void reduceitems(state *a, stype z, stype c)
{
  register item *i, *j, *k;
  register itype pb, wb;
  register stype q;

  pb = a->brp; 
  wb = a->brw;
  q = (long)DET( z + 1 - a->psumb2, c - a->wsumb2, pb, wb);
  i = a->h + 1; 
  j = a->litem; 
  k = a->h + 1;

  while (i <= j) {
    if (DET(i->p, i->w, pb, wb) < q) {
      i->y = 0; 
      SWAP(i, k); 
      i++; 
      k++; /* not feasible */
      a->curred++;
    } else {
      SWAP(i, j); 
      j--; /* feasible */
    }
  } // while

  a->h = k - 1;
  if (a->curred > reduced) 
    reduced = a->curred;
}


/* ======================================================================
   alloctables
   ====================================================================== */

static void alloctables(state *a)
{
  a->kpstates  = (dpstate  *)palloc(MAXSTATES, sizeof(dpstate));
  a->sstatesa1 = (wstate   *)palloc(SSSTATES,  sizeof(wstate));
  a->sstatesa2 = (wstate   *)palloc(SSSTATES,  sizeof(wstate));
  a->sstatesb1 = (wstate   *)palloc(SSSTATES,  sizeof(wstate));
  a->sstatesb2 = (wstate   *)palloc(SSSTATES,  sizeof(wstate));
  a->interv    = (interval *)palloc(SORTSTACK, sizeof(interval));
}


static void freetables(state *a)
{
  pfree(a->kpstates);
  pfree(a->sstatesa1);
  pfree(a->sstatesa2);
  pfree(a->sstatesb1);
  pfree(a->sstatesb2);
  pfree(a->interv);
}


/* ======================================================================
   mulbranch
   ====================================================================== */

static void mulbranch(state *a, stype *c1)
{
  item  *j, *h;
  mtype  i, a1;
  stype *c;
  stype  csum, ub;
  itype  p, w;

  iterates++;
  /* copy capacities, and tighten them */
  c = (stype *)palloc(a->m, sizeof(stype));
  memcpy(c, c1, a->m * sizeof(stype));
  subset_sum(a, FALSE, c);
  csum = a->wsum2;
  /* csum = tighten(a, c); */

  /* determine upper and lower bound */
  minknap(a, a->h+1, csum, a->z1 - a->psum);
  ub        = a->zstar + a->psum;
  a->brp    = a->b->p;
  a->brw    = a->b->w;
  a->psumb2 = a->psumb + a->psum;
  a->wsumb2 = a->wsumb; /* weight of fixed items are subtracted from c */

  if (ub > a->z1) {
    subset_sum(a, TRUE, c);
    if (a->psum2 > a->z1) 
      copysolution(a);
  }

  /* check upper bound */
  if ((ub > a->z1) && (a->h < a->litem) && (csum > 0)) {
    h = a->h; /* save h for freeing reduced items */
    reduceitems(a, a->z1, csum);
    findbest(a, c, &j, &i);
    if ((a->h < a->litem) && (j != NULL)) {
      a->h++; 
      SWAP(j, a->h); 
      j = a->h;
      if (j > a->maxh) 
        a->maxh = j;

      /* put item j in knapsack i */
      c[i] -= j->w; 
      a->psum += j->p; 
      a->wsum += j->w; 
      j->y = -(i+1);

      if (c[i] >= 0) 
        mulbranch(a, c);

      c[i] += j->w; 
      a->psum -= j->p; 
      a->wsum -= j->w;
      a->h--;

      /* exclude item j from knapsack i */
      a1 = j->a; 
      j->a = i+2; 
      j->y = 0; 
      p = j->p; 
      w = j->w;

      mulbranch(a, c);

      for (j = a->h+1; j != a->litem + 1; j++) {
        if ((j->p == p) && (j->w == w) && (j->a == i+2)) 
          break;
      }

      if (j == a->litem+1) 
        error("cannot find %hd,%hd", p, w);

      j->a = a1;
    } // if

    a->curred -= (a->h - h);
    a->h = h; /* free reduced items */
  } // if

  /* free and return */
  pfree(c);
} // mulbranch


/* ======================================================================
   mulknap
   ====================================================================== */
// n: the number of items to stuff in knapsacks
// m: the number of knapsacks
// p: an array of profits(or costs or values) of each item to stuff in knapsacks
// w: an array of weights of each item to stuff in knapsacks
// x: an array indicating which knapsack each item is stuffed into
// c: an array of capacities of each knapsack
int mulknap(int n, int m, int *p, int *w, int *x, int *c)
{
  register ntype i, l;
  register item *j, *k;
  state          a;
  item          *tab;
  interval      *inttab;
  //long           t1, t2;

  /* initialize debug variables, and start timer */
  iterates  = 0;
  tightened = 0;
  reduced   = 0;
  gub       = 0;
  //give_time(&t1);

  /* copy variables to internal structure */
  a.n         = n;
  a.m         = m;
  a.curred    = 0;

  /* allocate space for test example and two border items */
  tab = (item *) palloc(n+1, sizeof(item));
  a.fitem = &tab[1]; 
  a.litem = &tab[n];

  /* copy test instance */
  a.cap   = (stype *)palloc(a.m, sizeof(stype));

  // error check
  for (i = 1; i != m; i++) { 
    if (c[i-1] > c[i]) 
      error("c not ordered"); 
  }

  a.csum  = 0;

  for (i = 0; i != m; i++) { 
    a.cap[i] = c[i]; 
    a.csum  += c[i]; 
  }

  l = n;

  for ( i = 0, j = a.fitem; i != l; i++, j++) {
    j->x = 0; 
    j->y = 0; 
    j->a = 1; 
    j->w = w[i]; 
    j->p = p[i]; 
    j->xp = x+i; 
  }

  /* now the branch-and-bound part */
  a.z1   = 0;
  a.psum = 0;
  a.wsum = 0;
  a.h    = a.fitem - 1;
  a.maxh = a.h;
  alloctables(&a);

  /* run the branch-and-bound algorithm */ 
  mulbranch(&a, a.cap);

  /* define solution vector */
  k = a.litem + 1;

  for (j = a.fitem; j != k; j++) 
    *(j->xp) = j->x;

  /* free global tables */
  freetables(&a);
  pfree(a.cap); 
  pfree(tab);
  coresize = (a.maxh - a.fitem) + 1; 

  /* stop timer and return */
  //give_time(&t2); 
  //tottime = t2 - t1;
  //printf( "milliseconds: %3i\n", tottime );
  return( a.z1 );
} /* mulknap */











#define MAX(x,y) ((x>y)?(x):(y))

static int init_bins = 0;

static void count_bin_weights( int *bin, int n, int m, int *w, int *x, int vlvl )
{
  init_bins++;
  int binidx;
  int i;

  for ( i = 0; i < m; i++ ) 
    bin[i] = 0;

  for ( i = 0; i < n; i++ ) {
    binidx = x[i];
    if (binidx > 0) // has item been assigned to a bin?
      bin[binidx-1] += w[i];
    // else item has not been assigned to a bin
  }
}


static void print_bin_weights( int *bin, int n, int m, int *w, int *x, int vlvl )
{
  if ( vlvl > 1 ) {
    int i;
    if ( ! init_bins )
      count_bin_weights( bin, n, m, w, x, vlvl );

    for ( i = 0; i < m; i++ ) {
      printf( "bin[%2i]: %4i\n", i+1, bin[i] );
    }

    printf( "\n\n");
  }
}



static void print_solution( int z, int *bin, int n, int m, int *p, int *w, int *x, int *c, int vlvl )
{
  if ( vlvl > 0 ) {
    if ( ! init_bins )
      count_bin_weights( bin, n, m, w, x, vlvl );

    int cnt = 0;
    int i;
    for ( i = 0; i < n; i++ ) {
      if (x[i] > 0) cnt++;
    }

    if ( vlvl > 1 ) {
      printf( "\nz: %i\n\n", z );

      for ( i = 0; i < n; i++ ) {
        printf( "x[%2i]: %2i\tw[%2d]: %3d\n", i, x[i], i, w[i] );
      }
    }

    printf( "\nitems used: %i\n\n", cnt );
  }

  print_bin_weights( bin, n, m, w, x, vlvl );
}


static int resetbins( int bound, int m, int *c, int *bin )
{
  init_bins = 0;
  int i;

  for ( i = 0; i < m; i++ ) {
    c[i]   = bound;
    bin[i] = 0;
  }
}


int symmetric_subsum( int lower, int upper, int n, int m, int *p, int *w, int *x, int *bin, int vlvl )
{
  int bound = lower;
  int z;
  int found;
  int done = 0;

#ifdef __cplusplus
  class Finalizer
  { public:
    int *c;
    Finalizer(int m) { c = (int *)palloc(sizeof(int), m); }
    ~Finalizer() { free(c); /*printf("symmetric_subsum:finally!\n\n");*/ }
  };
  Finalizer finally(m); 
#else
  int *c = (int *)palloc(sizeof(int), m);
#endif

  if( vlvl > 0) {
    printf( "\n max_weight: %4i\n", upper );
    printf( "\nlower bound: %4i\n", lower );
  }
  CHK_RANGE_GREATERTHAN_0(upper,fmt("[max weight: %i]",upper))
    CHK_RANGE_GREATERTHAN_0(lower,fmt("[min weight: %i]",lower))

    while (1) {
      resetbins( bound, m, 
#ifdef __cplusplus
                 finally.c,
#else
                 c,
#endif
                 bin );

      z = mulknap( n, m, p, w, x, 
#ifdef __cplusplus
                   finally.c
#else
                   c
#endif
                   );

      found = z >= n;

      if( vlvl > 2) printf( "\nlower: %4i\tupper: %5i\tupper bound: %5i\tz: %6i\tfound: %i\tdone: %i\n", 
                            lower, upper, bound, z, found, done );

      if (done || (found && bound <= lower)) {
        if( vlvl > 3) {
          if (!done) 
            printf( "bounds as low as can go\n");
        }
        count_bin_weights( bin, n, m, w, x, vlvl );
        print_solution(z,bin,n,m,p,w,x,
#ifdef __cplusplus
                       finally.c
#else
                       c
#endif
                       , MAX(0,vlvl));
        if (vlvl == 1) print_bin_weights( bin, n, m, w, x, 2);
        break;
      }

      if (found) {
        if( vlvl > 3) printf( "search bottom half\n");
        upper = bound;
        bound = lower;
      }
      else { // not found
        if( vlvl > 3) printf( "search top half\n");
        lower = bound + 1;
        bound = (lower + upper)/2;
        if ( (bound <  lower) ||
             (bound >  upper) ||
             (lower >  upper)
             ) {
          if( vlvl > 3) printf( "bounds converged: %i %i %i\n", lower, upper, bound);
          done++;
        }
      }
      print_bin_weights( bin, n, m, w, x, vlvl );
    } // while

#ifndef __cplusplus
  pfree(c);
#endif
  return(z);
} // symmetric_subsum



/* valid domains (for most 32-bit machines):
 * tgtsum:  1,2,...,(2**31) - 1
 *      w:  1,2,...,(2**15) - 1
 *      	(note: items that weight less than 1 will be ignored)
 *      n:  1,2,...,(2**31) - 1
 */
int subsetsum( int n, int tgtsum, int *w, int *x, int vlvl )
{
  int  c;
  int  bin;

#ifdef __cplusplus
  class Finalizer
  { public:
    int *p; // array of int
    Finalizer(int n) { p = (int *)palloc(sizeof(int), n); }
    ~Finalizer() { free(p); /*printf("subsetsum:finally!\n\n");*/ }
  };
  Finalizer finally(n); 
#else
  int *p = (int *)palloc(sizeof(int), n);
#endif

  //CHK_RANGE_GREATERTHAN_0(upper,fmt("[max weight: %i]",upper))
  //CHK_RANGE_GREATERTHAN_0(lower,fmt("[min weight: %i]",lower))
  int i;
  for ( i = 0; i < n; i++ ) {
    // initialize arrays
#ifdef __cplusplus
    finally.p[i]  = w[i];
#else
    p[i]  = w[i];
#endif
    x[i]  = 0;
  }

  resetbins( tgtsum, 1, &c, &bin );

  // hopefully profit will equal tgtsum.
  int profit = mulknap( n, 1/*just 1 bin/knapsack*/, 
#ifdef __cplusplus
                        (int *)finally.p
#else
                        p
#endif
                        , w, x, &c );

#ifndef __cplusplus
  pfree(p);
#endif
  return profit;
} // subsetsum



#ifdef __cplusplus
// Satisfiability algorithm that uses a slow branch-and-bound technique.
// DO NOT USE THIS (SLOW) ALGORITHM!
// This algorithm can take only up to 32 variables.
class ExpSatisfiability32
{
 public:
  enum constants { MAX_VARIABLES = 32 };

  int m;  // number of clauses to satisfy
  int n;  // number of variables
  char **t; // solution matrix/table
  int color[32];
  int false_pops;
  int num_tests;
  int vlvl;

 ExpSatisfiability32(int _n, int _vlvl = 1) : m(0), n(_n), vlvl(_vlvl), t(NULL) 
    {
      if ( n > MAX_VARIABLES )
#ifdef __cplusplus
        throw std::runtime_error("Too many variables");
#else
      rb_raise(rb_eArgError, "Too many variables");
#endif
    }

  bool init(int _m,unsigned long *_c, unsigned long*s)
  {	false_pops = 0;
    num_tests  = 0;

    for ( int v = 0; v < n; v++ ) {
      sign_set(v,1,s);
      color[v] = 0;
    }

    if (! table_create())
      return false;

    return table_fill(_c);
  }

  ~ExpSatisfiability32()
    {
      dispose();
    }
  void dispose()
  {
    table_dispose();
  }

  int sign(int v, unsigned long *s)
  {
    return((*s & (1 << v)) ? 1 : -1);
  }
  void sign_set(int v, int val, unsigned long *s)
  {
    if (val < 1)
      (*s) &= ~(1 << v);
    else
      (*s) |=  (1 << v);
  }


  char table(int c,int v)
  {
    char *p = t[c];
    return p[v];
  }
  bool table_create()
  {
    t = (char **)calloc(m, sizeof(void *));
    if (!t) return false;
    int i;
    for ( i = 0; i < m; i++) {
      t[i] = (char *)calloc(n, sizeof(char));
      if ( !t[i] ) 
        return table_dispose();
    }

    return true;
  }
  bool table_dispose()
  {
    if (!t) return false;

    int i;
    for ( i = 0; i < m; i++) {
      if (!t[i])
        break;
      free(t[i]);
    }

    free(t);
    t = NULL;
    return false;
  }
  bool table_fill(unsigned long *c)
  {
    assert(t);
    assert(c);
    if ( m < 1 || n < 1 ) return false;

    int i;
    for ( i = 0; i < m; i++ ) {
      for ( int j = 0; j < 2; j++ ) {
        for ( int k = 0; k < n; k++ ) {
          int bitset = c[i+j] & (1<<k);
          if ( bitset )
            t[i][k] = ( !j ? 1 : -1 );
        }
      }
    }

    return true;
  }
  void cnf_dump()
  {
    assert(t);
    if ( m < 1 || n < 1 ) return;

    printf("CNF\n");

    int i,k;
    for ( i = 0; i < m; i++ ) {
      for ( k = 0; k < n; k++ ) {
        if ( t[i][k] )
          printf( " %3i",	(k+1) * t[i][k] );
      }
      printf(" 0\n");
    }

    printf("\n");
  }
  void table_dump()
  {
    assert(t);
    if ( m < 1 || n < 1 ) return;

    printf("TABLE\n");
    int i, k;
    for ( i = 0; i < m; i++ ) {
      printf("%4i:  ",i);
      for ( k = 0; k < n; k++ ) {
        if ( ! (k % 4) )
          printf("  ");
        printf( "%3i",	t[i][k] );
      }
      printf("\n");
    }

    printf("\n");
  }

  void color_dump()
  {
    printf("COLOR\n");
    int i;
    for ( i = 0; i < n; i++ )
      if ( color[i] )
        printf("%5i: %4i\n", i, color[i]);
      else
        printf("%5i: %4s\n", i, ".");

    printf("\n");
  }

  int push(int c,int v)
  {
    color[v]++;
    return c+1;
  }
  void pop(int c, int v)
  {
    false_pops++;
    color[v]--;
  }

  // For _m clauses defined in _c, solve satisfiability
  // and return solution vector in s.
  // Return true if satisfiable, false otherwise.
  bool solve(int _m, unsigned long *_c, unsigned long *s)
  {
    m = _m;
    bool r = init(_m,_c,s); 
    if (!r) return r;
    if (vlvl > 1) cnf_dump();
    if (vlvl > 1) table_dump();
    r = satisfiability( 0, 0, s );
    if (vlvl > 1) {
      printf("\nFALSE POPS: %i\n", false_pops );
      printf(  " NUM TESTS: %i\n\n", num_tests );
      color_dump();
    }
    return r;
  }
  bool satisfiability( int c, int v, unsigned long *s )
  {
    if ( c >= m ) { // reached end (solved!)
      if (vlvl > 1) printf("%4i %4i: *** SOLVED ***\n",c,v);
      return true;
    }

    if ( v >= n ) { // reached end of variables
      if (vlvl > 3) printf("%4i %4i: reached end of vars\n",c,v);
      return false;
    }

    num_tests++;

    if (table(c,v) == sign(v,s)) {
      if (vlvl > 3) printf("%4i %4i: PUSH to %i  %c\n",c,v,c+1, (sign(v,s) > 0) ? '+' : '-' );
      bool r = satisfiability( push(c,v), 0, s ); // next lvl
      if (vlvl > 3) printf("%4i %4i: POP: r: %i\n",c,v,r);
      if (r) return(r);
      pop(c,v);
    }

    // try moving right
    if (vlvl > 3) printf("%4i %4i: commence next col\n",c,v);
    bool r = satisfiability( c, v+1, s ); // next var
    if (vlvl > 3) printf("%4i %4i: (next col) pop and rtn r: %i\n",c,v,r);
    if (r) return r;

    if ((sign(v,s) <= -1) || (color[v] > 0) || table(c,v) == 0) {
      if (vlvl > 3) printf("%4i %4i: color: %i sign: %i, so pop\n",c,v,color[v],sign(v,s));
      return false;
    }

    // try changing sign as last resort
    sign_set(v,-1,s);
    if (vlvl > 3) printf("%4i %4i: set sign\n",c,v);
    r = (satisfiability( c, v, s ));
    if (vlvl > 3) printf("%4i %4i: pop: r: %i\n",c,v,r);
    if (r) return r;
    if ((sign(v,s) <= -1) && (color[v] < 1)) {
      if (vlvl > 3) printf("%4i %4i: REset sign\n",c,v);
      sign_set(v, 1,s);
    }
    return(r);
  }

}; // ExpSatisfiability32
#endif














#undef TEST
#ifdef TEST
static int test_interactive__symmetric_subsum()
{
  int  w[] = { 4, 2, 2, 20, 20, 11, 11, 3, 9, 13, 17, 17, 32, 4, 5, 7, 9, 11, 12, 14, 15, 16, 17, 18 };
  int  p[] = { 1, 1, 1,  1,  1,  1,  1, 1, 1,  1,  1,  1,  1, 1, 1, 1, 1,  1,  1,  1,  1,  1,  1,  1 };
  int  x[] = { 0, 0, 0,  0,  0,  0,  0, 0, 0,  0,  0,  0,  0, 0, 0, 0, 0,  0,  0,  0,  0,  0,  0,  0 };
  int  i;
  int  m; // number of bins
  int  n = sizeof(w)/sizeof(int);
  int  lower = 0;
  int  upper = 0;

  /* VLVL -- verbosity level
   * 0: no output
   * 1: minimum verbose: just grand totals
   * 2: just summary info
   * 3: intermediate work
   * 4: all details: show all: low-level debug
   */
  int  vlvl  = 1;

  printf( "\nnumber of items: %i\n\n", n );

  for ( i = 0; i < n; i++ ) {
    lower = MAX( lower, w[i] );
    upper = upper + w[i];
  }

  while (1) {
    printf( "num bins: " );
    scanf( "%i", &m );

    printf( "v lvl: " );
    scanf( "%i", &vlvl );

    int *bin = (int *)palloc(sizeof(int),m);
    symmetric_subsum(lower, upper, n, m, p, w, x, bin, vlvl );

    pfree(bin);
  }

  return 0;
} // test_interactive__symmetric_subsum



static int test_batch__symmetric_subsum(int n, int m, int cap, int vlvl)
{
  int  isz = sizeof(int);
  int *w = (int *)palloc(isz, n);
  int *p = (int *)palloc(isz, n);
  int *x = (int *)palloc(isz, n);
  int  i;
  int  lower = 0;
  int  upper = 0;
  int *bin = (int *)palloc(sizeof(int),m);

  srand(7);

  for ( i = 0; i < n; i++ ) {
    // initialize all arrays
    w[i]  = random_int(cap,1);
    CHK_DIV_BY_0(w[i],fmt("test_batch__symmetric_subsum: w: %i i: %i n: %i",w[i],i,n))

      p[i]  = 1;
    x[i]  = 0;

    lower = MAX( lower, w[i] );
    upper = upper + w[i];
  }

  if (vlvl > 0) { 
    printf( "\n num bins: %i\n", m );
    printf(   "num items: %i\n\n", n );
  }

  symmetric_subsum(lower, upper, n, m, p, w, x, bin, vlvl );

  pfree(w); pfree(p); pfree(x); pfree(bin);
  return 0;
} // test_batch__symmetric_subsum





static int test_batch__subsetsum(int n, int maxwgt, int tgt, int vlvl)
{
  int  isz = sizeof(int);
  int *w   = (int *)palloc(isz, n);
  int *x   = (int *)palloc(isz, n);
  int  c; 
  int  bin;

  srand(7);

  for ( int i = 0; i < n; i++ ) {
    // initialize weight array (same as profit array)
    w[i]  = random_int(maxwgt,1/*0: round down, 1: round up (no zero)*/);
    //CHK_DIV_BY_0(w[i],fmt("test_batch__subsetsum: w: %i i: %i n: %i",w[i],i,n))
  }

  if (vlvl > 0) { 
    printf( "tgt: %i\n", tgt );
    printf( "maxwgt: %i\n", maxwgt );
    printf( "num items: %i\n\n", n );
  }

  int profit = subsetsum( n, tgt, w, x, vlvl );

  init_bins++; // don't have to recount profit bin
  print_solution(profit,&profit,n,1,NULL/*p*/,w,x,&c,vlvl);
  if (vlvl == 1) print_bin_weights( &profit, n, 1, w, x, 2);

  pfree(w);
  pfree(x); 
  return profit;
} // test_batch__subsetsum



#ifdef false
#ifdef __cplusplus

// Satisfiability Tester (for only up to 32 variables if SAT32 is defined)
class TestSatisfiability
{
 public:
#ifdef SAT32
  unsigned long *c; // array of longs
#else
  char     **c;         // 2D matrix of chars
  ttype    **t;         // 2D matrix of integers
#endif
  int m; // number of clauses
  int vlvl;

 TestSatisfiability(int _vlvl = 1) : c(NULL), m(0), vlvl(_vlvl) {}
  ~TestSatisfiability() { dispose(); }

  void dispose()
  {
    if (vlvl > 3) printf( "dispose\n" );
    if (c) {
#ifdef SAT32
#else
      table_dispose();

      for ( int i = 0; i < m; i++ )
        free(c[i]);
#endif
      free(c);
      c = NULL;
    }
  }

  bool init(int _m, int n)
  {
    if (vlvl > 3) printf( "init\n" );
    m = _m;
    clauses_create(n);
    clauses_fill(n);
#ifdef SAT32
#else
    if (! table_create(n))
      return false;

    return table_fill(n);
#endif
  }

  unsigned long random_long32(int max)
  {
    unsigned long a1 = random_int(max,0);
    unsigned long a2 = random_int(max,0);
    return( a1 + a2 );
  }

  unsigned long n_bit_mask(int n)
  {
    signed long l = ~0;
    return ~(l << n);
  }


#ifdef SAT32
  void random_clause_create(unsigned long *c1, unsigned long *c2, int n)
  {
    if (vlvl > 3) printf( "random_clause_create (long *)\n" );
    unsigned long orig = 0;
    unsigned long mask = n_bit_mask(n);

    while (!(orig & mask)) {
      orig = random_long32(RAND_MAX);
    }
    unsigned long randmask = random_long32(RAND_MAX);
    *c1 = orig &  randmask;
    *c2 = orig & ~randmask;
  }
#else
  void random_clause_create( char *c1, char *c2, int n)
  {
    if (vlvl > 3) printf( "random_clause_create (char *)\n" );
    unsigned long orig = 0;
    unsigned long mask = n_bit_mask(n);

    while (!(orig & mask)) {
      orig = random_long32(RAND_MAX);
    }
    unsigned long randmask = random_long32(RAND_MAX);
    unsigned long v1 = orig &  randmask;
    unsigned long v2 = orig & ~randmask;

    if (vlvl > 3) printf( "v1:\n" );
    if (vlvl > 3) printf( "v2:\n" );

    for ( int i = 0; i < n; i++ ) {
      c1[i] = ((1<<i) & v1) > 0;
      c2[i] = ((1<<i) & v2) > 0;
    }
  }
#endif

  bool clauses_fill(int n)
  {
    if ( m < 1 ) return false;
    assert(c);
    if (vlvl > 3) printf( "clauses_fill\n" );

    for ( int i = 0; i < m; i++ )
#ifdef SAT32
      random_clause_create(c + i*2, c + i*2 + 1, n);
#else
    random_clause_create(c[i*2], c[i*2 + 1], n);
#endif

    return true;
  }
  bool clauses_create(int n)
  {
    if (c) dispose();
    if (vlvl > 3) printf( "clauses_create\n" );
#ifdef SAT32
    c = (unsigned long *)calloc(m*2,sizeof(unsigned long));
#else
    c = (char **)calloc(m*2,sizeof(char *));

    for ( int i = 0; i < m*2; i++ )
      c[i] = (char *)calloc(n,sizeof(char));
#endif
    return( c ? true : false );
  }
  void dump_clause(int i, int n)
  {
    if (!c) return;
    if (i >= m) return;
    printf( "clause %i\n", i );
#ifdef SAT32
    hexdump((char *)(c + 2*i), 8, stdout,1);
#else
    for ( int s = 0; s < 2; s++ ) {
      char *v = c[i*2 + s];
      for ( int i = 0; i < n; i++ )
        printf( "%3i", v[i] );

      printf( "\n" );
    }

    printf( "\n" );
#endif
  }
  void clauses_dump(int n)
  {
    if ( m < 1 ) return;
    assert(c);

    for ( int i = 0; i < m; i++ )
      dump_clause(i,n);
  }

#ifdef SAT32
#else
  ttype table(int r,int v)
  {
    ttype *p = t[r];
    return p[v];
  }
  bool table_create(int n)
  {
    if (vlvl > 3) printf( "table_create\n" );

    t = (ttype **)calloc(m, sizeof(void *));
    if (!t) return false;

    for (int i = 0; i < m; i++) {
      t[i] = (ttype *)calloc(n, sizeof(ttype));
      if ( !t[i] ) 
        return table_dispose();
    }

    return true;
  }
  bool table_dispose()
  {
    if (!t) return false;

    if (vlvl > 3) printf( "table_dispose\n" );

    for (int i = 0; i < m; i++) {
      if (!t[i])
        break;
      free(t[i]);
    }

    free(t);
    t = NULL;
    return false;
  }
  bool table_fill(int n)
  {
    assert(t);
    assert(c);
    if ( m < 1 || n < 1 ) return false;

    if (vlvl > 3) printf( "table_fill\n" );

    for ( int i = 0; i < m; i++ ) {
      for ( int j = 0; j < 2; j++ ) {
        for ( int k = 0; k < n; k++ ) {
          int bitset = c[i*2+j][k];
          if ( bitset ) {
            t[i][k] = ( !j ? 1 : -1 );
            if (vlvl > 3) printf( "i: %i k: %i sign: %i t_i_k: %i\n", i,k,j,t[i][k] );
          }
          else if (!j)
            t[i][k] = 0;
        }
        //hexdump((char *)(&(t[i][0])), 9*sizeof(int), stdout,1);
      }
    }

    return true;
  }
  void table_dump(int n)
  {
    assert(t);
    if ( m < 1 || n < 1 ) return;

    printf("TABLE\n");

    for ( int i = 0; i < m; i++ ) {
      printf("%4i:  ",i);
      for ( int k = 0; k < n; k++ ) {
        if ( ! (k % 4) )
          printf("  ");
        printf( "%3i",	t[i][k] );
      }
      printf("\n");
    }

    printf("\n");
  }
#endif


  bool test(int n, int _m)
  {
    if (vlvl > 3) printf( "test\n" );
    init(_m,n);
#ifdef SAT32
    unsigned long v;

    Satisfiability algorithm(n,vlvl);
    int r = algorithm.solve(_m,c,&v);
#else
    char *x = (char *)calloc(n,sizeof(char));
    int r = sat( n, _m, t, x, vlvl);
#endif
    if (r > 0) {
      if (vlvl > 0) printf("solution FOUND!\n");
    }
    else {
      if (vlvl > 0) printf("solution not found\n");
    }
    if (vlvl > 0) printf("(num vars: %i)\n",n);
    if (vlvl > 1) {
      printf("solution vector:\n");
#ifdef SAT32
      hexdump((char *)&v, 4, stdout,1);
#else
      for (int i = 0; i < n; i++)
        printf( "%3i", x[i] );

      printf( "\n\n" );
#endif
      if (vlvl > 1) table_dump(n);
      if (vlvl > 3) {
        clauses_dump(n);
      }
    }
#ifdef SAT32
#else
    free(x);
#endif
    return r;
  }
}; // TestSatisfiability

#endif //__cplusplus
#endif // false
#endif //TEST












#undef MAIN
#ifdef MAIN
#ifdef __cplusplus
static int run()
{
  TestSatisfiability t(2);

  for (int n = 18; n < 19; n++ ) {
    if (t.test(n,1532))
      return 1;
    printf("------------------------------------------------------------------------\n");
  }
  return 0;
  /*
    return test_batch__symmetric_subsum(
    120000, //int n
    2,      //int m
    32700,  //int cap
    1       //int vlvl
    );

    return 0;

    test_batch__subsetsum(
    20, //int n
    15, //int maxwgt
    27, //int tgt
    2 ); //int vlvl

    return 0;


    test_interactive__symmetric_subsum();
    return 0;
    return test_interactive__subset_sum();
    return 0;
  */
}





// run stand-alone (and test).
int main( int argc, char **argv )
{
  try {
    return run();
  }
  catch (std::exception &e) {
    fprintf(stderr, "### %s\n", e.what() );
  }
} // main
#endif
#endif // MAIN

