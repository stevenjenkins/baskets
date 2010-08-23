// ruby interface code
//  Author: Lou Vanek, vanek at acd dot net
// License: Same as Ruby
//    Date: 2/6/2006

#include "ruby.h"
#include <assert.h>



#define MAX(x,y) ((x>y)?(x):(y))
char *fmt(char *fmt, ...);
typedef signed char   ttype;  
int mulknap(int, int, int *, int *, int *, int *);
int symmetric_subsum(int, int, int, int, int *, int *, int *, int *, int);
int subsetsum(int, int, int *, int *, int);

// first, some utilities
static void bin_prnt_byte(unsigned char x)
{
	int n;
   	for(n=0; n<8; n++) {
	  printf ( "%c", (x & (1<<n)) ? '1' : '0' );
      if (n==3)
         printf(" "); /* insert a space between nibbles */
   }
}
static int hexdump( char *src, int sz, FILE *fp, int dump_binary )
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



		typedef struct 
		{
			ttype **t;
			int   vlvl;

			int n;
			int m;
		} Table;


		int table_dispose(Table *self)
		{
			if (!self->t) return 0;

			if (self->vlvl > 3) printf( "table_dispose\n" );
			int i;
			for (i = 0; i < self->m; i++) {
				if (!self->t[i])
					break;
				free(self->t[i]);
			}

			free(self->t);
			self->t = NULL;
			return 0;
		}
		int table_reserve(Table *self,int n)
		{
			if (self->vlvl > 3) printf( "table_reserve\n" );

			self->t = (ttype **)calloc(self->m, sizeof(void *));
			if (!self->t) return 0;
			int i;
			for (i = 0; i < self->m; i++) {
				self->t[i] = (ttype *)calloc(n, sizeof(ttype));
				if ( !self->t[i] ) 
					return table_dispose(self);
			}

			return 1;
		}
		void table_init(Table *self, int n_,int m_) {
			self->vlvl = 0; 
			self->n = n_;
		   	self->m = m_; 
			table_reserve(self, self->n); 
		}
		Table *table_create(int n, int m)
		{
			Table *self = (Table *)calloc(1,sizeof(Table));
			table_init(self,n,m);
			return self;
		}


		int table_set(Table *self,int r, int c, int v)
		{
			assert(self->t);
			if ( self->m < 1 || self->n < 1 ) return 0;

			if (v > 0)
				v = 1;
			else if (v < 0)
				v = -1;
			self->t[r][c] = v;
			return 1;
		}
		int table_dump(Table *self)
		{
			assert(self->t);
			if ( self->m < 1 || self->n < 1 ) return 0;

			int i, j;
			for ( i = 0; i < self->m; i++ )
				for ( j = 0; j < self->n; j++ )
					printf( "%2i ", self->t[i][j] );

			return 1;
		}



	typedef struct {
		char *data;
		int   n;
	} CVector;


	char *cvector_reserve(CVector *self)
	{
		self->data = (char *)calloc(self->n, sizeof(char));
		return self->data;
	}
	CVector *cvector_create(int n) 
	{
		CVector *self = (CVector *)calloc(1,sizeof(CVector));
		self->n = n;
		cvector_reserve(self);
		return self;
	}

	void cvector_dispose(CVector *self)
	{
		if (!self->data) return;
		free(self->data);
		self->data = NULL;
	}
	char cvector(CVector *self,int idx) 
	{
		if (!self->data || self->n < 1 || idx >= self->n )
			return 0;
		return self->data[idx];
	}




static int validate_ruby_numeric_array_range(VALUE ary, long upper_bound)
{
	int alr = RARRAY(ary)->len;
	int i;
	VALUE e;
	int r;
	int n = 0;

    for ( i = 0; i < alr; i++ ) {
		e = rb_ary_entry(ary, i);
		if (NIL_P(e))
			continue; // skip nil
		if (!FIXNUM_P(e))
			rb_raise(rb_eArgError, "array entries must all be fixnums");
		r = FIX2LONG(e);
		if (r >= upper_bound) {
			rb_warning("array entries shouldn't be greater than %i",upper_bound-1);
			n++;
		}
    }

	return n;
}


static int validate_c_numeric_array_range(int *ary, int n, long upper_bound)
{
	int i;
	int c = 0;

    for ( i = 0; i < n; i++ ) {
		if (ary[i] >= upper_bound) {
			rb_warning("array entries shouldn't be greater than %i",upper_bound-1);
			c++;
		}
    }

	return c;
}

// SUBSET-SUM -- Ruby
// this is the ruby-to-C interface to the SUBSET-SUM algorithm.
static VALUE
np_subsetsum(VALUE self, VALUE ary_values, VALUE tgt)
{
	int n, nl, i, r, tgtsum, vlvl = 0;
	n = 0;
	VALUE c;

	if(vlvl>3)fprintf(stderr, "np_subsetsum\n");
	// is 'ary_values' really an array?
	VALUE a = rb_check_array_type(ary_values);
	if (NIL_P(a))
		rb_raise(rb_eArgError, "set of numbers not defined (or not an array of numbers)");

	if(vlvl>3)fprintf(stderr, "np_sss: a: %x\n",a);
	// length of ary_values indicates 'n'
	nl = RARRAY(a)->len;

	// determine n, and validate each table entry (must be a Fixnum).
    for ( i = 0; i < nl; i++ ) {
		c = rb_ary_entry(a, i);
		if (NIL_P(c))
			continue; // skip nil
		if (!FIXNUM_P(c))
			rb_raise(rb_eArgError, "numbers-to-sum must all be fixnums");
		n++;
    }

	if(vlvl>3)fprintf(stderr, "np_sss: n: %i\n",n);

	// what should all the input numbers add up to?
	tgtsum = (int)NUM2LONG(tgt);

	int *t = (int *)calloc(n,sizeof(int));

	r = 0;

	// create a C vector representation of what is in ary_values
    for ( i = 0; i < nl; i++ ) {
		c = rb_ary_entry(a, i);
		if (!NIL_P(c)) {
			t[r] = FIX2LONG(c);
			if(vlvl>3)fprintf(stderr, "np_sss:table_set: %i/%i  %i\n", i, r, FIX2LONG(c));
			r++;
		}
    }

	validate_c_numeric_array_range(t, r, (1<<15)/*upper_bound*/);

	int *x = (int *)calloc(n,sizeof(int));

	if(vlvl>3)fprintf(stderr, "np_sss:r: %i n: %i tgt: %i\n",r,n,tgtsum);

	// call the C algorithm (in libnp.a, file mulknap.c)
	r = subsetsum( n,
			tgtsum,
			t,   //int *w
			x,   //int *x
			0);  //int vlvl

	if(vlvl>3)fprintf(stderr, "np_sss:post call: r: %i\n",r);
	free(t); t = NULL;

	// return result: an array of three elements:
	// 1. true/false, is there a subset that sums to the target number?
	// 2. array of Fixnums, 0 or 1, indicating whether number is included in the subset or not.
	// 3. r (either equal to tgtsum or the largest subsum up to tgtsum

	VALUE result = rb_ary_new2(3); // the return array
	VALUE      v = rb_ary_new2(n);

	if(vlvl>3)fprintf(stderr, "np_sss:ary_push\n");

	for (i=0; i<n; i++) {
		rb_ary_push(v, INT2FIX(x[i]));
		if(vlvl>3)fprintf(stderr, "np_sss:cvector: %i %i\n",x[i],i);
	}

	free(x); x = NULL;

	rb_ary_push(result, r==tgtsum ? Qtrue : Qfalse );
	rb_ary_push(result, v);
	rb_ary_push(result, INT2FIX(r));
	if(vlvl>3)fprintf(stderr, "np_sss:return\n");
	return result;

} // np_subsetsum



// SYMMETRIC SUBSET-SUM - Ruby
// this is the ruby-to-C interface to the SYMMETRIC SUBSET-SUM algorithm.
static VALUE
np_symsubsum(VALUE self, VALUE ary_values, VALUE num_partitions)
{
	int n, nl, i, r, p, vlvl = 0;
	n = 0;
	VALUE c;

	if(vlvl>3)fprintf(stderr, "np_symsubsum\n");
	// is 'ary_values' really an array?
	VALUE a = rb_check_array_type(ary_values);
	if (NIL_P(a))
		rb_raise(rb_eArgError, "set of numbers not defined (or not an array of numbers)");

	if(vlvl>3)fprintf(stderr, "np_sym: a: %x\n",a);
	// length of ary_values indicates 'n'
	nl = RARRAY(a)->len;

	// determine n, and validate each table entry (must be a Fixnum).
    for ( i = 0; i < nl; i++ ) {
		c = rb_ary_entry(a, i);
		if (NIL_P(c))
			continue; // skip nil
		if (!FIXNUM_P(c))
			rb_raise(rb_eArgError, "numbers-to-sum must all be fixnums");
		r = FIX2LONG(c);
		if (!r)
			rb_raise(rb_eArgError, "numbers cannot be 0");
		n++;
    }

	if(vlvl>3)fprintf(stderr, "np_sym: n: %i\n",n);

	// how many partitions should there be?
	p = (int)NUM2LONG(num_partitions);

	if ( p < 1 || n < 1 ) { // trivial result
		VALUE result = rb_ary_new2(2); // the return array
		VALUE     rb = rb_ary_new(); // an empty array of bin weights
		VALUE     rx = rb_ary_new(); // an empty array indicating which bin each number is placed in

		rb_ary_push(result, rb);
		rb_ary_push(result, rx);
		return result;
	}

	int *w = (int *)calloc(n,sizeof(int));

	r = 0;

	// create a C vector representation of what is in ary_values
    for ( i = 0; i < nl; i++ ) {
		c = rb_ary_entry(a, i);
		if (!NIL_P(c)) {
			w[r] = FIX2LONG(c);
			if(vlvl>3)fprintf(stderr, "np_sym:w: %i/%i  %i\n", i, r, FIX2LONG(c));
			r++;
		}
    }

	validate_c_numeric_array_range(w, r, (1<<15)/*upper_bound*/);

	int *x = (int *)calloc(n,sizeof(int));

	if(vlvl>3)fprintf(stderr, "np_sym:r: %i n: %i p: %i\n",r,n,p);

	int *v = (int *)calloc(n,sizeof(int)); // value of each item
	int  lower = 0;
	int  upper = 0;
	int *bin = (int *)calloc(p,sizeof(int));

	for ( i = 0; i < n; i++ ) {
		// initialize all arrays
		v[i]  = 1;
		x[i]  = 0;

		lower = MAX( lower, w[i] );
		upper = upper + w[i];
	}

	if (vlvl > 0) { 
		printf( "\nnum bins: %i\n", v );
		printf(   "num items: %i\n\n", n );
	}

	symmetric_subsum(lower,  // lower bounds on which to search
			upper, 
			n, 
			p,   // num partitions
			v,   // int *values/profits/costs
			w,   // int *weights
			x,   // int *partition to place in
			bin, // int *bin weights
			0);  //int vlvl

	free(v); v = NULL;
	free(w); w = NULL;
	if(vlvl>3)fprintf(stderr, "np_sym:post call\n");

	// return result: an array of two elements:
	// 1. array of weights of each bin (i.e. partition)
	// 2. array of Fixnums specifying which bin the item is placed in (base 1)

	VALUE result = rb_ary_new2(2); // the return array
	VALUE     rb = rb_ary_new2(p); // the array of bin weights
	VALUE     rx = rb_ary_new2(n); // the array indicating which bin each number is placed in

	if(vlvl>3)fprintf(stderr, "np_sym:ary_push\n");

	for (i=0; i<n; i++) {
		rb_ary_push(rx, INT2FIX(x[i]));
		if(vlvl>3)fprintf(stderr, "np_sym:x_i: %i %i\n",x[i],i);
	}

	free(x); x = NULL;

	for (i=0; i<p; i++) {
		rb_ary_push(rb, INT2FIX(bin[i]));
	}

	free(bin); bin = NULL;

	rb_ary_push(result, rb);
	rb_ary_push(result, rx);
	if(vlvl>3)fprintf(stderr, "np_sym:return\n");
	return result;

} // np_symsubsum








static VALUE valid_array_type(VALUE ary, char *warn_msg)
{
	VALUE w = rb_check_array_type(ary);
	if (NIL_P(w))
		rb_raise(rb_eArgError, warn_msg);
	return w;
}

static int validate_numeric_array(VALUE ary)
{
	int alr = RARRAY(ary)->len;
	int i;
	VALUE e;
	int r;
	int n = 0;

	// determine n, and validate each table entry (must be a Fixnum).
    for ( i = 0; i < alr; i++ ) {
		e = rb_ary_entry(ary, i);
		if (NIL_P(e))
			continue; // skip nil
		if (!FIXNUM_P(e))
			rb_raise(rb_eArgError, "array entries must all be fixnums");
		r = FIX2LONG(e);
		if (!r)
			rb_raise(rb_eArgError, "array entries cannot be 0");
		n++;
    }

	return n;
}


static int *copy_ruby_array_entries_to_c(VALUE ary, int sz)
{
	int r = 0;
	int i;
	VALUE c;

	int *a = (int *)calloc(sz, sizeof(int));

	// create a C vector representation of what is in ruby array ary
    for ( i = 0; i < sz; i++ ) {
		c = rb_ary_entry(ary, i);
		if (!NIL_P(c)) {
			a[r] = FIX2LONG(c);
			r++;
		}
    }

	return a;
}


static int compare_asc(const void * a, const void * b)
{
  return ( *(int*)a - *(int*)b );
}

static int compare_desc(const void * a, const void * b)
{
  return ( *(int*)b - *(int*)a );
}


static void sort_integers(int *a, int n)
{
	// make sure the capacities are sorted from low to high
	if (n < 2)
		; // do nothing, list is already sorted
	else if (n < 3) { // only 2 knapsacks
		if (a[0] > a[1]) { // need to swap knapsack capacities
			// swap
			int t = a[0];
			a[0]  = a[1];
			a[1]  = t;
		}
	}
	else { // use qsort on all arrays with length 3+
		qsort (a, n, sizeof(int), compare_asc);
	}
}



// MULTIPLE KNAPSACK 0-1 - Ruby
// this is the ruby-to-C interface to the MULTIPLE KNAPSACK 0-1 algorithm.
static VALUE
np_mulknap(VALUE self, VALUE ary_weights, VALUE ary_profits, VALUE ary_capacities)
{
	int   wl , pl , cl; 
	int   wlr, plr, clr;
	int   i  , r  , vlvl = 0;
	VALUE w  , p  , c;

	if(vlvl>3)fprintf(stderr, "np_mulknap\n");
	// is 'ary_weights' really an array?
	w = valid_array_type(ary_weights, 
			"weight array not defined (or not an array of numbers)");
	p = valid_array_type(ary_profits, 
			"profit array not defined (or not an array of numbers)");
	c = valid_array_type(ary_capacities, 
			"knapsack capacities array not defined (or not an array of numbers)");

	if(vlvl>3)fprintf(stderr, "np_knap: w: %x\n",w);
	// length of arrays
	wlr = RARRAY(w)->len;
	plr = RARRAY(p)->len;
	clr = RARRAY(c)->len;

	wl = validate_numeric_array(w); // or throw a ruby exception if a problem is found
	pl = validate_numeric_array(p);
	cl = validate_numeric_array(c);

	if (pl != wl )
		rb_warn("arrays are not all the same length (or have invalid values [nil or 0])");

	if(vlvl>3)fprintf(stderr, "np_knap: wl: %i pl: %i cl: %i\n",wl,pl,cl);

	int *wc = copy_ruby_array_entries_to_c(w, wlr);
	int *pc = copy_ruby_array_entries_to_c(p, wlr);
	int *cc = copy_ruby_array_entries_to_c(c, wlr);

	validate_c_numeric_array_range(wc, wl, (1<<15)/*upper_bound*/);
	validate_c_numeric_array_range(pc, pl, (1<<15)/*upper_bound*/);

	sort_integers(cc, cl);

	if (vlvl>3) {
		hexdump( (char *)wc, -1 + sizeof(int)*wl, stdout, 1 );
		hexdump( (char *)pc, -1 + sizeof(int)*wl, stdout, 1 );
		hexdump( (char *)cc, -1 + sizeof(int)*cl, stdout, 1 );
	}

	int *x = (int *)calloc(wl,sizeof(int));

	// the core algorithm call
	int profit = mulknap(wl, cl, pc, wc, x, cc);

	if (vlvl>3) hexdump( (char *)x, -1 + sizeof(int)*wl, stdout, 1 );

	if(vlvl>3)fprintf(stderr, "np_knap:post call: profit: %i\n",profit);

	// return result: an array of three elements:
	// 1. total profit that can be carried in knapsacks
	// 2. array of Fixnums, (0+), indicating which knapsack the item is placed in (if any)
	// 3. array of knapsack capacities, sorted from low to high

	VALUE result = rb_ary_new2(3);  // the return array
	VALUE     rx = rb_ary_new2(wl); // the array indicating which bin each number is placed in
		// if an item is not included in any knapsack, the value in this array will be 0.
	VALUE     cs = rb_ary_new2(cl); // the array of capacities (sorted from lo to hi)

	for (i=0; i<wl; i++) {
		rb_ary_push(rx, INT2FIX(x[i]));
		if(vlvl>3)fprintf(stderr, "np_knap:x_i: %i %i\n",x[i],i);
	}
	for (i=0; i<cl; i++) {
		rb_ary_push(cs, INT2FIX(cc[i]));
	}

	// determine whether the knapsack capacities had to be sorted.
	// If so, issue a warning if -W is specified on command line.
	VALUE j = rb_ary_cmp(cs,c);
	if (FIX2INT(j))
		rb_warning("the knapsacks had to be resorted from lowest to highest capacity.\n\
This effects the result returned.");

	free(wc); wc = NULL;
	free(pc); pc = NULL;
	free(cc); cc = NULL;
	free( x);  x = NULL;

	// total profit of all items that were placed in knapsacks
	rb_ary_push(result, INT2FIX(profit)); 
	// 2nd return param is array indicating which knapsack each item is placed in
	rb_ary_push(result, rx); 
	// 3rd return param is sorted knapsack capacities
	rb_ary_push(result, cs); 
	if(vlvl>3)fprintf(stderr, "np_knap:return\n");
	return result;

} // np_mulknap




// single "NP" module.
VALUE rb_mNP;
	
// Ruby extension initialization code
void
Init_NP()
{
	int vlvl = 0;
	if(vlvl>3)fprintf(stderr, "Init_NP\n");
    rb_mNP = rb_define_module("NP");

	rb_define_module_function(rb_mNP, "subset_sum", (VALUE(*)(ANYARGS))np_subsetsum, 2);
	rb_define_module_function(rb_mNP, "symmetric_subset_sum", (VALUE(*)(ANYARGS))np_symsubsum, 2);
	rb_define_module_function(rb_mNP, "mulknap", (VALUE(*)(ANYARGS))np_mulknap, 3);
	rb_define_const(rb_mNP, "VERSION", rb_float_new(1.000));
	if(vlvl>3)fprintf(stderr, "Init_NP:end\n");
}



