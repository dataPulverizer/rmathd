module choose;

import common;
import beta;


/*
** dmd choose.d common.d beta.d && ./choose
*/


T lfastchoose(T)(T n, T k)
{
    return -log(n + 1.) - lbeta!T(n - k + 1., k + 1.);
}


/* mathematically the same:
   less stable typically, but useful if n-k+1 < 0 : */
static T lfastchoose2(T)(T n, T k, int *s_choose)
{
    T r;
    r = lgammafn_sign(n - k + 1., s_choose);
    return lgammafn(n + 1.) - lgammafn(k + 1.) - r;
}


template ODD(T){
	T ODD(T k){
		return (k != 2 * floor(k/2.0));
	}
}


T lchoose(T)(T n, T k)
{
    T k0 = k;
    k = nearbyint(k);
    
    /* NaNs propagated correctly */
    if(isNaN(n) || isNaN(k))
    	return n + k;
    
    if (fabs(k - k0) > 1e-7){
	    //MATHLIB_WARNING2(_("'k' (%.2f) must be integer, rounded to %.0f"), k0, k);
	    doNothing();
    }
    
    if (k < 2) {
	    if (k <	 0)
	    	return -T.infinity;
	    if (k == 0)
	    	return 0.;
	    /* else: k == 1 */
	    return log(fabs(n));
    }
    /* else: k >= 2 */
    if (n < 0) {
	    return lchoose!T(-n + k - 1, k);
    } else if (!R_nonint(n)) {
	    n = nearbyint(n);
	    if(n < k)
	    	return -T.infinity;
	    /* k <= n :*/
	    if(n - k < 2)
	    	return lchoose!T(n, n - k); /* <- Symmetry */
	    /* else: n >= k+2 */
	    return lfastchoose!T(n, k);
    }
    /* else non-integer n >= 0 : */
    if (n < k - 1) {
	    int s;
	    return lfastchoose2!T(n, k, &s);
    }
    return lfastchoose!T(n, k);
}


enum k_small_max = 30;
/* 30 is somewhat arbitrary: it is on the *safe* side:
 * both speed and precision are clearly improved for k < 30.
*/


T choose(T)(T n, T k)
{
    T r, k0 = k;
    k = nearbyint(k);
    
    /* NaNs propagated correctly */
    if(isNaN(n) || isNaN(k))
    	return n + k;
    
    if (fabs(k - k0) > 1e-7){
	    //MATHLIB_WARNING2(_("'k' (%.2f) must be integer, rounded to %.0f"), k0, k);
	    doNothing();
    }

    if (k < k_small_max) {
	    int j;
	    if(n - k < k && n >= 0 && !R_nonint(n))
	    	k = n - k; /* <- Symmetry */
	    if (k <	 0)
	    	return 0.;
	    if (k == 0)
	    	return 1.;
	    /* else: k >= 1 */
	    r = n;
	    for(j = 2; j <= k; j++)
	        r *= (n - j + 1)/j;
	    return !R_nonint(n) ? nearbyint(r) : r;
	    /* might have got rounding errors */
    }
    /* else: k >= k_small_max */
    if (n < 0) {
	    r = choose!T(-n + k - 1, k);
	    if (ODD!T(k)) r = -r;
	    return r;
    }
    else if (!R_nonint(n)) {
	    n = nearbyint(n);
	    if(n < k)
	    	return 0.;
	    if(n - k < k_small_max)
	    	return choose!T(n, n - k); /* <- Symmetry */
	    return nearbyint(exp(lfastchoose!T(n, k)));
    }
    /* else non-integer n >= 0 : */
    if (n < k - 1) {
	    int s_choose;
	    r = lfastchoose2(n, k, /* -> */ &s_choose);
	    return s_choose * exp(r);
    }
    return exp(lfastchoose!T(n, k));
}


void test_choose()
{
	import std.stdio: writeln;
	writeln("choose(7., 4.): ", choose(7., 4.));
	writeln("lchoose(7., 4.): ", lchoose(7., 4.));
}

