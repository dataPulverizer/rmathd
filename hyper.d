module hyper;

import common;
import choose;
import binomial;


/* 
** normal.d poisson.d exponential.d
** dmd hyper.d common.d choose.d binomial.d && ./hyper
*/


T dhyper(T)(T x, T r, T b, T n, int give_log)
{
    T p, q, p1, p2, p3;
    
    mixin R_D__0!give_log;
    mixin R_D__1!give_log;
    if (isNaN(x) || isNaN(r) || isNaN(b) || isNaN(n))
	    return x + r + b + n;

    if (R_D_negInonint!T(r) || R_D_negInonint!T(b) || R_D_negInonint!T(n) || n > r + b)
	    return T.nan;
    if(x < 0)
    	return(R_D__0);
    mixin (R_D_nonint_check!(x));// incl warning

    x = nearbyint(x);
    r = nearbyint(r);
    b = nearbyint(b);
    n = nearbyint(n);

    if (n < x || r < x || n - x > b)
    	return R_D__0;
    if (n == 0)
    	return((x == 0) ? R_D__1 : R_D__0);

    p = (cast(T)n)/(cast(T)(r + b));
    q = (cast(T)(r + b - n))/(cast(T)(r + b));

    p1 = dbinom_raw!T(x,	r, p, q, give_log);
    p2 = dbinom_raw!T(n - x, b, p, q, give_log);
    p3 = dbinom_raw!T(n, r + b, p, q, give_log);

    return( (give_log) ? p1 + p2 - p3 : p1*p2/p3 );
}


static T pdhyper(T)(T x, T NR, T NB, T n, int log_p)
{
/*
 * Calculate
 *
 *	    phyper (x, NR, NB, n, TRUE, FALSE)
 *   [log]  ----------------------------------
 *	       dhyper (x, NR, NB, n, FALSE)
 *
 * without actually calling phyper.  This assumes that
 *
 *     x * (NR + NB) <= n * NR
 *
 */
    real sum = 0;
    real term = 1;

    while (x > 0 && term >= DBL_EPSILON * sum) {
	    term *= x * (NB - n + x) / (n + 1 - x) / (NR + 1 - x);
	    sum += term;
	    x--;
    }
    
    T ss = cast(T) sum;
    return log_p ? log1p(ss) : 1 + ss;
}


/* FIXME: The old phyper() code was basically used in ./qhyper.c as well
 * -----  We need to sync this again!
*/
T phyper(T)(T x, T NR, T NB, T n, int lower_tail, int log_p)
{
    /* Sample of  n balls from  NR red  and	 NB black ones;	 x are red */
    
    T d, pd;
    
    if(isNaN(x) || isNaN(NR) || isNaN(NB) || isNaN(n))
	    return x + NR + NB + n;
    
    x = floor (x + 1e-7);
    NR = nearbyint(NR);
    NB = nearbyint(NB);
    n  = nearbyint(n);

    if (NR < 0 || NB < 0 || !isFinite(NR + NB) || n < 0 || n > NR + NB)
	    return T.nan;

    if (x * (NR + NB) > n * NR) {
	    /* Swap tails.	*/
	    T oldNB = NB;
	    NB = NR;
	    NR = oldNB;
	    x = n - x - 1;
	    lower_tail = !lower_tail;
    }
    
    if (x < 0)
	    return R_DT_0!T(lower_tail, log_p);
    if (x >= NR || x >= n)
	    return R_DT_1!T(lower_tail, log_p);
    
    d  = dhyper!T(x, NR, NB, n, log_p);
    pd = pdhyper!T(x, NR, NB, n, log_p);
    
    return log_p ? R_DT_Log!T(d + pd, lower_tail) : R_D_Lval!T(d*pd, lower_tail);
}


T qhyper(T)(T p, T NR, T NB, T n, int lower_tail, int log_p)
{
/* This is basically the same code as  ./phyper.c  *used* to be --> FIXME! */
    T N, xstart, xend, xr, xb, sum, term;
    int small_N;
    
    if (isNaN(p) || isNaN(NR) || isNaN(NB) || isNaN(n))
	    return p + NR + NB + n;
    
    if(!isFinite(p) || !isFinite(NR) || !isFinite(NB) || !isFinite(n))
	    return T.nan;

    NR = nearbyint(NR);
    NB = nearbyint(NB);
    N = NR + NB;
    n = nearbyint(n);
    if (NR < 0 || NB < 0 || n < 0 || n > N)
	    return T.nan;

    /* Goal:  Find  xr (= #{red balls in sample}) such that
     *   phyper(xr,  NR,NB, n) >= p > phyper(xr - 1,  NR,NB, n)
     */

    xstart = fmax2!T(0, n - NB);
    xend = fmin2!T(n, NR);

    mixin (R_Q_P01_boundaries!(p, xstart, xend));

    xr = xstart;
    xb = n - xr;/* always ( = #{black balls in sample} ) */

    small_N = (N < 1000); /* won't have underflow in product below */
    /* if N is small,  term := product.ratio( bin.coef );
       otherwise work with its logarithm to protect against underflow */
    term = lfastchoose!T(NR, xr) + lfastchoose!T(NB, xb) - lfastchoose!T(N, n);
    if(small_N)
    	term = exp(term);
    NR -= xr;
    NB -= xb;

    mixin R_DT_qIv!p;
    if(!lower_tail || log_p) {
	    p = R_DT_qIv;
    }
    p *= 1 - 1000*DBL_EPSILON; /* was 64, but failed on FreeBSD sometimes */
    sum = small_N ? term : exp(term);

    while(sum < p && xr < xend) {
	    xr++;
	    NB++;
	    if (small_N) term *= (NR / xr) * (xb / NB);
	    else term += log((NR / xr) * (xb / NB));
	    sum += small_N ? term : exp(term);
	    xb--;
	    NR--;
    }
    return xr;
}


static T afc(T)(int i)
{
    // If (i > 7), use Stirling's approximation, otherwise use table lookup.
    const static T[8] al = [
	    0.0,/*ln(0!)=ln(1)*/
	    0.0,/*ln(1!)=ln(1)*/
	    0.69314718055994530941723212145817,/*ln(2) */
	    1.79175946922805500081247735838070,/*ln(6) */
	    3.17805383034794561964694160129705,/*ln(24)*/
	    4.78749174278204599424770093452324,
	    6.57925121201010099506017829290394,
	    8.52516136106541430016553103634712
	    /* 10.60460290274525022841722740072165, approx. value below =
	       10.6046028788027; rel.error = 2.26 10^{-9}
        
	      FIXME: Use constants and if(n > ..) decisions from ./stirlerr.c
	      -----  will be even *faster* for n > 500 (or so)
	    */
    ];

    if (i < 0) {
	    //MATHLIB_WARNING(("rhyper.c: afc(i), i=%d < 0 -- SHOULD NOT HAPPEN!\n"), i);
	    return -1; // unreached
    }
    if (i <= 7)
	    return al[i];
    // else i >= 8 :
    T di = i, i2 = di*di;
    return (di + 0.5) * log(di) - di + M_LN_SQRT_2PI + (0.0833333333333333 - 0.00277777777777778 / i2) / di;
}


//     rhyper(NR, NB, n) -- NR 'red', NB 'blue', n drawn, how many are 'red'
T rhyper(T)(T nn1in, T nn2in, T kkin)
{
    /* extern double afc(int); */

    int nn1, nn2, kk;
    int ix; // return value (coerced to double at the very end)
    //Rboolean
    int setup1, setup2;

    /* These should become 'thread_local globals' : */
    static int ks = -1, n1s = -1, n2s = -1;
    static int m, minjx, maxjx;
    static int k, n1, n2; // <- not allowing larger integer par
    static T tn;

    // II :
    static T w;
    // III:
    static T a, d, s, xl, xr, kl, kr, lamdl, lamdr, p1, p2, p3;

    /* check parameter validity */

    if(!isFinite(nn1in) || !isFinite(nn2in) || !isFinite(kkin))
	    return T.nan;

    nn1in = nearbyint(nn1in);
    nn2in = nearbyint(nn2in);
    kkin  = nearbyint(kkin);

    if (nn1in < 0 || nn2in < 0 || kkin < 0 || kkin > nn1in + nn2in)
	    return T.nan;
    if (nn1in >= INT_MAX || nn2in >= INT_MAX || kkin >= INT_MAX) {
	    /* large n -- evade integer overflow (and inappropriate algorithms)
	       -------- */
            // FIXME: Much faster to give rbinom() approx when appropriate; -> see Kuensch(1989)
	    // Johnson, Kotz,.. p.258 (top) mention the *four* different binomial approximations
	    if(kkin == 1.) { // Bernoulli
	        return rbinom!T(kkin, nn1in / (nn1in + nn2in));
	    }
	    // Slow, but safe: return  F^{-1}(U)  where F(.) = phyper(.) and  U ~ U[0,1]
	    return qhyper!T(unif_rand!T(), nn1in, nn2in, kkin, 0, 0);
    }
    nn1 = cast(int)nn1in;
    nn2 = cast(int)nn2in;
    kk  = cast(int)kkin;

    /* if new parameter values, initialize */
    if (nn1 != n1s || nn2 != n2s) {
	    setup1 = 1;	setup2 = 1;
    } else if (kk != ks) {
	    setup1 = 0;	setup2 = 1;
    } else {
	    setup1 = 0;	setup2 = 0;
    }
    if (setup1) {
	    n1s = nn1;
	    n2s = nn2;
	    tn = nn1 + nn2;
	    if (nn1 <= nn2) {
	        n1 = nn1;
	        n2 = nn2;
	    } else {
	        n1 = nn2;
	        n2 = nn1;
	    }
    }
    if (setup2) {
	    ks = kk;
	    if (kk + kk >= tn) {
	        k = cast(int)(tn - kk);
	    } else {
	        k = kk;
	    }
    }
    if (setup1 || setup2) {
	    m = cast(int) ((k + 1.) * (n1 + 1.) / (tn + 2.));
	    minjx = imax2(0, k - n2);
	    maxjx = imin2(n1, k);
        //#ifdef DEBUG_rhyper
        //	REprintf("rhyper(nn1=%d, nn2=%d, kk=%d), setup: floor(mean)= m=%d, jx in (%d..%d)\n",
        //		 nn1, nn2, kk, m, minjx, maxjx);
        //#endif
    }
    /* generate random variate --- Three basic cases */

    if (minjx == maxjx) { /* I: degenerate distribution ---------------- */
        //#ifdef DEBUG_rhyper
        //	REprintf("rhyper(), branch I (degenerate)\n");
        //#endif
	    ix = maxjx;
	    goto L_finis; // return appropriate variate
        
    } else if (m - minjx < 10) { // II: (Scaled) algorithm HIN (inverse transformation) ----
	const static T scale = 1e25; // scaling factor against (early) underflow
	const static T con = 57.5646273248511421;
					  // 25*log(10) = log(scale) { <==> exp(con) == scale }
	if (setup1 || setup2) {
	    T lw; // log(w);  w = exp(lw) * scale = exp(lw + log(scale)) = exp(lw + con)
	    if (k < n2) {
		    lw = afc!T(n2) + afc!T(n1 + n2 - k) - afc!T(n2 - k) - afc!T(n1 + n2);
	    } else {
		    lw = afc!T(n1) + afc!T(     k     ) - afc!T(k - n2) - afc!T(n1 + n2);
	    }
	    w = exp(lw + con);
	}
	T p, u;
    //#ifdef DEBUG_rhyper
    //	REprintf("rhyper(), branch II; w = %g > 0\n", w);
    //#endif
      L10:
	p = w;
	ix = minjx;
	u = unif_rand!T() * scale;
    //#ifdef DEBUG_rhyper
    //	REprintf("  _new_ u = %g\n", u);
    //#endif
	    while (u > p) {
	        u -= p;
	        p *= (cast(T) n1 - ix) * (k - ix);
	        ix++;
	        p = p / ix / (n2 - k + ix);
        //#ifdef DEBUG_rhyper
        //	    REprintf("       ix=%3d, u=%11g, p=%20.14g (u-p=%g)\n", ix, u, p, u-p);
        //#endif
	        if (ix > maxjx)
	    	    goto L10;
	        // FIXME  if(p == 0.)  we also "have lost"  => goto L10
	    }
    } else { /* III : H2PE Algorithm --------------------------------------- */

	T u,v;

	if (setup1 || setup2) {
	    s = sqrt((tn - k) * k * n1 * n2 / (tn - 1) / tn / tn);

	    /* remark: d is defined in reference without int. */
	    /* the truncation centers the cell boundaries at 0.5 */

	    d = cast(int) (1.5 * s) + .5;
	    xl = m - d + .5;
	    xr = m + d + .5;
	    a = afc!T(m) + afc!T(n1 - m) + afc!T(k - m) + afc!T(n2 - k + m);
	    kl = exp(a - afc!T(cast(int) (xl)) - afc!T(cast(int) (n1 - xl))
		     - afc!T(cast(int) (k - xl))
		     - afc!T(cast(int) (n2 - k + xl)));
	    kr = exp(a - afc!T(cast(int) (xr - 1))
		     - afc!T(cast(int) (n1 - xr + 1))
		     - afc!T(cast(int) (k - xr + 1))
		     - afc!T(cast(int) (n2 - k + xr - 1)));
	    lamdl = -log(xl * (n2 - k + xl) / (n1 - xl + 1) / (k - xl + 1));
	    lamdr = -log((n1 - xr + 1) * (k - xr + 1) / xr / (n2 - k + xr));
	    p1 = d + d;
	    p2 = p1 + kl / lamdl;
	    p3 = p2 + kr / lamdr;
	}
    //#ifdef DEBUG_rhyper
    //	REprintf("rhyper(), branch III {accept/reject}: (xl,xr)= (%g,%g); (lamdl,lamdr)= (%g,%g)\n",
    //		 xl, xr, lamdl,lamdr);
    //	REprintf("-------- p123= c(%g,%g,%g)\n", p1,p2, p3);
    //#endif
	int n_uv = 0;
      L30:
	u = unif_rand!T() * p3;
	v = unif_rand!T();
	n_uv++;
	if(n_uv >= 10000) {
	    //REprintf("rhyper() branch III: giving up after %d rejections", n_uv);
	    return T.nan;
    }
    //#ifdef DEBUG_rhyper
    //	REprintf(" ... L30: new (u=%g, v ~ U[0,1])[%d]\n", u, n_uv);
    //#endif

	if (u < p1) {		/* rectangular region */
	    ix = cast(int) (xl + u);
	} else if (u <= p2) {	/* left tail */
	    ix = cast(int) (xl + log(v) / lamdl);
	    if (ix < minjx)
		goto L30;
	    v = v * (u - p1) * lamdl;
	} else {		/* right tail */
	    ix = cast(int) (xr - log(v) / lamdr);
	    if (ix > maxjx)
		goto L30;
	    v = v * (u - p2) * lamdr;
	}

	/* acceptance/rejection test */
	//Rboolean
	int reject = 1;

	if (m < 100 || ix <= 50) {
	    /* explicit evaluation */
	    /* The original algorithm (and TOMS 668) have
		   f = f * i * (n2 - k + i) / (n1 - i) / (k - i);
	       in the (m > ix) case, but the definition of the
	       recurrence relation on p134 shows that the +1 is
	       needed. */
	    int i;
	    T f = 1.0;
	    if (m < ix) {
		for (i = m + 1; i <= ix; i++)
		    f = f * (n1 - i + 1) * (k - i + 1) / (n2 - k + i) / i;
	    } else if (m > ix) {
		for (i = ix + 1; i <= m; i++)
		    f = f * i * (n2 - k + i) / (n1 - i + 1) / (k - i + 1);
	    }
	    if (v <= f) {
		reject = 0;
	    }
	} else {

	    const static T deltal = 0.0078;
	    const static T deltau = 0.0034;

	    T e, g, r, t, y;
	    T de, dg, dr, ds, dt, gl, gu, nk, nm, ub;
	    T xk, xm, xn, y1, ym, yn, yk, alv;

    //#ifdef DEBUG_rhyper
    //	    REprintf(" ... accept/reject 'large' case v=%g\n", v);
    //#endif
	    /* squeeze using upper and lower bounds */
	    y = ix;
	    y1 = y + 1.0;
	    ym = y - m;
	    yn = n1 - y + 1.0;
	    yk = k - y + 1.0;
	    nk = n2 - k + y1;
	    r = -ym / y1;
	    s = ym / yn;
	    t = ym / yk;
	    e = -ym / nk;
	    g = yn * yk / (y1 * nk) - 1.0;
	    dg = 1.0;
	    if (g < 0.0)
		dg = 1.0 + g;
	    gu = g * (1.0 + g * (-0.5 + g / 3.0));
	    gl = gu - .25 * (g * g * g * g) / dg;
	    xm = m + 0.5;
	    xn = n1 - m + 0.5;
	    xk = k - m + 0.5;
	    nm = n2 - k + xm;
	    ub = y * gu - m * gl + deltau
		+ xm * r * (1. + r * (-0.5 + r / 3.0))
		+ xn * s * (1. + s * (-0.5 + s / 3.0))
		+ xk * t * (1. + t * (-0.5 + t / 3.0))
		+ nm * e * (1. + e * (-0.5 + e / 3.0));
	    /* test against upper bound */
	    alv = log(v);
	    if (alv > ub) {
		    reject = 1;
	    } else {
		    		/* test against lower bound */
		    dr = xm * (r * r * r * r);
		    if (r < 0.0)
		        dr /= (1.0 + r);
		    ds = xn * (s * s * s * s);
		    if (s < 0.0)
		        ds /= (1.0 + s);
		    dt = xk * (t * t * t * t);
		    if (t < 0.0)
		        dt /= (1.0 + t);
		    de = nm * (e * e * e * e);
		    if (e < 0.0)
		        de /= (1.0 + e);
		    if (alv < ub - 0.25 * (dr + ds + dt + de)
		        + (y + m) * (gl - gu) - deltal) {
		        reject = 0;
		    }
		    else {
		        /* * Stirling's formula to machine accuracy
		         */
		        if (alv <= (a - afc!T(ix) - afc!T(n1 - ix)
		    		- afc!T(k - ix) - afc!T(n2 - k + ix))) {
		    	reject = 0;
		        } else {
		    	reject = 1;
		        }
		    }
	    }
	} // else
	if (reject)
	    goto L30;
    }


L_finis:
    /* return appropriate variate */

    if (kk + kk >= tn) {
	if (nn1 > nn2) {
	    ix = kk - nn2 + ix;
	} else {
	    ix = nn1 - ix;
	}
    } else {
	if (nn1 > nn2)
	    ix = kk - ix;
    }
    return ix;
}



void test_hyper()
{
	import std.stdio: writeln;
	writeln("dhyper: ", dhyper(1., 6., 3., 2., 0));
	writeln("phyper: ", phyper(1., 6., 3., 2., 1, 0));
	writeln("qhyper: ", qhyper(.7, 6., 3., 3., 1, 0));
	writeln("rhyper: ", rhyper(4., 5., 5.), ", rhyper: ", rhyper(4., 5., 5.), ", rhyper: ", rhyper(4., 5., 5.));
}

