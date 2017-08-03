module nbeta;

import common;
import beta;
import toms708;
import nchisq;
import chisq;

/* 
** poisson.d gamma.d
** dmd nbeta.d common.d beta.d toms708.d nchisq.d chisq.d normal.d && ./nbeta
*/

T dnbeta(T)(T x, T a, T b, T ncp, int give_log)
{
    const static T eps = 1.0e-15;

    int kMax;
    T k, ncp2, dx2, d, D;
    real sum, term, p_k, q;
    mixin R_D__0!give_log;

    if (isNaN(x) || isNaN(a) || isNaN(b) || isNaN(ncp))
	    return x + a + b + ncp;
    
    if (ncp < 0 || a <= 0 || b <= 0)
	    return T.nan;

    if (!isFinite(a) || !isFinite(b) || !isFinite(ncp))
	    return T.nan;

    if (x < 0 || x > 1)
    	return R_D__0;
    if(ncp == 0)
	    return dbeta!T(x, a, b, give_log);

    /* New algorithm, starting with *largest* term : */
    ncp2 = 0.5 * ncp;
    dx2 = ncp2*x;
    d = (dx2 - a - 1)/2;
    D = d*d + dx2 * (a + b) - a;
    if(D <= 0) {
	    kMax = 0;
    } else {
	    D = ceil(d + sqrt(D));
	    kMax = (D > 0) ? cast(int)D : 0;
    }

    /* The starting "middle term" --- first look at it's log scale: */
    term = dbeta!T(x, a + kMax, b, /* log = */ 1);
    p_k = dpois_raw!T(kMax, ncp2,              1);
    if(x == 0. || !isFinite(term) || !isFinite(cast(T)p_k)) /* if term = +Inf */
	return R_D_exp!T(cast(T)(p_k + term), give_log);

    /* Now if s_k := p_k * t_k  {here = exp(p_k + term)} would underflow,
     * we should rather scale everything and re-scale at the end:*/

    p_k += term; /* = log(p_k) + log(t_k) == log(s_k) -- used at end to rescale */
    /* mid = 1 = the rescaled value, instead of  mid = exp(p_k); */

    /* Now sum from the inside out */
    sum = term = 1. /* = mid term */;
    /* middle to the left */
    k = kMax;
    while(k > 0 && term > sum * eps) {
	    k--;
	    q = /* 1 / r_k = */ (k + 1)*(k + a)/(k + a + b)/dx2;
	    term *= q;
	    sum += term;
    }
    /* middle to the right */
    term = 1.;
    k = kMax;
    do {
	    q = /* r_{old k} = */ dx2 * (k + a + b)/(k + a)/(k + 1);
	    k++;
	    term *= q;
	    sum += term;
    } while (term > sum * eps);
    
    return R_D_exp!T(cast(T)(p_k + log(sum)), give_log);
}


real pnbeta_raw(T)(T x, T o_x, T a, T b, T ncp)
{
    /* o_x  == 1 - x  but maybe more accurate */

    /* change errmax and itrmax if desired;
     * original (AS 226, R84) had  (errmax; itrmax) = (1e-6; 100) */
    const static T errmax = 1.0e-9;
    const int itrmax = 10000;  /* 100 is not enough for pf(ncp=200)
				     see PR#11277 */

    T a0, lbeta, c, errbd, x0, temp, tmp_c;
    int ierr;

    real ans, ax, gx, q, sumq;

    if (ncp < 0. || a <= 0. || b <= 0.)
    	return T.nan;

    if(x < 0. || o_x > 1. || (x == 0. && o_x == 1.))
    	return 0.;
    if(x > 1. || o_x < 0. || (x == 1. && o_x == 0.))
    	return 1.;

    c = ncp / 2.;

	/* initialize the series */

    x0 = floor(fmax2!T(c - 7. * sqrt(c), 0.));
    a0 = a + x0;
    lbeta = lgammafn!T(a0) + lgammafn!T(b) - lgammafn!T(a0 + b);
    /* temp = pbeta_raw(x, a0, b, TRUE, FALSE), but using (x, o_x): */
    bratio!T(a0, b, x, o_x, &temp, &tmp_c, &ierr, 0);

    gx = exp(a0 * log(x) + b * (x < .5 ? log1p(-x) : log(o_x))
	     - lbeta - log(a0));
    if (a0 > a)
	q = exp(-c + x0 * log(c) - lgammafn!T(x0 + 1.));
    else
	q = exp(-c);

    sumq = 1. - q;
    ans = ax = q * temp;

	/* recurse over subsequent terms until convergence is achieved */
    T j = floor(x0); // x0 could be billions, and is in package EnvStats
    do {
	    j++;
	    temp -= cast(T) gx;
	    gx *= x * (a + b + j - 1.) / (a + j);
	    q *= c / j;
	    sumq -= q;
	    ax = temp * q;
	    ans += ax;
	    errbd = cast(T)((temp - gx) * sumq);
    } while (errbd > errmax && j < itrmax + x0);

    if (errbd > errmax){
	    //ML_ERROR(ME_PRECISION, "pnbeta");
	    doNothing();
    }
    if (j >= itrmax + x0){
	    //ML_ERROR(ME_NOCONV, "pnbeta");
	    doNothing();
    }

    return ans;
}

T pnbeta2(T)(T x, T o_x, T a, T b, T ncp,
	/* o_x  == 1 - x  but maybe more accurate */
	int lower_tail, int log_p)
{
    real ans = pnbeta_raw!T(x, o_x, a,b, ncp);


    /* return R_DT_val(ans), but we want to warn about cancellation here */
    if (lower_tail)
	    return cast(T)(log_p ? log(ans) : ans);
    else {
	if (ans > 1. - 1e-10){
		//ML_ERROR(ME_PRECISION, "pnbeta");
		doNothing();
	}
	if (ans > 1.0)
		ans = 1.0;  /* Precaution */
	return cast(T) (log_p ? log1p(-ans) : (1. - ans));
    }
}

T pnbeta(T)(T x, T a, T b, T ncp, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(a) || isNaN(b) || isNaN(ncp))
	    return x + a + b + ncp;

    mixin (R_P_bounds_01!(x, 0., 1.));
    return pnbeta2!T(x, 1 - x, a, b, ncp, lower_tail, log_p);
}


T qnbeta(T)(T p, T a, T b, T ncp, int lower_tail, int log_p)
{
    const static T accu = 1e-15;
    const static T Eps = 1e-14; /* must be > accu */

    T ux, lx, nx, pp;
    
    if (isNaN(p) || isNaN(a) || isNaN(b) || isNaN(ncp))
	    return p + a + b + ncp;
    
    if (!isFinite(a))
    	return T.nan;

    if (ncp < 0. || a <= 0. || b <= 0.)
    	return T.nan;

    mixin (R_Q_P01_boundaries!(p, 0, 1));
    mixin R_DT_qIv!(p);
    
    p = R_DT_qIv;

    /* Invert pnbeta(.) :
     * 1. finding an upper and lower bound */
    if(p > 1 - DBL_EPSILON)
    	return 1.0;
    pp = fmin2!T(1 - DBL_EPSILON, p * (1 + Eps));
    for(ux = 0.5; ux < 1 - DBL_EPSILON && pnbeta!T(ux, a, b, ncp, 1, 0) < pp; ux = 0.5*(1 + ux)){};
    pp = p * (1 - Eps);
    for(lx = 0.5; lx > DBL_MIN && pnbeta!T(lx, a, b, ncp, 1, 0) > pp; lx *= 0.5){};

    /* 2. interval (lx,ux)  halving : */
    do {
	    nx = 0.5 * (lx + ux);
	    if (pnbeta!T(nx, a, b, ncp, 1, 0) > p)
	    	ux = nx;
	    else
	    	lx = nx;
    } while ((ux - lx) / nx > accu);

    return 0.5*(ux + lx);
}


T rnbeta(T)(T a, T b, T ncp)
{
	T X = rnchisq(2*a, ncp);
    return X/(X + rchisq(2*b));
}


void test_nbeta()
{
	import std.stdio: writeln;
	writeln("dnbeta: ", dnbeta(0.7, 6., 8., 20., 1));
	writeln("qnbeta: ", qnbeta(0.7, 6., 8., 20., 1, 0));
	writeln("pnbeta: ", pnbeta(0.7, 6., 8., 20., 1, 0));
	writeln("rnbeta: ", rnbeta(6., 8., 20.), ", rnbeta: ", rnbeta(6., 8., 20.), ", rnbeta: ", rnbeta(6., 8., 20.));
}

