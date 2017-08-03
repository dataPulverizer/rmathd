module f;

import common;
import gamma;
import normal;
import chisq;
import beta;


/*
** dmd f.d common.d gamma.d normal.d chisq.d beta.d && ./f
*/


T df(T)(T x, T m, T n, int give_log)
{
    T p, q, f, dens;

    mixin R_D__0!give_log;
    mixin R_D__1!give_log;

    if (isNaN(x) || isNaN(m) || isNaN(n))
	    return x + m + n;

    if (m <= 0 || n <= 0)
    	return T.nan;
    if (x < 0.)
    	return R_D__0;
    if (x == 0.)
    	return(m > 2 ? R_D__0 : (m == 2 ? R_D__1 : T.infinity));
    if (!isFinite(m) && !isFinite(n)) { /* both +Inf */
	    if(x == 1.)
	    	return T.infinity;
	    else
	    	return R_D__0;
    }
    if (!isFinite(n)) /* must be +Inf by now */
	    return(dgamma!T(x, m/2, 2./m, give_log));
    if (m > 1e14) {/* includes +Inf: code below is inaccurate there */
	    dens = dgamma!T(1./x, n/2, 2./n, give_log);
	    return give_log ? dens - 2*log(x): dens/(x*x);
    }

    f = 1./(n+x*m);
    q = n*f;
    p = x*m*f;

    if (m >= 2) {
	f = m*q/2;
	dens = dbinom_raw!T((m - 2)/2, (m + n - 2)/2, p, q, give_log);
    }
    else {
	f = m*m*q / (2*p*(m + n));
	dens = dbinom_raw!T(m/2, (m + n)/2, p, q, give_log);
    }
    return(give_log ? log(f) + dens : f*dens);
}


T pf(T)(T x, T df1, T df2, int lower_tail, int log_p)
{
    
    if (isNaN(x) || isNaN(df1) || isNaN(df2))
	return x + df2 + df1;
    
    if (df1 <= 0. || df2 <= 0.)
    	return T.nan;

    immutable(T) INF = T.infinity;
    mixin (R_P_bounds_01!(x, 0., INF)());

    /* move to pchisq for very large values - was 'df1 > 4e5' in 2.0.x,
       now only needed for df1 = Inf or df2 = Inf {since pbeta(0,*)=0} : */
    if (df2 == T.infinity) {
	    if (df1 == T.infinity) {
	        if(x <  1.)
	        	return R_DT_0!T(lower_tail, log_p);
	        if(x == 1.)
	        	return (log_p ? -M_LN2 : 0.5);
	        if(x >  1.)
	        	return R_DT_1!T(lower_tail, log_p);
	    }
        
	    return pchisq!T(x * df1, df1, lower_tail, log_p);
    }

    if (df1 == T.infinity)/* was "fudge"	'df1 > 4e5' in 2.0.x */
	return pchisq!T(df2 / x , df2, !lower_tail, log_p);

    /* Avoid squeezing pbeta's first parameter against 1 :  */
    if (df1 * x > df2)
	x = pbeta!T(df2 / (df2 + df1 * x), df2 / 2., df1 / 2., 
		  !lower_tail, log_p);
    else
	x = pbeta!T(df1 * x / (df2 + df1 * x), df1 / 2., df2 / 2.,
		  lower_tail, log_p);

    return !isNaN(x) ? x : T.nan;
}


T qf(T)(T p, T df1, T df2, int lower_tail, int log_p)
{
    
    if (isNaN(p) || isNaN(df1) || isNaN(df2))
	    return p + df1 + df2;
    
    if (df1 <= 0. || df2 <= 0.)
    	return T.nan;

    immutable(T) INF = T.infinity;
    mixin (R_Q_P01_boundaries!(p, 0, INF)());

    /* fudge the extreme DF cases -- qbeta doesn't do this well.
       But we still need to fudge the infinite ones.
     */

    if (df1 <= df2 && df2 > 4e5) {
	if(!isFinite(df1)) /* df1 == df2 == Inf : */
	    return 1.;
	/* else */
	return qchisq!T(p, df1, lower_tail, log_p) / df1;
    }
    if (df1 > 4e5) { /* and so  df2 < df1 */
	    return df2 / qchisq!T(p, df2, !lower_tail, log_p);
    }

    // FIXME: (1/qb - 1) = (1 - qb)/qb; if we know qb ~= 1, should use other tail
    p = (1. / qbeta!T(p, df2/2, df1/2, !lower_tail, log_p) - 1.) * (df2 / df1);
    return !isNaN(p) ? p : T.nan;
}


T rf(T)(T n1, T n2)
{
    T v1, v2;
    if (isNaN(n1) || isNaN(n2) || n1 <= 0. || n2 <= 0.)
	    return T.nan;

    v1 = isFinite(n1) ? (rchisq!T(n1) / n1) : 1;
    v2 = isFinite(n2) ? (rchisq!T(n2) / n2) : 1;
    return v1 / v2;
}



void test_f()
{
	import std.stdio: writeln;
	writeln("df: ", df(3., 5., 7., 0));
	writeln("pf: ", pf(3., 5., 7., 1, 0));
	writeln("qf: ", qf(0.7, 5., 7., 1, 0));
	writeln("rt: ", rf(5., 7.), ", rt: ", rf(5., 7.), ", rt: ", rf(5., 7.), ", rt: ", rf(5., 7.));
}


