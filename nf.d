module nf;

import common;
import nchisq;
import chisq;
import nbeta;
import gamma;
import normal;


/* 
** beta.d toms708.d 
** dmd nf.d common.d nchisq.d chisq.d nbeta.d gamma.d normal.d && ./nf
*/


T dnf(T)(T x, T df1, T df2, T ncp, int give_log)
{
    T y, z, f;

    mixin R_D__0!give_log;
    if (isNaN(x) || isNaN(df1) || isNaN(df2) || isNaN(ncp))
	    return x + df2 + df1 + ncp;

    /* want to compare dnf(ncp=0) behavior with df() one, hence *NOT* :
     * if (ncp == 0)
     *   return df(x, df1, df2, give_log); */

    if (df1 <= 0. || df2 <= 0. || ncp < 0)
    	return T.nan;
    if (x < 0.)
    	return R_D__0;
    if (!isFinite(ncp)) /* ncp = +Inf -- FIXME?: in some cases, limit exists */
	    return T.nan;

    /* This is not correct for  df1 == 2, ncp > 0 - and seems unneeded:
     *  if (x == 0.) return(df1 > 2 ? R_D__0 : (df1 == 2 ? R_D__1 : ML_POSINF));
     */
    if (!isFinite(df1) && !isFinite(df2)) { /* both +Inf */
	    /* PR: not sure about this (taken from  ncp==0)  -- FIXME ? */
	    if(x == 1.)
	    	return T.infinity;
	    else
	    	return R_D__0;
    }
    if (!isFinite(df2)) /* i.e.  = +Inf */
	    return df1* dnchisq!T(x*df1, df1, ncp, give_log);
    /*	 ==  dngamma(x, df1/2, 2./df1, ncp, give_log)  -- but that does not exist */
    if (df1 > 1e14 && ncp < 1e7) {
	    /* includes df1 == +Inf: code below is inaccurate there */
	    f = 1 + ncp/df1; /* assumes  ncp << df1 [ignores 2*ncp^(1/2)/df1*x term] */
	    z = dgamma(1./x/f, df2/2, 2./df2, give_log);
	    return give_log ? z - 2*log(x) - log(f) : z / (x*x) / f;
    }

    y = (df1 / df2) * x;
    z = dnbeta!T(y/(1 + y), df1 / 2., df2 / 2., ncp, give_log);
    return  give_log ?
	z + log(df1) - log(df2) - 2 * log1p(y) :
	z * (df1 / df2) /(1 + y) / (1 + y);
}


T pnf(T)(T x, T df1, T df2, T ncp, int lower_tail, int log_p)
{
    T y;

    if (isNaN(x) || isNaN(df1) || isNaN(df2) || isNaN(ncp))
	    return x + df2 + df1 + ncp;
    
    if (df1 <= 0. || df2 <= 0. || ncp < 0)
    	return T.nan;
    if (!isFinite(ncp))
    	return T.nan;
    if (!isFinite(df1) && !isFinite(df2)) /* both +Inf */
	    return T.nan;

    immutable(T) INF = T.infinity;
    mixin R_P_bounds_01!(x, 0., INF);

    if (df2 > 1e8) /* avoid problems with +Inf and loss of accuracy */
	return pnchisq!T(x * df1, df1, ncp, lower_tail, log_p);

    y = (df1 / df2) * x;
    return pnbeta2!T(y/(1. + y), 1./(1. + y), df1 / 2., df2 / 2., ncp, lower_tail, log_p);
}

T qnf(T)(T p, T df1, T df2, T ncp, int lower_tail, int log_p)
{
    T y;
    
    if (isNaN(p) || isNaN(df1) || isNaN(df2) || isNaN(ncp))
	    return p + df1 + df2 + ncp;
    
    if (df1 <= 0. || df2 <= 0. || ncp < 0)
    	return T.nan;
    if (!isFinite(ncp))
    	return T.nan;
    if (!isFinite(df1) && !isFinite(df2))
    	return T.nan;
    immutable(T) INF = T.infinity;
    mixin R_Q_P01_boundaries!(p, 0, INF);

    if (df2 > 1e8) /* avoid problems with +Inf and loss of accuracy */
	return qnchisq!T(p, df1, ncp, lower_tail, log_p)/df1;

    y = qnbeta!T(p, df1 / 2., df2 / 2., ncp, lower_tail, log_p);
    return y/(1-y) * (df2/df1);
}

T rnf(T)(T df1, T df2, T ncp) 
{
    return (rnchisq!T(df1, ncp = ncp)/df1)/(rchisq!T(df2)/df2);
}


void main()
{
	import std.stdio: writeln;
	writeln("dnf: ", dnf(7., 3., 4., 20., 0));
	writeln("pnf: ", pnf(7., 3., 4., 20., 1, 0));
	writeln("qnf: ", qnf(0.7, 3., 4., 20., 1, 0));
	writeln("rnf: ", rnf(3., 4., 20.), ", rnf: ", rnf(3., 4., 20.), ", rnf: ", rnf(3., 4., 20.));
}


