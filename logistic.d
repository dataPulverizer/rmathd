module logistic;

import common;


/* 
** 
** dmd logistic.d common.d && ./logistic
*/


T dlogis(T)(T x, T location, T scale, int give_log)
{
    T e, f;

    if (isNaN(x) || isNaN(location) || isNaN(scale))
	    return x + location + scale;
    
    if (scale <= 0.0)
	    return T.nan;

    x = fabs((x - location) / scale);
    e = exp(-x);
    f = 1.0 + e;
    return give_log ? -(x + log(scale * f * f)) : e / (scale * f * f);
}


/* Compute  log(1 + exp(x))  without overflow (and fast for x > 18)
   For the two cutoffs, consider
   curve(log1p(exp(x)) - x,       33.1, 33.5, n=2^10)
   curve(x+exp(-x) - log1p(exp(x)), 15, 25,   n=2^11)
*/
T Rf_log1pexp(T)(T x) {
    if(x <= 18.)
    	return log1p(exp(x));
    if(x > 33.3)
    	return x;
    // else: 18.0 < x <= 33.3 :
    return x + exp(-x);
}


T plogis(T)(T x, T location, T scale, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(location) || isNaN(scale))
	return x + location + scale;
    
    if (scale <= 0.0)
    	return T.nan;

    x = (x - location) / scale;
    if (isNaN(x))
    	return T.nan;
    mixin (R_P_bounds_Inf_01!(x));

    if(log_p) {
	    // log(1 / (1 + exp( +- x ))) = -log(1 + exp( +- x))
	    return -Rf_log1pexp!T(lower_tail ? -x : x);
    } else {
	    return 1 / (1 + exp(lower_tail ? -x : x));
    }
}


T qlogis(T)(T p, T location, T scale, int lower_tail, int log_p)
{
    if (isNaN(p) || isNaN(location) || isNaN(scale))
	    return p + location + scale;

    immutable(T) NINF = -T.infinity;
    immutable(T) INF = T.infinity;
    mixin (R_Q_P01_boundaries!(p, NINF, INF));

    if (scale <	 0.)
    	return T.nan;
    if (scale == 0.)
    	return location;

    /* p := logit(p) = log( p / (1-p) )	 : */
    if(log_p) {
	    if(lower_tail)
	        p = p - R_Log1_Exp!T(p);
	    else
	        p = R_Log1_Exp!T(p) - p;
    } else
	    p = log(lower_tail ? (p / (1. - p)) : ((1. - p) / p));

    return location + scale * p;
}


T rlogis(T)(T location, T scale)
{
    if (isNaN(location) || !isFinite(scale))
	    return T.nan;

    if (scale == 0. || !isFinite(location))
	    return location;
    else {
	    T u = unif_rand!T();
	return location + scale * log(u / (1. - u));
    }
}


void test_logistic()
{
	import std.stdio: writeln;
	writeln("dlogis: ", dlogis(1., 0., 1., 0));
	writeln("plogis: ", plogis(1., 0., 1., 1, 0));
	writeln("qlogis: ", qlogis(0.7, 0., 1., 1, 0));
	writeln("rlogis: ", rlogis(1., 1.), ", rlogis: ", rlogis(1., 1.), ", rlogis: ", rlogis(1., 1.));
}


