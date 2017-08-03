module geom;

import common;
import poisson;
import exponential;


/*
** dmd geom.d common.d normal.d poisson.d exponential.d && ./geom
*/


T dgeom(T)(T x, T p, int give_log)
{ 
    T prob;
    mixin R_D__0!give_log;
    
    if (isNaN(x) || isNaN(p))
    	return x + p;

    if (p <= 0 || p > 1)
    	return T.nan;

    mixin (R_D_nonint_check!(x));
    if (x < 0 || !isFinite(x) || p == 0)
    	return R_D__0;
    x = nearbyint(x);

    /* prob = (1-p)^x, stable for small p */
    prob = dbinom_raw!T(0., x, p, 1 - p, give_log);

    return((give_log) ? log(p) + prob : p*prob);
}


T pgeom(T)(T x, T p, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(p))
	    return x + p;
    
    if(p <= 0 || p > 1)
    	return T.nan;

    if (x < 0.)
    	return R_DT_0!T(lower_tail, log_p);
    if (!isFinite(x))
    	return R_DT_1!T(lower_tail, log_p);
    x = floor(x + 1e-7);

    if(p == 1.) { /* we cannot assume IEEE */
	    x = lower_tail ? 1: 0;
	    return log_p ? log(x) : x;
    }
    x = log1p(-p) * (x + 1);
    if (log_p)
	    return R_DT_Clog!T(x, lower_tail, log_p);
    else
	    return lower_tail ? -expm1(x) : exp(x);
}


T qgeom(T)(T p, T prob, int lower_tail, int log_p)
{
    if (isNaN(p) || isNaN(prob))
	    return p + prob;
    
    if (prob <= 0 || prob > 1)
    	return T.nan;

    mixin (R_Q_P01_check!(p)());
    if (prob == 1)
    	return 0;
    immutable(T) INF = T.infinity;
    mixin (R_Q_P01_boundaries!(p, 0, INF)());

/* add a fuzz to ensure left continuity, but value must be >= 0 */
    return fmax2!T(0, ceil(R_DT_Clog!T(p, lower_tail, log_p) / log1p(- prob) - 1 - 1e-12));
}


T rgeom(T)(T p)
{
    if (!isFinite(p) || p <= 0 || p > 1)
    	return T.nan;

    return rpois!T(exp_rand!T() * ((1 - p) / p));
}



void test_geom()
{
	import std.stdio: writeln;
	writeln("dgeom: ", dgeom(1., .5, 0));
	writeln("pgeom: ", pgeom(1., .5, 1, 0));
	writeln("qgeom: ", qgeom(0.8, 0.2, 1, 0));
	writeln("rgeom: ", rgeom(0.2), ", rgeom: ", rgeom(0.2), ", rgeom: ", rgeom(0.2), ", rgeom: ", rgeom(0.2));
}



