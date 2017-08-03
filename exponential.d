module exponential;

import common;

/*
** dmd exponential.d common.d && ./exponential
*/

auto dexp(T)(T x, T scale, int give_log)
{
    /* NaNs propagated correctly */
    if (isNaN(x) || isNaN(scale))
    	return x + scale;
    if (scale <= 0.0)
    	return T.nan;

    mixin R_D__0!(give_log);
    if (x < 0.)
	    return R_D__0;
    return (give_log ? (-x / scale) - log(scale) : exp(-x / scale) / scale);
}


auto pexp(T)(T x, T scale, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(scale))
        return x + scale;
    if (scale < 0)
        return T.nan;

    if (x <= 0.)
        return R_DT_0!T(lower_tail, log_p);
    /* same as weibull( shape = 1): */
    x = -(x / scale);
    return lower_tail ? (log_p ? R_Log1_Exp!T(x) : -expm1(x)) : R_D_exp!T(x, log_p);
}


auto qexp(T)(T p, T scale, int lower_tail, int log_p)
{
    if (isNaN(p) || isNaN(scale))
        return p + scale;

    if (scale < 0)
        return T.nan;

    mixin (R_Q_P01_check!p());
    if (p == R_DT_0!T(lower_tail, log_p))
        return 0;

    return - scale * R_DT_Clog!T(p, lower_tail, log_p);
}


auto rexp(T)(T scale)
{
    if (!isFinite(scale) || scale <= 0.0) {
        if(scale == 0.)
            return 0.;
        /* else */
        return T.nan;
    }
    return scale * exp_rand!T(); // --> in ./sexp.c
}



void test_exp()
{
	import std.stdio: write, writeln;
	writeln("dexp: ", dexp(2., 1., 0));
    writeln("pexp: ", pexp(2., 1., 1, 0));
    writeln("qexp: ", qexp(.8, 1., 1, 0));
    writeln("rexp: ", rexp(1.), ", rexp: ", rexp(1.),
            ", rexp: ", rexp(1.), ", rexp: ", rexp(1.));
}
