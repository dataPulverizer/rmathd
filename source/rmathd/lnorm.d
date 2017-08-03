module rmathd.lnorm;

public import rmathd.common;
public import rmathd.normal;

/*
** dmd lnorm.d common.d normal.d && ./lnorm
*/

T dlnorm(T: double)(T x, T meanlog, T sdlog, int give_log)
{
    T y;
    mixin R_D__0!give_log;

    if (isNaN(x) || isNaN(meanlog) || isNaN(sdlog))
	    return x + meanlog + sdlog;

    if(sdlog <= 0) {
	    if(sdlog < 0)
	    	return T.nan;
	    // sdlog == 0 :
	    return (log(x) == meanlog) ? T.infinity : R_D__0;
    }
    if(x <= 0)
    	return R_D__0;

    y = (log(x) - meanlog) / sdlog;
    return (give_log ? -(M_LN_SQRT_2PI   + 0.5 * y * y + log(x * sdlog)) : 
    	   M_1_SQRT_2PI * exp(-0.5 * y * y)/(x * sdlog));
}


T plnorm(T: double)(T x, T meanlog, T sdlog, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(meanlog) || isNaN(sdlog))
	    return x + meanlog + sdlog;

    if (sdlog < 0)
    	return T.nan;

    if (x > 0)
	    return pnorm!T(log(x), meanlog, sdlog, lower_tail, log_p);
    return R_DT_0!T(lower_tail, log_p);
}

T qlnorm(T: double)(T p, T meanlog, T sdlog, int lower_tail, int log_p)
{
    if (isNaN(p) || isNaN(meanlog) || isNaN(sdlog))
	    return p + meanlog + sdlog;
    
    immutable T INF = T.infinity;
    mixin (R_Q_P01_boundaries!(p, 0, INF)());

    return exp(qnorm!T(p, meanlog, sdlog, lower_tail, log_p));
}

T rlnorm(T: double)(T meanlog, T sdlog)
{
    if(isNaN(meanlog) || !isFinite(sdlog) || sdlog < 0.)
	    return T.nan;

    return exp(rnorm!T(meanlog, sdlog));
}


void test_lnorm()
{
	import std.stdio: writeln;
	writeln("dlnorm: ", dlnorm(10., 2., 1., 0));
	writeln("plnorm: ", plnorm(10., 2., 1., 1, 0));
	writeln("qlnorm: ", qlnorm(0.618897, 2., 1., 1, 0));
	writeln("rlnorm: ", rlnorm(2., 1.), ", rlnorm: ", rlnorm(2., 1.), ", rlnorm: ", rlnorm(2., 1.));
}

