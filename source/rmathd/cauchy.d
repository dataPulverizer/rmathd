module rmathd.cauchy;

public import rmathd.common;

/*
** dmd cauchy.d common.d && ./cauchy
*/

T dcauchy(T: double)(T x, T location, T scale, int give_log)
{
    T y;
    
    /* NaNs propagated correctly */
    if (isNaN(x) || isNaN(location) || isNaN(scale))
	return x + location + scale;
    
    if (scale <= 0)
    	return T.nan;

    y = (x - location) / scale;
    return give_log ? - log(M_PI * scale * (1. + y * y)) : 1. / (M_PI * scale * (1. + y * y));
}


T pcauchy(T: double)(T x, T location, T scale, int lower_tail, int log_p)
{
    
    if (isNaN(x) || isNaN(location) || isNaN(scale))
	    return x + location + scale;
    
    if (scale <= 0)
    	return T.nan;

    x = (x - location) / scale;
    if (isNaN(x))
    	return T.nan;
    
    if(!isFinite(x)) {
	    if(x < 0)
	    	return R_DT_0!T(lower_tail, log_p);
	    else
	    	return R_DT_1!T(lower_tail, log_p);
    }
    
    if (!lower_tail)
	x = -x;
    /* for large x, the standard formula suffers from cancellation.
     * This is from Morten Welinder thanks to  Ian Smith's  atan(1/x) : */
    if (fabs(x) > 1) {
	    T y = atan(1/x)/M_PI;
	    return (x > 0) ? R_D_Clog!T(y, log_p) : R_D_val!T(-y, log_p);
    } else
	    return R_D_val!T(0.5 + atan(x)/M_PI, log_p);
}


T qcauchy(T: double)(T p, T location, T scale, int lower_tail, int log_p)
{

    if (isNaN(p) || isNaN(location) || isNaN(scale))
	    return p + location + scale;
    
    mixin (R_Q_P01_check!(p)());
    if (scale <= 0 || !isFinite(scale)) {
	    if (scale == 0)
	    	return location;
	    /* else */ return T.nan;
    }

    if (log_p) {
	    if (p > -1) {
	        /* when ep := exp(p),
	         * tan(pi*ep)= -tan(pi*(-ep))= -tan(pi*(-ep)+pi) = -tan(pi*(1-ep)) =
	         *		 = -tan(pi*(-expm1(p))
	         * for p ~ 0, exp(p) ~ 1, tan(~0) may be better than tan(~pi).
	         */
	        if (p == 0.) /* needed, since 1/tan(-0) = -Inf  for some arch. */
	    	return location + (lower_tail ? scale : -scale) * T.infinity;
	        lower_tail = !lower_tail;
	        p = -expm1(p);
	    } else
	        p = exp(p);
    } else {
	    if (p > 0.5) {
	        if (p == 1.)
	    	    return location + (lower_tail ? scale : -scale) * T.infinity;
	        p = 1 - p;
	        lower_tail = !lower_tail;
	    }
    }

    if (p == 0.5) return location; // avoid 1/Inf below
    if (p == 0.) return location + (lower_tail ? scale : -scale) * -T.infinity; // p = 1. is handled above
    return location + (lower_tail ? -scale : scale) / tanpi(p);
    /*	-1/tan(pi * p) = -cot(pi * p) = tan(pi * (p - 1/2))  */
}


T rcauchy(T: double)(T location, T scale)
{
    if (isNaN(location) || !isFinite(scale) || scale < 0)
	    return T.nan;
    if (scale == 0. || !isFinite(location))
	    return location;
    else
	    return location + scale * tan(M_PI * unif_rand!T());
}


void test_cauchy()
{
	import std.stdio: writeln;
	writeln("dcauchy: ", dcauchy(1., 0., 1., 0));
	writeln("pcauchy: ", pcauchy(1., 0., 1., 1, 0));
	writeln("qcauchy: ", qcauchy(0.7, 0., 1., 1, 0));
	writeln("rcauchy: ", rcauchy(0., 1.), ", rcauchy: ", rcauchy(0., 1.), ", rcauchy: ", rcauchy(0., 1.));
}

