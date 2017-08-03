module uniform;

import common;

/*
** dmd uniform.d common.d && ./uniform
**
** dmd uniform.d common.d && ./uniform && rm uniform
*/

T dunif(T)(T x, T a, T b, int give_log)
{
    if (isNaN(x) || isNaN(a) || isNaN(b))
	    return x + a + b;

    if (b <= a)
    	return T.nan;

    if (a <= x && x <= b)
	    return give_log ? -log(b - a) : 1. / (b - a);
	mixin R_D__0!log_p;
    return R_D__0;
}

T punif(T)(T x, T a, T b, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(a) || isNaN(b))
	    return x + a + b;
    if (b < a)
    	return T.nan;
    if (!isFinite(a) || !isFinite(b))
    	return T.nan;

    if (x >= b)
	    return R_DT_1!T(lower_tail, log_p);
    if (x <= a)
	    return R_DT_0!T(lower_tail, log_p);
    if (lower_tail)
    	return R_D_val!T((x - a) / (b - a), log_p);
    else
    	return R_D_val!T((b - x) / (b - a), log_p);
}

T qunif(T)(T p, T a, T b, int lower_tail, int log_p)
{
    if (isNaN(p) || isNaN(a) || isNaN(b))
	    return p + a + b;

    mixin (R_Q_P01_check!(p)());
    if (!isFinite(a) || !isFinite(b))
    	return T.nan;
    if (b < a)
    	return T.nan;
    if (b == a)
    	return a;

    mixin R_DT_qIv!(p);
    return a + R_DT_qIv * (b - a);
}

T runif(T)(T a, T b)
{
    if (!isFinite(a) || !isFinite(b) || b < a)
    	return T.nan;
    if (a == b)
	    return a;
    else {
	    T u;
	    do {
	    	u = unif_rand!T();
	    } while (u <= 0 || u >= 1);
	    return a + (b - a) * u;
    }
}


void test_uniform()
{
	import std.stdio : writeln;
	writeln(unif_rand!double());
	set_seed(4321, 8765);
	writeln(unif_rand!double());
	writeln("punif: ", punif(0.5, 0., 1., 0, 0));
	writeln("qunif: ", qunif(0.5, 0., 1., 0, 0));
	writeln("runif: ", runif(0., 1.), ", ", runif(0., 1.), ", ", runif(0., 1.), ", ", runif(0., 1.));
}