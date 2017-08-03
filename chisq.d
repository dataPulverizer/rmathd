module chisq;

import common;
import normal;
import gamma;

/*
** dmd chisq.d common.d normal.d gamma.d && ./chisq
*/

T dchisq(T)(T x, T df, int give_log)
{
    return dgamma!T(x, df / 2., 2., give_log);
}

T pchisq(T)(T x, T df, int lower_tail, int log_p)
{
    return pgamma!T(x, df/2., 2., lower_tail, log_p);
}

T qchisq(T)(T p, T df, int lower_tail, int log_p)
{
    return qgamma!T(p, 0.5 * df, 2.0, lower_tail, log_p);
}

T rchisq(T)(T df)
{
    if (!isFinite(df) || df < 0.0)
    	return T.nan;

    return rgamma!T(df / 2.0, 2.0);
}


void test_chisq()
{
	import std.stdio: writeln;
	writeln("dchisq: ", dchisq(3., 9., 0));
	writeln("pchisq: ", pchisq(3., 9., 1, 0));
	writeln("qchisq: ", qchisq(.6, 9., 1, 0));
	writeln("rchisq: ", rchisq(9.), ", rchisq: ", rchisq(9.), ", rchisq: ", rchisq(9.));
}

