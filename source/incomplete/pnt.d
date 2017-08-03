module pnt;

import rmathd.common;
import rmathd.t;
import rmathd.normal;
import rmathd.beta;
import rmathd.chisq;

import std.stdio: writeln;


/* 
**
** dmd pnt.d common.d t.d normal.d beta.d chisq.d && ./pnt
*/


T pnt(T)(T t, T df, T ncp, int lower_tail, int log_p)
{
    T albeta, a, b, del, errbd, lambda, rxb, tt, x;
    real geven, godd, p, q, s, tnc, xeven, xodd;
    int it, negdel;

    /* note - itrmax and errmax may be changed to suit one's needs. */

    const int itrmax = 1000;
    const static T errmax = 1.0e-12;

    if (df <= 0.0)
    	return T.nan;
    if(ncp == 0.0)
    	return pt!T(t, df, lower_tail, log_p);

    if(!isFinite(t))
	    return (t < 0) ? R_DT_0!T(lower_tail, log_p) : R_DT_1!T(lower_tail, log_p);
    if (t >= 0.) {
	    negdel = 0; tt = t; del = ncp;
    } else {
	    /* We deal quickly with left tail if extreme,
	       since pt(q, df, ncp) <= pt(0, df, ncp) = \Phi(-ncp) */
	    if (ncp > 40 && (!log_p || !lower_tail))
	    	return R_DT_0!T(lower_tail, log_p);
	    negdel = 1;	tt = -t; del = -ncp;
    }

    if (df > 4e5 || del*del > 2*M_LN2*(-DBL_MIN_EXP)) {
	    /*-- 2nd part: if del > 37.62, then p=0 below
	      FIXME: test should depend on `df', `tt' AND `del' ! */
	    /* Approx. from	 Abramowitz & Stegun 26.7.10 (p.949) */
	    s = 1./(4.*df);
        
	    return pnorm!T(cast(T)(tt*(1. - s)), del,
	    	     sqrt(cast(T) (1. + tt*tt*2.*s)),
	    	     lower_tail != negdel, log_p);
    }

    /* initialize twin series */
    /* Guenther, J. (1978). Statist. Computn. Simuln. vol.6, 199. */

    x = t * t;
    rxb = df/(x + df);/* := (1 - x) {x below} -- but more accurately */
    x = x / (x + df);/* in [0,1) */
    //#ifdef DEBUG_pnt
    //    REprintf("pnt(t=%7g, df=%7g, ncp=%7g) ==> x= %10g:",t,df,ncp, x);
    //#endif
    if (x > 0.) {/* <==>  t != 0 */
	    lambda = del * del;
	    p = .5 * exp(-.5 * lambda);
        //#ifdef DEBUG_pnt
        //	REprintf("\t p=%10Lg\n",p);
        //#endif
	    if(p == 0.) { /* underflow! */
        
	        /*========== really use an other algorithm for this case !!! */
	        //ML_ERROR(ME_UNDERFLOW, "pnt");
	        //ML_ERROR(ME_RANGE, "pnt"); /* |ncp| too large */
	        //assert(0, "Underflow pnt");
	        //assert(0, "Range pnt");
	        return R_DT_0!T(lower_tail, log_p);
	    }
        //#ifdef DEBUG_pnt
        //	REprintf("it  1e5*(godd,   geven)|          p           q           s"
        //	       /* 1.3 1..4..7.9 1..4..7.9|1..4..7.901 1..4..7.901 1..4..7.901 */
        //		 "        pnt(*)     errbd\n");
        //	       /* 1..4..7..0..34 1..4..7.9*/
        //#endif
	    q = M_SQRT_2dPI * p * del;
	    s = .5 - p;
	    /* s = 0.5 - p = 0.5*(1 - exp(-.5 L)) =  -0.5*expm1(-.5 L)) */
	    if(s < 1e-7)
	        s = -0.5 * expm1(-0.5 * lambda);
	    a = .5;
	    b = .5 * df;
	    /* rxb = (1 - x) ^ b   [ ~= 1 - b*x for tiny x --> see 'xeven' below]
	     *       where '(1 - x)' =: rxb {accurately!} above */
	    rxb = pow(rxb, b);
	    albeta = M_LN_SQRT_PI + lgammafn!T(b) - lgammafn!T(.5 + b);
	    xodd = pbeta!T(x, a, b, /*lower*/1, /*log_p*/0);
	    godd = 2. * rxb * exp(a * log(x) - albeta);
	    tnc = b * x;
	    xeven = (tnc < DBL_EPSILON) ? tnc : 1. - rxb;
	    geven = tnc * rxb;
	    tnc = p * xodd + q * xeven;
        
	    /* repeat until convergence or iteration limit */
	    for(it = 1; it <= itrmax; it++) {
	        a += 1.;
	        xodd  -= godd;
	        xeven -= geven;
	        godd  *= x * (a + b - 1.) / a;
	        geven *= x * (a + b - .5) / (a + .5);
	        p *= lambda / (2 * it);
	        q *= lambda / (2 * it + 1);
	        tnc += p * xodd + q * xeven;
	        s -= p;
	        /* R 2.4.0 added test for rounding error here. */
	        if(s < -1.0e-10) { /* happens e.g. for (t,df,ncp)=(40,10,38.5), after 799 it.*/
	    	    
	    	    //ML_ERROR(ME_PRECISION, "pnt");
	    	    //assert(0, "Precision pnt");
                //#ifdef DEBUG_pnt
                //		REprintf("s = %#14.7Lg < 0 !!! ---> non-convergence!!\n", s);
                //#endif
	    	    goto finis;
	        }
	        if(s <= 0 && it > 1)
	        	goto finis;
	        errbd = cast(T)(2. * s * (xodd - godd));
            //#ifdef DEBUG_pnt
            //	    REprintf("%3d %#9.4g %#9.4g|%#11.4Lg %#11.4Lg %#11.4Lg %#14.10Lg %#9.4g\n",
            //		     it, 1e5*(double)godd, 1e5*(double)geven, p, q, s, tnc, errbd);
            //#endif
            writeln("for loop, tnc: ", tnc, ", s: ", s, ", p: ", p);
	        if(fabs(errbd) < errmax)
	        	goto finis;/*convergence*/
	    }
	        /* non-convergence:*/
	        //ML_ERROR(ME_NOCONV, "pnt");
	        assert(0, "Non-Convergence pnt");
    } else { /* x = t = 0 */
	    tnc = 0.;
    }
 finis:
    tnc += pnorm!T(- del, 0., 1., /*lower*/1, /*log_p*/0);
    
    writeln("tnc after finis: ", tnc);

    lower_tail = lower_tail != negdel; /* xor */
    if(tnc > 1 - 1e-10 && lower_tail)
    	assert(0, "Precision pnt{final}");
	    //ML_ERROR(ME_PRECISION, "pnt{final}");

    return R_DT_val!T(fmin2!T(cast(T)tnc, 1.), lower_tail, log_p);
}


void test_pnt()
{
	import std.stdio: writeln;
	writeln("pnt: ", pnt(3., 40., 2., 1, 0));
	writeln("pnt: ", pnt(-3., 40., 2., 1, 0));
}

