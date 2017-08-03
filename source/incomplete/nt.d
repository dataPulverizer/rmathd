module nt;

import rmathd.common;
import rmathd.t;
import rmathd.normal;
import rmathd.beta;
import rmathd.chisq;


/* 
** toms708.d 
** dmd nt.d common.d t.d normal.d beta.d chisq.d && ./nt
*/


T dnt(T)(T x, T df, T ncp, int give_log)
{
    T u;
    mixin R_D__0!give_log;
    
    if (isNaN(x) || isNaN(df))
	    return x + df;
    

    /* If non-positive df then error */
    if (df <= 0.0)
    	return T.nan;

    if(ncp == 0.0)
    	return dt!T(x, df, give_log);

    /* If x is infinite then return 0 */
    if(!isFinite(x))
	return R_D__0;

    /* If infinite df then the density is identical to a
       normal distribution with mean = ncp.  However, the formula
       loses a lot of accuracy around df=1e9
    */
    if(!isFinite(df) || df > 1e8)
	return dnorm!T(x, ncp, 1., give_log);

    /* Do calculations on log scale to stabilize */

    /* Consider two cases: x ~= 0 or not */
    if (fabs(x) > sqrt(df * DBL_EPSILON)) {
	u = log(df) - log(fabs(x)) +
	    log(fabs(pnt!T(x*sqrt((df + 2)/df), df + 2, ncp, 1, 0) -
		     pnt!T(x, df, ncp, 1, 0)));
	/* FIXME: the above still suffers from cancellation (but not horribly) */
    }
    else {  /* x ~= 0 : -> same value as for  x = 0 */
	u = lgammafn!T((df+1)/2) - lgammafn!T(df/2)
	    - (M_LN_SQRT_PI + .5*(log(df) + ncp*ncp));
    }

    return (give_log ? u : exp(u));
}



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
	    negdel = 0; tt = t;	 del = ncp;
    } else {
	    /* We deal quickly with left tail if extreme,
	       since pt(q, df, ncp) <= pt(0, df, ncp) = \Phi(-ncp) */
	    if (ncp > 40 && (!log_p || !lower_tail))
	    	return R_DT_0!T(lower_tail, log_p);
	    negdel = 1;	tt = -t; del = -ncp;
    }

    if (df > 4e5 || del*del > 2*M_LN2*(-(DBL_MIN_EXP))) {
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
	    //assert(0, "underflow error in pnt");
	    //assert(0, "range error in pnt");
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
        //assert(0, "precision error int pnt");
        
        //#ifdef DEBUG_pnt
        //		REprintf("s = %#14.7Lg < 0 !!! ---> non-convergence!!\n", s);
        //#endif
		goto finis;
	    }
	    if(s <= 0 && it > 1) goto finis;
	    errbd = cast(T)(2. * s * (xodd - godd));
        //#ifdef DEBUG_pnt
        //	    REprintf("%3d %#9.4g %#9.4g|%#11.4Lg %#11.4Lg %#11.4Lg %#14.10Lg %#9.4g\n",
        //		     it, 1e5*(double)godd, 1e5*(double)geven, p, q, s, tnc, errbd);
        //#endif
	    if(fabs(errbd) < errmax) goto finis;/*convergence*/
	}
	/* non-convergence:*/
	//ML_ERROR(ME_NOCONV, "pnt");
	assert(0, "non-convergence in pnt");
    } else { /* x = t = 0 */
	    tnc = 0.;
    }
 finis:
    tnc += pnorm!T(- del, 0., 1., /*lower*/1, /*log_p*/0);

    lower_tail = lower_tail != negdel; /* xor */
    if(tnc > 1 - 1e-10 && lower_tail){
    	//ML_ERROR(ME_PRECISION, "pnt{final}");
    	assert(0, "precision error in pnt");
    }
	
    return R_DT_val!T(fmin2!T(cast(T)tnc, 1),  lower_tail, log_p);
}

/* Currently returns the wrong answer! */
T qnt(T)(T p, T df, T ncp, int lower_tail, int log_p)
{
    const static T accu = 1e-13;
    const static T Eps = 1e-11; /* must be > accu */

    T ux, lx, nx, pp;

    if (isNaN(p) || isNaN(df) || isNaN(ncp))
	return p + df + ncp;
    
    /* Was
     * df = floor(df + 0.5);
     * if (df < 1 || ncp < 0) ML_ERR_return_NAN;
     */
    if (df <= 0.0)
    	return T.nan;

    if(ncp == 0.0 && df >= 1.0)
    	return qt!T(p, df, lower_tail, log_p);

    immutable(T) NINF = -T.infinity;
    immutable(T) INF = T.infinity;
    mixin (R_Q_P01_boundaries!(p, NINF, INF)());

    if (!isFinite(df)) // df = Inf ==> limit N(ncp,1)
	    return qnorm!T(p, ncp, 1., lower_tail, log_p);

    mixin R_DT_qIv!p;
    p = R_DT_qIv;

    /* Invert pnt(.) :
     * 1. finding an upper and lower bound */
    if(p > 1 - DBL_EPSILON)
    	return INF;
    pp = fmin2!T(1 - DBL_EPSILON, p * (1 + Eps));
    for(ux = fmax2!T(1., ncp);
	ux < DBL_MAX && pnt!T(ux, df, ncp, 1, 0) < pp;
	ux *= 2){}
    pp = p * (1 - Eps);
    for(lx = fmin2(-1., -ncp);
	(lx > -DBL_MAX) && (pnt!T(lx, df, ncp, 1, 0) > pp);
	lx *= 2){}
    
    /* 2. interval (lx,ux)  halving : */
    do {
	nx = 0.5 * (lx + ux); // could be zero
	if (pnt!T(nx, df, ncp, 1, 0) > p)
		ux = nx;
	else
		lx = nx;
    }
    while ((ux - lx) > accu * fmax2!T(fabs(lx), fabs(ux)));

    return 0.5 * (lx + ux);
}


T rnt(T)(T df, T ncp)
{
	return rnorm!T(ncp, 1.)/sqrt(rchisq!T(df)/df);
}


void test_nt()
{
	import std.stdio: writeln;
	writeln("dnt: ", dnt(2., 40., 2., 0));
	writeln("pnt: ", pnt(3., 40., 2., 1, 0));
	writeln("pnt (wrong answer): ", pnt(-3., 40., 2., 1, 0));
	//writeln("qnt: ", qnt(0.7, 40., 1., 1, 0));
	writeln("rnt: ", rnt(40., 2.), ", rnt: ", rnt(40., 2.), ", rnt: ", rnt(40., 2.));
}



