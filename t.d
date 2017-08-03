module t;

import common;
import beta;
import normal;
import chisq;

/*
** dmd t.d common.d normal.d beta.d chisq.d && ./t
*/


T dt(T)(T x, T n, int give_log)
{
    
    mixin R_D__0!give_log;
    if(isNaN(x) || isNaN(n))
	    return x + n;
    if (n <= 0)
    	return T.nan;
    if(!isFinite(x))
	    return R_D__0;
    if(!isFinite(n))
	    return dnorm!T(x, 0., 1., give_log);

    T u, t = -bd0!T(n/2., (n + 1)/2.) + stirlerr!T((n + 1)/2.) - stirlerr!T(n/2.),
	x2n = x*x/n, // in  [0, Inf]
	ax = 0., // <- -Wpedantic
	l_x2n; // := log(sqrt(1 + x2n)) = log(1 + x2n)/2
    int lrg_x2n =  (x2n > 1./DBL_EPSILON);
    if (lrg_x2n) { // large x^2/n :
	    ax = fabs(x);
	    l_x2n = log(ax) - log(n)/2.; // = log(x2n)/2 = 1/2 * log(x^2 / n)
	    u = //  log(1 + x2n) * n/2 =  n * log(1 + x2n)/2 =
	        n*l_x2n;
    } else if (x2n > 0.2) {
	    l_x2n = log(1 + x2n)/2.;
	    u = n * l_x2n;
    } else {
	    l_x2n = log1p(x2n)/2.;
	    u = -bd0(n/2.,(n+x*x)/2.) + x*x/2.;
    }

    //old: return  R_D_fexp(M_2PI*(1+x2n), t-u);

    // R_D_fexp(f,x) :=  (give_log ? -0.5*log(f)+(x) : exp(x)/sqrt(f))
    // f = 2pi*(1+x2n)
    //  ==> 0.5*log(f) = log(2pi)/2 + log(1+x2n)/2 = log(2pi)/2 + l_x2n
    //	     1/sqrt(f) = 1/sqrt(2pi * (1+ x^2 / n))
    //		       = 1/sqrt(2pi)/(|x|/sqrt(n)*sqrt(1+1/x2n))
    //		       = M_1_SQRT_2PI * sqrt(n)/ (|x|*sqrt(1+1/x2n))
    if(give_log)
	    return t - u - (M_LN_SQRT_2PI + l_x2n);

    // else :  if(lrg_x2n) : sqrt(1 + 1/x2n) ='= sqrt(1) = 1
    T I_sqrt_ = (lrg_x2n ? sqrt(n)/ax : exp(-l_x2n));
    return exp(t - u)*M_1_SQRT_2PI*I_sqrt_;
}


T pt(T)(T x, T n, int lower_tail, int log_p)
{
    /* return  P[ T <= x ]	where
     * T ~ t_{n}  (t distrib. with n degrees of freedom).
    
     *	--> ./pnt.c for NON-central
     */
    T val, nx;
    
    if (isNaN(x) || isNaN(n))
	    return x + n;
    
    if (n <= 0.0)
    	return T.nan;

    if(!isFinite(x))
	    return (x < 0) ? R_DT_0!T(lower_tail, log_p) : R_DT_1!T(lower_tail, log_p);
    if(!isFinite(n))
	    return pnorm!T(x, 0.0, 1.0, lower_tail, log_p);

    //#ifdef R_version_le_260
    //if (n > 4e5) { /*-- Fixme(?): test should depend on `n' AND `x' ! */
	//    /* Approx. from	 Abramowitz & Stegun 26.7.8 (p.949) */
	//    val = 1./(4.*n);
	//    return pnorm!T(x*(1. - val)/sqrt(1. + x*x*2.*val), 0.0, 1.0, lower_tail, log_p);
    //}
    //#endif

    nx = 1 + (x/n)*x;
    /* FIXME: This test is probably losing rather than gaining precision,
     * now that pbeta(*, log_p = TRUE) is much better.
     * Note however that a version of this test *is* needed for x*x > D_MAX */
    if(nx > 1e100) { /* <==>  x*x > 1e100 * n  */
	    /* Danger of underflow. So use Abramowitz & Stegun 26.5.4
	       pbeta(z, a, b) ~ z^a(1-z)^b / aB(a,b) ~ z^a / aB(a,b),
	       with z = 1/nx,  a = n/2,  b= 1/2 :
	    */
	    T lval;
	    lval = -0.5*n*(2*log(fabs(x)) - log(n)) - lbeta!T(0.5*n, 0.5) - log(0.5*n);
	    val = log_p ? lval : exp(lval);
    } else {
	    val = (n > x * x)
	        ? pbeta!T(x * x / (n + x * x), 0.5, n / 2., /*lower_tail*/0, log_p)
	        : pbeta!T(1. / nx,             n / 2., 0.5, /*lower_tail*/1, log_p);
    }

    /* Use "1 - v"  if	lower_tail  and	 x > 0 (but not both):*/
    if(x <= 0.)
	    lower_tail = !lower_tail;

    if(log_p) {
	    if(lower_tail)
	    	return log1p(-0.5*exp(val));
	    else
	    	return val - M_LN2; /* = log(.5* pbeta(....)) */
    } else {
	    val /= 2.;
	    mixin R_D_Cval!(val);
	    return R_D_Cval;
    }
}


T qt(T)(T p, T ndf, int lower_tail, int log_p)
{
    const static T eps = 1.0e-12;
    
    T P, q;
    
    if (isNaN(p) || isNaN(ndf))
	    return p + ndf;
	immutable(T) NINF = -T.infinity, INF = T.infinity;
    mixin (R_Q_P01_boundaries!(p, NINF, INF)());

    if (ndf <= 0)
    	return T.nan;

    if (ndf < 1) { /* based on qnt */
	    const static T accu = 1e-13;
	    const static T Eps = 1e-11; /* must be > accu */
        
	    T ux, lx, nx, pp;
        
	    int iter = 0;
        
        mixin R_DT_qIv!p;
	    p = R_DT_qIv;
        
	    /* Invert pt(.) :
	     * 1. finding an upper and lower bound */
	    if(p > 1 - DBL_EPSILON)
	    	return T.infinity;
	    pp = fmin2!T(1 - DBL_EPSILON, p * (1 + Eps));
	    for(ux = 1.; ux < DBL_MAX && pt(ux, ndf, 1, 0) < pp; ux *= 2){};
	    pp = p * (1 - Eps);
	    for(lx =-1.; lx > -DBL_MAX && pt(lx, ndf, 1, 0) > pp; lx *= 2){};
        
	    /* 2. interval (lx,ux)  halving
	       regula falsi failed on qt(0.1, 0.1)
	     */
	    do {
	        nx = 0.5 * (lx + ux);
	        if (pt(nx, ndf, 1, 0) > p) ux = nx; else lx = nx;
	    } while ((ux - lx) / fabs(nx) > accu && ++iter < 1000);
        
	    if(iter >= 1000){
	    	doNothing();
	    	//ML_ERROR(ME_PRECISION, "qt");
	    }
        
	    return 0.5*(lx + ux);
    }

    /* Old comment:
     * FIXME: "This test should depend on  ndf  AND p  !!
     * -----  and in fact should be replaced by
     * something like Abramowitz & Stegun 26.7.5 (p.949)"
     *
     * That would say that if the qnorm value is x then
     * the result is about x + (x^3+x)/4df + (5x^5+16x^3+3x)/96df^2
     * The differences are tiny even if x ~ 1e5, and qnorm is not
     * that accurate in the extreme tails.
     */
    if (ndf > 1e20)
    	return qnorm!T(p, 0., 1., lower_tail, log_p);

    P = R_D_qIv!T(p, log_p); /* if exp(p) underflows, we fix below */

    //Rboolean
    int neg = (!lower_tail || P < 0.5) && (lower_tail || P > 0.5),
	is_neg_lower = (lower_tail == neg); /* both TRUE or FALSE == !xor */

	//mixin R_D_Lval!p;
	mixin R_D_Cval!p;

    if(neg)
	    P = 2*(log_p ? (lower_tail ? P : -expm1(p)) : R_D_Lval!T(p, lower_tail));
    else
	    P = 2*(log_p ? (lower_tail ? -expm1(p) : P) : R_D_Cval);

    /* 0 <= P <= 1 ; P = 2*min(P', 1 - P')  in all cases */

    if (fabs(ndf - 2) < eps) {	/* df ~= 2 */
	    if(P > DBL_MIN) {
	        if(3* P < DBL_EPSILON) /* P ~= 0 */
	    	q = 1 / sqrt(P);
	        else if (P > 0.9)	   /* P ~= 1 */
	    	q = (1 - P) * sqrt(2 /(P * (2 - P)));
	        else /* eps/3 <= P <= 0.9 */
	    	q = sqrt(2 / (P * (2 - P)) - 2);
	    } else { /* P << 1, q = 1/sqrt(P) = ... */
	        if(log_p)
	    	    q = is_neg_lower ? exp(- p/2) / M_SQRT2 : 1/sqrt(-expm1(p));
	        else
	    	    q = T.infinity;
	    }
    } else if (ndf < 1 + eps) { /* df ~= 1  (df < 1 excluded above): Cauchy */
	    if(P == 1.) q = 0; // some versions of tanpi give Inf, some NaN
	    else if(P > 0)
	        q = 1/tanpi!T(P/2.);/* == - tan((P+1) * M_PI_2) -- suffers for P ~= 0 */
        
	    else { /* P = 0, but maybe = 2*exp(p) ! */
	        if(log_p) /* 1/tan(e) ~ 1/e */
	    	q = is_neg_lower ? M_1_PI * exp(-p) : -1./(M_PI * expm1(p));
	        else
	    	q = T.infinity;
	    }
    }
    else {		/*-- usual case;  including, e.g.,  df = 1.1 */
	T x = 0., y, log_P2 = 0./* -Wall */,
	    a = 1 / (ndf - 0.5),
	    b = 48 / (a * a),
	    c = ((20700 * a / b - 98) * a - 16) * a + 96.36,
	    d = ((94.5 / (b + c) - 3) / b + 1) * sqrt(a*M_PI_2)*ndf;

    //Rboolean
	int P_ok1 = P > DBL_MIN || !log_p,  P_ok = P_ok1;
	if(P_ok1) {
	    y = pow(d * P, 2.0 / ndf);
	    P_ok = (y >= DBL_EPSILON);
	}
	if(!P_ok) {// log.p && P very.small  ||  (d*P)^(2/df) =: y < eps_c
	    log_P2 = is_neg_lower ? R_D_log!T(p, log_p) : R_D_LExp!T(p, log_p); /* == log(P / 2) */
	    x = (log(d) + M_LN2 + log_P2) / ndf;
	    y = exp(2*x);
	}

	if ((ndf < 2.1 && P > 0.5) || y > 0.05 + a) { /* P > P0(df) */
	    /* Asymptotic inverse expansion about normal */
	    if(P_ok)
		    x = qnorm!T(0.5 * P, 0., 1., /*lower_tail*/1, /*log_p*/ 0);
	    else /* log_p && P underflowed */
		    x = qnorm!T(log_P2,  0., 1., lower_tail, /*log_p*/ 1);

	    y = x * x;
	    if (ndf < 5)
		    c += 0.3 * (ndf - 4.5) * (x + 0.6);
	    c = (((0.05 * d * x - 5) * x - 7) * x - 2) * x + b + c;
	    y = (((((0.4 * y + 6.3) * y + 36) * y + 94.5) / c
		  - y - 3) / b + 1) * x;
	    y = expm1(a * y * y);
	    q = sqrt(ndf * y);
	} else if(!P_ok && x < - M_LN2 * DBL_MANT_DIG) {/* 0.5* log(DBL_EPSILON) */
	    /* y above might have underflown */
	    q = sqrt(ndf)*exp(-x);
	} else { /* re-use 'y' from above */
	    y = ((1 / (((ndf + 6) / (ndf * y) - 0.089 * d - 0.822)
		       * (ndf + 2) * 3) + 0.5 / (ndf + 4))
		 * y - 1) * (ndf + 1) / (ndf + 2) + 1 / y;
	    q = sqrt(ndf * y);
	}


	/* Now apply 2-term Taylor expansion improvement (1-term = Newton):
	 * as by Hill (1981) [ref.above] */

	/* FIXME: This can be far from optimal when log_p = TRUE
	 *      but is still needed, e.g. for qt(-2, df=1.01, log=TRUE).
	 *	Probably also improvable when  lower_tail = FALSE */

	if(P_ok1) {
	    int it = 0;
	    while(it++ < 10 && (y = dt(q, ndf, 0)) > 0 &&
		  isFinite(x = (pt(q, ndf, 0, 0) - P/2) / y) &&
		  fabs(x) > 1e-14*fabs(q))
		/* Newton (=Taylor 1 term):
		 *  q += x;
		 * Taylor 2-term : */
		q += x * (1. + x * q * (ndf + 1) / (2 * (q * q + ndf)));
	}
    }
    if(neg) q = -q;
    return q;
}


T rt(T)(T df)
{
    if (isNaN(df) || df <= 0.0)
    	return T.nan;

    if(!isFinite(df))
	    return norm_rand!T();
    else {
    /* Some compilers (including MW6) evaluated this from right to left
    	return norm_rand() / sqrt(rchisq(df) / df); */
    	T num = norm_rand!T();
    	return num / sqrt(rchisq!T(df) / df);
    }
}


void test_t()
{
	import std.stdio: writeln;
	writeln("dt: ", dt(1., 20., 0));
	writeln("pt: ", pt(1., 20., 1, 0));
	writeln("qt: ", qt(0.7, 20., 1, 0));
	writeln("rt: ", rt(20.), ", rt: ", rt(20.), ", rt: ", rt(20.), ", rt: ", rt(20.));
}

