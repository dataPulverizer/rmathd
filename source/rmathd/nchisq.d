module rmathd.nchisq;

public import rmathd.common;
public import rmathd.gamma;
public import rmathd.chisq;
public import rmathd.poisson;
//import rmathd.normal;

/*
** dmd nchisq.d common.d normal.d chisq.d && ./nchisq
*/

/*
 * Compute the log of a sum from logs of terms, i.e.,
 *
 *     log (exp (logx) + exp (logy))
 *
 * without causing overflows and without throwing away large handfuls
 * of accuracy.
 */
T logspace_add(T)(T logx, T logy)
{
    return fmax2!T(logx, logy) + log1p(exp(-fabs(logx - logy)));
}

static const double _dbl_min_exp = M_LN2 * DBL_MIN_EXP;
T pnchisq_raw(T)(T x, T f, T theta /* = ncp */,
	    T errmax, T reltol, int itrmax,
	    int lower_tail, int log_p)
{
    T lam, x2, f2, term, bound, f_x_2n, f_2n;
    T l_lam = -1., l_x = -1.; /* initialized for -Wall */
    int n;
    //Rboolean
    int lamSml, tSml, is_r, is_b, is_it;
    real ans, u, v, t, lt, lu = -1;

    if (x <= 0.) {
      	if(x == 0. && f == 0.) {
      	    return lower_tail ? R_D_exp!T(-0.5*theta, log_p) : (log_p ? R_Log1_Exp!T(-0.5*theta) : -expm1(-0.5*theta));
      	}
      	/* x < 0  or {x==0, f > 0} */
	      return R_DT_0!T(lower_tail, log_p);
    }
    if(!isFinite(x))
        return R_DT_1!T(lower_tail, log_p);

    /* This is principally for use from qnchisq */

    if(theta < 80) { /* use 110 for Inf, as ppois(110, 80/2, lower.tail=FALSE) is 2e-20 */
	//real ans;
	int i;
	// Have  pgamma(x,s) < x^s / Gamma(s+1) (< and ~= for small x)
	// ==> pchisq(x, f) = pgamma(x, f/2, 2) = pgamma(x/2, f/2)
	//                  <  (x/2)^(f/2) / Gamma(f/2+1) < eps
	// <==>  f/2 * log(x/2) - log(Gamma(f/2+1)) < log(eps) ( ~= -708.3964 )
	// <==>        log(x/2) < 2/f*(log(Gamma(f/2+1)) + log(eps))
	// <==> log(x) < log(2) + 2/f*(log(Gamma(f/2+1)) + log(eps))
	if(lower_tail && f > 0. && log(x) < M_LN2 + 2/f*(lgamma!T(f/2. + 1) + _dbl_min_exp)) {
	    // all  pchisq(x, f+2*i, lower_tail, FALSE), i=0,...,110 would underflow to 0.
	    // ==> work in log scale
	    T lambda = 0.5 * theta;
	    T sum, sum2, pr = -lambda;
	    sum = sum2 = -T.infinity;
	    /* we need to renormalize here: the result could be very close to 1 */
	    for(i = 0; i < 110;  pr += log(lambda) - log(++i)) {
		sum2 = logspace_add!T(sum2, pr);
		sum = logspace_add!T(sum, pr + pchisq!T(x, f + 2*i, lower_tail, 1));
		if (sum2 >= -1e-15) /*<=> EXP(sum2) >= 1-1e-15 */
        break;
	    }
	    ans = sum - sum2;
	    return cast(T) (log_p ? ans : exp(ans));
	}
	else {
	    real lambda = 0.5 * theta;
	    real sum = 0, sum2 = 0, pr = exp(-lambda); // does this need a feature test?
	    /* we need to renormalize here: the result could be very close to 1 */
	    for(i = 0; i < 110;  pr *= lambda / ++i) {
		// pr == exp(-lambda) lambda^i / i!  ==  dpois(i, lambda)
		sum2 += pr;
		// pchisq(*, i, *) is  strictly decreasing to 0 for lower_tail=TRUE
		//                 and strictly increasing to 1 for lower_tail=FALSE
		sum += pr * pchisq!T(x, f + 2*i, lower_tail, 0);
		if (sum2 >= 1-1e-15)
        break;
	    }
	    ans = sum/sum2;
	    return cast(T) (log_p ? log(ans) : ans);
	}
    } // if(theta < 80)

    // else: theta == ncp >= 80 --------------------------------------------
    // Series expansion ------- FIXME: log_p=TRUE, lower_tail=FALSE only applied at end

    lam = .5 * theta;
    lamSml = (-lam < _dbl_min_exp);
    if(lamSml) {
	/* MATHLIB_ERROR(
	   "non centrality parameter (= %g) too large for current algorithm",
	   theta) */
        u = 0;
        lu = -lam;/* == ln(u) */
        l_lam = log(lam);
    } else {
	u = exp(-lam);
    }

    /* evaluate the first term */
    v = u;
    x2 = .5 * x;
    f2 = .5 * f;
    f_x_2n = f - x;

    if(f2 * DBL_EPSILON > 0.125 && /* very large f and x ~= f: probably needs */
       fabs(t = x2 - f2) <         /* another algorithm anyway */
       sqrt(DBL_EPSILON) * f2) {
	/* evade cancellation error */
	/* t = exp((1 - t)*(2 - t/(f2 + 1))) / sqrt(2*M_PI*(f2 + 1));*/
        lt = (1 - t)*(2 - t/(f2 + 1)) - M_LN_SQRT_2PI - 0.5 * log(f2 + 1);
    }
    else {
	/* Usual case 2: careful not to overflow .. : */
	lt = f2*log(x2) -x2 - lgammafn!T(f2 + 1);
    }

    tSml = (lt < _dbl_min_exp);
    if(tSml) {
	if (x > f + theta +  5* sqrt( 2*(f + 2*theta))) {
	    /* x > E[X] + 5* sigma(X) */
	    return R_DT_1!T(lower_tail, log_p); /* FIXME: could be more accurate than 0. */
	} /* else */
	l_x = log(x);
	ans = term = 0.; t = 0;
    }
    else {
	t = exp(lt);
	ans = term = cast(T) (v * t);
    }

    for (n = 1, f_2n = f + 2., f_x_2n += 2.;  ; n++, f_2n += 2, f_x_2n += 2) {
	/* f_2n    === f + 2*n
	 * f_x_2n  === f - x + 2*n   > 0  <==> (f+2n)  >   x */
	if (f_x_2n > 0) {
	    /* find the error bound and check for convergence */
	    bound = cast(T) (t*x / f_x_2n);
	    is_r = is_it = 0;
	    /* convergence only if BOTH absolute and relative error < 'bnd' */
	    is_b = (bound <= errmax); is_r = (term <= reltol * ans); is_it = (n > itrmax);
	    if((is_b && is_r) || is_it)
        {
		    break; /* out completely */
        }
	}

	/* evaluate the next term of the */
	/* expansion and then the partial sum */

        if(lamSml) {
            lu += l_lam - log(n); /* u = u* lam / n */
            if(lu >= _dbl_min_exp) {
		/* no underflow anymore ==> change regime */

                v = u = exp(lu); /* the first non-0 'u' */
                lamSml = 0;
            }
        } else {
	    u *= lam / n;
	    v += u;
	}
	if(tSml) {
            lt += l_x - log(f_2n);/* t <- t * (x / f2n) */
            if(lt >= _dbl_min_exp) {
		/* no underflow anymore ==> change regime */
                t = exp(lt); /* the first non-0 't' */
                tSml = 0;
            }
        } else {
	    t *= x / f_2n;
	}
        if(!lamSml && !tSml) {
	    term = cast(T) (v * t);
	    ans += term;
	}

    } /* for(n ...) */

    if (is_it) {
	      doNothing();
    }
    T dans = cast(T) ans;
    return R_DT_val!T(dans, lower_tail, log_p);
}


T pnchisq(T: double)(T x, T df, T ncp, int lower_tail, int log_p)
{
    T ans;
    if (isNaN(x) || isNaN(df) || isNaN(ncp))
	    return x + df + ncp;
    if (!isFinite(df) || !isFinite(ncp))
	    return T.nan;

    if (df < 0. || ncp < 0.)
    	return T.nan;

    mixin R_D__1!log_p;
    ans = pnchisq_raw!T(x, df, ncp, 1e-12, 8*DBL_EPSILON, 1000000, lower_tail, log_p);
    if(ncp >= 80) {
	    if(lower_tail) {
	        ans = fmin2!T(ans, R_D__1);  /* e.g., pchisq(555, 1.01, ncp = 80) */
	    } else { /* !lower_tail */
	        /* since we computed the other tail cancellation is likely */
	        if(ans < (log_p ? (-10. * M_LN10) : 1e-10)){
	        	doNothing();
	        }
	        if(!log_p) ans = fmax2!T(ans, 0.0);  /* Precaution PR#7099 */
	    }
    }
    if (!log_p || ans < -1e-8)
	    return ans;
    else { // log_p  &&  ans > -1e-8
	    // prob. = exp(ans) is near one: we can do better using the other tail
	    // FIXME: (sum,sum2) will be the same (=> return them as well and reuse here ?)
	    ans = pnchisq_raw!T(x, df, ncp, 1e-12, 8*DBL_EPSILON, 1000000, !lower_tail, 0);
	    return log1p(-ans);
    }
}


T dnchisq(T: double)(T x, T df, T ncp, int give_log)
{
    const static T eps = 5e-15;

    T i, ncp2, q, mid, dfmid, imax;
    real sum, term;

    if (isNaN(x) || isNaN(df) || isNaN(ncp))
	    return x + df + ncp;

    if (!isFinite(df) || !isFinite(ncp) || ncp < 0 || df < 0)
    	return T.nan;

    mixin R_D__0!give_log;

    if(x < 0)
    	return R_D__0;
    if(x == 0 && df < 2.)
	    return T.infinity;
    if(ncp == 0)
	    return (df > 0) ? dchisq!T(x, df, give_log) : R_D__0;
    if(x == T.infinity)
    	return R_D__0;

    ncp2 = 0.5 * ncp;

    /* find max element of sum */
    imax = ceil((-(2 + df) + sqrt((2 - df) * (2 - df) + 4*ncp*x))/4);
    if (imax < 0)
    	imax = 0;
    if(isFinite(imax)) {
	    dfmid = df + 2 * imax;
	    mid = dpois_raw!T(imax, ncp2, 0) * dchisq!T(x, dfmid, 0);
    } else /* imax = Inf */
	    mid = 0;

    if(mid == 0) {
	    /* underflow to 0 -- maybe numerically correct; maybe can be more accurate,
	     * particularly when  give_log = TRUE */
	    /* Use  central-chisq approximation formula when appropriate;
	     * ((FIXME: the optimal cutoff also depends on (x,df);  use always here? )) */
	    if(give_log || ncp > 1000.) {
	        T nl = df + ncp, ic = nl/(nl + ncp);/* = "1/(1+b)" Abramowitz & St.*/
	        return dchisq!T(x*ic, nl*ic, give_log);
	    } else
	        return R_D__0;
    }

    sum = mid;

    /* errorbound := term * q / (1-q)  now subsumed in while() / if() below: */

    /* upper tail */
    term = mid; df = dfmid; i = imax;
    T x2 = x * ncp2;
    do {
	    i++;
	    q = x2 / i / df;
	    df += 2;
	    term *= q;
	    sum += term;
    } while (q >= 1 || term * q > (1 - q)*eps || term > 1e-10*sum);
    /* lower tail */
    term = mid; df = dfmid; i = imax;
    while (i != 0) {
	    df -= 2;
	    q = i * df / x2;
	    i--;
	    term *= q;
	    sum += term;
	if (q < 1 && term * q <= (1 - q)*eps)
		break;
    }
    return R_D_val!T(cast(T)sum, give_log);
}


T qnchisq(T: double)(T p, T df, T ncp, int lower_tail, int log_p)
{
    const static T accu = 1e-13;
    const static T racc = 4*DBL_EPSILON;
    /* these two are for the "search" loops, can have less accuracy: */
    const static T Eps = 1e-11; /* must be > accu */
    const static T rEps= 1e-10; /* relative tolerance ... */

    T ux, lx, ux0, nx, pp;


    if (isNaN(p) || isNaN(df) || isNaN(ncp))
	    return p + df + ncp;

    if (!isFinite(df))
    	return T.nan;

    /* Was
     * df = floor(df + 0.5);
     * if (df < 1 || ncp < 0) ML_ERR_return_NAN;
     */
    if (df < 0 || ncp < 0)
    	return T.nan;

    immutable T INF = T.infinity;
    mixin (R_Q_P01_boundaries!(p, 0, INF)());

    pp = R_D_qIv!T(p, log_p);
    if(pp > 1 - DBL_EPSILON)
    	return lower_tail ? T.infinity : 0.0;

    /* Invert pnchisq(.) :
     * 1. finding an upper and lower bound */
    {
           /* This is Pearson's (1959) approximation,
              which is usually good to 4 figs or so.  */
	    T b, c, ff;
	    b = (ncp*ncp)/(df + 3*ncp);
	    c = (df + 3*ncp)/(df + 2*ncp);
	    ff = (df + 2 * ncp)/(c*c);
	    ux = b + c * qchisq!T(p, ff, lower_tail, log_p);
	    if(ux < 0) ux = 1;
	    ux0 = ux;
    }

    if(!lower_tail && ncp >= 80) {
	    /* in this case, pnchisq() works via lower_tail = TRUE */
	    if(pp < 1e-10){
	    	doNothing();
	    }
	    p = /* R_DT_qIv(p)*/ log_p ? -expm1(p) : (0.5 - (p) + 0.5);
	    lower_tail = 1;
    } else {
	    p = pp;
    }

    pp = fmin2!T(1 - DBL_EPSILON, p * (1 + Eps));
    if(lower_tail) {
        for(; ux < DBL_MAX &&
		pnchisq_raw!T(ux, df, ncp, Eps, rEps, 10000, 1, 0) < pp;
	    ux *= 2){}
	pp = p * (1 - Eps);
        for(lx = fmin2!T(ux0, DBL_MAX);
	    lx > DBL_MIN &&
		pnchisq_raw!T(lx, df, ncp, Eps, rEps, 10000, 1, 0) > pp;
	    lx *= 0.5){}
    }
    else {
        for(; ux < DBL_MAX &&
		pnchisq_raw!T(ux, df, ncp, Eps, rEps, 10000, 0, 0) > pp;
	    ux *= 2){}
	pp = p * (1 - Eps);
        for(lx = fmin2!T(ux0, DBL_MAX);
	    lx > DBL_MIN && pnchisq_raw!T(lx, df, ncp, Eps, rEps, 10000, 0, 0) < pp;
	    lx *= 0.5){}
    }

    /* 2. interval (lx,ux)  halving : */
    if(lower_tail) {
	do {
	    nx = 0.5 * (lx + ux);
	    if (pnchisq_raw!T(nx, df, ncp, accu, racc, 100000, 1, 0) > p)
		    ux = nx;
	    else
		    lx = nx;
	}
	while ((ux - lx) / nx > accu);
    } else {
	do {
	    nx = 0.5 * (lx + ux);
	    if (pnchisq_raw!T(nx, df, ncp, accu, racc, 100000, 0, 0) < p)
		    ux = nx;
	    else
		    lx = nx;
	}
	while ((ux - lx) / nx > accu);
    }
    return 0.5 * (ux + lx);
}


T rnchisq(T: double)(T df, T lambda)
{
    if (!isFinite(df) || !isFinite(lambda) || df < 0. || lambda < 0.)
	    return T.nan;

    if(lambda == 0.) {
	    return (df == 0.) ? 0. : rgamma!T(df / 2., 2.);
    } else {
	   T r = rpois!T(lambda / 2.);
	   if(r > 0.)  r = rchisq!T(2. * r);
	   if(df > 0.) r += rgamma!T(df / 2., 2.);
	   return r;
    }
}



void test_nchisq()
{
	import std.stdio: writeln;
	writeln("dnchisq: ", dnchisq(2., 3., 7., 0));
	writeln("pnchisq: ", pnchisq(10., 3., 7., 1, 0));
	writeln("qnchisq: ", qnchisq(.6, 3., 7., 1, 0));
	writeln("rnchisq: ", rnchisq(3., 7.), ", rnchisq: ", rnchisq(3., 7.) , ", rnchisq: ", rnchisq(3., 7.));
}

