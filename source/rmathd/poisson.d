module rmathd.poisson;

public import rmathd.common;
public import rmathd.uniform;
public import rmathd.gamma;
public import rmathd.normal;

/*
** dmd poisson.d uniform.d gamma.d common.d normal.d && ./poisson
*/

T dpois(T: double)(T x, T lambda, int give_log)
{
	mixin R_D__0!give_log;
    if(isNaN(x) || isNaN(lambda))
        return x + lambda;

    if (lambda < 0)
    	return T.nan;

    mixin R_D_nonint_check!(x);
    if (x < 0 || !isFinite(x))
	    return R_D__0;

    x = nearbyint(x);

    return( dpois_raw!T(x, lambda, give_log) );
}

T ppois(T: double)(T x, T lambda, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(lambda))
	    return x + lambda;

    if(lambda < 0.)
    	return T.nan;
    if (x < 0)
    	return R_DT_0!T(lower_tail, log_p);
    if (lambda == 0.)
    	return R_DT_1!T(lower_tail, log_p);
    if (!isFinite(x))
    	return R_DT_1!T(lower_tail, log_p);
    x = floor(x + 1e-7);

    return pgamma!T(lambda, x + 1, 1., !lower_tail, log_p);
}

static T do_search(T)(T y, ref T z, T p, T lambda, T incr)
{
    if(z >= p) {
	    		/* search to the left */
	    for(;;) {
	        if(y == 0 || (z = ppois!T(y - incr, lambda, /*l._t.*/1, /*log_p*/0)) < p)
	    	    return y;
	        y = fmax2(0, y - incr);
	    }
    } else {		/* search to the right */
	    for(;;) {
	        y = y + incr;
	        if((z = ppois!T(y, lambda, /*l._t.*/1, /*log_p*/0)) >= p)
	    	    return y;
	    }
    }
}

T qpois(T: double)(T p, T lambda, int lower_tail, int log_p)
{
    T mu, sigma, gamma, z, y;
    if (isNaN(p) || isNaN(lambda))
	    return p + lambda;
    if(!isFinite(lambda))
	    return T.nan;
    if(lambda < 0)
    	return T.nan;
    mixin (R_Q_P01_check!(p)());
    if(lambda == 0)
    	return 0;
    if(p == R_DT_0!T(lower_tail, log_p))
    	return 0;
    if(p == R_DT_1!T(lower_tail, log_p))
    	return T.infinity;

    mixin R_DT_qIv!(p);
    mu = lambda;
    sigma = sqrt(lambda);
    /* gamma = sigma; PR#8058 should be kurtosis which is mu^-0.5 */
    gamma = 1.0/sigma;

    /* Note : "same" code in qpois.c, qbinom.c, qnbinom.c --
     * FIXME: This is far from optimal [cancellation for p ~= 1, etc]: */
    if(!lower_tail || log_p) {
	    p = R_DT_qIv; /* need check again (cancellation!): */
	    if (p == 0.)
	    	return 0;
	    if (p == 1.)
	    	return T.infinity;
    }
    /* temporary hack --- FIXME --- */
    if (p + 1.01*EPSILON!T >= 1.)
    	return T.infinity;

    /* y := approx.value (Cornish-Fisher expansion) :  */
    z = qnorm!T(p, 0., 1., /*lower_tail*/1, /*log_p*/0);
    y = nearbyint(mu + sigma * (z + gamma * (z*z - 1) / 6));

    z = ppois!T(y, lambda, /*lower_tail*/1, /*log_p*/0);

    /* fuzz to ensure left continuity; 1 - 1e-7 may lose too much : */
    p *= 1 - 64*EPSILON!T;

    /* If the mean is not too large a simple search is OK */
    if(lambda < 1e5)
    	return do_search!T(y, z, p, lambda, 1);
    /* Otherwise be a bit cleverer in the search */
    {
	    T incr = floor(y * 0.001);
	    T oldincr;
	    do {
	        oldincr = incr;
	        y = do_search!T(y, z, p, lambda, incr);
	        incr = fmax2(1, floor(incr/100));
	    } while(oldincr > 1 && incr > lambda*1e-15);
	    return y;
    }
}


/* For rpois */
enum a0 = -0.5;
enum a1 =  0.3333333;
enum a2 = -0.2500068;
enum a3 =  0.2000118;
enum a4 = -0.1661269;
enum a5 =  0.1421878;
enum a6 = -0.1384794;
enum a7 =  0.1250060;

enum one_7 = 0.1428571428571428571;
enum one_12 = 0.0833333333333333333;
enum one_24 = 0.0416666666666666667;

T rpois(T: double)(T mu)
{
    /* Factorial Table (0:9)! */
    const static T[10] fact =
    [
	    1., 1., 2., 6., 24., 120., 720., 5040., 40320., 362880.
    ];

    /* These are static --- persistent between calls for same mu : */
    static int l, m;

    static T b1, b2, c, c0, c1, c2, c3;
    static T[36] pp;
    static T p0, p, q, s, d, omega;
    static T big_l;/* integer "w/o overflow" */
    static T muprev = 0., muprev2 = 0.;/*, muold	 = 0.*/

    /* Local Vars  [initialize some for -Wall]: */
    T del, difmuk= 0., E= 0., fk= 0., fx, fy, g, px, py, t, u= 0., v, x;
    T pois = -1.;
    int k, kflag, big_mu, new_big_mu = 0;

    if (!isFinite(mu) || mu < 0)
	    return T.nan;

    if (mu <= 0.)
	   return 0.;

    big_mu = mu >= 10.;
    if(big_mu)
	    new_big_mu = 0;

    if (!(big_mu && mu == muprev)) {/* maybe compute new persistent par.s */

	if (big_mu) {
	    new_big_mu = 1;
	    /* Case A. (recalculation of s,d,l	because mu has changed):
	     * The poisson probabilities pk exceed the discrete normal
	     * probabilities fk whenever k >= m(mu).
	     */
	    muprev = mu;
	    s = sqrt(mu);
	    d = 6. * mu * mu;
	    big_l = floor(mu - 1.1484);
	    /* = an upper bound to m(mu) for all mu >= 10.*/
	}
	else { /* Small mu ( < 10) -- not using normal approx. */

	    /* Case B. (start new table and calculate p0 if necessary) */

	    /*muprev = 0.;-* such that next time, mu != muprev ..*/
	    if (mu != muprev) {
		muprev = mu;
		m = imax2!int(1, cast(int) mu);
		l = 0; /* pp[] is already ok up to pp[l] */
		q = p0 = p = exp(-mu);
	    }

	    for(;;) {
		/* Step U. uniform sample for inversion method */
		u = unif_rand!T();
		if (u <= p0)
		    return 0.;

		/* Step T. table comparison until the end pp[l] of the
		   pp-table of cumulative poisson probabilities
		   (0.458 > ~= pp[9](= 0.45792971447) for mu=10 ) */
		if (l != 0) {
		    for (k = (u <= 0.458) ? 1 : imin2!int(l, m);  k <= l; k++)
			if (u <= pp[k])
			    return k;
		    if (l == 35) /* u > pp[35] */
			continue;
		}
		/* Step C. creation of new poisson
		   probabilities p[l..] and their cumulatives q =: pp[k] */
		l++;
		for (k = l; k <= 35; k++) {
		    p *= mu / k;
		    q += p;
		    pp[k] = q;
		    if (u <= q) {
			l = k;
			return k;
		    }
		}
		l = 35;
	    } /* end(repeat) */
	}/* mu < 10 */

    } /* end {initialize persistent vars} */

/* Only if mu >= 10 : ----------------------- */

    /* Step N. normal sample */
    g = mu + s * norm_rand!T();/* norm_rand() ~ N(0,1), standard normal */

    if (g >= 0.) {
	pois = floor(g);
	/* Step I. immediate acceptance if pois is large enough */
	if (pois >= big_l)
	    return pois;
	/* Step S. squeeze acceptance */
	fk = pois;
	difmuk = mu - fk;
	u = unif_rand!T(); /* ~ U(0,1) - sample */
	if (d * u >= difmuk * difmuk * difmuk)
	    return pois;
    }

    /* Step P. preparations for steps Q and H.
       (recalculations of parameters if necessary) */

    if (new_big_mu || mu != muprev2) {
        /* Careful! muprev2 is not always == muprev
	   because one might have exited in step I or S
	   */
        muprev2 = mu;
	omega = M_1_SQRT_2PI / s;
	/* The quantities b1, b2, c3, c2, c1, c0 are for the Hermite
	 * approximations to the discrete normal probabilities fk. */

	b1 = one_24 / mu;
	b2 = 0.3 * b1 * b1;
	c3 = one_7 * b1 * b2;
	c2 = b2 - 15. * c3;
	c1 = b1 - 6. * b2 + 45. * c3;
	c0 = 1. - b1 + 3. * b2 - 15. * c3;
	c = 0.1069 / mu; /* guarantees majorization by the 'hat'-function. */
    }

    if (g >= 0.) {
	    /* 'Subroutine' F is called (kflag=0 for correct return) */
	    kflag = 0;
	    goto Step_F;
    }


    for(;;) {
	/* Step E. Exponential Sample */

	E = exp_rand!T();	/* ~ Exp(1) (standard exponential) */

	/*  sample t from the laplace 'hat'
	    (if t <= -0.6744 then pk < fk for all mu >= 10.) */
	u = 2 * unif_rand!T() - 1.;
	t = 1.8 + fsign!T(E, u);
	if (t > -0.6744) {
	    pois = floor(mu + s * t);
	    fk = pois;
	    difmuk = mu - fk;

	    /* 'subroutine' F is called (kflag=1 for correct return) */
	    kflag = 1;

	  Step_F: /* 'subroutine' F : calculation of px,py,fx,fy. */

	    if (pois < 10) { /* use factorials from table fact[] */
		px = -mu;
		py = pow(mu, pois) / fact[cast(int)pois];
	    }
	    else {
		/* Case pois >= 10 uses polynomial approximation
		   a0-a7 for accuracy when advisable */
		del = one_12 / fk;
		del = del * (1. - 4.8 * del * del);
		v = difmuk / fk;
		if (fabs(v) <= 0.25)
		    px = fk * v * v * (((((((a7 * v + a6) * v + a5) * v + a4) *
					  v + a3) * v + a2) * v + a1) * v + a0)
			- del;
		else /* |v| > 1/4 */
		    px = fk * log(1. + v) - difmuk - del;
		py = M_1_SQRT_2PI / sqrt(fk);
	    }
	    x = (0.5 - difmuk) / s;
	    x *= x;/* x^2 */
	    fx = -0.5 * x;
	    fy = omega * (((c3 * x + c2) * x + c1) * x + c0);
	    if (kflag > 0) {
		/* Step H. Hat acceptance (E is repeated on rejection) */
		if (c * fabs(u) <= py * exp(px + E) - fy * exp(fx + E))
		    break;
	    } else
		/* Step Q. Quotient acceptance (rare case) */
		if (fy - u * fy <= py * exp(px - fx))
		    break;
	}/* t > -.67.. */
    }
    return pois;
}


void test_poisson()
{
	import std.stdio: write, writeln;
	writeln("dpois: ", dpois(2., 1., 0));
	writeln("ppois: ", ppois(2., 1., 1, 0));
	writeln("qpois: ", qpois(.9, 1., 1, 0));
	writeln("rpois: ", rpois(0.5), ", rpois: ", rpois(0.5), 
		", rpois: ", rpois(0.5), ", rpois: ", rpois(0.5)
		, ", rpois: ", rpois(0.5), ", rpois: ", rpois(0.5));
}
