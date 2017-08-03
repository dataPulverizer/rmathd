module rmathd.gamma;

public import rmathd.common;
public import rmathd.normal;
//import rmathd.uniform;

/*
** dmd gamma.d uniform.d normal.d common.d && ./gamma
*/

T dgamma(T: double)(T x, T shape, T scale, int give_log)
{
    T pr;
    if (isNaN(x) || isNaN(shape) || isNaN(scale))
        return x + shape + scale;

    mixin R_D__0!give_log;

    if (shape < 0 || scale <= 0)
    	return T.nan;
    if (x < 0)
	    return R_D__0;
    if (shape == 0) /* point mass at 0 */
	    return (x == 0)? T.infinity : R_D__0;
    if (x == 0) {
	    if (shape < 1)
	    	return T.infinity;
	    if (shape > 1)
	    	return R_D__0;
	    return give_log ? -log(scale) : 1 / scale;
    }

    if (shape < 1) {
	    pr = dpois_raw!T(shape, x/scale, give_log);
	    return give_log ?  pr + log(shape/x) : pr*shape/x;
    }
    /* else  shape >= 1 */
    pr = dpois_raw!T(shape - 1, x/scale, give_log);
    return give_log ? pr - log(scale) : pr/scale;
}

/* Continued fraction for calculation of
 *    1/i + x/(i+d) + x^2/(i+2*d) + x^3/(i+3*d) + ... = sum_{k=0}^Inf x^k/(i+k*d)
 *
 * auxilary in log1pmx() and lgamma1p()
 */
static T logcf(T)(T x, T i, T d, T eps /* ~ relative tolerance */)
{
    T c1 = 2 * d;
    T c2 = i + d;
    T c4 = c2 + d;
    T a1 = c2;
    T b1 = i * (c2 - i * x);
    T b2 = d * d * x;
    T a2 = c4 * c2 - b2;

    //#if 0
    //    assert(i > 0);
    //    assert(d >= 0);
    //#endif

    b2 = c4 * b1 - i * b2;

    while (fabs(a2 * b1 - a1 * b2) > fabs(eps * b1 * b2)) {
	T c3 = c2*c2*x;
	c2 += d;
	c4 += d;
	a1 = c4 * a2 - c3 * a1;
	b1 = c4 * b2 - c3 * b1;

	c3 = c1 * c1 * x;
	c1 += d;
	c4 += d;
	a2 = c4 * a1 - c3 * a2;
	b2 = c4 * b1 - c3 * b2;

	if (fabs (b2) > scalefactor) {
	    a1 /= scalefactor;
	    b1 /= scalefactor;
	    a2 /= scalefactor;
	    b2 /= scalefactor;
	} else if (fabs (b2) < 1 / scalefactor) {
	    a1 *= scalefactor;
	    b1 *= scalefactor;
	    a2 *= scalefactor;
	    b2 *= scalefactor;
	}
    }

    return a2 / b2;
}

/* Accurate calculation of log(1+x)-x, particularly for small x.  */
T log1pmx(T)(T x)
{
    static const(T) minLog1Value = -0.79149064;

    if (x > 1 || x < minLog1Value)
	    return log1p(x) - x;
    else { /* -.791 <=  x <= 1  -- expand in  [x/(2+x)]^2 =: y :
	    * log(1+x) - x =  x/(2+x) * [ 2 * y * S(y) - x],  with
	    * ---------------------------------------------
	    * S(y) = 1/3 + y/5 + y^2/7 + ... = \sum_{k=0}^\infty  y^k / (2k + 3)
	   */
	    T r = x / (2 + x), y = r * r;
	    if (fabs(x) < 1e-2) {
	        static const(T) two = 2;
	        return r * ((((two / 9 * y + two / 7) * y + two / 5) * y +
	    		    two / 3) * y - x);
	    } else {
	        static const(T) tol_logcf = 1e-14;
	        return r * (2 * y * logcf!T(y, 3, 2, tol_logcf) - x);
	    }
    }
}

/* Compute  log(gamma(a+1))  accurately also for small a (0 < a < 0.5). */
T lgamma1p(T)(T a)
{
    const(T) eulers_const = 0.5772156649015328606065120900824024;

    /* coeffs[i] holds (zeta(i+2)-1)/(i+2) , i = 0:(N-1), N = 40 : */
    const(int) N = 40;
    static const(T)[40] coeffs = [
	0.3224670334241132182362075833230126e-0,/* = (zeta(2)-1)/2 */
	0.6735230105319809513324605383715000e-1,/* = (zeta(3)-1)/3 */
	0.2058080842778454787900092413529198e-1,
	0.7385551028673985266273097291406834e-2,
	0.2890510330741523285752988298486755e-2,
	0.1192753911703260977113935692828109e-2,
	0.5096695247430424223356548135815582e-3,
	0.2231547584535793797614188036013401e-3,
	0.9945751278180853371459589003190170e-4,
	0.4492623673813314170020750240635786e-4,
	0.2050721277567069155316650397830591e-4,
	0.9439488275268395903987425104415055e-5,
	0.4374866789907487804181793223952411e-5,
	0.2039215753801366236781900709670839e-5,
	0.9551412130407419832857179772951265e-6,
	0.4492469198764566043294290331193655e-6,
	0.2120718480555466586923135901077628e-6,
	0.1004322482396809960872083050053344e-6,
	0.4769810169363980565760193417246730e-7,
	0.2271109460894316491031998116062124e-7,
	0.1083865921489695409107491757968159e-7,
	0.5183475041970046655121248647057669e-8,
	0.2483674543802478317185008663991718e-8,
	0.1192140140586091207442548202774640e-8,
	0.5731367241678862013330194857961011e-9,
	0.2759522885124233145178149692816341e-9,
	0.1330476437424448948149715720858008e-9,
	0.6422964563838100022082448087644648e-10,
	0.3104424774732227276239215783404066e-10,
	0.1502138408075414217093301048780668e-10,
	0.7275974480239079662504549924814047e-11,
	0.3527742476575915083615072228655483e-11,
	0.1711991790559617908601084114443031e-11,
	0.8315385841420284819798357793954418e-12,
	0.4042200525289440065536008957032895e-12,
	0.1966475631096616490411045679010286e-12,
	0.9573630387838555763782200936508615e-13,
	0.4664076026428374224576492565974577e-13,
	0.2273736960065972320633279596737272e-13,
	0.1109139947083452201658320007192334e-13/* = (zeta(40+1)-1)/(40+1) */
    ];

    const(T) c = 0.2273736845824652515226821577978691e-12;/* zeta(N+2)-1 */
    const(T) tol_logcf = 1e-14;
    T lgam;
    int i;

    if (fabs (a) >= 0.5)
	    return lgammafn!T(a + 1);

    /* Abramowitz & Stegun 6.1.33 : for |x| < 2,
     * <==> log(gamma(1+x)) = -(log(1+x) - x) - gamma*x + x^2 * \sum_{n=0}^\infty c_n (-x)^n
     * where c_n := (Zeta(n+2) - 1)/(n+2)  = coeffs[n]
     *
     * Here, another convergence acceleration trick is used to compute
     * lgam(x) :=  sum_{n=0..Inf} c_n (-x)^n
     */
    lgam = c * logcf!T(-a / 2, N + 2, 1, tol_logcf);
    for (i = N - 1; i >= 0; i--)
	    lgam = coeffs[i] - a * lgam;

    return (a * lgam - eulers_const) * a - log1pmx!T(a);
} /* lgamma1p */


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
    return fmax2!T(logx, logy) + log1p (exp (-fabs (logx - logy)));
}

/*
 * Compute the log of a difference from logs of terms, i.e.,
 *
 *     log (exp (logx) - exp (logy))
 *
 * without causing overflows and without throwing away large handfuls
 * of accuracy.
 */
T logspace_sub(T)(T logx, T logy)
{
    return logx + R_Log1_Exp!T(logy - logx);
}

/*
 * Compute the log of a sum from logs of terms, i.e.,
 *
 *     log (sum_i  exp (logx[i]) ) =
 *     log (e^M * sum_i  e^(logx[i] - M) ) =
 *     M + log( sum_i  e^(logx[i] - M)
 *
 * without causing overflows or throwing much accuracy.
 */
T logspace_sum(T)(const(T)* logx, int n)
{
    if(n == 0)
        return -T.infinity; // = log( sum(<empty>) )
    if(n == 1)
    	return logx[0];
    if(n == 2)
    	return logspace_add(logx[0], logx[1]);
    // else (n >= 3) :
    int i;
    // Mx := max_i log(x_i)
    T Mx = logx[0];
    for(i = 1; i < n; i++)
    	if(Mx < logx[i]) Mx = logx[i];
    real s = 0.;
    for(i = 0; i < n; i++)
    	s += exp(logx[i] - Mx);
    return Mx + cast(T)log(s);
}

/* dpois_wrap (x__1, lambda) := dpois(x__1 - 1, lambda);  where
 * dpois(k, L) := exp(-L) L^k / gamma(k+1)  {the usual Poisson probabilities}
 *
 * and  dpois*(.., give_log = TRUE) :=  log( dpois*(..) )
*/
static T dpois_wrap(T)(T x_plus_1, T lambda, int give_log)
{
	mixin R_D__0!(give_log);
	mixin M_cutoff!T;
    if (!isFinite(lambda))
	    return R_D__0;
    if (x_plus_1 > 1)
	    return dpois_raw!T(x_plus_1 - 1, lambda, give_log);
    if (lambda > fabs(x_plus_1 - 1) * M_cutoff)
	    return R_D_exp!T(-lambda - lgammafn!T(x_plus_1), give_log);
    else {
	T d = dpois_raw!T(x_plus_1, lambda, give_log);
	return give_log
	    ? d + log(x_plus_1 / lambda)
	    : d * (x_plus_1 / lambda);
    }
}

/*
 * Abramowitz and Stegun 6.5.29 [right]
 */
static T pgamma_smallx(T)(T x, T alph, int lower_tail, int log_p)
{
    T sum = 0, c = alph, n = 0, term;

    /*
     * Relative to 6.5.29 all terms have been multiplied by alph
     * and the first, thus being 1, is omitted.
     */

    do {
	    n++;
	    c *= -x / n;
	    term = c / (alph + n);
	    sum += term;
    } while (fabs(term) > EPSILON!T * fabs(sum));

    if (lower_tail) {
	    T f1 = log_p ? log1p(sum) : 1 + sum;
	    T f2;
	    if (alph > 1) {
	        f2 = dpois_raw!T(alph, x, log_p);
	        f2 = log_p ? f2 + x : f2 * exp (x);
	    } else if (log_p)
	        f2 = alph * log (x) - lgamma1p!T(alph);
	    else
	        f2 = pow(x, alph) / exp (lgamma1p!T(alph));
        
	    return log_p ? f1 + f2 : f1 * f2;
    } else {
	    T lf2 = alph * log (x) - lgamma1p!T(alph);
        
	    if (log_p)
	        return R_Log1_Exp!T(log1p(sum) + lf2);
	    else {
	        T f1m1 = sum;
	        T f2m1 = expm1 (lf2);
	        return -(f1m1 + f2m1 + f1m1 * f2m1);
	    }
    }
} /* pgamma_smallx() */


static T pd_upper_series(T)(T x, T y, int log_p)
{
    T term = x / y;
    T sum = term;

    do {
	    y++;
	    term *= x / y;
	    sum += term;
    } while (term > sum * EPSILON!T);

    /* sum =  \sum_{n=1}^ oo  x^n     / (y*(y+1)*...*(y+n-1))
     *	   =  \sum_{n=0}^ oo  x^(n+1) / (y*(y+1)*...*(y+n))
     *	   =  x/y * (1 + \sum_{n=1}^oo	x^n / ((y+1)*...*(y+n)))
     *	   ~  x/y +  o(x/y)   {which happens when alph -> Inf}
     */
    return log_p ? log(sum) : sum;
}


immutable(string) NEEDED_SCALE(string ctrl)()
{
	immutable(string) output = ctrl ~ `(b2 > scalefactor) {
	                         a1 /= scalefactor;
	                         b1 /= scalefactor;
	                         a2 /= scalefactor;
	                         b2 /= scalefactor;
	                     }`;
	return output;
}


static T pd_lower_cf (T)(T y, T d)
{
    T f = 0.0 /* -Wall */, of, f0;
    T i, c2, c3, c4,  a1, b1,  a2, b2;

    enum max_it = 200000;

    if (y == 0)
    	return 0;

    f0 = y/d;
    /* Needed, e.g. for  pgamma(10^c(100,295), shape= 1.1, log=TRUE): */
    if(fabs(y - 1) < fabs(d) * EPSILON!T) { /* includes y < d = Inf */
	    return (f0);
    }

    if(f0 > 1.) f0 = 1.;
    c2 = y;
    c4 = d; /* original (y,d), *not* potentially scaled ones!*/

    a1 = 0; b1 = 1;
    a2 = y; b2 = d;

    mixin (NEEDED_SCALE!("while")());

    i = 0; of = -1.; /* far away */
    while (i < max_it) {
	    i++;	c2--;	c3 = i * c2;	c4 += 2;
	    /* c2 = y - i,  c3 = i(y - i),  c4 = d + 2i,  for i odd */
	    a1 = c4 * a2 + c3 * a1;
	    b1 = c4 * b2 + c3 * b1;
        
	    i++;	c2--;	c3 = i * c2;	c4 += 2;
	    /* c2 = y - i,  c3 = i(y - i),  c4 = d + 2i,  for i even */
	    a2 = c4 * a1 + c3 * a2;
	    b2 = c4 * b1 + c3 * b2;
        
	    mixin (NEEDED_SCALE!("if")());
        
	    if (b2 != 0) {
	        f = a2 / b2;
	        /* convergence check: relative; "absolute" for very small f : */
	        if (fabs (f - of) <= EPSILON!T * fmax2(f0, fabs(f))) {
	    	    return f;
	        }
	        of = f;
	    }
    }

    return f;/* should not happen ... */
}


static T pd_lower_series(T)(T lambda, T y)
{
    T term = 1, sum = 0;

    while (y >= 1 && term > sum * EPSILON!T) {
	    term *= y / lambda;
	    sum += term;
	    y--;
    }
    /* sum =  \sum_{n=0}^ oo  y*(y-1)*...*(y - n) / lambda^(n+1)
     *	   =  y/lambda * (1 + \sum_{n=1}^Inf  (y-1)*...*(y-n) / lambda^n)
     *	   ~  y/lambda + o(y/lambda)
     */

    if (y != floor(y)) {
	    /*
	     * The series does not converge as the terms start getting
	     * bigger (besides flipping sign) for y < -lambda.
	     */
	    T f;
	    /* FIXME: in quite few cases, adding  term*f  has no effect (f too small)
	     *	  and is unnecessary e.g. for pgamma(4e12, 121.1) */
	    f = pd_lower_cf!T(y, lambda + 1 - y);
	    sum += term * f;
    }

    return sum;
} /* pd_lower_series() */


/*
 * Compute the following ratio with higher accuracy that would be had
 * from doing it directly.
 *
 *		 dnorm (x, 0, 1, FALSE)
 *	   ----------------------------------
 *	   pnorm (x, 0, 1, lower_tail, FALSE)
 *
 * Abramowitz & Stegun 26.2.12
 */
static T dpnorm(T)(T x, int lower_tail, T lp)
{
    /*
     * So as not to repeat a pnorm call, we expect
     *
     *	 lp == pnorm (x, 0, 1, lower_tail, TRUE)
     *
     * but use it only in the non-critical case where either x is small
     * or p==exp(lp) is close to 1.
     */

    if (x < 0) {
	    x = -x;
	    lower_tail = !lower_tail;
    }

    if (x > 10 && !lower_tail) {
	    T term = 1 / x;
	    T sum_ = term;
	    T x2 = x * x;
	    T i = 1;
        
	    do {
	        term *= -i / x2;
	        sum_ += term;
	        i += 2;
	    } while(fabs(term) > EPSILON!T*sum_);
        
	    return 1/sum_;
    } else {
	    T d = dnorm(x, 0., 1., 0);
	    return d/exp(lp);
    }
}

/*
 * Asymptotic expansion to calculate the probability that Poisson variate
 * has value <= x.
 * Various assertions about this are made (without proof) at
 * http://members.aol.com/iandjmsmith/PoissonApprox.htm
 */
static T ppois_asymp(T)(T x, T lambda, int lower_tail, int log_p)
{
    static const(T)[8] coefs_a = [
	-1e99, /* placeholder used for 1-indexing */
	2/3.,
	-4/135.,
	8/2835.,
	16/8505.,
	-8992/12629925.,
	-334144/492567075.,
	698752/1477701225.
    ];

    static const(T)[8] coefs_b = [
	-1e99, /* placeholder */
	1/12.,
	1/288.,
	-139/51840.,
	-571/2488320.,
	163879/209018880.,
	5246819/75246796800.,
	-534703531/902961561600.
    ];

    T elfb, elfb_term;
    T res12, res1_term, res1_ig, res2_term, res2_ig;
    T dfm, pt_, s2pt, f, np;
    int i;

    dfm = lambda - x;
    /* If lambda is large, the distribution is highly concentrated
       about lambda.  So representation error in x or lambda can lead
       to arbitrarily large values of pt_ and hence divergence of the
       coefficients of this approximation.
    */
    pt_ = - log1pmx (dfm / x);
    s2pt = sqrt (2 * x * pt_);
    if (dfm < 0)
    	s2pt = -s2pt;

    res12 = 0;
    res1_ig = res1_term = sqrt (x);
    res2_ig = res2_term = s2pt;
    for (i = 1; i < 8; i++) {
	    res12 += res1_ig * coefs_a[i];
	    res12 += res2_ig * coefs_b[i];
	    res1_term *= pt_ / i ;
	    res2_term *= 2 * pt_ / (2 * i + 1);
	    res1_ig = res1_ig / x + res1_term;
	    res2_ig = res2_ig / x + res2_term;
    }

    elfb = x;
    elfb_term = 1;
    for (i = 1; i < 8; i++) {
	    elfb += elfb_term * coefs_b[i];
	    elfb_term /= x;
    }
    if (!lower_tail)
    	elfb = -elfb;

    f = res12 / elfb;

    np = pnorm(s2pt, 0.0, 1.0, !lower_tail, log_p);

    if (log_p) {
	    T n_d_over_p = dpnorm (s2pt, !lower_tail, np);
	    return np + log1p (f * n_d_over_p);
    } else {
	    T nd = dnorm (s2pt, 0., 1., log_p);
	    return np + f * nd;
    }
} /* ppois_asymp() */

T pgamma_raw(T)(T x, T alph, int lower_tail, int log_p)
{
/* Here, assume that  (x,alph) are not NA  &  alph > 0 . */

    T res;
    mixin R_D__1!log_p;

    mixin R_P_bounds_01!(x, 0., T.infinity);

    if (x < 1) {
	    res = pgamma_smallx!T(x, alph, lower_tail, log_p);
    } else if (x <= alph - 1 && x < 0.8 * (alph + 50)) {
	    /* incl. large alph compared to x */
	    T sum = pd_upper_series!T(x, alph, log_p);/* = x/alph + o(x/alph) */
	    T d = dpois_wrap!T(alph, x, log_p);
	    if (!lower_tail)
	        res = log_p ? R_Log1_Exp!T(d + sum) : 1 - d * sum;
	    else
	        res = log_p ? sum + d : sum * d;
    } else if (alph - 1 < x && alph < 0.8 * (x + 50)) {
	    /* incl. large x compared to alph */
	    T sum;
	    T d = dpois_wrap!T(alph, x, log_p);
	    if (alph < 1) {
	        if (x * EPSILON!T > 1 - alph)
	    	sum = R_D__1;
	        else {
	    	T f = pd_lower_cf!T(alph, x - (alph - 1)) * x / alph;
	    	/* = [alph/(x - alph+1) + o(alph/(x-alph+1))] * x/alph = 1 + o(1) */
	    	sum = log_p ? log (f) : f;
	        }
	    } else {
	        sum = pd_lower_series!T(x, alph - 1);/* = (alph-1)/x + o((alph-1)/x) */
	        sum = log_p ? log1p (sum) : 1 + sum;
	    }
	    if (!lower_tail)
	        res = log_p ? sum + d : sum * d;
	    else
	        res = log_p ? R_Log1_Exp!T(d + sum) : 1 - d * sum;
    } else { /* x >= 1 and x fairly near alph. */
	    res = ppois_asymp!T(alph - 1, x, !lower_tail, log_p);
    }

    /*
     * We lose a fair amount of accuracy to underflow in the cases
     * where the final result is very close to DBL_MIN.	 In those
     * cases, simply redo via log space.
     */
    if (!log_p && res < MIN!T / EPSILON!T) {
	    /* with(.Machine, double.xmin / double.eps) #|-> 1.002084e-292 */
	    return exp(pgamma_raw!T(x, alph, lower_tail, 1));
    } else
	    return res;
}


T pgamma(T: double)(T x, T alph, T scale, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(alph) || isNaN(scale))
	    return x + alph + scale;
    if(alph < 0. || scale <= 0.)
	    return T.nan;
    x /= scale;

    if (isNaN(x)) /* eg. original x = scale = +Inf */
	    return x;

    if(alph == 0.) /* limit case; useful e.g. in pnchisq() */
	    return (x <= 0) ? R_DT_0!T(lower_tail, log_p): R_DT_1!T(lower_tail, log_p); /* <= assert  pgamma(0,0) ==> 0 */
    return pgamma_raw!T(x, alph, lower_tail, log_p);
}


T qchisq_appr(T)(T p, T nu, T g /* = log Gamma(nu/2) */,
		   int lower_tail, int log_p, T tol /* EPS1 */)
{
    enum C7	 = 4.67;
    enum C8	 = 6.66;
    enum C9	 = 6.73;
    enum C10 = 13.32;

    T alpha, a, c, ch, p1;
    T p2, q, t, x;

    /* test arguments and initialise */

    if (isNaN(p) || isNaN(nu))
	   return p + nu;
    mixin (R_Q_P01_check!(p)());
    if (nu <= 0)
    	return T.nan;

    alpha = 0.5 * nu;/* = [pq]gamma() shape */
    c = alpha - 1;

    if(nu < (-1.24)*(p1 = R_DT_log!T(p, lower_tail))) {	/* for small chi-squared */
	    /* log(alpha) + g = log(alpha) + log(gamma(alpha)) =
	     *        = log(alpha*gamma(alpha)) = lgamma(alpha+1) suffers from
	     *  catastrophic cancellation when alpha << 1
	     */
	    T lgam1pa = (alpha < 0.5) ? lgamma1p!T(alpha) : (log(alpha) + g);
	    ch = exp((lgam1pa + p1)/alpha + M_LN2);
    } else if(nu > 0.32) {	/*  using Wilson and Hilferty estimate */
        
	    x = qnorm!T(p, 0, 1, lower_tail, log_p);
	    p1 = 2./(9*nu);
	    ch = nu*pow(x*sqrt(p1) + 1-p1, 3);
        
	    /* approximation for p tending to 1: */
	    if( ch > 2.2*nu + 6 )
	        ch = -2*(R_DT_Clog!T(p, lower_tail, log_p) - c*log(0.5*ch) + g);
        
    } else { /* "small nu" : 1.24*(-log(p)) <= nu <= 0.32 */
        
	    ch = 0.4;
	    a = R_DT_Clog!T(p, lower_tail, log_p) + g + c*M_LN2;
        
	    do {
	        q = ch;
	        p1 = 1. / (1 + ch*(C7 + ch));
	        p2 = ch*(C9 + ch*(C8 + ch));
	        t = -0.5 +(C7 + 2*ch)*p1 - (C9 + ch*(C10 + 3*ch))/p2;
	        ch -= (1 - exp(a + 0.5*ch)*p2*p1)/t;
	    } while(fabs(q - ch) > tol * fabs(ch));
    }

    return ch;
}

T qgamma(T: double)(T p, T alpha, T scale, int lower_tail, int log_p)
/*			shape = alpha */
{
    enum EPS1 = 1e-2;
    enum EPS2 = 5e-7; /* final precision of AS 91 */
    enum EPS_N = 1e-15; /* precision of Newton step / iterations */
    enum LN_EPS = -36.043653389117156; /* = log(.Machine$double.eps) iff IEEE_754 */

    enum MAXIT = 1000; /* was 20 */

    enum pMIN = 1e-100; /* was 0.000002 = 2e-6 */
    enum pMAX = (1-1e-14); /* was (1-1e-12) and 0.999998 = 1 - 2e-6 */

    mixin R_D__0!log_p;

    const static T
	i420  = 1./ 420.,
	i2520 = 1./ 2520.,
	i5040 = 1./ 5040;

    T p_, a, b, c, g, ch, ch0, p1;
    T p2, q, s1, s2, s3, s4, s5, s6, t, x;
    int i, max_it_Newton = 1;

    /* test arguments and initialise */

    if (isNaN(p) || isNaN(alpha) || isNaN(scale))
	    return p + alpha + scale;

    mixin R_Q_P01_boundaries!(p, 0., T.infinity);

    if (alpha < 0 || scale <= 0)
    	return T.nan;

    if (alpha == 0) /* all mass at 0 : */ 
    	return 0.;

    if (alpha < 1e-10) {
    /* Warning seems unnecessary now: */
	    max_it_Newton = 7;/* may still be increased below */
    }

    mixin R_DT_qIv!(p);
    p_ = R_DT_qIv;/* lower_tail prob (in any case) */

    g = lgammafn!T(alpha);/* log Gamma(v/2) */

    /*----- Phase I : Starting Approximation */
    ch = qchisq_appr!T(p, /* nu= 'df' =  */ 2*alpha, /* lgamma(nu/2)= */ g,
		     lower_tail, log_p, /* tol= */ EPS1);
    if(!isFinite(ch)) {
	    /* forget about all iterations! */
	    max_it_Newton = 0; goto END;
    }
    if(ch < EPS2) {/* Corrected according to AS 91; MM, May 25, 1999 */
	    max_it_Newton = 20;
	    goto END;/* and do Newton steps */
    }

    /* FIXME: This (cutoff to {0, +Inf}) is far from optimal
     * -----  when log_p or !lower_tail, but NOT doing it can be even worse */
    if(p_ > pMAX || p_ < pMIN) {
	    /* did return ML_POSINF or 0.;	much better: */
	    max_it_Newton = 20;
	    goto END;/* and do Newton steps */
    }

/*----- Phase II: Iteration
 *	Call pgamma() [AS 239]	and calculate seven term taylor series
 */
    c = alpha - 1;
    s6 = (120 + c*(346 + 127*c)) * i5040; /* used below, is "const" */

    ch0 = ch;/* save initial approx. */
    for(i=1; i <= MAXIT; i++ ) {
	q = ch;
	p1 = 0.5*ch;
	p2 = p_ - pgamma_raw!T(p1, alpha, /*lower_tail*/1, /*log_p*/0);

	if(!isFinite(p2) || ch <= 0)
	{
		ch = ch0; max_it_Newton = 27; goto END; 
	}/*was  return ML_NAN;*/

	t = p2*exp(alpha*M_LN2 + g + p1 - c*log(ch));
	b = t/ch;
	a = 0.5*t - b*c;
	s1 = (210 + a*(140 + a*(105 + a*(84 + a*(70 + 60*a))))) * i420;
	s2 = (420 + a*(735 + a*(966 + a*(1141 + 1278*a)))) * i2520;
	s3 = (210 + a*(462 + a*(707 + 932*a))) * i2520;
	s4 = (252 + a*(672 + 1182*a) + c*(294 + a*(889 + 1740*a))) * i5040;
	s5 = (84 + 2264*a + c*(1175 + 606*a)) * i2520;

	ch += t*(1 + 0.5*t*s1 - b*c*(s1 - b*(s2 - b*(s3 - b*(s4 - b*(s5 - b*s6))))));
	if(fabs(q - ch) < EPS2*ch)
	    goto END;
	if(fabs(q - ch) > 0.1*ch) {/* diverging? -- also forces ch > 0 */
	    if(ch < q) ch = 0.9 * q; else ch = 1.1 * q;
	}
    }
/* no convergence in MAXIT iterations -- but we add Newton now... */
/* was
 *    ML_ERROR(ME_PRECISION, "qgamma");
 * does nothing in R !*/

END:
/* PR# 2214 :	 From: Morten Welinder <terra@diku.dk>, Fri, 25 Oct 2002 16:50
   --------	 To: R-bugs@biostat.ku.dk     Subject: qgamma precision

   * With a final Newton step, double accuracy, e.g. for (p= 7e-4; nu= 0.9)
   *
   * Improved (MM): - only if rel.Err > EPS_N (= 1e-15);
   *		    - also for lower_tail = FALSE	 or log_p = TRUE
   *		    - optionally *iterate* Newton
   */
    x = 0.5*scale*ch;
    if(max_it_Newton) {
	/* always use log scale */
	if (!log_p) {
	    p = log(p);
	    log_p = 1;
	}
	if(x == 0) {
	    const T _1_p = 1. + 1e-7;
	    const T _1_m = 1. - 1e-7;
	    x = MIN!T;
	    p_ = pgamma!T(x, alpha, scale, lower_tail, log_p);
	    if(( lower_tail && p_ > p * _1_p) ||
	       (!lower_tail && p_ < p * _1_m))
		return(0.);
	    /* else:  continue, using x = DBL_MIN instead of  0  */
	}
	else
	    p_ = pgamma!T(x, alpha, scale, lower_tail, log_p);
	if(p_ == -T.infinity)
		return 0; /* PR#14710 */
	for(i = 1; i <= max_it_Newton; i++) {
	    p1 = p_ - p;
	    if(fabs(p1) < fabs(EPS_N * p))
		break;
	    /* else */
	    if((g = dgamma!T(x, alpha, scale, log_p)) == R_D__0) {
		    break;
	    }
	    /* else :
	     * delta x = f(x)/f'(x);
	     * if(log_p) f(x) := log P(x) - p; f'(x) = d/dx log P(x) = P' / P
	     * ==> f(x)/f'(x) = f*P / P' = f*exp(p_) / P' (since p_ = log P(x))
	     */
	    t = log_p ? p1*exp(p_ - g) : p1/g ;/* = "delta x" */
	    t = lower_tail ? x - t : x + t;
	    p_ = pgamma!T(t, alpha, scale, lower_tail, log_p);
	    if (fabs(p_ - p) > fabs(p1) ||
		(i > 1 && fabs(p_ - p) == fabs(p1)) /* <- against flip-flop */) {
		    /* no improvement */
		    break;
	    } /* else : */
//#ifdef Harmful_notably_if_max_it_Newton_is_1
	    /* control step length: this could have started at
	       the initial approximation */
	    //if(t > 1.1*x) t = 1.1*x;
	    //else if(t < 0.9*x) t = 0.9*x;
//#endif
	    x = t;
	}
    }

    return x;
}


T rgamma(T: double)(T a, T scale)
{
/* Constants : */
    const static T sqrt32 = 5.656854;
    const static T exp_m1 = 0.36787944117144232159;/* exp(-1) = 1/e */

    /* Coefficients q[k] - for q0 = sum(q[k]*a^(-k))
     * Coefficients a[k] - for q = q0+(t*t/2)*sum(a[k]*v^k)
     * Coefficients e[k] - for exp(q)-1 = sum(e[k]*q^k)
     */
    const static T q1 = 0.04166669;
    const static T q2 = 0.02083148;
    const static T q3 = 0.00801191;
    const static T q4 = 0.00144121;
    const static T q5 = -7.388e-5;
    const static T q6 = 2.4511e-4;
    const static T q7 = 2.424e-4;

    const static T a1 = 0.3333333;
    const static T a2 = -0.250003;
    const static T a3 = 0.2000062;
    const static T a4 = -0.1662921;
    const static T a5 = 0.1423657;
    const static T a6 = -0.1367177;
    const static T a7 = 0.1233795;

    /* State variables [FIXME for threading!] :*/
    static T aa = 0.;
    static T aaa = 0.;
    static T s, s2, d;    /* no. 1 (step 1) */
    static T q0, b, si, c;/* no. 2 (step 4) */

    T e, p, q, r, t, u, v, w, x, ret_val;

    if (isNaN(a) || isNaN(scale))
	    return T.nan;
    if (a <= 0.0 || scale <= 0.0) {
	if(scale == 0. || a == 0.) return 0.;
	    return T.nan;
    }
    if(!isFinite(a) || !isFinite(scale))
    	return T.infinity;

    if (a < 1.) { /* GS algorithm for parameters a < 1 */
	    e = 1.0 + exp_m1 * a;
	    for(;;) {
	        p = e * unif_rand!T();
	        if (p >= 1.0) {
	    	x = -log((e - p) / a);
	    	if (exp_rand!T() >= (1.0 - a) * log(x))
	    	    break;
	        } else {
	    	x = exp(log(p) / a);
	    	if (exp_rand!T() >= x)
	    	    break;
	        }
	    }
	    return scale * x;
    }

    /* --- a >= 1 : GD algorithm --- */

    /* Step 1: Recalculations of s2, s, d if a has changed */
    if (a != aa) {
	    aa = a;
	    s2 = a - 0.5;
	    s = sqrt(s2);
	    d = sqrt32 - s * 12.0;
    }
    /* Step 2: t = standard normal deviate,
               x = (s,1/2) -normal deviate. */

    /* immediate acceptance (i) */
    t = norm_rand!T();
    x = s + 0.5 * t;
    ret_val = x * x;
    if (t >= 0.0)
	return scale * ret_val;

    /* Step 3: u = 0,1 - uniform sample. squeeze acceptance (s) */
    u = unif_rand!T();
    if (d * u <= t * t * t)
	return scale * ret_val;

    /* Step 4: recalculations of q0, b, si, c if necessary */

    if (a != aaa) {
	    aaa = a;
	    r = 1.0 / a;
	    q0 = ((((((q7 * r + q6) * r + q5) * r + q4) * r + q3) * r
	           + q2) * r + q1) * r;
        
	    /* Approximation depending on size of parameter a */
	    /* The constants in the expressions for b, si and c */
	    /* were established by numerical experiments */
        
	    if (a <= 3.686) {
	        b = 0.463 + s + 0.178 * s2;
	        si = 1.235;
	        c = 0.195 / s - 0.079 + 0.16 * s;
	    } else if (a <= 13.022) {
	        b = 1.654 + 0.0076 * s2;
	        si = 1.68 / s + 0.275;
	        c = 0.062 / s + 0.024;
	    } else {
	        b = 1.77;
	        si = 0.75;
	        c = 0.1515 / s;
	    }
    }
    /* Step 5: no quotient test if x not positive */

    if (x > 0.0) {
	/* Step 6: calculation of v and quotient q */
	v = t / (s + s);
	if (fabs(v) <= 0.25)
	    q = q0 + 0.5 * t * t * ((((((a7 * v + a6) * v + a5) * v + a4) * v
				      + a3) * v + a2) * v + a1) * v;
	else
	    q = q0 - s * t + 0.25 * t * t + (s2 + s2) * log(1.0 + v);


	/* Step 7: quotient acceptance (q) */
	if (log(1.0 - u) <= q)
	    return scale * ret_val;
    }

    for(;;) {
	/* Step 8: e = standard exponential deviate
	 *	u =  0,1 -uniform deviate
	 *	t = (b,si)-double exponential (laplace) sample */
	e = exp_rand!T();
	u = unif_rand!T();
	u = u + u - 1.0;
	if (u < 0.0)
	    t = b - si * e;
	else
	    t = b + si * e;
	/* Step	 9:  rejection if t < tau(1) = -0.71874483771719 */
	if (t >= -0.71874483771719) {
	    /* Step 10:	 calculation of v and quotient q */
	    v = t / (s + s);
	    if (fabs(v) <= 0.25)
		q = q0 + 0.5 * t * t *
		    ((((((a7 * v + a6) * v + a5) * v + a4) * v + a3) * v
		      + a2) * v + a1) * v;
	    else
		q = q0 - s * t + 0.25 * t * t + (s2 + s2) * log(1.0 + v);
	    /* Step 11:	 hat acceptance (h) */
	    /* (if q not positive go to step 8) */
	    if (q > 0.0) {
		w = expm1(q);
		/*  ^^^^^ original code had approximation with rel.err < 2e-7 */
		/* if t is rejected sample again at step 8 */
		if (c * fabs(u) <= w * exp(e - 0.5 * t * t))
		    break;
	    }
	}
    } /* repeat .. until  `t' is accepted */
    x = s + 0.5 * t;
    return scale * x * x;
}


void test_gamma()
{
	import std.stdio: write, writeln;
	writeln("dgamma: ", dgamma(1., 1., 1., 0));
	writeln("pgamma: ", pgamma(1., 1., 1., 1, 0));
	writeln("qgamma: ", qgamma(0.5, 1., 1., 1, 0));
	writeln("rgamma: ", rgamma(1., 1.), ", rgamma: ", rgamma(1., 1.) , ", rgamma: ", rgamma(1., 1.));
}
