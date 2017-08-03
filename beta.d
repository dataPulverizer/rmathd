module beta;

import common;
import toms708;

/*
** dmd beta.d common.d && ./beta
*/

T lbeta(T)(T a, T b)
{
    T corr, p, q;

    if(isNaN(a) || isNaN(b))
	    return a + b;

    p = q = a;
    if(b < p) p = b;/* := min(a,b) */
    if(b > q) q = b;/* := max(a,b) */

    /* both arguments must be >= 0 */
    if (p < 0)
	    return T.nan;
    else if (p == 0) {
	return T.infinity;
    }
    else if (!isFinite(q)) { /* q == +Inf */
	return -T.infinity;
    }

    if (p >= 10) {
	    /* p and q are big. */
	    corr = lgammacor!T(p) + lgammacor!T(q) - lgammacor!T(p + q);
	    return log(q) * -0.5 + M_LN_SQRT_2PI + corr + (p - 0.5) * log(p / (p + q)) + q * log1p(-p / (p + q));
    } else if (q >= 10) {
	    /* p is small, but q is big. */
	    corr = lgammacor!T(q) - lgammacor!T(p + q);
	    return lgammafn!T(p) + corr + p - p * log(p + q)
	    	+ (q - 0.5) * log1p(-p / (p + q));
    }
    else {
	/* p and q are small: p <= q < 10. */
	/* R change for very small args */
	if (p < 1e-306)
		return lgamma!T(p) + (lgamma!T(q) - lgamma!T(p + q));
	else return log(gammafn!T(p)*(gammafn!T(q)/gammafn!T(p + q)));
    }
}


auto beta(T)(T a, T b)
{
    //#ifdef NOMORE_FOR_THREADS
    static T xmin, xmax = 0;/*-> typically = 171.61447887 for IEEE */
    static T lnsml = 0;/*-> typically = -708.3964185 */

    if (xmax == 0) {
	    gammalims!T(&xmin, &xmax);
	    lnsml = log(d1mach!T(1));
    }
    //#else
    ///* For IEEE double precision DBL_EPSILON = 2^-52 = 2.220446049250313e-16 :
    // *   xmin, xmax : see ./gammalims.c
    // *   lnsml = log(DBL_MIN) = log(2 ^ -1022) = -1022 * log(2)
    //*/
    //# define xmin  -170.5674972726612
    //# define xmax   171.61447887182298
    //# define lnsml -708.39641853226412
    //#endif

    /* NaNs propagated correctly */
    if(isNaN(a) || isNaN(b))
    	return a + b;

    if (a < 0 || b < 0)
	    return T.nan;
    else if (a == 0 || b == 0)
	    return T.infinity;
    else if (!isFinite(a) || !isFinite(b))
	    return 0;

    if (a + b < xmax) {/* ~= 171.61 for IEEE */
        //	return gammafn(a) * gammafn(b) / gammafn(a+b);
	    /* All the terms are positive, and all can be large for large
	       or small arguments.  They are never much less than one.
	       gammafn(x) can still overflow for x ~ 1e-308,
	       but the result would too.
	    */
	    return (1/gammafn!T(a + b)) * gammafn!T(a) * gammafn!T(b);
    } else {
	    T val = lbeta!T(a, b);
        // underflow to 0 is not harmful per se;  exp(-999) also gives no warning
	    if (val < lnsml) {
	        /* a and/or b so big that beta underflows */
	        //ML_ERROR(ME_UNDERFLOW, "beta");
	        /* return ML_UNDERFLOW; pointless giving incorrect value */
	    }
	    return exp(val);
    }
}


auto dbeta(T)(T x, T a, T b, int give_log)
{
	mixin R_D__0!give_log;
    /* NaNs propagated correctly */
    if (isNaN(x) || isNaN(a) || isNaN(b))
    	return x + a + b;

    if (a < 0 || b < 0)
    	return T.nan;
    if (x < 0 || x > 1)
    	return(R_D__0);

    // limit cases for (a,b), leading to point masses
    if(a == 0 || b == 0 || !isFinite(a) || !isFinite(b)) {
	    if(a == 0 && b == 0) { // point mass 1/2 at each of {0,1} :
	        if (x == 0 || x == 1) 
	            return T.infinity;
	        else 
	            return R_D__0;
	    }
	    if (a == 0 || a/b == 0) { // point mass 1 at 0
	        if (x == 0) return T.infinity; else return R_D__0;
	    }
	    if (b == 0 || b/a == 0) { // point mass 1 at 1
	        if (x == 1) return T.infinity; else return R_D__0;
	    }
	    // else, remaining case:  a = b = Inf : point mass 1 at 1/2
	    if (x == 0.5) return T.infinity; else return R_D__0;
    }

    if (x == 0) {
	if(a > 1)
		return R_D__0;
	if(a < 1)
		return T.infinity;
	/* a == 1 : */ return R_D_val!T(b, give_log);
    }
    if (x == 1) {
	if(b > 1)
		return R_D__0;
	if(b < 1)
		return(T.infinity);
	/* b == 1 : */ return R_D_val!T(a, give_log);
    }

    T lval;
    if (a <= 2 || b <= 2)
	    lval = (a - 1)*log(x) + (b - 1)*log1p(-x) - lbeta!T(a, b);
    else
	    lval = log(a + b - 1) + dbinom_raw!T(a - 1, a + b - 2, x, 1 - x, 1);

    return R_D_exp!T(lval, give_log);
}


T pbeta_raw(T)(T x, T a, T b, int lower_tail, int log_p)
{
    // treat limit cases correctly here:
    if(a == 0 || b == 0 || !isFinite(a) || !isFinite(b)) {
	// NB:  0 < x < 1 :
	if(a == 0 && b == 0) // point mass 1/2 at each of {0,1} :
	    return (log_p ? -M_LN2 : 0.5);
	if (a == 0 || a/b == 0) // point mass 1 at 0 ==> P(X <= x) = 1, all x > 0
	    return R_DT_1!T(lower_tail, log_p);
	if (b == 0 || b/a == 0) // point mass 1 at 1 ==> P(X <= x) = 0, all x < 1
	    return R_DT_0!T(lower_tail, log_p);
	// else, remaining case:  a = b = Inf : point mass 1 at 1/2
	if (x < 0.5)
		return R_DT_0!T(lower_tail, log_p);
	else
		return R_DT_1!T(lower_tail, log_p);
    }
    // Now:  0 < a < Inf;  0 < b < Inf

    T x1 = 0.5 - x + 0.5, w, wc;
    int ierr;
    //====
    bratio!T(a, b, x, x1, &w, &wc, &ierr, log_p); /* -> ./toms708.c */
    //====
    // ierr in {10,14} <==> bgrat() error code ierr-10 in 1:4; for 1 and 4, warned *there*
    //if(ierr && ierr != 11 && ierr != 14)
	//    MATHLIB_WARNING4(_("pbeta_raw(%g, a=%g, b=%g, ..) -> bratio() gave error code %d"), x, a,b, ierr);
    return lower_tail ? w : wc;
} /* pbeta_raw() */

auto pbeta(T)(T x, T a, T b, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(a) || isNaN(b))
    	return x + a + b;

    if (a < 0 || b < 0)
    	return T.nan;
    // allowing a==0 and b==0  <==> treat as one- or two-point mass

    if (x <= 0)
	    return R_DT_0!T(lower_tail, log_p);
    if (x >= 1)
	    return R_DT_1!T(lower_tail, log_p);

    return pbeta_raw!T(x, a, b, lower_tail, log_p);
}

enum USE_LOG_X_CUTOFF = -5.;
enum n_NEWTON_FREE = 4;
enum MLOGICAL_NA = -1;

static const double DBL_very_MIN  = DBL_MIN / 4., 
       DBL_log_v_MIN = M_LN2*(DBL_MIN_EXP - 2), DBL_1__eps = 0x1.fffffffffffffp-1;

enum fpu = 3e-308;
enum acu_min = 1e-300;
enum p_lo = fpu;
enum p_hi = 1-2.22e-16;

enum const1 = 2.30753;
enum const2 = 0.27061;
enum const3 = 0.99229;
enum const4 = 0.04481;

immutable(string) return_q_0(){
	return `if(give_log_q){
	        	qb[0] = T.infinity; qb[1] = 0;
	        } else {
	        	qb[0] = 0; qb[1] = 1;
	        }
	            return;`;
}

immutable(string) return_q_1(){
	return `if(give_log_q){
	         	qb[0] = 0; qb[1] = -T.infinity;
	         } else {
	             qb[0] = 1; qb[1] = 0;
	         }
	         return;`;
}

immutable(string) return_q_half(){
	    return `if(give_log_q)
	                qb[0] = qb[1] = -M_LN2;
	            else
	            	qb[0] = qb[1] = 0.5;
	            return;`;
}

void qbeta_raw(T)(T alpha, T p, T q, int lower_tail, int log_p,
	  int swap_01, // {TRUE, NA, FALSE}: if NA, algorithm decides swap_tail
	  T log_q_cut, /* if == Inf: return log(qbeta(..));
			       otherwise, if finite: the bound for
			       switching to log(x)-scale; see use_log_x */
	  int n_N,  // number of "unconstrained" Newton steps before switching to constrained
	  T *qb) // = qb[0:1] = { qbeta(), 1 - qbeta() }
{
	//Rboolean
    int swap_choose = (swap_01 == MLOGICAL_NA),
	    swap_tail, log_, give_log_q = (log_q_cut == T.infinity),
	    use_log_x = give_log_q, // or u < log_q_cut  below
	    warned = 0, add_N_step = 1;
    int i_pb, i_inn, bad_init, bad_u;
    T adj = 1.;
    T a, la, logbeta, g, h, pp, p_, qq, r, s, t, w, y = -1., u_n;
    T wprev, prev;
    /* volatile */ T u, xinbta;

    // Assuming p >= 0, q >= 0  here ...

    // Deal with boundary cases here:
    if(alpha == R_DT_0!T(lower_tail, log_p)){
        //#define return_q_0						\
        //	if(give_log_q) { qb[0] = ML_NEGINF; qb[1] = 0; }	\
        //	else {           qb[0] = 0;         qb[1] = 1; }	\
        //	return
        mixin (return_q_0());
    }
    if(alpha == R_DT_1!T(lower_tail, log_p)){
        //#define return_q_1						\
        //	if(give_log_q) { qb[0] = 0; qb[1] = ML_NEGINF; }	\
        //	else {           qb[0] = 1; qb[1] = 0;         }	\
        //	return
	    mixin (return_q_1());
    }

    // check alpha {*before* transformation which may all accuracy}:
    if((log_p && alpha > 0) || (!log_p && (alpha < 0 || alpha > 1))) { // alpha is outside
	    //R_ifDEBUG_printf("qbeta(alpha=%g, %g, %g, .., log_p=%d): %s%s\n",
	    //		 alpha, p,q, log_p, "alpha not in ", log_p ? "[-Inf, 0]" : "[0,1]");
	    //ML_ERROR(ME_DOMAIN, "");
	    qb[0] = qb[1] = T.nan; return;
    }

    //  p==0, q==0, p = Inf, q = Inf  <==> treat as one- or two-point mass
    if(p == 0 || q == 0 || !isFinite(p) || !isFinite(q)) {
	    // We know 0 < T(alpha) < 1 : pbeta() is constant and trivial in {0, 1/2, 1}
	    //R_ifDEBUG_printf(
	    //    "qbeta(%g, %g, %g, lower_t=%d, log_p=%d): (p,q)-boundary: trivial\n",  alpha, p,q, lower_tail, log_p);
	    if(p == 0 && q == 0) { // point mass 1/2 at each of {0,1} :
	        if(alpha < R_D_half(log_p)){
	        	return_q_0;
	        }
	        if(alpha > R_D_half(log_p)){
	        	return_q_1;
	        }
	        // else:  alpha == "1/2"
        //#define return_q_half					\
        //	    if(give_log_q) qb[0] = qb[1] = -M_LN2;	\
        //	    else	   qb[0] = qb[1] = 0.5;		\
        //	    return
        
	        mixin (return_q_half());
	    } else if (p == 0 || p/q == 0) { // point mass 1 at 0 - "flipped around"
	        return_q_0;
	    } else if (q == 0 || q/p == 0) { // point mass 1 at 0 - "flipped around"
	        return_q_1;
	    }
	    // else:  p = q = Inf : point mass 1 at 1/2
	    mixin (return_q_half());
    }

    mixin R_DT_qIv!(alpha);
    mixin R_DT_CIv!(alpha);
    /* initialize */
    p_ = R_DT_qIv;/* lower_tail prob (in any case) */
    // Conceptually,  0 < p_ < 1  (but can be 0 or 1 because of cancellation!)
    logbeta = lbeta!T(p, q);

    swap_tail = (swap_choose) ? (p_ > 0.5) : swap_01;
    // change tail; default (swap_01 = NA): afterwards 0 < a <= 1/2
    if(swap_tail) { /* change tail, swap  p <-> q :*/
	    a = R_DT_CIv; // = 1 - p_ < 1/2
	    /* la := log(a), but without numerical cancellation: */
	    la = R_DT_Clog!T(alpha, lower_tail, log_p);
	    pp = q; qq = p;
    }
    else {
	    a = p_;
	    la = R_DT_log!T(alpha, lower_tail);
	    pp = p; qq = q;
    }

    /* calculate the initial approximation */

    /* Desired accuracy for Newton iterations (below) should depend on  (a,p)
     * This is from Remark .. on AS 109, adapted.
     * However, it's not clear if this is "optimal" for IEEE double prec.

     * acu = fmax2(acu_min, pow(10., -25. - 5./(pp * pp) - 1./(a * a)));

     * NEW: 'acu' accuracy NOT for squared adjustment, but simple;
     * ---- i.e.,  "new acu" = sqrt(old acu)
     */
    T acu = fmax2(acu_min, pow(10., -13. - 2.5/(pp * pp) - 0.5/(a * a)));
    // try to catch  "extreme left tail" early
    T tx, u0 = (la + log(pp) + logbeta) / pp; // = log(x_0)
    static const T log_eps_c = M_LN2 * (1. - DBL_MANT_DIG);// = log(DBL_EPSILON) = -36.04..
    r = pp*(1. - qq)/(pp + 1.);

    t = 0.2;
    // FIXME: Factor 0.2 is a bit arbitrary;  '1' is clearly much too much.

    //R_ifDEBUG_printf(
	//"qbeta(%g, %g, %g, lower_t=%d, log_p=%d):%s\n"
	//"  swap_tail=%d, la=%#8g, u0=%#8g (bnd: %g (%g)) ",
	//alpha, p,q, lower_tail, log_p,
	//(log_p && (p_ == 0. || p_ == 1.)) ? (p_==0.?" p_=0":" p_=1") : "",
	//swap_tail, la, u0,
	//(t*log_eps_c - log(fabs(pp*(1.-qq)*(2.-qq)/(2.*(pp+2.)))))/2.,
	// t*log_eps_c - log(fabs(r))
	//);

    if(M_LN2 * DBL_MIN_EXP < u0 && // cannot allow exp(u0) = 0 ==> exp(u1) = exp(u0) = 0
       u0 < -0.01 && // (must: u0 < 0, but too close to 0 <==> x = exp(u0) = 0.99..)
       // qq <= 2 && // <--- "arbitrary"
       // u0 <  t*log_eps_c - log(fabs(r)) &&
       u0 < (t*log_eps_c - log(fabs(pp*(1. - qq)*(2. - qq)/(2.*(pp + 2.)))))/2.)
    {
        // TODO: maybe jump here from below, when initial u "fails" ?
        // L_tail_u:
	    // MM's one-step correction (cheaper than 1 Newton!)
	    r = r*exp(u0);// = r*x0
	    if(r > -1.) {
	        u = u0 - log1p(r)/pp;
	        //R_ifDEBUG_printf("u1-u0=%9.3g --> choosing u = u1\n", u-u0);
	    } else {
	        u = u0;
	        //R_ifDEBUG_printf("cannot cheaply improve u0\n");
	    }
	    tx = xinbta = exp(u);
	    use_log_x = 1; // or (u < log_q_cut)  ??
	    goto L_Newton;
    }

    // y := y_\alpha in AS 64 := Hastings(1955) approximation of qnorm(1 - a) :
    r = sqrt(-2 * la);
    y = r - (const1 + const2 * r) / (1. + (const3 + const4 * r) * r);

    if (pp > 1 && qq > 1) { // use  Carter(1947), see AS 109, remark '5.'
	    r = (y * y - 3.) / 6.;
	    s = 1. / (pp + pp - 1.);
	    t = 1. / (qq + qq - 1.);
	    h = 2. / (s + t);
	    w = y * sqrt(h + r) / h - (t - s) * (r + 5. / 6. - 2. / (3. * h));
	    //R_ifDEBUG_printf("p,q > 1 => w=%g", w);
	    if(w > 300) { // exp(w+w) is huge or overflows
	        t = w+w + log(qq) - log(pp); // = argument of log1pexp(.)
	        u = // log(xinbta) = - log1p(qq/pp * exp(w+w)) = -log(1 + exp(t))
	    	(t <= 18) ? -log1p(exp(t)) : -t - exp(-t);
	        xinbta = exp(u);
	    } else {
	        xinbta = pp / (pp + qq * exp(w + w));
	        u = // log(xinbta)
	    	- log1p(qq/pp * exp(w + w));
	    }
    } else { // use the original AS 64 proposal, Scheffé-Tukey (1944) and Wilson-Hilferty
	r = qq + qq;
	    /* A slightly more stable version of  t := \chi^2_{alpha} of AS 64
	     * t = 1. / (9. * qq); t = r * R_pow_di(1. - t + y * sqrt(t), 3);  */
	    t = 1. / (3. * sqrt(qq));
	    t = r * R_pow_di!T(1. + t*(-t + y), 3);// = \chi^2_{alpha} of AS 64
	    s = 4. * pp + r - 2.;// 4p + 2q - 2 = numerator of new t = (...) / chi^2
	    //R_ifDEBUG_printf("min(p,q) <= 1: t=%g", t);
	    if (t == 0 || (t < 0. && s >= t)) { // cannot use chisq approx
	        // x0 = 1 - { (1-a)*q*B(p,q) } ^{1/q}    {AS 65}
	        // xinbta = 1. - exp((log(1-a)+ log(qq) + logbeta) / qq);
	        T l1ma;/* := log(1-a), directly from alpha (as 'la' above):
	    		 * FIXME: not worth it? log1p(-a) always the same ?? */
	        if(swap_tail)
	    	l1ma = R_DT_log!T(alpha, lower_tail);
	        else
	    	l1ma = R_DT_Clog!T(alpha, lower_tail, log_p);
	        //R_ifDEBUG_printf(" t <= 0 : log1p(-a)=%.15g, better l1ma=%.15g\n", log1p(-a), l1ma);
	        T xx = (l1ma + log(qq) + logbeta) / qq;
	        if(xx <= 0.) {
	    	xinbta = -expm1(xx);
	    	u = R_Log1_Exp!T(xx);// =  log(xinbta) = log(1 - exp(...A...))
	        } else { // xx > 0 ==> 1 - e^xx < 0 .. is nonsense
	    	    //R_ifDEBUG_printf(" xx=%g > 0: xinbta:= 1-e^xx < 0\n", xx);
	    	    xinbta = 0; u = -T.infinity; /// FIXME can do better?
	        }
	    } else {
	        t = s / t;
	        //R_ifDEBUG_printf(" t > 0 or s < t < 0:  new t = %g ( > 1 ?)\n", t);
	        if (t <= 1.) { // cannot use chisq, either
	    	    u = (la + log(pp) + logbeta) / pp;
	    	    xinbta = exp(u);
	        } else { // (1+x0)/(1-x0) = t,  solved for x0 :
	    	    xinbta = 1. - 2. / (t + 1.);
	    	    u = log1p(-2. / (t + 1.));
	        }
	    }
    }

    // Problem: If initial u is completely wrong, we make a wrong decision here
    if(swap_choose && (( swap_tail && u >= -exp(  log_q_cut)) || // ==> "swap back"
	(!swap_tail && u >= -exp(4*log_q_cut) && pp / qq < 1000.) // ==> "swap now"
	   )) {
	// "revert swap" -- and use_log_x
	swap_tail = !swap_tail;
	//R_ifDEBUG_printf(" u = %g (e^u = xinbta = %.16g) ==> ", u, xinbta);
	if(swap_tail) { // "swap now" (much less easily)
	    a = R_DT_CIv; // needed ?
	    la = R_DT_Clog!T(alpha, lower_tail, log_p);
	    pp = q; qq = p;
	}
	else { // swap back :
	    a = p_;
	    la = R_DT_log!T(alpha, lower_tail);
	    pp = p; qq = q;
	}
	//R_ifDEBUG_printf("\"%s\"; la = %g\n", (swap_tail ? "swap now" : "swap back"), la);
	// we could redo computations above, but this should be stable
	u = R_Log1_Exp!T(u);
	xinbta = exp(u);

/* Careful: "swap now"  should not fail if
   1) the above initial xinbta is "completely wrong"
   2) The correction step can go outside (u_n > 0 ==>  e^u > 1 is illegal)
   e.g., for  qbeta(0.2066, 0.143891, 0.05)
*/
    } //else R_ifDEBUG_printf("\n");

    if(!use_log_x)
	use_log_x = (u < log_q_cut);// <==> xinbta = e^u < exp(log_q_cut)
    //Rboolean
    bad_u = !isFinite(u);
    bad_init = bad_u || xinbta > p_hi;

    //R_ifDEBUG_printf(" -> u = %g, e^u = xinbta = %.16g, (Newton acu=%g%s%s%s)\n",
	//	     u, xinbta, acu, (bad_u ? ", ** bad u **" : ""),
	//	     ((bad_init && !bad_u) ? ", ** bad_init **" : ""),
	//	     (use_log_x ? ", on u = LOG(x) SCALE" : ""));

    u_n = 1.; // -Wall
    tx = xinbta; // keeping "original initial x" (for now)

    if(bad_u || u < log_q_cut) {
	    /* e.g.
	       qbeta(0.21, .001, 0.05)
	       try "left border" quickly, i.e.,
	       try at smallest positive number: */
	    w = pbeta_raw!T(DBL_very_MIN, pp, qq, 1, log_p);
	    if(w > (log_p ? la : a)) {
	        //R_ifDEBUG_printf(
	    	//" quantile is left of %g; \"convergence\"\n", DBL_very_MIN);
	        if(log_p || fabs(w - a) < fabs(0 - a)) { // DBL_very_MIN is better than 0
	    	    tx   = DBL_very_MIN;
	    	    u_n  = DBL_log_v_MIN;// = log(DBL_very_MIN)
	        } else {
	    	    tx   = 0.;
	    	    u_n  = -T.infinity;
	        }
	        use_log_x = log_p; add_N_step = 0; goto L_return;
	    } else {
	        //R_ifDEBUG_printf(" pbeta(%g, *) = %g <= %g (= %s) --> continuing\n",
	    	//	     DBL_log_v_MIN, w, (log_p ? la : a), (log_p ? "la" : "a"));
	        if(u  < DBL_log_v_MIN) {
	    	    u = DBL_log_v_MIN;// = log(DBL_very_MIN)
	    	    xinbta = DBL_very_MIN;
	        }
	    }
    }


    /* Sometimes the approximation is negative (and == 0 is also not "ok") */
    if (bad_init && !(use_log_x && tx > 0)) {
	    if(u == -T.infinity) {
	        //R_ifDEBUG_printf("  u = -Inf;");
	        u = M_LN2 * DBL_MIN_EXP;
	        xinbta = DBL_MIN;
	    } else {
	        //R_ifDEBUG_printf(" bad_init: u=%g, xinbta=%g;", u,xinbta);
	        xinbta = (xinbta > 1.1) // i.e. "way off"
	    	? 0.5 // otherwise, keep the respective boundary:
	    	: ((xinbta < p_lo) ? exp(u) : p_hi);
	        if(bad_u)
	    	    u = log(xinbta);
	        // otherwise: not changing "potentially better" u than the above
	    }
	    //R_ifDEBUG_printf(" -> (partly)new u=%g, xinbta=%g\n", u,xinbta);
    }

L_Newton:
    /* --------------------------------------------------------------------

     * Solve for x by a modified Newton-Raphson method, using pbeta_raw()
     */
    r = 1 - pp;
    t = 1 - qq;
    wprev = 0., prev = 1.; // -Wall

    if(use_log_x) { // find  log(xinbta) -- work in  u := log(x) scale
	    // if(bad_init && tx > 0) xinbta = tx;// may have been better
	    for (i_pb = 0; i_pb < 1000; i_pb++) {
	        // using log_p == TRUE  unconditionally here
	        /* FIXME: if exp(u) = xinbta underflows to 0,
	         *  want different formula pbeta_log(u, ..) */
	        y = pbeta_raw!T(xinbta, pp, qq, /*lower_tail = */ 1, 1);
        
	        /* w := Newton step size for   L(u) = log F(e^u)  =!= 0;   u := log(x)
	         *   =  (L(.) - la) / L'(.);  L'(u)= (F'(e^u) * e^u ) / F(e^u)
	         *   =  (L(.) - la)*F(.) / {F'(e^u) * e^u } =
	         *   =  (L(.) - la) * e^L(.) * e^{-log F'(e^u) - u}
	         *   =  ( y   - la) * e^{ y - u -log F'(e^u)}
	         and  -log F'(x)= -log f(x) = - -logbeta + (1-p) log(x) + (1-q) log(1-x)
	                                    = logbeta + (1-p) u + (1-q) log(1-e^u)
	        */
	        w = (y == -T.infinity) // y = -Inf  well possible: we are on log scale!
	    	? 0. : (y - la) * exp(y - u + logbeta + r * u + t * R_Log1_Exp(u));
	        if(!isFinite(w))
	    	break;
	        if (i_pb >= n_N && w * wprev <= 0.)
	    	prev = fmax2!T(fabs(adj),fpu);
	        //R_ifDEBUG_printf(
	    	//"N(i=%2d): u=%#20.16g, pb(e^u)=%#15.9g, w=%#15.9g, %s prev=%g,",
	    	//i_pb, u, y, w, (i_pb >= n_N && w * wprev <= 0.) ? "new" : "old", prev);
	        g = 1;
	        for (i_inn = 0; i_inn < 1000; i_inn++) {
	    	    adj = g * w;
	    	    // safe guard (here, from the very beginning)
	    	    if (fabs(adj) < prev) {
	    	        u_n = u - adj; // u_{n+1} = u_n - g*w
	    	        if (u_n <= 0.) { // <==> 0 <  xinbta := e^u  <= 1
	    	    	if (prev <= acu || fabs(w) <= acu) {
	    	     	    //R_ifDEBUG_printf(" it{in}=%d, -adj=%g, %s <= acu  ==> convergence\n",
	    	    		//i_inn, -adj, (prev <= acu) ? "prev" : "|w|");
	    	    	    goto L_converged;
	    	    	}
	    	    	// if (u_n != ML_NEGINF && u_n != 1)
	    	    	break;
	    	        }
	    	    }
	    	    g /= 3;
	        }
	        // (cancellation in (u_n -u) => may differ from adj:
	        T D = fmin2!T(fabs(adj), fabs(u_n - u));
	        /* R_ifDEBUG_printf(" delta(u)=%g\n", u_n - u); */
	        //R_ifDEBUG_printf(" it{in}=%d, delta(u)=%9.3g, D/|.|=%.3g\n",
	    	//	     i_inn, u_n - u, D/fabs(u_n + u));
	        if (D <= 4e-16 * fabs(u_n + u))
	    	goto L_converged;
	        u = u_n;
	        xinbta = exp(u);
	        wprev = w;
	    } // for(i )
        
    } else { // "normal scale" Newton

	for (i_pb=0; i_pb < 1000; i_pb++) {
	    y = pbeta_raw!T(xinbta, pp, qq, /*lower_tail = */ 1, log_p);
	    // delta{y} :   d_y = y - (log_p ? la : a);
	    if(!isFinite(y) && !(log_p && y == T.infinity))// y = -Inf  is ok if(log_p)
		{ // ML_ERR_return_NAN :
		    //ML_ERROR(ME_DOMAIN, "");
		    qb[0] = qb[1] = T.nan; return;
		}


	    /* w := Newton step size  (F(.) - a) / F'(.)  or,
	     * --   log: (lF - la) / (F' / F) = exp(lF) * (lF - la) / F'
	     */
	    w = log_p
		? (y - la) * exp(y + logbeta + r * log(xinbta) + t * log1p(-xinbta))
		: (y - a)  * exp(    logbeta + r * log(xinbta) + t * log1p(-xinbta));
	    if (i_pb >= n_N && w * wprev <= 0.)
		prev = fmax2!T(fabs(adj),fpu);
	    //R_ifDEBUG_printf(
		//"N(i=%2d): x0=%#17.15g, pb(x0)=%#15.9g, w=%#15.9g, %s prev=%g,",
		//i_pb, xinbta, y, w,
		//(i_pb >= n_N && w * wprev <= 0.) ? "new" : "old", prev);
	    g = 1;
	    for (i_inn = 0; i_inn < 1000; i_inn++) {
		    adj = g * w;
		    // take full Newton steps at the beginning; only then safe guard:
		    if (i_pb < n_N || fabs(adj) < prev) {
		        tx = xinbta - adj; // x_{n+1} = x_n - g*w
		        if (0. <= tx && tx <= 1.) {
		    	if (prev <= acu || fabs(w) <= acu) {
		    	    //R_ifDEBUG_printf(" it{in}=%d, delta(x)=%g, %s <= acu  ==> convergence\n",
		    		//	     i_inn, -adj, (prev <= acu) ? "prev" : "|w|");
		    	    goto L_converged;
		    	}
		    	if (tx != 0. && tx != 1)
		    	    break;
		        }
		    }
		    g /= 3;
	    }
	    //R_ifDEBUG_printf(" it{in}=%d, delta(x)=%g\n", i_inn, tx - xinbta);
	    if (fabs(tx - xinbta) <= 4e-16 * (tx + xinbta)) // "<=" : (.) == 0
		    goto L_converged;
	    xinbta = tx;
	    if(tx == 0) // "we have lost"
		    break;
	    wprev = w;
	} // for( i_pb ..)

    } // end{else : normal scale Newton}

    /*-- NOT converged: Iteration count --*/
    warned = 1;
    //ML_ERROR(ME_PRECISION, "qbeta");

L_converged:
    log_ = log_p || use_log_x; // only for printing
    //R_ifDEBUG_printf(" %s: Final delta(y) = %g%s\n",
	//	     warned ? "_NO_ convergence" : "converged",
	//	     y - (log_ ? la : a), (log_ ? " (log_)" : ""));
    if((log_ && y == -T.infinity) || (!log_ && y == 0)) {
	    // stuck at left, try if smallest positive number is "better"
	    w = pbeta_raw!T(DBL_very_MIN, pp, qq, 1, log_);
	    if(log_ || fabs(w - a) <= fabs(y - a)) {
	        tx  = DBL_very_MIN;
	        u_n = DBL_log_v_MIN;// = log(DBL_very_MIN)
	    }
	    add_N_step = 0; // not trying to do better anymore
    }
    else if(!warned && (log_ ? fabs(y - la) > 3 : fabs(y - a) > 1e-4)) {
	if(!(log_ && y == -T.infinity && pbeta_raw!T(DBL_1__eps, pp, qq, 1, 1) > la + 2))
		doNothing();
	    //MATHLIB_WARNING2( // low accuracy for more platform independent output:
		//"qbeta(a, *) =: x0 with |pbeta(x0,*%s) - alpha| = %.5g is not accurate",
		//(log_ ? ", log_" : ""), fabs(y - (log_ ? la : a)));
    }
L_return:
    if(give_log_q) { // ==> use_log_x , too
	    if(!use_log_x) // (see if claim above is true)
	        //MATHLIB_WARNING(
	    	//"qbeta() L_return, u_n=%g;  give_log_q=TRUE but use_log_x=FALSE -- please report!", u_n);
	    r = R_Log1_Exp!T(u_n);
	    if(swap_tail) {
	        qb[0] = r; qb[1] = u_n;
	    } else {
	        qb[0] = u_n; qb[1] = r;
	    }
    } else {
	if(use_log_x) {
	    if(add_N_step) {
		/* add one last Newton step on original x scale, e.g., for
		   qbeta(2^-98, 0.125, 2^-96) */
		xinbta = exp(u_n);
		y = pbeta_raw!T(xinbta, pp, qq, /*lower_tail = */ 1, log_p);
		w = log_p
		    ? (y - la) * exp(y + logbeta + r * log(xinbta) + t * log1p(-xinbta))
		    : (y - a)  * exp(logbeta + r * log(xinbta) + t * log1p(-xinbta));
		tx = xinbta - w;
		//R_ifDEBUG_printf(" Final Newton correction(non-log scale):\n"
		//						   //   \n  xinbta=%.16g
		//		 "  xinbta=%.16g, y=%g, w=-Delta(x)=%g. \n=> new x=%.16g\n",
		//    xinbta, y, w, tx);
	    } else {
		    if(swap_tail){
		        qb[0] = -expm1(u_n); qb[1] =  exp(u_n);
		    } else {
		        qb[0] =  exp(u_n); qb[1] = -expm1(u_n);
		    }
		    return;
	    }
	}
	    if(swap_tail){
	        qb[0] = 1 - tx; qb[1] = tx;
	    } else {
	        qb[0] = tx;	qb[1] = 1 - tx;
	    }
    }
    return;
}

T qbeta(T)(T alpha, T p, T q, int lower_tail, int log_p)
{

    /* test for admissibility of parameters */
    if (isNaN(p) || isNaN(q) || isNaN(alpha))
	    return p + q + alpha;
    if(p < 0. || q < 0.)
    	return T.nan;
    // allowing p==0 and q==0  <==> treat as one- or two-point mass

    T[2] qbet;// = { qbeta(), 1 - qbeta() }
    qbeta_raw!T(alpha, p, q, lower_tail, log_p, MLOGICAL_NA, USE_LOG_X_CUTOFF, n_NEWTON_FREE, qbet.ptr);
    return qbet[0];
}

enum expmax = (DBL_MAX_EXP * M_LN2); /* = log(DBL_MAX) */

immutable(string) v_w_from__u1_bet_b(){
	    return `v = beta * log(u1 / (1.0 - u1));
	    if (v <= expmax) {
		w = b * exp(v);
		if(!isFinite(w)) w = DBL_MAX;
	    } else
		w = DBL_MAX;`;
}

immutable(string) v_w_from__u1_bet_a(){
	    return `v = beta * log(u1 / (1.0 - u1));
	    if (v <= expmax) {
		w = a * exp(v);
		if(!isFinite(w)) w = DBL_MAX;
	    } else
		w = DBL_MAX;`;
}

auto rbeta(T)(T aa, T bb)
{
    if (isNaN(aa) || isNaN(bb) || aa < 0. || bb < 0.)
	    return T.nan;
    if (!isFinite(aa) && !isFinite(bb)) // a = b = Inf : all mass at 1/2
	    return 0.5;
    if (aa == 0. && bb == 0.) // point mass 1/2 at each of {0,1} :
	    return (unif_rand!T() < 0.5) ? 0. : 1.;
    // now, at least one of a, b is finite and positive
    if (!isFinite(aa) || bb == 0.)
    	return 1.0;
    if (!isFinite(bb) || aa == 0.)
    	return 0.0;

    T a, b, alpha;
    T r, s, t, u1, u2, v, w, y, z;
    int qsame;
    /* FIXME:  Keep Globals (properly) for threading */
    /* Uses these GLOBALS to save time when many rv's are generated : */
    static T beta, gamma, delta, k1, k2;
    static T olda = -1.0;
    static T oldb = -1.0;

    /* Test if we need new "initializing" */
    qsame = (olda == aa) && (oldb == bb);
    if (!qsame) { olda = aa; oldb = bb; }

    a = fmin2(aa, bb);
    b = fmax2(aa, bb); /* a <= b */
    alpha = a + b;

    //#define v_w_from__u1_bet(AA) 			\
    //	    v = beta * log(u1 / (1.0 - u1));	\
    //	    if (v <= expmax) {			\
    //		w = AA * exp(v);		\
    //		if(!R_FINITE(w)) w = DBL_MAX;	\
    //	    } else				\
    //		w = DBL_MAX


    if (a <= 1.0) {	/* --- Algorithm BC --- */

	/* changed notation, now also a <= b (was reversed) */

	if (!qsame) { /* initialize */
	    beta = 1.0 / a;
	    delta = 1.0 + b - a;
	    k1 = delta * (0.0138889 + 0.0416667 * a) / (b * beta - 0.777778);
	    k2 = 0.25 + (0.5 + 0.25 / delta) * a;
	}
	/* FIXME: "do { } while()", but not trivially because of "continue"s:*/
	for(;;) {
	    u1 = unif_rand!T();
	    u2 = unif_rand!T();
	    if (u1 < 0.5) {
		y = u1 * u2;
		z = u1 * y;
		if (0.25 * u2 + z - y >= k1)
		    continue;
	    } else {
		z = u1 * u1 * u2;
		if (z <= 0.25) {
		    mixin (v_w_from__u1_bet_b());
		    break;
		}
		if (z >= k2)
		    continue;
	    }

	    mixin (v_w_from__u1_bet_b());

	    if (alpha * (log(alpha / (a + w)) + v) - 1.3862944 >= log(z))
		break;
	}
	return (aa == a) ? a / (a + w) : w / (a + w);

    } else {		/* Algorithm BB */

	if (!qsame) { /* initialize */
	    beta = sqrt((alpha - 2.0) / (2.0 * a * b - alpha));
	    gamma = a + 1.0 / beta;
	}
	do {
	    u1 = unif_rand!T();
	    u2 = unif_rand!T();

	    mixin (v_w_from__u1_bet_a());

	    z = u1 * u1 * u2;
	    r = gamma * v - 1.3862944;
	    s = a + r - w;
	    if (s + 2.609438 >= 5.0 * z)
		break;
	    t = log(z);
	    if (s > t)
		break;
	} while (r + alpha * log(alpha / (b + w)) < t);

	return (aa != a) ? b / (b + w) : w / (b + w);
    }
}



void test_beta(){
	import std.stdio: writeln;
	writeln("beta: ", beta(2., 4.));
	writeln("dbeta: ", dbeta(.7, 3., 5., 1));
	writeln("pbeta: ", pbeta(.7, 3., 5., 1, 0));
	writeln("qbeta: ", qbeta(.7, 3., 5., 1, 0));
	writeln("rbeta: ", rbeta(3., 5.), ", rbeta: ", rbeta(3., 5.), ", rbeta: ", rbeta(3., 5.));
}
