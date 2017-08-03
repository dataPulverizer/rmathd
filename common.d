module common;

public import std.math: sin, cos, tan, atan, sqrt, exp, expm1, log, isNaN, isFinite, ldexp, nearbyint, floor,
                        round, abs, fabs, fmod, trunc, log1p, pow, ceil;
public import core.stdc.math: lgammaf, lgammal;
public import core.stdc.float_ : FLT_MIN_EXP, FLT_MANT_DIG, LDBL_MIN_EXP, DBL_MIN_EXP, DBL_MANT_DIG, LDBL_MANT_DIG,
                          FLT_MIN, DBL_MIN, LDBL_MIN, FLT_MAX, DBL_MAX, LDBL_MAX, FLT_EPSILON, DBL_EPSILON,
                          LDBL_EPSILON, FLT_MAX_EXP, DBL_MAX_EXP, LDBL_MAX_EXP, FLT_RADIX;

enum M_PI = 3.141592653589793238462643383280;
enum M_LN2 = 0.693147180559945309417232121458;
enum M_2PI = 6.283185307179586476925286766559;
enum M_LN10 = 2.302585092994045684017991454684;
enum M_1_PI = 0.318309886183790671537767526745;
enum M_PI_2 = 1.570796326794896619231321691640;
enum M_SQRT2 = 1.414213562373095048801688724210;
enum M_LN_2PI = 1.837877066409345483560659472811;
enum M_LOG10_2 = 0.301029995663981195213738894724;
enum M_SQRT_32 = 5.656854249492380195206754896838;
enum M_SQRT_PI = 1.772453850905516027298167483341;
enum M_SQRT_2dPI = 0.797884560802865355879892119869;
enum M_1_SQRT_2PI = 0.398942280401432677939946059934;
enum M_LN_SQRT_PI = 0.572364942924700087071713675677;
enum M_LN_SQRT_2PI = 0.918938533204672741780329736406;
enum M_LN_SQRT_PId2	= 0.225791352644727432363097614947;
enum CHAR_BIT = 8;
enum INT_MAX = int.max;

enum N01type {
    BUGGY_KINDERMAN_RAMAGE,
    AHRENS_DIETER,
    BOX_MULLER,
    USER_NORM,
    INVERSION,
    KINDERMAN_RAMAGE
}

enum BUGGY_KINDERMAN_RAMAGE = N01type.BUGGY_KINDERMAN_RAMAGE;
enum AHRENS_DIETER = N01type.AHRENS_DIETER;
enum BOX_MULLER = N01type.BOX_MULLER;
enum USER_NORM = N01type.USER_NORM;
enum INVERSION = N01type.INVERSION;
enum KINDERMAN_RAMAGE = N01type.KINDERMAN_RAMAGE;

void doNothing(){};

T fmax2(T)(T x, T y)
{
    if (isNaN(x) || isNaN(y))
        return x + y;
    return (x < y) ? y : x;
}

T max(T)(T x, T y)
{
    return (x < y) ? y : x;
}

alias imax2 = max;

T min(T)(T x, T y)
{
    return (x < y) ? x : y;
}
alias imin2 = min;

T fmin2(T)(T x, T y)
{
    if (isNaN(x) || isNaN(y))
        return x + y;
    return (x < y) ? x : y;
}

T fsign(T)(T x, T y)
{
    if (isNaN(x) || isNaN(y))
	    return x + y;
    return ((y >= 0) ? fabs(x) : -fabs(x));
}

/* lgamma float, double, real */
T lgamma(T: float)(T x)
{
    return lgammaf(x);
}

T lgamma(T: double)(T x)
{
    import core.stdc.math: lgamma;
    return lgamma(x);
}

T lgamma(T: real)(T x)
{
    return lgammal(x);
}


template SQR(T)
{
	auto SQR(T x)
	{
		return x*x;
	}
}

enum scalefactor = SQR(SQR(SQR(4294967296.0)));

template R_Log1_Exp(T)
{
    auto R_Log1_Exp(T x)
    {
    	return (x > -M_LN2 ? log(-expm1(x)) : log1p(-exp(x)));
    }
}

template R_DT_Log(T)
{
    auto R_DT_Log(T p, int lower_tail)
    {
        return (lower_tail? p : R_Log1_Exp!T(p));
    }
}

template R_D_exp(T)
{
	auto R_D_exp(T x, int log_p)
	{
		return (log_p ? x : exp(x));
	}
}

template R_D_log(T)
{
	auto R_D_log(T p, int log_p)
	{
		return (log_p ? p : log(p));
	}
}

template R_D_fexp(T)
{
	auto R_D_fexp(T f, T x, int give_log)
	{
		return (give_log ? -0.5*log(f) + x : exp(x)/sqrt(f));
	}
}

template MIN_EXP(T)
{
    static if(is(T : double))
        enum MIN_EXP = DBL_MIN_EXP;
    else static if(is(T : real))
        enum MIN_EXP = LDBL_MIN_EXP;
    else
        enum MIN_EXP = FLT_MIN_EXP;
}

template MANT_DIG(T)
{
    static if(is(T : double))
        enum MANT_DIG = DBL_MANT_DIG;
    else static if(is(T : real))
        enum MANT_DIG = LDBL_MANT_DIG;
    else
        enum MANT_DIG = FLT_MANT_DIG;
}

template MIN(T)
{
    static if(is(T : double))
        enum MIN = DBL_MIN;
    else static if(is(T : real))
        enum MIN = LDBL_MIN;
    else
        enum MIN = FLT_MIN;
}

template MAX(T)
{
    static if(is(T : double))
        enum MAX = DBL_MAX;
    else static if(is(T : real))
        enum MAX = LDBL_MAX;
    else
        enum MAX = FLT_MAX;
}

template EPSILON(T)
{
    static if(is(T : double))
        enum EPSILON = DBL_EPSILON;
    else static if(is(T : real))
        enum EPSILON = LDBL_EPSILON;
    else
        enum EPSILON = FLT_EPSILON;
}

template MAX_EXP(T)
{
    static if(is(T : double))
        enum MAX_EXP = DBL_MAX_EXP;
    else static if(is(T : real))
        enum MAX_EXP = LDBL_MAX_EXP;
    else
        enum MAX_EXP = FLT_MAX_EXP;
}

//static const double M_cutoff = M_LN2 * MAX_EXP!T/EPSILON!T;/*=3.196577e18*/

mixin template M_cutoff(T)
{
	static const(T) M_cutoff = M_LN2 * MAX_EXP!T/EPSILON!T;
}



mixin template R_D__0(alias log_p)
{
    T R_D__0 = (log_p ? -T.infinity : 0.);
}


mixin template R_D__1(alias log_p)
{
    T R_D__1 = (log_p ? 0. : 1.);
}

template R_D_val(T)
{
	auto R_D_val (T x, int log_p)
	{
		return (log_p ? log(x) : x);
	}
}

template R_D_Clog(T)
{
    auto R_D_Clog(T p, int log_p)
    {
        return (log_p ? log1p(-p) : (0.5 - p + 0.5));
    }
}

template R_DT_val(T)
{
    auto R_DT_val(T x, int lower_tail, int log_p)
    {
        return (lower_tail ? R_D_val!T(x, log_p) : R_D_Clog!T(x, log_p));
    }
}

template R_D_qIv(T)
{
    auto R_D_qIv(T p, int log_p)
    {
        return (log_p ? exp(p) : p);
    }
}

template R_DT_0(T)
{
    auto R_DT_0(int lower_tail, int log_p)
    {
        mixin R_D__0!log_p;
        mixin R_D__1!log_p;
        return (lower_tail ? R_D__0 : R_D__1);
    }
}


/*
template R_DT_0(alias lower_tail, alias log_p)
{
    mixin R_D__0!log_p;
    mixin R_D__1!log_p;
    T R_DT_0 = (lower_tail ? R_D__0 : R_D__1);
}
*/


template R_DT_1(T)
{
    auto R_DT_1(int lower_tail, int log_p)
    {
        mixin R_D__0!log_p;
        mixin R_D__1!log_p;
        return (lower_tail ? R_D__1 : R_D__0);
    }
}


auto R_D_half(int log_p){
    return (log_p ? -M_LN2 : 0.5);
}


/*
template R_DT_1(alias lower_tail, alias log_p)
{
    mixin R_D__0!log_p;
    mixin R_D__1!log_p;
    T R_DT_1 = (lower_tail ? R_D__1 : R_D__0);
}
*/

/* Mixin technique! */

/*
mixin template R_D_Lval(alias p)
{
    T R_D_Lval = (lower_tail ? (p) : (0.5 - p + 0.5));
}

mixin template R_DT_qIv(alias p)
{
    mixin R_D_Lval!(p);
    T R_DT_qIv = (log_p ? (lower_tail ? exp(p) : - expm1(p)) : R_D_Lval);
}
*/

template R_D_Lval(T)
{
    auto R_D_Lval(T p, int lower_tail)
    {
        return (lower_tail ? p : (0.5 - p + 0.5));
    }
}

mixin template R_DT_qIv(alias p)
{
    T R_DT_qIv = (log_p ? (lower_tail ? exp(p) : - expm1(p)) : R_D_Lval!T(p, lower_tail));
}


mixin template R_D_Cval(alias p)
{
    T R_D_Cval = (lower_tail ? (0.5 - p + 0.5) : p);
}

mixin template R_DT_CIv(alias p)
{
    mixin R_D_Cval!(p);
    T R_DT_CIv = (log_p ? (lower_tail ? -expm1(p) : exp(p)) : R_D_Cval);
}

template R_Q_P01_boundaries(alias p, alias LEFT, alias RIGHT)
{
    immutable(string) R_Q_P01_boundaries(){
        return `if (log_p) {
        if(p > 0)
            return T.nan;
        if(p == 0) /* upper bound*/
            return lower_tail ? ` ~ RIGHT.stringof ~ ` : ` ~ LEFT.stringof ~ `;
        if(p == -T.infinity)
            return lower_tail ? `~ LEFT.stringof ~ ` : ` ~ RIGHT.stringof ~ `;
        } else { /* !log_p */
        if(p < 0 || p > 1)
            return T.nan;
        if(p == 0)
            return lower_tail ? ` ~ LEFT.stringof ~ ` : ` ~ RIGHT.stringof ~ `;
        if(p == 1)
            return lower_tail ? ` ~ RIGHT.stringof ~ ` : ` ~ LEFT.stringof ~ `;
        }`;
    }
}

template R_Q_P01_check(alias p)
{
	immutable(string) R_Q_P01_check(){
	    return `if ((log_p	&& ` ~ p.stringof ~ ` > 0) || (!log_p && (` ~ p.stringof ~ ` < 0 || ` ~ p.stringof ~ ` > 1)))
	            return T.nan;`;
	}
}

template R_P_bounds_01(alias x, alias x_min, alias x_max)
{
    immutable(string) R_P_bounds_01(){
    	return `if(` ~ x.stringof ~ ` <= ` ~ x_min.stringof ~ `) return R_DT_0!T(lower_tail, log_p);
               if(` ~ x.stringof ~ ` >= ` ~ x_max.stringof ~ `) return R_DT_1!T(lower_tail, log_p);`;
    }
}

/* is typically not quite optimal for (-Inf,Inf) where
 * you'd rather have */
template R_P_bounds_Inf_01(alias x)
{
    immutable(string) R_P_bounds_Inf_01(){
        return `if(!isFinite(` ~ x.stringof ~ `)) {
                    if (` ~ x.stringof ~ ` > 0) return R_DT_1!T(lower_tail, log_p);
                    return R_DT_0!T(lower_tail, log_p);
                }`;
    }
}


template R_D_LExp(T)
{
    auto R_D_LExp(T x, int log_p)
    {
    	return (log_p ? R_Log1_Exp!T(x) : log1p(-x));
    }
}

template R_DT_Clog(T)
{
    auto R_DT_Clog(T p, int lower_tail, int log_p)
    {
    	return (lower_tail? R_D_LExp!T(p, log_p): R_D_log!T(p, lower_tail)); /* log(1-p) in qF*/
    }
}


template R_DT_log(T)
{
    auto R_DT_log(T p, int lower_tail)
    {
    	return (lower_tail? R_D_log!T(p, lower_tail) : R_D_LExp!T(p, lower_tail));
    }
}

auto R_pow_di(T)(T x, int n)
{
    T pow_ = 1.0;

    if (isNaN(x)) return x;
    if (n != 0) {
        if (!isFinite(x))
            return pow(x, cast(T)n);
        if (n < 0) {
            n = -n; x = 1/x;
        }
        for(;;) {
            if(n & 01)
                pow_ *= x;
            if(n >>= 1)
                x *= x;
            else
                break;
        }
    }
    return pow_;
}


template R_nonint(T){
	auto R_nonint(T x){
		return (fabs(x - nearbyint(x)) > 1e-7*fmax2!T(1., fabs(x)));
	}
}


template R_D_negInonint(T)
{
    auto R_D_negInonint(T x)
    {
    	return (x < 0. || R_nonint!T(x));
    }
}

/*
template R_D_Lval(T)
{
	auto R_D_Lval(T p, T lower_tail){
		return (lower_tail ? p : (0.5 - p + 0.5));
	}
}
*/

/*
template R_DT_qIv(T)
{
	auto R_DT_qIv(T p, T log_p, T lower_tail){
		return (log_p ? (lower_tail ? exp(p) : - expm1(p)) : R_D_Lval!T(p, lower_tail));
	}
}
*/

template R_D_nonint_check(alias x){
    enum R_D_nonint_check = `if(R_nonint(` ~ x.stringof ~ `)) {
	                             return R_D__0;
                             }`;
}

int chebyshev_init(T)(T* dos, int nos, T eta)
{
    int i, ii;
    T err;

    if (nos < 1)
	return 0;

    err = 0.0;
    i = 0;			/* just to avoid compiler warnings */
    for (ii = 1; ii <= nos; ii++) {
	i = nos - ii;
	err += fabs(dos[i]);
	if (err > eta) {
	    return i;
	}
    }
    return i;
}

T chebyshev_eval(T)(T x, const(T)* a, const(int) n)
{
    T b0, b1, b2, twox;
    int i;

    if (n < 1 || n > 1000)
    	return T.nan;

    if (x < -1.1 || x > 1.1)
    	return T.nan;

    twox = x * 2;
    b2 = b1 = 0;
    b0 = 0;
    for (i = 1; i <= n; i++) {
	    b2 = b1;
	    b1 = b0;
	    b0 = twox * b1 - b2 + a[n - i];
    }
    return (b0 - b2) * 0.5;
}

T d1mach(T)(int i)
{
    switch(i) {
    case 1: return MIN!T;
    case 2: return MAX!T;

    case 3: /* = FLT_RADIX  ^ - DBL_MANT_DIG
	      for IEEE:  = 2^-53 = 1.110223e-16 = .5*DBL_EPSILON */
	return 0.5*EPSILON!T;

    case 4: /* = FLT_RADIX  ^ (1- DBL_MANT_DIG) =
	      for IEEE:  = 2^-52 = DBL_EPSILON */
	return EPSILON!T;

    case 5: return M_LOG10_2;

    default: return 0.0;
    }
}

int i1mach(int i)
{
    switch(i) {

    case  1: return 5;
    case  2: return 6;
    case  3: return 0;
    case  4: return 0;

    case  5: return CHAR_BIT*int.sizeof;
    case  6: return int.sizeof/char.sizeof;

    case  7: return 2;
    case  8: return CHAR_BIT*int.sizeof - 1;
    case  9: return INT_MAX;

    case 10: return FLT_RADIX;

    case 11: return FLT_MANT_DIG;
    case 12: return FLT_MIN_EXP;
    case 13: return FLT_MAX_EXP;

    case 14: return DBL_MANT_DIG;
    case 15: return DBL_MIN_EXP;
    case 16: return DBL_MAX_EXP;

    default: return 0;
    }
}


void gammalims(T)(T* xmin, T* xmax)
{
/* FIXME: Even better: If IEEE, #define these in nmath.h
	  and don't call gammalims() at all
*/

    *xmin = -170.5674972726612;
    *xmax =  171.61447887182298;/*(3 Intel/Sparc architectures)*/

    double alnbig, alnsml, xln, xold;
    int i;

    alnsml = log(d1mach!T(1));
    *xmin = -alnsml;
    for (i = 1; i <= 10; ++i) {
	    xold = *xmin;
	    xln = log(*xmin);
	    *xmin -= *xmin * ((*xmin + .5) * xln - *xmin - .2258 + alnsml) /
	    	(*xmin * xln + .5);
	    if (fabs(*xmin - xold) < .005) {
	        *xmin = -(*xmin) + .01;
	        goto find_xmax;
	    }
    }

    /* unable to find xmin */

    //ML_ERROR(ME_NOCONV, "gammalims");
    *xmin = *xmax = T.nan;

find_xmax:

    alnbig = log(d1mach!T(2));
    *xmax = alnbig;
    for (i = 1; i <= 10; ++i) {
	    xold = *xmax;
	    xln = log(*xmax);
	    *xmax -= *xmax * ((*xmax - .5) * xln - *xmax + .9189 - alnbig) /
	    	(*xmax * xln - .5);
	    if (fabs(*xmax - xold) < .005) {
	        *xmax += -.01;
	        goto done;
	    }
    }

    /* unable to find xmax */

    //ML_ERROR(ME_NOCONV, "gammalims");
    *xmin = *xmax = T.nan;

done:
    *xmin = fmax2(*xmin, -(*xmax) + 1);
}

T lgammacor(T)(T x)
{
    const static T[15] algmcs = [
	+.1666389480451863247205729650822e+0,
	-.1384948176067563840732986059135e-4,
	+.9810825646924729426157171547487e-8,
	-.1809129475572494194263306266719e-10,
	+.6221098041892605227126015543416e-13,
	-.3399615005417721944303330599666e-15,
	+.2683181998482698748957538846666e-17,
	-.2868042435334643284144622399999e-19,
	+.3962837061046434803679306666666e-21,
	-.6831888753985766870111999999999e-23,
	+.1429227355942498147573333333333e-24,
	-.3547598158101070547199999999999e-26,
	+.1025680058010470912000000000000e-27,
	-.3401102254316748799999999999999e-29,
	+.1276642195630062933333333333333e-30
    ];

    T tmp;

/* For IEEE double precision DBL_EPSILON = 2^-52 = 2.220446049250313e-16 :
 *   xbig = 2 ^ 26.5
 *   xmax = DBL_MAX / 48 =  2^1020 / 3 */
    const(int) nalgm = 5;
    const(T) xbig  = 94906265.62425156;
    const(T) xmax  = 3.745194030963158e306;

    if (x < 10)
	    return T.nan;
    else if (x >= xmax) {
	    //ML_ERROR(ME_UNDERFLOW, "lgammacor");
	    /* allow to underflow below */
    }
    else if (x < xbig) {
	tmp = 10 / x;
	return chebyshev_eval!T(tmp * tmp * 2 - 1, algmcs.ptr, nalgm) / x;
    }
    return 1 / (x * 12);
}

/* Start of trig pi functions */

// cos(pi * x)  -- exact when x = k/2  for all integer k
T cospi(T)(T x) {
    if (isNaN(x))
    	return x;
    if(!isFinite(x))
    	return T.nan;

    x = fmod(fabs(x), 2.);// cos() symmetric; cos(pi(x + 2k)) == cos(pi x) for all integer k
    if(fmod(x, 1.) == 0.5)
    	return 0.;
    if(x == 1.)
    	return -1.;
    if(x == 0.)
    	return  1.;
    // otherwise
    return cos(M_PI * x);
}

// sin(pi * x)  -- exact when x = k/2  for all integer k
T sinpi(T)(T x) {
    if (isNaN(x)) return x;
    if(!isFinite(x))
    	return T.nan;

    x = fmod(x, 2.); // sin(pi(x + 2k)) == sin(pi x)  for all integer k
    // map (-2,2) --> (-1,1] :
    if(x <= -1)
    	x += 2.;
    else if (x > 1.)
    	x -= 2.;
    if(x == 0. || x == 1.)
    	return 0.;
    if(x ==  0.5)
    	return  1.;
    if(x == -0.5)
    	return -1.;
    // otherwise
    return sin(M_PI * x);
}


T tanpi(T)(T x)
{
    if (isNaN(x))
    	return x;
    if(!isFinite(x))
    	return T.nan;

    x = fmod(x, 1.); // tan(pi(x + k)) == tan(pi x)  for all integer k
    // map (-1,1) --> (-1/2, 1/2] :
    if(x <= -0.5)
    	x++;
    else if(x > 0.5)
    	x--;
    return (x == 0.) ? 0. : ((x == 0.5) ? T.nan : tan(M_PI * x));
}
/* End of trig pi functions */

T lgammafn_sign(T)(T x, int *sgn)
{
    T ans, y, sinpiy;

    //#ifdef NOMORE_FOR_THREADS
    //    static double xmax = 0.;
    //    static double dxrel = 0.;
    //
    //    if (xmax == 0) {/* initialize machine dependent constants _ONCE_ */
    //	xmax = d1mach(2)/log(d1mach(2));/* = 2.533 e305	 for IEEE double */
    //	dxrel = sqrt (d1mach(4));/* sqrt(Eps) ~ 1.49 e-8  for IEEE double */
    //    }
    //#else
    /* For IEEE double precision DBL_EPSILON = 2^-52 = 2.220446049250313e-16 :
       xmax  = DBL_MAX / log(DBL_MAX) = 2^1024 / (1024 * log(2)) = 2^1014 / log(2)
       dxrel = sqrt(DBL_EPSILON) = 2^-26 = 5^26 * 1e-26 (is *exact* below !)
     */
    enum xmax  = 2.5327372760800758e+305;
    enum dxrel = 1.490116119384765625e-8;

    if (sgn != null) *sgn = 1;

    if(isNaN(x))
    	return x;


    if (sgn != null && x < 0 && fmod(floor(-x), 2.) == 0)
	    *sgn = -1;

    if (x <= 0 && x == trunc(x)) { /* Negative integer argument */
	    //ML_ERROR(ME_RANGE, "lgamma");
	    return T.infinity;/* +Inf, since lgamma(x) = log|gamma(x)| */
    }

    y = fabs(x);

    if (y < 1e-306)
        return -log(y); // denormalized range, R change
    if (y <= 10)
    	return log(fabs(gammafn(x)));
    /*
      ELSE  y = |x| > 10 ---------------------- */

    if (y > xmax) {
	    //ML_ERROR(ME_RANGE, "lgamma");
	    return T.infinity;
    }

    if (x > 0) { /* i.e. y = x > 10 */
	    if(x > 1e17)
	        return(x*(log(x) - 1.));
	    else if(x > 4934720.)
	        return(M_LN_SQRT_2PI + (x - 0.5) * log(x) - x);
	    else
	        return M_LN_SQRT_2PI + (x - 0.5) * log(x) - x + lgammacor!T(x);
    }
    /* else: x < -10; y = -x */
    sinpiy = fabs(sinpi!T(y));

    if (sinpiy == 0) { /* Negative integer argument ===
			  Now UNNECESSARY: caught above */
	    //MATHLIB_WARNING(" ** should NEVER happen! *** [lgamma.c: Neg.int, y=%g]\n",y);
	    return T.nan;
    }

    ans = M_LN_SQRT_PId2 + (x - 0.5) * log(y) - x - log(sinpiy) - lgammacor!T(y);

    if(fabs((x - trunc(x - 0.5)) * ans / x) < dxrel) {

	    /* The answer is less than half precision because
	     * the argument is too near a negative integer. */

	    //ML_ERROR(ME_PRECISION, "lgamma");
    }

    return ans;
}

T lgammafn(T)(T x)
{
    return lgammafn_sign!T(x, null);
}


T stirlerr(T)(T n)
{

    enum S0 = 0.083333333333333333333;        /* 1/12 */
    enum S1 = 0.00277777777777777777778;      /* 1/360 */
    enum S2 = 0.00079365079365079365079365;   /* 1/1260 */
    enum S3 = 0.000595238095238095238095238;  /* 1/1680 */
    enum S4 = 0.0008417508417508417508417508; /* 1/1188 */

/*
  error for 0, 0.5, 1.0, 1.5, ..., 14.5, 15.0.
*/
    const static T[31] sferr_halves = [
	0.0, /* n=0 - wrong, place holder only */
	0.1534264097200273452913848,  /* 0.5 */
	0.0810614667953272582196702,  /* 1.0 */
	0.0548141210519176538961390,  /* 1.5 */
	0.0413406959554092940938221,  /* 2.0 */
	0.03316287351993628748511048, /* 2.5 */
	0.02767792568499833914878929, /* 3.0 */
	0.02374616365629749597132920, /* 3.5 */
	0.02079067210376509311152277, /* 4.0 */
	0.01848845053267318523077934, /* 4.5 */
	0.01664469118982119216319487, /* 5.0 */
	0.01513497322191737887351255, /* 5.5 */
	0.01387612882307074799874573, /* 6.0 */
	0.01281046524292022692424986, /* 6.5 */
	0.01189670994589177009505572, /* 7.0 */
	0.01110455975820691732662991, /* 7.5 */
	0.010411265261972096497478567, /* 8.0 */
	0.009799416126158803298389475, /* 8.5 */
	0.009255462182712732917728637, /* 9.0 */
	0.008768700134139385462952823, /* 9.5 */
	0.008330563433362871256469318, /* 10.0 */
	0.007934114564314020547248100, /* 10.5 */
	0.007573675487951840794972024, /* 11.0 */
	0.007244554301320383179543912, /* 11.5 */
	0.006942840107209529865664152, /* 12.0 */
	0.006665247032707682442354394, /* 12.5 */
	0.006408994188004207068439631, /* 13.0 */
	0.006171712263039457647532867, /* 13.5 */
	0.005951370112758847735624416, /* 14.0 */
	0.005746216513010115682023589, /* 14.5 */
	0.005554733551962801371038690  /* 15.0 */
    ];
    T nn;

    if (n <= 15.0) {
	    nn = n + n;
	    if (nn == cast(int)nn) return(sferr_halves[cast(int)nn]);
	        return(lgammafn!T(n + 1.) - (n + 0.5)*log(n) + n - M_LN_SQRT_2PI);
    }

    nn = n*n;
    if (n > 500)
    	return((S0 - S1/nn)/n);
    if (n >  80)
    	return((S0 - (S1 - S2/nn)/nn)/n);
    if (n >  35)
    	return((S0 - (S1 - (S2 - S3/nn)/nn)/nn)/n);
    /* 15 < n <= 35 : */
    return ((S0 - (S1 - (S2 - (S3 - S4/nn)/nn)/nn)/nn)/n);
}



T gammafn(T)(T x)
{
    const static T[42] gamcs = [
	+.8571195590989331421920062399942e-2,
	+.4415381324841006757191315771652e-2,
	+.5685043681599363378632664588789e-1,
	-.4219835396418560501012500186624e-2,
	+.1326808181212460220584006796352e-2,
	-.1893024529798880432523947023886e-3,
	+.3606925327441245256578082217225e-4,
	-.6056761904460864218485548290365e-5,
	+.1055829546302283344731823509093e-5,
	-.1811967365542384048291855891166e-6,
	+.3117724964715322277790254593169e-7,
	-.5354219639019687140874081024347e-8,
	+.9193275519859588946887786825940e-9,
	-.1577941280288339761767423273953e-9,
	+.2707980622934954543266540433089e-10,
	-.4646818653825730144081661058933e-11,
	+.7973350192007419656460767175359e-12,
	-.1368078209830916025799499172309e-12,
	+.2347319486563800657233471771688e-13,
	-.4027432614949066932766570534699e-14,
	+.6910051747372100912138336975257e-15,
	-.1185584500221992907052387126192e-15,
	+.2034148542496373955201026051932e-16,
	-.3490054341717405849274012949108e-17,
	+.5987993856485305567135051066026e-18,
	-.1027378057872228074490069778431e-18,
	+.1762702816060529824942759660748e-19,
	-.3024320653735306260958772112042e-20,
	+.5188914660218397839717833550506e-21,
	-.8902770842456576692449251601066e-22,
	+.1527474068493342602274596891306e-22,
	-.2620731256187362900257328332799e-23,
	+.4496464047830538670331046570666e-24,
	-.7714712731336877911703901525333e-25,
	+.1323635453126044036486572714666e-25,
	-.2270999412942928816702313813333e-26,
	+.3896418998003991449320816639999e-27,
	-.6685198115125953327792127999999e-28,
	+.1146998663140024384347613866666e-28,
	-.1967938586345134677295103999999e-29,
	+.3376448816585338090334890666666e-30,
	-.5793070335782135784625493333333e-31
    ];

    int i, n;
    T y;
    T sinpiy, value;

    //static int ngam = 0;
    //static T xmin = 0, xmax = 0., xsml = 0., dxrel = 0.;

    /* Initialize machine dependent constants, the first time gamma() is called.
	FIXME for threads ! */
    //if (ngam == 0) {
	//    ngam = chebyshev_init!T(gamcs, 42, EPSILON!T/20);/*was .1*d1mach(3)*/
	//    gammalims!T(&xmin, &xmax);/*-> ./gammalims.c */
	//    xsml = exp(fmax2(log(MIN!T), -log(MAX!T)) + 0.01);
	//    /*   = exp(.01)*DBL_MIN = 2.247e-308 for IEEE */
	//    dxrel = sqrt(EPSILON!T);/*was sqrt(d1mach(4)) */
    //}

    /* For IEEE double precision DBL_EPSILON = 2^-52 = 2.220446049250313e-16 :
     * (xmin, xmax) are non-trivial, see ./gammalims.c
     * xsml = exp(.01)*DBL_MIN
     * dxrel = sqrt(DBL_EPSILON) = 2 ^ -26
    */
    const(int) ngam = 22;
    const(T) xmin = -170.5674972726612;
    const(T) xmax = 171.61447887182298;
    const(T) xsml = 2.2474362225598545e-308;
    const(T) dxrel = 1.490116119384765696e-8;

    if(isNaN(x))
    	return x;

    /* If the argument is exactly zero or a negative integer
     * then return NaN. */
    if (x == 0 || (x < 0 && x == round(x))) {
    	//ML_ERROR(ME_DOMAIN, "gammafn");
	    return T.nan;
    }

    y = fabs(x);

    if (y <= 10) {

	/* Compute gamma(x) for -10 <= x <= 10
	 * Reduce the interval and find gamma(1 + y) for 0 <= y < 1
	 * first of all. */

	n = cast(int) x;
	if(x < 0)
		--n;
	y = x - n;/* n = floor(x)  ==>	y in [ 0, 1 ) */
	--n;
	value = chebyshev_eval!T(y * 2 - 1, gamcs.ptr, ngam) + .9375;
	if (n == 0)
	    return value;/* x = 1.dddd = 1+y */

	if (n < 0) {
	    /* compute gamma(x) for -10 <= x < 1 */

	    /* exact 0 or "-n" checked already above */

	    /* The answer is less than half precision */
	    /* because x too near a negative integer. */
	    if (x < -0.5 && fabs(x - cast(int)(x - 0.5) / x) < dxrel) {
		    //ML_ERROR(ME_PRECISION, "gammafn");
	    }

	    /* The argument is so close to 0 that the result would overflow. */
	    if (y < xsml) {
		    //ML_ERROR(ME_RANGE, "gammafn");
		    if(x > 0)
		    	return T.infinity;
		    else
		    	return -T.infinity;
	    }

	    n = -n;

	    for (i = 0; i < n; i++) {
		    value /= (x + i);
	    }
	    return value;
	} else {
	    /* gamma(x) for 2 <= x <= 10 */

	    for (i = 1; i <= n; i++) {
		    value *= (y + i);
	    }
	    return value;
	}
    }
    else {
	/* gamma(x) for	 y = |x| > 10. */

	if (x > xmax) {			/* Overflow */
	    //ML_ERROR(ME_RANGE, "gammafn");
	    return T.infinity;
	}

	if (x < xmin) {			/* Underflow */
	    //ML_ERROR(ME_UNDERFLOW, "gammafn");
	    return 0.;
	}

	if(y <= 50 && y == cast(int)y) { /* compute (n - 1)! */
	    value = 1.;
	    for (i = 2; i < y; i++)
	    	value *= i;
	}
	else { /* normal case */
	    value = exp((y - 0.5) * log(y) - y + M_LN_SQRT_2PI +
			((2*y == cast(int)2*y)? stirlerr!T(y) : lgammacor!T(y)));
	}
	if (x > 0)
	    return value;

	if (fabs((x - cast(int)(x - 0.5))/x) < dxrel){

	    /* The answer is less than half precision because */
	    /* the argument is too near a negative integer. */

	    //ML_ERROR(ME_PRECISION, "gammafn");
	}

	sinpiy = sinpi!T(y);
	if (sinpiy == 0) {		/* Negative integer arg - overflow */
	    //ML_ERROR(ME_RANGE, "gammafn");
	    return T.infinity;
	}

	return -M_PI / (y * sinpiy * value);
    }
}


T bd0(T)(T x, T np)
{
    T ej, s, s1, v;
    int j;

    if(!isFinite(x) || !isFinite(np) || np == 0.0)
    	return T.nan;

    if (fabs(x - np) < 0.1*(x + np)) {
	    v = (x - np)/(x + np);  // might underflow to 0
	    s = (x - np)*v;/* s using v -- change by MM */
	    if(fabs(s) < MIN!T)
	    	return s;
	    ej = 2*x*v;
	    v = v*v;
	    for (j = 1; j < 1000; j++) { /* Taylor series; 1000: no infinite loop
	    				as |v| < .1,  v^2000 is "zero" */
	        ej *= v;// = v^(2j+1)
	        s1 = s + ej/((j << 1) + 1);
	        if (s1 == s) /* last term was effectively 0 */
	    	    return s1 ;
	        s = s1;
	    }
    }
    /* else:  | x - np |  is not too small */
    return(x*log(x/np) + np - x);
}


// called from dpois, dgamma, pgamma, dnbeta, dnbinom, dnchisq :
T dpois_raw(T)(T x, T lambda, int give_log)
{
	mixin R_D__1!give_log;
	mixin R_D__0!give_log;
    if (lambda == 0)
    	return( (x == 0) ? R_D__1 : R_D__0 );
    if (!isFinite(lambda))
        return R_D__0; // including for the case where  x = lambda = +Inf
    if (x < 0)
    	return R_D__0;
    if (x <= lambda * MIN!T)
    	return R_D_exp!T(-lambda, give_log);
    if (lambda < x * MIN!T) {
	    if (!isFinite(x)) // lambda < x = +Inf
	        return R_D__0;
	    return(R_D_exp!T(-lambda + x*log(lambda) - lgammafn!T(x + 1), give_log));
    }
    return(R_D_fexp!T( M_2PI*x, -stirlerr!T(x) - bd0(x, lambda), give_log));
}


/* unif_rand */
static uint I1 = 1234, I2 = 5678;

void set_seed(uint i1, uint i2)
{
	I1 = i1; I2 = i2;
}

void get_seed(uint* i1, uint* i2)
{
	*i1 = I1; *i2 = I2;
}

T unif_rand(T)()
{
    import std.conv : octal;
	I1 = 36969*(I1 & octal!177777) + (I1>>16);
    I2 = 18000*(I2 & octal!177777) + (I2>>16);
    return ((I1 << 16)^(I2 & octal!177777)) * 2.328306437080797e-10;
}


T exp_rand(T)()
{
    /* q[k-1] = sum(log(2)^k / k!)  k=1,..,n, */
    /* The highest n (here 16) is determined by q[n-1] = 1.0 */
    /* within standard precision */
    const static T[] q =
    [
	0.6931471805599453,
	0.9333736875190459,
	0.9888777961838675,
	0.9984959252914960,
	0.9998292811061389,
	0.9999833164100727,
	0.9999985691438767,
	0.9999998906925558,
	0.9999999924734159,
	0.9999999995283275,
	0.9999999999728814,
	0.9999999999985598,
	0.9999999999999289,
	0.9999999999999968,
	0.9999999999999999,
	1.0000000000000000
    ];

    T a = 0.;
    T u = unif_rand!T();    /* precaution if u = 0 is ever returned */
    while(u <= 0. || u >= 1.)
    	u = unif_rand!T();
    for (;;) {
	    u += u;
	    if (u > 1.)
	        break;
	    a += q[0];
    }
    u -= 1.;

    if (u <= q[0])
	    return a + u;

    int i = 0;
    T ustar = unif_rand!T(), umin = ustar;
    do {
	    ustar = unif_rand!T();
	    if (umin > ustar)
	        umin = ustar;
	    i++;
    } while (u > q[i]);
    return a + umin * q[0];
}


auto dbinom_raw(T)(T x, T n, T p, T q, int give_log)
{
    T lf, lc;

    mixin R_D__0!give_log;
    mixin R_D__1!give_log;

    if (p == 0)
        return((x == 0) ? R_D__1 : R_D__0);
    if (q == 0)
        return((x == n) ? R_D__1 : R_D__0);

    if (x == 0) {
        if(n == 0)
            return R_D__1;
        lc = (p < 0.1) ? -bd0(n,n*q) - n*p : n*log(q);
        return( R_D_exp!T(lc, give_log) );
    }
    if (x == n) {
    lc = (q < 0.1) ? -bd0(n,n*p) - n*q : n*log(p);
    return( R_D_exp!T(lc, give_log) );
    }
    if (x < 0 || x > n) return( R_D__0 );

    /* n*p or n*q can underflow to zero if n and p or q are small.  This
       used to occur in dbeta, and gives NaN as from R 2.3.0.  */
    lc = stirlerr!T(n) - stirlerr!T(x) - stirlerr!T(n - x) - bd0!T(x,n*p) - bd0!T(n - x, n*q);

    /* f = (M_2PI*x*(n-x))/n; could overflow or underflow */
    /* Upto R 2.7.1:
     * lf = log(M_2PI) + log(x) + log(n-x) - log(n);
     * -- following is much better for  x << n : */
    lf = M_LN_2PI + log(x) + log1p(- x/n);

    return R_D_exp!T(lc - 0.5*lf, give_log);
}

