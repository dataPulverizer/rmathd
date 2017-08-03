module toms708;

import common;
import gamma;

static auto gamln1(T)(T a)
{
/* ----------------------------------------------------------------------- */
/*     EVALUATION OF LN(GAMMA(1 + A)) FOR -0.2 <= A <= 1.25 */
/* ----------------------------------------------------------------------- */

    T w;
    if (a < 0.6) {
    static T p0 = .577215664901533;
    static T p1 = .844203922187225;
    static T p2 = -.168860593646662;
    static T p3 = -.780427615533591;
    static T p4 = -.402055799310489;
    static T p5 = -.0673562214325671;
    static T p6 = -.00271935708322958;
    static T q1 = 2.88743195473681;
    static T q2 = 3.12755088914843;
    static T q3 = 1.56875193295039;
    static T q4 = .361951990101499;
    static T q5 = .0325038868253937;
    static T q6 = 6.67465618796164e-4;
    w = ((((((p6 * a + p5)* a + p4)* a + p3)* a + p2)* a + p1)* a + p0) /
        ((((((q6 * a + q5)* a + q4)* a + q3)* a + q2)* a + q1)* a + 1.);
    return -(a) * w;
    }
    else { /* 0.6 <= a <= 1.25 */
    static T r0 = .422784335098467;
    static T r1 = .848044614534529;
    static T r2 = .565221050691933;
    static T r3 = .156513060486551;
    static T r4 = .017050248402265;
    static T r5 = 4.97958207639485e-4;
    static T s1 = 1.24313399877507;
    static T s2 = .548042109832463;
    static T s3 = .10155218743983;
    static T s4 = .00713309612391;
    static T s5 = 1.16165475989616e-4;
    T x = a - 0.5 - 0.5;
    w = (((((r5 * x + r4) * x + r3) * x + r2) * x + r1) * x + r0) /
        (((((s5 * x + s4) * x + s3) * x + s2) * x + s1) * x + 1.);
    return x * w;
    }
} /* gamln1 */


static auto gamln(T)(T a)
{
/* -----------------------------------------------------------------------
 *            Evaluation of  ln(gamma(a))  for positive a
 * ----------------------------------------------------------------------- */
/*     Written by Alfred H. Morris */
/*          Naval Surface Warfare Center */
/*          Dahlgren, Virginia */
/* ----------------------------------------------------------------------- */

    static T d = .418938533204673;/* d == 0.5*(LN(2*PI) - 1) */

    static T c0 = .0833333333333333;
    static T c1 = -.00277777777760991;
    static T c2 = 7.9365066682539e-4;
    static T c3 = -5.9520293135187e-4;
    static T c4 = 8.37308034031215e-4;
    static T c5 = -.00165322962780713;

    if (a <= 0.8)
    return gamln1!T(a) - log(a); /* ln(G(a+1)) - ln(a) == ln(G(a+1)/a) = ln(G(a)) */
    else if (a <= 2.25)
    return gamln1!T(a - 0.5 - 0.5);

    else if (a < 10.) {
    int i, n = cast(int)(a - 1.25);
    T t = a;
    T w = 1.;
    for (i = 1; i <= n; ++i) {
        t += -1.;
        w *= t;
    }
    return gamln1!T(t - 1.) + log(w);
    }
    else { /* a >= 10 */
    T t = 1. / (a * a);
    T w = (((((c5 * t + c4) * t + c3) * t + c2) * t + c1) * t + c0) / a;
    return d + w + (a - 0.5) * (log(a) - 1.);
    }
} /* gamln */


static auto bcorr(T)(T a0, T b0)
{
/* ----------------------------------------------------------------------- */

/*     EVALUATION OF  DEL(A0) + DEL(B0) - DEL(A0 + B0)  WHERE */
/*     LN(GAMMA(A)) = (A - 0.5)*LN(A) - A + 0.5*LN(2*PI) + DEL(A). */
/*     IT IS ASSUMED THAT A0 >= 8 AND B0 >= 8. */

/* ----------------------------------------------------------------------- */
    /* Initialized data */

    static T c0 = .0833333333333333;
    static T c1 = -.00277777777760991;
    static T c2 = 7.9365066682539e-4;
    static T c3 = -5.9520293135187e-4;
    static T c4 = 8.37308034031215e-4;
    static T c5 = -.00165322962780713;

    /* System generated locals */
    T ret_val, r1;

    /* Local variables */
    T a, b, c, h, t, w, x, s3, s5, x2, s7, s9, s11;
/* ------------------------ */
    a = min!(T)(a0, b0);
    b = max!(T)(a0, b0);

    h = a / b;
    c = h / (h + 1.);
    x = 1. / (h + 1.);
    x2 = x * x;

/*                SET SN = (1 - X^N)/(1 - X) */

    s3 = x + x2 + 1.;
    s5 = x + x2 * s3 + 1.;
    s7 = x + x2 * s5 + 1.;
    s9 = x + x2 * s7 + 1.;
    s11 = x + x2 * s9 + 1.;

/*                SET W = DEL(B) - DEL(A + B) */

/* Computing 2nd power */
    r1 = 1. / b;
    t = r1 * r1;
    w = ((((c5 * s11 * t + c4 * s9) * t + c3 * s7) * t + c2 * s5) * t + c1 *
        s3) * t + c0;
    w *= c / b;

/*                   COMPUTE  DEL(A) + W */

/* Computing 2nd power */
    r1 = 1. / a;
    t = r1 * r1;
    ret_val = (((((c5 * t + c4) * t + c3) * t + c2) * t + c1) * t + c0) / a +
        w;
    return ret_val;
} /* bcorr */


static auto psi(T)(T x)
{
/* ---------------------------------------------------------------------

 *                 Evaluation of the Digamma function psi(x)

 *                           -----------

 *     Psi(xx) is assigned the value 0 when the digamma function cannot
 *     be computed.

 *     The main computation involves evaluation of rational Chebyshev
 *     approximations published in Math. Comp. 27, 123-127(1973) by
 *     Cody, Strecok and Thacher. */

/* --------------------------------------------------------------------- */
/*     Psi was written at Argonne National Laboratory for the FUNPACK */
/*     package of special function subroutines. Psi was modified by */
/*     A.H. Morris (NSWC). */
/* --------------------------------------------------------------------- */

    static T piov4 = .785398163397448; /* == pi / 4 */
/*     dx0 = zero of psi() to extended precision : */
    static T dx0 = 1.461632144968362341262659542325721325;

/* --------------------------------------------------------------------- */
/*     COEFFICIENTS FOR RATIONAL APPROXIMATION OF */
/*     PSI(X) / (X - X0),  0.5 <= X <= 3. */
    static T[7] p1 = [.0089538502298197,4.77762828042627,
            142.441585084029,1186.45200713425,3633.51846806499,
            4138.10161269013,1305.60269827897];
    static T[6] q1 = [44.8452573429826,520.752771467162,
            2210.0079924783,3641.27349079381,1908.310765963,
            6.91091682714533e-6];
/* --------------------------------------------------------------------- */


/* --------------------------------------------------------------------- */
/*     COEFFICIENTS FOR RATIONAL APPROXIMATION OF */
/*     PSI(X) - LN(X) + 1 / (2*X),  X > 3. */

    static T[4] p2 = [-2.12940445131011,-7.01677227766759,
            -4.48616543918019,-.648157123766197];
    static T[4] q2 = [32.2703493791143,89.2920700481861,
            54.6117738103215,7.77788548522962];
/* --------------------------------------------------------------------- */

    int i, m, n, nq;
    T d2;
    T w, z;
    T den, aug, sgn, xmx0, xmax1, upper, xsmall;

/* --------------------------------------------------------------------- */


/*     MACHINE DEPENDENT CONSTANTS ... */

/* --------------------------------------------------------------------- */
/*    XMAX1  = THE SMALLEST POSITIVE FLOATING POINT CONSTANT
           WITH ENTIRELY INT REPRESENTATION.  ALSO USED
           AS NEGATIVE OF LOWER BOUND ON ACCEPTABLE NEGATIVE
           ARGUMENTS AND AS THE POSITIVE ARGUMENT BEYOND WHICH
           PSI MAY BE REPRESENTED AS LOG(X).
 * Originally:  xmax1 = amin1(ipmpar(3), 1./spmpar(1))  */
    xmax1 = cast(T) INT_MAX;
    d2 = 0.5/d1mach!T(3); /*= 0.5 / (0.5 * DBL_EPS) = 1/DBL_EPSILON = 2^52 */
    if(xmax1 > d2) xmax1 = d2;

/* --------------------------------------------------------------------- */
/*        XSMALL = ABSOLUTE ARGUMENT BELOW WHICH PI*COTAN(PI*X) */
/*                 MAY BE REPRESENTED BY 1/X. */
    xsmall = 1e-9;
/* --------------------------------------------------------------------- */
    aug = 0.;
    if (x < 0.5) {
/* --------------------------------------------------------------------- */
/*     X < 0.5,  USE REFLECTION FORMULA */
/*     PSI(1-X) = PSI(X) + PI * COTAN(PI*X) */
/* --------------------------------------------------------------------- */
    if (fabs(x) <= xsmall) {

        if (x == 0.) {
        goto L_err;
        }
/* --------------------------------------------------------------------- */
/*     0 < |X| <= XSMALL.  USE 1/X AS A SUBSTITUTE */
/*     FOR  PI*COTAN(PI*X) */
/* --------------------------------------------------------------------- */
        aug = -1. / x;
    } else { /* |x| > xsmall */
/* --------------------------------------------------------------------- */
/*     REDUCTION OF ARGUMENT FOR COTAN */
/* --------------------------------------------------------------------- */
        /* L100: */
        w = -x;
        sgn = piov4;
        if (w <= 0.) {
        w = -w;
        sgn = -sgn;
        }
/* --------------------------------------------------------------------- */
/*     MAKE AN ERROR EXIT IF |X| >= XMAX1 */
/* --------------------------------------------------------------------- */
        if (w >= xmax1) {
        goto L_err;
        }
        nq = cast(int) w;
        w -= cast(T) nq;
        nq = cast(int) (w * 4.);
        w = (w - cast(T) nq * 0.25) * 4.;
/* --------------------------------------------------------------------- */
/*     W IS NOW RELATED TO THE FRACTIONAL PART OF  4. * X. */
/*     ADJUST ARGUMENT TO CORRESPOND TO VALUES IN FIRST */
/*     QUADRANT AND DETERMINE SIGN */
/* --------------------------------------------------------------------- */
        n = nq / 2;
        if (n + n != nq) {
        w = 1. - w;
        }
        z = piov4 * w;
        m = n / 2;
        if (m + m != n) {
        sgn = -sgn;
        }
/* --------------------------------------------------------------------- */
/*     DETERMINE FINAL VALUE FOR  -PI*COTAN(PI*X) */
/* --------------------------------------------------------------------- */
        n = (nq + 1) / 2;
        m = n / 2;
        m += m;
        if (m == n) {
/* --------------------------------------------------------------------- */
/*     CHECK FOR SINGULARITY */
/* --------------------------------------------------------------------- */
        if (z == 0.) {
            goto L_err;
        }
/* --------------------------------------------------------------------- */
/*     USE COS/SIN AS A SUBSTITUTE FOR COTAN, AND */
/*     SIN/COS AS A SUBSTITUTE FOR TAN */
/* --------------------------------------------------------------------- */
        aug = sgn*(cos(z) / sin(z) * 4.);

        } else { /* L140: */
        aug = sgn*(sin(z) / cos(z) * 4.);
        }
    }

    x = 1. - x;

    }
    /* L200: */
    if (x <= 3.) {
/* --------------------------------------------------------------------- */
/*     0.5 <= X <= 3. */
/* --------------------------------------------------------------------- */
    den = x;
    upper = p1[0] * x;

    for (i = 1; i <= 5; ++i) {
        den = (den + q1[i - 1]) * x;
        upper = (upper + p1[i]) * x;
    }

    den = (upper + p1[6]) / (den + q1[5]);
    xmx0 = x - dx0;
    return den * xmx0 + aug;
    }

/* --------------------------------------------------------------------- */
/*     IF X >= XMAX1, PSI = LN(X) */
/* --------------------------------------------------------------------- */
    if (x < xmax1) {
/* --------------------------------------------------------------------- */
/*     3. < X < XMAX1 */
/* --------------------------------------------------------------------- */
    w = 1. / (x * x);
    den = w;
    upper = p2[0] * w;

    for (i = 1; i <= 3; ++i) {
        den = (den + q2[i - 1]) * w;
        upper = (upper + p2[i]) * w;
    }

    aug = upper / (den + q2[3]) - 0.5 / x + aug;
    }
    return aug + log(x);

/* --------------------------------------------------------------------- */
/*     ERROR RETURN */
/* --------------------------------------------------------------------- */
L_err:
    return 0.;
} /* psi */


static auto gam1(T)(T a)
{
/*     ------------------------------------------------------------------ */
/*     COMPUTATION OF 1/GAMMA(A+1) - 1  FOR -0.5 <= A <= 1.5 */
/*     ------------------------------------------------------------------ */

    T d, t, w, bot, top;

    t = a;
    d = a - 0.5;
    // t := if(a > 1/2)  a-1  else  a
    if (d > 0.)
    t = d - 0.5;
    if (t < 0.) { /* L30: */
    static T[9] r = [-.422784335098468,-.771330383816272,
                     -.244757765222226,.118378989872749,9.30357293360349e-4,
                     -.0118290993445146,.00223047661158249,2.66505979058923e-4,
                     -1.32674909766242e-4];
    static T s1 = .273076135303957, s2 = .0559398236957378;

    top = (((((((r[8] * t + r[7]) * t + r[6]) * t + r[5]) * t + r[4]
             ) * t + r[3]) * t + r[2]) * t + r[1]) * t + r[0];
    bot = (s2 * t + s1) * t + 1.;
    w = top/bot;
    //R_ifDEBUG_printf("  gam1(a = %.15g): t < 0: w=%.15g\n", a, w);
    if (d > 0.)
        return t * w / a;
    else
        return a * (w + 0.5 + 0.5);

    } else if (t == 0) { // L10: a in {0, 1}
    return 0.;

    } else { /* t > 0;  L20: */
    static T[7] p = [.577215664901533,-.409078193005776,
                 -.230975380857675,.0597275330452234,.0076696818164949,
                 -.00514889771323592,5.89597428611429e-4];
    static T[5] q = [1.,.427569613095214,.158451672430138, .0261132021441447,.00423244297896961];

    top = (((((p[6] * t + p[5]) * t + p[4]) * t + p[3]) * t + p[2]
           ) * t + p[1]) * t + p[0];
    bot = (((q[4] * t + q[3]) * t + q[2]) * t + q[1]) * t + 1.;
    w = top/bot;
    //R_ifDEBUG_printf("  gam1(a = %.15g): t > 0: (is a < 1.5 ?)  w=%.15g\n", a, w);
    if (d > 0.) /* L21: */
        return t / a * (w - 0.5 - 0.5);
    else
        return a * w;
    }
} /* gam1 */


static auto exparg(T)(int l)
{
/* --------------------------------------------------------------------
 *     If l = 0 then  exparg(l) = The largest positive W for which
 *     exp(W) can be computed. With 0.99999 fuzz  ==> exparg(0) =   709.7756  nowadays

 *     if l = 1 (nonzero) then  exparg(l) = the largest negative W for
 *     which the computed value of exp(W) is nonzero.
 *     With 0.99999 fuzz              ==> exparg(1) =  -709.0825  nowadays

 *     Note... only an approximate value for exparg(L) is needed.
 * -------------------------------------------------------------------- */

    static const(T) lnb = .69314718055995;
    int m = (l == 0) ? i1mach(16) : i1mach(15) - 1;

    return m * lnb * .99999;
} /* exparg */


static auto esum(T)(int mu, T x, int give_log)
{
/* ----------------------------------------------------------------------- */
/*                    EVALUATION OF EXP(MU + X) */
/* ----------------------------------------------------------------------- */

    if(give_log)
        return x + cast(T) mu;

    // else :
    T w;
    if(x > 0.) { /* L10: */
    if(mu > 0)
        return exp(cast(T)mu)*exp(x);
    w = mu + x;
    if(w < 0.)
        return exp(cast(T)mu)*exp(x);
    }
    else { /* x <= 0 */
    if(mu < 0)
        return exp(cast(T)mu)*exp(x);
    w = mu + x;
    if(w > 0.)
        return exp(cast(T)mu)*exp(x);
    }
    return exp(w);

} /* esum */


auto rexpm1(T)(T x)
{
/* ----------------------------------------------------------------------- */
/*            EVALUATION OF THE FUNCTION EXP(X) - 1 */
/* ----------------------------------------------------------------------- */

    static T p1 = 9.14041914819518e-10;
    static T p2 = .0238082361044469;
    static T q1 = -.499999999085958;
    static T q2 = .107141568980644;
    static T q3 = -.0119041179760821;
    static T q4 = 5.95130811860248e-4;

    if (fabs(x) <= 0.15) {
        return x * (((p2 * x + p1) * x + 1.) /
                ((((q4 * x + q3) * x + q2) * x + q1) * x + 1.));
    }
    else { /* |x| > 0.15 : */
        T w = exp(x);
        if (x > 0.)
            return w * (0.5 - 1. / w + 0.5);
        else
            return w - 0.5 - 0.5;
    }

} /* rexpm1 */

static auto alnrel(T)(T a)
{
/* -----------------------------------------------------------------------
 *            Evaluation of the function ln(1 + a)
 * ----------------------------------------------------------------------- */

    if (fabs(a) > 0.375)
    return log(1. + a);
    // else : |a| <= 0.375
    static T p1 = -1.29418923021993,
        p2 = .405303492862024,
        p3 = -.0178874546012214,
        q1 = -1.62752256355323,
        q2 = .747811014037616,
        q3 = -.0845104217945565;
    T t = a / (a + 2.),
    t2 = t * t,
    w = (((p3 * t2 + p2) * t2 + p1) * t2 + 1.) /
    (((q3 * t2 + q2) * t2 + q1) * t2 + 1.);
    return t * 2. * w;

} /* alnrel */


static auto rlog1(T)(T x)
{
/* -----------------------------------------------------------------------
 *             Evaluation of the function  x - ln(1 + x)
 * ----------------------------------------------------------------------- */

    static T a = .0566749439387324;
    static T b = .0456512608815524;
    static T p0 = .333333333333333;
    static T p1 = -.224696413112536;
    static T p2 = .00620886815375787;
    static T q1 = -1.27408923933623;
    static T q2 = .354508718369557;

    T h, r, t, w, w1;
    if (x < -0.39 || x > 0.57) { /* direct evaluation */
        w = x + 0.5 + 0.5;
        return x - log(w);
    }
    /* else */
    if (x < -0.18) { /* L10: */
        h = x + .3;
        h /= .7;
        w1 = a - h * .3;
    } else if (x > 0.18) { /* L20: */
        h = x * .75 - .25;
        w1 = b + h / 3.;
    } else { /*     Argument Reduction */
        h = x;
        w1 = 0.;
    }

/* L30:                 Series Expansion */

    r = h/(h + 2.);
    t = r*r;
    w = ((p2 * t + p1) * t + p0) / ((q2 * t + q1) * t + 1.);
    return t * 2. * (1. / (1. - r) - r * w) + w1;

} /* rlog1 */


static auto erf__(T)(T x)
{
/* -----------------------------------------------------------------------
 *             EVALUATION OF THE REAL ERROR FUNCTION
 * ----------------------------------------------------------------------- */

    /* Initialized data */

    static T c = .564189583547756;
    static T[5] a = [7.7105849500132e-5,-.00133733772997339,
            .0323076579225834,.0479137145607681,.128379167095513];
    static T[3] b = [.00301048631703895,.0538971687740286,
            .375795757275549];
    static T[8] p = [-1.36864857382717e-7,.564195517478974,
            7.21175825088309,43.1622272220567,152.98928504694,
            339.320816734344,451.918953711873,300.459261020162];
    static T[8] q = [1.,12.7827273196294,77.0001529352295,
            277.585444743988,638.980264465631,931.35409485061,
            790.950925327898,300.459260956983];
    static T[5] r = [2.10144126479064,26.2370141675169,
            21.3688200555087,4.6580782871847,.282094791773523];
    static T[4] s = [94.153775055546,187.11481179959,
            99.0191814623914,18.0124575948747];

    /* Local variables */
    T t, x2, ax, bot, top;

    ax = fabs(x);
    if (ax <= 0.5) {
        t = x * x;
        top = (((a[0] * t + a[1]) * t + a[2]) * t + a[3]) * t + a[4] + 1.;
        bot = ((b[0] * t + b[1]) * t + b[2]) * t + 1.;
        
        return x * (top / bot);
    }

    // else:  |x| > 0.5

    if (ax <= 4.) { //  |x| in (0.5, 4]
        top = ((((((p[0] * ax + p[1]) * ax + p[2]) * ax + p[3]) * ax + p[4]) * ax
            + p[5]) * ax + p[6]) * ax + p[7];
        bot = ((((((q[0] * ax + q[1]) * ax + q[2]) * ax + q[3]) * ax + q[4]) * ax
            + q[5]) * ax + q[6]) * ax + q[7];
        T R = 0.5 - exp(-x * x) * top / bot + 0.5;
        return (x < 0) ? -R : R;
    }

    // else:  |x| > 4

    if (ax >= 5.8) {
        return x > 0 ? 1 : -1;
    }

    // else:  4 < |x| < 5.8
    x2 = x * x;
    t = 1. / x2;
    top = (((r[0] * t + r[1]) * t + r[2]) * t + r[3]) * t + r[4];
    bot = (((s[0] * t + s[1]) * t + s[2]) * t + s[3]) * t + 1.;
    t = (c - top / (x2 * bot)) / ax;
    T R = 0.5 - exp(-x2) * t + 0.5;
    return (x < 0) ? -R : R;
} /* erf */


static auto erfc1(T)(int ind, T x)
{
/* ----------------------------------------------------------------------- */
/*         EVALUATION OF THE COMPLEMENTARY ERROR FUNCTION */

/*          ERFC1(IND,X) = ERFC(X)            IF IND = 0 */
/*          ERFC1(IND,X) = EXP(X*X)*ERFC(X)   OTHERWISE */
/* ----------------------------------------------------------------------- */

    /* Initialized data */

    static T c = .564189583547756;
    static T[5] a = [7.7105849500132e-5,-.00133733772997339,
            .0323076579225834,.0479137145607681,.128379167095513];
    static T[3] b = [.00301048631703895,.0538971687740286, .375795757275549];
    static T[8] p = [-1.36864857382717e-7,.564195517478974,
            7.21175825088309,43.1622272220567,152.98928504694,
            339.320816734344,451.918953711873,300.459261020162];
    static T[8] q = [1.,12.7827273196294,77.0001529352295,
            277.585444743988,638.980264465631,931.35409485061,
            790.950925327898,300.459260956983];
    static T[5] r = [2.10144126479064,26.2370141675169,
            21.3688200555087,4.6580782871847,.282094791773523];
    static T[4] s = [94.153775055546,187.11481179959,
            99.0191814623914,18.0124575948747];

    T ret_val;
    T e, t, w, bot, top;

    T ax = fabs(x);
    //              |X| <= 0.5 */
    if (ax <= 0.5) {
        t = x * x,
            top = (((a[0] * t + a[1]) * t + a[2]) * t + a[3]) * t + a[4] + 1.,
            bot = ((b[0] * t + b[1]) * t + b[2]) * t + 1.;
        ret_val = 0.5 - x * (top / bot) + 0.5;
        if (ind != 0) {
            ret_val = exp(t) * ret_val;
        }
        return ret_val;
    }
    // else (L10:):     0.5 < |X| <= 4
    if (ax <= 4.) {
        top = ((((((p[0] * ax + p[1]) * ax + p[2]) * ax + p[3]) * ax + p[4]) * ax
            + p[5]) * ax + p[6]) * ax + p[7];
        bot = ((((((q[0] * ax + q[1]) * ax + q[2]) * ax + q[3]) * ax + q[4]) * ax
            + q[5]) * ax + q[6]) * ax + q[7];
        ret_val = top / bot;
    } else { //         |X| > 4
        // L20:
        if (x <= -5.6) {
            // L50:             LIMIT VALUE FOR "LARGE" NEGATIVE X
            ret_val = 2.;
            if (ind != 0) {
            ret_val = exp(x * x) * 2.;
            }
            return ret_val;
        }
        if (ind == 0 && (x > 100. || x * x > -exparg!T(1))) {
            // LIMIT VALUE FOR LARGE POSITIVE X   WHEN IND = 0
            // L60:
            return 0.;
        }
        
        // L30:
        t = 1. / (x * x);
        top = (((r[0] * t + r[1]) * t + r[2]) * t + r[3]) * t + r[4];
        bot = (((s[0] * t + s[1]) * t + s[2]) * t + s[3]) * t + 1.;
        ret_val = (c - t * top / bot) / ax;
    }

    // L40:                 FINAL ASSEMBLY
    if (ind != 0) {
        if (x < 0.)
            ret_val = exp(x * x) * 2. - ret_val;
    } else {
        // L41:  ind == 0 :
        w = x * x;
        t = w;
        e = w - t;
        ret_val = (0.5 - e + 0.5) * exp(-t) * ret_val;
        if (x < 0.)
            ret_val = 2. - ret_val;
    }
    return ret_val;

} /* erfc1 */


static auto basym(T)(T a, T b, T lambda, T eps, int log_p)
{
/* ----------------------------------------------------------------------- */
/*     ASYMPTOTIC EXPANSION FOR I_x(A,B) FOR LARGE A AND B. */
/*     LAMBDA = (A + B)*Y - B  AND EPS IS THE TOLERANCE USED. */
/*     IT IS ASSUMED THAT LAMBDA IS NONNEGATIVE AND THAT */
/*     A AND B ARE GREATER THAN OR EQUAL TO 15. */
/* ----------------------------------------------------------------------- */


/* ------------------------ */
/*     ****** NUM IS THE MAXIMUM VALUE THAT N CAN TAKE IN THE DO LOOP */
/*            ENDING AT STATEMENT 50. IT IS REQUIRED THAT NUM BE EVEN. */
    enum num_IT = 20;
/*            THE ARRAYS A0, B0, C, D HAVE DIMENSION NUM + 1. */

    static const(T) e0 = 1.12837916709551;/* e0 == 2/sqrt(pi) */
    static const(T) e1 = .353553390593274;/* e1 == 2^(-3/2)   */
    static const(T) ln_e0 = 0.120782237635245; /* == ln(e0) */

    T[num_IT + 1] a0, b0, c, d;

    T f = a * rlog1!T(-lambda/a) + b * rlog1!T(lambda/b), t;
    if(log_p)
        t = -f;
    else {
        t = exp(-f);
        if (t == 0.) {
            return 0; /* once underflow, always underflow .. */
        }
    }
    T z0 = sqrt(f),
    z = z0 / e1 * 0.5,
    z2 = f + f,
    h, r0, r1, w0;

    if (a < b) {
        h = a / b;
        r0 = 1. / (h + 1.);
        r1 = (b - a) / b;
        w0 = 1. / sqrt(a * (h + 1.));
    } else {
        h = b / a;
        r0 = 1. / (h + 1.);
        r1 = (b - a) / a;
        w0 = 1. / sqrt(b * (h + 1.));
    }

    a0[0] = r1 * .66666666666666663;
    c[0] = a0[0] * -0.5;
    d[0] = -c[0];
    T j0 = 0.5 / e0 * erfc1!T(1, z0),
    j1 = e1,
    sum = j0 + d[0] * w0 * j1;

    T s = 1.,
    h2 = h * h,
    hn = 1.,
    w = w0,
    znm1 = z,
    zn = z2;
    for (int n = 2; n <= num_IT; n += 2) {
        hn *= h2;
        a0[n - 1] = r0 * 2. * (h * hn + 1.) / (n + 2.);
        int np1 = n + 1;
        s += hn;
        a0[np1 - 1] = r1 * 2. * s / (n + 3.);
        
        for (int i = n; i <= np1; ++i) {
            T r = (i + 1.) * -0.5;
            b0[0] = r * a0[0];
            for (int m = 2; m <= i; ++m) {
            T bsum = 0.;
            for (int j = 1; j <= m-1; ++j) {
                int mmj = m - j;
                bsum += (j * r - mmj) * a0[j - 1] * b0[mmj - 1];
            }
            b0[m - 1] = r * a0[m - 1] + bsum / m;
            }
            c[i - 1] = b0[i - 1] / (i + 1.);
        
            T dsum = 0.;
            for (int j = 1; j <= i-1; ++j) {
            dsum += d[i - j - 1] * c[j - 1];
            }
            d[i - 1] = -(dsum + c[i - 1]);
        }
        
        j0 = e1 * znm1 + (n - 1.) * j0;
        j1 = e1 * zn + n * j1;
        znm1 = z2 * znm1;
        zn = z2 * zn;
        w *= w0;
        T t0 = d[n - 1] * w * j0;
        w *= w0;
        T t1 = d[np1 - 1] * w * j1;
        sum += t0 + t1;
        if (fabs(t0) + fabs(t1) <= eps * sum) {
            break;
        }
    }

    if(log_p)
    return ln_e0 + t - bcorr!T(a, b) + log(sum);
    else {
        T u = exp(-bcorr!T(a, b));
        return e0 * t * u * sum;
    }

} /* basym_ */


// called only from bgrat() , as   q_r = grat_r(b, z, log_r, eps)  :
static auto grat_r(T)(T a, T x, T log_r, T eps)
{
/* -----------------------------------------------------------------------
 *        Scaled complement of incomplete gamma ratio function
 *                   grat_r(a,x,r) :=  Q(a,x) / r
 * where
 *               Q(a,x) = pgamma(x,a, lower.tail=FALSE)
 *     and            r = e^(-x)* x^a / Gamma(a) ==  exp(log_r)
 *
 *     It is assumed that a <= 1.  eps is the tolerance to be used.
 * ----------------------------------------------------------------------- */

    if (a * x == 0.) { /* L130: */
        if (x <= a) {
            /* L100: */ return exp(-log_r);
        } else {
            /* L110:*/  return 0.;
        }
    } else if (a == 0.5) { // e.g. when called from pt()
        /* L120: */
        if (x < 0.25) {
            T p = erf__!T(sqrt(x));
            //R_ifDEBUG_printf(" grat_r(a=%g, x=%g ..)): a=1/2 --> p=erf__(.)= %g\n", a, x, p);
            return (0.5 - p + 0.5)*exp(-log_r);
        
            } else { // 2013-02-27: improvement for "large" x: direct computation of q/r:
            T sx = sqrt(x),
            q_r = erfc1!T(1, sx)/sx * M_SQRT_PI;
            //R_ifDEBUG_printf(" grat_r(a=%g, x=%g ..)): a=1/2 --> q_r=erfc1(..)/r= %g\n", a,x, q_r);
            return q_r;
        }
        
    } else if (x < 1.1) { /* L10:  Taylor series for  P(a,x)/x^a */
        
        T an = 3.,
            c = x,
            sum = x / (a + 3.),
            tol = eps * 0.1 / (a + 1.), t;
        do {
            an += 1.;
            c *= -(x / an);
            t = c / (a + an);
            sum += t;
        } while (fabs(t) > tol);
        
        //R_ifDEBUG_printf(" grat_r(a=%g, x=%g, log_r=%g): sum=%g; Taylor w/ %.0f terms", a,x,log_r, sum, an-3.);
        T j = a * x * ((sum/6. - 0.5/(a + 2.)) * x + 1./(a + 1.)),
            z = a * log(x),
            h = gam1!T(a),
            g = h + 1.;
        
        if ((x >= 0.25 && (a < x / 2.59)) || (z > -0.13394)) {
            // L40:
            T l = rexpm1!T(z),
            q = ((l + 0.5 + 0.5) * j - l) * g - h;
            if (q <= 0.) {
                //R_ifDEBUG_printf(" => q_r= 0.\n");
                /* L110:*/ return 0.;
            } else {
                //R_ifDEBUG_printf(" => q_r=%.15g\n", q * exp(-log_r));
                return q * exp(-log_r);
            }
        
        } else {
            T p = exp(z) * g * (0.5 - j + 0.5);
            //R_ifDEBUG_printf(" => q_r=%.15g\n", (0.5 - p + 0.5) * exp(-log_r));
            return /* q/r = */ (0.5 - p + 0.5) * exp(-log_r);
        }
        
    } else {
    /* L50: ----  (x >= 1.1)  ---- Continued Fraction Expansion */

    T a2n_1 = 1.,
        a2n = 1.,
        b2n_1 = x,
        b2n = x + (1. - a),
        c = 1., am0, an0;

    do {
        a2n_1 = x * a2n + c * a2n_1;
        b2n_1 = x * b2n + c * b2n_1;
        am0 = a2n_1 / b2n_1;
        c += 1.;
        T c_a = c - a;
        a2n = a2n_1 + c_a * a2n;
        b2n = b2n_1 + c_a * b2n;
        an0 = a2n/b2n;
    } while (fabs(an0 - am0) >= eps * an0);

    //R_ifDEBUG_printf(" grat_r(a=%g, x=%g, log_r=%g): Cont.frac. %.0f terms => q_r=%.15g\n", a,x, log_r, c-1., an0);
    return /* q/r = (r * an0)/r = */ an0;
    }
} /* grat_r */


static auto algdiv(T)(T a, T b)
{
/* ----------------------------------------------------------------------- */

/*     COMPUTATION OF LN(GAMMA(B)/GAMMA(A+B)) WHEN B >= 8 */

/*                         -------- */

/*     IN THIS ALGORITHM, DEL(X) IS THE FUNCTION DEFINED BY */
/*     LN(GAMMA(X)) = (X - 0.5)*LN(X) - X + 0.5*LN(2*PI) + DEL(X). */

/* ----------------------------------------------------------------------- */

    /* Initialized data */

    static T c0 = .0833333333333333;
    static T c1 = -.00277777777760991;
    static T c2 = 7.9365066682539e-4;
    static T c3 = -5.9520293135187e-4;
    static T c4 = 8.37308034031215e-4;
    static T c5 = -.00165322962780713;

    T c, d, h, t, u, v, w, x, s3, s5, x2, s7, s9, s11;

/* ------------------------ */
    if (a > b) {
        h = b / a;
        c = 1. / (h + 1.);
        x = h / (h + 1.);
        d = a + (b - 0.5);
    } else {
        h = a / b;
        c = h / (h + 1.);
        x = 1. / (h + 1.);
        d = b + (a - 0.5);
    }

/* Set s<n> = (1 - x^n)/(1 - x) : */

    x2 = x * x;
    s3 = x + x2 + 1.;
    s5 = x + x2 * s3 + 1.;
    s7 = x + x2 * s5 + 1.;
    s9 = x + x2 * s7 + 1.;
    s11 = x + x2 * s9 + 1.;

/* w := Del(b) - Del(a + b) */

    t = 1./ (b * b);
    w = ((((c5 * s11 * t + c4 * s9) * t + c3 * s7) * t + c2 * s5) * t + c1 *
        s3) * t + c0;
    w *= c / b;

/*                    COMBINE THE RESULTS */

    u = d * alnrel!T(a/b);
    v = a * (log(b) - 1.);
    if (u > v)
        return w - v - u;
    else
        return w - u - v;
} /* algdiv */


static void bgrat(T)(T a, T b, T x, T y, T* w, T eps, int* ierr, int log_w)
{
/* -----------------------------------------------------------------------
*     Asymptotic Expansion for I_x(a,b)  when a is larger than b.
*     Compute   w := w + I_x(a,b)
*     It is assumed a >= 15 and b <= 1.
*     eps is the tolerance used.
*     ierr is a variable that reports the status of the results.
*
* if(log_w),  *w  itself must be in log-space;
*     compute   w := w + I_x(a,b)  but return *w = log(w):
*          *w := log(exp(*w) + I_x(a,b)) = logspace_add(*w, log( I_x(a,b) ))
* ----------------------------------------------------------------------- */

    enum n_terms_bgrat = 30;
    T[n_terms_bgrat] c, d;
    T bm1 = b - 0.5 - 0.5, nu = a + bm1 * 0.5, /* nu = a + (b-1)/2 =: T, in (9.1) of * Didonato & Morris(1992), p.362 */
            lnx = (y > 0.375) ? log(x) : alnrel!T(-y), z = -nu * lnx; // z =: u in (9.1) of D.&M.(1992)

    if (b*z == 0.) {
        // should not happen, but does, e.g.,
        // for  pbeta(1e-320, 1e-5, 0.5)  i.e., _subnormal_ x,
        // Warning ... bgrat(a=20.5, b=1e-05, x=1, y=9.99989e-321): ..
        // MATHLIB_WARNING5(
        //    "bgrat(a=%g, b=%g, x=%g, y=%g): z=%g, b*z == 0 underflow, hence inaccurate pbeta()", a, b, x, y, z);
        /* L_Error:    THE EXPANSION CANNOT BE COMPUTED */
         *ierr = 1; return;
    }

/*                 COMPUTATION OF THE EXPANSION */
    T
    /* r1 = b * (gam1(b) + 1.) * exp(b * log(z)),// = b/gamma(b+1) z^b = z^b / gamma(b)
     * set r := exp(-z) * z^b / gamma(b) ;
     *          gam1(b) = 1/gamma(b+1) - 1 , b in [-1/2, 3/2] */
    // exp(a*lnx) underflows for large (a * lnx); e.g. large a ==> using log_r := log(r):
    // r = r1 * exp(a * lnx) * exp(bm1 * 0.5 * lnx);
    // log(r)=log(b) + log1p(gam1(b)) + b * log(z) + (a * lnx) + (bm1 * 0.5 * lnx),
    log_r = log(b) + log1p(gam1!T(b)) + b*log(z) + nu*lnx,
    // FIXME work with  log_u = log(u)  also when log_p=FALSE  (??)
    // u is 'factored out' from the expansion {and multiplied back, at the end}:
    log_u = log_r - (algdiv!T(b, a) + b*log(nu)),// algdiv(b,a) = log(gamma(a)/gamma(a+b))
    /* u = (log_p) ? log_r - u : exp(log_r-u); // =: M  in (9.2) of {reference above} */
    /* u = algdiv(b, a) + b * log(nu);// algdiv(b,a) = log(gamma(a)/gamma(a+b)) */
    // u = (log_p) ? log_u : exp(log_u); // =: M  in (9.2) of {reference above}
    u = exp(log_u);

    if (log_u == -T.infinity) {
        //R_ifDEBUG_printf(" bgrat(*): underflow log_u = -Inf  = log_r -u', log_r = %g ", log_r);
        /* L_Error:    THE EXPANSION CANNOT BE COMPUTED */ *ierr = 2; return;
    }

    // Rboolean
    int u_0 = (u == 0.); // underflow --> do work with log(u) == log_u !
    T l = // := *w/u .. but with care: such that it also works when u underflows to 0:
    log_w ? ((*w == -T.infinity) ? 0. : exp(*w - log_u)) : ((*w == 0.) ? 0. : exp(log(*w) - log_u));

        //R_ifDEBUG_printf(" bgrat(a=%g, b=%g, x=%g, *)\n -> u=%g, l='w/u'=%g, ", a,b,x, u, l);
    T q_r = grat_r(b, z, log_r, eps), // = q/r of former grat1(b,z, r, &p, &q)
        v = 0.25 / (nu * nu),
        t2 = lnx * 0.25 * lnx,
        j = q_r,
        sum = j,
        t = 1., cn = 1., n2 = 0.;
    for (int n = 1; n <= n_terms_bgrat; ++n) {
        T bp2n = b + n2;
        j = (bp2n * (bp2n + 1.) * j + (z + bp2n + 1.) * t) * v;
        n2 += 2.;
        t *= t2;
        cn /= n2 * (n2 + 1.);
        int nm1 = n - 1;
        c[nm1] = cn;
        T s = 0.;
        if (n > 1) {
            T coef = b - n;
            for (int i = 1; i <= nm1; ++i) {
                s += coef * c[i - 1] * d[nm1 - i];
                coef += b;
            }
        }
        d[nm1] = bm1 * cn + s / n;
        T dj = d[nm1] * j;
        sum += dj;
        if (sum <= 0.) {
            //R_ifDEBUG_printf(" bgrat(*): sum_n(..) <= 0; should not happen (n=%d)\n", n);
            /* L_Error:    THE EXPANSION CANNOT BE COMPUTED */ *ierr = 3; return;
        }
        if (fabs(dj) <= eps * (sum + l)) {
            *ierr = 0;
            break;
        } else if(n == n_terms_bgrat) { // never? ; please notify R-core if seen:
            *ierr = 4;
            //MATHLIB_WARNING5(
            //"bgrat(a=%g, b=%g, x=%g) *no* convergence: NOTIFY R-core!\n dj=%g, rel.err=%g\n", a,b,x, dj, fabs(dj) /(sum + l));
        }
    } // for(n .. n_terms..)

/*                    ADD THE RESULTS TO W */

    if(log_w) // *w is in log space already:
        *w = logspace_add!T(*w, log_u + log(sum));
    else
        *w += (u_0 ? exp(log_u + log(sum)) : u * sum);
    return;
} /* bgrat */


static auto gsumln(T)(T a, T b)
{
/* ----------------------------------------------------------------------- */
/*          EVALUATION OF THE FUNCTION LN(GAMMA(A + B)) */
/*          FOR 1 <= A <= 2  AND  1 <= B <= 2 */
/* ----------------------------------------------------------------------- */

    T x = a + b - 2.;/* in [0, 2] */

    if (x <= 0.25)
        return gamln1!T(x + 1.);

    /* else */
    if (x <= 1.25)
        return gamln1!T(x) + alnrel!T(x);
    /* else x > 1.25 : */
    return gamln1!T(x - 1.) + log(x * (x + 1.));

} /* gsumln */


static auto betaln(T)(T a0, T b0)
{
    /* -----------------------------------------------------------------------
     *     Evaluation of the logarithm of the beta function  ln(beta(a0,b0))
     * ----------------------------------------------------------------------- */

    static T e = .918938533204673;/* e == 0.5*LN(2*PI) */

    T a = min!T(a0 ,b0), b = max!T(a0, b0);
    int n;

    if (a < 8.) {
        if (a < 1.) {
        /* ----------------------------------------------------------------------- */
        //                          A < 1
        /* ----------------------------------------------------------------------- */
            if (b < 8.)
                return gamln!T(a) + (gamln!T(b) - gamln!T(a+b));
            else
                return gamln!T(a) + algdiv!T(a, b);
        }
        /* else */
        /* ----------------------------------------------------------------------- */
        //              1 <= A < 8
        /* ----------------------------------------------------------------------- */
        T w;
        if (a < 2.) {
            if (b <= 2.) {
                return gamln!T(a) + gamln!T(b) - gsumln!T(a, b);
            }
            /* else */
        
            if (b < 8.) {
                w = 0.;
                goto L40;
            }
            return gamln!T(a) + algdiv!T(a, b);
        }
        // else L30:    REDUCTION OF A WHEN B <= 1000
        
        if (b <= 1e3) {
            n = cast(int)(a - 1.);
            w = 1.;
            for (int i = 1; i <= n; ++i) {
                a += -1.;
                T h = a / b;
                w *= h / (h + 1.);
            }
            w = log(w);
        
            if (b >= 8.)
                return w + gamln!T(a) + algdiv!T(a, b);
        
            // else
        L40:
            //  1 < A <= B < 8 :  reduction of B
            n = cast(int)(b - 1.);
            T z = 1.;
            for (int i = 1; i <= n; ++i) {
                b += -1.;
                z *= b / (a + b);
            }
            return w + log(z) + (gamln!T(a) + (gamln!T(b) - gsumln!T(a, b)));
        } else { // L50:  reduction of A when  B > 1000
            n = cast(int)(a - 1.);
            w = 1.;
            for (int i = 1; i <= n; ++i) {
                a += -1.;
                w *= a / (a / b + 1.);
            }
            return log(w) - n * log(b) + (gamln!T(a) + algdiv!T(a, b));
        }
        
    } else {
    /* ----------------------------------------------------------------------- */
        // L60:         A >= 8
    /* ----------------------------------------------------------------------- */

    T w = bcorr!T(a, b), h = a / b,
        u = -(a - 0.5) * log(h / (h + 1.)),
        v = b * alnrel!T(h);
    if (u > v)
        return log(b) * -0.5 + e + w - v - u;
    else
        return log(b) * -0.5 + e + w - u - v;
    }

} /* betaln */



// called only once from  bup(),  as   r = brcmp1(mu, a, b, x, y, FALSE) / a;
static auto brcmp1(T)(int mu, T a, T b, T x, T y, int give_log)
{
/* -----------------------------------------------------------------------
 *          Evaluation of    exp(mu) * x^a * y^b / beta(a,b)
 * ----------------------------------------------------------------------- */

    static T const__ = .398942280401433; /* == 1/sqrt(2*pi); */
    /* R has  M_1_SQRT_2PI */

    /* Local variables */
    T c, t, u, v, z, a0, b0, apb;

    a0 = min!T(a,b);
    if (a0 < 8.) {
    T lnx, lny;
    if (x <= .375) {
        lnx = log(x);
        lny = alnrel!T(-x);
    } else if (y > .375) {
        // L11:
        lnx = log(x);
        lny = log(y);
    } else {
        lnx = alnrel!T(-y);
        lny = log(y);
    }

    // L20:
    z = a * lnx + b * lny;
    if (a0 >= 1.) {
        z -= betaln!T(a, b);
        return esum!T(mu, z, give_log);
    }
    // else :
    /* ----------------------------------------------------------------------- */
    /*              PROCEDURE FOR A < 1 OR B < 1 */
    /* ----------------------------------------------------------------------- */
    // L30:
    b0 = max!T(a,b);
    if (b0 >= 8.) {
    /* L80:                  ALGORITHM FOR b0 >= 8 */
        u = gamln1!T(a0) + algdiv!T(a0, b0);
        //R_ifDEBUG_printf(" brcmp1(mu,a,b,*): a0 < 1, b0 >= 8;  z=%.15g\n", z);
        return give_log ? log(a0) + esum!T(mu, z - u, 1) : a0  * esum!T(mu, z - u, 0);

    } else if (b0 <= 1.) {
        //                   a0 < 1, b0 <= 1
        T ans = esum!T(mu, z, give_log);
        if (ans == (give_log ? T.infinity : 0.))
            return ans;

        apb = a + b;
        if (apb > 1.) {
            // L40:
            u = a + b - 1.;
            z = (gam1!T(u) + 1.) / apb;
        } else {
            z = gam1!T(apb) + 1.;
        }
        // L50:
        c = give_log ? log1p(gam1!T(a)) + log1p(gam1!T(b)) - log(z) : (gam1!T(a) + 1.) * (gam1!T(b) + 1.) / z;
        //R_ifDEBUG_printf(" brcmp1(mu,a,b,*): a0 < 1, b0 <= 1;  c=%.15g\n", c);
        return give_log ? ans + log(a0) + c - log1p(a0 / b0) : ans * (a0 * c) / (a0 / b0 + 1.);
    }
    // else:               algorithm for    a0 < 1 < b0 < 8
    // L60:
    u = gamln1!T(a0);
    int n = cast(int)(b0 - 1.);
    if (n >= 1) {
        c = 1.;
        for (int i = 1; i <= n; ++i) {
            b0 += -1.;
            c *= b0 / (a0 + b0);
            /* L61: */
        }
        u += log(c); // TODO?: log(c) = log( prod(...) ) =  sum( log(...) )
    }
    // L70:
    z -= u;
    b0 += -1.;
    apb = a0 + b0;
    if (apb > 1.) {
        // L71:
        t = (gam1!T(apb - 1.) + 1.) / apb;
    } else {
        t = gam1!T(apb) + 1.;
    }
    //R_ifDEBUG_printf(" brcmp1(mu,a,b,*): a0 < 1 < b0 < 8;  t=%.15g\n", t);
    // L72:
    return give_log
        ? log(a0)+ esum!T(mu, z, 1) + log1p(gam1!T(b0)) - log(t) // TODO? log(t) = log1p(..)
        :     a0 * esum!T(mu, z, 0) * (gam1!T(b0) + 1.) / t;

    } else {

/* ----------------------------------------------------------------------- */
/*              PROCEDURE FOR A >= 8 AND B >= 8 */
/* ----------------------------------------------------------------------- */
    // L100:
    T h, x0, y0, lambda;
    if (a > b) {
        // L101:
        h = b / a;
        x0 = 1. / (h + 1.);// => lx0 := log(x0) = 0 - log1p(h)
        y0 = h / (h + 1.);
        lambda = (a + b) * y - b;
    } else {
        h = a / b;
        x0 = h / (h + 1.);  // => lx0 := log(x0) = - log1p(1/h)
        y0 = 1. / (h + 1.);
        lambda = a - (a + b) * x;
    }
    T lx0 = -log1p(b/a); // in both cases

    //R_ifDEBUG_printf(" brcmp1(mu,a,b,*): a,b >= 8;  x0=%.15g, lx0=log(x0)=%.15g\n", x0, lx0);
    // L110:
    T e = -lambda / a;
    if (fabs(e) > 0.6) {
        // L111:
        u = e - log(x / x0);
    } else {
        u = rlog1!T(e);
    }

    // L120:
    e = lambda / b;
    if (fabs(e) > 0.6) {
        // L121:
        v = e - log(y / y0);
    } else {
        v = rlog1!T(e);
    }

    // L130:
    z = esum!T(mu, -(a*u + b*v), give_log);
    return give_log ? log(const__) + (log(b) + lx0)/2. + z - bcorr!T(a, b)
        :     const__ * sqrt(b * x0)*z*exp(-bcorr!T(a, b));
    }

} /* brcmp1 */


static auto brcomp(T)(T a, T b, T x, T y, int log_p)
{
    /* -----------------------------------------------------------------------
     *       Evaluation of x^a * y^b / Beta(a,b)
     * ----------------------------------------------------------------------- */

    static T const__ = .398942280401433; /* == 1/sqrt(2*pi); */
    /* R has  M_1_SQRT_2PI , and M_LN_SQRT_2PI = ln(sqrt(2*pi)) = 0.918938.. */
    int i, n;
    T c, e, u, v, z, a0, b0, apb;

    mixin R_D__0!log_p;
    if (x == 0. || y == 0.) {
    return R_D__0;
    }
    a0 = min!T(a, b);
    if (a0 < 8.) {
    T lnx, lny;
    if (x <= .375) {
        lnx = log(x);
        lny = alnrel!T(-x);
    }
    else {
        if (y > .375) {
        lnx = log(x);
        lny = log(y);
        } else {
        lnx = alnrel!T(-y);
        lny = log(y);
        }
    }

    z = a * lnx + b * lny;
    if (a0 >= 1.) {
        z -= betaln!T(a, b);
        return R_D_exp!T(z, log_p);
    }

    /* ----------------------------------------------------------------------- */
    /*      PROCEDURE FOR a < 1 OR b < 1 */
    /* ----------------------------------------------------------------------- */

    b0 = max(a, b);
    if (b0 >= 8.) { /* L80: */
        u = gamln1!T(a0) + algdiv!T(a0, b0);

        return (log_p ? log(a0) + (z - u)  : a0 * exp(z - u));
    }
    /* else : */

    if (b0 <= 1.) { /*      algorithm for max(a,b) = b0 <= 1 */

        T e_z = R_D_exp!T(z, log_p);

        if (!log_p && e_z == 0.) /* exp() underflow */
        return 0.;

        apb = a + b;
        if (apb > 1.) {
        u = a + b - 1.;
        z = (gam1!T(u) + 1.) / apb;
        } else {
        z = gam1!T(apb) + 1.;
        }

        c = (gam1!T(a) + 1.) * (gam1!T(b) + 1.) / z;
        /* FIXME? log(a0*c)= log(a0)+ log(c) and that is improvable */
        return (log_p ? e_z + log(a0 * c) - log1p(a0/b0)
            : e_z * (a0 * c) / (a0 / b0 + 1.));
    }

    /* else :         ALGORITHM FOR 1 < b0 < 8 */

    u = gamln1!T(a0);
    n = cast(int)(b0 - 1.);
    if (n >= 1) {
        c = 1.;
        for (i = 1; i <= n; ++i) {
            b0 += -1.;
            c *= b0 / (a0 + b0);
        }
        u = log(c) + u;
    }
    z -= u;
    b0 += -1.;
    apb = a0 + b0;
    T t;
    if (apb > 1.) {
        u = a0 + b0 - 1.;
        t = (gam1!T(u) + 1.) / apb;
    } else {
        t = gam1!T(apb) + 1.;
    }

    return (log_p ? log(a0) + z + log1p(gam1!T(b0))  - log(t) : a0 * exp(z) * (gam1!T(b0) + 1.) / t);

    } else {
    /* ----------------------------------------------------------------------- */
    /*      PROCEDURE FOR A >= 8 AND B >= 8 */
    /* ----------------------------------------------------------------------- */
    T h, x0, y0, lambda;
    if (a <= b) {
        h = a / b;
        x0 = h / (h + 1.);
        y0 = 1. / (h + 1.);
        lambda = a - (a + b) * x;
    } else {
        h = b / a;
        x0 = 1. / (h + 1.);
        y0 = h / (h + 1.);
        lambda = (a + b) * y - b;
    }

    e = -lambda / a;
    if (fabs(e) > .6)
        u = e - log(x / x0);
    else
        u = rlog1!T(e);

    e = lambda / b;
    if (fabs(e) <= .6)
        v = rlog1!T(e);
    else
        v = e - log(y / y0);

    z = log_p ? -(a * u + b * v) : exp(-(a * u + b * v));

    return(log_p ? -M_LN_SQRT_2PI + .5*log(b * x0) + z - bcorr!T(a,b)
           : const__ * sqrt(b * x0) * z * exp(-bcorr!T(a, b)));
    }
} /* brcomp */



static auto bfrac(T)(T a, T b, T x, T y, T lambda, T eps, int log_p)
{
/* -----------------------------------------------------------------------
       Continued fraction expansion for I_x(a,b) when a, b > 1.
       It is assumed that  lambda = (a + b)*y - b.
   -----------------------------------------------------------------------*/

    T c, e, n, p, r, s, t, w, c0, c1, r0, an, bn, yp1, anp1, bnp1, beta, alpha, brc;

    if(!isFinite(lambda))
        return T.nan;// TODO: can return 0 or 1 (?)
    //R_ifDEBUG_printf(" bfrac(a=%g, b=%g, x=%g, y=%g, lambda=%g, eps=%g, log_p=%d):", a, b, x, y, lambda, eps, log_p);
    brc = brcomp!T(a, b, x, y, log_p);
    if(isNaN(brc)) { // e.g. from   L <- 1e308; pnbinom(L, L, mu = 5)
        //R_ifDEBUG_printf(" --> brcomp(a,b,x,y) = NaN\n");
        return T.nan; // TODO: could we know better?
    }
    if (!log_p && brc == 0.) {
        //R_ifDEBUG_printf(" --> brcomp(a,b,x,y) underflowed to 0.\n");
        return 0.;
    }
    //#ifdef DEBUG_bratio
    //    else
    //    REprintf("\n");
    //#endif

    c = lambda + 1.;
    c0 = b / a;
    c1 = 1. / a + 1.;
    yp1 = y + 1.;

    n = 0.;
    p = 1.;
    s = a + 1.;
    an = 0.;
    bn = 1.;
    anp1 = 1.;
    bnp1 = c / c1;
    r = c1 / c;

/*        CONTINUED FRACTION CALCULATION */

    do {
        n += 1.;
        t = n/a;
        w = n*(b - n)*x;
        e = a / s;
        alpha = p * (p + c0)*e*e*(w*x);
        e = (t + 1.) / (c1 + t + t);
        beta = n + w / s + e*(c + n*yp1);
        p = t + 1.;
        s += 2.;
        
        /* update an, bn, anp1, and bnp1 */
        
        t = alpha*an + beta*anp1; an = anp1; anp1 = t;
        t = alpha*bn + beta*bnp1; bn = bnp1; bnp1 = t;
        
        r0 = r;
        r = anp1 / bnp1;
        //#ifdef _not_normally_DEBUG_bfrac
        //    R_ifDEBUG_printf(" n=%5.0f, a_{n,n+1}= (%12g,%12g),  b_{n,n+1} = (%12g,%12g) => r0,r = (%14g,%14g)\n",
        //             n, an,anp1, bn,bnp1, r0, r);
        //#endif
        if (fabs(r - r0) <= eps * r)
            break;
        
        /* rescale an, bn, anp1, and bnp1 */
        
        an /= bnp1;
        bn /= bnp1;
        anp1 = r;
        bnp1 = 1.;
    } while (n < 10000);// arbitrary; had '1' --> infinite loop for  lambda = Inf
    //R_ifDEBUG_printf("  in bfrac(): n=%.0f terms cont.frac.; brc=%g, r=%g\n", n, brc, r);
    //if(n >= 10000 && fabs(r - r0) > eps * r)
    //    MATHLIB_WARNING5(" bfrac(a=%g, b=%g, x=%g, y=%g, lambda=%g) did *not* converge (in 10000 steps)\n", a, b, x, y, lambda);
    return (log_p ? brc + log(r) : brc*r);
} /* bfrac */



static auto bup(T)(T a, T b, T x, T y, int n, T eps, int give_log)
{
    /* ----------------------------------------------------------------------- */
    /*     EVALUATION OF I_x(A,B) - I_x(A+N,B) WHERE N IS A POSITIVE INT. */
    /*     EPS IS THE TOLERANCE USED. */
    /* ----------------------------------------------------------------------- */

    T ret_val;
    int i, k, mu;
    T d, l;

    // Obtain the scaling factor exp(-mu) and exp(mu)*(x^a * y^b / beta(a,b))/a

    T apb = a + b,
    ap1 = a + 1.;
    if (n > 1 && a >= 1. && apb >= ap1 * 1.1) {
        mu = cast(int)fabs(exparg!T(1));
        k = cast(int)exparg!T(0);
        if (mu > k)
            mu = k;
        d = exp(-cast(T) mu);
    } else {
        mu = 0;
        d = 1.;
    }

    /* L10: */
    ret_val = give_log ? brcmp1!T(mu, a, b, x, y, 1) - log(a) : brcmp1!T(mu, a, b, x, y, 0)  / a;
    if(n == 1 || (give_log && ret_val == -T.infinity) || (!give_log && ret_val == 0.))
        return ret_val;

    int nm1 = n - 1;
    T w = d;

    /* LET K BE THE INDEX OF THE MAXIMUM TERM */

    k = 0;
    if (b > 1.) {
    if (y > 1e-4) {
        T r = (b - 1.) * x / y - a;
        if (r >= 1.)
        k = (r < nm1) ? cast(int)r : nm1;
    } else
        k = nm1;

    // ADD THE INCREASING TERMS OF THE SERIES - if k > 0
    /* L30: */
        for (i = 0; i < k; ++i) {
            l = cast(T) i;
            d *= (apb + l) / (ap1 + l) * x;
            w += d;
        }
    }

    // L40:     ADD THE REMAINING TERMS OF THE SERIES

    for (i = k; i < nm1; ++i) {
        l = cast(T) i;
        d *= (apb + l) / (ap1 + l) * x;
        w += d;
        if (d <= eps * w) /* relativ convergence (eps) */
            break;
    }

    // L50: TERMINATE THE PROCEDURE
    if(give_log) {
        ret_val += log(w);
    } else
        ret_val *= w;

    return ret_val;
} /* bup */


static auto bpser(T)(T a, T b, T x, T eps, int log_p)
{
/* -----------------------------------------------------------------------
 * Power SERies expansion for evaluating I_x(a,b) when
 *         b <= 1 or b*x <= 0.7.   eps is the tolerance used.
 * NB: if log_p is TRUE, also use it if   (b < 40  & lambda > 650)
 * ----------------------------------------------------------------------- */

    int i, m;
    T ans, c, t, u, z, a0, b0, apb;
    mixin R_D__0!log_p;

    if (x == 0.) {
        return R_D__0;
    }
/* ----------------------------------------------------------------------- */
/*        compute the factor  x^a/(a*Beta(a,b)) */
/* ----------------------------------------------------------------------- */
    a0 = min!T(a,b);
    if (a0 >= 1.) { /*       ------  1 <= a0 <= b0  ------ */
        z = a * log(x) - betaln!T(a, b);
        ans = log_p ? z - log(a) : exp(z) / a;
    }
    else {
    b0 = max!T(a,b);

    if (b0 < 8.) {

        if (b0 <= 1.) { /*   ------  a0 < 1  and  b0 <= 1  ------ */

        if(log_p) {
            ans = a * log(x);
        } else {
            ans = pow(x, a);
            if (ans == 0.) /* once underflow, always underflow .. */
            return ans;
        }
        apb = a + b;
        if (apb > 1.) {
            u = a + b - 1.;
            z = (gam1!T(u) + 1.) / apb;
        } else {
            z = gam1!T(apb) + 1.;
        }
        c = (gam1!T(a) + 1.) * (gam1!T(b) + 1.) / z;

        if(log_p) /* FIXME ? -- improve quite a bit for c ~= 1 */
            ans += log(c * (b / apb));
        else
            ans *=  c * (b / apb);

        } else { /*     ------  a0 < 1 < b0 < 8  ------ */

        u = gamln1!T(a0);
        m = cast(int)(b0 - 1.);
        if (m >= 1) {
            c = 1.;
            for (i = 1; i <= m; ++i) {
            b0 += -1.;
            c *= b0 / (a0 + b0);
            }
            u += log(c);
        }

        z = a * log(x) - u;
        b0 += -1.; // => b0 in (0, 7)
        apb = a0 + b0;
        if (apb > 1.) {
            u = a0 + b0 - 1.;
            t = (gam1!T(u) + 1.) / apb;
        } else {
            t = gam1!T(apb) + 1.;
        }

        if(log_p) /* FIXME? potential for improving log(t) */
            ans = z + log(a0 / a) + log1p(gam1!T(b0)) - log(t);
        else
            ans = exp(z) * (a0 / a) * (gam1!T(b0) + 1.) / t;
        }

    } else { /*         ------  a0 < 1 < 8 <= b0  ------ */

        u = gamln1!T(a0) + algdiv!T(a0, b0);
        z = a * log(x) - u;

        if(log_p)
        ans = z + log(a0 / a);
        else
        ans = a0 / a * exp(z);
    }
    }
    //R_ifDEBUG_printf(" bpser(a=%g, b=%g, x=%g, log=%d): prelim.ans = %.14g;\n", a,b,x, log_p, ans);
    if (ans == R_D__0 || (!log_p && a <= eps * 0.1)) {
    return ans;
    }

    /* ----------------------------------------------------------------------- */
    /*             COMPUTE THE SERIES */
    /* ----------------------------------------------------------------------- */
    T tol = eps / a,
    n = 0.,
    sum = 0., w;
    c = 1.;
    do { // sum is alternating as long as n < b (<==> 1 - b/n < 0)
        n += 1.;
        c *= (0.5 - b / n + 0.5) * x;
        w = c / (a + n);
        sum += w;
    } while (n < 1e7 && fabs(w) > tol);
    if(fabs(w) > tol) { // the series did not converge (in time)
    // warn only when the result seems to matter:
    //if(( log_p && !(a*sum > -1. && fabs(log1p(a * sum)) < eps*fabs(ans))) || (!log_p && fabs(a*sum + 1.) != 1.))
        //MATHLIB_WARNING5(" bpser(a=%g, b=%g, x=%g,...) did not converge (n=1e7, |w|/tol=%g > 1; A=%g)", a,b,x, fabs(w)/tol, ans);
    }
    //R_ifDEBUG_printf("  -> n=%.0f iterations, |w|=%g %s %g=tol:=eps/a ==> a*sum=%g\n", n, fabs(w), (fabs(w) > tol) ? ">!!>" : "<=", tol, a*sum);
    if(log_p) {
        if (a*sum > -1.)
            ans += log1p(a*sum);
        else {
            //if(ans > ML_NEGINF)
            //MATHLIB_WARNING3("pbeta(*, log.p=TRUE) -> bpser(a=%g, b=%g, x=%g,...) underflow to -Inf", a, b, x);
            ans = -T.infinity;
        }
    } else if (a*sum > -1.)
        ans *= (a*sum + 1.);
    else // underflow to
        ans = 0.;
    return ans;
} /* bpser */



static auto apser(T)(T a, T b, T x, T eps)
{
/* -----------------------------------------------------------------------
 *     apser() yields the incomplete beta ratio  I_{1-x}(b,a)  for
 *     a <= min(eps,eps*b), b*x <= 1, and x <= 0.5,  i.e., a is very small.
 *     Use only if above inequalities are satisfied.
 * ----------------------------------------------------------------------- */

    static const(T) g = .577215664901533;

    T tol, c, j, s, t, aj;
    T bx = b * x;

    t = x - bx;
    if (b * eps <= 0.02)
        c = log(x) + psi!T(b) + g + t;
    else // b > 2e13 : psi(b) ~= log(b)
        c = log(bx) + g + t;

    tol = eps * 5. * fabs(c);
    j = 1.;
    s = 0.;
    do {
        j += 1.;
        t *= x - bx / j;
        aj = t / j;
        s += aj;
    } while (fabs(aj) > tol);

    return -a*(c + s);
} /* apser */


auto fpser(T)(T a, T b, T x, T eps, int log_p)
{
    /* ----------------------------------------------------------------------- *
    
     *                 EVALUATION OF I (A,B)
     *                                X
    
     *          FOR B < MIN(EPS, EPS*A) AND X <= 0.5
    
     * ----------------------------------------------------------------------- */

    T ans, c, s, t, an, tol;

    /* SET  ans := x^a : */
    if (log_p) {
        ans = a * log(x);
    } else if (a > eps * 0.001) {
        t = a * log(x);
        if (t < exparg!T(1)) { /* exp(t) would underflow */
            return 0.;
        }
        ans = exp(t);
    } else
    ans = 1.;

/*                NOTE THAT 1/B(A,B) = B */

    if (log_p)
        ans += log(b) - log(a);
    else
        ans *= b / a;

    tol = eps / a;
    an = a + 1.;
    t = x;
    s = t / an;
    do {
        an += 1.;
        t = x * t;
        c = t / an;
        s += c;
    } while (fabs(c) > tol);

    if (log_p)
        ans += log1p(a * s);
    else
        ans *= a * s + 1.;
    return ans;
} /* fpser */

immutable(string) SET_0_noswap(){
    return `a0 = a; x0 = x; b0 = b; y0 = y;`;
}

immutable(string) SET_0_swap(){  
    return `a0 = b;  x0 = y, b0 = a;  y0 = x;`;
}

void bratio(T)(T a, T b, T x, T y, T* w, T* w1, int *ierr, int log_p)
{
/* -----------------------------------------------------------------------

 *        Evaluation of the Incomplete Beta function I_x(a,b)

 *             --------------------

 *     It is assumed that a and b are nonnegative, and that x <= 1
 *     and y = 1 - x.  Bratio assigns w and w1 the values

 *          w  = I_x(a,b)
 *          w1 = 1 - I_x(a,b)

 *     ierr is a variable that reports the status of the results.
 *     If no input errors are detected then ierr is set to 0 and
 *     w and w1 are computed. otherwise, if an error is detected,
 *     then w and w1 are assigned the value 0 and ierr is set to
 *     one of the following values ...

 *    ierr = 1  if a or b is negative
 *    ierr = 2  if a = b = 0
 *    ierr = 3  if x < 0 or x > 1
 *    ierr = 4  if y < 0 or y > 1
 *    ierr = 5  if x + y != 1
 *    ierr = 6  if x = a = 0
 *    ierr = 7  if y = b = 0
 *    ierr = 8  (not used currently)
 *    ierr = 9  NaN in a, b, x, or y
 *    ierr = 10     (not used currently)
 *    ierr = 11  bgrat() error code 1 [+ warning in bgrat()]
 *    ierr = 12  bgrat() error code 2   (no warning here)
 *    ierr = 13  bgrat() error code 3   (no warning here)
 *    ierr = 14  bgrat() error code 4 [+ WARNING in bgrat()]


 * --------------------
 *     Written by Alfred H. Morris, Jr.
 *    Naval Surface Warfare Center
 *    Dahlgren, Virginia
 *     Revised ... Nov 1991
* ----------------------------------------------------------------------- */

    // Rboolean
    int do_swap, a_lt_b;
    int n, ierr1 = 0;
    T z, a0, b0, x0, y0, lambda;

    /*  eps is a machine dependent constant: the smallest
     *      floating point number for which   1. + eps > 1.
     * NOTE: for almost all purposes it is replaced by 1e-15 (~= 4.5 times larger) below */
    T eps = 2.*d1mach!T(3); /* == DBL_EPSILON (in R, Rmath) */

    /* ----------------------------------------------------------------------- */
    mixin R_D__0!log_p;
    mixin R_D__1!log_p;
    *w  = R_D__0;
    *w1 = R_D__0;

    //#ifdef IEEE_754
    // safeguard, preventing infinite loops further down
    if (isNaN(x) || isNaN(y) || isNaN(a) || isNaN(b)){
        *ierr = 9;
        return;
    }
    //#endif
    if(a < 0. || b < 0.){
        *ierr = 1;
        return;
    }
    if(a == 0. && b == 0.){
        *ierr = 2; return;
    }
    if(x < 0. || x > 1.){
        *ierr = 3; return;
    }
    if(y < 0. || y > 1.){
        *ierr = 4; return;
    }

    /* check that  'y == 1 - x' : */
    z = x + y - 0.5 - 0.5;

    if (fabs(z) > eps * 3.){
        *ierr = 5; return;
    }

    //R_ifDEBUG_printf("bratio(a=%g, b=%g, x=%9g, y=%9g, .., log_p=%d): ",
    //         a,b,x,y, log_p);
    *ierr = 0;
    if(x == 0.)
        goto L200;
    if(y == 0.)
        goto L210;

    if (a == 0.) goto L211;
    if (b == 0.) goto L201;

    eps = max!T(eps, 1e-15);
    //Rboolean
    a_lt_b = (a < b);
    if (/* max(a,b) */ (a_lt_b ? b : a) < eps * .001){ /* procedure for a and b < 0.001 * eps */
        // L230:  -- result *independent* of x (!)
        // *w  = a/(a+b)  and  w1 = b/(a+b) :
        if(log_p) {
            if(a_lt_b) {
            *w  = log1p(-a/(a+b)); // notably if a << b
            *w1 = log(a/(a+b));
            } else { // b <= a
            *w  = log(b/(a+b));
            *w1 = log1p(-b/(a+b));
            }
        } else {
            *w  = b/(a + b);
            *w1 = a/(a + b);
        }
        
        //R_ifDEBUG_printf("a & b very small -> simple ratios (%g,%g)\n", *w,*w1);
        return;
    }

//#define SET_0_noswap \
//    a0 = a;  x0 = x; \
//    b0 = b;  y0 = y;

//#define SET_0_swap   \
//    a0 = b;  x0 = y; \
//    b0 = a;  y0 = x;

    if (min!T(a,b) <= 1.) { /*------------------------ a <= 1  or  b <= 1 ---- */
        
        do_swap = (x > 0.5);
        if (do_swap) {
            mixin(SET_0_swap());
        } else {
            mixin(SET_0_noswap());
        }
        /* now have  x0 <= 1/2 <= y0  (still  x0+y0 == 1) */
        
        //R_ifDEBUG_printf(" min(a,b) <= 1, do_swap=%d;", do_swap);
        
        if (b0 < min!T(eps, eps * a0)) { /* L80: */
            *w = fpser!T(a0, b0, x0, eps, log_p);
            *w1 = log_p ? R_Log1_Exp!T(*w) : 0.5 - *w + 0.5;
            //R_ifDEBUG_printf("  b0 small -> w := fpser(*) = %.15g\n", *w);
            goto L_end;
        }
        
        if (a0 < min!T(eps, eps * b0) && b0 * x0 <= 1.) { /* L90: */
            *w1 = apser!T(a0, b0, x0, eps);
            //R_ifDEBUG_printf("  a0 small -> w1 := apser(*) = %.15g\n", *w1);
            goto L_end_from_w1;
        }
        
        //Rboolean
        int did_bup = 0;
        if (max!T(a0,b0) > 1.) { /* L20:  min(a,b) <= 1 < max(a,b)  */
            //R_ifDEBUG_printf("\n L20:  min(a,b) <= 1 < max(a,b); ");
            if (b0 <= 1.) goto L_w_bpser;
        
            if (x0 >= 0.29) /* was 0.3, PR#13786 */ goto L_w1_bpser;
        
            if (x0 < 0.1 && pow(x0*b0, a0) <= 0.7)  goto L_w_bpser;
        
            if (b0 > 15.) {
                *w1 = 0.;
                goto L131;
            }
        } else { /*  a, b <= 1 */
            //R_ifDEBUG_printf("\n      both a,b <= 1; ");
            if (a0 >= min!T(0.2, b0)) goto L_w_bpser;
        
            if (pow(x0, a0) <= 0.9) goto L_w_bpser;
        
            if (x0 >= 0.3) goto L_w1_bpser;
        }
        n = 20; /* goto L130; */
        *w1 = bup!T(b0, a0, y0, x0, n, eps, 0); did_bup = 1;
        //R_ifDEBUG_printf("  ... n=20 and *w1 := bup(*) = %.15g; ", *w1);
        b0 += n;
        L131:
        //R_ifDEBUG_printf(" L131: bgrat(*, w1=%.15g) ", *w1);
        bgrat!T(b0, a0, y0, x0, w1, 15*eps, &ierr1, 0);
        //#ifdef DEBUG_bratio
        //    REprintf(" ==> new w1=%.15g", *w1);
        //    if(ierr1) REprintf(" ERROR(code=%d)\n", ierr1) ; else REprintf("\n");
        //#endif
        if(*w1 == 0 || (0 < *w1 && *w1 < DBL_MIN)) { // w1=0 or very close:
            // "almost surely" from underflow, try more: [2013-03-04]
        // FIXME: it is even better to do this in bgrat *directly* at least for the case
        //  !did_bup, i.e., where *w1 = (0 or -Inf) on entry
            //R_ifDEBUG_printf(" denormalized or underflow (?) -> retrying: ");
            if(did_bup) { // re-do that part on log scale:
            *w1 = bup!T(b0-n, a0, y0, x0, n, eps, 1);
            }
            else *w1 = -T.infinity; // = 0 on log-scale
            bgrat!T(b0, a0, y0, x0, w1, 15*eps, &ierr1, 1);
            if(ierr1)
                *ierr = 10 + ierr1;
        //#ifdef DEBUG_bratio
        //        REprintf(" ==> new log(w1)=%.15g", *w1);
        //        if(ierr1) REprintf(" Error(code=%d)\n", ierr1) ; else REprintf("\n");
        //#endif
            goto L_end_from_w1_log;
        }
        // else
        if(ierr1)
            *ierr = 10 + ierr1;
        //if(*w1 < 0)
        //    MATHLIB_WARNING4("bratio(a=%g, b=%g, x=%g): bgrat() -> w1 = %g", a, b, x, *w1);
        goto L_end_from_w1;
    } else { /* L30: -------------------- both  a, b > 1  {a0 > 1  &  b0 > 1} ---*/
        
        /* lambda := a y - b x  =  (a + b)y  =  a - (a+b)x    {using x + y == 1},
         * ------ using the numerically best version : */
        lambda = isFinite(a + b) ? ((a > b) ? (a + b) * y - b : a - (a + b) * x) : a*y - b*x;
        do_swap = (lambda < 0.);
        if (do_swap) {
            lambda = -lambda;
            mixin (SET_0_swap());
        } else {
            mixin (SET_0_noswap());
        }
        
        //R_ifDEBUG_printf("  L30:  both  a, b > 1; |lambda| = %#g, do_swap = %d\n", lambda, do_swap);
        
        if (b0 < 40.) {
            //R_ifDEBUG_printf("  b0 < 40;");
            if (b0 * x0 <= 0.7 || (log_p && lambda > 650.)) // << added 2010-03; svn r51327
                goto L_w_bpser;
            else
                goto L140;
        }
        else if (a0 > b0) { /* ----  a0 > b0 >= 40  ---- */
            //R_ifDEBUG_printf("  a0 > b0 >= 40;");
            if (b0 <= 100. || lambda > b0 * 0.03)
                goto L_bfrac;
        
        } else if (a0 <= 100.) {
            //R_ifDEBUG_printf("  a0 <= 100; a0 <= b0 >= 40;");
            goto L_bfrac;
        }
        else if (lambda > a0 * 0.03) {
            //R_ifDEBUG_printf("  b0 >= a0 > 100; lambda > a0 * 0.03 ");
            goto L_bfrac;
        }
        
        /* else if none of the above    L180: */
        *w = basym!T(a0, b0, lambda, eps * 100., log_p);
        *w1 = log_p ? R_Log1_Exp!T(*w) : 0.5 - *w + 0.5;
        //R_ifDEBUG_printf("  b0 >= a0 > 100; lambda <= a0 * 0.03: *w:= basym(*) =%.15g\n", *w);
        goto L_end;
        
    } /* else: a, b > 1 */

/*            EVALUATION OF THE APPROPRIATE ALGORITHM */

L_w_bpser: // was L100
    *w = bpser!T(a0, b0, x0, eps, log_p);
    *w1 = log_p ? R_Log1_Exp!T(*w) : 0.5 - *w + 0.5;
    //R_ifDEBUG_printf(" L_w_bpser: *w := bpser(*) = %.15g\n", *w);
    goto L_end;

L_w1_bpser:  // was L110
    *w1 = bpser!T(b0, a0, y0, eps, log_p);
    *w  = log_p ? R_Log1_Exp!T(*w1) : 0.5 - *w1 + 0.5;
    //R_ifDEBUG_printf(" L_w1_bpser: *w1 := bpser(*) = %.15g\n", *w1);
    goto L_end;

L_bfrac:
    *w = bfrac!T(a0, b0, x0, y0, lambda, eps * 15., log_p);
    *w1 = log_p ? R_Log1_Exp!T(*w) : 0.5 - *w + 0.5;
    //R_ifDEBUG_printf(" L_bfrac: *w := bfrac(*) = %g\n", *w);
    goto L_end;

L140:
    /* b0 := fractional_part( b0 )  in (0, 1]  */
    n = cast(int) b0;
    b0 -= n;
    if (b0 == 0.) {
        --n; b0 = 1.;
    }

    *w = bup!T(b0, a0, y0, x0, n, eps, 0);

    if(*w < DBL_MIN && log_p) { /* do not believe it; try bpser() : */
        //R_ifDEBUG_printf(" L140: bup(b0=%g,..)=%.15g < DBL_MIN - not used; ", b0, *w);
        /*revert: */ b0 += n;
        /* which is only valid if b0 <= 1 || b0*x0 <= 0.7 */
        goto L_w_bpser;
    }
    //R_ifDEBUG_printf(" L140: *w := bup(b0=%g,..) = %.15g; ", b0, *w);
    if (x0 <= 0.7) {
        /* log_p :  TODO:  w = bup(.) + bpser(.)  -- not so easy to use log-scale */
        *w += bpser!T(a0, b0, x0, eps, /* log_p = */ 0);
        //R_ifDEBUG_printf(" x0 <= 0.7: *w := *w + bpser(*) = %.15g\n", *w);
        goto L_end_from_w;
    }
    /* L150: */
    if (a0 <= 15.) {
        n = 20;
        *w += bup!T(a0, b0, x0, y0, n, eps, 0);
        //R_ifDEBUG_printf("\n a0 <= 15: *w := *w + bup(*) = %.15g;", *w);
        a0 += n;
    }
    //R_ifDEBUG_printf(" bgrat(*, w=%.15g) ", *w);
    bgrat!T(a0, b0, x0, y0, w, 15*eps, &ierr1, 0);
    if(ierr1) *ierr = 10 + ierr1;
    //#ifdef DEBUG_bratio
    //    REprintf("==> new w=%.15g", *w);
    //    if(ierr1) REprintf(" Error(code=%d)\n", ierr1) ; else REprintf("\n");
    //#endif
    goto L_end_from_w;


/* TERMINATION OF THE PROCEDURE */

L200:
    if (a == 0.) { *ierr = 6;    return; }
    // else:
L201: *w  = R_D__0; *w1 = R_D__1; return;

L210:
    if (b == 0.) { *ierr = 7;    return; }
    // else:
L211: *w  = R_D__1; *w1 = R_D__0; return;

L_end_from_w:
    if(log_p) {
        *w1 = log1p(-*w);
        *w  = log(*w);
    } else {
        *w1 = 0.5 - *w + 0.5;
    }
    goto L_end;

L_end_from_w1:
    if(log_p) {
        *w  = log1p(-*w1);
        *w1 = log(*w1);
    } else {
        *w = 0.5 - *w1 + 0.5;
    }
    goto L_end;

L_end_from_w1_log:
    // *w1 = log(w1) already; w = 1 - w1  ==> log(w) = log(1 - w1) = log(1 - exp(*w1))
    if(log_p) {
        *w = R_Log1_Exp!T(*w1);
    } else {
        *w  = /* 1 - exp(*w1) */ -expm1(*w1);
        *w1 = exp(*w1);
    }
    goto L_end;


L_end:
    if (do_swap) { /* swap */
        T t = *w; *w = *w1; *w1 = t;
    }
    return;

} /* bratio */

