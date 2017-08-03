module normal;

import common;
import uniform;

/*
** dmd normal.d uniform.d common.d && ./normal
**
** dmd normal.d uniform.d common.d && ./normal && rm normal.o normal
*/

T dnorm(T)(T x, T mu, T sigma, int log_p)
{
    if (isNaN(x) || isNaN(mu) || isNaN(sigma))
        return x + mu + sigma;

    mixin R_D__0!log_p;
    if(!isFinite(sigma))
        return R_D__0;
    if(!isFinite(x) && mu == x) return T.nan;/* x-mu is NaN */
    if (sigma <= 0) {
        if (sigma < 0)
            return T.nan;
        /* sigma == 0 */
        return (x == mu) ? T.infinity : R_D__0;
    }
    x = (x - mu) / sigma;

    if(!isFinite(x))
        return R_D__0;

    x = fabs (x);
    if (x >= 2 * sqrt(T.max))
        return R_D__0;
    if (log_p)
        return -(M_LN_SQRT_2PI + 0.5 * x * x + log(sigma));
    // more accurate, less fast :
    if (x < 5)
        return M_1_SQRT_2PI * exp(-0.5 * x * x) / sigma;

    if (x > sqrt(-2*M_LN2*(MIN_EXP!T + 1 - MANT_DIG!T)))
        return 0.;

    T x1 = ldexp( nearbyint(ldexp(x, 16)), -16);
    T x2 = x - x1;
    return M_1_SQRT_2PI / sigma * (exp(-0.5 * x1 * x1) * exp( (-0.5 * x2 - x1) * x2 ) );
}


enum SIXTEN = 16;

template swap_tail()
{
    enum swap_tail = `if (x > 0.) {
        temp = cum;
        if(lower)
            cum = ccum;
        ccum = temp;
    }`;
}

template do_del(alias X)
{
    enum do_del = `xsq = trunc(` ~ X.stringof ~ ` * SIXTEN) / SIXTEN;
    del = (` ~ X.stringof ~ ` - xsq) * (` ~ X.stringof ~ ` + xsq);
    if(log_p) {
        cum = (-xsq * xsq * 0.5) + (-del * 0.5) + log(temp);
        if((lower && x > 0.) || (upper && x <= 0.))
          ccum = log1p(-exp(-xsq * xsq * 0.5) * exp(-del * 0.5) * temp);
    }                               
    else {
        cum = exp(-xsq * xsq * 0.5) * exp(-del * 0.5) * temp;
        ccum = 1.0 - cum;
    }`;
}

void pnorm_both(T)(T x, ref T cum, ref T ccum, int i_tail, in int log_p)
{
    const static T[5] a = [
    2.2352520354606839287,
    161.02823106855587881,
    1067.6894854603709582,
    18154.981253343561249,
    0.065682337918207449113
    ];
    const static T[4] b = [
    47.20258190468824187,
    976.09855173777669322,
    10260.932208618978205,
    45507.789335026729956
    ];
    const static T[9] c = [
        0.39894151208813466764,
        8.8831497943883759412,
        93.506656132177855979,
        597.27027639480026226,
        2494.5375852903726711,
        6848.1904505362823326,
        11602.651437647350124,
        9842.7148383839780218,
        1.0765576773720192317e-8
    ];
    const static T[8] d = [
        22.266688044328115691,
        235.38790178262499861,
        1519.377599407554805,
        6485.558298266760755,
        18615.571640885098091,
        34900.952721145977266,
        38912.003286093271411,
        19685.429676859990727
        ];
    const static T[6] p = [
        0.21589853405795699,
        0.1274011611602473639,
        0.022235277870649807,
        0.001421619193227893466,
        2.9112874951168792e-5,
        0.02307344176494017303
        ];
    const static T[5] q = [
        1.28426009614491121,
        0.468238212480865118,
        0.0659881378689285515,
        0.00378239633202758244,
        7.29751555083966205e-5
        ];

    T xden, xnum, temp, del, eps, xsq, y;
//#ifdef NO_DENORMS
    T min = MIN!T;
    int i, lower, upper;

    if(isNaN(x)){
        cum = ccum = x;
        return;
    }

    /* Consider changing these : */
    eps = EPSILON!T * 0.5;

    /* i_tail in {0,1,2} =^= {lower, upper, both} */
    lower = i_tail != 1;
    upper = i_tail != 0;

    mixin R_D__0!log_p;
    mixin R_D__1!log_p;
    y = fabs(x);
    if (y <= 0.67448975) { /* qnorm(3/4) = .6744.... -- earlier had 0.66291 */
        if (y > eps) {
            xsq = x * x;
            xnum = a[4] * xsq;
            xden = xsq;
            for (i = 0; i < 3; ++i) {
            xnum = (xnum + a[i]) * xsq;
            xden = (xden + b[i]) * xsq;
            }
        } else xnum = xden = 0.0;
        
        temp = x * (xnum + a[3]) / (xden + b[3]);
        if(lower)
            cum = 0.5 + temp;
        if(upper)
            ccum = 0.5 - temp;
        if(log_p) {
            if(lower)
                cum = log(cum);
            if(upper)
                ccum = log(ccum);
        }
    }
    else if (y <= M_SQRT_32) {

    /* Evaluate pnorm for 0.674.. = qnorm(3/4) < |x| <= sqrt(32) ~= 5.657 */

    xnum = c[8] * y;
    xden = y;
    for (i = 0; i < 7; ++i) {
        xnum = (xnum + c[i]) * y;
        xden = (xden + d[i]) * y;
    }
    temp = (xnum + c[7]) / (xden + d[7]);
        mixin (do_del!y);
        mixin swap_tail;
    }

/* else   |x| > sqrt(32) = 5.657 :
 * the next two case differentiations were really for lower=T, log=F
 * Particularly  *not*  for  log_p !

 * Cody had (-37.5193 < x  &&  x < 8.2924) ; R originally had y < 50
 *
 * Note that we do want symmetry(0), lower/upper -> hence use y
 */
    else if((log_p && y < 1e170) 
        || (lower && -37.5193 < x  &&  x < 8.2924)
        || (upper && -8.2924  < x  &&  x < 37.5193)
    ) {

    /* Evaluate pnorm for x in (-37.5, -5.657) union (5.657, 37.5) */
    xsq = 1.0 / (x * x); /* (1./x)*(1./x) might be better */
    xnum = p[5] * xsq;
    xden = xsq;
    for (i = 0; i < 4; ++i) {
        xnum = (xnum + p[i]) * xsq;
        xden = (xden + q[i]) * xsq;
    }
    temp = xsq * (xnum + p[4]) / (xden + q[4]);
    temp = (M_1_SQRT_2PI - temp) / y;

    mixin (do_del!x);
    mixin swap_tail;
    } else { /* large x such that probs are 0 or 1 */
        if(x > 0) {
            cum = R_D__1;
            ccum = R_D__0;
        } else {
                cum = R_D__0;
                ccum = R_D__1;
            }
    }


//#ifdef NO_DENORMS
    /* do not return "denormalized" -- we do in R */
    if(log_p) {
        if(cum > -min)
            cum = -0.;
        if(ccum > -min)
            ccum = -0.;
    }
    else {
        if(cum < min)
            cum = 0.;
        if(ccum < min)
            ccum = 0.;
    }

    return;
}

T pnorm(T)(T x, T mu, T sigma, int lower_tail, int log_p)
{
    T p, cp;

    /* Note: The structure of these checks has been carefully thought through.
     * For example, if x == mu and sigma == 0, we get the correct answer 1.
     */
    if(isNaN(x) || isNaN(mu) || isNaN(sigma))
        return x + mu + sigma;

    if(!x.isFinite && mu == x)
        return T.nan;

    if (sigma <= 0) {
        if(sigma < 0)
            return T.nan;
        /* sigma = 0 : */
        return (x < mu) ? R_DT_0!T(lower_tail, log_p) : R_DT_1!T(lower_tail, log_p);
    }
    p = (x - mu) / sigma;
    if(!p.isFinite)
        return (x < mu) ? R_DT_0!T(lower_tail, log_p) : R_DT_1!T(lower_tail, log_p);
    x = p;
    pnorm_both(x, p, cp, (lower_tail ? 0 : 1), log_p);
    return(lower_tail ? p : cp);
}

/*template R_Q_P01_boundaries(alias p, alias LEFT, alias RIGHT)
{
    enum R_Q_P01_boundaries = `if (log_p) {
        if(p > 0)
            return T.nan;
        if(p == 0)
            return lower_tail ? ` ~ RIGHT.stringof ~ ` : ` ~ LEFT.stringof ~ `;
        if(p == -T.infinity)
            return lower_tail ? ` ~ LEFT.stringof ~ ` : ` ~ RIGHT.stringof ~ `;
    } else {
        if(p < 0 || p > 1)
            return T.nan;
        if(p == 0)
            return lower_tail ? ` ~ LEFT.stringof ~` : ` ~ RIGHT.stringof ~ `;
        if(p == 1)
            return lower_tail ? ` ~ RIGHT.stringof ~ ` : ` ~ LEFT.stringof ~ `;
    }`;
}*/


T qnorm(T)(T p, T mu, T sigma, int lower_tail, int log_p)
{
    T p_, q, r, val;


    /* Convert this code snippet back to a mixin noe that you know how! */
    if (isNaN(p) || isNaN(mu) || isNaN(sigma))
        return p + mu + sigma;

    immutable(T) PINF = T.infinity;
    immutable(T) NINF = -T.infinity;
    mixin (R_Q_P01_boundaries!(p, NINF, PINF)());

    if(sigma  < 0)
        return T.nan;
    if(sigma == 0)
        return mu;

    mixin R_DT_qIv!p;
    p_ = R_DT_qIv;/* real lower_tail prob. p */
    q = p_ - 0.5;

/*-- use AS 241 --- */
/* double ppnd16_(double *p, long *ifault)*/
/*      ALGORITHM AS241  APPL. STATIST. (1988) VOL. 37, NO. 3

        Produces the normal deviate Z corresponding to a given lower
        tail area of P; Z is accurate to about 1 part in 10**16.

        (original fortran code used PARAMETER(..) for the coefficients
         and provided hash codes for checking them...)
*/
    if (fabs(q) <= .425) {/* 0.075 <= p <= 0.925 */
        r = .180625 - q * q;
    val =
            q * (((((((r * 2509.0809287301226727 +
                       33430.575583588128105) * r + 67265.770927008700853) * r +
                     45921.953931549871457) * r + 13731.693765509461125) * r +
                   1971.5909503065514427) * r + 133.14166789178437745) * r +
                 3.387132872796366608)
            / (((((((r * 5226.495278852854561 +
                     28729.085735721942674) * r + 39307.89580009271061) * r +
                   21213.794301586595867) * r + 5394.1960214247511077) * r +
                 687.1870074920579083) * r + 42.313330701600911252) * r + 1.);
    }
    else { /* closer than 0.075 from {0,1} boundary */

    /* r = min(p, 1-p) < 0.075 */
    mixin R_DT_CIv!p;
    if (q > 0)
        r = R_DT_CIv;/* 1-p */
    else
        r = p_;/* = R_DT_Iv(p) ^=  p */

    r = sqrt(- ((log_p &&
             ((lower_tail && q <= 0) || (!lower_tail && q > 0))) ?
            p : /* else */ log(r)));
        /* r = sqrt(-log(r))  <==>  min(p, 1-p) = exp( - r^2 ) */

        if (r <= 5.) { /* <==> min(p,1-p) >= exp(-25) ~= 1.3888e-11 */
            r += -1.6;
            val = (((((((r * 7.7454501427834140764e-4 +
                       .0227238449892691845833) * r + .24178072517745061177) *
                     r + 1.27045825245236838258) * r +
                    3.64784832476320460504) * r + 5.7694972214606914055) *
                  r + 4.6303378461565452959) * r +
                 1.42343711074968357734)
                / (((((((r *
                         1.05075007164441684324e-9 + 5.475938084995344946e-4) *
                        r + .0151986665636164571966) * r +
                       .14810397642748007459) * r + .68976733498510000455) *
                     r + 1.6763848301838038494) * r +
                    2.05319162663775882187) * r + 1.);
        }
        else { /* very close to  0 or 1 */
            r += -5.;
            val = (((((((r * 2.01033439929228813265e-7 +
                       2.71155556874348757815e-5) * r +
                      .0012426609473880784386) * r + .026532189526576123093) *
                    r + .29656057182850489123) * r +
                   1.7848265399172913358) * r + 5.4637849111641143699) *
                 r + 6.6579046435011037772)
                / (((((((r *
                         2.04426310338993978564e-15 + 1.4215117583164458887e-7)*
                        r + 1.8463183175100546818e-5) * r +
                       7.868691311456132591e-4) * r + .0148753612908506148525)
                     * r + .13692988092273580531) * r +
                    .59983220655588793769) * r + 1.);
        }

    if(q < 0.0)
        val = -val;
        /* return (q >= 0.)? r : -r ;*/
    }
    return mu + sigma * val;
}

double BM_norm_keep = 0.0;
N01type N01_kind = INVERSION;

alias void* function() DL_FUNC;
extern DL_FUNC User_norm_fun;

enum C1 = 0.398942280401433;
enum C2 = 0.180025191068563;

T norm_rand(T)()
{

    const static T[32] a =
    [
    0.0000000, 0.03917609, 0.07841241, 0.1177699,
    0.1573107, 0.19709910, 0.23720210, 0.2776904,
    0.3186394, 0.36012990, 0.40225010, 0.4450965,
    0.4887764, 0.53340970, 0.57913220, 0.6260990,
    0.6744898, 0.72451440, 0.77642180, 0.8305109,
    0.8871466, 0.94678180, 1.00999000, 1.0775160,
    1.1503490, 1.22985900, 1.31801100, 1.4177970,
    1.5341210, 1.67594000, 1.86273200, 2.1538750
    ];

    const static T[31] d =
    [
    0.0000000, 0.0000000, 0.0000000, 0.0000000,
    0.0000000, 0.2636843, 0.2425085, 0.2255674,
    0.2116342, 0.1999243, 0.1899108, 0.1812252,
    0.1736014, 0.1668419, 0.1607967, 0.1553497,
    0.1504094, 0.1459026, 0.1417700, 0.1379632,
    0.1344418, 0.1311722, 0.1281260, 0.1252791,
    0.1226109, 0.1201036, 0.1177417, 0.1155119,
    0.1134023, 0.1114027, 0.1095039
    ];

    const static T[31] t =
    [
    7.673828e-4, 0.002306870, 0.003860618, 0.005438454,
    0.007050699, 0.008708396, 0.010423570, 0.012209530,
    0.014081250, 0.016055790, 0.018152900, 0.020395730,
    0.022811770, 0.025434070, 0.028302960, 0.031468220,
    0.034992330, 0.038954830, 0.043458780, 0.048640350,
    0.054683340, 0.061842220, 0.070479830, 0.081131950,
    0.094624440, 0.112300100, 0.136498000, 0.171688600,
    0.227624100, 0.330498000, 0.584703100
    ];

    const static T[31] h =
    [
    0.03920617, 0.03932705, 0.03950999, 0.03975703,
    0.04007093, 0.04045533, 0.04091481, 0.04145507,
    0.04208311, 0.04280748, 0.04363863, 0.04458932,
    0.04567523, 0.04691571, 0.04833487, 0.04996298,
    0.05183859, 0.05401138, 0.05654656, 0.05953130,
    0.06308489, 0.06737503, 0.07264544, 0.07926471,
    0.08781922, 0.09930398, 0.11555990, 0.14043440,
    0.18361420, 0.27900160, 0.70104740
    ];

    /*----------- Constants and definitions for  Kinderman - Ramage --- */
    /*
     *  REFERENCE
     *
     *    Kinderman A. J. and Ramage J. G. (1976).
     *    Computer generation of normal random variables.
     *    JASA 71, 893-896.
     */

    const static T A =  2.216035867166471;

    T s, u1, w, y, u2, u3, aa, tt, theta, R;
    int i;


    template g(T)
    {
        auto g(T x)
        {
            return C1 * exp(-x*x/2.0) - C2*(A - x);
        }
    }

    switch(N01_kind) {

    case  AHRENS_DIETER: /* see Reference above */

    u1 = unif_rand!T();
    s = 0.0;
    if (u1 > 0.5)
        s = 1.0;
    u1 = u1 + u1 - s;
    u1 *= 32.0;
    i = cast(int) u1;
    if (i == 32)
        i = 31;
    if (i != 0) {
        u2 = u1 - i;
        aa = a[i - 1];
        while (u2 <= t[i - 1]) {
            u1 = unif_rand!T();
            w = u1 * (a[i] - aa);
            tt = (w * 0.5 + aa) * w;
            for(;;) {
                if (u2 > tt)
                    goto deliver;
                u1 = unif_rand!T();
                if (u2 < u1)
                    break;
                tt = u1;
                u2 = unif_rand!T();
            }
            u2 = unif_rand!T();
        }
        w = (u2 - t[i - 1]) * h[i - 1];
    } else {
        i = 6;
        aa = a[31];
        for(;;) {
        u1 = u1 + u1;
        if (u1 >= 1.0)
            break;
        aa = aa + d[i - 1];
        i = i + 1;
        }
        u1 = u1 - 1.0;
        for(;;) {
        w = u1 * d[i - 1];
        tt = (w * 0.5 + aa) * w;
        for(;;) {
            u2 = unif_rand!T();
            if (u2 > tt)
                goto jump;
            u1 = unif_rand!T();
            if (u2 < u1)
                break;
            tt = u1;
        }
        u1 = unif_rand!T();
        }
      jump:;
    }

      deliver:
    y = aa + w;
    return (s == 1.0) ? -y : y;

    /*-----------------------------------------------------------*/

    case BUGGY_KINDERMAN_RAMAGE: /* see Reference above */
    /* note: this has problems, but is retained for
     * reproducibility of older codes, with the same
     * numeric code */
    u1 = unif_rand!T();
    if(u1 < 0.884070402298758) {
        u2 = unif_rand!T();
        return A*(1.13113163544180 * u1 + u2 - 1);
    }

    if(u1 >= 0.973310954173898) { /* tail: */
        for(;;) {
        u2 = unif_rand!T();
        u3 = unif_rand!T();
        tt = (A*A - 2*log(u3));
        if( (u2*u2) < (A*A)/tt )
            return (u1 < 0.986655477086949) ? sqrt(tt) : -sqrt(tt);
        }
    }

    if(u1 >= 0.958720824790463) { /* region3: */
        for(;;) {
        u2 = unif_rand!T();
        u3 = unif_rand!T();
        tt = A - 0.630834801921960 * fmin2(u2, u3);
        if(fmax2(u2, u3) <= 0.755591531667601)
            return (u2 < u3) ? tt : -tt;
        if(0.034240503750111 * fabs(u2 - u3) <= g(tt))
            return (u2 < u3) ? tt : -tt;
        }
    }

    if(u1 >= 0.911312780288703) { /* region2: */
        for(;;) {
        u2 = unif_rand!T();
        u3 = unif_rand!T();
        tt = 0.479727404222441 + 1.105473661022070 * fmin2(u2, u3);
        if( fmax2(u2, u3) <= 0.872834976671790 )
            return (u2 < u3) ? tt : -tt;
        if( 0.049264496373128 * fabs(u2 - u3) <= g(tt) )
            return (u2 < u3) ? tt : -tt;
        }
    }

    /* ELSE  region1: */
    for(;;) {
        u2 = unif_rand!T();
        u3 = unif_rand!T();
        tt = 0.479727404222441 - 0.595507138015940 * fmin2(u2, u3);
        if(fmax2(u2, u3) <= 0.805577924423817)
            return (u2 < u3) ? tt : -tt;
    }
    case BOX_MULLER:
    if(BM_norm_keep != 0.0) { /* An exact test is intentional */
        s = BM_norm_keep;
        BM_norm_keep = 0.0;
        return s;
    } else {
        theta = 2 * M_PI * unif_rand!T();
        R = sqrt(-2 * log(unif_rand!T())) + 10 * MIN!T; /* ensure non-zero */
        BM_norm_keep = R * sin(theta);
        return R * cos(theta);
    }

    //case USER_NORM:
    //return cast(T)User_norm_fun();

    case INVERSION:
    enum BIG = 134217728; /* 2^27 */
    /* unif_rand() alone is not of high enough precision */
    u1 = unif_rand!T();
    u1 = cast(int)(BIG*u1) + unif_rand!T();
    return qnorm(u1/BIG, 0.0, 1.0, 1, 0);
    case KINDERMAN_RAMAGE: /* see Reference above */
    /* corrected version from Josef Leydold
     * */
    u1 = unif_rand!T();
    if(u1 < 0.884070402298758) {
        u2 = unif_rand!T();
        return A*(1.131131635444180*u1 + u2 - 1);
    }

    if(u1 >= 0.973310954173898) { /* tail: */
        for(;;) {
            u2 = unif_rand!T();
            u3 = unif_rand!T();
            tt = (A*A - 2*log(u3));
            if( u2*u2<(A*A)/tt )
                return (u1 < 0.986655477086949) ? sqrt(tt) : -sqrt(tt);
        }
    }

    if(u1 >= 0.958720824790463) { /* region3: */
        for(;;) {
        u2 = unif_rand!T();
        u3 = unif_rand!T();
        tt = A - 0.630834801921960*fmin2(u2, u3);
        if(fmax2(u2, u3) <= 0.755591531667601)
            return (u2 < u3) ? tt : -tt;
        if(0.034240503750111*fabs(u2 - u3) <= g(tt))
            return (u2 < u3) ? tt : -tt;
        }
    }

    if(u1 >= 0.911312780288703) { /* region2: */
        for(;;) {
            u2 = unif_rand!T();
            u3 = unif_rand!T();
            tt = 0.479727404222441+1.105473661022070*fmin2(u2, u3);
        if( fmax2(u2,u3)<=0.872834976671790 )
            return (u2 < u3) ? tt : -tt;
        if(0.049264496373128*fabs(u2 - u3)<=g(tt))
            return (u2 < u3) ? tt : -tt;
        }
    }

    /* ELSE  region1: */
    for(;;) {
        u2 = unif_rand!T();
        u3 = unif_rand!T();
        tt = 0.479727404222441-0.595507138015940*fmin2(u2, u3);
        if (tt < 0.) continue;
        if(fmax2(u2, u3) <= 0.805577924423817)
        return (u2 < u3) ? tt : -tt;
            if(0.053377549506886*fabs(u2 - u3) <= g(tt))
        return (u2 < u3) ? tt : -tt;
    }
    default:
    assert(0, "norm_rand(): invalid N01_kind: " ~ N01_kind.stringof);
        return 0.0;/*- -Wall */
    }/*switch*/
}


T rnorm(T)(T mu, T sigma)
{
    if (isNaN(mu) || !isFinite(sigma) || sigma < 0.)
        return T.nan;
    if (sigma == 0. || !isFinite(mu))
        return mu;
    else
        return mu + sigma * norm_rand!T();
}



void test_normal()
{
    import std.stdio: write, writeln;
    writeln("dnorm: ", "0: ", dnorm(0., 0., 1., 0), ", 1.96: ", dnorm(1.96, 0., 1., 0), 
            ", 1.644854: ", dnorm(1.644854, 0., 1., 0));
    writeln("pnorm: ", "z = 1.96: ", pnorm(1.96, 0, 1, 0, 0),
        ", z = 1.644854: ", pnorm(1.644854, 0, 1, 0, 0));
    writeln("qnorm: ", "p = 0.975: ", qnorm(0.975, 0, 1, 0, 0),
        ", p = 0.95: ", qnorm(0.95, 0, 1, 0, 0));
    writeln("rnorm(0., 1.): ", rnorm(0., 1.), "; rnorm(0., 1.): ", rnorm(0., 1.),
        "; rnorm(0., 1.): ", rnorm(0., 1.), "; rnorm(0., 1.): ", rnorm(0., 1.));
}





