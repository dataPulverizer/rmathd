module binomial;

import common;
import toms708;
import beta;
import normal;

/*
** dmd binomial.d common.d toms708.d beta.d normal.d && ./binomial
*/

T dbinom(T)(T x, T n, T p, int give_log)
{
    /* NaNs propagated correctly */
    if (isNaN(x) || isNaN(n) || isNaN(p))
    	return x + n + p;

    mixin R_D__0!give_log;

    if (p < 0 || p > 1 || R_D_negInonint!T(n))
	    return T.nan;
    mixin R_D_nonint_check!(x);
    if (x < 0 || !isFinite(x))
        return R_D__0;

    n = nearbyint(n);
    x = nearbyint(x);

    return dbinom_raw(x, n, p, 1 - p, give_log);
}

T pbinom(T)(T x, T n, T p, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(n) || isNaN(p))
        return x + n + p;
    if (!isFinite(n) || !isFinite(p))
        return T.nan;

    if(R_nonint!T(n)) {
        return T.nan;
    }
    n = nearbyint(n);
    if(n < 0 || p < 0 || p > 1)
        return T.nan;

    if (x < 0)
        return R_DT_0!T(lower_tail, log_p);
    x = floor(x + 1e-7);
    if (n <= x)
        return R_DT_1!T(lower_tail, log_p);
    return pbeta!T(p, x + 1, n - x, !lower_tail, log_p);
}

/* toms708.c */
static T do_search(T)(T y, T *z, T p, T n, T pr, T incr)
{
    if(*z >= p) {
            /* search to the left */
        //#ifdef DEBUG_qbinom
        //    REprintf("\tnew z=%7g >= p = %7g  --> search to left (y--) ..\n", z,p);
        //#endif
        for(;;) {
            T newz;
            if(y == 0 || (newz = pbinom!T(y - incr, n, pr, /*l._t.*/1, /*log_p*/0)) < p)
                return y;
            y = fmax2!T(0, y - incr);
            *z = newz;
        }
    } else {      /* search to the right */
        //#ifdef DEBUG_qbinom
        //    REprintf("\tnew z=%7g < p = %7g  --> search to right (y++) ..\n", z,p);
        //#endif
        for(;;) {
            y = fmin2!T(y + incr, n);
            if(y == n || (*z = pbinom!T(y, n, pr, /*l._t.*/1, /*log_p*/0)) >= p)
                return y;
        }
    }
}


T qbinom(T)(T p, T n, T pr, int lower_tail, int log_p)
{
    T q, mu, sigma, gamma, z, y;
    
    if (isNaN(p) || isNaN(n) || isNaN(pr))
        return p + n + pr;
    
    if(!isFinite(n) || !isFinite(pr))
        return T.nan;
    /* if log_p is true, p = -Inf is a legitimate value */
    if(!isFinite(p) && !log_p)
        return T.nan;

    if(n != floor(n + 0.5))
        return T.nan;
    if (pr < 0 || pr > 1 || n < 0)
        return T.nan;

    mixin (R_Q_P01_boundaries!(p, 0, n)());

    if (pr == 0. || n == 0)
        return 0.;

    q = 1 - pr;
    if(q == 0.) return n; /* covers the full range of the distribution */
    mu = n * pr;
    sigma = sqrt(n * pr * q);
    gamma = (q - pr) / sigma;

    //#ifdef DEBUG_qbinom
    //    REprintf("qbinom(p=%7g, n=%g, pr=%7g, l.t.=%d, log=%d): sigm=%g, gam=%g\n",
    //         p,n,pr, lower_tail, log_p, sigma, gamma);
    //#endif

    /* Note : "same" code in qpois.c, qbinom.c, qnbinom.c --
     * FIXME: This is far from optimal [cancellation for p ~= 1, etc]: */
     mixin R_DT_qIv!(p);
    if(!lower_tail || log_p) {
        p = R_DT_qIv; /* need check again (cancellation!): */
        if (p == 0.)
            return 0.;
        if (p == 1.)
            return n;
    }
    /* temporary hack --- FIXME --- */
    if (p + 1.01*DBL_EPSILON >= 1.) return n;

    /* y := approx.value (Cornish-Fisher expansion) :  */
    z = qnorm!T(p, 0., 1., /*lower_tail*/1, /*log_p*/0);
    y = floor(mu + sigma * (z + gamma * (z*z - 1) / 6) + 0.5);

    if(y > n) /* way off */ y = n;

    //#ifdef DEBUG_qbinom
    //    REprintf("  new (p,1-p)=(%7g,%7g), z=qnorm(..)=%7g, y=%5g\n", p, 1-p, z, y);
    //#endif
    z = pbinom!T(y, n, pr, /*lower_tail*/1, /*log_p*/0);

    /* fuzz to ensure left continuity: */
    p *= 1 - 64*DBL_EPSILON;

    if(n < 1e5) return do_search!T(y, &z, p, n, pr, 1);
    /* Otherwise be a bit cleverer in the search */
    {
    T incr = floor(n * 0.001), oldincr;
    do {
        oldincr = incr;
        y = do_search!T(y, &z, p, n, pr, incr);
        incr = fmax2!T(1, floor(incr/100));
    } while(oldincr > 1 && incr > n*1e-15);
    return y;
    }
}

T rbinom(T)(T nin, T pp)
{
    /* FIXME: These should become THREAD_specific globals : */

    static T c, fm, npq, p1, p2, p3, p4, qn;
    static T xl, xll, xlr, xm, xr;

    static T psave = -1.0;
    static int nsave = -1;
    static int m;

    T f, f1, f2, u, v, w, w2, x, x1, x2, z, z2;
    T p, q, np, g, r, al, alv, amaxp, ffm, ynorm;
    int i, ix, k, n;

    if (!isFinite(nin))
        return T.nan;
    r = nearbyint(nin);
    if (r != nin)
        return T.nan;
    if (!isFinite(pp) ||
    /* n=0, p=0, p=1 are not errors <TSL>*/
    r < 0 || pp < 0. || pp > 1.)
        return T.nan;

    if (r == 0 || pp == 0.) return 0;
    if (pp == 1.) return r;

    if (r >= INT_MAX)/* evade integer overflow,
            and r == INT_MAX gave only even values */
    return qbinom!T(unif_rand!T(), r, pp, /*lower_tail*/ 0, /*log_p*/ 0);
    /* else */
    n = cast(int) r;

    p = fmin2(pp, 1. - pp);
    q = 1. - p;
    np = n * p;
    r = p / q;
    g = r * (n + 1);

    /* Setup, perform only when parameters change [using static (globals): */

    /* FIXING: Want this thread safe
       -- use as little (thread globals) as possible
    */
    if (pp != psave || n != nsave) {
    psave = pp;
    nsave = n;
    if (np < 30.0) {
        /* inverse cdf logic for mean less than 30 */
        qn = R_pow_di!T(q, n);
        goto L_np_small;
    } else {
        ffm = np + p;
        m = cast(int) ffm;
        fm = m;
        npq = np*q;
        p1 = cast(int)(2.195 * sqrt(npq) - 4.6 * q) + 0.5;
        xm = fm + 0.5;
        xl = xm - p1;
        xr = xm + p1;
        c = 0.134 + 20.5 / (15.3 + fm);
        al = (ffm - xl) / (ffm - xl * p);
        xll = al * (1.0 + 0.5 * al);
        al = (xr - ffm) / (xr * q);
        xlr = al * (1.0 + 0.5 * al);
        p2 = p1 * (1.0 + c + c);
        p3 = p2 + c / xll;
        p4 = p3 + c / xlr;
    }
    } else if (n == nsave) {
    if (np < 30.0)
        goto L_np_small;
    }

    /*-------------------------- np = n*p >= 30 : ------------------- */
    for(;;) {
      u = unif_rand!T() * p4;
      v = unif_rand!T();
      /* triangular region */
      if (u <= p1) {
      ix = cast(int)(xm - p1 * v + u);
      goto finis;
      }
      /* parallelogram region */
      if (u <= p2) {
      x = xl + (u - p1) / c;
      v = v * c + 1.0 - fabs(xm - x) / p1;
      if (v > 1.0 || v <= 0.)
          continue;
      ix = cast(int) x;
      } else {
      if (u > p3) { /* right tail */
          ix = cast(int)(xr - log(v) / xlr);
          if (ix > n)
          continue;
          v = v * (u - p3) * xlr;
      } else {/* left tail */
          ix = cast(int)(xl + log(v) / xll);
          if (ix < 0)
          continue;
          v = v * (u - p2) * xll;
      }
      }
      /* determine appropriate way to perform accept/reject test */
      k = abs(ix - m);
      if (k <= 20 || k >= npq / 2 - 1) {
      /* explicit evaluation */
      f = 1.0;
      if (m < ix) {
          for (i = m + 1; i <= ix; i++)
          f *= (g / i - r);
      } else if (m != ix) {
          for (i = ix + 1; i <= m; i++)
          f /= (g / i - r);
      }
      if (v <= f)
          goto finis;
      } else {
      /* squeezing using upper and lower bounds on log(f(x)) */
      amaxp = (k / npq) * ((k * (k / 3. + 0.625) + 0.1666666666666) / npq + 0.5);
      ynorm = -k * k / (2.0 * npq);
      alv = log(v);
      if (alv < ynorm - amaxp)
          goto finis;
      if (alv <= ynorm + amaxp) {
          /* stirling's formula to machine accuracy */
          /* for the final acceptance/rejection test */
          x1 = ix + 1;
          f1 = fm + 1.0;
          z = n + 1 - fm;
          w = n - ix + 1.0;
          z2 = z * z;
          x2 = x1 * x1;
          f2 = f1 * f1;
          w2 = w * w;
          if (alv <= xm * log(f1 / x1) + (n - m + 0.5) * log(z / w) + (ix - m) * log(w * p / (x1 * q)) + (13860.0 - (462.0 - (132.0 - (99.0 - 140.0 / f2) / f2) / f2) / f2) / f1 / 166320.0 + (13860.0 - (462.0 - (132.0 - (99.0 - 140.0 / z2) / z2) / z2) / z2) / z / 166320.0 + (13860.0 - (462.0 - (132.0 - (99.0 - 140.0 / x2) / x2) / x2) / x2) / x1 / 166320.0 + (13860.0 - (462.0 - (132.0 - (99.0 - 140.0 / w2) / w2) / w2) / w2) / w / 166320.)
          goto finis;
      }
      }
  }

 L_np_small:
    /*---------------------- np = n*p < 30 : ------------------------- */

  for(;;) {
     ix = 0;
     f = qn;
     u = unif_rand!T();
     for(;;) {
     if (u < f)
         goto finis;
     if (ix > 110)
         break;
     u -= f;
     ix++;
     f *= (g / ix - r);
     }
  }
 finis:
    if (psave > 0.5)
     ix = n - ix;
  return cast(T)ix;
}



void test_binomial()
{
    import std.stdio: writeln;
    writeln("dbinom: ", dbinom(2., 4., .5, 0));
    writeln("pbinom: ", pbinom(2., 4., .5, 1, 0));
    writeln("qbinom: ", qbinom(.8, 4., .5, 1, 0));
    writeln("rbinom: ", rbinom(20, .3), ", rbinom: ", rbinom(20, .3), ", rbinom: ", rbinom(20, .3));
}
