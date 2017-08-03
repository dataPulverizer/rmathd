module nbinomial;

import common;
import beta;
import poisson;
import toms708;
import normal;
import gamma;

/* 
** 
** dmd nbinomial.d common.d beta.d poisson.d toms708 normal.d gamma.d && ./nbinomial
*/


T dnbinom(T)(T x, T size, T prob, int give_log)
{
    T ans, p;
    mixin R_D__0!give_log;
    mixin R_D__1!give_log;
    
    if (isNaN(x) || isNaN(size) || isNaN(prob))
        return x + size + prob;

    if (prob <= 0 || prob > 1 || size < 0)
    	return T.nan;
    mixin (R_D_nonint_check!(x));
    if (x < 0 || !isFinite(x))
    	return R_D__0;
    /* limiting case as size approaches zero is point mass at zero */
    if (x == 0 && size == 0)
    	return R_D__1;
    x = nearbyint(x);
    if(!isFinite(size)) size = DBL_MAX;

    ans = dbinom_raw!T(size, x + size, prob, 1 - prob, give_log);
    p = (cast(T)size)/(size + x);
    return((give_log) ? log(p) + ans : p * ans);
}


T dnbinom_mu(T)(T x, T size, T mu, int give_log)
{
    /* originally, just set  prob :=  size / (size + mu)  and called dbinom_raw(),
     * but that suffers from cancellation when   mu << size  */

    mixin R_D__0!give_log;
    mixin R_D__1!give_log;

    if (isNaN(x) || isNaN(size) || isNaN(mu))
        return x + size + mu;

    if (mu < 0 || size < 0)
        return T.nan;
    mixin (R_D_nonint_check!(x));
    if (x < 0 || !isFinite(x))
        return R_D__0;

    /* limiting case as size approaches zero is point mass at zero,
     * even if mu is kept constant. limit distribution does not
     * have mean mu, though.
     */
    if (x == 0 && size == 0)
        return R_D__1;
    x = nearbyint(x);
    if(!isFinite(size)) // limit case: Poisson
        return(dpois_raw!T(x, mu, give_log));

    if(x == 0)/* be accurate, both for n << mu, and n >> mu :*/
        return R_D_exp!T(size * (size < mu ? log(size/(size + mu)) : log1p(-mu/(size + mu))), give_log);
    if(x < 1e-10 * size) { /* don't use dbinom_raw() but MM's formula: */
        /* FIXME --- 1e-8 shows problem; rather use algdiv() from ./toms708.c */
        T p = (size < mu ? log(size/(1 + size/mu)) : log(mu / (1 + mu/size)));
        return R_D_exp!T(x * p - mu - lgamma!T(x + 1) +
                   log1p(x*(x - 1)/(2*size)), give_log);
    } else {
        /* no unnecessary cancellation inside dbinom_raw, when
         * x_ = size and n_ = x+size are so close that n_ - x_ loses accuracy */
        T p = (cast(T)size)/(size + x),
            ans = dbinom_raw!T(size, x + size, size/(size + mu), mu/(size + mu), give_log);
        return((give_log) ? log(p) + ans : p * ans);
    }
}


T pnbinom(T)(T x, T size, T prob, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(size) || isNaN(prob))
        return x + size + prob;
    if(!isFinite(size) || !isFinite(prob))
        return T.nan;

    if (size < 0 || prob <= 0 || prob > 1)
        return T.nan;

    /* limiting case: point mass at zero */
    if (size == 0)
        return (x >= 0) ? R_DT_1!T(lower_tail, log_p): R_DT_0!T(lower_tail, log_p);

    if (x < 0)
        return R_DT_0!T(lower_tail, log_p);
    if (!isFinite(x))
        return R_DT_1!T(lower_tail, log_p);
    x = floor(x + 1e-7);
    return pbeta!T(prob, size, x + 1, lower_tail, log_p);
}


T pnbinom_mu(T)(T x, T size, T mu, int lower_tail, int log_p)
{
    if (isNaN(x) || isNaN(size) || isNaN(mu))
        return x + size + mu;
    if(!isFinite(mu))
        return T.nan;
    
    if (size < 0 || mu < 0)
        return T.nan;

    /* limiting case: point mass at zero */
    if (size == 0)
        return (x >= 0) ? R_DT_1!T(lower_tail, log_p) : R_DT_0!T(lower_tail, log_p);

    if (x < 0)
        return R_DT_0!T(lower_tail, log_p);
    if (!isFinite(x))
        return R_DT_1!T(lower_tail, log_p);
    if (!isFinite(size)) // limit case: Poisson
        return(ppois!T(x, mu, lower_tail, log_p));

    x = floor(x + 1e-7);
    /* return
     * pbeta(pr, size, x + 1, lower_tail, log_p);  pr = size/(size + mu), 1-pr = mu/(size+mu)
     *
     *= pbeta_raw(pr, size, x + 1, lower_tail, log_p)
     *            x.  pin   qin
     *=  bratio (pin,  qin, x., 1-x., &w, &wc, &ierr, log_p),  and return w or wc ..
     *=  bratio (size, x+1, pr, 1-pr, &w, &wc, &ierr, log_p) */
    {
    int ierr;
    T w, wc;
    bratio!T(size, x + 1, size/(size + mu), mu/(size + mu), &w, &wc, &ierr, log_p);
    if(ierr){
        //MATHLIB_WARNING(_("pnbinom_mu() -> bratio() gave error code %d"), ierr);
        doNothing();
    }
    return lower_tail ? w : wc;
    }
}


static T do_search(T)(T y, T *z, T p, T n, T pr, T incr)
{
    if(*z >= p) {   /* search to the left */
        for(;;) {
            if(y == 0 || (*z = pnbinom!T(y - incr, n, pr, /*l._t.*/1, /*log_p*/0)) < p)
                return y;
            y = fmax2!T(0, y - incr);
        }
    } else {      /* search to the right */
        for(;;) {
            y = y + incr;
            if((*z = pnbinom!T(y, n, pr, /*l._t.*/1, /*log_p*/0)) >= p)
                return y;
        }
    }
}


T qnbinom(T)(T p, T size, T prob, int lower_tail, int log_p)
{
    T P, Q, mu, sigma, gamma, z, y;

    if (isNaN(p) || isNaN(size) || isNaN(prob))
    return p + size + prob;

    /* this happens if specified via mu, size, since
       prob == size/(size+mu)
    */
    if (prob == 0 && size == 0)
        return 0;

    if (prob <= 0 || prob > 1 || size < 0)
        return T.nan;

    if (prob == 1 || size == 0)
        return 0;

    immutable(T) INF = T.infinity;
    mixin (R_Q_P01_boundaries!(p, 0, INF));

    Q = 1.0 / prob;
    P = (1.0 - prob) * Q;
    mu = size * P;
    sigma = sqrt(size * P * Q);
    gamma = (Q + P)/sigma;

    mixin R_DT_qIv!p;
    /* Note : "same" code in qpois.c, qbinom.c, qnbinom.c --
     * FIXME: This is far from optimal [cancellation for p ~= 1, etc]: */
    if(!lower_tail || log_p) {
    p = R_DT_qIv; /* need check again (cancellation!): */
    if (p == R_DT_0!T(lower_tail, log_p))
        return 0;
    if (p == R_DT_1!T(lower_tail, log_p))
        return T.infinity;
    }
    /* temporary hack --- FIXME --- */
    if (p + 1.01*DBL_EPSILON >= 1.)
        return T.infinity;

    /* y := approx.value (Cornish-Fisher expansion) :  */
    z = qnorm!T(p, 0., 1., /*lower_tail*/1, /*log_p*/0);
    y = nearbyint(mu + sigma * (z + gamma * (z*z - 1) / 6));

    z = pnbinom!T(y, size, prob, /*lower_tail*/1, /*log_p*/0);

    /* fuzz to ensure left continuity: */
    p *= 1 - 64*DBL_EPSILON;

    /* If the C-F value is not too large a simple search is OK */
    if(y < 1e5)
        return do_search!T(y, &z, p, size, prob, 1);
    /* Otherwise be a bit cleverer in the search */
    {
    T incr = floor(y * 0.001), oldincr;
    do {
        oldincr = incr;
        y = do_search!T(y, &z, p, size, prob, incr);
        incr = fmax2!T(1, floor(incr/100));
    } while(oldincr > 1 && incr > y*1e-15);
    return y;
    }
}

T qnbinom_mu(T)(T p, T size, T mu, int lower_tail, int log_p)
{
    if (size == T.infinity) // limit case: Poisson
        return(qpois!T(p, mu, lower_tail, log_p));
    /* FIXME!  Implement properly!! (not losing accuracy for very large size (prob ~= 1)*/
    return qnbinom!T(p, size, /* prob = */ size/(size + mu), lower_tail, log_p);
}


T rnbinom(T)(T size, T prob)
{
    if(!isFinite(prob) || isNaN(size) || size <= 0 || prob <= 0 || prob > 1)
    /* prob = 1 is ok, PR#1218 */
        return T.nan;
    if(!isFinite(size)) size = DBL_MAX / 2.; // '/2' to prevent rgamma() returning Inf
    return (prob == 1) ? 0 : rpois(rgamma!T(size, (1 - prob) / prob));
}

T rnbinom_mu(T)(T size, T mu)
{
    if(!isFinite(mu) || isNaN(size) || size <= 0 || mu < 0)
        return T.nan;
    if(!isFinite(size)) size = DBL_MAX / 2.;
    return (mu == 0) ? 0 : rpois!T(rgamma!T(size, mu / size));
}


void test_nbinomial()
{
    import std.stdio: writeln;
	writeln("dnbinom: ", dnbinom(2., 8., 0.7, 0));
    writeln("dnbinom_mu: ", dnbinom_mu(2., 8., 0.7, 0));
    writeln("pnbinom: ", pnbinom(2., 8., 0.7, 1, 0));
    writeln("pnbinom_mu: ", pnbinom_mu(2., 8., 0.7, 1, 0));
    writeln("qnbinom: ", qnbinom(.8, 8., 0.7, 1, 0));
    writeln("qnbinom_mu: ", qnbinom_mu(.8, 8., 0.7, 1, 0));
    writeln("rnbinom: ", rnbinom(8., 0.2), ", rnbinom: ", rnbinom(8., 0.2), ", rnbinom: ", rnbinom(8., 0.2));
    writeln("rnbinom_mu: ", rnbinom_mu(8., 0.7), ", rnbinom_mu: ", rnbinom_mu(8., 0.7), ", rnbinom_mu: ", rnbinom_mu(8., 0.7));
}

