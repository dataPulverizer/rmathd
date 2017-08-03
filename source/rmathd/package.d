module rmathd;

public import rmathd.common: set_seed, get_seed, gammafn, lgammafn, lgammafn_sign, dpois_raw, sinpi, cospi, tanpi;
public import rmathd.beta: beta, dbeta, pbeta, qbeta, rbeta, lbeta;
public import rmathd.binomial: dbinom, pbinom, qbinom, rbinom;
public import rmathd.cauchy: dcauchy, pcauchy, qcauchy, rcauchy;
public import rmathd.chisq: dchisq, pchisq, qchisq, rchisq;
public import rmathd.choose: choose, lchoose;
public import rmathd.exponential: dexp, pexp, qexp, rexp;
public import rmathd.f: df, pf, qf, rf;
public import rmathd.gamma: dgamma, pgamma, qgamma, rgamma;
public import rmathd.geom: dgeom, pgeom, qgeom, rgeom;
public import rmathd.hyper: dhyper, phyper, qhyper, rhyper;
public import rmathd.lnorm: dlnorm, plnorm, qlnorm, rlnorm;
public import rmathd.logistic: dlogis, plogis, qlogis, rlogis;
public import rmathd.nbeta: dnbeta, pnbeta, qnbeta, rnbeta;
public import rmathd.nbinomial: dnbinom, pnbinom, qnbinom, rnbinom, dnbinom_mu, pnbinom_mu, qnbinom_mu, rnbinom_mu;
public import rmathd.nchisq: dnchisq, pnchisq, qnchisq, rnchisq;
public import rmathd.nf: dnf, pnf, qnf, rnf;
public import rmathd.normal: dnorm, pnorm, qnorm, rnorm, pnorm_both;
public import rmathd.poisson: dpois, ppois, qpois, rpois;
public import rmathd.t: dt, pt, qt, rt;
public import rmathd.uniform: dunif, punif, qunif, runif;
public import rmathd.weibull: dweibull, pweibull, qweibull, rweibull;

void demo()
{
	import std.stdio: write, writeln;
	/* Gamma */
	writeln("dgamma: ", dgamma(1., 1., 1., 0));
	writeln("pgamma: ", pgamma(1., 1., 1., 1, 0));
	writeln("qgamma: ", qgamma(0.5, 1., 1., 1, 0));
	writeln("rgamma: ", rgamma(1., 1.), ", rgamma: ", rgamma(1., 1.) , ", rgamma: ", rgamma(1., 1.));
	/* Normal */
	writeln("dnorm: ", "0: ", dnorm(0., 0., 1., 0), ", 1.96: ", dnorm(1.96, 0., 1., 0), 
            ", 1.644854: ", dnorm(1.644854, 0., 1., 0));
    writeln("pnorm: ", "z = 1.96: ", pnorm(1.96, 0, 1, 0, 0),
        ", z = 1.644854: ", pnorm(1.644854, 0, 1, 0, 0));
    writeln("qnorm: ", "p = 0.975: ", qnorm(0.975, 0, 1, 0, 0),
        ", p = 0.95: ", qnorm(0.95, 0, 1, 0, 0));
    writeln("rnorm(0., 1.): ", rnorm(0., 1.), "; rnorm(0., 1.): ", rnorm(0., 1.),
        "; rnorm(0., 1.): ", rnorm(0., 1.), "; rnorm(0., 1.): ", rnorm(0., 1.));
}