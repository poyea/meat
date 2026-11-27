#import "../meat.typ": *

= Continuous alphabets

Quantities are in nats.
Densities are relative to the reference measure on the space.
On $RR$, the reference measure is the Lebesgue measure $lambda$.
There is no bracket notation for differential entropy.
Bracket notation can conflict with index syntax, for example `h[i]`.
In this chapter, $eta(t) := -t log t$ for $t > 0$ and $eta(0) := 0$.

== Differential entropy
#source("Meat.Continuous.DifferentialEntropy")

#definition(
  "Differential entropy",
  lean: ("Meat.measureDiffEntropy", "Meat.diffEntropy", "Meat.diffEntropy_def"),
)[
  Let $E$ be a measure space with reference measure $lambda$, and let $nu$ be a measure on $E$ with Radon-Nikodym derivative $f := d nu \/ d lambda$.
  The differential entropy of $nu$ is
  $ h(nu) := integral_E eta(f(x)) thin d lambda(x). $
  For $X : Omega -> E$ and a measure $mu$ on $Omega$, $h(X) := h(X_* mu)$.
]

Lean uses the Bochner integral.
If $eta compose f$ is not integrable, the Bochner integral gives the value $0$.

#lemma(
  "Entropy as an expectation",
  lean: ("Meat.measureDiffEntropy_eq_neg_integral_log", "Meat.integrable_negMulLog_rnDeriv_iff"),
)[
  Let $lambda$ and $nu$ be $sigma$-finite with $nu << lambda$, and let $f := d nu \/ d lambda$.
  Then
  $ h(nu) = -integral_E log f(x) thin d nu(x). $
  Also, $eta compose f$ is $lambda$-integrable if and only if $log compose f$ is $nu$-integrable.
][
  Since $nu << lambda$, Mathlib gives $integral_E f(x) g(x) thin d lambda(x) = integral_E g(x) thin d nu(x)$ for every $g$.
  It also gives that $f g$ is $lambda$-integrable if and only if $g$ is $nu$-integrable.
  Take $g := log compose f$ and use $f log f = -eta(f)$.
]

No integrability hypothesis is needed for the identity.
If one side is not integrable, neither is the other, and both Bochner integrals are $0$.

== Divergence for measures with densities
#source("Meat.Continuous.Divergence")

The Kullback-Leibler divergence of two measures does not depend on a reference measure:
$ D(nu || rho) = integral_E log (d nu) / (d rho) (x) thin d nu(x). $
Mathlib defines it for all measures as `InformationTheory.klDiv`, with values in $[0, infinity]$.
It is $infinity$ when $nu$ is not absolutely continuous with respect to $rho$, or when the log-likelihood ratio is not $nu$-integrable.
Mathlib also proves Gibbs' inequality and its equality case for this divergence.
So this file defines no new divergence.
It reuses Mathlib's divergence and links it to differential entropy.
Below, $D(nu || rho)$ is the real number obtained from Mathlib's divergence, with $infinity$ sent to $0$.
Since Mathlib's divergence is in $[0, infinity]$, $D(nu || rho) >= 0$ always.
The content of Gibbs' inequality is in Mathlib's formula for the finite case: for probability measures with $nu << rho$, $D(nu || rho)$ is the integral of the log-likelihood ratio.
The discrete divergence of the Shannon chapter is a different object, on finite alphabets only.

#theorem(
  "Divergence and differential entropy",
  lean: "Meat.toReal_klDiv_eq_neg_measureDiffEntropy_sub",
)[
  Let $lambda$ be $sigma$-finite, and let $nu$ and $rho$ be probability measures on $E$ with $nu << lambda$ and $nu << rho$.
  Let $f := d nu \/ d lambda$ and $g := d rho \/ d lambda$.
  Assume that $eta compose f$ is $lambda$-integrable and that $log compose g$ is $nu$-integrable.
  Then
  $ D(nu || rho) = -h(nu) - integral_E log g(x) thin d nu(x). $
][
  By the chain rule for Radon-Nikodym derivatives, $(d nu \/ d rho) dot g = f$ $lambda$-almost everywhere, so also $nu$-almost everywhere.
  Also $nu$-almost everywhere, $d nu \/ d rho in (0, infinity)$, $f > 0$ and $g < infinity$.
  Then $g != 0$, so $log (d nu \/ d rho) = log f - log g$ $nu$-almost everywhere.
  By the lemma on entropy as an expectation, $log compose f$ is $nu$-integrable.
  Since $nu(E) = rho(E) = 1$, Mathlib gives $D(nu || rho) = integral_E log (d nu \/ d rho) thin d nu$.
  Split the integral, and use $h(nu) = -integral_E log f thin d nu$.
]

#corollary(
  "Cross-entropy bound",
  lean: "Meat.measureDiffEntropy_le_neg_integral_log_rnDeriv",
)[
  Under the hypotheses of the theorem above,
  $ h(nu) <= -integral_E log g(x) thin d nu(x). $
][
  The left side of the theorem is $D(nu || rho) >= 0$.
]

== Gaussian variables and channels
#source("Meat.Continuous.Gaussian")

For $m in RR$ and $v >= 0$, $cal(N)(m, v)$ is the Gaussian measure with mean $m$ and variance $v$.
For $v > 0$, its density is
$ phi(x) := (2 pi v)^(-1 \/ 2) exp(-(x - m)^2 \/ (2 v)). $
For $v = 0$, Mathlib sets $phi := 0$, and $cal(N)(m, 0)$ is the point mass at $m$.

#lemma(
  "Gaussian log-density",
  lean: ("Meat.neg_log_gaussianPDFReal", "Meat.toReal_rnDeriv_gaussianReal"),
)[
  If $v > 0$, then for every $x in RR$,
  $ -log phi(x) = 1/2 log (2 pi v) + (x - m)^2 / (2 v). $
  For every $v >= 0$, $d cal(N)(m, v) \/ d lambda = phi$ $lambda$-almost everywhere.
][
  The logarithm of $(2 pi v)^(-1 \/ 2) exp(t)$ is $-1/2 log (2 pi v) + t$.
  The second claim is Mathlib's formula for the Radon-Nikodym derivative of $cal(N)(m, v)$.
]

#lemma(
  "Gaussian cross-entropy",
  lean: ("Meat.integrable_log_rnDeriv_gaussianReal", "Meat.neg_integral_log_rnDeriv_gaussianReal"),
)[
  Let $v > 0$ and let $g := d cal(N)(m, v) \/ d lambda$.
  Let $nu$ be a finite measure on $RR$ with $nu << lambda$ such that $x |-> (x - m)^2$ is $nu$-integrable.
  Then $log compose g$ is $nu$-integrable.
  If $nu$ is a probability measure, then
  $ -integral log g(x) thin d nu(x) = 1/2 log (2 pi v) + (integral (x - m)^2 thin d nu(x)) / (2 v). $
][
  Since $nu << lambda$, $g = phi$ $nu$-almost everywhere.
  By the lemma above, $log g(x) = -(1/2 log (2 pi v) + (x - m)^2 \/ (2 v))$ for $nu$-almost every $x$.
  This is a constant plus a multiple of an integrable function, and $nu$ is finite.
  Integrate, using $nu(RR) = 1$.
]

#theorem("Entropy of a Gaussian", lean: "Meat.measureDiffEntropy_gaussianReal")[][
  The measure $cal(N)(m, v)$ is absolutely continuous with respect to $lambda$.
  Let $g := d cal(N)(m, v) \/ d lambda$.
  By the lemma on entropy as an expectation, $h(cal(N)(m, v)) = -integral log g thin d cal(N)(m, v)$.
  The mean of $cal(N)(m, v)$ is $m$ and its variance is $v$, so $integral (x - m)^2 thin d cal(N)(m, v)(x) = v$.
  All moments of $cal(N)(m, v)$ are finite, so $x |-> (x - m)^2$ is integrable.
  By the Gaussian cross-entropy lemma,
  $ h(cal(N)(m, v)) = 1/2 log (2 pi v) + v / (2 v) = 1/2 log (2 pi v) + 1/2 = 1/2 log (2 pi e v), $
  since $log (2 pi e v) = 1 + log (2 pi v)$.
]

#definition("AWGN capacity formula", lean: "Meat.awgnCapacity")[
  For $P, N in RR$,
  $ C(P, N) := 1/2 log (1 + P / N). $
]

In this formula, $P$ is the power constraint and $N$ is the noise variance.
The operational definition of the Gaussian channel and its coding theorem are in the sections below.

== Maximum entropy
#source("Meat.Continuous.MaxEntropy")

#theorem(
  "Maximum entropy under a second-moment bound",
  lean: "Meat.measureDiffEntropy_le_of_integral_sq_le",
)[
  Let $nu$ be a probability measure on $RR$ with $nu << lambda$, and let $f := d nu \/ d lambda$.
  Assume that $eta compose f$ is $lambda$-integrable.
  Let $m in RR$ and $v > 0$.
  Assume that $x |-> (x - m)^2$ is $nu$-integrable and that
  $ integral (x - m)^2 thin d nu(x) <= v. $
  Then
  $ h(nu) <= 1/2 log (2 pi e v). $
][
  Let $rho := cal(N)(m, v)$ and $g := d rho \/ d lambda$.
  Since $phi > 0$, $lambda << rho$, so $nu << rho$.
  By the Gaussian cross-entropy lemma, $log compose g$ is $nu$-integrable.
  The cross-entropy bound and the same lemma give
  $ h(nu) <= 1/2 log (2 pi v) + (integral (x - m)^2 thin d nu(x)) / (2 v) <= 1/2 log (2 pi v) + 1/2 = 1/2 log (2 pi e v). $
  In other words, $0 <= D(nu || rho) = -h(nu) + 1/2 log (2 pi v) + (integral (x - m)^2 thin d nu(x)) \/ (2 v)$.
]

The integrability hypothesis on $eta compose f$ cannot be dropped.
If it fails, the Bochner integral gives $h(nu) = 0$.
Scaling keeps it failing and makes the variance as small as we like.
Then $0 > 1/2 log (2 pi e v)$ when $2 pi e v < 1$.

#corollary(
  "Random variable form",
  lean: "Meat.diffEntropy_le_of_integral_sq_le",
)[
  Let $mu$ be a probability measure on $Omega$, and let $X : Omega -> RR$ be almost everywhere measurable with $X_* mu << lambda$.
  Assume that $eta compose (d X_* mu \/ d lambda)$ is $lambda$-integrable.
  Let $m in RR$ and $v > 0$.
  Assume that $omega |-> (X(omega) - m)^2$ is $mu$-integrable and that
  $ integral (X(omega) - m)^2 thin d mu(omega) <= v. $
  Then
  $ h(X) <= 1/2 log (2 pi e v). $
][
  By the change of variables formula, $integral (x - m)^2 thin d X_* mu(x) = integral (X(omega) - m)^2 thin d mu(omega)$.
  Integrability transfers in the same way.
  Apply the theorem to $X_* mu$.
]

#lemma(
  "Positive variance",
  lean: "Meat.variance_pos_of_absolutelyContinuous",
)[
  Let $nu$ be a probability measure on $RR$ with $nu << lambda$ and finite second moment.
  Then the variance of $nu$ is positive.
][
  Let $a$ be the mean of $nu$.
  If the variance is $0$, then $x = a$ for $nu$-almost every $x$, so $nu({a}) = 1$.
  But $lambda({a}) = 0$, so $nu({a}) = 0$.
]

#theorem(
  "Gaussian maximizes differential entropy",
  lean: "Meat.measureDiffEntropy_le_of_variance",
)[
  Let $nu$ be a probability measure on $RR$ with $nu << lambda$, finite second moment and variance $sigma^2$.
  Let $f := d nu \/ d lambda$, and assume that $eta compose f$ is $lambda$-integrable.
  Then
  $ h(nu) <= 1/2 log (2 pi e sigma^2). $
  Equality holds for $nu = cal(N)(m, sigma^2)$.
][
  Let $a$ be the mean of $nu$.
  By the lemma above, $sigma^2 > 0$.
  The function $x |-> (x - a)^2$ is $nu$-integrable, and its integral is $sigma^2$.
  Apply the second-moment theorem with $m := a$ and $v := sigma^2$.
  Equality for $cal(N)(m, sigma^2)$ is the entropy of a Gaussian, since the variance of $cal(N)(m, sigma^2)$ is $sigma^2$.
]

== The heat flow
#source("Meat.Continuous.HeatFlow")

Adding independent Gaussian noise of variance $s$ to a random variable with law $nu$ runs the heat equation for time $s / 2$ on its density.
This section builds that density and its derivatives for an arbitrary probability measure $nu$ on $RR$.

#definition(
  "Heat kernel",
  lean: ("Meat.heatKernel", "Meat.heatKernel_pos", "Meat.gaussianPDFReal_eq_heatKernel", "Meat.integral_heatKernel", "Meat.continuous_heatKernel"),
)[
  For $s, u in RR$,
  $ k_s (u) := (2 pi s)^(-1/2) exp(-u^2 / (2 s)). $
  For $s > 0$, $k_s > 0$, $k_s$ is continuous, $k_s (u - m)$ is the density of $cal(N)(m, s)$, and $integral k_s (u - m) thin d u = 1$.
]

#lemma(
  "Derivatives of the heat kernel",
  lean: ("Meat.hasDerivAt_heatKernel", "Meat.hasDerivAt_heatKernel_deriv", "Meat.hasDerivAt_heatKernel_time"),
)[
  $ partial_u k_s (u) = -(u / s) k_s (u), quad partial_u^2 k_s (u) = (u^2 / s^2 - 1 / s) k_s (u), $
  and for $s > 0$,
  $ partial_s k_s (u) = 1/2 (u^2 / s^2 - 1 / s) k_s (u) = 1/2 partial_u^2 k_s (u). $
][
  The chain rule and the product rule.
  For the time derivative, $d / (d s) (2 pi s)^(-1/2) = -(2 pi s)^(-1/2) \/ (2 s)$ and $d / (d s) (-u^2 \/ (2 s)) = u^2 \/ (2 s^2)$.
]

#lemma(
  "Gaussian envelope",
  lean: (
    "Meat.heatKernel_le", "Meat.heatEnvelope", "Meat.heatEnvelope_nonneg",
    "Meat.continuous_heatEnvelope", "Meat.abs_mul_heatKernel_le", "Meat.heatPoly_one",
    "Meat.heatPoly_deriv", "Meat.heatPoly_deriv2", "Meat.heatPoly_time", "Meat.heatEnvelope_le",
    "Meat.integrable_pow_mul_exp_neg_mul_sq", "Meat.integrable_heatEnvelope",
  ),
)[
  Let $0 < a <= s <= b$, and let
  $ E_(a, b) (u) := (2 pi a)^(-1/2) (1 + 1 / a)^2 (1 + u^2) e^(-u^2 / (2 b)). $
  Then $k_s (u) <= (2 pi a)^(-1/2) e^(-u^2 / (2 b))$.
  If $|c| <= (1 + 1 / a)^2 (1 + u^2)$, then $|c k_s (u)| <= E_(a, b)(u)$.
  The factors $1$, $-u / s$, $u^2 / s^2 - 1 / s$ and half of the last satisfy this bound.
  Moreover $E_(a, b) <= (2 pi a)^(-1/2) (1 + 1 / a)^2 (1 + 2 b)$, $u^n e^(-c u^2)$ is integrable for $c > 0$, and so $(1 + u^2) E_(a, b)(u)$ is integrable.
][
  $(2 pi s)^(-1/2) <= (2 pi a)^(-1/2)$ and $u^2 \/ (2 s) >= u^2 \/ (2 b)$.
  The polynomial bounds use $1 \/ s <= 1 \/ a$ and $|u| <= 1 + u^2$.
  The constant bound uses $u^2 e^(-u^2 \/ (2 b)) <= 2 b$, from $x <= e^x$.
  Integrability of $u^n e^(-c u^2)$ is Mathlib's Gaussian integral for real powers.
]

#definition(
  "Heat density",
  lean: ("Meat.heatDensity", "Meat.heatDensityDeriv", "Meat.heatDensityDeriv2"),
)[
  For a measure $nu$ on $RR$ and $s, x in RR$,
  $ p_s (x) := integral k_s (x - y) thin d nu(y), quad p'_s (x) := integral -((x - y) / s) k_s (x - y) thin d nu(y), $
  $ p''_s (x) := integral ((x - y)^2 / s^2 - 1 / s) k_s (x - y) thin d nu(y). $
]

#theorem(
  "Smoothness of the heat density",
  lean: (
    "Meat.integrable_mul_heatKernel", "Meat.integrable_heatKernel_comp",
    "Meat.integrable_heatEnvelope_comp", "Meat.abs_integral_mul_heatKernel_le",
    "Meat.heatDensity_pos", "Meat.heatDensity_le", "Meat.hasDerivAt_heatDensity",
    "Meat.hasDerivAt_heatDensityDeriv", "Meat.hasDerivAt_heatDensity_time",
    "Meat.continuous_heatDensity", "Meat.continuous_heatDensityDeriv",
    "Meat.continuous_heatDensityDeriv2",
  ),
)[
  Let $nu$ be a probability measure and $s > 0$.
  Then $0 < p_s (x) <= (2 pi s)^(-1/2)$, $partial_x p_s = p'_s$, $partial_x p'_s = p''_s$, and the heat equation holds:
  $ partial_s p_s (x) = 1/2 p''_s (x). $
  The functions $p_s$, $p'_s$ and $p''_s$ are continuous, and $|integral c(x - y) k_s (x - y) thin d nu(y)| <= integral E_(a, b)(x - y) thin d nu(y)$ for every admissible factor $c$.
][
  Differentiate under the integral sign.
  The envelope bounds every derivative by a constant, which is $nu$-integrable because $nu$ is finite.
  For the time derivative, take $s' in (s \/ 2, 2 s)$ and the envelope $E_(s \/ 2, 2 s)$.
  Positivity: the integrand is positive everywhere and $nu(RR) = 1$.
]

#theorem(
  "The heat density is the density of the smoothed law",
  lean: ("Meat.withDensity_conv_eq", "Meat.gaussianReal_conv_eq_withDensity", "Meat.measureDiffEntropy_conv_gaussianReal"),
)[
  If $F$ is measurable, then $(lambda dot F) * rho = lambda dot (x |-> integral F(x - y) thin d rho(y))$.
  In particular, for $s > 0$,
  $ cal(N)(0, s) * nu = lambda dot p_s, quad h(nu * cal(N)(0, s)) = integral eta(p_s (x)) thin d x. $
][
  Test against a measurable $phi >= 0$, translate by $y$ inside the inner integral, and swap the integrals by Tonelli.
  Then $integral^- "ofReal"(k_s (x - y)) thin d nu(y) = "ofReal"(p_s (x))$ because $k_s$ is integrable and positive.
  The Radon-Nikodym derivative of $lambda dot p_s$ is $p_s$ almost everywhere.
]

#lemma(
  "Weighted integrability against a convolution",
  lean: "Meat.integrable_mul_integral_comp_sub",
)[
  Let $nu$ be a probability measure with $integral y^2 thin d nu < infinity$.
  Let $g >= 0$ be measurable with $(1 + u^2) g(u)$ integrable.
  Then $x |-> (1 + x^2) integral g(x - y) thin d nu(y)$ is integrable.
][
  $1 + x^2 <= 2 (1 + y^2)(1 + (x - y)^2)$.
  The function $(x, y) |-> 2 (1 + y^2)(1 + (x - y)^2) g(x - y)$ is integrable on $lambda times nu$, since each section is a translate and its integral is $2 (1 + y^2) integral (1 + u^2) g$.
  Integrate out $y$.
]


== The de Bruijn identity
#source("Meat.Continuous.DeBruijn")

Throughout, $nu$ is a probability measure on $RR$ with $integral y^2 thin d nu(y) < infinity$, and $p_s$ is its heat density from the previous section.

#lemma(
  "Weighted Cauchy-Schwarz inequality",
  lean: "Meat.sq_integral_mul_le",
)[
  Let $w >= 0$, and let $w$, $w f$ and $w f^2$ be integrable.
  Then
  $ (integral w f)^2 <= (integral w) (integral w f^2). $
][
  For every $c$, $0 <= integral w (f - c)^2 = B - 2 c A + c^2 W$.
  If $W > 0$, take $c = A \/ W$.
  If $W = 0$ and $A != 0$, take $c = (B + 1) \/ (2 A)$ for a contradiction.
]

#lemma(
  "Integrability along the heat flow",
  lean: (
    "Meat.heatPoly_sq", "Meat.integrable_negMulLog_heatDensity", "Meat.integrable_heatFisher",
    "Meat.integrable_heatDensity", "Meat.integrable_heatDensityDeriv", "Meat.integral_heatDensity",
  ),
)[
  For $s > 0$, the functions $eta compose p_s$, $(p'_s)^2 \/ p_s$, $p_s$ and $p'_s$ are integrable, and $integral p_s = 1$.
][
  Choose $R$ with $nu([-R, R]) >= 1 / 2$.
  Then $p_s (x) >= 1/2 (2 pi b)^(-1/2) e^(-(x^2 + R^2) \/ a)$ for $a <= s <= b$, and with $p_s <= (2 pi a)^(-1/2)$ this gives $|1 + log p_s (x)| <= L (1 + x^2)$.
  By Cauchy-Schwarz with weight $k_s (x - y)$, $(p'_s)^2 \/ p_s <= integral (x - y)^2 \/ s^2 k_s (x - y) thin d nu(y)$.
  Every function above is then bounded by a constant times $(1 + x^2) integral E(x - y) thin d nu(y)$, which is integrable by the weighted integrability lemma.
  The total mass is $1$ because $lambda dot p_s = cal(N)(0, s) * nu$ is a probability measure.
]

#definition("Fisher information along the heat flow", lean: ("Meat.heatFisher", "Meat.heatFisher_nonneg"))[
  $ J(s) := integral (p'_s (x))^2 / p_s (x) thin d x. $
  For $s > 0$, $J(s) >= 0$.
]

#lemma(
  "Integration by parts",
  lean: "Meat.integral_neg_log_mul_heatDensityDeriv2",
)[
  For $s > 0$,
  $ integral (-log p_s (x) - 1) (p''_s (x) / 2) thin d x = J(s) / 2. $
][
  Let $G := (1 + log p_s) p'_s$.
  Then $G' = (p'_s)^2 \/ p_s + (1 + log p_s) p''_s$.
  Both $G$ and $G'$ are integrable, so $integral G' = 0$.
  No limit at infinity is needed for this.
]

#theorem(
  "de Bruijn identity",
  lean: "Meat.hasDerivAt_heatEntropy",
)[
  For $t > 0$, the function $s |-> h(nu * cal(N)(0, s)) = integral eta(p_s (x)) thin d x$ has derivative $J(t) \/ 2$ at $t$.
][
  By the heat equation, $partial_s eta(p_s) = (-log p_s - 1) p''_s \/ 2$.
  For $s in (t \/ 2, 2 t)$ this is bounded by $L (1 + x^2) integral E_(t \/ 2, 2 t)(x - y) thin d nu(y)$, which is integrable.
  So the derivative passes under the integral, and integration by parts gives $J(t) \/ 2$.
]


== Fisher information
#source("Meat.Continuous.Fisher")

Fisher information measures how sharply a density changes under a shift.
The de Bruijn identity links it to the derivative of differential entropy along the heat flow.

#definition("Fisher information", lean: "Meat.fisherInfo")[
  For $f : RR -> RR$,
  $ J(f) := integral (f'(x))^2 / f(x) thin d x. $
  Lean divides by zero as zero, so points with $f(x) = 0$ add nothing.
]

#lemma(
  "Derivative of the Gaussian density",
  lean: "Meat.hasDerivAt_gaussianPDFReal",
)[
  Let $phi_(m, v)$ be the density of $cal(N)(m, v)$.
  For every $x in RR$,
  $ phi_(m, v)'(x) = -(x - m) / v dot phi_(m, v)(x). $
][
  Differentiate $phi_(m, v)(x) = (2 pi v)^(-1/2) exp(-(x - m)^2 \/ (2 v))$ by the chain rule.
  For $v = 0$ both sides are $0$, because Lean sets $phi_(m, 0) = 0$ and divides by zero as zero.
]

#theorem(
  "Fisher information of a Gaussian",
  lean: "Meat.fisherInfo_gaussianPDFReal",
)[
  For $v > 0$,
  $ J(phi_(m, v)) = 1 / v. $
][
  By the lemma, $(phi')^2 \/ phi = (x - m)^2 \/ v^2 dot phi$, since $phi > 0$.
  So $J(phi) = v^(-2) integral (x - m)^2 phi(x) thin d x = v^(-2) dot v = 1 \/ v$.
]

#theorem(
  "Cramér-Rao bound for a location parameter",
  lean: "Meat.one_le_integral_sq_mul_fisherInfo",
)[
  Let $f : RR -> RR$ be differentiable and nonnegative with $integral f = 1$, and let $m in RR$.
  Assume that $f$, $(x - m) f'(x)$, $(x - m)^2 f(x)$ and $(f')^2 \/ f$ are integrable, and that $(x - m) f(x) -> 0$ as $x -> plus.minus infinity$.
  Then
  $ 1 <= (integral (x - m)^2 f(x) thin d x) dot J(f). $
  In particular $"Var"(f) dot J(f) >= 1$, with equality for Gaussians.
][
  The derivative of $(x - m) f(x)$ is $f(x) + (x - m) f'(x)$.
  It is integrable, and $(x - m) f(x)$ tends to $0$ at both ends, so its integral is $0$.
  Hence $integral (x - m) f'(x) thin d x = -1$.
  Let $V := integral (x - m)^2 f$.
  For every $a in RR$ and every $x$,
  $ a^2 (x - m)^2 f(x) + 2 a (x - m) f'(x) + (f'(x))^2 / f(x) >= 0. $
  If $f(x) > 0$, the left side is $f(x) (a (x - m) + f'(x) \/ f(x))^2$.
  If $f(x) = 0$, then $x$ is a minimum of $f$, so $f'(x) = 0$ and the left side is $0$.
  Integrate: $a^2 V - 2 a + J(f) >= 0$ for all $a$.
  If $V = 0$, take $a = J(f) \/ 2 + 1$ for a contradiction.
  If $V > 0$, take $a = 1 \/ V$ to get $J(f) >= 1 \/ V$.
]

The Gaussian attains equality: $V = v$ and $J = 1 \/ v$.

#lemma(
  "Fisher information of the heat density",
  lean: "Meat.fisherInfo_heatDensity",
)[
  For a probability measure $nu$ and $s > 0$, $J(p_s)$ equals the heat-flow Fisher information $J(s)$ of the de Bruijn section.
][
  The derivative of $p_s$ is $p'_s$.
]


== Stam's inequality with a Gaussian summand
#source("Meat.Continuous.Stam")

#lemma(
  "Product of heat kernels",
  lean: ("Meat.heatKernel_mul_heatKernel", "Meat.heatKernel_le_const"),
)[
  For $t, u > 0$, let $sigma := t u \/ (t + u)$.
  Then
  $ k_t (z) k_u (w - z) = k_(t + u)(w) k_sigma (z - t w \/ (t + u)). $
  Also $k_s <= (2 pi s)^(-1/2)$.
][
  Complete the square in the exponent, and use $2 pi t dot 2 pi u = 2 pi (t + u) dot 2 pi sigma$ for the constants.
]

#lemma(
  "Gaussian moments",
  lean: ("Meat.integrable_mul_heatKernel_volume", "Meat.integral_mul_heatKernel_moment"),
)[
  For $s > 0$, $c(v) k_s (v)$ is integrable for every admissible factor $c$, and
  $ integral k_s = 1, quad integral v k_s (v) thin d v = 0, quad integral v^2 k_s (v) thin d v = s. $
][
  The envelope bounds the integrand.
  The moments are the mass, mean and variance of $cal(N)(0, s)$.
]

#lemma(
  "Chapman-Kolmogorov identities",
  lean: (
    "Meat.integral_heatKernel_mul_heatKernel", "Meat.integral_heatKernel_deriv_mul_heatKernel",
    "Meat.integral_heatKernel_mul_heatKernel_deriv",
  ),
)[
  For $t, u > 0$,
  $ integral k_t (z) k_u (w - z) thin d z = k_(t + u)(w), $
  $ integral -(z / t) k_t (z) k_u (w - z) thin d z = integral k_t (z) (-(w - z) / u) k_u (w - z) thin d z = -(w / (t + u)) k_(t + u)(w). $
][
  Apply the product lemma, and integrate the shifted kernel $k_sigma$ against $1$, $z$ and $w - z$.
]

#theorem(
  "Semigroup property of the heat density",
  lean: ("Meat.heatDensity_add", "Meat.heatDensityDeriv_add", "Meat.heatDensityDeriv_add'"),
)[
  For a probability measure $nu$ and $t, u > 0$,
  $ p_(t + u)(x) = integral p_t (z) k_u (x - z) thin d z, $
  $ p'_(t + u)(x) = integral p'_t (z) k_u (x - z) thin d z = integral p_t (z) (-(x - z) / u) k_u (x - z) thin d z. $
][
  Write $p_t (z)$ as an integral over $nu$, swap the order by Fubini (the integrand is bounded by a translate of an integrable function times a constant), shift $z$ by $y$, and apply the Chapman-Kolmogorov identities.
]

#theorem(
  "Stam's inequality along the heat flow",
  lean: "Meat.heatFisher_add_le",
)[
  Let $nu$ be a probability measure with finite second moment, and $t, u > 0$.
  Then
  $ J(t + u) <= J(t) / (1 + u J(t)), quad "equivalently" quad 1 / J(t + u) >= 1 / J(t) + u. $
][
  Fix $lambda in [0, 1]$.
  By the semigroup property, $p'_(t + u)(x) = integral w_x g_x$ with weight $w_x (z) = p_t (z) k_u (x - z)$ and
  $ g_x (z) = lambda p'_t (z) / p_t (z) - (1 - lambda)(x - z) / u. $
  Since $integral w_x = p_(t + u)(x)$, the weighted Cauchy-Schwarz inequality gives $(p'_(t + u))^2 \/ p_(t + u) <= integral w_x g_x^2$.
  Integrate in $x$ and swap by Fubini.
  The Gaussian moments give $integral w_x g_x^2 thin d x = p_t (z) (lambda^2 (p'_t \/ p_t)^2 + (1 - lambda)^2 \/ u)$ and kill the cross term.
  So $J(t + u) <= lambda^2 J(t) + (1 - lambda)^2 \/ u$.
  Take $lambda = 1 \/ (1 + u J(t))$.
]


== The entropy power inequality
#source("Meat.Continuous.EPI")

#definition("Entropy power", lean: "Meat.entropyPower")[
  For a measure $nu$ on $RR$,
  $ N(nu) := e^(2 h(nu)) / (2 pi e). $
]

#lemma(
  "Basic facts on entropy power",
  lean: ("Meat.entropyPower_pos", "Meat.exp_two_mul_measureDiffEntropy"),
)[
  $N(nu) > 0$, and $e^(2 h(nu)) = 2 pi e dot N(nu)$.
][
  Both follow from the definition.
]

#theorem(
  "Entropy power of a Gaussian",
  lean: ("Meat.entropyPower_gaussianReal", "Meat.entropyPower_gaussianReal_conv"),
)[
  For $v > 0$, $N(cal(N)(m, v)) = v$.
  For $v_1, v_2 > 0$,
  $ N(cal(N)(m_1, v_1) * cal(N)(m_2, v_2)) = N(cal(N)(m_1, v_1)) + N(cal(N)(m_2, v_2)). $
  So Gaussians attain equality in the entropy power inequality.
][
  $h(cal(N)(m, v)) = 1/2 log(2 pi e v)$, so $e^(2 h) = 2 pi e v$.
  The convolution of two Gaussians is $cal(N)(m_1 + m_2, v_1 + v_2)$.
]

#theorem(
  "Entropy power is at most the variance",
  lean: "Meat.entropyPower_le_variance",
)[
  Let $nu$ be a probability measure on $RR$ with $nu << lambda$, finite second moment and $eta compose (d nu \/ d lambda)$ integrable.
  Then $N(nu) <= "Var"(nu)$.
][
  This is the maximum entropy theorem, $h(nu) <= 1/2 log(2 pi e "Var"(nu))$, after taking $exp(2 dot)$.
]

#theorem(
  "Adding independent noise increases differential entropy",
  lean: "Meat.measureDiffEntropy_le_conv",
)[
  Let $nu, rho$ be probability measures on $RR$ with $nu << lambda$.
  Assume that $eta compose (d nu \/ d lambda)$ and $eta compose (d (nu * rho) \/ d lambda)$ are integrable.
  Then
  $ h(nu) <= h(nu * rho). $
  The measure $rho$ need not have a density.
][
  Let $f := d nu \/ d lambda$.
  First, $nu * rho$ has density $g(x) := integral f(x - y) thin d rho(y)$.
  To see this, test against a measurable $phi >= 0$, move the shift onto $f$ by translation invariance of $lambda$, and swap the integrals by Tonelli.
  The function $(x, y) |-> eta(f(x - y))$ is integrable on $lambda times rho$, since each section is a translate of $eta compose f$.
  For almost every $x$, $y |-> f(x - y)$ is $rho$-integrable, and Jensen's inequality for the concave $eta$ gives
  $ integral eta(f(x - y)) thin d rho(y) <= eta(g(x)). $
  Integrate in $x$ and swap by Fubini:
  $ h(nu) = integral integral eta(f(x - y)) thin d x thin d rho(y) <= integral eta(g(x)) thin d x = h(nu * rho). $
]

The integrability hypothesis on $nu * rho$ cannot be dropped, because the Bochner integral of a non-integrable function is $0$.

#corollary(
  "Random variable form",
  lean: "Meat.diffEntropy_le_diffEntropy_add",
)[
  Let $X, Y$ be independent real random variables, with $X$ having a density and the integrability hypotheses above for $X$ and $X + Y$.
  Then $h(X) <= h(X + Y)$.
][
  The law of $X + Y$ is $X_* mu * Y_* mu$.
]

#corollary(
  "The entropy power inequality within a factor of two",
  lean: ("Meat.max_entropyPower_le_conv", "Meat.entropyPower_add_le_two_mul_conv"),
)[
  Let $nu, rho$ be probability measures on $RR$ with densities, and with $eta$ of the densities of $nu$, $rho$ and $nu * rho$ integrable.
  Then
  $ max(N(nu), N(rho)) <= N(nu * rho), quad N(nu) + N(rho) <= 2 N(nu * rho). $
][
  Apply the theorem to $nu * rho$ and to $rho * nu = nu * rho$, and use that $exp$ is monotone.
  The second inequality follows, since a sum of two numbers is at most twice their maximum.
]

#definition(
  "Entropy power inequality",
  lean: ("Meat.EntropyPowerInequality", "Meat.GaussianEntropyPowerInequality"),
)[
  The entropy power inequality is the statement: for all probability measures $nu, rho$ on $RR$ with densities, finite second moments, and $eta$ of the densities of $nu$, $rho$ and $nu * rho$ integrable,
  $ e^(2 h(nu * rho)) >= e^(2 h(nu)) + e^(2 h(rho)). $
  Its Gaussian case is the statement: for every probability measure $nu$ with a density, finite second moment and $eta$ of its density integrable, and every $v > 0$,
  $ e^(2 h(nu * cal(N)(0, v))) >= e^(2 h(nu)) + 2 pi e v. $
  The Gaussian case is proved below.
  The general case is still a proposition here.
]

#lemma(
  "Entropy power form",
  lean: "Meat.entropyPowerInequality_iff_entropyPower",
)[
  The entropy power inequality holds if and only if $N(nu) + N(rho) <= N(nu * rho)$ under the same hypotheses.
][
  Divide by $2 pi e > 0$.
]

#lemma(
  "Entropy along the heat flow",
  lean: ("Meat.integrable_negMulLog_conv_gaussianReal", "Meat.heatEntropy_ge"),
)[
  Let $nu$ be a probability measure with finite second moment, and $s > 0$.
  Then $eta$ of the density of $nu * cal(N)(0, s)$ is integrable, and
  $ integral eta(p_s (x)) thin d x >= 1/2 log(2 pi e s). $
][
  The density of $nu * cal(N)(0, s)$ is $p_s$ almost everywhere.
  The bound is the noise theorem applied to $cal(N)(0, s) * nu$.
]

#theorem(
  "Isoperimetric inequality for entropy along the heat flow",
  lean: "Meat.two_pi_e_le_exp_mul_heatFisher",
)[
  Let $nu$ be a probability measure with finite second moment, and $t > 0$.
  Then
  $ e^(2 h(nu * cal(N)(0, t))) J(t) >= 2 pi e, $
  that is, $N J >= 1$.
][
  Let $H(s) := h(nu * cal(N)(0, s))$.
  The function $Phi(tau) := H(t + tau) - 1/2 log(1 + tau J(t))$ has derivative $J(t + tau) \/ 2 - J(t) \/ (2 (1 + tau J(t)))$ by de Bruijn.
  By Stam's inequality the derivative is $<= 0$, so $Phi(T) <= Phi(0) = H(t)$ for $T >= 0$.
  With $H(t + T) >= 1/2 log(2 pi e (t + T))$ this gives
  $ 2 pi e (t + T) <= e^(2 H(t)) (1 + T J(t)) quad "for all" T > 0. $
  If $e^(2 H(t)) J(t) < 2 pi e$, then $T = e^(2 H(t)) \/ (2 pi e - e^(2 H(t)) J(t)) + 1$ contradicts this.
  No asymptotics as $T -> infinity$ are needed.
]

#theorem(
  "Entropy power inequality with a Gaussian summand",
  lean: "Meat.gaussianEntropyPowerInequality",
)[
  Let $nu$ be a probability measure on $RR$ with $nu << lambda$, finite second moment, and $eta compose (d nu \/ d lambda)$ integrable.
  Let $v > 0$.
  Then
  $ e^(2 h(nu * cal(N)(0, v))) >= e^(2 h(nu)) + 2 pi e v. $
][
  Let $H(s) := h(nu * cal(N)(0, s))$ and $c := 2 pi e$.
  By de Bruijn, $s |-> e^(2 H(s)) - c s$ has derivative $e^(2 H(s)) J(s) - c >= 0$ on $(0, infinity)$, by the isoperimetric inequality.
  So for $0 < epsilon < v$, $e^(2 H(v)) >= e^(2 H(epsilon)) + c (v - epsilon)$.
  Adding independent noise increases differential entropy, so $H(epsilon) >= h(nu)$.
  Let $epsilon -> 0$.
  No continuity of $H$ at $0$ is needed.
]

#theorem(
  "Gaussian noise and entropy power",
  lean: "Meat.diffEntropy_add_gaussian_ge",
)[
  Let $X$ be a real random variable with a density, finite second moment and $eta$ of its density integrable.
  Let $Z ~ cal(N)(0, v)$ with $v > 0$ be independent of $X$.
  Then
  $ h(X + Z) >= 1/2 log(e^(2 h(X)) + 2 pi e v). $
][
  The law of $X + Z$ is $X_* mu * cal(N)(0, v)$.
  Take $log$ of the previous theorem and divide by $2$.
]

This is the form that the converse for the degraded Gaussian broadcast channel uses.
With $Y_1 = X + Z_1$ and $Y_2 = Y_1 + Z'$, where $Z' ~ cal(N)(0, N_2 - N_1)$ is independent of $Y_1$, it gives $h(Y_2) >= 1/2 log(e^(2 h(Y_1)) + 2 pi e (N_2 - N_1))$.

#theorem(
  "Unconditional Gaussian noise bound",
  lean: "Meat.max_diffEntropy_le_add_gaussian",
)[
  Let $X$ have a density with $eta$ of the density integrable.
  Let $Z ~ cal(N)(0, v)$ with $v > 0$ be independent of $X$, and assume $eta$ of the density of $X + Z$ is integrable.
  Then
  $ max(h(X), 1/2 log(2 pi e v)) <= h(X + Z). $
][
  Apply the noise theorem twice: to $X_* mu * cal(N)(0, v)$ and to $cal(N)(0, v) * X_* mu$.
]

So $e^(2 h(X + Z)) >= 1/2 (e^(2 h(X)) + 2 pi e v)$ with no unproved hypothesis: the Gaussian case up to a factor of two.


== Stam's inequality for two summands
#source("Meat.Continuous.StamTwo")

In this section $nu$ and $rho$ are probability measures on $RR$.
Write $p^nu_s$ and $J_nu (s)$ for the heat density and the Fisher information of $nu$ at time $s$, and the same for $rho$ and $nu * rho$.

#lemma(
  "Second moment of a convolution",
  lean: "Meat.integrable_sq_conv",
)[
  If $nu$ and $rho$ have finite second moments, then so does $nu * rho$, and
  $ integral y^2 thin d (nu * rho)(y) = integral y^2 thin d nu(y) + 2 (integral y thin d nu(y)) (integral y thin d rho(y)) + integral y^2 thin d rho(y). $
][
  The measure $nu * rho$ is the image of $nu times rho$ under $(y, z) |-> y + z$.
  Expand $(y + z)^2$.
  Each of the three terms is integrable on the product, and the cross term splits by Fubini into a product of the two means.
]

#theorem(
  "Stam's inequality for two summands",
  lean: "Meat.heatFisher_conv_le",
)[
  Let $nu, rho$ have finite second moments, let $s, u > 0$, and let $l in RR$.
  Then
  $ J_(nu * rho)(s + u) <= l^2 J_nu (s) + (1 - l)^2 J_rho (u). $
][
  Write $P := p^nu_s$, $Q := p^rho_u$, and $P'$, $Q'$ for their derivatives.
  First, the heat densities convolve: $p^(nu * rho)_(s + u) = P * Q$.
  This follows from $cal(N)(0, s + u) = cal(N)(0, s) * cal(N)(0, u)$ and the associativity and commutativity of convolution, since two continuous densities of the same measure are equal.
  Differentiation under the integral sign gives $(p^(nu * rho)_(s + u))' = P * Q' = P' * Q$.
  Fix $x$, and let $w(z) := P(z) Q(x - z)$ and
  $ g(z) := l P'(z) / P(z) + (1 - l) Q'(x - z) / Q(x - z). $
  Then $integral w = p^(nu * rho)_(s + u)(x)$ and $integral w g = (p^(nu * rho)_(s + u))'(x)$.
  The weighted Cauchy-Schwarz inequality gives
  $ ((p^(nu * rho)_(s + u))'(x))^2 / p^(nu * rho)_(s + u)(x) <= integral w g^2. $
  Integrate in $x$ and swap the integrals by Fubini.
  For fixed $z$, the integral over $x$ of $w g^2$ is $l^2 P'(z)^2 \/ P(z) + (1 - l)^2 J_rho (u) P(z)$, because $integral Q = 1$ and $integral Q' = 0$ kill the cross term.
  Integrate in $z$.
]

With $l = J_rho (u) \/ (J_nu (s) + J_rho (u))$ this is the usual form $1 \/ J_(nu * rho)(s + u) >= 1 \/ J_nu (s) + 1 \/ J_rho (u)$.
Stam's inequality with a Gaussian summand is the case where $rho$ is a point mass.


== The entropy power inequality for smoothed summands
#source("Meat.Continuous.EPITwo")

Write $H_nu (s) := integral eta(p^nu_s (x)) thin d x = h(nu * cal(N)(0, s))$ for the entropy along the heat flow.

#theorem(
  "Entropy power inequality along the heat flow",
  lean: "Meat.heatEntropyPowerInequality",
)[
  Let $nu, rho$ be probability measures on $RR$ with finite second moments, and let $s, u > 0$.
  Then
  $ e^(2 H_nu (s)) + e^(2 H_rho (u)) <= e^(2 H_(nu * rho)(s + u)). $
  The measures $nu$ and $rho$ need not have densities.
][
  Let $M_nu$ be the second moment of $nu$.
  The second moment of $nu * cal(N)(0, t)$ is $M_nu + t$, so the maximum entropy theorem gives $H_nu (t) <= 1/2 log(2 pi e (M_nu + t))$.
  Together with $H_nu (t) >= 1/2 log(2 pi e t)$, this pins down $H_nu (t)$ for large $t$.

  Fix $theta in (0, 1)$ and let
  $ D(tau) := H_(nu * rho)(s + u + tau) - theta H_nu (s + theta tau) - (1 - theta) H_rho (u + (1 - theta) tau). $
  By de Bruijn,
  $ D'(tau) = 1/2 (J_(nu * rho)(s + u + tau) - theta^2 J_nu (s + theta tau) - (1 - theta)^2 J_rho (u + (1 - theta) tau)), $
  and Stam's inequality for two summands with $l = theta$ makes this $<= 0$.
  So $D$ is antitone on $[0, infinity)$.
  The two bounds above give $D(tau) >= L(tau)$, where
  $ L(tau) := 1/2 (log((s + u) / tau + 1) - theta log((M_nu + s) / tau + theta) - (1 - theta) log((M_rho + u) / tau + 1 - theta)), $
  since the terms $log(2 pi e tau)$ cancel.
  As $tau -> infinity$, $L(tau) -> 1/2 (eta(theta) + eta(1 - theta))$.
  Hence
  $ H_(nu * rho)(s + u) = D(0) >= theta H_nu (s) + (1 - theta) H_rho (u) + 1/2 (eta(theta) + eta(1 - theta)). $
  Let $a := e^(2 H_nu (s))$, $b := e^(2 H_rho (u))$ and $theta := a \/ (a + b)$.
  Then $log theta = 2 H_nu (s) - log(a + b)$ and $log(1 - theta) = 2 H_rho (u) - log(a + b)$, so the right side equals $1/2 log(a + b)$.
  Take $exp(2 dot)$.
]

#theorem(
  "Entropy power inequality with a smoothed summand",
  lean: "Meat.entropyPowerInequality_conv_gaussianReal",
)[
  Let $nu$ be a probability measure on $RR$ with $nu << lambda$, finite second moment, and $eta compose (d nu \/ d lambda)$ integrable.
  Let $rho$ be a probability measure with finite second moment, and $v > 0$.
  Then
  $ e^(2 h(nu)) + e^(2 h(rho * cal(N)(0, v))) <= e^(2 h(nu * (rho * cal(N)(0, v)))). $
  The measure $rho$ need not have a density.
][
  By associativity, $h(nu * (rho * cal(N)(0, v))) = H_(nu * rho)(v)$, and $h(rho * cal(N)(0, v)) = H_rho (v)$.
  For $0 < epsilon < v$, the previous theorem at times $epsilon$ and $v - epsilon$ gives
  $ e^(2 H_nu (epsilon)) + e^(2 H_rho (v - epsilon)) <= e^(2 H_(nu * rho)(v)). $
  Adding independent noise increases differential entropy, so $h(nu) <= H_nu (epsilon)$.
  The function $H_rho$ is differentiable at $v > 0$ by de Bruijn, so it is continuous there.
  Let $epsilon -> 0$ from above.
]

With $rho$ a point mass at $0$ this is the entropy power inequality with a Gaussian summand.

#corollary(
  "Entropy power inequality up to a small Gaussian",
  lean: "Meat.entropyPowerInequality_conv_conv_gaussianReal",
)[
  Let $nu, rho$ be probability measures on $RR$ with densities, finite second moments, and $eta$ of both densities integrable.
  Then for every $v > 0$,
  $ e^(2 h(nu)) + e^(2 h(rho)) <= e^(2 h(nu * (rho * cal(N)(0, v)))). $
][
  Apply the previous theorem, and use $h(rho) <= h(rho * cal(N)(0, v))$, since adding independent noise increases differential entropy.
]

The unconditional entropy power inequality would follow from this corollary if $h(nu * rho * cal(N)(0, v)) -> h(nu * rho)$ as $v -> 0$.
The lower bound $h(nu * rho) <= h(nu * rho * cal(N)(0, v))$ holds, but the upper bound needs the lower semicontinuity of relative entropy under weak convergence.
That is not yet formalized, so the general case is still open here.


== The AWGN channel
#source("Meat.Continuous.AWGN")

The additive white Gaussian noise (AWGN) channel maps an input $x in RR$ to $Y = x + Z$, with $Z ~ cal(N)(0, N)$ and $N > 0$.
The noise is independent across channel uses.
Each codeword must satisfy an average power constraint $P$.
In Lean, a negative noise variance $N$ is replaced by $0$, but all theorems assume $N > 0$.

#definition(
  "Noise and codes",
  lean: (
    "Meat.AWGN.noise",
    "Meat.AWGN.isProbabilityMeasure_noise",
    "Meat.AWGN.Code",
    "Meat.AWGN.Code.errorProb",
    "Meat.AWGN.Code.avgError",
  ),
)[
  The noise law on $RR^n$ is the product measure $cal(N)(0, N)^(times.o n)$.
  It is a probability measure.
  A code of length $n$ with $k$ messages and power $P$ is a pair $(f, g)$.
  The encoder $f : [k] -> RR^n$ satisfies $sum_(i = 1)^n f(m)_i^2 <= n P$ for every $m$.
  The decoder $g : RR^n -> [k]$ is measurable.
  The error probability of message $m$ is
  $ lambda_m := cal(N)(0, N)^(times.o n) ({z : g(f(m) + z) != m}), $
  and the average error probability is $overline(lambda) := k^(-1) sum_m lambda_m$.
]

#definition("Achievable rate", lean: "Meat.AWGN.Achievable")[
  A rate $R in RR$ is achievable for power $P$ and noise $N$ if for every $epsilon > 0$ there exists $n_0 in NN$ such that for every $n >= n_0$ there exist $k in NN$ with $k >= e^(n R)$ and a code of length $n$ with $k$ messages, power $P$ and $overline(lambda) <= epsilon$.
]

The definition mirrors the definition for discrete memoryless channels.
The power constraint holds for each codeword, not only on average over the messages.

#lemma(
  "Rate zero and the sign of the capacity",
  lean: ("Meat.AWGN.achievable_zero", "Meat.AWGN.awgnCapacity_nonneg"),
)[
  If $P >= 0$, then $R = 0$ is achievable for every $N$.
  If also $N > 0$, then $C(P, N) >= 0$.
][
  Take $k = 1$, the zero codeword and the constant decoder.
  The zero codeword uses power $0 <= n P$, and the decoder never errs.
  For the second claim, $1 + P \/ N >= 1$, so its logarithm is nonnegative.
]

#theorem(
  "Assembly of the coding theorem",
  lean: "Meat.AWGN.closure_achievable_eq_of",
)[
  Let $P >= 0$ and $N > 0$.
  Assume that every $R$ with $0 <= R < C(P, N)$ is achievable, and that every achievable $R$ satisfies $R <= C(P, N)$.
  Then
  $ overline({R >= 0 : R "achievable"}) = [0, C(P, N)]. $
][
  The proof is the same as for the channel coding theorem.
  The second assumption puts the set inside the closed interval $[0, C(P, N)]$.
  If $C(P, N) = 0$, the interval is ${0}$, and $0$ is achievable.
  Otherwise, the first assumption gives $[0, C(P, N))$, whose closure is $[0, C(P, N)]$.
]

== AWGN converse
#source("Meat.Continuous.AWGNConverse")

The converse does not use differential entropy.
It turns a code into a channel with finite input and output alphabets.
Then it bounds the information of that channel with one Gaussian reference measure.
Each message $m$ gives a law of the decoded message $g(f(m) + Z)$ on $[k]$.
This is a DMC $V$ from $[k]$ to $[k]$, and the code becomes a code of length $1$ for $V$.
Fano's inequality from the channel chapter applies to this code.
The information of $V$ with uniform input is bounded by a divergence against the law of $g(G)$.
Here $G$ is a centered Gaussian vector with variances $P_i + N$, and $P_i$ is the average power of coordinate $i$ over the codebook.
The divergence of the decoded laws is at most the divergence of the Gaussian laws on $RR^n$, which has a closed form.

#lemma("Densities of product measures", lean: "Meat.pi_withDensity")[
  Let $rho_i$ be probability measures and $f_i >= 0$ measurable, for $i$ in a finite set.
  Assume that each $rho_i$ with density $f_i$ is $sigma$-finite.
  Then the product of the measures $f_i rho_i$ is the product measure $times.o_i rho_i$ with density $x |-> product_i f_i (x_i)$.
][
  Compare both sides on boxes $product_i s_i$.
  The right side gives $integral product_i bb(1)_(s_i) (x_i) f_i (x_i) thin d (times.o_i rho_i)(x)$.
  The coordinates are independent under the product measure, so this integral is $product_i integral_(s_i) f_i thin d rho_i$.
  This is the left side on the box.
]

#lemma(
  "Divergence of a finite partition",
  lean: "Meat.sum_mul_log_sub_log_le_integral",
)[
  Let $mu$ be a probability measure and $rho$ a finite measure.
  Let $mu$ have density $e^L$ with respect to $rho$, with $L$ measurable and $mu$-integrable.
  Let $d$ be a measurable map to a finite set $J$, and let $mu_j := mu(d^(-1)(j))$ and $rho_j := rho(d^(-1)(j))$.
  Then
  $ sum_(j in J) mu_j (log mu_j - log rho_j) <= integral L thin d mu. $
][
  Fix a cell $A := d^(-1)(j)$.
  We show $mu_j (log mu_j - log rho_j) <= integral_A L thin d mu$.
  If $mu_j = 0$, both sides are $0$.
  Otherwise $rho_j > 0$, since $mu << rho$.
  At every point, $log t <= t - 1$ with $t := (mu_j \/ rho_j) e^(-L)$ gives
  $ log mu_j - log rho_j - L <= mu_j / rho_j e^(-L) - 1. $
  Integrate over $A$ with respect to $mu$.
  Since $e^(-L) e^L = 1$, $integral_A e^(-L) thin d mu = rho_j$, so the right side integrates to $0$.
  Sum over $j$; the cells cover the space.
]

The left side is the divergence of the push-forwards of $mu$ and $rho$ by $d$.
The right side is $D(mu || rho)$.
So the lemma is data processing for divergence, for a map to a finite set.

#lemma(
  "Golden formula bound",
  lean: "Meat.DMC.inputMutualInfo_le_sum_mul_log_sub",
)[
  Let $W$ be a DMC with finite alphabets and $p in Delta(A)$.
  Let $r : B -> [0, infinity)$ with $sum_b r(b) <= 1$.
  Assume that $r(b) = 0$ implies $W(b given a) = 0$ for every $a$.
  Then
  $ I(p) <= sum_a p(a) sum_b W(b given a) (log W(b given a) - log r(b)). $
][
  Write $I(p) = H(Y) - H(Y given X)$.
  The term $H(Y given X)$ is $-sum_(a, b) p(a) W(b given a) log W(b given a)$.
  Let $q(b) := sum_a p(a) W(b given a)$ be the output law.
  Gibbs' inequality gives $H(Y) = -sum_b q(b) log q(b) <= -sum_b q(b) log r(b)$.
  Expand $q$ and combine the two sums.
]

#lemma(
  "Shifted noise",
  lean: ("Meat.AWGN.map_noise_add", "Meat.AWGN.map_noise_add_absolutelyContinuous"),
)[
  Let $x in RR^n$.
  The law of $x + Z$ for $Z ~ cal(N)(0, N)^(times.o n)$ is $times.o_i cal(N)(x_i, N)$.
  If $N > 0$ and $S_i > 0$ for every $i$, this law is absolutely continuous with respect to $times.o_i cal(N)(0, S_i)$.
][
  The push-forward of a product measure by a coordinatewise map is the product of the push-forwards.
  A shift of $cal(N)(0, N)$ by $x_i$ is $cal(N)(x_i, N)$.
  For the second claim, $cal(N)(x_i, N)$ is $cal(N)(0, S_i)$ with the density $e^(ell_i)$, where
  $ ell_i (t) := 1/2 log (S_i / N) - (t - x_i)^2 / (2 N) + t^2 / (2 S_i). $
  This holds because the Gaussian densities satisfy $phi_(0, S_i) e^(ell_i) = phi_(x_i, N)$.
  By the lemma on densities of product measures, the product has the density $e^(sum_i ell_i (t_i))$.
]

#lemma(
  "Divergence bound for one codeword",
  lean: "Meat.AWGN.sum_mul_log_sub_log_le",
)[
  Let $N > 0$, $x in RR^n$ and $S in RR^n$ with $S_i > 0$.
  Let $mu$ be the law of $x + Z$ and $rho := times.o_i cal(N)(0, S_i)$.
  Let $d$ be a measurable map from $RR^n$ to a finite set $J$, with cells $A_j := d^(-1)(j)$.
  Then
  $ sum_j mu(A_j) (log mu(A_j) - log rho(A_j)) <= sum_(i = 1)^n (1/2 log (S_i / N) - 1/2 + (x_i^2 + N) / (2 S_i)). $
][
  Apply the lemma on finite partitions with $L(t) := sum_i ell_i (t_i)$ from the lemma on shifted noise.
  Under $mu$, $t_i ~ cal(N)(x_i, N)$, so $integral (t_i - x_i)^2 = N$ and $integral t_i^2 = N + x_i^2$.
  Each $ell_i$ is a polynomial of degree $2$, so it is integrable, and
  $ integral ell_i thin d cal(N)(x_i, N) = 1/2 log (S_i / N) - 1/2 + (x_i^2 + N) / (2 S_i). $
  The integral of $L$ is the sum of these terms.
]

#lemma("Concavity of the logarithm", lean: "Meat.AWGN.sum_log_le_mul_log_div")[
  For $a_1, dots, a_n > 0$,
  $ sum_(i = 1)^n log a_i <= n log ((sum_i a_i) / n). $
][
  For $n = 0$ both sides are $0$.
  Otherwise let $overline(a) > 0$ be the mean.
  Then $log a_i - log overline(a) = log (a_i \/ overline(a)) <= a_i \/ overline(a) - 1$.
  The right side sums to $n - n = 0$.
]

#definition(
  "Decoded channel",
  lean: (
    "Meat.AWGN.Code.measurable_dec_add",
    "Meat.AWGN.Code.channel",
    "Meat.AWGN.Code.channel_apply",
  ),
)[
  For a code $(f, g)$, the map $z |-> g(f(m) + z)$ is measurable.
  The decoded channel is the DMC $V$ from $[k]$ to $[k]$ with
  $ V(j given m) := P(g(f(m) + Z) = j) = mu_m (g^(-1)(j)), $
  where $mu_m$ is the law of $f(m) + Z$.
]

#theorem(
  "Information of the decoded channel",
  lean: "Meat.AWGN.Code.inputMutualInfo_channel_le",
)[
  Let $N > 0$ and let $p$ be the uniform law on $[k]$.
  For the decoded channel of every code of length $n$ with power $P$, $I(p) <= n C(P, N)$.
][
  The uniform law exists only when $k >= 1$.
  Let $P_i := k^(-1) sum_m f(m)_i^2$ and $S_i := P_i + N > 0$.
  Let $rho := times.o_i cal(N)(0, S_i)$ and $r(j) := rho(g^(-1)(j))$.
  These numbers sum to $1$.
  If $r(j) = 0$, then $V(j given m) = 0$ by absolute continuity.
  The golden formula bound and the bound for one codeword give
  $ I(p) <= k^(-1) sum_m sum_i (1/2 log (S_i / N) - 1/2 + (f(m)_i^2 + N) / (2 S_i)) = sum_i 1/2 log (S_i / N), $
  because the average of $f(m)_i^2 + N$ over $m$ is $S_i$.
  The power constraint gives $sum_i P_i <= n P$.
  So the mean of the $S_i \/ N$ is at most $1 + P \/ N$.
  By concavity of the logarithm, $sum_i 1/2 log (S_i \/ N) <= n dot 1/2 log (1 + P \/ N)$.
]

#theorem("Converse for one AWGN code", lean: "Meat.AWGN.Code.one_sub_mul_log_le")[
  Let $N > 0$ and $k >= 1$.
  Every code of length $n$ with $k$ messages and power $P$ satisfies
  $ (1 - overline(lambda)) log k <= n C(P, N) + log 2. $
][
  View the code as a code of length $1$ for the decoded channel, with the identity encoder and the identity decoder.
  Its average error probability is $overline(lambda)$, since its errors are the events $g(f(m) + Z) != m$.
  The converse of the channel chapter gives $I(U; Y) <= I(p)$ for the uniform $p$.
  Fano's inequality gives $H(U given Y) <= log 2 + overline(lambda) log k$.
  With the theorem above, $log k = I(U; Y) + H(U given Y) <= n C(P, N) + log 2 + overline(lambda) log k$.
]

#theorem("AWGN converse", lean: "Meat.AWGN.le_awgnCapacity_of_achievable")[
  Let $P >= 0$ and $N > 0$.
  If $R$ is achievable, then $R <= C(P, N)$.
][
  The proof is the weak converse of the channel chapter, with the converse for one AWGN code.
  Suppose that $R > C(P, N) >= 0$, and let $delta := R - C(P, N)$ and $epsilon := delta \/ (2 R)$.
  For large $n$ there is a code with $k >= e^(n R)$ and $overline(lambda) <= epsilon$.
  Then $(1 - epsilon) n R <= n C(P, N) + log 2$, so $n delta <= 2 log 2$.
  This fails for $n > 2 log 2 \/ delta$.
]

The usual proof uses the maximum entropy theorem to show $I(X^n; Y^n) <= sum_i 1/2 log (1 + P_i \/ N)$.
That route needs mutual information for continuous outputs, which is not defined here.
The route above stays with finite alphabets, and the Gaussian computation is the same.

== AWGN achievability
#source("Meat.Continuous.AWGNAchievability")

Achievability reduces to the coding theorem for a DMC.
Quantizing one channel use is not enough.
If every input amplitude is at most $sqrt(P)$, then every codeword meets the power constraint.
But this is a peak constraint, and its capacity is strictly less than $C(P, N)$.
So the reduction uses blocks of $L$ channel uses.
Each block input is a vector $a(x) in RR^L$ with $sum_l a(x)_l^2 <= L P$, so every codeword made of blocks meets the power constraint.

#definition("Block channel", lean: "Meat.AWGN.blockChannel")[
  Let $L in NN$, let $A$ be a set, let $a : A -> RR^L$, and let $q : RR^L -> B$ with $B$ finite.
  The block channel is the DMC from $A$ to $B$ with
  $ W(b given x) := P(q(a(x) + Z) = b), quad Z ~ cal(N)(0, N)^(times.o L). $
]

#theorem(
  "Achievability by block quantization",
  lean: "Meat.AWGN.achievable_of_lt_inputMutualInfo_blockChannel",
)[
  Let $P >= 0$, $R >= 0$ and $L >= 1$.
  Let $A$ and $B$ be finite, $q$ measurable, and $sum_l a(x)_l^2 <= L P$ for every $x$.
  If $L R < I(p)$ for some $p in Delta(A)$ and the block channel, then $R$ is achievable for power $P$ and noise $N$.
][
  Choose $R_1$ with $R < R_1$ and $L R_1 < I(p)$.
  By achievability for the DMC, the rate $L R_1$ is achievable for the block channel.
  Let $n >= n_0$ and write $n = m L + r$ with $0 <= r < L$.
  The coordinates of $RR^n$ split into $m$ blocks of length $L$ and $r$ extra coordinates.
  A DMC code of length $m$ gives an AWGN code.
  The encoder writes $a(x_t)$ into block $t$ and $0$ into the extra coordinates.
  The decoder applies $q$ to each block and then the DMC decoder.
  Each codeword has power at most $m L P <= n P$.
  The noise law on $RR^n$, mapped to the blocks, is the product of $m$ copies of the noise law on $RR^L$.
  So the block outputs are independent with laws $W(dot given x_t)$, and the AWGN code has the same error probability as the DMC code.
  For rates, $n R <= (m + 1) L R <= m L R_1$ once $m >= R \/ (R_1 - R)$, so $k >= e^(m L R_1) >= e^(n R)$.
  Take $n_0 := L max(N_1, m_1)$, where $N_1$ comes from the DMC and $m_1 > R \/ (R_1 - R)$.
  Then $n >= n_0$ gives $m >= max(N_1, m_1)$.
]

#theorem(
  "Coding theorem from a quantization bound",
  lean: "Meat.AWGN.closure_achievable_eq_of_quantization",
)[
  Let $P >= 0$ and $N > 0$.
  Assume that for every $R$ with $0 <= R < C(P, N)$ there are $L >= 1$, finite sets $A$ and $B$, a map $a : A -> RR^L$ with $sum_l a(x)_l^2 <= L P$, a measurable $q : RR^L -> B$ and $p in Delta(A)$, with $L R < I(p)$ for the block channel.
  Then
  $ overline({R >= 0 : R "achievable"}) = [0, C(P, N)]. $
][
  Combine the assembly theorem, the AWGN converse and achievability by block quantization.
]

The next three sections prove the quantization bound.
The input of each block is a quantized Gaussian vector with power $theta < P$.
If a block has too much power, it is replaced by the zero block.
The information of the block channel is bounded below with a guessed posterior density, so no continuous mutual information is needed.

== A lower bound on information
#source("Meat.Continuous.InfoBound")

The converse bounds $I(p)$ above with a reference law on the outputs.
Achievability needs a bound below.
Here the input of a DMC is a quantized continuous variable $Q(T)$.
The bound uses a function $u(t, b)$ that plays the role of a posterior density of $T$ given the output $b$, relative to the law of $T$.

#lemma("Expectations of quantized variables", lean: "Meat.DMC.integral_comp_eq_sum")[
  Let $mu$ be a finite measure on $T$, let $A$ be finite, let $Q : T -> A$ be measurable and let $g : A -> RR$.
  Then
  $ integral g(Q(t)) thin d mu(t) = sum_(x in A) mu(Q^(-1)(x)) g(x). $
][
  The left side is the integral of $g$ against the push-forward of $mu$ by $Q$.
  That push-forward is a finite measure on a finite set, so its integral is a finite sum.
]

#lemma("Information as a finite sum", lean: "Meat.DMC.inputMutualInfo_eq_sum")[
  Let $W$ be a DMC with finite alphabets, $p in Delta(A)$, and let $q(b) := sum_a p(a) W(b given a)$ be the output law.
  Then
  $ I(p) = sum_(a, b) p(a) W(b given a) (log W(b given a) - log q(b)). $
][
  Write $I(p) = H(Y) - H(Y given X)$.
  The channel chapter gives $H(Y given X) = -sum_(a, b) p(a) W(b given a) log W(b given a)$.
  Also $H(Y) = -sum_(a, b) p(a) W(b given a) log q(b)$, since the output law is the push-forward of the joint law.
]

#theorem(
  "Information bound from a continuous input",
  lean: "Meat.DMC.integral_sum_mul_log_le_inputMutualInfo",
)[
  Let $W$ be a DMC with finite alphabets $A$ and $B$.
  Let $mu$ be a probability measure on $T$, let $Q : T -> A$ be measurable, and let $p(x) := mu(Q^(-1)(x))$.
  Let $u : T times B -> (0, infinity)$ be such that for every $b$, $integral u(t, b) thin d mu(t) = 1$ and $t |-> log u(t, b)$ is $mu$-integrable.
  Then
  $ integral sum_b W(b given Q(t)) log u(t, b) thin d mu(t) <= I(p). $
][
  Let $w(x, b) := W(b given x)$ and let $q$ be the output law.
  Then $q(b) >= p(x) w(x, b)$ for all $x$ and $b$.
  By the two lemmas,
  $ I(p) = integral sum_b w(Q(t), b) (log w(Q(t), b) - log q(b)) thin d mu(t). $
  The set of $t$ with $p(Q(t)) = 0$ is a finite union of sets $Q^(-1)(x)$ of measure $0$.
  Fix $t$ with $p(Q(t)) > 0$ and fix $b$.
  If $w(Q(t), b) > 0$, then $q(b) > 0$, and $log y >= 1 - 1 \/ y$ with $y := w \/ (q(b) u(t, b))$ gives
  $ w (log w - log q(b) - log u(t, b)) >= w - q(b) u(t, b). $
  If $w(Q(t), b) = 0$, the left side is $0$ and the right side is at most $0$.
  Sum over $b$ and integrate.
  The right side integrates to $1 - sum_b q(b) = 0$, because $sum_b w(x, b) = 1$ and $integral u(t, b) thin d mu(t) = 1$.
]

Let $u(t, b)$ be the density of the law of $T$ given the output $b$, relative to $mu$.
Then the left side is the information between $T$ and the output.
The output depends on $T$ only through $Q(T)$, so this information is $I(p)$, and the bound is tight.
For a discrete $X$ with law $p$, this is the bound of Barber and Agakov, $I(X; Y) >= H(X) + bb(E) log v(X given Y)$ for every conditional law $v$, with $u := v \/ p$.

== Quantizers and one channel use
#source("Meat.Continuous.AWGNQuantization")

#definition(
  "Uniform quantizer",
  lean: (
    "Meat.AWGN.Level",
    "Meat.AWGN.level",
    "Meat.AWGN.value",
    "Meat.AWGN.measurable_level",
    "Meat.AWGN.measurable_value_level",
  ),
)[
  For $n in NN$, the levels are the integers $k$ with $|k| <= n^2$.
  The quantizer sends $y in RR$ to the level
  $ k_n (y) := max(-n^2, min(n^2, floor(n y))), $
  and the value of a level $k$ is $k \/ n$.
  Write $Q_n (y) := k_n (y) \/ n$.
  Both $k_n$ and $Q_n$ are measurable.
]

For $n = 0$, Lean divides by $0$, so every value is $0$.

#lemma(
  "Quantizer bounds",
  lean: ("Meat.AWGN.abs_value_le", "Meat.AWGN.abs_value_level_le", "Meat.AWGN.abs_value_level_sub_le"),
)[
  Every level $k$ satisfies $|k \/ n| <= n$.
  Every $y$ satisfies $|Q_n (y)| <= |y| + 1$.
  If $|y| + 1 <= n$, then $|Q_n (y) - y| <= 1 \/ n$.
][
  The first claim is $|k| <= n^2$.
  For the second, $n y - 1 < floor(n y) <= n y$ gives $|floor(n y)| <= n |y| + 1$.
  Clamping to $[-n^2, n^2]$ does not increase the absolute value, so $|Q_n (y)| <= |y| + 1 \/ n$.
  For the third, $n >= 1$ and $|y| <= n - 1$ give $|floor(n y)| <= n^2$.
  So the clamp does nothing, and $0 <= n y - floor(n y) < 1$.
]

#lemma("Quantizers converge", lean: "Meat.AWGN.tendsto_value_level")[
  If $y_n -> y$, then $Q_n (y_n) -> y$.
][
  For large $n$, $|y_n| < |y| + 1$ and $n >= |y| + 2$.
  Then the last quantizer bound gives $|Q_n (y_n) - y_n| <= 1 \/ n$, which tends to $0$.
]

#definition("Gaussian ratio", lean: "Meat.AWGN.postRatio")[
  For $theta, s, m, t in RR$, let $phi_(m, s)$ be the density of $cal(N)(m, s)$ and
  $ u_(theta, s, m)(t) := phi_(m, s)(t) / phi_(0, theta)(t). $
]

#lemma(
  "Properties of the Gaussian ratio",
  lean: (
    "Meat.AWGN.postRatio_pos",
    "Meat.AWGN.log_postRatio",
    "Meat.AWGN.integral_postRatio",
    "Meat.AWGN.integrable_sq_gaussianReal",
    "Meat.AWGN.integral_sq_gaussianReal",
    "Meat.AWGN.integrable_log_postRatio",
  ),
)[
  Let $theta > 0$ and $s > 0$.
  Then $u_(theta, s, m) > 0$ and
  $ log u_(theta, s, m)(t) = 1/2 log (theta / s) + t^2 / (2 theta) - (t - m)^2 / (2 s). $
  Also $integral u_(theta, s, m) thin d cal(N)(0, theta) = 1$, and $log u_(theta, s, m)$ is $cal(N)(0, theta)$-integrable.
  For every $v >= 0$, $t |-> t^2$ is $cal(N)(0, v)$-integrable with integral $v$.
][
  Both densities are positive.
  The formula is the Gaussian log-density lemma applied twice.
  The measure $cal(N)(0, theta)$ has density $phi_(0, theta)$, so the integral of $u_(theta, s, m)$ is $integral phi_(m, s) thin d lambda = 1$.
  The logarithm is a polynomial of degree $2$, and Gaussian measures have finite moments.
  The second moment of $cal(N)(0, v)$ is its variance, since the mean is $0$.
]

Let $X ~ cal(N)(0, theta)$ and $Z ~ cal(N)(0, N)$ be independent, and $Y := X + Z$.
The law of $X$ given $Y = y$ is $cal(N)(alpha y, s)$ with
$ alpha := theta / (theta + N), quad s := (theta N) / (theta + N). $
The gain below uses this posterior, evaluated at the quantized output.

#definition("Gain of one channel use", lean: ("Meat.AWGN.letterRatio", "Meat.AWGN.letterGain"))[
  Let $theta, N in RR$, with $alpha$ and $s$ as above.
  For $n in NN$ and a level $b$, let $u_n (t, b) := u_(theta, s, alpha b \/ n)(t)$.
  The gain is
  $ J_n := integral log u_n (t, k_n (Q_n (t) + z)) thin d (cal(N)(0, theta) times.o cal(N)(0, N))(t, z). $
]

The input is $Q_n (t)$ and the output level is $k_n (Q_n (t) + z)$.
By the theorem of the previous section, $J_n$ is at most the information of this quantized channel with the law of $k_n (T)$ as input.

#lemma(
  "Formula for the gain",
  lean: ("Meat.AWGN.log_letterRatio", "Meat.AWGN.integrable_post_sq", "Meat.AWGN.letterGain_eq"),
)[
  Let $theta > 0$, $N > 0$ and $0 <= alpha' <= 1$.
  The map $(t, z) |-> (t - alpha' Q_n (Q_n (t) + z))^2$ is integrable for $cal(N)(0, theta) times.o cal(N)(0, N)$.
  With $alpha$ and $s$ as above,
  $ J_n = 1/2 log (theta / s) + 1/2 - 1 / (2 s) integral (t - alpha Q_n (Q_n (t) + z))^2 thin d (cal(N)(0, theta) times.o cal(N)(0, N)). $
][
  By the quantizer bounds, $|Q_n (Q_n (t) + z)| <= |t| + |z| + 2$.
  So $|t - alpha' Q_n (Q_n (t) + z)| <= 2 |t| + |z| + 2$, and the square is at most $12 t^2 + 3 z^2 + 12$, which is integrable.
  The formula comes from the logarithm of the Gaussian ratio and $integral t^2 thin d cal(N)(0, theta) = theta$.
]

#lemma(
  "Limits of quantized moments",
  lean: (
    "Meat.AWGN.tendsto_integral_sq_value_level",
    "Meat.AWGN.integral_post_limit",
    "Meat.AWGN.tendsto_integral_post_sq",
  ),
)[
  As $n -> infinity$, $integral Q_n (t)^2 thin d cal(N)(0, theta)(t) -> theta$.
  For $0 <= alpha' <= 1$,
  $ integral (t - alpha' Q_n (Q_n (t) + z))^2 -> integral (t - alpha' (t + z))^2 = (1 - alpha')^2 theta + alpha'^2 N, $
  where the integrals are for $cal(N)(0, theta) times.o cal(N)(0, N)$.
][
  Use dominated convergence.
  The bounds are $2 t^2 + 2$ and $12 t^2 + 3 z^2 + 12$.
  By the convergence lemma, $Q_n (t) -> t$, so $Q_n (t) + z -> t + z$ and $Q_n (Q_n (t) + z) -> t + z$.
  For the limit, expand the square.
  The cross term vanishes, because $integral t z$ is the product of the two means, which are $0$.
]

#theorem("The gain tends to the capacity formula", lean: "Meat.AWGN.tendsto_letterGain")[
  If $theta > 0$ and $N > 0$, then $J_n -> C(theta, N)$.
][
  By the two lemmas, $J_n$ tends to $1/2 log (theta \/ s) + 1/2 - ((1 - alpha)^2 theta + alpha^2 N) \/ (2 s)$.
  A computation gives $(1 - alpha)^2 theta + alpha^2 N = s$ and $theta \/ s = 1 + theta \/ N$.
  So the limit is $1/2 log (1 + theta \/ N)$.
]

One channel use is not enough for the coding theorem.
The input values reach $plus.minus n$, so single letters can break the power constraint.
The next section uses blocks, and the law of large numbers.

== The AWGN coding theorem
#source("Meat.Continuous.AWGNCapacity")

Fix $theta > 0$, $N > 0$, $n$ and a block length $L >= 1$.
The block input is a vector of $L$ levels.
Its value is sent if its power is at most $L P$, and the zero block is sent otherwise.
The input law is the law of the levels of $L$ independent $cal(N)(0, theta)$ variables.

#lemma("Expectations for the block channel", lean: "Meat.AWGN.sum_blockChannel_toReal_mul")[
  For the block channel $W$ with input map $a$ and measurable quantizer $q$, every $x$ and every $g : B -> RR$,
  $ sum_b W(b given x) g(b) = bb(E) g(q(a(x) + Z)), quad Z ~ cal(N)(0, N)^(times.o L). $
][
  The law $W(dot given x)$ is the push-forward of the noise law by $z |-> q(a(x) + z)$.
  Integrate $g$ against it, as in the lemma on quantized variables.
]

#lemma(
  "The gain function",
  lean: (
    "Meat.AWGN.measurable_log_letterRatio",
    "Meat.AWGN.integrable_log_letterRatio_level",
    "Meat.AWGN.abs_log_letterRatio_sub_le",
  ),
)[
  Let $theta > 0$ and $N > 0$.
  For measurable $f$ and $g$, the map $x |-> log u_n (f(x), g(x))$ is measurable.
  The integrand of $J_n$ is integrable.
  For all $t$ and levels $b$ and $b'$,
  $ |log u_n (t, b) - log u_n (t, b')| <= (4 n |t| + 4 n^2) / (2 s). $
][
  The ratio is a quotient of Gaussian densities, which are jointly measurable in the mean and the point.
  Integrability follows from the formula for the gain.
  For the bound, let $c := alpha b \/ n$ and $c' := alpha b' \/ n$, so $|c|, |c'| <= n$.
  The difference is $(c - c')(2 t - c - c') \/ (2 s)$, and $|c - c'| <= 2 n$ and $|2 t - c - c'| <= 2 |t| + 2 n$.
]

#definition(
  "Clipped block input",
  lean: (
    "Meat.AWGN.clipValue",
    "Meat.AWGN.sum_sq_clipValue_le",
    "Meat.AWGN.blockInput",
    "Meat.AWGN.blockQuant",
    "Meat.AWGN.measurable_blockQuant",
    "Meat.AWGN.blockLaw",
    "Meat.AWGN.measurable_clipValue_level",
  ),
)[
  For a vector $x$ of $L$ levels, let
  $ "clip"(x) := (x_l \/ n)_l "if" sum_l (x_l \/ n)^2 <= L P, quad "clip"(x) := 0 "otherwise". $
  If $P >= 0$, then $sum_l "clip"(x)_l^2 <= L P$.
  The input alphabet is the set of vectors of $L$ levels, numbered by $[s']$, where $s'$ is its size.
  The block quantizer is $q(y) := (k_n (y_l))_l$, read in $[s']$.
  It is measurable, and so is $t |-> "clip"(q(t))$.
  The input law is the law of $q(T)$ for $T ~ cal(N)(0, theta)^(times.o L)$.
]

The same quantizer $q$ gives the input law and reads the channel output.

#theorem("Information of the clipped block channel", lean: "Meat.AWGN.integral_blockGain_le")[
  Let $theta > 0$ and $N > 0$, and let $p$ be the input law above.
  Then $I(p)$ for the block channel with input map $"clip"$ and quantizer $q$ is at least
  $ integral integral sum_l log u_n (t_l, k_n ("clip"(q(t))_l + z_l)) thin d cal(N)(0, N)^(times.o L)(z) thin d cal(N)(0, theta)^(times.o L)(t). $
][
  Apply the information bound from a continuous input with $mu := cal(N)(0, theta)^(times.o L)$, $Q := q$ and $u(t, b) := product_l u_n (t_l, b_l)$.
  Each factor is positive and has integral $1$ for $cal(N)(0, theta)$, so the product has integral $1$ for the product measure.
  The logarithm of the product is $sum_l log u_n (t_l, b_l)$.
  Each term is integrable, because the coordinate $t_l$ has law $cal(N)(0, theta)$.
  The lemma on expectations for the block channel turns the sum over outputs into the inner integral over the noise.
]

#definition(
  "Clipped set",
  lean: ("Meat.AWGN.badSet", "Meat.AWGN.measurableSet_badSet", "Meat.AWGN.clipValue_of_notMem_badSet"),
)[
  Let $E := {t in RR^L : L P < sum_l Q_n (t_l)^2}$.
  This set is measurable, and if $t in.not E$, then $"clip"(q(t)) = (Q_n (t_l))_l$.
]

#theorem("Cost of clipping", lean: "Meat.AWGN.integral_blockGain_ge")[
  Let $theta > 0$, $N > 0$ and $c > 0$, and let $mu := cal(N)(0, theta)^(times.o L)$.
  Then the double integral of the theorem above is at least
  $ L J_n - (L ((4 n c + 4 n^2) mu(E) + 4 n theta \/ c)) / (2 s). $
][
  Write $G(t, z)$ for the integrand and $G_0 (t, z) := sum_l g(t_l, z_l)$, where $g$ is the integrand of $J_n$.
  So $G_0$ is $G$ without clipping.
  For $t in.not E$, $G = G_0$.
  For $t in E$, the bound on the gain function gives a difference of at most $(4 n |t_l| + 4 n^2) \/ (2 s)$ in each term.
  Since $|t_l| <= c + t_l^2 \/ c$,
  $ |G(t, z) - G_0 (t, z)| <= sum_l ((4 n c + 4 n^2) bb(1)_E (t) + (4 n \/ c) t_l^2) / (2 s). $
  The right side is integrable for the product of $mu$ and the noise law, and its integral is the subtracted term, since $integral t_l^2 thin d mu = theta$.
  The map $(t, z) |-> (t_l, z_l)$ preserves the measures, so $integral G_0 = L J_n$.
  So $G$ is integrable, and Fubini's theorem turns the double integral into the integral of $G$ for the product measure.
]

#lemma("Chebyshev bound for clipping", lean: "Meat.AWGN.measureReal_badSet_le")[
  Let $L >= 1$, let $m := integral Q_n (t)^2 thin d cal(N)(0, theta)(t)$, and assume $m < P$.
  Let $V$ be the variance of $t |-> Q_n (t)^2$ for $cal(N)(0, theta)$.
  Then
  $ cal(N)(0, theta)^(times.o L)(E) <= V / (L (P - m)^2). $
][
  Let $S(t) := sum_l Q_n (t_l)^2$.
  The function $Q_n^2$ is bounded by $n^2$, so it is square-integrable.
  The coordinates are independent for the product measure, so $S$ has mean $L m$ and variance $L V$.
  If $t in E$, then $S(t) - L m > L (P - m) > 0$.
  Chebyshev's inequality gives the bound $L V \/ (L (P - m))^2$.
]

#theorem("Quantization bound", lean: "Meat.AWGN.exists_blockQuantization")[
  Let $P >= 0$ and $N > 0$.
  For every $R$ with $0 <= R < C(P, N)$ there are $L >= 1$, $s', t' in NN$, a map $a : [s'] -> RR^L$ with $sum_l a(x)_l^2 <= L P$ for every $x$, a measurable $q : RR^L -> [t']$ and $p in Delta([s'])$, with $L R < I(p)$ for the block channel.
][
  Since $C(P, N) > R >= 0$, we have $P > 0$.
  The map $theta |-> C(theta, N)$ is continuous, so there is $theta in (0, P)$ with $R < C(theta, N)$.
  Let $eta := (C(theta, N) - R) \/ 4$.
  By the limit theorems, there is $n$ with $J_n > R + 3 eta$ and $m < P$, with $m$ and $V$ as in the Chebyshev bound.
  Let $c := 4 n theta \/ (2 s eta) + 1$, so that $4 n theta \/ (2 s c) < eta$.
  Let $K := (4 n c + 4 n^2) V \/ (2 s (P - m)^2)$ and $L := ceil(K \/ eta) + 1$, so that $K < L eta$.
  Take the clipped block input, the block quantizer and its input law.
  By the two theorems and the Chebyshev bound,
  $ I(p) >= L J_n - K - L dot (4 n theta) / (2 s c) > L (R + 3 eta) - 2 L eta > L R. $
]

#theorem("AWGN coding theorem", lean: "Meat.AWGN.closure_achievable_eq")[
  Let $P >= 0$ and $N > 0$.
  Then
  $ overline({R >= 0 : R "achievable"}) = [0, C(P, N)]. $
][
  Apply the coding theorem from a quantization bound, with the quantization bound above.
]


== Water filling
#source("Meat.Continuous.WaterFilling")

There are finitely many Gaussian channels in parallel, with noise variances $N_i > 0$ and a total power budget $P >= 0$.
With powers $p_i$, the sum of the capacities is $sum_i C(p_i, N_i)$, where $C(p, N) = 1/2 log(1 + p \/ N)$.
This section solves the optimization over the powers.
The operational capacity of parallel Gaussian channels is proved later in this chapter.

#definition(
  "Rates, allocations and water levels",
  lean: (
    "Meat.WaterFilling.rate",
    "Meat.WaterFilling.fill",
    "Meat.WaterFilling.Feasible",
    "Meat.WaterFilling.capacity",
  ),
)[
  The rate of an allocation $p$ is $r(p) := sum_i C(p_i, N_i)$.
  An allocation is feasible for $P$ if $p_i >= 0$ for all $i$ and $sum_i p_i <= P$.
  The water-filling allocation at level $nu$ is $p_i^nu := max(nu - N_i, 0)$.
  The capacity is $sup {r(p) : p "feasible for" P}$.
]

#lemma(
  "The water-filling allocation",
  lean: (
    "Meat.WaterFilling.fill_nonneg",
    "Meat.WaterFilling.fill_pos_iff",
    "Meat.WaterFilling.add_fill_of_pos",
    "Meat.WaterFilling.fill_eq_zero_iff",
    "Meat.WaterFilling.continuous_sum_fill",
    "Meat.WaterFilling.fill_feasible",
  ),
)[
  $p_i^nu >= 0$, and $p_i^nu > 0$ if and only if $N_i < nu$, in which case $N_i + p_i^nu = nu$.
  $p_i^nu = 0$ if and only if $nu <= N_i$.
  The total $sum_i p_i^nu$ is continuous in $nu$, and if it equals $P$, then $p^nu$ is feasible.
]

#lemma("Existence of the water level", lean: "Meat.WaterFilling.exists_level")[
  If there is at least one channel and $P >= 0$, there is $nu >= min_i N_i$ with $sum_i p_i^nu = P$.
][
  The total is $0$ at $nu = min_i N_i$ and at least $P$ at $nu = min_i N_i + P$.
  Apply the intermediate value theorem.
]

#theorem(
  "Optimality and uniqueness",
  lean: ("Meat.WaterFilling.rate_le_rate_fill", "Meat.WaterFilling.capacity_eq", "Meat.WaterFilling.rate_fill_eq"),
)[
  Let $nu > 0$ with $sum_i p_i^nu = P$.
  Every feasible $p$ has $r(p) <= r(p^nu)$, with strict inequality if $p != p^nu$.
  Hence the capacity is $r(p^nu) = sum_i 1/2 log(max(nu, N_i) \/ N_i)$.
][
  By concavity of the logarithm, $log(N_i + p_i) - log(N_i + p_i^nu) <= (p_i - p_i^nu) \/ (N_i + p_i^nu)$, strictly if $p_i != p_i^nu$.
  If $p_i^nu > 0$, the denominator is $nu$.
  If $p_i^nu = 0$, the right side is $p_i \/ N_i <= p_i \/ nu$.
  Summing, the right sides add to at most $(sum_i p_i - P) \/ nu <= 0$.
]

#theorem("Water filling", lean: "Meat.WaterFilling.exists_waterFilling")[
  If there is at least one channel, $N_i > 0$ for all $i$ and $P >= 0$, then there is a water level $nu > 0$ such that:
  - $p^nu$ is feasible and uses the whole budget;
  - $N_i + p_i^nu = nu$ whenever $p_i^nu > 0$, and $nu <= N_i$ whenever $p_i^nu = 0$;
  - the capacity is $sum_i 1/2 log(max(nu, N_i) \/ N_i)$;
  - $p^nu$ is the only feasible allocation that reaches the capacity.
][
  Combine the existence of the level with optimality and uniqueness.
  The level is positive because it is at least $min_i N_i$.
]

The second item is the Karush-Kuhn-Tucker condition: the channels that get power are filled up to the common level $nu$.

== Gaussian multiple access and broadcast channels
#source("Meat.Continuous.GaussianMultiUser")

This section has the regions of the Gaussian multiple access channel $Y = X_1 + X_2 + Z$ and of the degraded Gaussian broadcast channel $Y_j = X + Z_j$, the algebra of their corner points, and the maximum entropy bounds behind their converses.
The next section proves the operational capacity theorem of the multiple access channel.
The section after it proves the inner bound of the broadcast channel; its converse needs the entropy power inequality and is not formalized.

#lemma(
  "Capacity algebra",
  lean: (
    "Meat.GaussianMultiUser.awgnCapacity_add",
    "Meat.GaussianMultiUser.awgnCapacity_mono",
    "Meat.GaussianMultiUser.awgnCapacity_nonneg'",
  ),
)[
  For $P_1, P_2 >= 0$ and $N > 0$, $C(P_1, N) + C(P_2, P_1 + N) = C(P_1 + P_2, N)$.
  $C(P, N)$ is nonnegative and monotone in $P$.
][
  $(1 + P_1 \/ N)(1 + P_2 \/ (P_1 + N)) = 1 + (P_1 + P_2) \/ N$.
]

#definition("Gaussian multiple access region", lean: "Meat.GaussianMultiUser.macRegion")[
  The region for powers $P_1, P_2$ and noise $N$ is the set of $(R_1, R_2) >= 0$ with
  $ R_1 <= C(P_1, N), quad R_2 <= C(P_2, N), quad R_1 + R_2 <= C(P_1 + P_2, N). $
]

#proposition("Successive decoding corner", lean: "Meat.GaussianMultiUser.corner_mem_macRegion")[
  The point $(C(P_1, N), C(P_2, P_1 + N))$ is in the region and has the largest sum rate $C(P_1 + P_2, N)$.
][
  Receiver decodes user $2$ first, treating user $1$ as noise of power $P_1$, then subtracts it.
  The algebra gives the sum, and $C(P_2, P_1 + N) <= C(P_2, N)$.
]

#definition("Degraded Gaussian broadcast region", lean: "Meat.GaussianMultiUser.bcRegion")[
  For power $P$ and noises $N_1 <= N_2$, the region is the union over $alpha in [0, 1]$ of the sets of $(R_1, R_2) >= 0$ with
  $ R_1 <= C(alpha P, N_1), quad R_2 <= C((1 - alpha) P, alpha P + N_2). $
]

#proposition("Equal noises", lean: "Meat.GaussianMultiUser.bcRegion_sum_of_eq")[
  If $N_1 = N_2 = N$, the boundary point for $alpha$ is in the region and has sum rate $C(P, N)$, the single-user capacity.
][
  The capacity algebra with $P_1 = alpha P$ and $P_2 = (1 - alpha) P$.
]

#theorem(
  "Maximum entropy bounds",
  lean: (
    "Meat.GaussianMultiUser.diffEntropy_le_of_variance_le",
    "Meat.GaussianMultiUser.diffEntropy_mac_le",
    "Meat.GaussianMultiUser.diffEntropy_bc_le",
    "Meat.GaussianMultiUser.sub_gaussian_le_awgnCapacity",
  ),
)[
  If $Y$ has a density, finite second moment and $"Var"(Y) <= v$, then $h(Y) <= 1/2 log(2 pi e v)$.
  If $X_1, X_2$ are independent, $X_1 + X_2$ is independent of $Z$, $"Var"(X_j) <= P_j$ and $"Var"(Z) = N$, then $h(X_1 + X_2 + Z) <= 1/2 log(2 pi e (P_1 + P_2 + N))$.
  If $X$ is independent of $Z$, $"Var"(X) <= P$ and $"Var"(Z) = N$, then $h(X + Z) <= 1/2 log(2 pi e (P + N))$.
  In each case, subtracting the entropy $1/2 log(2 pi e N)$ of the Gaussian noise leaves at most $C(P_1 + P_2, N)$, respectively $C(P, N)$.
][
  The Gaussian maximizes differential entropy for a given variance, and the variances of independent variables add.
  These are the steps that bound $I((X_1, X_2); Y)$ in the converse for the multiple access channel and $I(X; Y_2)$ in the converse for the broadcast channel.
]


== The Gaussian multiple access channel
#source("Meat.Continuous.GaussianMAC")

The two-user Gaussian multiple access channel maps inputs $x_1, x_2 in RR$ to $Y = x_1 + x_2 + Z$, with $Z ~ cal(N)(0, N)$ and $N > 0$, independent across channel uses.
Each codeword of user $j$ must satisfy the power constraint $P_j$.

#definition(
  "Codes and achievable pairs",
  lean: (
    "Meat.GaussianMAC.Code",
    "Meat.GaussianMAC.Code.errorProb",
    "Meat.GaussianMAC.Code.avgError",
    "Meat.GaussianMAC.Achievable",
  ),
)[
  A code of length $n$ with $k_1$ and $k_2$ messages and powers $P_1, P_2$ is a triple $(f_1, f_2, g)$.
  The encoder $f_j : [k_j] -> RR^n$ satisfies $sum_i f_j (m)_i^2 <= n P_j$ for every $m$.
  The decoder $g : RR^n -> [k_1] times [k_2]$ is measurable.
  The error probability of $(m_1, m_2)$ is
  $ lambda_(m_1 m_2) := cal(N)(0, N)^(times.o n) ({z : g(f_1 (m_1) + f_2 (m_2) + z) != (m_1, m_2)}), $
  and $overline(lambda) := (k_1 k_2)^(-1) sum lambda_(m_1 m_2)$.
  A pair $(R_1, R_2)$ is achievable if for every $epsilon > 0$ there is $n_0$ such that for every $n >= n_0$ there are $k_j >= e^(n R_j)$ and a code of length $n$ with $overline(lambda) <= epsilon$.
]

#lemma(
  "Swapping the users",
  lean: (
    "Meat.GaussianMAC.Code.swap",
    "Meat.GaussianMAC.Code.errorProb_swap",
    "Meat.GaussianMAC.Code.avgError_swap",
    "Meat.GaussianMAC.Achievable.swap",
  ),
)[
  Exchanging the encoders and the two components of the decoder gives a code for powers $(P_2, P_1)$ with the same error probabilities.
  So $(R_1, R_2)$ is achievable for $(P_1, P_2)$ if and only if $(R_2, R_1)$ is achievable for $(P_2, P_1)$.
][
  Addition is commutative, and the sum over message pairs is invariant under the swap.
]

#lemma(
  "A genie gives a single-user code",
  lean: (
    "Meat.GaussianMAC.Code.exists_awgnCode",
    "Meat.GaussianMAC.Achievable.awgn₁",
    "Meat.GaussianMAC.Achievable.awgn₂",
  ),
)[
  If $k_2 > 0$, every code has an AWGN code for power $P_1$ with $k_1$ messages and average error at most $overline(lambda)$.
  So if $(R_1, R_2)$ is achievable, then $R_1$ is achievable for the AWGN channel with power $P_1$, and $R_2$ for power $P_2$.
][
  Choose $m_2$ minimizing $sum_(m_1) lambda_(m_1 m_2)$, so $k_1^(-1) sum_(m_1) lambda_(m_1 m_2) <= overline(lambda)$.
  Keep $f_1$ and decode $y$ by the first component of $g(y + f_2 (m_2))$.
  An error of this decoder at $m_1$ is an error of $g$ at $(m_1, m_2)$.
  The second claim follows by swapping the users.
]

#theorem("Converse for the sum rate", lean: "Meat.GaussianMAC.Code.one_sub_mul_log_le")[
  If $N > 0$ and $k_1, k_2 > 0$, every code satisfies
  $ (1 - overline(lambda)) (log k_1 + log k_2) <= n C(P_1 + P_2, N) + log 2. $
][
  Let $mu_j := k_j^(-1) sum_m f_j (m)$ and consider the single-user code with messages $(m_1, m_2)$, codewords $f_1 (m_1) - mu_1 + f_2 (m_2) - mu_2$ and decoder $y |-> g(y + mu_1 + mu_2)$.
  It has the same error probabilities.
  Its codewords may break the power constraint, but their average power is at most $n (P_1 + P_2)$.
  Indeed, the cross term $sum_(m_1, m_2) chevron.l f_1 (m_1) - mu_1, f_2 (m_2) - mu_2 chevron.r$ vanishes, and centering does not increase the second moment.
  The proof of the converse for one AWGN code uses only the average power, so it applies to this code with power $P_1 + P_2$.
]

#theorem(
  "Converse",
  lean: ("Meat.GaussianMAC.Achievable.add_le", "Meat.GaussianMAC.Achievable.mem_macRegion"),
)[
  Let $P_1, P_2 >= 0$ and $N > 0$.
  If $(R_1, R_2)$ is achievable, then $R_1 + R_2 <= C(P_1 + P_2, N)$.
  If also $R_1, R_2 >= 0$, then $(R_1, R_2)$ is in the Gaussian multiple access region.
][
  The sum bound follows from the previous theorem as the AWGN converse follows from the converse for one code: let $n -> infinity$ with $overline(lambda) <= epsilon$.
  The single-rate bounds are the AWGN converse applied to the genie codes.
]

#source("Meat.Continuous.GaussianMACQuantization")

The achievability proof quantizes both inputs as in the AWGN coding theorem.
User $1$ sends the clipped levels of $L$ independent $cal(N)(0, theta_1)$ variables and user $2$ those of $cal(N)(0, theta_2)$ variables.
The new ingredient is the information that the output carries about user $2$ when user $1$ is treated as noise.
For this, the gain uses the Gaussian posterior for the noise variance $theta_1 + N$, evaluated at the quantized output.

#lemma(
  "Bound on the gain function",
  lean: ("Meat.GaussianMAC.abs_log_letterRatio_le", "Meat.GaussianMAC.integrable_log_letterRatio"),
)[
  Let $theta > 0$, $N > 0$, and $u_n$ and $s$ as in the gain of one channel use.
  For every $t$ and level $b$,
  $ |log u_n (t, b)| <= |1/2 log(theta \/ s)| + n^2 / s + (1 / (2 theta) + 1 / s) t^2. $
  So $x |-> log u_n (f(x), g(x))$ is integrable for every finite measure when $f$ and $g$ are measurable and $f^2$ is integrable.
][
  The level value $alpha b \/ n$ has absolute value at most $n$, so $(t - alpha b \/ n)^2 <= 2 t^2 + 2 n^2$.
  Insert this in the formula for $log u_n$.
]

#definition("Gain with interference", lean: "Meat.GaussianMAC.tinGain")[
  Let $u'_n$ be the function $u_n$ for the variances $theta_2$ and $theta_1 + N$.
  For independent $T_1 ~ cal(N)(0, theta_1)$, $T_2 ~ cal(N)(0, theta_2)$ and $Z ~ cal(N)(0, N)$,
  $ J'_n := bb(E) log u'_n (T_2, k_n (Q_n (T_1) + Q_n (T_2) + Z)). $
]

#theorem(
  "The gain with interference tends to the capacity formula",
  lean: ("Meat.GaussianMAC.tinGain_eq", "Meat.GaussianMAC.tendsto_tinGain"),
)[
  If $theta_1, theta_2, N > 0$, then $J'_n -> C(theta_2, theta_1 + N)$.
][
  As for one channel use, with $alpha := theta_2 \/ (theta_2 + theta_1 + N)$ and $s := theta_2 (theta_1 + N) \/ (theta_2 + theta_1 + N)$,
  $ J'_n = 1/2 log (theta_2 / s) + 1/2 - 1 / (2 s) bb(E) (T_2 - alpha Q_n (Q_n (T_1) + Q_n (T_2) + Z))^2. $
  The square is at most $4 T_1^2 + 16 T_2^2 + 4 Z^2 + 36$, so dominated convergence applies.
  The limit is $bb(E) (T_2 - alpha (T_1 + T_2 + Z))^2 = (1 - alpha)^2 theta_2 + alpha^2 (theta_1 + N)$, since the cross terms have mean $0$.
  The rest is the computation for one channel use with noise variance $theta_1 + N$.
]

#lemma("Clipping both users", lean: "Meat.GaussianMAC.integral_tinGain_ge")[
  Let $theta_1, theta_2, N > 0$, $c > 0$, and let $beta_j$ be the probability that the unclipped block of user $j$ has power above $L P_j$.
  The expectation over $T_1, T_2 ~$ i.i.d. Gaussian blocks and the noise of
  $ sum_(l = 1)^L log u'_n (T_(2 l), k_n (x_1 (T_1)_l + x_2 (T_2)_l + Z_l)), $
  where $x_j$ is the clipped block input of user $j$, is at least
  $ L J'_n - L ((4 n c + 4 n^2)(beta_1 + beta_2) + 4 n theta_2 \/ c) / (2 s). $
][
  As for one user.
  If neither block is clipped, the summands are i.i.d. with mean $J'_n$.
  Otherwise, the difference of the logarithms is at most $(4 n |t| + 4 n^2) \/ (2 s)$, and $|t| <= c + t^2 \/ c$.
]

#source("Meat.Continuous.GaussianMACAchievability")

#theorem("Reduction to a discrete channel", lean: "Meat.GaussianMAC.achievable_of_lt_blockChannel")[
  Let $P_1, P_2, R_1, R_2 >= 0$, $L >= 1$, finite input alphabets with maps $a_j : A_j -> RR^L$ of power at most $L P_j$, and a measurable quantizer $q$ of $RR^L$ to a finite set.
  Let $W$ be the discrete multiple access channel $(x_1, x_2) |-> q(a_1 (x_1) + a_2 (x_2) + Z)$ and let $p_1, p_2$ be input laws.
  If $L R_1 < I(X_1; Y | X_2)$, $L R_2 < I(X_2; Y | X_1)$ and $L (R_1 + R_2) < I(X_1, X_2; Y)$, then $(R_1, R_2)$ is achievable.
][
  By the discrete theorem, $(L (R_1 + delta), L (R_2 + delta))$ is achievable for $W$ for a small $delta > 0$.
  A code of length $m$ for $W$ gives a Gaussian code of length $n = m L + r$ with $r < L$: send $a_j$ blockwise, pad with zeros and quantize each block.
  The error probabilities agree.
  For large $m$, $n R_j <= m L (R_j + delta)$.
]

#theorem("Achievability", lean: "Meat.GaussianMAC.achievable_of_lt")[
  Let $P_1, P_2, N > 0$ and $R_1, R_2 >= 0$ with $R_1 < C(P_1, N)$, $R_2 < C(P_2, N)$ and $R_1 + R_2 < C(P_1 + P_2, N)$.
  Then $(R_1, R_2)$ is achievable.
][
  Choose $tau < 1$ such that the three inequalities hold for $theta_j := tau P_j$.
  Use the block inputs of the AWGN coding theorem for both users, and the output quantizer
  $ y |-> (k_n (y), (k_n (y - a_2 (x_2)))_(x_2), (k_n (y - a_1 (x_1)))_(x_1)). $
  The extra components let the variational lower bound on information subtract the other user.
  This gives $I(X_1; Y | X_2) = I(X_1; X_2, Y) >= $ the single-user expectation for user $1$, the same for user $2$, and $I(X_1, X_2; Y) >=$ the expectation of the clipping lemma plus the single-user expectation for user $1$.
  For the last bound, the test function is the product of $u'_n$ at the first component and of the user-$1$ test function at the component indexed by the level of user $2$, which still integrates to $1$.
  By the limits of $J_n$ and $J'_n$, and by Chebyshev's inequality for the clipping probabilities, the three informations exceed $L (C(theta_1, N) - 2 eta)$, $L (C(theta_2, N) - 2 eta)$ and $L (C(theta_1, N) + C(theta_2, theta_1 + N) - 4 eta)$ for suitable $n$, $c$ and $L$.
  Since $C(theta_1, N) + C(theta_2, theta_1 + N) = C(theta_1 + theta_2, N)$, the reduction applies.
]

#lemma(
  "One silent user",
  lean: ("Meat.GaussianMAC.achievable_zero_left", "Meat.GaussianMAC.achievable_zero_right"),
)[
  If $P_1 >= 0$ and $R$ is achievable for the AWGN channel with power $P_2$, then $(0, R)$ is achievable.
  Symmetrically for user $1$.
][
  User $1$ has one message and sends the zero codeword.
]

#theorem("Gaussian multiple access coding theorem", lean: "Meat.GaussianMAC.closure_achievable_eq")[
  If $P_1, P_2 >= 0$ and $N > 0$, the closure of the set of achievable pairs $(R_1, R_2) >= 0$ is the Gaussian multiple access region.
][
  The region is closed and contains every achievable pair by the converse.
  If $P_1 = 0$, the region is ${0} times [0, C(P_2, N)]$, and the AWGN coding theorem with the silent user lemma gives it.
  The case $P_2 = 0$ is symmetric.
  If $P_1, P_2 > 0$, then $C(P_j, N) > 0$, and for a point $R$ of the region and $eta > 0$ the point $(max(R_1 - eta \/ 2, 0), max(R_2 - eta \/ 2, 0))$ satisfies the strict inequalities of the achievability theorem.
]


== The degraded Gaussian broadcast channel
#source("Meat.Continuous.GaussianBroadcast")

The Gaussian broadcast channel maps an input $x in RR$ to $Y_1 = x + Z_1$ and $Y_2 = x + Z_2$, with $Z_j ~ cal(N)(0, N_j)$, independent of each other and across channel uses.
The codewords satisfy the power constraint $P$.
The error event depends only on the marginal laws of the two outputs, so the independence of $Z_1$ and $Z_2$ is no restriction.

#definition(
  "Codes and achievable pairs",
  lean: (
    "Meat.GaussianBroadcast.Code",
    "Meat.GaussianBroadcast.Code.errorProb",
    "Meat.GaussianBroadcast.Code.avgError",
    "Meat.GaussianBroadcast.Achievable",
  ),
)[
  A code of length $n$ with $k_1$ and $k_2$ messages and power $P$ is a triple $(f, g_1, g_2)$.
  The encoder $f : [k_1] times [k_2] -> RR^n$ satisfies $sum_i f(m)_i^2 <= n P$ for every $m$.
  The decoders $g_j : RR^n -> [k_j]$ are measurable.
  The error probability of $m = (m_1, m_2)$ is
  $ lambda_m := (cal(N)(0, N_1)^(times.o n) times.o cal(N)(0, N_2)^(times.o n)) ({(z_1, z_2) : (g_1 (f(m) + z_1), g_2 (f(m) + z_2)) != m}), $
  and $overline(lambda) := (k_1 k_2)^(-1) sum_m lambda_m$.
  Achievable pairs are defined as for the multiple access channel.
]

#lemma("Union bound", lean: "Meat.GaussianBroadcast.Code.errorProb_le")[
  $lambda_m$ is at most the probability that $g_1$ errs on $m_1$ plus the probability that $g_2$ errs on $m_2$.
][
  The error event is contained in the union of the two cylinders, whose measures are the two single-receiver error probabilities.
]

#lemma(
  "One silent user",
  lean: ("Meat.GaussianBroadcast.achievable_zero_left", "Meat.GaussianBroadcast.achievable_zero_right"),
)[
  If $R$ is achievable for the AWGN channel with power $P$ and noise $N_2$, then $(0, R)$ is achievable.
  If $R$ is achievable for noise $N_1$, then $(R, 0)$ is achievable.
][
  The silent user has one message and a constant decoder, which never errs.
  By the union bound, the error probability is at most that of the AWGN code.
]

#source("Meat.Continuous.GaussianBroadcastQuantization")

The inner bound uses superposition coding.
User $2$ gets the cloud: the levels of $L$ independent $cal(N)(0, theta_2)$ variables.
User $1$ gets the satellite: the levels of $L$ independent $cal(N)(0, theta_1)$ variables.
The sum is sent if its power is at most $L P$, and the zero block is sent otherwise.
Clipping the sum, not each part, keeps the power constraint for every codeword.

#definition(
  "Clipped superposition",
  lean: (
    "Meat.GaussianBroadcast.sumClip",
    "Meat.GaussianBroadcast.sum_sq_sumClip_le",
    "Meat.GaussianBroadcast.sumSignal",
    "Meat.GaussianBroadcast.measurable_sumSignal",
    "Meat.GaussianBroadcast.sumBad",
    "Meat.GaussianBroadcast.measurableSet_sumBad",
    "Meat.GaussianBroadcast.sumSignal_of_notMem",
  ),
)[
  For $w in RR^L$, $"clip"_P (w) := w$ if $sum_l w_l^2 <= L P$, and $0$ otherwise.
  Its power is at most $L P$ when $P >= 0$.
  For blocks $t_1, t_2 in RR^L$, the signal is $S(t_1, t_2) := "clip"_P (Q_n (t_1) + Q_n (t_2))$, with $Q_n$ applied to each letter.
  The bad set is the set of $(t_1, t_2)$ where the clipping acts, and outside it $S(t_1, t_2) = Q_n (t_1) + Q_n (t_2)$.
]

#lemma(
  "Clipping is rare",
  lean: "Meat.GaussianBroadcast.eventually_tendsto_sumBad",
)[
  If $theta_1, theta_2 > 0$ and $theta_1 + theta_2 < P$, then for all large $n$ the probability of the bad set tends to $0$ as $L -> infinity$.
][
  By dominated convergence with the bound $3 a^2 + 3 b^2 + 12$, $bb(E) (Q_n (T_1) + Q_n (T_2))^2 -> bb(E) (T_1 + T_2)^2 = theta_1 + theta_2 < P$.
  Fix such an $n$.
  The letters of $(T_1, T_2)$ are i.i.d., so Chebyshev's inequality bounds the probability of the bad set by $"Var" \/ (L (P - m_n)^2)$, as in the AWGN coding theorem.
]

#lemma(
  "Gains of the two receivers",
  lean: ("Meat.GaussianBroadcast.integral_satGain_ge", "Meat.GaussianBroadcast.integral_cloudGain_ge"),
)[
  Let $theta_1, theta_2, N > 0$, $c > 0$, and let $beta$ be the probability of the bad set.
  For the satellite, with $u_n$ the function for $theta_1$ and $N$,
  $ bb(E) sum_l log u_n (T_(1 l), k_n (S(T_1, T_2)_l - Q_n (T_(2 l)) + Z_l)) >= L J_n - L ((4 n c + 4 n^2) beta + 4 n theta_1 \/ c) / (2 s). $
  For the cloud, with $u'_n$ the function for $theta_2$ and $theta_1 + N$ and $s'$ its variance,
  $ bb(E) sum_l log u'_n (T_(2 l), k_n (S(T_1, T_2)_l + Z_l)) >= L J'_n - L ((4 n c + 4 n^2) beta + 4 n theta_2 \/ c) / (2 s'). $
][
  As for the multiple access channel.
  Outside the bad set the summands are i.i.d. with means $J_n$ and $J'_n$.
  On the bad set, the difference of the logarithms is at most $(4 n |t| + 4 n^2) \/ (2 s)$ and $|t| <= c + t^2 \/ c$.
]

#source("Meat.Continuous.GaussianBroadcastAchievability")

#definition(
  "Discrete broadcast block channel",
  lean: (
    "Meat.GaussianBroadcast.blockChannel₂",
    "Meat.GaussianBroadcast.map_fst_blockChannel₂",
    "Meat.GaussianBroadcast.map_snd_blockChannel₂",
  ),
)[
  For a finite alphabet $A$ with a map $a : A -> RR^L$ and measurable quantizers $q_1, q_2$, the broadcast channel sends $x$ to the independent pair $(q_1 (a(x) + Z_1), q_2 (a(x) + Z_2))$.
  Its marginals are the block channels for the two receivers.
]

#theorem("Reduction to a discrete channel", lean: "Meat.GaussianBroadcast.achievable_of_lt_blockChannel")[
  Let $P, R_1, R_2 >= 0$, $L >= 1$, $a$ of power at most $L P$, and let $p_U$ and $p_(X | U)$ be a cloud law and a satellite channel for this discrete broadcast channel.
  If $L R_1 < I(X; Y_1 | U)$, $L R_2 < I(U; Y_2)$ and $L (R_1 + R_2) < I(X; Y_1)$, then $(R_1, R_2)$ is achievable.
][
  The superposition coding theorem gives codes of length $m$ for rates $L (R_j + delta)$.
  Send them blockwise as for the multiple access channel.
  By the union bound, the Gaussian error is at most the sum of the two single-receiver errors of the discrete code.
  Each is at most the discrete error, so the average error is at most twice the discrete one.
]

#theorem("Superposition coding", lean: "Meat.GaussianBroadcast.achievable_of_lt")[
  Let $theta_1, theta_2 > 0$ with $theta_1 + theta_2 < P$, $0 < N_1 <= N_2$ and $R_1, R_2 >= 0$.
  If $R_1 < C(theta_1, N_1)$ and $R_2 < C(theta_2, theta_1 + N_2)$, then $(R_1, R_2)$ is achievable.
][
  Use the clipped superposition with the cloud $U$ of user $2$ and the satellite of user $1$.
  Receiver $1$ quantizes $y$ and also $y - Q_n (u)$ for every cloud block $u$.
  The variational lower bound on information gives three bounds.
  First, $I(X; Y_1 | U) = I(V; U, Y_1)$, where $V$ is the satellite, is at least the satellite expectation of the previous lemma with noise $N_1$.
  This uses the independence of $U$ and $V$, and that $(V, U)$ given $U$ carries the same information as $V$.
  Second, $I(U; Y_2)$ is at least the cloud expectation with noise $N_2$.
  Third, $I(X; Y_1)$ is at least the sum of the cloud and satellite expectations with noise $N_1$, with the product test function of the multiple access proof.
  The first two bounds average over the other user's block, which is undone with Fubini's theorem.
  By the limits of $J_n$ and $J'_n$, and since clipping is rare, the bounds exceed $L (C(theta_1, N_1) - 2 eta)$, $L (C(theta_2, theta_1 + N_2) - 2 eta)$ and $L (C(theta_1, N_1) + C(theta_2, theta_1 + N_1) - 4 eta)$.
  Since $N_1 <= N_2$, $C(theta_2, theta_1 + N_2) <= C(theta_2, theta_1 + N_1)$, so the reduction applies.
]

#theorem("Inner bound for the degraded Gaussian broadcast channel", lean: "Meat.GaussianBroadcast.bcRegion_subset_closure")[
  If $P >= 0$ and $0 < N_1 <= N_2$, the degraded Gaussian broadcast region is contained in the closure of the set of achievable pairs $(R_1, R_2) >= 0$.
][
  Let $(R_1, R_2)$ be in the set for $alpha$.
  If $alpha P = 0$, then $R_1 = 0$ and $R_2 <= C(P, N_2)$, and the AWGN coding theorem with a silent user gives the point.
  If $(1 - alpha) P = 0$, the same holds with the users exchanged.
  Otherwise, for $eta > 0$ choose $tau < 1$ close to $1$ and apply superposition coding with $theta_1 = tau alpha P$ and $theta_2 = tau (1 - alpha) P$ to $(max(R_1 - eta \/ 2, 0), max(R_2 - eta \/ 2, 0))$.
  Both capacities are continuous in $tau$ and positive for $tau > 0$.
]

The converse, and so the equality of the closure with the region, needs the entropy power inequality.

== Dirty-paper coding
#source("Meat.Continuous.DirtyPaper")

The dirty-paper channel maps an input $x in RR$ to $Y = x + S + Z$.
The interference $S ~ cal(N)(0, Q)$ and the noise $Z ~ cal(N)(0, N)$ are independent, and independent across channel uses.
The encoder knows the whole interference sequence before it sends, and the decoder does not see it.
The codewords satisfy the power constraint $P$ for every message and every interference sequence.
Costa (1983) showed that the interference costs nothing: the capacity is the AWGN capacity $C(P, N)$, whatever $Q$ is.
In Lean, a negative variance $Q$ is replaced by $0$, and the theorems hold for every $Q in RR$.

#definition(
  "Codes with known interference",
  lean: (
    "Meat.DirtyPaper.Code",
    "Meat.DirtyPaper.Code.errorProb",
    "Meat.DirtyPaper.Code.avgError",
  ),
)[
  A code of length $n$ with $k$ messages and power $P$ is a pair $(f, g)$.
  The encoder $f : [k] times RR^n -> RR^n$ is measurable in the interference for each message, and satisfies $sum_(i = 1)^n f(m, s)_i^2 <= n P$ for every $m$ and $s$.
  The decoder $g : RR^n -> [k]$ is measurable.
  The error probability of message $m$ is
  $ lambda_m := integral cal(N)(0, N)^(times.o n) ({z : g(f(m, s) + s + z) != m}) thin d cal(N)(0, Q)^(times.o n)(s), $
  and the average error probability is $overline(lambda) := k^(-1) sum_m lambda_m$.
]

#definition("Achievable rate", lean: "Meat.DirtyPaper.Achievable")[
  A rate $R in RR$ is achievable for power $P$, interference $Q$ and noise $N$ if for every $epsilon > 0$ there exists $n_0 in NN$ such that for every $n >= n_0$ there exist $k in NN$ with $k >= e^(n R)$ and a code of length $n$ with $k$ messages, power $P$ and $overline(lambda) <= epsilon$.
]

#lemma(
  "Fixing the interference",
  lean: (
    "Meat.DirtyPaper.Code.toAWGN",
    "Meat.DirtyPaper.Code.exists_avgError_toAWGN_le",
    "Meat.DirtyPaper.Achievable.awgn",
  ),
)[
  For a code $(f, g)$ and $s in RR^n$, the pair $(f(dot, s), y |-> g(y + s))$ is an AWGN code with the same power.
  Some $s$ gives an AWGN code whose average error is at most $overline(lambda)$.
  So every rate achievable with known interference is achievable for the AWGN channel with power $P$ and noise $N$.
][
  The error probability of message $m$ for the AWGN code at $s$ is the inner measure in the definition of $lambda_m$.
  The set ${(s, z) : g(f(m, s) + s + z) != m}$ is measurable, so this inner measure is measurable in $s$.
  By Tonelli's theorem, $overline(lambda)$ is the integral over $s$ of the average error of the AWGN code at $s$.
  A measurable function takes a value at most its integral against a probability measure at some point.
]

#theorem(
  "Converse with known interference",
  lean: "Meat.DirtyPaper.le_awgnCapacity_of_achievable",
)[
  If $P >= 0$, $N > 0$ and $R$ is achievable for $P$, $Q$ and $N$, then $R <= C(P, N)$.
][
  By the previous lemma, $R$ is achievable for the AWGN channel, and the AWGN converse applies.
]

#lemma("Rate zero", lean: "Meat.DirtyPaper.achievable_zero")[
  If $P >= 0$, then $R = 0$ is achievable for every $Q$ and $N$.
][
  Take $k = 1$, the zero encoder and the constant decoder, which never errs.
]

#theorem(
  "Assembly of the dirty-paper theorem",
  lean: "Meat.DirtyPaper.closure_achievable_eq_of",
)[
  Let $P >= 0$ and $N > 0$.
  Assume that every $R$ with $0 <= R < C(P, N)$ is achievable for $P$, $Q$ and $N$.
  Then
  $ overline({R >= 0 : R "achievable"}) = [0, C(P, N)]. $
][
  The converse puts the set inside $[0, C(P, N)]$.
  The rest is as for the AWGN channel, with the lemma on rate zero.
]

#source("Meat.Continuous.DirtyPaperAchievability")

Achievability reduces to a discrete channel with state, as the AWGN proof reduces to a discrete channel.
A block of $L$ channel uses becomes one letter.
The state of a block is a quantization of its interference, and the encoder sees only this quantized state.

#definition(
  "Block channel with state",
  lean: (
    "Meat.DirtyPaper.letter",
    "Meat.DirtyPaper.stateLaw",
    "Meat.DirtyPaper.chan",
    "Meat.DirtyPaper.stateLaw_mul_chan",
  ),
)[
  Let $Sigma$, $A$ and $B$ be finite sets, let $q_S : RR^L -> Sigma$ and $q : RR^L -> B$ be measurable, and let $a : A -> RR^L$.
  Let $S ~ cal(N)(0, Q)^(times.o L)$ and $Z ~ cal(N)(0, N)^(times.o L)$ be independent.
  The letter law is the law on $Sigma times B^A$ of the pair $(q_S (S), F)$ with $F(x) := q(a(x) + S + Z)$.
  The state law $p_S$ is its first marginal.
  The channel $W(y given x, sigma)$ is the conditional probability of $F(x) = y$ given $q_S (S) = sigma$ when $p_S (sigma) > 0$, and the law of $F(x)$ otherwise.
  So for all $x$, $sigma$ and $y$,
  $ p_S (sigma) W(y given x, sigma) = sum_(f : f(x) = y) P(q_S (S) = sigma, F = f). $
]

#definition(
  "Codes from block codes",
  lean: ("Meat.DirtyPaper.toCode", "Meat.DirtyPaper.avgError_toCode"),
)[
  Let $P >= 0$, $n = m L + r$, let $a$ have power $sum_l a(x)_l^2 <= L P$ for every $x$, and let $(f_0, g_0)$ be a code of length $m$ for the channel $W$ with state law $p_S$.
  The code of length $n$ cuts $s$ into $m$ blocks of length $L$ and drops the last $r$ entries.
  It sends $a(f_0 (i, sigma)_t)$ in block $t$, where $sigma_t := q_S$ of block $t$ of $s$, and zeros in the last $r$ entries.
  The decoder applies $q$ to each block of $y$ and then $g_0$.
  Its power is at most $m L P <= n P$, and its average error equals the average error of $(f_0, g_0)$.
]

The equality of errors comes from the block structure of the Gaussian laws.
The blocks of $cal(N)(0, v)^(times.o n)$ are i.i.d. with law $cal(N)(0, v)^(times.o L)$.
So the letters $(q_S (S_t), F_t)$ of the $m$ blocks are i.i.d. with the letter law.
The error event depends only on these letters, and summing over the functions $F_t$ with $F_t (x_t) = y_t$ gives the product of the channel by the last identity.

#theorem(
  "Reduction to a discrete channel with state",
  lean: "Meat.DirtyPaper.achievable_of_lt_infoCapacity_block",
)[
  Let $P, R >= 0$, $L >= 1$, $A$ nonempty, and let $a$ have power at most $L P$.
  If $L R < C_"GP"$ for the block channel $W$ with state law $p_S$, then $R$ is achievable for $P$, $Q$ and $N$.
][
  Choose $R_1$ with $R < R_1 < C_"GP" \/ L$.
  Gelfand-Pinsker achievability gives $n_1$ and codes of every length $m >= n_1$ with rate $L R_1$ and error at most $epsilon$.
  Choose $m_1 > R \/ (R_1 - R)$.
  For $n >= L max(n_1, m_1)$, let $m := floor(n \/ L)$ and $r := n - m L < L$, and use the code from the block code of length $m$.
  Since $R <= m (R_1 - R)$, $n R <= m L R + L R <= m L R_1$, so the number of messages is at least $e^(n R)$.
]

#theorem(
  "Dirty-paper theorem from a block quantization",
  lean: "Meat.DirtyPaper.closure_achievable_eq_of_quantization",
)[
  Let $P >= 0$ and $N > 0$.
  Assume that for every $R$ with $0 <= R < C(P, N)$ there exist $L >= 1$, finite sets $Sigma$, $A$, $B$ with $A$ nonempty, measurable $q_S$ and $q$, and $a$ of power at most $L P$, with $L R < C_"GP"$ for the block channel.
  Then
  $ overline({R >= 0 : R "achievable"}) = [0, C(P, N)]. $
][
  Combine the reduction with the assembly of the dirty-paper theorem.
]

#source("Meat.Continuous.DirtyPaperQuantization")

The AWGN proof bounds the information of the quantized channel below with a test function.
For a channel with state the objective is $I(U ; Y) - I(U ; S)$, and the same idea needs one more factor for the state.

#lemma(
  "A lower bound on the Gelfand-Pinsker objective",
  lean: "Meat.DirtyPaper.integral_log_le_mutualInfo_sub",
)[
  Let $nu$ be a probability measure on $Omega$, and let $S$, $U$ and $Y$ be measurable maps into finite sets.
  Let $g : Omega -> (0, infinity)$ be measurable with $log g$ integrable.
  Let $Psi(u, y) >= 0$ with $sum_u Psi(u, y) <= 1$ for every $y$.
  Assume that for all $sigma$, $u$ and $y$,
  $ (integral_({S = sigma, U = u, Y = y}) g thin d nu) dot nu(U = u, S = sigma) <= Psi(u, y) dot nu(S = sigma, U = u, Y = y) dot nu(S = sigma). $
  Then
  $ integral log g thin d nu <= I(U ; Y) - I(U ; S). $
][
  Let $F := log p(U, Y) - log p(Y) - log p(U, S) + log p(S)$, so that $integral F thin d nu = I(U ; Y) - I(U ; S)$.
  Let $k := g dot p(U, S) p(Y) \/ (p(S) p(U, Y))$.
  Almost surely all four probabilities are positive, and $log g = F + log k <= F + k - 1$.
  On the cell $(sigma, u, y)$, the assumption gives $integral k <= Psi(u, y) p(sigma, u, y) p(y) \/ p(u, y)$.
  Summing over $sigma$ gives at most $Psi(u, y) p(y)$, then summing over $u$ and $y$ gives at most $sum_y p(y) = 1$.
  So $integral (k - 1) thin d nu <= 0$.
]

#theorem(
  "Costa's dirty-paper theorem",
  lean: "Meat.DirtyPaper.closure_achievable_eq",
)[
  Let $P >= 0$ and $N > 0$.
  For every $Q$,
  $ overline({R >= 0 : R "achievable for" P, Q, N}) = [0, C(P, N)] = [0, 1/2 log(1 + P / N)]. $
][
  We check the assumption of the dirty-paper theorem from a block quantization.
  Let $0 <= R < C(P, N)$, so $P > 0$.
  By continuity, choose $0 < theta < P$ with $R < C(theta, N)$, and let $alpha := theta \/ (theta + N)$ and $s := theta N \/ (theta + N)$.
  Costa's auxiliary is $U := T + alpha S$ with $T ~ cal(N)(0, theta)$ independent of $S$, and the input is $X := U - alpha S$.

  Quantize letter by letter with $Q_n$ from the AWGN proof.
  Let $hat(S) := Q_n (S)$.
  The state is the vector of levels of $S$, and the output quantizer $q$ is the vector of levels of $y$.
  The input alphabet is the set of pairs $(u, sigma)$ of level vectors, and $a(u, sigma) := "clip"_P (u \/ n - alpha sigma \/ n)$, so the power is at most $L P$.
  On the probability space of $(T, S, Z)$, the auxiliary is the vector of levels of $T + alpha hat(S)$, and the letter is $X_l := Q_n (T_l + alpha hat(S)_l) - alpha hat(S)_l$ before clipping.

  For the upper bound, take $g := product_l u_(theta, s, m_l)(T_l)$ with $m_l := alpha Q_n (Y_l) - alpha hat(S)_l$.
  On a cell the mean $m_l$ is fixed, and $T$ ranges over a box.
  Integrating the Gaussian ratio over that box gives $Psi(u, y) := product_l cal(N)(alpha y_l \/ n, s)(k_n^(-1)(u_l))$, and these sum to at most $1$ over $u$.
  So the lemma gives $integral log g <= I(U ; Y) - I(U ; S)$.
  The state has law $p_S$, and $Y$ given $(S, U, X)$ follows $W$, so the kernel form of the Gelfand-Pinsker formula gives $I(U ; Y) - I(U ; S) <= C_"GP"$.

  For the lower bound, $log g$ is a sum over the letters.
  Outside the clipping set the summands are i.i.d. with mean
  $ J_n = 1/2 log (theta / s) + 1/2 - 1 / (2 s) bb(E) (T - M_n)^2, $
  where $M_n := alpha Q_n (X + S + Z) - alpha hat(S)$.
  As $n -> infinity$, $M_n -> alpha (T + Z)$, and dominated convergence gives $bb(E) (T - M_n)^2 -> (1 - alpha)^2 theta + alpha^2 N = s$.
  So $J_n -> 1/2 log (theta \/ s) = C(theta, N)$.
  Since $|M_n| <= 2 n$, on the clipping set each summand moves by at most $(8 n |t| + 16 n^2) \/ (2 s)$, and $|t| <= c + t^2 \/ c$.
  With $beta$ the probability of the clipping set, this gives
  $ integral log g >= L J_n - L ((8 n c + 16 n^2) beta + 8 n theta \/ c) / (2 s). $

  Finally, $bb(E) X_l^2 -> theta < P$ by dominated convergence, and Chebyshev's inequality gives $beta <= "Var" \/ (L (P - m_n)^2)$ with $m_n := bb(E) X_l^2$.
  Let $eta := (C(theta, N) - R) \/ 4$.
  Choose $n$ with $J_n > R + 3 eta$ and $m_n < P$, then $c$ with $8 n theta \/ (2 s c) < eta$, then $L$ large.
  Then $C_"GP" > L (R + eta) > L R$.
]


== Parallel Gaussian channels
#source("Meat.Continuous.ParallelGaussian")

There are finitely many Gaussian channels $i in iota$ with noise variances $N_i > 0$.
In each of $n$ channel uses the sender puts one real number on each channel, and the total power over all channels and all uses is at most $n P$.
This section proves that the operational capacity is the water-filling capacity of the previous chapter.

#lemma("Random coding for one Gaussian channel", lean: "Meat.AWGN.achievable_of_lt")[
  If $P >= 0$, $N > 0$ and $0 <= R < C(P, N)$, then $R$ is achievable for the Gaussian channel.
][
  The block quantization of the Gaussian chapter gives a finite channel with enough information, and random coding on it gives the codes.
]

#definition(
  "Codes for parallel channels",
  lean: (
    "Meat.Parallel.noise",
    "Meat.Parallel.isProbabilityMeasure_noise",
    "Meat.Parallel.Code",
    "Meat.Parallel.Code.errorProb",
    "Meat.Parallel.Code.avgError",
    "Meat.Parallel.Achievable",
    "Meat.Parallel.achievable_zero",
  ),
)[
  The noise is the product over $i$ of the Gaussian noise vectors of variance $N_i$ and length $n$.
  A code of length $n$ with $k$ messages has codewords $x(m) in RR^(iota times [n])$ with $sum_i sum_t x(m)_(i, t)^2 <= n P$, and a measurable decoder.
  The error probability of $m$ is the probability that the decoder does not return $m$ when $x(m) + Z$ is received.
  Achievable rates are defined as for one Gaussian channel, and the rate $0$ is achievable.
]

#definition(
  "Product codes",
  lean: (
    "Meat.Parallel.prodEquiv",
    "Meat.Parallel.productCode",
    "Meat.Parallel.errorProb_productCode_le",
    "Meat.Parallel.avgError_productCode_le",
  ),
)[
  Given a Gaussian code with power $Q_i$ and $k_i$ messages for each channel, with $sum_i Q_i <= P$, the product code sends the codeword of message $m_i$ on channel $i$ and decodes each channel separately.
  Its messages are $product_i [k_i]$, numbered by a bijection with $[product_i k_i]$.
  Its error probability is at most the sum of the error probabilities of the components, and so is its average error probability.
][
  The product code errs only if some component errs, and the noise on channel $i$ has the law of the component noise.
  For the average, a function of the $i$th message summed over all message vectors counts each value $product_(j != i) k_j$ times.
]

#theorem("Achievability", lean: "Meat.Parallel.achievable_of_lt")[
  If there is at least one channel, $P >= 0$, $N_i > 0$ and $R$ is below the water-filling capacity, then $R$ is achievable.
][
  Let $p$ be the water-filling allocation, so the capacity is $sum_i C(p_i, N_i)$.
  With $delta := (sum_i C(p_i, N_i) - R) \/ |iota|$, the rates $R_i := max(C(p_i, N_i) - delta, 0)$ are achievable for the single channels and $sum_i R_i >= R$.
  Take component codes with average error at most $epsilon \/ |iota|$ and form the product code.
  Its power is at most $n sum_i p_i = n P$.
]

#lemma("Spreading power over time", lean: "Meat.Parallel.sum_awgnCapacity_le")[
  If $P_(i, t) >= 0$ and $sum_i sum_t P_(i, t) <= n P$, then $sum_i sum_t C(P_(i, t), N_i)$ is at most $n$ times the water-filling capacity.
][
  View the $n |iota|$ channels $(i, t)$ with noise $N_i$ as one parallel system with budget $n P$.
  The water level of the original system fills each copy of channel $i$ with $p_i^nu$, so it uses exactly $n P$.
  By optimality of water filling, the sum is at most $n sum_i C(p_i^nu, N_i)$.
]

#lemma(
  "Golden formula with a product Gaussian reference",
  lean: (
    "Meat.Parallel.map_noise_add",
    "Meat.Parallel.map_noise_add_absolutelyContinuous",
    "Meat.Parallel.sum_mul_log_sub_log_le",
  ),
)[
  The law of $x + Z$ is the product of the Gaussians of means $x_(i, t)$ and variances $N_i$.
  It is absolutely continuous with respect to the product $rho$ of centered Gaussians of variances $S_(i, t) > 0$.
  For every measurable map $d$ into a finite set,
  $ sum_j P_x (d = j) (log P_x (d = j) - log rho(d = j)) <= sum_i sum_t (1/2 log(S_(i, t) \/ N_i) - 1/2 + (x_(i, t)^2 + N_i) / (2 S_(i, t))). $
][
  The density of the law of $x + Z$ with respect to $rho$ is the product of the Gaussian likelihood ratios.
  The data processing step of the Gaussian converse bounds the left side by the expected log-density, which is computed coordinate by coordinate.
]

#theorem(
  "Converse",
  lean: (
    "Meat.Parallel.Code.measurable_dec_add",
    "Meat.Parallel.Code.channel",
    "Meat.Parallel.Code.channel_apply",
    "Meat.Parallel.Code.inputMutualInfo_channel_le",
    "Meat.Parallel.Code.one_sub_mul_log_le",
    "Meat.Parallel.capacity_nonneg",
    "Meat.Parallel.le_capacity_of_achievable",
  ),
)[
  For every code, $(1 - overline(lambda)) log k <= n C_"wf" + log 2$, where $C_"wf" >= 0$ is the water-filling capacity.
  Hence every achievable rate is at most $C_"wf"$.
][
  The code induces a finite channel from messages to decoded messages.
  With uniform messages, take $S_(i, t) := overline(P)_(i, t) + N_i$, where $overline(P)_(i, t)$ is the average power of the codewords on channel $i$ at time $t$.
  Averaged over messages, the golden formula gives $sum_i sum_t C(overline(P)_(i, t), N_i)$, which is at most $n C_"wf"$ by spreading power over time.
  Fano's inequality finishes the bound, and the rate statement follows as for one Gaussian channel.
]

#theorem("Capacity of parallel Gaussian channels", lean: "Meat.Parallel.closure_achievable_eq")[
  If there is at least one channel, $P >= 0$ and $N_i > 0$ for all $i$, then
  $ overline({R >= 0 : R "achievable"}) = [0, C_"wf"], quad C_"wf" = sum_i 1/2 log(max(nu, N_i) \/ N_i), $
  where $nu$ is the water level.
][
  Achievability and the converse, as for one Gaussian channel.
]

== MIMO Gaussian channels
#source("Meat.Continuous.MIMO")

Let $E$ and $F$ be finite-dimensional real inner product spaces and $H : E -> F$ a linear map, the channel matrix.
In each of $n$ channel uses the sender puts a vector $x_t in E$, the receiver sees $H x_t + Z_t$ in $F$, and $Z_t$ is isotropic Gaussian noise of variance $N$.
The total power is $sum_t norm(x_t)^2 <= n P$.
A singular value decomposition turns this channel into parallel Gaussian channels, one for each nonzero singular value.
This section proves that the capacity is the water-filling capacity of those parallel channels.

#definition("Singular value decomposition", lean: ("Meat.MIMO.SVD", "Meat.MIMO.SVD.Active"))[
  A singular value decomposition of $H$ consists of an orthonormal basis $(v_j)_(j in iota)$ of $E$, an orthonormal basis $(u_i)_(i in kappa)$ of $F$, numbers $sigma_j >= 0$ and a map $e : iota -> kappa$, injective on $\{j : sigma_j > 0\}$, with $H v_j = sigma_j u_(e(j))$.
  The active indices are those $j$ with $sigma_j > 0$.
]

#definition(
  "Codes for the MIMO channel",
  lean: (
    "Meat.MIMO.noiseLetter",
    "Meat.MIMO.noise",
    "Meat.MIMO.isProbabilityMeasure_noiseLetter",
    "Meat.MIMO.isProbabilityMeasure_noise",
    "Meat.MIMO.Code",
    "Meat.MIMO.Code.errorProb",
    "Meat.MIMO.Code.avgError",
    "Meat.MIMO.Achievable",
    "Meat.MIMO.achievable_zero",
  ),
)[
  One noise letter is the standard Gaussian on $F$ scaled by $sqrt(N)$, and the noise of length $n$ is the product of $n$ letters.
  A code of length $n$ with $k$ messages has codewords $x(m) in E^n$ with $sum_t norm(x(m)_t)^2 <= n P$, and a measurable decoder on $F^n$.
  The error probability of $m$ is the probability that the decoder does not return $m$ when $(H x(m)_t + Z_t)_t$ is received.
  Achievable rates are defined as for one Gaussian channel, and the rate $0$ is achievable.
]

#lemma("Projected noise", lean: ("Meat.MIMO.SVD.project", "Meat.MIMO.SVD.map_noise_project"))[
  For an active $j$ let $"proj"(z)_(j, t) := sigma_j^(-1) chevron.l u_(e(j)), z_t chevron.r$.
  If $N >= 0$, the image of the noise under $"proj"$ is the noise of the parallel Gaussian channels with variances $N \/ sigma_j^2$.
][
  The coordinates $chevron.l u_i, Z_t chevron.r$ in an orthonormal basis are independent centered Gaussians of variance $N$.
  Keeping the coordinates $e(j)$, which are distinct, and scaling by $sigma_j^(-1)$ gives independent Gaussians of variance $N \/ sigma_j^2$.
]

#theorem(
  "Achievability",
  lean: (
    "Meat.MIMO.SVD.ofParallel",
    "Meat.MIMO.SVD.avgError_ofParallel",
    "Meat.MIMO.SVD.achievable_of_lt",
  ),
)[
  If some index is active, $P >= 0$, $N > 0$ and $R$ is below the water-filling capacity of the parallel channels with noise $N \/ sigma_j^2$, then $R$ is achievable.
][
  A parallel code with codewords $c(m)_(j, t)$ gives the MIMO codeword $x(m)_t := sum_j c(m)_(j, t) v_j$, which has the same power since $(v_j)$ is orthonormal.
  The receiver applies $"proj"$ and then the parallel decoder.
  Since $"proj"(H x(m) + Z) = c(m) + "proj"(Z)$, the projected noise lemma shows that both codes have the same average error probability.
  Achievability for parallel channels finishes the proof.
]

#theorem(
  "Converse",
  lean: (
    "Meat.MIMO.Code.channel",
    "Meat.MIMO.Code.inputMutualInfo_channel_le",
    "Meat.MIMO.Code.one_sub_mul_log_le",
    "Meat.MIMO.SVD.le_capacity_of_achievable",
  ),
)[
  If some index is active, then for every code $(1 - overline(lambda)) log k <= n C_"wf" + log 2$, where $C_"wf"$ is the water-filling capacity of the parallel channels with noise $N \/ sigma_j^2$.
  Hence every achievable rate is at most $C_"wf"$.
][
  The code induces a finite channel from messages to decoded messages.
  In the coordinates $chevron.l u_i, dot chevron.r$ the output is a parallel Gaussian channel over $kappa$ with noise $N$ and inputs $chevron.l u_i, H x(m)_t chevron.r$.
  The golden formula for parallel channels, with uniform messages and reference variances the average power plus $N$, bounds the mutual information by $sum_i sum_t C(overline(P)_(i, t), N)$.
  Coordinates outside the image of the active indices carry no signal.
  For an active $j$, $chevron.l u_(e(j)), H x chevron.r = sigma_j chevron.l v_j, x chevron.r$, so the term is $C(Q_(j, t), N \/ sigma_j^2)$ with $Q_(j, t)$ the average of $chevron.l v_j, x(m)_t chevron.r^2$.
  By Bessel's inequality $sum_j sum_t Q_(j, t) <= n P$, and spreading power over time bounds the sum by $n C_"wf"$.
  Fano's inequality finishes the bound, and the rate statement follows as for one Gaussian channel.
]

#theorem("Capacity for a given decomposition", lean: "Meat.MIMO.SVD.closure_achievable_eq")[
  If some index is active, $P >= 0$ and $N > 0$, then
  $ overline({R >= 0 : R "achievable"}) = [0, C_"wf"]. $
][
  Achievability and the converse, as for one Gaussian channel.
]

#lemma("Existence of a singular value decomposition", lean: ("Meat.MIMO.isSymmetric_gram", "Meat.MIMO.exists_svd"))[
  The map $H^* H$ is symmetric.
  If $H != 0$, there is a singular value decomposition indexed by $[dim E]$ and $[dim F]$ with some active index, and each $v_j$ is an eigenvector of $H^* H$ with eigenvalue $sigma_j^2$.
][
  Let $(v_j)$ be an orthonormal eigenbasis of $H^* H$ with eigenvalues $lambda_j$.
  Then $chevron.l H v_j, H v_k chevron.r = lambda_k [j = k]$, so $lambda_j = norm(H v_j)^2 >= 0$; put $sigma_j := sqrt(lambda_j)$.
  The vectors $sigma_j^(-1) H v_j$ for active $j$ are orthonormal, so there are at most $dim F$ of them.
  Embed the active indices into $[dim F]$ and extend these vectors to an orthonormal basis $(u_i)$ of $F$.
  For inactive $j$, $norm(H v_j)^2 = sigma_j^2 = 0$, so $H v_j = 0 = sigma_j u_(e(j))$ for any choice of $e(j)$.
  Some index is active, since otherwise $H$ vanishes on a basis.
]

#theorem("Capacity of the MIMO Gaussian channel", lean: "Meat.MIMO.closure_achievable_eq")[
  If $H != 0$, $P >= 0$ and $N > 0$, then there is a singular value decomposition with $H^* H v_j = sigma_j^2 v_j$ for all $j$, and
  $ overline({R >= 0 : R "achievable"}) = [0, C_"wf"], quad C_"wf" = sum_(j: sigma_j > 0) 1/2 log(max(nu, N \/ sigma_j^2) \/ (N \/ sigma_j^2)), $
  where $nu$ is the water level.
  So the capacity is water filling over the squared singular values of $H$.
][
  Combine the existence of a decomposition with the capacity for a given decomposition.
]
