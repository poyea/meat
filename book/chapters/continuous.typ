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
The operational capacity of parallel Gaussian channels is not formalized.

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
The operational capacity theorems for these channels are not formalized.

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
