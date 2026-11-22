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

The quantization bound is not in Lean yet.
A proof takes a discrete input law close to $cal(N)(0, P')$ with $P' < P$ and a fine output quantizer.
It shows that the quantized information is close to $1/2 log (1 + P' \/ N)$.
With blocks, the input law is restricted to vectors of empirical power at most $L P$.
By the law of large numbers, this restriction costs little information when $L$ is large.
