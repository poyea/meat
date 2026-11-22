#import "../meat.typ": *

= Hypothesis testing

A test observes $n$ independent symbols from a finite alphabet $S$.
Under the hypothesis $H_0$, each symbol has the law $p$.
Under the hypothesis $H_1$, each symbol has the law $q$.
A test is a set $A subset.eq S^n$: it decides $H_0$ on $A$ and $H_1$ outside $A$.
The type-I error is $p^n (A^c)$, and the type-II error is $q^n (A)$.
The notation is as in the sections on typical sequences and on the method of types.
In particular, $nu_p$ is the measure of $p$, and $D(p || q) := D(nu_p || nu_q)$.

== Stein's lemma
#source("Meat.Testing.Stein")

Stein's lemma fixes a bound $epsilon$ on the type-I error and asks how fast the best type-II error decays.
The answer is $e^(-n D(p || q))$.
The divergence is real valued, so the lemma assumes $nu_p << nu_q$, that is, $q(s) = 0$ implies $p(s) = 0$.
Without this assumption the true divergence is $+infinity$.

#theorem("Weak law of large numbers", lean: "Meat.tendsto_sum_iidProb_abs_sub_le")[
  Let $f : S -> RR$, let $mu := sum_s p_s f(s)$ and let $delta > 0$.
  Then
  $ lim_(n -> infinity) p^n ({x : |sum_i f(x_i) - n mu| <= n delta}) = 1. $
][
  Let $Y := f - mu$, so $sum_s p_s Y(s) = 0$, and let $sigma^2 := sum_s p_s Y(s)^2$.
  As in the proof of the asymptotic equipartition property, $sum_x p^n (x) (sum_i Y(x_i))^2 = n sigma^2$.
  A sequence outside the set has $(n delta)^2 < (sum_i Y(x_i))^2$.
  So the probability outside the set is at most $n sigma^2 \/ (n delta)^2 = sigma^2 \/ (n delta^2)$, by Chebyshev's inequality.
]

#lemma(
  "Divergence and likelihood ratios",
  lean: (
    "Meat.klDiv_toMeasure",
    "Meat.PMF.toMeasure_absolutelyContinuous_iff",
    "Meat.iidProb_eq_exp_mul",
  ),
)[
  $D(p || q) = sum_s p_s log (p_s \/ q_s)$.
  On a countable set, $nu_p << nu_q$ if and only if $q(s) = 0$ implies $p(s) = 0$ for every $s$.
  If this holds and $p^n (x) > 0$, then
  $ p^n (x) = exp(sum_i log (p(x_i)) / (q(x_i))) q^n (x). $
][
  The first statement is the definition with $nu_p ({s}) = p(s)$.
  The second is the lemma on absolute continuity on a finite set.
  For the third, every $p(x_i)$ is positive, so every $q(x_i)$ is positive, and each factor is $exp(log (p(x_i) \/ q(x_i))) q(x_i)$.
]

#definition("Optimal type-II error", lean: "Meat.steinBeta")[
  For $epsilon in RR$,
  $ beta_n (epsilon) := inf {q^n (A) : A subset.eq S^n, p^n (A^c) <= epsilon}. $
]

The infimum is over a finite set, so for $epsilon >= 0$ it is a minimum.

#theorem("Achievability", lean: "Meat.stein_achievability")[
  Let $nu_p << nu_q$, $epsilon > 0$ and $delta > 0$.
  For all large $n$ there is a test $A$ with
  $ p^n (A^c) <= epsilon, quad q^n (A) <= e^(-n (D(p || q) - delta)). $
][
  Let $L(x) := sum_i log (p(x_i) \/ q(x_i))$ be the log-likelihood ratio.
  Let $A$ be the set of $x$ with $p^n (x) > 0$ and $|L(x) - n D(p || q)| <= n delta$.
  Sequences with $p^n (x) = 0$ do not change $p^n (A)$, so $p^n (A) -> 1$ by the weak law with $f(s) := log (p_s \/ q_s)$, whose mean is $D(p || q)$.
  So $p^n (A^c) <= epsilon$ for large $n$.
  On $A$, $L(x) >= n (D(p || q) - delta)$, so $q^n (x) = e^(-L(x)) p^n (x) <= e^(-n (D(p || q) - delta)) p^n (x)$.
  Sum over $A$ and use $p^n (A) <= 1$.
]

The condition $p^n (x) > 0$ in $A$ is necessary: where $p_s = 0$, Lean has $log (p_s \/ q_s) = 0$, and such sequences could have large $q^n$ probability.

#theorem("Converse", lean: "Meat.stein_converse")[
  Let $nu_p << nu_q$, $epsilon < 1$ and $delta > 0$.
  For all large $n$, every test $A$ with $p^n (A^c) <= epsilon$ has
  $ q^n (A) >= e^(-n (D(p || q) + delta)). $
][
  Let $B$ be the set of $x$ with $|L(x) - n D(p || q)| <= n delta \/ 2$.
  By the weak law, $p^n (B) > 1 - (1 - epsilon) \/ 2$ for large $n$.
  Since $p^n (A) >= 1 - epsilon$ and $p^n (A union B) <= 1$, we get $p^n (A inter B) >= (1 - epsilon) \/ 2$.
  Each $x in A inter B$ with $p^n (x) > 0$ has $L(x) <= n (D(p || q) + delta \/ 2)$, so $q^n (x) >= e^(-n (D(p || q) + delta \/ 2)) p^n (x)$.
  This is also true if $p^n (x) = 0$.
  Hence $q^n (A) >= e^(-n (D(p || q) + delta \/ 2)) (1 - epsilon) \/ 2$.
  For large $n$, $e^(-n delta \/ 2) <= (1 - epsilon) \/ 2$.
]

#theorem("Chernoff-Stein lemma", lean: "Meat.tendsto_steinBeta")[
  Let $nu_p << nu_q$ and $0 < epsilon < 1$.
  Then
  $ lim_(n -> infinity) -1/n log beta_n (epsilon) = D(p || q). $
][
  The minimum $beta_n (epsilon)$ is attained by some test, so the converse with $delta = 1$ gives $beta_n (epsilon) > 0$ for large $n$.
  For $a < D(p || q)$, achievability with $delta := (D(p || q) - a) \/ 2$ gives $beta_n (epsilon) <= e^(-n (D(p || q) - delta))$, so $-1/n log beta_n (epsilon) >= D(p || q) - delta > a$.
  For $b > D(p || q)$, the converse with $delta := (b - D(p || q)) \/ 2$ applied to an optimal test gives $-1/n log beta_n (epsilon) <= D(p || q) + delta < b$.
]

The exponent does not depend on $epsilon$.
This is a strong converse: even a type-I error close to $1$ does not give a better exponent.

== Sanov's theorem
#source("Meat.Testing.Sanov")

Sanov's theorem gives the exponent of the probability that the type of $n$ symbols from $q$ is in a set $E$ of distributions.
Here $E$ is a set of measures on $S$.
Only the probability measures in $E$ matter, because every type of length $n > 0$ is a probability measure.

#theorem("Upper bound", lean: "Meat.sum_iidProb_seqType_mem_le")[
  Let $c in RR$ with $c <= D(P || nu_q)$ for every probability measure $P in E$ with $P << nu_q$.
  Then for every $n$,
  $ q^n ({x : P_x in E}) <= (n + 1)^(|S|) e^(-n c). $
][
  For $n = 0$, the left side is at most $1$ and the right side is $1$.
  For $n > 0$, split the event over the type classes.
  A type $P in E$ with $P << nu_q$ has $q^n (T(P)) <= e^(-n D(P || nu_q)) <= e^(-n c)$.
  A type $P$ without $P << nu_q$ has $q^n (T(P)) = 0$.
  There are at most $(n + 1)^(|S|)$ types.
]

The bound holds for every set $E$.

#theorem("Lower bound", lean: "Meat.le_sum_iidProb_seqType_mem")[
  Let $P$ be a probability measure with $P << nu_q$.
  Suppose that for some $delta > 0$, every probability measure $Q$ with $|Q({s}) - P({s})| < delta$ for all $s$ is in $E$.
  Then for every $eta > 0$ and all large $n$,
  $ q^n ({x : P_x in E}) >= e^(-n (D(P || nu_q) + eta)). $
][
  Take the sequences $x^((n))$ of the approximation lemma for the weights $P({s})$, and let $Q_n := P_(x^((n)))$.
  Each $Q_n << nu_q$: a symbol $s$ with $q(s) = 0$ has $P({s}) = 0$, so it does not occur in $x^((n))$.
  By the continuity of the divergence, $D(Q_n || nu_q) -> D(P || nu_q)$.
  For large $n$, $Q_n in E$, $D(Q_n || nu_q) < D(P || nu_q) + eta \/ 2$ and $(n + 1)^(|S|) <= e^(n eta \/ 2)$.
  The event contains $T(Q_n)$, and $q^n (T(Q_n)) >= e^(-n D(Q_n || nu_q)) \/ (n + 1)^(|S|)$.
]

#definition("Sanov exponent", lean: "Meat.sanovExponent")[
  $ D(E || q) := inf {D(P || nu_q) : P in E, P "a probability measure", P << nu_q}. $
]

The infimum is over the measures where the real divergence is the true divergence.
If this set is empty, Lean gives $D(E || q) = 0$, so the theorem below assumes that it is not empty.

#theorem("Sanov's theorem", lean: "Meat.tendsto_sanov")[
  Let $E$ be open among probability measures: for every $P in E$ there is $delta > 0$ such that every probability measure $Q$ with $|Q({s}) - P({s})| < delta$ for all $s$ is in $E$.
  Suppose that some probability measure $P in E$ has $P << nu_q$.
  Then
  $ lim_(n -> infinity) -1/n log q^n ({x : P_x in E}) = D(E || q). $
][
  By the lower bound for one $P$, the probability is positive for large $n$.
  For $a < D(E || q)$, the upper bound with $c := D(E || q)$ and $(n + 1)^(|S|) <= e^(n (D(E || q) - a) \/ 2)$ gives $-1/n log q^n (dots) >= D(E || q) - (D(E || q) - a) \/ 2 > a$.
  For $b > D(E || q)$, choose $P$ in the set with $D(P || nu_q) < b$.
  The lower bound with $eta := (b - D(P || nu_q)) \/ 2$ gives $-1/n log q^n (dots) <= D(P || nu_q) + eta < b$.
]

For a closed set $E$ the upper bound still holds, but the limit can fail when the infimum is attained only at boundary points that types cannot reach.

== Chernoff information
#source("Meat.Testing.Chernoff")

In the Bayesian setting, both hypotheses have positive prior probabilities.
We take equal priors and add the two errors.
Other positive priors change the error by a bounded factor, so they do not change the exponent.

#definition("Bayesian error", lean: "Meat.bayesError")[
  $ e_n := min_(A subset.eq S^n) (p^n (A^c) + q^n (A)). $
]

#definition("Chernoff information", lean: "Meat.chernoffInfo")[
  $ C(p, q) := sup_(0 < lambda < 1) -log sum_s p_s^lambda q_s^(1 - lambda). $
]

The usual definition is $-min_(lambda in [0, 1]) log sum_s p_s^lambda q_s^(1 - lambda)$ with $0^0 := 0$ in the endpoints.
In Lean, $0^0 = 1$, so the endpoints would use the wrong value.
On the open interval, $0^lambda = 0$, and the supremum equals the usual maximum by continuity.
The theorems assume that some $s$ has $p(s) > 0$ and $q(s) > 0$.
Otherwise $e_n = 0$ and the true value of $C(p, q)$ is $+infinity$.

#lemma("The likelihood ratio test", lean: "Meat.bayesError_eq_sum_min")[
  $ e_n = sum_x min(p^n (x), q^n (x)). $
][
  Every test pays $p^n (x)$ or $q^n (x)$ at each $x$, so it pays at least the minimum.
  The test $A := {x : q^n (x) <= p^n (x)}$ pays exactly the minimum.
]

#theorem("Chernoff bound", lean: ("Meat.bayesError_le_pow", "Meat.bayesError_pos", "Meat.bayesError_le_exp"))[
  For every $lambda in [0, 1]$,
  $ e_n <= (sum_s p_s^lambda q_s^(1 - lambda))^n. $
  If some $s$ has $p(s) > 0$ and $q(s) > 0$, then $e_n > 0$ and
  $ e_n <= e^(-n C(p, q)). $
][
  For $a, b >= 0$, $min(a, b) <= a^lambda b^(1 - lambda)$: if $a <= b$, then $a = a^lambda a^(1 - lambda) <= a^lambda b^(1 - lambda)$, and the other case is the same.
  Apply this to $p^n (x)$ and $q^n (x)$.
  The product of the powers is $product_i p(x_i)^lambda q(x_i)^(1 - lambda)$, and the sum over $x$ is the $n$-th power of the sum over $s$.
  The constant sequence at $s$ has positive probability under both laws, so $e_n > 0$.
  Then $-1/n log e_n >= -log sum_s p_s^lambda q_s^(1 - lambda)$ for every $lambda in (0, 1)$, so $-1/n log e_n >= C(p, q)$.
]

#theorem("Converse", lean: "Meat.exp_le_bayesError")[
  Let some $s$ have $p(s) > 0$ and $q(s) > 0$, and let $eta > 0$.
  For all large $n$,
  $ e_n >= e^(-n (C(p, q) + eta)). $
][
  Let $A$ be the set of $s$ with $p(s) > 0$ and $q(s) > 0$.
  For $mu in RR$ let $w_mu (s) := p_s^mu q_s^(1 - mu)$ on $A$ and $0$ outside, $Z(mu) := sum_s w_mu (s) > 0$ and $Q_mu := w_mu \/ Z(mu)$.
  Let $m(mu) := sum_s Q_mu (s) (log p_s - log q_s)$.
  On $A$, $log Q_mu (s) = mu log p_s + (1 - mu) log q_s - log Z(mu)$.
  So
  $ sum_s (Q_mu log Q_mu - Q_mu log p_s) = -(1 - mu) m(mu) - log Z(mu), quad sum_s (Q_mu log Q_mu - Q_mu log q_s) = mu m(mu) - log Z(mu). $
  The function $m$ is continuous.
  If $m(0) >= 0$, take $mu := 0$; if $m(1) <= 0$, take $mu := 1$; otherwise the intermediate value theorem gives $mu in [0, 1]$ with $m(mu) = 0$.
  In each case both sums are at most $-log Z(mu)$.
  For $lambda in (0, 1)$, $Z(lambda) = sum_s p_s^lambda q_s^(1 - lambda)$, so $-log Z(lambda) <= C(p, q)$.
  Since $-log Z$ is continuous and $[0, 1]$ is the closure of $(0, 1)$, also $-log Z(mu) <= C(p, q)$.
  Now take the sequences of the approximation lemma for $Q_mu$, and let $nu_n$ be their types.
  Only symbols in $A$ occur, so $nu_n << nu_p$ and $nu_n << nu_q$.
  By the continuity of the divergence, $D(nu_n || nu_p)$ and $D(nu_n || nu_q)$ tend to the two sums above.
  So for large $n$, both are less than $C(p, q) + eta \/ 2$.
  Each $x in T(nu_n)$ then has $min(p^n (x), q^n (x)) >= e^(-n H(nu_n)) e^(-n (C(p, q) + eta \/ 2))$.
  With $|T(nu_n)| >= e^(n H(nu_n)) \/ (n + 1)^(|S|)$ and $(n + 1)^(|S|) <= e^(n eta \/ 2)$, this gives the bound.
]

The measure $Q_mu$ is the tilted distribution between $q$ and $p$.
At the chosen $mu$, it is equally far from $p$ and from $q$ in divergence.

#theorem("Chernoff's theorem", lean: "Meat.tendsto_chernoff")[
  If some $s$ has $p(s) > 0$ and $q(s) > 0$, then
  $ lim_(n -> infinity) -1/n log e_n = C(p, q). $
][
  The Chernoff bound gives $-1/n log e_n >= C(p, q)$ for $n > 0$.
  For $b > C(p, q)$, the converse with $eta := (b - C(p, q)) \/ 2$ gives $-1/n log e_n <= C(p, q) + eta < b$ for large $n$.
]
