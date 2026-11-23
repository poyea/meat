#import "../meat.typ": *

= Shannon information measures

A random variable is a measurable map $X : Omega -> S$.
The space $Omega$ is a measurable space with a measure $mu$.
The alphabet $S$ is always finite.
All quantities are in nats.
Each logarithm in this book is a natural logarithm.
A joint random variable is a pair: $(X, Y)$ is the map $omega |-> (X(omega), Y(omega))$.
In this chapter, $eta : [0, infinity) -> RR$ is the function with $eta(t) = -t log t$ for $t > 0$ and $eta(0) = 0$.

== Entropy and mutual information
#source("Meat.Shannon.Entropy")

#definition("Entropy of a measure", lean: "Meat.measureEntropy")[
  Let $S$ be a finite set and let $nu$ be a measure on $S$.
  The entropy of $nu$ is
  $ H(nu) := sum_(s in S) eta(nu_s), $
  where $nu_s := nu({s})$ if $nu({s}) < infinity$ and $nu_s := 0$ otherwise.
]

#definition("Entropy", lean: ("Meat.entropy", "Meat.entropy_def"))[
  Let $mu$ be a measure on $Omega$ and let $X : Omega -> S$.
  The entropy of $X$ under $mu$ is $H(X) := H(X_* mu)$, where $X_* mu := mu compose X^(-1)$ is the push-forward of $mu$ by $X$.
]

The Lean notation for $H(X)$ is `H[X ; μ]`.

#definition("Conditional entropy", lean: ("Meat.condEntropy", "Meat.condEntropy_def"))[
  For $X : Omega -> S$ and $Y : Omega -> T$,
  $ H(X given Y) := H(X, Y) - H(Y). $
]

#definition("Mutual information", lean: ("Meat.mutualInfo", "Meat.mutualInfo_def"))[
  For $X : Omega -> S$ and $Y : Omega -> T$,
  $ I(X; Y) := H(X) + H(Y) - H(X, Y). $
]

#definition(
  "Conditional mutual information",
  lean: ("Meat.condMutualInfo", "Meat.condMutualInfo_def"),
)[
  For $X : Omega -> S$, $Y : Omega -> T$ and $Z : Omega -> U$,
  $ I(X; Y given Z) := H(X given Z) + H(Y given Z) - H((X, Y) given Z). $
]

The Lean notation is `H[X | Y ; μ]`, `I[X : Y ; μ]` and `I[X : Y | Z ; μ]`.
These definitions use differences of entropies.
They do not use expected values of log-likelihood ratios.
Because of this, they do not need conditional distributions.

#proposition("Chain rule", lean: "Meat.entropy_pair_eq_add_condEntropy")[]

#proposition(lean: "Meat.mutualInfo_eq_entropy_sub_condEntropy")[]

== The same quantities in bits
#source("Meat.Shannon.Bits")

Nats are the primary unit.
To change a quantity from nats to bits, divide it by $log 2$.
Because this change is linear, each identity and each linear inequality in nats is also true in bits.

#definition(
  "Nats and bits",
  lean: (
    "Meat.natsToBits",
    "Meat.bitsToNats",
    "Meat.log_two_ne_zero",
    "Meat.bitsToNats_natsToBits",
    "Meat.natsToBits_bitsToNats",
  ),
)[
  Define $beta, gamma : RR -> RR$ by $beta(x) := x \/ log 2$ and $gamma(y) := y log 2$.
  Since $log 2 != 0$, $gamma compose beta = beta compose gamma = id_RR$.
]

#definition(
  "Measures in bits",
  lean: (
    "Meat.entropyBits",
    "Meat.condEntropyBits",
    "Meat.mutualInfoBits",
    "Meat.condMutualInfoBits",
    "Meat.entropyBits_def",
    "Meat.condEntropyBits_def",
    "Meat.mutualInfoBits_def",
    "Meat.condMutualInfoBits_def",
  ),
)[
  $ H_2(X) := beta(H(X)), quad H_2(X given Y) := beta(H(X given Y)), $
  $ I_2(X; Y) := beta(I(X; Y)), quad I_2(X; Y given Z) := beta(I(X; Y given Z)). $
]

The Lean notation is `H₂[X ; μ]`, `H₂[X | Y ; μ]`, `I₂[X : Y ; μ]` and `I₂[X : Y | Z ; μ]`.

#proposition(
  "Chain rule in bits",
  lean: (
    "Meat.entropyBits_pair_eq_add_condEntropyBits",
    "Meat.mutualInfoBits_eq_entropyBits_sub_condEntropyBits",
  ),
)[]

== Shannon-type inequalities
#source("Meat.Shannon.Inequalities")

In most results of this section, $mu$ is a probability measure.
Each statement lists its assumptions.
The alphabets $S$, $T$ and $U$ are finite, and each singleton is measurable.
There are four basic inequalities: $H(X) >= 0$, $H(X given Y) >= 0$, $I(X; Y) >= 0$ and $I(X; Y given Z) >= 0$.
Each Shannon-type inequality is a sum of basic inequalities with nonnegative coefficients.
Most of the proofs use relabeling, Gibbs' inequality and the entropy of a push-forward.

#source("Meat.Shannon.Relabel")

#lemma(
  "Relabeling",
  lean: (
    "Meat.measureEntropy_map_of_injective",
    "Meat.entropy_comp_of_injective",
    "Meat.entropy_comm",
    "Meat.entropy_assoc",
    "Meat.entropy_pair_comp",
    "Meat.entropy_comm_left",
    "Meat.entropy_pair_pair_comp",
  ),
)[
  Let $nu$ be a measure on $S$ and let $f : S -> T$ be injective.
  Then $H(f_* nu) = H(nu)$.
  Hence $H(f compose X) = H(X)$ for every $X : Omega -> S$ and every measure $mu$.
  In particular, for all $X$, $Y$, $Z$ and all maps $g : S -> T$ and $h : T -> U$,
  $ H(X, Y) = H(Y, X), quad H((X, Y), Z) = H(X, (Y, Z)), quad H(X, g compose X) = H(X), $
  $ H((X, Y), Z) = H((Y, X), Z), quad H(X, (Y, h compose Y)) = H(X, Y). $
  No measurability and no probability assumption is necessary.
][
  Since $f$ is injective, $f^(-1)({f(s)}) = {s}$ for every $s in S$, and $f^(-1)({t}) = emptyset$ for $t in.not f(S)$.
  Hence $(f_* nu)_(f(s)) = nu_s$, and $(f_* nu)_t = 0$ for $t in.not f(S)$.
  The two sums that define the entropies have the same nonzero terms, because $eta(0) = 0$.
  If $X$ is almost everywhere measurable, then $(f compose X)_* mu = f_* (X_* mu)$, so the first statement gives $H(f compose X) = H(X)$.
  Every map on $S$ is measurable and its image sets are measurable, so $f$ is a measurable embedding.
  Thus if $X$ is not almost everywhere measurable, then $f compose X$ is not either.
  Then Lean defines each push-forward as the zero measure if $mu = 0$, and as a Dirac measure otherwise.
  Each of these measures has entropy $0$, because $eta(0) = eta(1) = 0$.
  The special cases follow from the injectivity of $(s, t) |-> (t, s)$, of $(s, (t, u)) |-> ((s, t), u)$, of $s |-> (s, g(s))$, of $((s, t), u) |-> ((t, s), u)$ and of $(s, t) |-> (s, (t, h(t)))$.
]

#source("Meat.Shannon.Inequalities")

#lemma("Gibbs' inequality", lean: "Meat.sum_mul_log_le_sum_mul_log")[
  Let $I$ be a finite set and let $p, q : I -> [0, infinity)$ with $sum_i q_i <= sum_i p_i$.
  Assume that $p_i = 0$ for every $i$ with $q_i = 0$.
  Then
  $ sum_i p_i log q_i <= sum_i p_i log p_i. $
  As in Lean, $log 0 := 0$.
  The terms with $p_i = 0$ are $0$ on both sides.
][
  We show $p_i log q_i - p_i log p_i <= q_i - p_i$ for each $i$.
  If $p_i = 0$, the left side is $0$ and the right side is $q_i >= 0$.
  If $p_i > 0$, then $q_i > 0$ by the assumption.
  For every $t > 0$, $log t <= t - 1$.
  Put $t := q_i \/ p_i$ and multiply by $p_i$.
  This gives $p_i (log q_i - log p_i) <= q_i - p_i$.
  The sum over $i$ gives
  $ sum_i p_i log q_i - sum_i p_i log p_i <= sum_i q_i - sum_i p_i <= 0. $
]

#lemma("Equality in Gibbs' inequality", lean: "Meat.sum_mul_log_eq_sum_mul_log_iff")[
  Let $I$, $p$ and $q$ satisfy the assumptions of Gibbs' inequality.
  Then
  $ sum_i p_i log q_i = sum_i p_i log p_i $
  if and only if $q_i = p_i$ for every $i$.
][
  If $q = p$, the two sums are equal.
  For the converse, let $d_i := (q_i - p_i) - (p_i log q_i - p_i log p_i)$.
  The proof of Gibbs' inequality shows $d_i >= 0$ for each $i$.
  If the two sums are equal, then $sum_i d_i = sum_i q_i - sum_i p_i <= 0$.
  Hence $d_i = 0$ for each $i$.
  If $p_i = 0$, then $d_i = q_i$, so $q_i = 0 = p_i$.
  If $p_i > 0$, then $q_i > 0$, and $d_i = 0$ says $p_i (log t - (t - 1)) = 0$ with $t := q_i \/ p_i$.
  For $t > 0$ with $t != 1$, $log t < t - 1$.
  Thus $t = 1$, that is, $q_i = p_i$.
]

#lemma(
  "Singletons and push-forwards",
  lean: (
    "Meat.sum_measureReal_singleton_eq_one",
    "Meat.measureReal_map_singleton",
    "Meat.measureReal_singleton_le_map",
    "Meat.sum_measureReal_mul_comp",
  ),
)[][
  Every map $f : A -> B$ is measurable, because $A$ is finite and its singletons are measurable.
  (1) The singletons of $A$ are disjoint and their union is $A$, so the sum is $nu(A) = 1$.
  (2) The set $f^(-1)({b})$ is the disjoint union of the singletons ${a}$ with $f(a) = b$.
  (3) The point $a$ is in $f^(-1)({f(a)})$, and $nu$ is monotone.
  (4) Group the terms of the left side by the fibers of $f$.
  On the fiber of $b$, the factor $g(f(a))$ is $g(b)$, and by (2) the sum of $nu({a})$ over the fiber is $(f_* nu)({b})$.
]

#lemma(
  "Entropy of a push-forward",
  lean: (
    "Meat.measureEntropy_eq_neg_sum_mul_log",
    "Meat.measureEntropy_map_eq_neg_sum_mul_log",
    "Meat.measureEntropy_nonneg",
    "Meat.measureEntropy_map_le",
  ),
)[
  Let $A$ and $B$ be finite sets in which each singleton is measurable.
  Let $nu$ be a finite measure on $A$, let $f : A -> B$ and write $nu_a := nu({a})$.
  Then
  $ H(nu) = -sum_a nu_a log nu_a, quad H(f_* nu) = -sum_a nu_a log (f_* nu)_(f(a)) $
  and $H(f_* nu) <= H(nu)$.
  If $nu$ is a probability measure, then $H(nu) >= 0$.
  The first formula needs no assumption on $nu$ or on the singletons.
][
  The first formula is the definition of $eta$, with $log 0 = 0$.
  Apply it to $f_* nu$.
  Then group the terms by the fibers of $f$ with $g(b) := log (f_* nu)_b$, as in the preceding lemma.
  This gives the second formula.
  Also $nu_a <= (f_* nu)_(f(a))$ by the preceding lemma.
  If $nu_a > 0$, then $log nu_a <= log (f_* nu)_(f(a))$, because $log$ is increasing on $(0, infinity)$.
  If $nu_a = 0$, both terms are $0$.
  Compare the two formulas term by term to get $H(f_* nu) <= H(nu)$.
  If $nu$ is a probability measure, then each $nu_a$ is in $[0, 1]$, and $eta >= 0$ on $[0, 1]$.
]

#theorem("Range of entropy", lean: ("Meat.entropy_nonneg", "Meat.entropy_le_log_card"))[][
  Let $p_s := (X_* mu)_s$.
  In Lean, $X_* mu$ is a probability measure also when $X$ is not measurable, because it is then a Dirac measure.
  Hence $H(X) >= 0$ by the push-forward lemma, and $sum_s p_s = 1$.
  For the upper bound, apply Gibbs' inequality with $q_s := 1 \/ |S|$.
  Then $q_s > 0$ and $sum_s q_s = 1 = sum_s p_s$.
  Since $sum_s p_s log q_s = -log |S|$, we get $-log |S| <= sum_s p_s log p_s = -H(X)$.
  Neither bound uses the measurability of $X$.
]

#lemma(
  "The core inequality",
  lean: ("Meat.sum_mul_log_map_mul_map_div_map", "Meat.sum_map_mul_map_div_map_le_one"),
)[][
  Write $P := f_* nu$, $Q := g_* nu$, $R := k_* nu$ and $nu_a := nu({a})$, and let
  $ q_a := P_(f(a)) Q_(g(a)) \/ R_(k(a)). $
  (1) If $nu_a > 0$, then $P_(f(a))$, $Q_(g(a))$ and $R_(k(a))$ are at least $nu_a$, so they are positive.
  Then $nu_a log q_a = nu_a (log P_(f(a)) + log Q_(g(a)) - log R_(k(a)))$.
  This equation is also true when $nu_a = 0$.
  Sum over $a$ and apply the push-forward lemma to $f$, $g$ and $k$.
  (2) Because $a |-> (f(a), g(a))$ is injective and all terms are nonnegative,
  $ sum_a q_a <= sum_(b in B) P_b / R_(phi(b)) sum_(c : psi(c) = phi(b)) Q_c. $
  Since $psi_* Q = (psi compose g)_* nu = R$, the inner sum is $R_(phi(b))$.
  Thus each outer term is at most $P_b$, and $sum_b P_b = 1$.
]

#theorem(
  "Basic inequalities",
  lean: ("Meat.condEntropy_nonneg", "Meat.mutualInfo_nonneg", "Meat.condMutualInfo_nonneg"),
)[][
  Let $nu$ be a probability measure on a finite set $A$ and write $nu_a := nu({a})$.

  _Step 1: the core inequality._
  Let $f : A -> B$, $g : A -> C$ and $k : A -> D$, with $a |-> (f(a), g(a))$ injective.
  Assume $k = phi compose f = psi compose g$ for some maps $phi : B -> D$ and $psi : C -> D$.
  We show
  $ H(nu) + H(k_* nu) <= H(f_* nu) + H(g_* nu). $
  Let $q_a$ be as in the core inequality.
  If $nu_a > 0$, then $q_a > 0$, because each factor of $q_a$ is at least $nu_a$.
  By the core inequality, $sum_a q_a <= 1 = sum_a nu_a$ and
  $ sum_a nu_a log q_a = H(k_* nu) - H(f_* nu) - H(g_* nu). $
  Gibbs' inequality with $p_a := nu_a$ now gives $H(k_* nu) - H(f_* nu) - H(g_* nu) <= -H(nu)$.

  _Step 2: the three inequalities._
  For a measurable $W : Omega -> A$ and every map $f$, $(f compose W)_* mu = f_* (W_* mu)$.
  Let $nu$ be the law of $(X, Y)$.
  Let $pi(x, y) := y$, so $Y_* mu = pi_* nu$.
  Then $H(X given Y) = H(nu) - H(pi_* nu) >= 0$ by the push-forward lemma.
  For $I(X; Y)$, apply step 1 with $f(x, y) := x$, $g(x, y) := y$ and $D$ a one-point set.
  Then $H(k_* nu) >= 0$ by the push-forward lemma, so $H(X, Y) <= H(X) + H(Y)$.
  For $I(X; Y given Z)$, let $nu$ be the law of $((X, Y), Z)$.
  Apply step 1 with $f((x, y), z) := (x, z)$, $g((x, y), z) := (y, z)$ and $k((x, y), z) := z$.
  This gives
  $ I(X; Y given Z) = H(X, Z) + H(Y, Z) - H((X, Y), Z) - H(Z) >= 0. $
]

#proposition("Symmetry", lean: ("Meat.mutualInfo_comm", "Meat.condMutualInfo_comm"))[][
  By relabeling, $H(X, Y) = H(Y, X)$, and the first identity follows from the definition.
  Also by relabeling, $H((X, Y), Z) = H((Y, X), Z)$, so $H((X, Y) given Z) = H((Y, X) given Z)$, and the second identity follows.
  Neither identity needs measurability or a probability measure.
]

#corollary(
  "Consequences",
  lean: (
    "Meat.condEntropy_le_entropy",
    "Meat.entropy_pair_le_add",
    "Meat.entropy_le_entropy_pair",
    "Meat.entropy_submodular",
  ),
)[][
  (1) $H(X) - H(X given Y) = I(X; Y) >= 0$.
  (2) $H(X) + H(Y) - H(X, Y) = I(X; Y) >= 0$.
  (3) By relabeling, $H(X, Y) - H(X) = H(Y, X) - H(X) = H(Y given X) >= 0$.
  (4) Expanding each conditional entropy as $H(A given Z) = H(A, Z) - H(Z)$ gives
  $ I(X; Y given Z) = H(X, Z) + H(Y, Z) - H((X, Y), Z) - H(Z) >= 0. $
]

#lemma("Functions do not increase entropy", lean: "Meat.entropy_comp_le")[][
  Every map $f : S -> T$ is measurable, because $S$ is finite and its singletons are measurable.
  By relabeling and the definition of conditional entropy,
  $ H(X) = H(X, f compose X) = H(f compose X) + H(X given f compose X) >= H(f compose X). $
]

#proposition("Chain rule for mutual information", lean: "Meat.mutualInfo_pair_eq_add_condMutualInfo")[][
  Expanding the definitions,
  $ I(X; Z) + I(X; Y given Z) = H(X) + H(Y, Z) - H((X, Y), Z), $
  $ I(X; (Y, Z)) = H(X) + H(Y, Z) - H(X, (Y, Z)). $
  The two right sides are equal because $H((X, Y), Z) = H(X, (Y, Z))$ by relabeling.
  No measurability and no probability assumption is necessary.
]

#theorem("Data processing", lean: "Meat.mutualInfo_comp_le")[][
  By relabeling with the injections $t |-> (t, f(t))$ and $(s, t) |-> (s, (t, f(t)))$, $H(Y, f compose Y) = H(Y)$ and $H(X, (Y, f compose Y)) = H(X, Y)$.
  Hence $I(X; (Y, f compose Y)) = I(X; Y)$.
  The map $f compose Y$ is measurable, because $f$ is.
  By the chain rule for mutual information and $I(X; Y given f compose Y) >= 0$,
  $ I(X; Y) = I(X; (Y, f compose Y)) = I(X; f compose Y) + I(X; Y given f compose Y) >= I(X; f compose Y). $
]

== Divergence
#source("Meat.Shannon.Divergence")

In this section, $S$ and $T$ are finite sets, and each singleton is measurable.
For a measure $nu$ on $S$, write $nu_s := nu({s})$ as before.
The divergence is a real number, defined as a finite sum with the Lean conventions $log 0 = 0$ and $x \/ 0 = 0$.
The usual definition is $+infinity$ when some $s$ has $nu_s > 0$ and $rho_s = 0$.
At such an $s$, the Lean sum has the term $nu_s log 0 = 0$, which has no meaning.
Thus each result that needs the true value assumes $nu << rho$.
On a finite set, $nu << rho$ means that $rho_s = 0$ implies $nu_s = 0$ for every $s$.
We use real values for the same reason that entropy is real.
The chain rule and the identities for $I(X; Y)$ and $H(X)$ are then linear equations in $RR$.
Later files add and subtract these equations, and with values in $[0, infinity]$ each step would need a finiteness condition.
In the two identities, $nu << rho$ is always true, so they have no assumption.
Mathlib has a general divergence `InformationTheory.klDiv` with values in $[0, infinity]$.
It uses Radon-Nikodym derivatives and integrals.
Here each quantity is a finite sum, so we do not use it.

#definition("Divergence", lean: "Meat.klDiv")[
  Let $nu$ and $rho$ be measures on $S$.
  The Kullback-Leibler divergence of $nu$ from $rho$ is
  $ D(nu || rho) := sum_(s in S) nu_s log (nu_s / rho_s). $
]

#definition("Conditional divergence", lean: "Meat.condKLDiv")[
  Let $nu$ and $rho$ be measures on $S$ and let $f : S -> T$.
  Write $N := f_* nu$ and $R := f_* rho$.
  The divergence of $nu$ from $rho$ given $f$ is
  $ D_f (nu || rho) := sum_(s in S) nu_s log ((nu_s R_(f(s))) / (rho_s N_(f(s)))). $
]

If all the numbers are positive, then $nu_s \/ N_(f(s))$ is the probability of $s$ under $nu$, given the fiber of $f$ that contains $s$.
The same is true for $rho_s \/ R_(f(s))$ and $rho$.
Thus $D_f (nu || rho)$ is the divergence between the conditional laws on each fiber, averaged with the weights $N$.
As a single finite sum, it does not need conditional distributions.

#proposition("Divergence from itself", lean: "Meat.klDiv_self")[][
  If $nu_s > 0$, the term is $nu_s log 1 = 0$.
  If $nu_s = 0$, the term is $0$.
  No assumption on $nu$ is necessary.
]

#theorem("Gibbs' inequality for divergence", lean: ("Meat.klDiv_nonneg", "Meat.klDiv_eq_zero_iff"))[][
  If $nu_s > 0$, then $rho_s > 0$ because $nu << rho$, so $nu_s log (nu_s \/ rho_s) = nu_s log nu_s - nu_s log rho_s$.
  If $nu_s = 0$, both sides are $0$.
  Hence
  $ D(nu || rho) = sum_s nu_s log nu_s - sum_s nu_s log rho_s. $
  Apply Gibbs' inequality with $p := nu$ and $q := rho$.
  Its assumptions hold: both sums are $1$, and $q_s = 0$ implies $p_s = 0$.
  Thus $sum_s nu_s log rho_s <= sum_s nu_s log nu_s$, which is $D(nu || rho) >= 0$.
  If $D(nu || rho) = 0$, then the two sums are equal.
  The equality case of Gibbs' inequality then gives $rho_s = nu_s$ for each $s$.
  A measure on a finite set is determined by its values on singletons, so $nu = rho$.
  The converse is the preceding proposition.
]

#theorem(
  "Chain rule for divergence",
  lean: (
    "Meat.klDiv_eq_klDiv_map_add_condKLDiv",
    "Meat.condKLDiv_nonneg",
    "Meat.klDiv_map_le",
  ),
)[][
  Write $N := f_* nu$ and $R := f_* rho$.
  For every $g : T -> RR$, group the terms by the fibers of $f$, as in the lemma on singletons and push-forwards:
  $ sum_s nu_s g(f(s)) = sum_t N_t g(t). $
  With $g(t) := log (N_t \/ R_t)$, this gives $D(N || R) = sum_s nu_s log (N_(f(s)) \/ R_(f(s)))$.
  Now compare the terms for each $s$.
  If $nu_s = 0$, all of them are $0$.
  If $nu_s > 0$, then $rho_s > 0$ because $nu << rho$, and $N_(f(s)) >= nu_s > 0$ and $R_(f(s)) >= rho_s > 0$.
  Since $N_(f(s)) / R_(f(s)) dot (nu_s R_(f(s))) / (rho_s N_(f(s))) = nu_s / rho_s$, the logarithms add.
  This proves the chain rule.

  For $D_f (nu || rho) >= 0$, let $p_s := nu_s$ and $q_s := rho_s N_(f(s)) \/ R_(f(s))$.
  Then $p_s \/ q_s = nu_s R_(f(s)) \/ (rho_s N_(f(s)))$, also when a denominator is $0$.
  Suppose that $q_s = 0$.
  If $rho_s = 0$, then $p_s = 0$ because $nu << rho$.
  If $N_(f(s)) = 0$, then $p_s <= N_(f(s)) = 0$.
  If $R_(f(s)) = 0$, then $rho_s <= R_(f(s)) = 0$, so again $p_s = 0$.
  By the same grouping for $rho$,
  $ sum_s q_s = sum_t R_t N_t / R_t <= sum_t N_t = sum_s p_s, $
  because the term for $t$ is $N_t$ if $R_t > 0$ and $0$ if $R_t = 0$.
  As in the proof of Gibbs' inequality for divergence, Gibbs' inequality gives $sum_s p_s log (p_s \/ q_s) >= 0$.
  This is the log-sum inequality, applied on each fiber of $f$.
  The last statement follows from the first two.
]

Let $S = A times B$ and let $f$ be the projection to $A$.
Then the chain rule is $D(P_(A B) || Q_(A B)) = D(P_A || Q_A) + D_f (P_(A B) || Q_(A B))$.
The last term is the divergence of the conditional laws of $B$ given $A$, averaged over $P_A$.

In the next theorem, $times.o$ is the product measure.

#theorem("Mutual information as a divergence", lean: "Meat.mutualInfo_eq_klDiv")[][
  Let $nu := (X, Y)_* mu$, $P := X_* mu$ and $Q := Y_* mu$.
  Then $(P times.o Q)({(x, y)}) = P_x Q_y$, because ${(x, y)} = {x} times {y}$.
  Because $X$ and $Y$ are measurable, $P$ and $Q$ are the push-forwards of $nu$ by the two projections.
  If $nu_(x y) > 0$, then $P_x >= nu_(x y) > 0$ and $Q_y >= nu_(x y) > 0$, so
  $ nu_(x y) log (nu_(x y) / (P_x Q_y)) = nu_(x y) log nu_(x y) - nu_(x y) log P_x - nu_(x y) log Q_y. $
  If $nu_(x y) = 0$, both sides are $0$.
  Sum over $(x, y)$ and apply the push-forward lemma to the two projections.
  This gives $D(nu || P times.o Q) = -H(X, Y) + H(X) + H(Y) = I(X; Y)$.
  The positivity argument above also shows that $nu << P times.o Q$, so this assumption is not necessary.
]

Let $cal(U)(S)$ be the uniform probability measure on $S$, so $cal(U)(S)({s}) = 1 \/ |S|$ for each $s$.
In Lean, it is `uniformOn univ`.

#theorem(
  "Entropy as a divergence",
  lean: ("Meat.measureEntropy_eq_log_card_sub_klDiv", "Meat.entropy_eq_log_card_sub_klDiv"),
)[][
  Write $u := cal(U)(S)$, so $u_s = 1 \/ |S|$.
  If $nu_s > 0$, then $|S| > 0$ and $nu_s log (nu_s \/ u_s) = nu_s log (nu_s |S|) = nu_s log nu_s + nu_s log |S|$.
  If $nu_s = 0$, both sides are $0$.
  Since $sum_s nu_s = 1$, the sum is $D(nu || u) = -H(nu) + log |S|$.
  For the second statement, $X_* mu$ is a probability measure in Lean also when $X$ is not measurable, so no measurability is necessary.
  Together with Gibbs' inequality for divergence, this gives $H(X) <= log |S|$ again, with equality if and only if $X_* mu = cal(U)(S)$.
]

== Markov chains
#source("Meat.Shannon.Markov")

In this section, $X : Omega -> S$, $Y : Omega -> T$ and $Z : Omega -> U$.
A Markov chain is defined by an information quantity, in the style of the rest of this chapter.
The usual definition by conditional distributions is then a theorem.
That theorem needs the case of equality in Gibbs' inequality.

#definition("Markov chain", lean: ("Meat.MarkovChain", "Meat.markovChain_def"))[
  The random variables $X$, $Y$, $Z$ form a Markov chain $X -> Y -> Z$ under $mu$ if
  $ I(X; Z given Y) = 0. $
]

The Lean notation is `MarkovChain X Y Z μ`.

#proposition(lean: "Meat.mutualInfo_add_condMutualInfo_comm")[][
  By the chain rule for mutual information, the left side is $I(X; (Z, Y))$ and the right side is $I(X; (Y, Z))$.
  Expanding the definitions, the left side is $H(X) + H(Z, Y) - H((X, Z), Y)$.
  The right side is $H(X) + H(Y, Z) - H((X, Y), Z)$.
  The two are equal by relabeling with $(z, y) |-> (y, z)$ and $((x, z), y) |-> ((x, y), z)$.
  No measurability and no probability assumption is necessary.
]

#proposition("Symmetry", lean: ("Meat.markovChain_comm", "Meat.MarkovChain.symm"))[][
  $I(X; Z given Y) = I(Z; X given Y)$ by the symmetry of conditional mutual information.
]

#proposition("Functions of the middle variable", lean: "Meat.markovChain_comp")[][
  By relabeling, $H(f compose Y, Y) = H(Y)$ and $H((X, f compose Y), Y) = H(X, Y)$.
  Expanding the definitions,
  $ I(X; f compose Y given Y) = (H(X, Y) - H(Y)) + (H(f compose Y, Y) - H(Y)) - (H((X, f compose Y), Y) - H(Y)) = 0. $
  No measurability and no probability assumption is necessary.
]

#theorem(
  "Data processing inequality",
  lean: (
    "Meat.MarkovChain.mutualInfo_le_left",
    "Meat.MarkovChain.mutualInfo_le_right",
    "Meat.MarkovChain.condMutualInfo_le",
  ),
)[][
  Since $I(X; Z given Y) = 0$, the identity above gives
  $ I(X; Y) = I(X; Z) + I(X; Y given Z). $
  Both terms on the right are nonnegative by the basic inequalities.
  So $I(X; Z) <= I(X; Y)$ and $I(X; Y given Z) <= I(X; Y)$.
  By symmetry, $Z -> Y -> X$, so $I(Z; X) <= I(Z; Y)$.
  The symmetry of mutual information gives $I(X; Z) <= I(Y; Z)$.
]

#lemma("Conditioning on a function", lean: "Meat.condEntropy_le_condEntropy_comp")[][
  Write $V := f compose Y$.
  By relabeling, $H(Y, V) = H(Y)$ and $H((X, Y), V) = H(X, Y)$.
  Expanding $I(X; Y given V) >= 0$ gives
  $ H(X, V) - H(V) >= H((X, Y), V) - H(Y, V) = H(X, Y) - H(Y). $
  The left side is $H(X given V)$ and the right side is $H(X given Y)$.
]

#theorem("Factorization", lean: "Meat.markovChain_iff")[
  Let $mu$ be a probability measure and let $X$, $Y$ and $Z$ be measurable.
  Write $p(x, y, z) := mu{X = x, Y = y, Z = z}$, $p(x, y) := mu{X = x, Y = y}$, $p(y, z) := mu{Y = y, Z = z}$ and $p(y) := mu{Y = y}$.
  Then $X -> Y -> Z$ if and only if
  $ p(x, y, z) p(y) = p(x, y) p(y, z) $
  for all $x in S$, $y in T$ and $z in U$.
][
  Let $nu$ be the law of $((X, Z), Y)$ on $A := (S times U) times T$, and write $nu_a := nu({a})$.
  Let $f((x, z), y) := (x, y)$, $g((x, z), y) := (z, y)$ and $k((x, z), y) := y$.
  Write $P := f_* nu$, $Q := g_* nu$ and $R := k_* nu$.
  These are the laws of $(X, Y)$, $(Z, Y)$ and $Y$.
  By definition, $I(X; Z given Y) = H(P) + H(Q) - H(nu) - H(R)$.
  Let $q_a := P_(f(a)) Q_(g(a)) \/ R_(k(a))$, as in the core inequality.
  The map $a |-> (f(a), g(a))$ is injective, and $k$ is the projection to $T$ composed with $f$ and with $g$.
  So the core inequality gives $sum_a q_a <= 1$ and
  $ I(X; Z given Y) = sum_a nu_a log nu_a - sum_a nu_a log q_a. $
  If $q_a = 0$, then $nu_a = 0$, because $P_(f(a))$, $Q_(g(a))$ and $R_(k(a))$ are at least $nu_a$.
  By the equality case of Gibbs' inequality, $I(X; Z given Y) = 0$ if and only if $q_a = nu_a$ for every $a$.
  Fix $a = ((x, z), y)$.
  If $R_y > 0$, then $q_a = nu_a$ is the equation $nu_a R_y = P_(x, y) Q_(z, y)$.
  If $R_y = 0$, then $nu_a = 0$, $P_(x, y) = 0$ and $q_a = 0$, so both conditions hold.
  Finally, $nu_a = p(x, y, z)$, $P_(x, y) = p(x, y)$, $Q_(z, y) = p(y, z)$ and $R_y = p(y)$, because $X$, $Y$ and $Z$ are measurable.
]

== Fano's inequality
#source("Meat.Shannon.Fano")

In this section, $mu$ is a probability measure and $X : Omega -> S$ is measurable.
An estimator of $X$ is a measurable map $hat(X) : Omega -> S$.
Its error probability is $P_e := mu{hat(X) != X}$.
The binary entropy is $h(p) := -p log p - (1 - p) log (1 - p)$, which is `Real.binEntropy` in Mathlib.

#theorem("Fano's inequality", lean: "Meat.condEntropy_le_binEntropy_add_mul_log")[
  For every measurable estimator $hat(X)$ of $X$,
  $ H(X given hat(X)) <= h(P_e) + P_e log (|S| - 1). $
][
  The usual proof uses the error indicator $E := [hat(X) != X]$ and the chain rule for $H(X, E given hat(X))$.
  We use one application of Gibbs' inequality instead, which needs no conditional entropy given an event.
  Let $nu$ be the law of $(X, hat(X))$ on $S times S$, and write $nu_(x, s) := nu({(x, s)})$.
  Let $R_s := mu{hat(X) = s}$ be the law of $hat(X)$, and write $p := P_e$ and $n := |S| - 1$.
  The sum of $nu$ off the diagonal is $p$, and the sum on the diagonal is $1 - p$.
  Let
  $ c(x, s) := cases(1 - p & "if" x = s, p \/ n & "if" x != s,) quad q_(x, s) := R_s c(x, s). $
  For fixed $s$, $sum_x c(x, s) = (1 - p) + n dot p \/ n$, which is $1$ if $n > 0$ and $1 - p$ if $n = 0$.
  Hence $sum_(x, s) q_(x, s) <= sum_s R_s = 1$.
  If $nu_(x, s) > 0$, then $q_(x, s) > 0$.
  Indeed, $R_s >= nu_(x, s)$.
  On the diagonal, $1 - p >= nu_(x, s)$.
  Off the diagonal, $p >= nu_(x, s)$, and $n >= 1$ because $x != s$.
  Gibbs' inequality gives $sum nu_(x, s) log q_(x, s) <= sum nu_(x, s) log nu_(x, s) = -H(X, hat(X))$.
  Split the left side into $sum nu_(x, s) log R_s$ and $sum nu_(x, s) log c(x, s)$.
  By the push-forward lemma, the first part is $-H(hat(X))$.
  The second part is $(1 - p) log (1 - p) + p log (p \/ n)$.
  If $p > 0$, some off-diagonal $nu_(x, s)$ is positive, so $n > 0$ and $p log (p \/ n) = p log p - p log n$.
  This equation is also true if $p = 0$.
  Hence
  $ -H(hat(X)) - h(p) - p log n <= -H(X, hat(X)), $
  that is, $H(X given hat(X)) = H(X, hat(X)) - H(hat(X)) <= h(p) + p log n$.
]

#corollary(
  "Fano's inequality for a decoder",
  lean: ("Meat.condEntropy_le_binEntropy_add_mul_log_of_comp", "Meat.condEntropy_le_log_two_add_mul_log_card"),
)[
  Let $Y : Omega -> T$ be measurable, let $g : T -> S$ and let $P_e := mu{g compose Y != X}$.
  Then
  $ H(X given Y) <= h(P_e) + P_e log (|S| - 1) quad "and" quad H(X given Y) <= log 2 + P_e log |S|. $
][
  By conditioning on a function, $H(X given Y) <= H(X given g compose Y)$.
  Apply Fano's inequality to the estimator $hat(X) := g compose Y$, which is measurable because $g$ is.
  For the second bound, $h(P_e) <= log 2$.
  Also $log (|S| - 1) <= log |S|$: if $|S| >= 2$, this is monotonicity of $log$, and if $|S| <= 1$, both sides are $0$.
  Multiply by $P_e >= 0$.
]

== Typical sequences
#source("Meat.Shannon.Typical")

A source emits $n$ independent symbols with the same law $p$ on a finite alphabet $S$.
In Lean, $p$ is a `PMF S`, as in the channel and source coding files.
Its entropy is $H(p) := H(nu_p)$, where $nu_p$ is the measure of $p$.
A sequence is a map $x : {1, ..., n} -> S$.
Write $p_s$ for the real number $p(s)$.

#definition("Product probability", lean: ("Meat.iidProb", "Meat.iidProb_nonneg", "Meat.sum_iidProb"))[
  The probability of a sequence $x$ is
  $ p^n (x) := product_(i = 1)^n p_(x_i). $
  Then $p^n (x) >= 0$ and $sum_x p^n (x) = 1$.
][
  By distributivity, $sum_x product_i p_(x_i) = product_i sum_s p_s = 1$.
]

#lemma("Total mass", lean: ("Meat.sum_pmf_eq_one", "Meat.sum_toReal_pmf_eq_one"))[
  A law $p$ on a finite set $S$ has $sum_s p(s) = 1$ in $[0, infinity]$ and $sum_s p_s = 1$ in $RR$.
][
  On a finite set the series of $p$ is a finite sum, and its value is $1$.
  Each $p(s)$ is finite, so the real value of the sum is the sum of the real values.
]

#lemma(
  "Push-forward of a law",
  lean: ("Meat.toReal_map_apply", "Meat.PMF.map_apply_of_injective"),
)[
  Let $p$ be a law on a finite set $Omega$, let $g : Omega -> Omega'$ and let $g_* p$ be its push-forward.
  Then $(g_* p)(t) = sum_(s : g(s) = t) p(s)$.
  If $g$ is injective, then $(g_* p)(g(s)) = p(s)$ for every $s$, also on an infinite set.
][
  The first identity is the definition of the push-forward on a finite set.
  If $g$ is injective, only $s$ itself is sent to $g(s)$.
]

#lemma("Entropy of a probability mass function", lean: "Meat.measureEntropy_toMeasure")[][
  Each singleton is measurable, so $nu_p ({s}) = p(s)$.
]

#lemma(
  "Logarithm of a product probability",
  lean: ("Meat.negMulLog_iidProb", "Meat.sum_toReal_mul_neg_log"),
)[
  For every sequence $x$,
  $ eta(p^n (x)) = p^n (x) sum_i (-log p_(x_i)). $
  Also $sum_s p_s (-log p_s) = H(p)$.
][
  If $p^n (x) > 0$, then $log p^n (x) = sum_i log p_(x_i)$, because every factor is positive.
  If $p^n (x) = 0$, both sides are $0$.
  The second identity is $eta(t) = t (-log t)$ in each term of $H(p)$.
]

#definition("Typical set", lean: ("Meat.typicalSet", "Meat.iidProb_pos_of_mem_typicalSet", "Meat.mem_typicalSet_iff"))[
  Let $epsilon in RR$.
  The weakly typical set $A_epsilon^((n))$ is the set of sequences $x$ with
  $ e^(-n (H(p) + epsilon)) <= p^n (x) <= e^(-n (H(p) - epsilon)). $
  Every typical sequence has $p^n (x) > 0$.
  For $n > 0$, $x in A_epsilon^((n))$ if and only if $p^n (x) > 0$ and
  $ abs(-1/n log p^n (x) - H(p)) <= epsilon. $
][
  The lower bound is positive, so $p^n (x) > 0$.
  Then take logarithms of the two bounds and divide by $n$.
]

The two-sided bound is the definition, and the logarithmic form is a lemma.
With the logarithmic form alone, a sequence with $p^n (x) = 0$ would have $log p^n (x) = 0$ in Lean.
Such a sequence could then be typical, and the size bound below would fail.

#theorem("Asymptotic equipartition property", lean: "Meat.tendsto_sum_iidProb_typicalSet")[][
  Let $f(s) := -log p_s$ and $Y(s) := f(s) - H(p)$.
  Then $sum_s p_s f(s) = H(p)$, so $sum_s p_s Y(s) = 0$.
  Let $sigma^2 := sum_s p_s Y(s)^2$.
  For coordinates $i$ and $j$, write $Y(x_i) Y(x_j)$ as a product over all coordinates $k$ of factors $g_k (x_k)$.
  By distributivity,
  $ sum_x p^n (x) Y(x_i) Y(x_j) = product_k sum_s p_s g_k (s). $
  If $i != j$, the factor for $k = i$ is $sum_s p_s Y(s) = 0$.
  If $i = j$, the factor for $k = i$ is $sigma^2$ and every other factor is $1$.
  Hence
  $ sum_x p^n (x) (sum_i Y(x_i))^2 = n sigma^2. $
  Let $n > 0$ and let $x in.not A_epsilon^((n))$ with $p^n (x) > 0$.
  Then $-log p^n (x) = sum_i f(x_i)$ by the logarithm lemma, so $-1/n log p^n (x) - H(p) = 1/n sum_i Y(x_i)$.
  By the logarithmic form of typicality, $(n epsilon)^2 < (sum_i Y(x_i))^2$.
  So $p^n (x) <= p^n (x) (sum_i Y(x_i))^2 \/ (n epsilon)^2$.
  This is also true if $p^n (x) = 0$.
  Sum over all $x in.not A_epsilon^((n))$, and bound by the sum over all $x$.
  This is Chebyshev's inequality:
  $ 1 - p^n (A_epsilon^((n))) <= (n sigma^2) / (n epsilon)^2 = sigma^2 / (n epsilon^2). $
  The right side tends to $0$, and $p^n (A_epsilon^((n))) <= 1$.
]

The proof needs no law of large numbers from Mathlib.
On a finite alphabet, the variance $sigma^2$ is a finite sum.

#theorem("Size of the typical set", lean: ("Meat.card_typicalSet_le", "Meat.eventually_le_card_typicalSet"))[][
  Each typical $x$ has $p^n (x) >= e^(-n (H(p) + epsilon))$.
  So $abs(A_epsilon^((n))) e^(-n (H(p) + epsilon)) <= p^n (A_epsilon^((n))) <= 1$.
  For the lower bound, the asymptotic equipartition property gives $p^n (A_epsilon^((n))) >= 1 - epsilon$ for all large $n$.
  Each typical $x$ has $p^n (x) <= e^(-n (H(p) - epsilon))$.
  So $1 - epsilon <= abs(A_epsilon^((n))) e^(-n (H(p) - epsilon))$.
]

Now let $p$ be a law on $S times T$.
Let $p_1$ and $p_2$ be its marginals on $S$ and $T$.
A pair of sequences $(x, y)$ is also the sequence $i |-> (x_i, y_i)$ in $S times T$.
In this subsection, $p^n (x, y)$ is the probability of that sequence.

#lemma("Marginals", lean: ("Meat.sum_iidProb_pair_right", "Meat.sum_iidProb_pair_left", "Meat.sum_iidProb_pair"))[
  $ sum_y p^n (x, y) = p_1^n (x), quad sum_x p^n (x, y) = p_2^n (y), quad sum_(x, y) p^n (x, y) = 1. $
][
  By distributivity, $sum_y product_i p_(x_i, y_i) = product_i sum_t p_(x_i, t) = product_i p_1 (x_i)$.
  Here $p_1 (s) = sum_t p(s, t)$, by the lemma on push-forwards.
  For the last identity, sum the first one over $x$ and use $sum_x p_1^n (x) = 1$.
]

#definition("Jointly typical set", lean: "Meat.jointlyTypicalSet")[
  The jointly typical set $J_epsilon^((n))$ is the set of pairs $(x, y)$ with
  $x in A_epsilon^((n)) (p_1)$, $y in A_epsilon^((n)) (p_2)$ and $(x, y) in A_epsilon^((n)) (p)$.
]

#theorem("Joint asymptotic equipartition property", lean: "Meat.tendsto_sum_iidProb_jointlyTypicalSet")[
  Let $epsilon > 0$.
  Then $p^n (J_epsilon^((n))) -> 1$ as $n -> infinity$.
][
  A pair outside $J_epsilon^((n))$ fails one of the three conditions.
  So $1 - p^n (J_epsilon^((n)))$ is at most the sum of three terms.
  By the marginal lemma, the first term is $1 - p_1^n (A_epsilon^((n)) (p_1))$.
  In the same way, the second term is $1 - p_2^n (A_epsilon^((n)) (p_2))$.
  The map $(x, y) |-> (i |-> (x_i, y_i))$ is a bijection, so the third term is $1 - p^n (A_epsilon^((n)) (p))$.
  Each term tends to $0$ by the asymptotic equipartition property.
  Also $p^n (J_epsilon^((n))) <= 1$.
]

#theorem(
  "Size of the jointly typical set",
  lean: ("Meat.card_jointlyTypicalSet_le", "Meat.sum_iidProb_mul_iidProb_jointlyTypicalSet_le"),
)[
  For every $n$ and $epsilon$,
  $ abs(J_epsilon^((n))) <= e^(n (H(p) + epsilon)). $
  Let $tilde(X)^n$ and $tilde(Y)^n$ be independent, with laws $p_1^n$ and $p_2^n$.
  Let $I$ be the mutual information of the two coordinates under $p$.
  Then
  $ sum_((x, y) in J_epsilon^((n))) p_1^n (x) p_2^n (y) <= e^(-n (I - 3 epsilon)). $
][
  The map $(x, y) |-> (i |-> (x_i, y_i))$ is injective and sends $J_epsilon^((n))$ into $A_epsilon^((n)) (p)$.
  So the first bound follows from the size of the typical set.
  For each $(x, y) in J_epsilon^((n))$,
  $ p_1^n (x) p_2^n (y) <= e^(-n (H(p_1) - epsilon)) e^(-n (H(p_2) - epsilon)). $
  Multiply by $abs(J_epsilon^((n)))$ and use the first bound.
  The exponent is $n (H(p) + epsilon) - n (H(p_1) - epsilon) - n (H(p_2) - epsilon) = -n (I - 3 epsilon)$.
  Here $I = H(p_1) + H(p_2) - H(p)$, because the push-forward of $nu_p$ by a coordinate is the measure of the marginal.
]

The mutual information in this bound is `mutualInfo` of the two coordinate maps under $nu_p$.
For the channel $W$ and input law $q$, take $p$ to be the law of the pair (input, output).
Then $nu_p$ is `jointMeasure W q`, and $I$ is the information `inputMutualInfo W q` of the channel coding theorem.

#lemma("Exponential decay", lean: "Meat.tendsto_exp_nat_mul")[
  If $c < 0$, then $e^(n c) -> 0$ as $n -> infinity$.
][
  $e^(n c) = (e^c)^n$ and $0 < e^c < 1$.
]

The coding proofs in later chapters use this lemma to show that the exponential terms of their error bounds tend to $0$.

== Averages
#source("Meat.Shannon.Average")

Random codes are analyzed through finite weighted sums.
Let $iota$ and $X$ be finite sets, and let $w_i : X -> RR$ for each $i in iota$.
A map $C : iota -> X$ gets the product weight $product_i w_i (C(i))$.
If each $w_i$ is a probability mass function, this weight is the law of independent entries $C(i)$ with laws $w_i$.
In most uses all $w_i$ are the same law $w$.

#lemma("Sum over a complement", lean: "Meat.sum_ite_mem_zero")[
  Let $X$ be a finite set, let $s subset.eq X$ and let $f : X -> RR$.
  Then
  $ sum_(x in X without s) f(x) = sum_(x in X) f(x) - sum_(x in s) f(x). $
  In Lean the left side is a sum over all $x$ of $f(x)$ if $x in.not s$ and $0$ otherwise.
][
  Split the sum over all $x$ into the sum over $s$ and the sum over the complement of $s$.
  The terms in $s$ are $0$ on the left side.
]

#lemma("Weighted average", lean: "Meat.exists_le_of_sum_mul_le")[][
  Suppose that $f(i) > t$ for every $i$.
  Since $sum_i w(i) = 1$, some $w(j) > 0$.
  So $sum_i w(i) f(i) > sum_i w(i) t = t$, which is a contradiction.
]

#lemma(
  "Product weights",
  lean: (
    "Meat.sum_prod_mul_prod",
    "Meat.sum_prod",
    "Meat.sum_prod_mul_apply",
    "Meat.sum_prod_mul_apply_mul_apply",
    "Meat.sum_prod_mul_apply_apply",
  ),
)[][
  The first identity is distributivity: the product $product_i sum_x w_i (x) g_i (x)$ expands to a sum over all maps $C$.
  The other identities assume $sum_x w_i (x) = 1$ for every $i$.
  For the second identity, take $g_i = 1$ for every $i$.
  For the third, take $g_j = f$ and $g_i = 1$ for $i != j$.
  For the fourth, take $g_j = f$, $g_k = g$ and $g_i = 1$ for the other $i$.
  Each factor with $g_i = 1$ is equal to $1$.
  For the last, write $F(C(j), C(k)) = sum_(x, x') [C(j) = x] [C(k) = x'] F(x, x')$, where $[P]$ is $1$ if $P$ is true and $0$ otherwise.
  By the fourth identity, the average of $[C(j) = x] [C(k) = x']$ is $w_j (x) w_k (x')$.
]

#lemma("Sums over pair sequences", lean: "Meat.sum_arrow_prod")[
  For every $f : (S times T)^iota -> RR$,
  $ sum_u f(u) = sum_(a in S^iota) sum_(b in T^iota) f((a_i, b_i)_i). $
][
  The map $u |-> ((u_i)_1, (u_i)_2)$ is a bijection from $(S times T)^iota$ to $S^iota times T^iota$.
]

== Sequences of random variables
#source("Meat.Shannon.Product")

A random sequence is a map $Y : Omega -> S^n$.
Its coordinates are the random variables $Y_i : omega |-> Y(omega)_i$.
In this section, $H_mu$ is the entropy under the measure $mu$.

#lemma(
  "Information under a push-forward",
  lean: ("Meat.entropy_map", "Meat.condEntropy_map", "Meat.mutualInfo_map", "Meat.condMutualInfo_map"),
)[
  Let $g : Omega -> Omega'$ and $X : Omega' -> S$ be measurable.
  Then $H_(g_* mu) (X) = H_mu (X compose g)$.
  For measurable $Y$ and $Z$, each of $H(X given Y)$, $I(X; Y)$ and $I(X; Y given Z)$ under $g_* mu$ is the same quantity for $X compose g$, $Y compose g$ and $Z compose g$ under $mu$.
][
  Both sides of the first identity are the entropy of the measure $X_* (g_* mu) = (X compose g)_* mu$.
  Each other quantity is a sum and difference of entropies of $X$, $Y$, $Z$ and their pairs.
]

#lemma("Uniform entropy", lean: "Meat.entropy_eq_log_card")[
  If $(X_* mu)({s}) = |S|^(-1)$ for every $s in S$, then $H(X) = log |S|$.
][
  Each of the $|S|$ terms is $eta(|S|^(-1)) = |S|^(-1) log |S|$.
  If $S$ is empty, both sides are $0$.
]

#theorem("Subadditivity", lean: "Meat.entropy_pi_le_sum")[
  Let $mu$ be a probability measure, and let each coordinate $Y_i$ be measurable.
  Then
  $ H(Y) <= sum_(i = 1)^n H(Y_i). $
][
  Induction on $n$.
  For $n = 0$, the set $S^0$ has one element, so $H(Y) <= log 1 = 0$.
  For $n + 1$, the map $(s, t) |-> (s, t_1, dots, t_n)$ from $S times S^n$ to $S^(n + 1)$ is injective.
  So $H(Y) = H(Y_0, (Y_1, dots, Y_n))$ by relabeling, with the coordinates numbered from $0$.
  This is at most $H(Y_0) + H(Y_1, dots, Y_n)$ by subadditivity for pairs.
  Apply the induction hypothesis to $(Y_1, dots, Y_n)$.
]

== I.i.d. sequences
#source("Meat.Shannon.Iid")

In this section, $p$ is a law on $S times T$ with marginals $p_1$ and $p_2$, as in the section on typical sequences.
Under $nu_p$, the coordinate maps are $pi_1$ and $pi_2$.

#lemma(
  "Pair laws",
  lean: ("Meat.condEntropy_fst_snd_toMeasure", "Meat.condEntropy_snd_fst_toMeasure"),
)[
  Under $nu_p$,
  $ H(pi_1 given pi_2) = H(p) - H(p_2), quad H(pi_2 given pi_1) = H(p) - H(p_1). $
][
  By definition, $H(pi_1 given pi_2) = H(pi_1, pi_2) - H(pi_2)$.
  The map $omega |-> (pi_1 (omega), pi_2 (omega))$ is the identity, so $H(pi_1, pi_2) = H(p)$.
  The push-forward of $nu_p$ by $pi_2$ is the measure of $p_2$, so $H(pi_2) = H(p_2)$.
  For the second identity, the map $omega |-> (pi_2 (omega), pi_1 (omega))$ is the swap, which is injective.
  So $H(pi_2, pi_1) = H(p)$ by relabeling.
]

#theorem("Entropy of an i.i.d. sequence", lean: "Meat.sum_negMulLog_iidProb")[
  Let $q$ be a law on a finite set $A$.
  Then
  $ sum_(x in A^n) eta(q^n (x)) = n H(q). $
][
  By the logarithm lemma, $eta(q^n (x)) = q^n (x) sum_i (-log q_(x_i))$.
  Sum over $x$ and exchange the two sums.
  The $i$-th sum depends only on $x_i$.
  By the product weights lemma and the logarithm lemma, it is $sum_a q_a (-log q_a) = H(q)$.
]

== Random binning
#source("Meat.Shannon.Binning")

A bin map $f : iota -> [k]$ puts each element of a finite set $iota$ into one of $k$ bins, where $[k] := {1, dots, k}$.
A random bin map has the constant weight $k^(-|iota|)$, which is the product weight of the uniform law on $[k]$.
So the bins of the elements are independent and uniform.

#lemma("Bin collision", lean: ("Meat.sum_uniform", "Meat.sum_uniform_mul_ite_eq"))[
  Let $k > 0$ and $a, b in iota$.
  Then $sum_(f : iota -> [k]) k^(-|iota|) = 1$ and
  $ sum_(f : iota -> [k]) k^(-|iota|) [f(a) = f(b)] = cases(1 & "if" a = b, 1 / k & "if" a != b.) $
  Here $[P]$ is $1$ if the statement $P$ is true and $0$ otherwise.
][
  The uniform law on $[k]$ sums to $1$, so the weights sum to $1$ by the product weights lemma.
  If $a = b$, the indicator is $1$.
  If $a != b$, write $[f(a) = f(b)] = sum_(m in [k]) [f(a) = m] [f(b) = m]$.
  By the product weights lemma, the average of the term for $m$ is $(1 \/ k) (1 \/ k)$.
  There are $k$ values of $m$.
]

#theorem(
  "Conditionally typical sequences",
  lean: ("Meat.card_filter_snd_jointlyTypicalSet_le", "Meat.card_filter_fst_jointlyTypicalSet_le"),
)[
  Let $p$ be a law on $S times T$, let $epsilon in RR$ and let $J := J_epsilon^((n)) (p)$.
  For every $y in T^n$ and $x in S^n$,
  $ |{x' : (x', y) in J}| <= e^(n (H(p) - H(p_2) + 2 epsilon)), quad |{y' : (x, y') in J}| <= e^(n (H(p) - H(p_1) + 2 epsilon)). $
][
  If no $x'$ has $(x', y) in J$, the left side is $0$.
  Otherwise $y in A_epsilon^((n)) (p_2)$, so $p_2^n (y) <= e^(-n (H(p_2) - epsilon))$.
  Each $x'$ with $(x', y) in J$ has $p^n (x', y) >= e^(-n (H(p) + epsilon))$.
  Sum over these $x'$.
  By the marginal lemma, the sum is at most $sum_(x') p^n (x', y) = p_2^n (y)$.
  So $|{x' : (x', y) in J}| e^(-n (H(p) + epsilon)) <= e^(-n (H(p_2) - epsilon))$.
  The second bound is the same with the roles of $S$ and $T$ exchanged.
]

== Superposition typicality
#source("Meat.Shannon.Superposition")

Superposition coding uses three sequences: a cloud center $u$, a satellite $x$ and an output $y$.
In this section, $p$ is a law on $(S times T) times R$, with $u in S^n$, $x in T^n$ and $y in R^n$.
Its marginals are $p_U$ on $S$, $p_(U X)$ on $S times T$, $p_(U Y)$ on $S times R$, $p_(X Y)$ on $T times R$ and $p_Y$ on $R$.
The section starts with tools for push-forward laws.

#lemma(
  "Push-forward of a product law",
  lean: ("Meat.iidProb_map", "Meat.sum_iidProb_mul_comp", "Meat.sum_ite_comp_eq"),
)[
  Let $p$ be a law on a finite set $Omega$, let $g : Omega -> Omega'$ and let $g_* p$ be its push-forward.
  For $y in Omega'^n$,
  $ (g_* p)^n (y) = sum_(w : g compose w = y) p^n (w). $
  So for every $F$ on $Omega'^n$,
  $ sum_w p^n (w) F(g compose w) = sum_y (g_* p)^n (y) F(y). $
  In particular, the $p^n$-probability that $g compose w$ fails a property $P$ is $1 - (g_* p)^n (P)$.
][
  By the lemma on push-forwards of a law, $(g_* p)(t) = sum_(s : g(s) = t) p(s)$.
  The product over $i$ of the sums over $s$ with $g(s) = y_i$ expands to a sum over the sequences $w$ with $g(w_i) = y_i$ for every $i$.
  For the second identity, group the sequences $w$ by the value of $g compose w$.
  For the last statement, take $F$ the indicator of the failure of $P$, and use that $(g_* p)^n$ sums to $1$.
]

#lemma("Entropy of a variable under a law", lean: "Meat.entropy_toMeasure")[
  Let $p$ be a law on a finite set $Omega$ with measure $nu_p$, and let $X : Omega -> S$.
  Then $H_(nu_p) (X) = H(X_* p)$.
][
  The measure of $X_* p$ is the push-forward of $nu_p$ by $X$.
  Every map on a finite set with measurable singletons is measurable.
]

The measure of $g_* p$ is the push-forward of $nu_p$ by $g$.
So the lemma on information under a push-forward also holds for $nu_(g_* p)$ and $nu_p$.

#definition(
  "Superposition typical set",
  lean: (
    "Meat.superpositionTypicalSet",
    "Meat.mem_superpositionTypicalSet",
    "Meat.superpositionTypicalSet_subset",
  ),
)[
  Let $epsilon in RR$.
  The set $T_epsilon^((n)) (p)$ is the set of pairs $(w, y)$ with $w = (u, x) in (S times T)^n$ and $y in R^n$ such that
  - $(w, y) in J_epsilon^((n)) (p)$,
  - $u in A_epsilon^((n)) (p_U)$ and $(u, y) in A_epsilon^((n)) (p_(U Y))$,
  - $(x, y) in J_epsilon^((n)) (p_(X Y))$.
  So it is a subset of $J_epsilon^((n)) (p)$.
]

#theorem("Superposition AEP", lean: "Meat.tendsto_sum_iidProb_superpositionTypicalSet")[
  Let $epsilon > 0$.
  Then $p^n (T_epsilon^((n)) (p)) -> 1$ as $n -> infinity$.
][
  Each of the four conditions fails with a probability that tends to $0$.
  For the first, this is the joint asymptotic equipartition property for $p$.
  Each other condition is a property of $g compose (w, y)$ for a coordinate map $g$.
  By the lemma on push-forwards, its failure probability is $1 - p_g^n (A)$ for the marginal $p_g$ and its typical set $A$.
  This tends to $0$ by the asymptotic equipartition property for $p_g$.
  The probability of a union of four events is at most the sum of the four probabilities.
]

#theorem("Same cloud bound", lean: "Meat.sum_superpositionTypicalSet_le_condMutualInfo")[
  Let $I := I(X; Y given U)$ under $nu_p$, where $U$, $X$ and $Y$ are the three coordinates.
  Then
  $ sum_((u, x, y) in T_epsilon^((n)) (p)) (p_(U X)^n (u, x) p_(U Y)^n (u, y)) / (p_U^n (u)) <= e^(-n (I - 4 epsilon)). $
][
  On $T_epsilon^((n)) (p)$, the typical set bounds give $p_(U X)^n (u, x) <= e^(-n (H(p_(U X)) - epsilon))$, $p_(U Y)^n (u, y) <= e^(-n (H(p_(U Y)) - epsilon))$ and $p_U^n (u) >= e^(-n (H(p_U) + epsilon))$.
  The set has at most $e^(n (H(p) + epsilon))$ elements, because it is a subset of $J_epsilon^((n)) (p)$.
  So the sum is at most $e^(-n (H(p_(U X)) + H(p_(U Y)) - H(p_U) - H(p) - 4 epsilon))$.
  By the definition of conditional mutual information and by relabeling,
  $ I = H(p_(U X)) + H(p_(U Y)) - H(p_U) - H(p). $
]

#theorem("Other cloud bound", lean: "Meat.sum_superpositionTypicalSet_le_mutualInfo")[
  Let $I := I(X; Y)$ under $nu_p$.
  Then
  $ sum_((w, y) in T_epsilon^((n)) (p)) p_(U X)^n (w) p_Y^n (y) <= e^(-n (I - 3 epsilon)). $
][
  Each term is nonnegative, and $(x, y) in J_epsilon^((n)) (p_(X Y))$ on the set.
  So the sum is at most the sum over all $(u, x, y)$ with $(x, y) in J_epsilon^((n)) (p_(X Y))$.
  The sum over $u$ of $p_(U X)^n (u, x)$ is $p_X^n (x)$, by the marginal lemma.
  The rest is the independent-pair bound for $p_(X Y)$.
  Its mutual information is $I$, by the lemma on information under a push-forward, because the measure of $p_(X Y)$ is a push-forward of $nu_p$.
]

The bound uses the condition on $(x, y)$ and does not need the Markov chain $U -> X -> Y$.
This is the reason for the last condition in the definition of $T_epsilon^((n)) (p)$.

== Tools for two senders
#source("Meat.Shannon.TypicalIntersection")

#lemma("Intersections of likely sets", lean: "Meat.tendsto_sum_of_mem_iff_and")[
  For each $n$, let $w_n >= 0$ be weights with total at most $1$, and let $u_n = s_n inter t_n$.
  If $w_n (s_n) -> 1$ and $w_n (t_n) -> 1$, then $w_n (u_n) -> 1$.
][
  We have $w_n (s_n union t_n) + w_n (u_n) = w_n (s_n) + w_n (t_n)$ and $w_n (s_n union t_n) <= 1$.
  So $w_n (s_n) + w_n (t_n) - 1 <= w_n (u_n) <= 1$.
]

#source("Meat.Shannon.Conditional")

#proposition(
  "Relabeling",
  lean: ("Meat.condEntropy_comp_of_injective", "Meat.mutualInfo_comp_right_of_injective"),
)[
  For an injective $f$, $H(f(X) given Z) = H(X given Z)$ and $I(X; f(Y)) = I(X; Y)$.
][
  Each quantity is a sum and difference of entropies.
  An injective relabeling does not change entropy.
]

#lemma(
  "Conditional information as a difference",
  lean: "Meat.condMutualInfo_eq_condEntropy_sub_condEntropy",
)[
  $ I(X; Y given Z) = H(Y given Z) - H(Y given (X, Z)). $
][
  Expand both sides in joint entropies.
  The term $H((X, Y), Z)$ on the left is $H(Y, (X, Z))$ on the right, by relabeling.
]

#theorem("Conditional subadditivity", lean: "Meat.condEntropy_pi_le_sum")[
  For a sequence $Y = (Y_1, dots, Y_n)$ and a random variable $Z$,
  $ H(Y given Z) <= sum_(i = 1)^n H(Y_i given Z). $
][
  Induction on $n$, as for subadditivity.
  For $n = 0$, $Y$ is constant, so $H(Y given Z) = 0$.
  For the step, split $Y$ into $Y_1$ and the tail, and use $H((A, B) given Z) <= H(A given Z) + H(B given Z)$, which is $I(A; B given Z) >= 0$.
]

#lemma("Independence", lean: "Meat.mutualInfo_eq_zero_of_measureReal_eq_mul")[
  If the law of $(X, Y)$ is the product of the laws of $X$ and $Y$, then $I(X; Y) = 0$.
][
  With $P$ and $Q$ the laws of $X$ and $Y$, $eta(P(s) Q(t)) = Q(t) eta(P(s)) + P(s) eta(Q(t))$, where $eta(x) := -x log x$.
  Sum over $s$ and $t$: $H(X, Y) = H(X) + H(Y)$.
]

== Tools for lossy coding
#source("Meat.Shannon.LargeNumbers")

The rate-distortion theorem needs three more tools.
The first is a weak law of large numbers for a function of an i.i.d. sequence.
The second is the log-sum inequality for two terms.
The third is a covering lemma for jointly typical sets.

#theorem("Weak law of large numbers", lean: "Meat.tendsto_sum_iidProb_sum_le")[
  Let $p$ be a probability mass function on a finite set $A$, let $f : A -> RR$, and let $m := sum_a p(a) f(a)$.
  For every $epsilon > 0$,
  $ sum_(x in A^n : sum_i f(x_i) <= n (m + epsilon)) p^n (x) -> 1 quad "as" n -> infinity. $
][
  This is the Chebyshev argument of the asymptotic equipartition property, with $f$ in place of $-log p$.
  Let $Y(a) := f(a) - m$, so that $sum_a p(a) Y(a) = 0$.
  Let $V := sum_a p(a) Y(a)^2$.
  Under $p^n$, the cross terms $Y(x_i) Y(x_j)$ with $i != j$ have mean $0$, so the mean of $(sum_i Y(x_i))^2$ is $n V$.
  If $sum_i f(x_i) > n (m + epsilon)$, then $sum_i Y(x_i) > n epsilon$, so $(sum_i Y(x_i))^2 > (n epsilon)^2$.
  So for $n > 0$ the mass outside the set is at most $n V \/ (n epsilon)^2 = V \/ (epsilon^2 n)$.
  The set has mass between $1 - V \/ (epsilon^2 n)$ and $1$.
]

#source("Meat.Shannon.LogSum")

#theorem("Log-sum inequality", lean: "Meat.add_mul_log_div_add_le")[
  Let $a_1, a_2, b_1, b_2 >= 0$, with $a_i = 0$ whenever $b_i = 0$.
  Then
  $ (a_1 + a_2) log (a_1 + a_2) / (b_1 + b_2) <= a_1 log a_1 / b_1 + a_2 log a_2 / b_2. $
  In Lean, $x \/ 0 = 0$ and $log 0 = 0$, so the hypothesis on zeros is necessary.
][
  If $b_1 + b_2 = 0$, then $b_1 = b_2 = 0$, so $a_1 = a_2 = 0$ and both sides are $0$.
  Otherwise let $B := b_1 + b_2 > 0$ and $phi(x) := x log x$, which is convex on $[0, infinity)$.
  Apply convexity at the points $a_i \/ b_i$ with the weights $b_i \/ B$.
  Since $a_i = 0$ when $b_i = 0$, $(b_i \/ B)(a_i \/ b_i) = a_i \/ B$ and $(b_i \/ B) phi(a_i \/ b_i) = a_i log(a_i \/ b_i) \/ B$.
  So $phi((a_1 + a_2) \/ B) <= (a_1 log(a_1 \/ b_1) + a_2 log(a_2 \/ b_2)) \/ B$.
  Multiply by $B$.
]

#source("Meat.Shannon.Covering")

#lemma("An exponential bound", lean: "Meat.one_sub_mul_pow_le")[
  Let $a <= 1$, $0 <= b <= 1$ and $k in NN$.
  Then $(1 - a b)^k <= 1 - b + e^(-k a)$.
][
  The map $x |-> x^k$ is convex on $[0, infinity)$.
  The point $1 - a b$ is the convex combination $(1 - b) dot 1 + b (1 - a)$ of $1$ and $1 - a >= 0$.
  So $(1 - a b)^k <= (1 - b) + b (1 - a)^k <= 1 - b + (1 - a)^k$.
  Finally $0 <= 1 - a <= e^(-a)$, so $(1 - a)^k <= e^(-k a)$.
]

#theorem("Covering lemma", lean: "Meat.sum_iidProb_mul_one_sub_pow_le")[
  Let $p$ be a probability mass function on $S times T$ with marginals $p_1$ and $p_2$, and let $I := I(X; Y)$ for $(X, Y)$ with the law $p$.
  Let $epsilon >= 0$, let $J subset.eq J_epsilon^((n)) (p)$, and let $k in NN$.
  For $x in S^n$, let $Q(x) := sum_(y : (x, y) in J) p_2^n (y)$.
  Then
  $ sum_x p_1^n (x) (1 - Q(x))^k <= (1 - p^n (J)) + exp(-k e^(-n (I + 3 epsilon))). $
][
  The term $p_1^n (x) (1 - Q(x))^k$ is the probability that $x$ is drawn and that none of $k$ independent codewords drawn from $p_2^n$ is jointly typical with $x$.
  Let $a := e^(-n (I + 3 epsilon))$, so $0 < a <= 1$ because $I >= 0$.
  For $(x, y) in J$, the three typicality bounds give $p_1^n (x) >= e^(-n (H(p_1) + epsilon))$, $p_2^n (y) >= e^(-n (H(p_2) + epsilon))$ and $p^n (x, y) <= e^(-n (H(p) - epsilon))$.
  Since $I = H(p_1) + H(p_2) - H(p)$, this gives $a p^n (x, y) <= p_1^n (x) p_2^n (y)$.
  Fix $x$ and let $B(x) := sum_(y : (x, y) in J) p^n (x, y)$.
  Then $0 <= B(x) <= p_1^n (x)$, by the marginal lemma, and $a B(x) <= p_1^n (x) Q(x)$.
  If $p_1^n (x) = 0$, then $B(x) = 0$, and the term is $0$.
  Otherwise let $b := B(x) \/ p_1^n (x) in [0, 1]$.
  Then $a b <= Q(x) <= 1$, so $(1 - Q(x))^k <= (1 - a b)^k <= 1 - b + e^(-k a)$, by the exponential bound.
  Multiply by $p_1^n (x)$: the term is at most $p_1^n (x) - B(x) + p_1^n (x) e^(-k a)$.
  Sum over $x$.
  The sums of $p_1^n (x)$ and of $B(x)$ are $1$ and $p^n (J)$.
]

== The method of types
#source("Meat.Shannon.Types")

The method of types groups the sequences in $S^n$ by their empirical distribution.
In this section, $S$ is a finite set with measurable singletons, and $q$ is a law on $S$.
A sequence is a map $x : {1, dots, n} -> S$, and $q^n (x)$ is its product probability, as in the section on typical sequences.

#definition("Counts", lean: "Meat.typeCount")[
  For a sequence $x$ and $s in S$, the count of $s$ in $x$ is
  $ N(s given x) := |{i : x_i = s}|. $
]

#lemma(
  "Counts and sums",
  lean: (
    "Meat.sum_typeCount",
    "Meat.typeCount_le",
    "Meat.prod_comp_eq_prod_pow",
    "Meat.sum_comp_eq_sum_typeCount_mul",
    "Meat.prod_comp_eq_exp",
    "Meat.typeCount_cons",
  ),
)[
  For every sequence $x$ of length $n$, $sum_s N(s given x) = n$ and $N(s given x) <= n$.
  For every $f : S -> M$ into a commutative monoid, $product_i f(x_i) = product_s f(s)^(N(s given x))$.
  For every $f : S -> RR$, $sum_i f(x_i) = sum_s N(s given x) f(s)$.
  If $w(x_i) > 0$ for every $i$, then $product_i w(x_i) = exp(sum_s N(s given x) log w(s))$.
  For $a in S$ and a sequence $y$ of length $n$, the sequence $(a, y)$ of length $n + 1$ has $N(s given (a, y)) = N(s given y) + [a = s]$.
][
  Group the coordinates $i$ by the value $x_i$.
  For the exponential form, write each factor as $exp(log w(x_i))$ and use the sum formula.
  For the last statement, the first coordinate adds $1$ to the count of $a$.
]

#theorem(
  "Number of sequences with given counts",
  lean: ("Meat.card_typeCount_eq_mul_prod_factorial", "Meat.exists_typeCount_eq"),
)[
  Let $k : S -> NN$ with $sum_s k(s) = n$.
  Then the number of sequences $x$ of length $n$ with $N(dot given x) = k$ satisfies
  $ |{x : N(dot given x) = k}| product_s k(s)! = n!. $
  In particular, such a sequence exists.
][
  Induction on $n$.
  For $n = 0$, $k = 0$, and the empty sequence is the only sequence.
  For $n + 1$, split $x = (a, y)$.
  By the count lemma, $N(dot given (a, y)) = k$ holds if and only if $k(a) >= 1$ and $N(dot given y) = k - e_a$, where $e_a$ is the indicator of $a$.
  The counts $k - e_a$ sum to $n$, and $product_s k(s)! = k(a) product_s (k - e_a)(s)!$.
  By induction, the number of sequences that start with $a$, times $product_s k(s)!$, is $k(a) n!$.
  This is also true if $k(a) = 0$.
  Sum over $a$: the result is $(n + 1) n! = (n + 1)!$.
  The right side is positive, so the set is not empty.
]

#lemma("Factorial inequality", lean: "Meat.factorial_mul_pow_le")[
  For all $j, k in NN$, $k! k^j <= j! k^k$.
][
  If $j <= k$, then $k! = j! k (k - 1) dots (j + 1) <= j! k^(k - j)$.
  If $j = k + m$, then $j! >= k! (k + 1)^m >= k! k^m$.
]

#definition(
  "Type of a sequence",
  lean: (
    "Meat.seqType",
    "Meat.seqType_apply_singleton",
    "Meat.seqType_real",
    "Meat.isProbabilityMeasure_seqType",
  ),
)[
  The type of a sequence $x$ of length $n$ is the measure
  $ P_x := sum_s (N(s given x)) / n delta_s $
  on $S$, where $delta_s$ is the Dirac measure at $s$.
  So $P_x ({s}) = N(s given x) \/ n$.
  If $n > 0$, then $P_x$ is a probability measure.
]

For $n = 0$, Lean has $N(s given x) \/ 0 = 0$, so $P_x$ is the zero measure.
The results below are true also for $n = 0$, unless they say otherwise.

#definition(
  "Types and type classes",
  lean: (
    "Meat.typeSet",
    "Meat.typeClass",
    "Meat.mem_typeSet",
    "Meat.mem_typeClass",
    "Meat.seqType_eq_seqType_iff",
  ),
)[
  The set of types of length $n$ is $cal(P)_n := {P_x : x in S^n}$.
  The type class of a measure $P$ is $T(P) := {x in S^n : P_x = P}$.
  Two sequences have the same type if and only if they have the same counts.
]

#theorem("Number of types", lean: "Meat.card_typeSet_le")[
  $ |cal(P)_n| <= (n + 1)^(|S|). $
][
  The type $P_x$ is a function of the counts $N(dot given x)$.
  Each count is in ${0, dots, n}$, so there are at most $(n + 1)^(|S|)$ count vectors.
]

#lemma(
  "Absolute continuity on a finite set",
  lean: (
    "Meat.absolutelyContinuous_iff_singleton",
    "Meat.PMF.toMeasure_real_singleton",
    "Meat.seqType_absolutelyContinuous_iff",
  ),
)[
  On a countable set with measurable singletons, $nu << rho$ if and only if $rho({s}) = 0$ implies $nu({s}) = 0$ for every $s$.
  The measure $nu_q$ of a law $q$ has $nu_q ({s}) = q(s)$.
  So $P_x << nu_q$ if and only if $q(x_i) != 0$ for every $i$.
][
  A set of measure $0$ is the countable union of its singletons.
  The type has $P_x ({s}) > 0$ exactly when $s$ occurs in $x$.
]

#lemma(
  "Entropy plus divergence",
  lean: ("Meat.measureEntropy_add_klDiv", "Meat.klDiv_eq_sum_sub"),
)[
  Let $rho$ be a finite measure and $nu << rho$.
  Then
  $ H(nu) + D(nu || rho) = -sum_s nu_s log rho_s, quad D(nu || rho) = sum_s (nu_s log nu_s - nu_s log rho_s). $
][
  If $nu_s = 0$, each term is $0$.
  If $nu_s > 0$, then $rho_s > 0$ by absolute continuity, so $log (nu_s \/ rho_s) = log nu_s - log rho_s$.
  Then $eta(nu_s) + nu_s log (nu_s \/ rho_s) = -nu_s log rho_s$.
]

Without $nu << rho$, the Lean sum has the term $nu_s log 0 = 0$ where $rho_s = 0$, and both identities can fail.

#theorem(
  "Probability of a sequence",
  lean: ("Meat.iidProb_eq_exp", "Meat.iidProb_eq_zero", "Meat.prod_seqType_real"),
)[
  Let $x$ be a sequence of length $n$.
  If $P_x << nu_q$, then
  $ q^n (x) = e^(-n (H(P_x) + D(P_x || nu_q))). $
  Otherwise $q^n (x) = 0$.
  In particular, with $q$ replaced by the weights of $P_x$, $product_i P_x ({x_i}) = e^(-n H(P_x))$.
][
  If $P_x << nu_q$, every $q(x_i)$ is positive.
  By the exponential form of the count lemma, $q^n (x) = exp(sum_s N(s given x) log q_s)$.
  Since $N(s given x) = n P_x ({s})$, the exponent is $-n (H(P_x) + D(P_x || nu_q))$ by the lemma on entropy plus divergence.
  Otherwise some $q(x_i)$ is $0$, so the product is $0$.
  The last statement is the same computation with $D(P_x || P_x) = 0$.
]

This is the support convention: $D(P || q)$ is the true divergence only for $P << nu_q$, and sequences of other types have probability $0$.

#lemma(
  "Sums over type classes",
  lean: ("Meat.sum_seqType_real", "Meat.sum_typeSet_sum_typeClass"),
)[
  If $n > 0$, then $sum_s P_x ({s}) = 1$.
  For every $f : S^n -> RR$,
  $ sum_(P in cal(P)_n) sum_(x in T(P)) f(x) = sum_x f(x). $
][
  The type of $x$ is a probability measure.
  The type classes of the types in $cal(P)_n$ partition $S^n$.
]

#lemma("The type class is the most likely class", lean: "Meat.card_mul_prod_pow_le")[
  Let $x$ and $y$ be sequences of length $n$ with counts $k$ and $j$.
  Then
  $ |{z : N(dot given z) = j}| product_s k(s)^(j(s)) <= |{z : N(dot given z) = k}| product_s k(s)^(k(s)). $
][
  Multiply both sides by $product_s j(s)! product_s k(s)!$.
  By the counting theorem, the left side becomes $n! product_s k(s)! k(s)^(j(s))$ and the right side becomes $n! product_s j(s)! k(s)^(k(s))$.
  Compare the factors with the factorial inequality.
]

Divide both sides by $n^n = product_s n^(j(s)) = product_s n^(k(s))$.
With $P := P_x$, the left side is the probability of $T(P_y)$ under $P^n$, and the right side is the probability of $T(P)$ under $P^n$.

#theorem(
  "Size of a type class",
  lean: ("Meat.card_typeClass_le", "Meat.card_typeClass_ge"),
)[
  For every measure $P$ on $S$,
  $ |T(P)| <= e^(n H(P)). $
  If $P in cal(P)_n$, then
  $ e^(n H(P)) / (n + 1)^(|S|) <= |T(P)|. $
][
  If $T(P)$ is empty, the upper bound is clear.
  Otherwise $P = P_x$ for some $x$.
  Let $P^n (z) := product_i P({z_i})$.
  These weights sum to $1$, and each $z in T(P)$ has $P^n (z) = e^(-n H(P))$.
  So $|T(P)| e^(-n H(P)) <= 1$.
  For the lower bound, split the total weight $1$ over the type classes.
  By the previous lemma, each class has $P^n$ weight at most $|T(P)| e^(-n H(P))$.
  So $1 <= |cal(P)_n| |T(P)| e^(-n H(P)) <= (n + 1)^(|S|) |T(P)| e^(-n H(P))$.
]

#theorem(
  "Probability of a type class",
  lean: ("Meat.sum_iidProb_typeClass_le", "Meat.le_sum_iidProb_typeClass"),
)[
  For every measure $P$ on $S$,
  $ q^n (T(P)) <= e^(-n D(P || nu_q)). $
  If $P in cal(P)_n$ and $P << nu_q$, then
  $ e^(-n D(P || nu_q)) / (n + 1)^(|S|) <= q^n (T(P)). $
][
  If $P << nu_q$, every $x in T(P)$ has $q^n (x) = e^(-n H(P)) e^(-n D(P || nu_q))$.
  Multiply by the size bounds of $T(P)$.
  If $P$ is not absolutely continuous with respect to $nu_q$, every $x in T(P)$ has $q^n (x) = 0$.
]

The upper bound needs no assumption, because $q^n (T(P)) = 0$ when the real divergence has no meaning.

#lemma("Continuity of the divergence", lean: "Meat.tendsto_klDiv")[
  Let $rho$ be a finite measure, let $nu_k << rho$ for every $k$, and let $nu_k ({s}) -> w_s$ for every $s$.
  Then
  $ D(nu_k || rho) -> sum_s (w_s log w_s - w_s log rho_s). $
][
  By the lemma on entropy plus divergence, each $D(nu_k || rho)$ is a sum of the continuous functions $t |-> t log t - t log rho_s$ at $nu_k ({s})$.
]

#lemma("Approximation by types", lean: "Meat.exists_seq_typeCount_tendsto")[
  Let $w : S -> [0, infinity)$ with $sum_s w_s = 1$.
  Then there are sequences $x^((n))$ of length $n$ such that $N(s given x^((n))) = 0$ whenever $w_s = 0$, and $N(s given x^((n))) \/ n -> w_s$ for every $s$.
][
  Fix $s_0$ with $w_(s_0) > 0$.
  Let $k_n (s) := floor(n w_s)$ for $s != s_0$, and give the rest $n - sum_(s != s_0) k_n (s) >= 0$ to $s_0$.
  A sequence with these counts exists by the counting theorem.
  For $s != s_0$, $floor(n w_s) \/ n -> w_s$, and $k_n (s_0) \/ n -> 1 - sum_(s != s_0) w_s = w_(s_0)$.
]

#lemma(
  "Exponential rates",
  lean: (
    "Meat.eventually_pow_le_exp",
    "Meat.le_neg_log_div_of_le_exp",
    "Meat.neg_log_div_le_of_exp_le",
  ),
)[
  For $k in NN$ and $eta > 0$, $(n + 1)^k <= e^(n eta)$ for all large $n$.
  Let $n > 0$.
  If $0 < y <= e^(-n c)$, then $c <= -1/n log y$.
  If $e^(-n c) <= y$, then $-1/n log y <= c$.
][
  The ratio $m^k \/ e^(m eta \/ 2)$ tends to $0$, so $(n + 1)^k <= e^((n + 1) eta \/ 2) <= e^(n eta)$ for large $n$.
  The other two statements follow from taking logarithms.
]

== Chain rules
#source("Meat.Shannon.ChainRule")

For a sequence $y = (y_1, dots, y_n)$ and an index $i$, the prefix $y^(i - 1) := (y_1, dots, y_(i - 1))$ is the part of $y$ before position $i$.
The chain rules write the entropy of a sequence as a sum of conditional entropies, one for each letter given the letters before it.
No independence is needed: the identities hold for every joint law.

#definition("Prefix", lean: "Meat.seqPrefix")[
  For $y : [n] -> S$ and $i in [n]$, $y^(i - 1) : [i - 1] -> S$ is the map $j |-> y_j$.
]

#lemma(
  "Relabeling the condition and the pair rule",
  lean: ("Meat.condEntropy_cond_of_injective", "Meat.condEntropy_pair_eq_add"),
)[
  If $Z' = e(Z)$ for an injective map $e$, then $H(X given Z') = H(X given Z)$.
  Also $H(X, Y given Z) = H(X given Z) + H(Y given X, Z)$.
][
  Both sides are differences of joint entropies.
  The joint entropies are equal by injective relabeling.
]

#theorem(
  "Chain rules",
  lean: (
    "Meat.condEntropy_eq_sum",
    "Meat.entropy_eq_sum",
    "Meat.condMutualInfo_eq_sum",
    "Meat.mutualInfo_eq_sum",
  ),
)[
  For a random sequence $Y^n$ and random variables $W$ and $Z$,
  $ H(Y^n given W) = sum_(i = 1)^n H(Y_i given W, Y^(i - 1)), quad H(Y^n) = sum_(i = 1)^n H(Y_i given Y^(i - 1)), $
  $ I(Y^n ; W given Z) = sum_(i = 1)^n I(Y_i ; W given Z, Y^(i - 1)), quad I(Y^n ; W) = sum_(i = 1)^n I(Y_i ; W given Y^(i - 1)). $
  The unconditional forms assume a probability measure.
][
  Induction on $n$.
  The map $y |-> (y^(n - 1), y_n)$ is injective, so $H(Y^n given W) = H(Y^(n - 1), Y_n given W)$.
  The pair rule gives $H(Y^(n - 1) given W) + H(Y_n given Y^(n - 1), W)$.
  The first term is the sum for $n - 1$, and the second term is the last summand after a swap of the condition.
  For $H(Y^n)$, take $W$ constant: conditioning on a constant does nothing.
  For mutual information, write $I(Y^n ; W given Z) = H(Y^n given Z) - H(Y^n given W, Z)$ and subtract the two chain rules term by term.
]

== Han's inequality and Shearer's lemma
#source("Meat.Shannon.Combinatorial")

For a random sequence $Y = (Y_1, dots, Y_n)$ and a set $A subset.eq [n]$, the subsequence $Y_A$ is the family $(Y_j)_(j in A)$.
Shearer's lemma bounds the entropy of $Y$ by the entropies of subsequences that cover each coordinate often enough.
Han's inequality is the case of the $n$ sets that leave out one coordinate each.

#definition("Subsequence", lean: "Meat.seqRestrict")[
  For $y : [n] -> S$ and $A subset.eq [n]$, $y_A : A -> S$ is the restriction $j |-> y_j$.
]

#lemma("Entropy of a subsequence", lean: "Meat.sum_condEntropy_le_entropy_restrict")[
  For every $A subset.eq [n]$,
  $ sum_(i in A) H(Y_i given Y^(i - 1)) <= H(Y_A). $
][
  Induction on $A$, adding its largest element $a$ last.
  The map $y_(A union {a}) |-> (y_a, y_A)$ is injective, so $H(Y_(A union {a})) = H(Y_A) + H(Y_a given Y_A)$.
  Every element of $A$ is smaller than $a$, so $Y_A$ is a function of the prefix $Y^(a - 1)$.
  Conditioning on a function gives $H(Y_a given Y^(a - 1)) <= H(Y_a given Y_A)$.
  The empty set has sum $0$ and entropy at least $0$.
]

#theorem("Shearer's lemma", lean: "Meat.shearer")[
  Let $(A_t)_(t in I)$ be a finite family of subsets of $[n]$ such that each $i in [n]$ lies in at least $k$ of the sets.
  Then
  $ k H(Y) <= sum_(t in I) H(Y_(A_t)). $
][
  Write $c_i := H(Y_i given Y^(i - 1)) >= 0$, so $H(Y) = sum_i c_i$ by the chain rule.
  Then $k H(Y) <= sum_i |{t : i in A_t}| c_i = sum_t sum_(i in A_t) c_i$.
  By the lemma, each inner sum is at most $H(Y_(A_t))$.
]

#corollary("Han's inequality", lean: "Meat.han")[
  $ (n - 1) H(Y) <= sum_(i = 1)^n H(Y_([n] without {i})). $
][
  Apply Shearer's lemma to the sets $[n] without {t}$.
  Each $i$ lies in all of them except the one with $t = i$, so $k = n - 1$.
  For $n = 0$ both sides are trivial.
]

== Entropy rate
#source("Meat.Shannon.EntropyRate")

A process is a sequence $X_0, X_1, dots$ of random variables on one probability space, with values in a finite set $S$.
Its block of length $n$ is $X^n = (X_0, dots, X_(n - 1))$.
For a stationary process, the conditional entropy of the next letter decreases, and the entropy per letter converges to the same limit.

#definition(
  "Blocks, stationarity and Markov processes",
  lean: ("Meat.block", "Meat.shiftBlock", "Meat.Stationary", "Meat.IsMarkovProcess"),
)[
  The block of length $n$ shifted by $k$ is $(X_k, dots, X_(k + n - 1))$, and the block $X^n$ is the shift by $0$.
  The process is stationary if every shifted block has the same law as the block of the same length.
  It is a Markov process if $X^n -> X_n -> X_(n + 1)$ is a Markov chain for every $n$.
]

#definition("Entropy rate", lean: "Meat.entropyRate")[
  $ H(cal(X)) := inf_n H(X_n given X^n). $
]

#lemma(
  "Entropy of blocks",
  lean: ("Meat.entropy_shiftBlock_succ", "Meat.entropy_block_succ", "Meat.entropy_block_eq_sum"),
)[
  $H(X^(n + 1)) = H(X^n) + H(X_n given X^n)$, and the same holds for shifted blocks.
  So $H(X^n) = sum_(i < n) H(X_i given X^i)$.
][
  The map that splits a block into its last letter and the rest is injective.
  Then add the terms, starting from the empty block, which has entropy $0$.
]

#theorem("Conditional entropy decreases", lean: ("Meat.condEntropy_succ_le", "Meat.condEntropy_antitone"))[
  For a stationary process, $H(X_(n + 1) given X^(n + 1)) <= H(X_n given X^n)$.
][
  Dropping $X_0$ from the condition can only increase the conditional entropy, so $H(X_(n + 1) given X^(n + 1)) <= H(X_(n + 1) given X_1, dots, X_n)$.
  By the lemma for the block shifted by $1$, the right side is $H(X_1, dots, X_(n + 1)) - H(X_1, dots, X_n)$.
  By stationarity, this is $H(X^(n + 1)) - H(X^n) = H(X_n given X^n)$.
]

#theorem("Entropy rate as a limit", lean: ("Meat.tendsto_condEntropy", "Meat.tendsto_entropy_div"))[
  For a stationary process,
  $ H(X_n given X^n) -> H(cal(X)) quad "and" quad H(X^n) / n -> H(cal(X)). $
][
  The conditional entropies decrease and are at least $0$, so they converge to their infimum.
  By the lemma, $H(X^n) \/ n$ is the Cesàro mean of the conditional entropies, so it has the same limit.
]

#theorem("Entropy rate of a stationary Markov process", lean: "Meat.entropyRate_of_markov")[
  For a stationary Markov process, $H(cal(X)) = H(X_1 given X_0)$.
][
  For $n = m + 1$, the block $X^(m + 1)$ is a relabeling of $(X^m, X_m)$.
  The Markov property gives $H(X_(m + 1) given X^m, X_m) = H(X_(m + 1) given X_m)$.
  By stationarity, the pair $(X_m, X_(m + 1))$ has the law of $(X_0, X_1)$, so this is $H(X_1 given X_0)$.
  So all terms from $n = 1$ on equal $H(X_1 given X_0)$, and the term for $n = 0$ is at least as large.
  The infimum is $H(X_1 given X_0)$.
]


== Strong typicality and the Markov lemma
#source("Meat.Shannon.MarkovLemma")

Weak typicality controls the probability of a whole sequence.
Strong typicality controls the frequency of every letter, so averages of every function are close to their expectations.
This is what the Markov lemma and the analysis of distortion need.
In this section, $A$ and $B$ are finite sets, $N(a given x)$ is the number of positions $i$ with $x_i = a$, and a target $r : A -> RR$ is a vector of letter frequencies.
The bounds are explicit, so they hold uniformly over all typical input sequences.

#definition("Strongly typical set", lean: ("Meat.strongTypicalSet", "Meat.mem_strongTypicalSet"))[
  $ T_epsilon^((n)) (r) := {x in A^n : |N(a given x) / n - r(a)| <= epsilon "for all" a in A}. $
]

#lemma("Typical average", lean: "Meat.abs_avg_sub_le_of_mem_strongTypicalSet")[
  Let $n >= 1$ and $x in T_epsilon^((n)) (r)$.
  For every $f : A -> RR$,
  $ |1 / n sum_(i = 1)^n f(x_i) - sum_a r(a) f(a)| <= epsilon sum_a |f(a)|. $
][
  Group the sum by letters: $sum_i f(x_i) = sum_a N(a given x) f(a)$.
  Each letter contributes at most $epsilon |f(a)|$.
]

#lemma("Second moment of a sum of independent terms", lean: "Meat.sum_prod_mul_sq_sum")[
  Let $w_1, dots, w_n$ be probability vectors on $B$, and let $g_i : B -> RR$ have mean $sum_b w_i (b) g_i (b) = 0$ under $w_i$.
  Under the product law $product_i w_i (y_i)$,
  $ EE (sum_i g_i (Y_i))^2 = sum_i sum_b w_i (b) g_i (b)^2. $
][
  Expand the square.
  For $i != j$, the expectation of $g_i (Y_i) g_j (Y_j)$ factors into the two means, which are $0$.
  For $i = j$, the other coordinates sum to $1$.
]

#theorem("Conditional typicality lemma", lean: "Meat.sum_not_mem_strongTypicalSet_le")[
  Let $W$ be a channel from $A$ to $B$, let $n >= 1$, $eta > 0$, and $x in T_delta^((n)) (r)$.
  Let $Y^n$ have the law $product_i W(y_i given x_i)$.
  Then the probability that $(x, Y^n) in.not T_(delta + eta)^((n)) (r W)$ is at most
  $ (|A| |B|) / (4 n eta^2), $
  where $(r W)(a, b) := r(a) W(b given a)$.
][
  Fix $(a, b)$.
  Let $S := N((a, b) given (x, Y^n)) - N(a given x) W(b given a)$.
  It is a sum of independent terms with mean $0$, one for each position $i$ with $x_i = a$.
  By the second moment lemma, $EE S^2 = N(a given x) W(b given a) (1 - W(b given a)) <= n / 4$.
  Write $N((a, b) given (x, Y^n)) / n - r(a) W(b given a) = S / n + (N(a given x) / n - r(a)) W(b given a)$.
  The last term is at most $delta$ in absolute value, so a deviation larger than $delta + eta$ forces $|S| > n eta$.
  So the indicator of the bad event is at most $sum_((a, b)) S_(a b)^2 / (n eta)^2$.
  Take the expectation: the bound is $|A| |B| (n / 4) / (n eta)^2$.
]

#corollary("Markov lemma", lean: "Meat.markov_lemma")[
  Let $U -> X -> Y$, where $Y$ is the output of $W$ on input $X$.
  If $(u^n, x^n) in T_delta^((n)) (r)$ and $Y^n$ has the law $product_i W(y_i given x_i)$, then the probability that $(u^n, x^n, Y^n) in.not T_(delta + eta)^((n)) (r W)$ is at most $|U| |A| |B| \/ (4 n eta^2)$.
][
  Apply the conditional typicality lemma to the pair alphabet $U times A$ and the channel $(u, x) |-> W(dot given x)$, which ignores $u$.
]

This is the form of the Markov lemma that a covering encoder needs.
Given $X^n = x^n$, the side information $Y^n$ is drawn from $product_i p(y_i given x_i)$ independently of the codeword $u^n$ that the encoder chose from $x^n$.
The bound does not depend on $u^n$ or $x^n$, so it can be averaged over the encoder's choice.
