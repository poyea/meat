#import "../meat.typ": *

= Source coding

== Slepian-Wolf coding
#source("Meat.Source.SlepianWolf")

Two encoders observe two correlated sources.
Each encoder sees only one source.
One decoder recovers the two sources.
Rates are in nats for each source symbol.
The two encoders together need only the rate $H(X, Y)$.
This rate is the same rate that is necessary when one encoder sees the two sources.
In this section, $S$ and $T$ are finite sets and $p$ is a probability mass function on $S times T$.

#definition("Distributed source code", lean: ("Meat.SWCode", "Meat.SWCode.errorProb"))[
  Let $n in NN$ and let $M_1$ and $M_2$ be sets.
  A distributed source code of length $n$ is a triple $(f_1, f_2, g)$ of maps
  $ f_1 : S^n -> M_1, quad f_2 : T^n -> M_2, quad g : M_1 times M_2 -> S^n times T^n. $
  Its error probability for $p$ is
  $ P_e := sum_((x^n, y^n) : g(f_1(x^n), f_2(y^n)) != (x^n, y^n)) product_(i = 1)^n p(x_i, y_i). $
]

#definition(
  "Achievable rate pair",
  lean: ("Meat.SlepianWolf.Achievable", "Meat.SlepianWolf.achievableRegion"),
)[
  A pair $(R_1, R_2) in RR^2$ is achievable for $p$ if for every $epsilon > 0$ there exists $N in NN$ such that for every $n >= N$ there exist $k_1, k_2 in NN$ with $k_i <= e^(n R_i)$ and a code of length $n$ with $M_i = {1, dots, k_i}$ and $P_e <= epsilon$.
  The achievable region $cal(A)(p)$ is the set of achievable pairs.
]

#definition("Slepian-Wolf region", lean: "Meat.SlepianWolf.rateRegion")[
  Let $(X, Y)$ have the law $p$.
  $ cal(R)(p) := {(R_1, R_2) in RR^2 : R_1 >= H(X given Y), R_2 >= H(Y given X), R_1 + R_2 >= H(X, Y)}. $
]

== Slepian-Wolf achievability
#source("Meat.Source.SlepianWolfAchievability")

This section proves the inclusion $supset.eq$ of the Slepian-Wolf theorem.
The proof is random binning with joint typicality decoding.
As in the Shannon chapter, $p_1$ and $p_2$ are the marginals of $p$, $H(p)$ is the entropy of $p$, and $p^n (x, y)$ is the probability of the pair of sequences $(x, y)$.
Here $[k] := {1, dots, k}$, and $[P]$ is $1$ if the statement $P$ is true and $0$ otherwise.
The analysis is in $RR$.
In Lean, $P_e$ is in $[0, infinity]$, and a lemma below converts between the two.

#definition("Binning code", lean: ("Meat.SWCode.typicalDecoder", "Meat.SWCode.binningCode"))[
  Let $f_1 : S^n -> M_1$ and $f_2 : T^n -> M_2$ be bin maps.
  Let $J subset.eq S^n times T^n$ and let $d in S^n times T^n$.
  For $(m_1, m_2) in M_1 times M_2$, the decoder output $g(m_1, m_2)$ is a pair $(x, y) in J$ with $f_1(x) = m_1$ and $f_2(y) = m_2$ if one exists, and $d$ otherwise.
  The binning code is the code $(f_1, f_2, g)$.
]

#lemma("Union bound", lean: "Meat.SWCode.ite_typicalDecoder_le")[
  For every pair $(x, y)$,
  $ [g(f_1(x), f_2(y)) != (x, y)] <= [(x, y) in.not J] + sum_((x', y') in J without {(x, y)}) [f_1(x') = f_1(x)] [f_2(y') = f_2(y)]. $
][
  Suppose that the decoder output is not $(x, y)$.
  If $(x, y) in.not J$, the first term is $1$.
  If $(x, y) in J$, then $(x, y)$ is a candidate for the decoder.
  So the decoder outputs a pair $(x', y') in J$ with $f_1(x') = f_1(x)$ and $f_2(y') = f_2(y)$.
  This pair is not $(x, y)$, so its term in the sum is $1$.
  All terms are nonnegative.
]

#lemma("Real error probability", lean: ("Meat.SWCode.errorProb_ne_top", "Meat.SWCode.errorProb_toReal"))[
  The error probability $P_e$ of a code is finite, and $P_e$ is equal to the real sum
  $ sum_((x, y)) [g(f_1(x), f_2(y)) != (x, y)] p^n (x, y). $
][
  Each term is $0$ or a finite product of finite values.
  So the real value of the sum is the sum of the real values.
]

For the rest of this section, fix $epsilon in RR$, a default pair $d$ and $k_1, k_2 > 0$.
Let $J := J_epsilon^((n)) (p)$.
The bin maps $f_1 : S^n -> [k_1]$ and $f_2 : T^n -> [k_2]$ are random, with the constant weight $k_1^(-|S|^n) k_2^(-|T|^n)$.
So the bins of the sequences are independent and uniform.
Let $P_e (f_1, f_2)$ be the error probability of the binning code of $f_1$, $f_2$, $J$ and $d$.

#theorem("Random binning bound", lean: "Meat.SlepianWolf.sum_errorProb_binningCode_le")[
  The weighted average of $P_e (f_1, f_2)$ over all bin maps is at most
  $ (1 - p^n (J)) + e^(n (H(p) - H(p_2) + 2 epsilon)) / k_1 + e^(n (H(p) - H(p_1) + 2 epsilon)) / k_2 + e^(n (H(p) + epsilon)) / (k_1 k_2). $
][
  Let $beta$ be the sum of the last three terms.
  Fix $(x, y)$ and average the union bound over the bin maps.
  The weights sum to $1$, so the first term stays $[(x, y) in.not J]$.
  The weight is a weight on $f_1$ times a weight on $f_2$.
  The term for $(x', y')$ is a function of $f_1$ times a function of $f_2$.
  By the bin collision lemma, its average is $b_1 b_2$.
  Here $b_1 = 1$ if $x' = x$ and $b_1 = 1 \/ k_1$ otherwise, and $b_2$ is the same for $y'$, $y$ and $k_2$.
  Since $(x', y') != (x, y)$, at most one of $x' = x$ and $y' = y$ is true, so
  $ b_1 b_2 <= [y' = y] / k_1 + [x' = x] / k_2 + 1 / (k_1 k_2). $
  Sum over all $(x', y') in J$.
  The three sums are $|{x' : (x', y) in J}| \/ k_1$, $|{y' : (x, y') in J}| \/ k_2$ and $|J| \/ (k_1 k_2)$.
  By the bound on conditionally typical sequences and the size of the jointly typical set, the sum is at most $beta$.
  So the average error indicator of $(x, y)$ is at most $[(x, y) in.not J] + beta$.
  Multiply by $p^n (x, y)$ and sum over $(x, y)$.
  This gives $sum_((x, y) in.not J) p^n (x, y) + beta = (1 - p^n (J)) + beta$.
]

#corollary("A good binning exists", lean: "Meat.SlepianWolf.exists_binningCode_errorProb_le")[
  Some bin maps $f_1$ and $f_2$ have $P_e (f_1, f_2)$ at most the bound of the random binning theorem.
][
  The weights are nonnegative, and their sum is $1$.
  By the weighted average lemma, some $(f_1, f_2)$ has the real value of $P_e (f_1, f_2)$ at most the bound.
  The value $P_e (f_1, f_2)$ is finite, so the bound also holds in $[0, infinity]$.
]

#theorem("Achievability", lean: "Meat.SlepianWolf.achievable_of_lt")[
  Let $(X, Y)$ have the law $p$.
  If $R_1 > H(X given Y)$, $R_2 > H(Y given X)$ and $R_1 + R_2 > H(X, Y)$, then $(R_1, R_2)$ is achievable for $p$.
][
  Conditional entropy is nonnegative, so $R_1 >= 0$ and $R_2 >= 0$.
  By the lemma on pair laws, $H(X given Y) = H(p) - H(p_2)$ and $H(Y given X) = H(p) - H(p_1)$.
  Also $H(X, Y) = H(p)$.
  Let $gamma$ be a quarter of the smallest of the three slacks $R_1 - H(X given Y)$, $R_2 - H(Y given X)$ and $R_1 + R_2 - H(X, Y)$.
  Then $gamma > 0$.
  Let $epsilon > 0$, and choose $delta in RR$ with $0 < delta < epsilon$.
  By the joint asymptotic equipartition property, $1 - p^n (J_gamma^((n))) -> 0$.
  The three terms
  $ 2 e^(n (H(p) - H(p_2) + 2 gamma - R_1)), quad 2 e^(n (H(p) - H(p_1) + 2 gamma - R_2)), quad 4 e^(n (H(p) + gamma - R_1 - R_2)) $
  also tend to $0$, because the three exponents are at most $-2 n gamma$, $-2 n gamma$ and $-3 n gamma$.
  Take $N$ such that the sum of the four terms is less than $delta$ for every $n >= N$.
  Let $n >= N$ and $k_i := floor(e^(n R_i))$.
  Then $k_i <= e^(n R_i)$.
  Since $n R_i >= 0$, also $k_i >= 1$ and $e^(n R_i) < k_i + 1 <= 2 k_i$, so $1 \/ k_i <= 2 e^(-n R_i)$.
  Some $(s, t)$ has $p(s, t) > 0$, and the default pair $d$ is the pair of constant sequences $s$ and $t$.
  The corollary with the typicality parameter $gamma$ gives a code with $P_e$ at most the sum of the four terms.
  So $P_e < delta < epsilon$.
]

== Slepian-Wolf converse
#source("Meat.Source.SlepianWolfConverse")

This section proves the inclusion $subset.eq$ of the Slepian-Wolf theorem.
The proof uses Fano's inequality for the pair of source sequences, given the pair of indices.
The alphabets $S$ and $T$ are finite, and each singleton is measurable.
In this section, $c = (f_1, f_2, g)$ is a code of length $n$ with finite $M_1$ and $M_2$.

#definition(
  "Source sequences",
  lean: (
    "Meat.SlepianWolf.seqMeasure",
    "Meat.SlepianWolf.isProbabilityMeasure_seqMeasure",
    "Meat.SlepianWolf.seqMeasure_real_singleton",
  ),
)[
  The law $mu_n$ on $S^n times T^n$ is
  $ mu_n (x, y) := p^n (x, y). $
  It is a probability measure.
  Under $mu_n$, the two coordinate maps $X^n$ and $Y^n$ are the two source sequences.
][
  The map $(x, y) |-> (i |-> (x_i, y_i))$ is a bijection onto $(S times T)^n$.
  By distributivity, the masses sum to $product_i sum_a p(a) = 1$.
]

#lemma(
  "Entropy of the source sequences",
  lean: (
    "Meat.SlepianWolf.entropy_seqMeasure",
    "Meat.SlepianWolf.entropy_fst_seqMeasure",
    "Meat.SlepianWolf.entropy_snd_seqMeasure",
  ),
)[
  Under $mu_n$,
  $ H(X^n, Y^n) = n H(p), quad H(X^n) = n H(p_1), quad H(Y^n) = n H(p_2). $
][
  The law of $(X^n, Y^n)$ is $mu_n$.
  By the bijection above, $H(X^n, Y^n) = sum_z eta(p^n (z))$, where $z$ runs over $(S times T)^n$ and $eta$ is the function of the Shannon chapter.
  This is $n H(p)$ by the entropy of an i.i.d. sequence.
  The law of $Y^n$ at $y$ is $sum_x p^n (x, y) = p_2^n (y)$, by the marginal lemma.
  So $H(Y^n) = sum_y eta(p_2^n (y)) = n H(p_2)$.
  The case of $X^n$ is the same.
]

#lemma("Error event", lean: "Meat.SlepianWolf.measureReal_dec_ne")[
  $ mu_n (g(f_1(X^n), f_2(Y^n)) != (X^n, Y^n)) = P_e. $
][
  Both sides are the sum of $p^n (x, y)$ over the pairs $(x, y)$ with $g(f_1(x), f_2(y)) != (x, y)$.
]

#lemma("Fano step", lean: "Meat.SlepianWolf.condEntropy_seqMeasure_le")[
  Let $U := (f_1(X^n), f_2(Y^n))$ be the pair of indices.
  Then
  $ H((X^n, Y^n) given U) <= log 2 + P_e n (log |S| + log |T|). $
][
  Apply the corollary of Fano's inequality to $(X^n, Y^n)$, $U$ and the decoder $g$.
  By the error event lemma, the error probability is $P_e$.
  The set $S^n times T^n$ has $|S|^n |T|^n$ elements.
  Since $p$ exists, $S$ and $T$ are nonempty, so $log (|S|^n |T|^n) = n (log |S| + log |T|)$.
]

#theorem(
  "Converse for one code",
  lean: (
    "Meat.SlepianWolf.mul_condEntropy_fst_snd_le",
    "Meat.SlepianWolf.mul_condEntropy_snd_fst_le",
    "Meat.SlepianWolf.mul_entropy_le",
  ),
)[
  Let $(X, Y)$ have the law $p$, and let $F := log 2 + P_e n (log |S| + log |T|)$.
  Then
  $ n H(X given Y) <= log |M_1| + F, quad n H(Y given X) <= log |M_2| + F, quad n H(X, Y) <= log |M_1| + log |M_2| + F. $
][
  The pair $U$ is a function of $(X^n, Y^n)$.
  So $H(X^n, Y^n) = H(U) + H((X^n, Y^n) given U) <= H(U) + F$, by the Fano step.
  By subadditivity for pairs, $H(U) <= H(f_1(X^n)) + H(f_2(Y^n))$.
  Also $H(f_1(X^n)) <= log |M_1|$, and $H(f_2(Y^n)) <= H(Y^n)$ because $f_2(Y^n)$ is a function of $Y^n$.
  So $H(X^n, Y^n) - H(Y^n) <= log |M_1| + F$.
  By the entropy of the source sequences and the lemma on pair laws, the left side is $n (H(p) - H(p_2)) = n H(X given Y)$.
  The second bound is the same with the roles of the two sources exchanged.
  For the third bound, use $H(f_1(X^n)) <= log |M_1|$, $H(f_2(Y^n)) <= log |M_2|$ and $H(X^n, Y^n) = n H(p) = n H(X, Y)$.
]

This route does not use the chain rule for sequences.
The single-letter step is the exact identity $H(X^n, Y^n) = n H(p)$ for i.i.d. pairs.

#theorem("Weak converse", lean: "Meat.SlepianWolf.mem_rateRegion_of_achievable")[
  If $(R_1, R_2)$ is achievable for $p$, then $(R_1, R_2) in cal(R)(p)$.
][
  It suffices to prove that the three bounds of $cal(R)(p)$ hold up to $delta$, for every $delta > 0$.
  Let $L := log |S| + log |T| >= 0$ and $e := delta \/ (2 (L + 1))$.
  Then $e > 0$ and $e L <= delta \/ 2$.
  Achievability gives $N$ for $e$.
  Take $n >= N$ with $n > 2 log 2 \/ delta$, and a code with $k_i <= e^(n R_i)$ and $P_e <= e$.
  The map $f_1$ sends the nonempty set $S^n$ into $[k_1]$, so $k_1 >= 1$ and $log k_1 <= n R_1$.
  In the same way, $log k_2 <= n R_2$.
  Also $P_e n L <= n delta \/ 2$ and $log 2 < n delta \/ 2$.
  The converse for one code gives $n H(X given Y) <= n R_1 + n delta$, and the same for the other two bounds.
  Divide by $n > 0$.
]

== Slepian-Wolf theorem
#source("Meat.Source.SlepianWolfTheorem")

#proposition("The rate region is closed", lean: "Meat.SlepianWolf.isClosed_rateRegion")[
  The set $cal(R)(p)$ is closed in $RR^2$.
][
  The set $cal(R)(p)$ is the intersection of three sets.
  Each is defined by a non-strict inequality between continuous functions of $(R_1, R_2)$, so each is closed.
]

#theorem("Slepian-Wolf", lean: "Meat.SlepianWolf.closure_achievableRegion_eq")[][
  _Inclusion $subset.eq$._
  By the weak converse, $cal(A)(p) subset.eq cal(R)(p)$.
  The set $cal(R)(p)$ is closed, so it also contains the closure of $cal(A)(p)$.

  _Inclusion $supset.eq$._
  Let $(R_1, R_2) in cal(R)(p)$ and $delta > 0$.
  The pair $(R_1 + delta, R_2 + delta)$ satisfies the three inequalities strictly.
  So it is achievable, by the achievability theorem.
  As $delta -> 0$ from above, $(R_1 + delta, R_2 + delta) -> (R_1, R_2)$.
  So $(R_1, R_2)$ is in the closure of $cal(A)(p)$.
]
