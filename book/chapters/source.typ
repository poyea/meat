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

== Lossless source coding
#source("Meat.Source.Lossless")

One encoder sees a block of $n$ symbols of an i.i.d. source.
It sends one of $k$ indices.
The decoder must recover the block.
The fixed-length source coding theorem says that the rates above $H(p)$ nats per symbol are achievable, and that the rates below $H(p)$ are not.
Below $H(p)$ the error probability even tends to $1$.
In this section, $S$ is a finite set and $p$ is a probability mass function on $S$.
As in the Shannon chapter, $H(p)$ is the entropy of $p$, $p^n (x)$ is the probability of a sequence $x in S^n$, and $A_epsilon^((n))$ is the weakly typical set.

#definition(
  "Block source code",
  lean: ("Meat.SourceCode", "Meat.SourceCode.errorProb", "Meat.SourceCode.correctSet"),
)[
  Let $n in NN$ and let $M$ be a set.
  A block source code of length $n$ is a pair $(f, g)$ of maps
  $ f : S^n -> M, quad g : M -> S^n. $
  Its error probability for $p$ is
  $ P_e := sum_(x : g(f(x)) != x) product_(i = 1)^n p(x_i). $
  Its set of correctly decoded sequences is $C := {x in S^n : g(f(x)) = x}$.
]

#lemma(
  "Basic facts",
  lean: (
    "Meat.SourceCode.card_correctSet_le",
    "Meat.SourceCode.errorProb_ne_top",
    "Meat.SourceCode.errorProb_toReal",
    "Meat.SourceCode.errorProb_le_one",
  ),
)[
  If $M$ is finite, then $|C| <= |M|$.
  The value $P_e$ is finite, $P_e = 1 - p^n (C)$, and $P_e <= 1$.
][
  The map $f$ is injective on $C$, because $g$ inverts it there.
  So $|C| <= |M|$.
  Each term of $P_e$ is $0$ or a finite product of finite values, so $P_e$ is finite and its real value is the sum of the real values.
  This sum is $sum_(x in.not C) p^n (x) = 1 - p^n (C)$, because $p^n$ sums to $1$.
  Since $p^n (C) >= 0$, $P_e <= 1$.
]

#definition("Code of a set", lean: "Meat.SourceCode.ofFinset")[
  Let $A subset.eq S^n$, let $k in NN$ with $|A| <= k$ and $k > 0$, and let $d in S^n$.
  Fix a numbering of $A$ by ${0, dots, |A| - 1}$.
  The encoder sends each $x in A$ to its number and every other sequence to $0$.
  The decoder sends $m < |A|$ to the sequence with number $m$ and every other index to $d$.
  Here the index set is $M = {0, dots, k - 1}$.
]

#lemma(
  "The code of a set",
  lean: (
    "Meat.SourceCode.ofFinset_dec_enc",
    "Meat.SourceCode.subset_correctSet_ofFinset",
    "Meat.SourceCode.errorProb_ofFinset_le",
  ),
)[
  The code of $A$ decodes every $x in A$ correctly, so $A subset.eq C$ and $P_e <= 1 - p^n (A)$.
][
  For $x in A$, the index of $x$ is its number, which is less than $|A|$.
  So the decoder returns the sequence with this number, which is $x$.
  Then $A subset.eq C$, and $P_e = 1 - p^n (C) <= 1 - p^n (A)$.
]

#definition(
  "Achievable rate",
  lean: ("Meat.Lossless.Achievable", "Meat.Lossless.achievableRates"),
)[
  A rate $R in RR$ is achievable for $p$ if for every $epsilon > 0$ there exists $N in NN$ such that for every $n >= N$ there exist $k in NN$ with $k <= e^(n R)$ and a code of length $n$ with $M = {0, dots, k - 1}$ and $P_e <= epsilon$.
  The set of achievable rates is $cal(A)(p)$.
]

A code with $k = 0$ has no encoder, since $S^n$ is not empty.
So an achievable rate needs $e^(n R) >= 1$ for large $n$, that is $R >= 0$.

#lemma("Small sets", lean: "Meat.Lossless.sum_iidProb_le_card_mul_add")[
  For every $epsilon in RR$ and every $A subset.eq S^n$,
  $ p^n (A) <= |A| e^(-n (H(p) - epsilon)) + (1 - p^n (A_epsilon^((n)))). $
][
  Split $A$ into the typical part and the rest.
  Each typical $x$ has $p^n (x) <= e^(-n (H(p) - epsilon))$, and the typical part has at most $|A|$ elements.
  The rest lies outside $A_epsilon^((n))$, so its probability is at most $1 - p^n (A_epsilon^((n)))$.
]

#theorem("Sets of small rate have small probability", lean: "Meat.Lossless.eventually_sum_iidProb_le")[
  Let $R < H(p)$ and $delta > 0$.
  For every large $n$, every $A subset.eq S^n$ with $|A| <= e^(n R)$ has $p^n (A) <= delta$.
][
  Let $epsilon := (H(p) - R) \/ 2 > 0$.
  By the small sets lemma, $p^n (A) <= e^(n (R - H(p) + epsilon)) + (1 - p^n (A_epsilon^((n))))$.
  The exponent is $-n epsilon$, so the first term tends to $0$.
  The second term tends to $0$ by the asymptotic equipartition property.
  So the bound is at most $delta$ for large $n$, and it does not depend on $A$.
]

#theorem(
  "Strong converse",
  lean: ("Meat.Lossless.eventually_one_sub_le_errorProb", "Meat.Lossless.tendsto_errorProb_one"),
)[
  Let $R < H(p)$ and $delta > 0$.
  For every large $n$, every code of length $n$ with $k <= e^(n R)$ indices has $P_e >= 1 - delta$.
  So for every sequence of codes $c_n$ of length $n$ with $k_n <= e^(n R)$ indices, $P_e (c_n) -> 1$.
][
  The set $C$ of a code has $|C| <= k <= e^(n R)$.
  By the theorem on sets of small rate, $p^n (C) <= delta$ for large $n$.
  So $P_e = 1 - p^n (C) >= 1 - delta$.
  For the sequence, $1 - delta <= P_e (c_n) <= 1$ for large $n$, for every $delta > 0$.
  So the real values tend to $1$, and so do the values in $[0, infinity]$.
]

#theorem("Converse", lean: "Meat.Lossless.le_of_achievable")[
  If $R$ is achievable for $p$, then $R >= H(p)$.
][
  Suppose $R < H(p)$.
  By the strong converse with $delta = 1 \/ 2$, every code with $k <= e^(n R)$ has $P_e >= 1 \/ 2$ for large $n$.
  Achievability with $epsilon = 1 \/ 4$ gives such a code with $P_e <= 1 \/ 4$ for large $n$.
  This is a contradiction.
]

The converse does not use Fano's inequality.
The strong converse gives more: any error probability below $1$ fails below $H(p)$.

#theorem("Achievability", lean: "Meat.Lossless.achievable_of_lt")[
  If $R > H(p)$, then $R$ is achievable for $p$.
][
  Let $gamma := (R - H(p)) \/ 2 > 0$, and let $epsilon > 0$.
  Entropy is nonnegative, so $R > 0$.
  By the asymptotic equipartition property, $1 - p^n (A_gamma^((n))) -> 0$.
  Take $N$ such that $1 - p^n (A_gamma^((n))) < epsilon$ for every $n >= N$.
  Let $n >= N$ and $k := floor(e^(n R))$.
  Then $k <= e^(n R)$, and $k >= 1$ because $n R >= 0$.
  By the size of the typical set, $|A_gamma^((n))| <= e^(n (H(p) + gamma)) <= e^(n R)$.
  The size is an integer, so $|A_gamma^((n))| <= k$.
  Some $s in S$ has $p(s) > 0$, and $d$ is the constant sequence $s$.
  The code of $A_gamma^((n))$ has $P_e <= 1 - p^n (A_gamma^((n))) < epsilon$.
]

#theorem("Fixed-length source coding theorem", lean: "Meat.Lossless.closure_achievableRates_eq")[
  The closure of $cal(A)(p)$ is $[H(p), infinity)$.
][
  By the converse, $cal(A)(p) subset.eq [H(p), infinity)$, and this set is closed.
  By achievability, $(H(p), infinity) subset.eq cal(A)(p)$.
  The closure of $(H(p), infinity)$ is $[H(p), infinity)$.
]

== Prefix codes
#source("Meat.Source.Prefix")

A variable-length code maps each source symbol to a word over an alphabet with $D$ letters.
The words can have different lengths.
This section proves the Kraft and McMillan inequalities, their converse, and the bounds on the expected length that follow.
Mathlib proves Kraft and McMillan for sets of words.
This section transfers them to codes that are maps.
In this section, $S$ is a finite set, $D >= 1$ is a natural number, and $[D] := {0, dots, D - 1}$.
A word is a finite list of letters in $[D]$, and $|w|$ is the length of the word $w$.
Entropy is in nats, as in the Shannon chapter.

#definition(
  "Codes",
  lean: ("Meat.IsPrefixCode", "Meat.IsUDCode", "Meat.expectedLength"),
)[
  A code is a map $c$ from $S$ to words.
  It is a prefix code if $c(s)$ is a prefix of $c(t)$ only when $s = t$.
  Its extension $c^*$ maps a list $(s_1, dots, s_k)$ of symbols to the concatenation $c(s_1) dots c(s_k)$.
  The code is uniquely decodable if $c^*$ is injective.
  For a probability mass function $p$ on $S$, the expected length of $c$ is
  $ L(c) := sum_(s in S) p(s) |c(s)|. $
]

The condition for a prefix code also makes $c$ injective.
If $|S| = 1$, the code with the empty word is a prefix code.
The Shannon code below needs this case.

#lemma(
  "Basic facts",
  lean: (
    "Meat.IsPrefixCode.injective",
    "Meat.IsUDCode.injective",
    "Meat.IsUDCode.ne_nil",
    "Meat.IsPrefixCode.isUDCode",
  ),
)[
  A prefix code is injective.
  A uniquely decodable code is injective, and it has no empty codeword.
  A prefix code with no empty codeword is uniquely decodable.
][
  Each word is a prefix of itself, so $c(s) = c(t)$ gives $s = t$.
  For a uniquely decodable code, $c^*(s) = c^*(t)$ for one-symbol lists gives $s = t$.
  If $c(s)$ is empty, then $c^*(s) = c^*(s, s)$, which contradicts injectivity.
  For the last statement, the set of codewords is prefix-free in the sense of Mathlib and does not contain the empty word.
  Mathlib proves that such a set is uniquely decodable.
  Two lists of codewords with the same concatenation have the same first codeword, because one of the two first codewords is a prefix of the other.
  Since $c$ is injective, the lists of symbols are also equal.
]

#theorem(
  "Kraft-McMillan inequality",
  lean: ("Meat.IsPrefixCode.kraft", "Meat.IsUDCode.kraft"),
)[
  If $c$ is a prefix code or a uniquely decodable code, then
  $ sum_(s in S) D^(-|c(s)|) <= 1. $
][
  Since $c$ is injective, the sum is the Kraft sum of the finite set $C$ of codewords.
  For a prefix code, $C$ is prefix-free, and Mathlib proves Kraft's inequality for $C$.
  For a uniquely decodable code, $C$ is uniquely decodable, and Mathlib proves McMillan's inequality for $C$.
  McMillan's proof counts the words in powers of the Kraft sum.
  Let $K$ be the Kraft sum and $m$ the largest codeword length.
  Then $K^r$ is a sum over $r$-tuples of codewords of $D^(-ell)$, where $ell$ is the length of the concatenation.
  Unique decodability makes the concatenations distinct.
  There are at most $D^ell$ words of length $ell$, and $r <= ell <= r m$, so $K^r <= r m$.
  If $K > 1$, then $K^r$ grows faster than $r m$, which is a contradiction.
]

#theorem("Kraft's converse", lean: "Meat.exists_isPrefixCode_of_kraft")[
  Let $ell : S -> NN$ with $sum_(s in S) D^(-ell(s)) <= 1$.
  Then there is a prefix code $c$ with $|c(s)| = ell(s)$ for every $s in S$.
][
  Induct on a subset $T subset.eq S$, and add the symbols in the order of increasing $ell$.
  For $T = emptyset$ there is nothing to prove.
  Let $a in.not T$ with $ell(t) <= ell(a) =: L$ for every $t in T$, and let $c$ be a prefix code on $T$ with the right lengths.
  The Kraft sum on $T$ is at most $1 - D^(-L)$.
  The number of words of length $L$ that have some $c(t)$ as a prefix is at most
  $ sum_(t in T) D^(L - ell(t)) = D^L sum_(t in T) D^(-ell(t)) <= D^L - 1. $
  There are $D^L$ words of length $L$, so some word $w$ of length $L$ has no $c(t)$ as a prefix.
  Set $c(a) := w$.
  If $w$ is a prefix of $c(t)$, then $|c(t)| <= L$ gives $c(t) = w$, so $c(t)$ is a prefix of $w$, which is false.
  So $c$ is a prefix code on $T union {a}$.
]

#theorem(
  "Entropy bound",
  lean: (
    "Meat.measureEntropy_le_of_kraft",
    "Meat.IsUDCode.measureEntropy_le",
    "Meat.IsPrefixCode.measureEntropy_le",
  ),
)[
  Let $p$ be a probability mass function on $S$.
  If $ell : S -> NN$ satisfies $sum_s D^(-ell(s)) <= 1$, then
  $ H(p) <= (sum_(s in S) p(s) ell(s)) log D. $
  In particular, $H(p) <= L(c) log D$ for every prefix code and every uniquely decodable code $c$.
][
  Let $q(s) := D^(-ell(s)) > 0$.
  Then $sum_s q(s) <= 1 = sum_s p(s)$.
  Gibbs' inequality gives $sum_s p(s) log q(s) <= sum_s p(s) log p(s)$.
  The left side is $-(sum_s p(s) ell(s)) log D$ and the right side is $-H(p)$.
  For codes, apply the Kraft-McMillan inequality to $ell(s) := |c(s)|$.
]

#theorem("Shannon code", lean: "Meat.exists_isPrefixCode_expectedLength_lt")[
  Let $D >= 2$, and let $p$ be a probability mass function on $S$ with $p(s) > 0$ for every $s$.
  Then there is a prefix code $c$ with
  $ L(c) < H(p) / (log D) + 1. $
][
  Let $x(s) := -log p(s) \/ log D >= 0$ and $ell(s) := ceil(x(s))$.
  Then $ell(s) log D >= -log p(s)$, so $D^(ell(s)) >= 1 \/ p(s)$ and $D^(-ell(s)) <= p(s)$.
  So the lengths $ell$ satisfy Kraft's inequality, and Kraft's converse gives a prefix code with these lengths.
  Since $ell(s) < x(s) + 1$ and $p(s) > 0$,
  $ L(c) < sum_s p(s) (x(s) + 1) = H(p) / (log D) + 1. $
]

The positivity assumption is necessary.
If $|S| >= 2$ and $p(s) = 1$ for one $s$, then $H(p) = 0$.
Then $L(c) < 1$ forces $c(s)$ to be empty, and a code with an empty codeword on two or more symbols is not a prefix code.

== Huffman codes
#source("Meat.Source.Huffman")

Huffman's algorithm builds an optimal binary prefix code.
It merges the two lightest subtrees again and again.
This section computes the codeword lengths of Huffman's tree and proves that they are optimal.
Kraft's converse then gives a code with these lengths.
A code built from its lengths in this way is a canonical Huffman code.
In this section, the code alphabet is $[2] = {0, 1}$.

#lemma("Sibling lemma", lean: "Meat.exists_sibling_lengths")[
  Let $F$ be a finite set with nonnegative weights $w(i)$.
  Let $a != b$ in $F$, where $a$ has the smallest weight and $b$ has the smallest weight in $F without {a}$.
  Let $ell : F -> NN$ satisfy $sum_(i in F) 2^(-ell(i)) <= 1$.
  Then there is $ell' : F -> NN$ with $sum_(i in F) 2^(-ell'(i)) <= 1$, $ell'(b) = ell'(a) >= 1$ and
  $ sum_(i in F) w(i) ell'(i) <= sum_(i in F) w(i) ell(i). $
][
  Induct on $sum_i ell(i)$.
  Let $x$ have the largest length $M := ell(x)$.

  _Case 1: another $y != x$ also has $ell(y) = M$._
  Then $M >= 1$, because two terms equal to $1$ would make the Kraft sum at least $2$.
  Exchange the lengths of $a$ and $x$.
  The Kraft sum does not change.
  The cost changes by $(w(x) - w(a)) (ell(a) - M) <= 0$.
  Now $a$ has length $M$, and some $y' != a$ also has length $M$.
  Exchange the lengths of $b$ and $y'$.
  The cost again does not increase, because $w(b) <= w(y')$ and every length is at most $M$.
  Now $a$ and $b$ both have length $M >= 1$.

  _Case 2: every $y != x$ has $ell(y) < M$._
  Since $|F| >= 2$, $M >= 1$.
  Multiply the Kraft inequality by $2^M$.
  This gives $1 + E <= 2^M$, where $E := sum_(y != x) 2^(M - ell(y))$.
  Each term of $E$ is even, and $2^M$ is even, so $E + 2 <= 2^M$.
  So the length $M - 1$ for $x$ still satisfies Kraft's inequality.
  The cost does not increase, and $sum_i ell(i)$ decreases.
  The induction hypothesis gives $ell'$.
]

#definition("Huffman lengths", lean: "Meat.huffmanLength")[
  Let $p$ be a weight function on a set $A$.
  A forest is a finite set $F$ of finite subsets of $A$, called blocks.
  The weight of a block $t$ is $w(t) := sum_(s in t) p(s)$.
  If $|F| <= 1$, every Huffman length is $0$.
  Otherwise let $a in F$ have the smallest weight, and let $b$ have the smallest weight in $F without {a}$.
  The merged forest is $F' := (F without {a, b}) union {a union b}$.
  The Huffman lengths of $F$ are
  $ ell_F (a) = ell_F (b) := ell_(F') (a union b) + 1, quad ell_F (t) := ell_(F') (t) "for the other" t. $
]

The recursion stops, because $|F'| < |F|$.
The blocks play the role of subtrees, and $ell_F (t)$ is the depth of the subtree $t$ in Huffman's final tree.
When there are ties, a fixed choice picks $a$ and $b$.

#theorem("Huffman lengths are complete", lean: "Meat.sum_huffmanLength")[
  Let $F$ be a nonempty forest of nonempty and pairwise disjoint blocks.
  Then
  $ sum_(t in F) 2^(-ell_F (t)) = 1. $
][
  Induct on $|F|$.
  If $|F| = 1$, the sum is $2^0 = 1$.
  Otherwise the blocks of $F'$ are also nonempty and pairwise disjoint.
  The block $a union b$ is not in $F without {a, b}$, because it would meet $a$.
  So the terms of $a$ and $b$ in $F$ add up to the term of $a union b$ in $F'$:
  $ 2^(-ell_(F') (a union b) - 1) + 2^(-ell_(F') (a union b) - 1) = 2^(-ell_(F') (a union b)). $
  The other terms are the same, and the sum over $F'$ is $1$ by induction.
]

#theorem("Huffman lengths are optimal", lean: "Meat.huffmanLength_le")[
  Let $p >= 0$, and let $F$ be a forest of nonempty and pairwise disjoint blocks.
  If $ell : F -> NN$ satisfies $sum_(t in F) 2^(-ell(t)) <= 1$, then
  $ sum_(t in F) w(t) ell_F (t) <= sum_(t in F) w(t) ell(t). $
][
  Induct on $|F|$.
  If $|F| <= 1$, the left side is $0$ and the right side is nonnegative.
  Otherwise the sibling lemma gives $ell^*$ with Kraft's inequality, $ell^*(a) = ell^*(b) = m + 1$ and a cost at most the cost of $ell$.
  On $F'$, let $ell'(a union b) := m$ and $ell'(t) := ell^*(t)$ for the other blocks.
  The Kraft sum of $ell'$ on $F'$ is the Kraft sum of $ell^*$ on $F$, so it is at most $1$.
  Since $a$ and $b$ are disjoint, $w(a union b) = w(a) + w(b)$.
  So the cost of $ell'$ on $F'$ is the cost of $ell^*$ on $F$ minus $w(a) + w(b)$.
  In the same way, the Huffman cost of $F$ is the Huffman cost of $F'$ plus $w(a) + w(b)$.
  The induction hypothesis on $F'$ gives the bound.
]

#definition(
  "Huffman code",
  lean: (
    "Meat.huffmanCodeLength",
    "Meat.huffmanCode",
    "Meat.sum_huffmanCodeLength",
    "Meat.isPrefixCode_huffmanCode",
    "Meat.length_huffmanCode",
  ),
)[
  Let $p$ be a probability mass function on $S$.
  The Huffman length $ell_H (s)$ is the Huffman length of ${s}$ in the forest of singletons ${{s} : s in S}$, with the weights $p$.
  Then $sum_(s in S) 2^(-ell_H (s)) = 1$.
  The Huffman code $c_H$ is a binary prefix code with $|c_H (s)| = ell_H (s)$, given by Kraft's converse.
][
  The singletons are nonempty and pairwise disjoint, so the sum is $1$ by completeness.
  In particular, Kraft's inequality holds and Kraft's converse applies.
]

#theorem(
  "Optimality of Huffman codes",
  lean: (
    "Meat.huffmanCodeLength_le",
    "Meat.IsPrefixCode.expectedLength_huffmanCode_le",
    "Meat.IsUDCode.expectedLength_huffmanCode_le",
  ),
)[
  If $ell : S -> NN$ satisfies $sum_s 2^(-ell(s)) <= 1$, then $sum_s p(s) ell_H (s) <= sum_s p(s) ell(s)$.
  In particular, $L(c_H) <= L(c)$ for every binary prefix code and every binary uniquely decodable code $c$.
][
  Apply the optimality of Huffman lengths to the forest of singletons, with $ell({s}) := ell(s)$.
  The weight of ${s}$ is $p(s)$.
  For codes, the Kraft-McMillan inequality gives Kraft's inequality for $ell(s) := |c(s)|$.
]

#corollary("Huffman code and entropy", lean: "Meat.expectedLength_huffmanCode_lt")[
  If $p(s) > 0$ for every $s$, then
  $ L(c_H) < H(p) / (log 2) + 1. $
][
  The Shannon code with $D = 2$ is a prefix code with expected length less than $H(p) \/ log 2 + 1$.
  The expected length $L(c_H)$ is at most this length, by optimality.
]

== Variable-length source coding
#source("Meat.Source.LosslessVariable")

This section codes blocks of $n$ symbols of an i.i.d. source with variable-length words.
The block alphabet $S^n$ is finite, so the results of the prefix codes section apply to it.
The minimal expected length per symbol tends to $H(p) \/ log D$.
In this section, $S$ is a finite set, $p$ is a probability mass function on $S$, $D$ is a natural number, and $L(c)$ is the expected length of a code $c$.

#definition(
  "Block law",
  lean: ("Meat.sum_prod_pmf_eq_one", "Meat.iidPMF", "Meat.iidPMF_toReal", "Meat.iidPMF_ne_zero"),
)[
  The block law $p^n$ is the probability mass function on $S^n$ with
  $ p^n (x) := product_(i = 1)^n p(x_i). $
  Its real values are the product probabilities of the Shannon chapter.
  If $p(s) > 0$ for every $s$, then $p^n (x) > 0$ for every $x$.
][
  By distributivity, $sum_x product_i p(x_i) = product_i sum_s p(s) = 1$.
  A finite product of nonzero factors is nonzero.
]

#lemma("Entropy of the block law", lean: "Meat.measureEntropy_iidPMF")[
  $ H(p^n) = n H(p). $
][
  The masses of $p^n$ are the product probabilities.
  The claim is the entropy of an i.i.d. sequence.
]

#theorem("Shannon code without positivity", lean: "Meat.exists_isPrefixCode_expectedLength_le")[
  Let $D >= 2$.
  There is a prefix code $c$ on $S$ with no empty codeword and
  $ L(c) <= H(p) / (log D) + 1. $
][
  Let $x(s) := -log p(s) \/ log D >= 0$ and $m(s) := floor(x(s)) + 1 > x(s)$.
  For $p(s) > 0$, $D^(-m(s)) < p(s)$.
  So $K := sum_(s : p(s) > 0) D^(-m(s)) < sum_s p(s) = 1$, because some $s$ has $p(s) > 0$.
  Since $D^(-ell) -> 0$, there is $ell_0 >= 1$ with $|S| D^(-ell_0) < 1 - K$.
  Let $ell(s) := m(s)$ if $p(s) > 0$ and $ell(s) := ell_0$ otherwise.
  Then $sum_s D^(-ell(s)) <= K + |S| D^(-ell_0) < 1$.
  Kraft's converse gives a prefix code with these lengths.
  Every length is at least $1$, so no codeword is empty.
  The symbols with $p(s) = 0$ do not count in $L(c)$, and $m(s) <= x(s) + 1$, so
  $ L(c) <= sum_s p(s) (x(s) + 1) = H(p) / (log D) + 1. $
]

The bound is not strict in general.
For $|S| >= 2$ and a deterministic source, every prefix code with no empty codeword has $L(c) >= 1 = H(p) \/ log D + 1$.

#theorem(
  "Converse for block codes",
  lean: ("Meat.IsUDCode.mul_measureEntropy_le", "Meat.IsUDCode.div_log_le_expectedLength_div"),
)[
  Let $c$ be a uniquely decodable code on $S^n$ with $D >= 1$ letters.
  Then $n H(p) <= L(c) log D$, where $L(c)$ is taken for $p^n$.
  If $D >= 2$ and $n > 0$, then
  $ H(p) / (log D) <= L(c) / n. $
][
  The entropy bound of the prefix codes section for $p^n$ gives $H(p^n) <= L(c) log D$.
  By the entropy of the block law, $H(p^n) = n H(p)$.
  For $D >= 2$, $log D > 0$, and dividing by $n log D$ gives the second form.
]

#theorem(
  "Achievability for block codes",
  lean: (
    "Meat.exists_isPrefixCode_block_le",
    "Meat.exists_isPrefixCode_block_lt",
    "Meat.exists_isPrefixCode_block_div_le",
    "Meat.exists_isPrefixCode_block_div_lt",
  ),
)[
  Let $D >= 2$.
  There is a prefix code $c$ on $S^n$ with no empty codeword and $L(c) <= n H(p) \/ log D + 1$.
  If $p(s) > 0$ for every $s$, there is a prefix code with $L(c) < n H(p) \/ log D + 1$.
  For $n > 0$, these bounds read
  $ L(c) / n <= H(p) / (log D) + 1 / n quad "and" quad L(c) / n < H(p) / (log D) + 1 / n. $
][
  Apply the Shannon code without positivity to $p^n$, and use $H(p^n) = n H(p)$.
  If $p$ is positive, then $p^n$ is positive, and the Shannon code of the prefix codes section gives the strict bound.
  Divide by $n$.
]

#definition("Minimal expected length", lean: "Meat.minExpectedLength")[
  $L_n^*$ is the infimum of $L(c)$ over all uniquely decodable codes $c$ on $S^n$ with $D$ letters, where $L(c)$ is taken for $p^n$.
]

#theorem(
  "Variable-length source coding theorem",
  lean: ("Meat.minExpectedLength_bounds", "Meat.tendsto_minExpectedLength_div"),
)[
  Let $D >= 2$.
  For every $n$,
  $ (n H(p)) / (log D) <= L_n^* <= (n H(p)) / (log D) + 1. $
  So $L_n^* \/ n -> H(p) \/ log D$ as $n -> infinity$.
][
  The prefix code of the achievability theorem has no empty codeword, so it is uniquely decodable.
  So the set of lengths is nonempty, and $L_n^*$ is at most its length.
  By the converse, every length in the set is at least $n H(p) \/ log D$.
  So the set is bounded below, and $L_n^*$ is at least this bound.
  For $n > 0$, divide by $n$: $H(p) \/ log D <= L_n^* \/ n <= H(p) \/ log D + 1 \/ n$.
  The upper bound tends to $H(p) \/ log D$.
]
