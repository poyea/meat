#import "../meat.typ": *

= Worked examples

This chapter computes a few standard quantities by hand.
Each result is small, but each one is a complete Lean proof.
The examples use only results from earlier chapters:

- the definitions of entropy, conditional entropy and mutual information in "Entropy and mutual information", and the unit change in "The same quantities in bits";
- the bound $H(X) <= log |S|$ from "Shannon-type inequalities", and the uniform entropy and total mass lemmas from "Typical sequences" and "Sequences of random variables";
- the channel $W$, the law $nu_p$ and the capacity $C(W)$ from "Point-to-point channels", and the noise entropy lemma and the range of the information from "Converse";
- the marginals of $nu_p$ from "Rate-distortion coding";
- Gibbs' inequality and its equality case from "Shannon-type inequalities";
- prefix codes and Kraft's inequality from "Prefix codes", and Huffman's lengths from "Huffman codes".

All logarithms are natural logarithms, so entropies are in nats.
To get bits, divide by $log 2$.
As in the Shannon chapter, $eta(t) := -t log t$ for $t > 0$ and $eta(0) := 0$.
The binary entropy function is
$ h(p) := -p log p - (1 - p) log (1 - p) = eta(p) + eta(1 - p). $
Mathlib defines it as `Real.binEntropy`.
In this chapter, $Delta(A)$ is the set of probability mass functions on a finite set $A$.
For $p in Delta(A)$, $p(a)$ is the probability of the letter $a$.

== Binary entropy
#source("Meat.Examples.Binary")

A random variable with two values is a coin.
Its whole law is one number: the probability $p$ of heads.
So its entropy is a function of $p$ only, and this function is $h$.

#proposition(
  "Entropy of a coin",
  lean: (
    "Meat.Examples.measureEntropy_bool",
    "Meat.Examples.entropy_bool",
    "Meat.Examples.measureEntropy_bernoulli",
  ),
)[
  Let $nu$ be a probability measure on ${"true", "false"}$.
  Then $H(nu) = h(nu({"true"}))$.
  Let $X : Omega -> {"true", "false"}$ be measurable and let $mu$ be a probability measure on $Omega$.
  Then $H(X) = h(mu(X = "true"))$.
  For $p in [0, 1]$, the Bernoulli law with $nu({"true"}) = p$ and $nu({"false"}) = 1 - p$ has entropy $h(p)$.
][
  By definition, $H(nu)$ is a sum over the two letters:
  $H(nu) = eta(nu({"false"})) + eta(nu({"true"}))$.
  The total mass is $1$, so $nu({"false"}) = 1 - nu({"true"})$.
  Write $q := nu({"true"})$.
  Then $H(nu) = eta(1 - q) + eta(q) = h(q)$.
  For $X$, the entropy is $H(X_* mu)$, and $X_* mu({"true"}) = mu(X^(-1)({"true"})) = mu(X = "true")$.
  For the Bernoulli law, $q = p$.
]

#proposition(
  "Values of the binary entropy",
  lean: (
    "Meat.Examples.binEntropy_half",
    "Meat.Examples.binEntropy_symm",
    "Meat.Examples.binEntropy_le_log_two",
    "Meat.Examples.binEntropy_eq_log_two_iff",
  ),
)[
  For every real $p$:
  + $h(1/2) = log 2$;
  + $h(1 - p) = h(p)$;
  + $h(p) <= log 2$;
  + $h(p) = log 2$ if and only if $p = 1/2$.
][
  For (1), $h(1/2) = 2 dot (-(1/2) log (1/2)) = log 2$.
  For (2), replace $p$ by $1 - p$ in $eta(p) + eta(1 - p)$: the two terms change places.
  Mathlib proves (3) and (4) with calculus.
  The derivative of $h$ is $log (1 - p) - log p$.
  It is positive for $p < 1/2$ and negative for $p > 1/2$.
  So $h$ increases strictly up to $1/2$ and decreases strictly after $1/2$.
  Its only maximum is at $p = 1/2$, and the maximum value is $h(1/2) = log 2$.
  Outside $[0, 1]$, $h$ is negative, so the bound also holds there.
]

So a coin carries at most one bit, and only a fair coin carries exactly one bit.

== Uniform laws
#source("Meat.Examples.Uniform")

A uniform law gives the same probability to each element of a finite set.
Its entropy is the largest possible entropy on that set.

#proposition(
  "Entropy of a uniform law",
  lean: "Meat.Examples.measureEntropy_uniformOfFinset",
)[
  Let $s$ be a finite subset of a finite set $S$ with $n := |s|$ elements.
  Let $nu$ be the uniform law on $s$, so $nu({x}) = 1/n$ for $x in s$ and $nu({x}) = 0$ otherwise.
  Then $H(nu) = log n$.
][
  Each $x in.not s$ contributes $eta(0) = 0$.
  Each $x in s$ contributes $eta(1/n) = (1/n) log n$.
  There are $n$ such terms, so the sum is $n dot (1/n) log n = log n$.
  If $s$ is empty, then $n = 0$, the measure is zero, and both sides are $0$, because $log 0 = 0$ in Lean.
]

The channel examples below need the uniform law as a probability mass function.

#definition(
  "Uniform probability mass function",
  lean: (
    "Meat.Examples.uniformPMF",
    "Meat.Examples.uniformPMF_toReal",
    "Meat.Examples.measureEntropy_uniformPMF",
  ),
)[
  Let $S$ be a finite nonempty set.
  The uniform probability mass function $u_S in Delta(S)$ is $u_S (s) := 1/|S|$ for every $s in S$.
  Its entropy is $log |S|$.
]

#corollary(
  "A die and a coin",
  lean: ("Meat.Examples.measureEntropy_die", "Meat.Examples.entropyBits_fair_coin"),
)[
  A fair six-sided die has entropy $log 6$ nats.
  Let $X$ be a measurable random variable with values in ${"true", "false"}$ and $mu(X = "true") = 1/2$.
  Then $X$ has entropy $1$ bit: $H_2(X) = H(X) / log 2 = 1$.
][
  The die is the uniform law on a set with $6$ elements, so its entropy is $log 6$.
  For the coin, the binary entropy section gives $H(X) = h(1/2) = log 2$.
  In bits this is $log 2 / log 2 = 1$.
]

== Noiseless and useless channels
#source("Meat.Examples.Noiseless")

This section first proves four tools for the channel examples.
Then it computes the capacity of the two extreme channels.
Recall that for $p in Delta(A)$, $nu_p$ is the law on $A times B$ with $nu_p ({(a, b)}) = p(a) W(b given a)$.
The input is $pi_1$ and the output is $pi_2$.
So $I(p) = I(pi_1; pi_2)$ under $nu_p$, and $C(W) = sup_p I(p)$.

#lemma(
  "Tools for capacity",
  lean: (
    "Meat.Examples.outputLaw_real",
    "Meat.Examples.condEntropy_of_rows",
    "Meat.Examples.inputMutualInfo_eq",
    "Meat.Examples.capacity_eq_of_le",
  ),
)[
  Let $W$ be a channel from $A$ to $B$ and let $p in Delta(A)$.
  + The output has the law $P(pi_2 = b) = sum_(a in A) p(a) W(b given a)$.
  + Suppose that every row of $W$ has the same entropy $c$: $sum_(b in B) eta(W(b given a)) = c$ for every $a$. Then $H(pi_2 given pi_1) = c$.
  + $I(p) = H(pi_2) - H(pi_2 given pi_1)$.
  + Suppose that $I(p) <= C$ for every $p$, and that $I(p_0) = C$ for some $p_0$. Then $C(W) = C$.
][
  For (1), add $nu_p ({(a, b)}) = p(a) W(b given a)$ over $a$.
  For (2), the noise entropy lemma gives
  $ H(pi_2 given pi_1) = -sum_(a, b) p(a) W(b given a) log W(b given a) = sum_a p(a) sum_b eta(W(b given a)). $
  The inner sum is $c$ for each $a$, and $sum_a p(a) = 1$, so the result is $c$.
  For (3), mutual information is symmetric, and $I(pi_2; pi_1) = H(pi_2) - H(pi_2 given pi_1)$ by definition.
  For (4), the supremum is at most $C$, because every $I(p)$ is at most $C$.
  The supremum is at least $I(p_0) = C$.
]

#definition("Noiseless channel", lean: "Meat.Examples.noiseless")[
  The noiseless channel on $A$ sends each input to itself: $W(b given a) = 1$ if $b = a$ and $0$ otherwise.
]

#theorem("Capacity of the noiseless channel", lean: "Meat.Examples.capacity_noiseless")[
  Let $A$ be a finite nonempty set.
  The noiseless channel on $A$ has capacity $log |A|$.
][
  For every channel, $I(p) <= log |A|$, by the range of the information.
  Take the uniform input $p = u_A$.
  Each row of $W$ is a point mass, so its entropy is $eta(1) + eta(0) + dots + eta(0) = 0$.
  By tool (2), $H(pi_2 given pi_1) = 0$.
  Write $[b = a]$ for $1$ if $b = a$ and $0$ otherwise.
  By tool (1), $P(pi_2 = b) = sum_a (1/|A|) [b = a] = 1/|A|$, so the output is uniform.
  The uniform entropy lemma gives $H(pi_2) = log |A|$.
  By tool (3), $I(u_A) = log |A| - 0$.
  Tool (4) gives $C = log |A|$.
]

#definition("Constant channel", lean: "Meat.Examples.constChannel")[
  Let $w in Delta(B)$.
  The constant channel ignores its input: $W(b given a) = w(b)$ for every $a$.
]

#theorem(
  "A constant channel carries nothing",
  lean: ("Meat.Examples.inputMutualInfo_constChannel", "Meat.Examples.capacity_constChannel"),
)[
  For the constant channel with output law $w$, $I(p) = 0$ for every $p in Delta(A)$.
  So its capacity is $0$.
][
  Every row is $w$, so every row has entropy $c := sum_b eta(w(b))$.
  By tool (2), $H(pi_2 given pi_1) = c$.
  By tool (1), $P(pi_2 = b) = sum_a p(a) w(b) = w(b)$, so $H(pi_2) = c$ too.
  By tool (3), $I(p) = c - c = 0$.
  The capacity is the supremum of the constant $0$, which is $0$.
]

== The binary symmetric channel
#source("Meat.Examples.BSC")

The binary symmetric channel sends one bit.
With probability $1 - p$ the bit arrives unchanged, and with probability $p$ it is flipped.
The number $p in [0, 1]$ is the crossover probability.

#definition(
  "Binary symmetric channel",
  lean: ("Meat.Examples.bsc", "Meat.Examples.bsc_toReal"),
)[
  For $p in [0, 1]$, the binary symmetric channel $"BSC"(p)$ from ${"true", "false"}$ to ${"true", "false"}$ is
  $ W(b given a) := 1 - p "if" b = a, quad W(b given a) := p "if" b != a. $
]

#lemma(
  "Information of the binary symmetric channel",
  lean: (
    "Meat.Examples.condEntropy_bsc",
    "Meat.Examples.inputMutualInfo_bsc_le",
    "Meat.Examples.inputMutualInfo_bsc_uniform",
  ),
)[
  For every input law $q$, $H(pi_2 given pi_1) = h(p)$ and $I(q) <= log 2 - h(p)$.
  For the uniform input, $I(q) = log 2 - h(p)$.
][
  Each row of $W$ has the two values $1 - p$ and $p$.
  So each row has entropy $eta(1 - p) + eta(p) = h(p)$.
  Tool (2) gives $H(pi_2 given pi_1) = h(p)$, whatever the input is.
  The output takes two values, so $H(pi_2) <= log 2$.
  Tool (3) gives $I(q) = H(pi_2) - h(p) <= log 2 - h(p)$.
  For the uniform input, tool (1) gives
  $ P(pi_2 = b) = (1/2)(1 - p) + (1/2) p = 1/2 $
  for each $b$.
  So the output is uniform, and $H(pi_2) = log 2$.
]

#theorem(
  "Capacity of the binary symmetric channel",
  lean: ("Meat.Examples.capacity_bsc", "Meat.Examples.capacity_bsc_zero", "Meat.Examples.capacity_bsc_half"),
)[
  For $p in [0, 1]$,
  $ C("BSC"(p)) = log 2 - h(p). $
  In bits this is $1 - h(p) / log 2$.
  In particular, $C("BSC"(0)) = log 2$ and $C("BSC"(1/2)) = 0$.
][
  The lemma gives the bound $I(q) <= log 2 - h(p)$ for every $q$, and equality for the uniform input.
  Tool (4) gives the capacity.
  For $p = 0$, $h(0) = 0$.
  For $p = 1/2$, $h(1/2) = log 2$.
]

When $p = 1/2$, the output is a fair coin flip that does not depend on the input.
So the channel carries no information.
The same formula gives $C("BSC"(1)) = log 2$: a channel that always flips the bit is as good as a noiseless one.

== The binary erasure channel
#source("Meat.Examples.BEC")

The binary erasure channel sends one bit.
With probability $1 - e$ the bit arrives unchanged.
With probability $e$ it is erased: the receiver sees the symbol $?$ and knows that the bit is lost.
In Lean, the output alphabet is `Option Bool`, and `none` is the erasure $?$.
The Lean statements in this section hold for every measurable structure on `Option Bool` in which each singleton is measurable.

#definition(
  "Binary erasure channel",
  lean: ("Meat.Examples.bec", "Meat.Examples.bec_toReal"),
)[
  For $e in [0, 1]$, the binary erasure channel $"BEC"(e)$ from ${"true", "false"}$ to ${"true", "false", ?}$ is
  $ W(? given a) := e, quad W(a given a) := 1 - e, quad W(b given a) := 0 "if" b != a "and" b != ?. $
]

#lemma(
  "Information of the binary erasure channel",
  lean: (
    "Meat.Examples.condEntropy_bec",
    "Meat.Examples.entropy_output_bec",
    "Meat.Examples.inputMutualInfo_bec",
    "Meat.Examples.measureEntropy_pmf_bool_le",
  ),
)[
  Let $q in Delta({"true", "false"})$ be the input law.
  Then $H(pi_2 given pi_1) = h(e)$, $H(pi_2) = h(e) + (1 - e) H(q)$, and
  $ I(q) = (1 - e) H(q). $
  Also $H(q) <= log 2$.
][
  Each row has the values $e$, $1 - e$ and $0$.
  Its entropy is $eta(e) + eta(1 - e) + eta(0) = h(e)$, so tool (2) gives $H(pi_2 given pi_1) = h(e)$.
  By tool (1), $P(pi_2 = ?) = sum_a q(a) e = e$ and $P(pi_2 = b) = q(b)(1 - e)$ for each bit $b$.
  For $x, y >= 0$, $eta(x y) = y eta(x) + x eta(y)$.
  So
  $ H(pi_2) = eta(e) + sum_b eta(q(b)(1 - e)) = eta(e) + (1 - e) sum_b eta(q(b)) + eta(1 - e) sum_b q(b). $
  The last sum is $1$, and $sum_b eta(q(b)) = H(q)$.
  So $H(pi_2) = h(e) + (1 - e) H(q)$.
  Tool (3) gives $I(q) = H(pi_2) - h(e) = (1 - e) H(q)$.
  Finally, $q$ is a law on two letters, so $H(q) <= log 2$.
]

#theorem("Capacity of the binary erasure channel", lean: "Meat.Examples.capacity_bec")[
  For $e in [0, 1]$,
  $ C("BEC"(e)) = (1 - e) log 2. $
  In bits this is $1 - e$.
][
  Since $1 - e >= 0$ and $H(q) <= log 2$, every input gives $I(q) <= (1 - e) log 2$.
  The uniform input has $H(q) = log 2$, so it gives equality.
  Tool (4) gives the capacity.
]

The result is easy to read.
A fraction $e$ of the bits is lost, and the other bits arrive without error.
So at most a fraction $1 - e$ of a bit gets through per use.

== Products and sums of channels
#source("Meat.Examples.Product")

Two channels can be used side by side, or one of them can be chosen at each use.
Shannon (1948) computed both capacities.
Using both channels in parallel adds the capacities.
Choosing one channel at each use adds the exponentials: $e^C = e^(C_1) + e^(C_2)$.

#definition(
  "Product laws and product channels",
  lean: (
    "Meat.Examples.prodPMF",
    "Meat.Examples.prodChannel",
    "Meat.Examples.prodPMF_apply",
    "Meat.Examples.map_fst_prodPMF",
    "Meat.Examples.map_snd_prodPMF",
  ),
)[
  For laws $p_1$ on $A_1$ and $p_2$ on $A_2$, the product law is $(p_1 times.o p_2)(a_1, a_2) = p_1 (a_1) p_2 (a_2)$; its marginals are $p_1$ and $p_2$.
  The product of channels $W_1 : A_1 -> B_1$ and $W_2 : A_2 -> B_2$ is $(W_1 times W_2)((b_1, b_2) given (a_1, a_2)) = W_1 (b_1 given a_1) W_2 (b_2 given a_2)$.
]

#lemma(
  "Information of a product channel",
  lean: ("Meat.Examples.inputMutualInfo_prodChannel_le", "Meat.Examples.inputMutualInfo_prodChannel_prodPMF"),
)[
  For every input law $p$ on $A_1 times A_2$ with marginals $p_1$ and $p_2$,
  $ I_(W_1 times W_2)(p) <= I_(W_1)(p_1) + I_(W_2)(p_2), $
  with equality when $p = p_1 times.o p_2$.
][
  The map $((a_1, a_2), (b_1, b_2)) |-> (a_1, b_1)$ sends the joint law to the joint law of $W_1$ and $p_1$, and the same holds for the second coordinates.
  Since $log (W_1 W_2) = log W_1 + log W_2$ on the support, $H(Y given X) = H(Y_1 given X_1) + H(Y_2 given X_2)$.
  Subadditivity gives $H(Y_1, Y_2) <= H(Y_1) + H(Y_2)$.
  For a product input, the output law is the product of the output laws, so $Y_1$ and $Y_2$ are independent and $I(Y_1 ; Y_2) = 0$.
]

#theorem("Capacity of a product channel", lean: "Meat.Examples.capacity_prodChannel")[
  If $A_1$ and $A_2$ are nonempty,
  $ C(W_1 times W_2) = C(W_1) + C(W_2). $
][
  The lemma bounds every $I_(W_1 times W_2)(p)$ by $C(W_1) + C(W_2)$.
  For $delta > 0$, pick $p_k$ with $I_(W_k)(p_k) > C(W_k) - delta / 2$; the product input reaches $C(W_1) + C(W_2) - delta$.
]

#definition(
  "Sum of channels",
  lean: ("Meat.Examples.sumChannel", "Meat.Examples.measurableSingletonClass_sum"),
)[
  The sum $W_1 plus.o W_2 : A_1 union.sq A_2 -> B_1 union.sq B_2$ uses $W_1$ on inputs from $A_1$ and $W_2$ on inputs from $A_2$, and the output shows which channel was used.
  Singletons in a disjoint union of measurable spaces with measurable singletons are measurable.
]

#theorem("Capacity of a sum channel", lean: "Meat.Examples.capacity_sumChannel")[
  If $A_1$ and $A_2$ are nonempty,
  $ C(W_1 plus.o W_2) = log(e^(C(W_1)) + e^(C(W_2))). $
][
  Write an input law as $p = lambda p_1 + (1 - lambda) p_2$, with $lambda$ the mass of $A_1$; take any $p_k$ when its weight is $0$.
  The output law on $B_1$ is $lambda q_1$ and on $B_2$ is $(1 - lambda) q_2$, and $u v log(u v) = v (u log u) + u (v log v)$, so
  $ I(p) = h(lambda) + lambda I_(W_1)(p_1) + (1 - lambda) I_(W_2)(p_2), $
  with $h(lambda) = -lambda log lambda - (1 - lambda) log(1 - lambda)$.
  For all $c_1, c_2$ and $lambda in [0, 1]$, Gibbs' inequality against the law $(e^(c_1), e^(c_2)) / (e^(c_1) + e^(c_2))$ gives $h(lambda) + lambda c_1 + (1 - lambda) c_2 <= log(e^(c_1) + e^(c_2))$, with equality at $lambda = e^(c_1) / (e^(c_1) + e^(c_2))$.
  This bounds every $I(p)$, and near-optimal $p_1, p_2$ with the optimal $lambda$ come within any $delta$ of the bound.
]


== A dyadic source and its Huffman code
#source("Meat.Examples.HuffmanExample")

This section builds a source for which the entropy bound on expected length is exact.
A probability mass function is dyadic if every probability is a power of $1/2$.

#definition(
  "A dyadic source and a code",
  lean: (
    "Meat.Examples.dyadicSource",
    "Meat.Examples.dyadicSource_toReal",
    "Meat.Examples.dyadicLengths",
    "Meat.Examples.dyadicCode",
  ),
)[
  The source $p$ on the four symbols ${0, 1, 2, 3}$ has
  $ p(0) = 1/2, quad p(1) = 1/4, quad p(2) = 1/8, quad p(3) = 1/8. $
  The code $c$ maps the symbols to the binary words $0$, $10$, $110$ and $111$.
  Its lengths are $ell = (1, 2, 3, 3)$.
]

#proposition(
  "The code",
  lean: (
    "Meat.Examples.isPrefixCode_dyadicCode",
    "Meat.Examples.length_dyadicCode",
    "Meat.Examples.kraft_dyadicLengths",
    "Meat.Examples.expectedLength_dyadicCode",
  ),
)[
  The code $c$ is a prefix code with lengths $(1, 2, 3, 3)$.
  Its lengths satisfy Kraft's inequality with equality:
  $ 2^(-1) + 2^(-2) + 2^(-3) + 2^(-3) = 1. $
  Its expected length is $L(c) = 7/4$.
][
  No word is a prefix of another word: Lean checks the $16$ pairs one by one.
  The Kraft sum is $1/2 + 1/4 + 1/8 + 1/8 = 1$.
  The expected length is
  $ (1/2) dot 1 + (1/4) dot 2 + (1/8) dot 3 + (1/8) dot 3 = 1/2 + 1/2 + 3/8 + 3/8 = 7/4. $
]

#proposition(
  "Entropy of the source",
  lean: ("Meat.Examples.measureEntropy_dyadicSource", "Meat.Examples.entropyBits_dyadicSource"),
)[
  $H(p) = (7/4) log 2$.
  In bits, the entropy is $7/4$.
][
  Use $log 4 = 2 log 2$ and $log 8 = 3 log 2$.
  Then
  $ H(p) = (1/2) log 2 + (1/4) log 4 + 2 dot (1/8) log 8 = (1/2 + 1/2 + 3/4) log 2 = (7/4) log 2. $
]

So the expected length of $c$ equals the entropy in bits.
The entropy bound for prefix codes says that no prefix code does better.

#theorem(
  "The code is optimal",
  lean: ("Meat.Examples.expectedLength_le_dyadicCode", "Meat.Examples.expectedLength_huffmanCode_dyadicSource"),
)[
  Every binary prefix code $c'$ for the source has $L(c) <= L(c')$.
  The Huffman code for the source has expected length exactly $7/4$.
][
  For a binary prefix code $c'$, the entropy bound gives $H(p) <= L(c') log 2$.
  With $H(p) = (7/4) log 2$, this is $7/4 <= L(c')$, and $L(c) = 7/4$.
  The Huffman code is a prefix code, so its expected length is at least $7/4$.
  The Huffman code is optimal among prefix codes, so its expected length is at most $L(c) = 7/4$.
]

The Huffman algorithm in Lean breaks ties by a choice that Lean cannot compute.
So Lean cannot run the algorithm on this source.
The next theorem finds its lengths anyway, from the equality case of Gibbs' inequality.

#theorem(
  "Huffman's lengths",
  lean: "Meat.Examples.huffmanCodeLength_dyadicSource",
)[
  The Huffman code lengths of the source are $(1, 2, 3, 3)$.
][
  Let $ell_H$ be the Huffman lengths and let $r(s) := 2^(-ell_H (s))$.
  The Huffman lengths satisfy Kraft's inequality with equality, so $sum_s r(s) = 1 = sum_s p(s)$.
  By the previous theorem, $sum_s p(s) ell_H (s) = 7/4$.
  So
  $ sum_s p(s) log r(s) = -(7/4) log 2 = -H(p) = sum_s p(s) log p(s). $
  This is the equality case of Gibbs' inequality, so $r(s) = p(s)$ for every $s$.
  Then $2^(-ell_H (0)) = 1/2$, so $ell_H (0) = 1$.
  In the same way, $ell_H (1) = 2$ and $ell_H (2) = ell_H (3) = 3$.
]

The general lesson: when every $p(s)$ is a power of $1/2$, the lengths $ell(s) = log_2 (1 / p(s))$ are whole numbers.
These lengths satisfy Kraft's inequality with equality, and the expected length equals the entropy in bits.
