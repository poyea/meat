#import "../meat.typ": *

= Channel coding

Rates are in nats for each channel use.
A rate is achievable if sufficiently long codes exist for each specified average error probability.
Each coding theorem states that the closure of the achievable region is equal to an information region.
The closure is necessary because rates on the boundary are not always achievable.
In this chapter, $Delta(B)$ is the set of probability mass functions on a set $B$, and $[k] := {1, dots, k}$.

== Point-to-point channels
#source("Meat.Channel.Basic")

#definition("Discrete memoryless channel", lean: ("Meat.DMC", "Meat.DMC.blockProb"))[
  A discrete memoryless channel from $A$ to $B$ is a map $W : A -> Delta(B)$.
  For $n in NN$, $x^n in A^n$ and $y^n in B^n$, its $n$-fold extension is
  $ W^n (y^n given x^n) := product_(i = 1)^n W(y_i given x_i). $
]

Multi-user channels use the same type.
A multiple access channel is a DMC from $A_1 times A_2$.
A broadcast channel is a DMC to $B_1 times B_2$.

#definition(
  "Block code",
  lean: ("Meat.BlockCode", "Meat.BlockCode.errorProb", "Meat.BlockCode.avgError"),
)[
  Let $n in NN$ and let $M$ be a finite set.
  A block code of length $n$ is a pair $(f, g)$ of maps $f : M -> A^n$ and $g : B^n -> M$.
  For $m in M$ its error probability is
  $ lambda_m := sum_(y^n in B^n : g(y^n) != m) W^n (y^n given f(m)), $
  and its average error probability is $overline(lambda) := |M|^(-1) sum_(m in M) lambda_m$.
]

#definition(
  "Information capacity",
  lean: ("Meat.DMC.jointMeasure", "Meat.DMC.inputMutualInfo", "Meat.DMC.capacity"),
)[
  Let $A$ and $B$ be finite.
  For $p in Delta(A)$, let $(X, Y)$ have the law $p(x) W(y given x)$ on $A times B$, and let $I(p) := I(X; Y)$.
  The information capacity of $W$ is
  $ C(W) := sup_(p in Delta(A)) I(p). $
]

#definition("Achievable rate", lean: "Meat.DMC.Achievable")[
  A rate $R in RR$ is achievable for $W$ if for every $epsilon > 0$ there exists $N in NN$ such that for every $n >= N$ there exist $k in NN$ with $k >= e^(n R)$ and a block code of length $n$ with $M = [k]$ and $overline(lambda) <= epsilon$.
]

== Achievability
#source("Meat.Channel.Achievability")

This subsection proves the inclusion $supset.eq$ of the channel coding theorem.
The proof is random coding with joint typicality decoding.
The analysis is in $RR$.
In Lean, error probabilities are in $[0, infinity]$, and a lemma below converts between the two.
Here $[P]$ is $1$ if the statement $P$ is true and $0$ otherwise.

#definition(
  "Pair law",
  lean: (
    "Meat.DMC.jointPMF",
    "Meat.DMC.jointMeasure_eq_toMeasure",
    "Meat.DMC.jointPMF_apply",
    "Meat.DMC.jointPMF_map_fst",
    "Meat.DMC.iidProb_jointPMF",
  ),
)[
  For $q in Delta(A)$, the pair law $p_(W, q) in Delta(A times B)$ is the law of the pair (input, output) when the input has law $q$:
  $ p_(W, q) (a, b) := q(a) W(b given a). $
  Its measure is the measure in the definition of $I(q)$.
  So $I(q)$ is the mutual information of the two coordinates under $p_(W, q)$.
  The first marginal of $p_(W, q)$ is $q$.
  For sequences, $p_(W, q)^n (x, y) = q^n (x) W^n (y given x)$.
][
  In Lean, $p_(W, q)$ is the bind of $q$ with the map that sends $a$ to the push-forward of $W(a)$ by $b |-> (a, b)$.
  So the measure identity holds by definition.
  At $(a, b)$, only the input $a$ and the output $b$ contribute to the sums in the bind and the push-forward.
  The push-forward of $W(a)$ by $b |-> a$ is the point mass at $a$, and the bind of $q$ with point masses is $q$.
  The identity for sequences is the product of the identity for single letters.
]

#lemma(
  "Real error probabilities",
  lean: (
    "Meat.DMC.blockProb_ne_top",
    "Meat.DMC.sum_blockProb_eq_one",
    "Meat.BlockCode.errorProb_ne_top",
    "Meat.BlockCode.errorProb_toReal",
    "Meat.BlockCode.avgError_le_ofReal",
  ),
)[
  The values $W^n (y given x)$ and $lambda_m$ are finite, and $sum_y W^n (y given x) = 1$.
  The error probability $lambda_m$ is equal to the real sum
  $ sum_(y : g(y) != m) W^n (y given f(m)). $
  Let $M$ be nonempty and let $delta in RR$.
  If $sum_m lambda_m <= |M| delta$ in $RR$, then $overline(lambda) <= delta$.
][
  A finite product and a finite sum of finite values are finite.
  By distributivity, $sum_y product_i W(y_i given x_i) = product_i sum_b W(b given x_i) = 1$.
  The real value of the sum is the sum of the real values.
  For the average, $delta >= 0$, because the left side is nonnegative and $|M| > 0$.
  Then $sum_m lambda_m <= |M| delta$ also holds in $[0, infinity]$.
  Divide by $|M|$.
]

#definition(
  "Typicality code",
  lean: ("Meat.BlockCode.typicalDecoder", "Meat.BlockCode.typicalCode", "Meat.BlockCode.typicalDecoder_eq"),
)[
  Let $C : M -> A^n$ be a codebook, let $J subset.eq A^n times B^n$ and let $m_0 in M$.
  For $y in B^n$, the decoder output $g(y)$ is a message $m$ with $(C(m), y) in J$ if one exists, and $m_0$ otherwise.
  The typicality code is the block code $(C, g)$.
  If $(C(m), y) in J$ and $(C(m'), y) in.not J$ for every $m' != m$, then $g(y) = m$.
][
  The decoder chooses a message $m'$ with $(C(m'), y) in J$.
  By the second condition, $m' = m$.
]

#lemma(
  "Typicality decoder",
  lean: ("Meat.BlockCode.typicalDecoder_mem", "Meat.BlockCode.ite_comp_typicalDecoder_le"),
)[
  Let $g$ be the decoder of the typicality code for $C$, $J$ and $m_0$.
  If $(C(m), y) in J$, then $(C(g(y)), y) in J$.
  Let $pi : M -> M'$ and $b >= 0$.
  Then
  $ [pi(g(y)) != pi(m)] b <= [(C(m), y) in.not J] b + sum_(m' : pi(m') != pi(m)) [(C(m'), y) in J] b. $
][
  If some message is typical with $y$, the decoder outputs such a message.
  For the bound, suppose that $pi(g(y)) != pi(m)$ and $(C(m), y) in J$.
  Then $g(y)$ is a message $m'$ with $pi(m') != pi(m)$ and $(C(m'), y) in J$, and the sum contains the term $b$.
  All terms are nonnegative.
]

The map $pi$ lets a receiver ignore part of the message.
With $pi$ the identity, the lemma gives the union bound below.
The broadcast section uses $pi(m_1, m_2) = m_1$ for a receiver that may decode $m_2$ wrongly.

#lemma("Union bound", lean: "Meat.BlockCode.errorProb_typicalCode_toReal_le")[
  For the typicality code, every message $m$ has
  $ lambda_m <= sum_y [(C(m), y) in.not J] W^n (y given C(m)) + sum_(m' != m) sum_y [(C(m'), y) in J] W^n (y given C(m)). $
][
  Apply the typicality decoder lemma with $pi$ the identity and $b = W^n (y given C(m))$, and sum over $y$.
]

For the rest of this subsection, fix $q in Delta(A)$ and $epsilon in RR$.
Let $p := p_(W, q)$, let $J := J_epsilon^((n)) (p)$ and let $I := I(q)$.
The codebook $C : M -> A^n$ is random, with the product weight $product_m q^n (C(m))$.
So the codewords are independent with the law $q^n$.
Let $lambda_m (C)$ and $overline(lambda)(C)$ be the error probabilities of the typicality code of $C$, $J$ and a fixed $m_0$.

#lemma(
  "Error terms of random codewords",
  lean: ("Meat.DMC.sum_iidProb_mul_sum_ite_jointPMF", "Meat.DMC.sum_iidProb_mul_iidProb_mul_sum_le"),
)[
  Let $V$ be a DMC from $A$ to $B$ and let $q in Delta(A)$.
  For every $J' subset.eq A^n times B^n$,
  $ sum_x q^n (x) sum_y [(x, y) in.not J'] V^n (y given x) = 1 - p_(V, q)^n (J'). $
  For $J' := J_epsilon^((n)) (p_(V, q))$,
  $ sum_(x, x') q^n (x) q^n (x') sum_y [(x', y) in J'] V^n (y given x) <= e^(-n (I_V (q) - 3 epsilon)). $
][
  For the first identity, $q^n (x) V^n (y given x) = p_(V, q)^n (x, y)$, and $p_(V, q)^n$ sums to $1$.
  For the second, summing over $x$ first gives $sum_x p_(V, q)^n (x, y) = p_2^n (y)$, by the marginal lemma.
  The first marginal of $p_(V, q)$ is $q$.
  So the sum is $sum_((x', y) in J') p_1^n (x') p_2^n (y)$, which is at most $e^(-n (I_V (q) - 3 epsilon))$ by the independent-pair bound.
]

#theorem("Random coding bound", lean: "Meat.DMC.sum_errorProb_typicalCode_le")[
  For every message $m$,
  $ sum_C (product_(m') q^n (C(m'))) lambda_m (C) <= (1 - p^n (J)) + (|M| - 1) e^(-n (I - 3 epsilon)). $
][
  Average the union bound over $C$.
  The first term depends only on $C(m)$.
  By the product weights lemma, its average is
  $ sum_x q^n (x) sum_y [(x, y) in.not J] W^n (y given x) = 1 - p^n (J), $
  by the lemma on error terms.
  Fix $m' != m$.
  The term $sum_y [(C(m'), y) in J] W^n (y given C(m))$ is a function of $C(m)$ and $C(m')$.
  By the product weights lemma at two indices, its average is
  $ sum_(x, x') q^n (x) q^n (x') sum_y [(x', y) in J] W^n (y given x), $
  which is at most $e^(-n (I - 3 epsilon))$ by the lemma on error terms.
  There are $|M| - 1$ messages $m' != m$.
]

#corollary("A good codebook exists", lean: "Meat.DMC.exists_typicalCode_avgError_le")[
  Some codebook $C$ has
  $ overline(lambda)(C) <= (1 - p^n (J)) + (|M| - 1) e^(-n (I - 3 epsilon)). $
][
  Let $beta$ be the right side.
  Sum the random coding bound over $m$.
  So the weighted average of $sum_m lambda_m (C)$ is at most $|M| beta$.
  The weights are nonnegative, and their sum is $1$.
  By the weighted average lemma, some $C$ has $sum_m lambda_m (C) <= |M| beta$.
  Then $overline(lambda)(C) <= beta$, by the lemma on real error probabilities.
]

#theorem("Achievability", lean: "Meat.DMC.achievable_of_lt_inputMutualInfo")[
  Let $A$ and $B$ be finite, let $q in Delta(A)$ and let $R < I(q)$.
  Then $R$ is achievable for $W$.
][
  Let $epsilon > 0$, and choose $delta in RR$ with $0 < delta < epsilon$.
  Let $eta := (I(q) - R) \/ 4$.
  Then $eta > 0$ and $R - (I(q) - 3 eta) = -eta$.
  By the joint asymptotic equipartition property, $1 - p^n (J_eta^((n))) -> 0$.
  Also $e^(n (R - (I(q) - 3 eta))) -> 0$ by exponential decay, because $R - (I(q) - 3 eta) = -eta < 0$.
  Take $N$ such that the sum of these two terms is less than $delta$ for every $n >= N$.
  Let $n >= N$ and $k := ceil(e^(n R))$.
  Then $k >= 1$, $k >= e^(n R)$ and $k - 1 <= e^(n R)$.
  The corollary with $M = [k]$, the typicality parameter $eta$ and $m_0 = 1$ gives a code with
  $ overline(lambda) <= (1 - p^n (J_eta^((n)))) + e^(n R) e^(-n (I(q) - 3 eta)) < delta. $
]

#lemma("Clamped rates", lean: "Meat.exp_mul_max_le")[
  Let $k in NN$ and $R in RR$.
  If $e^(n R) <= k$, then $e^(n max(R, 0)) <= k$.
][
  If $R <= 0$, then $e^(n max(R, 0)) = 1$, and $k >= e^(n R) > 0$ gives $k >= 1$.
  Otherwise $max(R, 0) = R$.
]

The multi-user sections use this lemma to replace a negative rate by $0$.

#corollary("Rates below capacity", lean: ("Meat.DMC.achievable_of_lt_capacity", "Meat.DMC.achievable_zero"))[][
  For the first statement, suppose that $Delta(A)$ is empty.
  Then $C(W) = 0$, because Lean defines the supremum over the empty set as $0$.
  This contradicts $0 <= R < C(W)$.
  So $Delta(A)$ is nonempty, and some $q$ has $R < I(q)$, because $R$ is less than the supremum.
  Apply the achievability theorem.
  For the second statement, use one message, so $k = 1 = e^(n dot 0)$.
  The encoder sends a fixed sequence, and this needs a nonempty $A$.
  Every decoder output is the correct message, so $overline(lambda) = 0$.
]

== Converse
#source("Meat.Channel.Converse")

This subsection proves the inclusion $subset.eq$ of the channel coding theorem.
The proof uses Fano's inequality and a bound on the information that $n$ uses of $W$ can carry.
The alphabets $A$ and $B$ are finite, and each singleton is measurable.
For $p in Delta(A)$, $nu_p$ is the law $p(a) W(b given a)$ on $A times B$ from the definition of $I(p)$.
Under $nu_p$, the coordinate maps are $pi_1$ (the input) and $pi_2$ (the output).

#proposition(
  "Range of the information",
  lean: (
    "Meat.DMC.isProbabilityMeasure_jointMeasure",
    "Meat.DMC.inputMutualInfo_nonneg",
    "Meat.DMC.inputMutualInfo_le_log_card",
    "Meat.DMC.inputMutualInfo_le_log_card_output",
  ),
)[
  The law $nu_p$ is a probability measure.
  For every $p in Delta(A)$,
  $ 0 <= I(p) <= log |A|, quad I(p) <= log |B|. $
][
  The law $nu_p$ is the measure of a probability mass function.
  Mutual information is nonnegative.
  Also $I(p) = H(pi_1) - H(pi_1 given pi_2) <= H(pi_1) <= log |A|$, because conditional entropy is nonnegative.
  In the same way, $I(p) = H(pi_2) - H(pi_2 given pi_1) <= log |B|$.
]

#proposition(
  "Capacity is finite",
  lean: (
    "Meat.DMC.bddAbove_range_inputMutualInfo",
    "Meat.DMC.inputMutualInfo_le_capacity",
    "Meat.DMC.capacity_nonneg",
  ),
)[
  The set ${I(p) : p in Delta(A)}$ is bounded above.
  Hence $I(p) <= C(W)$ for every $p in Delta(A)$.
  Also $C(W) >= 0$.
][
  The bound $log |A|$ is an upper bound.
  So $C(W)$ is the least upper bound, and it is at least each $I(p)$.
  Each $I(p)$ is nonnegative.
  If $Delta(A)$ is empty, Lean defines the supremum as $0$, so $C(W) >= 0$ in each case.
]

#lemma("Noise entropy", lean: "Meat.DMC.condEntropy_snd_fst_jointMeasure")[
  $ H(pi_2 given pi_1) = -sum_((a, b) in A times B) p(a) W(b given a) log W(b given a), $
  where the entropies are under $nu_p$.
][
  By definition, $H(pi_2 given pi_1) = H(pi_2, pi_1) - H(pi_1)$.
  The map $(a, b) |-> (b, a)$ is injective, so $H(pi_2, pi_1) = H(nu_p) = -sum_(a, b) nu_p (a, b) log nu_p (a, b)$.
  The first marginal of $nu_p$ is $p$, so $H(pi_1) = -sum_(a, b) nu_p (a, b) log p(a)$.
  If $nu_p (a, b) = p(a) W(b given a) > 0$, then $log nu_p (a, b) - log p(a) = log W(b given a)$.
  Terms with $nu_p (a, b) = 0$ are zero on both sides.
]

Now fix a finite nonempty message set $M$ and a block code $c = (f, g)$ of length $n$.

#definition(
  "Message and output",
  lean: (
    "Meat.sum_inv_card",
    "Meat.BlockCode.codeMeasure",
    "Meat.BlockCode.isProbabilityMeasure_codeMeasure",
    "Meat.BlockCode.inputLaw",
  ),
)[
  The uniform weights satisfy $sum_(m in M) |M|^(-1) = 1$.
  The law $mu_c$ on $M times B^n$ is
  $ mu_c (m, y^n) := |M|^(-1) W^n (y^n given f(m)). $
  It is a probability measure.
  Under $mu_c$, the message $U$ and the output $Y^n$ are the two coordinate maps.
  So $U$ is uniform on $M$, and $Y^n$ is the output of $W^n$ for the input $f(U)$.
  For $i in [n]$, the input law $p_i in Delta(A)$ is the law of the $i$-th input letter $f(U)_i$:
  $ p_i (a) := |M|^(-1) |{m in M : f(m)_i = a}|. $
][
  For each $x^n$, distributivity gives $sum_(y^n) product_i W(y_i given x_i) = product_i sum_b W(b given x_i) = 1$.
  So the masses $mu_c (m, y^n)$ sum to $|M| dot |M|^(-1) = 1$.
]

#lemma(
  "Message entropy and error",
  lean: ("Meat.BlockCode.entropy_fst_codeMeasure", "Meat.BlockCode.measureReal_dec_ne"),
)[
  $ H(U) = log |M|, quad mu_c (g(Y^n) != U) = overline(lambda). $
][
  The law of $U$ is $m |-> |M|^(-1) sum_(y^n) W^n (y^n given f(m)) = |M|^(-1)$.
  The entropy of the uniform law on $M$ is $log |M|$.
  For the second identity, $mu_c (g(Y^n) != U) = |M|^(-1) sum_m sum_(y^n : g(y^n) != m) W^n (y^n given f(m)) = |M|^(-1) sum_m lambda_m$.
]

#lemma("One letter", lean: "Meat.BlockCode.map_codeMeasure")[
  For each $i in [n]$, the law of $(f(U)_i, Y_i)$ under $mu_c$ is $nu_(p_i)$.
][
  Fix $(a, b)$ and $m$ with $f(m)_i = a$.
  Write $W^n (y^n given f(m))$ as a product over the positions.
  Summing over all $y^n$ with $y_i = b$ gives $W(b given a) product_(j != i) sum_(b') W(b' given f(m)_j) = W(b given a)$.
  Summing over $m$ gives $|M|^(-1) |{m : f(m)_i = a}| W(b given a) = p_i (a) W(b given a) = nu_(p_i) (a, b)$.
]

#theorem("Memoryless noise", lean: "Meat.BlockCode.condEntropy_snd_fst_codeMeasure")[
  $ H(Y^n given U) = sum_(i = 1)^n H_(nu_(p_i)) (pi_2 given pi_1). $
][
  By relabeling, $H(Y^n given U) = H(mu_c) - H(U) = H(mu_c) - log |M|$.
  If $mu_c (m, y^n) > 0$, then every factor $W(y_i given f(m)_i)$ is positive, and
  $ log mu_c (m, y^n) = -log |M| + sum_i log W(y_i given f(m)_i). $
  Multiply by $mu_c (m, y^n)$, sum over $(m, y^n)$ and exchange the two sums.
  This gives $H(mu_c) = log |M| - sum_i sum_(m, y^n) mu_c (m, y^n) log W(y_i given f(m)_i)$.
  The $i$-th inner sum depends only on $(f(m)_i, y_i)$, so by the one letter lemma it is $sum_(a, b) nu_(p_i) (a, b) log W(b given a)$.
  By the noise entropy lemma, this is $-H_(nu_(p_i)) (pi_2 given pi_1)$.
]

#theorem(
  "Information of a block",
  lean: ("Meat.BlockCode.mutualInfo_le_sum_inputMutualInfo", "Meat.BlockCode.mutualInfo_le_mul_capacity"),
)[
  $ I(U; Y^n) <= sum_(i = 1)^n I(p_i) <= n C(W). $
][
  By symmetry, $I(U; Y^n) = H(Y^n) - H(Y^n given U)$.
  By subadditivity, $H(Y^n) <= sum_i H(Y_i)$.
  By the one letter lemma, $H(Y_i) = H_(nu_(p_i)) (pi_2)$.
  With the memoryless noise theorem,
  $ I(U; Y^n) <= sum_i (H_(nu_(p_i)) (pi_2) - H_(nu_(p_i)) (pi_2 given pi_1)) = sum_i I(p_i). $
  Each $I(p_i)$ is at most $C(W)$.
]

This route does not use the Markov chain $U -> f(U) -> Y^n$.
The data processing step and the single-letter bound are both in the memoryless noise theorem.

#lemma("Fano step", lean: "Meat.BlockCode.condEntropy_fst_snd_codeMeasure_le")[
  $ H(U given Y^n) <= log 2 + overline(lambda) log |M|. $
][
  Apply the corollary of Fano's inequality to $U$, $Y^n$ and the decoder $g$.
  The error probability $mu_c (g(Y^n) != U)$ is $overline(lambda)$.
]

#theorem("Converse for one code", lean: "Meat.BlockCode.one_sub_mul_log_card_le")[
  $ (1 - overline(lambda)) log |M| <= n C(W) + log 2. $
][
  We have $log |M| = H(U) = I(U; Y^n) + H(U given Y^n) <= n C(W) + log 2 + overline(lambda) log |M|$.
]

#theorem("Weak converse", lean: "Meat.DMC.le_capacity_of_achievable")[][
  Suppose that $R > C(W)$, and let $delta := R - C(W) > 0$.
  Since $C(W) >= 0$, also $R > 0$.
  Let $epsilon := delta \/ (2 R)$.
  Then $epsilon R = delta \/ 2$ and $0 < epsilon < 1$.
  Achievability gives $N$ for this $epsilon$.
  Take $n >= N$ with $n > 2 log 2 \/ delta$, and a code with $M = [k]$, $k >= e^(n R)$ and $overline(lambda) <= epsilon$.
  Then $k >= 1$ and $log k >= n R$.
  By the converse for one code,
  $ (1 - epsilon) n R <= (1 - epsilon) log k <= (1 - overline(lambda)) log k <= n C(W) + log 2. $
  The left side is $n R - n delta \/ 2 = n C(W) + n delta \/ 2$.
  So $n delta <= 2 log 2$, which contradicts the choice of $n$.
]

== Channel coding theorem
#source("Meat.Channel.CodingTheorem")

#theorem("Channel coding theorem", lean: "Meat.DMC.closure_achievable_eq")[][
  _Inclusion $subset.eq$._
  By the converse, every achievable $R$ satisfies $R <= C(W)$.
  So the set of achievable $R >= 0$ is a subset of $[0, C(W)]$.
  This interval is closed, so it also contains the closure.

  _Inclusion $supset.eq$._
  By the converse section, $C(W) >= 0$.
  If $C(W) = 0$, the interval is ${0}$, and the rate $0$ is achievable with one message.
  If $C(W) > 0$, every $R in [0, C(W))$ is achievable by the achievability section.
  The closure of $[0, C(W))$ is $[0, C(W)]$.
]

== Multiple access channels
#source("Meat.Channel.MultipleAccess")

Two senders have independent messages.
The two senders use one receiver through a DMC $W$ from $A_1 times A_2$ to $B$.

#definition(
  "Multiple access code",
  lean: ("Meat.MACCode", "Meat.MACCode.errorProb", "Meat.MACCode.avgError"),
)[
  Let $n in NN$ and let $M_1$ and $M_2$ be finite sets.
  A multiple access code of length $n$ is a triple $(f_1, f_2, g)$ of maps $f_j : M_j -> A_j^n$ and $g : B^n -> M_1 times M_2$.
  For $m = (m_1, m_2)$ its error probability is
  $ lambda_m := sum_(y^n : g(y^n) != m) W^n (y^n given (f_1(m_1), f_2(m_2))), $
  where the input pair is read coordinatewise, and $overline(lambda) := (|M_1| |M_2|)^(-1) sum_m lambda_m$.
]

#definition("Achievable rate pair", lean: ("Meat.MAC.Achievable", "Meat.MAC.achievableRegion"))[
  A pair $(R_1, R_2)$ with $R_1, R_2 >= 0$ is achievable for $W$ if for every $epsilon > 0$ there exists $N$ such that for every $n >= N$ there exist $k_1, k_2 in NN$ with $k_j >= e^(n R_j)$ and a code of length $n$ with $M_j = [k_j]$ and $overline(lambda) <= epsilon$.
  The achievable region $cal(A)(W)$ is the set of achievable pairs.
]

#definition("Pentagon", lean: ("Meat.MAC.jointMeasure", "Meat.MAC.pentagon"))[
  For $p_1 in Delta(A_1)$ and $p_2 in Delta(A_2)$, let $(X_1, X_2, Y)$ have the law $p_1(x_1) p_2(x_2) W(y given x_1, x_2)$.
  The pentagon $cal(P)(p_1, p_2)$ is the set of $(R_1, R_2) in [0, infinity)^2$ with
  $ R_1 <= I(X_1; Y given X_2), quad R_2 <= I(X_2; Y given X_1), quad R_1 + R_2 <= I((X_1, X_2); Y). $
]

#definition("Capacity region", lean: "Meat.MAC.capacityRegion")[
  $ cal(C)(W) := overline(op("conv") union.big_(p_1, p_2) cal(P)(p_1, p_2)). $
]

== Multiple access achievability
#source("Meat.Channel.MultipleAccessAchievability")

This section proves the inclusion $cal(C)(W) subset.eq overline(cal(A)(W))$.
The proof is random coding with two independent codebooks and joint typicality decoding, followed by time sharing.
It reuses the point-to-point machinery: a multiple access code is a block code for the message pair, and each error event is a point-to-point error event for a suitable channel.
Here $[P]$ is $1$ if the statement $P$ is true and $0$ otherwise, and for $a in A_1^n$ and $b in A_2^n$ the pair sequence $(a, b) in (A_1 times A_2)^n$ is read coordinatewise.

#definition(
  "Codes for the message pair",
  lean: (
    "Meat.MACCode.toBlockCode",
    "Meat.MACCode.errorProb_toBlockCode",
    "Meat.MACCode.avgError_toBlockCode",
    "Meat.MACCode.typicalCode",
    "Meat.MACCode.toBlockCode_typicalCode",
  ),
)[
  A multiple access code $(f_1, f_2, g)$ is the block code for the channel $W$ with messages $M_1 times M_2$, encoder $(m_1, m_2) |-> (f_1 (m_1), f_2 (m_2))$ and decoder $g$.
  The two codes have the same error probabilities and the same average error probability.
  For codebooks $C_1 : M_1 -> A_1^n$ and $C_2 : M_2 -> A_2^n$, a set $J subset.eq (A_1 times A_2)^n times B^n$ and $m_0 in M_1 times M_2$, the typicality code is the multiple access code whose block code is the typicality code of the pair codebook $(C_1, C_2)$.
][
  The error probabilities have the same definition.
  For the average, $|M_1 times M_2| = |M_1| |M_2|$.
]

#definition(
  "Product input and side channels",
  lean: (
    "Meat.MAC.inputPMF",
    "Meat.MAC.inputPMF_apply",
    "Meat.MAC.iidProb_inputPMF",
    "Meat.MAC.sideChannel₁",
    "Meat.MAC.sideChannel₂",
    "Meat.MAC.blockProb_sideChannel₁",
    "Meat.MAC.blockProb_sideChannel₂",
  ),
)[
  For $p_1 in Delta(A_1)$ and $p_2 in Delta(A_2)$, the product input is $(p_1 times p_2)(a_1, a_2) := p_1 (a_1) p_2 (a_2)$, so $(p_1 times p_2)^n (a, b) = p_1^n (a) p_2^n (b)$.
  The first side channel $V_1$ goes from $A_1$ to $A_2 times B$ with $V_1 (a_2, y given a_1) := p_2 (a_2) W(y given a_1, a_2)$.
  It is the channel that sender 1 sees when the input of sender 2 is random and counts as part of the output.
  The second side channel $V_2$ from $A_2$ to $A_1 times B$ is $V_2 (a_1, y given a_2) := p_1 (a_1) W(y given a_1, a_2)$.
  For sequences, $V_1^n ((b, y) given a) = p_2^n (b) W^n (y given (a, b))$ and $V_2^n ((a, y) given b) = p_1^n (a) W^n (y given (a, b))$.
][
  In Lean, each one is a pair law of the point-to-point section.
  The identities for sequences are products of the identities for letters.
]

#proposition(
  "One joint law, three views",
  lean: (
    "Meat.MAC.jointPMF",
    "Meat.MAC.jointMeasure_eq_toMeasure",
    "Meat.MAC.jointPMF_eq_sideChannel₁",
    "Meat.MAC.jointPMF_apply",
    "Meat.MAC.jointPMF_inputPMF",
    "Meat.MAC.jointPMF_sideChannel₂",
    "Meat.MAC.iidProb_jointPMF_inputPMF",
    "Meat.MAC.iidProb_jointPMF_sideChannel₁",
    "Meat.MAC.iidProb_jointPMF_sideChannel₂",
    "Meat.MAC.isProbabilityMeasure_jointMeasure",
  ),
)[
  Let $p(a_1, a_2, y) := p_1 (a_1) p_2 (a_2) W(y given a_1, a_2)$ be the law of the pentagon definition.
  Its measure is a probability measure.
  The pair laws $p_(W, p_1 times p_2)$, $p_(V_1, p_1)$ and $p_(V_2, p_2)$ are $p$ with the coordinates regrouped as $((a_1, a_2), y)$, $(a_1, (a_2, y))$ and $(a_2, (a_1, y))$.
  So each of their $n$-fold laws at a regrouped triple of sequences $(a, b, y)$ is $p_1^n (a) p_2^n (b) W^n (y given (a, b))$.
][
  All laws are explicit products, and both sides agree at every point.
  A push-forward by an injective map takes the value of the original law at the preimage.
]

#proposition(
  "Information of the three views",
  lean: (
    "Meat.MAC.inputMutualInfo_inputPMF",
    "Meat.MAC.inputMutualInfo_sideChannel₁",
    "Meat.MAC.inputMutualInfo_sideChannel₂",
    "Meat.MAC.condMutualInfo_le_inputMutualInfo_sideChannel₁",
    "Meat.MAC.condMutualInfo_le_inputMutualInfo_sideChannel₂",
  ),
)[
  Let $(X_1, X_2, Y)$ have the law $p$.
  Then $I_W (p_1 times p_2) = I((X_1, X_2); Y)$, $I_(V_1) (p_1) = I(X_1; (X_2, Y))$ and $I_(V_2) (p_2) = I(X_2; (X_1, Y))$.
  Also
  $ I(X_1; Y given X_2) <= I_(V_1) (p_1), quad I(X_2; Y given X_1) <= I_(V_2) (p_2). $
][
  The identities follow from the regroupings, since mutual information is invariant under push-forward and injective relabeling.
  By the chain rule, $I(X_1; (Y, X_2)) = I(X_1; X_2) + I(X_1; Y given X_2)$, and $I(X_1; X_2) >= 0$.
  The second inequality is the same with the senders exchanged.
]

For the rest of this section fix $p_1$, $p_2$ and $epsilon$.

#definition(
  "Decoding set",
  lean: ("Meat.MAC.decodingSet", "Meat.MAC.mem_decodingSet", "Meat.MAC.tendsto_sum_iidProb_decodingSet"),
)[
  The decoding set $D_epsilon^((n))$ is the set of $((a, b), y)$ with
  $ ((a, b), y) in J_epsilon^((n)) (p_(W, p_1 times p_2)), quad (a, (b, y)) in J_epsilon^((n)) (p_(V_1, p_1)), quad (b, (a, y)) in J_epsilon^((n)) (p_(V_2, p_2)). $
  If $epsilon > 0$, then $p_(W, p_1 times p_2)^n (D_epsilon^((n))) -> 1$.
][
  Each of the three conditions has probability tending to $1$ by the joint asymptotic equipartition property, because the three pair laws are regroupings of one law.
  If the probabilities of two sets tend to $1$, so does the probability of their intersection, by the intersection lemma of the Shannon chapter.
]

#lemma(
  "Average error terms",
  lean: (
    "Meat.MAC.sum_sum_iidProb_mul_sum_ite_decodingSet",
    "Meat.MAC.sum_sum_mul_sum_decodingSet_le₁",
    "Meat.MAC.sum_sum_mul_sum_decodingSet_le₂",
    "Meat.MAC.sum_sum_mul_sum_decodingSet_le₃",
  ),
)[
  Let $D := D_epsilon^((n))$ and $T(x', x) := sum_y [(x', y) in D] W^n (y given x)$.
  The true pair is atypical with average probability
  $ sum_(a, b) p_1^n (a) p_2^n (b) sum_y [((a, b), y) in.not D] W^n (y given (a, b)) = 1 - p_(W, p_1 times p_2)^n (D). $
  A wrong first message, a wrong second message and two wrong messages are typical with average probability at most
  $ sum_(a, a', b) p_1^n (a) p_1^n (a') p_2^n (b) T((a', b), (a, b)) <= e^(-n (I_(V_1) (p_1) - 3 epsilon)), $
  $ sum_(a, b, b') p_1^n (a) p_2^n (b) p_2^n (b') T((a, b'), (a, b)) <= e^(-n (I_(V_2) (p_2) - 3 epsilon)), $
  $ sum_(a, a', b, b') p_1^n (a) p_1^n (a') p_2^n (b) p_2^n (b') T((a', b'), (a, b)) <= e^(-n (I_W (p_1 times p_2) - 3 epsilon)). $
][
  The first identity is the first identity of the lemma on error terms of random codewords, for the input law $p_1 times p_2$.
  For a wrong first message, membership in $D$ implies $(a', (b, y)) in J_epsilon^((n)) (p_(V_1, p_1))$.
  Sum over $b$ and $y$ together: $p_2^n (b) W^n (y given (a, b)) = V_1^n ((b, y) given a)$.
  So the sum is at most the left side of the second bound in the lemma on error terms of random codewords, for $V_1$ and $p_1$.
  A wrong second message is the same with $V_2$.
  For two wrong messages, group $(a, b)$ and $(a', b')$ into codewords of the product input, and use the same bound for $W$ and $p_1 times p_2$.
]

#theorem(
  "Random coding bound for two senders",
  lean: ("Meat.MAC.sum_errorProb_typicalCode_le", "Meat.MAC.exists_typicalCode_avgError_le"),
)[
  Draw $C_1$ and $C_2$ with the product weights of $p_1^n$ and $p_2^n$, and decode with $D_epsilon^((n))$.
  For every message pair $m$, the average of $lambda_m$ over the codebooks is at most
  $ beta := (1 - p_(W, p_1 times p_2)^n (D)) + (|M_1| - 1) e_1 + (|M_2| - 1) e_2 + (|M_1| - 1)(|M_2| - 1) e_3, $
  where $e_1$, $e_2$ and $e_3$ are the three exponential bounds of the lemma.
  Hence some codebooks have $overline(lambda) <= beta$.
][
  The union bound of the point-to-point section, applied to the code for the message pair, bounds $lambda_m$ by the atypicality of the true pair plus a sum over wrong pairs $m' != m$.
  Split the wrong pairs into three groups: only the first message wrong, only the second message wrong, and both wrong.
  In each term only the codewords $C_1 (m_1)$, $C_1 (m'_1)$, $C_2 (m_2)$ and $C_2 (m'_2)$ appear.
  Average first over $C_2$ and then over $C_1$ with the product weights lemmas, for one index or for two distinct indices.
  The four averages are the four terms of the lemma.
  A weighted average over codebooks of $sum_m lambda_m$ is at most $|M_1| |M_2| beta$, so some codebooks attain this bound.
]

#theorem("Achievability inside a pentagon", lean: "Meat.MAC.achievable_of_lt")[
  If $R_1 < I(X_1; Y given X_2)$, $R_2 < I(X_2; Y given X_1)$ and $R_1 + R_2 < I((X_1, X_2); Y)$, then $(R_1, R_2)$ is achievable.
][
  Let $eta$ be a quarter of the smallest of the three slacks.
  Take $k_j := ceil(e^(n R_j))$, so $k_j - 1 <= e^(n R_j)$.
  By the information of the three views, $e_1 <= e^(-n (I(X_1; Y given X_2) - 3 eta))$ and $e_2 <= e^(-n (I(X_2; Y given X_1) - 3 eta))$, and $e_3 = e^(-n (I((X_1, X_2); Y) - 3 eta))$.
  So each of the last three terms of $beta$ is at most $e^(-n eta)$.
  The first term tends to $0$ by the decoding set lemma.
  For large $n$, $beta$ is below any prescribed bound.
]

Time sharing concatenates two codes.

#definition(
  "Concatenation and relabeling",
  lean: ("Meat.MACCode.append", "Meat.MACCode.relabel"),
)[
  For codes $c$ of length $n$ and $c'$ of length $n'$, the concatenation $c c'$ of length $n + n'$ sends $((m_1, m'_1), (m_2, m'_2))$ by sending $(m_1, m_2)$ with $c$ and then $(m'_1, m'_2)$ with $c'$.
  It decodes the first $n$ outputs with $c$ and the last $n'$ outputs with $c'$.
  A relabeling by bijections $e_1 : M_1 -> M'_1$ and $e_2 : M_2 -> M'_2$ renames the messages.
]

#proposition(
  "Errors of concatenated codes",
  lean: (
    "Meat.MACCode.errorProb_ne_top",
    "Meat.MACCode.errorProb_relabel",
    "Meat.MACCode.avgError_relabel",
    "Meat.MACCode.sum_errorProb_toReal",
    "Meat.MACCode.avgError_ne_top",
    "Meat.MACCode.errorProb_append_le",
    "Meat.MACCode.avgError_append_le",
  ),
)[
  Error probabilities are finite.
  A relabeling has the same error probabilities at the renamed messages and the same average error probability.
  If all message sets are nonempty, then $sum_m lambda_m = |M_1| |M_2| overline(lambda)$ in $RR$, and $overline(lambda) < infinity$.
  The concatenation has $lambda_((m_1, m'_1), (m_2, m'_2)) <= lambda_((m_1, m_2)) + lambda'_((m'_1, m'_2))$ and $overline(lambda) <= overline(lambda)(c) + overline(lambda)(c')$.
][
  The channel is memoryless, so $W^(n + n') (y y' given x x') = W^n (y given x) W^(n') (y' given x')$.
  The concatenated decoder errs only if one of the two decoders errs.
  So the error indicator is at most $[g(y) "wrong"] + [g'(y') "wrong"]$.
  Sum over $y$ and $y'$, and use $sum_y W^n (y given x) = 1$.
  Averaging over the message quadruples gives the bound for $overline(lambda)$.
]

#theorem(
  "Time sharing",
  lean: (
    "Meat.MAC.Achievable.mono",
    "Meat.MAC.Achievable.max_zero",
    "Meat.MAC.mem_closure_achievableRegion",
    "Meat.MAC.Achievable.timeSharing",
    "Meat.MAC.convex_closure_achievableRegion",
  ),
)[
  Achievability is preserved by lowering the rates and by replacing each rate $R_j$ with $max(R_j, 0)$.
  If $R_1, R_2 >= 0$ and $(R_1 - delta, R_2 - delta)$ is achievable for every $delta > 0$, then $(R_1, R_2) in overline(cal(A)(W))$.
  If $(R_1, R_2)$ and $(R'_1, R'_2)$ are achievable, $a, b >= 0$, $a + b = 1$ and $delta > 0$, then $(a R_1 + b R'_1 - delta, a R_2 + b R'_2 - delta)$ is achievable.
  Hence $overline(cal(A)(W))$ is convex.
][
  Lower rates need fewer messages.
  A number of messages $k >= e^(n R)$ with $R < 0$ is still at least $1 = e^(n dot 0)$, by the lemma on clamped rates.
  For the closure, the clamped points $(max(R_1 - delta, 0), max(R_2 - delta, 0))$ are achievable and within $delta$ of $(R_1, R_2)$.
  For time sharing with $a, b > 0$, take $n_1 := floor(a n)$ and concatenate a code of length $n_1$ for the first pair with a code of length $n - n_1$ for the second pair, each with error at most $epsilon \/ 2$.
  Then $n_1 R_1 + (n - n_1) R'_1 >= n (a R_1 + b R'_1) - |R_1 - R'_1|$, which is at least $n (a R_1 + b R'_1 - delta)$ for large $n$.
  Relabel the product message sets to $[k_1 k'_1]$ and $[k_2 k'_2]$.
  If $a = 0$ or $b = 0$, lower the rates of one pair.
  For convexity, the convex combination of two achievable pairs is in $overline(cal(A)(W))$ by the two previous statements.
  The map $(x, y) |-> a x + b y$ is continuous, so the closure of a set with this property is convex.
]

#corollary(
  "Achievability of the capacity region",
  lean: (
    "Meat.MAC.pentagon_subset_closure_achievableRegion",
    "Meat.MAC.capacityRegion_subset_closure_achievableRegion",
  ),
)[
  Every pentagon is a subset of $overline(cal(A)(W))$, and $cal(C)(W) subset.eq overline(cal(A)(W))$.
][
  For a point of a pentagon and $delta > 0$, the point $(R_1 - delta, R_2 - delta)$ satisfies the three strict inequalities, so it is achievable.
  The closure statement of the time sharing theorem applies.
  The set $overline(cal(A)(W))$ is closed, convex and contains every pentagon, so it contains the closure of the convex hull of their union.
]

== Multiple access converse
#source("Meat.Channel.MultipleAccessConverse")

This section proves the inclusion $overline(cal(A)(W)) subset.eq cal(C)(W)$.
The proof uses Fano's inequality for each message, a single-letter bound for each rate and for the sum rate, and an averaging argument for pentagons.

#proposition(
  "Pentagon geometry",
  lean: (
    "Meat.MAC.inputPMF_map_fst",
    "Meat.MAC.inputPMF_map_snd",
    "Meat.MAC.inputPMF_map",
    "Meat.MAC.jointPMF_map_input",
    "Meat.MAC.mutualInfo_inputs_eq_zero",
    "Meat.MAC.condMutualInfo_nonneg₁",
    "Meat.MAC.condMutualInfo_nonneg₂",
    "Meat.MAC.mutualInfo_eq_add₁",
    "Meat.MAC.mutualInfo_eq_add₂",
    "Meat.MAC.condMutualInfo_le_mutualInfo₁",
    "Meat.MAC.condMutualInfo_le_mutualInfo₂",
    "Meat.MAC.mutualInfo_le_add",
  ),
)[
  The marginals of $p_1 times p_2$ are $p_1$ and $p_2$, and the push-forward of $p_1 times p_2$ by $f times g$ is $(f_* p_1) times (g_* p_2)$.
  The law of $(X_1, X_2)$ is $p_1 times p_2$, so $I(X_1; X_2) = 0$.
  Write $I_1 := I(X_1; Y given X_2)$, $I_2 := I(X_2; Y given X_1)$ and $I_3 := I((X_1, X_2); Y)$.
  Then $I_3 = I(X_2; Y) + I_1 = I(X_1; Y) + I_2$, and
  $ 0 <= I_1 <= I_3, quad 0 <= I_2 <= I_3, quad I_3 <= I_1 + I_2. $
][
  The identities are the chain rule.
  The inequalities $I_j <= I_3$ follow because mutual information is nonnegative.
  For the last one, $I(X_2; X_1) + I(X_2; Y given X_1) = I(X_2; Y) + I(X_2; X_1 given Y)$.
  Since $I(X_2; X_1) = 0$, this gives $I(X_2; Y) <= I_2$, so $I_3 <= I_1 + I_2$.
  Independence is used only here.
]

#proposition(
  "Exchanging the senders",
  lean: (
    "Meat.MAC.jointPMF_swap",
    "Meat.MAC.condMutualInfo_swap",
    "Meat.MACCode.swap",
    "Meat.MACCode.avgError_swap",
  ),
)[
  Let $W'(y given a_2, a_1) := W(y given a_1, a_2)$.
  The law for $W'$, $p_2$ and $p_1$ is the law for $W$, $p_1$ and $p_2$ with the inputs exchanged, so its $I_1$ is the $I_2$ of $W$.
  Exchanging the encoders and the decoder outputs of a code for $W$ gives a code for $W'$ with the same average error probability.
][
  The laws agree at every point.
  The error probability of the exchanged code at $(m_2, m_1)$ is the error probability of the original code at $(m_1, m_2)$.
]

#lemma("Noise of one letter", lean: "Meat.MAC.condMutualInfo_eq_condEntropy_sub")[
  Under the pair law $nu$ of $W$ and $p_1 times p_2$ on $(A_1 times A_2) times B$,
  $ I(X_1; Y given X_2) = H_nu (Y given X_2) - H_nu (Y given (X_1, X_2)). $
][
  This is the identity $I(X; Y given Z) = H(Y given Z) - H(Y given (X, Z))$ of the Shannon chapter, transported along the regrouping.
]

Now fix a code $c = (f_1, f_2, g)$ with nonempty message sets.
Under the law $mu_c$ of the point-to-point converse for the code of the message pair, the messages $U_1$ and $U_2$ are independent and uniform.

#definition(
  "Input laws of the senders",
  lean: (
    "Meat.MACCode.inputLaw₁",
    "Meat.MACCode.inputLaw₂",
    "Meat.MACCode.inputLaw₁_swap",
    "Meat.MACCode.inputLaw₂_swap",
    "Meat.MACCode.toBlockCode_inputLaw",
  ),
)[
  For $i in [n]$, $p_(1 i) in Delta(A_1)$ is the law of $f_1 (U_1)_i$ for uniform $U_1$, and $p_(2 i)$ is the law of $f_2 (U_2)_i$.
  The input law of the $i$-th letter of the code for the message pair is $p_(1 i) times p_(2 i)$.
  Exchanging the senders exchanges the two input laws.
][
  The uniform law on $M_1 times M_2$ is the product of the uniform laws.
  Push it forward by $(m_1, m_2) |-> (f_1 (m_1)_i, f_2 (m_2)_i)$.
]

In the next theorem, $I_j (i)$ is $I_j$ for the law of $W$, $p_(1 i)$ and $p_(2 i)$.

#theorem(
  "Converse for one code",
  lean: (
    "Meat.MACCode.one_sub_mul_log_card_le_sum_mutualInfo",
    "Meat.MACCode.one_sub_mul_log_card_le_sum_condMutualInfo₁",
    "Meat.MACCode.one_sub_mul_log_card_le_sum_condMutualInfo₂",
  ),
)[
  $ (1 - overline(lambda)) log (|M_1| |M_2|) <= sum_(i = 1)^n I_3 (i) + log 2, $
  $ (1 - overline(lambda)) log |M_1| <= sum_(i = 1)^n I_1 (i) + log 2, quad (1 - overline(lambda)) log |M_2| <= sum_(i = 1)^n I_2 (i) + log 2. $
][
  The first bound is the converse for one code of the point-to-point section, applied to the code for the message pair, with $sum_i I_W (p_(1 i) times p_(2 i))$ in place of $n C(W)$.

  For the second bound, let $U = (U_1, U_2)$ and $Y^n$ be the output.
  Since $H(U) = log |M_1| + log |M_2|$ and $H(U_2) <= log |M_2|$,
  $ log |M_1| <= H(U) - H(U_2) = H(Y^n given U_2) - H(Y^n given U) + H(U_1 given (Y^n, U_2)). $
  The identity holds because $H(U_1, Y^n, U_2) = H(Y^n, U)$.
  Conditioning reduces entropy, so $H(U_1 given (Y^n, U_2)) <= H(U_1 given Y^n)$.
  Fano's inequality with the decoder $y |-> g(y)_1$ gives $H(U_1 given Y^n) <= log 2 + overline(lambda) log |M_1|$, since this decoder errs only when $g$ errs.
  By the memoryless noise theorem, $H(Y^n given U) = sum_i H_(nu_i) (Y given (X_1, X_2))$.
  By conditional subadditivity, $H(Y^n given U_2) <= sum_i H(Y_i given U_2)$.
  The input $X_(2 i) = f_2 (U_2)_i$ is a function of $U_2$, so $H(Y_i given U_2) <= H(Y_i given X_(2 i)) = H_(nu_i) (Y given X_2)$ by the one letter lemma.
  By the noise of one letter, the difference of the two sums is $sum_i I_1 (i)$.
  The third bound is the second bound for the code with the senders exchanged.
]

#lemma("Averages of pentagons", lean: "Meat.MAC.mem_convexHull_of_sum_le")[
  Let $iota$ be finite and nonempty with $N := |iota|$.
  For each $i$, let $a_i <= c_i$, $b_i <= c_i$ and $c_i <= a_i + b_i$, and let $S_i$ contain the pentagon ${R >= 0 : R_1 <= a_i, R_2 <= b_i, R_1 + R_2 <= c_i}$.
  If $x, y >= 0$, $N x <= sum_i a_i$, $N y <= sum_i b_i$ and $N (x + y) <= sum_i c_i$, then $(x, y) in op("conv") union.big_i S_i$.
][
  Let $overline(a)$, $overline(b)$ and $overline(c)$ be the averages.
  Let $t := max(x, overline(c) - overline(b))$, so $overline(c) - overline(b) <= t <= overline(a)$, $x <= t$ and $y <= overline(c) - t$.
  Write $t = theta overline(a) + (1 - theta)(overline(c) - overline(b))$ with $theta in [0, 1]$.
  Let $u_i := theta a_i + (1 - theta)(c_i - b_i)$, a point between $c_i - b_i$ and $a_i$, so $(u_i, c_i - u_i)$ is on the slanted edge of the $i$-th pentagon.
  The average of $u_i$ is $t$.
  Let $s := x \/ t$ and $r := y \/ (overline(c) - t)$, both in $[0, 1]$, with $s t = x$ and $r (overline(c) - t) = y$.
  The points $(s u_i, r (c_i - u_i))$ lie in the pentagons, and their average is $(x, y)$.
]

#theorem("Weak converse for two senders", lean: "Meat.MAC.mem_capacityRegion_of_mem_achievableRegion")[
  Every point of $cal(A)(W)$ lies in $cal(C)(W)$.
][
  Let $(R_1, R_2) in cal(A)(W)$ and $eta > 0$.
  Choose $epsilon <= 1 \/ 2$ with $epsilon (R_1 + R_2 + 1) <= eta \/ 2$, and $n$ large with $log 2 \/ n < eta \/ 2$.
  Take a code of length $n$ with $k_j >= e^(n R_j)$ and $overline(lambda) <= epsilon$.
  By the converse for one code, $x_0 := (1 - epsilon) R_1 - log 2 \/ n$ and $y_0 := (1 - epsilon) R_2 - log 2 \/ n$ satisfy
  $ n x_0 <= sum_i I_1 (i), quad n y_0 <= sum_i I_2 (i), quad n (x_0 + y_0) <= sum_i I_3 (i). $
  By the pentagon geometry, the same holds for $x := max(x_0, 0)$ and $y := max(y_0, 0)$.
  The lemma on averages of pentagons puts $(x, y)$ in the convex hull of the union of the pentagons of the letters.
  The distance from $(R_1, R_2)$ to $(x, y)$ is at most $max(epsilon R_1, epsilon R_2) + log 2 \/ n < eta$.
  So $(R_1, R_2)$ is in the closure of the convex hull.
]

== Multiple access theorem
#source("Meat.Channel.MultipleAccessTheorem")

#theorem("Multiple access capacity, Ahlswede and Liao", lean: "Meat.MAC.closure_achievableRegion_eq")[][
  _Inclusion $subset.eq$._
  By the weak converse, $cal(A)(W) subset.eq cal(C)(W)$.
  The set $cal(C)(W)$ is closed, so it also contains the closure.

  _Inclusion $supset.eq$._
  This is the achievability of the capacity region.
]

== Broadcast channels
#source("Meat.Channel.Broadcast")

One sender sends private messages to two receivers through a DMC $W$ from $A$ to $B_1 times B_2$.

#definition(
  "Broadcast code",
  lean: ("Meat.BCCode", "Meat.BCCode.errorProb", "Meat.BCCode.avgError"),
)[
  Let $n in NN$ and let $M_1$ and $M_2$ be finite sets.
  A broadcast code of length $n$ is a triple $(f, g_1, g_2)$ of maps $f : M_1 times M_2 -> A^n$ and $g_j : B_j^n -> M_j$.
  For $m = (m_1, m_2)$ its error probability is
  $ lambda_m := sum_(y^n in (B_1 times B_2)^n : (g_1(y_1^n), g_2(y_2^n)) != m) W^n (y^n given f(m)), $
  where $y_j^n$ is the $j$-th component sequence of $y^n$, and $overline(lambda) := (|M_1| |M_2|)^(-1) sum_m lambda_m$.
]

#definition("Achievable rate pair", lean: ("Meat.BC.Achievable", "Meat.BC.achievableRegion"))[
  Achievability of $(R_1, R_2)$ and the achievable region $cal(A)(W)$ are defined as for the multiple access channel, with broadcast codes in place of multiple access codes.
]

#definition(
  "Superposition region",
  lean: ("Meat.BC.jointMeasure", "Meat.BC.superpositionRegion"),
)[
  Let $V$ be a finite set, $p_U in Delta(V)$ and $p_X : V -> Delta(A)$.
  Let $(U, X, Y_1, Y_2)$ have the law $p_U(u) p_X (x given u) W(y_1, y_2 given x)$.
  The superposition region $cal(S)(p_U, p_X)$ is the set of $(R_1, R_2) in [0, infinity)^2$ with
  $ R_1 <= I(X; Y_1 given U), quad R_2 <= I(U; Y_2), quad R_1 + R_2 <= I(X; Y_1). $
]

By construction, $U -> X -> (Y_1, Y_2)$ is a Markov chain.

== Broadcast achievability
#source("Meat.Channel.BroadcastAchievability")

This section proves the superposition inner bound of Cover and Bergmans.
The proof is superposition coding with typicality decoding.
Receiver 2 decodes only $m_2$.
Receiver 1 decodes the pair $(m_1, m_2)$, but only its $m_1$ needs to be correct.
In this section, $W$ is a broadcast channel from $A$ to $B_1 times B_2$, and all sets are finite.

#lemma(
  "Block probabilities",
  lean: (
    "Meat.DMC.toReal_blockProb",
    "Meat.DMC.toReal_blockProb_bind",
    "Meat.DMC.toReal_blockProb_map",
    "Meat.DMC.sum_blockProb_mul_comp",
  ),
)[
  For a DMC $W$ from $A$ to $B$, the real value of $W^n (y given x)$ is $product_i W(y_i given x_i)$.
  For a DMC $kappa$ from $V$ to $A$, the composite channel $u |-> sum_a kappa(a given u) W(dot given a)$ has
  $ W'^n (y given u) = sum_x kappa^n (x given u) W^n (y given x). $
  For a map $g : B -> B'$, the channel $W_g := g_* W$ has $W_g^n (y' given x) = sum_(y : g compose y = y') W^n (y given x)$.
  So $sum_y W^n (y given x) F(g compose y) = sum_(y') W_g^n (y' given x) F(y')$.
][
  Each statement is a product over the positions of a statement for one letter.
  Distributivity exchanges the product of sums and the sum of products.
  The last identity groups the sequences $y$ by the value of $g compose y$.
]

#lemma("Averages with a pair law", lean: "Meat.DMC.sum_iidProb_jointPMF_mul")[
  For $kappa$ from $V$ to $A$ and $q in Delta(V)$, a sum over $w = (u, x) in (V times A)^n$ splits as
  $ sum_w p_(kappa, q)^n (w) F(u, x) = sum_u q^n (u) sum_x kappa^n (x given u) F(u, x). $
][
  This follows from $p_(kappa, q)^n (u, x) = q^n (u) kappa^n (x given u)$ and from the bijection between $(V times A)^n$ and $V^n times A^n$.
]

#lemma(
  "Broadcast error probabilities",
  lean: ("Meat.BCCode.errorProb_ne_top", "Meat.BCCode.errorProb_toReal_le", "Meat.BCCode.avgError_le_ofReal"),
)[
  Let $W_1$ and $W_2$ be the two marginal channels of $W$.
  For a broadcast code $(f, g_1, g_2)$, $lambda_m$ is finite, and
  $ lambda_m <= sum_(y_1 : g_1 (y_1) != m_1) W_1^n (y_1 given f(m)) + sum_(y_2 : g_2 (y_2) != m_2) W_2^n (y_2 given f(m)). $
  If $M_1$ and $M_2$ are nonempty and $sum_m lambda_m <= |M_1| |M_2| delta$ in $RR$, then $overline(lambda) <= delta$.
][
  An error means that one of the two decoders is wrong.
  The sum over $y = (y_1, y_2)$ of a function of $y_j$ is a sum over $y_j$ with the marginal channel $W_j$, by the lemma on block probabilities.
  The last statement is the same as for block codes.
]

#definition(
  "Superposition laws",
  lean: (
    "Meat.BC.jointPMF",
    "Meat.BC.jointMeasure_eq_toMeasure",
    "Meat.BC.channel₁",
    "Meat.BC.channel₂",
    "Meat.BC.cloudChannel₁",
    "Meat.BC.cloudChannel₂",
    "Meat.BC.law₁",
  ),
)[
  Let $p_U in Delta(V)$ and $p_X : V -> Delta(A)$.
  The law $p_U (u) p_X (x given u) W(y_1, y_2 given x)$ is the law in the definition of the superposition region.
  The channels $W_1$ and $W_2$ are the marginal channels of $W$.
  The cloud channels $W'_j (y given u) := sum_x p_X (x given u) W_j (y given x)$ are the channels from $U$ to $Y_j$.
  Receiver 1 uses the law $p_1$ of $((U, X), Y_1)$:
  $ p_1 ((u, x), y_1) := p_U (u) p_X (x given u) W_1 (y_1 given x). $
]

#lemma(
  "Marginals of the superposition laws",
  lean: (
    "Meat.BC.law₁_eq_map",
    "Meat.BC.jointPMF_cloudChannel₂",
    "Meat.BC.law₁_map_fst",
    "Meat.BC.law₁_map_cloud",
    "Meat.BC.law₁_map_cloud_output",
  ),
)[
  The law $p_1$ is the push-forward of the joint law by $(u, x, y_1, y_2) |-> ((u, x), y_1)$.
  The law of $(U, Y_2)$ is $p_U (u) W'_2 (y given u)$.
  The marginals of $p_1$ on $(U, X)$, on $U$ and on $(U, Y_1)$ are $p_U (u) p_X (x given u)$, $p_U$ and $p_U (u) W'_1 (y given u)$.
][
  Each side is a nested bind of $p_U$, $p_X$ and $W$, followed by a map.
  A map is a bind with a point mass, and binds are associative.
  So both sides reduce to the same nested bind.
]

#lemma(
  "Rates of the superposition region",
  lean: ("Meat.BC.mutualInfo_cloud_eq", "Meat.BC.condMutualInfo_eq_law₁", "Meat.BC.mutualInfo_eq_law₁"),
)[
  $I(U; Y_2)$ is the information $I_(W'_2) (p_U)$ of the cloud channel.
  $I(X; Y_1 given U)$ and $I(X; Y_1)$ are the same quantities computed under $p_1$.
][
  Apply the lemma on information under a push-forward to the push-forwards in the marginals lemma.
]

#definition(
  "Superposition code",
  lean: ("Meat.BC.superpositionCode", "Meat.BC.errorProb_superpositionCode_toReal_le"),
)[
  Let $C_U : M_2 -> V^n$ and $C_X : M_1 times M_2 -> A^n$ be codebooks, and let $J_1$ and $J_2$ be typicality sets.
  The encoder sends $C_X (m_1, m_2)$.
  Receiver 2 is the typicality decoder for $C_U$ and $J_2$.
  Receiver 1 is the typicality decoder for $m |-> (C_U (m_2), C_X (m))$ and $J_1$, followed by the first coordinate.
  Write $w(m) := (C_U (m_2), C_X (m))$.
  For every message $m$,
  $ lambda_m <= sum_(y) [(w(m), y) in.not J_1] W_1^n (y given C_X (m)) + sum_(m' : m'_1 != m_1) sum_y [(w(m'), y) in J_1] W_1^n (y given C_X (m)) + lambda^((2))_m, $
  where $lambda^((2))_m$ is the error of receiver 2 at $m$, with $W_2$.
][
  Apply the lemma on broadcast error probabilities.
  Bound the error of receiver 1 by the typicality decoder lemma with $pi(m) = m_1$.
]

#definition(
  "Random superposition codebook",
  lean: (
    "Meat.BC.codebookWeight",
    "Meat.BC.codebookWeight_nonneg",
    "Meat.BC.sum_codebookWeight",
    "Meat.BC.sum_codebookWeight_mul_apply",
    "Meat.BC.sum_codebookWeight_mul_apply_mul_apply",
  ),
)[
  The weight of $(C_U, C_X)$ is
  $ omega(C_U, C_X) := product_(m_2) p_U^n (C_U (m_2)) product_m p_X^n (C_X (m) given C_U (m_2)). $
  So the cloud centers are independent with law $p_U^n$.
  Given the cloud centers, the satellites are independent, and $C_X (m)$ has law $p_X^n (dot given C_U (m_2))$.
  The weights are nonnegative and sum to $1$.
  For fixed $C_U$, the average over $C_X$ of a function of $C_X (m)$ is the average with $p_X^n (dot given C_U (m_2))$.
  For $m' != m$, the average of a product of a function of $C_X (m')$ and a function of $C_X (m)$ is the product of the averages.
][
  For fixed $C_U$, apply the product weights lemma with the weights $p_X^n (dot given C_U (m_2))$, one for each $m$.
  Each of these weights sums to $1$ by the lemma on real error probabilities.
  Then the product weights lemma handles the cloud centers.
]

For the rest of this section, fix $epsilon in RR$.
Let $J_1 := T_epsilon^((n)) (p_1)$ and $J_2 := J_epsilon^((n)) (p_(W'_2, p_U))$.
Let $I_1 := I(X; Y_1 given U)$, $I_2 := I(U; Y_2)$ and $I_3 := I(X; Y_1)$.
All averages are with the weight $omega$.

#lemma(
  "Average error terms",
  lean: (
    "Meat.BC.sum_codebookWeight_mul_miss",
    "Meat.BC.sum_codebookWeight_mul_cloud_error",
    "Meat.BC.sum_codebookWeight_mul_same_cloud",
    "Meat.BC.sum_codebookWeight_mul_other_cloud",
  ),
)[
  The average of the first term in the bound of the superposition code is $1 - p_1^n (J_1)$.
  The average of $lambda^((2))_m$ is at most $(1 - p_(W'_2, p_U)^n (J_2)) + (|M_2| - 1) e^(-n (I_2 - 3 epsilon))$.
  Let $m'_1 != m_1$.
  If $m'_2 = m_2$, the average of the term for $m'$ is at most $e^(-n (I_1 - 4 epsilon))$.
  If $m'_2 != m_2$, it is at most $e^(-n (I_3 - 3 epsilon))$.
][
  _First term._
  It depends on $(C_U (m_2), C_X (m))$, whose law is $p_U^n (u) p_X^n (x given u)$.
  So its average is $sum_(u, x) p_U^n (u) p_X^n (x given u) sum_y [((u, x), y) in.not J_1] W_1^n (y given x) = 1 - p_1^n (J_1)$.

  _Receiver 2._
  The decoder depends only on $C_U$.
  For fixed $C_U$, the average over $C_X (m)$ replaces $W_2^n (y given C_X (m))$ by $W'^n_2 (y given C_U (m_2))$.
  So the average is the average error of the point-to-point typicality code for the cloud channel $W'_2$ with the codebook $C_U$.
  Apply the random coding bound of the point-to-point case.

  _Same cloud._
  Then $m' != m$, and $C_X (m')$ and $C_X (m)$ are independent given $u := C_U (m_2)$.
  The average of $W_1^n (y given C_X (m))$ given $u$ is $W'^n_1 (y given u)$.
  So the average of the term is
  $ sum_((u, x, y) in J_1) p_U^n (u) p_X^n (x given u) W'^n_1 (y given u). $
  By the marginals lemma, each term is $p_(U X)^n (u, x) p_(U Y)^n (u, y) \/ p_U^n (u)$ for the marginals of $p_1$, also when $p_U^n (u) = 0$.
  Apply the same cloud bound.

  _Other cloud._
  The two cloud centers are independent, so the average is
  $ sum_y (sum_((u, x) : ((u, x), y) in J_1) p_U^n (u) p_X^n (x given u)) (sum_(u, x) p_U^n (u) p_X^n (x given u) W_1^n (y given x)). $
  The second factor is the marginal $p_(1, Y)^n (y)$ of $p_1$.
  So the average is $sum_((w, y) in J_1) p_(U X)^n (w) p_Y^n (y)$.
  Apply the other cloud bound.
]

#theorem(
  "Superposition coding bound",
  lean: ("Meat.BC.sum_errorProb_superpositionCode_le", "Meat.BC.exists_superpositionCode_avgError_le"),
)[
  For every message $m$, the average of $lambda_m$ is at most
  $ beta := (1 - p_1^n (J_1)) + (|M_1| - 1) e^(-n (I_1 - 4 epsilon)) + (|M_1| - 1) (|M_2| - 1) e^(-n (I_3 - 3 epsilon)) $
  $ + (1 - p_(W'_2, p_U)^n (J_2)) + (|M_2| - 1) e^(-n (I_2 - 3 epsilon)). $
  So some superposition code has $overline(lambda) <= beta$.
][
  Average the bound of the superposition code.
  There are $|M_1| - 1$ messages $m'$ with $m'_1 != m_1$ and $m'_2 = m_2$.
  There are $(|M_1| - 1) (|M_2| - 1)$ messages $m'$ with $m'_1 != m_1$ and $m'_2 != m_2$.
  Apply the lemma on average error terms.
  The weighted average of $sum_m lambda_m$ is at most $|M_1| |M_2| beta$.
  By the weighted average lemma, some codebook has $sum_m lambda_m <= |M_1| |M_2| beta$.
]

#theorem("Superposition achievability", lean: "Meat.BC.achievable_of_lt")[
  Let $R_1 < I_1$, $R_2 < I_2$ and $R_1 + R_2 < I_3$.
  Then the pair $(max(R_1, 0), max(R_2, 0))$ is achievable for $W$.
][
  Let $epsilon > 0$, and choose $delta$ with $0 < delta < epsilon$.
  Let $eta$ be one fifth of the smallest of the three gaps $I_1 - R_1$, $I_2 - R_2$ and $I_3 - R_1 - R_2$.
  Then the exponents $R_1 - I_1 + 4 eta$, $R_2 - I_2 + 3 eta$ and $R_1 + R_2 - I_3 + 3 eta$ are negative.
  By the superposition AEP and the joint AEP, $1 - p_1^n (J_1) -> 0$ and $1 - p_(W'_2, p_U)^n (J_2) -> 0$.
  Take $N$ such that these two terms and the three exponentials $e^(n (dots))$ sum to less than $delta$ for $n >= N$.
  Let $k_j := ceil(e^(n R_j))$.
  Then $k_j >= 1$, $k_j - 1 <= e^(n R_j)$, and $k_j >= e^(n max(R_j, 0))$ by the lemma on clamped rates.
  The superposition coding bound with typicality parameter $eta$ gives a code with $overline(lambda) < delta$.
]

The maximum handles negative rates.
If $R_1 <= 0$, then $k_1 = 1$, and receiver 1 never errs.
This is needed on the boundary: if $I_1 = 0$, only the rate $R_1 = 0$ is in the region.

#theorem(
  "Superposition inner bound, Cover and Bergmans",
  lean: "Meat.BC.superpositionRegion_subset",
)[][
  Let $(R_1, R_2) in cal(S)(p_U, p_X)$, and let $t > 0$.
  The pair $(R_1 - t, R_2 - t)$ satisfies the three strict inequalities.
  So $(max(R_1 - t, 0), max(R_2 - t, 0))$ is achievable, and it is in $cal(A)(W)$.
  As $t -> 0$, this pair tends to $(R_1, R_2)$, because $R_1, R_2 >= 0$.
  So $(R_1, R_2)$ is in the closure of $cal(A)(W)$.
]

The third inequality of the region bounds $R_1 + R_2$ by $I(X; Y_1)$, not by $I((U, X); Y_1)$.
The other cloud bound gives this directly.
The two forms are equal, because $U -> X -> Y_1$ is a Markov chain.

If $Y_2$ is a degraded version of $Y_1$, the union of these regions over all $(p_U, p_X)$ is equal to the capacity region.
For the general broadcast channel, the capacity region is an open problem.

== Feedback
#source("Meat.Channel.Feedback")

With feedback, the encoder sees the past outputs of the channel before it chooses the next input.
This section proves that feedback does not increase the capacity of a DMC.
The converse uses the interactive code measure of the chapter on open problems.

#definition(
  "Feedback code",
  lean: (
    "Meat.FeedbackCode",
    "Meat.FeedbackCode.errorProb",
    "Meat.FeedbackCode.avgError",
    "Meat.FeedbackCode.ofBlockCode",
    "Meat.FeedbackCode.errorProb_ofBlockCode",
    "Meat.FeedbackCode.avgError_ofBlockCode",
  ),
)[
  A feedback code of length $n$ is a pair $(f, g)$ of encoders $f_i : M times B^(i - 1) -> A$ for $i in [n]$ and a decoder $g : B^n -> M$.
  The law of the outputs for the message $m$ is
  $ P(y^n given m) = product_(i = 1)^n W(y_i given f_i (m, y^(i - 1))). $
  The error probability $lambda_m$ is the probability that $g(y^n) != m$, and $overline(lambda)$ is the average over $m$.
  A block code is a feedback code that ignores the past outputs, with the same error probabilities.
]

#definition("Achievable rate with feedback", lean: ("Meat.DMC.FeedbackAchievable", "Meat.DMC.Achievable.feedback"))[
  A rate $R$ is achievable with feedback if it is achievable as in the point-to-point section, with feedback codes in place of block codes.
  Every achievable rate is achievable with feedback.
]

#lemma(
  "Converse for one feedback code",
  lean: ("Meat.FeedbackCode.measureReal_dec_ne", "Meat.FeedbackCode.one_sub_mul_log_card_le"),
)[
  For a feedback code with nonempty message set,
  $ (1 - overline(lambda)) log |M| <= n C(W) + log 2. $
][
  The average error is the measure of the error event under the interactive code measure.
  By the sum-rate converse for interactive codes, $(1 - overline(lambda)) log |M| <= sum_i I_(p_i)(X; Y) + log 2$, where $p_i$ is the law of the input at time $i$.
  The key step is $H(Y_i given M, Y^(i - 1)) = H(Y_i given X_i)$: given the message and the past, the law of $Y_i$ is $W(dot given X_i)$.
  Each term is $I_W (p_i) <= C(W)$.
]

#theorem(
  "Feedback does not increase capacity, Shannon",
  lean: ("Meat.DMC.le_capacity_of_feedbackAchievable", "Meat.DMC.closure_feedbackAchievable_eq"),
)[
  Every rate achievable with feedback is at most $C(W)$.
  If $A$ is nonempty, the closure of the set of rates $R >= 0$ achievable with feedback is $[0, C(W)]$.
][
  The first claim follows from the converse for one feedback code, as in the weak converse without feedback.
  For the second claim, the set is contained in $[0, C(W)]$, which is closed.
  It contains the set of rates achievable without feedback, whose closure is $[0, C(W)]$ by the channel coding theorem.
]

Feedback can still help in other ways.
It can make coding simpler, it can improve the error exponent, and it can enlarge the capacity region of a multiple access channel.

== Wiretap channels
#source("Meat.Channel.Wiretap")

A sender sends a message to a legitimate receiver over a DMC $W$ from $A$ to $B times E$.
The legitimate receiver sees $Y in B$, and an eavesdropper sees $Z in E$.
The message must stay secret from the eavesdropper.
The encoder may use private randomness.

#definition(
  "Wiretap code",
  lean: (
    "Meat.WiretapCode",
    "Meat.WiretapCode.errorProb",
    "Meat.WiretapCode.avgError",
    "Meat.WiretapCode.toFn",
    "Meat.WiretapCode.leakage",
  ),
)[
  A wiretap code of length $n$ is a pair $(f, g)$ of an encoder $f : M times L -> A^n$ and a decoder $g : B^n -> M$.
  The set $L$ holds the private randomness of the encoder.
  For $(m, l)$, the error probability is the probability under $W^n (dot given f(m, l))$ that $g(y^n) != m$, and $overline(lambda)$ is its average over $M times L$.
  Let $(U, V)$ be uniform on $M times L$, and let the outputs have law $W^n (dot given f(U, V))$.
  The leakage of the code is $I(U; Z^n)$.
]

#definition("Achievable secrecy rate", lean: "Meat.Wiretap.Achievable")[
  A rate $R$ is achievable if for every $epsilon > 0$ there exists $N$ such that for every $n >= N$ there are $k >= e^(n R)$, $l >= 1$ and a wiretap code of length $n$ with $M = [k]$ and $L = [l]$, $overline(lambda) <= epsilon$ and leakage at most $n epsilon$.
]

This is weak secrecy: the leakage per letter goes to $0$.

#definition(
  "Secrecy capacities",
  lean: (
    "Meat.Wiretap.degraded",
    "Meat.Wiretap.secrecyRate",
    "Meat.Wiretap.secrecyCapacity",
    "Meat.Wiretap.ckMeasure",
    "Meat.Wiretap.ckCapacity",
  ),
)[
  The channel is physically degraded if $W(y, z given x) = W_1 (y given x) D(z given y)$ for DMCs $W_1$ from $A$ to $B$ and $D$ from $B$ to $E$.
  For $p in Delta(A)$, let $(X, Y, Z)$ have the law $p(x) W(y, z given x)$.
  The secrecy rate of $p$ is $I(X; Y) - I(X; Z)$, and Wyner's secrecy capacity is $C_s (W) := sup_p (I(X; Y) - I(X; Z))$.
  The Csiszár-Körner capacity is the supremum of $I(V; Y) - I(V; Z)$ over all $k in NN$ and laws $q(v, x)$ on $[k] times A$, where $(V, X, Y, Z)$ has the law $q(v, x) W(y, z given x)$.
]

#theorem("Secrecy capacity, Csiszár and Körner")[
  For every wiretap channel, the closure of the set of achievable rates $R >= 0$ is $[0, C_"CK"(W)]$.
][
  Achievability uses a random codebook with $e^(n (I(V; Y) - I(V; Z)))$ bins, each with $e^(n I(V; Z))$ codewords drawn from $p_V$, and a channel prefix $p(x given v)$.
  The private randomness picks the codeword in the bin, and this confuses the eavesdropper.
  The converse uses the Csiszár sum identity, with $V_i := (M, Y^(i - 1), Z_(i + 1)^n)$.
  This theorem is not in Lean.
]

#lemma(
  "Converse for one wiretap code",
  lean: ("Meat.WiretapCode.measureReal_dec_ne", "Meat.WiretapCode.entropy_message", "Meat.WiretapCode.one_sub_mul_log_card_le"),
)[
  Let $p_i$ be the law of the input at time $i$ under the code.
  Then
  $ (1 - overline(lambda)) log |M| <= I(U; Z^n) + sum_(i = 1)^n I_(p_i)(X; Y given Z) + log 2. $
][
  The average error is the measure of the error event, and $H(U) = log |M|$.
  By Fano's inequality, $log |M| <= I(U; Y^n) + log 2 + overline(lambda) log |M|$.
  Next, $I(U; Y^n) <= I(U; Y^n, Z^n) = I(U; Z^n) + I(U; Y^n given Z^n)$.
  Write $T := (U, V)$.
  Then $I(U; Y^n given Z^n) = H(Y^n given Z^n) - H(Y^n given U, Z^n) <= H(Y^n given Z^n) - H(Y^n given T, Z^n)$.
  By subadditivity, $H(Y^n given Z^n) <= sum_i H(Y_i given Z_i)$.
  By the chain rule, $H(Y^n given T, Z^n) = H(Y^n, Z^n given T) - H(Z^n given T)$.
  The first term is $sum_i H(Y_i, Z_i given X_i)$, because the code measure is memoryless given $T$.
  The second term is at most $sum_i H(Z_i given X_i)$, because $X_i$ is a function of $T$.
  So $I(U; Y^n given Z^n) <= sum_i (H(Y_i given Z_i) - H(Y_i given X_i, Z_i)) = sum_i I(X_i; Y_i given Z_i)$.
]

#lemma(
  "Degraded channels",
  lean: (
    "Meat.Wiretap.jointPMF_degraded_map",
    "Meat.Wiretap.condEntropy_degraded",
    "Meat.Wiretap.condMutualInfo_degraded",
    "Meat.Wiretap.secrecyRate_le_log_card",
    "Meat.Wiretap.secrecyRate_le_secrecyCapacity",
  ),
)[
  For a physically degraded channel, $X -> Y -> Z$ is a Markov chain, and
  $ I(X; Y given Z) = I(X; Y) - I(X; Z). $
  The secrecy rate is at most $log |B|$, so it is at most $C_s (W)$.
][
  The law of $(X, Y)$ is $p(x) W_1 (y given x)$, and given $(X, Y)$ the law of $Z$ is $D(dot given Y)$.
  By the kernel lemma, $H(Z given X, Y) = H(Z given Y)$, so $I(X; Z given Y) = 0$.
  Then $I(X; Y) = I(X; Y, Z) = I(X; Z) + I(X; Y given Z)$ by the chain rule.
  The bound holds because $I(X; Y) <= H(Y) <= log |B|$ and $I(X; Z) >= 0$.
]

#theorem("Converse for the degraded wiretap channel, Wyner", lean: "Meat.Wiretap.le_secrecyCapacity_of_achievable")[
  For a physically degraded channel, every achievable rate is at most $C_s (W)$.
][
  The secrecy capacity is nonnegative, because the secrecy rate of a degraded channel is a conditional mutual information.
  Suppose $R > C_s$ and let $delta := R - C_s$ and $epsilon := delta \/ (2 (R + 1))$.
  Take a code with $k >= e^(n R)$, $overline(lambda) <= epsilon$ and leakage at most $n epsilon$.
  By the converse for one code and the lemma on degraded channels, $(1 - epsilon) log k <= n epsilon + n C_s + log 2$.
  Since $(1 - epsilon) R - epsilon = C_s + delta \/ 2$, this gives $n delta \/ 2 <= log 2$, which fails for large $n$.
]

#theorem("Achievability for the degraded wiretap channel, Wyner")[
  For a physically degraded channel, every $R < C_s (W)$ is achievable, so the closure of the achievable rates is $[0, C_s (W)]$.
][
  Wiretap coding: random binning with $e^(n R)$ bins of $e^(n I(X; Z))$ codewords each.
  The legitimate receiver decodes the codeword by joint typicality.
  The eavesdropper can almost decode the codeword within the bin, so the leakage is small.
  This proof is not in Lean.
]

For a degraded channel, $C_"CK" (W) = C_s (W)$, because $V -> X -> Y -> Z$ is a Markov chain.


== Channels with state
#source("Meat.Channel.State")

A channel with state has an input $x in A$, a state $s$ in a finite set $S$ and an output $y in B$, with transition law $W(y given x, s)$.
The states are i.i.d. with law $p_S$, and the encoder knows the whole state sequence before it sends, so it knows the state noncausally.
The decoder does not see the state.
Gelfand and Pinsker (1980) showed that the capacity is the largest value of $I(U ; Y) - I(U ; S)$ over auxiliary variables $U$.
This section states the model and the capacity formula, and proves the Csiszár sum identity, which is the key step of the converse.
The coding theorem itself is not yet in Lean.

#definition("Code for a channel with state", lean: ("Meat.StateCode", "Meat.StateCode.avgError"))[
  A code of length $n$ with message set $M$ is a pair of maps $f : M times S^n -> A^n$ and $g : B^n -> M$.
  Its average error probability is
  $ P_e := 1 / |M| sum_m sum_(s in S^n) p_S^n (s) sum_(y : g(y) != m) product_(i = 1)^n W(y_i given f(m, s)_i, s_i). $
]

#definition(
  "Achievable rates and capacity",
  lean: ("Meat.GelfandPinsker.Achievable", "Meat.GelfandPinsker.capacity"),
)[
  A rate $R$ is achievable if for every $epsilon > 0$ there exists $N$ such that for every $n >= N$ some code of length $n$ has at least $e^(n R)$ messages and $P_e <= epsilon$.
  The capacity is the supremum of the achievable rates.
]

#definition(
  "Gelfand-Pinsker formula",
  lean: ("Meat.GelfandPinsker.jointLaw", "Meat.GelfandPinsker.infoCapacity"),
)[
  For a law $q$ of $(S, U, X)$ with $U$ in a finite set $[m]$, the joint law adds the output $Y$ drawn from $W(dot given X, S)$.
  The formula is
  $ C_"GP" := sup {I(U ; Y) - I(U ; S) : q "has" S "marginal" p_S}. $
  The sup is over general conditional laws of $(U, X)$ given $S$.
  Gelfand and Pinsker showed that taking $X$ a function of $(U, S)$ gives the same value.
]

The Gelfand-Pinsker theorem says that the capacity equals $C_"GP"$.
In Lean, neither direction is proved yet.
The converse also needs the memoryless structure of the coding measure, and achievability needs covering inside bins and joint typicality decoding.

#lemma(
  "Chain rules over a set of coordinates",
  lean: ("Meat.condMutualInfo_restrict_eq_sum_min", "Meat.condMutualInfo_restrict_eq_sum_max"),
)[
  For a random sequence $S^n$, a set $A subset.eq [n]$ and random variables $X$ and $Z$,
  $ I(X ; S_A given Z) = sum_(j in A) I(X ; S_j given S_(A inter (j, n]), Z) = sum_(j in A) I(X ; S_j given S_(A inter [1, j)), Z). $
][
  Induction on $A$.
  For the first form, add the smallest element $a$ of the new set.
  The map $s_(A union {a}) |-> (s_A, s_a)$ is injective, so $I(X ; S_(A union {a}) given Z) = I(X ; S_A given Z) + I(X ; S_a given S_A, Z)$ by the chain rule.
  Every element of $A$ is larger than $a$, so the new term is the term for $a$.
  The terms for $j in A$ do not change, because $a$ is smaller than $j$.
  For the second form, add the largest element instead.
  The empty set gives a constant, whose conditional mutual information is $0$.
]

#theorem("Csiszár sum identity", lean: "Meat.csiszar_sum")[
  For random sequences $Y^n$ and $S^n$ and a random variable $V$,
  $ sum_(i = 1)^n I(S_(i + 1)^n ; Y_i given V, Y^(i - 1)) = sum_(j = 1)^n I(Y^(j - 1) ; S_j given V, S_(j + 1)^n). $
][
  Expand the left term for $i$ with the first chain rule, over the coordinates $j > i$ of $S$.
  This gives $sum_(j > i) I(Y_i ; S_j given S_(j + 1)^n, V, Y^(i - 1))$.
  Expand the right term for $j$ with the second chain rule, over the coordinates $i < j$ of $Y$.
  This gives $sum_(i < j) I(S_j ; Y_i given Y^(i - 1), V, S_(j + 1)^n)$.
  The two summands for a pair $i < j$ are equal by symmetry of conditional mutual information and a relabeling of the condition.
  Exchange the order of the double sum.
]


== Strong converse
#source("Meat.Channel.StrongConverse")

The weak converse says that rates above capacity cannot have a small error probability.
The strong converse says more: the error probability tends to $1$.
The proof is Wolfowitz's argument with an output law that mixes the output laws of all types.
Write $w(b given a) := W(b given a)$ as a real number, and for $x in A^n$ let $k_a$ be the number of times $a$ occurs in $x$.

#definition(
  "Output laws and types",
  lean: (
    "Meat.DMC.outputLaw",
    "Meat.DMC.typeWeight",
    "Meat.DMC.typePMF",
    "Meat.DMC.typePMF_toReal",
    "Meat.DMC.typeWeight_nonneg",
    "Meat.DMC.one_le_typeCount",
  ),
)[
  For weights $P$ on $A$, the output law is $(P W)(b) := sum_a P(a) w(b given a)$.
  The type of $x in A^n$ is $P_x (a) := k_a \/ n$, and for $n > 0$ it is a law on $A$.
  Every letter of $x$ has $k_(x_t) >= 1$.
]

#lemma(
  "Output laws",
  lean: (
    "Meat.DMC.sum_outputLaw",
    "Meat.DMC.outputLaw_nonneg",
    "Meat.DMC.le_outputLaw",
    "Meat.DMC.outputLaw_le_one",
  ),
)[
  $sum_b (P W)(b) = sum_a P(a)$.
  If $P >= 0$, then $0 <= P(a) w(b given a) <= (P W)(b)$, and if moreover $sum_a P(a) = 1$, then $(P W)(b) <= 1$.
]

#lemma("Information as a divergence sum", lean: "Meat.DMC.inputMutualInfo_eq_sum_log_div")[
  $ I(p, W) = sum_a sum_b p(a) w(b given a) log (w(b given a)) / ((p W)(b)). $
][
  $I = H(Y) - H(Y given X)$, with $H(Y given X) = -sum p(a) w(b given a) log w(b given a)$ and $H(Y) = -sum_b (p W)(b) log (p W)(b)$.
  Terms with $p(a) w(b given a) = 0$ vanish on both sides.
]

#lemma(
  "Analytic facts",
  lean: ("Meat.DMC.mul_log_sq_le", "Meat.DMC.sum_prod_mul_sq"),
)[
  For $0 < p <= 1$, $p (log p)^2 <= 2$.
  If $w_t$ are laws on $B$ and $sum_b w_t (b) f_t (b) = 0$ for each $t$, then
  $ sum_(y in B^n) product_t w_t (y_t) (sum_t f_t (y_t))^2 = sum_t sum_b w_t (b) f_t (b)^2. $
][
  With $p = e^(-s)$, the bound is $s^2 <= 2 e^s$.
  For the second claim, expand the square: the cross terms factor and vanish.
]

#definition(
  "Mixture of type outputs",
  lean: (
    "Meat.DMC.typeCounts",
    "Meat.DMC.card_typeCounts_le",
    "Meat.DMC.typeMix",
    "Meat.DMC.outSeq",
    "Meat.DMC.sum_typeMix_le",
    "Meat.DMC.outSeq_le_typeMix",
  ),
)[
  Let $T_n$ be the set of count vectors of sequences in $A^n$, so $|T_n| <= (n + 1)^(|A|)$.
  The mixture is $Q(y) := |T_n|^(-1) sum_(k in T_n) product_t (P_k W)(y_t)$, and $sum_y Q(y) <= 1$.
  For $x in A^n$ let $Q_x (y) := product_t (P_x W)(y_t)$.
  Then $Q_x <= |T_n| Q$.
]

#lemma("Wolfowitz bound", lean: "Meat.DMC.one_sub_avgError_le")[
  For every code with message set $M$ and every $lambda >= 0$,
  $ 1 - overline(lambda) <= 1 / (|M|) sum_m sum_y [W^n (y given f(m)) > lambda Q_(f(m)) (y)] W^n (y given f(m)) + (lambda |T_n|) / (|M|). $
][
  The probability of correct decoding is $|M|^(-1) sum_m sum_(y : g(y) = m) W^n (y given f(m))$.
  If $W^n (y given f(m)) <= lambda Q_(f(m)) (y)$, bound the term by $lambda |T_n| Q(y)$.
  The decoding sets are disjoint, so these terms sum to at most $lambda |T_n|$.
]

#lemma(
  "Mean and variance of the information density",
  lean: (
    "Meat.DMC.sum_mean_le_capacity",
    "Meat.DMC.logBound",
    "Meat.DMC.abs_log_le_logBound",
    "Meat.DMC.sum_mul_log_sq_le",
    "Meat.DMC.sum_log_typeCount_sq_le",
  ),
)[
  Let $Z_t (b) := log w(b given x_t) \/ (P_x W)(b)$ and $L := sum_(a, b) |log w(b given a)|$.
  Then $sum_t sum_b w(b given x_t) Z_t (b) = n I(P_x, W) <= n C$.
  Also $sum_b w(b given x_t) Z_t (b)^2 <= (log (n \/ k_(x_t)))^2 + L^2$ and $sum_t (log (n \/ k_(x_t)))^2 <= 2 n |A|$.
][
  The mean is a sum over letters, so it is $sum_a k_a$ times the divergence of $w(dot given a)$ from $P_x W$, which is $n I(P_x, W)$.
  If $Z_t >= 0$, then $Z_t <= log (n \/ k_(x_t))$ because $(P_x W)(b) >= (k_(x_t) \/ n) w(b given x_t)$.
  If $Z_t < 0$, then $Z_t >= log w(b given x_t) >= -L$ because $(P_x W)(b) <= 1$.
  The last sum is $n sum_a (k_a \/ n)(log (k_a \/ n))^2 <= 2 n |A|$.
]

#lemma("The error event", lean: "Meat.DMC.sum_error_event_le")[
  For $n > 0$, $delta > 0$, $lambda = e^(n (C + delta))$ and every $x in A^n$,
  $ sum_y [W^n (y given x) > lambda Q_x (y)] W^n (y given x) <= (L^2 + 2 |A|) / (n delta^2). $
][
  On the event, all letters have positive probability and $sum_t Z_t (y_t) > n (C + delta)$.
  Since the means sum to at most $n C$, the centered sum exceeds $n delta$.
  Chebyshev's inequality with the variance identity and the bounds above gives the claim.
]

#theorem("Strong converse", lean: "Meat.DMC.strongConverse")[
  If $R > C(W)$ and $epsilon > 0$, then there is $N$ such that for every $n >= N$ every code of length $n$ with at least $e^(n R)$ messages has $overline(lambda) >= 1 - epsilon$.
][
  Let $delta := (R - C) \/ 2$ and $lambda := e^(n (C + delta))$ in the Wolfowitz bound.
  The first term is at most $(L^2 + 2 |A|) \/ (n delta^2)$.
  The second is at most $(n + 1)^(|A|) e^(n (C + delta) - n R) <= e^(-n delta \/ 2)$ for large $n$.
]

== Random coding error exponent
#source("Meat.Channel.ErrorExponent")

Gallager's bound gives an error probability that decays exponentially in the block length for every rate below capacity.

#definition(
  "Gallager's function",
  lean: (
    "Meat.DMC.gallagerTerm",
    "Meat.DMC.gallagerSum",
    "Meat.DMC.gallagerE0",
    "Meat.DMC.gallagerTerm_nonneg",
    "Meat.DMC.gallagerSum_nonneg",
  ),
)[
  For $p in Delta(A)$ and $rho > -1$,
  $ E_0 (rho, p) := -log sum_b (sum_a p(a) w(b given a)^(1 \/ (1 + rho)))^(1 + rho). $
]

#definition(
  "Maximum likelihood codes",
  lean: (
    "Meat.DMC.mlDecode",
    "Meat.DMC.le_mlDecode",
    "Meat.DMC.mlCode",
    "Meat.DMC.codebookWeight",
  ),
)[
  For a codebook $C : M -> A^n$, the maximum likelihood decoder picks a message $m$ that maximizes $W^n (y given C(m))$.
  The codebook weight is $product_m p^n (C(m))$.
]

#lemma(
  "Gallager's bound for one codebook",
  lean: ("Meat.DMC.iidProb_mul_blockProb_rpow", "Meat.DMC.errorProb_mlCode_le"),
)[
  For $rho >= 0$ and $s := 1 \/ (1 + rho)$,
  $ lambda_m <= sum_y W^n (y given C(m))^s (sum_(m' != m) W^n (y given C(m'))^s)^rho. $
  Also $sum_x p^n (x) W^n (y given x)^s = product_t sum_a p(a) w(y_t given a)^s$.
][
  If the decoder errs at $y$, some $m' != m$ has $W^n (y given C(m')) >= W^n (y given C(m))$.
  Then the bracket is at least $W^n (y given C(m))^(s rho)$, and $s + s rho = 1$.
]

#theorem(
  "Random coding bound",
  lean: ("Meat.DMC.sum_codebookWeight_errorProb_mlCode_le", "Meat.DMC.exists_mlCode_avgError_le"),
)[
  For $0 <= rho <= 1$, the expected error probability of each message is at most $(|M| - 1)^rho e^(-n E_0 (rho, p))$.
  Hence some codebook has $overline(lambda) <= (|M| - 1)^rho e^(-n E_0 (rho, p))$.
][
  The codeword of $m$ is independent of the others.
  Reweight the codebooks by $W^n (y given C(m))^s$ and apply Jensen's inequality to the concave map $t |-> t^rho$.
  The other codewords contribute $(|M| - 1) sum_x p^n (x) W^n (y given x)^s$.
  Sum over $y$ and factor over letters.
]

#lemma(
  "Values and bounds of the function",
  lean: (
    "Meat.DMC.gallagerTerm_zero",
    "Meat.DMC.gallagerSum_zero",
    "Meat.DMC.outputLaw_le_gallagerTerm",
    "Meat.DMC.inv_card_le_gallagerSum",
    "Meat.DMC.gallagerSum_pos",
    "Meat.DMC.gallagerE0_le",
  ),
)[
  $E_0 (0, p) = 0$.
  For $0 <= rho <= 1$, the inner sum is at least $(p W)(b)$, the outer sum is at least $1 \/ |B|$, and $E_0 (rho, p) <= log |B|$.
][
  $w^s >= w$ for $0 <= w <= 1$ and $s <= 1$.
  Then $sum_b (p W)(b)^(1 + rho) >= sum_b (p W)(b)^2 >= 1 \/ |B|$ by the Cauchy-Schwarz inequality.
]

#definition(
  "Random coding exponent",
  lean: (
    "Meat.DMC.exists_code_avgError_le_exp",
    "Meat.DMC.randomCodingExponent",
    "Meat.DMC.exists_code_of_lt_randomCodingExponent",
  ),
)[
  $ E_r (R) := sup_(0 <= rho <= 1, p) (E_0 (rho, p) - rho R). $
  For every $n$, $0 <= rho <= 1$ and $p$ there is a code of length $n$ with at least $e^(n R)$ messages and $overline(lambda) <= e^(-n (E_0 (rho, p) - rho R))$.
  Hence for every $E < E_r (R)$ and every $n$ there is such a code with $overline(lambda) <= e^(-n E)$.
]

#lemma(
  "Slope at zero",
  lean: ("Meat.DMC.inputMutualInfo_eq_sub", "Meat.DMC.hasDerivAt_gallagerSum"),
)[
  The map $f(rho) := sum_b (sum_a p(a) w(b given a)^(1 \/ (1 + rho)))^(1 + rho)$ has derivative $-I(p, W)$ at $rho = 0$.
  For $0 <= rho <= 1$, $f(rho) = e^(-E_0 (rho, p))$.
][
  Each inner term $p(a) w^(1 \/ (1 + rho))$ has derivative $-p(a) w log w$ at $0$, and is constant $0$ near $0$ when $w = 0$.
  If $(p W)(b) > 0$, the outer term has derivative $(p W)(b) log (p W)(b) - sum_a p(a) w log w$; otherwise it is $0$ near $0$.
  The sum over $b$ is $-H(Y) + H(Y given X) = -I(p, W)$.
]

#theorem(
  "The exponent is positive below capacity",
  lean: ("Meat.DMC.exists_lt_gallagerE0", "Meat.DMC.randomCodingExponent_pos"),
)[
  If $R < I(p, W)$, then $rho R < E_0 (rho, p)$ for some $0 < rho <= 1$.
  Hence $E_r (R) > 0$ for $R < C(W)$.
][
  Let $f$ be as in the slope lemma, so $f(0) = 1$.
  For small $rho > 0$, $f(rho) < 1 - rho (I + R) \/ 2$ by the slope at zero.
  Then $E_0 (rho, p) = -log f(rho) >= 1 - f(rho) > rho R$.
  The set in the supremum is bounded above by $log |B| + |R|$.
]

The sphere packing bound, the matching upper bound on the exponent for rates near capacity, is not formalized.


== Wiretap achievability
#source("Meat.Channel.WiretapAchievability")

This section proves that every rate below $I(X; Y) - I(X; Z)$ is achievable for every wiretap channel.
With Wyner's converse, this gives the secrecy capacity of the physically degraded wiretap channel.
The code is a random codebook with a randomization index.
The legitimate receiver decodes both the message and the index.
Secrecy follows because an eavesdropper who knows the message could decode the index, so the index uses up all the information that the eavesdropper gets.

#definition(
  "Marginal channels",
  lean: (
    "Meat.Wiretap.toB",
    "Meat.Wiretap.toE",
    "Meat.Wiretap.toB_apply",
    "Meat.Wiretap.toE_apply",
    "Meat.Wiretap.sum_mul_blockProb_toB",
    "Meat.Wiretap.sum_mul_blockProb_toE",
    "Meat.Wiretap.jointPMF_toB",
    "Meat.Wiretap.jointPMF_toE",
  ),
)[
  The channel $W_B$ from $A$ to $B$ is the law of $Y$, and the channel $W_E$ from $A$ to $E$ is the law of $Z$.
  So $W_B (b given a) = sum_e W(b, e given a)$, and the same holds for $W_E$.
  Sums of a function of $y^n$ against $W^n$ are sums against $W_B^n$, and the same holds for $z^n$ and $W_E^n$.
  The joint laws of $W_B$ and $W_E$ with an input law $p$ are the push-forwards of the joint law of $W$ and $p$.
]

#lemma(
  "Entropy of products and concavity",
  lean: (
    "Meat.Wiretap.pmfH",
    "Meat.Wiretap.sum_negMulLog_blockProb",
    "Meat.Wiretap.sum_iidProb_mul_apply",
    "Meat.Wiretap.pmfH_concave",
  ),
)[
  Let $H(q) := sum_s -q(s) log q(s)$.
  For a DMC $V$ and $x in A^n$, $H(V^n (dot given x)) = sum_(i = 1)^n H(V(dot given x_i))$.
  Under the i.i.d. law $p^n$, the letter $x_i$ has law $p$.
  For weights $w_j >= 0$ with $sum_j w_j = 1$ and laws $P_j$, $sum_j w_j H(P_j) <= H(sum_j w_j P_j)$.
][
  For the first claim, write $-log product_i V(z_i given x_i) = sum_i -log V(z_i given x_i)$ and sum out the other letters.
  The last claim is Jensen's inequality for the concave function $t |-> -t log t$, at each point.
]

#definition(
  "Codebook code",
  lean: (
    "Meat.Wiretap.bookCode",
    "Meat.Wiretap.errorProb_bookCode_le",
    "Meat.Wiretap.bookMeasure",
    "Meat.Wiretap.isProbabilityMeasure_bookMeasure",
    "Meat.Wiretap.eveDec",
    "Meat.Wiretap.measureReal_eveDec_ne",
  ),
)[
  Let $C : M times L -> A^n$ be a codebook.
  The wiretap code of $C$ sends $C(m, l)$, and its decoder keeps the first component of the joint typicality decoder of $C$ for $W_B$.
  Its error probability at $(m, l)$ is at most the error probability of the typicality code of $C$ for $W_B$.
  Let $mu_C$ be the code measure of $(U, Y^n, Z^n)$ with $U = (M, L)$ uniform.
  The eavesdropper decoder uses $m$ and $z^n$ and the typicality decoder of the row $C(m, dot)$ for $W_E$.
  Its error probability under $mu_C$ is the average error of these typicality codes.
]

#lemma(
  "Entropies of a codebook code",
  lean: (
    "Meat.Wiretap.bookMeasure_pair",
    "Meat.Wiretap.bookMeasure_out",
    "Meat.Wiretap.entropy_out_bookMeasure",
    "Meat.Wiretap.condEntropy_out_bookMeasure",
  ),
)[
  Under $mu_C$, $P(Z^n = z, U = u) = W_E^n (z given C(u)) \/ |M times L|$.
  So $H(Z^n)$ is the entropy of the average of the laws $W_E^n (dot given C(u))$, and
  $ H(Z^n given U) = 1 / (|M| |L|) sum_u sum_(i = 1)^n H(W_E (dot given C(u)_i)). $
][
  The first identity follows from the marginal channel lemma.
  For the second one, $H(Z^n, U) = log (|M| |L|) + 1 / (|M| |L|) sum_u H(W_E^n (dot given C(u)))$ by $-x y log (x y) = -x y log x - x y log y$, and $H(U) = log (|M| |L|)$.
]

#lemma("Leakage of a codebook code", lean: "Meat.Wiretap.leakage_bookCode_le")[
  Let $P_E$ be the error probability of the eavesdropper decoder.
  Then
  $ I(M; Z^n) <= H(Z^n) - H(Z^n given U) - log |L| + log 2 + P_E log |L|. $
][
  The identity $I(M; Z^n) = H(Z^n) - H(Z^n given U) - H(L given M) + H(L given Z^n, M)$ follows from the definitions.
  The messages are uniform, so $H(L given M) = log |L|$.
  Fano's inequality with the eavesdropper decoder gives $H(L given Z^n, M) <= log 2 + P_E log |L|$.
]

Now let the codebook be random, with all letters i.i.d. $p$.
Write $w(C) := product_u p^n (C(u))$.

#lemma(
  "Averages over the codebook",
  lean: (
    "Meat.Wiretap.sum_prod_mul_row",
    "Meat.Wiretap.sum_condEntropy_out",
    "Meat.Wiretap.sum_entropy_out_le",
    "Meat.Wiretap.sum_eveError_le",
    "Meat.Wiretap.sum_bobError_le",
  ),
)[
  Let $q$ be the law of $Z$ for the input law $p$.
  Then
  $ sum_C w(C) H_C (Z^n given U) = n sum_a p(a) H(W_E (dot given a)), quad sum_C w(C) H_C (Z^n) <= n H(q). $
  The averages of the eavesdropper error and of the legitimate receiver error are at most the random coding bounds of the point-to-point section, for the channels $W_E$ with $|L|$ messages and $W_B$ with $|M| |L|$ messages.
][
  Each row $C(m, dot)$ of a random codebook is itself a random codebook, so averages of functions of one row are averages over random codebooks with $|L|$ codewords.
  The letter $C(u)_i$ has law $p$, which gives the first identity.
  The average of the laws of $Z^n$ is $q^n$, so the concavity lemma gives the inequality, and $H(q^n) = n H(q)$.
]

#lemma(
  "Secrecy rate in terms of the marginal channels",
  lean: ("Meat.Wiretap.inputMutualInfo_toE", "Meat.Wiretap.secrecyRate_eq"),
)[
  $I(X; Z) = H(q) - sum_a p(a) H(W_E (dot given a))$, and the secrecy rate of $p$ is $I_(W_B)(p) - I_(W_E)(p)$.
]

#lemma("A good codebook", lean: "Meat.Wiretap.exists_book")[
  For every $n >= 1$, $k$, $l$ and typicality parameter $gamma$, there is a codebook $C$ with
  $ overline(lambda)_B (C) + I_C (M; Z^n) / n <= beta_B + (n I(X; Z) - log l + log 2 + beta_E log l) / n, $
  where $overline(lambda)_B$ is the average error of the typicality code for $W_B$, and $beta_B$ and $beta_E$ are the two random coding bounds.
][
  Average the leakage bound over the codebook with the averages above, and add the average error.
  Some codebook is at most the average.
]

#theorem("Wyner's achievability", lean: ("Meat.Wiretap.achievable_of_lt", "Meat.Wiretap.achievable_zero"))[
  If $0 <= R < I(X; Y) - I(X; Z)$ for some input law $p$, then $R$ is an achievable secrecy rate.
  If $A$ is nonempty, the rate $0$ is achievable.
][
  Let $g := I(X; Y) - I(X; Z) - R$ and $eta := min(g, epsilon) \/ 16$.
  Take $k := ceil(e^(n R))$ messages and $l := ceil(e^(n R_L))$ indices, with $R_L := max(I(X; Z) - 4 eta, 0)$.
  Then $R + R_L <= I(X; Y) - 4 eta$, so the receiver term of $beta_B$ is at most $4 e^(-n eta)$.
  Also $(l - 1) e^(-n (I(X; Z) - 3 eta)) <= e^(-n eta)$, so the eavesdropper term of $beta_E$ is small.
  Since $n (I(X; Z) - 4 eta) <= log l <= log 2 + n I(X; Z)$, the leakage term is at most $4 eta + log 2 \/ n + beta_E (log 2 \/ n + I(X; Z))$.
  For large $n$, the bound of the good codebook lemma is at most $epsilon$.
  Both the average error and the leakage per letter are then at most $epsilon$.
  For the rate $0$, one message suffices: there is no error and no leakage.
]

#theorem(
  "Secrecy capacity of the degraded wiretap channel, Wyner",
  lean: "Meat.Wiretap.closure_achievable_eq",
)[
  For a physically degraded channel with $A$ nonempty, the closure of the set of achievable rates $R >= 0$ is $[0, C_s (W)]$.
][
  The converse gives the inclusion in $[0, C_s]$.
  If $C_s = 0$, the rate $0$ is achievable.
  Otherwise every $R in [0, C_s)$ is below the secrecy rate of some $p$, so it is achievable, and the closure of $[0, C_s)$ is $[0, C_s]$.
]

Achievability holds for every wiretap channel, not only for degraded ones.
For a general channel, Csiszár and Körner add an auxiliary variable $V$ and a channel prefix from $V$ to $X$, and the capacity is the supremum of $I(V; Y) - I(V; Z)$.
Their converse uses the Csiszár sum identity, which is not in Lean.
