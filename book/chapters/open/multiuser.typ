#import "../../meat.typ": *

== Single-letter formulas
#source("Meat.Open.EntropicFormula")

The open problems of this part ask for a single-letter formula for a capacity region.
To state them as propositions, this section fixes what a single-letter formula is.
It is a finite list of linear inequalities on the rates.
The right sides are linear combinations of entropies of one letter.
The letter is a tuple of auxiliary variables, channel inputs and channel outputs.
The auxiliary variables take values in a set whose size may depend on the sizes of the alphabets.
Finitely many linear equations in the same entropies can restrict the admissible laws, for example to impose conditional independence.
Every capacity region known in closed form, such as the multiple access region, has this form.

#definition(
  "Entropic formula",
  lean: (
    "Meat.EntropicFormula",
    "Meat.EntropicFormula.pmfEntropy",
    "Meat.EntropicFormula.mask",
    "Meat.EntropicFormula.entropyVector",
    "Meat.EntropicFormula.Admissible",
    "Meat.EntropicFormula.region",
    "Meat.EntropicFormula.value",
  ),
)[
  Let $m, r in NN$.
  An entropic formula $F$ with $m$ auxiliary coordinates and $r$ channel coordinates is given by $L, J in NN$, coefficients $a_l, b_l in RR$ for $l in [L]$, and maps $c_l, d_j$ from $cal(P)([m]) times cal(P)([r])$ to $RR$ for $l in [L]$ and $j in [J]$.
  For a law $P$ of a pair $(U, Z)$ with $U in [k]^m$ and $Z in C^r$, and for $S = (S_1, S_2)$, let $h_P (S)$ be the entropy of $(U_(S_1), Z_(S_2))$.
  Here $U_(S_1)$ keeps the coordinates in $S_1$ and replaces the others by a blank symbol, and the entropy of a law $p$ on a finite set is $sum_a -p(a) log p(a)$.
  The law is admissible if $sum_S d_j (S) h_P (S) = 0$ for every $j$.
  Its region is the set of $(R_1, R_2) in [0, infinity)^2$ with
  $ a_l R_1 + b_l R_2 <= sum_S c_l (S) h_P (S) quad "for all" l. $
  For a family of laws $P_q$, the value of $F$ is the closure of the union of the regions of the admissible $P_q$.
]

#definition(
  "Letters of a two-user channel",
  lean: (
    "Meat.EntropicFormula.letter₃",
    "Meat.EntropicFormula.letter₄",
    "Meat.EntropicFormula.letterLaw₃",
    "Meat.EntropicFormula.letterLaw₄",
  ),
)[
  For a DMC $W$ from $A_1 times A_2$ to $B$, the letter of $(a_1, a_2, b)$ is the tuple of its three coordinates in $A_1 union.sq A_2 union.sq B$.
  For a law $q$ of $(U, X_1, X_2)$ with $U in [k]^m$, the letter law is the law of $(U, (X_1, X_2, Y))$, where $Y$ is the output of $W$ for the input $(X_1, X_2)$.
  For a DMC from $A_1 times A_2$ to $B_1 times B_2$, the letter has the four coordinates $X_1, X_2, Y_1, Y_2$.
]

The law $q$ of $(U, X_1, X_2)$ is arbitrary, so a formula can use correlated inputs.
Independent inputs, as in the interference channel, can be imposed by an admissibility equation such as $I(U_1, X_1; U_2, X_2 given U_0) = 0$.

== Interference channels
#source("Meat.Open.Interference")

Two senders send independent messages to two receivers.
Receiver $j$ wants only message $j$.
The channel is a DMC $W$ from $A_1 times A_2$ to $B_1 times B_2$, and receiver $j$ sees the component $Y_j$.
All sets are finite.

#definition(
  "Interference code",
  lean: (
    "Meat.ICCode",
    "Meat.ICCode.errorProb",
    "Meat.ICCode.avgError",
    "Meat.ICCode.toMACCode",
    "Meat.ICCode.errorProb_toMACCode",
    "Meat.ICCode.avgError_toMACCode",
  ),
)[
  An interference code of length $n$ is a tuple $(f_1, f_2, g_1, g_2)$ of maps $f_j : M_j -> A_j^n$ and $g_j : B_j^n -> M_j$.
  For $m = (m_1, m_2)$, its error probability $lambda_m$ is the probability under $W^n (dot given (f_1(m_1), f_2(m_2)))$ that $(g_1(y_1^n), g_2(y_2^n)) != m$, and $overline(lambda)$ is the average over $m$.
  It is also a multiple access code for $W$ with output $B_1 times B_2$ and decoder $y^n |-> (g_1(y_1^n), g_2(y_2^n))$, with the same error probabilities.
][
  The two definitions agree term by term.
]

#definition(
  "Achievable rate pair",
  lean: ("Meat.IC.Achievable", "Meat.IC.achievableRegion", "Meat.IC.out₁", "Meat.IC.out₂"),
)[
  Achievability of $(R_1, R_2)$ and the achievable region $cal(A)(W)$ are defined as for the multiple access channel, with interference codes.
  The marginal channels $W_1$ from $A_1 times A_2$ to $B_1$ and $W_2$ to $B_2$ are the laws of $Y_1$ and $Y_2$.
]

#open-problem("Capacity region of the interference channel", lean: "Meat.IC.SingleLetterCapacity")[
  There are $m in NN$, a size function $kappa$ and an entropic formula $F$ with $m$ auxiliary coordinates and four channel coordinates such that for all nonempty finite $A_1, A_2$, all finite $B_1, B_2$ and every DMC $W$ from $A_1 times A_2$ to $B_1 times B_2$,
  $ overline(cal(A)(W)) = "value of" F "on the letter laws of" W "with" U in [kappa(|A_1|, |A_2|, |B_1|, |B_2|)]^m. $
]

The problem goes back to Shannon (1961) and Ahlswede (1974).
The best known inner bound is the Han-Kobayashi region (1981).
Nair, Xia and Yazdanpanah (2015) showed that this region is not tight for some channels, so the proposition does not say that it is.
The capacity region is known under strong interference (Sato, 1981; Costa and El Gamal, 1987) and for some deterministic channels (El Gamal and Costa, 1982).
For the Gaussian channel, Etkin, Tse and Wang (2008) found the region to within one bit.

#definition(
  "Han-Kobayashi region",
  lean: ("Meat.IC.hkJointMeasure", "Meat.IC.hkRegion", "Meat.IC.hanKobayashiRegion"),
)[
  Let $Q$, $V_1$, $V_2$ be finite, $p_Q in Delta(Q)$ and $p_j : Q -> Delta(V_j times A_j)$.
  Let $(Q, U_1, X_1, U_2, X_2, Y_1, Y_2)$ have the law $p_Q(q) p_1(u_1, x_1 given q) p_2(u_2, x_2 given q) W(y_1, y_2 given x_1, x_2)$.
  The region $cal(H)(p_Q, p_1, p_2)$ is the set of $(R_1, R_2) in [0, infinity)^2$ with
  $ R_1 <= I(X_1; Y_1 given U_2, Q), quad R_2 <= I(X_2; Y_2 given U_1, Q), $
  $ R_1 + R_2 <= I(X_1, U_2; Y_1 given Q) + I(X_2; Y_2 given U_1, U_2, Q), $
  $ R_1 + R_2 <= I(X_2, U_1; Y_2 given Q) + I(X_1; Y_1 given U_1, U_2, Q), $
  $ R_1 + R_2 <= I(X_1, U_2; Y_1 given U_1, Q) + I(X_2, U_1; Y_2 given U_2, Q), $
  $ 2 R_1 + R_2 <= I(X_1, U_2; Y_1 given Q) + I(X_1; Y_1 given U_1, U_2, Q) + I(X_2, U_1; Y_2 given U_2, Q), $
  $ R_1 + 2 R_2 <= I(X_2, U_1; Y_2 given Q) + I(X_2; Y_2 given U_1, U_2, Q) + I(X_1, U_2; Y_1 given U_1, Q). $
  The Han-Kobayashi region $cal(H)(W)$ is the union over $k in NN$ with $Q = V_1 = V_2 = [k]$.
]

This is the compact form of Chong, Motani, Garg and El Gamal (2008).
$U_j$ carries the part of message $j$ that both receivers decode.

#theorem("Han-Kobayashi inner bound")[
  $cal(H)(W) subset.eq overline(cal(A)(W))$.
][
  Rate splitting, superposition coding and simultaneous nonunique decoding.
  This proof is not in Lean.
]

#definition(
  "Compound and strong interference regions",
  lean: (
    "Meat.IC.compoundRegion",
    "Meat.IC.StrongInterference",
    "Meat.IC.strongRegion",
    "Meat.IC.strongInterferenceRegion",
  ),
)[
  For $p_1 in Delta(A_1)$ and $p_2 in Delta(A_2)$, let $cal(P)_j (p_1, p_2)$ be the pentagon of the multiple access channel $W_j$.
  The compound region is $cal(K)(W) := overline(op("conv") union.big_(p_1, p_2) (cal(P)_1 (p_1, p_2) inter cal(P)_2 (p_1, p_2)))$.
  The channel has strong interference if for all $p_1, p_2$,
  $ I(X_1; Y_1 given X_2) <= I(X_1; Y_2 given X_2), quad I(X_2; Y_2 given X_1) <= I(X_2; Y_1 given X_1), $
  where each side is computed with the law $p_1 p_2 W_j$ of its output.
  The region $cal(S)(p_1, p_2)$ is the set of $(R_1, R_2) in [0, infinity)^2$ with
  $ R_1 <= I(X_1; Y_1 given X_2), quad R_2 <= I(X_2; Y_2 given X_1), quad R_1 + R_2 <= min(I(X_1, X_2; Y_1), I(X_1, X_2; Y_2)), $
  and $cal(S)(W) := overline(op("conv") union.big_(p_1, p_2) cal(S)(p_1, p_2))$.
]

#lemma(
  "Marginal channels",
  lean: (
    "Meat.IC.out₁_apply",
    "Meat.IC.out₂_apply",
    "Meat.IC.blockProb_out₁",
    "Meat.IC.blockProb_out₂",
    "Meat.IC.sum_mul_blockProb_out₁",
    "Meat.IC.sum_mul_blockProb_out₂",
  ),
)[
  $W_1 (b_1 given a) = sum_(b_2) W(b_1, b_2 given a)$, and the same holds for $W_1^n$ on sequences.
  For every $f$ on $B_1^n$, $sum_(y^n) f(y_1^n) W^n (y^n given x^n) = sum_(y_1^n) f(y_1^n) W_1^n (y_1^n given x^n)$.
  The same holds for the second receiver.
][
  A product of sums is a sum of products.
  Split each output sequence into its two component sequences.
]

#proposition("Cooperative outer bound", lean: (
  "Meat.IC.Achievable.toMAC",
  "Meat.IC.achievableRegion_subset",
  "Meat.IC.closure_achievableRegion_subset",
))[
  An achievable pair for $W$ is achievable for the multiple access channel $W$ with output $B_1 times B_2$.
  So $overline(cal(A)(W))$ is contained in the multiple access capacity region of $W$ with both outputs.
][
  Use the interference code as a multiple access code.
  Then apply the multiple access capacity theorem.
]

#definition(
  "Codes from two multiple access codes, concatenation and relabeling",
  lean: (
    "Meat.ICCode.ofMACCodes",
    "Meat.ICCode.errorProb_ofMACCodes_le",
    "Meat.ICCode.append",
    "Meat.ICCode.relabel",
    "Meat.ICCode.toMACCode_append",
    "Meat.ICCode.toMACCode_relabel",
  ),
)[
  Let $c_1$ be a multiple access code for $W_1$ and $c_2$ one for $W_2$ with the same encoders.
  The interference code takes these encoders, the first decoded message of $c_1$ at receiver 1 and the second decoded message of $c_2$ at receiver 2.
  Then $lambda_m <= lambda_m (c_1, W_1) + lambda_m (c_2, W_2)$.
  Concatenation and relabeling of interference codes are those of the multiple access codes, componentwise at each receiver.
][
  The interference code errs only if $c_1$ errs or $c_2$ errs.
  Bound the indicator by the sum of the two indicators and use the marginal channels.
  Concatenation and relabeling commute with the passage to multiple access codes by definition.
]

#proposition(
  "Time sharing",
  lean: (
    "Meat.IC.Achievable.mono",
    "Meat.IC.Achievable.max_zero",
    "Meat.IC.mem_closure_achievableRegion",
    "Meat.IC.Achievable.timeSharing",
    "Meat.IC.convex_closure_achievableRegion",
  ),
)[
  Achievability is monotone in the rates, and the set $overline(cal(A)(W))$ is convex.
  If $(R_1 - delta, R_2 - delta)$ is achievable for every $delta > 0$ and $R >= 0$, then $R in overline(cal(A)(W))$.
][
  The proof of the multiple access case applies.
  The concatenated code has average error at most the sum of the two average errors, by the bound for multiple access codes.
]

#theorem(
  "Compound multiple access inner bound",
  lean: (
    "Meat.IC.typicalBound",
    "Meat.IC.typicalCode",
    "Meat.IC.exists_typicalCode_avgError_le",
    "Meat.IC.achievable_of_lt",
    "Meat.IC.inter_pentagon_subset_closure_achievableRegion",
    "Meat.IC.compoundRegion_subset_closure_achievableRegion",
  ),
)[
  If $(R_1, R_2)$ is strictly inside both pentagons $cal(P)_1 (p_1, p_2)$ and $cal(P)_2 (p_1, p_2)$, it is achievable.
  So $cal(K)(W) subset.eq overline(cal(A)(W))$.
][
  Draw two independent codebooks with letters i.i.d. $p_1$ and $p_2$.
  Each receiver uses the joint typicality decoder of the multiple access achievability for its marginal channel, and keeps its own message.
  By the bound for codes from two multiple access codes, the expected error is at most the sum of the two random coding bounds of the multiple access section.
  So one pair of codebooks has average error at most this sum, which tends to $0$ when the rates are strictly inside both pentagons.
  Time sharing gives the closed convex hull.
]

#theorem(
  "Strong interference achievability, Sato and Costa-El Gamal",
  lean: (
    "Meat.IC.inter_pentagon_subset_strongRegion",
    "Meat.IC.strongRegion_subset_inter_pentagon",
    "Meat.IC.strongInterferenceRegion_eq_compoundRegion",
    "Meat.IC.strongInterferenceRegion_subset_closure_achievableRegion",
  ),
)[
  Always $cal(P)_1 inter cal(P)_2 subset.eq cal(S)$.
  Under strong interference, $cal(P)_1 inter cal(P)_2 = cal(S)$, so $cal(S)(W) = cal(K)(W) subset.eq overline(cal(A)(W))$.
][
  The region $cal(S)$ keeps the direct rate bound of each pentagon and both sum bounds.
  Under strong interference, the cross rate bound of each pentagon follows from the direct rate bound of the other.
]

#source("Meat.Open.InterferenceStrongConverse")

#definition(
  "Time-shared strong interference region",
  lean: ("Meat.IC.strongTimeSharingRegion", "Meat.IC.strongCapacityRegion"),
)[
  For a law $p_Q$ on $"Fin" k$ and input laws $p_1 (q)$, $p_2 (q)$, the region $cal(S)_Q (W)$ is the set of pairs $(R_1, R_2) >= 0$ with
  $ R_1 <= sum_q p_Q (q) I(X_1; Y_1 given X_2), quad R_2 <= sum_q p_Q (q) I(X_2; Y_2 given X_1), $
  $ R_1 + R_2 <= sum_q p_Q (q) I(X_1, X_2; Y_1), quad R_1 + R_2 <= sum_q p_Q (q) I(X_1, X_2; Y_2), $
  where the terms with index $q$ are taken under $p_1 (q) times p_2 (q)$ and the marginal channels $W_1$, $W_2$.
  The region $cal(C)_"s" (W)$ is the closure of the union of all $cal(S)_Q (W)$.
  This is the region with $I(dot given Q)$ terms; the two sum bounds are averaged separately, so it can be strictly larger than $cal(S)(W)$.
]

#theorem(
  "Strong interference converse, Costa and El Gamal",
  lean: (
    "Meat.IC.achievableRegion_subset_strongCapacityRegion",
    "Meat.IC.closure_achievableRegion_subset_strongCapacityRegion",
  ),
)[
  Under strong interference, $overline(cal(A)(W)) subset.eq cal(C)_"s" (W)$.
][
  First, the single-letter condition with $p_1$ a point mass at $x_1$ says that for each $x_1$ the channel $x_2 |-> W(x_1, x_2)$ is more capable for receiver 1 than for receiver 2: $I(X_2; Y_2) <= I(X_2; Y_1)$ for every input law.
  Take a code, uniform messages $M_1, M_2$, and the outputs $Y_1^n, Y_2^n$.
  The Csiszár telescoping identity, applied to $(M_1, M_2)$ and to $M_1$, writes $I(M_2; Y_1^n given M_1) - I(M_2; Y_2^n given M_1)$ as a sum over $i$ of $I(M_2; Y_(1 i) given M_1, S_i) - I(M_2; Y_(2 i) given M_1, S_i)$ with $S_i = (Y_1^(i-1), Y_(2, i+1)^n)$.
  Given $(M_1, S_i, M_2)$, the letter $Y_i$ has law $W(x_(1 i)(M_1), x_(2 i)(M_2))$, so each term is nonnegative by the more capable property.
  Hence $I(M_2; Y_2^n given M_1) <= I(M_2; Y_1^n given M_1)$.
  Fano's inequality at receiver 1, the independence of $M_1$ and $M_2$, and the letter bounds of the multiple access converse give $(1 - P_e) log k_1 <= sum_i I(X_(1 i); Y_(1 i) given X_(2 i)) + log 2$.
  With the previous inequality they give $(1 - P_e)(log k_1 + log k_2) <= sum_i I(X_(1 i), X_(2 i); Y_(1 i)) + 2 log 2$.
  The bounds at receiver 2 follow by exchanging the two users.
  Dividing by $n$ puts the rate pair near $cal(S)_Q (W)$ with $Q$ uniform on the letters.
]

#source("Meat.Open.InterferenceStrongAchievability")

#theorem(
  "Strong interference capacity, Costa and El Gamal",
  lean: (
    "Meat.IC.strongTimeSharingRegion_subset_closure_achievableRegion",
    "Meat.IC.strongCapacityRegion_subset_closure_achievableRegion",
    "Meat.IC.closure_achievableRegion_eq_strongCapacityRegion",
  ),
)[
  Under strong interference, $overline(cal(A)(W)) = cal(C)_"s" (W)$.
][
  Coded time sharing is done by a state channel.
  The inputs are maps $f_1 : "Fin" k -> A_1$ and $f_2 : "Fin" k -> A_2$, a state $Q tilde p_Q$ is drawn at each use, the channel acts as $W(f_1 (Q), f_2 (Q))$, and both receivers also see $Q$.
  With product input laws $times.big_q p_1 (q)$ and $times.big_q p_2 (q)$, each of the six quantities of the compound inner bound for the state channel is at least the $p_Q$-average of the corresponding quantity for $W$.
  For example $I(F_1; Q, Y_1 given F_2) >= I(F_1; Y_1 given Q, F_2)$, and given $(Q, F_2) = (q, f_2)$ the channel from $F_1$ to $Y_1$ is $f_1 |-> W_1(f_1 (q), f_2 (q))$, whose mutual information is at least that of $W_1(dot, f_2 (q))$ with input $p_1 (q)$.
  Strong interference bounds the cross terms by the direct ones, so the compound inner bound makes every point of $cal(S)_Q (W)$, shrunk by $delta$, achievable on the state channel.
  A code for the state channel has average error equal to the $p_Q^n$-average of the errors of the codes for $W$ obtained by fixing the state sequence.
  So some fixed state sequence gives a code for $W$ with no larger error and the same rates.
  The converse gives the other inclusion.
]

== Two-way channels
#source("Meat.Open.TwoWay")

Two users exchange messages over one channel.
The channel is a DMC $W$ from $A_1 times A_2$ to $B_1 times B_2$.
User $j$ sends $X_j$ and sees $Y_j$.
Each user may choose its next input from its message and all its past outputs.

#definition(
  "Two-way code",
  lean: (
    "Meat.TwoWayCode",
    "Meat.TwoWayCode.past",
    "Meat.TwoWayCode.input",
    "Meat.TwoWayCode.outputProb",
    "Meat.TwoWayCode.errorProb",
    "Meat.TwoWayCode.avgError",
  ),
)[
  A two-way code of length $n$ has encoders $f_(j i) : M_j times B_j^i -> A_j$ for $i in [n]$ and decoders $g_1 : M_1 times B_1^n -> M_2$ and $g_2 : M_2 times B_2^n -> M_1$.
  For messages $m$ and outputs $y^n$, the input at time $i$ is $(f_(1 i)(m_1, y_1^(i - 1)), f_(2 i)(m_2, y_2^(i - 1)))$, and the law of the outputs is
  $ P(y^n given m) = product_(i = 1)^n W(y_i given x_i (m, y^(i - 1))). $
  The error probability $lambda_m$ is the probability that $g_1(m_1, y_1^n) != m_2$ or $g_2(m_2, y_2^n) != m_1$, and $overline(lambda)$ is the average over $m$.
]

#definition("Achievable rate pair", lean: ("Meat.TwoWay.Achievable", "Meat.TwoWay.achievableRegion"))[
  Achievability and $cal(A)(W)$ are defined as for the multiple access channel, with two-way codes.
]

#open-problem("Capacity region of the two-way channel", lean: "Meat.TwoWay.SingleLetterCapacity")[
  There are $m$, $kappa$ and an entropic formula $F$ with four channel coordinates such that $overline(cal(A)(W))$ is the value of $F$ on the letter laws of $W$, for every two-way channel $W$ with nonempty input sets.
]

Shannon (1961) posed the problem and gave the inner and outer bounds below.
They agree when $W$ is symmetric in a suitable sense, but not in general.
Dueck (1979) showed that adaptive coding can beat the inner bound, and Hekstra and Willems (1989) improved the outer bound.
For the binary multiplying channel, the region is still unknown.

#definition(
  "Shannon's bounds",
  lean: (
    "Meat.TwoWay.rectangle",
    "Meat.TwoWay.innerBound",
    "Meat.TwoWay.outerBound",
    "Meat.TwoWay.innerBound_subset_outerBound",
  ),
)[
  For a law $p$ of $(X_1, X_2)$, let $(X_1, X_2, Y_1, Y_2)$ have the law $p(x_1, x_2) W(y_1, y_2 given x_1, x_2)$.
  The rectangle $cal(R)(p)$ is the set of $(R_1, R_2) in [0, infinity)^2$ with
  $ R_1 <= I(X_1; Y_2 given X_2), quad R_2 <= I(X_2; Y_1 given X_1). $
  The inner bound is $cal(I)(W) := overline(op("conv") union.big_(p_1, p_2) cal(R)(p_1 times p_2))$, and the outer bound is $cal(O)(W) := overline(op("conv") union.big_p cal(R)(p))$.
  Clearly $cal(I)(W) subset.eq cal(O)(W)$.
]

The inner bound is proved by a reduction to the interference channel.
User 2 is receiver 1 of an interference channel that sees $(X_2, Y_2)$, and user 1 is receiver 2 that sees $(X_1, Y_1)$.

#definition(
  "Interference channel of a two-way channel",
  lean: (
    "Meat.TwoWay.toInterference",
    "Meat.TwoWayCode.ofICCode",
    "Meat.TwoWay.out₁_toInterference",
    "Meat.TwoWay.out₂_toInterference",
  ),
)[
  $W'$ is the DMC from $A_1 times A_2$ to $(A_2 times B_2) times (A_1 times B_1)$ that outputs $((x_2, y_2), (x_1, y_1))$ with $y ~ W(dot given x)$.
  An interference code $(f_1, f_2, g_1, g_2)$ for $W'$ gives a two-way code that ignores the past outputs, with $g_1'(m_1, y_1^n) := g_2(f_1(m_1), y_1^n)$ and $g_2'(m_2, y_2^n) := g_1(f_2(m_2), y_2^n)$.
  The marginal channels of $W'$ output $(x_2, y_2)$ and $(x_1, y_1)$.
]

#lemma(
  "Entropy of a variable that is known",
  lean: (
    "Meat.TwoWay.condMutualInfo_pair_cond",
    "Meat.TwoWay.condMutualInfo_pair_self",
    "Meat.TwoWay.mutualInfo_pair_self",
    "Meat.TwoWay.condMutualInfo_le_condEntropy",
  ),
)[
  $I(X; (Z, Y) given Z) = I(X; Y given Z)$, $I(X; (X, Y) given Z) = H(X given Z)$, $I(X; (X, Y)) = H(X)$, and $I(X; Y given Z) <= H(X given Z)$.
][
  The first three follow from the definitions, since a repeated coordinate does not change an entropy.
  The last is $I(X; Y given Z) = H(X given Z) - H(X given Y, Z)$.
]

#proposition(
  "Reduction to the interference channel",
  lean: (
    "Meat.TwoWay.sum_mul_blockProb_map",
    "Meat.TwoWay.errorProb_ofICCode",
    "Meat.TwoWay.avgError_ofICCode",
    "Meat.TwoWay.Achievable.of_interference",
    "Meat.TwoWay.achievableRegion_interference_subset",
  ),
)[
  The two-way code of an interference code for $W'$ has the same error probabilities.
  So $cal(A)(W') subset.eq cal(A)(W)$, where the first region is for interference codes.
][
  Sums against the push-forward channel $W'$ are sums against $W$ of the pushed function.
  The two decoding events agree.
]

#theorem(
  "Shannon's inner bound",
  lean: (
    "Meat.TwoWay.jointMeasure_map",
    "Meat.TwoWay.condMutualInfo_rectangle₁",
    "Meat.TwoWay.condMutualInfo_rectangle₂",
    "Meat.TwoWay.rectangle_subset_closure_achievableRegion_interference",
    "Meat.TwoWay.innerBound_subset_closure_achievableRegion",
  ),
)[
  $cal(I)(W) subset.eq overline(cal(A)(W))$.
][
  Fix $p_1, p_2$ and $R in cal(R)(p_1 times p_2)$.
  The six quantities of the two pentagons of $W'$ are, by the lemma on known variables,
  $ I(X_1; Y_2 given X_2), quad H(X_2 given X_1), quad H(X_2) + I(X_1; Y_2 given X_2), $
  $ H(X_1 given X_2), quad I(X_2; Y_1 given X_1), quad H(X_1) + I(X_2; Y_1 given X_1). $
  Since $I(X_2; Y_1 given X_1) <= H(X_2 given X_1) <= H(X_2)$ and symmetrically, $(R_1 - delta, R_2 - delta)$ is strictly inside both pentagons.
  By the compound multiple access inner bound it is achievable for $W'$, hence for $W$.
  The set $overline(cal(A)(W'))$ is closed and convex, so it contains $cal(I)(W)$.
]

The two converses below use the interactive code measure of the last section.
The per-letter input law $p_i$ of a code is the law of $(X_(1 i), X_(2 i))$ under uniform messages.

#lemma(
  "Converse for one two-way code",
  lean: (
    "Meat.TwoWayCode.toFn",
    "Meat.TwoWayCode.outputProb_eq",
    "Meat.TwoWayCode.measureReal_dec_ne",
    "Meat.TwoWay.condMutualInfo_eq_sub₁",
    "Meat.TwoWay.condMutualInfo_eq_sub₂",
    "Meat.TwoWay.one_sub_mul_log_card_le₁",
    "Meat.TwoWay.one_sub_mul_log_card_le₂",
  ),
)[
  For a two-way code with average error $overline(lambda)$ and per-letter laws $p_i$,
  $ (1 - overline(lambda)) log |M_1| <= sum_i I_(p_i)(X_1; Y_2 given X_2) + log 2, $
  $ (1 - overline(lambda)) log |M_2| <= sum_i I_(p_i)(X_2; Y_1 given X_1) + log 2. $
][
  The code is an interactive code for $W$ with input map $(m, i, y^(i - 1)) |-> (f_(1 i)(m_1, y_1^(i - 1)), f_(2 i)(m_2, y_2^(i - 1)))$, and its average error is the measure of the error event.
  User 2 decodes $m_1$ from $(m_2, y_2^n)$, and its own input $X_(2 i)$ is a function of $(M_2, Y_2^(i - 1))$.
  Apply the converse for interactive codes with $Y_2$ as the observed output.
  Each difference of conditional entropies is $I(X_1; Y_2 given X_2)$.
  The second bound is the same with the roles of the users exchanged.
]

#theorem(
  "Shannon's outer bound",
  lean: (
    "Meat.TwoWay.mem_outerBound_of_mem_achievableRegion",
    "Meat.TwoWay.closure_achievableRegion_subset_outerBound",
  ),
)[
  $overline(cal(A)(W)) subset.eq cal(O)(W)$.
][
  Fix an achievable pair and $eta > 0$, and take a code of length $n$ with small error as in the multiple access converse.
  Let $x := max((1 - epsilon) R_1 - log 2 \/ n, 0)$ and $y := max((1 - epsilon) R_2 - log 2 \/ n, 0)$.
  By the converse for one code, $n x <= sum_i a_i$ and $n y <= sum_i b_i$, where $a_i$ and $b_i$ are the two quantities of the rectangle $cal(R)(p_i)$.
  The lemma on averages of pentagons, with sum bound $a_i + b_i$, puts $(x, y)$ in the convex hull of the rectangles.
  The distance from $(R_1, R_2)$ to $(x, y)$ is less than $eta$.
]

== Multiple access channels with feedback
#source("Meat.Open.MACFeedback")

Both senders see the past outputs of a multiple access channel $W$ from $A_1 times A_2$ to $B$.

#definition(
  "Feedback code",
  lean: (
    "Meat.FeedbackMACCode",
    "Meat.FeedbackMACCode.past",
    "Meat.FeedbackMACCode.input",
    "Meat.FeedbackMACCode.outputProb",
    "Meat.FeedbackMACCode.errorProb",
    "Meat.FeedbackMACCode.avgError",
    "Meat.FeedbackMACCode.ofMACCode",
    "Meat.FeedbackMACCode.errorProb_ofMACCode",
    "Meat.FeedbackMACCode.avgError_ofMACCode",
  ),
)[
  A feedback code of length $n$ has encoders $f_(j i) : M_j times B^i -> A_j$ for $i in [n]$ and a decoder $g : B^n -> M_1 times M_2$.
  The law of the outputs is $P(y^n given m) = product_i W(y_i given f_(1 i)(m_1, y^(i - 1)), f_(2 i)(m_2, y^(i - 1)))$, and $lambda_m$ is the probability that $g(y^n) != m$.
  A multiple access code is a feedback code that ignores the past outputs, with the same error probabilities.
]

#definition(
  "Achievable rate pair",
  lean: ("Meat.FeedbackMAC.Achievable", "Meat.FeedbackMAC.achievableRegion"),
)[
  Achievability and $cal(A)_"fb" (W)$ are defined as for the multiple access channel, with feedback codes.
]

#open-problem(
  "Capacity region of the multiple access channel with feedback",
  lean: "Meat.FeedbackMAC.SingleLetterCapacity",
)[
  There are $m$, $kappa$ and an entropic formula $F$ with three channel coordinates such that $overline(cal(A)_"fb" (W))$ is the value of $F$ on the letter laws of $W$, for every $W$ with nonempty input sets.
]

Gaarder and Wolf (1975) showed that feedback can enlarge the capacity region of a multiple access channel.
Cover and Leung (1981) gave the inner bound below, and Willems (1982) showed that it is tight when one input is a function of the output and the other input.
Kramer (1998) gave a multi-letter formula with directed information, which is not single-letter.
Bross and Lapidoth (2005) and others improved the Cover-Leung bound for some channels.
For the two-user Gaussian channel $Y = X_1 + X_2 + Z$ with powers $P_1, P_2$ and noise power $N$, Ozarow (1984) found the capacity region:
it is the union over $rho in [0, 1]$ of the pairs with
$ R_1 <= 1 / 2 log (1 + P_1 (1 - rho^2) / N), quad R_2 <= 1 / 2 log (1 + P_2 (1 - rho^2) / N), $
$ R_1 + R_2 <= 1 / 2 log (1 + (P_1 + P_2 + 2 rho sqrt(P_1 P_2)) / N). $
His achievability is a Schalkwijk-Kailath type linear scheme.
This Gaussian result is not in Lean.

#proposition(
  "Feedback does not shrink the region",
  lean: (
    "Meat.FeedbackMAC.Achievable.of_MAC",
    "Meat.FeedbackMAC.achievableRegion_MAC_subset",
    "Meat.FeedbackMAC.capacityRegion_subset_closure_achievableRegion",
  ),
)[
  The multiple access capacity region $cal(C)(W)$ is contained in $overline(cal(A)_"fb" (W))$.
][
  A code without feedback is a feedback code with the same average error.
  Then apply the achievability of $cal(C)(W)$.
]

#definition(
  "Cut-set bound",
  lean: ("Meat.FeedbackMAC.cutSetPentagon", "Meat.FeedbackMAC.cutSetBound"),
)[
  For a law $p$ of $(X_1, X_2)$, let $(X_1, X_2, Y)$ have the law $p(x_1, x_2) W(y given x_1, x_2)$.
  The pentagon $cal(P)(p)$ is the set of $(R_1, R_2) in [0, infinity)^2$ with
  $ R_1 <= I(X_1; Y given X_2), quad R_2 <= I(X_2; Y given X_1), quad R_1 + R_2 <= I(X_1, X_2; Y). $
  The cut-set bound is $overline(op("conv") union.big_p cal(P)(p))$.
]

#proposition(
  "The cut-set bound contains the capacity region without feedback",
  lean: ("Meat.FeedbackMAC.pentagon_eq_cutSetPentagon", "Meat.FeedbackMAC.capacityRegion_subset_cutSetBound"),
)[
  For product laws, $cal(P)(p_1 times p_2)$ is the multiple access pentagon, so $cal(C)(W)$ is contained in the cut-set bound.
][
  The law of $((X_1, X_2), Y)$ for $p_1 times p_2$ is the regrouped multiple access law, and mutual information is invariant under the regrouping.
]

#lemma(
  "Converse for one feedback code",
  lean: (
    "Meat.FeedbackMACCode.toFn",
    "Meat.FeedbackMACCode.outputProb_eq",
    "Meat.FeedbackMACCode.measureReal_dec_ne",
    "Meat.FeedbackMAC.condMutualInfo_eq_sub₁",
    "Meat.FeedbackMAC.condMutualInfo_eq_sub₂",
    "Meat.FeedbackMAC.mutualInfo_eq_sub",
    "Meat.FeedbackMAC.one_sub_mul_log_card_le₁",
    "Meat.FeedbackMAC.one_sub_mul_log_card_le₂",
    "Meat.FeedbackMAC.one_sub_mul_log_card_le₃",
  ),
)[
  For a feedback code with average error $overline(lambda)$ and per-letter laws $p_i$ of $(X_(1 i), X_(2 i))$,
  $ (1 - overline(lambda)) log |M_1| <= sum_i I_(p_i)(X_1; Y given X_2) + log 2, $
  $ (1 - overline(lambda)) log |M_2| <= sum_i I_(p_i)(X_2; Y given X_1) + log 2, $
  $ (1 - overline(lambda)) log (|M_1| |M_2|) <= sum_i I_(p_i)(X_1, X_2; Y) + log 2. $
][
  The code is an interactive code for $W$.
  For the first bound, a genie gives $m_2$ to the decoder, which keeps its first decoded message.
  Then $X_(2 i)$ is a function of $(M_2, Y^(i - 1))$, and the converse for interactive codes applies.
  The second bound exchanges the senders.
  The third bound is the sum-rate converse for interactive codes.
]

#lemma("Averaging the cut-set quantities", lean: "Meat.FeedbackMAC.sum_le_mul_avg")[
  Let $overline(p) := 1 / n sum_i p_i$.
  Then $sum_i I_(p_i)(X_1; Y given X_2) <= n I_(overline(p))(X_1; Y given X_2)$.
  The same holds for $I(X_2; Y given X_1)$ and $I(X_1, X_2; Y)$.
][
  Each quantity is $H(Y given G) - H(Y given X_1, X_2)$ for a function $G$ of the input.
  The first term is concave in the input law, by the mixture lemma.
  The second term is linear in the input law.
]

#theorem(
  "Cut-set outer bound",
  lean: (
    "Meat.FeedbackMAC.mem_cutSetBound_of_mem_achievableRegion",
    "Meat.FeedbackMAC.closure_achievableRegion_subset_cutSetBound",
  ),
)[
  $overline(cal(A)_"fb" (W))$ is contained in the cut-set bound.
][
  Fix an achievable pair and $eta > 0$, and take a code of length $n$ with small error.
  Let $x := max((1 - epsilon) R_1 - log 2 \/ n, 0)$ and $y := max((1 - epsilon) R_2 - log 2 \/ n, 0)$.
  By the converse for one code and the averaging lemma, $(x, y)$ lies in the pentagon $cal(P)(overline(p))$.
  The clipping at $0$ is allowed because $I(X_1; Y given X_2)$ and $I(X_2; Y given X_1)$ are at most $I(X_1, X_2; Y)$, by the chain rule.
  The distance from $(R_1, R_2)$ to $(x, y)$ is less than $eta$, so the pair is in the closure of the union of the pentagons.
]

#definition(
  "Cover-Leung region",
  lean: (
    "Meat.FeedbackMAC.coverLeungMeasure",
    "Meat.FeedbackMAC.coverLeungPentagon",
    "Meat.FeedbackMAC.coverLeungRegion",
  ),
)[
  Let $V$ be finite, $p_U in Delta(V)$ and $p_j : V -> Delta(A_j)$.
  Let $(U, X_1, X_2, Y)$ have the law $p_U(u) p_1(x_1 given u) p_2(x_2 given u) W(y given x_1, x_2)$.
  The pentagon is the set of $(R_1, R_2) in [0, infinity)^2$ with
  $ R_1 <= I(X_1; Y given X_2, U), quad R_2 <= I(X_2; Y given X_1, U), quad R_1 + R_2 <= I(X_1, X_2; Y). $
  The Cover-Leung region is the closed convex hull of the union over $V = [k]$, $k in NN$.
]

#theorem("Cover-Leung inner bound")[
  The Cover-Leung region is contained in $overline(cal(A)_"fb" (W))$.
][
  Block Markov superposition coding: in each block, both senders decode the other's fresh message from the feedback, and cooperate in the next block through $U$.
  This proof is not in Lean.
]

== Interactive codes
#source("Meat.Open.Interactive")

An interactive code chooses the input at time $i$ from the message and the past outputs.
Feedback codes and two-way codes are interactive codes.
This section gives the code measure of such a code and the converse bounds that the two previous sections use.
It uses the chain rule over sequences from the Shannon chapter.

#definition(
  "Sequence probability",
  lean: (
    "Meat.Interactive.seqProb",
    "Meat.Interactive.restrict",
    "Meat.Interactive.tail",
    "Meat.Interactive.emptyPrefix",
    "Meat.Interactive.seqPrefix_cons",
    "Meat.Interactive.seqProb_cons",
  ),
)[
  For a DMC $W$ from $A$ to $B$ and maps $phi_i : B^(i - 1) -> A$, the probability of $y in B^n$ is
  $ P_phi (y) := product_(i = 1)^n W(y_i given phi_i (y^(i - 1))). $
  Let $phi|_i$ be the restriction of $phi$ to the first $i - 1$ letters, and let $phi_b (j, q) := phi_(j + 1)(b, q)$.
  Then $P_phi (b, z) = W(b given phi_1) P_(phi_b) (z)$.
]

#lemma("Causal laws", lean: ("Meat.Interactive.sum_seqProb", "Meat.Interactive.sum_mul_seqProb"))[
  $sum_y P_phi (y) = 1$.
  For every $i$ and every function $F$ of $(y^(i - 1), y_i)$,
  $ sum_y F(y^(i - 1), y_i) P_phi (y) = sum_(p in B^(i - 1)) sum_b F(p, b) P_(phi|_i) (p) W(b given phi_i (p)). $
][
  Induction on $n$, splitting off the first letter of $y$.
  In the second identity, the future letters sum to $1$ by the first identity.
]

#lemma(
  "Conditional entropy through a kernel",
  lean: ("Meat.Interactive.measureReal_comp_eq_sum", "Meat.Interactive.condEntropy_eq_comp_of_kernel"),
)[
  If $P(G = g, Y = s) = P(G = g) K(s given f(g))$ for all $g$ and $s$, then $H(Y given G) = H(Y given f(G))$.
][
  The hypothesis gives the factorization of the Markov chain $G -> f(G) -> Y$, so $I(G; Y given f(G)) = 0$.
  Since $(G, f(G))$ is an injective image of $G$, $H(Y given G, f(G)) = H(Y given G)$.
]

#lemma(
  "Mixtures",
  lean: (
    "Meat.Interactive.entropy_toMeasure",
    "Meat.Interactive.condEntropy_const",
    "Meat.Interactive.uniformPMF",
    "Meat.Interactive.mixture",
    "Meat.Interactive.mixture_apply",
    "Meat.Interactive.map_mixture",
    "Meat.Interactive.map_snd_mixture",
    "Meat.Interactive.entropy_mixture",
    "Meat.Interactive.condEntropy_mixture",
    "Meat.Interactive.sum_condEntropy_le",
    "Meat.Interactive.sum_entropy_le",
    "Meat.Interactive.jointPMF_bind",
    "Meat.Interactive.condEntropy_jointMeasure_avg",
  ),
)[
  Let $P_1, dots, P_k$ be laws on a finite set and $overline(P) := 1 / k sum_q P_q$.
  For all $f$ and $g$, $1 / k sum_q H_(P_q) (f given g) <= H_(overline(P)) (f given g)$ and $1 / k sum_q H_(P_q) (f) <= H_(overline(P)) (f)$.
  For a DMC $W$ and input laws $p_q$, the joint law of $W$ and $overline(p)$ is the average of the joint laws of $W$ and $p_q$.
  Also $1 / k sum_q H_(p_q) (Y given X) = H_(overline(p)) (Y given X)$.
][
  Let $Q$ be uniform on $[k]$, and let $Z$ have law $P_Q$ given $Q$.
  Then $H(Q, f(Z)) = log k + 1 / k sum_q H_(P_q)(f)$, because $-x y log (x y) = -x y log x - x y log y$.
  So $H(f(Z) given Q, g(Z)) = 1 / k sum_q H_(P_q)(f given g)$, and removing $Q$ from the condition increases the entropy.
  The law of $Z$ is $overline(P)$.
  The last identity holds because $H(Y given X) = -sum_(x, y) p(x) W(y given x) log W(y given x)$ is linear in $p$.
]

#definition(
  "Code measure",
  lean: (
    "Meat.Interactive.sum_codeMass",
    "Meat.Interactive.codePMF",
    "Meat.Interactive.sum_codePMF_mul",
    "Meat.Interactive.inputLaw",
    "Meat.Interactive.map_codePMF_letter",
    "Meat.Interactive.codeMeasure",
    "Meat.Interactive.isProbabilityMeasure_codeMeasure",
    "Meat.Interactive.codeMeasure_apply",
    "Meat.Interactive.codeMeasure_prefix",
    "Meat.Interactive.map_codeMeasure_letter",
    "Meat.Interactive.codeMeasure_kernel",
    "Meat.Interactive.condEntropy_prefix_eq",
    "Meat.Interactive.entropy_fst_codeMeasure",
  ),
)[
  For input maps $phi_m$, $m in M$, the code measure is the law of $(U, Y^n)$, where $U$ is uniform on $M$ and $Y^n$ has law $P_(phi_U)$ given $U$.
  The input law $p_i$ is the law of $X_i := phi_(U, i)(Y^(i - 1))$, and the law of $(X_i, Y_i)$ is the joint law of $W$ and $p_i$.
  Given $(U, Y^(i - 1))$, the law of $Y_i$ is $W(dot given X_i)$.
  So for every function $h$, $H(h(Y_i) given U, Y^(i - 1)) = H(h(Y_i) given X_i)$.
  Also $H(U) = log |M|$.
][
  All identities follow from the causal laws.
  The conditional entropy identity is the kernel lemma.
]

#theorem(
  "Converse for interactive codes",
  lean: (
    "Meat.Interactive.one_sub_mul_log_card_le_sum",
    "Meat.Interactive.one_sub_mul_log_card_le_sum_mutualInfo",
  ),
)[
  Let $M$ be identified with $J times K$.
  Let a receiver know the component $K$ of $U$, see $Z_i := h(Y_i)$, and decode the component $J$ with error probability $lambda$.
  Assume that $pi(X_i)$ is a function of $(K, Z^(i - 1))$ for a map $pi$ of the inputs.
  Then
  $ (1 - lambda) log |J| <= sum_i (H_(p_i)(h(Y) given pi(X)) - H_(p_i)(h(Y) given X)) + log 2. $
  If a decoder of $U$ from $Y^n$ has error probability $lambda$, then $(1 - lambda) log |M| <= sum_i I_(p_i)(X; Y) + log 2$.
][
  Write $U_J$ and $U_K$ for the components.
  Since $H(U) = log |J| + log |K|$ and $H(U_K) <= log |K|$, we get $log |J| <= H(U_J given U_K) = I(Z^n; U_J given U_K) + H(U_J given Z^n, U_K)$.
  Fano's inequality bounds the last term by $log 2 + lambda log |J|$.
  By the chain rule, $I(Z^n; U_J given U_K) = sum_i I(Z_i; U_J given U_K, Z^(i - 1))$.
  Each term is $H(Z_i given U_K, Z^(i - 1)) - H(Z_i given U, Z^(i - 1))$.
  The first entropy is at most $H(Z_i given pi(X_i))$, because $pi(X_i)$ is a function of $(U_K, Z^(i - 1))$.
  The second is at least $H(Z_i given U, Y^(i - 1)) = H(Z_i given X_i)$.
  The sum-rate bound is the same argument without $K$, with $H(Y_i given Y^(i - 1)) <= H(Y_i)$.
]
