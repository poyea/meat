#import "../meat.typ": *

= Many users

This chapter extends the two-user results of the channel chapter to $K$ users.
Users are indexed by $[K] = {0, dots, K - 1}$.
For a family of sets $A_k$ we write $A := product_k A_k$, and for $S subset.eq [K]$ we write $x_S := (x_k)_(k in S)$ and $S^c := [K] without S$.
Rates are vectors $R in RR^K$, and $R(S) := sum_(k in S) R_k$.

== Multiple access channels with $K$ senders
#source("Meat.Channel.MultipleAccessK")

There are $K$ senders with independent messages and one receiver.
The channel is a DMC $W$ from $A = product_k A_k$ to $B$.

#definition("Product law", lean: "Meat.piPMF")[
  For laws $p_i in Delta(A_i)$ over a finite index set, the product law is $(product_i p_i)(x) := product_i p_i (x_i)$.
]

#definition(
  "Code for K senders",
  lean: ("Meat.MACKCode", "Meat.MACKCode.input", "Meat.MACKCode.errorProb", "Meat.MACKCode.avgError"),
)[
  Let $n in NN$ and let $M_k$ be finite sets.
  A code of length $n$ is a family of encoders $f_k : M_k -> A_k^n$ and a decoder $g : B^n -> product_k M_k$.
  For $m in product_k M_k$ the input sequence is $x(m)_i := (f_k (m_k)_i)_k$.
  The error probability is $lambda_m := sum_(y^n : g(y^n) != m) W^n (y^n given x(m))$, and $overline(lambda) := (product_k |M_k|)^(-1) sum_m lambda_m$.
]

#definition("Achievable rate vector", lean: ("Meat.MACK.Achievable", "Meat.MACK.achievableRegion"))[
  A vector $R in RR^K$ is achievable for $W$ if for every $epsilon > 0$ there is $N$ such that for every $n >= N$ there are $L_k in NN$ with $L_k >= e^(n R_k)$ and a code of length $n$ with $M_k = [L_k]$ and $overline(lambda) <= epsilon$.
  The achievable region $cal(A)(W)$ is the set of achievable vectors with $R_k >= 0$ for all $k$.
]

#definition(
  "Masked inputs",
  lean: (
    "Meat.MACK.Masked",
    "Meat.MACK.instMeasurableSpaceMasked",
    "Meat.MACK.instMeasurableSingletonClassMasked",
    "Meat.MACK.instFintypeMasked",
    "Meat.MACK.mask",
  ),
)[
  The masked type is $product_k (A_k union {star})$, with the discrete measurable structure.
  For $S subset.eq [K]$ the mask of $x in A$ keeps $x_k$ for $k in S$ and puts $star$ elsewhere.
  It is the random variable $X_S$ in a form whose type does not depend on $S$.
]

#definition(
  "Polymatroid and capacity region",
  lean: ("Meat.MACK.subsetInfo", "Meat.MACK.polymatroid", "Meat.MACK.capacityRegion"),
)[
  For $p_k in Delta(A_k)$, let $(X, Y)$ have the law $(product_k p_k)(x) W(y given x)$.
  For $S subset.eq [K]$ let $I_p (S) := I(X_S; Y given X_(S^c))$.
  The polymatroid $cal(P)(p)$ is the set of $R in [0, infinity)^K$ with $R(S) <= I_p (S)$ for all $S$.
  The capacity region is $ cal(C)(W) := overline(op("conv") union.big_p cal(P)(p)). $
]

For $K = 2$ the constraints for $S = {0}$, ${1}$ and ${0, 1}$ are the three constraints of the pentagon.
The constraint for $S = emptyset$ is $0 <= 0$.

== Achievability for $K$ senders
#source("Meat.Channel.MultipleAccessKAchievability")

This section proves $cal(C)(W) subset.eq overline(cal(A)(W))$.
The proof is random coding with $K$ independent codebooks and joint typicality decoding.
There is one typicality test for each subset $S$.
A wrong message vector $m'$ differs from the sent vector $m$ exactly on a nonempty set $S$, and this gives $2^K - 1$ error events.
For the event $S$, the codewords of the users in $S$ are independent of the received sequence and of the other codewords, so it is a point-to-point error event for a side channel.

#proposition(
  "Product laws",
  lean: ("Meat.piPMF_apply", "Meat.iidProb_piPMF", "Meat.piPMF_map", "Meat.splitEquiv", "Meat.piPMF_split"),
)[
  $(product_i p_i)(x) = product_i p_i (x_i)$, and for sequences $(product_i p_i)^n (x) = product_i p_i^n (x_(dot, i))$.
  The push-forward of $product_i p_i$ by a coordinatewise map $(f_i)$ is $product_i (f_i)_* p_i$.
  The map $x |-> (x_S, x_(S^c))$ is a bijection, and $(product_i p_i)(x) = (product_(i in S) p_i)(x_S) (product_(i in.not S) p_i)(x_(S^c))$.
][
  The first identities are products of the coordinate identities.
  For the push-forward, write the sum over preimages as a product of sums over coordinates.
]

#lemma("Finite intersections of typical events", lean: "Meat.tendsto_sum_filter_forall")[
  Let $w_n$ be probability weights and $P_i$ events for $i$ in a finite set $T$.
  If $w_n (P_i) -> 1$ for each $i$, then $w_n (inter.big_(i in T) P_i) -> 1$.
][
  Induction on $T$, with the two-set case of the channel chapter.
]

#definition(
  "Side channels",
  lean: (
    "Meat.MACK.Inside",
    "Meat.MACK.Outside",
    "Meat.MACK.instDecidableEqForallFinInside",
    "Meat.MACK.instDecidableEqForallFinProdOutside",
    "Meat.MACK.sideChannel",
    "Meat.MACK.sidePMF",
  ),
)[
  For $S subset.eq [K]$, let $A_S := product_(k in S) A_k$ and $A_(S^c) := product_(k in.not S) A_k$.
  The side channel $V_S$ from $A_S$ to $A_(S^c) times B$ is $V_S (v, y given u) := (product_(k in.not S) p_k)(v) W(y given (u, v))$.
  The side law is the joint law of the input $(product_(k in S) p_k)$ and the output of $V_S$.
  The two instances make the sequence types decidable without a deep instance search.
]

#proposition(
  "The side law is a view of the joint law",
  lean: (
    "Meat.MACK.sidePMF_apply",
    "Meat.MACK.sidePMF_eq_map",
    "Meat.MACK.iidProb_sidePMF",
    "Meat.MACK.blockProb_sideChannel",
  ),
)[
  The side law of $(u, (v, y))$ is $(product_k p_k)(u, v) W(y given (u, v))$, so it is the law of $(X_S, (X_(S^c), Y))$.
  The same holds for sequences, and $V_S^n ((v, y) given u) = (product_(k in.not S) p_k)^n (v) W^n (y given (u, v))$.
][
  Split the product law with the bijection $x |-> (x_S, x_(S^c))$.
]

#lemma("Side information", lean: "Meat.MACK.subsetInfo_le_inputMutualInfo")[
  $I(X_S; Y given X_(S^c)) <= I(X_S; (X_(S^c), Y))$, and the right side is the mutual information of the side channel $V_S$ with input law $product_(k in S) p_k$.
][
  The chain rule gives $I(X_S; (Y, X_(S^c))) = I(X_S; X_(S^c)) + I(X_S; Y given X_(S^c))$.
  The masks are injective functions of $x_S$ and $x_(S^c)$, so they do not change the information.
]

#definition(
  "Decoding set",
  lean: ("Meat.MACK.splitSeq", "Meat.MACK.decodingSet", "Meat.MACK.mem_decodingSet"),
)[
  The decoding set $D_n^epsilon$ is the set of pairs $(x, y) in A^n times B^n$ such that for every $S subset.eq [K]$ the pair $(x_S, (x_(S^c), y))$ is jointly typical for the side law of $S$.
]

#lemma("Typicality of the sent codewords", lean: "Meat.MACK.tendsto_sum_iidProb_decodingSet")[
  For $epsilon > 0$, the probability of $D_n^epsilon$ under the i.i.d. joint law of $(X, Y)$ tends to $1$.
][
  For each $S$ the event is the joint typicality event of the side law, read through the bijection of sequences.
  Intersect the $2^K$ events.
]

#definition(
  "Random codebooks",
  lean: ("Meat.MACK.codebookWeight", "Meat.MACK.codeInput", "Meat.MACK.sum_mul_comp_eq"),
)[
  A codebook is a family $C_k : M_k -> A_k^n$.
  Its weight is $product_k product_(m_k) p_k^n (C_k (m_k))$, so the codewords are independent with laws $p_k^n$.
  The input of the codebook for $m$ is $x_C (m)_i := (C_k (m_k)_i)_k$.
  An expectation of a function of $phi(C)$ is the sum against the push-forward weight of $phi$.
]

#lemma(
  "Laws of codewords",
  lean: ("Meat.MACK.sum_ite_codeInput_eq", "Meat.MACK.sum_ite_pattern_eq"),
)[
  Under the codebook weight, $x_C (m)$ has the law $(product_k p_k)^n$.
  If $m_k != m'_k$ for $k in S$, then $(x_C (m)_S, x_C (m')_S, x_C (m)_(S^c))$ has the law $(product_(k in S) p_k)^n times (product_(k in S) p_k)^n times (product_(k in.not S) p_k)^n$.
][
  The event that the codebook has given values at the relevant messages is a product of events, one for each user.
  Sum each factor over the codebook of that user, as in the point-to-point case.
]

#lemma(
  "The error events",
  lean: ("Meat.MACK.sum_codebookWeight_mul_sum_ite", "Meat.MACK.sum_codebookWeight_mul_sum_le"),
)[
  The expected probability that $(x_C (m), Y^n)$ is not in $D_n^epsilon$ is $1 - P(D_n^epsilon)$.
  If $m'$ differs from $m$ exactly on $S$, the expected probability that $(x_C (m'), Y^n) in D_n^epsilon$ is at most $e^(-n (I_S - 3 epsilon))$, where $I_S$ is the side information of $S$.
][
  For the second bound, $x_C (m')$ agrees with $x_C (m)$ outside $S$.
  By the law of codewords, $x_C (m')_S$ is independent of $x_C (m)$ and of $Y^n$.
  The test for $S$ in $D_n^epsilon$ is a joint typicality test for $V_S$, so the bound is the point-to-point bound for $V_S$.
]

#definition(
  "Codes for the message vector",
  lean: (
    "Meat.MACKCode.toBlockCode",
    "Meat.MACKCode.errorProb_toBlockCode",
    "Meat.MACKCode.avgError_toBlockCode",
    "Meat.MACKCode.typicalCode",
    "Meat.MACKCode.toBlockCode_typicalCode",
    "Meat.MACK.pattern",
  ),
)[
  A code for $K$ senders is a block code with messages $product_k M_k$, and the two codes have the same error probabilities.
  The typicality code of a codebook uses the typicality decoder for $D_n^epsilon$.
  The pattern of $(m, m')$ is the set of $k$ with $m'_k != m_k$.
]

#theorem(
  "Random coding bound",
  lean: ("Meat.MACK.sum_errorProb_typicalCode_le", "Meat.MACK.exists_typicalCode_avgError_le"),
)[
  For every $m$, the expected error probability of the typicality code is at most
  $ 1 - P(D_n^epsilon) + sum_(S != emptyset) product_(k in S) (|M_k| - 1) e^(-n (I_S - 3 epsilon)). $
  Hence some codebook has an average error probability at most this bound.
][
  Apply the union bound of the typicality decoder.
  Group the wrong messages $m'$ by their pattern $S$.
  There are at most $product_(k in S) (|M_k| - 1)$ of them, and each one has the bound of the error events.
  Average over $m$ and pick a codebook that is at least as good as the average.
]

#theorem("Random coding for K senders", lean: "Meat.MACK.achievable_of_lt")[
  If $R(S) < I_p (S)$ for every nonempty $S$, then $R$ is achievable.
][
  Choose $eta > 0$ with $4 eta <= I_p (S) - R(S)$ for every nonempty $S$, and $L_k := ceil(e^(n R_k))$.
  Each term of the random coding bound with $epsilon = eta$ is at most $e^(-n eta)$, because $product_(k in S) (L_k - 1) <= e^(n R(S))$ and $I_p (S) <= I_S$.
  The bound tends to $0$.
]

#definition("Concatenation and relabeling", lean: ("Meat.MACKCode.append", "Meat.MACKCode.relabel"))[
  Two codes of lengths $n$ and $n'$ give a code of length $n + n'$ with message sets $M_k times M'_k$, which sends both codes one after the other.
  A code can be relabeled by bijections $M_k tilde.equiv M'_k$.
]

#lemma(
  "Errors of concatenation",
  lean: (
    "Meat.MACKCode.errorProb_ne_top",
    "Meat.MACKCode.errorProb_relabel",
    "Meat.MACKCode.avgError_relabel",
    "Meat.MACKCode.sum_errorProb_toReal",
    "Meat.MACKCode.avgError_ne_top",
    "Meat.MACKCode.errorProb_append_le",
    "Meat.MACKCode.avgError_append_le",
  ),
)[
  Relabeling does not change the average error probability.
  The average error probability of a concatenation is at most the sum of the two average error probabilities.
][
  The concatenation decodes wrong only if one of the two parts decodes wrong.
  Average over the product message set.
]

#theorem(
  "Time sharing",
  lean: (
    "Meat.MACK.Achievable.mono",
    "Meat.MACK.Achievable.max_zero",
    "Meat.MACK.mem_closure_achievableRegion",
    "Meat.MACK.Achievable.timeSharing",
    "Meat.MACK.convex_closure_achievableRegion",
  ),
)[
  Achievability is monotone, and the clamp $max(R_k, 0)$ of an achievable vector is achievable.
  If $R_k >= 0$ and $R - delta$ is achievable for every $delta > 0$, then $R in overline(cal(A)(W))$.
  If $R$ and $R'$ are achievable, $a, b >= 0$, $a + b = 1$ and $delta > 0$, then $a R + b R' - delta$ is achievable.
  So $overline(cal(A)(W))$ is convex.
][
  Use a code for $R$ of length $floor(a n)$ followed by a code for $R'$ of length $n - floor(a n)$.
  The rate loss is at most $sum_k |R_k - R'_k| \/ n$.
]

#theorem(
  "Inner bound",
  lean: (
    "Meat.MACK.polymatroid_subset_closure_achievableRegion",
    "Meat.MACK.capacityRegion_subset_closure_achievableRegion",
  ),
)[
  $cal(P)(p) subset.eq overline(cal(A)(W))$ for every $p$, and $cal(C)(W) subset.eq overline(cal(A)(W))$.
][
  For $R in cal(P)(p)$ and $delta > 0$, $R(S) - |S| delta < I_p (S)$ for every nonempty $S$, so $R - delta$ is achievable.
  The closure of the achievable region is closed and convex.
]

== Converse for $K$ senders
#source("Meat.Channel.MultipleAccessKConverse")

This section proves $overline(cal(A)(W)) subset.eq cal(C)(W)$.
Fano's inequality with a genie gives one bound for each subset $S$.
The averaging step uses a supporting hyperplane and the greedy vertices of a polymatroid.

#lemma("Determined variables", lean: "Meat.entropy_eq_of_determined")[
  If $Y = f(X)$ and $X = g(Y)$, then $H(X) = H(Y)$.
][
  $H(f(X)) <= H(X)$ and $H(g(Y)) <= H(Y)$.
]

#definition(
  "Operations on masks",
  lean: (
    "Meat.MACK.restrictMask",
    "Meat.MACK.unionMask",
    "Meat.MACK.restrictMask_mask",
    "Meat.MACK.unionMask_mask",
    "Meat.MACK.mask_pair_injective",
    "Meat.MACK.mask_univ_injective",
  ),
)[
  Restriction to $T$ puts $star$ outside $T$, and the union on $T$ takes the first mask on $T$ and the second one elsewhere.
  For $T subset.eq T'$ the restriction of $X_(T')$ to $T$ is $X_T$, and the union on $T$ of $X_T$ and $X_(T')$ is $X_(T union T')$.
  The maps $x |-> (X_S, X_(S^c))$ and $x |-> X_([K])$ are injective.
]

#lemma(
  "Independence of disjoint inputs",
  lean: ("Meat.MACK.piPMF_map_mask_apply", "Meat.MACK.piPMF_map_mask_pair_apply", "Meat.MACK.mutualInfo_mask_eq_zero"),
)[
  If $T inter T' = emptyset$, then $I(X_T; X_(T')) = 0$.
][
  The masks are coordinatewise maps, so the law of $(X_T, X_(T'))$ is a product over coordinates.
  In each coordinate one of the two masks is constant, so each factor splits.
]

#definition("Residual entropy", lean: "Meat.MACK.residual")[
  For $T subset.eq [K]$ let $h(T) := H(Y given X_T)$.
]

#proposition(
  "The rank function is a polymatroid rank",
  lean: (
    "Meat.MACK.condEntropy_mask_univ",
    "Meat.MACK.subsetInfo_eq_residual",
    "Meat.MACK.subsetInfo_empty",
    "Meat.MACK.residual_anti",
    "Meat.MACK.residual_sub_le",
    "Meat.MACK.subsetInfo_le_insert",
    "Meat.MACK.subsetInfo_insert_sub_le",
  ),
)[
  $I_p (S) = h(S^c) - h([K])$ and $I_p (emptyset) = 0$.
  $h$ is antitone, so $I_p$ is monotone.
  If $F subset.eq F'$ and $k in.not F'$, then $h(F) - h(F union {k}) <= h(F') - h(F' union {k})$.
  Hence if $T subset.eq T'$ and $k in.not T'$, then $I_p (T' union {k}) - I_p (T') <= I_p (T union {k}) - I_p (T)$.
][
  For the third claim write $a := X_k$, $c := X_F$ and $d := X_(F')$.
  By independence $H(a, c) = H(a) + H(c)$ and $H(a, d) = H(a) + H(d)$.
  The claim becomes $H(Y, a, d) + H(Y, c) <= H(Y, d) + H(Y, a, c)$.
  This is the submodularity of entropy for $a$, $d$ and $(Y, c)$, since $c$ is a function of $d$.
  The last claim is the third one with $F = (T' union {k})^c$ and $F' = (T union {k})^c$.
]

#definition(
  "Prefix sets and greedy vectors",
  lean: (
    "Meat.MACK.prefixSet",
    "Meat.MACK.prefixSet_succ",
    "Meat.MACK.notMem_prefixSet_self",
    "Meat.MACK.prefixSet_zero",
    "Meat.MACK.prefixSet_card",
    "Meat.MACK.sum_prefixSet",
    "Meat.MACK.sum_prefixSet_telescope",
    "Meat.MACK.greedy",
  ),
)[
  For a permutation $sigma$ of $[K]$, the prefix set $P_j$ is the set of $k$ with $sigma^(-1)(k) < j$.
  So $P_0 = emptyset$, $P_K = [K]$ and $P_(sigma^(-1)(k) + 1) = P_(sigma^(-1)(k)) union {k}$.
  For a set function $f$, the greedy vector is $g_k := f(P_(sigma^(-1)(k) + 1)) - f(P_(sigma^(-1)(k)))$.
  Sums over prefix sets are sums over initial segments in the order $sigma$, so sums of increments telescope.
]

#lemma(
  "Greedy vectors of a polymatroid",
  lean: ("Meat.MACK.sum_greedy_prefixSet", "Meat.MACK.greedy_nonneg", "Meat.MACK.sum_greedy_le"),
)[
  Let $f(emptyset) = 0$.
  Then $g(P_j) = f(P_j)$ for $j <= K$.
  If $f$ is monotone, then $g_k >= 0$.
  If $f$ has decreasing increments, then $g(T) <= f(T)$ for every $T$.
][
  For the last claim, compare $g_k$ with the increment of $f$ along the prefix sets intersected with $T$.
  For $k in T$ this increment is at least $g_k$ by decreasing increments, and for $k in.not T$ it is $0$.
  The increments telescope to $f(T) - f(emptyset)$.
]

#lemma("Summation by parts", lean: ("Meat.MACK.abel_nonneg", "Meat.MACK.sum_mul_le_of_prefixSet"))[
  Let $w >= 0$ be decreasing along $sigma$.
  If $alpha(P_j) <= beta(P_j)$ for all $j <= K$, then $sum_k w_k alpha_k <= sum_k w_k beta_k$.
][
  With $c := beta - alpha$ in the order $sigma$ and prefix sums $C_j >= 0$, induction gives $sum_(i <= j) w_i c_i >= w_j C_(j + 1)$.
]

#definition("Letter laws of a code", lean: ("Meat.MACKCode.inputLaw", "Meat.MACKCode.toBlockCode_inputLaw"))[
  For a code and a time $i$, the letter law of user $k$ is the law of $f_k (M_k)_i$ with $M_k$ uniform.
  The law of the whole input letter is the product of the letter laws, because the messages are independent.
]

#theorem("Fano bound for a subset", lean: "Meat.MACKCode.one_sub_mul_log_le_sum_subsetInfo")[
  For every code and every $S subset.eq [K]$,
  $ (1 - overline(lambda)) log product_(k in S) |M_k| <= sum_(i = 1)^n I_(p_i) (S) + log 2, $
  where $p_i$ is the family of letter laws at time $i$.
][
  Let a genie give the messages $M_(S^c)$ to the receiver.
  Fano's inequality gives $H(M_S given Y^n, M_(S^c)) <= log 2 + overline(lambda) log |M_S|$.
  Also $H(M_S given Y^n, M_(S^c)) >= log |M_S| + H(Y^n given M) - H(Y^n given M_(S^c))$.
  Then $H(Y^n given M) = sum_i H(Y_i given X_i)$ and $H(Y^n given M_(S^c)) <= sum_i H(Y_i given X_(S^c, i))$, because $X_(S^c, i)$ is a function of $M_(S^c)$.
  The difference of the two sums is $sum_i I_(p_i) (S)$.
]

#theorem(
  "Converse for K senders",
  lean: ("Meat.MACK.greedy_mem_polymatroid", "Meat.MACK.mem_capacityRegion_of_mem_achievableRegion"),
)[
  Greedy vectors of $I_p$, with some coordinates set to $0$, are in $cal(P)(p)$.
  Every $R in cal(A)(W)$ is in $cal(C)(W)$.
][
  Suppose $R in.not cal(C)(W)$.
  Since $cal(C)(W)$ is closed and convex, there are $lambda in RR^K$ and $u$ with $lambda dot z < u < lambda dot R$ for all $z in cal(C)(W)$.
  Let $w := max(lambda, 0)$ and order $[K]$ so that $w$ is decreasing.
  Take a code with small error probability and large $n$.
  By the Fano bounds, $(1 - epsilon) R(S) <= n^(-1) sum_i I_(p_i) (S) + n^(-1) log 2$ for every $S$.
  Let $overline(g)$ be the average of the greedy vectors of the $I_(p_i)$.
  Its prefix sums are the averages of $I_(p_i) (P_j)$, so summation by parts gives $(1 - epsilon) w dot R <= w dot overline(g) + (sum_k w_k) n^(-1) log 2$.
  Setting the coordinates with $lambda_k < 0$ to $0$ turns $overline(g)$ into a point $z$ of $op("conv") union.big_p cal(P)(p)$ with $lambda dot z = w dot overline(g)$.
  Since $lambda dot R <= w dot R$, this gives $(1 - epsilon) lambda dot R <= u + o(1)$, which contradicts $u < lambda dot R$.
]

== Capacity region for $K$ senders
#source("Meat.Channel.MultipleAccessKTheorem")

#theorem("Capacity region of the multiple access channel", lean: "Meat.MACK.closure_achievableRegion_eq")[
  $ overline(cal(A)(W)) = overline(op("conv") union.big_p cal(P)(p)). $
][
  The inner bound and the converse.
]

== Broadcast channels with $K$ receivers
#source("Meat.Channel.BroadcastK")

One sender has $K$ independent messages, one for each receiver.
The channel is a DMC $W$ from $A$ to $product_k B_k$, and receiver $k$ sees the coordinate $Y_k$.
For degraded channels the capacity region is the union of superposition regions.

#definition(
  "Broadcast code",
  lean: ("Meat.BCKCode", "Meat.BCKCode.decode", "Meat.BCKCode.errorProb", "Meat.BCKCode.avgError"),
)[
  A code of length $n$ is an encoder $f : product_k M_k -> A^n$ and decoders $g_k : B_k^n -> M_k$.
  For $m$ the error probability is the probability that $(g_k (Y_k^n))_k != m$, and $overline(lambda)$ is its average over $m$.
]

#definition(
  "Achievable rates and degraded channels",
  lean: ("Meat.BCK.Achievable", "Meat.BCK.achievableRegion", "Meat.BCK.out", "Meat.BCK.IsDegraded"),
)[
  Achievable vectors and $cal(A)(W)$ are defined as for $K$ senders.
  The marginal channel $W_k$ from $A$ to $B_k$ is the law of $Y_k$.
  $W$ is degraded if for all $k <= j$ there is a DMC $D$ from $B_k$ to $B_j$ with $W_j (dot given a) = sum_(y_k) W_k (y_k given a) D(dot given y_k)$.
  So receiver $0$ is the strongest and the chain is $X -> Y_0 -> Y_1 -> dots -> Y_(K - 1)$ in law.
]

#definition(
  "Superposition region",
  lean: (
    "Meat.BCK.layer",
    "Meat.BCK.above",
    "Meat.BCK.layerPMF",
    "Meat.BCK.superpositionRegion",
    "Meat.BCK.superpositionUnion",
  ),
)[
  Let $K >= 1$, let $V_j$ be finite, $q in Delta(product_j V_j)$ and $f : V_0 -> A$.
  Let $(V, Y)$ have the law $q(v) W(y given f(v_0))$.
  For receiver $k$ let $U_k := (V_j)_(j >= k)$, so $U_(K - 1) -> dots -> U_1 -> U_0$ is a chain of functions and $X = f(V_0)$ is a function of $U_0$.
  The superposition region is the set of $R >= 0$ with
  $ R_k <= I(U_k; Y_k given U_(k + 1)) quad "for all" k, $
  with $U_K$ constant.
  The union is over all alphabet sizes, all $q$ and all $f$.
]

For $K = 2$ this is the region $R_1 <= I(X; Y_1 given U)$, $R_2 <= I(U; Y_2)$ of degraded superposition coding, with $U = V_1$.
The subsections below prove $overline(cal(A)(W)) = overline(union.big cal(S)(q, f))$ for degraded $W$.
Its achievability is layered superposition coding, and its converse uses Fano's inequality at each receiver and the degraded chain.

=== Converse for degraded channels
#source("Meat.Open.BroadcastKConverse")

#theorem("Converse for the degraded broadcast channel", lean: "Meat.BCK.achievableRegion_subset_of_isDegraded")[
  Let $K >= 1$, let $A$ be finite and let $W$ be degraded.
  Then $cal(A)(W) subset.eq overline(union.big cal(S)(q, f))$.
][
  Replace $W$ by a twin channel with the same marginals in which $Y_0 -> Y_1 -> dots -> Y_(K - 1)$ is a chain at each time; the error probabilities do not change.
  Fix a code and a time $i$.
  Let $U_j$ hold the messages $M_l$ for $l >= j$ and the output blocks of the receivers $l >= j - 1$, the other coordinates fixed to a default value.
  Fano's inequality at receiver $k$ and the chain rule give $(1 - epsilon) n R_k - log 2 <= sum_i I(U_(k, i); Y_(k, i) given U_(k + 1, i))$, where the degraded chain removes the cross terms.
  A uniform time index mixes the $n$ letters into one law in the union, and the rates converge as $epsilon -> 0$ and $n -> infinity$.
]

=== Achievability by successive decoding
#source("Meat.Channel.BroadcastKAchievability")

#theorem("Inner bound for the degraded broadcast channel", lean: "Meat.BCK.superpositionUnion_subset_closure_achievableRegion")[
  Let $K >= 1$ and let $W$ be degraded.
  Then $union.big cal(S)(q, f) subset.eq overline(cal(A)(W))$.
][
  Write each layer as a function of the layers above it: there are independent random maps $T_l : product_j V_j -> V_l$ such that $V_l = T_l (V_(> l))$ has the law $q$.
  Then $(T_l)_l$ are the inputs of a channel with $K$ independent senders, and $X = f(V_0)$.
  Draw independent codebooks of maps for each layer.
  Receiver $k$ decodes the layers $K - 1, dots, k$ one at a time.
  At layer $l$ it uses a typicality decoder for the channel from $T_l$ to $(Y_k, T_(> l))$, with the layers above already decoded.
  If every step with the true layers above is correct, the whole decoder is correct, so the error probability is at most a sum of $K (K + 1) / 2$ step errors.
  Averaged over the codebooks, each step error is the random coding bound of one channel, and its mutual information is at least $I(U_l; Y_k given U_(l + 1))$.
  Since $W$ is degraded and $k <= l$, this is at least $I(U_l; Y_l given U_(l + 1)) >= R_l$ by data processing.
  So $R - delta$ is achievable for every $delta > 0$.
]

=== Capacity region
#source("Meat.Channel.BroadcastKCapacity")

#theorem("Capacity region of the degraded broadcast channel", lean: "Meat.BCK.closure_achievableRegion_eq_of_isDegraded")[
  Let $K >= 1$, let $A$ be finite and let $W$ be degraded.
  Then $ overline(cal(A)(W)) = overline(union.big cal(S)(q, f)). $
][
  The inner bound and the converse.
]

== Interference channels with $K$ users
#source("Meat.Open.InterferenceK")

There are $K$ sender and receiver pairs.
The channel is a DMC $W$ from $product_k A_k$ to $product_k B_k$.
Receiver $k$ sees $Y_k$ and wants the message of sender $k$ only.

#definition(
  "Interference code",
  lean: (
    "Meat.ICKCode",
    "Meat.ICKCode.toMACKCode",
    "Meat.ICKCode.errorProb",
    "Meat.ICKCode.avgError",
    "Meat.ICKCode.errorProb_toMACKCode",
    "Meat.ICKCode.avgError_toMACKCode",
    "Meat.ICKCode.append",
    "Meat.ICKCode.relabel",
    "Meat.ICKCode.toMACKCode_append",
    "Meat.ICKCode.toMACKCode_relabel",
  ),
)[
  A code of length $n$ is a family of encoders $f_k : M_k -> A_k^n$ and decoders $g_k : B_k^n -> M_k$.
  For $m$ the error probability is the probability that $(g_k (Y_k^n))_k != m$.
  With the joint decoder $y |-> (g_k (y_k))_k$ it is a code for $K$ senders with output $product_k B_k$, with the same error probabilities.
  Concatenation and relabeling commute with this view.
]

#definition(
  "Achievable rates",
  lean: ("Meat.ICK.Achievable", "Meat.ICK.achievableRegion", "Meat.ICK.out"),
)[
  Achievable vectors and $cal(A)(W)$ are defined as for $K$ senders.
  The marginal channel $W_k$ from $product_j A_j$ to $B_k$ is the law of $Y_k$.
]

#definition(
  "Rate formulas",
  lean: (
    "Meat.ICK.RateFormula",
    "Meat.ICK.RateFormula.Admissible",
    "Meat.ICK.RateFormula.region",
    "Meat.ICK.RateFormula.value",
    "Meat.ICK.letter",
    "Meat.ICK.letterLaw",
  ),
)[
  A rate formula with $m$ auxiliary coordinates and $r$ channel coordinates has numbers $a_(l, k)$ and coefficients $c_(l, S)$ and $d_(j, S)$, indexed by pairs $S$ of subsets of the coordinates.
  For an entropy vector $h$, its region is the set of $R >= 0$ with $sum_k a_(l, k) R_k <= sum_S c_(l, S) h_S$ for all $l$, and $h$ is admissible if $sum_S d_(j, S) h_S = 0$ for all $j$.
  The letter law of $W$ and a law $q$ of $(U, X)$ with $U in [kappa]^m$ is the law of $(U, X_0, dots, X_(K - 1), Y_0, dots, Y_(K - 1))$.
  The value of the formula is the closure of the union of the regions of the admissible entropy vectors of the letter laws.
]

#open-problem("Capacity region of the interference channel with K users", lean: "Meat.ICK.SingleLetterCapacity")[
  There are $m in NN$, a size function $kappa$ and a rate formula $F$ with $m$ auxiliary coordinates and $2 K$ channel coordinates such that for all nonempty finite $A_k$, all finite $B_k$ and every DMC $W$ from $product_k A_k$ to $product_k B_k$,
  $ overline(cal(A)(W)) = "value of" F "on the letter laws of" W "with" U in [kappa(|A|, |B|)]^m. $
]

For $K = 1$ the statement holds by the channel coding theorem.
For $K = 2$ it is the open problem of the two-user interference channel, posed by Shannon (1961) and Ahlswede (1974).
For $K >= 3$ even the Gaussian case is open, and interference alignment (Cadambe and Jafar, 2008) shows that the degrees of freedom behave differently from the two-user case.

#theorem(
  "Cooperative outer bound",
  lean: ("Meat.ICK.Achievable.toMACK", "Meat.ICK.achievableRegion_subset", "Meat.ICK.closure_achievableRegion_subset"),
)[
  $overline(cal(A)(W)) subset.eq cal(C)(W)$, where $W$ is read as a channel for $K$ senders with output $(Y_0, dots, Y_(K - 1))$.
][
  An interference code is a code for $K$ senders with the same average error probability.
  Apply the capacity theorem for $K$ senders.
]

#theorem(
  "Time sharing",
  lean: (
    "Meat.ICK.Achievable.mono",
    "Meat.ICK.Achievable.max_zero",
    "Meat.ICK.mem_closure_achievableRegion",
    "Meat.ICK.Achievable.timeSharing",
    "Meat.ICK.convex_closure_achievableRegion",
  ),
)[
  The statements of the time sharing theorem for $K$ senders hold for interference codes, and $overline(cal(A)(W))$ is convex.
][
  The same proof, with the errors of concatenations read through the view as a code for $K$ senders.
]

#lemma(
  "Marginal channels",
  lean: ("Meat.ICK.blockProb_out", "Meat.ICK.sum_mul_blockProb_out"),
)[
  $W_k^n (z given x) = sum_(y : y_k = z) W^n (y given x)$, and $sum_y F(y_k) W^n (y given x) = sum_z F(z) W_k^n (z given x)$.
][
  Expand the product over times as a sum over sequences.
]

#lemma(
  "Each receiver decodes all messages",
  lean: ("Meat.ICKCode.ofMACKCodes", "Meat.ICKCode.errorProb_ofMACKCodes_le"),
)[
  Let $f$ be encoders and let $G_k : B_k^n -> product_j M_j$ be decoders for $K$ senders over $W_k$.
  The interference code with decoders $g_k := (G_k)_k$ has error probability at most $sum_k lambda_m^((k))$, where $lambda_m^((k))$ is the error probability of $(f, G_k)$ for $W_k$.
][
  If receiver $k$ decodes its own message wrong, then $G_k$ decodes the vector wrong.
  Apply the union bound and the marginal identity.
]

#theorem(
  "Compound inner bound",
  lean: (
    "Meat.ICK.compoundRegion",
    "Meat.ICK.typicalCode",
    "Meat.ICK.typicalBound",
    "Meat.ICK.exists_typicalCode_avgError_le",
    "Meat.ICK.achievable_of_lt",
    "Meat.ICK.inter_polymatroid_subset_closure_achievableRegion",
    "Meat.ICK.compoundRegion_subset_closure_achievableRegion",
  ),
)[
  Let $cal(K)(W) := overline(op("conv") union.big_p inter.big_k cal(P)_k (p))$, where $cal(P)_k (p)$ is the polymatroid of $W_k$.
  If $R(S) < I_(p, k) (S)$ for all $k$ and all nonempty $S$, then $R$ is achievable.
  Hence $cal(K)(W) subset.eq overline(cal(A)(W))$.
][
  Use one random codebook and, at receiver $k$, the typicality decoder for $W_k$.
  The expected error probability is at most the sum over $k$ of the random coding bounds for $K$ senders, which tends to $0$.
  Then use time sharing.
]

The compound inner bound asks every receiver to decode all messages.
Treating interference as noise and the Han-Kobayashi scheme for $K$ users are not formalized.


== Two senders as a special case
#source("Meat.Channel.MultipleAccessKTwo")

This section checks that for $K = 2$ the polymatroid is the pentagon of the channel chapter, and that the two capacity regions agree.
A family $A_0, A_1$ is read as the pair $A_0 times A_1$.

#definition(
  "The channel as a two-sender channel",
  lean: (
    "Meat.MACK.twoChannel",
    "Meat.MACK.twoMap",
    "Meat.MACK.twoMap_injective",
    "Meat.MACK.jointPMF_map_twoMap",
    "Meat.MACK.map_jointMeasure_twoMap",
  ),
)[
  For a DMC $W$ from $product_(k < 2) A_k$ to $B$, the channel $W_2$ from $A_0 times A_1$ to $B$ is $W_2 (y given a_0, a_1) := W(y given (a_0, a_1))$.
  The map $(x, y) |-> (x_0, x_1, y)$ is injective.
  It sends the joint law of $(X, Y)$ for the product input $p_0 times p_1$ to the joint law of the pentagon for $W_2$, $p_0$ and $p_1$.
][
  Both laws give $(a_0, a_1, y)$ the weight $p_0 (a_0) p_1 (a_1) W(y given (a_0, a_1))$.
]

#lemma(
  "Residual entropies for two senders",
  lean: (
    "Meat.MACK.residual_univ_two",
    "Meat.MACK.residual_univ_two'",
    "Meat.MACK.residual_compl_zero",
    "Meat.MACK.residual_compl_one",
    "Meat.MACK.residual_empty_two",
  ),
)[
  $h([2]) = H(Y given X_0, X_1) = H(Y given X_1, X_0)$, $h({1}) = H(Y given X_1)$, $h({0}) = H(Y given X_0)$ and $h(emptyset) = H(Y)$.
][
  Each mask is an injective function of the listed coordinates, and the empty mask is constant.
  Conditioning on an injective function of a variable is conditioning on the variable, and conditioning on a constant does nothing.
]

#proposition(
  "Rank function for two senders",
  lean: ("Meat.MACK.subsetInfo_zero_two", "Meat.MACK.subsetInfo_one_two", "Meat.MACK.subsetInfo_univ_two"),
)[
  In the pentagon law for $W_2$, $p_0$ and $p_1$,
  $ I_p ({0}) = I(X_0; Y given X_1), quad I_p ({1}) = I(X_1; Y given X_0), quad I_p ([2]) = I((X_0, X_1); Y). $
][
  $I_p (S) = h(S^c) - h([2])$.
  Use the residual entropies and move them to the pentagon law along the injective map.
]

#theorem(
  "Polymatroid and pentagon",
  lean: ("Meat.MACK.mem_polymatroid_two_iff", "Meat.MACK.capacityRegion_two"),
)[
  $R in cal(P)(p)$ if and only if $(R_0, R_1)$ is in the pentagon of $W_2$, $p_0$ and $p_1$.
  The capacity region for $K = 2$ is the preimage of the capacity region of $W_2$ under $R |-> (R_0, R_1)$.
][
  The subsets of $[2]$ are $emptyset$, ${0}$, ${1}$ and $[2]$, and their constraints are $0 <= 0$ and the three pentagon constraints.
  The map $R |-> (R_0, R_1)$ is a linear homeomorphism, so it commutes with convex hulls and closures.
  The union over $p$ of its images of the polymatroids is the union of the pentagons over $(p_0, p_1)$.
]
