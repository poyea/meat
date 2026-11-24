#import "../../meat.typ": *

== Broadcast channels
#source("Meat.Open.Broadcast")

The broadcast channel, its codes and the superposition region are defined in the chapter on channel coding.
There, $W$ is a DMC from $A$ to $B_1 times B_2$, and receiver $j$ sees $Y_j$.
The capacity region of the two-receiver broadcast channel is known for many classes of channels.
It is open in general.
This section states the problem, defines the best known inner and outer bounds, and proves the inclusions that need no coding argument.
All sets are finite.

#definition(
  "Marton region",
  lean: ("Meat.BC.martonSumRate", "Meat.BC.martonRegionOf", "Meat.BC.martonRegion"),
)[
  Let $T$, $V_1$ and $V_2$ be finite sets, $q in Delta(T times V_1 times V_2)$ and $p_X : T times V_1 times V_2 -> Delta(A)$.
  Let $(T, V_1, V_2, X, Y_1, Y_2)$ have the law $q(t, v_1, v_2) p_X (x given t, v_1, v_2) W(y_1, y_2 given x)$.
  Let
  $ S := I(V_1; Y_1 given T) + I(V_2; Y_2 given T) - I(V_1; V_2 given T). $
  The Marton region $cal(M)(q, p_X)$ is the set of $(R_1, R_2) in [0, infinity)^2$ with
  $ R_1 <= I(T, V_1; Y_1), quad R_2 <= I(T, V_2; Y_2), quad R_1 + R_2 <= min(I(T; Y_1), I(T; Y_2)) + S. $
  The Marton region $cal(M)(W)$ of $W$ is the union of $cal(M)(q, p_X)$ over all $k_0, k_1, k_2 in NN$ with $T = [k_0]$, $V_1 = [k_1]$ and $V_2 = [k_2]$.
]

This is the region for two private messages, with a common auxiliary variable $T$.
It is due to Marton (1979), in the form of Gelfand and Pinsker (1980).
Marton's region is contained in the closure of the achievable region, by random binning and superposition coding.
This coding theorem is not in Lean.

#definition("UV outer bound", lean: ("Meat.BC.uvRegionOf", "Meat.BC.uvRegion"))[
  Let $V_1$ and $V_2$ be finite sets, $q in Delta(V_1 times V_2)$ and $p_X : V_1 times V_2 -> Delta(A)$.
  Let $(U, V, X, Y_1, Y_2)$ have the law $q(u, v) p_X (x given u, v) W(y_1, y_2 given x)$.
  The region $cal(O)(q, p_X)$ is the set of $(R_1, R_2) in [0, infinity)^2$ with
  $ R_1 <= I(U; Y_1), quad R_2 <= I(V; Y_2), $
  $ R_1 + R_2 <= I(U; Y_1) + I(X; Y_2 given U), quad R_1 + R_2 <= I(V; Y_2) + I(X; Y_1 given V). $
  The UV outer bound $cal(O)(W)$ is the union of $cal(O)(q, p_X)$ over all $k_1, k_2 in NN$ with $V_1 = [k_1]$ and $V_2 = [k_2]$.
]

Nair and El Gamal (2007) proved that the achievable region is contained in $cal(O)(W)$.
Their proof uses the Csiszár sum identity, and it is not in Lean.
The UV outer bound is known not to be tight in general.

#lemma(
  "Tools for finite laws",
  lean: (
    "Meat.sum_measureReal_inter",
    "Meat.markovChain_of_factor",
    "Meat.map_apply_inj",
    "Meat.measureReal_map_toMeasure",
    "Meat.condMutualInfo_comp_right_le",
    "Meat.condMutualInfo_comp_left_le",
  ),
)[
  Summing the probabilities of $X = x$ and an event over $x$ gives the probability of the event.
  If the law of $(X, Y, Z)$ factors as the law of $(X, Y)$ times a function of $(y, z)$, then $X -> Y -> Z$.
  The push-forward of a PMF by an injective map takes the same value at the image of a point.
  The measure of a singleton under the push-forward of a PMF is the value of the pushed PMF.
  Conditional mutual information does not increase when a map is applied to either of its first two variables.
][
  The first statement splits the event by the value of $X$.
  For the second, summing the factorization over $x$ gives the law of $(Y, Z)$, and the criterion for Markov chains follows.
  The last statement compares conditional entropies, since conditioning on a function of a variable gives at least as much entropy.
]

#definition("Superposition union", lean: "Meat.BC.superpositionUnion")[
  The superposition union $cal(S)(W)$ is the union of the superposition regions $cal(S)(p_U, p_X)$ over all $k in NN$, $p_U in Delta([k])$ and $p_X : [k] -> Delta(A)$.
]

#definition("Degraded broadcast channel", lean: "Meat.BC.IsDegraded")[
  The channel $W$ is degraded if there is a DMC $D$ from $B_1$ to $B_2$ with
  $ W_2 (y_2 given x) = sum_(y_1) W_1 (y_1 given x) D(y_2 given y_1) $
  for all $x$ and $y_2$, where $W_1$ and $W_2$ are the marginal channels of $W$.
]

This is stochastic degradedness: receiver 2 sees a noisier version of what receiver 1 sees.
It constrains only the marginal channels, and the achievable region depends only on these.

#open-problem("Capacity region of the broadcast channel", lean: "Meat.BC.MartonIsCapacity")[
  For all $a, b_1, b_2 in NN$ and every DMC $W$ from $[a]$ to $[b_1] times [b_2]$,
  $ overline(cal(A)(W)) = overline(cal(M)(W)). $
]

The problem is open since Cover (1972).
The inclusion $supset.eq$ is Marton's coding theorem.
Equality is known for degraded channels (Bergmans, 1973; Gallager, 1974; Ahlswede and Körner, 1975), less noisy channels (Körner and Marton, 1977), more capable channels (El Gamal, 1979), deterministic channels (Marton, 1977; Pinsker, 1978) and semideterministic channels (Gelfand and Pinsker, 1980).
In each of these classes the capacity region is equal to Marton's region.
No channel is known for which Marton's region is smaller than the capacity region.
The formulation with closures on both sides does not depend on whether the union $cal(M)(W)$ is closed.

#definition("Laws for the inclusions", lean: ("Meat.BC.martonLaw", "Meat.BC.uvLaw"))[
  Let $V$ be a finite set, $p_U in Delta(V)$ and $p_X : V -> Delta(A)$.
  Let $q_M$ be the law of $(U, X, *)$ on $V times A times {*}$, and let $q_O$ be the law of $(X, U)$ on $A times V$, where $(U, X)$ has the law $p_U (u) p_X (x given u)$.
]

#lemma(
  "Joint laws of the inclusions",
  lean: ("Meat.BC.jointMeasure_martonLaw", "Meat.BC.jointMeasure_uvLaw"),
)[
  Let $(U, X, Y_1, Y_2)$ have the law of the superposition region.
  With the input $p_X (t) := delta_x$ for $t = (u, x, *)$, the law of the Marton region for $q_M$ is the law of $((U, X, *), X, Y_1, Y_2)$.
  With the input $p_X (t) := delta_x$ for $t = (x, u)$, the law of the UV outer bound for $q_O$ is the law of $((X, U), X, Y_1, Y_2)$.
][
  Both sides are nested binds of $p_U$, $p_X$ and $W$, followed by a map.
  Binds are associative, so both sides reduce to the same nested bind.
]

#theorem(
  "Superposition is inside Marton and UV",
  lean: ("Meat.BC.superpositionRegion_subset_martonRegionOf", "Meat.BC.superpositionRegion_subset_uvRegionOf"),
)[
  For every finite $V$, $p_U in Delta(V)$ and $p_X : V -> Delta(A)$,
  $ cal(S)(p_U, p_X) subset.eq cal(M)(q_M, p'_X), quad cal(S)(p_U, p_X) subset.eq cal(O)(q_O, p''_X), $
  with the inputs $p'_X$ and $p''_X$ of the lemma on joint laws.
][
  Let $(R_1, R_2) in cal(S)(p_U, p_X)$.
  By the lemma on joint laws, each quantity of the Marton region is a quantity of $(U, X, Y_1, Y_2)$ with $T = U$, $V_1 = X$ and $V_2$ constant.
  A constant variable gives $I(V_2; Y_2 given T) = I(V_1; V_2 given T) = 0$ and $I(T, V_2; Y_2) = I(U; Y_2)$.
  So $S = I(X; Y_1 given U)$.
  By the chain rule, $I(U, X; Y_1) = I(U; Y_1) + I(X; Y_1 given U) = I(X; Y_1) + I(U; Y_1 given X)$.
  So $R_1 <= I(X; Y_1 given U) <= I(U, X; Y_1)$, and $R_1 + R_2 <= I(X; Y_1) <= I(U; Y_1) + S$.
  Also $R_2 <= I(U; Y_2)$ and $R_1 + R_2 <= I(U; Y_2) + S$.

  For the UV outer bound take $U = X$ and $V = U$.
  Then $R_1 <= R_1 + R_2 <= I(X; Y_1)$, and $R_1 + R_2 <= I(X; Y_1) + I(X; Y_2 given X)$ because conditional information is nonnegative.
  The other two bounds are the bounds of $cal(S)(p_U, p_X)$.
]

#lemma(
  "Relabeling auxiliary variables",
  lean: (
    "Meat.BC.jointMeasure_map_equiv",
    "Meat.BC.superpositionRegion_map_equiv",
    "Meat.BC.martonRegionOf_map_equiv",
    "Meat.BC.uvRegionOf_map_equiv",
  ),
)[
  Let $e : V -> V'$ be a bijection.
  The joint law for $e_* p_U$ and $p_X compose e^(-1)$ is the push-forward of the joint law for $p_U$ and $p_X$ by $e$ on the first coordinate.
  So $cal(S)(e_* p_U, p_X compose e^(-1)) = cal(S)(p_U, p_X)$.
  The same holds for the Marton region with bijections of $T$, $V_1$ and $V_2$, and for the UV outer bound with bijections of $V_1$ and $V_2$.
][
  The first statement is a computation with binds.
  Information under a push-forward is information of the composed variables.
  Entropy is invariant under injective maps, so each information term is unchanged.
]

#theorem(
  "Superposition union",
  lean: (
    "Meat.BC.superpositionUnion_subset_martonRegion",
    "Meat.BC.superpositionUnion_subset_uvRegion",
    "Meat.BC.superpositionUnion_subset_closure",
    "Meat.BC.closure_superpositionUnion_subset",
  ),
)[
  $ cal(S)(W) subset.eq cal(M)(W), quad cal(S)(W) subset.eq cal(O)(W), quad overline(cal(S)(W)) subset.eq overline(cal(A)(W)). $
][
  For the first two inclusions, apply the inclusions for one law.
  Then relabel $A$ as $[|A|]$, and the one-point set as $[1]$.
  The last inclusion is the superposition inner bound of Cover and Bergmans, and the closure of the achievable region is closed.
]

For a degraded channel, the closure of the achievable region is equal to $overline(cal(S)(W))$.
The inclusion $supset.eq$ is the last theorem.
The next section proves the converse inclusion.

== Degraded broadcast channels
#source("Meat.Open.BroadcastConverse")

This section proves the weak converse for the degraded broadcast channel (Gallager, 1974; Ahlswede and Körner, 1975).
With the superposition inner bound it gives the capacity region.
The proof replaces $W$ by a physically degraded channel with the same marginals.
Then it follows the chain rule with the auxiliary variable $U_i = (M_2, Y^(i - 1))$, where $Y = (Y_1, Y_2)$.
It ends with time sharing, so that one law of $(U, X, Y_1, Y_2)$ gives the bound.
All sets are finite.

#definition(
  "Degraded twin",
  lean: (
    "Meat.BC.degradedTwin",
    "Meat.BC.channel₁_degradedTwin",
    "Meat.BC.channel₂_degradedTwin",
    "Meat.BC.degradedTwin_apply",
  ),
)[
  Let $D$ be a DMC from $B_1$ to $B_2$.
  The degraded twin of $W$ is $W'(y_1, y_2 given x) := W_1 (y_1 given x) D(y_2 given y_1)$.
  Its first marginal is $W_1$.
  If $W$ is degraded through $D$, its second marginal is $W_2$.
]

#lemma("Regions depend on marginals", lean: "Meat.BC.superpositionRegion_congr")[
  If $W$ and $W'$ have the same marginal channels, then $cal(S)(p_U, p_X)$ is the same for $W$ and $W'$.
][
  $I(X; Y_1 given U)$ and $I(X; Y_1)$ are computed from the law of $(U, X, Y_1)$, which uses only $W_1$.
  $I(U; Y_2)$ is computed from the law of $(U, Y_2)$, which uses only $W_2$.
]

#definition(
  "Twin block code",
  lean: (
    "Meat.BC.twinCode",
    "Meat.BC.sum_error₁_le",
    "Meat.BC.sum_error₂_le",
    "Meat.BC.twinCode_errorProb_le",
    "Meat.BC.twinCode_avgError_le",
  ),
)[
  A broadcast code $(f, g_1, g_2)$ is also a block code with message $(m_1, m_2)$, encoder $f$ and decoder $(g_1, g_2)$ on the joint output.
  The error of receiver $j$ alone is at most $lambda_m$.
  If $W'$ has the same marginals as $W$, the error of the block code on $W'$ is at most $2 lambda_m$, and its average error is at most $2 overline(lambda)$.
]

#definition(
  "Padded prefixes and letter laws",
  lean: (
    "Meat.BC.padPrefix",
    "Meat.BC.padPrefix_injective",
    "Meat.BC.condEntropy_seq_pad",
    "Meat.BC.sum_codeMass",
    "Meat.BC.codePMF",
    "Meat.BC.codeMeasure_eq",
    "Meat.BC.letterPMF",
    "Meat.BC.letterPMF_toMeasure",
  ),
)[
  For $y in B^n$, $i in [n]$ and $d in B$, the padded prefix keeps $y_j$ for $j < i$ and puts $d$ elsewhere.
  It is an injective function of $(y_1, dots, y_(i - 1))$, and its values lie in one set for all $i$.
  The code law is the law of $(M, Y^n)$ with $M$ uniform.
  For a map $kappa$ on messages, the letter law at time $i$ is the law of $((kappa(M), "pad"_i (Y^n)), X_i, Y_i)$.
]

#lemma("Memoryless letters", lean: ("Meat.BC.sum_padPrefix", "Meat.BC.letterPMF_apply"))[
  The letter law has the form $q_i (u, x) W(y given x)$, where $q_i$ is the law of $(U_i, X_i)$.
][
  Fix the message.
  The condition on the padded prefix is a product of conditions on single coordinates.
  So the sum over $y^n$ of $W^n$ with this condition is a product of sums over single letters.
  At time $i$ the letter $y_i$ is free, and every later letter sums to $1$.
]

#lemma(
  "Mixtures",
  lean: ("Meat.BC.unifPMF", "Meat.BC.entropy_mixture", "Meat.BC.condEntropy_mixture", "Meat.BC.entropy_mixture_ge"),
)[
  Let $Q$ be uniform on $[n]$, and let $R$ have law $L_q$ given $Q = q$.
  Then $H(Q, Z(R)) = log n + n^(-1) sum_q H_(L_q) (Z)$.
  So $H(F(R) given Q, G(R)) = n^(-1) sum_q H_(L_q) (F given G)$, and $H(F(R)) >= n^(-1) sum_q H_(L_q) (F)$.
][
  The probability of $(q, t)$ is $n^(-1) L_q (Z = t)$.
  Split $eta(n^(-1) a) = n^(-1) eta(a) + a eta(n^(-1))$ and sum.
  The last inequality is $H(F) >= H(F given Q)$.
]

#lemma(
  "Laws with a channel factor",
  lean: (
    "Meat.BC.markovChain_of_pmf",
    "Meat.BC.jointPMF_eq_map",
    "Meat.BC.jointPMF_apply'",
    "Meat.BC.jointPMF_map_input",
    "Meat.BC.exists_jointPMF_eq",
    "Meat.BC.markovChain_of_memoryless",
    "Meat.BC.jointPMF_memoryless",
  ),
)[
  If the law of $(X, Y, Z)$ factors as the law of $(X, Y)$ times a kernel $kappa(z given y)$, then $X -> Y -> Z$.
  A law $sigma$ of $(U, X, Y)$ of the form $sigma(u, x) W(y given x)$ is the superposition law of some $p_U$ and $p_X$.
  Every superposition law has this form, so $U -> X -> (Y_1, Y_2)$.
][
  The first statement checks the criterion for Markov chains, after summing the factorization over $x$.
  For the second, take $p_U$ the law of $U$, and $p_X (x given u) := sigma(u, x) / p_U (u)$ when $p_U (u) > 0$.
]

#lemma("Sum rate of the degraded twin", lean: "Meat.BC.sum_le_of_degradedTwin")[
  For the degraded twin $W'$ and every superposition law,
  $ I(X; Y_1 given U) + I(U; Y_2) <= I(X; Y_1). $
][
  $U -> X -> Y_1$ gives $I(U; Y_1 given X) = 0$.
  The twin factors as $W_1 D$, so $(U, X) -> Y_1 -> Y_2$, hence $U -> Y_1 -> Y_2$ and $I(U; Y_2) <= I(U; Y_1)$.
  The chain rule gives $I(X; Y_1) = I(U; Y_1) + I(X; Y_1 given U)$.
]

#lemma(
  "Letter bounds",
  lean: ("Meat.BC.condEntropy_twin_letter", "Meat.BC.letter_bound₁", "Meat.BC.letter_eq₂"),
)[
  Under the code law on the twin, with $U_i = (M_2, "pad"_i (Y^n))$,
  $ H(Y_i given U_i) - H(Y_i given X_i) <= I_(q_i) (X; Y_1 given U), quad I_(q_i) (U; Y_2) = H(Y_(2, i)) - H(Y_(2, i) given U_i). $
][
  Split $H(Y_i given U_i) = H(Y_(1, i) given U_i) + H(Y_(2, i) given Y_(1, i), U_i)$, and drop $U_i$ in the second term.
  Split $H(Y_i given X_i)$ the same way, and use $X_i -> Y_(1, i) -> Y_(2, i)$ for the twin.
  The letter law is memoryless, so $H(Y_1 given X, U) = H(Y_1 given X)$ under $q_i$.
]

#theorem("Weak converse for one code", lean: "Meat.BC.code_bounds")[
  Let $overline(lambda)$ be the average error of a broadcast code of length $n$ on $W$, degraded through $D$.
  Then
  $ (1 - 2 overline(lambda)) log |M_1| - log 2 <= sum_i I_(q_i) (X; Y_1 given U), quad (1 - 2 overline(lambda)) log |M_2| - log 2 <= sum_i I_(q_i) (U; Y_2). $
][
  Use the twin block code on $W'$.
  $H(M_1, M_2) = log |M_1| + log |M_2|$ gives $log |M_1| <= H(M_1 given M_2)$ and $log |M_2| <= H(M_2)$.
  For receiver 1, $H(M_1 given M_2) = I(M_1; Y^n given M_2) + H(M_1 given Y^n, M_2)$.
  The second term is at most $H(M_1 given Y_1^n)$, which Fano bounds by $log 2 + 2 overline(lambda) log |M_1|$.
  The chain rule writes $I(M_1; Y^n given M_2) = sum_i (H(Y_i given U_i) - H(Y_i given X_i))$, and the letter bounds finish.
  For receiver 2, $I(M_2; Y_2^n) <= sum_i H(Y_(2, i)) - sum_i H(Y_(2, i) given U_i)$, by subadditivity, the chain rule and conditioning on more.
]

#theorem("Time sharing", lean: "Meat.BC.mixture_mem")[
  Let $L_1, dots, L_n$ be memoryless laws for the twin, and let $r_1, r_2 >= 0$ with $n r_1 <= sum_q I_(L_q) (X; Y_1 given U)$ and $n r_2 <= sum_q I_(L_q) (U; Y_2)$.
  Then $(r_1, r_2) in cal(S)(W)$.
][
  Mix the laws with a uniform $Q$, and take $(Q, U)$ as the new auxiliary variable.
  The mixture is memoryless, so it is a superposition law.
  By the mixture lemma, $I(X; Y_1 given Q, U)$ is the average, and $I(Q, U; Y_2)$ is at least the average.
  The sum rate bound of the twin gives the third constraint.
  The regions of $W$ and $W'$ agree, and relabeling puts the auxiliary set in the form $[k]$.
]

#theorem(
  "Capacity region of the degraded broadcast channel",
  lean: ("Meat.BC.achievableRegion_subset_of_isDegraded", "Meat.BC.closure_achievableRegion_eq_of_isDegraded"),
)[
  If $W$ is degraded, then $cal(A)(W) subset.eq overline(cal(S)(W))$, and
  $ overline(cal(A)(W)) = overline(cal(S)(W)). $
][
  Let $(R_1, R_2)$ be achievable and $delta > 0$.
  Take a code with small $overline(lambda)$ and large $n$, with $k_j >= e^(n R_j)$.
  The weak converse and time sharing put $r_j := max(0, (1 - 2 overline(lambda)) R_j - log 2 / n)$ in $cal(S)(W)$.
  Then $|R_j - r_j| <= 2 overline(lambda) R_j + log 2 / n < delta$.
  The other inclusion is the superposition inner bound.
]

== Relay channels
#source("Meat.Open.Relay")

A relay channel has a sender, a relay and a receiver.
The sender sends $X$, and the relay sends $X_1$.
The receiver sees $Y$, and the relay sees $Y_1$.
So a relay channel is a DMC $W$ from $A times A_1$ to $B times B_1$.
At each time the relay sends a function of what it has seen before.

#definition(
  "Relay code",
  lean: ("Meat.RelayCode", "Meat.RelayCode.seqProb", "Meat.RelayCode.errorProb", "Meat.RelayCode.avgError"),
)[
  Let $n in NN$ and let $M$ be a finite set.
  A relay code of length $n$ is a triple $(f, r, g)$ of an encoder $f : M -> A^n$, relay functions $r_i : B_1^n -> A_1$ for $i in [n]$, and a decoder $g : B^n -> M$.
  The relay functions are causal: $r_i (y_1^n)$ depends only on $y_(1, 1), dots, y_(1, i - 1)$.
  For $m in M$ and output sequences $(y^n, y_1^n)$, let
  $ P_m (y^n, y_1^n) := product_(i = 1)^n W(y_i, y_(1, i) given f(m)_i, r_i (y_1^n)). $
  The error probability is $lambda_m := sum_((y^n, y_1^n) : g(y^n) != m) P_m (y^n, y_1^n)$, and $overline(lambda) := |M|^(-1) sum_m lambda_m$.
]

Causality makes $P_m$ a probability mass function.
Lean keeps causality as a field of the code.

#definition("Achievable rate", lean: ("Meat.Relay.Achievable", "Meat.Relay.achievableRates"))[
  Achievability of a rate $R$ is defined as for a DMC, with relay codes in place of block codes.
  The set of achievable rates is the set of achievable $R >= 0$.
]

#definition("Direct transmission", lean: ("Meat.Relay.directChannel", "Meat.Relay.directCode"))[
  Fix a relay symbol $x_1 in A_1$.
  The direct channel is the DMC $W_(x_1) (y given x) := sum_(y_1) W(y, y_1 given x, x_1)$ from $A$ to $B$.
  A block code $(f, g)$ for $W_(x_1)$ gives the relay code $(f, r, g)$ with $r_i := x_1$ for all $i$.
  The constant relay functions are causal.
]

#theorem(
  "Direct transmission is achievable",
  lean: (
    "Meat.Relay.errorProb_directCode",
    "Meat.Relay.achievable_of_directChannel",
    "Meat.Relay.Icc_capacity_directChannel_subset",
  ),
)[
  The relay code of a block code $(f, g)$ has the same error probabilities on $W$ as $(f, g)$ on $W_(x_1)$.
  So every rate achievable for $W_(x_1)$ is achievable for $W$.
  If $A$ is nonempty, then $[0, C(W_(x_1))]$ is contained in the closure of the set of achievable rates of $W$.
][
  With constant relay functions, $P_m (y^n, y_1^n) = product_i W(y_i, y_(1, i) given f(m)_i, x_1)$.
  The error event depends only on $y^n$.
  Summing over $y_1^n$ turns the product into $W_(x_1)^n (y^n given f(m))$, by the lemma on block probabilities.
  The last statement is the channel coding theorem for $W_(x_1)$.
]

So the relay channel capacity is at least $max_(x_1) C(W_(x_1))$.

#definition(
  "Cut-set and decode-forward bounds",
  lean: (
    "Meat.Relay.cutSetRate",
    "Meat.Relay.decodeForwardRate",
    "Meat.Relay.cutSetBound",
    "Meat.Relay.decodeForwardBound",
  ),
)[
  For $p in Delta(A times A_1)$, let $(X, X_1, Y, Y_1)$ have the law $p(x, x_1) W(y, y_1 given x, x_1)$.
  Let
  $ R_"cs" (p) := min(I(X, X_1; Y), I(X; Y, Y_1 given X_1)), quad R_"df" (p) := min(I(X, X_1; Y), I(X; Y_1 given X_1)). $
  The cut-set bound is $C_"cs" := sup_p R_"cs" (p)$, and the decode-forward bound is $C_"df" := sup_p R_"df" (p)$.
]

Cover and El Gamal (1979) proved that every achievable rate is at most $C_"cs"$, and that every rate below $C_"df"$ is achievable.
The upper bound is proved in the last section of this chapter.
Decode-forward achievability is in Lean, in the sections on block-Markov relay codes below.
The theorem on direct transmission above is a simpler, weaker lower bound.

#definition("Degraded relay channel", lean: "Meat.Relay.IsDegraded")[
  The relay channel $W$ is physically degraded if there is a DMC $K$ from $A_1 times B_1$ to $B$ with
  $ W(y, y_1 given x, x_1) = W_1 (y_1 given x, x_1) K(y given x_1, y_1) $
  for all $x, x_1, y, y_1$, where $W_1$ is the marginal channel to the relay.
]

So $X -> (X_1, Y_1) -> Y$ is a Markov chain for every input law.

#definition("Cut-set tightness", lean: "Meat.Relay.CutSetTight")[
  The cut-set bound is tight for $W$ if the closure of the set of achievable rates is $[0, C_"cs"]$.
]

This property holds for physically degraded channels (Cover and El Gamal, 1979), for reversely degraded channels and for semideterministic channels (El Gamal and Aref, 1982).
It fails in general.
Aleksic, Razaghi and Yu (2009) found a relay channel whose capacity is strictly smaller than the cut-set bound.
So cut-set tightness is not the open problem.

#lemma("Relay output law", lean: "Meat.Relay.jointPMF_map_relayOutput")[
  The law of $((X, X_1), Y_1)$ is $p(x, x_1) W_1 (y_1 given x, x_1)$.
][
  The map forgets $Y$.
  A map of a bind is a bind of maps.
]

#theorem(
  "Decode-forward is below the cut-set bound",
  lean: (
    "Meat.Relay.decodeForwardRate_le_cutSetRate",
    "Meat.Relay.cutSetRate_le_log_card",
    "Meat.Relay.decodeForwardBound_le_cutSetBound",
  ),
)[
  For every $p$, $R_"df" (p) <= R_"cs" (p) <= log |B|$.
  So $C_"df" <= C_"cs"$.
][
  By the chain rule, $I(X; Y, Y_1 given X_1) = I(X; Y_1 given X_1) + I(X; Y given Y_1, X_1)$, and the last term is nonnegative.
  Also $R_"cs" (p) <= I(X, X_1; Y) <= H(Y) <= log |B|$.
  So the rates are bounded, and the suprema compare.
]

#theorem(
  "Degraded relay channel",
  lean: (
    "Meat.Relay.markovChain_of_isDegraded",
    "Meat.Relay.cutSetRate_eq_decodeForwardRate",
    "Meat.Relay.cutSetBound_eq_decodeForwardBound",
  ),
)[
  If $W$ is physically degraded, then $X -> (Y_1, X_1) -> Y$ is a Markov chain for every $p$.
  So $R_"cs" (p) = R_"df" (p)$ for every $p$, and $C_"cs" = C_"df"$.
][
  The probability of $(x, (y_1, x_1), y)$ is $p(x, x_1) W_1 (y_1 given x, x_1) K(y given x_1, y_1)$.
  The probability of $(x, (y_1, x_1))$ is $p(x, x_1) W_1 (y_1 given x, x_1)$, by the lemma on the relay output law.
  So the first factors as the second times a function of $(y_1, x_1)$ and $y$.
  Such a factorization gives the Markov chain, by the criterion for Markov chains.
  Then $I(X; Y given Y_1, X_1) = 0$, and the chain rule gives $I(X; Y, Y_1 given X_1) = I(X; Y_1 given X_1)$.
]

With the two coding theorems of Cover and El Gamal, this theorem gives the capacity $C_"cs" = C_"df"$ of the physically degraded relay channel.
The cut-set upper bound is in Lean, in the last section of this chapter.
Decode-forward achievability is in Lean too, so the capacity of the physically degraded relay channel is a Lean theorem: see the section on the capacity of the degraded relay channel.

#definition("Single-letter laws", lean: ("Meat.Relay.lawEntropy", "Meat.Relay.IsLaw"))[
  Let $k in NN$, and let the alphabets be $[a]$, $[a_1]$, $[b]$ and $[b_1]$.
  A law $q$ of $(U, X, X_1, Y, Y_1)$ with $U in [k]$ is a single-letter law for $W$ if the law of $(X, X_1, Y, Y_1)$ is $p(x, x_1) W(y, y_1 given x, x_1)$, where $p$ is the law of $(X, X_1)$.
  Number the five variables $0, dots, 4$.
  For $S subset.eq {0, dots, 4}$, $H_S (q)$ is the entropy of the variables in $S$ under $q$.
]

The variable $U$ may depend on all the others, so $U$ can play the role of a time-sharing variable, a cloud center or a compressed relay output.
In Lean, $H_S (q)$ is the entropy of the map that keeps the coordinates in $S$, encoded as natural numbers, and sends the others to $0$.

#open-problem("Capacity of the relay channel", lean: "Meat.Relay.SingleLetterCapacity")[
  There are a map $K : NN^4 -> NN$, numbers $J, J' in NN$ and integers $c_(j, S)$ for $j in [J]$ and $d_(j, S)$ for $j in [J']$, with $S subset.eq {0, dots, 4}$, with the following property.
  For all $a, a_1, b, b_1 in NN$ and every relay channel $W$ from $[a + 1] times [a_1 + 1]$ to $[b + 1] times [b_1 + 1]$, with $k := K(a, a_1, b, b_1)$, the closure of the set of achievable rates is $[0, C]$, where
  $ C := sup_q min_(j in [J]) sum_S c_(j, S) H_S (q) $
  and $q$ ranges over the single-letter laws for $W$ with $U in [k]$ and $sum_S d_(j, S) H_S (q) = 0$ for all $j in [J']$.
]

This is one precise reading of the question whether the relay channel has a single-letter capacity formula.
The formula is a maximum of a minimum of linear combinations of entropies, over one auxiliary variable with a bounded alphabet.
The constraints $d$ can state independence and Markov conditions, because these are linear equations in entropies.
The cut-set bound and the decode-forward bound have this form, with $U$ unused.
The compress-forward bound has this form with $U = hat(Y)_1$, the constraint $I(X; X_1) = 0$ and the Markov condition $hat(Y)_1 -> (X_1, Y_1) -> (X, Y)$.
The problem has been open since van der Meulen (1971).
The capacity is known for the physically degraded, reversely degraded and semideterministic relay channels, and for some classes of primitive relay channels.
The alphabets in the statement are nonempty, so that rate $0$ is achievable.

== Relay cut-set bound
#source("Meat.Open.RelayConverse")

This section proves the cut-set upper bound of Cover and El Gamal (1979).
The relay functions are causal, so the law of the outputs is not a product.
The proof first shows that every letter is still memoryless given the past.

#lemma("Causal sums", lean: ("Meat.prod_prefix_update", "Meat.sum_causal_prefix"))[
  Let $f_j (z, dot)$ be probability mass functions on $S$ that depend only on $z_1, dots, z_(j - 1)$.
  For every $k <= n$ and $a in S^n$,
  $ sum_(z : z_l = a_l, l < k) product_j f_j (z, z_j) = product_(j < k) f_j (a, a_j). $
][
  Induction on $n - k$.
  For $k = n$ only $z = a$ remains.
  For $k < n$, split the sum by the value $s$ of $z_k$, and apply the induction hypothesis to $a$ with $a_k$ replaced by $s$.
  The factor $f_k (a, s)$ sums to $1$ over $s$.
]

#definition(
  "Relay code law",
  lean: (
    "Meat.RelayCode.causal_seq",
    "Meat.RelayCode.sum_seqProb",
    "Meat.RelayCode.sum_codeMass",
    "Meat.RelayCode.codePMF",
    "Meat.RelayCode.measureReal_dec_ne",
  ),
)[
  Let $B$ and $B_1$ be nonempty.
  For each message, $P_m$ sums to $1$, by the lemma on causal sums with $k = 0$.
  The code law is the law of $(M, (Y^n, Y_1^n))$ with $M$ uniform.
  Under it the probability that $g(Y^n) != M$ is $overline(lambda)$.
]

#definition(
  "Relay letters",
  lean: (
    "Meat.RelayCode.letterPMF",
    "Meat.RelayCode.letterInput",
    "Meat.RelayCode.input",
    "Meat.RelayCode.isCausal",
    "Meat.RelayCode.letterPMF_apply",
    "Meat.RelayCode.letterPMF_eq",
    "Meat.RelayCode.letterLaw",
    "Meat.jointPMF_comp_input_map",
    "Meat.condEntropy_comp_input",
  ),
)[
  Let $Z_i := (Y_i, Y_(1, i))$ and $U_i := (M, "pad"_i (Z^n))$.
  The inputs at time $i$ are a function $(X_i, X_(1, i)) = g_i (U_i)$.
  The law of $(U_i, Z_i)$ is $q_i (u) W(z given g_i (u))$, by the lemma on causal sums with $k = i$ and $k = i + 1$.
  Let $p_i$ be the law of $g_i (U_i)$.
  For a channel $K$ composed with an input map $g$, $H(Z given U) = H(Z given g(U))$.
]

#lemma(
  "Relay letter entropies",
  lean: (
    "Meat.RelayCode.map_codePMF_input",
    "Meat.RelayCode.condEntropy_letter",
    "Meat.RelayCode.condEntropy_letter_fst",
  ),
)[
  The law of $(g_i (U_i), Z_i)$ is $p_i (x, x_1) W(z given x, x_1)$.
  Moreover, $H(Z_i given U_i)$ and $H(Y_i given U_i)$ are the conditional entropies of $Z$ and $Y$ given $(X, X_1)$ under this law.
][
  The first statement maps the letter law by $g_i$.
  The others follow from the lemma on channels composed with an input map, applied to $W$ and to its marginal channel to $Y$.
]

#theorem("Two cuts", lean: ("Meat.RelayCode.mutualInfo_le_sum₁", "Meat.RelayCode.mutualInfo_le_sum₂"))[
  Under the code law, with all information terms on the right under $p_i W$,
  $ I(M; Y^n) <= sum_i I(X, X_1; Y), quad I(M; Y^n) <= sum_i I(X; Y, Y_1 given X_1). $
][
  For the first cut, $H(Y^n) <= sum_i H(Y_i)$, and the chain rule gives $H(Y^n given M) >= sum_i H(Y_i given U_i)$.
  For the second cut, $I(M; Y^n) <= I(M; Z^n)$.
  The chain rule gives $H(Z^n) = sum_i H(Z_i given Z^(i - 1)) <= sum_i H(Z_i given X_(1, i))$, because $X_(1, i)$ is a function of $Z^(i - 1)$.
  It also gives $H(Z^n given M) = sum_i H(Z_i given U_i)$.
]

#lemma("Concavity in the input law", lean: "Meat.cutSet_mixture")[
  Let $overline(p)$ be the uniform mixture of $p_1, dots, p_n$.
  Then $n^(-1) sum_i I_(p_i) (X, X_1; Y) <= I_(overline(p)) (X, X_1; Y)$, and the same holds for $I(X; Y, Y_1 given X_1)$.
][
  In the mixture, $Q -> (X, X_1) -> (Y, Y_1)$.
  So $H(Z given X, X_1) = H(Z given Q, X, X_1)$, which is the average, and the same holds for $Y$.
  Also $H(Y) >= H(Y given Q)$ and $H(Z given X_1) >= H(Z given Q, X_1)$, and the right sides are averages.
]

#theorem(
  "Cut-set bound",
  lean: (
    "Meat.Relay.cutSetBound_nonneg",
    "Meat.Relay.one_sub_mul_log_card_le",
    "Meat.Relay.le_cutSetBound_of_achievable",
    "Meat.Relay.closure_achievableRates_subset",
    "Meat.Relay.closure_achievableRates_subset_of_isDegraded",
  ),
)[
  Let $B$ and $B_1$ be nonempty.
  For a relay code with $k$ messages and length $n >= 1$, $(1 - overline(lambda)) log k <= n C_"cs" + log 2$.
  Every achievable rate is at most $C_"cs"$, and the closure of the set of achievable rates is contained in $[0, C_"cs"]$.
  If $W$ is physically degraded, it is contained in $[0, C_"df"]$.
][
  Fano gives $log k - log 2 - overline(lambda) log k <= I(M; Y^n)$.
  The two cuts and concavity bound $I(M; Y^n)$ by $n R_"cs" (overline(p)) <= n C_"cs"$.
  The rest is the argument of the weak converse for the DMC.
  For a degraded channel, $C_"cs" = C_"df"$.
]
