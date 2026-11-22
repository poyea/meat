#import "../../meat.typ": *

== Distributed lossy source coding
#source("Meat.Open.DistributedLossy")

Two encoders observe two correlated sources $X$ and $Y$.
Each encoder sees only its own source.
One decoder reconstructs both sources, each within its own distortion.
Rates are in nats for each source symbol.
In this section, $S$, $T$, $U$ and $V$ are finite sets, $p$ is a probability mass function on $S times T$, and $d_1 : S times U -> RR$ and $d_2 : T times V -> RR$ are distortion measures.
For sequences, $d(x, hat(x)) := 1/n sum_(i = 1)^n d(x_i, hat(x)_i)$ is the block distortion of the rate-distortion chapter.

#definition(
  "Distributed lossy code",
  lean: ("Meat.DLCode", "Meat.DLCode.distortion₁", "Meat.DLCode.distortion₂"),
)[
  A distributed lossy code of length $n$ with $k_1$ and $k_2$ indices is a triple $(f_1, f_2, g)$ of maps
  $ f_1 : S^n -> [k_1], quad f_2 : T^n -> [k_2], quad g : [k_1] times [k_2] -> U^n times V^n. $
  Write $g = (g_1, g_2)$.
  Its expected distortions for $p$ are
  $ D_1 (c) := sum_((x, y)) p^n (x, y) d_1 (x, g_1 (f_1 (x), f_2 (y))), quad D_2 (c) := sum_((x, y)) p^n (x, y) d_2 (y, g_2 (f_1 (x), f_2 (y))). $
]

#definition("Joint code", lean: "Meat.DLCode.joint")[
  The joint code of $c$ is the lossy code for the source $S times T$ with $k_1 k_2$ indices.
  Its encoder sends the pair $(f_1 (x), f_2 (y))$ as one index in $[k_1 k_2]$.
  Its decoder is $g$, read letter by letter as a sequence in $(U times V)^n$.
]

#lemma("Distortion of the joint code", lean: "Meat.DLCode.joint_distortion")[
  For $a, b in RR$, the expected distortion of the joint code for the distortion measure $a d_1 + b d_2$ is $a D_1 (c) + b D_2 (c)$.
][
  Reindex the sum over $(S times T)^n$ as a sum over $S^n times T^n$.
  The block distortion is linear in the distortion measure.
]

#definition(
  "Achievable rates and distortions",
  lean: ("Meat.DistributedLossy.Achievable", "Meat.DistributedLossy.achievableRegion"),
)[
  A tuple $(R_1, R_2, D_1, D_2)$ is achievable if for every $epsilon > 0$ there exists $N$ such that for every $n >= N$ there exists a code of length $n$ with $k_i <= e^(n R_i)$, $D_1 (c) <= D_1 + epsilon$ and $D_2 (c) <= D_2 + epsilon$.
  The achievable region is the set of these tuples.
]

#definition(
  "Berger-Tung bounds",
  lean: ("Meat.DistributedLossy.bergerTungOuter", "Meat.DistributedLossy.bergerTungInner"),
)[
  Take finite auxiliary alphabets $[m_1]$ and $[m_2]$, a law $q$ of $(X, Y, U_1, U_2)$ whose $(X, Y)$ marginal is $p$, and maps $phi_1 : [m_1] times [m_2] -> U$ and $phi_2 : [m_1] times [m_2] -> V$.
  The rate conditions are
  $ R_1 >= I(X, Y ; U_1 given U_2), quad R_2 >= I(X, Y ; U_2 given U_1), quad R_1 + R_2 >= I(X, Y ; U_1, U_2), $
  and the distortion conditions are $EE d_1 (X, phi_1 (U_1, U_2)) <= D_1$ and $EE d_2 (Y, phi_2 (U_1, U_2)) <= D_2$.
  The outer bound uses the Markov chains $U_1 -> X -> Y$ and $U_2 -> Y -> X$.
  The inner bound uses the Markov chains $U_1 -> X -> (Y, U_2)$ and $U_2 -> Y -> (X, U_1)$.
  These two chains together are the long Markov chain $U_1 -> X -> Y -> U_2$.
  Under the long chain, $I(X, Y ; U_1 given U_2) = I(X ; U_1 given U_2)$, which is the usual form of the inner bound.
]

#definition("Cooperative bound", lean: "Meat.DistributedLossy.cooperativeRegion")[
  A tuple $(R_1, R_2, D_1, D_2)$ is in the cooperative region if for all $a, b >= 0$, the pair $(R_1 + R_2, a D_1 + b D_2)$ is in the rate-distortion region of the source $p$ on $S times T$ with the distortion measure $a d_1 + b d_2$.
]

#open-problem("Rate region of distributed lossy coding", lean: "Meat.DistributedLossyProblem")[
  For all finite $S$, $T$, $U$, $V$, all $p$ and all nonnegative $d_1$ and $d_2$, the closure of the achievable region is the closure of the Berger-Tung inner bound.
]

Berger (1977) and Tung (1978) gave the inner and outer bounds.
They differ only in the Markov conditions, and they are not known to coincide.
The inner bound is tight when one distortion is zero (Berger and Yeung, 1989).
The quadratic Gaussian two-terminal case is solved: Wagner, Tavildar and Viswanath (2008) proved that the Berger-Tung inner bound is tight there.
That case has continuous alphabets and is not in Lean.

#theorem("Inner bound in outer bound", lean: "Meat.DistributedLossy.bergerTungInner_subset_bergerTungOuter")[
  The Berger-Tung inner bound is a subset of the Berger-Tung outer bound.
][
  The rate and distortion conditions are the same.
  For the Markov conditions, the chain rule gives $I(U_1 ; Y, U_2 given X) = I(U_1 ; Y given X) + I(U_1 ; U_2 given Y, X)$.
  Both terms are nonnegative, so $I(U_1 ; Y, U_2 given X) = 0$ gives $I(U_1 ; Y given X) = 0$.
  The second chain is the same.
]

#lemma("Joint coding reduction", lean: "Meat.DistributedLossy.Achievable.joint")[
  Let $a, b >= 0$.
  If $(R_1, R_2, D_1, D_2)$ is achievable, then $(R_1 + R_2, a D_1 + b D_2)$ is achievable for the source $p$ with the distortion measure $a d_1 + b d_2$.
][
  Given $epsilon$, apply the hypothesis with $epsilon \/ (a + b + 1)$.
  The joint code has $k_1 k_2 <= e^(n (R_1 + R_2))$ indices.
  By the distortion lemma its distortion is at most $a D_1 + b D_2 + (a + b) epsilon \/ (a + b + 1) <= a D_1 + b D_2 + epsilon$.
]

#theorem(
  "Cooperative outer bound",
  lean: (
    "Meat.DistributedLossy.achievableRegion_subset_cooperativeRegion",
    "Meat.DistributedLossy.isClosed_cooperativeRegion",
    "Meat.DistributedLossy.closure_achievableRegion_subset_cooperativeRegion",
  ),
)[
  Let $U$ and $V$ be nonempty.
  The cooperative region is closed, and it contains the closure of the achievable region.
][
  By the reduction and the rate-distortion converse, each achievable tuple is in the region.
  The region is an intersection of preimages of closed rate-distortion regions under continuous maps, so it is closed.
]

The cooperative bound is the bound for one encoder that sees both sources.
It is weaker than the Berger-Tung outer bound, which the next section proves.

== The Berger-Tung converse
#source("Meat.Open.DistributedLossyConverse")

This section proves that the Berger-Tung outer bound contains the closure of the achievable region.
The proof is the converse of Berger (1977) and Tung (1978).
It uses the chain rules of the Shannon chapter, auxiliaries built from the indices and the past, and a time-sharing variable.
Fix a code $c = (f_1, f_2, g)$ of length $n >= 1$.
Let $Z^n = (X^n, Y^n)$ have the law $p^n$, and let $M_1 := f_1 (X^n)$ and $M_2 := f_2 (Y^n)$.
For each letter $i$, let
$ U_(1 i) := (M_1, Z^(i - 1)), quad U_(2 i) := (M_2, Z^(i - 1)). $
In Lean the past $Z^(i - 1)$ is stored as a sequence of length $n$ with a blank symbol after position $i - 1$, so all $U_(1 i)$ take values in one finite set.

The proof has four steps.

+ _Rates for each letter._
  $I(Z^n ; M_1 given M_2) <= H(M_1) <= log k_1$.
  By the chain rule, $I(Z^n ; M_1 given M_2) = sum_i I(Z_i ; M_1 given M_2, Z^(i - 1)) = sum_i I(Z_i ; U_(1 i) given U_(2 i))$.
  The second rate is the same.
  For the sum rate, $H(M_1, M_2) >= H(Z^n) - H(Z^n given M_1, M_2)$.
  The entropy of the i.i.d. sequence is $sum_i H(Z_i)$, and the chain rule splits $H(Z^n given M_1, M_2)$.
  This gives $log k_1 + log k_2 >= sum_i I(Z_i ; U_(1 i), U_(2 i))$.
+ _Markov chains for each letter._
  Under $p^n$, the letter $Z_i$ is independent of the other letters $Z_(-i)$, since the mass factors.
  The auxiliary $U_(1 i)$ is a function of $X_i$ and $Z_(-i)$.
  So $I(U_(1 i) ; Y_i given X_i) <= I(Z_(-i) ; Y_i given X_i) <= I(Z_(-i) ; Z_i) = 0$, which is the chain $U_(1 i) -> X_i -> Y_i$.
  The chain $U_(2 i) -> Y_i -> X_i$ is the same.
+ _Time sharing._
  Let $Q$ be uniform on $[n]$ and independent of $Z^n$.
  Let $(X, Y) := Z_Q$, $U_1 := (Q, U_(1 Q))$ and $U_2 := (Q, U_(2 Q))$, encoded as elements of finite sets $[m_1]$ and $[m_2]$.
  Since each $Z_i$ has the law $p$, the pair $(X, Y)$ has the law $p$.
  An entropy of a variable that contains $Q$ is $log n$ plus the average of the entropies for each letter, and an entropy of a variable whose law does not depend on $i$ is that common entropy.
  So each information quantity of the single-letter law is the average of the quantities for each letter.
  This gives the Markov chains, $I(X, Y ; U_1 given U_2) <= log k_1 \/ n$, $I(X, Y ; U_2 given U_1) <= log k_2 \/ n$ and $I(X, Y ; U_1, U_2) <= (log k_1 + log k_2) \/ n$.
+ _Distortion._
  The reconstruction $phi_1 (U_1, U_2)$ reads $Q$ and the two indices from the auxiliaries and returns letter $Q$ of $g_1 (M_1, M_2)$.
  Its expected distortion is the average over $i$ of the expected distortion of letter $i$, which is $D_1 (c)$.

#theorem("Converse for one code", lean: "Meat.DistributedLossy.code_mem_bergerTungOuter")[
  For a code of length $n >= 1$ with $k_1$ and $k_2$ indices, the tuple $(log k_1 \/ n, log k_2 \/ n, D_1 (c), D_2 (c))$ is in the Berger-Tung outer bound.
][
  The four steps above.
]

#lemma("Monotonicity", lean: "Meat.DistributedLossy.bergerTungOuter_mono")[
  If a tuple is in the Berger-Tung outer bound, then so is every tuple that is at least as large in each coordinate.
][
  All conditions are upper bounds on the information quantities and the distortions.
]

#theorem(
  "Berger-Tung converse",
  lean: (
    "Meat.DistributedLossy.mem_bergerTungOuter_of_achievable",
    "Meat.DistributedLossy.achievableRegion_subset_closure_bergerTungOuter",
    "Meat.DistributedLossy.closure_achievableRegion_subset_closure_bergerTungOuter",
  ),
)[
  If $(R_1, R_2, D_1, D_2)$ is achievable, then $(R_1, R_2, D_1 + delta, D_2 + delta)$ is in the Berger-Tung outer bound for every $delta > 0$.
  So the closure of the achievable region is a subset of the closure of the outer bound.
][
  Take a code of length $n = max(N, 1)$ for $delta$.
  Some $p(s, t) > 0$, so $k_1, k_2 >= 1$, and $k_i <= e^(n R_i)$ gives $log k_i \/ n <= R_i$.
  Apply the converse for one code and monotonicity.
  As $delta -> 0$, the points tend to the achievable tuple.
]

The outer bound is not known to be closed, because it has no bound on the sizes of the auxiliary alphabets in Lean.
So the closure appears on both sides.

== Multiple descriptions
#source("Meat.Open.MultipleDescriptions")

One encoder sends two descriptions of a source $X$.
A decoder that gets only description $j$ reconstructs $X$ within distortion $D_j$.
A decoder that gets both descriptions reconstructs $X$ within distortion $D_0$.
In this section, $S$ and $T$ are finite, $p$ is a probability mass function on $S$, and $d : S times T -> RR$ is a distortion measure.

#definition(
  "Multiple description code",
  lean: ("Meat.MDCode", "Meat.MDCode.side₁", "Meat.MDCode.side₂", "Meat.MDCode.central"),
)[
  A multiple description code of length $n$ is a tuple of maps
  $ f_1 : S^n -> [k_1], quad f_2 : S^n -> [k_2], quad g_0 : [k_1] times [k_2] -> T^n, quad g_1 : [k_1] -> T^n, quad g_2 : [k_2] -> T^n. $
  The side codes are the lossy codes $(f_1, g_1)$ and $(f_2, g_2)$.
  The central code is the lossy code with $k_1 k_2$ indices that sends the pair $(f_1 (x), f_2 (x))$ as one index and decodes with $g_0$.
]

#lemma("Central distortion", lean: "Meat.MDCode.central_distortion")[
  The expected distortion of the central code is $sum_x p^n (x) d(x, g_0 (f_1 (x), f_2 (x)))$.
][
  The index map $[k_1] times [k_2] -> [k_1 k_2]$ is a bijection.
]

#definition(
  "Achievable rates and distortions",
  lean: ("Meat.MultipleDescriptions.Achievable", "Meat.MultipleDescriptions.achievableRegion"),
)[
  A tuple $(R_1, R_2, D_0, D_1, D_2)$ is achievable if for every $epsilon > 0$ there exists $N$ such that for every $n >= N$ there exists a code of length $n$ with $k_i <= e^(n R_i)$, central distortion at most $D_0 + epsilon$, and side distortions at most $D_1 + epsilon$ and $D_2 + epsilon$.
  The achievable region is the set of these tuples.
]

#definition(
  "El Gamal-Cover region",
  lean: ("Meat.MultipleDescriptions.expectedDist", "Meat.MultipleDescriptions.elGamalCoverRegion"),
)[
  For a law $q$ of $(X, V)$ and a map $phi$ on $V$, the expected distortion is $sum_((x, v)) q(x, v) d(x, phi(v))$.
  The El Gamal-Cover region is the set of tuples such that some law $q$ of $(X, hat(X)_0, hat(X)_1, hat(X)_2)$ with $X$ marginal $p$ has $EE d(X, hat(X)_j) <= D_j$ for $j = 0, 1, 2$ and
  $ R_1 >= I(X ; hat(X)_1), quad R_2 >= I(X ; hat(X)_2), quad R_1 + R_2 >= I(X ; hat(X)_0, hat(X)_1, hat(X)_2) + I(hat(X)_1 ; hat(X)_2). $
]

#definition("Zhang-Berger region", lean: "Meat.MultipleDescriptions.zhangBergerRegion")[
  The Zhang-Berger region adds a common auxiliary $W$ in a finite set $[m]$.
  It is the set of tuples such that some law of $(X, W, hat(X)_0, hat(X)_1, hat(X)_2)$ with $X$ marginal $p$ has $EE d(X, hat(X)_j) <= D_j$ and
  $ R_1 >= I(X ; W, hat(X)_1), quad R_2 >= I(X ; W, hat(X)_2), $
  $ R_1 + R_2 >= 2 I(X ; W) + I(X ; hat(X)_0, hat(X)_1, hat(X)_2 given W) + I(hat(X)_1 ; hat(X)_2 given W). $
]

#definition("Outer bound", lean: "Meat.MultipleDescriptions.outerRegion")[
  The outer region is the set of tuples with $(R_1, D_1)$, $(R_2, D_2)$ and $(R_1 + R_2, D_0)$ in the rate-distortion region of $p$.
]

#open-problem("Multiple descriptions region", lean: "Meat.MultipleDescriptionsProblem")[
  For all finite $S$ and $T$, all $p$ and all nonnegative $d$, the closure of the achievable region is the closure of the Zhang-Berger region.
]

El Gamal and Cover (1982) proved that their region is achievable.
Zhang and Berger (1987) showed that a common description can do strictly better, so the El Gamal-Cover region is not tight in general.
The Zhang-Berger region is the best known inner bound for two descriptions, and whether it is tight is open.
Ahlswede (1985) showed that the El Gamal-Cover region is tight when there is no excess rate, that is, when $R_1 + R_2 = R(D_0)$.
Ozarow (1980) solved the quadratic Gaussian case, which has continuous alphabets and is not in Lean.

#lemma(
  "Each description is a lossy code",
  lean: (
    "Meat.MultipleDescriptions.Achievable.side₁",
    "Meat.MultipleDescriptions.Achievable.side₂",
    "Meat.MultipleDescriptions.Achievable.central",
  ),
)[
  If $(R_1, R_2, D_0, D_1, D_2)$ is achievable, then $(R_1, D_1)$, $(R_2, D_2)$ and $(R_1 + R_2, D_0)$ are achievable for the rate-distortion problem of $p$.
][
  Use the side codes and the central code.
  The central code has $k_1 k_2 <= e^(n R_1) e^(n R_2) = e^(n (R_1 + R_2))$ indices.
]

#theorem(
  "Outer bound",
  lean: (
    "Meat.MultipleDescriptions.achievableRegion_subset_outerRegion",
    "Meat.MultipleDescriptions.isClosed_outerRegion",
    "Meat.MultipleDescriptions.closure_achievableRegion_subset_outerRegion",
  ),
)[
  Let $T$ be nonempty.
  The outer region is closed, and it contains the closure of the achievable region.
][
  By the lemma and the rate-distortion converse, each achievable tuple is in the region.
  The rate-distortion region is closed, and the region is an intersection of its preimages under continuous maps.
]

#lemma("Single-letter points", lean: "Meat.MultipleDescriptions.mem_rateRegion_of_pmf")[
  Let $T$ be nonempty, and let $q$ be a law of $(X, V)$ with $X$ marginal $p$.
  If $EE d(X, phi(V)) <= D$ and $I(X ; phi(V)) <= R$, then $(R, D)$ is in the rate-distortion region of $p$.
][
  The law of $(X, phi(V))$ is $p$ followed by a channel $W$.
  Then $I(X ; phi(V))$ is the mutual information of $W$ at $p$, and the expected distortion is the expected distortion of $W$.
  The region contains every pair above such a point.
]

#theorem("El Gamal-Cover region in outer bound", lean: "Meat.MultipleDescriptions.elGamalCoverRegion_subset_outerRegion")[
  Let $T$ be nonempty.
  The El Gamal-Cover region is a subset of the outer region.
][
  The side conditions follow from the single-letter lemma.
  For the central condition, $I(X ; hat(X)_0) <= I(X ; hat(X)_0, hat(X)_1, hat(X)_2)$ by data processing, and $I(hat(X)_1 ; hat(X)_2) >= 0$.
  So $R_1 + R_2 >= I(X ; hat(X)_0)$, and the single-letter lemma applies.
]

The achievability of the El Gamal-Cover region is not yet in Lean.

== Secret key agreement
#source("Meat.Open.SecretKey")

Alice, Bob and Eve observe $n$ independent copies of $(X, Y, Z)$ with law $p$ on finite sets $S times T times E$.
Alice and Bob talk over a public channel that Eve hears.
At the end, each of them computes a key, and the keys should agree and be hidden from Eve.
This is the source model of Maurer (1993) and Ahlswede and Csiszár (1993).
In this section, $mu_n$ is the i.i.d. law of $n$ copies of $(X, Y, Z)$, and $X^n$, $Y^n$, $Z^n$ are its three sequences.

#definition(
  "Public discussion protocol",
  lean: (
    "Meat.SKProtocol",
    "Meat.SKProtocol.transcript",
    "Meat.SKProtocol.pub",
    "Meat.SKProtocol.keyAlice",
    "Meat.SKProtocol.keyBob",
    "Meat.SecretKey.eveSeq",
  ),
)[
  A protocol with $r$ rounds, messages in $[L]$ and keys in $[k]$ consists of message maps and key maps.
  In round $j$, the message is $a_j (x, tau)$ if $j$ is even and $b_j (y, tau)$ if $j$ is odd, where $tau in [L]^j$ is the transcript so far.
  The transcript $F in [L]^r$ is the sequence of all messages.
  The keys are $K_A := kappa_A (X^n, F)$ and $K_B := kappa_B (Y^n, F)$.
  The protocol is deterministic: Alice and Bob have no private randomness.
]

#definition(
  "Achievable key rate and capacity",
  lean: ("Meat.SecretKey.Achievable", "Meat.SecretKey.capacity"),
)[
  A rate $R$ is achievable if for every $epsilon > 0$ there exists $N$ such that for every $n >= N$ some protocol has $k >= e^(n (R - epsilon))$ and
  $ mu_n (K_A != K_B) <= epsilon, quad I(K_A ; Z^n, F) <= n epsilon, quad log k - H(K_A) <= n epsilon. $
  The secret key capacity $C_"SK" (p)$ is the supremum of the achievable rates.
]

The secrecy and uniformity conditions are the weak ones of Maurer (1993).
Maurer and Wolf (2000) showed that the strong conditions give the same capacity.

#definition("Intrinsic information", lean: "Meat.SecretKey.intrinsicInfo")[
  $ I(X ; Y arrow.b Z) := inf_(m, W) I(X ; Y given overline(Z)), $
  where $W$ runs over channels from $E$ to $[m]$ and $overline(Z)$ is the output of $W$ on input $Z$.
]

#open-problem("Bound information", lean: "Meat.BoundInformationProblem")[
  Some finite law $p$ has $I(X ; Y arrow.b Z) > 0$ and $C_"SK" (p) = 0$.
]

No single-letter formula for $C_"SK" (p)$ is known.
It satisfies $I(X ; Y) - I(X ; Z) <= C_"SK" (p) <= I(X ; Y arrow.b Z) <= I(X ; Y given Z)$.
The lower bound is the one-way rate of Maurer and of Ahlswede and Csiszár.
The intrinsic information bound is due to Maurer and Wolf (1999).
Renner and Wolf (2003) showed that the intrinsic information bound is not tight in general.
Gisin and Wolf (2000) asked whether bound information exists, as an analogue of bound entanglement.
For three or more parties it exists (Acín, Cirac and Masanes, 2004).
For two parties the question is open.

#theorem("Single letters", lean: "Meat.SecretKey.condMutualInfo_iid")[
  $ I(X^n ; Y^n given Z^n) = n I(X ; Y given Z). $
][
  Each entropy of a coordinatewise image of the sequence is $n$ times the entropy of the letter image.
  This is the marginal of an i.i.d. law and the entropy of an i.i.d. sequence.
  Pairs of sequences are relabeled as sequences of pairs.
  Expand the conditional mutual information into four entropies.
]

#lemma("Public discussion does not help", lean: "Meat.SecretKey.condMutualInfo_transcript_le")[
  For the transcript $F_j$ after $j$ rounds,
  $ I(X^n ; Y^n given Z^n, F_j) <= I(X^n ; Y^n given Z^n). $
][
  Induction on $j$.
  The transcript $F_0$ is constant.
  Let $C := (Z^n, F_j)$ and let $M$ be the message of round $j$.
  The pair $(C, M)$ is a relabeling of $(Z^n, F_(j + 1))$.
  If $M$ is a function of $(X^n, C)$, then
  $ I(X^n ; Y^n given C) - I(X^n ; Y^n given C, M) = I(M ; Y^n given C) >= 0. $
  If $M$ is a function of $(Y^n, C)$, the same holds with $X^n$ and $Y^n$ exchanged.
]

#lemma("Keys", lean: "Meat.SecretKey.condMutualInfo_keys_le")[
  $ I(K_A ; K_B given Z^n, F) <= n I(X ; Y given Z). $
][
  Let $C := (Z^n, F)$.
  If $A'$ is a function of $(A, C)$, then $I(A ; B given C) - I(A' ; B given C) = I(A ; B given A', C) >= 0$.
  Apply this to $K_A$ as a function of $(X^n, C)$, then to $K_B$ as a function of $(Y^n, C)$.
  Then use the lemma on public discussion with $j = r$ and the theorem on single letters.
]

#theorem("Converse for one protocol", lean: "Meat.SecretKey.log_card_le")[
  Let $P_e := mu_n (K_A != K_B)$.
  Then
  $ (1 - P_e) log k <= n I(X ; Y given Z) + log 2 + I(K_A ; Z^n, F) + (log k - H(K_A)). $
][
  Let $C := (Z^n, F)$.
  Then $H(K_A) = H(K_A given C) + I(K_A ; C)$ and $H(K_A given C) = I(K_B ; K_A given C) + H(K_A given K_B, C)$.
  Also $H(K_A given K_B, C) <= H(K_A given K_B) <= log 2 + P_e log k$ by Fano's inequality.
  Bound $I(K_A ; K_B given C)$ by the lemma on keys, and write $log k = H(K_A) + (log k - H(K_A))$.
]

#theorem("Upper bound", lean: "Meat.SecretKey.le_condMutualInfo_of_achievable")[
  Every achievable rate $R$ satisfies $R <= I(X ; Y given Z)$.
][
  Suppose $g := R - I(X ; Y given Z) > 0$, and let $epsilon := min(1/2, g \/ (2 (|R| + 4)))$.
  Take $n >= N$ with $log 2 < n epsilon$ and a protocol from the definition.
  Then $n (R - epsilon) <= log k$, and $1 - P_e >= 1 - epsilon >= 0$.
  The converse for one protocol gives $(1 - epsilon) n (R - epsilon) < n (I(X ; Y given Z) + 3 epsilon)$.
  Divide by $n$ and expand.
  This gives $g < epsilon (|R| + 4) <= g \/ 2$, a contradiction.
]

#theorem(
  "Capacity bounds",
  lean: ("Meat.SecretKey.achievable_zero", "Meat.SecretKey.capacity_le", "Meat.SecretKey.capacity_nonneg"),
)[
  The rate $0$ is achievable, and $0 <= C_"SK" (p) <= I(X ; Y given Z)$.
][
  For rate $0$, use no messages and the key set $[1]$.
  The keys agree, and the key has entropy $0 = log 1$, so it carries no information.
  The upper bound on achievable rates bounds the supremum.
]

The bound $C_"SK" (p) <= I(X ; Y arrow.b Z)$ is not yet in Lean.
The next section proves the one-way lower bound $C_"SK" (p) >= I(X ; Y) - I(X ; Z)$.

== The one-way lower bound
#source("Meat.Open.SecretKeyAchievability")

This section proves $C_"SK" (p) >= I(X ; Y) - I(X ; Z)$, the lower bound of Maurer (1993) and of Ahlswede and Csiszár (1993).
The protocol uses one message.
Alice bins her sequence $X^n$ twice: a public bin $F = f(X^n)$ that Bob can decode, and a key bin $K = kappa(X^n)$.
Bob recovers $X^n$ from $F$ and $Y^n$ with a Slepian-Wolf decoder, so he also knows $K$.
Secrecy follows from a genie argument: a decoder that saw $(F, K)$ and $Z^n$ could recover $X^n$.
So $(F, K)$ carries almost all of the information in $X^n$ that $Z^n$ does not have, and $F$ alone cannot reveal much of $K$.
For a law $q$ of a pair, let $J$ be its jointly typical set and $q^n (J)$ the probability of $J$.

#definition("Slepian-Wolf bound", lean: "Meat.SecretKey.swBound")[
  For a law $q$ of $(A, B)$, $gamma in RR$ and $k_1, k_2 in NN$,
  $ beta(q, n, gamma, k_1, k_2) := (1 - q^n (J)) + e^(n (H(A given B) + 2 gamma)) / k_1 + e^(n (H(B given A) + 2 gamma)) / k_2 + e^(n (H(A, B) + gamma)) / (k_1 k_2). $
  This is the bound of the random binning theorem of the source coding chapter.
]

#lemma("Two decoders share one bin", lean: "Meat.SecretKey.exists_binning_two")[
  Let $q_Y$ be a law of $(X, Y)$, let $q_Z$ be a law of $(X, Z)$, and let $k, L, K_2, K_3 >= 1$.
  Then there are maps $kappa : S^n -> [k]$, $f : S^n -> [L]$, $f_2 : T^n -> [K_2]$ and $g_2 : E^n -> [K_3]$ such that
  $ P_e^Y + P_e^Z <= beta(q_Y, n, gamma, L, K_2) + beta(q_Z, n, gamma, k L, K_3). $
  Here $P_e^Y$ is the error probability of the binning code with bins $f$ and $f_2$ for $q_Y$.
  $P_e^Z$ is the error probability of the binning code with bins $x |-> (kappa(x), f(x))$ in $[k L]$ and $g_2$ for $q_Z$.
][
  Average in two stages over the shared bin $f$.
  For each $f$, let $Phi(f)$ be the average of $P_e^Y$ over $f_2$, and let $Psi(f)$ be the average of $P_e^Z$ over $(kappa, g_2)$.
  The average of $Phi$ over $f$ is the random binning average for $q_Y$, so it is at most the first bound.
  The pair $(kappa, f)$ is a bijective relabeling of a uniform bin map into $[k L]$, so the average of $Psi$ over $f$ is the random binning average for $q_Z$.
  Some $f$ has $Phi(f) + Psi(f)$ at most the sum of the averages.
  Then some $f_2$ has $P_e^Y <= Phi(f)$ and some $(kappa, g_2)$ has $P_e^Z <= Psi(f)$.
]

#theorem("One-way lower bound", lean: "Meat.SecretKey.achievable_of_lt")[
  Every rate $R < I(X ; Y) - I(X ; Z)$ is achievable.
][
  If $R <= 0$, the rate $0$ is achievable, and a smaller rate is achievable too.
  Let $R > 0$.
  Then $I(X ; Y) - I(X ; Z) = H(X given Z) - H(X given Y) > R$.
  Given $epsilon > 0$, let $gamma := min(epsilon \/ 32, 1 \/ 4)$ and
  $ L := ceil(e^(n (H(X given Y) + 4 gamma))), quad k := ceil(e^(n (H(X given Z) - H(X given Y)))), quad K_2 := ceil(e^(n (log |T| + 1))), quad K_3 := ceil(e^(n (log |E| + 1))). $
  Then $k >= e^(n (R - epsilon))$, $k L >= e^(n (H(X given Z) + 4 gamma))$, and $log k + log L <= 2 log 2 + n (H(X given Z) + 4 gamma)$.
  With these sizes, each term of $beta$ after the first is at most $e^(-n gamma)$, so the sum of the two bounds tends to $0$ by the joint asymptotic equipartition property.
  Take the maps of the lemma.
  Alice sends $F = f(X^n)$ and keeps $K = kappa(X^n)$.
  Bob decodes $hat(X)^n$ from $F$ and $f_2 (Y^n)$ with the typical decoder and keeps $kappa(hat(X)^n)$.
  The keys differ only if the Slepian-Wolf decoder for $q_Y$ fails, so the error is at most $P_e^Y$.
  For secrecy, let $G := (F, K)$.
  Since $G$ is a function of $X^n$,
  $ H(X^n given Z^n) = H(G given Z^n) + H(X^n given G, Z^n) = H(F given Z^n) + H(K given F, Z^n) + H(X^n given G, Z^n). $
  The genie decoder recovers $X^n$ from $G$ and $Z^n$ with the code for $q_Z$, so Fano's inequality gives $H(X^n given G, Z^n) <= log 2 + P_e^Z n log |S|$.
  With $H(F given Z^n) <= log L$ and $H(X^n given Z^n) = n H(X given Z)$,
  $ H(K given F, Z^n) >= n H(X given Z) - log L - log 2 - P_e^Z n log |S|. $
  Then $I(K ; Z^n, F) = H(K) - H(K given F, Z^n)$ and $log k - H(K) <= log k - H(K given F, Z^n)$ are both at most $3 log 2 + 4 n gamma + P_e^Z n log |S|$.
  For large $n$ this is at most $n epsilon$.
]

#corollary("Capacity lower bound", lean: "Meat.SecretKey.sub_le_capacity")[
  $ I(X ; Y) - I(X ; Z) <= C_"SK" (p). $
][
  Otherwise some rate $R$ lies strictly between $C_"SK" (p)$ and $I(X ; Y) - I(X ; Z)$.
  It is achievable by the theorem, and the set of achievable rates is bounded above by $I(X ; Y given Z)$, so $R <= C_"SK" (p)$.
  This is a contradiction.
]

== The Courtade-Kumar conjecture
#source("Meat.Open.CourtadeKumar")

Let $X$ be uniform on ${0, 1}^n$, and let $Y$ be the output of $n$ uses of a binary symmetric channel with crossover probability $alpha$ on input $X$.
The conjecture says that no Boolean function of $X$ carries more information about $Y$ than one input bit.
In this section, $h$ is the binary entropy function in nats, and $0 <= alpha <= 1$.

#definition(
  "Binary symmetric pair",
  lean: (
    "Meat.CourtadeKumar.bscWeight",
    "Meat.CourtadeKumar.bscWeight_nonneg",
    "Meat.CourtadeKumar.sum_bscWeight",
    "Meat.CourtadeKumar.sum_negMulLog_bscWeight",
    "Meat.CourtadeKumar.bscPair",
    "Meat.CourtadeKumar.bscPair_toReal",
  ),
)[
  The channel weight is $w(b, c) := 1 - alpha$ if $b = c$ and $w(b, c) := alpha$ otherwise.
  It is nonnegative, $sum_b w(b, c) = 1$, and $sum_b eta(w(b, c)) = h(alpha)$.
  The pair law is $q(b, c) := w(b, c) \/ 2$ on ${0, 1}^2$.
  The law of $(X, Y)$ is $mu_n := q^n$, the Slepian-Wolf law of $n$ copies of $q$.
][
  Each claim is a case check on $c$.
]

#open-problem("Courtade-Kumar conjecture", lean: "Meat.CourtadeKumarConjecture")[
  For every $n$, every $alpha in [0, 1]$ and every $f : {0, 1}^n -> {0, 1}$,
  $ I(f(X) ; Y) <= log 2 - h(alpha). $
  In bits this is $I(f(X) ; Y) <= 1 - h_2 (alpha)$.
]

Courtade and Kumar (2014) posed the conjecture.
Dictator functions $f(x) = x_i$ attain the bound, as shown below.
Partial results are known: the bound holds for $alpha$ close to $1\/2$ (Samorodnitsky, 2016), and weaker constants hold for all $alpha$.
The general case is open.

#lemma("Law of a dictator and the output", lean: "Meat.CourtadeKumar.measureReal_dictator_pair")[
  For $i in [n]$, $b in {0, 1}$ and $y in {0, 1}^n$,
  $ mu_n (X_i = b, Y = y) = 2^(-n) w(b, y_i). $
][
  The mass of $(x, y)$ is $2^(-n) product_j w(x_j, y_j)$.
  Sum over $x$ with $x_i = b$.
  Each coordinate $j != i$ sums to $1$, and coordinate $i$ gives $w(b, y_i)$.
]

#lemma(
  "Entropies",
  lean: (
    "Meat.CourtadeKumar.entropy_dictator_pair",
    "Meat.CourtadeKumar.entropy_dictator",
    "Meat.CourtadeKumar.entropy_output",
  ),
)[
  $ H(X_i, Y) = h(alpha) + n log 2, quad H(X_i) = log 2, quad H(Y) = n log 2. $
][
  For $H(X_i, Y)$, use $eta(2^(-n) w) = 2^(-n) eta(w) + w eta(2^(-n))$ and sum over $b$ and then over $y$.
  The law of $Y$ is uniform, since $sum_b 2^(-n) w(b, y_i) = 2^(-n)$.
  The law of $X_i$ is uniform, since $sum_y 2^(-n) w(b, y_i) = 1\/2$.
]

#theorem(
  "Dictators attain the bound",
  lean: ("Meat.CourtadeKumar.mutualInfo_dictator", "Meat.CourtadeKumar.mutualInfoBits_dictator"),
)[
  For every $i in [n]$, $I(X_i ; Y) = log 2 - h(alpha)$.
  In bits, $I(X_i ; Y) = 1 - h(alpha) \/ log 2$.
][
  $I(X_i ; Y) = H(X_i) + H(Y) - H(X_i, Y) = log 2 + n log 2 - h(alpha) - n log 2$.
  Divide by $log 2$ for bits.
]
