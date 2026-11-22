#import "../../meat.typ": *

== The entropy region
#source("Meat.Open.EntropyRegion")

Take $n$ random variables on finite alphabets.
Their joint entropies, one for each subset of the variables, form a vector in $RR^(2^n)$.
The set of all such vectors is the entropy region.
Its closure describes every linear law that entropy obeys.
For $n <= 3$ the closure is the Shannon polymatroid cone.
For $n >= 4$ it is strictly smaller, and nobody knows what it is.

#definition("Entropy vector", lean: ("Meat.subvector", "Meat.entropyVector"))[
  Let $X_0, dots, X_(n-1) : Omega -> S$ be random variables on a finite alphabet $S$.
  For $A subset.eq {0, dots, n-1}$, the subvector $X_A$ is the map $omega |-> (X_i (omega))_(i in A)$.
  The entropy vector of the family is the map
  $ h_X : A |-> H(X_A). $
]

A common alphabet is no restriction, since finite alphabets embed into one large enough alphabet.
Lean measures entropy in nats.

#definition("Entropy region", lean: "Meat.entropyRegion")[
  $Gamma^*_n$ is the set of maps $h$ from subsets of ${0, dots, n-1}$ to $RR$ such that $h = h_X$ for some $k$ and some probability measure on $(op("Fin") k)^n$, where $X_i$ is the $i$-th coordinate.
]

#definition("Shannon outer bound", lean: "Meat.shannonRegion")[
  $Gamma_n$ is the set of polymatroids: maps $h$ with $h(emptyset) = 0$, $h(A) <= h(B)$ for $A subset.eq B$, and
  $ h(A union B) + h(A inter B) <= h(A) + h(B). $
]

#lemma("Measurability of subvectors", lean: "Meat.measurable_subvector")[
  If each $X_i$ is measurable, then each $X_A$ is measurable.
][
  A map into a product is measurable when each coordinate is.
]

#lemma("Polymatroid axioms", lean: ("Meat.entropyVector_empty", "Meat.entropyVector_mono", "Meat.entropyVector_submodular", "Meat.entropyVector_mem_shannonRegion"))[
  Let $mu$ be a probability measure and let each $X_i$ be measurable.
  Then $h_X(emptyset) = 0$, $h_X$ is monotone, and $h_X$ is submodular.
  So $h_X in Gamma_n$.
][
  $X_emptyset$ takes one value, so its entropy is $0$.
  If $A subset.eq B$, then $X_A$ is a function of $X_B$, so $H(X_A) <= H(X_B)$.
  For submodularity, apply $H(X, Y, Z) + H(Z) <= H(X, Z) + H(Y, Z)$ to $X = X_A$, $Y = X_B$ and $Z = X_(A inter B)$.
  Since $Z$ is a function of $X_A$ and of $X_B$, the right side is $H(X_A) + H(X_B)$.
  The triple $(X_A, X_B, X_(A inter B))$ is an injective relabeling of $X_(A union B)$, so the left side is $h_X(A union B) + h_X(A inter B)$.
]

#lemma("The entropy vector depends only on the law", lean: "Meat.entropyVector_eq_map")[
  $h_X$ under $mu$ equals the entropy vector of the coordinate variables under the joint law of $(X_0, dots, X_(n-1))$.
][
  Each $H(X_A)$ is the entropy of the push-forward measure, and $X_A$ factors through the joint map.
]

#lemma("Reindexing", lean: "Meat.entropyVector_map_emb")[
  Let $e : {0, dots, m-1} -> {0, dots, n-1}$ be injective.
  Then $h_X (e(A)) = h_(X compose e) (A)$.
][
  The subvectors $X_(e(A))$ and $(X compose e)_A$ are functions of each other, so they have the same entropy.
]

#theorem("Every entropy vector is entropic", lean: "Meat.entropyVector_mem_entropyRegion")[
  If $mu$ is a probability measure and each $X_i$ is measurable, then $h_X in Gamma^*_n$.
][
  Relabel $S$ as $op("Fin") |S|$ by a bijection $e$.
  This does not change any entropy.
  Then take the joint law of $(e compose X_0, dots, e compose X_(n-1))$ and use the previous lemma.
]

#theorem("Shannon outer bound", lean: ("Meat.entropyRegion_subset_shannonRegion", "Meat.isClosed_shannonRegion", "Meat.closure_entropyRegion_subset_shannonRegion"))[
  $Gamma^*_n subset.eq Gamma_n$.
  The set $Gamma_n$ is closed, so $overline(Gamma^*_n) subset.eq Gamma_n$.
][
  The first claim is the polymatroid lemma for the coordinate variables.
  Each axiom is an equation or a non-strict inequality between continuous functions of $h$, so $Gamma_n$ is an intersection of closed sets.
]

Write $I_h (A; B | C) = h(A union C) + h(B union C) - h(A union B union C) - h(C)$ and $I_h (A; B) = I_h (A; B | emptyset)$.
For an entropy vector these are the conditional mutual informations.

#definition("Zhang-Yeung region", lean: "Meat.zhangYeungRegion")[
  The set of $h$ on subsets of ${0, 1, 2, 3}$ with
  $ 2 I_h (2; 3) <= I_h (0; 1) + I_h (0; {2, 3}) + 3 I_h (2; 3 | 0) + I_h (2; 3 | 1). $
]

Lean writes this inequality with the values $h(A)$ expanded.

#lemma("The Zhang-Yeung region is closed", lean: "Meat.isClosed_zhangYeungRegion")[
  The Zhang-Yeung region is a closed set.
][
  Both sides are linear in $h$, so they are continuous.
]

#theorem("Zhang-Yeung inequality", lean: ("Meat.entropyRegion_subset_zhangYeungRegion", "Meat.closure_entropyRegion_subset_zhangYeungRegion", "Meat.entropyVector_mem_zhangYeungRegion"))[
  For four random variables $A, B, C, D$ on finite alphabets,
  $ 2 I(C; D) <= I(A; B) + I(A; C D) + 3 I(C; D | A) + I(C; D | B). $
  So $Gamma^*_4$ and its closure lie in the Zhang-Yeung region.
][
  Let $p$ be the joint law of $(A, B, C, D)$.
  Build a fifth variable $R$, a copy of $A$ over $(C, D)$, on the explicit product space with weights
  $ q(a, b, c, d, r) = p(a, b, c, d) dot p(A = r, C = c, D = d) / p(C = c, D = d), $
  with $q = 0$ when the denominator is $0$.
  Three facts follow by direct summation.
  The law of $(A, B, C, D)$ is unchanged.
  The pair $(R, (C, D))$ has the same law as $(A, (C, D))$.
  $R$ and $(A, B, C, D)$ are conditionally independent given $(C, D)$, by the factorization criterion for Markov chains.
  In terms of the entropy vector $g$ of $(A, B, C, D, R)$, indexed $0, dots, 4$, this gives
  $g{4} = g{0}$, $g{2,4} = g{0,2}$, $g{3,4} = g{0,3}$, $g{2,3,4} = g{0,2,3}$ and
  $ g{2,3,4} + g{0,1,2,3} = g{0,1,2,3,4} + g{2,3}. $
  Now add these eleven Shannon inequalities, each an instance of submodularity of $g$:
  $I(2;3|1,4)$, $I(0;4|1,2,3)$, $I(3;4|0,1)$, $I(0;4|2)$, $I(1;4|2)$, $I(2;3|0,4)$, $I(0;1|4)$, $I(0;4|3)$, $I(1;4|3)$, $I(2;4|0,1,3)$ and $I(1;4|0,2,3)$, all $>= 0$.
  With the five equations, the sum is the inequality.
  A small linear program found these coefficients.
  The values of $g$ on subsets of ${0, 1, 2, 3}$ are the values of the original vector, by reindexing.
  For the last claim, use that every entropy vector is entropic.
]

#theorem("The Shannon bound is not tight for four variables", lean: ("Meat.shannonRegion_not_subset_zhangYeungRegion", "Meat.closure_entropyRegion_ssubset_shannonRegion"))[
  There is a polymatroid on four elements that violates the Zhang-Yeung inequality.
  Hence $overline(Gamma^*_4) subset.neq Gamma_4$.
][
  Take $h(emptyset) = 0$, $h(A) = 2$ for singletons, $h{0,1} = 4$, $h(A) = 3$ for the other pairs, and $h(A) = 4$ for the larger sets.
  A finite check shows it is a polymatroid.
  Here $I_h (2;3) = 1$, $I_h (0;1) = 0$, $I_h (0;{2,3}) = 1$ and both conditional terms are $0$.
  So the left side is $2$ and the right side is $1$.
]

Zhang and Yeung (1998) found this first non-Shannon inequality.
Matúš (2007) found an infinite family of linear inequalities for $n = 4$ that are all needed, so $overline(Gamma^*_4)$ is not polyhedral.
No finite list of linear inequalities describes it, and no other explicit description is known.

#definition("Linear entropy functionals", lean: ("Meat.subsetCode", "Meat.entropyFunctional"))[
  Code a subset $A$ by the number $sum_(i in A) 2^i$.
  A list $c$ of integers gives the functional $h |-> sum_A c_(op("code")(A)) h(A)$, with missing entries read as $0$.
]

#open-problem("Decidability of information inequalities", lean: "Meat.InformationInequalitiesDecidable")[
  There is an algorithm that decides, for given $n$ and integer coefficients $c$, whether $sum_A c_A h(A) >= 0$ for all $h in Gamma^*_n$.
]

This is our formal reading of "describe $overline(Gamma^*_n)$ for $n >= 4$".
A functional is nonnegative on $Gamma^*_n$ if and only if it is nonnegative on the closure, so the question is about the closure.
A finite description would answer it, and Matúš's theorem rules out the simplest one.
Pippenger (1986) asked for the laws of information theory.
The question stays open even for $n = 4$.
For conditional information inequalities the analogous problem is undecidable (Li, 2023).
For Shannon-type inequalities it is decidable by linear programming (Yeung, 1997).

== Shannon capacity of graphs
#source("Meat.Open.GraphCapacity")

A channel can confuse some pairs of input letters.
Draw an edge between two letters that can be confused.
The zero-error capacity of the channel depends only on this confusability graph.
Shannon (1956) introduced it and computed it for all graphs on at most five vertices except the 5-cycle.

#definition("Strong product", lean: ("Meat.strongProd", "Meat.strongPow"))[
  In $G times.square H$, distinct pairs $(a, b)$ and $(c, d)$ are adjacent if $a = c$ or $a tilde c$, and $b = d$ or $b tilde d$.
  In the power $G^(times.square n)$ on words $V^n$, distinct words $x, y$ are adjacent if $x_i = y_i$ or $x_i tilde y_i$ for every $i$.
]

Two words of length $n$ are adjacent exactly when the channel can confuse them.
So an independent set in $G^(times.square n)$ is a zero-error code of length $n$.

#definition("Shannon capacity", lean: "Meat.shannonCapacity")[
  With $alpha$ the independence number,
  $ Theta(G) := sup_(n >= 1) alpha(G^(times.square n))^(1 \/ n). $
]

By Fekete's lemma this supremum is also the limit, since $alpha$ is supermultiplicative.
The zero-error capacity in nats is $log Theta(G)$.

#theorem("Supermultiplicativity", lean: ("Meat.mul_indepNum_le_strongProd", "Meat.pow_indepNum_le_strongPow"))[
  $alpha(G) alpha(H) <= alpha(G times.square H)$ and $alpha(G)^n <= alpha(G^(times.square n))$.
][
  The product of independent sets is independent.
  Two distinct words of the product differ in some coordinate, and there they are distinct and not adjacent.
]

#lemma("Trivial upper bound", lean: ("Meat.indepNum_strongPow_le", "Meat.shannonCapacity_le_card"))[
  $alpha(G^(times.square n)) <= |V|^n$, so $Theta(G) <= |V|$.
][
  An independent set is a set of words.
]

#theorem("Independence number bound", lean: ("Meat.rpow_indepNum_le_shannonCapacity", "Meat.indepNum_le_shannonCapacity"))[
  For every $n >= 1$, $alpha(G^(times.square n))^(1\/n) <= Theta(G)$.
  In particular $alpha(G) <= Theta(G)$.
][
  The terms are bounded by $|V|$, so the supremum is an upper bound of each.
  For $n = 1$, use $alpha(G) <= alpha(G^(times.square 1))$.
]

#theorem("Lower bound for the 5-cycle", lean: "Meat.sqrt_five_le_shannonCapacity_cycleGraph_five")[
  $sqrt(5) <= Theta(C_5)$.
][
  The words $(i, 2i op("mod") 5)$ for $i = 0, dots, 4$ are independent in $C_5^(times.square 2)$.
  If two first letters are adjacent, the second letters differ by $2$, so they are distinct and not adjacent.
  So $alpha(C_5^(times.square 2)) >= 5$.
]

#definition("Orthonormal representation", lean: "Meat.OrthoRep")[
  An orthonormal representation of $G$ in $RR^d$ is a family of unit vectors $u_v$, $v in V$, and a unit vector $c$, the handle, with $u_v perp u_w$ whenever $v != w$ are not adjacent.
]

#definition("Lovász theta", lean: "Meat.lovaszTheta")[
  $ theta.alt(G) := inf {t >= 0 : "some orthonormal representation has" t chevron.l u_v, c chevron.r^2 >= 1 "for all" v}. $
]

This is $min_(u, c) max_v 1 \/ chevron.l u_v, c chevron.r^2$ in Lovász's form.

#theorem("Lovász bound", lean: ("Meat.indepNum_strongPow_le_of_orthoRep", "Meat.shannonCapacity_le_of_orthoRep", "Meat.shannonCapacity_le_lovaszTheta"))[
  If an orthonormal representation of $G$ has $t chevron.l u_v, c chevron.r^2 >= 1$ for all $v$, with $t >= 0$, then $alpha(G^(times.square n)) <= t^n$ for all $n$, and $Theta(G) <= t$.
  Hence $Theta(G) <= theta.alt(G)$ for every nonempty finite $G$.
][
  For a word $x$, let $U_x$ be the tensor product $u_(x_1) times.o dots times.o u_(x_n)$, and let $C = c times.o dots times.o c$.
  Lean writes these as functions on $(op("Fin") d)^n$, so that $chevron.l U_x, U_y chevron.r = product_i chevron.l u_(x_i), u_(y_i) chevron.r$.
  Two distinct words of an independent set $S$ have a coordinate where the letters are distinct and not adjacent, so $U_x perp U_y$.
  Hence the $U_x$, $x in S$, are orthonormal.
  Bessel's inequality gives $sum_(x in S) chevron.l U_x, C chevron.r^2 <= |C|^2 = 1$.
  Each term is $product_i chevron.l u_(x_i), c chevron.r^2 >= t^(-n)$, so $|S| <= t^n$.
  For the last claim, the standard basis with the handle $|V|^(-1\/2)(1, dots, 1)$ is a representation with $t = |V|$, so the infimum is over a nonempty set.
]

#theorem("Lovász (1979)", lean: ("Meat.shannonCapacity_cycleGraph_five", "Meat.lovaszTheta_cycleGraph_five_le", "Meat.lovaszTheta_cycleGraph_five"))[
  $Theta(C_5) = theta.alt(C_5) = sqrt(5)$.
][
  Use Lovász's umbrella in $RR^3$ with handle $c = (0, 0, 1)$.
  Let $r = sqrt(5)$, $sigma = sqrt(1 - r\/5)$ and $tau = sqrt(r\/5)$.
  Put $u_k = (sigma cos(2 pi k \/ 5), sigma sin(2 pi k \/ 5), tau)$.
  Lean writes the cosines and sines with $(r - 1)\/4$, $(r + 1)\/4$, $sqrt(10 + 2r)\/4$ and $sqrt(10 - 2r)\/4$, so no trigonometry is needed.
  Each $u_k$ is a unit vector.
  Non-adjacent vertices differ by $2$ modulo $5$, and then $chevron.l u_k, u_(k+2) chevron.r = -sigma^2 (r+1)\/4 + tau^2 = 0$.
  Also $sqrt(5) chevron.l u_k, c chevron.r^2 = r tau^2 = 1$.
  So the Lovász bound gives $Theta(C_5) <= sqrt(5)$ and $theta.alt(C_5) <= sqrt(5)$.
  The lower bound for the 5-cycle and $Theta <= theta.alt$ give the equalities.
]

#open-problem("Shannon capacity of the 7-cycle", lean: "Meat.ShannonCapacityCycleSeven")[
  $ Theta(C_7) = (7 cos(pi\/7)) / (1 + cos(pi\/7)). $
]

The right side is $theta.alt(C_7) approx 3.3177$ (Lovász, 1979), so it is an upper bound.
The best lower bound is $367^(1\/5) approx 3.2578$ (Polak and Schrijver, 2019).
Whether $Theta(C_7)$ equals $theta.alt(C_7)$ is open, and so is its value.
We state the equality as the open proposition, since neither it nor its negation is known.

#definition("Graphs from codes", lean: "Meat.graphOfCode")[
  A number $m$ and a list $E$ of pairs of numbers give the graph on ${0, dots, m-1}$ where $i tilde j$ if $i != j$ and $(i, j)$ or $(j, i)$ is in $E$.
]

#open-problem("Computability of the Shannon capacity", lean: "Meat.ShannonCapacityComputable")[
  There is a computable map that sends a graph $(m, E)$ and $k$ to a rational number within $1\/(k+1)$ of $Theta(G)$.
]

Each $alpha(G^(times.square n))$ is computable, so $Theta(G)$ can be approximated from below.
No computable upper bounds that converge to $Theta(G)$ are known.
Alon and Lubetzky (2006) showed that $alpha(G^(times.square n))^(1\/n)$ can behave irregularly in $n$.

== The binary deletion channel
#source("Meat.Open.Deletion")

The binary deletion channel deletes each input bit independently with probability $d$.
The receiver sees the remaining bits in order, without their positions.
Dobrushin (1967) showed that the capacity is the limit of the normalized block capacities.

#definition("Deletion channel", lean: ("Meat.keepPMF", "Meat.deletionOutput", "Meat.encodeOutput", "Meat.deletionChannel"))[
  For $d in [0, 1]$, the keep pattern $K in {0, 1}^n$ has independent coordinates with $P(K_i = 1) = 1 - d$.
  The output for input $x in {0, 1}^n$ is the list $(x_i)_(i : K_i = 1)$, in order.
  Lean encodes a list of length at most $n$ as its length and its bits padded with zeros, in $op("Fin") (n+1) times {0, 1}^n$.
  The $n$-block deletion channel $W_n$ is the resulting map from $x$ to the law of the encoded output.
]

#definition("Deletion capacity", lean: "Meat.deletionCapacity")[
  $ C(d) := limsup_(n -> infinity) (C(W_n)) / n, $
  where $C(W_n)$ is the capacity of $W_n$ as a channel with input alphabet ${0, 1}^n$, in nats.
]

By Dobrushin's theorem the $limsup$ is a limit and equals the operational capacity.
Lean does not prove this.

#theorem("Trivial bounds", lean: ("Meat.capacity_deletionChannel_le", "Meat.deletionCapacity_nonneg", "Meat.deletionCapacity_le_log_two"))[
  $C(W_n) <= n log 2$, and $0 <= C(d) <= log 2$.
][
  Mutual information is at most the entropy of the input, which is at most $log 2^n$.
  It is also nonnegative.
  So $C(W_n)\/n in [0, log 2]$ for all $n$, and the $limsup$ stays in this interval.
]

#theorem("Erasure upper bound, one block", lean: ("Meat.inputMutualInfo_deletionChannel_le", "Meat.capacity_deletionChannel_le_erasure"))[
  For every input law on ${0, 1}^n$,
  $ I(X; Y) <= log(n + 1) + n (1 - d) log 2, $
  so $C(W_n) <= log(n + 1) + n (1 - d) log 2$.
][
  First $I(X; Y) <= H(Y)$, since $H(X) <= H(X, Y)$.
  Call an encoded output $(ell, z)$ valid if $z_j = 0$ for all $j >= ell$.
  Every output of the channel is valid, since the output list has length at most $n$.
  For each $ell$ there are at most $2^ell$ valid $z$: restriction to the first $ell$ coordinates is injective on them.
  Put $q(ell, z) = 2^(-ell) \/ (n + 1)$ on valid outputs and $q = 0$ elsewhere.
  Then $sum q <= sum_(ell = 0)^n 1 \/ (n + 1) = 1$, and $q > 0$ on the support of $Y$.
  Gibbs' inequality gives
  $ H(Y) <= -sum_y P(Y = y) log q(y) = log(n + 1) + log 2 dot EE[ell(Y)]. $
  The length of the output is the number of kept bits.
  For each input, its mean is $sum_i P(K_i = 1) = n (1 - d)$.
  Lean computes $P(K_i = 1)$ by factoring the sum over keep patterns into a product of one-letter sums.
]

#theorem("Erasure upper bound", lean: "Meat.deletionCapacity_le_erasure")[
  $C(d) <= (1 - d) log 2$.
][
  Divide the block bound by $n$.
  Since $log(n + 1) \/ n -> 0$, the upper sequence tends to $(1 - d) log 2$, and the $limsup$ of $C(W_n) \/ n$ is at most its limit.
]

This is the capacity of the binary erasure channel with erasure probability $d$.
The receiver of the deletion channel learns less than the receiver of the erasure channel, who also sees where the deletions are.
Lean does not use this comparison.
It bounds the output entropy directly.

#open-problem("Single-letter formula for the deletion channel", lean: "Meat.DeletionCapacitySingleLetter")[
  There are $k$, $m$ and polynomials $V_(a b)$ with rational coefficients such that for every $d in [0, 1]$ there is a channel $W$ from $op("Fin") k$ to $op("Fin") m$ with $W(b | a) = V_(a b)(d)$ and $C(d) = C(W)$.
]

This is one honest reading of "a single-letter formula": the capacity is the Shannon capacity of one fixed finite memoryless channel whose transition probabilities depend polynomially on $d$.
No such formula, and no closed form of any kind, is known.
The best results are bounds.
Known: $C(d) >= 1 - h(d)$ bits for $d <= 1\/2$ (Gallager, 1961), $C(d) >= (1 - d)\/9$ bits (Mitzenmacher and Drinea, 2006), $C(d) <= 1 - d$ bits as above, $C(d) = 1 - h(d) + O(d)$ as $d -> 0$ (Kanoria and Montanari, 2013), and numerical upper bounds (Fertonani and Duman, 2010; Rahmati and Duman, 2015).

== Network capacity with general demands
#source("Meat.Open.NetworkCapacity")

With one source and multicast demands, the min-cut is the capacity and linear codes reach it.
With several sources and arbitrary demands, neither statement holds.

#definition("Multi-source network code", lean: ("Meat.Network.MultiCode", "Meat.Network.MultiCode.Decodes"))[
  Let $m$ messages have source nodes $s_0, dots, s_(m-1)$.
  A code with message set $M$ and alphabet $F$ is a family of maps $e_(u v) : M^m -> F^(c(u,v))$ such that each $e_(u v)$ is a function of the symbols entering $u$ and of the messages with source $u$.
  Node $t$ decodes message $i$ if $M_i$ is a function of the symbols entering $t$ and of the messages with source $t$.
]

#definition("Solvability and capacity", lean: ("Meat.Network.Solvable", "Meat.Network.codingCapacity"))[
  A demand is a relation "node $t$ wants message $i$".
  The network is $(k, ell)$-solvable if for some $q >= 2$ there is a code with $M = (op("Fin") q)^k$ and $F = (op("Fin") q)^ell$ in which every demand is decoded.
  The coding capacity is $sup {k \/ ell : ell > 0, (k, ell)"-solvable"}$.
]

#definition("Linear codes", lean: ("Meat.Network.MultiCode.IsLinear", "Meat.Network.LinearSolvable"))[
  Over a field $K$, with $M = K^k$ and $F = K^ell$, a code is linear if every $e_(u v)$ is $K$-linear in the messages.
  The network is linearly solvable over $K$ if some linear code decodes every demand.
]

#definition("Encoded instances", lean: ("Meat.NetworkInstance", "Meat.NetworkInstance.network", "Meat.NetworkInstance.source", "Meat.NetworkInstance.demand", "Meat.NetworkInstance.capacity"))[
  An instance is a tuple $(n, E, s, D)$ of numbers and lists.
  It has nodes ${0, dots, n}$, $c(u, v)$ is the number of copies of $(u, v)$ in $E$, message $i$ has source $s_i op("mod") (n+1)$, and $t$ wants $i$ if $(t, i) in D$.
]

#open-problem("Computability of network coding capacity", lean: "Meat.NetworkCodingCapacityComputable")[
  There is a computable map that sends an acyclic instance and $k$ to a rational number within $1\/(k+1)$ of its coding capacity.
]

Whether the capacity of a general network is computable is open.
It is tied to the entropy region: the capacity is a linear optimization over $overline(Gamma^*_N)$ (Yan, Yeung and Zhang, 2007).
Li (2023) showed that the related problem of deciding solvability with conditional information constraints is undecidable.

#definition("Insufficiency of linear coding", lean: "Meat.LinearCodingInsufficient")[
  There is an acyclic instance that is $(1, 1)$-solvable, but for no finite field $K$ and no $k >= 1$ is it linearly $(k, k)$-solvable over $K$.
]

Dougherty, Freiling and Zeger (2005) proved this statement with an explicit network that is solvable over an alphabet of size $4$.
Lean states it but does not prove it, so it is a definition here.
It is not an open problem.
