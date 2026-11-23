#import "../meat.typ": *

= Network coding

== Single-source multicast
#source("Meat.Network.Coding")

A source sends the same message to a set of sinks.
The links of the network have no errors.
Each edge carries one symbol for each use.
Routing alone does not always achieve the min-cut.
Network coding achieves the min-cut, because intermediate nodes can combine their inputs.

#definition("Network", lean: ("Meat.Network", "Meat.Network.IsAcyclic"))[
  A network on a set $V$ is a map $c : V times V -> NN$.
  The number $c(u, v)$ is the number of edges from $u$ to $v$.
  The network is acyclic if there exists $r : V -> NN$ such that $r(u) < r(v)$ for all $u, v in V$ with $c(u, v) > 0$.
]

#definition("Cuts", lean: ("Meat.Network.cutValue", "Meat.Network.minCut"))[
  Let $V$ be finite.
  The value of $S subset.eq V$ is
  $ op("cut")(S) := sum_(u in S) sum_(v in V without S) c(u, v). $
  For $s, t in V$ with $s != t$,
  $ op("mincut")(s, t) := min {op("cut")(S) : S subset.eq V, s in S, t in.not S}. $
]

If $s = t$, no such set $S$ exists, and Lean gives the value $0$.

#definition("Network code", lean: ("Meat.Network.Code", "Meat.Network.Code.Decodes"))[
  Let $s in V$ and let $M$ and $F$ be sets.
  A network code with source $s$, message set $M$ and alphabet $F$ is a family of maps $e_(u v) : M -> F^(c(u, v))$, for $u, v in V$, with the property that follows.
  For all $u, v in V$ with $u != s$ there exists $phi_(u v) : product_(w in V) F^(c(w, u)) -> F^(c(u, v))$ with
  $ e_(u v)(m) = phi_(u v) ((e_(w u)(m))_(w in V)) quad "for all" m in M. $
  A node $t$ decodes if there exists $d : product_(w in V) F^(c(w, t)) -> M$ with $d((e_(w t)(m))_(w in V)) = m$ for all $m in M$.
]

On an acyclic network, this definition is equivalent to the usual recursive definition with local encoding functions.

== The cut-set bound
#source("Meat.Network.CutSetBound")

A cut separates the source from a sink.
Everything a sink sees must cross every such cut.
So the message set cannot be larger than the set of values that cross the cut.

#lemma("Information crosses the cut", lean: "Meat.Network.incoming_eq_of_cut")[
  Let the network be acyclic, let $(e_(u v))$ be a network code with source $s$, and let $S subset.eq V$ with $s in S$.
  Let $m, m' in M$ with $e_(u v)(m) = e_(u v)(m')$ for all $u in S$ and $v in.not S$.
  Then $e_(w v)(m) = e_(w v)(m')$ for all $v in.not S$ and $w in V$.
][
  Let $r$ be a rank function of the network.
  Use strong induction on $r(v)$.
  Let $v in.not S$ and $w in V$, and assume $c(w, v) > 0$, since otherwise there is nothing to show.
  If $w in S$, the claim is the hypothesis.
  Otherwise $w != s$, so $e_(w v)$ is a function of the symbols that enter $w$.
  Since $r(w) < r(v)$ and $w in.not S$, these symbols agree for $m$ and $m'$ by induction.
]

#theorem("Cut-set bound", lean: "Meat.Network.le_cutValue_of_decodes")[
  Let the network be acyclic, let $F$ be a finite set with at least two elements, and let $(e_(u v))$ be a network code with source $s$, message set $F^h$ and alphabet $F$.
  If $t$ decodes, then $h <= op("cut")(S)$ for every $S subset.eq V$ with $s in S$ and $t in.not S$.
][
  Let $D$ be the set of edges from $S$ to $V without S$, so $|D| = op("cut")(S)$.
  Map each message $m$ to the symbols $X(m) in F^D$ that it puts on $D$.
  If $X(m) = X(m')$, then by the lemma the symbols that enter $t$ agree, so decoding gives $m = m'$.
  Hence $X$ is injective and $|F|^h <= |F|^(op("cut")(S))$.
  Since $|F| >= 2$, $h <= op("cut")(S)$.
]

#corollary("Min-cut bound", lean: "Meat.Network.le_minCut_of_decodes")[
  In the same setting, if $s != t$ and $t$ decodes, then $h <= op("mincut")(s, t)$.
][
  Since $s != t$, the set ${s}$ is a cut, so the infimum is over a nonempty set.
  Each cut has value at least $h$ by the theorem.
]

== Linear codes
#source("Meat.Network.Linear")

A linear code puts a linear form $g_e$ on each edge $e$.
The edge carries $g_e (m)$ for the message $m in F^h$.
A node $u != s$ can compute the symbol on an edge out of $u$ if its form is in the span of the forms on the edges into $u$.
A node $t$ decodes if the forms on the edges into $t$ span the dual space.
The proof below chooses the forms one node at a time, in the order of the rank function.
It needs neither Menger's theorem nor polynomials.

#lemma("Avoiding subspaces", lean: "Meat.Network.exists_mem_forall_notMem")[
  Let $F$ be a finite field, let $I, U_1, dots, U_n$ be subspaces of an $F$-vector space with $I subset.eq.not U_k$ for every $k$, and let $n <= |F|$.
  Then there exists $y in I$ with $y in.not U_k$ for every $k$.
][
  Use induction on $n$.
  The case $n = 0$ is trivial.
  By induction there is $v in I$ outside $U_1, dots, U_(n-1)$.
  If $v in.not U_n$, we are done.
  Otherwise take $w in I without U_n$.
  No point $w + c v$ with $c in F$ is in $U_n$, since $v in U_n$ and $w in.not U_n$.
  Each $U_k$ with $k < n$ holds at most one of these points, since two of them would put $v$ in $U_k$.
  Since there are $|F| > n - 1$ points, one of them avoids every $U_k$.
]

#lemma("Adding a vector", lean: "Meat.Network.finrank_sup_span_singleton")[
  Let $U$ be a subspace of a finite-dimensional vector space, and let $y in.not U$.
  Then $dim(U + F y) = dim U + 1$.
][
  Since $y in.not U$, $y != 0$ and $U inter F y = 0$.
  Apply $dim(U + W) + dim(U inter W) = dim U + dim W$.
]

#lemma("Generic choice", lean: "Meat.Network.exists_generic")[
  Let $F$ be a finite field, let $I$ and $W_j$, for $j$ in a finite set $J$, be subspaces of a finite-dimensional $F$-vector space, and let $A$ be a finite set with $|J| dot 2^(|A|) <= |F|$.
  Then there exist $x_a in I$, for $a in A$, such that for all $j in J$ and $B subset.eq A$,
  $ dim(W_j + op("span") {x_a : a in B}) >= min(dim W_j + |B|, dim(W_j + I)). $
][
  Use induction on $A$.
  For $A = emptyset$, take all $x_a = 0$.
  To add a new element $a$, keep the vectors for the old set and consider the subspaces $U_(j, B) = W_j + op("span") {x_b : b in B}$ for old sets $B$ with $I subset.eq.not U_(j, B)$.
  There are at most $|J| dot 2^(|A| - 1) <= |F|$ of them, so the avoidance lemma gives $x_a in I$ outside all of them.
  Let $B$ contain $a$, and let $B_0 = B without {a}$.
  If $I subset.eq U_(j, B_0)$, then $W_j + I subset.eq U_(j, B_0) + F x_a$.
  Otherwise $x_a in.not U_(j, B_0)$, so the dimension grows by one, and the bound for $B_0$ gives the bound for $B$.
]

#theorem("Linear codes achieve the min-cut", lean: "Meat.Network.exists_code_of_le_minCut")[
  Let $V$ be finite, let the network be acyclic, let $s in V$, let $T subset.eq V$ with $s in.not T$, and let $h in NN$ with $op("mincut")(s, t) >= h$ for every $t in T$.
  Let $F$ be a finite field with $|F| >= 2^(|V| + sum_(u, v) c(u, v))$.
  Then there exists a network code with source $s$, message set $F^h$ and alphabet $F$ such that every $t in T$ decodes.
][
  For $P, Y subset.eq V$, let $W_P (Y)$ be the span of the forms on the edges from $P$ to $Y$.
  For a set $P$ of processed nodes and a choice of forms, consider these conditions:
  + every predecessor of a node $u in P$ with $u != s$ is in $P$;
  + for $u in P$ with $u != s$, the form on each edge out of $u$ is in the span of the forms on the edges into $u$;
  + for $t in T inter P$, the forms on the edges into $t$ span the dual space;
  + for every $S$ with $s in S$, $P subset.eq S$ and $T subset.eq.not S$,
    $ h <= dim W_P (V without S) + sum_(u in S without P) sum_(v in.not S) c(u, v). $
  For $P = emptyset$, the last condition is the min-cut hypothesis, and the others are empty.

  Now let $P != V$ satisfy the conditions.
  If $s in.not P$, let $u = s$.
  Otherwise let $u$ be a node outside $P$ of minimal rank, so all predecessors of $u$ are in $P$.
  Let $I$ be the whole dual space if $u = s$, and the span of the forms on the edges into $u$ otherwise.
  Apply the generic choice lemma with $W_S = W_P (V without S)$ for all $S subset.eq V$, and with $A$ the set of edges out of $u$.
  The bound on $|F|$ makes this possible.
  This gives new forms on the edges out of $u$, all in $I$, so condition (2) holds for $u$.
  The forms on the edges out of $P$ do not change.

  For condition (4) with $P union {u}$, fix $S$ with $u in S$.
  Let $k$ be the number of edges from $u$ to $V without S$, and let $r$ be the number of edges from $S without (P union {u})$ to $V without S$.
  Condition (4) for $S$ gives $h <= dim W_S + k + r$.
  If $u != s$, condition (4) for $S without {u}$ gives $h <= dim(W_S + I) + r$, because no edge enters $u$ from outside $P$.
  If $u = s$, the same bound holds because $W_S + I$ is the whole space.
  The generic choice bounds the dimension of $W_S$ plus the new forms below by $min(dim W_S + k, dim(W_S + I))$, and (4) follows.

  For condition (3) with $u in T$, apply (4) for $P$ with $S = V without {u}$.
  The sum is $0$, since all predecessors of $u$ are in $P$.
  So the forms on the edges into $u$ span a space of dimension at least $h$.

  After $|V|$ steps, $P = V$.
  Condition (2) makes the forms a network code, in which each local map is a linear combination.
  Condition (3) makes the map from the message to the symbols that enter $t$ injective, so $t$ decodes.
]

== Max-flow min-cut for network coding
#source("Meat.Network.Multicast")

#theorem(
  "Max-flow min-cut for network coding, Ahlswede, Cai, Li and Yeung",
  lean: "Meat.Network.multicast_iff",
)[
  Let $V$ be finite, let the network be acyclic, let $s in V$, let $T subset.eq V$ with $s in.not T$, and let $h in NN$.
  The following are equivalent:
  + $op("mincut")(s, t) >= h$ for every $t in T$;
  + there exist a finite field $F$ and a network code with source $s$, message set $F^h$ and alphabet $F$ such that every $t in T$ decodes.
][
  _(2) implies (1)._
  A field has at least two elements, and $s != t$ for every $t in T$, so the min-cut bound applies.

  _(1) implies (2)._
  Take a prime $p >= 2^(|V| + sum_(u, v) c(u, v))$ and $F = ZZ slash p ZZ$.
  Linear codes over $F$ achieve the min-cut.
]

The statement also holds for $h = 0$.
Then both sides are true, since $F^0$ has one element.



== Random linear network coding
#source("Meat.Network.RandomLinear")

This section proves that random linear network coding succeeds with high probability (Ho, Médard, Koetter, Karger, Effros, Shi and Leong, 2006).
Every node forwards random linear combinations of what it receives, and every sink inverts the resulting linear map.
The proof bounds the failure probability with the Schwartz-Zippel lemma.
The polynomial in the lemma is nonzero because a good linear code exists over a large extension field.

In this section, $N$ is an acyclic network on a finite set $V$, $s$ is the source and $T$ is a set of sinks with $s in.not T$.
Each sink has min-cut at least $h$ from $s$.
An edge is a triple $(u, v, i)$ with $i < c(u, v)$, and $E$ is the set of edges.

#definition(
  "Edges and incoming families",
  lean: (
    "Meat.Network.RLNC.Edge",
    "Meat.Network.RLNC.edg",
    "Meat.Network.RLNC.mem_edg",
    "Meat.Network.RLNC.card_edg",
    "Meat.Network.RLNC.inFam",
  ),
)[
  For sets $X$ and $Y$ of nodes, $E(X, Y)$ is the set of edges from $X$ to $Y$, and $|E(X, Y)| = sum_(u in X) sum_(v in Y) c(u, v)$.
  For a family $g$ indexed by edges and a node $u$, the incoming family of $u$ is the family of $g$ on the edges into $u$.
]

#theorem("Linear codes as families", lean: "Meat.Network.RLNC.exists_linear_family")[
  If $|F| >= 2^(|V| + |E|)$, there is a family $g$ of linear functionals on $F^h$, indexed by edges, such that
  every edge out of a node $u != s$ is in the span of the incoming family of $u$, and the incoming family of every sink spans the dual space.
][
  This is the construction of the section on linear codes, which builds the family one node at a time in a topological order.
  The construction itself is stated there for codes; here its output is kept as a family of functionals.
]

#definition(
  "Local coefficients and global vectors",
  lean: (
    "Meat.Network.RLNC.Idx",
    "Meat.Network.RLNC.src",
    "Meat.Network.RLNC.gIter",
    "Meat.Network.RLNC.gIter_succ",
    "Meat.Network.RLNC.glob",
  ),
)[
  A choice of local coefficients $beta$ gives, for each edge $e$ out of $u$, a coefficient $beta(e, k)$ for each source symbol $k in [h]$, used only if $u = s$, and a coefficient $beta(e, e')$ for each edge $e'$ into $u$.
  The global vectors are the fixed point of
  $ g_e = [u = s] (beta(e, k))_k + sum_(e' "into" u) beta(e, e') g_(e'). $
  Lean defines them by iterating this map $|V|$ times from $0$, over any commutative ring.
]

#lemma(
  "Global vectors are well defined",
  lean: (
    "Meat.Network.RLNC.pot",
    "Meat.Network.RLNC.pot_lt_card",
    "Meat.Network.RLNC.pot_lt",
    "Meat.Network.RLNC.gIter_succ_eq",
    "Meat.Network.RLNC.gIter_eq_of_le",
    "Meat.Network.RLNC.glob_eq",
    "Meat.Network.RLNC.glob_unique",
    "Meat.Network.RLNC.gIter_map",
    "Meat.Network.RLNC.glob_map",
  ),
)[
  Let the potential of a node be the number of nodes of smaller rank, so it is less than $|V|$ and grows along every edge.
  The iterates are constant from step $"pot"(u) + 1$ on, for every edge out of $u$.
  So the global vectors satisfy the fixed point equation, and they are its only solution.
  A ring homomorphism applied to the coefficients is applied to the global vectors.
][
  Induction on the number of steps: an edge into $u$ comes from a node of smaller potential.
  For uniqueness, the same induction compares the iterates with any solution.
]

#lemma(
  "Good coefficients over a large field",
  lean: (
    "Meat.Network.RLNC.coordMap",
    "Meat.Network.RLNC.coordMap_injective",
    "Meat.Network.RLNC.coordMap_surjective",
    "Meat.Network.RLNC.exists_spanning_coeffs",
  ),
)[
  If $|K| >= 2^(|V| + |E|)$, there are local coefficients over $K$ whose global vectors on the edges into every sink span $K^h$.
][
  Take the family of linear functionals of the previous theorem, and write each functional by its values on the unit vectors.
  At the source take the coordinates themselves as coefficients.
  At other nodes take the coefficients of the span relation.
  Then the coordinates solve the fixed point equation, so they are the global vectors.
  The coordinate map is a linear bijection, so the incoming families still span.
]

#lemma(
  "Spanning and determinants",
  lean: ("Meat.Network.RLNC.exists_det_ne_zero", "Meat.Network.RLNC.span_eq_top_of_det_ne_zero"),
)[
  A finite family in $L^h$ spans $L^h$ if and only if some $h$ of its vectors form a matrix with nonzero determinant.
][
  A spanning family contains a basis, of $h$ vectors.
  A matrix has nonzero determinant exactly when its rows are linearly independent, and $h$ independent vectors span $L^h$.
]

#lemma(
  "Determinant polynomials",
  lean: (
    "Meat.Network.RLNC.totalDegree_gIter",
    "Meat.Network.RLNC.detPoly",
    "Meat.Network.RLNC.totalDegree_detPoly",
    "Meat.Network.RLNC.eval_detPoly",
  ),
)[
  With the local coefficients as variables, every entry of a global vector is a polynomial of total degree at most $|V|$.
  For a sink $t$ and $h$ edges into $t$, the determinant of their global vectors is a polynomial of total degree at most $h |V|$, and evaluating it at a point gives the determinant of the global vectors at that point.
][
  Each iteration step multiplies by one variable.
  A determinant is a signed sum of products of $h$ entries.
  Evaluation is a ring homomorphism.
]

#theorem("Random linear network coding", lean: "Meat.Network.RLNC.card_fail_le")[
  Let $F$ be a finite field with $q$ elements, and choose the local coefficients uniformly at random from $F$.
  The probability that the global vectors into some sink fail to span $F^h$ is at most $|T| h |V| \/ q$.
][
  Let $p$ be the characteristic of $F$, and let $K$ be an extension of $F$ of degree $|V| + |E| + 1$, so $|K| >= 2^(|V| + |E|)$.
  Take good coefficients over $K$, and for each sink $h$ edges with a nonzero determinant there.
  The product $P$ of the determinant polynomials of the sinks is nonzero, because its value at the good coefficients is nonzero.
  It has total degree at most $|T| h |V|$.
  If $P$ does not vanish at the random coefficients, every determinant is nonzero and every sink spans.
  The Schwartz-Zippel lemma bounds the probability that $P$ vanishes by $deg P \/ q$.
]

#theorem(
  "Random linear codes decode",
  lean: ("Meat.Network.RLNC.linCode", "Meat.Network.RLNC.decodes_of_span", "Meat.Network.RLNC.card_not_decodes_le"),
)[
  The local coefficients define a network code in which edge $e$ carries the inner product of $g_e$ with the message.
  A sink whose incoming global vectors span $F^h$ decodes.
  So the probability that some sink cannot decode is at most $|T| h |V| \/ q$.
][
  The edges out of a node other than the source carry linear combinations of the incoming symbols, by the fixed point equation.
  If two messages give the same incoming symbols, their difference is orthogonal to every incoming vector, hence to $F^h$, so it is $0$.
]

== Cut-set bound for discrete memoryless networks
#source("Meat.Network.CutSet")

A discrete memoryless network has a finite set $V$ of nodes.
Every node $v$ sends a symbol $x_v in A$ and receives a symbol $y_v in B$ at each time, through a DMC $W$ from $A^V$ to $B^V$.
Node $s$ has a message for node $d != s$.
This section proves the cut-set bound of El Gamal (1981): every achievable rate is at most
$ sup_p min_(S : s in S, d in.not S) I(X_S; Y_(S^c) given X_(S^c)). $
The proof generalizes the second cut of the relay channel.

#definition(
  "Causal codes",
  lean: (
    "Meat.Causal.IsCausal",
    "Meat.Causal.seqProb",
    "Meat.Causal.sum_seqProb",
    "Meat.Causal.sum_codeMass",
    "Meat.Causal.codePMF",
  ),
)[
  Let $K$ be a DMC from $X$ to $S$, and let the input at time $i$ be a function of the message and of the outputs before time $i$.
  The sequence law $product_i K(z_i given x_i (m, z^(i - 1)))$ sums to $1$, and with a uniform message it gives the code law.
][
  This is the lemma on causal sums with no fixed prefix.
]

#lemma(
  "Memoryless letters of causal codes",
  lean: (
    "Meat.Causal.letterPMF",
    "Meat.Causal.letterInput",
    "Meat.Causal.letterPMF_apply",
    "Meat.Causal.letterPMF_eq",
    "Meat.Causal.letterLaw",
    "Meat.Causal.letterInput_pad",
    "Meat.Causal.map_codePMF_input",
    "Meat.Causal.condEntropy_letter",
  ),
)[
  Let $U_i := (M, "pad"_i (Z^n))$.
  The law of $(U_i, Z_i)$ is $q_i (u) K(z given x_i (u))$.
  So the law of $(X_i, Z_i)$ is $p_i K$, where $p_i$ is the law of $X_i$, and for every map $h$ on outputs, $H(h(Z_i) given U_i)$ is the conditional entropy of $h(Z)$ given $X$ under $p_i K$.
][
  This is the argument for relay letters, with a general input map: the lemma on causal sums with $k = i$ and $k = i + 1$, and the lemma on channels composed with an input map.
]

#definition(
  "Network codes",
  lean: (
    "Meat.DMN.Code",
    "Meat.DMN.Code.input",
    "Meat.DMN.Code.isCausal",
    "Meat.DMN.Code.errorProb",
    "Meat.DMN.Code.avgError",
    "Meat.DMN.Achievable",
    "Meat.DMN.achievableRates",
  ),
)[
  A network code of length $n$ gives every node $v$ and time $i$ a map from the message and the outputs of $v$ to $A$.
  Only the source may use the message, and the map uses only the outputs before time $i$.
  Node $d$ decodes from its outputs.
  Error probabilities and achievable rates are defined as for a DMC.
]

#definition(
  "Cut rates",
  lean: (
    "Meat.DMN.cutRate",
    "Meat.DMN.cutSetBound",
    "Meat.DMN.cutRate_eq",
    "Meat.DMN.cutRate_nonneg",
    "Meat.DMN.cutRate_le_log_card",
    "Meat.DMN.cutSetBound_nonneg",
  ),
)[
  For $p in Delta(A^V)$ and a set $S$ of nodes, the cut rate is $I(X_S; Y_(S^c) given X_(S^c))$ under $p W$.
  It equals $H(Y_(S^c) given X_(S^c)) - H(Y_(S^c) given X)$, and lies between $0$ and $log |B^(S^c)|$.
  The cut-set bound $C_"cs"$ is the supremum over $p$ of the minimum over cuts with $s in S$ and $d in.not S$.
]

#theorem("One cut", lean: "Meat.DMN.mutualInfo_le_sum_cut")[
  For every cut $S$ with $s in S$ and $d in.not S$, under the code law,
  $ I(M; Y_d^n) <= sum_i I(X_S; Y_(S^c) given X_(S^c)) $
  with the right side under $p_i W$.
][
  Let $Z := Y_(S^c)$.
  Then $I(M; Y_d^n) <= I(M; Z^n) = H(Z^n) - H(Z^n given M)$.
  The nodes outside $S$ do not see the message, so $X_(S^c, i)$ is a function of $Z^(i - 1)$, and $H(Z^n) <= sum_i H(Z_i given X_(S^c, i))$.
  The chain rule and conditioning on all past outputs give $H(Z^n given M) >= sum_i H(Z_i given U_i)$, which is $sum_i H(Z_i given X_i)$ by the lemma on memoryless letters.
]

#lemma("Concavity of cut rates", lean: "Meat.DMN.cutRate_mixture")[
  For the uniform mixture $overline(p)$ of $p_1, dots, p_n$, the average of the cut rates is at most the cut rate of $overline(p)$, for every $S$.
][
  This is the concavity lemma for the relay channel, with $X_1$ replaced by $X_(S^c)$ and $(Y, Y_1)$ by $Y_(S^c)$.
]

#theorem(
  "Cut-set bound",
  lean: (
    "Meat.DMN.measureReal_dec_ne",
    "Meat.DMN.one_sub_mul_log_card_le",
    "Meat.DMN.le_cutSetBound_of_achievable",
    "Meat.DMN.closure_achievableRates_subset",
  ),
)[
  Let $B$ be nonempty and $s != d$.
  For a network code with $k$ messages and length $n >= 1$, $(1 - overline(lambda)) log k <= n C_"cs" + log 2$.
  Every achievable rate is at most $C_"cs"$, and the closure of the set of achievable rates is contained in $[0, C_"cs"]$.
][
  Fano gives $log k - log 2 - overline(lambda) log k <= I(M; Y_d^n)$.
  For every cut, the bound for one cut and concavity give $I(M; Y_d^n) <= n I_S (overline(p))$.
  So $I(M; Y_d^n) <= n min_S I_S (overline(p)) <= n C_"cs"$.
  The rest is the argument of the weak converse for the DMC.
]
