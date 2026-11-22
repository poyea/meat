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

