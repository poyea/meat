#import "../meat.typ": *

= Learning paths

This chapter is a map of the book.
It gives three learning paths, the background that each path assumes, and a guide to the Lean statements.
Read the background sections that you need, then follow one path.
Come back to the guide to the Lean statements when a statement or a badge is not clear.

== What the book contains

The book has these chapters:
- _Shannon information measures_: entropy, mutual information, divergence, Markov chains, Fano's inequality, typical sequences and the method of types.
- _Worked examples_: numerical examples that use the definitions of the first chapter.
- _Source coding_: lossless codes, prefix codes, Huffman codes, rate-distortion and Slepian-Wolf coding.
- _Channel coding_: the channel coding theorem, multiple access channels and broadcast channels.
- _Network coding_: the cut-set bound and the max-flow min-cut theorem for multicast.
- _Continuous alphabets_: differential entropy, the Gaussian law and the Gaussian channel.
- _Hypothesis testing_: Stein's lemma, Sanov's theorem and Chernoff information.
- _Open problems_: problems that nobody has solved, with their known bounds and solved special cases.
- _Exercises_: graded exercises for each chapter.

Each definition and each theorem names the Lean declaration that it describes.
Lean is a proof assistant: it checks each proof down to the axioms.
The Lean library is the folder `Meat/` of the repository.
You do not need to read Lean to read this book.
The last section of this chapter explains how to read the Lean statements when you want to.

== Three learning paths

Each path is an ordered list of steps.
Each step names a chapter and some of its sections, and says what the step needs.
"Needs" lists the background sections of this chapter and the earlier steps that the step uses.
On a first reading, read the statements and the text between them, and skip a proof when it is long.
Then come back to the proofs.
Each path ends with the exercises of its chapters.

=== The undergraduate path

This path goes from the definition of entropy to the channel coding theorem.
It needs the mathematics of a strong second-year undergraduate: finite sums, logarithms, limits and induction.

+ *Background.*
  Read the sections on finite probability spaces, random variables, expectation, logarithms and convexity below.

+ *Shannon information measures*, sections "Entropy and mutual information" and "The same quantities in bits".
  You learn the definitions of $H(X)$, $H(X given Y)$, $I(X; Y)$ and $I(X; Y given Z)$, and the chain rule.

  _Needs:_ finite probability spaces, random variables, logarithms.

+ *Shannon information measures*, section "Shannon-type inequalities".
  Read the statements of "Range of entropy", "Basic inequalities", "Consequences", "Functions do not increase entropy" and "Data processing" first.
  Then read "Gibbs' inequality" and its proof, because most later proofs use it.
  The lemmas on push-forwards and the core inequality are technical, and you can skip their proofs at first.

  _Needs:_ step 2, the inequality $log t <= t - 1$, convexity.

+ *Worked examples*, all sections: binary entropy, the uniform law, the capacity of the binary symmetric channel and of the binary erasure channel, the noiseless channel, and a Huffman example.
  Do each computation yourself before you read the answer.

  _Needs:_ steps 2 and 3.

+ *Source coding*, sections "Prefix codes" and "Huffman codes".
  You learn the Kraft-McMillan inequality, the bound $H(p) <= L(c) log D$ on the expected length, and why Huffman codes are optimal.

  _Needs:_ step 3 (Gibbs' inequality), induction.

+ *Shannon information measures*, section "Typical sequences".
  You learn the asymptotic equipartition property and the size of the typical set.

  _Needs:_ expectation and Chebyshev's inequality, limits.

+ *Source coding*, sections "Lossless source coding" and "Variable-length source coding".
  These sections prove that $H(p)$ is the smallest rate for lossless coding.

  _Needs:_ step 6, limits and closure.

+ *Shannon information measures*, statements of the sections "Fano's inequality", "Averages" and "Sequences of random variables".
  The channel coding theorem uses Fano's inequality for its converse, and averages over random codebooks for its achievability.
  You can accept these statements now, and read their proofs on the graduate path.

  _Needs:_ step 3.

+ *Channel coding*, sections "Point-to-point channels", "Achievability", "Converse" and "Channel coding theorem".
  This is the main theorem of the path: the closure of the set of achievable rates is $[0, C(W)]$.

  _Needs:_ steps 6, 7 and 8, limits and closure.

=== The graduate path

This path covers the rest of the classical theory: lossy and distributed source coding, channels with two users, continuous alphabets and error exponents.
It assumes the undergraduate path.
Some steps also need measure theory or linear algebra, as listed.

+ *Shannon information measures*, section "Divergence".
  You learn $D(nu || rho)$, its chain rule, and that $I(X; Y)$ and $H(X)$ are divergences.

  _Needs:_ Gibbs' inequality, absolute continuity on a finite set (defined in the section).

+ *Shannon information measures*, sections "Markov chains" and "Fano's inequality", with all proofs.

  _Needs:_ step 1, the equality case of Gibbs' inequality.

+ *Shannon information measures*, sections "Averages", "Sequences of random variables", "I.i.d. sequences" and "Chain rules".

  _Needs:_ induction, sums over sequences.

+ *Shannon information measures*, section "The method of types".
  You learn to count sequences by their empirical distribution.

  _Needs:_ step 1, factorials and binomial coefficients, limits.

+ *Shannon information measures*, section "Tools for lossy coding".
  Then *Source coding*, sections "Rate-distortion coding", "Rate-distortion converse", "Rate-distortion achievability" and "Rate-distortion theorem".

  _Needs:_ convexity, the fact that a continuous function on a compact set attains its minimum, step 3.

+ *Shannon information measures*, section "Random binning".
  Then *Source coding*, sections "Slepian-Wolf coding", "Slepian-Wolf achievability", "Slepian-Wolf converse" and "Slepian-Wolf theorem".

  _Needs:_ typical sequences, step 2.

+ *Shannon information measures*, sections "Superposition typicality" and "Tools for two senders".
  Then *Channel coding*, sections "Multiple access channels", "Multiple access achievability", "Multiple access converse", "Multiple access theorem", "Broadcast channels" and "Broadcast achievability".
  Then *Open problems*, section "Degraded broadcast channels", which gives a solved case of the broadcast channel.

  _Needs:_ the channel coding theorem, convex hulls and time sharing, step 3.

+ *Continuous alphabets*, all sections in order: "Differential entropy", "Divergence for measures with densities", "Gaussian variables and channels", "Maximum entropy", "The AWGN channel", "AWGN converse", "AWGN achievability", "A lower bound on information", "Quantizers and one channel use" and "The AWGN coding theorem".

  _Needs:_ the Lebesgue integral, densities and the Radon-Nikodym derivative, Fubini's theorem, the Gaussian law, the channel coding theorem.

+ *Hypothesis testing*, sections "Stein's lemma", "Sanov's theorem" and "Chernoff information".

  _Needs:_ step 4, the weak law of large numbers (proved in the chapter), the intermediate value theorem.

=== The research path

This path goes to the edge of what is known.
It assumes the undergraduate path and steps 1 to 7 of the graduate path.
The aim is to understand the open problems well enough to work on them, in mathematics or in Lean.

+ *Network coding*, sections "Single-source multicast", "The cut-set bound", "Linear codes" and "Max-flow min-cut for network coding".

  _Needs:_ linear algebra over a finite field, the dimension formula $dim(U + W) + dim(U inter W) = dim U + dim W$, directed acyclic graphs.

+ *Open problems*, section "The entropy region".
  You learn the Shannon outer bound, the Zhang-Yeung inequality, and why the region for four variables is not known.

  _Needs:_ Shannon-type inequalities, submodular functions, the idea of a linear program.

+ *Open problems*, section "Shannon capacity of graphs".
  You learn the Lovász bound and the capacity of the 5-cycle.

  _Needs:_ graphs and independent sets, inner products, tensor products, Bessel's inequality.

+ *Open problems*, the rest of the chapter.
  Read the introduction of the chapter first: it explains how Lean states an open problem.
  Then read "Single-letter formulas", because several open problems ask for a single-letter formula.
  Then read the other sections in any order: "Broadcast channels", "Relay channels", "Relay cut-set bound", "Interference channels", "Two-way channels", "Multiple access channels with feedback", "Interactive codes", "The binary deletion channel", "Network capacity with general demands", "Distributed lossy source coding", "The Berger-Tung converse", "Multiple descriptions", "Secret key agreement", "The one-way lower bound", "The intrinsic information bound" and "The Courtade-Kumar conjecture".

  _Needs:_ the graduate path for the multi-user sections, step 1 for the network section.

+ *The repository*, file `docs/PLAN.md`.
  It lists the topics that are planned but not yet in Lean, and what each one needs.
  Each row is a possible project.

== Background

This section collects the mathematics that the paths assume.
It is a reminder, not a full course.
Each part ends with the places in the book that use it.

=== Finite probability spaces

A finite probability space is a finite set $Omega$ with a map $p : Omega -> [0, 1]$ such that $sum_(omega in Omega) p(omega) = 1$.
An event is a subset $A subset.eq Omega$, and its probability is $P(A) := sum_(omega in A) p(omega)$.
Then $P(Omega) = 1$, and $P(A union B) = P(A) + P(B)$ when $A$ and $B$ are disjoint.

The book works with a more general object.
A measure $mu$ on a set $Omega$ gives each measurable set $A$ a value $mu(A) in [0, infinity]$, and it is additive on countable disjoint unions.
A probability measure has $mu(Omega) = 1$.
On a finite set in which each singleton is measurable, a probability measure is the same as a map $p$ as above, with $p(omega) := mu({omega})$.
All alphabets in the book are finite, except in the chapter _Continuous alphabets_.
So you can think of every space as finite, until that chapter.

A probability mass function on a finite set $S$ is a map $p : S -> [0, 1]$ with $sum_s p(s) = 1$.
The book writes $Delta(S)$ for the set of probability mass functions on $S$.

_Used in:_ every chapter.

=== Random variables are maps

A random variable is a map $X : Omega -> S$ from the probability space to an alphabet $S$.
It is not a number that changes at random.
It is a fixed function, and the randomness is in the point $omega$.
The law of $X$ is the measure $X_* mu$ on $S$ with
$ (X_* mu)(A) := mu(X^(-1)(A)) = mu({omega : X(omega) in A}). $
It is also called the push-forward of $mu$ by $X$.
We write $P(X = s) := (X_* mu)({s})$.

Two random variables $X : Omega -> S$ and $Y : Omega -> T$ give the pair $(X, Y) : Omega -> S times T$, the map $omega |-> (X(omega), Y(omega))$.
A map $f : S -> T$ gives the random variable $f compose X$, often written $f(X)$.
$X$ and $Y$ are independent if $P(X = s, Y = t) = P(X = s) P(Y = t)$ for all $s$ and $t$.

Entropy depends only on the law.
So two random variables with the same law have the same entropy, even on different spaces.

_Used in:_ "Entropy and mutual information" and every later section.

=== Expectation

Let $X : Omega -> S$ with $S$ finite, and let $g : S -> RR$.
The expectation of $g(X)$ is
$ bb(E)[g(X)] := sum_(s in S) P(X = s) g(s). $
It is linear: $bb(E)[a g(X) + b k(X)] = a bb(E)[g(X)] + b bb(E)[k(X)]$ for $a, b in RR$ and $k : S -> RR$.
The variance of a real random variable $Y$ is $op("Var")(Y) := bb(E)[(Y - bb(E)[Y])^2]$.

Chebyshev's inequality says that for every $t > 0$,
$ P(|Y - bb(E)[Y]| >= t) <= op("Var")(Y) / t^2. $
For a sum of $n$ independent copies of $Y$, the variance is $n op("Var")(Y)$.
With $t = n epsilon$, this gives the weak law of large numbers: the average of the copies is within $epsilon$ of $bb(E)[Y]$ with probability at least $1 - op("Var")(Y) \/ (n epsilon^2)$.

The entropy of $X$ is an expectation.
Let $p(s) := P(X = s)$.
Then $H(X) = bb(E)[-log p(X)]$, where terms with $p(s) = 0$ count as $0$.

_Used in:_ "Typical sequences" (the asymptotic equipartition property is the weak law for $-log p(X)$), "Tools for lossy coding", "Stein's lemma".

=== Logarithms, nats and bits

In this book, $log$ is the natural logarithm, with base $e$.
The rules are $log(a b) = log a + log b$ and $log(a^k) = k log a$ for $a, b > 0$.
The most used inequality is
$ log t <= t - 1 quad "for every" t > 0, $
with equality only at $t = 1$.
It follows from the concavity of $log$: the line $t - 1$ is tangent to $log$ at $t = 1$.

Information measured with $log$ is in nats.
Information measured with $log_2$ is in bits, and $log_2 t = log t \/ log 2$.
So a quantity in bits is the quantity in nats divided by $log 2 approx 0.693$.
One bit is about $0.693$ nats, and one nat is about $1.443$ bits.
All results in the book are in nats, and the section "The same quantities in bits" transfers them to bits.

The function $t |-> t log t$ has no value at $t = 0$, but $t log t -> 0$ as $t -> 0$.
So the book sets $eta(t) := -t log t$ for $t > 0$ and $eta(0) := 0$.
Then $H(X) = sum_s eta(P(X = s))$.

A code with $k$ messages and block length $n$ has rate $R = (log k) \/ n$ nats per symbol.
Equivalently $k = e^(n R)$.
This is why the coding theorems compare $k$ with $e^(n R)$.

_Used in:_ every chapter.

=== Convexity and Jensen's inequality

A function $f : I -> RR$ on an interval $I$ is convex if
$ f(lambda x + (1 - lambda) y) <= lambda f(x) + (1 - lambda) f(y) $
for all $x, y in I$ and $lambda in [0, 1]$.
It is concave if $-f$ is convex.
A function with $f'' >= 0$ on $I$ is convex.
So $t |-> t log t$ is convex on $[0, infinity)$, and $log$ is concave on $(0, infinity)$.

Jensen's inequality extends the definition to many points.
If $f$ is convex, $x_1, dots, x_k in I$ and $w_1, dots, w_k >= 0$ with $sum_i w_i = 1$, then
$ f(sum_i w_i x_i) <= sum_i w_i f(x_i). $
In terms of a random variable $Y$ with values in $I$, this is $f(bb(E)[Y]) <= bb(E)[f(Y)]$.

Gibbs' inequality is the most important use in the book.
Let $p$ and $q$ be probability mass functions on $S$ with $q(s) > 0$ whenever $p(s) > 0$.
The concavity of $log$ gives
$ sum_(s : p(s) > 0) p(s) log (q(s) / p(s)) <= log sum_(s : p(s) > 0) q(s) <= log 1 = 0. $
The book proves the same result with $log t <= t - 1$ instead of Jensen's inequality.

A set $K subset.eq RR^k$ is convex if it contains the segment between any two of its points.
The convex hull of a set is the smallest convex set that contains it.
Convex hulls describe time sharing: a code can use one scheme for part of the time and another scheme for the rest.

_Used in:_ "Shannon-type inequalities", "Divergence", "Prefix codes", "Rate-distortion coding", "Multiple access channels", "Maximum entropy".

=== Limits, limsup and closure

A sequence $a_1, a_2, dots$ of real numbers tends to $a$ if for every $epsilon > 0$ there is $N$ with $|a_n - a| <= epsilon$ for every $n >= N$.
We write $a_n -> a$ or $lim_(n -> infinity) a_n = a$.
The phrase "for all large $n$" means "for every $n >= N$, for some $N$".
Most coding proofs end with a statement of this form.

The supremum $sup A$ of a set $A subset.eq RR$ is its least upper bound, and the infimum $inf A$ is its greatest lower bound.
A sequence need not have a limit.
Its limit superior is
$ limsup_(n -> infinity) a_n := lim_(N -> infinity) sup_(n >= N) a_n. $
The sequence $N |-> sup_(n >= N) a_n$ does not increase, so this limit always exists in $[-infinity, infinity]$.
For example, $a_n = (-1)^n$ has no limit, but $limsup_n a_n = 1$.
If $a_n -> a$, then $limsup_n a_n = a$.
The chapter _Open problems_ defines the capacity of the deletion channel as a $limsup$, because it is not known in Lean that the limit exists.

The closure $overline(A)$ of a set $A subset.eq RR^k$ is the set of all limits of sequences in $A$.
A set is closed if it is equal to its closure.
For example, the closure of $[0, C)$ is $[0, C]$, and $[0, C]$ is closed.

Coding theorems are stated with closures for the reason that follows.
A rate $R$ is achievable if, for every $epsilon > 0$ and all large $n$, some code of length $n$ with about $e^(n R)$ messages has error probability at most $epsilon$.
The converse proves that every achievable rate is in an information region, for example $[0, C(W)]$.
The achievability proof shows that every rate strictly inside the region is achievable.
These two facts leave out the boundary of the region.
A rate on the boundary may or may not be achievable, and the answer depends on finer estimates and on the exact definition of a code.
The closure does not see the difference: the closure of the achievable set is the whole region in either case.
So each coding theorem has the form
$ overline({"achievable rates"}) = "information region". $
The region is closed, and the statement is exactly what the two proofs give.

_Used in:_ "Lossless source coding", "Channel coding theorem", "Slepian-Wolf theorem", "Rate-distortion theorem", "Multiple access theorem", "The AWGN coding theorem", "The binary deletion channel".

== Reading the Lean statements

This section explains the badges, the Lean notation, the conventions that Lean uses, and how to find the Lean source of a statement.

=== Badges

Each definition and each theorem has a badge in its top right corner.
The build computes the badge from the Lean library, so it is never out of date.

- #badge("proved"): the Lean declaration exists, and Lean has checked its proof.
  No declaration that it uses contains `sorry`.
  For a definition, it means that the definition exists and uses no `sorry`.
- #badge("sorry"): the statement is in Lean, but its proof, or a proof that it uses, is the placeholder `sorry`.
  Lean accepts `sorry` as a proof of anything, so the statement is not yet checked.
- #badge("informal"): the statement is only in this book.
  The Lean library does not contain it, so nothing checks it.
  The book uses this badge for known results that are not yet formalized, such as the Han-Kobayashi inner bound.
- #badge("open"): the statement is an open problem.
  Lean states it as a named proposition, a `def ... : Prop`, and never as a theorem.
  Nothing in the library proves it or assumes it.
- #badge("missing"): the book names a Lean declaration that does not exist.
  This is an error in the book.

A proof that Lean has checked is a proof of the Lean statement, from the Lean definitions.
It is not a proof that the definitions say what the book says.
So read each definition and compare it with the text.
The book points out the places where the Lean definition differs from the usual one.

=== Notation

Most theorems show their statement twice: once as mathematics, and once as Lean source in a grey box.
When the text of a theorem is empty, the mathematics is generated from the Lean statement.
Then the line "_Assume ..._" lists the hypotheses of the Lean theorem.

The table gives the Lean notation that you meet most often.
Here $mu$ is a measure on $Omega$, $X : Omega -> S$, $Y : Omega -> T$ and $Z : Omega -> U$.

#table(
  columns: (auto, auto, 1fr),
  align: (left, left, left),
  stroke: none,
  table.hline(),
  [*Lean*], [*Book*], [*Meaning*],
  table.hline(stroke: 0.5pt),
  [`H[X ; μ]`], [$H(X)$], [Entropy of $X$ under $mu$, in nats.],
  [`H[X | Y ; μ]`], [$H(X given Y)$], [Conditional entropy, defined as $H(X, Y) - H(Y)$.],
  [`I[X : Y ; μ]`], [$I(X; Y)$], [Mutual information, defined as $H(X) + H(Y) - H(X, Y)$.],
  [`I[X : Y | Z ; μ]`], [$I(X; Y given Z)$], [Conditional mutual information.],
  [`H₂[X ; μ]`, `I₂[X : Y ; μ]`], [$H_2 (X)$, $I_2 (X; Y)$], [The same quantities in bits.],
  [`fun ω => (X ω, Y ω)`], [$(X, Y)$], [The pair of two random variables.],
  [`f ∘ X`], [$f(X)$], [A function of a random variable.],
  [`μ.map X`, `Measure.map X μ`], [$X_* mu$], [The law of $X$: the push-forward of $mu$ by $X$.],
  [`ν.real {s}`], [$nu({s})$], [The mass of the point $s$, as a real number.],
  [`ℝ≥0∞`], [$[0, infinity]$], [The extended nonnegative reals. Measures and probability mass functions take values here.],
  [`x.toReal`], [], [The real number of $x in [0, infinity]$, with $infinity$ sent to $0$.],
  [`PMF S`], [$Delta(S)$], [Probability mass functions on $S$. For `p : PMF S`, `p s` is in `ℝ≥0∞`.],
  [`p.toMeasure`], [$nu_p$], [The measure of a probability mass function.],
  [`Fintype.card S`], [$|S|$], [The number of elements of a finite set.],
  [`Fin n → S`], [$S^n$], [Sequences of length $n$. Lean numbers the positions $0, dots, n - 1$.],
  [`Real.log`, `Real.negMulLog`], [$log$, $eta$], [Natural logarithm and $eta(t) = -t log t$.],
  [`Real.binEntropy`], [$h$], [Binary entropy in nats.],
  [`klDiv ν ρ`], [$D(nu || rho)$], [Kullback-Leibler divergence.],
  [`ν ≪ ρ`], [$nu << rho$], [Absolute continuity: $rho(A) = 0$ implies $nu(A) = 0$.],
  [`MarkovChain X Y Z μ`], [$X -> Y -> Z$], [Markov chain, defined by $I(X; Z given Y) = 0$.],
  [`DMC A B`], [$A -> Delta(B)$], [Discrete memoryless channel.],
  [`closure A`], [$overline(A)$], [Closure of a set.],
  [`Set.Icc a b`], [$[a, b]$], [Closed interval.],
  [`Tendsto f atTop (𝓝 a)`], [$f(n) -> a$], [Limit as $n -> infinity$.],
  [`∀ᶠ n in atTop, P n`], [], [$P(n)$ holds for all large $n$.],
  table.hline(),
)

The square brackets in `H[X ; μ]` always name the measure $mu$.
The book often leaves $mu$ out, when only one measure is in use.

=== Achievable rates and regions

Here is the Lean definition of an achievable rate for a channel $W$, from `Meat/Channel/Basic.lean`.

```lean
def Achievable [Fintype B] (W : DMC A B) (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : BlockCode (Fin k) A B n, c.avgError W ≤ ε
```

Read it from left to right:
for every $epsilon > 0$, there is $N$ such that for every $n >= N$, there are a number $k >= e^(n R)$ of messages and a block code of length $n$ for the messages ${0, dots, k - 1}$ with average error probability at most $epsilon$.
The error probability is in `ℝ≥0∞`, because it is a sum of probabilities in `ℝ≥0∞`.

The channel coding theorem in Lean is

```lean
closure {R : ℝ | 0 ≤ R ∧ Achievable W R} = Set.Icc 0 (capacity W)
```

This is $overline({R >= 0 : R "achievable"}) = [0, C(W)]$.
Every other coding theorem has the same pattern.
An achievable region is a set of rate pairs instead of rates.
Its information region is a set in $RR^2$ described by inequalities between mutual informations, such as the pentagon of the multiple access channel.

=== Lean conventions

Lean is a total language: every function has a value at every input.
So some expressions that have no value in mathematics have a value in Lean.
The book points them out where they matter.

- $log 0 = 0$, and $log x = log |x|$ for $x < 0$.
- $x \/ 0 = 0$.
- The infimum or supremum of an empty set of reals is $0$, and so is the supremum of an unbounded set.
  This is why the capacity $C(W) := sup_p I(p)$ needs the lemma that the set of values $I(p)$ is bounded.
- For real powers, $0^0 = 1$.
  The chapter _Hypothesis testing_ avoids this in the definition of Chernoff information.
- `x.toReal` sends $infinity$ to $0$.
- In the natural numbers, subtraction stops at $0$: $3 - 5 = 0$.
- Positions in a sequence of length $n$ are $0, dots, n - 1$, while the book writes $1, dots, n$.

A hypothesis in a Lean statement often rules out one of these cases.
For example, `[Fintype S]` says that $S$ is finite, `[MeasurableSingletonClass S]` says that each singleton of $S$ is measurable, `[IsProbabilityMeasure μ]` says that $mu(Omega) = 1$, and `(hX : Measurable X)` says that $X$ is measurable.

=== Finding the Lean source

There are four ways to go from a statement in the book to its Lean source.

+ The grey box under a statement shows the declaration name and a link of the form `file:line`.
  The link opens the file in the repository at that line.
+ Each section starts with a link to its Lean file.
  A module name maps to a path: `Meat.Shannon.Entropy` is the file `Meat/Shannon/Entropy.lean`.
+ A declaration name has a namespace part and a last part.
  For example, `Meat.DMC.closure_achievable_eq` is declared as `theorem closure_achievable_eq` inside `namespace DMC`, in the file `Meat/Channel/CodingTheorem.lean`.
  To find it, search for the last part: `grep -rn "closure_achievable_eq" Meat`.
+ The _Uses_ line under a statement lists the statements of the book that its Lean proof uses.
  Follow these links to go down the proof.

The book ends with the section "Lean coverage".
In strict mode, the build checks that each declaration of the library is in some statement of the book.

To run Lean yourself, install Lean with `elan`, clone the repository, run `lake exe cache get` to download a compiled Mathlib, and run `lake build`.
Then open a file in an editor with the Lean extension.
When you put the cursor in a proof, the editor shows the hypotheses and the goal at that point.
