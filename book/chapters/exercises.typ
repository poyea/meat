#import "../meat.typ": *

#let exercise-count = counter("meat-exercise")
#let exercise-answers = state("meat-exercise-answers", ())
#let exercise-levels = (
  basic: (word: "basic", color: rgb("#2e7d32")),
  intermediate: (word: "intermediate", color: rgb("#1a4f8b")),
  advanced: (word: "advanced", color: rgb("#6a1b9a")),
)

#let exercise(level, title: none, hint: none, answer: none, compare: (), formalize: false, body) = {
  exercise-count.step()
  context {
    let number = str(counter(heading).get().at(1, default: 0)) + "." + str(exercise-count.get().first())
    let l = exercise-levels.at(level)
    let names = if type(compare) == str { (compare,) } else { compare }
    block(width: 100%, breakable: true, above: 1.3em, below: 1.3em, {
      grid(
        columns: (1fr, auto),
        column-gutter: 1em,
        [*Exercise #number*#if title != none [ (#title)]],
        text(size: 8.5pt, fill: l.color)[#l.word#if formalize [, formalize]],
      )
      v(-0.3em)
      body
      if hint != none {
        block(above: 0.7em, text(size: 9.5pt)[_Hint._ #hint])
      }
      if names.len() > 0 {
        block(above: 0.6em, text(size: 9pt)[_In Lean:_ #names.map(n => raw(n)).join(", ")])
      }
    })
    if answer != none {
      exercise-answers.update(a => a + ((number, title, answer),))
    }
  }
}

= Exercises

Each section of this chapter has exercises for one chapter of the book.
Each exercise has a level:
- _basic_: a direct use of a definition or a theorem, often a computation;
- _intermediate_: a short proof, or a computation that needs an idea;
- _advanced_: a longer proof, or a result that the book does not prove.

Most exercises have a hint.
The basic exercises have short answers in the last section of this chapter.
Try each exercise before you read its hint.

Some exercises are proved in the Lean library.
For these, the line _In Lean_ names the Lean declarations, so that you can compare your proof with the Lean proof.
To find a declaration, see the section "Finding the Lean source" of the chapter _How to use this book_.

The exercises marked _formalize_ ask you to write Lean.
Put your code in a new file that starts with `import Meat`, inside the repository, and build it with `lake build` or in an editor with the Lean extension.
These exercises assume that you know the basics of Lean and Mathlib.

#show heading.where(level: 2): it => {
  exercise-count.update(0)
  it
}

== Shannon information measures

In this section, all random variables are defined on one probability space and take values in finite sets.
For $p in [0, 1]$, $h(p) := -p log p - (1 - p) log (1 - p)$ is the binary entropy in nats, with $0 log 0 := 0$.
The binary entropy in bits is $h_2 (p) := h(p) \/ log 2$.
A quantity "in bits" is the quantity in nats divided by $log 2$.

#exercise(
  "basic",
  title: "Uniform law",
  compare: "Meat.entropy_eq_log_card",
  answer: [
    $H(X) = log 8 = 3 log 2 approx 2.079$ nats, which is $3$ bits.
  ],
)[
  Let $X$ be uniform on a set with $8$ elements.
  Compute $H(X)$ in nats and in bits.
]

#exercise(
  "basic",
  title: "Three letters",
  hint: [In bits, a letter with probability $2^(-k)$ contributes $k 2^(-k)$.],
  answer: [
    $H(X) = 1/2 dot 1 + 2 dot 1/4 dot 2 = 1.5$ bits.
    This is less than $log_2 3 approx 1.585$ bits, the entropy of the uniform law on three letters.
  ],
)[
  Let $X$ take the values $a$, $b$, $c$ with probabilities $1/2$, $1/4$, $1/4$.
  Compute $H(X)$ in bits, and compare it with the entropy of the uniform law on three letters.
]

#exercise(
  "basic",
  title: "Binary entropy",
  hint: [The derivative of $-t log t$ is $-log t - 1$.],
  answer: [
    The formula for $h$ does not change when $p$ and $1 - p$ are exchanged.
    $h(0) = h(1) = 0$ because $0 log 0 = 0$ and $log 1 = 0$, and $h(1/2) = 2 dot 1/2 log 2 = log 2$.
    For $0 < p < 1$, $h'(p) = (-log p - 1) + (log (1 - p) + 1) = log ((1 - p) / p)$.
    This is positive for $p < 1/2$ and negative for $p > 1/2$.
    So $h$ increases on $[0, 1/2]$, decreases on $[1/2, 1]$, and its maximum is $h(1/2) = log 2$, that is, $1$ bit.
  ],
)[
  Show that $h(p) = h(1 - p)$, $h(0) = h(1) = 0$ and $h(1/2) = log 2$.
  Compute $h'(p)$ for $0 < p < 1$.
  Deduce that $h$ increases on $[0, 1/2]$ and that its maximum is $log 2$.
]

#exercise(
  "basic",
  title: "Information about itself",
  hint: [The map $s |-> (s, s)$ is injective. Use the relabeling lemma.],
  compare: "Meat.entropy_pair_comp",
  answer: [
    By relabeling with the injective map $s |-> (s, s)$, $H(X, X) = H(X)$.
    Then $H(X given X) = H(X, X) - H(X) = 0$ and $I(X; X) = H(X) + H(X) - H(X, X) = H(X)$.
  ],
)[
  Show that $H(X, X) = H(X)$, $H(X given X) = 0$ and $I(X; X) = H(X)$.
]

#exercise(
  "basic",
  title: "A joint table",
  answer: [
    The law of $X$ is $(3/4, 1/4)$, so $H(X) = h_2 (1/4) approx 0.811$.
    The law of $Y$ is $(1/2, 1/2)$, so $H(Y) = 1$.
    The pair has the masses $1/2$, $1/4$, $1/4$, so $H(X, Y) = 1.5$.
    Then $H(X given Y) = 0.5$, $H(Y given X) approx 0.689$ and $I(X; Y) approx 0.311$, all in bits.
  ],
)[
  Let $X$ and $Y$ take values in ${0, 1}$, with
  $ P(X = 0, Y = 0) = 1/2, quad P(X = 0, Y = 1) = 1/4, quad P(X = 1, Y = 0) = 0, quad P(X = 1, Y = 1) = 1/4. $
  Compute $H(X)$, $H(Y)$, $H(X, Y)$, $H(X given Y)$, $H(Y given X)$ and $I(X; Y)$ in bits.
]

#exercise(
  "basic",
  title: "Fano's inequality gives a lower bound on the error",
  hint: [Use the second form of Fano's inequality for a decoder, $H(X given Y) <= log 2 + P_e log |S|$, and divide by $log 2$.],
  compare: "Meat.condEntropy_le_log_two_add_mul_log_card",
  answer: [
    In bits, the inequality is $H(X given Y) <= 1 + P_e log_2 16 = 1 + 4 P_e$.
    With $H(X given Y) = 2$, this gives $P_e >= 1/4$.
  ],
)[
  Let $X$ take values in a set $S$ with $16$ elements, and let $Y$ be another random variable.
  Suppose that $H(X given Y) = 2$ bits.
  Show that every decoder $g$ has error probability $P_e := P(g(Y) != X) >= 1/4$.
]

#exercise(
  "basic",
  title: "Divergence is not symmetric",
  compare: ("Meat.klDiv", "Meat.klDiv_nonneg"),
  answer: [
    $D(p || q) = 1/2 log_2 (2/3) + 1/2 log_2 2 = 1 - 1/2 log_2 3 approx 0.208$ bits.
    $D(q || p) = 3/4 log_2 (3/2) + 1/4 log_2 (1/2) = 3/4 log_2 3 - 1 approx 0.189$ bits.
    The two values are different.
  ],
)[
  On ${0, 1}$, let $p = (1/2, 1/2)$ and $q = (3/4, 1/4)$.
  Compute $D(p || q)$ and $D(q || p)$ in bits.
]

#exercise(
  "intermediate",
  title: "Maximum of entropy",
  hint: [Apply Gibbs' inequality with $q_s := 1 \/ |S|$. For the equality case, use the equality case of Gibbs' inequality, or the identity $H(X) = log |S| - D(X_* mu || cal(U)(S))$.],
  compare: ("Meat.entropy_le_log_card", "Meat.entropy_eq_log_card_sub_klDiv", "Meat.klDiv_eq_zero_iff"),
)[
  Prove that $H(X) <= log |S|$ for $X$ with values in $S$.
  Show that equality holds if and only if the law of $X$ is uniform on $S$.
]

#exercise(
  "intermediate",
  title: "Conditional entropy as an average",
  hint: [Write $P(X = s, Y = y) = P(Y = y) P(X = s given Y = y)$ and use $eta(a b) = a eta(b) + b eta(a)$ for $a, b >= 0$.],
)[
  For $y$ with $P(Y = y) > 0$, let $P(X = s given Y = y) := P(X = s, Y = y) \/ P(Y = y)$, and let
  $ H(X given Y = y) := sum_s eta(P(X = s given Y = y)) $
  be the entropy of the conditional law.
  Prove that
  $ H(X given Y) = sum_(y : P(Y = y) > 0) P(Y = y) H(X given Y = y). $
]

#exercise(
  "intermediate",
  title: "Conditioning on one value can increase entropy",
  hint: [First compute the law of $X$. Then use the previous exercise.],
)[
  Let $Y$ take values in ${0, 1}$ with $P(Y = 0) = 3/4$.
  Given $Y = 0$, let $X = 0$.
  Given $Y = 1$, let $X$ be uniform on ${0, 1}$.
  Compute $H(X)$, $H(X given Y = 1)$ and $H(X given Y)$ in bits.
  Check that $H(X given Y = 1) > H(X)$ but $H(X given Y) <= H(X)$.
]

#exercise(
  "intermediate",
  title: "Functions do not increase entropy",
  hint: [$H(X) = H(X, f(X)) = H(f(X)) + H(X given f(X))$. For the equality case, use the exercise on conditional entropy as an average.],
  compare: "Meat.entropy_comp_le",
)[
  Let $f : S -> T$.
  Prove that $H(f(X)) <= H(X)$.
  Show that equality holds if and only if $f$ is injective on the set ${s : P(X = s) > 0}$.
]

#exercise(
  "intermediate",
  title: "Chain rule for three variables",
  hint: [Expand each conditional entropy as a difference. You need one relabeling: $H((X, Y), Z) = H(X, (Y, Z))$.],
  compare: ("Meat.entropy_eq_sum", "Meat.entropy_pi_le_sum"),
)[
  Prove that $H(X, Y, Z) = H(X) + H(Y given X) + H(Z given X, Y)$.
  Deduce that $H(X, Y, Z) <= H(X) + H(Y) + H(Z)$.
]

#exercise(
  "intermediate",
  title: "Data processing",
  hint: [Expand $I(X; (Y, Z))$ with the chain rule for mutual information in two ways.],
  compare: ("Meat.MarkovChain.mutualInfo_le_left", "Meat.markovChain_comp", "Meat.mutualInfo_comp_le"),
)[
  Let $X -> Y -> Z$ be a Markov chain, that is, $I(X; Z given Y) = 0$.
  Prove that $I(X; Z) <= I(X; Y)$.
  Then show that $X -> Y -> g(Y)$ is a Markov chain for every map $g$, and deduce that $I(X; g(Y)) <= I(X; Y)$.
]

#exercise(
  "intermediate",
  title: "Mutual information is a divergence",
  hint: [Write each term $P(x, y) log (P(x, y) \/ (P(x) P(y)))$ as a sum of three logarithms, and sum over $y$ or over $x$.],
  compare: ("Meat.mutualInfo_eq_klDiv", "Meat.klDiv_eq_zero_iff", "Meat.mutualInfo_eq_zero_of_measureReal_eq_mul"),
)[
  Let $P_(X Y)$ be the law of $(X, Y)$, and let $P_X times.o P_Y$ be the product of the laws of $X$ and $Y$.
  Prove that $I(X; Y) = D(P_(X Y) || P_X times.o P_Y)$.
  Deduce that $I(X; Y) >= 0$, with equality if and only if $X$ and $Y$ are independent.
]

#exercise(
  "intermediate",
  title: "Fano's inequality is sharp",
  hint: [Take $hat(X)$ constant, equal to one letter $s_0$, and choose the law of $X$.],
  compare: "Meat.condEntropy_le_binEntropy_add_mul_log",
)[
  Let $|S| >= 2$ and $0 <= q <= (|S| - 1) \/ |S|$.
  Find $X$ and an estimator $hat(X)$ with $P(hat(X) != X) = q$ and
  $ H(X given hat(X)) = h(q) + q log (|S| - 1). $
]

#exercise(
  "intermediate",
  title: "Typical sequences of a coin",
  hint: [For a sequence with $k$ ones, $p^n (x) = p^k (1 - p)^(n - k)$.],
  compare: "Meat.mem_typicalSet_iff",
)[
  Let $0 < p < 1$, and consider the law on ${0, 1}$ with $P(1) = p$.
  Let $x in {0, 1}^n$ have $k$ ones.
  Show that
  $ -1/n log p^n (x) - h(p) = (k/n - p) log ((1 - p) / p). $
  Deduce that, for $p != 1/2$ and $n > 0$, $x in A_epsilon^((n))$ if and only if $|k \/ n - p| <= epsilon \/ |log ((1 - p) \/ p)|$.
  What is $A_epsilon^((n))$ for $p = 1/2$ and $epsilon >= 0$?
]

#exercise(
  "intermediate",
  title: "Number of types",
  hint: [A type of length $n$ is a vector of counts. Count the ways to write $n$ as an ordered sum of $m$ nonnegative integers.],
  compare: "Meat.card_typeSet_le",
)[
  Let $|S| = m$ and $n >= 1$.
  Show that the number of types of length $n$ is the binomial coefficient $binom(n + m - 1, m - 1)$.
  Compare it with the bound $(n + 1)^m$ for $m = 2$ and $n = 10$.
]

#exercise(
  "advanced",
  title: "Han's inequality for three variables",
  hint: [Add the submodular inequality $H(X_1, X_2, X_3) + H(X_1) <= H(X_1, X_2) + H(X_1, X_3)$ and the subadditive inequality $H(X_1, X_2, X_3) <= H(X_1) + H(X_2, X_3)$.],
)[
  Prove that
  $ 2 H(X_1, X_2, X_3) <= H(X_1, X_2) + H(X_1, X_3) + H(X_2, X_3). $
  Then state and prove the version for $n$ variables: $(n - 1) H(X_1, dots, X_n) <= sum_(i = 1)^n H(X_1, dots, X_(i - 1), X_(i + 1), dots, X_n)$.
  This result is not yet in Lean: `docs/PLAN.md` lists it as a planned topic.
]

#exercise(
  "advanced",
  title: "Zero conditional entropy",
  hint: [Use the exercise on conditional entropy as an average. When is the entropy of a law equal to $0$?],
)[
  Prove that $H(X given Y) = 0$ if and only if there is a map $g$ with $P(X = g(Y)) = 1$.
]

#exercise(
  "advanced",
  title: "The log-sum inequality for many terms",
  hint: [Use induction on $n$. Group the first $n - 1$ terms into one term and apply the two-term inequality.],
  compare: "Meat.add_mul_log_div_add_le",
)[
  Let $a_1, dots, a_n >= 0$ and $b_1, dots, b_n >= 0$, with $a_i = 0$ whenever $b_i = 0$.
  Let $a := sum_i a_i$ and $b := sum_i b_i$.
  Prove that
  $ a log a / b <= sum_(i = 1)^n a_i log a_i / b_i, $
  with $0 log (0 \/ x) := 0$.
  The Lean library proves the case $n = 2$.
]

#exercise(
  "basic",
  title: "Mutual information with itself in Lean",
  formalize: true,
  hint: [Rewrite with `Meat.mutualInfo_def`, then use `Meat.entropy_pair_comp μ id`. You may need `simpa` or `show` to match `fun ω => (X ω, X ω)` with `fun ω => (X ω, id (X ω))`.],
  answer: [
    One proof is `rw [Meat.mutualInfo_def, show H[fun ω => (X ω, X ω) ; μ] = H[X ; μ] from Meat.entropy_pair_comp μ id]` followed by `ring`.
    The exact steps may differ with the Mathlib version.
  ],
)[
  State and prove in Lean, for a finite type `S` with a measurable space structure:
  ```lean
  theorem mutualInfo_self (X : Ω → S) (μ : Measure Ω) : I[X : X ; μ] = H[X ; μ]
  ```
]

#exercise(
  "advanced",
  title: "Han's inequality in Lean",
  formalize: true,
  hint: [Use `Meat.entropy_submodular` with the three variables in a suitable order, `Meat.entropy_pair_le_add`, and the relabeling lemmas `Meat.entropy_comm`, `Meat.entropy_assoc` and `Meat.entropy_comm_left` to match the pairs.],
)[
  State and prove in Lean the inequality of the exercise on Han's inequality for three measurable random variables under a probability measure:
  ```lean
  2 * H[fun ω => ((X ω, Y ω), Z ω) ; μ]
    ≤ H[fun ω => (X ω, Y ω) ; μ] + H[fun ω => (X ω, Z ω) ; μ] + H[fun ω => (Y ω, Z ω) ; μ]
  ```
]

== Source coding

In this section, a code maps each source symbol to a word over an alphabet with $D$ letters, and $L(c) := sum_s p(s) |c(s)|$ is its expected length.
Unless an exercise says otherwise, $D = 2$ and lengths and entropies are in bits.

#exercise(
  "basic",
  title: "Prefix or not",
  hint: [For (b), read the codewords backwards. For (c), find one string with two parsings.],
  compare: ("Meat.IsPrefixCode.kraft", "Meat.IsUDCode.kraft"),
  answer: [
    (a) is a prefix code, and its Kraft sum is $1/2 + 1/4 + 1/8 + 1/8 = 1$.
    (b) is not a prefix code, since $0$ is a prefix of $01$.
    It is uniquely decodable: no codeword is a suffix of another, so a string can be decoded from its right end.
    (c) is not uniquely decodable: $010$ is both $0 dot 10$ and $01 dot 0$.
    Its Kraft sum is $1$, so Kraft's inequality alone does not detect this.
  ],
)[
  For each binary code, decide whether it is a prefix code and whether it is uniquely decodable:
  (a) ${0, 10, 110, 111}$; (b) ${0, 01, 11}$; (c) ${0, 01, 10}$.
]

#exercise(
  "basic",
  title: "Kraft's converse",
  compare: "Meat.exists_isPrefixCode_of_kraft",
  answer: [
    (a) No: the Kraft sum is $1/2 + 1/4 + 1/4 + 1/8 = 9/8 > 1$.
    (b) Yes: the Kraft sum is $1$, and ${0, 10, 110, 111}$ has these lengths.
    (c) Yes: the Kraft sum is $1/3 + 1/3 + 3/9 = 1$, and ${0, 1, 20, 21, 22}$ has these lengths.
  ],
)[
  Is there a prefix code with these codeword lengths?
  If there is, give one.
  (a) $D = 2$, lengths $1, 2, 2, 3$.
  (b) $D = 2$, lengths $1, 2, 3, 3$.
  (c) $D = 3$, lengths $1, 1, 2, 2, 2$.
]

#exercise(
  "basic",
  title: "A Huffman code",
  hint: [There are ties. Different choices give different lengths but the same expected length.],
  compare: ("Meat.huffmanCodeLength_le", "Meat.expectedLength_huffmanCode_lt"),
  answer: [
    Merge $0.1 + 0.1 = 0.2$, then $0.2 + 0.2 = 0.4$, then $0.2 + 0.4 = 0.6$, then $0.4 + 0.6 = 1$.
    One choice gives the lengths $(1, 2, 3, 4, 4)$, another gives $(2, 2, 2, 3, 3)$.
    In both cases $L = 2.2$ bits.
    The entropy is $H(p) approx 2.122$ bits, so $H(p) <= L < H(p) + 1$.
  ],
)[
  Let $p = (0.4, 0.2, 0.2, 0.1, 0.1)$.
  Find a binary Huffman code, its expected length, and $H(p)$.
]

#exercise(
  "basic",
  title: "Dyadic laws",
  answer: [
    The Shannon lengths $ceil(-log_2 p(s))$ are $1, 2, 3, 3$, for example the code ${0, 10, 110, 111}$.
    Then $L = 1/2 + 2/4 + 3/8 + 3/8 = 1.75$ bits, and $H(p) = 1.75$ bits.
    So $L = H(p)$: no code does better.
  ],
)[
  Let $p = (1/2, 1/4, 1/8, 1/8)$.
  Find the Shannon code lengths $ceil(-log_2 p(s))$, the expected length, and $H(p)$.
]

#exercise(
  "basic",
  title: "A biased coin source",
  compare: ("Meat.Lossless.closure_achievableRates_eq", "Meat.Lossless.tendsto_errorProb_one"),
  answer: [
    (a) $H = h_2 (0.1) approx 0.469$ bits.
    (b) Every rate above $0.469$ bits per symbol is achievable, and the closure of the achievable rates is $[0.469, infinity)$ in bits.
    (c) The rate $0.3$ is below $H$, so by the strong converse the error probability of every code tends to $1$.
  ],
)[
  A source emits independent bits, each equal to $1$ with probability $0.1$.
  (a) Compute its entropy in bits.
  (b) For which rates, in bits per symbol, does the fixed-length source coding theorem give codes with small error probability?
  (c) What happens to the error probability for codes of rate $0.3$ bits per symbol?
  The book measures rates in nats: a rate of $R$ bits is $R log 2$ nats.
]

#exercise(
  "basic",
  title: "No empty codeword",
  compare: "Meat.IsUDCode.ne_nil",
  answer: [
    If $c(s)$ is empty, the lists $(s)$ and $(s, s)$ have the same concatenation, so $c$ is not uniquely decodable.
    The empty word is a prefix of every word.
    So if $c(s)$ is empty in a prefix code, then $c(s)$ is a prefix of $c(t)$ for every $t$, and $t = s$ for every $t$.
  ],
)[
  Show that a uniquely decodable code has no empty codeword.
  Show that a prefix code with an empty codeword has only one symbol.
]

#exercise(
  "intermediate",
  title: "Blocks help",
  hint: [For pairs, the probabilities are $0.81$, $0.09$, $0.09$ and $0.01$.],
  compare: "Meat.tendsto_minExpectedLength_div",
)[
  Let $p = (0.9, 0.1)$.
  Show that the best binary code for one symbol has $L = 1$ bit.
  Find a Huffman code for pairs of symbols, and its expected length per symbol.
  Compare both with $H(p) approx 0.469$ bits and with the bound $L_n^* \/ n <= H(p) + 1 \/ n$ of the variable-length source coding theorem.
]

#exercise(
  "intermediate",
  title: "Equality in the entropy bound",
  hint: [Look at the proof of the entropy bound with $q(s) := D^(-|c(s)|)$, and use the equality case of Gibbs' inequality.],
  compare: ("Meat.IsPrefixCode.measureEntropy_le", "Meat.sum_mul_log_eq_sum_mul_log_iff"),
)[
  Let $c$ be a prefix code with $D$ letters.
  Prove that $L(c) log D = H(p)$ if and only if $p(s) = D^(-|c(s)|)$ for every $s$.
]

#exercise(
  "intermediate",
  title: "Slepian-Wolf for a noisy copy",
  hint: [$H(X, Y) = H(X) + H(Y given X)$, and given $X$, $Y$ is determined by $N$.],
  compare: "Meat.SlepianWolf.closure_achievableRegion_eq",
)[
  Let $X$ be a uniform bit, let $N$ be a bit with $P(N = 1) = 0.1$ independent of $X$, and let $Y := X plus.o N$, where $plus.o$ is addition modulo $2$.
  Compute $H(X given Y)$, $H(Y given X)$ and $H(X, Y)$ in bits.
  Draw the Slepian-Wolf region and give its two corner points.
  Compare the smallest sum rate with the sum rate $H(X) + H(Y)$ of separate coding.
]

#exercise(
  "intermediate",
  title: "Shape of the rate-distortion function",
  hint: [If $W_1$ and $W_2$ are test channels, the mixture $lambda W_1 + (1 - lambda) W_2$ has expected distortion $lambda E_(W_1) d + (1 - lambda) E_(W_2) d$, and its rate is at most $lambda I_(W_1)(p) + (1 - lambda) I_(W_2)(p)$ by convexity in the channel.],
  compare: ("Meat.RateDistortion.rdf_le_rdf", "Meat.RateDistortion.convexOn_rdf", "Meat.DMC.inputMutualInfo_le_of_toReal_eq"),
)[
  Prove that $R(D)$ does not increase with $D$ and is convex on $[D_min, infinity)$.
]

#exercise(
  "advanced",
  title: "Binary source with Hamming distortion",
  hint: [For the lower bound, $I(X; hat(X)) = H(X) - H(X plus.o hat(X) given hat(X)) >= log 2 - H(X plus.o hat(X))$, and $P(X plus.o hat(X) = 1) <= D$. For the upper bound, choose a test channel such that $hat(X)$ is uniform and $X = hat(X) plus.o N$ with $P(N = 1) = D$.],
)[
  Let $p$ be uniform on ${0, 1}$, let $T = {0, 1}$ and let $d(s, t) := 1$ if $s != t$ and $0$ otherwise.
  Prove that $R(D) = log 2 - h(D)$ for $0 <= D <= 1/2$ and $R(D) = 0$ for $D >= 1/2$.
  This example is not in Lean.
]

#exercise(
  "advanced",
  title: "McMillan's inequality",
  hint: [Let $K := sum_s D^(-|c(s)|)$ and let $m$ be the largest codeword length. Expand $K^r$ as a sum over lists of $r$ symbols, and group the lists by the length of their concatenation.],
  compare: "Meat.IsUDCode.kraft",
)[
  Let $c$ be a uniquely decodable code with $D$ letters.
  Prove that $K^r <= r m$ for every $r >= 1$, and deduce that $K <= 1$.
]

#exercise(
  "intermediate",
  title: "A concrete prefix code in Lean",
  formalize: true,
  hint: [Unfold `Meat.IsPrefixCode` and try `decide`: the prefix relation on lists of `Fin 2` is decidable.],
  compare: ("Meat.IsPrefixCode", "Meat.IsPrefixCode.kraft"),
)[
  Define `c : Fin 4 → List (Fin 2)` for the code ${0, 10, 110, 111}$.
  Prove `Meat.IsPrefixCode c`.
  Then use `Meat.IsPrefixCode.kraft` to obtain $sum_s (1 \/ 2)^(|c(s)|) <= 1$, and check by computation that the sum is exactly $1$.
]

== Channel coding

In this section, $W$ is a discrete memoryless channel from $A$ to $B$, $I(p)$ is the mutual information of input and output for the input law $p$, and $C(W) := sup_p I(p)$ is the capacity.
Capacities are in bits unless an exercise says otherwise.

#exercise(
  "basic",
  title: "Rates",
  answer: [
    The rate is $log_2 1024 \/ 20 = 10 \/ 20 = 0.5$ bits per channel use, which is $0.5 log 2 approx 0.347$ nats.
  ],
)[
  A code has $1024$ messages and block length $20$.
  What is its rate in bits and in nats per channel use?
]

#exercise(
  "basic",
  title: "Useless channels",
  compare: ("Meat.DMC.inputMutualInfo_le_log_card_output", "Meat.mutualInfo_eq_zero_of_measureReal_eq_mul"),
  answer: [
    (a) $I(p) <= log |B| = log 1 = 0$ for every $p$, so $C(W) = 0$.
    (b) If $W(dot given x)$ is the same law $r$ for every $x$, then $P(X = x, Y = y) = p(x) r(y)$, so $X$ and $Y$ are independent and $I(p) = 0$.
  ],
)[
  Show that $C(W) = 0$ in each case:
  (a) $B$ has one element;
  (b) $W(dot given x)$ is the same law for every input $x$.
]

#exercise(
  "basic",
  title: "The noisy typewriter",
  hint: [Compute $H(Y given X)$ with the noise entropy lemma. Then bound $H(Y)$.],
  compare: "Meat.DMC.condEntropy_snd_fst_jointMeasure",
  answer: [
    For every input, the output is uniform on two letters, so $H(Y given X) = 1$ bit for every input law.
    Then $I(p) = H(Y) - 1 <= log_2 4 - 1 = 1$ bit.
    The uniform input gives the uniform output, so $C(W) = 1$ bit.
    The inputs $0$ and $2$ have disjoint sets of outputs, so they send $1$ bit per use with no error at all.
  ],
)[
  Let $A = B = {0, 1, 2, 3}$, and let $W(x given x) = W(x + 1 mod 4 given x) = 1/2$ for each $x$.
  Compute $C(W)$.
  Find a code that sends $1$ bit per channel use with error probability $0$.
]

#exercise(
  "intermediate",
  title: "The Z-channel",
  hint: [With $a := P(X = 1)$, show that $I(p) = h_2 (a \/ 2) - a$ bits, and maximize over $a$.],
)[
  Let $A = B = {0, 1}$, $W(0 given 0) = 1$, and $W(0 given 1) = W(1 given 1) = 1/2$.
  Show that $C(W) = log_2 (5/4) approx 0.322$ bits, attained at $P(X = 1) = 2/5$.
]

#exercise(
  "intermediate",
  title: "Above capacity",
  hint: [Start from $(1 - overline(lambda)) log k <= n C(W) + log 2$, with $C(W)$ in nats, and use $log k >= n R$.],
  compare: ("Meat.BlockCode.one_sub_mul_log_card_le", "Meat.DMC.le_capacity_of_achievable"),
)[
  Let $R > 0$, and let a code of length $n$ have $k >= e^(n R)$ messages.
  Prove that its average error probability satisfies
  $ overline(lambda) >= 1 - C(W) / R - (log 2) / (n R). $
  Deduce that no rate $R > C(W)$ is achievable.
]

#exercise(
  "intermediate",
  title: "Why the closure",
  hint: [A code with $k >= e^(n R)$ messages also has $k >= e^(n R')$ messages when $R' <= R$.],
  compare: ("Meat.DMC.achievable_zero", "Meat.DMC.closure_achievable_eq"),
)[
  Let $A$ be nonempty.
  Show that the rate $0$ is achievable, and that if $R$ is achievable and $0 <= R' <= R$, then $R'$ is achievable.
  Deduce from the channel coding theorem that every $R$ with $0 <= R < C(W)$ is achievable.
  Explain why the theorem does not say whether $R = C(W)$ is achievable.
]

#exercise(
  "intermediate",
  title: "The binary adder channel",
  hint: [Given $X_2$, the output determines $X_1$.],
  compare: "Meat.MAC.closure_achievableRegion_eq",
)[
  Two senders send bits $X_1$ and $X_2$, and the receiver sees the integer $Y = X_1 + X_2 in {0, 1, 2}$.
  For independent uniform inputs, compute the pentagon: $I(X_1; Y given X_2)$, $I(X_2; Y given X_1)$ and $I((X_1, X_2); Y)$ in bits.
  Show that the sum rate $1.5$ bits is larger than the rate $1$ bit that the two senders get when they take turns.
]

#exercise(
  "intermediate",
  title: "Extreme cases of superposition",
  hint: [If $U$ is constant, then $I(U; Y_2) = 0$. If $U = X$, then $I(X; Y_1 given U) = 0$.],
  compare: "Meat.BC.achievable_of_lt",
)[
  For a broadcast channel, compute the superposition region $cal(S)(p_U, p_X)$ in two cases:
  (a) $U$ is constant;
  (b) $U = X$.
  Interpret each case as a code that serves only one receiver.
]

#exercise(
  "advanced",
  title: "Symmetric channels",
  hint: [Show that $H(Y given X)$ does not depend on the input law, and that the uniform input gives the uniform output.],
)[
  Suppose that the rows $W(dot given x)$ are permutations of each other, and that the columns $(W(y given x))_x$ are permutations of each other.
  Let $r$ be one row.
  Prove that $C(W) = log |B| - H(r)$, attained by the uniform input.
  Deduce the capacity $1 - h_2 (q)$ of the binary symmetric channel with crossover probability $q$.
  This result is not in Lean.
]

#exercise(
  "advanced",
  title: "Concavity of the information",
  hint: [Write $I(p) = H(Y) - sum_x p(x) H(W(dot given x))$. The law of $Y$ is linear in $p$, and entropy is concave in the law.],
)[
  Prove that $p |-> I(p)$ is concave on $Delta(A)$.
  First prove that the entropy of a law is a concave function of the law.
  Explain why this makes the computation of $C(W)$ a convex optimization problem.
]

#exercise(
  "intermediate",
  title: "Capacity of a channel with one output in Lean",
  formalize: true,
  hint: [Use `le_antisymm`. For the upper bound, `Real.iSup_le` needs a bound for each input law and that the bound is nonnegative, so it also covers an empty set of laws. Then use `Meat.DMC.inputMutualInfo_le_log_card_output`, `Fintype.card_unit` and `Real.log_one`. For the lower bound, use `Meat.DMC.capacity_nonneg`.],
  compare: ("Meat.DMC.capacity", "Meat.DMC.capacity_nonneg"),
)[
  State and prove in Lean that every channel `W : Meat.DMC A Unit` with a finite input type has `W.capacity = 0`.
  Add the type class hypotheses that the lemmas need.
]

== Network coding

In this section, the butterfly network has the nodes $s$, $a$, $b$, $c$, $d$, $t_1$ and $t_2$, and one edge in each of the pairs
$ (s, a), (s, b), (a, c), (b, c), (c, d), (a, t_1), (b, t_2), (d, t_1), (d, t_2). $
The source is $s$ and the sinks are $t_1$ and $t_2$.

#exercise(
  "basic",
  title: "Min-cuts of the butterfly",
  hint: [For the lower bound, find two paths from $s$ to $t_1$ with no common edge.],
  compare: "Meat.Network.le_minCut_of_decodes",
  answer: [
    The cut ${s}$ has value $2$, so $op("mincut")(s, t_1) <= 2$.
    The paths $s -> a -> t_1$ and $s -> b -> c -> d -> t_1$ have no common edge.
    Every cut that separates $s$ from $t_1$ contains an edge of each path, so its value is at least $2$.
    So $op("mincut")(s, t_1) = 2$, and $op("mincut")(s, t_2) = 2$ in the same way.
  ],
)[
  Compute $op("mincut")(s, t_1)$ and $op("mincut")(s, t_2)$.
]

#exercise(
  "basic",
  title: "The XOR code",
  compare: "Meat.Network.multicast_iff",
  answer: [
    Over $FF_2$, send $m_1$ on $(s, a)$, $(a, c)$ and $(a, t_1)$, and $m_2$ on $(s, b)$, $(b, c)$ and $(b, t_2)$.
    Node $c$ sends $m_1 + m_2$ on $(c, d)$, and $d$ sends it on $(d, t_1)$ and $(d, t_2)$.
    Then $t_1$ computes $m_2 = m_1 + (m_1 + m_2)$, and $t_2$ computes $m_1 = m_2 + (m_1 + m_2)$.
  ],
)[
  Give a network code over the field $FF_2 = {0, 1}$ with message $(m_1, m_2) in FF_2^2$ such that both sinks decode.
]

#exercise(
  "intermediate",
  title: "Routing is not enough",
  hint: [Suppose that the edge $(c, d)$ carries $m_1$. What must the edges $(s, a)$ and $(s, b)$ carry?],
)[
  In a routing scheme, each edge carries a copy of $m_1$ or of $m_2$, and a node can only forward what it receives.
  Show that no routing scheme delivers both messages to both sinks in one use of the butterfly network.
]

#exercise(
  "basic",
  title: "Why two symbols",
  compare: "Meat.Network.le_cutValue_of_decodes",
  answer: [
    If $|F| = 1$, then $F^h$ has one element for every $h$.
    Every node decodes, because there is only one message.
    So $h$ can be larger than every cut value, and the bound fails.
  ],
)[
  The cut-set bound assumes that the alphabet $F$ has at least two elements.
  Show that the bound fails for $|F| = 1$.
]

#exercise(
  "basic",
  title: "Field size",
  compare: "Meat.Network.exists_code_of_le_minCut",
  answer: [
    $|V| = 7$ and there are $9$ edges, so the theorem asks for $|F| >= 2^(7 + 9) = 65536$.
    The XOR code works over $FF_2$, so the bound is far from necessary here.
  ],
)[
  The theorem that linear codes achieve the min-cut asks for a field with $|F| >= 2^(|V| + sum_(u, v) c(u, v))$.
  Compute this bound for the butterfly network, and compare it with the field of the XOR code.
]

#exercise(
  "intermediate",
  title: "Avoiding subspaces needs a large field",
  hint: [The space $FF_2^2$ has exactly three subspaces of dimension $1$.],
  compare: "Meat.Network.exists_mem_forall_notMem",
)[
  Let $I := FF_2^2$, and let $U_1$, $U_2$, $U_3$ be its three subspaces of dimension $1$.
  Show that $I subset.eq.not U_k$ for each $k$, but that every $y in I$ is in some $U_k$.
  Explain why this shows that the condition $n <= |F|$ in the lemma on avoiding subspaces cannot be dropped.
]

#exercise(
  "advanced",
  title: "An entropy form of the cut-set bound",
  hint: [By the lemma that information crosses the cut, the symbols that enter $t$ are a function of the symbols on the edges of the cut. Then use subadditivity.],
  compare: "Meat.Network.incoming_eq_of_cut",
)[
  Let $M$ be uniform on $F^h$, and consider a network code on an acyclic network in which $t$ decodes.
  Let $S$ be a cut with $s in S$ and $t in.not S$, and let $E_e$ be the symbol on the edge $e$ as a function of $M$.
  Prove that
  $ h log |F| = H(M) <= sum_(e "from" S "to" V without S) H(E_e) <= op("cut")(S) log |F|. $
  This form extends to codes in which the message is not uniform.
]

#exercise(
  "advanced",
  title: "Acyclic networks",
  hint: [For the converse, let $r(v)$ be the length of the longest path that ends at $v$.],
  compare: "Meat.Network.IsAcyclic",
)[
  Prove that a network on a finite set $V$ has a rank function $r$, with $r(u) < r(v)$ whenever $c(u, v) > 0$, if and only if it has no directed cycle.
]

#exercise(
  "intermediate",
  title: "The butterfly in Lean",
  formalize: true,
  hint: [Define `cap` by pattern matching on `Fin 7 → Fin 7 → ℕ`. For acyclicity, give the rank function explicitly. `Meat.Network.cutValue` is a finite sum, so `decide` or `rfl` can evaluate it for a given set.],
  compare: ("Meat.Network.IsAcyclic", "Meat.Network.cutValue"),
)[
  Define the butterfly network as a `Meat.Network (Fin 7)`.
  Prove that it is acyclic, and that the cut ${s}$ has value $2$.
  As a harder step, prove that `Meat.Network.minCut` of the source and each sink is $2$.
]

== Continuous alphabets

In this section, $h(nu)$ is the differential entropy of a law $nu$ on $RR$ with a density, in nats.

#exercise(
  "basic",
  title: "Uniform law on an interval",
  answer: [
    The density is $f = 1 \/ a$ on $[0, a]$, so $h = -integral_0^a (1 \/ a) log (1 \/ a) thin d x = log a$.
    For $a = 1/2$, $h = -log 2 < 0$.
    Differential entropy can be negative, unlike discrete entropy.
  ],
)[
  Compute the differential entropy of the uniform law on $[0, a]$, for $a > 0$.
  Find a value of $a$ for which it is negative.
]

#exercise(
  "basic",
  title: "Gaussian entropy",
  compare: "Meat.measureDiffEntropy_gaussianReal",
  answer: [
    $h = 1/2 log (2 pi e) approx 1.419$ nats, which is about $2.047$ bits.
  ],
)[
  Compute the differential entropy of $cal(N)(0, 1)$ in nats and in bits.
]

#exercise(
  "basic",
  title: "Gaussian channel capacity",
  compare: ("Meat.awgnCapacity", "Meat.AWGN.closure_achievable_eq"),
  answer: [
    In bits, $C = 1/2 log_2 (1 + P \/ N)$.
    For $P \/ N = 15$, $C = 1/2 log_2 16 = 2$ bits.
    For $P \/ N = 1$, $C = 1/2$ bit.
  ],
)[
  Compute the capacity of the Gaussian channel in bits per channel use for the signal-to-noise ratios $P \/ N = 15$ and $P \/ N = 1$.
]

#exercise(
  "intermediate",
  title: "Scaling",
  hint: [If $X$ has density $f$, then $a X + b$ has density $x |-> f((x - b) \/ a) \/ |a|$.],
)[
  Let $X$ have a density and let $a != 0$ and $b$ be real.
  Prove that $h(a X + b) = h(X) + log |a|$.
  This result is not in Lean.
]

#exercise(
  "intermediate",
  title: "Uniform against Gaussian",
  hint: [Use the first exercise of this section and the previous one.],
  compare: "Meat.measureDiffEntropy_le_of_variance",
)[
  The uniform law on $[-sqrt(3), sqrt(3)]$ has variance $1$.
  Compute its differential entropy, and compare it with the entropy of $cal(N)(0, 1)$.
  Which theorem of the chapter predicts the result?
]

#exercise(
  "intermediate",
  title: "Low and high signal-to-noise ratio",
  hint: [$log (1 + x) = x + O(x^2)$ as $x -> 0$.],
)[
  Show that $C(P, N) = P \/ (2 N) + O((P \/ N)^2)$ nats as $P \/ N -> 0$.
  Show that $C(4 P, N) - C(P, N) -> log 2$ nats, that is $1$ bit, as $P \/ N -> infinity$.
  Interpret both statements in terms of the power that one more bit costs.
]

#exercise(
  "intermediate",
  title: "The exponential law maximizes entropy",
  hint: [Apply the cross-entropy bound with the exponential density $g(x) := e^(-x \/ m) \/ m$ on $[0, infinity)$.],
  compare: "Meat.measureDiffEntropy_le_neg_integral_log_rnDeriv",
)[
  Let $nu$ be a law on $[0, infinity)$ with a density and mean $m > 0$, with the integrability conditions of the cross-entropy bound.
  Prove that $h(nu) <= 1 + log m$, and that the exponential law with mean $m$ attains the bound.
]

#exercise(
  "advanced",
  title: "Why the integrability hypothesis",
  hint: [Put spikes of mass $c \/ k^2$ and width $(c \/ k^2) e^(-k^2)$ in $[0, 1]$, for $k = 1, 2, dots$, with $c$ such that the masses sum to $1$.],
)[
  Construct a density $f$ on $[0, 1]$ with $integral f log f = +infinity$.
  Its variance is finite, because it lives in $[0, 1]$.
  Explain why the maximum entropy theorem needs the hypothesis that $eta compose f$ is integrable, given that Lean sets the integral of a function that is not integrable to $0$.
]

#exercise(
  "advanced",
  title: "Water-filling",
  hint: [Maximize $sum_i 1/2 log (1 + P_i \/ N_i)$ under $sum_i P_i <= P$ and $P_i >= 0$. The Lagrange conditions give $P_i = max(nu - N_i, 0)$ for a level $nu$.],
)[
  Two independent Gaussian channels have noise variances $N_1 = 1$ and $N_2 = 3$, and the total power is $P = 4$.
  Show that the best split is $P_1 = 3$ and $P_2 = 1$, and that the total capacity is $1/2 log_2 (16 \/ 3) approx 1.21$ bits.
  Parallel Gaussian channels are not yet in Lean: `docs/PLAN.md` lists them as a planned topic.
]

#exercise(
  "intermediate",
  title: "Monotonicity of the capacity formula in Lean",
  formalize: true,
  hint: [Unfold `Meat.awgnCapacity`. Use `Real.log_le_log` and the monotonicity of division by a positive number.],
  compare: "Meat.awgnCapacity",
)[
  State and prove in Lean: if $N > 0$, $P >= 0$ and $P <= P'$, then `Meat.awgnCapacity P N ≤ Meat.awgnCapacity P' N`.
]

== Hypothesis testing

In this section, $p$ and $q$ are laws on a finite set $S$, $H_0$ says that the symbols have the law $p$, and $H_1$ says that they have the law $q$.

#exercise(
  "basic",
  title: "Stein exponent",
  compare: "Meat.tendsto_steinBeta",
  answer: [
    $D(p || q) = 1 - 1/2 log_2 3 approx 0.208$ bits, which is $1/2 log (4/3) approx 0.144$ nats.
    So $beta_n (epsilon)$ decays like $2^(-0.208 n)$, up to factors that grow slower than every exponential.
  ],
)[
  Let $p = (1/2, 1/2)$ and $q = (3/4, 1/4)$ on ${0, 1}$.
  Find the exponent of the best type-II error $beta_n (epsilon)$ for a fixed $0 < epsilon < 1$.
]

#exercise(
  "basic",
  title: "Bayesian error for one symbol",
  compare: "Meat.bayesError_eq_sum_min",
  answer: [
    $e_1 = min(1/2, 3/4) + min(1/2, 1/4) = 1/2 + 1/4 = 3/4$.
    The best test decides $H_0$ exactly on ${1}$, where $q <= p$.
  ],
)[
  With $p$ and $q$ as in the previous exercise, compute the Bayesian error $e_1 = min_A (p(A^c) + q(A))$ for one symbol, and find the best test.
]

#exercise(
  "intermediate",
  title: "Chernoff information of a symmetric pair",
  hint: [The function $Z(lambda) := sum_s p(s)^lambda q(s)^(1 - lambda)$ is convex, and here $Z(lambda) = Z(1 - lambda)$.],
  compare: "Meat.tendsto_chernoff",
)[
  Let $0 < a < 1$, $p = (a, 1 - a)$ and $q = (1 - a, a)$.
  Show that $C(p, q) = -log (2 sqrt(a (1 - a)))$.
  Compute it for $a = 1/4$.
]

#exercise(
  "intermediate",
  title: "Chernoff information and divergence",
  hint: [Apply Jensen's inequality to $log$: $log sum_s p(s) (q(s) \/ p(s))^(1 - lambda) >= (1 - lambda) sum_s p(s) log (q(s) \/ p(s))$, where the sums are over $s$ with $p(s) > 0$.],
)[
  Assume that $p$ and $q$ give positive mass to the same letters.
  Prove that $C(p, q) <= min(D(p || q), D(q || p))$.
]

#exercise(
  "intermediate",
  title: "Sanov's theorem for a coin",
  hint: [For $t > 1/2$, $D((1 - t, t) || (1/2, 1/2)) = log 2 - h(t)$, and this increases with $t$.],
  compare: "Meat.tendsto_sanov",
)[
  Let $q$ be the fair coin, and let $E$ be the set of laws $P$ on ${0, 1}$ with $P({1}) > 3/4$.
  Compute $D(E || q)$ in bits.
  Interpret the result: how fast does the probability of seeing more than $75%$ ones decay?
]

#exercise(
  "intermediate",
  title: "Without absolute continuity",
  hint: [Use the test that decides $H_0$ when the letter $s$ occurs.],
  compare: "Meat.steinBeta",
)[
  Suppose that some letter $s$ has $p(s) > 0$ and $q(s) = 0$, and let $0 < epsilon < 1$.
  Show that $beta_n (epsilon) = 0$ for all large $n$.
  Explain why Stein's lemma assumes that $nu_p << nu_q$.
]

#exercise(
  "intermediate",
  title: "The Chernoff bound",
  hint: [If $a <= b$, then $a = a^lambda a^(1 - lambda) <= a^lambda b^(1 - lambda)$.],
  compare: "Meat.bayesError_le_pow",
)[
  Prove that $min(a, b) <= a^lambda b^(1 - lambda)$ for $a, b >= 0$ and $lambda in [0, 1]$.
  Deduce that $e_n <= (sum_s p(s)^lambda q(s)^(1 - lambda))^n$.
  For $lambda = 1/2$, this is the Bhattacharyya bound.
]

#exercise(
  "advanced",
  title: "Sanov's theorem needs an open set",
  hint: [The value $P_x ({1})$ of a type is a rational number.],
)[
  Let $q$ be the fair coin, and let $E$ be the set that contains only the law $P$ with $P({1}) = 1 \/ sqrt(2)$.
  Show that $q^n ({x : P_x in E}) = 0$ for every $n >= 1$, while $D(E || q)$ is finite and positive.
  Explain which hypothesis of Sanov's theorem fails.
]

#exercise(
  "intermediate",
  title: "A bound on the optimal error in Lean",
  formalize: true,
  hint: [Use the test $A = S^n$, which has type-I error $0$. The infimum is over a finite type, so it is bounded below by $0$, and `ciInf_le` applies.],
  compare: "Meat.steinBeta",
)[
  Prove in Lean that `Meat.steinBeta p q n ε ≤ 1` for every `ε ≥ 0`.
]

== Open problems

#exercise(
  "basic",
  title: "Open problems as propositions",
  answer: [
    A theorem proved with `sorry` can be used in other proofs as if it were true, and Lean would accept those proofs.
    A definition `def P : Prop` is only a statement: no proof can use it as a fact without a proof of it.
    So the library never claims or assumes an open problem.
  ],
)[
  The library states each open problem as `def ... : Prop`, not as a theorem with `sorry`.
  Explain why.
]

#exercise(
  "basic",
  title: "A code for the 5-cycle",
  compare: "Meat.sqrt_five_le_shannonCapacity_cycleGraph_five",
  answer: [
    The words are $(0, 0)$, $(1, 2)$, $(2, 4)$, $(3, 1)$ and $(4, 3)$.
    Two first letters $i$ and $i + 1$ give second letters $2 i$ and $2 i + 2$, which differ by $2$ modulo $5$, so they are distinct and not adjacent.
    Two first letters that differ by $2$ are distinct and not adjacent.
    So the five words are pairwise not adjacent in $C_5^(times.square 2)$.
    $C_5$ has no independent set of size $3$, so $alpha(C_5) = 2$, while $Theta(C_5) >= 5^(1\/2) = sqrt(5) > 2$.
  ],
)[
  Check that the five words $(i, 2 i mod 5)$, $i = 0, dots, 4$, are pairwise not adjacent in $C_5^(times.square 2)$.
  Compute $alpha(C_5)$, and conclude that $Theta(C_5) > alpha(C_5)$.
]

#exercise(
  "basic",
  title: "A polymatroid that is not entropic",
  compare: "Meat.shannonRegion_not_subset_zhangYeungRegion",
  answer: [
    $I_h (2; 3) = 2 + 2 - 3 = 1$, $I_h (0; 1) = 2 + 2 - 4 = 0$, $I_h (0; {2, 3}) = 2 + 3 - 4 = 1$, $I_h (2; 3 given 0) = 3 + 3 - 4 - 2 = 0$ and $I_h (2; 3 given 1) = 0$ in the same way.
    The left side of the Zhang-Yeung inequality is $2$, and the right side is $1$.
  ],
)[
  Let $h(emptyset) = 0$, $h(A) = 2$ for singletons, $h({0, 1}) = 4$, $h(A) = 3$ for the other pairs, and $h(A) = 4$ for sets with three or four elements.
  Compute the five terms $I_h$ of the Zhang-Yeung inequality, and check that $h$ violates it.
]

#exercise(
  "basic",
  title: "Bounds for the deletion channel",
  compare: "Meat.deletionCapacity_le_erasure",
  answer: [
    The lower bound is $1 - h_2 (0.1) approx 0.531$ bits, and the upper bound is $1 - 0.1 = 0.9$ bits.
    The capacity is between them, and its exact value is unknown.
  ],
)[
  For the deletion probability $d = 0.1$, compute Gallager's lower bound $1 - h_2 (d)$ and the erasure upper bound $1 - d$, in bits.
]

#exercise(
  "intermediate",
  title: "The entropy region for two variables",
  hint: [Write a polymatroid $(h_1, h_2, h_(12))$ as $a (1, 0, 1) + b (0, 1, 1) + c (1, 1, 1)$, and find a pair of random variables for each of the three vectors.],
  compare: "Meat.entropyVector_mem_shannonRegion",
)[
  For $n = 2$, a vector is $(h({0}), h({1}), h({0, 1}))$.
  Show that every polymatroid on two elements is a combination with nonnegative coefficients of $(1, 0, 1)$, $(0, 1, 1)$ and $(1, 1, 1)$.
  Show that each of these three vectors, multiplied by $log 2$, is an entropy vector.
  You may use without proof that the closure of $Gamma^*_n$ is a convex cone.
  Deduce that $overline(Gamma^*_2) = Gamma_2$.
]

#exercise(
  "intermediate",
  title: "The parity of two bits in the Courtade-Kumar problem",
  hint: [$Y_1 plus.o Y_2 = f(X) plus.o Z_1 plus.o Z_2$, where $Z_i$ is the noise on bit $i$. Show that $I(f(X); Y) = I(f(X); Y_1 plus.o Y_2)$.],
  compare: "Meat.CourtadeKumar.mutualInfo_dictator",
)[
  Let $n = 2$ and $f(x) := x_1 plus.o x_2$.
  Show that $I(f(X); Y) = 1 - h_2 (2 alpha (1 - alpha))$ bits.
  Show that this is at most $1 - h_2 (alpha)$, the value for the dictator $f(x) = x_1$.
]

#exercise(
  "intermediate",
  title: "A secret key from a noisy eavesdropper",
  hint: [$I(X; Y) = H(X)$ because $Y = X$. Also $I(X; Y given Z) = H(X given Z)$.],
  compare: ("Meat.SecretKey.le_condMutualInfo_of_achievable", "Meat.SecretKey.achievable_of_lt"),
)[
  Let $X$ be a uniform bit, $Y := X$, and $Z := X plus.o N$ with $P(N = 1) = 1/4$ and $N$ independent of $X$.
  Compute the upper bound $I(X; Y given Z)$ and the lower bound $I(X; Y) - I(X; Z)$ on the secret key capacity.
  Conclude that $C_"SK" = h_2 (1/4) approx 0.811$ bits for this law.
]

#exercise(
  "advanced",
  title: "Lovász's umbrella",
  hint: [$cos (4 pi \/ 5) = -(sqrt(5) + 1) \/ 4$.],
  compare: "Meat.shannonCapacity_cycleGraph_five",
)[
  Let $r := sqrt(5)$, $sigma := sqrt(1 - r \/ 5)$, $tau := sqrt(r \/ 5)$ and $u_k := (sigma cos(2 pi k \/ 5), sigma sin(2 pi k \/ 5), tau)$ for $k = 0, dots, 4$, with handle $c := (0, 0, 1)$.
  Check that each $u_k$ is a unit vector, that $chevron.l u_k, u_(k + 2) chevron.r = 0$, and that $sqrt(5) chevron.l u_k, c chevron.r^2 = 1$.
  Deduce that $Theta(C_5) <= sqrt(5)$.
]

#exercise(
  "advanced",
  title: "The capacity of a graph is a limit",
  hint: [Let $a_n := log alpha(G^(times.square n))$. Show that $a_(m + n) >= a_m + a_n$, and prove Fekete's lemma: for such a sequence, $a_n \/ n$ tends to $sup_n a_n \/ n$.],
  compare: "Meat.mul_indepNum_le_strongProd",
)[
  Prove that $alpha(G^(times.square n))^(1 \/ n) -> Theta(G)$ as $n -> infinity$.
  The Lean library defines $Theta(G)$ as the supremum and does not prove that it is a limit.
]

#exercise(
  "advanced",
  title: "The Courtade-Kumar conjecture for one bit in Lean",
  formalize: true,
  hint: [For $n = 1$ there are four Boolean functions. For a constant function, the information is $0$. For the two others, the function is injective, so the information is the information of the dictator. `Meat.mutualInfo_comp_right_of_injective` and `Meat.mutualInfo_comm` relabel one argument.],
  compare: ("Meat.CourtadeKumarConjecture", "Meat.CourtadeKumar.mutualInfo_dictator"),
)[
  Read the definition `Meat.CourtadeKumarConjecture`.
  State its case $n = 1$ as a Lean theorem, and prove it.
]

== Short answers

This section collects the answers to the basic exercises.

#context {
  for (number, title, body) in exercise-answers.final() {
    block(above: 1em, breakable: true)[*#number* #if title != none [(#title)]. #body]
  }
}
