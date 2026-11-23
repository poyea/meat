#import "../../meat.typ": *

== Block-Markov relay codes
#source("Meat.Open.RelayAchievability")

Decode-forward achievability uses block-Markov coding (Cover and El Gamal, 1979).
This section defines the block-Markov relay code and proves that its relay functions are causal.
The next two sections prove decode-forward achievability and the capacity of the physically degraded relay channel.

The transmission has $b + 1$ blocks of length $m$, so its length is $(b + 1) m$.
The sender has $b$ messages $w_0, dots, w_(b - 1)$ in a set $K$, and a fixed symbol $k_0 in K$ stands for the messages before the first block and after the last.

#definition(
  "Blocks of a sequence",
  lean: ("Meat.Relay.blockOf", "Meat.Relay.finProdFinEquiv_lt"),
)[
  A time in $[(b + 1) m]$ is a pair of a block $beta$ and a position $j$ in the block, through the bijection $(beta, j) |-> j + m beta$.
  Block $beta$ of a sequence $y$ is the sequence of its values at the positions of block $beta$.
  Every time of an earlier block comes before every time of a later block.
]

#definition(
  "Relay and receiver estimates",
  lean: ("Meat.Relay.relayEstimate", "Meat.Relay.relayEstimate_congr", "Meat.Relay.destEstimate"),
)[
  Let $phi : K times B_1^m -> K$ be the relay decoder and $psi : K times B^m -> K$ the receiver decoder.
  The relay estimate starts at $k_0$, and after block $beta$ it is $phi(hat(w)_(beta - 1), y_1 "in block" beta)$.
  The estimate used in block $beta$ depends only on the relay outputs of the blocks before $beta$.
  The receiver decodes backward: it starts at $k_0$ for the last block, and from its estimate of $w_beta$ and block $beta$ it gets its estimate of $w_(beta - 1)$ with $psi$.
][
  The second statement is an induction on the block index.
  Each step uses only one earlier block, on which the two output sequences agree.
]

#definition(
  "Block-Markov code",
  lean: ("Meat.Relay.currentMessage", "Meat.Relay.previousMessage", "Meat.Relay.blockMarkovCode"),
)[
  Let $C_1 : K -> A_1^m$ be the relay codebook and $C : K times K -> A^m$ the sender codebook.
  In block $beta$ the sender sends $C(w_beta, w_(beta - 1))$, with $w_b := k_0$ and $w_(-1) := k_0$.
  The relay sends $C_1 (hat(w)_(beta - 1))$, where $hat(w)_(beta - 1)$ is its estimate from the earlier blocks.
  The receiver outputs its backward estimates.
  The relay functions are causal, so this is a relay code.
][
  Causality follows from the property of the relay estimate and the order of the blocks.
]

The rate of this code is $b log |K| \/ ((b + 1) m)$, which tends to $log |K| \/ m$ as $b$ grows.
With random codebooks, $C_1$ independent with law $p(x_1)^m$ and $C(w, w')$ with law $p(x given x_1)^m$ given $C_1 (w')$, typicality decoders give a small error when the rate is below $I(X; Y_1 given X_1)$ at the relay and below $I(X, X_1; Y)$ at the receiver.
The next section carries out this analysis.

== Decode-forward analysis
#source("Meat.Open.RelayDecodeForward")

The analysis compares the relay code with a genie code, in which the relay always knows the previous message.
On the outputs where every relay estimate is correct, the two codes have the same probabilities.
This bounds the error of the block-Markov code by a sum of single-block errors of the genie code.
Each single-block error is a decoding error of a superposition code, and the averages over random codebooks come from the superposition analysis of the broadcast channel.

#lemma("Comparison of two laws", lean: "Meat.Relay.sum_ite_le_of_agree")[
  Let $f$ and $g$ be probability mass functions on a finite set, equal on a set $G$.
  Then for every event $E$, $f(E) <= g(E union G^c)$.
][
  On $G$ the two functions agree, and off $G$ we have $f(E) - g(E union G^c) <= f - g$ pointwise.
  The sum of $f - g$ off $G$ is $0$, because both sums are $1$ and the sums over $G$ agree.
]

#lemma(
  "Blocks of a product law",
  lean: (
    "Meat.Relay.blockSplit",
    "Meat.Relay.blockSplit_apply",
    "Meat.Relay.toReal_blockProb_split",
    "Meat.Relay.sum_blockProb_block",
  ),
)[
  Sequences of length $b m$ are tuples of $b$ blocks of length $m$, and $W^(b m)$ is the product of the block laws.
  So the probability under $W^(b m)$ of an event that depends only on block $beta$ is its probability under the law of block $beta$.
][
  The bijection $(beta, j) |-> j + m beta$ turns the product over times into a product over blocks.
  All other blocks sum to $1$.
]

#lemma(
  "Genie comparison",
  lean: (
    "Meat.Relay.genieInput",
    "Meat.Relay.blockOf_genieInput",
    "Meat.Relay.seqProb_eq_of_good",
    "Meat.Relay.good_of_relay",
    "Meat.Relay.dec_of_dest",
    "Meat.Relay.errorProb_blockMarkov_le",
  ),
)[
  The genie input in block $beta$ is $(C(w_beta, w_(beta - 1)), C_1 (w_(beta - 1)))$.
  If every relay estimate is correct on an output sequence, the relay code and the genie input give it the same probability.
  If the relay decodes $w_k$ correctly from block $k$ and the true $w_(k - 1)$ for every $k$, then every relay estimate is correct.
  If the receiver decodes $w_k$ correctly from block $k + 1$ and the true $w_(k + 1)$ for every $k$, then it outputs $w$.
  So $lambda_w$ is at most the sum over $k$ of these single-block errors under the genie law, where the relay errors use the channel to $Y_1$ and the receiver errors use the channel to $Y$.
][
  The second and third statements are inductions over the blocks, forward for the relay and backward for the receiver.
  The bound follows from the comparison of two laws with $G$ the set where all relay estimates are correct, and from the lemma on blocks of a product law.
]

#definition(
  "Superposition codebooks for the relay",
  lean: (
    "Meat.Relay.satLaw",
    "Meat.Relay.relayBC",
    "Meat.Relay.destBC",
    "Meat.Relay.channel₁_relayBC",
    "Meat.Relay.fst_eq_of_codebookWeight_ne_zero",
  ),
)[
  Let $p_U in Delta(A_1)$ and $p_X : A_1 -> Delta(A)$.
  The satellite law is $(x_1, x)$ with $x tilde p_X (dot given x_1)$, so a satellite codeword carries its cloud.
  The relay channel $W$ gives two broadcast-type channels from $A_1 times A$: one whose first output is $Y_1$, and one whose first output is $Y$.
  Codebooks are random superposition codebooks $C_U : K -> A_1^m$ and $C_X : K times K -> (A_1 times A)^m$, with cloud index the previous message.
  Every codebook with positive weight has $C_X (a, b)$ with first coordinates $C_U (b)$.
]

#lemma(
  "Average single-block errors",
  lean: ("Meat.Relay.sum_codebookWeight_relayError", "Meat.Relay.sum_codebookWeight_destError"),
)[
  For a typicality decoder at the relay that knows the cloud $b$ and searches the satellites, the average error is at most
  $ (1 - P(T_epsilon)) + (|K| - 1) e^(-m (I(X; Y_1 given X_1) - 4 epsilon)). $
  For a typicality decoder at the receiver that knows the satellite index and searches the clouds, the average error is at most
  $ (1 - P(T_epsilon)) + (|K| - 1) e^(-m (I(X, X_1; Y) - 3 epsilon)). $
][
  On the support of the codebook weight, the genie channel input is the satellite codeword.
  Then the typicality decoder bound splits the error into a miss term and false alarms.
  A wrong satellite in the same cloud is the same-cloud term of the broadcast analysis, and a wrong cloud is the other-cloud term.
]

#theorem(
  "Decode-forward codes",
  lean: (
    "Meat.Relay.currentMessage_castSucc",
    "Meat.Relay.previousMessage_succ",
    "Meat.Relay.errorProb_ne_top'",
    "Meat.Relay.avgError_le_ofReal'",
    "Meat.Relay.relayDecoder",
    "Meat.Relay.destDecoder",
    "Meat.Relay.dfCode",
    "Meat.Relay.dfBound",
    "Meat.Relay.sum_codebookWeight_errorProb_dfCode_le",
    "Meat.Relay.exists_dfCode_avgError_le",
  ),
)[
  For every $b$, $m$ and $epsilon$ there are codebooks such that the block-Markov code with typicality decoders has average error at most
  $ b ((1 - P(T_epsilon^1)) + (|K| - 1) e^(-m (I(X; Y_1 given X_1) - 4 epsilon))) + b ((1 - P(T_epsilon^2)) + (|K| - 1) e^(-m (I(X, X_1; Y) - 3 epsilon))). $
][
  Average the genie comparison over the random codebooks, with the bounds on single-block errors.
  The bound does not depend on the messages, so it bounds the average over codebooks of $overline(lambda)$.
  Some codebook is at most the average.
]

== Capacity of the degraded relay channel
#source("Meat.Open.RelayCapacity")

#definition(
  "Relabeled and padded codes",
  lean: (
    "Meat.RelayCode.relabel",
    "Meat.RelayCode.avgError_relabel",
    "Meat.RelayCode.pad",
    "Meat.RelayCode.splitEquiv",
    "Meat.RelayCode.splitEquiv_symm_castAdd",
    "Meat.RelayCode.splitEquiv_symm_natAdd",
    "Meat.RelayCode.errorProb_pad",
    "Meat.RelayCode.avgError_pad",
  ),
)[
  A bijection of message sets turns a relay code into one with the same average error.
  A relay code of length $n$ becomes a code of length $n + r$ by sending fixed symbols at the end and ignoring the last $r$ outputs.
  It has the same error probabilities.
][
  The extra letters do not depend on the messages, and their outputs sum to $1$.
]

#lemma(
  "Input laws as superposition laws",
  lean: (
    "Meat.Relay.exists_input_decomp",
    "Meat.Relay.law₁_relayBC",
    "Meat.Relay.law₁_destBC",
    "Meat.Relay.relayInfo_eq",
    "Meat.Relay.destInfo_eq",
  ),
)[
  Every $p in Delta(A times A_1)$ is the law of $(X, X_1)$ with $X_1 tilde p_U$ and $X tilde p_X (dot given X_1)$.
  Under the corresponding superposition laws, the two rates of the single-block errors are $I(X; Y_1 given X_1)$ and $I(X, X_1; Y)$ under $p W$.
][
  Take $p_U$ the law of $X_1$ and $p_X$ its conditional law where $p_U > 0$.
  The superposition laws are push-forwards of $p W$, and the information terms are unchanged by injective relabeling.
]

#theorem(
  "Decode-forward achievability",
  lean: (
    "Meat.Relay.achievable_of_nonpos",
    "Meat.Relay.achievable_mono",
    "Meat.Relay.achievable_of_lt_info",
    "Meat.Relay.achievable_of_lt_decodeForwardRate",
    "Meat.Relay.decodeForwardBound_nonneg",
    "Meat.Relay.Icc_decodeForwardBound_subset",
  ),
)[
  Let all four alphabets be nonempty.
  Every $R < R_"df" (p)$ is achievable, and $[0, C_"df"]$ is contained in the closure of the set of achievable rates.
][
  Rates $R <= 0$ are achievable with one message.
  For $R > 0$ let $g := min(I(X; Y_1 given X_1), I(X, X_1; Y)) - R$, $epsilon := g \/ 16$ and $R'' := R + g \/ 2$.
  Fix $b$ with $b g \/ 2 > R$ and take $|K| = ceil(e^(m R''))$.
  Then the bound on decode-forward codes tends to $0$ as $m$ grows, because $R'' < I - 4 epsilon$ for both rates.
  For a length $n$, write $n = (b + 1) m + r$ with $r <= b$, relabel the messages as $[|K|^b]$ and pad with $r$ letters.
  For large $m$, $n R <= (b + 1)(m + 1) R <= b m R'' <= log |K|^b$.
  The last statement follows as in the channel coding theorem.
]

#theorem("Capacity of the degraded relay channel", lean: "Meat.Relay.closure_achievableRates_eq_of_isDegraded")[
  Let all four alphabets be nonempty.
  If $W$ is physically degraded, the closure of the set of achievable rates is $[0, C_"df"]$.
][
  The inclusion $supset.eq$ is decode-forward achievability.
  The inclusion $subset.eq$ is the cut-set bound, with $C_"cs" = C_"df"$ for degraded channels.
]
