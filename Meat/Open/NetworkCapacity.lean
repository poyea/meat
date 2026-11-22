import Mathlib.Computability.Partrec
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Field.Defs
import Meat.Network.Coding

namespace Meat

namespace Network

variable {V : Type*} {m : ℕ}

structure MultiCode (N : Network V) (src : Fin m → V) (Msg F : Type*) where
  edge : ∀ u v : V, (Fin m → Msg) → Fin (N.cap u v) → F
  causal : ∀ u v : V,
    ∃ f : (∀ w : V, Fin (N.cap w u) → F) → ({i // src i = u} → Msg) → Fin (N.cap u v) → F,
      ∀ M : Fin m → Msg, edge u v M = f (fun w => edge w u M) fun i => M i.1

def MultiCode.Decodes {N : Network V} {src : Fin m → V} {Msg F : Type*}
    (c : MultiCode N src Msg F) (t : V) (i : Fin m) : Prop :=
  ∃ d : (∀ w : V, Fin (N.cap w t) → F) → ({j // src j = t} → Msg) → Msg,
    ∀ M : Fin m → Msg, d (fun w => c.edge w t M) (fun j => M j.1) = M i

def Solvable (N : Network V) (src : Fin m → V) (dem : V → Fin m → Prop) (k ℓ : ℕ) : Prop :=
  ∃ q : ℕ, 2 ≤ q ∧ ∃ c : MultiCode N src (Fin k → Fin q) (Fin ℓ → Fin q),
    ∀ t i, dem t i → c.Decodes t i

def MultiCode.IsLinear {N : Network V} {src : Fin m → V} {K : Type*} [Field K] {k ℓ : ℕ}
    (c : MultiCode N src (Fin k → K) (Fin ℓ → K)) : Prop :=
  ∀ u v (a : K) (M M' : Fin m → Fin k → K),
    c.edge u v (a • M + M') = a • c.edge u v M + c.edge u v M'

def LinearSolvable (N : Network V) (src : Fin m → V) (dem : V → Fin m → Prop) (K : Type*)
    [Field K] (k ℓ : ℕ) : Prop :=
  ∃ c : MultiCode N src (Fin k → K) (Fin ℓ → K), c.IsLinear ∧ ∀ t i, dem t i → c.Decodes t i

noncomputable def codingCapacity (N : Network V) (src : Fin m → V) (dem : V → Fin m → Prop) : ℝ :=
  sSup {r : ℝ | ∃ k ℓ : ℕ, 0 < ℓ ∧ Solvable N src dem k ℓ ∧ r = k / ℓ}

end Network

abbrev NetworkInstance := ℕ × List (ℕ × ℕ) × List ℕ × List (ℕ × ℕ)

def NetworkInstance.network (I : NetworkInstance) : Network (Fin (I.1 + 1)) :=
  ⟨fun u v => I.2.1.count ((u : ℕ), (v : ℕ))⟩

def NetworkInstance.source (I : NetworkInstance) (i : Fin I.2.2.1.length) : Fin (I.1 + 1) :=
  Fin.ofNat _ (I.2.2.1.get i)

def NetworkInstance.demand (I : NetworkInstance) (t : Fin (I.1 + 1))
    (i : Fin I.2.2.1.length) : Prop :=
  ((t : ℕ), (i : ℕ)) ∈ I.2.2.2

noncomputable def NetworkInstance.capacity (I : NetworkInstance) : ℝ :=
  Network.codingCapacity I.network I.source I.demand

def NetworkCodingCapacityComputable : Prop :=
  ∃ f : NetworkInstance × ℕ → ℤ × ℕ, Computable f ∧ ∀ I k,
    I.network.IsAcyclic →
      |((f (I, k)).1 : ℝ) / ((f (I, k)).2 + 1) - I.capacity| ≤ 1 / ((k : ℝ) + 1)

def LinearCodingInsufficient : Prop :=
  ∃ I : NetworkInstance, I.network.IsAcyclic ∧ Network.Solvable I.network I.source I.demand 1 1 ∧
    ∀ (K : Type) [Field K] [Fintype K] (k : ℕ), 0 < k →
      ¬Network.LinearSolvable I.network I.source I.demand K k k

end Meat
