import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.Lattice.Nat

namespace Meat

structure Network (V : Type*) where
  cap : V → V → ℕ

namespace Network

variable {V : Type*}

def IsAcyclic (N : Network V) : Prop :=
  ∃ rank : V → ℕ, ∀ u v, 0 < N.cap u v → rank u < rank v

def cutValue [Fintype V] [DecidableEq V] (N : Network V) (S : Finset V) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, N.cap u v

noncomputable def minCut [Fintype V] [DecidableEq V] (N : Network V) (s t : V) : ℕ :=
  ⨅ S : {S : Finset V // s ∈ S ∧ t ∉ S}, cutValue N S.1

structure Code (N : Network V) (s : V) (Msg F : Type*) where
  edge : ∀ u v : V, Msg → Fin (N.cap u v) → F
  causal : ∀ u v : V, u ≠ s →
    ∃ f : (∀ w : V, Fin (N.cap w u) → F) → Fin (N.cap u v) → F,
      ∀ m : Msg, edge u v m = f (fun w => edge w u m)

def Code.Decodes {N : Network V} {s : V} {Msg F : Type*} (c : Code N s Msg F) (t : V) : Prop :=
  ∃ d : (∀ w : V, Fin (N.cap w t) → F) → Msg, ∀ m : Msg, d (fun w => c.edge w t m) = m

end Network

end Meat
