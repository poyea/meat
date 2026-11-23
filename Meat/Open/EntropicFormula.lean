import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.Monoid
import Meat.Channel.Basic

open scoped ENNReal

namespace Meat

structure EntropicFormula (m r : ℕ) where
  L : ℕ
  J : ℕ
  a : Fin L → ℝ
  b : Fin L → ℝ
  c : Fin L → Finset (Fin m) × Finset (Fin r) → ℝ
  d : Fin J → Finset (Fin m) × Finset (Fin r) → ℝ

namespace EntropicFormula

noncomputable def pmfEntropy {α : Type*} [Fintype α] (p : PMF α) : ℝ :=
  ∑ a, Real.negMulLog (p a).toReal

def mask {α : Type*} {r : ℕ} (T : Finset (Fin r)) (v : Fin r → α) : Fin r → Option α :=
  fun j => if j ∈ T then some (v j) else none

variable {m r k : ℕ} {C : Type*} [Fintype C]

noncomputable def entropyVector (P : PMF ((Fin m → Fin k) × (Fin r → C)))
    (S : Finset (Fin m) × Finset (Fin r)) : ℝ :=
  pmfEntropy (P.map fun ω => (mask S.1 ω.1, mask S.2 ω.2))

def Admissible (F : EntropicFormula m r) (h : Finset (Fin m) × Finset (Fin r) → ℝ) : Prop :=
  ∀ j, ∑ S, F.d j S * h S = 0

def region (F : EntropicFormula m r) (h : Finset (Fin m) × Finset (Fin r) → ℝ) :
    Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∀ l, F.a l * R.1 + F.b l * R.2 ≤ ∑ S, F.c l S * h S}

def value {ι : Type*} (F : EntropicFormula m r)
    (law : ι → PMF ((Fin m → Fin k) × (Fin r → C))) : Set (ℝ × ℝ) :=
  closure (⋃ q, ⋃ (_ : F.Admissible (entropyVector (law q))),
    F.region (entropyVector (law q)))

variable {A₁ A₂ B B₁ B₂ : Type*}

def letter₃ (a₁ : A₁) (a₂ : A₂) (b : B) : Fin 3 → A₁ ⊕ A₂ ⊕ B :=
  ![Sum.inl a₁, Sum.inr (Sum.inl a₂), Sum.inr (Sum.inr b)]

def letter₄ (a₁ : A₁) (a₂ : A₂) (b : B₁ × B₂) : Fin 4 → A₁ ⊕ A₂ ⊕ B₁ ⊕ B₂ :=
  ![Sum.inl a₁, Sum.inr (Sum.inl a₂), Sum.inr (Sum.inr (Sum.inl b.1)),
    Sum.inr (Sum.inr (Sum.inr b.2))]

noncomputable def letterLaw₃ (W : DMC (A₁ × A₂) B) (q : PMF ((Fin m → Fin k) × A₁ × A₂)) :
    PMF ((Fin m → Fin k) × (Fin 3 → A₁ ⊕ A₂ ⊕ B)) :=
  q.bind fun ω => (W ω.2).map fun b => (ω.1, letter₃ ω.2.1 ω.2.2 b)

noncomputable def letterLaw₄ (W : DMC (A₁ × A₂) (B₁ × B₂))
    (q : PMF ((Fin m → Fin k) × A₁ × A₂)) :
    PMF ((Fin m → Fin k) × (Fin 4 → A₁ ⊕ A₂ ⊕ B₁ ⊕ B₂)) :=
  q.bind fun ω => (W ω.2).map fun b => (ω.1, letter₄ ω.2.1 ω.2.2 b)

end EntropicFormula

end Meat
