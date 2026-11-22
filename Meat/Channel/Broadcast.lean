import Meat.Channel.Basic

open MeasureTheory
open scoped ENNReal

namespace Meat

structure BCCode (M₁ M₂ A B₁ B₂ : Type*) (n : ℕ) where
  enc : M₁ × M₂ → Fin n → A
  dec₁ : (Fin n → B₁) → M₁
  dec₂ : (Fin n → B₂) → M₂

namespace BCCode

variable {M₁ M₂ A B₁ B₂ : Type*} {n : ℕ}

noncomputable def errorProb [Fintype B₁] [Fintype B₂] [DecidableEq M₁] [DecidableEq M₂]
    (c : BCCode M₁ M₂ A B₁ B₂ n) (W : DMC A (B₁ × B₂)) (m : M₁ × M₂) : ℝ≥0∞ :=
  ∑ y : Fin n → B₁ × B₂,
    if (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) = m then 0
    else DMC.blockProb W (c.enc m) y

noncomputable def avgError [Fintype B₁] [Fintype B₂] [Fintype M₁] [Fintype M₂]
    [DecidableEq M₁] [DecidableEq M₂]
    (c : BCCode M₁ M₂ A B₁ B₂ n) (W : DMC A (B₁ × B₂)) : ℝ≥0∞ :=
  (∑ m : M₁ × M₂, c.errorProb W m) / ((Fintype.card M₁ : ℝ≥0∞) * (Fintype.card M₂ : ℝ≥0∞))

end BCCode

namespace BC

variable {A B₁ B₂ V : Type*}

def Achievable [Fintype B₁] [Fintype B₂] (W : DMC A (B₁ × B₂)) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k₁ k₂ : ℕ, Real.exp (n * R₁) ≤ k₁ ∧ Real.exp (n * R₂) ≤ k₂ ∧
      ∃ c : BCCode (Fin k₁) (Fin k₂) A B₁ B₂ n, c.avgError W ≤ ε

def achievableRegion [Fintype B₁] [Fintype B₂] (W : DMC A (B₁ × B₂)) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ Achievable W R.1 R.2}

variable [Fintype A] [MeasurableSpace A] [Fintype B₁] [MeasurableSpace B₁]
  [Fintype B₂] [MeasurableSpace B₂] [Fintype V] [MeasurableSpace V]

noncomputable def jointMeasure (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    Measure (V × A × B₁ × B₂) :=
  (pU.bind fun u => (pX u).bind fun a => (W a).map fun y => (u, a, y)).toMeasure

noncomputable def superpositionRegion (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧
    R.1 ≤ condMutualInfo (fun ω : V × A × B₁ × B₂ => ω.2.1)
      (fun ω : V × A × B₁ × B₂ => ω.2.2.1) (fun ω : V × A × B₁ × B₂ => ω.1)
      (jointMeasure W pU pX) ∧
    R.2 ≤ mutualInfo (fun ω : V × A × B₁ × B₂ => ω.1)
      (fun ω : V × A × B₁ × B₂ => ω.2.2.2) (jointMeasure W pU pX) ∧
    R.1 + R.2 ≤ mutualInfo (fun ω : V × A × B₁ × B₂ => ω.2.1)
      (fun ω : V × A × B₁ × B₂ => ω.2.2.1) (jointMeasure W pU pX)}

end BC

end Meat
