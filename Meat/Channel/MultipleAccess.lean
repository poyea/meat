import Meat.Channel.Basic

open MeasureTheory
open scoped ENNReal

namespace Meat

structure MACCode (M₁ M₂ A₁ A₂ B : Type*) (n : ℕ) where
  enc₁ : M₁ → Fin n → A₁
  enc₂ : M₂ → Fin n → A₂
  dec : (Fin n → B) → M₁ × M₂

namespace MACCode

variable {M₁ M₂ A₁ A₂ B : Type*} {n : ℕ}

noncomputable def errorProb [Fintype B] [DecidableEq M₁] [DecidableEq M₂]
    (c : MACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) (m : M₁ × M₂) : ℝ≥0∞ :=
  ∑ y : Fin n → B,
    if c.dec y = m then 0
    else DMC.blockProb W (fun i => (c.enc₁ m.1 i, c.enc₂ m.2 i)) y

noncomputable def avgError [Fintype B] [Fintype M₁] [Fintype M₂]
    [DecidableEq M₁] [DecidableEq M₂]
    (c : MACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) : ℝ≥0∞ :=
  (∑ m : M₁ × M₂, c.errorProb W m) / ((Fintype.card M₁ : ℝ≥0∞) * (Fintype.card M₂ : ℝ≥0∞))

end MACCode

namespace MAC

variable {A₁ A₂ B : Type*}

def Achievable [Fintype B] (W : DMC (A₁ × A₂) B) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k₁ k₂ : ℕ, Real.exp (n * R₁) ≤ k₁ ∧ Real.exp (n * R₂) ≤ k₂ ∧
      ∃ c : MACCode (Fin k₁) (Fin k₂) A₁ A₂ B n, c.avgError W ≤ ε

def achievableRegion [Fintype B] (W : DMC (A₁ × A₂) B) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ Achievable W R.1 R.2}

variable [Fintype A₁] [MeasurableSpace A₁] [Fintype A₂] [MeasurableSpace A₂]
  [Fintype B] [MeasurableSpace B]

noncomputable def jointMeasure (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    Measure (A₁ × A₂ × B) :=
  (p₁.bind fun a₁ => p₂.bind fun a₂ => (W (a₁, a₂)).map fun b => (a₁, a₂, b)).toMeasure

noncomputable def pentagon (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧
    R.1 ≤ condMutualInfo (fun ω : A₁ × A₂ × B => ω.1) (fun ω : A₁ × A₂ × B => ω.2.2)
      (fun ω : A₁ × A₂ × B => ω.2.1) (jointMeasure W p₁ p₂) ∧
    R.2 ≤ condMutualInfo (fun ω : A₁ × A₂ × B => ω.2.1) (fun ω : A₁ × A₂ × B => ω.2.2)
      (fun ω : A₁ × A₂ × B => ω.1) (jointMeasure W p₁ p₂) ∧
    R.1 + R.2 ≤ mutualInfo (fun ω : A₁ × A₂ × B => (ω.1, ω.2.1))
      (fun ω : A₁ × A₂ × B => ω.2.2) (jointMeasure W p₁ p₂)}

noncomputable def capacityRegion (W : DMC (A₁ × A₂) B) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ (⋃ p₁ : PMF A₁, ⋃ p₂ : PMF A₂, pentagon W p₁ p₂))

end MAC

end Meat
