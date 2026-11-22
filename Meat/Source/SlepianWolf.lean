import Mathlib.Probability.ProbabilityMassFunction.Basic
import Meat.Shannon.Entropy

open MeasureTheory
open scoped ENNReal

namespace Meat

structure SWCode (M₁ M₂ S T : Type*) (n : ℕ) where
  enc₁ : (Fin n → S) → M₁
  enc₂ : (Fin n → T) → M₂
  dec : M₁ × M₂ → (Fin n → S) × (Fin n → T)

namespace SWCode

variable {M₁ M₂ S T : Type*} {n : ℕ}

noncomputable def errorProb [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (c : SWCode M₁ M₂ S T n) (p : PMF (S × T)) : ℝ≥0∞ :=
  ∑ xy : (Fin n → S) × (Fin n → T),
    if c.dec (c.enc₁ xy.1, c.enc₂ xy.2) = xy then 0
    else ∏ i, p (xy.1 i, xy.2 i)

end SWCode

namespace SlepianWolf

variable {S T : Type*} [Fintype S] [Fintype T]

def Achievable [DecidableEq S] [DecidableEq T] (p : PMF (S × T)) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k₁ k₂ : ℕ, (k₁ : ℝ) ≤ Real.exp (n * R₁) ∧ (k₂ : ℝ) ≤ Real.exp (n * R₂) ∧
      ∃ c : SWCode (Fin k₁) (Fin k₂) S T n, c.errorProb p ≤ ε

def achievableRegion [DecidableEq S] [DecidableEq T] (p : PMF (S × T)) : Set (ℝ × ℝ) :=
  {R | Achievable p R.1 R.2}

variable [MeasurableSpace S] [MeasurableSpace T]

noncomputable def rateRegion (p : PMF (S × T)) : Set (ℝ × ℝ) :=
  {R |
    condEntropy (fun ω : S × T => ω.1) (fun ω : S × T => ω.2) p.toMeasure ≤ R.1 ∧
    condEntropy (fun ω : S × T => ω.2) (fun ω : S × T => ω.1) p.toMeasure ≤ R.2 ∧
    entropy (fun ω : S × T => ω) p.toMeasure ≤ R.1 + R.2}

end SlepianWolf

end Meat
