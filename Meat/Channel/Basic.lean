import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Meat.Shannon.Entropy

open MeasureTheory
open scoped ENNReal

namespace Meat

abbrev DMC (A B : Type*) := A → PMF B

structure BlockCode (M A B : Type*) (n : ℕ) where
  enc : M → Fin n → A
  dec : (Fin n → B) → M

namespace DMC

variable {A B : Type*}

noncomputable def blockProb {n : ℕ} (W : DMC A B) (x : Fin n → A) (y : Fin n → B) : ℝ≥0∞ :=
  ∏ i, W (x i) (y i)

noncomputable def jointMeasure [MeasurableSpace A] [MeasurableSpace B]
    (W : DMC A B) (p : PMF A) : Measure (A × B) :=
  (p.bind fun a => (W a).map fun b => (a, b)).toMeasure

noncomputable def inputMutualInfo [Fintype A] [MeasurableSpace A] [Fintype B] [MeasurableSpace B]
    (W : DMC A B) (p : PMF A) : ℝ :=
  mutualInfo (fun ω : A × B => ω.1) (fun ω : A × B => ω.2) (jointMeasure W p)

noncomputable def capacity [Fintype A] [MeasurableSpace A] [Fintype B] [MeasurableSpace B]
    (W : DMC A B) : ℝ :=
  ⨆ p : PMF A, inputMutualInfo W p

end DMC

namespace BlockCode

variable {M A B : Type*} {n : ℕ}

noncomputable def errorProb [Fintype B] [DecidableEq M]
    (c : BlockCode M A B n) (W : DMC A B) (m : M) : ℝ≥0∞ :=
  ∑ y : Fin n → B, if c.dec y = m then 0 else DMC.blockProb W (c.enc m) y

noncomputable def avgError [Fintype B] [Fintype M] [DecidableEq M]
    (c : BlockCode M A B n) (W : DMC A B) : ℝ≥0∞ :=
  (∑ m, c.errorProb W m) / (Fintype.card M : ℝ≥0∞)

end BlockCode

namespace DMC

variable {A B : Type*}

def Achievable [Fintype B] (W : DMC A B) (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : BlockCode (Fin k) A B n, c.avgError W ≤ ε

end DMC

end Meat
