import Mathlib.Probability.Distributions.Gaussian.Real
import Meat.Continuous.Gaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Meat

namespace AWGN

noncomputable def noise (N : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 N.toNNReal

instance isProbabilityMeasure_noise (N : ℝ) (n : ℕ) : IsProbabilityMeasure (noise N n) := by
  unfold noise
  infer_instance

structure Code (P : ℝ) (n k : ℕ) where
  enc : Fin k → Fin n → ℝ
  power : ∀ m, ∑ i, enc m i ^ 2 ≤ n * P
  dec : (Fin n → ℝ) → Fin k
  measurable_dec : Measurable dec

namespace Code

variable {P : ℝ} {n k : ℕ}

noncomputable def errorProb (c : Code P n k) (N : ℝ) (m : Fin k) : ℝ≥0∞ :=
  noise N n {z | c.dec (c.enc m + z) ≠ m}

noncomputable def avgError (c : Code P n k) (N : ℝ) : ℝ≥0∞ :=
  (∑ m, c.errorProb N m) / k

end Code

def Achievable (P N R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : Code P n k, c.avgError N ≤ ε

theorem achievable_zero {P : ℝ} (hP : 0 ≤ P) (N : ℝ) : Achievable P N 0 := by
  intro ε _
  refine ⟨0, fun n _ => ⟨1, by simp, ⟨fun _ _ => 0, fun _ => by
    simpa using mul_nonneg n.cast_nonneg hP,
    fun _ => 0, measurable_const⟩, ?_⟩⟩
  simp [Code.avgError, Code.errorProb, Subsingleton.elim _ (0 : Fin 1)]

theorem awgnCapacity_nonneg {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) : 0 ≤ awgnCapacity P N :=
  mul_nonneg (by norm_num) (Real.log_nonneg (by have := div_nonneg hP hN.le; linarith))

theorem closure_achievable_eq_of {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (hach : ∀ R, 0 ≤ R → R < awgnCapacity P N → Achievable P N R)
    (hconv : ∀ R, Achievable P N R → R ≤ awgnCapacity P N) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable P N R} = Set.Icc 0 (awgnCapacity P N) := by
  refine subset_antisymm (closure_minimal (fun R hR => ⟨hR.1, hconv R hR.2⟩) isClosed_Icc)
    fun R hR => ?_
  rcases (awgnCapacity_nonneg hP hN).eq_or_lt with h | h
  · rw [← h, Set.Icc_self, Set.mem_singleton_iff] at hR
    exact subset_closure ⟨hR.symm ▸ le_rfl, hR ▸ achievable_zero hP N⟩
  · rw [← closure_Ico h.ne] at hR
    refine closure_mono (fun R (hR : R ∈ Set.Ico 0 (awgnCapacity P N)) => ?_) hR
    exact ⟨hR.1, hach R hR.1 hR.2⟩

end AWGN

end Meat
