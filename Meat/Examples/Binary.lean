import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Probability.Distributions.Bernoulli
import Meat.Shannon.Inequalities

open MeasureTheory ProbabilityTheory

namespace Meat.Examples

theorem measureEntropy_bool (ν : Measure Bool) [IsProbabilityMeasure ν] :
    measureEntropy ν = Real.binEntropy (ν.real {true}) := by
  have h := sum_measureReal_singleton_eq_one ν
  rw [Fintype.sum_bool] at h
  rw [measureEntropy, Fintype.sum_bool, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    ← h, add_sub_cancel_left]

theorem entropy_bool {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → Bool} (hX : Measurable X) :
    H[X ; μ] = Real.binEntropy (μ.real {ω | X ω = true}) := by
  rw [entropy, measureEntropy_bool, map_measureReal_apply hX (measurableSet_singleton _)]
  rfl

theorem measureEntropy_bernoulli (p : unitInterval) :
    measureEntropy (bernoulliMeasure true false p) = Real.binEntropy p := by
  rw [measureEntropy_bool]
  simp

theorem binEntropy_half : Real.binEntropy (1 / 2) = Real.log 2 := by
  rw [one_div, Real.binEntropy_two_inv]

theorem binEntropy_symm (p : ℝ) : Real.binEntropy (1 - p) = Real.binEntropy p :=
  Real.binEntropy_one_sub p

theorem binEntropy_le_log_two (p : ℝ) : Real.binEntropy p ≤ Real.log 2 :=
  Real.binEntropy_le_log_two

theorem binEntropy_eq_log_two_iff (p : ℝ) : Real.binEntropy p = Real.log 2 ↔ p = 1 / 2 := by
  rw [Real.binEntropy_eq_log_two, one_div]

end Meat.Examples
