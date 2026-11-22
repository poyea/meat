import Meat.Continuous.Divergence
import Meat.Continuous.Gaussian

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Meat

theorem measureDiffEntropy_le_of_integral_sq_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν ≪ volume) (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal))
    (m : ℝ) {v : ℝ} (hv : 0 < v) (hm : Integrable (fun x => (x - m) ^ 2) ν)
    (hle : ∫ x, (x - m) ^ 2 ∂ν ≤ v) :
    measureDiffEntropy ν ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * v) := by
  set w : ℝ≥0 := ⟨v, hv.le⟩
  have hw : w ≠ 0 := fun h => hv.ne' (congrArg NNReal.toReal h)
  have hwv : (w : ℝ) = v := rfl
  have hpos : (0 : ℝ) < 2 * Real.pi * v := by positivity
  have hle' := measureDiffEntropy_le_neg_integral_log_rnDeriv hν
    (hν.trans (gaussianReal_absolutelyContinuous' m hw)) hf
    (integrable_log_rnDeriv_gaussianReal hν m hw hm)
  rw [neg_integral_log_rnDeriv_gaussianReal hν m hw hm, hwv] at hle'
  rw [show 2 * Real.pi * Real.exp 1 * v = Real.exp 1 * (2 * Real.pi * v) by ring,
    Real.log_mul (Real.exp_pos 1).ne' hpos.ne', Real.log_exp]
  have : (∫ x, (x - m) ^ 2 ∂ν) / (2 * v) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

theorem variance_pos_of_absolutelyContinuous {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν ≪ volume) (hX : MemLp id 2 ν) : 0 < Var[id; ν] := by
  refine (variance_nonneg _ _).lt_of_ne fun h => ?_
  have hae := ae_eq_integral_of_variance_eq_zero hX h.symm
  have h1 : ν {ν[id]} = 1 := by
    rw [← measure_univ (μ := ν)]
    refine measure_congr ?_
    filter_upwards [hae] with x hx
    simpa using hx
  have h0 : ν {ν[id]} = 0 := hν (Real.volume_singleton)
  rw [h0] at h1
  exact zero_ne_one h1

theorem measureDiffEntropy_le_of_variance {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν ≪ volume) (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal))
    (hX : MemLp id 2 ν) :
    measureDiffEntropy ν ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * Var[id; ν]) := by
  have hm : Integrable (fun x => (x - ν[id]) ^ 2) ν := (hX.sub (memLp_const _)).integrable_sq
  refine measureDiffEntropy_le_of_integral_sq_le hν hf ν[id]
    (variance_pos_of_absolutelyContinuous hν hX) hm ?_
  rw [variance_eq_integral hX.aemeasurable]
  rfl

theorem diffEntropy_le_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : AEMeasurable X μ) (hν : μ.map X ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog ((μ.map X).rnDeriv volume x).toReal))
    (m : ℝ) {v : ℝ} (hv : 0 < v) (hm : Integrable (fun ω => (X ω - m) ^ 2) μ)
    (hle : ∫ ω, (X ω - m) ^ 2 ∂μ ≤ v) :
    diffEntropy X μ ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * v) := by
  have hg : AEStronglyMeasurable (fun x : ℝ => (x - m) ^ 2) (μ.map X) := by fun_prop
  refine measureDiffEntropy_le_of_integral_sq_le hν hf m hv
    ((integrable_map_measure hg hX).2 hm) ?_
  rwa [integral_map hX hg]

end Meat
