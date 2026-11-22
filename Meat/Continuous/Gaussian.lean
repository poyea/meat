import Mathlib.Probability.Distributions.Gaussian.Real
import Meat.Continuous.DifferentialEntropy

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Meat

theorem neg_log_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    -Real.log (gaussianPDFReal m v x)
      = (1 / 2) * Real.log (2 * Real.pi * v) + (x - m) ^ 2 / (2 * v) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have hpos : (0 : ℝ) < 2 * Real.pi * v := by positivity
  rw [gaussianPDFReal, Real.log_mul (inv_ne_zero (Real.sqrt_pos.2 hpos).ne') (Real.exp_pos _).ne',
    Real.log_inv, Real.log_sqrt hpos.le, Real.log_exp]
  ring

theorem toReal_rnDeriv_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∀ᵐ x, ((gaussianReal m v).rnDeriv volume x).toReal = gaussianPDFReal m v x := by
  filter_upwards [rnDeriv_gaussianReal m v] with x hx
  rw [hx, toReal_gaussianPDF]

private lemma log_rnDeriv_gaussianReal_ae {ν : Measure ℝ} (hν : ν ≪ volume) (m : ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) :
    (fun x => Real.log ((gaussianReal m v).rnDeriv volume x).toReal) =ᵐ[ν]
      fun x => -((1 / 2) * Real.log (2 * Real.pi * v) + (x - m) ^ 2 / (2 * v)) := by
  filter_upwards [hν.ae_le (toReal_rnDeriv_gaussianReal m v)] with x hx
  rw [hx, ← neg_log_gaussianPDFReal m hv x, neg_neg]

theorem integrable_log_rnDeriv_gaussianReal {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ν ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hm : Integrable (fun x => (x - m) ^ 2) ν) :
    Integrable (fun x => Real.log ((gaussianReal m v).rnDeriv volume x).toReal) ν :=
  ((integrable_const _).add (hm.div_const _)).neg.congr (log_rnDeriv_gaussianReal_ae hν m hv).symm

theorem neg_integral_log_rnDeriv_gaussianReal {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hm : Integrable (fun x => (x - m) ^ 2) ν) :
    -∫ x, Real.log ((gaussianReal m v).rnDeriv volume x).toReal ∂ν
      = (1 / 2) * Real.log (2 * Real.pi * v) + (∫ x, (x - m) ^ 2 ∂ν) / (2 * v) := by
  rw [integral_congr_ae (log_rnDeriv_gaussianReal_ae hν m hv), integral_neg, neg_neg,
    integral_add (integrable_const _) (hm.div_const _), integral_const, integral_div]
  simp

theorem measureDiffEntropy_gaussianReal (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    measureDiffEntropy (gaussianReal m v)
      = (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * v) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have hpos : (0 : ℝ) < 2 * Real.pi * v := by positivity
  have hsq : ∫ x, (x - m) ^ 2 ∂gaussianReal m v = v := by
    have := variance_fun_id_gaussianReal (μ := m) (v := v)
    rwa [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at this
  have hint : Integrable (fun x => (x - m) ^ 2) (gaussianReal m v) :=
    ((memLp_id_gaussianReal' 2 (by simp)).sub (memLp_const m)).integrable_sq
  have hac := gaussianReal_absolutelyContinuous m hv
  rw [measureDiffEntropy_eq_neg_integral_log hac,
    neg_integral_log_rnDeriv_gaussianReal hac m hv hint, hsq,
    show 2 * Real.pi * Real.exp 1 * v = Real.exp 1 * (2 * Real.pi * v) by ring,
    Real.log_mul (Real.exp_pos 1).ne' hpos.ne', Real.log_exp]
  field_simp
  ring

noncomputable def awgnCapacity (P N : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 + P / N)

end Meat
