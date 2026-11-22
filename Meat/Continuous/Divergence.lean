import Mathlib.InformationTheory.KullbackLeibler.Basic
import Meat.Continuous.DifferentialEntropy

open MeasureTheory

namespace Meat

variable {E : Type*} [MeasureSpace E] [SigmaFinite (volume : Measure E)]

theorem toReal_klDiv_eq_neg_measureDiffEntropy_sub {ν ρ : Measure E}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] (hν : ν ≪ volume) (hνρ : ν ≪ ρ)
    (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal))
    (hg : Integrable (fun x => Real.log (ρ.rnDeriv volume x).toReal) ν) :
    (InformationTheory.klDiv ν ρ).toReal
      = -measureDiffEntropy ν - ∫ x, Real.log (ρ.rnDeriv volume x).toReal ∂ν := by
  have hllr : llr ν ρ =ᵐ[ν] fun x =>
      Real.log (ν.rnDeriv volume x).toReal - Real.log (ρ.rnDeriv volume x).toReal := by
    filter_upwards [hν.ae_le (Measure.rnDeriv_mul_rnDeriv (κ := volume) hνρ),
      Measure.rnDeriv_pos hνρ, hνρ.ae_le (Measure.rnDeriv_ne_top ν ρ),
      hν.ae_le (Measure.rnDeriv_ne_top ρ volume), Measure.rnDeriv_pos hν] with x h1 h2 h3 h4 h5
    have h6 : ρ.rnDeriv volume x ≠ 0 := by
      rintro h
      simp only [Pi.mul_apply, h, mul_zero] at h1
      exact h5.ne h1
    rw [llr, ← h1, Pi.mul_apply, ENNReal.toReal_mul,
      Real.log_mul (ENNReal.toReal_pos h2.ne' h3).ne' (ENNReal.toReal_pos h6 h4).ne']
    ring
  rw [InformationTheory.toReal_klDiv_of_measure_eq hνρ (by simp), integral_congr_ae hllr,
    integral_sub ((integrable_negMulLog_rnDeriv_iff hν).1 hf) hg,
    measureDiffEntropy_eq_neg_integral_log hν]
  ring

theorem measureDiffEntropy_le_neg_integral_log_rnDeriv {ν ρ : Measure E}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] (hν : ν ≪ volume) (hνρ : ν ≪ ρ)
    (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal))
    (hg : Integrable (fun x => Real.log (ρ.rnDeriv volume x).toReal) ν) :
    measureDiffEntropy ν ≤ -∫ x, Real.log (ρ.rnDeriv volume x).toReal ∂ν := by
  have := toReal_klDiv_eq_neg_measureDiffEntropy_sub hν hνρ hf hg
  linarith [(InformationTheory.klDiv ν ρ).toReal_nonneg]

end Meat
