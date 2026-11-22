import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

open MeasureTheory

namespace Meat

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasureSpace E]

noncomputable def measureDiffEntropy (ν : Measure E) : ℝ :=
  ∫ x, Real.negMulLog (ν.rnDeriv volume x).toReal

noncomputable def diffEntropy (X : Ω → E) (μ : Measure Ω) : ℝ :=
  measureDiffEntropy (μ.map X)

theorem diffEntropy_def (X : Ω → E) (μ : Measure Ω) :
    diffEntropy X μ = ∫ x, Real.negMulLog ((μ.map X).rnDeriv volume x).toReal := rfl

variable [SigmaFinite (volume : Measure E)]

theorem measureDiffEntropy_eq_neg_integral_log {ν : Measure E} [SigmaFinite ν]
    (hν : ν ≪ volume) :
    measureDiffEntropy ν = -∫ x, Real.log (ν.rnDeriv volume x).toReal ∂ν := by
  rw [measureDiffEntropy, ← integral_rnDeriv_smul hν, ← integral_neg]
  simp [Real.negMulLog, smul_eq_mul]

theorem integrable_negMulLog_rnDeriv_iff {ν : Measure E} [SigmaFinite ν] (hν : ν ≪ volume) :
    Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal)
      ↔ Integrable (fun x => Real.log (ν.rnDeriv volume x).toReal) ν := by
  rw [← integrable_rnDeriv_smul_iff hν, ← integrable_neg_iff]
  simp [Real.negMulLog, smul_eq_mul]

end Meat
