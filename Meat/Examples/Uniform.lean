import Mathlib.Probability.Distributions.Uniform
import Meat.Channel.Converse
import Meat.Examples.Binary
import Meat.Shannon.Bits

open MeasureTheory
open scoped ENNReal

namespace Meat.Examples

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem measureEntropy_uniformOfFinset (s : Finset S) :
    measureEntropy (Measure.uniformOfFinset s) = Real.log s.card := by
  classical
  have e : ∀ x, Real.negMulLog ((Measure.uniformOfFinset s).real {x}) =
      if x ∈ s then (s.card : ℝ)⁻¹ * Real.log s.card else 0 := fun x => by
    split_ifs with hx <;> simp [measureReal_def, hx, Real.negMulLog, Real.log_inv]
  rw [measureEntropy, Finset.sum_congr rfl fun x _ => e x, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  rcases eq_or_ne (s.card : ℝ) 0 with h | h
  · simp [h]
  · field_simp

noncomputable def uniformPMF (S : Type*) [Fintype S] [Nonempty S] : PMF S :=
  PMF.ofFintype (fun _ => (Fintype.card S : ℝ≥0∞)⁻¹) (sum_inv_card S)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem uniformPMF_toReal [Nonempty S] (s : S) :
    (uniformPMF S s).toReal = (Fintype.card S : ℝ)⁻¹ := by
  simp [uniformPMF]

theorem measureEntropy_uniformPMF [Nonempty S] :
    measureEntropy (uniformPMF S).toMeasure = Real.log (Fintype.card S) := by
  have h : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [measureEntropy_toMeasure]
  simp only [uniformPMF_toReal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog,
    Real.log_inv]
  field_simp

theorem measureEntropy_die :
    measureEntropy (Measure.uniformOfFinset (Finset.univ : Finset (Fin 6))) = Real.log 6 := by
  simp [measureEntropy_uniformOfFinset]

theorem entropyBits_fair_coin {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → Bool} (hX : Measurable X)
    (h : μ.real {ω | X ω = true} = 1 / 2) : H₂[X ; μ] = 1 := by
  rw [entropyBits_def, entropy_bool μ hX, h, binEntropy_half, div_self log_two_ne_zero]

end Meat.Examples
