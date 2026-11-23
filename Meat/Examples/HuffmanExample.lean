import Meat.Shannon.Bits
import Meat.Source.Huffman

open MeasureTheory

namespace Meat.Examples

noncomputable def dyadicSource : PMF (Fin 4) :=
  PMF.ofFintype (fun s => ENNReal.ofReal (![1 / 2, 1 / 4, 1 / 8, 1 / 8] s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun s _ => by fin_cases s <;> norm_num, Fin.sum_univ_four]
    norm_num)

theorem dyadicSource_toReal (s : Fin 4) :
    (dyadicSource s).toReal = ![1 / 2, 1 / 4, 1 / 8, 1 / 8] s := by
  rw [dyadicSource, PMF.ofFintype_apply, ENNReal.toReal_ofReal (by fin_cases s <;> norm_num)]

def dyadicLengths : Fin 4 → ℕ := ![1, 2, 3, 3]

def dyadicCode : Fin 4 → List (Fin 2) := ![[0], [1, 0], [1, 1, 0], [1, 1, 1]]

theorem isPrefixCode_dyadicCode : IsPrefixCode dyadicCode := by
  unfold IsPrefixCode
  decide

theorem length_dyadicCode (s : Fin 4) : (dyadicCode s).length = dyadicLengths s := by
  fin_cases s <;> rfl

theorem kraft_dyadicLengths : ∑ s, (1 / 2 : ℝ) ^ dyadicLengths s = 1 := by
  simp [Fin.sum_univ_four, dyadicLengths]
  norm_num

theorem expectedLength_dyadicCode : expectedLength dyadicSource dyadicCode = 7 / 4 := by
  simp [expectedLength, Fin.sum_univ_four, dyadicSource_toReal, dyadicCode]
  norm_num

theorem measureEntropy_dyadicSource :
    measureEntropy dyadicSource.toMeasure = 7 / 4 * Real.log 2 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [measureEntropy_toMeasure]
  simp [Fin.sum_univ_four, dyadicSource_toReal, Real.negMulLog, Real.log_inv, h4, h8]
  ring

theorem entropyBits_dyadicSource : measureEntropy dyadicSource.toMeasure / Real.log 2 = 7 / 4 := by
  rw [measureEntropy_dyadicSource, mul_div_assoc, div_self log_two_ne_zero, mul_one]

theorem expectedLength_le_dyadicCode {c : Fin 4 → List (Fin 2)} (hc : IsPrefixCode c) :
    expectedLength dyadicSource dyadicCode ≤ expectedLength dyadicSource c := by
  have h := hc.measureEntropy_le dyadicSource
  rw [measureEntropy_dyadicSource, Nat.cast_ofNat] at h
  rw [expectedLength_dyadicCode]
  exact le_of_mul_le_mul_right h (Real.log_pos one_lt_two)

theorem expectedLength_huffmanCode_dyadicSource :
    expectedLength dyadicSource (huffmanCode dyadicSource) = 7 / 4 := by
  refine le_antisymm ?_ ?_
  · rw [← expectedLength_dyadicCode]
    exact isPrefixCode_dyadicCode.expectedLength_huffmanCode_le dyadicSource
  · exact expectedLength_dyadicCode ▸
      expectedLength_le_dyadicCode (isPrefixCode_huffmanCode dyadicSource)

theorem huffmanCodeLength_dyadicSource : huffmanCodeLength dyadicSource = dyadicLengths := by
  have hL : ∑ s, (dyadicSource s).toReal * huffmanCodeLength dyadicSource s = 7 / 4 := by
    simpa [expectedLength, length_huffmanCode] using expectedLength_huffmanCode_dyadicSource
  have hH : ∑ s, (dyadicSource s).toReal * -Real.log (dyadicSource s).toReal =
      7 / 4 * Real.log 2 :=
    (sum_toReal_mul_neg_log dyadicSource).trans measureEntropy_dyadicSource
  have hq := (sum_mul_log_eq_sum_mul_log_iff Finset.univ
    (p := fun s => (dyadicSource s).toReal)
    (q := fun s => (1 / 2 : ℝ) ^ huffmanCodeLength dyadicSource s)
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => by positivity)
    (fun _ _ h => absurd h (by positivity))
    (by rw [sum_huffmanCodeLength, sum_toReal_pmf_eq_one])).1 (by
      simp only [Real.log_pow, one_div, Real.log_inv]
      simp only [mul_neg, Finset.sum_neg_distrib] at hH
      have : ∑ s, (dyadicSource s).toReal * (huffmanCodeLength dyadicSource s * -Real.log 2) =
          -(7 / 4 * Real.log 2) := by
        rw [← hL, Finset.sum_mul, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      linarith)
  funext s
  refine pow_right_injective₀ (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) ?_
  simp only
  rw [hq s (Finset.mem_univ s), dyadicSource_toReal]
  fin_cases s <;> norm_num [dyadicLengths]

end Meat.Examples
