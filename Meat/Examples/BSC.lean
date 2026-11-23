import Meat.Examples.Noiseless

open MeasureTheory

namespace Meat.Examples

variable {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)

noncomputable def bsc (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : DMC Bool Bool := fun a =>
  PMF.ofFintype (fun b => ENNReal.ofReal (if b = a then 1 - p else p)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun b _ => by split_ifs <;> linarith, Fintype.sum_bool]
    cases a <;> simp)

theorem bsc_toReal (a b : Bool) : (bsc p h0 h1 a b).toReal = if b = a then 1 - p else p := by
  rw [bsc, PMF.ofFintype_apply, ENNReal.toReal_ofReal (by split_ifs <;> linarith)]

theorem condEntropy_bsc (q : PMF Bool) :
    H[Prod.snd | Prod.fst ; (bsc p h0 h1).jointMeasure q] = Real.binEntropy p :=
  condEntropy_of_rows _ _ fun a => by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    cases a <;> simp [bsc_toReal, add_comm]

theorem inputMutualInfo_bsc_le (q : PMF Bool) :
    (bsc p h0 h1).inputMutualInfo q ≤ Real.log 2 - Real.binEntropy p := by
  have h := entropy_le_log_card ((bsc p h0 h1).jointMeasure q)
    (X := (Prod.snd : Bool × Bool → Bool))
  rw [Fintype.card_bool, Nat.cast_ofNat] at h
  rw [inputMutualInfo_eq, condEntropy_bsc]
  linarith

theorem inputMutualInfo_bsc_uniform :
    (bsc p h0 h1).inputMutualInfo (uniformPMF Bool) = Real.log 2 - Real.binEntropy p := by
  have hY : H[Prod.snd ; (bsc p h0 h1).jointMeasure (uniformPMF Bool)] = Real.log 2 := by
    rw [entropy_eq_log_card _ fun b => ?_, Fintype.card_bool, Nat.cast_ofNat]
    rw [outputLaw_real]
    cases b <;> simp [bsc_toReal, uniformPMF_toReal] <;> ring
  rw [inputMutualInfo_eq, hY, condEntropy_bsc]

theorem capacity_bsc : (bsc p h0 h1).capacity = Real.log 2 - Real.binEntropy p :=
  capacity_eq_of_le _ (inputMutualInfo_bsc_le h0 h1) _ (inputMutualInfo_bsc_uniform h0 h1)

theorem capacity_bsc_zero : (bsc 0 le_rfl zero_le_one).capacity = Real.log 2 := by
  simp [capacity_bsc]

theorem capacity_bsc_half : (bsc (1 / 2) (by norm_num) (by norm_num)).capacity = 0 := by
  rw [capacity_bsc, binEntropy_half, sub_self]

end Meat.Examples
