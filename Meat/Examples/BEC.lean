import Meat.Examples.Noiseless

open MeasureTheory

namespace Meat.Examples

variable [MeasurableSpace (Option Bool)] [MeasurableSingletonClass (Option Bool)]
  {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1)

noncomputable def bec (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) : DMC Bool (Option Bool) := fun a =>
  PMF.ofFintype (fun y => ENNReal.ofReal (if y = none then e else if y = some a then 1 - e else 0))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => by split_ifs <;> linarith,
        Fintype.sum_option, Fintype.sum_bool]
      cases a <;> simp)

omit [MeasurableSpace (Option Bool)] [MeasurableSingletonClass (Option Bool)] in
theorem bec_toReal (a : Bool) (y : Option Bool) :
    (bec e h0 h1 a y).toReal = if y = none then e else if y = some a then 1 - e else 0 := by
  rw [bec, PMF.ofFintype_apply, ENNReal.toReal_ofReal (by split_ifs <;> linarith)]

theorem condEntropy_bec (q : PMF Bool) :
    H[Prod.snd | Prod.fst ; (bec e h0 h1).jointMeasure q] = Real.binEntropy e :=
  condEntropy_of_rows _ _ fun a => by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    cases a <;> simp [bec_toReal, Fintype.sum_option]

theorem entropy_output_bec (q : PMF Bool) :
    H[Prod.snd ; (bec e h0 h1).jointMeasure q] =
      Real.binEntropy e + (1 - e) * measureEntropy q.toMeasure := by
  have hn : ∑ a, (q a).toReal * (bec e h0 h1 a none).toReal = e := by
    simp only [bec_toReal, ite_true, ← Finset.sum_mul, sum_toReal_pmf_eq_one, one_mul]
  have hs : ∀ b, ∑ a, (q a).toReal * (bec e h0 h1 a (some b)).toReal = (q b).toReal * (1 - e) :=
    fun b => by simp [bec_toReal]
  rw [entropy_def, Fintype.sum_option, measureEntropy_toMeasure,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [outputLaw_real, hn, hs, Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, sum_toReal_pmf_eq_one]
  ring

theorem inputMutualInfo_bec (q : PMF Bool) :
    (bec e h0 h1).inputMutualInfo q = (1 - e) * measureEntropy q.toMeasure := by
  rw [inputMutualInfo_eq, entropy_output_bec, condEntropy_bec]
  ring

omit [MeasurableSpace (Option Bool)] [MeasurableSingletonClass (Option Bool)] in
theorem measureEntropy_pmf_bool_le (q : PMF Bool) : measureEntropy q.toMeasure ≤ Real.log 2 := by
  have h := entropy_le_log_card q.toMeasure (X := (id : Bool → Bool))
  rwa [entropy, Measure.map_id, Fintype.card_bool, Nat.cast_ofNat] at h

theorem capacity_bec : (bec e h0 h1).capacity = (1 - e) * Real.log 2 := by
  refine capacity_eq_of_le _ (fun q => ?_) (uniformPMF Bool) ?_
  · rw [inputMutualInfo_bec]
    exact mul_le_mul_of_nonneg_left (measureEntropy_pmf_bool_le q) (by linarith)
  · rw [inputMutualInfo_bec, measureEntropy_uniformPMF, Fintype.card_bool, Nat.cast_ofNat]

end Meat.Examples
