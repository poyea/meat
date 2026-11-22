import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.GetD
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.UnitInterval
import Meat.Channel.Converse

open MeasureTheory Filter
open scoped ENNReal unitInterval

namespace Meat

noncomputable def keepPMF (n : ℕ) (d : I) : PMF (Fin n → Bool) :=
  PMF.ofFintype (fun k => ∏ i, if k i then ENNReal.ofReal (1 - d) else ENNReal.ofReal d) (by
    rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) =>
      if b = true then ENNReal.ofReal (1 - (d : ℝ)) else ENNReal.ofReal d)]
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    rw [← ENNReal.ofReal_add (by linarith [d.2.2]) d.2.1]
    simp)

def deletionOutput {n : ℕ} (x : Fin n → Bool) (keep : Fin n → Bool) : List Bool :=
  ((List.finRange n).filter keep).map x

def encodeOutput (n : ℕ) (l : List Bool) : Fin (n + 1) × (Fin n → Bool) :=
  (⟨min l.length n, Nat.lt_succ_of_le (min_le_right _ _)⟩, fun j => l.getD j false)

noncomputable def deletionChannel (n : ℕ) (d : I) :
    DMC (Fin n → Bool) (Fin (n + 1) × (Fin n → Bool)) :=
  fun x => (keepPMF n d).map fun keep => encodeOutput n (deletionOutput x keep)

noncomputable def deletionCapacity (d : I) : ℝ :=
  limsup (fun n : ℕ => (deletionChannel n d).capacity / n) atTop

def DeletionCapacitySingleLetter : Prop :=
  ∃ (k m : ℕ) (V : Fin k → Fin m → Polynomial ℚ), ∀ d : I, ∃ W : DMC (Fin k) (Fin m),
    (∀ a b, (W a b).toReal = (V a b).eval₂ (algebraMap ℚ ℝ) d) ∧
      deletionCapacity d = W.capacity

theorem capacity_deletionChannel_le (n : ℕ) (d : I) :
    (deletionChannel n d).capacity ≤ n * Real.log 2 := by
  refine Real.iSup_le (fun p => ?_) (by positivity)
  have h := (deletionChannel n d).inputMutualInfo_le_log_card p
  simpa [Fintype.card_fun, Real.log_pow] using h

private lemma deletion_ratio_mem (n : ℕ) (d : I) :
    0 ≤ (deletionChannel n d).capacity / n ∧
      (deletionChannel n d).capacity / n ≤ Real.log 2 := by
  refine ⟨div_nonneg (DMC.capacity_nonneg _) (by positivity), ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.log_nonneg]
  · rw [div_le_iff₀ (by exact_mod_cast hn), mul_comm]
    exact capacity_deletionChannel_le n d

theorem deletionCapacity_nonneg (d : I) : 0 ≤ deletionCapacity d :=
  le_limsup_of_frequently_le (Frequently.of_forall fun n => (deletion_ratio_mem n d).1)
    (isBoundedUnder_of ⟨Real.log 2, fun n => (deletion_ratio_mem n d).2⟩)

theorem deletionCapacity_le_log_two (d : I) : deletionCapacity d ≤ Real.log 2 :=
  limsup_le_of_le (isCoboundedUnder_le_of_le atTop fun n => (deletion_ratio_mem n d).1)
    (Eventually.of_forall fun n => (deletion_ratio_mem n d).2)

private lemma measureEntropy_le_of_weight {B : Type*} [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (ν : Measure B) [IsProbabilityMeasure ν] (q : B → ℝ)
    (hq : ∀ b, 0 ≤ q b) (hsum : ∑ b, q b ≤ 1) (hsupp : ∀ b, q b = 0 → ν.real {b} = 0) :
    measureEntropy ν ≤ -∑ b, ν.real {b} * Real.log (q b) := by
  have h := sum_mul_log_le_sum_mul_log Finset.univ (p := fun b => ν.real {b}) (q := q)
    (fun _ _ => measureReal_nonneg) (fun b _ => hq b) (fun b _ => hsupp b)
    (by rw [sum_measureReal_singleton_eq_one]; exact hsum)
  rw [measureEntropy_eq_neg_sum_mul_log]
  linarith

private def ValidOutput {n : ℕ} (b : Fin (n + 1) × (Fin n → Bool)) : Prop :=
  ∀ j : Fin n, (b.1 : ℕ) ≤ j → b.2 j = false

private instance {n : ℕ} : DecidablePred (ValidOutput (n := n)) := fun _ => by
  unfold ValidOutput
  infer_instance

private lemma length_deletionOutput {n : ℕ} (x keep : Fin n → Bool) :
    (deletionOutput x keep).length = ∑ i, if keep i then 1 else 0 := by
  rw [deletionOutput, List.length_map, ← Finset.card_filter]
  rw [Finset.filter, Finset.card_mk, Finset.univ, Fin.fintype]
  simp [List.finRange]

private lemma validOutput_encode {n : ℕ} (l : List Bool) (hl : l.length ≤ n) :
    ValidOutput (encodeOutput n l) := by
  intro j hj
  simp only [encodeOutput, min_eq_left hl] at hj ⊢
  exact List.getD_eq_default _ _ hj

private lemma card_valid_le {n : ℕ} (ℓ : Fin (n + 1)) :
    (Finset.univ.filter fun z : Fin n → Bool => ValidOutput (ℓ, z)).card ≤ 2 ^ (ℓ : ℕ) := by
  have hℓ : (ℓ : ℕ) ≤ n := Nat.lt_succ_iff.1 ℓ.2
  calc _ ≤ (Finset.univ : Finset (Fin ℓ → Bool)).card := by
        refine Finset.card_le_card_of_injOn (fun z i => z ⟨i, i.2.trans_le hℓ⟩)
          (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
        intro z hz z' hz' h
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz hz'
        funext j
        by_cases hj : (j : ℕ) < ℓ
        · exact congrFun h ⟨j, hj⟩
        · exact (hz j (not_lt.1 hj)).trans (hz' j (not_lt.1 hj)).symm
    _ = 2 ^ (ℓ : ℕ) := by simp

private lemma keepPMF_toReal {n : ℕ} (d : I) (k : Fin n → Bool) :
    (keepPMF n d k).toReal = ∏ i, if k i then 1 - (d : ℝ) else d := by
  rw [keepPMF, PMF.ofFintype_apply, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact ENNReal.toReal_ofReal (by linarith [d.2.2])
  · exact ENNReal.toReal_ofReal d.2.1

private lemma deletionChannel_toReal {n : ℕ} (d : I) (x : Fin n → Bool)
    (b : Fin (n + 1) × (Fin n → Bool)) :
    (deletionChannel n d x b).toReal = ∑ k, if encodeOutput n (deletionOutput x k) = b then
      ∏ i, (if k i then 1 - (d : ℝ) else d) else 0 := by
  rw [deletionChannel, PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun k _ => by
    split_ifs
    exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top]]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : encodeOutput n (deletionOutput x k) = b
  · simp [h, keepPMF_toReal]
  · simp [h, Ne.symm h]

private lemma sum_keep_mul_indicator {n : ℕ} (d : I) (i : Fin n) :
    ∑ k : Fin n → Bool, (∏ j, if k j then 1 - (d : ℝ) else d) * (if k i then 1 else 0)
      = 1 - d := by
  let g : Fin n → Bool → ℝ := fun j b =>
    (if b then 1 - (d : ℝ) else d) * (if j = i then (if b then 1 else 0) else 1)
  have e : ∀ k : Fin n → Bool,
      (∏ j, if k j then 1 - (d : ℝ) else d) * (if k i then 1 else 0) = ∏ j, g j (k j) := by
    intro k
    simp only [g, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  simp only [e]
  rw [← Fintype.prod_sum]
  have h : ∀ j, ∑ b, g j b = if j = i then 1 - (d : ℝ) else 1 := by
    intro j
    by_cases hj : j = i <;> simp [g, hj]
  simp only [h, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

private lemma sum_deletionChannel_mul_length {n : ℕ} (d : I) (x : Fin n → Bool) :
    ∑ b : Fin (n + 1) × (Fin n → Bool), (deletionChannel n d x b).toReal * (b.1 : ℕ)
      = n * (1 - d) := by
  simp only [deletionChannel_toReal, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hl : ∀ k, ((encodeOutput n (deletionOutput x k)).1 : ℕ)
      = ∑ i, if k i then 1 else 0 := by
    intro k
    have hle : (deletionOutput x k).length ≤ n := by
      rw [deletionOutput, List.length_map]
      exact (List.length_filter_le _ _).trans (List.length_finRange).le
    rw [length_deletionOutput] at hle
    simp only [encodeOutput, length_deletionOutput, min_eq_left hle]
  simp only [hl, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [sum_keep_mul_indicator, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

private lemma outputLaw_real {n : ℕ} (d : I) (p : PMF (Fin n → Bool))
    (b : Fin (n + 1) × (Fin n → Bool)) :
    (((deletionChannel n d).jointMeasure p).map Prod.snd).real {b}
      = ∑ a, (p a).toReal * (deletionChannel n d a b).toReal := by
  classical
  rw [measureReal_map_singleton, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single b (fun b' _ hb' => by simp [hb']) (by simp)]
  split_ifs with h
  swap
  · exact absurd rfl h
  rw [measureReal_def, DMC.jointMeasure_eq_toMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), DMC.jointPMF_apply,
    ENNReal.toReal_mul]

private lemma sum_pmf_toReal {α : Type*} [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum fun a _ => PMF.apply_ne_top p a, h, ENNReal.toReal_one]

theorem inputMutualInfo_deletionChannel_le (n : ℕ) (d : I) (p : PMF (Fin n → Bool)) :
    (deletionChannel n d).inputMutualInfo p ≤ Real.log (n + 1) + n * (1 - d) * Real.log 2 := by
  classical
  set W := deletionChannel n d
  set J := W.jointMeasure p
  set ν := J.map Prod.snd
  have hI : W.inputMutualInfo p ≤ measureEntropy ν := by
    have h := entropy_le_entropy_pair J (X := (Prod.fst : _ → Fin n → Bool))
      (Y := (Prod.snd : _ → Fin (n + 1) × (Fin n → Bool))) measurable_fst measurable_snd
    have h' : W.inputMutualInfo p = H[Prod.fst ; J] + H[Prod.snd ; J]
        - H[fun ω => (ω.1, ω.2) ; J] := rfl
    have h'' : H[Prod.snd ; J] = measureEntropy ν := rfl
    linarith
  let q : Fin (n + 1) × (Fin n → Bool) → ℝ := fun b =>
    if ValidOutput b then ((2 : ℝ) ^ (b.1 : ℕ))⁻¹ / (n + 1) else 0
  have hq : ∀ b, 0 ≤ q b := fun b => by
    simp only [q]
    split_ifs <;> positivity
  have hW0 : ∀ a b, ¬ValidOutput b → (W a b).toReal = 0 := by
    intro a b hb
    rw [deletionChannel_toReal]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hle : (deletionOutput a k).length ≤ n := by
      rw [deletionOutput, List.length_map]
      exact (List.length_filter_le _ _).trans (List.length_finRange).le
    have hv := validOutput_encode (deletionOutput a k) hle
    split_ifs with h
    · exact absurd (h ▸ hv) hb
    · rfl
  have hν : ∀ b, ν.real {b} = ∑ a, (p a).toReal * (W a b).toReal := fun b =>
    outputLaw_real d p b
  have hν0 : ∀ b, ¬ValidOutput b → ν.real {b} = 0 := by
    intro b hb
    rw [hν]
    exact Finset.sum_eq_zero fun a _ => by rw [hW0 a b hb, mul_zero]
  have hsum : ∑ b, q b ≤ 1 := by
    rw [Fintype.sum_prod_type]
    calc ∑ ℓ : Fin (n + 1), ∑ z : Fin n → Bool, q (ℓ, z)
        ≤ ∑ ℓ : Fin (n + 1), (1 : ℝ) / (n + 1) := by
          refine Finset.sum_le_sum fun ℓ _ => ?_
          simp only [q]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hc : ((Finset.univ.filter fun z : Fin n → Bool => ValidOutput (ℓ, z)).card : ℝ)
              ≤ 2 ^ (ℓ : ℕ) := by exact_mod_cast card_valid_le ℓ
          have h2 : (0 : ℝ) < 2 ^ (ℓ : ℕ) := by positivity
          calc _ ≤ (2 : ℝ) ^ (ℓ : ℕ) * (((2 : ℝ) ^ (ℓ : ℕ))⁻¹ / (n + 1)) := by gcongr
            _ = 1 / (n + 1) := by field_simp
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          field_simp
  have hsupp : ∀ b, q b = 0 → ν.real {b} = 0 := by
    intro b hb
    by_cases hv : ValidOutput b
    · exfalso
      simp only [q, hv, ite_true] at hb
      have : (0 : ℝ) < ((2 : ℝ) ^ (b.1 : ℕ))⁻¹ / (n + 1) := by positivity
      exact this.ne' hb
    · exact hν0 b hv
  have hH := measureEntropy_le_of_weight ν q hq hsum hsupp
  have hterm : ∀ b, ν.real {b} * Real.log (q b)
      = -(ν.real {b} * ((b.1 : ℕ) * Real.log 2) + ν.real {b} * Real.log (n + 1)) := by
    intro b
    by_cases hv : ValidOutput b
    · simp only [q, hv, ite_true]
      rw [Real.log_div (by positivity) (by positivity), Real.log_inv, Real.log_pow]
      ring
    · rw [hν0 b hv]
      ring
  have hE : ∑ b, ν.real {b} * (b.1 : ℕ) = n * (1 - d) := by
    simp only [hν, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hL : ∀ x, ∑ b, (W x b).toReal * ((b.1 : ℕ) : ℝ) = n * (1 - d) := fun x =>
      sum_deletionChannel_mul_length d x
    simp only [mul_assoc, ← Finset.mul_sum, hL]
    rw [← Finset.sum_mul, sum_pmf_toReal, one_mul]
  have hS : ∑ b, ν.real {b} = 1 := sum_measureReal_singleton_eq_one ν
  simp only [hterm, Finset.sum_neg_distrib, neg_neg, Finset.sum_add_distrib] at hH
  simp only [← mul_assoc] at hH
  rw [← Finset.sum_mul, hE, ← Finset.sum_mul, hS] at hH
  linarith

theorem capacity_deletionChannel_le_erasure (n : ℕ) (d : I) :
    (deletionChannel n d).capacity ≤ Real.log (n + 1) + n * (1 - d) * Real.log 2 := by
  have hd : (0 : ℝ) ≤ 1 - d := by linarith [d.2.2]
  exact Real.iSup_le (inputMutualInfo_deletionChannel_le n d)
    (add_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hd) (Real.log_nonneg one_le_two)))

theorem deletionCapacity_le_erasure (d : I) : deletionCapacity d ≤ (1 - d) * Real.log 2 := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
    refine h.congr fun n => ?_
    simp
  have hv : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n + (1 - d) * Real.log 2) atTop
      (nhds ((1 - d) * Real.log 2)) := by
    simpa using hlog.add_const ((1 - (d : ℝ)) * Real.log 2)
  have hle : (fun n : ℕ => (deletionChannel n d).capacity / n)
      ≤ᶠ[atTop] fun n => Real.log ((n : ℝ) + 1) / n + (1 - d) * Real.log 2 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
    linarith [capacity_deletionChannel_le_erasure n d]
  calc deletionCapacity d
      ≤ limsup (fun n : ℕ => Real.log ((n : ℝ) + 1) / n + (1 - d) * Real.log 2) atTop :=
        limsup_le_limsup hle
          (isCoboundedUnder_le_of_le atTop fun n => (deletion_ratio_mem n d).1)
          hv.isBoundedUnder_le
    _ = (1 - d) * Real.log 2 := hv.limsup_eq

end Meat
