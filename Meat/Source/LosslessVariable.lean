import Meat.Shannon.Iid
import Meat.Source.Prefix

open MeasureTheory Filter Topology Finset

namespace Meat

variable {S : Type*} [Fintype S]

theorem sum_prod_pmf_eq_one (p : PMF S) (n : ℕ) : ∑ x : Fin n → S, ∏ i, p (x i) = 1 := by
  rw [← Fintype.prod_sum, sum_pmf_eq_one, prod_const_one]

noncomputable def iidPMF (p : PMF S) (n : ℕ) : PMF (Fin n → S) :=
  PMF.ofFintype (fun x => ∏ i, p (x i)) (sum_prod_pmf_eq_one p n)

theorem iidPMF_toReal (p : PMF S) {n : ℕ} (x : Fin n → S) :
    (iidPMF p n x).toReal = iidProb p x := by
  rw [iidPMF, PMF.ofFintype_apply, ENNReal.toReal_prod]
  rfl

theorem iidPMF_ne_zero {p : PMF S} (hp : ∀ s, p s ≠ 0) {n : ℕ} (x : Fin n → S) :
    iidPMF p n x ≠ 0 := by
  rw [iidPMF, PMF.ofFintype_apply]
  exact prod_ne_zero_iff.2 fun i _ => hp (x i)

variable [MeasurableSpace S] [MeasurableSingletonClass S]

theorem measureEntropy_iidPMF (p : PMF S) (n : ℕ) :
    measureEntropy (iidPMF p n).toMeasure = n * measureEntropy p.toMeasure := by
  rw [measureEntropy_toMeasure, ← sum_negMulLog_iidProb p n]
  simp_rw [iidPMF_toReal]

theorem exists_isPrefixCode_expectedLength_le {D : ℕ} (hD : 2 ≤ D) (p : PMF S) :
    ∃ c : S → List (Fin D), IsPrefixCode c ∧ (∀ s, c s ≠ []) ∧
      expectedLength p c ≤ measureEntropy p.toMeasure / Real.log D + 1 := by
  have : NeZero D := ⟨by omega⟩
  have hD0 : (0 : ℝ) < D := by positivity
  have hD1 : (1 : ℝ) < D := by exact_mod_cast hD
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hp1 : ∀ s, (p s).toReal ≤ 1 := fun s =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using p.coe_le_one s)
  set x : S → ℝ := fun s => -Real.log (p s).toReal / Real.log D with hx
  have hx0 : ∀ s, 0 ≤ x s := fun s =>
    div_nonneg (neg_nonneg.2 (Real.log_nonpos ENNReal.toReal_nonneg (hp1 s))) hlogD.le
  set m : S → ℕ := fun s => ⌊x s⌋₊ + 1 with hmdef
  have hlt : ∀ s, p s ≠ 0 → (1 / (D : ℝ)) ^ m s < (p s).toReal := fun s hs => by
    have hpos : 0 < (p s).toReal := ENNReal.toReal_pos hs (p.apply_ne_top s)
    have hm : x s < m s := by simpa [m] using Nat.lt_floor_add_one (x s)
    have h2 : (p s).toReal⁻¹ < (D : ℝ) ^ m s := by
      rw [← Real.exp_log (inv_pos.2 hpos), Real.log_inv, ← Real.exp_log (pow_pos hD0 _),
        Real.log_pow]
      refine Real.exp_lt_exp.2 ?_
      have he : -Real.log (p s).toReal = x s * Real.log D := by
        simp only [x]
        field_simp
      rw [he]
      exact mul_lt_mul_of_pos_right hm hlogD
    rw [one_div_pow, div_lt_iff₀ (pow_pos hD0 _)]
    calc (1 : ℝ) = (p s).toReal * (p s).toReal⁻¹ := (mul_inv_cancel₀ hpos.ne').symm
      _ < (p s).toReal * (D : ℝ) ^ m s := mul_lt_mul_of_pos_left h2 hpos
  set K := ∑ s, (if p s = 0 then 0 else (1 / (D : ℝ)) ^ m s) with hK
  have hK1 : K < 1 := by
    obtain ⟨s₀, hs₀⟩ := p.support_nonempty
    rw [← sum_toReal_pmf_eq_one p]
    refine sum_lt_sum (fun s _ => ?_) ⟨s₀, mem_univ _, ?_⟩
    · by_cases h : p s = 0
      · simp [h]
      · simpa [h] using (hlt s h).le
    · have h : p s₀ ≠ 0 := hs₀
      simpa [h] using hlt s₀ h
  have hq0 : (0 : ℝ) ≤ 1 / D := by positivity
  have hq1 : (1 / D : ℝ) < 1 := by rw [div_lt_one hD0]; exact hD1
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (Fintype.card S : ℝ)
  rw [mul_zero] at ht
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (sub_pos.2 hK1)))
  set L := max N 1
  have hL := hN L (le_max_left _ _)
  set ℓ : S → ℕ := fun s => if p s = 0 then L else m s with hℓ
  have hkraft : ∑ s, (1 / (D : ℝ)) ^ ℓ s ≤ 1 := by
    have h : ∀ s, (1 / (D : ℝ)) ^ ℓ s
        ≤ (if p s = 0 then 0 else (1 / (D : ℝ)) ^ m s) + (1 / (D : ℝ)) ^ L := fun s => by
      by_cases h : p s = 0
      · simp [ℓ, h]
      · simp only [ℓ, h, ite_false]
        exact le_add_of_nonneg_right (pow_nonneg hq0 _)
    refine (sum_le_sum fun s _ => h s).trans ?_
    rw [sum_add_distrib, ← hK, sum_const, card_univ, nsmul_eq_mul]
    linarith
  obtain ⟨c, hc, hlen⟩ := exists_isPrefixCode_of_kraft ℓ hkraft
  refine ⟨c, hc, fun s h => ?_, ?_⟩
  · have h1 := hlen s
    rw [h, List.length_nil] at h1
    by_cases hs : p s = 0
    · simp only [ℓ, hs, ite_true] at h1
      exact absurd h1.symm (by omega)
    · simp only [ℓ, hs, ite_false, m] at h1
      omega
  · have hle : expectedLength p c ≤ ∑ s, (p s).toReal * (x s + 1) := by
      simp only [expectedLength, hlen]
      refine sum_le_sum fun s _ => ?_
      by_cases hs : p s = 0
      · simp [hs]
      · simp only [ℓ, hs, ite_false, m]
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        push_cast
        linarith [Nat.floor_le (hx0 s)]
    have heq : ∑ s, (p s).toReal * (x s + 1) = measureEntropy p.toMeasure / Real.log D + 1 := by
      simp only [mul_add, mul_one, sum_add_distrib, sum_toReal_pmf_eq_one, measureEntropy_toMeasure,
        sum_div, x, Real.negMulLog]
      congr 1
      exact sum_congr rfl fun s _ => by ring
    linarith

variable {n D : ℕ}

theorem IsUDCode.mul_measureEntropy_le [NeZero D] (p : PMF S)
    {c : (Fin n → S) → List (Fin D)} (hc : IsUDCode c) :
    n * measureEntropy p.toMeasure ≤ expectedLength (iidPMF p n) c * Real.log D := by
  rw [← measureEntropy_iidPMF]
  exact hc.measureEntropy_le _

theorem IsUDCode.div_log_le_expectedLength_div (hD : 2 ≤ D) (hn : 0 < n) (p : PMF S)
    {c : (Fin n → S) → List (Fin D)} (hc : IsUDCode c) :
    measureEntropy p.toMeasure / Real.log D ≤ expectedLength (iidPMF p n) c / n := by
  have : NeZero D := ⟨by omega⟩
  have hlogD : 0 < Real.log D := Real.log_pos (by exact_mod_cast hD)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [div_le_div_iff₀ hlogD hn']
  linarith [hc.mul_measureEntropy_le p]

theorem exists_isPrefixCode_block_le (hD : 2 ≤ D) (p : PMF S) (n : ℕ) :
    ∃ c : (Fin n → S) → List (Fin D), IsPrefixCode c ∧ (∀ x, c x ≠ []) ∧
      expectedLength (iidPMF p n) c ≤ n * measureEntropy p.toMeasure / Real.log D + 1 := by
  obtain ⟨c, hc, hne, hle⟩ := exists_isPrefixCode_expectedLength_le hD (iidPMF p n)
  exact ⟨c, hc, hne, by rwa [measureEntropy_iidPMF] at hle⟩

theorem exists_isPrefixCode_block_lt (hD : 2 ≤ D) {p : PMF S} (hp : ∀ s, p s ≠ 0) (n : ℕ) :
    ∃ c : (Fin n → S) → List (Fin D), IsPrefixCode c ∧
      expectedLength (iidPMF p n) c < n * measureEntropy p.toMeasure / Real.log D + 1 := by
  obtain ⟨c, hc, hlt⟩ := exists_isPrefixCode_expectedLength_lt hD (iidPMF p n) (iidPMF_ne_zero hp)
  exact ⟨c, hc, by rwa [measureEntropy_iidPMF] at hlt⟩

private lemma div_add_one_div (hn : 0 < n) (a : ℝ) : (n * a + 1) / n = a + 1 / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  field_simp

theorem exists_isPrefixCode_block_div_le (hD : 2 ≤ D) (p : PMF S) (hn : 0 < n) :
    ∃ c : (Fin n → S) → List (Fin D), IsPrefixCode c ∧ (∀ x, c x ≠ []) ∧
      expectedLength (iidPMF p n) c / n ≤ measureEntropy p.toMeasure / Real.log D + 1 / n := by
  obtain ⟨c, hc, hne, hle⟩ := exists_isPrefixCode_block_le hD p n
  refine ⟨c, hc, hne, ?_⟩
  rw [← div_add_one_div hn, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hle (Nat.cast_nonneg n)

theorem exists_isPrefixCode_block_div_lt (hD : 2 ≤ D) {p : PMF S} (hp : ∀ s, p s ≠ 0)
    (hn : 0 < n) :
    ∃ c : (Fin n → S) → List (Fin D), IsPrefixCode c ∧
      expectedLength (iidPMF p n) c / n < measureEntropy p.toMeasure / Real.log D + 1 / n := by
  obtain ⟨c, hc, hlt⟩ := exists_isPrefixCode_block_lt hD hp n
  refine ⟨c, hc, ?_⟩
  rw [← div_add_one_div hn, ← mul_div_assoc]
  exact div_lt_div_of_pos_right hlt (Nat.cast_pos.2 hn)

noncomputable def minExpectedLength (p : PMF S) (n D : ℕ) : ℝ :=
  sInf {L | ∃ c : (Fin n → S) → List (Fin D), IsUDCode c ∧ expectedLength (iidPMF p n) c = L}

theorem minExpectedLength_bounds (hD : 2 ≤ D) (p : PMF S) (n : ℕ) :
    n * measureEntropy p.toMeasure / Real.log D ≤ minExpectedLength p n D ∧
      minExpectedLength p n D ≤ n * measureEntropy p.toMeasure / Real.log D + 1 := by
  have : NeZero D := ⟨by omega⟩
  have hlogD : 0 < Real.log D := Real.log_pos (by exact_mod_cast hD)
  have hlow : ∀ L ∈ {L | ∃ c : (Fin n → S) → List (Fin D), IsUDCode c ∧
      expectedLength (iidPMF p n) c = L}, n * measureEntropy p.toMeasure / Real.log D ≤ L := by
    rintro L ⟨c, hc, rfl⟩
    rw [div_le_iff₀ hlogD]
    exact hc.mul_measureEntropy_le p
  obtain ⟨c, hc, hne, hle⟩ := exists_isPrefixCode_block_le hD p n
  have hmem : expectedLength (iidPMF p n) c ∈ {L | ∃ c : (Fin n → S) → List (Fin D),
      IsUDCode c ∧ expectedLength (iidPMF p n) c = L} := ⟨c, hc.isUDCode hne, rfl⟩
  exact ⟨le_csInf ⟨_, hmem⟩ hlow, (csInf_le ⟨_, hlow⟩ hmem).trans hle⟩

theorem tendsto_minExpectedLength_div (hD : 2 ≤ D) (p : PMF S) :
    Tendsto (fun n : ℕ => minExpectedLength p n D / n) atTop
      (𝓝 (measureEntropy p.toMeasure / Real.log D)) := by
  have hu : Tendsto (fun n : ℕ => measureEntropy p.toMeasure / Real.log D + 1 / n) atTop
      (𝓝 (measureEntropy p.toMeasure / Real.log D)) := by
    simpa using (tendsto_const_nhds (x := measureEntropy p.toMeasure / Real.log D)).add
      tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [le_div_iff₀ hn', div_mul_eq_mul_div, mul_comm]
    exact (minExpectedLength_bounds hD p n).1
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← div_add_one_div hn, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (minExpectedLength_bounds hD p n).2 (Nat.cast_nonneg n)

end Meat
