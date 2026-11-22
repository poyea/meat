import Meat.Shannon.Types

open MeasureTheory Filter Topology Finset

namespace Meat

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private lemma sum_iidProb_mul_mul (p : PMF S) {n : ℕ} (Y : S → ℝ)
    (hY : ∑ s, (p s).toReal * Y s = 0) (i j : Fin n) :
    ∑ x, iidProb p x * (Y (x i) * Y (x j)) =
      if i = j then ∑ s, (p s).toReal * Y s ^ 2 else 0 := by
  have h := sum_prod_mul_prod (fun (_ : Fin n) s => (p s).toReal) fun k s =>
    (if k = i then Y s else 1) * (if k = j then Y s else 1)
  simp only [prod_mul_distrib, prod_ite_eq', mem_univ, ite_true] at h
  simp only [iidProb]
  rw [h]
  split_ifs with hij
  · subst hij
    rw [prod_eq_single i (fun k _ hk => by simp [hk, sum_toReal_pmf_eq_one]) (by simp)]
    simp [sq]
  · exact prod_eq_zero (mem_univ i) (by simp [hij, hY])

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private lemma sum_iidProb_mul_sq (p : PMF S) {n : ℕ} (Y : S → ℝ)
    (hY : ∑ s, (p s).toReal * Y s = 0) :
    ∑ x : Fin n → S, iidProb p x * (∑ i, Y (x i)) ^ 2 = n * ∑ s, (p s).toReal * Y s ^ 2 := by
  simp_rw [sq, sum_mul_sum, mul_sum]
  rw [sum_comm]
  rw [Finset.sum_congr rfl fun i _ => by rw [sum_comm]]
  simp [sum_iidProb_mul_mul p Y hY, ← sq, mul_sum]

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem tendsto_sum_iidProb_abs_sub_le (p : PMF S) (f : S → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => ∑ x : Fin n → S with
      |∑ i, f (x i) - n * ∑ s, (p s).toReal * f s| ≤ n * δ, iidProb p x) atTop (𝓝 1) := by
  classical
  set E := ∑ s, (p s).toReal * f s
  set Y : S → ℝ := fun s => f s - E
  have hY : ∑ s, (p s).toReal * Y s = 0 := by
    simp only [Y, mul_sub, sum_sub_distrib, ← sum_mul, sum_toReal_pmf_eq_one, one_mul]
    exact sub_self _
  set V := ∑ s, (p s).toReal * Y s ^ 2
  have key : ∀ n : ℕ, 0 < n → 1 - V / δ ^ 2 / n
      ≤ ∑ x : Fin n → S with |∑ i, f (x i) - n * E| ≤ n * δ, iidProb p x := by
    intro n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hnδ : 0 < (n * δ) ^ 2 := by positivity
    have hpt : ∀ x : Fin n → S, (if |∑ i, f (x i) - n * E| ≤ n * δ then 0 else iidProb p x)
        ≤ iidProb p x * (∑ i, Y (x i)) ^ 2 / (n * δ) ^ 2 := by
      intro x
      split_ifs with hx
      · exact div_nonneg (mul_nonneg (iidProb_nonneg p x) (sq_nonneg _)) hnδ.le
      have hs : ∑ i, Y (x i) = ∑ i, f (x i) - n * E := by
        simp [Y, sum_sub_distrib]
      rw [hs]
      push Not at hx
      have : (n * δ) ^ 2 < (∑ i, f (x i) - n * E) ^ 2 := by
        rw [← sq_abs (∑ i, f (x i) - n * E)]
        exact pow_lt_pow_left₀ hx (by positivity) two_ne_zero
      rw [le_div_iff₀ hnδ]
      exact mul_le_mul_of_nonneg_left this.le (iidProb_nonneg p x)
    have hsum := sum_le_sum fun x (_ : x ∈ univ) => hpt x
    rw [← sum_div, sum_iidProb_mul_sq p Y hY] at hsum
    have hc : ∑ x : Fin n → S, (if |∑ i, f (x i) - n * E| ≤ n * δ then 0 else iidProb p x)
        = 1 - ∑ x : Fin n → S with |∑ i, f (x i) - n * E| ≤ n * δ, iidProb p x := by
      rw [← sum_iidProb p n, sum_filter, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by split_ifs <;> simp
    rw [hc] at hsum
    have he : n * V / (n * δ) ^ 2 = V / δ ^ 2 / n := by
      field_simp
    linarith
  have hl : Tendsto (fun n : ℕ => 1 - V / δ ^ 2 / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (V / δ ^ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact key n hn
  · refine Eventually.of_forall fun n => ?_
    rw [← sum_iidProb p n]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => iidProb_nonneg p x

omit [DecidableEq S] in
theorem klDiv_toMeasure (p q : PMF S) :
    klDiv p.toMeasure q.toMeasure
      = ∑ s, (p s).toReal * Real.log ((p s).toReal / (q s).toReal) := by
  simp [klDiv, PMF.toMeasure_real_singleton]

omit [Fintype S] [DecidableEq S] in
theorem PMF.toMeasure_absolutelyContinuous_iff [Countable S] (p q : PMF S) :
    p.toMeasure ≪ q.toMeasure ↔ ∀ s, q s = 0 → p s = 0 := by
  rw [absolutelyContinuous_iff_singleton]
  simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem iidProb_eq_exp_mul {n : ℕ} {p q : PMF S} (hpq : ∀ s, q s = 0 → p s = 0) {x : Fin n → S}
    (hx : 0 < iidProb p x) :
    iidProb p x
      = Real.exp (∑ i, Real.log ((p (x i)).toReal / (q (x i)).toReal)) * iidProb q x := by
  have hp : ∀ i, p (x i) ≠ 0 := fun i h => by
    have := prod_ne_zero_iff.1 hx.ne' i (mem_univ i)
    simp [h] at this
  rw [Real.exp_sum, iidProb, iidProb, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  have h1 := ENNReal.toReal_pos (hp i) (p.apply_ne_top _)
  have h2 := ENNReal.toReal_pos (fun h => hp i (hpq _ h)) (q.apply_ne_top (x i))
  rw [Real.exp_log (div_pos h1 h2), div_mul_cancel₀ _ h2.ne']

noncomputable def steinBeta (p q : PMF S) (n : ℕ) (ε : ℝ) : ℝ :=
  ⨅ A : {A : Finset (Fin n → S) // ∑ x ∈ Aᶜ, iidProb p x ≤ ε}, ∑ x ∈ A.1, iidProb q x

omit [DecidableEq S] in
private lemma tendsto_llr (p q : PMF S) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => ∑ x : Fin n → S with
      |∑ i, Real.log ((p (x i)).toReal / (q (x i)).toReal) - n * klDiv p.toMeasure q.toMeasure|
        ≤ n * δ, iidProb p x) atTop (𝓝 1) := by
  have h := tendsto_sum_iidProb_abs_sub_le p (fun s => Real.log ((p s).toReal / (q s).toReal)) hδ
  beta_reduce at h
  rw [← klDiv_toMeasure] at h
  exact h

theorem stein_achievability (p q : PMF S) (hpq : p.toMeasure ≪ q.toMeasure) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ A : Finset (Fin n → S), ∑ x ∈ Aᶜ, iidProb p x ≤ ε ∧
      ∑ x ∈ A, iidProb q x ≤ Real.exp (-(n * (klDiv p.toMeasure q.toMeasure - δ))) := by
  rw [PMF.toMeasure_absolutelyContinuous_iff] at hpq
  set D := klDiv p.toMeasure q.toMeasure
  set f : S → ℝ := fun s => Real.log ((p s).toReal / (q s).toReal)
  filter_upwards [(tendsto_llr p q hδ).eventually (lt_mem_nhds (show 1 - ε < 1 by linarith))]
    with n hn
  refine ⟨({x | 0 < iidProb p x ∧ |∑ i, f (x i) - n * D| ≤ n * δ} : Finset (Fin n → S)), ?_, ?_⟩
  · have e : ∑ x : Fin n → S with 0 < iidProb p x ∧ |∑ i, f (x i) - n * D| ≤ n * δ, iidProb p x
        = ∑ x : Fin n → S with |∑ i, f (x i) - n * D| ≤ n * δ, iidProb p x := by
      rw [sum_filter, sum_filter]
      refine sum_congr rfl fun x _ => ?_
      rcases (iidProb_nonneg p x).eq_or_lt with h | h
      · simp [← h]
      · simp [h]
    have hc := sum_compl_add_sum
      ({x | 0 < iidProb p x ∧ |∑ i, f (x i) - n * D| ≤ n * δ} : Finset (Fin n → S))
      (iidProb p)
    rw [sum_iidProb, e] at hc
    linarith
  · have hle : ∀ x ∈ ({x | 0 < iidProb p x ∧ |∑ i, f (x i) - n * D| ≤ n * δ} :
        Finset (Fin n → S)), iidProb q x ≤ Real.exp (-(n * (D - δ))) * iidProb p x := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      have he := iidProb_eq_exp_mul hpq hx.1
      have hb : n * (D - δ) ≤ ∑ i, f (x i) := by
        have := (abs_le.1 hx.2).1
        linarith
      rw [he, ← mul_assoc, ← Real.exp_add]
      refine le_mul_of_one_le_left (iidProb_nonneg q x) (Real.one_le_exp ?_)
      simp only [f] at hb
      linarith
    refine (sum_le_sum hle).trans ?_
    rw [← mul_sum]
    refine mul_le_of_le_one_right (Real.exp_pos _).le ?_
    rw [← sum_iidProb p n]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => iidProb_nonneg p x

theorem stein_converse (p q : PMF S) (hpq : p.toMeasure ≪ q.toMeasure) {ε δ : ℝ}
    (hε : ε < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset (Fin n → S), ∑ x ∈ Aᶜ, iidProb p x ≤ ε →
      Real.exp (-(n * (klDiv p.toMeasure q.toMeasure + δ))) ≤ ∑ x ∈ A, iidProb q x := by
  rw [PMF.toMeasure_absolutelyContinuous_iff] at hpq
  set D := klDiv p.toMeasure q.toMeasure
  set f : S → ℝ := fun s => Real.log ((p s).toReal / (q s).toReal)
  have hε' : 0 < (1 - ε) / 2 := by linarith
  filter_upwards [(tendsto_llr p q (half_pos hδ)).eventually
      (lt_mem_nhds (show 1 - (1 - ε) / 2 < 1 by linarith)),
    (tendsto_exp_nat_mul (show -(δ / 2) < 0 by linarith)).eventually (gt_mem_nhds hε')]
    with n hn hexp A hA
  set B : Finset (Fin n → S) := {x | |∑ i, f (x i) - n * D| ≤ n * (δ / 2)}
  have hA1 : 1 - ε ≤ ∑ x ∈ A, iidProb p x := by
    have := sum_compl_add_sum A (iidProb p)
    rw [sum_iidProb] at this
    linarith
  have hAB : (1 - ε) / 2 ≤ ∑ x ∈ A ∩ B, iidProb p x := by
    have hu := sum_union_inter (s₁ := A) (s₂ := B) (f := iidProb p)
    have h1 : ∑ x ∈ A ∪ B, iidProb p x ≤ 1 := by
      rw [← sum_iidProb p n]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => iidProb_nonneg p x
    have hB : 1 - (1 - ε) / 2 < ∑ x ∈ B, iidProb p x := hn
    linarith
  have hle : ∀ x ∈ A ∩ B, Real.exp (-(n * (D + δ / 2))) * iidProb p x ≤ iidProb q x := by
    intro x hx
    rcases (iidProb_nonneg p x).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero]
      exact iidProb_nonneg q x
    have hb : ∑ i, f (x i) ≤ n * (D + δ / 2) := by
      have := (abs_le.1 (mem_filter.1 (mem_inter.1 hx).2).2).2
      linarith
    rw [iidProb_eq_exp_mul hpq h0, ← mul_assoc, ← Real.exp_add]
    refine mul_le_of_le_one_left (iidProb_nonneg q x) (Real.exp_le_one_iff.2 ?_)
    simp only [f] at hb
    linarith
  calc Real.exp (-(n * (D + δ)))
      = Real.exp (-(n * (D + δ / 2))) * Real.exp (n * -(δ / 2)) := by
        rw [← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(n * (D + δ / 2))) * ∑ x ∈ A ∩ B, iidProb p x :=
        mul_le_mul_of_nonneg_left (hexp.le.trans hAB) (Real.exp_pos _).le
    _ ≤ ∑ x ∈ A ∩ B, iidProb q x := by
        rw [mul_sum]
        exact sum_le_sum hle
    _ ≤ ∑ x ∈ A, iidProb q x :=
        sum_le_sum_of_subset_of_nonneg inter_subset_left fun x _ _ => iidProb_nonneg q x

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
private lemma steinBeta_spec (p q : PMF S) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∃ A : Finset (Fin n → S), ∑ x ∈ Aᶜ, iidProb p x ≤ ε ∧
      ∑ x ∈ A, iidProb q x = steinBeta p q n ε) ∧
    ∀ A : Finset (Fin n → S), ∑ x ∈ Aᶜ, iidProb p x ≤ ε →
      steinBeta p q n ε ≤ ∑ x ∈ A, iidProb q x := by
  have : Nonempty {A : Finset (Fin n → S) // ∑ x ∈ Aᶜ, iidProb p x ≤ ε} :=
    ⟨⟨univ, by simp [hε]⟩⟩
  refine ⟨?_, fun A hA => ?_⟩
  · obtain ⟨⟨A, hA⟩, e⟩ := exists_eq_ciInf_of_finite
      (f := fun A : {A : Finset (Fin n → S) // ∑ x ∈ Aᶜ, iidProb p x ≤ ε} =>
        ∑ x ∈ A.1, iidProb q x)
    exact ⟨A, hA, e⟩
  · exact ciInf_le (Set.finite_range _).bddBelow (⟨A, hA⟩ :
      {A : Finset (Fin n → S) // ∑ x ∈ Aᶜ, iidProb p x ≤ ε})

theorem tendsto_steinBeta (p q : PMF S) (hpq : p.toMeasure ≪ q.toMeasure) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => -Real.log (steinBeta p q n ε) / n) atTop
      (𝓝 (klDiv p.toMeasure q.toMeasure)) := by
  set D := klDiv p.toMeasure q.toMeasure
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < steinBeta p q n ε := by
    filter_upwards [stein_converse p q hpq hε1 one_pos] with n hn
    obtain ⟨A, hA, e⟩ := (steinBeta_spec p q n hε0.le).1
    exact e ▸ (Real.exp_pos _).trans_le (hn A hA)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hpos, stein_achievability p q hpq hε0 (half_pos (sub_pos.2 ha)),
      eventually_gt_atTop 0] with n hn hA hn0
    obtain ⟨A, hA, hq⟩ := hA
    refine lt_of_lt_of_le (show a < D - (D - a) / 2 by linarith)
      (le_neg_log_div_of_le_exp hn0 hn (((steinBeta_spec p q n hε0.le).2 A hA).trans hq))
  · filter_upwards [stein_converse p q hpq hε1 (half_pos (sub_pos.2 hb)),
      eventually_gt_atTop 0] with n hn hn0
    obtain ⟨A, hA, e⟩ := (steinBeta_spec p q n hε0.le).1
    refine (neg_log_div_le_of_exp_le hn0 (e ▸ hn A hA)).trans_lt ?_
    linarith

end Meat
