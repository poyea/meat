import Meat.Shannon.Types

open MeasureTheory Filter Topology Finset

namespace Meat

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

noncomputable def bayesError (p q : PMF S) (n : ℕ) : ℝ :=
  ⨅ A : Finset (Fin n → S), (∑ x ∈ Aᶜ, iidProb p x + ∑ x ∈ A, iidProb q x)

noncomputable def chernoffInfo (p q : PMF S) : ℝ :=
  ⨆ t : Set.Ioo (0 : ℝ) 1,
    -Real.log (∑ s, (p s).toReal ^ (t : ℝ) * (q s).toReal ^ (1 - (t : ℝ)))

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem bayesError_eq_sum_min (p q : PMF S) (n : ℕ) :
    bayesError p q n = ∑ x : Fin n → S, min (iidProb p x) (iidProb q x) := by
  refine le_antisymm ?_ (le_ciInf fun A => ?_)
  · refine (ciInf_le (Set.finite_range _).bddBelow
      ({x | iidProb q x ≤ iidProb p x} : Finset (Fin n → S))).trans_eq ?_
    rw [← sum_compl_add_sum ({x | iidProb q x ≤ iidProb p x} : Finset (Fin n → S))]
    congr 1
    · refine sum_congr rfl fun x hx => ?_
      simp only [mem_compl, mem_filter, mem_univ, true_and, not_le] at hx
      exact (min_eq_left hx.le).symm
    · refine sum_congr rfl fun x hx => ?_
      simp only [mem_filter, mem_univ, true_and] at hx
      exact (min_eq_right hx).symm
  · rw [← sum_compl_add_sum A]
    exact add_le_add (sum_le_sum fun x _ => min_le_left _ _)
      (sum_le_sum fun x _ => min_le_right _ _)

private lemma min_le_rpow_mul_rpow {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : min a b ≤ a ^ t * b ^ (1 - t) := by
  have split : ∀ c : ℝ, 0 ≤ c → c = c ^ t * c ^ (1 - t) := fun c hc => by
    rw [← Real.rpow_add' hc (by norm_num), add_sub_cancel, Real.rpow_one]
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    calc a = a ^ t * a ^ (1 - t) := split a ha
      _ ≤ a ^ t * b ^ (1 - t) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha h (by linarith)) (Real.rpow_nonneg ha t)
  · rw [min_eq_right h]
    calc b = b ^ t * b ^ (1 - t) := split b hb
      _ ≤ a ^ t * b ^ (1 - t) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hb h ht0) (Real.rpow_nonneg hb _)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem bayesError_le_pow (p q : PMF S) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    bayesError p q n ≤ (∑ s, (p s).toReal ^ t * (q s).toReal ^ (1 - t)) ^ n := by
  rw [bayesError_eq_sum_min]
  have h : (∑ s, (p s).toReal ^ t * (q s).toReal ^ (1 - t)) ^ n
      = ∑ x : Fin n → S, ∏ i, ((p (x i)).toReal ^ t * (q (x i)).toReal ^ (1 - t)) := by
    rw [← Fintype.prod_sum (fun (_ : Fin n) s => (p s).toReal ^ t * (q s).toReal ^ (1 - t)),
      prod_const, card_univ, Fintype.card_fin]
  rw [h]
  refine sum_le_sum fun x _ => ?_
  rw [prod_mul_distrib, Real.finsetProd_rpow _ _ (fun i _ => ENNReal.toReal_nonneg),
    Real.finsetProd_rpow _ _ (fun i _ => ENNReal.toReal_nonneg)]
  exact min_le_rpow_mul_rpow (iidProb_nonneg p x) (iidProb_nonneg q x) ht0 ht1

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem bayesError_pos (p q : PMF S) (hpq : ∃ s, p s ≠ 0 ∧ q s ≠ 0) (n : ℕ) :
    0 < bayesError p q n := by
  obtain ⟨s, hp, hq⟩ := hpq
  rw [bayesError_eq_sum_min]
  have hx : 0 < min (iidProb p fun _ : Fin n => s) (iidProb q fun _ : Fin n => s) :=
    lt_min (prod_pos fun i _ => ENNReal.toReal_pos hp (p.apply_ne_top _))
      (prod_pos fun i _ => ENNReal.toReal_pos hq (q.apply_ne_top _))
  exact hx.trans_le (single_le_sum (f := fun x => min (iidProb p x) (iidProb q x))
    (fun x _ => le_min (iidProb_nonneg p x) (iidProb_nonneg q x)) (mem_univ _))

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private lemma bddAbove_chernoff (p q : PMF S) (hpq : ∃ s, p s ≠ 0 ∧ q s ≠ 0) :
    BddAbove (Set.range fun t : Set.Ioo (0 : ℝ) 1 =>
      -Real.log (∑ s, (p s).toReal ^ (t : ℝ) * (q s).toReal ^ (1 - (t : ℝ)))) := by
  obtain ⟨s, hp, hq⟩ := hpq
  have ha := ENNReal.toReal_pos hp (p.apply_ne_top s)
  have hb := ENNReal.toReal_pos hq (q.apply_ne_top s)
  set m := min (p s).toReal (q s).toReal
  have hm : 0 < m := lt_min ha hb
  refine ⟨-Real.log m, ?_⟩
  rintro _ ⟨⟨t, ht0, ht1⟩, rfl⟩
  simp only
  have hle : m ≤ ∑ s, (p s).toReal ^ t * (q s).toReal ^ (1 - t) := by
    refine le_trans ?_ (single_le_sum (fun s _ => mul_nonneg (Real.rpow_nonneg
      ENNReal.toReal_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)) (mem_univ s))
    calc m = m ^ t * m ^ (1 - t) := by
          rw [← Real.rpow_add' hm.le (by norm_num), add_sub_cancel, Real.rpow_one]
      _ ≤ (p s).toReal ^ t * (q s).toReal ^ (1 - t) :=
          mul_le_mul (Real.rpow_le_rpow hm.le (min_le_left _ _) ht0.le)
            (Real.rpow_le_rpow hm.le (min_le_right _ _) (by linarith))
            (Real.rpow_nonneg hm.le _) (Real.rpow_nonneg ha.le _)
  linarith [Real.log_le_log hm hle]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem bayesError_le_exp (p q : PMF S) (hpq : ∃ s, p s ≠ 0 ∧ q s ≠ 0) (n : ℕ) :
    bayesError p q n ≤ Real.exp (-(n * chernoffInfo p q)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using bayesError_le_pow p q 0 (t := 1 / 2) (by norm_num) (by norm_num)
  have he := bayesError_pos p q hpq n
  obtain ⟨s₀, hp, hq⟩ := hpq
  have hC : chernoffInfo p q ≤ -Real.log (bayesError p q n) / n := by
    have : Nonempty (Set.Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
    refine ciSup_le fun ⟨t, ht0, ht1⟩ => ?_
    have hZ : 0 < ∑ s, (p s).toReal ^ t * (q s).toReal ^ (1 - t) := lt_of_lt_of_le (mul_pos
        (Real.rpow_pos_of_pos (ENNReal.toReal_pos hp (p.apply_ne_top _)) t)
        (Real.rpow_pos_of_pos (ENNReal.toReal_pos hq (q.apply_ne_top _)) _))
      (single_le_sum (f := fun s => (p s).toReal ^ t * (q s).toReal ^ (1 - t))
        (fun s _ => mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)) (mem_univ s₀))
    refine le_neg_log_div_of_le_exp hn he ((bayesError_le_pow p q n ht0.le ht1.le).trans_eq ?_)
    rw [mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hZ]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [le_div_iff₀ hn'] at hC
  calc bayesError p q n = Real.exp (Real.log (bayesError p q n)) := (Real.exp_log he).symm
    _ ≤ Real.exp (-(n * chernoffInfo p q)) := Real.exp_le_exp.2 (by linarith)

theorem exp_le_bayesError (p q : PMF S) (hpq : ∃ s, p s ≠ 0 ∧ q s ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(n * (chernoffInfo p q + η))) ≤ bayesError p q n := by
  classical
  obtain ⟨s₀, hp₀, hq₀⟩ := hpq
  have hapos : ∀ s, p s ≠ 0 → 0 < (p s).toReal := fun s h =>
    ENNReal.toReal_pos h (p.apply_ne_top s)
  have hbpos : ∀ s, q s ≠ 0 → 0 < (q s).toReal := fun s h =>
    ENNReal.toReal_pos h (q.apply_ne_top s)
  obtain ⟨w, hw⟩ : ∃ w : ℝ → S → ℝ, ∀ μ s, w μ s = if p s ≠ 0 ∧ q s ≠ 0 then
      (p s).toReal ^ μ * (q s).toReal ^ (1 - μ) else 0 := ⟨_, fun _ _ => rfl⟩
  have hw0 : ∀ μ s, 0 ≤ w μ s := fun μ s => by
    rw [hw]
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    · exact le_rfl
  have hwB : ∀ μ s, p s ≠ 0 ∧ q s ≠ 0 → w μ s = (p s).toReal ^ μ * (q s).toReal ^ (1 - μ) :=
    fun μ s h => by
      rw [hw]
      split_ifs
      rfl
  have hwA : ∀ μ s, ¬(p s ≠ 0 ∧ q s ≠ 0) → w μ s = 0 := fun μ s h => by simp [hw, h]
  have hwcont : ∀ s, Continuous fun μ => w μ s := fun s => by
    simp_rw [hw]
    split_ifs with h
    · exact (Real.continuous_const_rpow (hapos s h.1).ne').mul
        ((Real.continuous_const_rpow (hbpos s h.2).ne').comp (continuous_const.sub continuous_id))
    · exact continuous_const
  obtain ⟨Z, hZd⟩ : ∃ Z : ℝ → ℝ, ∀ μ, Z μ = ∑ s, w μ s := ⟨_, fun _ => rfl⟩
  have hZ : ∀ μ, 0 < Z μ := fun μ => by
    rw [hZd]
    refine lt_of_lt_of_le ?_ (single_le_sum (fun s _ => hw0 μ s) (mem_univ s₀))
    rw [hwB μ s₀ ⟨hp₀, hq₀⟩]
    exact mul_pos (Real.rpow_pos_of_pos (hapos _ hp₀) _) (Real.rpow_pos_of_pos (hbpos _ hq₀) _)
  have hZcont : Continuous Z := by
    rw [funext hZd]
    exact continuous_finsetSum _ fun s _ => hwcont s
  set L : S → ℝ := fun s => Real.log (p s).toReal - Real.log (q s).toReal
  obtain ⟨m, hmd⟩ : ∃ m : ℝ → ℝ, ∀ μ, m μ = ∑ s, w μ s / Z μ * L s := ⟨_, fun _ => rfl⟩
  have hmcont : Continuous m := by
    rw [funext hmd]
    exact continuous_finsetSum _ fun s _ =>
      ((hwcont s).div hZcont fun μ => (hZ μ).ne').mul continuous_const
  have hQ1 : ∀ μ, ∑ s, w μ s / Z μ = 1 := fun μ => by
    rw [← sum_div, ← hZd, div_self (hZ μ).ne']
  have hlogQ : ∀ μ s, p s ≠ 0 ∧ q s ≠ 0 → Real.log (w μ s / Z μ)
      = μ * Real.log (p s).toReal + (1 - μ) * Real.log (q s).toReal - Real.log (Z μ) := by
    intro μ s h
    have h1 := Real.rpow_pos_of_pos (hapos s h.1) μ
    have h2 := Real.rpow_pos_of_pos (hbpos s h.2) (1 - μ)
    rw [hwB μ s h, Real.log_div (mul_pos h1 h2).ne' (hZ μ).ne', Real.log_mul h1.ne' h2.ne',
      Real.log_rpow (hapos s h.1), Real.log_rpow (hbpos s h.2)]
  have hLp : ∀ μ, ∑ s, (w μ s / Z μ * Real.log (w μ s / Z μ)
      - w μ s / Z μ * Real.log (p s).toReal) = -(1 - μ) * m μ - Real.log (Z μ) := by
    intro μ
    have e : ∀ s, w μ s / Z μ * Real.log (w μ s / Z μ) - w μ s / Z μ * Real.log (p s).toReal
        = -(1 - μ) * (w μ s / Z μ * L s) - Real.log (Z μ) * (w μ s / Z μ) := fun s => by
      by_cases h : p s ≠ 0 ∧ q s ≠ 0
      · rw [hlogQ μ s h]
        ring
      · simp [hwA μ s h]
    rw [sum_congr rfl fun s _ => e s, sum_sub_distrib, ← mul_sum, ← mul_sum, hQ1, ← hmd]
    ring
  have hLq : ∀ μ, ∑ s, (w μ s / Z μ * Real.log (w μ s / Z μ)
      - w μ s / Z μ * Real.log (q s).toReal) = μ * m μ - Real.log (Z μ) := by
    intro μ
    have e : ∀ s, w μ s / Z μ * Real.log (w μ s / Z μ) - w μ s / Z μ * Real.log (q s).toReal
        = μ * (w μ s / Z μ * L s) - Real.log (Z μ) * (w μ s / Z μ) := fun s => by
      by_cases h : p s ≠ 0 ∧ q s ≠ 0
      · rw [hlogQ μ s h]
        ring
      · simp [hwA μ s h]
    rw [sum_congr rfl fun s _ => e s, sum_sub_distrib, ← mul_sum, ← mul_sum, hQ1, ← hmd]
    ring
  obtain ⟨μ, hμ, hμp, hμq⟩ : ∃ μ ∈ Set.Icc (0 : ℝ) 1, -(1 - μ) * m μ ≤ 0 ∧ μ * m μ ≤ 0 := by
    by_cases h0 : 0 ≤ m 0
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by linarith, by simp⟩
    by_cases h1 : m 1 ≤ 0
    · exact ⟨1, ⟨zero_le_one, le_rfl⟩, by simp, by linarith⟩
    obtain ⟨μ, hμ, hm⟩ := intermediate_value_Icc zero_le_one hmcont.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (m 0) (m 1) from ⟨by linarith, by linarith⟩)
    exact ⟨μ, hμ, by rw [hm]; simp, by rw [hm]; simp⟩
  have hFC : -Real.log (Z μ) ≤ chernoffInfo p q := by
    have hin : ∀ t ∈ Set.Ioo (0 : ℝ) 1, -Real.log (Z t) ≤ chernoffInfo p q := by
      intro t ht
      have e : Z t = ∑ s, (p s).toReal ^ t * (q s).toReal ^ (1 - t) := by
        rw [hZd]
        refine sum_congr rfl fun s _ => ?_
        rw [hw]
        split_ifs with h
        · rfl
        · rcases not_and_or.1 h with h | h
          · rw [not_not.1 h, ENNReal.toReal_zero, Real.zero_rpow ht.1.ne', zero_mul]
          · rw [not_not.1 h, ENNReal.toReal_zero, Real.zero_rpow (by linarith [ht.2]), mul_zero]
      rw [e]
      exact le_ciSup (bddAbove_chernoff p q ⟨s₀, hp₀, hq₀⟩) (⟨t, ht⟩ : Set.Ioo (0 : ℝ) 1)
    have hne : (𝓝[Set.Ioo (0 : ℝ) 1] μ).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo zero_ne_one]
      exact hμ
    have hcont : Tendsto (fun t => -Real.log (Z t)) (𝓝[Set.Ioo (0 : ℝ) 1] μ)
        (𝓝 (-Real.log (Z μ))) :=
      ((Real.continuousAt_log (hZ μ).ne').comp hZcont.continuousAt).neg.tendsto.mono_left
        nhdsWithin_le_nhds
    exact le_of_tendsto hcont (eventually_nhdsWithin_of_forall hin)
  obtain ⟨x, hx0, hx⟩ := exists_seq_typeCount_tendsto (fun s => w μ s / Z μ)
    (fun s => div_nonneg (hw0 μ s) (hZ μ).le) (hQ1 μ)
  have hreal : ∀ s, Tendsto (fun n => (seqType (x n)).real {s}) atTop (𝓝 (w μ s / Z μ)) :=
    fun s => (hx s).congr fun n => (seqType_real (x n) s).symm
  have hcount : ∀ n i, p (x n i) ≠ 0 ∧ q (x n i) ≠ 0 := fun n i => by
    by_contra h
    have := hx0 n (x n i) (by rw [hwA μ _ h, zero_div])
    exact (card_pos.2 ⟨i, by simp⟩ : 0 < typeCount (x n) (x n i)).ne' this
  have hacp : ∀ n, seqType (x n) ≪ p.toMeasure := fun n =>
    (seqType_absolutelyContinuous_iff _ _).2 fun i => (hcount n i).1
  have hacq : ∀ n, seqType (x n) ≪ q.toMeasure := fun n =>
    (seqType_absolutelyContinuous_iff _ _).2 fun i => (hcount n i).2
  have hDp := tendsto_klDiv hacp hreal
  have hDq := tendsto_klDiv hacq hreal
  simp only [PMF.toMeasure_real_singleton] at hDp hDq
  rw [hLp] at hDp
  rw [hLq] at hDq
  set C := chernoffInfo p q
  filter_upwards [hDp.eventually (gt_mem_nhds
      (show -(1 - μ) * m μ - Real.log (Z μ) < C + η / 2 by linarith)),
    hDq.eventually (gt_mem_nhds (show μ * m μ - Real.log (Z μ) < C + η / 2 by linarith)),
    eventually_pow_le_exp (Fintype.card S) (half_pos hη)] with n hnp hnq hpow
  set ν := seqType (x n)
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmin : ∀ y ∈ typeClass ν n,
      Real.exp (-(n * measureEntropy ν)) * Real.exp (-(n * (C + η / 2)))
        ≤ min (iidProb p y) (iidProb q y) := by
    intro y hy
    have hyν := mem_typeClass.1 hy
    rw [← Real.exp_add]
    refine le_min ?_ ?_
    · rw [iidProb_eq_exp p y (hyν ▸ hacp n), hyν]
      exact Real.exp_le_exp.2 (by nlinarith)
    · rw [iidProb_eq_exp q y (hyν ▸ hacq n), hyν]
      exact Real.exp_le_exp.2 (by nlinarith)
  have hsum : #(typeClass ν n)
      * (Real.exp (-(n * measureEntropy ν)) * Real.exp (-(n * (C + η / 2))))
        ≤ bayesError p q n := by
    rw [bayesError_eq_sum_min, ← nsmul_eq_mul, ← sum_const]
    refine (sum_le_sum hmin).trans ?_
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ =>
      le_min (iidProb_nonneg p y) (iidProb_nonneg q y)
  have hT := card_typeClass_ge (mem_typeSet.2 ⟨x n, rfl⟩ : ν ∈ typeSet n)
  refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_right hT (by positivity)) hsum)
  have e1 : Real.exp (n * measureEntropy ν) * Real.exp (-(n * measureEntropy ν)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hpos : (0 : ℝ) < (n + 1) ^ Fintype.card S := by positivity
  rw [← mul_assoc, div_mul_eq_mul_div, e1, one_div_mul_eq_div, le_div_iff₀ hpos]
  calc Real.exp (-(n * (C + η))) * (n + 1) ^ Fintype.card S
      ≤ Real.exp (-(n * (C + η))) * Real.exp (n * (η / 2)) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (-(n * (C + η / 2))) := by
        rw [← Real.exp_add]
        ring_nf

theorem tendsto_chernoff (p q : PMF S) (hpq : ∃ s, p s ≠ 0 ∧ q s ≠ 0) :
    Tendsto (fun n : ℕ => -Real.log (bayesError p q n) / n) atTop (𝓝 (chernoffInfo p q)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact ha.trans_le (le_neg_log_div_of_le_exp hn (bayesError_pos p q hpq n)
      (bayesError_le_exp p q hpq n))
  · filter_upwards [exp_le_bayesError p q hpq (half_pos (sub_pos.2 hb)),
      eventually_gt_atTop 0] with n hn hn0
    refine (neg_log_div_le_of_exp_le hn0 hn).trans_lt ?_
    linarith

end Meat
