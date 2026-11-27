import Meat.Source.Helper
import Meat.Source.WynerZivAchievability

open MeasureTheory Finset Filter Topology
open scoped ENNReal

namespace Meat

namespace Helper

open RateDistortion WynerZiv

section Laws

variable {S T : Type*} [Fintype S] [Fintype T] {m : ℕ}

private noncomputable def pY (q : PMF (T × S × Fin m)) (y : T) : ℝ :=
  ∑ x, ∑ u, (q (y, x, u)).toReal

private noncomputable def pXY (q : PMF (T × S × Fin m)) (y : T) (x : S) : ℝ :=
  ∑ u, (q (y, x, u)).toReal

omit [Fintype S] [Fintype T] in
private lemma pXY_nonneg (q : PMF (T × S × Fin m)) (y : T) (x : S) : 0 ≤ pXY q y x :=
  sum_nonneg fun _ _ => ENNReal.toReal_nonneg

omit [Fintype T] in
private lemma pY_nonneg (q : PMF (T × S × Fin m)) (y : T) : 0 ≤ pY q y :=
  sum_nonneg fun x _ => pXY_nonneg q y x

private noncomputable def chan (q : PMF (T × S × Fin m)) (x₀ : S) (y : T) : PMF S := by
  classical
  exact if h : pY q y = 0 then PMF.pure x₀ else
    PMF.ofFintype (fun x => ENNReal.ofReal (pXY q y x / pY q y)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun x _ =>
        div_nonneg (pXY_nonneg q y x) (pY_nonneg q y), ← sum_div]
      change ENNReal.ofReal (pY q y / pY q y) = 1
      rw [div_self h, ENNReal.ofReal_one])

omit [Fintype T] in
private lemma pXY_eq_mul (q : PMF (T × S × Fin m)) (x₀ : S) (y : T) (x : S) :
    pXY q y x = pY q y * (chan q x₀ y x).toReal := by
  classical
  unfold chan
  by_cases h : pY q y = 0
  · have : pXY q y x ≤ 0 := h ▸ single_le_sum (f := fun x' => pXY q y x')
      (fun x' _ => pXY_nonneg q y x') (mem_univ x)
    rw [le_antisymm this (pXY_nonneg q y x)]
    simp [h]
  · simp only [h, dite_false]
    rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal
      (div_nonneg (pXY_nonneg q y x) (pY_nonneg q y)), mul_div_cancel₀ _ h]

omit [Fintype T] in
private lemma toReal_map_fst [Finite T] (q : PMF (T × S × Fin m)) (y : T) :
    ((q.map Prod.fst) y).toReal = pY q y := by
  classical
  have := Fintype.ofFinite T
  rw [toReal_map_apply, sum_filter, Fintype.sum_prod_type,
    sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
  simp [pY, Fintype.sum_prod_type]

omit [Fintype S] [Fintype T] in
private lemma toReal_map_swap [Finite S] [Finite T] (q : PMF (T × S × Fin m)) (x : S) (y : T) :
    ((q.map fun a => (a.2.1, a.1)) (x, y)).toReal = pXY q y x := by
  classical
  have := Fintype.ofFinite S
  have := Fintype.ofFinite T
  rw [toReal_map_apply, sum_filter, Fintype.sum_prod_type,
    sum_eq_single y (fun b _ hb => by simp [hb]) (by simp), Fintype.sum_prod_type,
    sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
  simp [pXY]

omit [Fintype T] in
private lemma iidProb_source_eq [Finite T] (q : PMF (T × S × Fin m)) (x₀ : S) {n : ℕ}
    (x : Fin n → S) (y : Fin n → T) :
    iidProb (q.map fun a => (a.2.1, a.1)) (fun i => (x i, y i)) =
      iidProb (q.map Prod.fst) y * ∏ i, (chan q x₀ (y i) (x i)).toReal := by
  simp only [iidProb, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [toReal_map_swap, toReal_map_fst, pXY_eq_mul q x₀]

end Laws

section Measure

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {m : ℕ}

private lemma real_setOf (q : PMF (T × S × Fin m)) (P : T × S × Fin m → Prop)
    [DecidablePred P] :
    q.toMeasure.real {ω | P ω} = ∑ ω, if P ω then (q ω).toReal else 0 := by
  rw [measureReal_def, PMF.toMeasure_apply_fintype, ENNReal.toReal_sum fun _ _ =>
    ne_top_of_le_ne_top (PMF.apply_ne_top _ _) (Set.indicator_le_self _ _ _)]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : P ω
  · simp [h]
  · simp [h]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma sum_fst_eq [DecidableEq T] (y : T) (F : T × S × Fin m → ℝ) :
    ∑ ω : T × S × Fin m, (if ω.1 = y then F ω else 0) = ∑ x, ∑ u, F (y, x, u) := by
  rw [Fintype.sum_prod_type, sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
  simp [Fintype.sum_prod_type]

private lemma markov_factor (q : PMF (T × S × Fin m))
    (hM : MarkovChain (fun a : T × S × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) (y : T) (x : S) (u : Fin m) :
    (q (y, x, u)).toReal * pY q y = lawXU q (y, u) * pXY q y x := by
  classical
  have h := (markovChain_iff (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _)).1 hM u y x
  have m1 : q.toMeasure.real {ω : T × S × Fin m | ω.2.2 = u ∧ ω.1 = y ∧ ω.2.1 = x} =
      (q (y, x, u)).toReal := by
    have : {ω : T × S × Fin m | ω.2.2 = u ∧ ω.1 = y ∧ ω.2.1 = x} = {(y, x, u)} := by
      ext ⟨a, b, c⟩
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
      tauto
    rw [this, measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have m2 : q.toMeasure.real {ω : T × S × Fin m | ω.1 = y} = pY q y := by
    rw [real_setOf, sum_fst_eq]
    rfl
  have m3 : q.toMeasure.real {ω : T × S × Fin m | ω.2.2 = u ∧ ω.1 = y} = lawXU q (y, u) := by
    rw [real_setOf]
    rw [sum_congr rfl fun ω _ => show (if ω.2.2 = u ∧ ω.1 = y then (q ω).toReal else 0) =
      if ω.1 = y then (if ω.2.2 = u then (q ω).toReal else 0) else 0 by
        by_cases h1 : ω.1 = y <;> by_cases h2 : ω.2.2 = u <;> simp [h1, h2]]
    rw [sum_fst_eq]
    simp [lawXU]
  have m4 : q.toMeasure.real {ω : T × S × Fin m | ω.1 = y ∧ ω.2.1 = x} = pXY q y x := by
    rw [real_setOf]
    rw [sum_congr rfl fun ω _ => show (if ω.1 = y ∧ ω.2.1 = x then (q ω).toReal else 0) =
      if ω.1 = y then (if ω.2.1 = x then (q ω).toReal else 0) else 0 by
        by_cases h1 : ω.1 = y <;> by_cases h2 : ω.2.1 = x <;> simp [h1, h2]]
    rw [sum_fst_eq, sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
    simp [pXY]
  rw [m1, m2, m3, m4] at h
  exact h

private lemma eq_mul_chan (q : PMF (T × S × Fin m))
    (hM : MarkovChain (fun a : T × S × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) (x₀ : S) (y : T) (x : S) (u : Fin m) :
    (q (y, x, u)).toReal = lawXU q (y, u) * (chan q x₀ y x).toReal := by
  by_cases h : pY q y = 0
  · have h1 : (q (y, x, u)).toReal ≤ 0 := h ▸
      (single_le_sum (f := fun u' => (q (y, x, u')).toReal) (fun _ _ => ENNReal.toReal_nonneg)
        (mem_univ u)).trans (single_le_sum (f := fun x' => pXY q y x')
          (fun x' _ => pXY_nonneg q y x') (mem_univ x))
    have h2 : lawXU q (y, u) ≤ 0 := h ▸ by
      rw [lawXU, pY, sum_comm]
      exact single_le_sum (f := fun u' => ∑ x', (q (y, x', u')).toReal)
        (fun _ _ => sum_nonneg fun _ _ => ENNReal.toReal_nonneg) (mem_univ u)
    rw [le_antisymm h1 ENNReal.toReal_nonneg, le_antisymm h2
      (sum_nonneg fun _ _ => ENNReal.toReal_nonneg), zero_mul]
  · have e := pXY_eq_mul q x₀ y x
    have := markov_factor q hM y x u
    rw [e] at this
    have hp : 0 < pY q y := lt_of_le_of_ne (pY_nonneg q y) (Ne.symm h)
    nlinarith [mul_comm (lawXU q (y, u)) (pY q y * (chan q x₀ y x).toReal)]

private lemma entropy_eq_sum' {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] [DecidableEq W] (q : PMF (T × S × Fin m))
    (f : T × S × Fin m → W) :
    H[f ; q.toMeasure] = ∑ w, Real.negMulLog (∑ ω, if f ω = w then (q ω).toReal else 0) := by
  rw [entropy_def]
  refine sum_congr rfl fun w _ => congrArg _ ?_
  rw [measureReal_map_singleton, sum_filter]
  refine sum_congr rfl fun ω _ => ?_
  split_ifs
  · rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  · rfl

private lemma condEntropy_eq_lawYU (q : PMF (T × S × Fin m)) :
    H[fun a : T × S × Fin m => a.2.1 | fun a => a.2.2 ; q.toMeasure] =
      ∑ z, Real.negMulLog (lawYU q z) - ∑ u, Real.negMulLog (∑ x, lawYU q (x, u)) := by
  classical
  rw [condEntropy_def, entropy_eq_sum', entropy_eq_sum']
  congr 1
  · refine sum_congr rfl fun ⟨a, b⟩ _ => congrArg _ ?_
    simp only [Fintype.sum_prod_type, lawYU]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_eq_single a (fun c _ hc => by simp [hc]) (by simp)]
    simp
  · refine sum_congr rfl fun u _ => congrArg _ ?_
    simp only [Fintype.sum_prod_type, lawYU]
    rw [sum_comm]
    simp

end Measure

section Decoder

variable {S T : Type*} [Fintype S] [Fintype T] {m : ℕ}

private noncomputable def pU (q : PMF (T × S × Fin m)) (u : Fin m) : ℝ :=
  ∑ x, lawYU q (x, u)

private noncomputable def wt (q : PMF (T × S × Fin m)) (l : ℝ) (u : Fin m) (x : S) : ℝ :=
  (1 - l) * (lawYU q (x, u) / pU q u) + l / Fintype.card S

private noncomputable def cost (q : PMF (T × S × Fin m)) (l : ℝ)
    (t : (Fin m × T) × S) : ℝ :=
  -Real.log (wt q l t.1.1 t.2)

private noncomputable def dset (q : PMF (T × S × Fin m)) (l c : ℝ) (n : ℕ)
    (u : Fin n → Fin m) : Finset (Fin n → S) := by
  classical
  exact univ.filter fun x => Real.exp (-(n * c)) ≤ ∏ i, wt q l (u i) (x i)

omit [Fintype S] in
private lemma lawYU_nonneg (q : PMF (T × S × Fin m)) (z : S × Fin m) : 0 ≤ lawYU q z :=
  sum_nonneg fun _ _ => ENNReal.toReal_nonneg

private lemma pU_nonneg (q : PMF (T × S × Fin m)) (u : Fin m) : 0 ≤ pU q u :=
  sum_nonneg fun x _ => lawYU_nonneg q (x, u)

private lemma wt_pos (q : PMF (T × S × Fin m)) [Nonempty S] {l : ℝ} (h0 : 0 < l)
    (h1 : l < 1) (u : Fin m) (x : S) : 0 < wt q l u x := by
  have hS : (0 : ℝ) < Fintype.card S := Nat.cast_pos.2 Fintype.card_pos
  have : 0 ≤ (1 - l) * (lawYU q (x, u) / pU q u) :=
    mul_nonneg (by linarith) (div_nonneg (lawYU_nonneg q _) (pU_nonneg q u))
  unfold wt
  positivity

private lemma sum_wt_le (q : PMF (T × S × Fin m)) [Nonempty S] {l : ℝ}
    (h1 : l ≤ 1) (u : Fin m) : ∑ x, wt q l u x ≤ 1 := by
  have hS : (0 : ℝ) < Fintype.card S := Nat.cast_pos.2 Fintype.card_pos
  have hV : ∑ x, lawYU q (x, u) / pU q u ≤ 1 := by
    rw [← sum_div]
    change pU q u / pU q u ≤ 1
    by_cases h : pU q u = 0
    · rw [h, div_zero]
      exact zero_le_one
    · rw [div_self h]
  simp only [wt, sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
  rw [mul_div_cancel₀ _ hS.ne']
  nlinarith

private lemma card_dset_le (q : PMF (T × S × Fin m)) [Nonempty S] {l : ℝ} (h0 : 0 < l)
    (h1 : l < 1) (c : ℝ) {n : ℕ} (u : Fin n → Fin m) :
    ((dset q l c n u).card : ℝ) ≤ Real.exp (n * c) := by
  classical
  have hw0 : ∀ i x, 0 ≤ wt q l i x := fun i x => (wt_pos q h0 h1 i x).le
  have hlow : (dset q l c n u).card * Real.exp (-(n * c)) ≤
      ∑ x ∈ dset q l c n u, ∏ i, wt q l (u i) (x i) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun x hx => (mem_filter.1 hx).2
  have hall : ∑ x ∈ dset q l c n u, ∏ i, wt q l (u i) (x i) ≤ 1 := by
    refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ =>
      prod_nonneg fun i _ => hw0 _ _).trans ?_
    rw [← Fintype.prod_sum (fun i s => wt q l (u i) s)]
    exact prod_le_one₀ (fun i _ => sum_nonneg fun s _ => hw0 _ _)
      fun i _ => sum_wt_le q h1.le (u i)
  have h := hlow.trans hall
  rw [← le_div_iff₀ (Real.exp_pos _), one_div, ← Real.exp_neg, neg_neg] at h
  exact h

end Decoder

section Mean

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {m : ℕ}

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma sum_law3_mul (q : PMF (T × S × Fin m)) (g : S → Fin m → ℝ) :
    ∑ t : (Fin m × T) × S, (q (t.1.2, t.2, t.1.1)).toReal * g t.2 t.1.1 =
      ∑ x, ∑ u, lawYU q (x, u) * g x u := by
  calc _ = ∑ u, ∑ y, ∑ x, (q (y, x, u)).toReal * g x u := by
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    _ = ∑ u, ∑ x, ∑ y, (q (y, x, u)).toReal * g x u := sum_congr rfl fun u _ => sum_comm
    _ = ∑ x, ∑ u, ∑ y, (q (y, x, u)).toReal * g x u := sum_comm
    _ = _ := by simp only [lawYU, sum_mul]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma cost_le (q : PMF (T × S × Fin m)) [Nonempty S] {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) (t : (Fin m × T) × S) :
    (q (t.1.2, t.2, t.1.1)).toReal * cost q l t ≤ (q (t.1.2, t.2, t.1.1)).toReal *
      (-Real.log (1 - l) - Real.log (lawYU q (t.2, t.1.1)) + Real.log (pU q t.1.1)) := by
  obtain ⟨⟨u, y⟩, x⟩ := t
  rcases (ENNReal.toReal_nonneg (a := q (y, x, u))).eq_or_lt with h | h
  · rw [← h, zero_mul, zero_mul]
  refine mul_le_mul_of_nonneg_left ?_ h.le
  have hL : (q (y, x, u)).toReal ≤ lawYU q (x, u) :=
    single_le_sum (f := fun y' => (q (y', x, u)).toReal) (fun _ _ => ENNReal.toReal_nonneg)
      (mem_univ y)
  have hP : lawYU q (x, u) ≤ pU q u :=
    single_le_sum (f := fun x' => lawYU q (x', u)) (fun x' _ => lawYU_nonneg q (x', u))
      (mem_univ x)
  have hL0 : 0 < lawYU q (x, u) := h.trans_le hL
  have hP0 : 0 < pU q u := hL0.trans_le hP
  have h1l : 0 < 1 - l := by linarith
  have hS : (0 : ℝ) < Fintype.card S := Nat.cast_pos.2 Fintype.card_pos
  have hle : (1 - l) * (lawYU q (x, u) / pU q u) ≤ wt q l u x := by
    unfold wt
    have : 0 ≤ l / Fintype.card S := by positivity
    linarith
  have hlog := Real.log_le_log (by positivity) hle
  rw [Real.log_mul h1l.ne' (div_pos hL0 hP0).ne', Real.log_div hL0.ne' hP0.ne'] at hlog
  simp only [cost]
  linarith

private lemma sum_cost_le (q : PMF (T × S × Fin m)) [Nonempty S] {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) :
    ∑ t : (Fin m × T) × S, (q (t.1.2, t.2, t.1.1)).toReal * cost q l t ≤
      H[fun a : T × S × Fin m => a.2.1 | fun a => a.2.2 ; q.toMeasure] - Real.log (1 - l) := by
  refine (sum_le_sum fun t _ => cost_le q hl0 hl1 t).trans_eq ?_
  have e1 := sum_law3_mul q fun (_ : S) (_ : Fin m) => (1 : ℝ)
  have e2 := sum_law3_mul q fun x u => Real.log (lawYU q (x, u))
  have e3 := sum_law3_mul q fun (_ : S) u => Real.log (pU q u)
  simp only [mul_one] at e1
  have hq0 : ∑ t : (Fin m × T) × S, (q (t.1.2, t.2, t.1.1)).toReal = 1 :=
    (Fintype.sum_equiv ⟨fun t : (Fin m × T) × S => (t.1.2, t.2, t.1.1),
      fun a => ((a.2.2, a.1), a.2.1), fun _ => rfl, fun _ => rfl⟩ _
      (fun a => (q a).toReal) fun _ => rfl).trans (sum_toReal_pmf_eq_one q)
  have hq1 : ∑ x, ∑ u, lawYU q (x, u) = 1 := e1.symm.trans hq0
  rw [condEntropy_eq_lawYU]
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← sum_mul]
  rw [e1, hq1, e2, e3]
  have r1 : ∑ x, ∑ u, lawYU q (x, u) * Real.log (lawYU q (x, u)) =
      -∑ z, Real.negMulLog (lawYU q z) := by
    rw [Fintype.sum_prod_type]
    simp only [Real.negMulLog, neg_mul, sum_neg_distrib, neg_neg]
  have r2 : ∑ x, ∑ u, lawYU q (x, u) * Real.log (pU q u) =
      -∑ u, Real.negMulLog (∑ x, lawYU q (x, u)) := by
    rw [sum_comm]
    simp only [Real.negMulLog, ← sum_mul, neg_mul, sum_neg_distrib, neg_neg]
    rfl
  rw [r1, r2]
  ring

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma mem_dset [DecidableEq S] [DecidableEq T] (q : PMF (T × S × Fin m)) [Nonempty S]
    {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {n : ℕ} (hn : 0 < n) {ε H γ : ℝ}
    (hε : ε * ∑ t, |cost q l t| ≤ γ)
    (hmean : ∑ t : (Fin m × T) × S, (q (t.1.2, t.2, t.1.1)).toReal * cost q l t ≤ H + γ)
    {u : Fin n → Fin m} {y : Fin n → T} {x : Fin n → S}
    (ht : (fun i => ((u i, y i), x i)) ∈
      strongTypicalSet (fun t : (Fin m × T) × S => (q (t.1.2, t.2, t.1.1)).toReal) n ε) :
    x ∈ dset q l (H + γ + γ) n u := by
  classical
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h := abs_avg_sub_le_of_mem_strongTypicalSet hn ht (cost q l)
  have h1 : ∑ i, cost q l ((u i, y i), x i) ≤ n * (H + γ + γ) := by
    have := (abs_le.1 h).2
    rw [div_sub' hn'.ne', div_le_iff₀ hn'] at this
    nlinarith
  have hprod : ∏ i, wt q l (u i) (x i) = Real.exp (-∑ i, cost q l ((u i, y i), x i)) := by
    simp only [cost, sum_neg_distrib, neg_neg, Real.exp_sum]
    exact prod_congr rfl fun i _ => (Real.exp_log (wt_pos q hl0 hl1 _ _)).symm
  simp only [dset, mem_filter, mem_univ, true_and]
  rw [hprod]
  exact Real.exp_le_exp.2 (by linarith)

end Mean

section Code

variable {S T : Type*} {m n K k : ℕ}

private noncomputable def coverIdx (Tc : Finset (Fin n → T × Fin m)) (C : Fin K → Fin n → Fin m)
    (l₀ : Fin K) (y : Fin n → T) : Fin K := by
  classical
  exact if h : ∃ l, (fun i => (y i, C l i)) ∈ Tc then h.choose else l₀

private noncomputable def binDec (D : (Fin n → Fin m) → Finset (Fin n → S))
    (C : Fin K → Fin n → Fin m) (β : (Fin n → S) → Fin k) (x₀ : Fin n → S)
    (b : Fin k × Fin K) : Fin n → S := by
  classical
  exact if h : ∃ x, β x = b.1 ∧ x ∈ D (C b.2) then h.choose else x₀

private noncomputable def randCode (Tc : Finset (Fin n → T × Fin m))
    (D : (Fin n → Fin m) → Finset (Fin n → S)) (C : Fin K → Fin n → Fin m)
    (β : (Fin n → S) → Fin k) (l₀ : Fin K) (x₀ : Fin n → S) : HelperCode S T n k K :=
  ⟨β, coverIdx Tc C l₀, binDec D C β x₀⟩

private lemma coverIdx_mem {Tc : Finset (Fin n → T × Fin m)} {C : Fin K → Fin n → Fin m}
    (l₀ : Fin K) {y : Fin n → T} (h : ∃ l, (fun i => (y i, C l i)) ∈ Tc) :
    (fun i => (y i, C (coverIdx Tc C l₀ y) i)) ∈ Tc := by
  simp only [coverIdx, h, dite_true]
  exact h.choose_spec

private lemma err_le [DecidableEq S] (Tc : Finset (Fin n → T × Fin m))
    (D : (Fin n → Fin m) → Finset (Fin n → S)) (C : Fin K → Fin n → Fin m)
    (β : (Fin n → S) → Fin k) (l₀ : Fin K) (x₀ : Fin n → S) (x : Fin n → S) (y : Fin n → T)
    [Decidable (∀ l, (fun i => (y i, C l i)) ∉ Tc)]
    [Decidable ((∃ l, (fun i => (y i, C l i)) ∈ Tc) ∧ x ∉ D (C (coverIdx Tc C l₀ y)))]
    [Decidable (∃ x', x' ≠ x ∧ β x' = β x ∧ x' ∈ D (C (coverIdx Tc C l₀ y)))] :
    (if (randCode Tc D C β l₀ x₀).dec ((randCode Tc D C β l₀ x₀).enc x,
        (randCode Tc D C β l₀ x₀).help y) = x then (0 : ℝ) else 1) ≤
      (if ∀ l, (fun i => (y i, C l i)) ∉ Tc then 1 else 0) +
      (if (∃ l, (fun i => (y i, C l i)) ∈ Tc) ∧ x ∉ D (C (coverIdx Tc C l₀ y)) then 1 else 0) +
      (if ∃ x', x' ≠ x ∧ β x' = β x ∧ x' ∈ D (C (coverIdx Tc C l₀ y)) then 1 else 0) := by
  classical
  change (if binDec D C β x₀ (β x, coverIdx Tc C l₀ y) = x then (0 : ℝ) else 1) ≤ _
  split_ifs <;> norm_num
  rename_i h0 h1 h2 h3
  have h1' : ∃ l, (fun i => (y i, C l i)) ∈ Tc := by simpa using h1
  have hx : x ∈ D (C (coverIdx Tc C l₀ y)) := by
    by_contra h
    exact h2 ⟨h1', h⟩
  have he : ∃ x', β x' = β x ∧ x' ∈ D (C (coverIdx Tc C l₀ y)) := ⟨x, rfl, hx⟩
  have hs := he.choose_spec
  refine h3 ⟨he.choose, fun h => h0 ?_, hs.1, hs.2⟩
  simp only [binDec, he, dite_true]
  exact h

private lemma sum_bins_le' {ι : Type*} [Fintype ι] [DecidableEq ι] (hk : 0 < k) (L : ι)
    (A : ι → Prop) [DecidablePred A] :
    ∑ β : ι → Fin k, (∏ _l : ι, (k : ℝ)⁻¹) *
        (if ∃ l, l ≠ L ∧ β l = β L ∧ A l then 1 else 0) ≤
      (k : ℝ)⁻¹ * ∑ l, if A l then 1 else 0 := by
  classical
  have hw0 : (0 : ℝ) ≤ ∏ _l : ι, (k : ℝ)⁻¹ := prod_nonneg fun _ _ => by positivity
  have hind : ∀ β : ι → Fin k, (if ∃ l, l ≠ L ∧ β l = β L ∧ A l then (1 : ℝ) else 0) ≤
      ∑ l, (if l ≠ L ∧ A l then (1 : ℝ) else 0) * (if β l = β L then 1 else 0) := by
    intro β
    split_ifs with h
    · obtain ⟨l, hl, hb, ha⟩ := h
      calc (1 : ℝ) = (if l ≠ L ∧ A l then (1 : ℝ) else 0) * (if β l = β L then 1 else 0) := by
            simp [hl, ha, hb]
        _ ≤ _ := single_le_sum (f := fun l => (if l ≠ L ∧ A l then (1 : ℝ) else 0) *
            (if β l = β L then 1 else 0)) (fun _ _ => by split_ifs <;> norm_num) (mem_univ l)
    · exact sum_nonneg fun _ _ => by split_ifs <;> norm_num
  calc ∑ β : ι → Fin k, (∏ _l : ι, (k : ℝ)⁻¹) *
        (if ∃ l, l ≠ L ∧ β l = β L ∧ A l then 1 else 0)
      ≤ ∑ β : ι → Fin k, (∏ _l : ι, (k : ℝ)⁻¹) *
        ∑ l, (if l ≠ L ∧ A l then (1 : ℝ) else 0) * (if β l = β L then 1 else 0) :=
        sum_le_sum fun β _ => mul_le_mul_of_nonneg_left (hind β) hw0
    _ = ∑ l, (if l ≠ L ∧ A l then (1 : ℝ) else 0) *
        ∑ β : ι → Fin k, (∏ _l : ι, (k : ℝ)⁻¹) * (if β l = β L then 1 else 0) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun l _ => sum_congr rfl fun β _ => by ring
    _ ≤ ∑ l, (if A l then (1 : ℝ) else 0) * (k : ℝ)⁻¹ := by
        refine sum_le_sum fun l _ => ?_
        rw [sum_uniform_mul_ite_eq hk l L]
        by_cases hl : l = L
        · simp only [hl, ne_eq, not_true_eq_false, false_and, ite_false, zero_mul]
          split_ifs <;> positivity
        · simp only [ne_eq, hl, not_false_eq_true, true_and, ite_false]
          split_ifs <;> simp
    _ = _ := by rw [mul_sum]; exact sum_congr rfl fun l _ => mul_comm _ _

end Code

section Average

variable {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T] {m n K k : ℕ}

omit [Fintype T] in
private lemma avg_bins (Tc : Finset (Fin n → T × Fin m))
    (D : (Fin n → Fin m) → Finset (Fin n → S)) {e : ℝ} (hD : ∀ u, ((D u).card : ℝ) ≤ e)
    (hk : 0 < k) (C : Fin K → Fin n → Fin m) (l₀ : Fin K) (x₀ x : Fin n → S) (y : Fin n → T) :
    ∑ β : (Fin n → S) → Fin k, (∏ _l : Fin n → S, (k : ℝ)⁻¹) *
        (if (randCode Tc D C β l₀ x₀).dec ((randCode Tc D C β l₀ x₀).enc x,
          (randCode Tc D C β l₀ x₀).help y) = x then (0 : ℝ) else 1) ≤
      (if ∀ l, (fun i => (y i, C l i)) ∉ Tc then 1 else 0) +
      (if (∃ l, (fun i => (y i, C l i)) ∈ Tc) ∧ x ∉ D (C (coverIdx Tc C l₀ y)) then 1 else 0) +
      (k : ℝ)⁻¹ * e := by
  classical
  set F1 : ℝ := if ∀ l, (fun i => (y i, C l i)) ∉ Tc then 1 else 0
  set F2 : ℝ := if (∃ l, (fun i => (y i, C l i)) ∈ Tc) ∧ x ∉ D (C (coverIdx Tc C l₀ y)) then 1
    else 0
  set u := C (coverIdx Tc C l₀ y)
  have hw0 : (0 : ℝ) ≤ ∏ _l : Fin n → S, (k : ℝ)⁻¹ := prod_nonneg fun _ _ => by positivity
  have hbins := sum_bins_le' hk x (fun l => l ∈ D u)
  have hcard : ∑ l : Fin n → S, (if l ∈ D u then (1 : ℝ) else 0) ≤ e := by
    rw [sum_boole, filter_mem_eq_inter, univ_inter]
    exact hD u
  have h1 := sum_uniform (ι := Fin n → S) hk
  calc _ ≤ ∑ β : (Fin n → S) → Fin k, (∏ _l : Fin n → S, (k : ℝ)⁻¹) * (F1 + F2 +
          (if ∃ x', x' ≠ x ∧ β x' = β x ∧ x' ∈ D u then 1 else 0)) :=
        sum_le_sum fun β _ => mul_le_mul_of_nonneg_left (err_le Tc D C β l₀ x₀ x y) hw0
    _ = (F1 + F2) * ∑ β : (Fin n → S) → Fin k, (∏ _l : Fin n → S, (k : ℝ)⁻¹) +
        ∑ β : (Fin n → S) → Fin k, (∏ _l : Fin n → S, (k : ℝ)⁻¹) *
          (if ∃ x', x' ≠ x ∧ β x' = β x ∧ x' ∈ D u then 1 else 0) := by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun β _ => by ring
    _ ≤ _ := by
        rw [h1, mul_one]
        have := mul_le_mul_of_nonneg_left hcard (inv_nonneg.2 (Nat.cast_nonneg k))
        linarith

omit [Fintype T] in
private lemma avg_point (Tc : Finset (Fin n → T × Fin m))
    (D : (Fin n → Fin m) → Finset (Fin n → S)) {e : ℝ} (hD : ∀ u, ((D u).card : ℝ) ≤ e)
    (hk : 0 < k) (qU : PMF (Fin m)) (l₀ : Fin K) (x₀ x : Fin n → S) (y : Fin n → T) :
    ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb qU (C l)) *
      ∑ β : (Fin n → S) → Fin k, (∏ _l : Fin n → S, (k : ℝ)⁻¹) *
        (if (randCode Tc D C β l₀ x₀).dec ((randCode Tc D C β l₀ x₀).enc x,
          (randCode Tc D C β l₀ x₀).help y) = x then (0 : ℝ) else 1) ≤
      (1 - ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tc),
          iidProb qU u) ^ K +
        ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb qU (C l)) *
          (if (∃ l, (fun i => (y i, C l i)) ∈ Tc) ∧ x ∉ D (C (coverIdx Tc C l₀ y)) then 1
            else 0) +
        (k : ℝ)⁻¹ * e := by
  classical
  set w : (Fin K → Fin n → Fin m) → ℝ := fun C => ∏ l, iidProb qU (C l) with hw
  have hw0 : ∀ C, 0 ≤ w C := fun C => prod_nonneg fun _ _ => iidProb_nonneg _ _
  have hw1 : ∑ C, w C = 1 := sum_prod _ fun _ => sum_iidProb qU n
  have e1 : ∑ C, w C * (if ∀ l, (fun i => (y i, C l i)) ∉ Tc then 1 else 0) =
      (1 - ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tc),
        iidProb qU u) ^ K := by
    rw [← sum_codebook_not_mem]
    exact sum_congr rfl fun C _ => by simp [w]
  calc _ ≤ ∑ C, w C * ((if ∀ l, (fun i => (y i, C l i)) ∉ Tc then 1 else 0) +
          (if (∃ l, (fun i => (y i, C l i)) ∈ Tc) ∧ x ∉ D (C (coverIdx Tc C l₀ y)) then 1
            else 0) + (k : ℝ)⁻¹ * e) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left
          (avg_bins Tc D hD hk C l₀ x₀ x y) (hw0 C)
    _ = _ := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hw1, e1, one_mul]
        rfl

private lemma sum_mul_sum_sum_comm {α X Y : Type*} [Fintype α] [Fintype X] [Fintype Y]
    (w : α → ℝ) (P : X → Y → ℝ) (f : α → X → Y → ℝ) :
    ∑ a, w a * ∑ x, ∑ y, P x y * f a x y = ∑ x, ∑ y, P x y * ∑ a, w a * f a x y := by
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_congr rfl fun a _ => by ring

private lemma exists_code_le (q : PMF (T × S × Fin m)) (s₀ : S) (Tc : Finset (Fin n → T × Fin m))
    (D : (Fin n → Fin m) → Finset (Fin n → S)) {e : ℝ} (hD : ∀ u, ((D u).card : ℝ) ≤ e)
    (hk : 0 < k) (l₀ : Fin K) (x₀ : Fin n → S) {a₁ a₂ : ℝ}
    (hA : ∑ y : Fin n → T, iidProb (q.map Prod.fst) y *
      (1 - ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tc),
        iidProb (q.map fun a => a.2.2) u) ^ K ≤ a₁)
    (hB : ∑ y : Fin n → T, iidProb (q.map Prod.fst) y *
      ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb (q.map fun a => a.2.2) (C l)) *
        ∑ x : Fin n → S, (∏ i, (chan q s₀ (y i) (x i)).toReal) *
          (if (∃ l, (fun i => (y i, C l i)) ∈ Tc) ∧ x ∉ D (C (coverIdx Tc C l₀ y)) then 1
            else 0) ≤ a₂) :
    ∃ c : HelperCode S T n k K, c.errorProb (q.map fun a => (a.2.1, a.1)) ≤
      a₁ + a₂ + (k : ℝ)⁻¹ * e := by
  set p := q.map fun a => (a.2.1, a.1)
  set qU := q.map fun a => a.2.2
  set pYm := q.map Prod.fst
  set W : (Fin n → S) → (Fin n → T) → ℝ := fun x y => ∏ i, (chan q s₀ (y i) (x i)).toReal
  set err : (Fin K → Fin n → Fin m) → ((Fin n → S) → Fin k) → (Fin n → S) → (Fin n → T) → ℝ :=
    fun C β x y => if (randCode Tc D C β l₀ x₀).dec ((randCode Tc D C β l₀ x₀).enc x,
      (randCode Tc D C β l₀ x₀).help y) = x then (0 : ℝ) else 1
  set F2 : (Fin K → Fin n → Fin m) → (Fin n → S) → (Fin n → T) → ℝ := fun C x y =>
    if (∃ l, (fun i => (y i, C l i)) ∈ Tc) ∧ x ∉ D (C (coverIdx Tc C l₀ y)) then 1 else 0
  set A : (Fin n → T) → ℝ := fun y =>
    (1 - ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tc),
      iidProb qU u) ^ K
  set wC : (Fin K → Fin n → Fin m) → ℝ := fun C => ∏ l, iidProb qU (C l)
  have hW1 : ∀ y, ∑ x, W x y = 1 := fun y => by
    simp only [W]
    rw [← Fintype.prod_sum (fun i s => (chan q s₀ (y i) s).toReal)]
    exact prod_eq_one fun i _ => sum_toReal_pmf_eq_one _
  have hW0 : ∀ x y, 0 ≤ W x y := fun x y => prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hP : ∀ x y, iidProb p (fun i => (x i, y i)) = iidProb pYm y * W x y :=
    fun x y => iidProb_source_eq q s₀ x y
  have herr : ∀ C β, (randCode Tc D C β l₀ x₀).errorProb p =
      ∑ x, ∑ y, iidProb p (fun i => (x i, y i)) * err C β x y := fun C β => by
    rw [HelperCode.errorProb, sum_arrow_prod]
  have hwC0 : ∀ C, 0 ≤ wC C := fun C => prod_nonneg fun _ _ => iidProb_nonneg _ _
  have hwC1 : ∑ C, wC C = 1 := sum_prod _ fun _ => sum_iidProb qU n
  have hwβ0 : ∀ β : (Fin n → S) → Fin k, (0 : ℝ) ≤ ∏ _l : Fin n → S, (k : ℝ)⁻¹ :=
    fun _ => prod_nonneg fun _ _ => by positivity
  have hwβ1 := sum_uniform (ι := Fin n → S) hk
  have hpt : ∀ x y, ∑ C, wC C * ∑ β : (Fin n → S) → Fin k, (∏ _l : Fin n → S, (k : ℝ)⁻¹) *
      err C β x y ≤ A y + ∑ C, wC C * F2 C x y + (k : ℝ)⁻¹ * e :=
    fun x y => avg_point Tc D hD hk qU l₀ x₀ x y
  have hy : ∀ y, ∑ x, iidProb p (fun i => (x i, y i)) *
      (A y + ∑ C, wC C * F2 C x y + (k : ℝ)⁻¹ * e) = iidProb pYm y * A y +
        iidProb pYm y * ∑ C, wC C * ∑ x, W x y * F2 C x y +
        (k : ℝ)⁻¹ * e * iidProb pYm y := fun y => by
    simp only [hP]
    have e1 : ∀ x, iidProb pYm y * W x y * (A y + ∑ C, wC C * F2 C x y + (k : ℝ)⁻¹ * e) =
        iidProb pYm y * A y * W x y + iidProb pYm y * (W x y * ∑ C, wC C * F2 C x y) +
          (k : ℝ)⁻¹ * e * iidProb pYm y * W x y := fun x => by ring
    rw [sum_congr rfl fun x _ => e1 x, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
      ← mul_sum, hW1, mul_one, mul_one]
    congr 2
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun C _ => sum_congr rfl fun x _ => by ring
  have htot : ∑ C, wC C * ∑ β : (Fin n → S) → Fin k, (∏ _l : Fin n → S, (k : ℝ)⁻¹) *
      (randCode Tc D C β l₀ x₀).errorProb p ≤ a₁ + a₂ + (k : ℝ)⁻¹ * e := by
    simp only [herr]
    rw [sum_congr rfl fun C _ => by rw [sum_mul_sum_sum_comm], sum_mul_sum_sum_comm]
    calc _ ≤ ∑ x, ∑ y, iidProb p (fun i => (x i, y i)) *
          (A y + ∑ C, wC C * F2 C x y + (k : ℝ)⁻¹ * e) :=
          sum_le_sum fun x _ => sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hpt x y) (iidProb_nonneg _ _)
      _ = ∑ y, iidProb pYm y * A y + ∑ y, iidProb pYm y * ∑ C, wC C * ∑ x, W x y * F2 C x y +
          (k : ℝ)⁻¹ * e * ∑ y, iidProb pYm y := by
          rw [sum_comm]
          rw [sum_congr rfl fun y _ => hy y, sum_add_distrib, sum_add_distrib, ← mul_sum]
      _ ≤ _ := by
          rw [sum_iidProb, mul_one]
          linarith
  obtain ⟨C, hC'⟩ := exists_le_of_sum_mul_le hwC0 hwC1 htot
  obtain ⟨β, hβ⟩ := exists_le_of_sum_mul_le hwβ0 hwβ1 hC'
  exact ⟨randCode Tc D C β l₀ x₀, hβ⟩

end Average

section Bounds

variable {S T : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [Fintype T] [DecidableEq T] [MeasurableSpace T]
  [MeasurableSingletonClass T] {m n : ℕ}

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq T]
  [MeasurableSpace T] [MeasurableSingletonClass T] in
private lemma toReal_map_U (q : PMF (T × S × Fin m)) (u : Fin m) :
    ((q.map fun a => a.2.2) u).toReal = ∑ y, lawXU q (y, u) := by
  rw [toReal_map_apply, sum_filter]
  simp [Fintype.sum_prod_type, lawXU]

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype T]
  [DecidableEq T] [MeasurableSpace T] [MeasurableSingletonClass T] in
private lemma toReal_map_fst' [Finite T] (q : PMF (T × S × Fin m)) (y : T) :
    ((q.map Prod.fst) y).toReal = ∑ u, lawXU q (y, u) := by
  rw [toReal_map_fst, pY]
  simp only [lawXU]
  exact sum_comm

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma cover_part (q : PMF (T × S × Fin m)) (K : ℕ) (hn : 0 < n)
    (Tc : Finset (Fin n → T × Fin m)) {ε a : ℝ} (hε : 0 < ε) (ha1 : a ≤ 1)
    (hcov : ∀ y : Fin n → T, (∀ s, |(typeCount y s : ℝ) / n - ∑ u, lawXU q (s, u)| ≤ ε) →
      (∀ s, ∑ u, lawXU q (s, u) = 0 → typeCount y s = 0) →
      a ≤ ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tc),
        iidProb (q.map fun a => a.2.2) u) :
    ∑ y : Fin n → T, iidProb (q.map Prod.fst) y *
      (1 - ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tc),
        iidProb (q.map fun a => a.2.2) u) ^ K ≤
      Real.exp (-(K * a)) + Fintype.card T / (4 * n * ε ^ 2) := by
  set pX := q.map Prod.fst
  set qU := q.map fun a => a.2.2
  set σ : (Fin n → T) → ℝ := fun x =>
    ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (x i, u i)) ∈ Tc), iidProb qU u
  set Ty := strongTypicalSet (fun s => (pX s).toReal) n ε
  have hpX : ∀ s, (pX s).toReal = ∑ u, lawXU q (s, u) := toReal_map_fst' q
  have hσ0 : ∀ x, 0 ≤ σ x := fun x => sum_nonneg fun u _ => iidProb_nonneg _ _
  have hσ1 : ∀ x, σ x ≤ 1 := fun x => (sum_le_sum_of_subset_of_nonneg (subset_univ _)
    fun u _ _ => iidProb_nonneg _ _).trans_eq (sum_iidProb qU n)
  have hbound : ∀ x, iidProb pX x * (1 - σ x) ^ K ≤
      iidProb pX x * Real.exp (-(K * a)) + (if x ∈ Ty then 0 else iidProb pX x) := by
    intro x
    have hp0 := iidProb_nonneg pX x
    have hpow1 : (1 - σ x) ^ K ≤ 1 := pow_le_one₀ (by linarith [hσ1 x]) (by linarith [hσ0 x])
    by_cases hT : x ∈ Ty
    · simp only [hT, ↓reduceIte, add_zero]
      by_cases hx0 : iidProb pX x = 0
      · rw [hx0, zero_mul, zero_mul]
      refine mul_le_mul_of_nonneg_left ?_ hp0
      have hsupp : ∀ s, ∑ u, lawXU q (s, u) = 0 → typeCount x s = 0 := fun s hs => by
        by_contra hc
        obtain ⟨i, hi⟩ : ∃ i, x i = s := by
          by_contra hne
          push Not at hne
          exact hc (by simp [typeCount, hne])
        exact hx0 (prod_eq_zero (mem_univ i) (by rw [hi, hpX, hs]))
      have ha := hcov x (fun s => by rw [← hpX]; exact mem_strongTypicalSet.1 hT s) hsupp
      have h1 := one_sub_mul_pow_le ha1 zero_le_one le_rfl K
      rw [mul_one, sub_self, zero_add] at h1
      exact (pow_le_pow_left₀ (by linarith [hσ1 x]) (by linarith) K).trans h1
    · simp only [hT, ↓reduceIte]
      nlinarith [mul_le_mul_of_nonneg_left hpow1 hp0, Real.exp_pos (-(K * a))]
  have hnot : ∑ x : Fin n → T, (if x ∈ Ty then 0 else iidProb pX x) ≤
      Fintype.card T / (4 * n * ε ^ 2) := by
    refine le_trans (le_of_eq ?_) (sum_iidProb_not_mem_strongTypicalSet_le pX hε hn)
    rw [sum_filter]
    exact sum_congr rfl fun x _ => by split_ifs <;> rfl
  calc _ ≤ ∑ x, (iidProb pX x * Real.exp (-(K * a)) + (if x ∈ Ty then 0 else iidProb pX x)) :=
        sum_le_sum fun x _ => hbound x
    _ ≤ _ := by
        rw [sum_add_distrib, ← sum_mul, sum_iidProb, one_mul]
        linarith

private lemma bin_part (q : PMF (T × S × Fin m))
    (hM : MarkovChain (fun a : T × S × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) (s₀ : S) (hn : 0 < n) {δ η : ℝ} (hη : 0 < η) {K : ℕ} (l₀ : Fin K)
    (D : (Fin n → Fin m) → Finset (Fin n → S))
    (hmem : ∀ (u : Fin n → Fin m) (y : Fin n → T) (x : Fin n → S),
      (fun i => ((u i, y i), x i)) ∈ strongTypicalSet
        (fun t : (Fin m × T) × S => (q (t.1.2, t.2, t.1.1)).toReal) n (δ + η) → x ∈ D u) :
    ∑ y : Fin n → T, iidProb (q.map Prod.fst) y *
      ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb (q.map fun a => a.2.2) (C l)) *
        ∑ x : Fin n → S, (∏ i, (chan q s₀ (y i) (x i)).toReal) *
          (if (∃ l, (fun i => (y i, C l i)) ∈ strongTypicalSet (lawXU q) n δ) ∧
            x ∉ D (C (coverIdx (strongTypicalSet (lawXU q) n δ) C l₀ y)) then 1 else 0) ≤
      Fintype.card (Fin m × T) * Fintype.card S / (4 * n * η ^ 2) := by
  set qU := q.map fun a => a.2.2
  set Tc := strongTypicalSet (lawXU q) n δ
  set Bm : ℝ := Fintype.card (Fin m × T) * Fintype.card S / (4 * n * η ^ 2)
  have hBm : 0 ≤ Bm := by positivity
  have hwC0 : ∀ C : Fin K → Fin n → Fin m, 0 ≤ ∏ l, iidProb qU (C l) :=
    fun C => prod_nonneg fun _ _ => iidProb_nonneg _ _
  have hwC1 : ∑ C : Fin K → Fin n → Fin m, ∏ l, iidProb qU (C l) = 1 :=
    sum_prod _ fun _ => sum_iidProb qU n
  have hlaw : (fun t : (Fin m × T) × S => (fun z : Fin m × T => lawXU q (z.2, z.1)) t.1 *
      (chan q s₀ t.1.2 t.2).toReal) = fun t => (q (t.1.2, t.2, t.1.1)).toReal :=
    funext fun t => (eq_mul_chan q hM s₀ t.1.2 t.2 t.1.1).symm
  have hinner : ∀ y (C : Fin K → Fin n → Fin m), ∑ x : Fin n → S,
      (∏ i, (chan q s₀ (y i) (x i)).toReal) *
        (if (∃ l, (fun i => (y i, C l i)) ∈ Tc) ∧ x ∉ D (C (coverIdx Tc C l₀ y)) then 1
          else 0) ≤ Bm := by
    intro y C
    by_cases h : ∃ l, (fun i => (y i, C l i)) ∈ Tc
    · set u := C (coverIdx Tc C l₀ y)
      have hux := mem_strongTypicalSet_swap.1 (coverIdx_mem l₀ h)
      have hm := markov_lemma (chan q s₀) (fun z : Fin m × T => lawXU q (z.2, z.1)) hη hn hux
      rw [hlaw] at hm
      refine le_trans ?_ hm
      rw [sum_filter]
      refine sum_le_sum fun x _ => ?_
      simp only [h, true_and]
      by_cases hx : x ∈ D u
      · simp only [hx, not_true_eq_false, ite_false, mul_zero]
        split_ifs <;> positivity
      · have : (fun i => ((u i, y i), x i)) ∉ strongTypicalSet
            (fun t : (Fin m × T) × S => (q (t.1.2, t.2, t.1.1)).toReal) n (δ + η) :=
          fun ht => hx (hmem u y x ht)
        simp only [hx, not_false_eq_true, ite_true, mul_one]
        exact le_of_eq (ite_eq_left_of_eq_true _ _ (eq_true this)).symm
    · simp only [h, false_and, ↓reduceIte, mul_zero, sum_const_zero]
      exact hBm
  calc _ ≤ ∑ y : Fin n → T, iidProb (q.map Prod.fst) y *
        ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb qU (C l)) * Bm :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (sum_le_sum fun C _ =>
          mul_le_mul_of_nonneg_left (hinner y C) (hwC0 C)) (iidProb_nonneg _ _)
    _ = Bm := by
        rw [← sum_mul (f := fun C : Fin K → Fin n → Fin m => ∏ l, iidProb qU (C l)), hwC1,
          one_mul, ← sum_mul, sum_iidProb, one_mul]

end Bounds

private lemma half_le_floor {z : ℝ} (hz : 1 ≤ z) : z / 2 ≤ ⌊z⌋₊ := by
  have hlt := Nat.lt_floor_add_one z
  have hge : (1 : ℝ) ≤ ⌊z⌋₊ := Nat.one_le_cast.2 (Nat.le_floor (by simpa using hz))
  linarith

section Main

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {m : ℕ}

theorem achievable_of_lt [DecidableEq S] (q : PMF (T × S × Fin m))
    (hM : MarkovChain (fun a : T × S × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) {R₁ R₂ : ℝ}
    (h₁ : H[fun a : T × S × Fin m => a.2.1 | fun a => a.2.2 ; q.toMeasure] < R₁)
    (h₂ : I[fun a : T × S × Fin m => a.1 : fun a => a.2.2 ; q.toMeasure] < R₂) :
    Achievable (q.map fun a => (a.2.1, a.1)) R₁ R₂ := by
  classical
  obtain ⟨⟨t₀, s₀, u₀⟩, -⟩ := q.support_nonempty
  have : Nonempty S := ⟨s₀⟩
  set Hc := H[fun a : T × S × Fin m => a.2.1 | fun a => a.2.2 ; q.toMeasure]
  have hJ : I[fun a : T × S × Fin m => a.1 : fun a => a.2.2 ; q.toMeasure] =
      jointInfo (lawXU q) := mutualInfo_eq_jointInfo q
  set J := jointInfo (lawXU q)
  have hJ0 : 0 ≤ J := jointInfo_lawXU_nonneg q
  have hHc0 : 0 ≤ Hc := condEntropy_nonneg _ (measurable_of_finite _) (measurable_of_finite _)
  intro ε hε
  set γ := (R₁ - Hc) / 4 with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  set l := 1 - Real.exp (-γ) with hldef
  have hl0 : 0 < l := by
    have := Real.exp_lt_one_iff.2 (show -γ < 0 by linarith)
    linarith
  have hl1 : l < 1 := by
    have := Real.exp_pos (-γ)
    linarith
  have hlog : Real.log (1 - l) = -γ := by rw [hldef, sub_sub_cancel, Real.log_exp]
  set F := ∑ t, |cost q l t|
  have hF0 : 0 ≤ F := sum_nonneg fun t _ => abs_nonneg _
  have hmean : ∑ t : (Fin m × T) × S, (q (t.1.2, t.2, t.1.1)).toReal * cost q l t ≤ Hc + γ := by
    have := sum_cost_le q hl0 hl1
    rw [hlog] at this
    linarith
  set δ₂ := (R₂ - J) / 4 with hδ₂def
  have hδ₂ : 0 < δ₂ := by rw [hδ₂def]; linarith
  set δ := min δ₂ (γ / (2 * (F + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min hδ₂ (by positivity)
  have hδδ₂ : δ ≤ δ₂ := min_le_left _ _
  have hδF : (δ + δ) * F ≤ γ := by
    have h1 : δ ≤ γ / (2 * (F + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  obtain ⟨εc, hεc, hcov⟩ := strong_covering (lawXU q) (fun _ => sum_nonneg fun _ _ =>
    ENNReal.toReal_nonneg) (q.map fun a => a.2.2) (toReal_map_U q) hδ0
  have hR₁0 : 0 ≤ R₁ := by linarith
  have hR₂0 : 0 ≤ R₂ := by linarith
  have hexp1 : ∀ n : ℕ, ∀ r : ℝ, 0 ≤ r → 1 ≤ Real.exp (n * r) := fun n r hr =>
    Real.one_le_exp (mul_nonneg (Nat.cast_nonneg n) hr)
  set K₂ : ℕ → ℕ := fun n => ⌊Real.exp (n * R₂)⌋₊
  set kk : ℕ → ℕ := fun n => ⌊Real.exp (n * R₁)⌋₊
  set a : ℕ → ℝ := fun n => Real.exp (-(n * (J + δ)))
  have hK₂ : ∀ n, 0 < K₂ n := fun n => Nat.floor_pos.2 (hexp1 n R₂ hR₂0)
  have hkk : ∀ n, 0 < kk n := fun n => Nat.floor_pos.2 (hexp1 n R₁ hR₁0)
  have ha1 : ∀ n, a n ≤ 1 := fun n => Real.exp_le_one_iff.2 (by
    have : 0 ≤ (n : ℝ) * (J + δ) := mul_nonneg (Nat.cast_nonneg n) (by linarith)
    linarith)
  have t1 : Tendsto (fun n => Real.exp (-(K₂ n * a n))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_exp_nat_mul (show -(δ₂ / 2) < 0 by linarith)) (fun n => (Real.exp_pos _).le)
      fun n => Real.exp_le_exp.2 ?_
    have h1 := half_le_floor (hexp1 n R₂ hR₂0)
    have h2 : Real.exp (n * R₂) * a n = Real.exp (n * (R₂ - J - δ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : (n : ℝ) * δ₂ ≤ Real.exp (n * (R₂ - J - δ)) := by
      have := Real.add_one_le_exp (n * (R₂ - J - δ))
      have : (n : ℝ) * δ₂ ≤ n * (R₂ - J - δ) :=
        mul_le_mul_of_nonneg_left (by rw [hδ₂def] at hδδ₂ ⊢; linarith) (Nat.cast_nonneg n)
      linarith
    have h4 : (n : ℝ) * δ₂ / 2 ≤ K₂ n * a n := by
      calc (n : ℝ) * δ₂ / 2 ≤ Real.exp (n * R₂) / 2 * a n := by
            rw [div_mul_eq_mul_div, h2]
            linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    linarith
  have t2 : ∀ c e : ℝ, Tendsto (fun n : ℕ => c / (4 * n * e)) atTop (𝓝 0) := fun c e => by
    refine (tendsto_const_div_atTop_nhds_zero_nat (c / (4 * e))).congr fun n => ?_
    rw [div_div]
    ring
  have t4 : Tendsto (fun n => (kk n : ℝ)⁻¹ * Real.exp (n * (Hc + γ + γ))) atTop (𝓝 0) := by
    have hc := (tendsto_exp_nat_mul (show -(γ + γ) < 0 by linarith)).const_mul 2
    rw [mul_zero] at hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun n => by positivity) fun n => ?_
    have hk2 := half_le_floor (hexp1 n R₁ hR₁0)
    have hkpos : (0 : ℝ) < kk n := Nat.cast_pos.2 (hkk n)
    have hinv : (kk n : ℝ)⁻¹ ≤ 2 * Real.exp (-(n * R₁)) := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hkpos]
      have := Real.exp_pos (n * R₁)
      have h := mul_le_mul_of_nonneg_left hk2
        (by positivity : (0 : ℝ) ≤ 2 * (Real.exp (n * R₁))⁻¹)
      rw [show 2 * (Real.exp (n * R₁))⁻¹ * (Real.exp (n * R₁) / 2) = 1 by field_simp] at h
      linarith
    calc (kk n : ℝ)⁻¹ * Real.exp (n * (Hc + γ + γ))
        ≤ 2 * Real.exp (-(n * R₁)) * Real.exp (n * (Hc + γ + γ)) :=
          mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
      _ = 2 * Real.exp (n * -(γ + γ)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          rw [hγdef]
          ring
  have hB := ((t1.add (t2 (Fintype.card T) (εc ^ 2))).add
    (t2 (Fintype.card (Fin m × T) * Fintype.card S) (δ ^ 2))).add t4
  simp only [add_zero] at hB
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hB.eventually (gt_mem_nhds hε)).and
    (hcov.and (eventually_gt_atTop 0)))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hBn, hcovn, hn0⟩ := hN n hn
  have hmem : ∀ (u : Fin n → Fin m) (y : Fin n → T) (x : Fin n → S),
      (fun i => ((u i, y i), x i)) ∈ strongTypicalSet
        (fun t : (Fin m × T) × S => (q (t.1.2, t.2, t.1.1)).toReal) n (δ + δ) →
        x ∈ dset q l (Hc + γ + γ) n u :=
    fun u y x ht => mem_dset q hl0 hl1 hn0 hδF hmean ht
  have hA := cover_part q (K₂ n) hn0 (strongTypicalSet (lawXU q) n δ) hεc (ha1 n) hcovn
  have hBp := bin_part q hM s₀ hn0 hδ0 (⟨0, hK₂ n⟩ : Fin (K₂ n)) (dset q l (Hc + γ + γ) n) hmem
  obtain ⟨c, hc⟩ := exists_code_le q s₀ (strongTypicalSet (lawXU q) n δ)
    (dset q l (Hc + γ + γ) n) (card_dset_le q hl0 hl1 _) (hkk n) ⟨0, hK₂ n⟩ (fun _ => s₀) hA hBp
  exact ⟨kk n, K₂ n, Nat.floor_le (Real.exp_pos _).le, Nat.floor_le (Real.exp_pos _).le, c,
    hc.trans (by linarith)⟩

end Main

end Helper

end Meat
