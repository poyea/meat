import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Meat.Shannon.Average
import Meat.Shannon.Entropy

open MeasureTheory Filter Topology Finset

namespace Meat

noncomputable def iidProb {S : Type*} {n : ℕ} (p : PMF S) (x : Fin n → S) : ℝ :=
  ∏ i, (p (x i)).toReal

variable {S T : Type*}
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

noncomputable def typicalSet (p : PMF S) (n : ℕ) (ε : ℝ) : Finset (Fin n → S) := by
  classical
  exact {x | Real.exp (-(n * (measureEntropy p.toMeasure + ε))) ≤ iidProb p x ∧
    iidProb p x ≤ Real.exp (-(n * (measureEntropy p.toMeasure - ε)))}

noncomputable def jointlyTypicalSet (p : PMF (S × T)) (n : ℕ) (ε : ℝ) :
    Finset ((Fin n → S) × (Fin n → T)) := by
  classical
  exact {xy | xy.1 ∈ typicalSet (p.map Prod.fst) n ε ∧ xy.2 ∈ typicalSet (p.map Prod.snd) n ε ∧
    (fun i => (xy.1 i, xy.2 i)) ∈ typicalSet p n ε}

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem iidProb_nonneg {n : ℕ} (p : PMF S) (x : Fin n → S) : 0 ≤ iidProb p x :=
  prod_nonneg fun _ _ => ENNReal.toReal_nonneg

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem sum_pmf_eq_one (p : PMF S) : ∑ s, p s = 1 := by
  simpa [tsum_fintype] using p.tsum_coe

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem sum_toReal_pmf_eq_one (p : PMF S) : ∑ s, (p s).toReal = 1 := by
  rw [← ENNReal.toReal_sum fun s _ => p.apply_ne_top s, sum_pmf_eq_one, ENNReal.toReal_one]

theorem PMF.map_apply_of_injective {α β : Type*} (p : PMF α) {f : α → β}
    (hf : Function.Injective f) (a : α) : p.map f (f a) = p a := by
  classical
  rw [PMF.map_apply, tsum_eq_single a fun b hb => ite_eq_right_iff.2 fun h =>
    absurd h (hf.ne (Ne.symm hb))]
  simp

theorem toReal_map_apply {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω'] (p : PMF Ω) (g : Ω → Ω')
    (t : Ω') : (p.map g t).toReal = ∑ s with g s = t, (p s).toReal := by
  rw [PMF.map_apply, tsum_fintype,
    ENNReal.toReal_sum fun t _ => by split_ifs <;> simp [p.apply_ne_top], sum_filter]
  refine sum_congr rfl fun s _ => ?_
  by_cases h : g s = t
  · simp [h]
  · simp [h, Ne.symm h]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem sum_iidProb (p : PMF S) (n : ℕ) : ∑ x : Fin n → S, iidProb p x = 1 :=
  sum_prod (fun _ s => (p s).toReal) fun _ => sum_toReal_pmf_eq_one p

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem negMulLog_iidProb {n : ℕ} (p : PMF S) (x : Fin n → S) :
    Real.negMulLog (iidProb p x) = iidProb p x * ∑ i, -Real.log (p (x i)).toReal := by
  rcases (iidProb_nonneg p x).eq_or_lt with h | h
  · rw [← h]
    simp
  rw [Real.negMulLog, iidProb, Real.log_prod fun i _ => prod_ne_zero_iff.1 h.ne' i (mem_univ i),
    sum_neg_distrib]
  ring

theorem measureEntropy_toMeasure (p : PMF S) :
    measureEntropy p.toMeasure = ∑ s, Real.negMulLog (p s).toReal := by
  simp [measureEntropy, Measure.real, p.toMeasure_apply_singleton _ (measurableSet_singleton _)]

omit [MeasurableSingletonClass S] in
theorem iidProb_pos_of_mem_typicalSet {p : PMF S} {n : ℕ} {ε : ℝ} {x : Fin n → S}
    (hx : x ∈ typicalSet p n ε) : 0 < iidProb p x := by
  simp only [typicalSet, mem_filter, mem_univ, true_and] at hx
  exact (Real.exp_pos _).trans_le hx.1

omit [MeasurableSingletonClass S] in
theorem mem_typicalSet_iff {p : PMF S} {n : ℕ} {ε : ℝ} {x : Fin n → S} (hn : 0 < n) :
    x ∈ typicalSet p n ε ↔
      0 < iidProb p x ∧ |-Real.log (iidProb p x) / n - measureEntropy p.toMeasure| ≤ ε := by
  refine ⟨fun hx => ⟨iidProb_pos_of_mem_typicalSet hx, ?_⟩, fun ⟨hx, h⟩ => ?_⟩
  · have hP := iidProb_pos_of_mem_typicalSet hx
    simp only [typicalSet, mem_filter, mem_univ, true_and] at hx
    rw [← Real.le_log_iff_exp_le hP, ← Real.log_le_iff_le_exp hP] at hx
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [abs_le, le_sub_iff_add_le, sub_le_iff_le_add, le_div_iff₀ hn', div_le_iff₀ hn']
    constructor <;> linarith [hx.1, hx.2]
  · simp only [typicalSet, mem_filter, mem_univ, true_and]
    rw [← Real.le_log_iff_exp_le hx, ← Real.log_le_iff_le_exp hx]
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [abs_le, le_sub_iff_add_le, sub_le_iff_le_add, le_div_iff₀ hn', div_le_iff₀ hn'] at h
    constructor <;> linarith [h.1, h.2]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
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

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
private lemma sum_iidProb_mul_sq (p : PMF S) {n : ℕ} (Y : S → ℝ)
    (hY : ∑ s, (p s).toReal * Y s = 0) :
    ∑ x : Fin n → S, iidProb p x * (∑ i, Y (x i)) ^ 2 = n * ∑ s, (p s).toReal * Y s ^ 2 := by
  simp_rw [sq, sum_mul_sum, mul_sum]
  rw [sum_comm]
  rw [Finset.sum_congr rfl fun i _ => by rw [sum_comm]]
  simp [sum_iidProb_mul_mul p Y hY, ← sq, mul_sum]

theorem sum_toReal_mul_neg_log (p : PMF S) :
    ∑ s, (p s).toReal * -Real.log (p s).toReal = measureEntropy p.toMeasure := by
  rw [measureEntropy_toMeasure]
  exact sum_congr rfl fun s _ => by rw [Real.negMulLog]; ring

private lemma one_sub_le_sum_iidProb_typicalSet (p : PMF S) {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hε : 0 < ε) :
    1 - (∑ s, (p s).toReal * (-Real.log (p s).toReal - measureEntropy p.toMeasure) ^ 2) / ε ^ 2 / n
      ≤ ∑ x ∈ typicalSet p n ε, iidProb p x := by
  classical
  set H := measureEntropy p.toMeasure
  set Y : S → ℝ := fun s => -Real.log (p s).toReal - H
  have hY : ∑ s, (p s).toReal * Y s = 0 := by
    simp only [Y, mul_sub, sum_sub_distrib, sum_toReal_mul_neg_log, ← sum_mul,
      sum_toReal_pmf_eq_one, one_mul]
    exact sub_self _
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hnε : 0 < (n * ε) ^ 2 := by positivity
  have key : ∀ x, (if x ∈ typicalSet p n ε then 0 else iidProb p x)
      ≤ iidProb p x * (∑ i, Y (x i)) ^ 2 / (n * ε) ^ 2 := by
    intro x
    split_ifs with hx
    · exact div_nonneg (mul_nonneg (iidProb_nonneg p x) (sq_nonneg _)) hnε.le
    rcases (iidProb_nonneg p x).eq_or_lt with h0 | h0
    · simp [← h0]
    rw [mem_typicalSet_iff hn, not_and, not_le] at hx
    have hlt := hx h0
    have hsum : -Real.log (iidProb p x) / n - H = (∑ i, Y (x i)) / n := by
      have hl : -Real.log (iidProb p x) = ∑ i, -Real.log (p (x i)).toReal := mul_left_cancel₀
        h0.ne' (by rw [← negMulLog_iidProb, Real.negMulLog, neg_mul, mul_neg])
      rw [hl]
      simp only [Y, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [hsum, abs_div, abs_of_pos hn', lt_div_iff₀ hn'] at hlt
    have hsq : (n * ε) ^ 2 < (∑ i, Y (x i)) ^ 2 := by
      rw [← sq_abs (∑ i, Y (x i))]
      exact pow_lt_pow_left₀ (by linarith) (by positivity) two_ne_zero
    rw [le_div_iff₀ hnε]
    exact mul_le_mul_of_nonneg_left hsq.le h0.le
  have hsum := sum_le_sum fun x (_ : x ∈ univ) => key x
  rw [← sum_div, sum_iidProb_mul_sq p Y hY] at hsum
  have hc : ∑ x, (if x ∈ typicalSet p n ε then 0 else iidProb p x)
      = 1 - ∑ x ∈ typicalSet p n ε, iidProb p x := by
    rw [sum_ite_mem_zero, sum_iidProb]
  rw [hc] at hsum
  have he : (↑n * ∑ s, (p s).toReal * Y s ^ 2) / (↑n * ε) ^ 2
      = (∑ s, (p s).toReal * Y s ^ 2) / ε ^ 2 / n := by
    have := hn'.ne'
    have := hε.ne'
    field_simp
  change 1 - (∑ s, (p s).toReal * Y s ^ 2) / ε ^ 2 / n ≤ _
  linarith

theorem tendsto_exp_nat_mul {c : ℝ} (hc : c < 0) :
    Tendsto (fun n : ℕ => Real.exp (n * c)) atTop (𝓝 0) := by
  simp_rw [Real.exp_nat_mul]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.2 hc)

theorem tendsto_sum_iidProb_typicalSet (p : PMF S) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => ∑ x ∈ typicalSet p n ε, iidProb p x) atTop (𝓝 1) := by
  set V := ∑ s, (p s).toReal * (-Real.log (p s).toReal - measureEntropy p.toMeasure) ^ 2
  have hl : Tendsto (fun n : ℕ => 1 - V / ε ^ 2 / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (V / ε ^ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact one_sub_le_sum_iidProb_typicalSet p hn hε
  · refine Eventually.of_forall fun n => ?_
    rw [← sum_iidProb p n]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => iidProb_nonneg p x

omit [MeasurableSingletonClass S] in
theorem card_typicalSet_le (p : PMF S) (n : ℕ) (ε : ℝ) :
    ((typicalSet p n ε).card : ℝ) ≤ Real.exp (n * (measureEntropy p.toMeasure + ε)) := by
  have h : ∑ x ∈ typicalSet p n ε, Real.exp (-(n * (measureEntropy p.toMeasure + ε)))
      ≤ ∑ x ∈ typicalSet p n ε, iidProb p x := sum_le_sum fun x hx => by
    simp only [typicalSet, mem_filter, mem_univ, true_and] at hx
    exact hx.1
  rw [sum_const, nsmul_eq_mul] at h
  have h1 : ∑ x ∈ typicalSet p n ε, iidProb p x ≤ 1 := by
    rw [← sum_iidProb p n]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => iidProb_nonneg p x
  rw [Real.exp_neg] at h
  rw [← div_le_one (Real.exp_pos _)]
  exact (h.trans h1)

theorem eventually_le_card_typicalSet (p : PMF S) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (1 - ε) * Real.exp (n * (measureEntropy p.toMeasure - ε))
      ≤ (typicalSet p n ε).card := by
  filter_upwards [(tendsto_sum_iidProb_typicalSet p hε).eventually_const_le
    (show 1 - ε < 1 by linarith)] with n hn
  have h : ∑ x ∈ typicalSet p n ε, iidProb p x
      ≤ ∑ x ∈ typicalSet p n ε, Real.exp (-(n * (measureEntropy p.toMeasure - ε))) :=
    sum_le_sum fun x hx => by
      simp only [typicalSet, mem_filter, mem_univ, true_and] at hx
      exact hx.2
  rw [sum_const, nsmul_eq_mul, Real.exp_neg] at h
  calc (1 - ε) * Real.exp (n * (measureEntropy p.toMeasure - ε))
      ≤ (typicalSet p n ε).card * (Real.exp (n * (measureEntropy p.toMeasure - ε)))⁻¹
        * Real.exp (n * (measureEntropy p.toMeasure - ε)) :=
        mul_le_mul_of_nonneg_right (hn.trans h) (Real.exp_pos _).le
    _ = (typicalSet p n ε).card := inv_mul_cancel_right₀ (Real.exp_pos _).ne' _

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
theorem sum_iidProb_pair_right [Finite S] (p : PMF (S × T)) {n : ℕ} (x : Fin n → S) :
    ∑ y : Fin n → T, iidProb p (fun i => (x i, y i)) = iidProb (p.map Prod.fst) x := by
  classical
  have := Fintype.ofFinite S
  have h : ∀ s, (p.map Prod.fst s).toReal = ∑ t, (p (s, t)).toReal := fun s => by
    rw [toReal_map_apply, sum_filter, Fintype.sum_prod_type,
      sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]
    simp
  simp only [iidProb, h]
  rw [Fintype.prod_sum]

omit [Fintype T] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
theorem sum_iidProb_pair_left [Finite T] (p : PMF (S × T)) {n : ℕ} (y : Fin n → T) :
    ∑ x : Fin n → S, iidProb p (fun i => (x i, y i)) = iidProb (p.map Prod.snd) y := by
  classical
  have := Fintype.ofFinite T
  have h : ∀ t, (p.map Prod.snd t).toReal = ∑ s, (p (s, t)).toReal := fun t => by
    rw [toReal_map_apply, sum_filter, Fintype.sum_prod_type_right,
      sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]
    simp
  simp only [iidProb, h]
  rw [Fintype.prod_sum]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
theorem sum_iidProb_pair (p : PMF (S × T)) (n : ℕ) :
    ∑ xy : (Fin n → S) × (Fin n → T), iidProb p (fun i => (xy.1 i, xy.2 i)) = 1 := by
  rw [Fintype.sum_prod_type, ← sum_iidProb (p.map Prod.fst) n]
  exact sum_congr rfl fun x _ => sum_iidProb_pair_right p x

theorem tendsto_sum_iidProb_jointlyTypicalSet (p : PMF (S × T)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => ∑ xy ∈ jointlyTypicalSet p n ε, iidProb p (fun i => (xy.1 i, xy.2 i)))
      atTop (𝓝 1) := by
  classical
  have hl := (((tendsto_sum_iidProb_typicalSet (p.map Prod.fst) hε).add
    (tendsto_sum_iidProb_typicalSet (p.map Prod.snd) hε)).add
    (tendsto_sum_iidProb_typicalSet p hε)).sub_const 2
  norm_num at hl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (fun n => ?_) fun n => ?_
  · set f : (Fin n → S) × (Fin n → T) → ℝ := fun xy => iidProb p fun i => (xy.1 i, xy.2 i)
    have h1 : ∑ xy, (if xy.1 ∈ typicalSet (p.map Prod.fst) n ε then 0 else f xy)
        = 1 - ∑ x ∈ typicalSet (p.map Prod.fst) n ε, iidProb (p.map Prod.fst) x := by
      rw [Fintype.sum_prod_type, ← sum_iidProb (p.map Prod.fst) n, ← sum_ite_mem_zero]
      refine sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ typicalSet (p.map Prod.fst) n ε
      · simp [hx]
      · simp [hx, f, sum_iidProb_pair_right]
    have h2 : ∑ xy, (if xy.2 ∈ typicalSet (p.map Prod.snd) n ε then 0 else f xy)
        = 1 - ∑ y ∈ typicalSet (p.map Prod.snd) n ε, iidProb (p.map Prod.snd) y := by
      rw [Fintype.sum_prod_type_right, ← sum_iidProb (p.map Prod.snd) n, ← sum_ite_mem_zero]
      refine sum_congr rfl fun y _ => ?_
      by_cases hy : y ∈ typicalSet (p.map Prod.snd) n ε
      · simp [hy]
      · simp [hy, f, sum_iidProb_pair_left]
    have h3 : ∑ xy, (if (fun i => (xy.1 i, xy.2 i)) ∈ typicalSet p n ε then 0 else f xy)
        = 1 - ∑ z ∈ typicalSet p n ε, iidProb p z := by
      rw [← sum_iidProb p n, ← sum_ite_mem_zero]
      exact Equiv.sum_comp (Equiv.arrowProdEquivProdArrow _ _ _).symm
        fun z => if z ∈ typicalSet p n ε then 0 else iidProb p z
    have hJ : ∑ xy, (if xy ∈ jointlyTypicalSet p n ε then 0 else f xy)
        ≤ ∑ xy, ((if xy.1 ∈ typicalSet (p.map Prod.fst) n ε then 0 else f xy)
          + (if xy.2 ∈ typicalSet (p.map Prod.snd) n ε then 0 else f xy)
          + (if (fun i => (xy.1 i, xy.2 i)) ∈ typicalSet p n ε then 0 else f xy)) := by
      refine sum_le_sum fun xy _ => ?_
      have hf : 0 ≤ f xy := iidProb_nonneg _ _
      simp only [jointlyTypicalSet, mem_filter, mem_univ, true_and]
      split_ifs <;> simp_all
    rw [sum_add_distrib, sum_add_distrib, h1, h2, h3, sum_ite_mem_zero] at hJ
    rw [sum_iidProb_pair p n] at hJ
    linarith
  · rw [← sum_iidProb_pair p n]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => iidProb_nonneg _ _

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem card_jointlyTypicalSet_le (p : PMF (S × T)) (n : ℕ) (ε : ℝ) :
    ((jointlyTypicalSet p n ε).card : ℝ) ≤ Real.exp (n * (measureEntropy p.toMeasure + ε)) := by
  refine le_trans ?_ (card_typicalSet_le p n ε)
  have h : (jointlyTypicalSet p n ε).card ≤ (typicalSet p n ε).card := by
    refine card_le_card_of_injOn (fun xy i => (xy.1 i, xy.2 i)) (fun xy hxy => ?_) ?_
    · simp only [jointlyTypicalSet, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hxy
      exact hxy.2.2
    · intro a _ b _ hab
      exact Prod.ext (funext fun i => congrArg Prod.fst (congrFun hab i))
        (funext fun i => congrArg Prod.snd (congrFun hab i))
  exact_mod_cast h

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
private lemma mutualInfo_fst_snd (p : PMF (S × T)) :
    mutualInfo (fun ω : S × T => ω.1) (fun ω => ω.2) p.toMeasure
      = measureEntropy (p.map Prod.fst).toMeasure + measureEntropy (p.map Prod.snd).toMeasure
        - measureEntropy p.toMeasure := by
  simp only [mutualInfo, entropy]
  have h : p.toMeasure.map (fun ω : S × T => (ω.1, ω.2)) = p.toMeasure := Measure.map_id'
  rw [h, PMF.toMeasure_map (f := Prod.fst) (p := p) (hf := measurable_fst),
    PMF.toMeasure_map (f := Prod.snd) (p := p) (hf := measurable_snd)]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem sum_iidProb_mul_iidProb_jointlyTypicalSet_le (p : PMF (S × T)) (n : ℕ) (ε : ℝ) :
    ∑ xy ∈ jointlyTypicalSet p n ε, iidProb (p.map Prod.fst) xy.1 * iidProb (p.map Prod.snd) xy.2
      ≤ Real.exp (-(n * (mutualInfo (fun ω : S × T => ω.1) (fun ω => ω.2) p.toMeasure
        - 3 * ε))) := by
  set c := Real.exp (-(n * (measureEntropy (p.map Prod.fst).toMeasure - ε))) *
    Real.exp (-(n * (measureEntropy (p.map Prod.snd).toMeasure - ε))) with hc
  have h : ∑ xy ∈ jointlyTypicalSet p n ε,
      iidProb (p.map Prod.fst) xy.1 * iidProb (p.map Prod.snd) xy.2
        ≤ ∑ xy ∈ jointlyTypicalSet p n ε, c := sum_le_sum fun xy hxy => by
    simp only [jointlyTypicalSet, typicalSet, mem_filter, mem_univ, true_and] at hxy
    exact mul_le_mul hxy.1.2 hxy.2.1.2 (iidProb_nonneg _ _) (Real.exp_pos _).le
  rw [sum_const, nsmul_eq_mul] at h
  refine h.trans ((mul_le_mul_of_nonneg_right (card_jointlyTypicalSet_le p n ε)
    (by positivity)).trans_eq ?_)
  rw [hc, mutualInfo_fst_snd, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end Meat
