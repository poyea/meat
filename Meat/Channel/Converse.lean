import Meat.Channel.Achievability
import Meat.Shannon.Fano
import Meat.Shannon.Product

open MeasureTheory
open scoped ENNReal

namespace Meat

namespace DMC

variable {A B : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

instance isProbabilityMeasure_jointMeasure (W : DMC A B) (p : PMF A) :
    IsProbabilityMeasure (W.jointMeasure p) := by
  unfold jointMeasure
  infer_instance

theorem inputMutualInfo_nonneg (W : DMC A B) (p : PMF A) : 0 ≤ W.inputMutualInfo p :=
  mutualInfo_nonneg _ measurable_fst measurable_snd

theorem inputMutualInfo_le_log_card (W : DMC A B) (p : PMF A) :
    W.inputMutualInfo p ≤ Real.log (Fintype.card A) := by
  have h1 := condEntropy_nonneg (W.jointMeasure p) (X := (Prod.fst : A × B → A))
    (Y := Prod.snd) measurable_fst measurable_snd
  have h2 := entropy_le_log_card (W.jointMeasure p) (X := (Prod.fst : A × B → A))
  rw [inputMutualInfo, mutualInfo_eq_entropy_sub_condEntropy]
  linarith

theorem inputMutualInfo_le_log_card_output (W : DMC A B) (p : PMF A) :
    W.inputMutualInfo p ≤ Real.log (Fintype.card B) := by
  have h1 := condEntropy_nonneg (W.jointMeasure p) (X := (Prod.snd : A × B → B))
    (Y := Prod.fst) measurable_snd measurable_fst
  have h2 := entropy_le_log_card (W.jointMeasure p) (X := (Prod.snd : A × B → B))
  rw [inputMutualInfo, mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
  linarith

theorem bddAbove_range_inputMutualInfo (W : DMC A B) : BddAbove (Set.range W.inputMutualInfo) :=
  ⟨_, Set.forall_mem_range.2 W.inputMutualInfo_le_log_card⟩

theorem inputMutualInfo_le_capacity (W : DMC A B) (p : PMF A) :
    W.inputMutualInfo p ≤ W.capacity :=
  le_ciSup W.bddAbove_range_inputMutualInfo p

theorem capacity_nonneg (W : DMC A B) : 0 ≤ W.capacity :=
  Real.iSup_nonneg W.inputMutualInfo_nonneg

omit [Fintype A] [Fintype B] in
private lemma jointMeasure_real_singleton (W : DMC A B) (p : PMF A) (x : A × B) :
    (W.jointMeasure p).real {x} = (p x.1).toReal * (W x.1 x.2).toReal := by
  rw [measureReal_def, jointMeasure_eq_toMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), ← ENNReal.toReal_mul,
    ← jointPMF_apply]

theorem condEntropy_snd_fst_jointMeasure (W : DMC A B) (p : PMF A) :
    H[Prod.snd | Prod.fst ; W.jointMeasure p]
      = -∑ x : A × B, (W.jointMeasure p).real {x} * Real.log (W x.1 x.2).toReal := by
  set ν := W.jointMeasure p
  have hν : ν.map Prod.fst = p.toMeasure :=
    (PMF.toMeasure_map _ _ measurable_fst).trans (congrArg PMF.toMeasure (jointPMF_map_fst W p))
  have h1 : H[fun x : A × B => (x.2, x.1) ; ν] = measureEntropy ν := by
    rw [show (fun x : A × B => (x.2, x.1)) = Prod.swap ∘ id from rfl,
      entropy_comp_of_injective ν Prod.swap_injective, entropy, Measure.map_id]
  have h2 : H[Prod.fst ; ν] = -∑ x : A × B, ν.real {x} * Real.log ((ν.map Prod.fst).real {x.1}) :=
    measureEntropy_map_eq_neg_sum_mul_log ν Prod.fst
  rw [condEntropy_def, h1, h2, measureEntropy_eq_neg_sum_mul_log, hν,
    ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [ν]
  rw [jointMeasure_real_singleton, measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rcases eq_or_ne ((p x.1).toReal * (W x.1 x.2).toReal) 0 with h | h
  · simp [h]
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 h
  rw [Real.log_mul ha hb]
  ring

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private lemma sum_ite_blockProb {n : ℕ} [DecidableEq B] (W : DMC A B) (x : Fin n → A)
    (i : Fin n) (b : B) :
    ∑ y : Fin n → B, (if y i = b then W.blockProb x y else 0) = W (x i) b := by
  classical
  let f : Fin n → B → ℝ≥0∞ := fun j c => if j = i then (if c = b then W (x j) c else 0)
    else W (x j) c
  have h : ∀ y : Fin n → B, (if y i = b then W.blockProb x y else 0) = ∏ j, f j (y j) := by
    intro y
    by_cases hy : y i = b
    · rw [ite_eq_left hy, blockProb]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst hj
        simp [f, hy]
      · simp [f, hj]
    · rw [ite_eq_right hy]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [f, hy])).symm
  simp_rw [h]
  rw [← Fintype.prod_sum]
  have h2 : ∀ j, ∑ c, f j c = if j = i then W (x i) b else 1 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp [f]
    · simp only [f, ite_eq_right hj]
      exact sum_pmf_eq_one _
  simp_rw [h2]
  rw [Finset.prod_ite_eq']
  simp

end DMC

theorem sum_inv_card (M : Type*) [Fintype M] [Nonempty M] :
    ∑ _ : M, (Fintype.card M : ℝ≥0∞)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

namespace BlockCode

variable {M A B : Type*} {n : ℕ} [Fintype M] [Nonempty M] [MeasurableSpace M]
  [MeasurableSingletonClass M] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

omit [MeasurableSpace M] [MeasurableSingletonClass M] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private lemma sum_codeMass (c : BlockCode M A B n) (W : DMC A B) :
    ∑ ω : M × (Fin n → B), (Fintype.card M : ℝ≥0∞)⁻¹ * W.blockProb (c.enc ω.1) ω.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, DMC.sum_blockProb_eq_one, mul_one]
  exact sum_inv_card M

omit [MeasurableSingletonClass M] [MeasurableSingletonClass B] in
noncomputable def codeMeasure (c : BlockCode M A B n) (W : DMC A B) : Measure (M × (Fin n → B)) :=
  (PMF.ofFintype _ (sum_codeMass c W)).toMeasure

omit [MeasurableSpace M] [MeasurableSingletonClass M] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
noncomputable def inputLaw (c : BlockCode M A B n) (i : Fin n) : PMF A :=
  (PMF.ofFintype _ (sum_inv_card M)).map fun m => c.enc m i

omit [MeasurableSingletonClass M] [MeasurableSingletonClass B] in
instance isProbabilityMeasure_codeMeasure (c : BlockCode M A B n) (W : DMC A B) :
    IsProbabilityMeasure (c.codeMeasure W) := by
  unfold codeMeasure
  infer_instance

private lemma codeMeasure_apply (c : BlockCode M A B n) (W : DMC A B)
    (s : Set (M × (Fin n → B))) :
    c.codeMeasure W s = ∑ ω, s.indicator
      (fun ω => (Fintype.card M : ℝ≥0∞)⁻¹ * W.blockProb (c.enc ω.1) ω.2) ω := by
  rw [codeMeasure, PMF.toMeasure_apply_fintype]
  rfl

private lemma codeMeasure_real_singleton (c : BlockCode M A B n) (W : DMC A B)
    (ω : M × (Fin n → B)) :
    (c.codeMeasure W).real {ω}
      = (Fintype.card M : ℝ)⁻¹ * ∏ i, (W (c.enc ω.1 i) (ω.2 i)).toReal := by
  rw [measureReal_def, codeMeasure_apply, Finset.sum_eq_single ω (fun b _ hb => by simp [hb])
    (by simp), Set.indicator_of_mem (Set.mem_singleton ω), ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, DMC.blockProb, ENNReal.toReal_prod]

private lemma map_apply_singleton (c : BlockCode M A B n) (W : DMC A B) {S : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq S] (f : M × (Fin n → B) → S)
    (s : S) :
    (c.codeMeasure W).map f {s} = ∑ ω, if f ω = s then
      (Fintype.card M : ℝ≥0∞)⁻¹ * W.blockProb (c.enc ω.1) ω.2 else 0 := by
  rw [Measure.map_apply (measurable_of_finite f) (measurableSet_singleton s), codeMeasure_apply]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : f ω = s <;> simp [h]

theorem entropy_fst_codeMeasure (c : BlockCode M A B n) (W : DMC A B) :
    H[Prod.fst ; c.codeMeasure W] = Real.log (Fintype.card M) := by
  classical
  refine entropy_eq_log_card _ fun m => ?_
  rw [measureReal_def, map_apply_singleton, Fintype.sum_prod_type, Finset.sum_eq_single m
    (fun b _ hb => by simp [hb]) (by simp)]
  simp only [ite_true]
  rw [← Finset.mul_sum, DMC.sum_blockProb_eq_one, mul_one, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

theorem measureReal_dec_ne (c : BlockCode M A B n) (W : DMC A B) [DecidableEq M] :
    (c.codeMeasure W).real {ω | c.dec ω.2 ≠ ω.1} = (c.avgError W).toReal := by
  rw [measureReal_def, codeMeasure_apply, avgError, div_eq_mul_inv, mul_comm, Finset.mul_sum,
    Fintype.sum_prod_type]
  refine congrArg ENNReal.toReal (Finset.sum_congr rfl fun m _ => ?_)
  rw [errorProb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : c.dec y = m <;> simp [Set.indicator, h]

theorem map_codeMeasure [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (c : BlockCode M A B n) (W : DMC A B) (i : Fin n) :
    (c.codeMeasure W).map (fun ω => (c.enc ω.1 i, ω.2 i)) = W.jointMeasure (c.inputLaw i) := by
  classical
  refine Measure.ext_of_singleton fun x => ?_
  rw [map_apply_singleton, DMC.jointMeasure_eq_toMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    show DMC.jointPMF W (c.inputLaw i) x = _ from DMC.jointPMF_apply W (c.inputLaw i) x.1 x.2,
    inputLaw, PMF.map_apply, tsum_fintype,
    Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [PMF.ofFintype_apply, Prod.ext_iff, ite_and]
  by_cases hm : c.enc m i = x.1
  · simp only [hm, ite_true]
    rw [← hm, ← DMC.sum_ite_blockProb W (c.enc m) i x.2, Finset.mul_sum]
    simp only [mul_ite, mul_zero]
  · simp [hm, Ne.symm hm]

theorem condEntropy_snd_fst_codeMeasure [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (c : BlockCode M A B n) (W : DMC A B) :
    H[Prod.snd | Prod.fst ; c.codeMeasure W]
      = ∑ i, H[Prod.snd | Prod.fst ; W.jointMeasure (c.inputLaw i)] := by
  set μ := c.codeMeasure W
  have h1 : H[fun ω : M × (Fin n → B) => (ω.2, ω.1) ; μ] = measureEntropy μ := by
    rw [show (fun ω : M × (Fin n → B) => (ω.2, ω.1)) = Prod.swap ∘ id from rfl,
      entropy_comp_of_injective μ Prod.swap_injective, entropy, Measure.map_id]
  have hk : (Fintype.card M : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have h2 : ∀ ω, μ.real {ω} * Real.log (μ.real {ω})
      = -(μ.real {ω} * Real.log (Fintype.card M))
        + ∑ i, μ.real {ω} * Real.log (W (c.enc ω.1 i) (ω.2 i)).toReal := by
    intro ω
    rcases eq_or_ne (μ.real {ω}) 0 with h | h
    · simp [h]
    have hP := codeMeasure_real_singleton c W ω
    have ht : ∏ i, (W (c.enc ω.1 i) (ω.2 i)).toReal ≠ 0 := fun h0 => h (by rw [hP, h0, mul_zero])
    rw [hP, Real.log_mul hk ht, Real.log_inv,
      Real.log_prod fun i _ => Finset.prod_ne_zero_iff.1 ht i (Finset.mem_univ i), ← hP, mul_add,
      Finset.mul_sum]
    ring
  have h3 : ∀ i, ∑ ω, μ.real {ω} * Real.log (W (c.enc ω.1 i) (ω.2 i)).toReal
      = ∑ x : A × B, (W.jointMeasure (c.inputLaw i)).real {x} * Real.log (W x.1 x.2).toReal := by
    intro i
    rw [← map_codeMeasure c W i]
    exact sum_measureReal_mul_comp μ (fun ω => (c.enc ω.1 i, ω.2 i))
      (fun x => Real.log (W x.1 x.2).toReal)
  rw [condEntropy_def, h1, entropy_fst_codeMeasure, measureEntropy_eq_neg_sum_mul_log,
    Finset.sum_congr rfl fun ω _ => h2 ω, Finset.sum_add_distrib, Finset.sum_comm,
    Finset.sum_congr rfl fun i _ => h3 i]
  simp only [DMC.condEntropy_snd_fst_jointMeasure, Finset.sum_neg_distrib]
  rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one]
  ring

theorem mutualInfo_le_sum_inputMutualInfo [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (c : BlockCode M A B n) (W : DMC A B) :
    I[Prod.fst : Prod.snd ; c.codeMeasure W] ≤ ∑ i, W.inputMutualInfo (c.inputLaw i) := by
  have hY : H[Prod.snd ; c.codeMeasure W]
      ≤ ∑ i, H[fun ω : M × (Fin n → B) => ω.2 i ; c.codeMeasure W] :=
    entropy_pi_le_sum _ fun _ => measurable_of_finite _
  have hi : ∀ i, H[fun ω : M × (Fin n → B) => ω.2 i ; c.codeMeasure W]
      = H[Prod.snd ; W.jointMeasure (c.inputLaw i)] := by
    intro i
    rw [← map_codeMeasure c W i, entropy_map _ (measurable_of_finite _) measurable_snd]
    rfl
  have hI : ∀ i, W.inputMutualInfo (c.inputLaw i) = H[Prod.snd ; W.jointMeasure (c.inputLaw i)]
      - H[Prod.snd | Prod.fst ; W.jointMeasure (c.inputLaw i)] := by
    intro i
    rw [DMC.inputMutualInfo, mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
  rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy, condEntropy_snd_fst_codeMeasure]
  simp only [hI, Finset.sum_sub_distrib, ← hi]
  linarith

theorem mutualInfo_le_mul_capacity [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (c : BlockCode M A B n) (W : DMC A B) :
    I[Prod.fst : Prod.snd ; c.codeMeasure W] ≤ n * W.capacity := by
  refine (c.mutualInfo_le_sum_inputMutualInfo W).trans ?_
  refine (Finset.sum_le_sum fun i _ => W.inputMutualInfo_le_capacity (c.inputLaw i)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem condEntropy_fst_snd_codeMeasure_le [DecidableEq M] (c : BlockCode M A B n)
    (W : DMC A B) :
    H[Prod.fst | Prod.snd ; c.codeMeasure W]
      ≤ Real.log 2 + (c.avgError W).toReal * Real.log (Fintype.card M) := by
  have h := condEntropy_le_log_two_add_mul_log_card (μ := c.codeMeasure W) measurable_fst
    measurable_snd c.dec
  rwa [measureReal_dec_ne] at h

theorem one_sub_mul_log_card_le [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [DecidableEq M] (c : BlockCode M A B n) (W : DMC A B) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M) ≤ n * W.capacity + Real.log 2 := by
  have h1 := c.mutualInfo_le_mul_capacity W
  have h2 := c.condEntropy_fst_snd_codeMeasure_le W
  have h3 := mutualInfo_eq_entropy_sub_condEntropy Prod.fst Prod.snd (c.codeMeasure W)
  rw [entropy_fst_codeMeasure] at h3
  have h4 : (1 - (c.avgError W).toReal) * Real.log (Fintype.card M)
      = Real.log (Fintype.card M) - (c.avgError W).toReal * Real.log (Fintype.card M) := by ring
  linarith

end BlockCode

namespace DMC

variable {A B : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem le_capacity_of_achievable (W : DMC A B) {R : ℝ} (h : W.Achievable R) :
    R ≤ W.capacity := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hC := W.capacity_nonneg
  set C := W.capacity
  set δ := R - C with hδ
  have hδ0 : 0 < δ := by linarith
  have hR : 0 < R := by linarith
  set e := δ / (2 * R) with he
  have he0 : 0 < e := by positivity
  have he1 : e * R = δ / 2 := by
    rw [he]
    field_simp
  have he2 : 0 < 1 - e := by nlinarith
  obtain ⟨N, hN⟩ := h (ENNReal.ofReal e) (ENNReal.ofReal_pos.2 he0)
  obtain ⟨n0, hn0⟩ := exists_nat_gt (2 * Real.log 2 / δ)
  obtain ⟨n, hNn, hn0n⟩ : ∃ n : ℕ, N ≤ n ∧ n0 ≤ n := ⟨max N n0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hNn
  have hn : 2 * Real.log 2 < n * δ := by
    rw [← div_lt_iff₀ hδ0]
    exact hn0.trans_le (by exact_mod_cast hn0n)
  have hk0 : (0 : ℝ) < k := (Real.exp_pos _).trans_le hk
  have : Nonempty (Fin k) := ⟨⟨0, by exact_mod_cast hk0⟩⟩
  have key := c.one_sub_mul_log_card_le W
  rw [Fintype.card_fin] at key
  have hPe : (c.avgError W).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1 : (1 - e) * Real.log k ≤ n * C + Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)).trans key
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

end DMC

end Meat
