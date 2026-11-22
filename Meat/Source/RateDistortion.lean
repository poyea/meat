import Meat.Channel.Converse
import Meat.Shannon.LogSum

open MeasureTheory Finset Topology

namespace Meat

structure LossyCode (S T : Type*) (n k : ℕ) where
  enc : (Fin n → S) → Fin k
  dec : Fin k → Fin n → T

namespace RateDistortion

variable {S T : Type*}

noncomputable def blockDist (d : S → T → ℝ) {n : ℕ} (x : Fin n → S) (y : Fin n → T) : ℝ :=
  (∑ i, d (x i) (y i)) / n

end RateDistortion

namespace LossyCode

variable {S T : Type*} {n k : ℕ}

noncomputable def distortion [Fintype S] (c : LossyCode S T n k) (p : PMF S) (d : S → T → ℝ) :
    ℝ :=
  ∑ x, iidProb p x * RateDistortion.blockDist d x (c.dec (c.enc x))

end LossyCode

namespace RateDistortion

variable {S T : Type*}

def Achievable [Fintype S] (p : PMF S) (d : S → T → ℝ) (R D : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (n * R) ∧ ∃ c : LossyCode S T n k, c.distortion p d ≤ D + ε

def achievableRegion [Fintype S] (p : PMF S) (d : S → T → ℝ) : Set (ℝ × ℝ) :=
  {RD | Achievable p d RD.1 RD.2}

noncomputable def expDist [Fintype S] [Fintype T] (p : PMF S) (d : S → T → ℝ) (W : DMC S T) :
    ℝ :=
  ∑ s, ∑ t, (p s).toReal * (W s t).toReal * d s t

noncomputable def minDist [Fintype S] (p : PMF S) (d : S → T → ℝ) : ℝ :=
  ∑ s, (p s).toReal * ⨅ t, d s t

noncomputable def rdf [Fintype S] [MeasurableSpace S] [Fintype T] [MeasurableSpace T]
    (p : PMF S) (d : S → T → ℝ) (D : ℝ) : ℝ :=
  sInf ((fun W : DMC S T => W.inputMutualInfo p) '' {W | expDist p d W ≤ D})

noncomputable def rateRegion [Fintype S] [MeasurableSpace S] [Fintype T] [MeasurableSpace T]
    (p : PMF S) (d : S → T → ℝ) : Set (ℝ × ℝ) :=
  {RD | minDist p d ≤ RD.2 ∧ rdf p d RD.2 ≤ RD.1}

end RateDistortion

namespace DMC

variable {S T : Type*} [Fintype S] [Fintype T]

noncomputable def ofMatrix (w : S → T → ℝ) (hw : ∀ s t, 0 ≤ w s t) (h1 : ∀ s, ∑ t, w s t = 1) :
    DMC S T :=
  fun s => PMF.ofFintype (fun t => ENNReal.ofReal (w s t)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun t _ => hw s t, h1 s, ENNReal.ofReal_one])

omit [Fintype S] in
theorem toReal_ofMatrix (w : S → T → ℝ) (hw : ∀ s t, 0 ≤ w s t) (h1 : ∀ s, ∑ t, w s t = 1)
    (s : S) (t : T) : (ofMatrix w hw h1 s t).toReal = w s t := by
  simp [ofMatrix, ENNReal.toReal_ofReal (hw s t)]

variable [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma sum_filter_fst [DecidableEq S] {β : Type*} [AddCommMonoid β] (f : S × T → β) (s : S) :
    ∑ x : S × T with x.1 = s, f x = ∑ t, f (s, t) := by
  rw [sum_filter, Fintype.sum_prod_type, sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]
  simp

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma sum_filter_snd [DecidableEq T] {β : Type*} [AddCommMonoid β] (f : S × T → β) (t : T) :
    ∑ x : S × T with x.2 = t, f x = ∑ s, f (s, t) := by
  rw [sum_filter, Fintype.sum_prod_type_right,
    sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]
  simp

omit [Fintype S] in
theorem measureReal_map_fst [Finite S] (ν : Measure (S × T)) [IsFiniteMeasure ν] (s : S) :
    (ν.map Prod.fst).real {s} = ∑ t, ν.real {(s, t)} := by
  classical
  have := Fintype.ofFinite S
  rw [measureReal_map_singleton]
  convert sum_filter_fst (fun x => ν.real {x}) s

omit [Fintype T] in
theorem measureReal_map_snd [Finite T] (ν : Measure (S × T)) [IsFiniteMeasure ν] (t : T) :
    (ν.map Prod.snd).real {t} = ∑ s, ν.real {(s, t)} := by
  classical
  have := Fintype.ofFinite T
  rw [measureReal_map_singleton]
  convert sum_filter_snd (fun x => ν.real {x}) t

theorem mutualInfo_fst_snd_eq_sum (ν : Measure (S × T)) [IsFiniteMeasure ν] :
    I[Prod.fst : Prod.snd ; ν] = ∑ s, Real.negMulLog (∑ t, ν.real {(s, t)}) +
      ∑ t, Real.negMulLog (∑ s, ν.real {(s, t)}) - ∑ s, ∑ t, Real.negMulLog (ν.real {(s, t)}) := by
  have h : ν.map (fun ω : S × T => (ω.1, ω.2)) = ν := Measure.map_id'
  rw [mutualInfo_def, entropy_def, entropy_def, entropy_def, h, Fintype.sum_prod_type]
  simp only [measureReal_map_fst, measureReal_map_snd]

omit [Fintype S] [Fintype T] in
theorem jointMeasure_real_singleton (W : DMC S T) (p : PMF S) (s : S) (t : T) :
    (W.jointMeasure p).real {(s, t)} = (p s).toReal * (W s t).toReal := by
  rw [measureReal_def, jointMeasure_eq_toMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), jointPMF_apply,
    ENNReal.toReal_mul]

private noncomputable def miSum (P : S → ℝ) (w : S → T → ℝ) : ℝ :=
  ∑ s, Real.negMulLog (∑ t, P s * w s t) + ∑ t, Real.negMulLog (∑ s, P s * w s t) -
    ∑ s, ∑ t, Real.negMulLog (P s * w s t)

private noncomputable def klSum (P : S → ℝ) (w : S → T → ℝ) : ℝ :=
  ∑ s, ∑ t, P s * w s t * Real.log (P s * w s t / (P s * ∑ s', P s' * w s' t))

private def stoch (S T : Type*) [Fintype T] : Set (S → T → ℝ) :=
  {w | (∀ s t, 0 ≤ w s t) ∧ ∀ s, ∑ t, w s t = 1}

private lemma inputMutualInfo_eq_miSum (W : DMC S T) (p : PMF S) :
    W.inputMutualInfo p = miSum (fun s => (p s).toReal) (fun s t => (W s t).toReal) := by
  have h := mutualInfo_fst_snd_eq_sum (W.jointMeasure p)
  simp only [jointMeasure_real_singleton] at h
  exact h

omit [Fintype T] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma mul_eq_zero_of_mul_sum_eq_zero {P : S → ℝ} {w : S → T → ℝ} (hP : ∀ s, 0 ≤ P s)
    (h0 : ∀ s t, 0 ≤ w s t) {s : S} {t : T} (h : P s * ∑ s', P s' * w s' t = 0) :
    P s * w s t = 0 := by
  rcases mul_eq_zero.1 h with h | h
  · simp [h]
  · exact le_antisymm (h ▸ single_le_sum (f := fun s' => P s' * w s' t)
      (fun s' _ => mul_nonneg (hP s') (h0 s' t)) (mem_univ s)) (mul_nonneg (hP s) (h0 s t))

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma miSum_eq_klSum {P : S → ℝ} (hP : ∀ s, 0 ≤ P s) {w : S → T → ℝ}
    (hw : w ∈ stoch S T) : miSum P w = klSum P w := by
  obtain ⟨h0, h1⟩ := hw
  have hrow : ∀ s, ∑ t, P s * w s t = P s := fun s => by rw [← mul_sum, h1, mul_one]
  have e1 : ∑ s, Real.negMulLog (∑ t, P s * w s t)
      = -∑ s, ∑ t, P s * w s t * Real.log (P s) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun s _ => ?_
    rw [← sum_mul, hrow, Real.negMulLog]
    ring
  have e2 : ∑ t, Real.negMulLog (∑ s, P s * w s t)
      = -∑ s, ∑ t, P s * w s t * Real.log (∑ s', P s' * w s' t) := by
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [← sum_mul, Real.negMulLog]
    ring
  have e3 : ∑ s, ∑ t, Real.negMulLog (P s * w s t)
      = -∑ s, ∑ t, P s * w s t * Real.log (P s * w s t) := by
    simp only [Real.negMulLog, ← sum_neg_distrib]
    refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => by ring
  have e4 : miSum P w = ∑ s, ∑ t, (P s * w s t * Real.log (P s * w s t) -
      P s * w s t * Real.log (P s) - P s * w s t * Real.log (∑ s', P s' * w s' t)) := by
    simp only [sum_sub_distrib]
    rw [miSum, e1, e2, e3]
    ring
  rw [e4, klSum]
  refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
  rcases eq_or_ne (P s * w s t) 0 with ha | ha
  · simp [ha]
  have hPs : P s ≠ 0 := left_ne_zero_of_mul ha
  have hq : 0 < ∑ s', P s' * w s' t :=
    ((mul_nonneg (hP s) (h0 s t)).lt_of_ne' ha).trans_le (single_le_sum
      (f := fun s' => P s' * w s' t) (fun s' _ => mul_nonneg (hP s') (h0 s' t)) (mem_univ s))
  rw [Real.log_div ha (mul_ne_zero hPs hq.ne'), Real.log_mul hPs hq.ne']
  ring

private lemma mul_mul_log_div_mul (c a b : ℝ) :
    c * a * Real.log (c * a / (c * b)) = c * (a * Real.log (a / b)) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [mul_div_mul_left _ _ hc]
    ring

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma klSum_mix_le {P : S → ℝ} (hP : ∀ s, 0 ≤ P s) {w₁ w₂ : S → T → ℝ}
    (hw₁ : w₁ ∈ stoch S T) (hw₂ : w₂ ∈ stoch S T) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    klSum P (fun s t => c₁ * w₁ s t + c₂ * w₂ s t) ≤ c₁ * klSum P w₁ + c₂ * klSum P w₂ := by
  simp only [klSum]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun s _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun t _ => ?_
  have ha : P s * (c₁ * w₁ s t + c₂ * w₂ s t) = c₁ * (P s * w₁ s t) + c₂ * (P s * w₂ s t) := by
    ring
  have hb : P s * ∑ s', P s' * (c₁ * w₁ s' t + c₂ * w₂ s' t) =
      c₁ * (P s * ∑ s', P s' * w₁ s' t) + c₂ * (P s * ∑ s', P s' * w₂ s' t) := by
    simp only [mul_add, sum_add_distrib, mul_sum]
    congr 1 <;> exact sum_congr rfl fun _ _ => by ring
  have hq : ∀ w : S → T → ℝ, (∀ s t, 0 ≤ w s t) → 0 ≤ P s * ∑ s', P s' * w s' t :=
    fun w h0 => mul_nonneg (hP s) (sum_nonneg fun s' _ => mul_nonneg (hP s') (h0 s' t))
  have hz : ∀ (c : ℝ) (w : S → T → ℝ), (∀ s t, 0 ≤ w s t) →
      c * (P s * ∑ s', P s' * w s' t) = 0 → c * (P s * w s t) = 0 := by
    intro c w h0 h
    rcases mul_eq_zero.1 h with h | h
    · simp [h]
    · rw [mul_eq_zero_of_mul_sum_eq_zero hP h0 h, mul_zero]
  have key := add_mul_log_div_add_le (mul_nonneg hc₁ (mul_nonneg (hP s) (hw₁.1 s t)))
    (mul_nonneg hc₂ (mul_nonneg (hP s) (hw₂.1 s t))) (mul_nonneg hc₁ (hq w₁ hw₁.1))
    (mul_nonneg hc₂ (hq w₂ hw₂.1)) (hz c₁ w₁ hw₁.1) (hz c₂ w₂ hw₂.1)
  rw [mul_mul_log_div_mul c₁ (P s * w₁ s t), mul_mul_log_div_mul c₂ (P s * w₂ s t)] at key
  rw [ha, hb]
  linarith

theorem inputMutualInfo_le_of_toReal_eq (p : PMF S) {W W₁ W₂ : DMC S T} {c₁ c₂ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hW : ∀ s t, (W s t).toReal = c₁ * (W₁ s t).toReal + c₂ * (W₂ s t).toReal) :
    W.inputMutualInfo p ≤ c₁ * W₁.inputMutualInfo p + c₂ * W₂.inputMutualInfo p := by
  have hP : ∀ s, 0 ≤ (p s).toReal := fun s => ENNReal.toReal_nonneg
  have hs : ∀ V : DMC S T, (fun s t => (V s t).toReal) ∈ stoch S T :=
    fun V => ⟨fun s t => ENNReal.toReal_nonneg, fun s => sum_toReal_pmf_eq_one (V s)⟩
  simp only [inputMutualInfo_eq_miSum, miSum_eq_klSum hP (hs _)]
  have e : (fun s t => (W s t).toReal) = fun s t => c₁ * (W₁ s t).toReal + c₂ * (W₂ s t).toReal :=
    funext fun s => funext fun t => hW s t
  rw [e]
  exact klSum_mix_le hP (hs W₁) (hs W₂) hc₁ hc₂

omit [Fintype S] [Fintype T] in
theorem exists_jointMeasure_eq [Finite S] [Finite T] [Nonempty T] (p : PMF S)
    (ν : Measure (S × T)) [IsProbabilityMeasure ν] (h : ν.map Prod.fst = p.toMeasure) :
    ∃ W : DMC S T, W.jointMeasure p = ν := by
  classical
  have := Fintype.ofFinite S
  have := Fintype.ofFinite T
  obtain ⟨t₀⟩ := ‹Nonempty T›
  have hm : ∀ s, ∑ t, ν.real {(s, t)} = (p s).toReal := fun s => by
    rw [← measureReal_map_fst, h, measureReal_def,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  set w : S → T → ℝ := fun s t =>
    if (p s).toReal = 0 then (if t = t₀ then 1 else 0) else ν.real {(s, t)} / (p s).toReal
  have hw0 : ∀ s t, 0 ≤ w s t := fun s t => by
    simp only [w]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
    · exact div_nonneg measureReal_nonneg ENNReal.toReal_nonneg
  have hw1 : ∀ s, ∑ t, w s t = 1 := fun s => by
    simp only [w]
    split_ifs with hs
    · simp
    · rw [← sum_div, hm, div_self hs]
  refine ⟨ofMatrix w hw0 hw1, Measure.ext_of_singleton fun x => ?_⟩
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top ν _)]
  congr 1
  obtain ⟨s, t⟩ := x
  rw [jointMeasure_real_singleton, toReal_ofMatrix]
  by_cases hs : (p s).toReal = 0
  · rw [hs, zero_mul]
    have : ν.real {(s, t)} ≤ 0 := calc
      ν.real {(s, t)} ≤ ∑ t', ν.real {(s, t')} :=
        single_le_sum (f := fun t' => ν.real {(s, t')}) (fun _ _ => measureReal_nonneg)
          (mem_univ t)
      _ = 0 := by rw [hm, hs]
    exact (le_antisymm this measureReal_nonneg).symm
  · simp only [w, hs, ite_false]
    field_simp

end DMC

namespace RateDistortion

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

private noncomputable def distSum (P : S → ℝ) (d : S → T → ℝ) (w : S → T → ℝ) : ℝ :=
  ∑ s, ∑ t, P s * w s t * d s t

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma continuous_distSum (P : S → ℝ) (d : S → T → ℝ) :
    Continuous (distSum P d) := by
  unfold distSum
  fun_prop

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma continuous_miSum (P : S → ℝ) : Continuous (DMC.miSum (T := T) P) := by
  unfold DMC.miSum
  fun_prop

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma isCompact_stoch : IsCompact (DMC.stoch S T) := by
  have hK : IsCompact (Set.univ.pi fun _ : S => Set.univ.pi fun _ : T => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hK.of_isClosed_subset ?_ ?_
  · have e : DMC.stoch S T = (⋂ s, ⋂ t, {w : S → T → ℝ | 0 ≤ w s t}) ∩
        ⋂ s, {w : S → T → ℝ | ∑ t, w s t = 1} := by
      ext w
      simp [DMC.stoch]
    rw [e]
    exact (isClosed_iInter fun s => isClosed_iInter fun t =>
      isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_iInter fun s => isClosed_eq (by fun_prop) continuous_const)
  · intro w hw
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    exact fun s t => ⟨hw.1 s t, (hw.2 s) ▸ single_le_sum (fun t _ => hw.1 s t) (mem_univ t)⟩

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma mat_mem (W : DMC S T) : (fun s t => (W s t).toReal) ∈ DMC.stoch S T :=
  ⟨fun _ _ => ENNReal.toReal_nonneg, fun s => sum_toReal_pmf_eq_one (W s)⟩

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
theorem minDist_le_expDist (p : PMF S) (d : S → T → ℝ) (W : DMC S T) :
    minDist p d ≤ expDist p d W := by
  unfold minDist expDist
  refine sum_le_sum fun s _ => ?_
  calc (p s).toReal * ⨅ t, d s t = ∑ t, (p s).toReal * (W s t).toReal * ⨅ t', d s t' := by
        rw [← sum_mul, ← mul_sum, sum_toReal_pmf_eq_one, mul_one]
    _ ≤ _ := sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
        (ciInf_le (Finite.bddBelow_range _) t)
        (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
theorem exists_expDist_eq_minDist [Nonempty T] (p : PMF S) (d : S → T → ℝ) :
    ∃ W : DMC S T, expDist p d W = minDist p d := by
  classical
  choose g hg using fun s =>
    Set.mem_range.1 ((Set.range_nonempty fun t => d s t).csInf_mem
      (Set.finite_range fun t => d s t))
  refine ⟨fun s => PMF.pure (g s), sum_congr rfl fun s _ => ?_⟩
  rw [sum_eq_single (g s) (fun t _ ht => by simp [PMF.pure_apply, ht]) (by simp)]
  simp only [PMF.pure_apply, ite_true, ENNReal.toReal_one, mul_one, hg s]
  rfl

private lemma bddBelow_image (p : PMF S) (d : S → T → ℝ) (D : ℝ) :
    BddBelow ((fun W : DMC S T => W.inputMutualInfo p) '' {W | expDist p d W ≤ D}) :=
  ⟨0, by
    rintro _ ⟨W, -, rfl⟩
    exact DMC.inputMutualInfo_nonneg W p⟩

theorem rdf_nonneg (p : PMF S) (d : S → T → ℝ) (D : ℝ) : 0 ≤ rdf p d D :=
  Real.sInf_nonneg (by
    rintro _ ⟨W, -, rfl⟩
    exact DMC.inputMutualInfo_nonneg W p)

theorem rdf_le_inputMutualInfo {p : PMF S} {d : S → T → ℝ} {D : ℝ} {W : DMC S T}
    (h : expDist p d W ≤ D) : rdf p d D ≤ W.inputMutualInfo p :=
  csInf_le (bddBelow_image p d D) ⟨W, h, rfl⟩

theorem exists_rdf_eq [Nonempty T] (p : PMF S) (d : S → T → ℝ) {D : ℝ} (hD : minDist p d ≤ D) :
    ∃ W : DMC S T, expDist p d W ≤ D ∧ W.inputMutualInfo p = rdf p d D := by
  set P : S → ℝ := fun s => (p s).toReal
  set K := DMC.stoch S T ∩ {w | distSum P d w ≤ D}
  have hK : IsCompact K :=
    isCompact_stoch.inter_right (isClosed_le (continuous_distSum P d) continuous_const)
  obtain ⟨W₀, hW₀⟩ := exists_expDist_eq_minDist (T := T) p d
  have hne : K.Nonempty := ⟨_, mat_mem W₀, show expDist p d W₀ ≤ D from hW₀ ▸ hD⟩
  obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hne (continuous_miSum P).continuousOn
  set W := DMC.ofMatrix w hw.1.1 hw.1.2
  have hmat : (fun s t => (W s t).toReal) = w :=
    funext fun s => funext fun t => DMC.toReal_ofMatrix _ _ _ s t
  have hE : expDist p d W = distSum P d w := by
    rw [← hmat]
    rfl
  have hI : W.inputMutualInfo p = DMC.miSum P w := by
    rw [DMC.inputMutualInfo_eq_miSum, hmat]
  have hWD : expDist p d W ≤ D := hE ▸ hw.2
  refine ⟨W, hWD, le_antisymm ?_ (rdf_le_inputMutualInfo hWD)⟩
  refine le_csInf ⟨_, W, hWD, rfl⟩ ?_
  rintro _ ⟨V, hV, rfl⟩
  change W.inputMutualInfo p ≤ V.inputMutualInfo p
  rw [hI, DMC.inputMutualInfo_eq_miSum]
  exact isMinOn_iff.1 hmin _ ⟨mat_mem V, hV⟩

theorem rdf_le_rdf [Nonempty T] {p : PMF S} {d : S → T → ℝ} {D D' : ℝ} (hD : minDist p d ≤ D)
    (h : D ≤ D') : rdf p d D' ≤ rdf p d D := by
  obtain ⟨W, hW, hI⟩ := exists_rdf_eq p d hD
  exact hI ▸ rdf_le_inputMutualInfo (hW.trans h)

theorem convexOn_rdf [Nonempty T] (p : PMF S) (d : S → T → ℝ) :
    ConvexOn ℝ (Set.Ici (minDist p d)) (rdf p d) := by
  refine ⟨convex_Ici _, fun x hx y hy a b ha hb hab => ?_⟩
  obtain ⟨W₁, hW₁, hI₁⟩ := exists_rdf_eq p d hx
  obtain ⟨W₂, hW₂, hI₂⟩ := exists_rdf_eq p d hy
  set w : S → T → ℝ := fun s t => a * (W₁ s t).toReal + b * (W₂ s t).toReal
  have hw0 : ∀ s t, 0 ≤ w s t := fun s t =>
    add_nonneg (mul_nonneg ha ENNReal.toReal_nonneg) (mul_nonneg hb ENNReal.toReal_nonneg)
  have hw1 : ∀ s, ∑ t, w s t = 1 := fun s => by
    simp only [w, sum_add_distrib, ← mul_sum, sum_toReal_pmf_eq_one, mul_one, hab]
  set W := DMC.ofMatrix w hw0 hw1
  have hW : ∀ s t, (W s t).toReal = a * (W₁ s t).toReal + b * (W₂ s t).toReal :=
    DMC.toReal_ofMatrix w hw0 hw1
  have hE : expDist p d W = a * expDist p d W₁ + b * expDist p d W₂ := by
    simp only [expDist, hW, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun s _ => sum_congr rfl fun t _ => by ring
  simp only [smul_eq_mul]
  calc rdf p d (a * x + b * y) ≤ W.inputMutualInfo p := rdf_le_inputMutualInfo (by
        rw [hE]
        exact add_le_add (mul_le_mul_of_nonneg_left hW₁ ha) (mul_le_mul_of_nonneg_left hW₂ hb))
    _ ≤ a * W₁.inputMutualInfo p + b * W₂.inputMutualInfo p :=
        DMC.inputMutualInfo_le_of_toReal_eq p ha hb hW
    _ = a * rdf p d x + b * rdf p d y := by rw [hI₁, hI₂]

theorem rateRegion_eq [Nonempty T] (p : PMF S) (d : S → T → ℝ) :
    rateRegion p d =
      {RD | ∃ W : DMC S T, expDist p d W ≤ RD.2 ∧ W.inputMutualInfo p ≤ RD.1} := by
  ext ⟨R, D⟩
  constructor
  · rintro ⟨hD, hR⟩
    obtain ⟨W, hW, hI⟩ := exists_rdf_eq p d hD
    exact ⟨W, hW, hI ▸ hR⟩
  · rintro ⟨W, hW, hI⟩
    exact ⟨(minDist_le_expDist p d W).trans hW, (rdf_le_inputMutualInfo hW).trans hI⟩

theorem isClosed_rateRegion [Nonempty T] (p : PMF S) (d : S → T → ℝ) :
    IsClosed (rateRegion p d) := by
  set P : S → ℝ := fun s => (p s).toReal
  have : CompactSpace (DMC.stoch S T) := isCompact_iff_compactSpace.1 isCompact_stoch
  set Z : Set ((ℝ × ℝ) × DMC.stoch S T) :=
    {z | distSum P d z.2.1 ≤ z.1.2 ∧ DMC.miSum P z.2.1 ≤ z.1.1}
  have hZ : IsClosed Z :=
    (isClosed_le ((continuous_distSum P d).comp (continuous_subtype_val.comp continuous_snd))
      (continuous_snd.comp continuous_fst)).inter
    (isClosed_le ((continuous_miSum P).comp (continuous_subtype_val.comp continuous_snd))
      (continuous_fst.comp continuous_fst))
  have he : rateRegion p d = Prod.fst '' Z := by
    rw [rateRegion_eq]
    ext ⟨R, D⟩
    constructor
    · rintro ⟨W, hW, hI⟩
      refine ⟨((R, D), ⟨_, mat_mem W⟩), ⟨hW, ?_⟩, rfl⟩
      rw [← DMC.inputMutualInfo_eq_miSum]
      exact hI
    · rintro ⟨⟨RD', w⟩, ⟨hE, hI⟩, rfl⟩
      set W := DMC.ofMatrix w.1 w.2.1 w.2.2
      have hmat : (fun s t => (W s t).toReal) = w.1 :=
        funext fun s => funext fun t => DMC.toReal_ofMatrix _ _ _ s t
      refine ⟨W, ?_, ?_⟩
      · change distSum P d (fun s t => (W s t).toReal) ≤ D
        rw [hmat]
        exact hE
      · rw [DMC.inputMutualInfo_eq_miSum, hmat]
        exact hI
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hZ

end RateDistortion

end Meat
