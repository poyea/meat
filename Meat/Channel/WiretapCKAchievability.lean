import Meat.Channel.WiretapCK

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace Wiretap

section Prefix

variable {A B E V : Type*}

private noncomputable def unifPMF (m : ℕ) [NeZero m] : PMF (Fin m) :=
  PMF.ofFintype (fun _ => (m : ℝ≥0∞)⁻¹) (by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp [NeZero.ne m]) (ENNReal.natCast_ne_top m))

noncomputable def prefixChannel {m : ℕ} [NeZero m] (W : DMC A (B × E)) (f : V → Fin m → A) :
    DMC V (B × E) :=
  fun v => (unifPMF m).bind fun t => W (f v t)

theorem prefixChannel_apply {m : ℕ} [NeZero m] (W : DMC A (B × E)) (f : V → Fin m → A) (v : V)
    (s : B × E) : prefixChannel W f v s = ∑ t, (m : ℝ≥0∞)⁻¹ * W (f v t) s := by
  rw [prefixChannel, PMF.bind_apply, tsum_fintype]
  rfl

private def simKey (l m n : ℕ) : Fin (l * m ^ n) ≃ Fin l × (Fin n → Fin m) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finFunctionFinEquiv.symm)

private def simCode {k l m n : ℕ} (f : V → Fin m → A) (c : WiretapCode (Fin k) (Fin l) V B n) :
    WiretapCode (Fin k) (Fin (l * m ^ n)) A B n :=
  ⟨fun u i => f (c.enc (u.1, (simKey l m n u.2).1) i) ((simKey l m n u.2).2 i), c.dec⟩

variable [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

private lemma codeMeasure_msg_out {M L : Type*} [Fintype M] [MeasurableSpace M]
    [MeasurableSingletonClass M] [Nonempty M] [Fintype L] [MeasurableSpace L]
    [MeasurableSingletonClass L] [Nonempty L]
    {n : ℕ} (c : WiretapCode M L A B n) (W : DMC A (B × E)) (a : M) (y : Fin n → B × E) :
    Interactive.codeMeasure W (c.toFn (E := E)) {ω | (ω.1.1, ω.2) = (a, y)} =
      (Fintype.card (M × L) : ℝ≥0∞)⁻¹ * ∑ l, DMC.blockProb W (c.enc (a, l)) y := by
  classical
  rw [Interactive.codeMeasure_apply, Fintype.sum_prod_type,
    sum_eq_single a (fun a' _ ha => by simp [ha]) (by simp), mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_eq_single y (fun y' _ hy => by simp [hy]) (by simp)]
  simp only [ite_true]
  rfl

private lemma map_codeMeasure_simCode {k l m n : ℕ} [NeZero k] [NeZero l] [NeZero m]
    (W : DMC A (B × E)) (f : V → Fin m → A) (c : WiretapCode (Fin k) (Fin l) V B n) :
    (Interactive.codeMeasure W ((simCode f c).toFn (E := E))).map (fun ω => (ω.1.1, ω.2)) =
      (Interactive.codeMeasure (prefixChannel W f) (c.toFn (E := E))).map
        (fun ω => (ω.1.1, ω.2)) := by
  classical
  refine Measure.ext_of_singleton fun p => ?_
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  change Interactive.codeMeasure W ((simCode f c).toFn (E := E)) {ω | (ω.1.1, ω.2) = (p.1, p.2)} =
    Interactive.codeMeasure (prefixChannel W f) (c.toFn (E := E)) {ω | (ω.1.1, ω.2) = (p.1, p.2)}
  rw [codeMeasure_msg_out, codeMeasure_msg_out, ← (simKey l m n).symm.sum_comp,
    Fintype.sum_prod_type]
  have hm : (m : ℝ≥0∞) ≠ 0 := by simp [NeZero.ne m]
  have hb : ∀ v : Fin n → V, ∑ t : Fin n → Fin m, DMC.blockProb W (fun i => f (v i) (t i)) p.2 =
      (m : ℝ≥0∞) ^ n * DMC.blockProb (prefixChannel W f) v p.2 := by
    intro v
    simp only [DMC.blockProb, prefixChannel_apply, ← mul_sum, prod_mul_distrib, prod_const,
      card_univ, Fintype.card_fin, ← mul_assoc, ← mul_pow,
      ENNReal.mul_inv_cancel hm (ENNReal.natCast_ne_top m), one_pow, one_mul]
    exact (Fintype.prod_sum fun i t => W (f (v i) t) (p.2 i)).symm
  have hs : ∀ j : Fin l, ∑ t : Fin n → Fin m,
      DMC.blockProb W ((simCode f c).enc (p.1, (simKey l m n).symm (j, t))) p.2 =
      (m : ℝ≥0∞) ^ n * DMC.blockProb (prefixChannel W f) (c.enc (p.1, j)) p.2 := fun j => by
    rw [← hb]
    refine sum_congr rfl fun t _ => ?_
    simp [simCode]
  simp only [hs, ← mul_sum]
  rw [← mul_assoc]
  congr 1
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  rw [ENNReal.mul_inv (Or.inl (by simp [NeZero.ne k])) (Or.inl (ENNReal.natCast_ne_top _)),
    ENNReal.mul_inv (Or.inl (by simp [NeZero.ne l])) (Or.inl (ENNReal.natCast_ne_top _)),
    ENNReal.mul_inv (Or.inl (by simp [NeZero.ne k])) (Or.inl (ENNReal.natCast_ne_top _))]
  rw [mul_assoc, mul_assoc, ENNReal.inv_mul_cancel (pow_ne_zero _ hm)
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top m)), mul_one]

theorem achievable_of_prefixChannel {m : ℕ} [NeZero m] (W : DMC A (B × E)) (f : V → Fin m → A)
    {R : ℝ} (h : Achievable (prefixChannel W f) R) : Achievable W R := by
  classical
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, l, _, _, hk, c, hc, hleak⟩ := hN n hn
  have : NeZero (l * m ^ n) := ⟨Nat.mul_ne_zero (NeZero.ne l) (pow_ne_zero _ (NeZero.ne m))⟩
  have hmap := map_codeMeasure_simCode (E := E) W f c
  set μ₁ := Interactive.codeMeasure W ((simCode f c).toFn (E := E))
  set μ₂ := Interactive.codeMeasure (prefixChannel W f) (c.toFn (E := E))
  refine ⟨k, l * m ^ n, inferInstance, inferInstance, hk, simCode f c, ?_, ?_⟩
  · have h1 := (simCode f c).measureReal_dec_ne W
    have h2 := c.measureReal_dec_ne (prefixChannel W f)
    have e1 : μ₁.real {ω | (simCode f c).dec (fun i => (ω.2 i).1) ≠ ω.1.1} =
        (μ₁.map fun ω => (ω.1.1, ω.2)).real {p | c.dec (fun i => (p.2 i).1) ≠ p.1} := by
      rw [map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
      rfl
    have e2 : μ₂.real {ω | c.dec (fun i => (ω.2 i).1) ≠ ω.1.1} =
        (μ₂.map fun ω => (ω.1.1, ω.2)).real {p | c.dec (fun i => (p.2 i).1) ≠ p.1} := by
      rw [map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
      rfl
    have hne : (simCode f c).avgError W ≠ ⊤ :=
      (ENNReal.div_lt_top (ENNReal.sum_ne_top.2 fun u _ => ENNReal.sum_ne_top.2 fun y _ => by
        split_ifs
        · exact ENNReal.zero_ne_top
        · exact DMC.blockProb_ne_top _ _ _) (by simp [NeZero.ne k, NeZero.ne l, NeZero.ne m])).ne
    have h3 : ((simCode f c).avgError W).toReal ≤ ε := by
      rw [← h1, e1, hmap, ← e2, h2]
      exact ENNReal.toReal_le_of_le_ofReal hε.le hc
    rw [← ENNReal.ofReal_toReal hne]
    exact ENNReal.ofReal_le_ofReal h3
  · have e1 : (simCode f c).leakage W = I[Prod.fst : fun p i => (p.2 i).2 ;
        μ₁.map fun ω => (ω.1.1, ω.2)] := by
      rw [mutualInfo_map _ (measurable_of_finite _) measurable_fst (measurable_of_finite _)]
      rfl
    have e2 : c.leakage (prefixChannel W f) = I[Prod.fst : fun p i => (p.2 i).2 ;
        μ₂.map fun ω => (ω.1.1, ω.2)] := by
      rw [mutualInfo_map _ (measurable_of_finite _) measurable_fst (measurable_of_finite _)]
      rfl
    rw [e1, hmap, ← e2]
    exact hleak

private noncomputable def prefixJoint {m : ℕ} [NeZero m] (pV : PMF V) (f : V → Fin m → A) :
    PMF (V × A) :=
  pV.bind fun v => (unifPMF m).map fun t => (v, f v t)

private lemma secrecyRate_prefixChannel [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
    {k m : ℕ} [NeZero m] (W : DMC A (B × E)) (pV : PMF (Fin k)) (f : Fin k → Fin m → A) :
    secrecyRate (prefixChannel W f) pV =
      I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.1 ;
          ckMeasure W (prefixJoint pV f)] -
        I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.2 ;
          ckMeasure W (prefixJoint pV f)] := by
  have hmap : (ckMeasure W (prefixJoint pV f)).map (fun ω => (ω.1, ω.2.2)) =
      (prefixChannel W f).jointMeasure pV := by
    rw [ckMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _), DMC.jointMeasure]
    congr 1
    simp only [prefixJoint, prefixChannel, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
      Function.comp_apply, PMF.map_comp]
    rfl
  rw [secrecyRate, ← hmap, mutualInfo_map _ (measurable_of_finite _) measurable_fst
    (measurable_of_finite _), mutualInfo_map _ (measurable_of_finite _) measurable_fst
    (measurable_of_finite _)]
  rfl

end Prefix

section Continuity

variable {A B E : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E] {k : ℕ}

open Classical in
private noncomputable def ckH {T : Type*} [Fintype T] (W : DMC A (B × E))
    (g : Fin k × A × (B × E) → T) (r : Fin k × A → ℝ) : ℝ :=
  ∑ t, Real.negMulLog (∑ va, r va * ∑ s, if g (va.1, va.2, s) = t then (W va.2 s).toReal else 0)

omit [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableSpace E] [MeasurableSingletonClass E] in
private lemma continuous_ckH {T : Type*} [Fintype T] (W : DMC A (B × E))
    (g : Fin k × A × (B × E) → T) : Continuous (ckH W g) :=
  continuous_finsetSum _ fun _ _ => Real.continuous_negMulLog.comp
    (continuous_finsetSum _ fun va _ => (continuous_apply va).mul continuous_const)

private lemma entropy_ckMeasure {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (W : DMC A (B × E)) (q : PMF (Fin k × A))
    (g : Fin k × A × (B × E) → T) :
    H[g ; ckMeasure W q] = ckH W g fun va => (q va).toReal := by
  classical
  rw [entropy_def, ckH]
  refine sum_congr rfl fun t _ => congrArg _ ?_
  have hE : (DMC.jointPMF (fun va : Fin k × A => W va.2) q).map
      (fun p => (p.1.1, p.1.2, p.2)) =
      q.bind fun va => (W va.2).map fun y => (va.1, va.2, y) := by
    simp only [DMC.jointPMF, PMF.map_bind, PMF.map_comp]
    rfl
  rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton t), ckMeasure, ← hE,
    ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet, measureReal_def,
    PMF.toMeasure_apply_fintype, Fintype.sum_prod_type,
    ENNReal.toReal_sum fun va _ => ENNReal.sum_ne_top.2 fun s _ =>
      ne_top_of_le_ne_top (PMF.apply_ne_top _ _) (Set.indicator_le_self _ _ _)]
  refine sum_congr rfl fun va _ => ?_
  rw [ENNReal.toReal_sum fun s _ =>
      ne_top_of_le_ne_top (PMF.apply_ne_top _ _) (Set.indicator_le_self _ _ _), mul_sum]
  refine sum_congr rfl fun s _ => ?_
  by_cases h : g (va.1, va.2, s) = t
  · simp [Set.indicator, h, DMC.jointPMF_apply, ENNReal.toReal_mul]
  · simp [Set.indicator, h]

private noncomputable def ckRateFun (W : DMC A (B × E)) (r : Fin k × A → ℝ) : ℝ :=
  ckH W (fun ω : Fin k × A × (B × E) => ω.2.2.1) r -
    ckH W (fun ω : Fin k × A × (B × E) => (ω.1, ω.2.2.1)) r -
    ckH W (fun ω : Fin k × A × (B × E) => ω.2.2.2) r +
    ckH W (fun ω : Fin k × A × (B × E) => (ω.1, ω.2.2.2)) r

private lemma ckRate_eq (W : DMC A (B × E)) (q : PMF (Fin k × A)) :
    I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.1 ; ckMeasure W q] -
      I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.2 ; ckMeasure W q] =
      ckRateFun W fun va => (q va).toReal := by
  simp only [mutualInfo_def, entropy_ckMeasure, ckRateFun]
  ring

omit [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableSpace E] [MeasurableSingletonClass E] in
private lemma continuous_ckRateFun (W : DMC A (B × E)) : Continuous (ckRateFun (k := k) W) :=
  (((continuous_ckH W _).sub (continuous_ckH W _)).sub (continuous_ckH W _)).add
    (continuous_ckH W _)

end Continuity

section Approx

variable {A : Type*} [Fintype A] {k : ℕ}

private noncomputable def fiberFun {m : ℕ} (c : A → ℕ) (hc : ∑ x, c x = m) : Fin m → A :=
  fun t => ((Fintype.equivFinOfCardEq (α := Σ x, Fin (c x))
    (by rw [Fintype.card_sigma]; simpa using hc)).symm t).1

private lemma sum_fiberFun {m : ℕ} (c : A → ℕ) (hc : ∑ x, c x = m) {M : Type*} [AddCommMonoid M]
    (g : A → M) : ∑ t, g (fiberFun c hc t) = ∑ x, c x • g x := by
  unfold fiberFun
  rw [Equiv.sum_comp _ (fun s : Σ x, Fin (c x) => g s.1), Fintype.sum_sigma]
  simp

open Classical in
omit [Fintype A] in
private lemma prefixJoint_apply {V : Type*} [Finite V] {m : ℕ} [NeZero m] (pV : PMF V)
    (f : V → Fin m → A) (v : V) (x : A) :
    prefixJoint pV f (v, x) = pV v * ∑ t, if f v t = x then (m : ℝ≥0∞)⁻¹ else 0 := by
  classical
  have := Fintype.ofFinite V
  rw [prefixJoint, PMF.bind_apply, tsum_fintype,
    sum_eq_single v (fun v' _ hv => by simp [PMF.map_apply, Ne.symm hv]) (by simp),
    PMF.map_apply, tsum_fintype]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  by_cases h : f v t = x
  · simp [h, unifPMF]
  · simp [Ne.symm h, h]

private noncomputable def apxK (q : PMF (Fin k × A)) (v : Fin k) (x : A) : ℝ :=
  (q (v, x)).toReal / ((q.map Prod.fst) v).toReal

open Classical in
private noncomputable def apxCnt (q : PMF (Fin k × A)) (x₀ : A) (N : ℕ) (v : Fin k) (x : A) : ℕ :=
  if x = x₀ then N - ∑ x' ∈ univ.erase x₀, ⌊apxK q v x' * N⌋₊ else ⌊apxK q v x * N⌋₊

private lemma map_fst_toReal (q : PMF (Fin k × A)) (v : Fin k) :
    ((q.map Prod.fst) v).toReal = ∑ x, (q (v, x)).toReal := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    sum_eq_single v (fun v' _ hv => by simp [Ne.symm hv]) (by simp),
    ← ENNReal.toReal_sum fun x _ => PMF.apply_ne_top _ _]
  simp

omit [Fintype A] in
private lemma apxK_nonneg (q : PMF (Fin k × A)) (v : Fin k) (x : A) : 0 ≤ apxK q v x :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

private lemma sum_apxK_le (q : PMF (Fin k × A)) (v : Fin k) : ∑ x, apxK q v x ≤ 1 := by
  simp only [apxK]
  rw [← sum_div, ← map_fst_toReal]
  exact div_self_le_one _

private lemma sum_floor_le (q : PMF (Fin k × A)) [DecidableEq A] (x₀ : A) (N : ℕ) (v : Fin k) :
    ∑ x' ∈ univ.erase x₀, ⌊apxK q v x' * N⌋₊ ≤ N := by
  have h : (∑ x' ∈ univ.erase x₀, ⌊apxK q v x' * N⌋₊ : ℝ) ≤ N :=
    calc (∑ x' ∈ univ.erase x₀, ⌊apxK q v x' * N⌋₊ : ℝ)
        ≤ ∑ x' ∈ univ.erase x₀, apxK q v x' * N :=
          sum_le_sum fun x' _ => Nat.floor_le (mul_nonneg (apxK_nonneg q v x') (Nat.cast_nonneg N))
      _ ≤ ∑ x', apxK q v x' * N :=
          sum_le_univ_sum_of_nonneg fun x' => mul_nonneg (apxK_nonneg q v x') (Nat.cast_nonneg N)
      _ ≤ N := by
          rw [← sum_mul]
          exact mul_le_of_le_one_left (Nat.cast_nonneg N) (sum_apxK_le q v)
  exact_mod_cast h

private lemma sum_apxCnt (q : PMF (Fin k × A)) (x₀ : A) (N : ℕ) (v : Fin k) :
    ∑ x, apxCnt q x₀ N v x = N := by
  classical
  have h0 : apxCnt q x₀ N v x₀ = N - ∑ x' ∈ univ.erase x₀, ⌊apxK q v x' * N⌋₊ := by
    simp [apxCnt]
  have h1 : ∀ x ∈ univ.erase x₀, apxCnt q x₀ N v x = ⌊apxK q v x * N⌋₊ := fun x hx => by
    simp [apxCnt, ne_of_mem_erase hx]
  rw [← add_sum_erase _ _ (mem_univ x₀), h0, sum_congr rfl h1]
  exact Nat.sub_add_cancel (sum_floor_le q x₀ N v)

private lemma toReal_prefixJoint_apx (q : PMF (Fin k × A)) (x₀ : A) (N : ℕ) [NeZero N] (v : Fin k)
    (x : A) :
    (prefixJoint (q.map Prod.fst) (fun v => fiberFun (apxCnt q x₀ N v) (sum_apxCnt q x₀ N v))
      (v, x)).toReal = ((q.map Prod.fst) v).toReal * ((apxCnt q x₀ N v x : ℝ) / N) := by
  classical
  rw [prefixJoint_apply, sum_fiberFun _ _ (fun y => if y = x then (N : ℝ≥0∞)⁻¹ else 0)]
  simp only [smul_ite, smul_zero, sum_ite_eq', mem_univ, ite_true, nsmul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv, div_eq_mul_inv]

open Classical in
private lemma tendsto_apxCnt (q : PMF (Fin k × A)) (x₀ : A) (v : Fin k) (x : A) :
    Tendsto (fun m : ℕ => (apxCnt q x₀ (m + 1) v x : ℝ) / ((m + 1 : ℕ) : ℝ)) atTop
      (𝓝 (if x = x₀ then 1 - ∑ x' ∈ univ.erase x₀, apxK q v x' else apxK q v x)) := by
  have hfl : ∀ x', Tendsto (fun m : ℕ => (⌊apxK q v x' * ((m + 1 : ℕ) : ℝ)⌋₊ : ℝ) /
      ((m + 1 : ℕ) : ℝ)) atTop (𝓝 (apxK q v x')) := fun x' =>
    ((tendsto_nat_floor_mul_div_atTop (apxK_nonneg q v x')).comp
      tendsto_natCast_atTop_atTop).comp (tendsto_add_atTop_nat 1)
  by_cases hx : x = x₀
  · subst hx
    rw [ite_eq_left_of_eq_true _ _ (eq_self x)]
    refine ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_finsetSum _ fun x' _ => hfl x')).congr
      fun m => ?_
    have hN : ((m + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)
    simp only [apxCnt, ite_true]
    rw [Nat.cast_sub (sum_floor_le q x (m + 1) v), Nat.cast_sum, sub_div, div_self hN, sum_div]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
    refine (hfl x).congr fun m => ?_
    simp only [apxCnt, hx, ite_false]

open Classical in
private lemma mul_apx_limit (q : PMF (Fin k × A)) (x₀ : A) (v : Fin k) (x : A) :
    ((q.map Prod.fst) v).toReal *
      (if x = x₀ then 1 - ∑ x' ∈ univ.erase x₀, apxK q v x' else apxK q v x) =
      (q (v, x)).toReal := by
  simp only [apxK, map_fst_toReal]
  have hQ : ∀ y, 0 ≤ (q (v, y)).toReal := fun y => ENNReal.toReal_nonneg
  rcases eq_or_ne (∑ y, (q (v, y)).toReal) 0 with h0 | h0
  · rw [h0, zero_mul, (sum_eq_zero_iff_of_nonneg fun y _ => hQ y).1 h0 x (mem_univ x)]
  by_cases hx : x = x₀
  · subst hx
    rw [ite_eq_left_of_eq_true _ _ (eq_self x), mul_sub, mul_one, mul_sum,
      sum_congr rfl fun y _ => mul_div_cancel₀ _ h0, ← add_sum_erase _ _ (mem_univ x)]
    ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hx), mul_div_cancel₀ _ h0]

private lemma tendsto_prefixJoint_apx (q : PMF (Fin k × A)) (x₀ : A) (va : Fin k × A) :
    Tendsto (fun m : ℕ => (prefixJoint (q.map Prod.fst)
      (fun v => fiberFun (apxCnt q x₀ (m + 1) v) (sum_apxCnt q x₀ (m + 1) v)) va).toReal) atTop
      (𝓝 (q va).toReal) := by
  classical
  have h := (tendsto_const_nhds (x := ((q.map Prod.fst) va.1).toReal)).mul
    (tendsto_apxCnt q x₀ va.1 va.2)
  rw [mul_apx_limit] at h
  exact h.congr fun m => (toReal_prefixJoint_apx q x₀ (m + 1) va.1 va.2).symm

end Approx

section Main

variable {A B E : Type*} [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

theorem achievable_of_lt_ckCapacity [Nonempty A] (W : DMC A (B × E)) {R : ℝ} (hR0 : 0 ≤ R)
    (h : R < ckCapacity W) : Achievable W R := by
  have := Fintype.ofFinite A
  obtain ⟨k, hk⟩ := exists_lt_of_lt_ciSup h
  have : Nonempty (PMF (Fin k × A)) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    rw [Real.iSup_of_isEmpty] at hk
    linarith
  obtain ⟨q, hq⟩ := exists_lt_of_lt_ciSup hk
  set x₀ := Classical.arbitrary A
  rw [ckRate_eq] at hq
  have ht := ((continuous_ckRateFun W).tendsto _).comp
    (tendsto_pi_nhds.2 (tendsto_prefixJoint_apx q x₀))
  obtain ⟨m, hm⟩ := (ht.eventually (lt_mem_nhds hq)).exists
  rw [Function.comp_apply, ← ckRate_eq, ← secrecyRate_prefixChannel] at hm
  exact achievable_of_prefixChannel W _ (achievable_of_lt _ _ hR0 hm)

theorem closure_achievable_eq_ckCapacity [Nonempty A] (W : DMC A (B × E)) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable W R} = Set.Icc 0 (ckCapacity W) := by
  have := Fintype.ofFinite A
  refine subset_antisymm (closure_minimal
    (fun R hR => ⟨hR.1, le_ckCapacity_of_achievable W hR.2⟩) isClosed_Icc) ?_
  intro R hR
  rcases (hR.1.trans hR.2).eq_or_lt with h | h
  · rw [← h, Set.Icc_self, Set.mem_singleton_iff] at hR
    exact subset_closure ⟨hR.symm ▸ le_rfl, hR ▸ achievable_zero _⟩
  · rw [← closure_Ico h.ne] at hR
    refine closure_mono (fun R (hR : R ∈ Set.Ico 0 (ckCapacity W)) => ?_) hR
    exact ⟨hR.1, achievable_of_lt_ckCapacity W hR.1 hR.2⟩

end Main

end Wiretap

end Meat
