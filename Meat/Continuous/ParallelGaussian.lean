import Meat.Continuous.AWGNCapacity
import Meat.Continuous.AWGNConverse
import Meat.Continuous.WaterFilling

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Meat

namespace AWGN

theorem achievable_of_lt {P N R : ℝ} (hP : 0 ≤ P) (hN : 0 < N) (hR : 0 ≤ R)
    (hRC : R < awgnCapacity P N) : Achievable P N R := by
  obtain ⟨L, s, t, a, q, p, hL, ha, hq, hI⟩ := exists_blockQuantization hP hN R hR hRC
  exact achievable_of_lt_inputMutualInfo_blockChannel hP hR hL a ha q hq p hI

end AWGN

namespace Parallel

variable {ι : Type*} [Fintype ι]

noncomputable def noise (N : ι → ℝ) (n : ℕ) : Measure (ι → Fin n → ℝ) :=
  Measure.pi fun i => AWGN.noise (N i) n

instance isProbabilityMeasure_noise (N : ι → ℝ) (n : ℕ) : IsProbabilityMeasure (noise N n) := by
  unfold noise
  infer_instance

variable (ι) in
structure Code (P : ℝ) (n k : ℕ) where
  enc : Fin k → ι → Fin n → ℝ
  power : ∀ m, ∑ i, ∑ t, enc m i t ^ 2 ≤ n * P
  dec : (ι → Fin n → ℝ) → Fin k
  measurable_dec : Measurable dec

namespace Code

variable {P : ℝ} {n k : ℕ}

noncomputable def errorProb (c : Code ι P n k) (N : ι → ℝ) (m : Fin k) : ℝ≥0∞ :=
  noise N n {z | c.dec (c.enc m + z) ≠ m}

noncomputable def avgError (c : Code ι P n k) (N : ι → ℝ) : ℝ≥0∞ :=
  (∑ m, c.errorProb N m) / k

end Code

def Achievable (P : ℝ) (N : ι → ℝ) (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : Code ι P n k, c.avgError N ≤ ε

theorem achievable_zero {P : ℝ} (hP : 0 ≤ P) (N : ι → ℝ) : Achievable P N 0 := by
  intro ε _
  refine ⟨0, fun n _ => ⟨1, by simp, ⟨fun _ _ _ => 0, fun _ => by
    simpa using mul_nonneg n.cast_nonneg hP,
    fun _ => 0, measurable_const⟩, ?_⟩⟩
  simp [Code.avgError, Code.errorProb, Subsingleton.elim _ (0 : Fin 1)]

section Product

variable [DecidableEq ι] {n : ℕ} {k : ι → ℕ} {Q : ι → ℝ}

noncomputable def prodEquiv (k : ι → ℕ) : (∀ i, Fin (k i)) ≃ Fin (∏ i, k i) :=
  Fintype.equivFinOfCardEq (by simp [Fintype.card_pi])

noncomputable def productCode (c : ∀ i, AWGN.Code (Q i) n (k i)) {P : ℝ}
    (hQ : ∑ i, Q i ≤ P) : Code ι P n (∏ i, k i) where
  enc m i t := (c i).enc ((prodEquiv k).symm m i) t
  power m := by
    calc ∑ i, ∑ t, (c i).enc ((prodEquiv k).symm m i) t ^ 2 ≤ ∑ i, n * Q i :=
          sum_le_sum fun i _ => (c i).power _
      _ = n * ∑ i, Q i := by rw [mul_sum]
      _ ≤ n * P := mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg n)
  dec z := prodEquiv k fun i => (c i).dec (z i)
  measurable_dec := (measurable_of_countable _).comp
    (measurable_pi_iff.2 fun i => (c i).measurable_dec.comp (measurable_pi_apply i))

theorem errorProb_productCode_le (c : ∀ i, AWGN.Code (Q i) n (k i)) {P : ℝ}
    (hQ : ∑ i, Q i ≤ P) (N : ι → ℝ) (m : Fin (∏ i, k i)) :
    (productCode c hQ).errorProb N m ≤
      ∑ i, (c i).errorProb (N i) ((prodEquiv k).symm m i) := by
  have hsub : {z : ι → Fin n → ℝ | (productCode c hQ).dec ((productCode c hQ).enc m + z) ≠ m} ⊆
      ⋃ i, (fun z : ι → Fin n → ℝ => z i) ⁻¹'
        {w | (c i).dec ((c i).enc ((prodEquiv k).symm m i) + w) ≠ (prodEquiv k).symm m i} := by
    intro z hz
    by_contra h
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists] at h
    apply hz
    have h' : ∀ i, (c i).dec ((c i).enc ((prodEquiv k).symm m i) + z i) =
        (prodEquiv k).symm m i := fun i => by simpa using h i
    have e : (productCode c hQ).dec ((productCode c hQ).enc m + z) =
        prodEquiv k fun i => (c i).dec ((c i).enc ((prodEquiv k).symm m i) + z i) := rfl
    rw [e, funext h', Equiv.apply_symm_apply]
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
    (le_of_eq (sum_congr rfl fun i _ => ?_)))
  have hs : MeasurableSet {w : Fin n → ℝ | (c i).dec ((c i).enc ((prodEquiv k).symm m i) + w) ≠
      (prodEquiv k).symm m i} :=
    ((c i).measurable_dec_add _) (measurableSet_singleton _).compl
  exact (measurePreserving_eval (fun i => AWGN.noise (N i) n) i).measure_preimage
    hs.nullMeasurableSet

theorem avgError_productCode_le (c : ∀ i, AWGN.Code (Q i) n (k i)) {P : ℝ}
    (hQ : ∑ i, Q i ≤ P) (N : ι → ℝ) (hk : ∀ i, 0 < k i) :
    (productCode c hQ).avgError N ≤ ∑ i, (c i).avgError (N i) := by
  classical
  have hK : ((∏ i, k i : ℕ) : ℝ≥0∞) = Fintype.card (∀ i, Fin (k i)) := by
    simp [Fintype.card_pi]
  have hsum : ∑ m, (productCode c hQ).errorProb N m ≤
      ∑ a : ∀ i, Fin (k i), ∑ i, (c i).errorProb (N i) (a i) := by
    rw [← (prodEquiv k).sum_comp]
    refine sum_le_sum fun a _ => ?_
    have := errorProb_productCode_le c hQ N (prodEquiv k a)
    simpa using this
  have hi : ∀ i, (∑ a : ∀ j, Fin (k j), (c i).errorProb (N i) (a i)) /
      Fintype.card (∀ j, Fin (k j)) = (c i).avgError (N i) := by
    intro i
    set e := Equiv.piSplitAt i fun j => Fin (k j)
    have : Nonempty (∀ j : {j // j ≠ i}, Fin (k j)) := ⟨fun j => ⟨0, hk j.1⟩⟩
    have hr : Fintype.card (∀ j : {j // j ≠ i}, Fin (k j)) ≠ 0 :=
      Fintype.card_ne_zero (α := ∀ j : {j // j ≠ i}, Fin (k j))
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Fintype.card_congr e, Fintype.card_prod,
      Fintype.card_fin]
    have hx : ∀ x y, e.symm (x, y) i = x := fun x y => by simp [e, Equiv.piSplitAt]
    simp only [hx, sum_const, card_univ, nsmul_eq_mul]
    rw [← mul_sum, Nat.cast_mul, mul_comm _ (∑ x, _),
      ENNReal.mul_div_mul_right _ _ (by exact_mod_cast hr) (ENNReal.natCast_ne_top _)]
    rfl
  calc (productCode c hQ).avgError N = (∑ m, (productCode c hQ).errorProb N m) /
        (Fintype.card (∀ i, Fin (k i)) : ℝ≥0∞) := by rw [Code.avgError, hK]
    _ ≤ (∑ a : ∀ i, Fin (k i), ∑ i, (c i).errorProb (N i) (a i)) /
        (Fintype.card (∀ i, Fin (k i)) : ℝ≥0∞) := by gcongr
    _ = ∑ i, (c i).avgError (N i) := by
        rw [sum_comm, ENNReal.sum_div]
        exact sum_congr rfl fun i _ => hi i

end Product

section Rates

theorem achievable_of_lt [Nonempty ι] {P : ℝ} {N : ι → ℝ} (hP : 0 ≤ P) (hN : ∀ i, 0 < N i)
    {R : ℝ} (hRC : R < WaterFilling.capacity N P) : Achievable P N R := by
  classical
  obtain ⟨ν, hν, -, hfill, -, -, -, -⟩ := WaterFilling.exists_waterFilling hN hP
  rw [WaterFilling.capacity_eq hN hν hfill] at hRC
  set p := WaterFilling.fill N ν
  set C : ι → ℝ := fun i => awgnCapacity (p i) (N i)
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  set δ := (WaterFilling.rate N p - R) / Fintype.card ι
  have hδ : 0 < δ := div_pos (by linarith) hcard
  set Ri : ι → ℝ := fun i => max (C i - δ) 0
  have hach : ∀ i, AWGN.Achievable (p i) (N i) (Ri i) := by
    intro i
    by_cases h : C i - δ ≤ 0
    · rw [show Ri i = 0 from max_eq_right h]
      exact AWGN.achievable_zero (WaterFilling.fill_nonneg N ν i) _
    · push Not at h
      rw [show Ri i = C i - δ from max_eq_left h.le]
      exact AWGN.achievable_of_lt (WaterFilling.fill_nonneg N ν i) (hN i) h.le (by linarith)
  have hsumR : R ≤ ∑ i, Ri i := by
    have h1 : ∑ i, (C i - δ) ≤ ∑ i, Ri i := sum_le_sum fun i _ => le_max_left _ _
    rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at h1
    have e : (Fintype.card ι : ℝ) * δ = WaterFilling.rate N p - R := by
      simp only [δ]
      field_simp
    have e2 : ∑ i, C i = WaterFilling.rate N p := rfl
    linarith
  intro ε hε
  set ε' := ε / Fintype.card ι
  have hε' : 0 < ε' := ENNReal.div_pos hε.ne' (ENNReal.natCast_ne_top _)
  choose n₀ hn₀ using fun i => hach i ε' hε'
  refine ⟨univ.sup n₀, fun n hn => ?_⟩
  have hni : ∀ i, n₀ i ≤ n := fun i => (le_sup (f := n₀) (mem_univ i)).trans hn
  choose k hk c hc using fun i => hn₀ i n (hni i)
  have hk0 : ∀ i, 0 < k i := fun i => Nat.cast_pos.1 ((Real.exp_pos _).trans_le (hk i))
  refine ⟨∏ i, k i, ?_, productCode c hfill.le, ?_⟩
  · rw [Nat.cast_prod]
    calc Real.exp (n * R) ≤ Real.exp (n * ∑ i, Ri i) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsumR (Nat.cast_nonneg n))
      _ = ∏ i, Real.exp (n * Ri i) := by rw [mul_sum, Real.exp_sum]
      _ ≤ _ := prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) fun i _ => hk i
  · calc _ ≤ ∑ i, (c i).avgError (N i) := avgError_productCode_le c hfill.le N hk0
      _ ≤ ∑ _i : ι, ε' := sum_le_sum fun i _ => hc i
      _ = ε := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          exact ENNReal.mul_div_cancel (by simp) (ENNReal.natCast_ne_top _)

end Rates

theorem sum_awgnCapacity_le [Nonempty ι] {P : ℝ} {N : ι → ℝ} (hP : 0 ≤ P)
    (hN : ∀ i, 0 < N i) {n : ℕ} (Pb : ι → Fin n → ℝ) (hPb : ∀ i t, 0 ≤ Pb i t)
    (hsum : ∑ i, ∑ t, Pb i t ≤ n * P) :
    ∑ i, ∑ t, awgnCapacity (Pb i t) (N i) ≤ n * WaterFilling.capacity N P := by
  obtain ⟨ν, hν, -, hfill, -, -, -, -⟩ := WaterFilling.exists_waterFilling hN hP
  set N' : ι × Fin n → ℝ := fun q => N q.1
  have hfill' : ∑ q, WaterFilling.fill N' ν q = n * P := by
    rw [Fintype.sum_prod_type]
    simp only [N', WaterFilling.fill, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_sum, ← hfill]
    rfl
  have hfeas : WaterFilling.Feasible (n * P) fun q : ι × Fin n => Pb q.1 q.2 :=
    ⟨fun q => hPb q.1 q.2, by rw [Fintype.sum_prod_type]; exact hsum⟩
  have h := (WaterFilling.rate_le_rate_fill (fun q => hN q.1) hν hfill' hfeas).1
  have e1 : WaterFilling.rate N' (fun q : ι × Fin n => Pb q.1 q.2) =
      ∑ i, ∑ t, awgnCapacity (Pb i t) (N i) := by
    rw [WaterFilling.rate, Fintype.sum_prod_type]
  have e2 : WaterFilling.rate N' (WaterFilling.fill N' ν) =
      n * WaterFilling.rate N (WaterFilling.fill N ν) := by
    rw [WaterFilling.rate, Fintype.sum_prod_type, WaterFilling.rate, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have hy : ∀ y : Fin n, awgnCapacity (WaterFilling.fill N' ν (i, y)) (N' (i, y)) =
        awgnCapacity (WaterFilling.fill N ν i) (N i) := fun y => rfl
    rw [sum_congr rfl fun y _ => hy y, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [e1, e2, ← WaterFilling.capacity_eq hN hν hfill] at h
  exact h

private noncomputable def llr (x N S t : ℝ) : ℝ :=
  1 / 2 * Real.log (S / N) - (t - x) ^ 2 / (2 * N) + t ^ 2 / (2 * S)

private lemma measurable_llr (x N S : ℝ) : Measurable (llr x N S) := by
  unfold llr
  fun_prop

private lemma gaussianReal_eq_withDensity (x : ℝ) {N S : ℝ} (hN : 0 < N) (hS : 0 < S) :
    gaussianReal x N.toNNReal = (gaussianReal 0 S.toNNReal).withDensity
      fun t => ENNReal.ofReal (Real.exp (llr x N S t)) := by
  have hm : Measurable fun t => ENNReal.ofReal (Real.exp (llr x N S t)) :=
    (Real.measurable_exp.comp (measurable_llr x N S)).ennreal_ofReal
  rw [gaussianReal_of_var_ne_zero _ (by simpa using hN), gaussianReal_of_var_ne_zero _
    (by simpa using hS), ← withDensity_mul _ (measurable_gaussianPDF _ _) hm]
  congr 1
  funext t
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal_def, Real.coe_toNNReal _ hN.le, Real.coe_toNNReal _ hS.le, llr]
  have hs : Real.exp (1 / 2 * Real.log (S / N)) = √S / √N := by
    rw [← Real.sqrt_div hS.le, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos hS hN), mul_comm]
  rw [Real.exp_add, Real.exp_sub, hs, Real.sqrt_mul (by positivity) S,
    Real.sqrt_mul (by positivity) N]
  have hSp : 0 < √S := Real.sqrt_pos.2 hS
  have hNp : 0 < √N := Real.sqrt_pos.2 hN
  have hpi : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  field_simp
  rw [← Real.exp_add, ← Real.exp_add]
  ring_nf

private lemma integrable_sq_sub (x c : ℝ) (v : ℝ≥0) :
    Integrable (fun t => (t - c) ^ 2) (gaussianReal x v) :=
  ((memLp_id_gaussianReal 2).sub (memLp_const c)).integrable_sq

private lemma integrable_id' (x : ℝ) (v : ℝ≥0) : Integrable (fun t : ℝ => t) (gaussianReal x v) :=
  (memLp_id_gaussianReal 1).integrable le_rfl

private lemma integral_sq_sub (x : ℝ) (v : ℝ≥0) : ∫ t, (t - x) ^ 2 ∂gaussianReal x v = v := by
  have h := variance_id_gaussianReal (μ := x) (v := v)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

private lemma integral_sq (x : ℝ) (v : ℝ≥0) : ∫ t, t ^ 2 ∂gaussianReal x v = v + x ^ 2 := by
  have h : (fun t : ℝ => t ^ 2) = fun t => (t - x) ^ 2 + 2 * x * t - x ^ 2 :=
    funext fun t => by ring
  have i1 : Integrable (fun t : ℝ => (t - x) ^ 2 + 2 * x * t) (gaussianReal x v) :=
    (integrable_sq_sub x x v).add ((integrable_id' x v).const_mul _)
  rw [h, integral_sub i1 (integrable_const _), integral_add (integrable_sq_sub x x v)
    ((integrable_id' x v).const_mul _), integral_const_mul, integral_sq_sub,
    integral_id_gaussianReal]
  simp
  ring

private lemma integrable_sq (x : ℝ) (v : ℝ≥0) :
    Integrable (fun t : ℝ => t ^ 2) (gaussianReal x v) := by
  simpa using integrable_sq_sub x 0 v

private lemma integrable_llr (x : ℝ) (N S : ℝ) (v : ℝ≥0) :
    Integrable (llr x N S) (gaussianReal x v) :=
  ((integrable_const _).sub ((integrable_sq_sub x x v).div_const _)).add
    ((integrable_sq x v).div_const (2 * S))

private lemma integral_llr (x : ℝ) {N S : ℝ} (hN : 0 < N) :
    ∫ t, llr x N S t ∂gaussianReal x N.toNNReal
      = 1 / 2 * Real.log (S / N) - 1 / 2 + (x ^ 2 + N) / (2 * S) := by
  unfold llr
  have i1 : Integrable (fun t => 1 / 2 * Real.log (S / N) - (t - x) ^ 2 / (2 * N))
      (gaussianReal x N.toNNReal) :=
    (integrable_const _).sub ((integrable_sq_sub x x _).div_const _)
  rw [integral_add i1 ((integrable_sq x _).div_const (2 * S)),
    integral_sub (integrable_const _) ((integrable_sq_sub x x _).div_const _), integral_div,
    integral_div, integral_sq_sub, integral_sq, integral_const]
  simp only [Real.coe_toNNReal _ hN.le, probReal_univ, smul_eq_mul, one_mul]
  field_simp
  ring

theorem map_noise_add (N : ι → ℝ) {n : ℕ} (x : ι → Fin n → ℝ) :
    (noise N n).map (fun z => x + z) =
      Measure.pi fun i => Measure.pi fun t => gaussianReal (x i t) (N i).toNNReal := by
  have h : (fun z : ι → Fin n → ℝ => x + z) = fun z i => (fun w => x i + w) (z i) := rfl
  have : ∀ i, SigmaFinite ((AWGN.noise (N i) n).map fun w => x i + w) := fun i => by
    rw [AWGN.map_noise_add]
    infer_instance
  rw [noise, h, Measure.pi_map_pi fun i => (measurable_const_add (x i)).aemeasurable]
  congr 1
  funext i
  exact AWGN.map_noise_add (x i)

private lemma pi_gaussianReal_eq_withDensity {N : ℝ} (hN : 0 < N) {n : ℕ} (x S : Fin n → ℝ)
    (hS : ∀ t, 0 < S t) : (Measure.pi fun t => gaussianReal (x t) N.toNNReal)
      = (Measure.pi fun t => gaussianReal 0 (S t).toNNReal).withDensity
        fun z => ENNReal.ofReal (Real.exp (∑ t, llr (x t) N (S t) (z t))) := by
  set g : Fin n → ℝ → ℝ≥0∞ := fun t u => ENNReal.ofReal (Real.exp (llr (x t) N (S t) u))
  have hg : ∀ t, Measurable (g t) := fun t =>
    (Real.measurable_exp.comp (measurable_llr _ _ _)).ennreal_ofReal
  have hw : ∀ t, gaussianReal (x t) N.toNNReal
      = (gaussianReal 0 (S t).toNNReal).withDensity (g t) :=
    fun t => gaussianReal_eq_withDensity (x t) hN (hS t)
  have : ∀ t, SigmaFinite ((gaussianReal 0 (S t).toNNReal).withDensity (g t)) := fun t => by
    rw [← hw t]
    infer_instance
  rw [show (fun t => gaussianReal (x t) N.toNNReal) = fun t =>
    (gaussianReal 0 (S t).toNNReal).withDensity (g t) from funext hw, pi_withDensity _ _ hg]
  congr 1
  funext z
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun t _ => (Real.exp_pos _).le]

private lemma pi_pi_eq_withDensity {N : ι → ℝ} (hN : ∀ i, 0 < N i) {n : ℕ}
    (x S : ι → Fin n → ℝ) (hS : ∀ i t, 0 < S i t) :
    (Measure.pi fun i => Measure.pi fun t => gaussianReal (x i t) (N i).toNNReal)
      = (Measure.pi fun i => Measure.pi fun t => gaussianReal 0 (S i t).toNNReal).withDensity
        fun z => ENNReal.ofReal (Real.exp (∑ i, ∑ t, llr (x i t) (N i) (S i t) (z i t))) := by
  set g : ι → (Fin n → ℝ) → ℝ≥0∞ := fun i w =>
    ENNReal.ofReal (Real.exp (∑ t, llr (x i t) (N i) (S i t) (w t)))
  have hg : ∀ i, Measurable (g i) := fun i =>
    (Real.measurable_exp.comp (Finset.measurable_sum _ fun t _ =>
      (measurable_llr _ _ _).comp (measurable_pi_apply t))).ennreal_ofReal
  have hw : ∀ i, (Measure.pi fun t => gaussianReal (x i t) (N i).toNNReal)
      = (Measure.pi fun t => gaussianReal 0 (S i t).toNNReal).withDensity (g i) :=
    fun i => pi_gaussianReal_eq_withDensity (hN i) (x i) (S i) (hS i)
  have : ∀ i, SigmaFinite ((Measure.pi fun t => gaussianReal 0 (S i t).toNNReal).withDensity
      (g i)) := fun i => by
    rw [← hw i]
    infer_instance
  rw [show (fun i => Measure.pi fun t => gaussianReal (x i t) (N i).toNNReal) = fun i =>
    (Measure.pi fun t => gaussianReal 0 (S i t).toNNReal).withDensity (g i) from funext hw,
    pi_withDensity _ _ hg]
  congr 1
  funext z
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]

theorem map_noise_add_absolutelyContinuous {N : ι → ℝ} (hN : ∀ i, 0 < N i) {n : ℕ}
    (x S : ι → Fin n → ℝ) (hS : ∀ i t, 0 < S i t) :
    (noise N n).map (fun z => x + z) ≪
      Measure.pi fun i => Measure.pi fun t => gaussianReal 0 (S i t).toNNReal := by
  rw [map_noise_add, pi_pi_eq_withDensity hN x S hS]
  exact withDensity_absolutelyContinuous _ _

theorem sum_mul_log_sub_log_le {N : ι → ℝ} (hN : ∀ i, 0 < N i) {n : ℕ}
    (x S : ι → Fin n → ℝ) (hS : ∀ i t, 0 < S i t) {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] {d : (ι → Fin n → ℝ) → J} (hd : Measurable d) :
    ∑ j, ((noise N n).map (fun z => x + z)).real (d ⁻¹' {j})
      * (Real.log (((noise N n).map (fun z => x + z)).real (d ⁻¹' {j}))
        - Real.log ((Measure.pi fun i => Measure.pi fun t =>
            gaussianReal 0 (S i t).toNNReal).real (d ⁻¹' {j})))
      ≤ ∑ i, ∑ t, (1 / 2 * Real.log (S i t / N i) - 1 / 2 +
          (x i t ^ 2 + N i) / (2 * S i t)) := by
  rw [map_noise_add]
  have hμ := pi_pi_eq_withDensity hN x S hS
  have hLm : Measurable fun z : ι → Fin n → ℝ => ∑ i, ∑ t, llr (x i t) (N i) (S i t) (z i t) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun t _ =>
      (measurable_llr _ _ _).comp ((measurable_pi_apply t).comp (measurable_pi_apply i))
  have hi : ∀ i t, Integrable (fun z : ι → Fin n → ℝ => llr (x i t) (N i) (S i t) (z i t))
      (Measure.pi fun i => Measure.pi fun t => gaussianReal (x i t) (N i).toNNReal) :=
    fun i t => integrable_comp_eval
      (μ := fun i => Measure.pi fun t => gaussianReal (x i t) (N i).toNNReal) (i := i)
      (f := fun w : Fin n → ℝ => llr (x i t) (N i) (S i t) (w t))
      (integrable_comp_eval (μ := fun t => gaussianReal (x i t) (N i).toNNReal) (i := t)
        (integrable_llr _ _ _ _))
  have hint : Integrable (fun z : ι → Fin n → ℝ => ∑ i, ∑ t,
      llr (x i t) (N i) (S i t) (z i t))
      (Measure.pi fun i => Measure.pi fun t => gaussianReal (x i t) (N i).toNNReal) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun t _ => hi i t
  refine (sum_mul_log_sub_log_le_integral hLm hμ hint hd).trans_eq ?_
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun t _ => hi i t]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun t _ => hi i t]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 := integral_comp_eval
    (μ := fun i => Measure.pi fun t => gaussianReal (x i t) (N i).toNNReal) (i := i)
    (f := fun w : Fin n → ℝ => llr (x i t) (N i) (S i t) (w t))
    ((measurable_llr _ _ _).comp (measurable_pi_apply t)).aestronglyMeasurable
  have h2 := integral_comp_eval (μ := fun t => gaussianReal (x i t) (N i).toNNReal) (i := t)
    (f := llr (x i t) (N i) (S i t)) (measurable_llr _ _ _).aestronglyMeasurable
  exact h1.trans (h2.trans (integral_llr _ (hN i)))

private lemma avg_aux {k : ℕ} (hk : 0 < k) {N : ℝ} (hN : 0 < N) (x : Fin k → ℝ)
    {Pb : ℝ} (hPb : Pb = (∑ a, x a ^ 2) / k) :
    ∑ a, (k : ℝ)⁻¹ * (1 / 2 * Real.log ((Pb + N) / N) - 1 / 2 + (x a ^ 2 + N) / (2 * (Pb + N)))
      = awgnCapacity Pb N := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hPb0 : 0 ≤ Pb := by rw [hPb]; positivity
  have hS : 0 < Pb + N := by linarith
  have hsq : ∑ a, x a ^ 2 = k * Pb := by rw [hPb]; field_simp
  have hlog : (Pb + N) / N = 1 + Pb / N := by field_simp; ring
  rw [← mul_sum, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← sum_div, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hsq,
    hlog]
  unfold awgnCapacity
  field_simp
  ring

namespace Code

variable {P : ℝ} {n k : ℕ}

theorem measurable_dec_add (c : Code ι P n k) (m : Fin k) :
    Measurable fun z => c.dec (c.enc m + z) :=
  c.measurable_dec.comp (measurable_const_add _)

noncomputable def channel (c : Code ι P n k) (N : ι → ℝ) : DMC (Fin k) (Fin k) :=
  fun m => ((noise N n).map fun z => c.dec (c.enc m + z)).toPMF

theorem channel_apply (c : Code ι P n k) (N : ι → ℝ) (m j : Fin k) :
    c.channel N m j = ((noise N n).map fun z => c.enc m + z) (c.dec ⁻¹' {j}) := by
  rw [channel, Measure.toPMF_apply, Measure.map_apply (c.measurable_dec_add m)
    (measurableSet_singleton j), Measure.map_apply (measurable_const_add _)
    (c.measurable_dec (measurableSet_singleton j))]
  rfl

private def toBlockCode (k : ℕ) : BlockCode (Fin k) (Fin k) (Fin k) 1 :=
  ⟨fun m _ => m, fun y => y 0⟩

private lemma avgError_toBlockCode (c : Code ι P n k) (N : ι → ℝ) :
    (toBlockCode k).avgError (c.channel N) = c.avgError N := by
  classical
  simp only [BlockCode.avgError, avgError, Fintype.card_fin]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [BlockCode.errorProb, ← (Equiv.funUnique (Fin 1) (Fin k)).symm.sum_comp]
  simp only [DMC.blockProb, toBlockCode, Fin.prod_univ_one]
  have h : ∀ j : Fin k, (Equiv.funUnique (Fin 1) (Fin k)).symm j 0 = j := fun j => rfl
  simp only [h, channel, Measure.toPMF_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, sum_measure_singleton,
    Measure.map_apply (c.measurable_dec_add m) (Finset.measurableSet _), errorProb]
  congr 1
  ext z
  simp

private lemma inputLaw_toBlockCode (hk : 0 < k) (a : Fin k) :
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    ((toBlockCode k).inputLaw 0 a).toReal = (k : ℝ)⁻¹ := by
  simp only [BlockCode.inputLaw, toBlockCode, PMF.map_apply, PMF.ofFintype_apply, Fintype.card_fin]
  rw [tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
  simp

theorem inputMutualInfo_channel_le [Nonempty ι] (c : Code ι P n k) (hP : 0 ≤ P) {N : ι → ℝ}
    (hN : ∀ i, 0 < N i) (p : PMF (Fin k)) (hp : ∀ a, (p a).toReal = (k : ℝ)⁻¹) :
    (c.channel N).inputMutualInfo p ≤ n * WaterFilling.capacity N P := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact absurd (p.tsum_coe) (by simp)
  set Pb : ι → Fin n → ℝ := fun i t => (∑ m, c.enc m i t ^ 2) / k
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hPb : ∀ i t, 0 ≤ Pb i t := fun i t =>
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hk'.le
  set S : ι → Fin n → ℝ := fun i t => Pb i t + N i
  have hS : ∀ i t, 0 < S i t := fun i t => by simp only [S]; linarith [hPb i t, hN i]
  set ρ := Measure.pi fun i => Measure.pi fun t => gaussianReal 0 (S i t).toNNReal
  set r : Fin k → ℝ := fun j => ρ.real (c.dec ⁻¹' {j})
  have hV : ∀ m j, (c.channel N m j).toReal
      = ((noise N n).map fun z => c.enc m + z).real (c.dec ⁻¹' {j}) := fun m j => by
    rw [channel_apply]
    rfl
  have hsum : ∑ j, r j = 1 := by
    have h : ∀ j, r j = (ρ.map c.dec).real {j} := fun j =>
      (map_measureReal_apply c.measurable_dec (measurableSet_singleton j)).symm
    simp only [h]
    exact sum_measureReal_singleton_eq_one _
  have hz : ∀ a j, r j = 0 → (c.channel N a j).toReal = 0 := by
    intro a j hj
    rw [hV, measureReal_def, map_noise_add_absolutelyContinuous hN (c.enc a) S hS
      ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 hj), ENNReal.toReal_zero]
  refine (DMC.inputMutualInfo_le_sum_mul_log_sub _ p (fun _ => measureReal_nonneg)
    hsum.le hz).trans ?_
  have hper : ∀ a, ∑ j, (c.channel N a j).toReal
      * (Real.log (c.channel N a j).toReal - Real.log (r j))
      ≤ ∑ i, ∑ t, (1 / 2 * Real.log (S i t / N i) - 1 / 2 +
          (c.enc a i t ^ 2 + N i) / (2 * S i t)) := by
    intro a
    simp only [hV]
    exact sum_mul_log_sub_log_le hN (c.enc a) S hS c.measurable_dec
  refine (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hper a)
    (by rw [hp]; positivity)).trans ?_
  have havg : ∑ a, (p a).toReal * ∑ i, ∑ t, (1 / 2 * Real.log (S i t / N i) - 1 / 2 +
        (c.enc a i t ^ 2 + N i) / (2 * S i t))
      = ∑ i, ∑ t, awgnCapacity (Pb i t) (N i) := by
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact avg_aux hk (hN i) (fun a => c.enc a i t) rfl
  rw [havg]
  refine sum_awgnCapacity_le hP hN Pb hPb ?_
  simp only [Pb, ← Finset.sum_div]
  rw [div_le_iff₀ hk']
  calc ∑ i, ∑ t, ∑ m, c.enc m i t ^ 2 = ∑ i, ∑ m, ∑ t, c.enc m i t ^ 2 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ t, c.enc m i t ^ 2 := Finset.sum_comm
    _ ≤ ∑ _m : Fin k, (n * P) := Finset.sum_le_sum fun m _ => c.power m
    _ = n * P * k := by simp [mul_comm]

theorem one_sub_mul_log_le [Nonempty ι] (c : Code ι P n k) (hP : 0 ≤ P) {N : ι → ℝ}
    (hN : ∀ i, 0 < N i) (hk : 0 < k) :
    (1 - (c.avgError N).toReal) * Real.log k ≤
      n * WaterFilling.capacity N P + Real.log 2 := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h1 := (toBlockCode k).mutualInfo_le_sum_inputMutualInfo (c.channel N)
  rw [Fin.sum_univ_one] at h1
  have h2 := (toBlockCode k).condEntropy_fst_snd_codeMeasure_le (c.channel N)
  have h3 := mutualInfo_eq_entropy_sub_condEntropy Prod.fst Prod.snd
    ((toBlockCode k).codeMeasure (c.channel N))
  rw [BlockCode.entropy_fst_codeMeasure] at h3
  rw [avgError_toBlockCode] at h2
  have h4 := c.inputMutualInfo_channel_le hP hN _ (inputLaw_toBlockCode hk)
  rw [Fintype.card_fin] at h2 h3
  nlinarith

end Code

theorem capacity_nonneg [Nonempty ι] {P : ℝ} {N : ι → ℝ} (hP : 0 ≤ P) (hN : ∀ i, 0 < N i) :
    0 ≤ WaterFilling.capacity N P := by
  obtain ⟨ν, hν, -, hfill, -, -, -, -⟩ := WaterFilling.exists_waterFilling hN hP
  rw [WaterFilling.capacity_eq hN hν hfill]
  exact sum_nonneg fun i _ => AWGN.awgnCapacity_nonneg (WaterFilling.fill_nonneg N ν i) (hN i)

theorem le_capacity_of_achievable [Nonempty ι] {P R : ℝ} {N : ι → ℝ} (hP : 0 ≤ P)
    (hN : ∀ i, 0 < N i) (h : Achievable P N R) : R ≤ WaterFilling.capacity N P := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hC := capacity_nonneg hP hN
  set C := WaterFilling.capacity N P
  set δ := R - C with hδ
  have hδ0 : 0 < δ := by linarith
  have hR : 0 < R := by linarith
  set e := δ / (2 * R) with he
  have he0 : 0 < e := by positivity
  have he1 : e * R = δ / 2 := by
    rw [he]
    field_simp
  have he2 : 0 < 1 - e := by nlinarith
  obtain ⟨n₀, hn₀⟩ := h (ENNReal.ofReal e) (ENNReal.ofReal_pos.2 he0)
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (2 * Real.log 2 / δ)
  obtain ⟨n, hNn, hn0n⟩ : ∃ n : ℕ, n₀ ≤ n ∧ m₀ ≤ n :=
    ⟨max n₀ m₀, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨k, hk, c, hc⟩ := hn₀ n hNn
  have hn : 2 * Real.log 2 < n * δ := by
    rw [← div_lt_iff₀ hδ0]
    exact hm₀.trans_le (by exact_mod_cast hn0n)
  have hk0 : (0 : ℝ) < k := (Real.exp_pos _).trans_le hk
  have key := c.one_sub_mul_log_le hP hN (by exact_mod_cast hk0)
  have hPe : (c.avgError N).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1 : (1 - e) * Real.log k ≤ n * C + Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)).trans key
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

theorem closure_achievable_eq [Nonempty ι] {P : ℝ} {N : ι → ℝ} (hP : 0 ≤ P)
    (hN : ∀ i, 0 < N i) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable P N R} = Set.Icc 0 (WaterFilling.capacity N P) := by
  refine subset_antisymm (closure_minimal (fun R hR => ⟨hR.1, le_capacity_of_achievable hP hN
    hR.2⟩) isClosed_Icc) fun R hR => ?_
  rcases (capacity_nonneg hP hN).eq_or_lt with h | h
  · rw [← h, Set.Icc_self, Set.mem_singleton_iff] at hR
    exact subset_closure ⟨hR.symm ▸ le_rfl, hR ▸ achievable_zero hP N⟩
  · rw [← closure_Ico h.ne] at hR
    refine closure_mono (fun R (hR : R ∈ Set.Ico 0 (WaterFilling.capacity N P)) => ?_) hR
    exact ⟨hR.1, achievable_of_lt hP hN hR.2⟩

end Parallel

end Meat
