import Meat.Continuous.AWGN
import Meat.Channel.Achievability
import Meat.Channel.Converse

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Meat

theorem pi_withDensity {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (ρ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ρ i)] (f : ∀ i, α i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((ρ i).withDensity (f i))] :
    Measure.pi (fun i => ((ρ i).withDensity (f i) : Measure (α i)))
      = (Measure.pi ρ).withDensity fun x => ∏ i, f i (x i) := by
  classical
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  have h : (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i))
      = fun x => ∏ i, (s i).indicator (f i) (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by simpa [Set.mem_pi] using hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [h]
  refine (lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (ω : ∀ i, α i) => (s i).indicator (f i) (ω i))
    (iIndepFun_pi fun i => ((hf i).indicator (hs i)).aemeasurable)
    fun i => ((hf i).indicator (hs i)).comp (measurable_pi_apply (X := α) i)).trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(measurePreserving_eval ρ i).lintegral_comp ((hf i).indicator (hs i)),
    lintegral_indicator (hs i), withDensity_apply _ (hs i)]

theorem sum_mul_log_sub_log_le_integral {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J] {μ ρ : Measure Ω} [IsProbabilityMeasure μ]
    [IsFiniteMeasure ρ] {L : Ω → ℝ} (hL : Measurable L)
    (hμ : μ = ρ.withDensity fun ω => ENNReal.ofReal (Real.exp (L ω))) (hLi : Integrable L μ)
    {d : Ω → J} (hd : Measurable d) :
    ∑ j, μ.real (d ⁻¹' {j}) * (Real.log (μ.real (d ⁻¹' {j})) - Real.log (ρ.real (d ⁻¹' {j})))
      ≤ ∫ ω, L ω ∂μ := by
  classical
  set f : Ω → ℝ≥0 := fun ω => (Real.exp (L ω)).toNNReal
  have hf : Measurable f := (Real.measurable_exp.comp hL).real_toNNReal
  have hμf : μ = ρ.withDensity fun ω => (f ω : ℝ≥0∞) := hμ
  have hac : μ ≪ ρ := hμf ▸ withDensity_absolutelyContinuous _ _
  have hexp : Integrable (fun ω => Real.exp (-L ω)) μ := by
    rw [hμf, integrable_withDensity_iff_integrable_smul hf]
    refine (integrable_const (1 : ℝ)).congr (ae_of_all _ fun ω => ?_)
    simp [f, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, ← Real.exp_add]
  have hcell : ∀ j, μ.real (d ⁻¹' {j}) * (Real.log (μ.real (d ⁻¹' {j}))
      - Real.log (ρ.real (d ⁻¹' {j}))) ≤ ∫ ω in d ⁻¹' {j}, L ω ∂μ := by
    intro j
    set A := d ⁻¹' {j}
    have hA : MeasurableSet A := hd (measurableSet_singleton j)
    set a := μ.real A
    set b := ρ.real A
    rcases (measureReal_nonneg (μ := μ) (s := A)).eq_or_lt with ha | ha
    · rw [show a = 0 from ha.symm, zero_mul, setIntegral_measure_zero _
        ((measureReal_eq_zero_iff (measure_ne_top μ A)).1 ha.symm)]
    have hb : 0 < b := by
      refine ENNReal.toReal_pos (fun h0 => ?_) (measure_ne_top ρ A)
      exact (ENNReal.toReal_pos_iff.1 ha).1.ne' (hac h0)
    have hpt : ∀ ω, Real.log a - Real.log b - L ω ≤ a / b * Real.exp (-L ω) - 1 := by
      intro ω
      have h := Real.log_le_sub_one_of_pos (mul_pos (div_pos ha hb) (Real.exp_pos (-L ω)))
      rwa [Real.log_mul (div_pos ha hb).ne' (Real.exp_pos _).ne', Real.log_exp,
        Real.log_div ha.ne' hb.ne', ← sub_eq_add_neg] at h
    have hint : ∫ ω in A, Real.exp (-L ω) ∂μ = b := by
      rw [hμf, setIntegral_withDensity_eq_setIntegral_smul hf _ hA]
      have : ∀ ω, f ω • Real.exp (-L ω) = 1 := fun ω => by
        simp [f, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, ← Real.exp_add]
      simp [this, b, measureReal_def]
    have hmono : ∫ ω in A, (Real.log a - Real.log b - L ω) ∂μ
        ≤ ∫ ω in A, (a / b * Real.exp (-L ω) - 1) ∂μ :=
      setIntegral_mono ((integrable_const _).sub hLi).integrableOn
        (((hexp.const_mul (a / b)).sub (integrable_const 1))).integrableOn hpt
    rw [integral_sub (integrable_const _).integrableOn hLi.integrableOn, integral_sub
      (hexp.const_mul _).integrableOn (integrable_const _).integrableOn, integral_const_mul,
      hint, setIntegral_const, setIntegral_const] at hmono
    simp only [smul_eq_mul, mul_one] at hmono
    have : a / b * b = a := div_mul_cancel₀ a hb.ne'
    change μ.real A * (Real.log a - Real.log b) - _ ≤ _ at hmono
    nlinarith
  refine (Finset.sum_le_sum fun j _ => hcell j).trans_eq ?_
  rw [← integral_iUnion_fintype (fun j => hd (measurableSet_singleton j))
    (fun i j hij => Set.disjoint_left.2 fun ω hi hj => hij (hi.symm.trans hj))
    fun _ => hLi.integrableOn]
  have hU : (⋃ j, d ⁻¹' {j}) = Set.univ := Set.eq_univ_of_forall fun ω =>
    Set.mem_iUnion.2 ⟨d ω, rfl⟩
  rw [hU, setIntegral_univ]

namespace DMC

variable {A B : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem inputMutualInfo_le_sum_mul_log_sub (W : DMC A B) (p : PMF A) {r : B → ℝ}
    (hr : ∀ b, 0 ≤ r b) (hsum : ∑ b, r b ≤ 1) (hz : ∀ a b, r b = 0 → (W a b).toReal = 0) :
    W.inputMutualInfo p
      ≤ ∑ a, (p a).toReal * ∑ b, (W a b).toReal * (Real.log (W a b).toReal - Real.log (r b)) := by
  classical
  set ν := W.jointMeasure p
  have hν : ∀ x : A × B, ν.real {x} = (p x.1).toReal * (W x.1 x.2).toReal := by
    intro x
    simp only [ν]
    rw [measureReal_def, jointMeasure_eq_toMeasure,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), jointPMF_apply,
      ENNReal.toReal_mul]
  set q : B → ℝ := fun b => (ν.map Prod.snd).real {b}
  have hq : ∀ b, q b = ∑ a, ν.real {(a, b)} := by
    intro b
    simp only [q, measureReal_map_singleton, Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_ite_eq' Finset.univ b _]
    simp
  have hq1 : ∑ b, q b = 1 := sum_measureReal_singleton_eq_one _
  have hG := sum_mul_log_le_sum_mul_log Finset.univ (p := q) (q := r)
    (fun b _ => measureReal_nonneg) (fun b _ => hr b) (fun b _ hb => by
      rw [hq]
      exact Finset.sum_eq_zero fun a _ => by rw [hν, hz a b hb, mul_zero])
    (by rw [hq1]; exact hsum)
  have hqr : ∑ b, q b * Real.log (r b) = ∑ x : A × B, ν.real {x} * Real.log (r x.2) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp [hq, Finset.sum_mul]
  have hH : H[Prod.snd ; ν] = -∑ b, q b * Real.log (q b) := by
    simp [entropy, measureEntropy, Real.negMulLog, q, Finset.sum_neg_distrib]
  have hR : ∑ a, (p a).toReal * ∑ b, (W a b).toReal * (Real.log (W a b).toReal - Real.log (r b))
      = ∑ x : A × B, ν.real {x} * Real.log (W x.1 x.2).toReal
        - ∑ x : A × B, ν.real {x} * Real.log (r x.2) := by
    rw [← Finset.sum_sub_distrib, Fintype.sum_prod_type]
    simp only [hν, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [inputMutualInfo, mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy, hH,
    condEntropy_snd_fst_jointMeasure, hR]
  linarith

end DMC

namespace AWGN

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

theorem map_noise_add {N : ℝ} {n : ℕ} (x : Fin n → ℝ) :
    (noise N n).map (fun z => x + z) = Measure.pi fun i => gaussianReal (x i) N.toNNReal := by
  have h : (fun z : Fin n → ℝ => x + z) = fun z i => z i + x i :=
    funext fun z => funext fun i => add_comm _ _
  have : ∀ i, SigmaFinite ((gaussianReal 0 N.toNNReal).map (· + x i)) := fun i => by
    rw [gaussianReal_map_add_const]
    infer_instance
  rw [noise, h, Measure.pi_map_pi fun i => (measurable_add_const (x i)).aemeasurable]
  simp [gaussianReal_map_add_const]

private lemma pi_gaussianReal_eq_withDensity {N : ℝ} (hN : 0 < N) {n : ℕ} (x S : Fin n → ℝ)
    (hS : ∀ i, 0 < S i) : (Measure.pi fun i => gaussianReal (x i) N.toNNReal)
      = (Measure.pi fun i => gaussianReal 0 (S i).toNNReal).withDensity
        fun z => ENNReal.ofReal (Real.exp (∑ i, llr (x i) N (S i) (z i))) := by
  set g : Fin n → ℝ → ℝ≥0∞ := fun i t => ENNReal.ofReal (Real.exp (llr (x i) N (S i) t))
  have hg : ∀ i, Measurable (g i) := fun i =>
    (Real.measurable_exp.comp (measurable_llr _ _ _)).ennreal_ofReal
  have hw : ∀ i, gaussianReal (x i) N.toNNReal
      = (gaussianReal 0 (S i).toNNReal).withDensity (g i) :=
    fun i => gaussianReal_eq_withDensity (x i) hN (hS i)
  have : ∀ i, SigmaFinite ((gaussianReal 0 (S i).toNNReal).withDensity (g i)) := fun i => by
    rw [← hw i]
    infer_instance
  rw [show (fun i => gaussianReal (x i) N.toNNReal) = fun i =>
    (gaussianReal 0 (S i).toNNReal).withDensity (g i) from funext hw, pi_withDensity _ _ hg]
  congr 1
  funext z
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]

theorem map_noise_add_absolutelyContinuous {N : ℝ} (hN : 0 < N) {n : ℕ} (x S : Fin n → ℝ)
    (hS : ∀ i, 0 < S i) :
    (noise N n).map (fun z => x + z) ≪ Measure.pi fun i => gaussianReal 0 (S i).toNNReal := by
  rw [map_noise_add, pi_gaussianReal_eq_withDensity hN x S hS]
  exact withDensity_absolutelyContinuous _ _

theorem sum_mul_log_sub_log_le {N : ℝ} (hN : 0 < N) {n : ℕ} (x S : Fin n → ℝ)
    (hS : ∀ i, 0 < S i) {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {d : (Fin n → ℝ) → J} (hd : Measurable d) :
    ∑ j, ((noise N n).map (fun z => x + z)).real (d ⁻¹' {j})
      * (Real.log (((noise N n).map (fun z => x + z)).real (d ⁻¹' {j}))
        - Real.log ((Measure.pi fun i => gaussianReal 0 (S i).toNNReal).real (d ⁻¹' {j})))
      ≤ ∑ i, (1 / 2 * Real.log (S i / N) - 1 / 2 + (x i ^ 2 + N) / (2 * S i)) := by
  rw [map_noise_add]
  have hμ := pi_gaussianReal_eq_withDensity hN x S hS
  have hLm : Measurable fun z : Fin n → ℝ => ∑ i, llr (x i) N (S i) (z i) :=
    Finset.measurable_sum _ fun i _ => (measurable_llr _ _ _).comp (measurable_pi_apply i)
  have hi : ∀ i, Integrable (fun z : Fin n → ℝ => llr (x i) N (S i) (z i))
      (Measure.pi fun i => gaussianReal (x i) N.toNNReal) := fun i =>
    integrable_comp_eval (integrable_llr _ _ _ _)
  refine (sum_mul_log_sub_log_le_integral hLm hμ (integrable_finsetSum _ fun i _ => hi i)
    hd).trans_eq ?_
  rw [integral_finsetSum _ fun i _ => hi i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_comp_eval (measurable_llr _ _ _).aestronglyMeasurable, integral_llr _ hN]

theorem sum_log_le_mul_log_div {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    ∑ i, Real.log (a i) ≤ n * Real.log ((∑ i, a i) / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : NeZero n := ⟨hn.ne'⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set m := (∑ i, a i) / n
  have hm : 0 < m := div_pos (Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty) hn'
  have h : ∀ i, Real.log (a i) - Real.log m ≤ a i / m - 1 := fun i => by
    rw [← Real.log_div (ha i).ne' hm.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (ha i) hm)
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div] at hs
  have hm' : (∑ i, a i) / m = n := by
    simp only [m]
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ _
      (Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty).ne']
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    hm'] at hs
  linarith

namespace Code

variable {P : ℝ} {n k : ℕ}

theorem measurable_dec_add (c : Code P n k) (m : Fin k) :
    Measurable fun z => c.dec (c.enc m + z) :=
  c.measurable_dec.comp (measurable_const_add _)

noncomputable def channel (c : Code P n k) (N : ℝ) : DMC (Fin k) (Fin k) :=
  fun m => ((noise N n).map fun z => c.dec (c.enc m + z)).toPMF

theorem channel_apply (c : Code P n k) (N : ℝ) (m j : Fin k) :
    c.channel N m j = ((noise N n).map fun z => c.enc m + z) (c.dec ⁻¹' {j}) := by
  rw [channel, Measure.toPMF_apply, Measure.map_apply (c.measurable_dec_add m)
    (measurableSet_singleton j), Measure.map_apply (measurable_const_add _)
    (c.measurable_dec (measurableSet_singleton j))]
  rfl

private def toBlockCode (k : ℕ) : BlockCode (Fin k) (Fin k) (Fin k) 1 :=
  ⟨fun m _ => m, fun y => y 0⟩

private lemma avgError_toBlockCode (c : Code P n k) (N : ℝ) :
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

theorem inputMutualInfo_channel_le (c : Code P n k) {N : ℝ} (hN : 0 < N) (p : PMF (Fin k))
    (hp : ∀ a, (p a).toReal = (k : ℝ)⁻¹) :
    (c.channel N).inputMutualInfo p ≤ n * awgnCapacity P N := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact absurd (p.tsum_coe) (by simp)
  set Pb : Fin n → ℝ := fun i => (∑ m, c.enc m i ^ 2) / k
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hPb : ∀ i, 0 ≤ Pb i := fun i => div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hk'.le
  set S : Fin n → ℝ := fun i => Pb i + N
  have hS : ∀ i, 0 < S i := fun i => by simp only [S]; linarith [hPb i]
  set ρ := Measure.pi fun i => gaussianReal 0 (S i).toNNReal
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
      ≤ ∑ i, (1 / 2 * Real.log (S i / N) - 1 / 2 + (c.enc a i ^ 2 + N) / (2 * S i)) := by
    intro a
    simp only [hV]
    exact sum_mul_log_sub_log_le hN (c.enc a) S hS c.measurable_dec
  refine (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hper a)
    (by rw [hp]; positivity)).trans ?_
  have havg : ∑ a, (p a).toReal
      * ∑ i, (1 / 2 * Real.log (S i / N) - 1 / 2 + (c.enc a i ^ 2 + N) / (2 * S i))
      = ∑ i, 1 / 2 * Real.log (S i / N) := by
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hSi := (hS i).ne'
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_div,
      Finset.sum_add_distrib, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, S, Pb] at hSi ⊢
    field_simp
    ring
  rw [havg, ← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hlog := sum_log_le_mul_log_div (fun i => S i / N) fun i => div_pos (hS i) hN
  have hpow : ∑ i, Pb i ≤ n * P := by
    simp only [Pb, ← Finset.sum_div]
    rw [Finset.sum_comm, div_le_iff₀ hk']
    calc ∑ m, ∑ i, c.enc m i ^ 2 ≤ ∑ _m : Fin k, (n * P) := Finset.sum_le_sum fun m _ => c.power m
      _ = n * P * k := by simp [mul_comm]
  have hmean : (∑ i, S i / N) / n ≤ 1 + P / N := by
    rw [div_le_iff₀ hn', ← Finset.sum_div, div_le_iff₀ hN]
    simp only [S, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    nlinarith
  have hpos : 0 < (∑ i, S i / N) / n :=
    div_pos (Finset.sum_pos (fun i _ => div_pos (hS i) hN)
      (@Finset.univ_nonempty _ _ ⟨⟨0, hn⟩⟩)) hn'
  have h2 := Real.log_le_log hpos hmean
  unfold awgnCapacity
  nlinarith

theorem one_sub_mul_log_le (c : Code P n k) {N : ℝ} (hN : 0 < N) (hk : 0 < k) :
    (1 - (c.avgError N).toReal) * Real.log k ≤ n * awgnCapacity P N + Real.log 2 := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h1 := (toBlockCode k).mutualInfo_le_sum_inputMutualInfo (c.channel N)
  rw [Fin.sum_univ_one] at h1
  have h2 := (toBlockCode k).condEntropy_fst_snd_codeMeasure_le (c.channel N)
  have h3 := mutualInfo_eq_entropy_sub_condEntropy Prod.fst Prod.snd
    ((toBlockCode k).codeMeasure (c.channel N))
  rw [BlockCode.entropy_fst_codeMeasure] at h3
  rw [avgError_toBlockCode] at h2
  have h4 := c.inputMutualInfo_channel_le hN _ (inputLaw_toBlockCode hk)
  rw [Fintype.card_fin] at h2 h3
  nlinarith

end Code

theorem le_awgnCapacity_of_achievable {P N R : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (h : Achievable P N R) : R ≤ awgnCapacity P N := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hC := awgnCapacity_nonneg hP hN
  set C := awgnCapacity P N
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
  have key := c.one_sub_mul_log_le hN (by exact_mod_cast hk0)
  have hPe : (c.avgError N).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1 : (1 - e) * Real.log k ≤ n * C + Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)).trans key
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

end AWGN

end Meat
