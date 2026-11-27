import Meat.Continuous.EPITwo
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

private noncomputable def smooth (v : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, h y * heatKernel v (x - y)

private lemma integrable_heatKernel_sub {v : ℝ} (hv : 0 < v) (m : ℝ) :
    Integrable fun u => heatKernel v (u - m) :=
  Integrable.of_integral_ne_zero (by rw [integral_heatKernel hv m]; exact one_ne_zero)

private lemma integrable_heatKernel' {v : ℝ} (hv : 0 < v) : Integrable (heatKernel v) := by
  simpa using integrable_heatKernel_sub hv 0

private lemma lintegral_heatKernel {v : ℝ} (hv : 0 < v) (y : ℝ) :
    ∫⁻ x, ENNReal.ofReal (heatKernel v (x - y)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel_sub hv y)
    (ae_of_all _ fun x => (heatKernel_pos hv _).le), integral_heatKernel hv y, ENNReal.ofReal_one]

private lemma lintegral_heatKernel' {v : ℝ} (hv : 0 < v) :
    ∫⁻ x, ENNReal.ofReal (heatKernel v x) = 1 := by
  simpa using lintegral_heatKernel hv 0

private lemma measurable_smooth (v : ℝ) {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (smooth v h) :=
  ((hh.comp measurable_snd).mul ((continuous_heatKernel v).measurable.comp
    (measurable_fst.sub measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable

private lemma integrable_mul_heatKernel_sub {h : ℝ → ℝ} (hh : Integrable h) {v : ℝ} (hv : 0 < v)
    (x : ℝ) : Integrable fun y => h y * heatKernel v (x - y) :=
  hh.mul_bdd
    ((continuous_heatKernel v).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (heatKernel_pos hv _)]
      exact heatKernel_le_const hv _)

private lemma smooth_sub {v : ℝ} (hv : 0 < v) {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (x : ℝ) : smooth v f x - smooth v g x = smooth v (fun y => f y - g y) x := by
  simp only [smooth]
  rw [← integral_sub (integrable_mul_heatKernel_sub hf hv x)
    (integrable_mul_heatKernel_sub hg hv x)]
  congr 1
  ext y
  ring

private lemma lintegral_smooth_le {v : ℝ} (hv : 0 < v) {h : ℝ → ℝ} (hh : Measurable h) :
    ∫⁻ x, ‖smooth v h x‖ₑ ≤ ∫⁻ y, ‖h y‖ₑ := by
  calc ∫⁻ x, ‖smooth v h x‖ₑ
      ≤ ∫⁻ x, ∫⁻ y, ‖h y‖ₑ * ENNReal.ofReal (heatKernel v (x - y)) := by
        refine lintegral_mono fun x => (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        refine lintegral_congr fun y => ?_
        rw [enorm_mul, Real.enorm_of_nonneg (heatKernel_pos hv _).le]
    _ = ∫⁻ y, ∫⁻ x, ‖h y‖ₑ * ENNReal.ofReal (heatKernel v (x - y)) :=
        lintegral_lintegral_swap ((hh.comp measurable_snd).enorm.mul
          ((continuous_heatKernel v).measurable.comp
            (measurable_fst.sub measurable_snd)).ennreal_ofReal).aemeasurable
    _ = ∫⁻ y, ‖h y‖ₑ := by
        refine lintegral_congr fun y => ?_
        have hm : Measurable fun x => ENNReal.ofReal (heatKernel v (x - y)) :=
          ((continuous_heatKernel v).comp
            (continuous_id.sub continuous_const)).measurable.ennreal_ofReal
        rw [lintegral_const_mul _ hm, lintegral_heatKernel hv y, mul_one]

private lemma tendsto_translate {g : ℝ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Tendsto (fun z => ∫⁻ x, ‖g (x - z) - g x‖ₑ) (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  set S := Metric.cthickening 1 (tsupport g)
  have hS : IsCompact S := hgs.isCompact.cthickening
  have hgC : ∀ y, ‖g y‖ₑ ≤ ENNReal.ofReal C := fun y => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC y)
  have h0 : ∫⁻ _ : ℝ, (0 : ℝ≥0∞) = 0 := lintegral_zero
  rw [← h0]
  refine tendsto_lintegral_filter_of_dominated_convergence
    (S.indicator fun _ => 2 * ENNReal.ofReal C)
    (Eventually.of_forall fun z =>
      ((hgc.comp (continuous_id.sub continuous_const)).sub hgc).measurable.enorm) ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with z hz
    refine ae_of_all _ fun x => ?_
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      calc ‖g (x - z) - g x‖ₑ ≤ ‖g (x - z)‖ₑ + ‖g x‖ₑ := enorm_sub_le
        _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := add_le_add (hgC _) (hgC _)
        _ = 2 * ENNReal.ofReal C := (two_mul _).symm
    · have h1 : g x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hx (Metric.self_subset_cthickening _ h)
      have h2 : g (x - z) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun h => hx ?_
        refine Metric.mem_cthickening_of_dist_le x (x - z) 1 _ h ?_
        rw [Metric.mem_ball, dist_zero_right] at hz
        rw [dist_eq_norm, sub_sub_cancel]
        exact hz.le
      simp [h1, h2]
  · rw [lintegral_indicator_const hS.measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
      hS.measure_lt_top.ne
  · refine ae_of_all _ fun x => ?_
    have : Tendsto (fun z => g (x - z) - g x) (𝓝 0) (𝓝 (g (x - 0) - g x)) :=
      ((hgc.comp (continuous_const.sub continuous_id)).sub continuous_const).tendsto 0
    simpa using this.enorm

private lemma tendsto_smooth_of_compact {g : ℝ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    {v : ℕ → ℝ} (hv0 : ∀ n, 0 < v n) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ‖smooth (v n) g x - g x‖ₑ) atTop (𝓝 0) := by
  set ω : ℝ → ℝ≥0∞ := fun z => ∫⁻ x, ‖g (x - z) - g x‖ₑ
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hgm : Measurable g := hgc.measurable
  set B := 2 * ∫⁻ x, ‖g x‖ₑ
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top (by simp) hgi.2.ne
  have hωB : ∀ z, ω z ≤ B := fun z => by
    calc ω z ≤ ∫⁻ x, (‖g (x - z)‖ₑ + ‖g x‖ₑ) := lintegral_mono fun x => enorm_sub_le
      _ = (∫⁻ x, ‖g (x - z)‖ₑ) + ∫⁻ x, ‖g x‖ₑ := by
        have hm : Measurable fun x => ‖g (x - z)‖ₑ :=
          (hgm.comp (measurable_id.sub measurable_const)).enorm
        exact lintegral_add_left hm _
      _ = B := by rw [lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) z, ← two_mul]
  have hpt : ∀ n, ∫⁻ x, ‖smooth (v n) g x - g x‖ₑ
      ≤ ∫⁻ z, ENNReal.ofReal (heatKernel (v n) z) * ω z := by
    intro n
    have hvn := hv0 n
    have hk := (integral_mul_heatKernel_moment hvn).1
    have hki := integrable_heatKernel' hvn
    have key : ∀ x, smooth (v n) g x - g x = ∫ z, (g (x - z) - g x) * heatKernel (v n) z := by
      intro x
      have e1 : smooth (v n) g x = ∫ z, g (x - z) * heatKernel (v n) z := by
        simp only [smooth]
        rw [← integral_sub_left_eq_self _ volume x]
        simp only [sub_sub_cancel]
      have i1 : Integrable fun z => g (x - z) * heatKernel (v n) z :=
        hki.bdd_mul (hgc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
          (ae_of_all _ fun z => hC _)
      rw [e1, show (fun z => (g (x - z) - g x) * heatKernel (v n) z)
          = fun z => g (x - z) * heatKernel (v n) z - g x * heatKernel (v n) z by
            ext z
            ring,
        integral_sub i1 (hki.const_mul _), integral_const_mul, hk, mul_one]
    calc ∫⁻ x, ‖smooth (v n) g x - g x‖ₑ
        ≤ ∫⁻ x, ∫⁻ z, ‖g (x - z) - g x‖ₑ * ENNReal.ofReal (heatKernel (v n) z) := by
          refine lintegral_mono fun x => ?_
          rw [key x]
          refine (enorm_integral_le_lintegral_enorm _).trans_eq (lintegral_congr fun z => ?_)
          rw [enorm_mul, Real.enorm_of_nonneg (heatKernel_pos hvn z).le]
      _ = ∫⁻ z, ∫⁻ x, ‖g (x - z) - g x‖ₑ * ENNReal.ofReal (heatKernel (v n) z) :=
          lintegral_lintegral_swap ((((hgc.comp (continuous_fst.sub continuous_snd)).sub
            (hgc.comp continuous_fst)).measurable.enorm).mul
            ((continuous_heatKernel _).measurable.comp measurable_snd).ennreal_ofReal).aemeasurable
      _ = ∫⁻ z, ENNReal.ofReal (heatKernel (v n) z) * ω z := by
          refine lintegral_congr fun z => ?_
          have hm : Measurable fun x => ‖g (x - z) - g x‖ₑ :=
            ((hgc.comp (continuous_id.sub continuous_const)).sub hgc).measurable.enorm
          rw [lintegral_mul_const _ hm, mul_comm]
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨δ, hδ, hδω⟩ := Metric.eventually_nhds_iff.1
    ((ENNReal.tendsto_nhds_zero.1 (tendsto_translate hgc hgs)) (ε / 2) hε2)
  have hωb : ∀ z, ω z ≤ ε / 2 + B * ENNReal.ofReal (z ^ 2 / δ ^ 2) := by
    intro z
    by_cases hz : dist z 0 < δ
    · exact (hδω hz).trans le_self_add
    · have h1 : 1 ≤ z ^ 2 / δ ^ 2 := by
        rw [Real.dist_eq, sub_zero, not_lt] at hz
        rw [one_le_div (by positivity)]
        nlinarith [abs_nonneg z, sq_abs z]
      calc ω z ≤ B := hωB z
        _ = B * ENNReal.ofReal 1 := by simp
        _ ≤ B * ENNReal.ofReal (z ^ 2 / δ ^ 2) := by gcongr
        _ ≤ _ := le_add_self
  have hlim : Tendsto (fun n => B * ENNReal.ofReal (v n / δ ^ 2)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal (hv.div_const (δ ^ 2))) (Or.inr hB)
    simpa using this
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hlim) (ε / 2) hε2] with n hn
  have hvn := hv0 n
  have hm : ∫ z, z ^ 2 / δ ^ 2 * heatKernel (v n) z = v n / δ ^ 2 := by
    simp_rw [div_mul_eq_mul_div]
    rw [integral_div, (integral_mul_heatKernel_moment hvn).2.2]
  have hmi : Integrable fun z => z ^ 2 / δ ^ 2 * heatKernel (v n) z :=
    Integrable.of_integral_ne_zero (by rw [hm]; positivity)
  have hmeas : Measurable fun z => ENNReal.ofReal (heatKernel (v n) z) :=
    (continuous_heatKernel _).measurable.ennreal_ofReal
  have hmeas2 : Measurable fun z => ENNReal.ofReal (z ^ 2 / δ ^ 2 * heatKernel (v n) z) :=
    (((continuous_pow 2).div_const _).mul (continuous_heatKernel _)).measurable.ennreal_ofReal
  calc ∫⁻ x, ‖smooth (v n) g x - g x‖ₑ ≤ ∫⁻ z, ENNReal.ofReal (heatKernel (v n) z) * ω z := hpt n
    _ ≤ ∫⁻ z, (ENNReal.ofReal (heatKernel (v n) z) * (ε / 2) +
        B * ENNReal.ofReal (z ^ 2 / δ ^ 2 * heatKernel (v n) z)) := by
        refine lintegral_mono fun z => ?_
        calc ENNReal.ofReal (heatKernel (v n) z) * ω z
            ≤ ENNReal.ofReal (heatKernel (v n) z) *
                (ε / 2 + B * ENNReal.ofReal (z ^ 2 / δ ^ 2)) := by
              gcongr
              exact hωb z
          _ = _ := by
              rw [ENNReal.ofReal_mul (by positivity)]
              ring
    _ = ε / 2 + B * ENNReal.ofReal (v n / δ ^ 2) := by
        rw [lintegral_add_left (hmeas.mul_const _), lintegral_mul_const _ hmeas,
          lintegral_const_mul _ hmeas2, lintegral_heatKernel' hvn, one_mul,
          ← ofReal_integral_eq_lintegral_ofReal hmi
            (ae_of_all _ fun z => by have := heatKernel_pos hvn z; positivity), hm]
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl hn
    _ = ε := ENNReal.add_halves ε

private lemma tendsto_smooth {f : ℝ → ℝ} (hfm : Measurable f) (hfi : Integrable f) {v : ℕ → ℝ}
    (hv0 : ∀ n, 0 < v n) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ‖smooth (v n) f x - f x‖ₑ) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  obtain ⟨g, hgs, hfg, hgc, hgi⟩ :=
    Integrable.exists_hasCompactSupport_lintegral_sub_le hfi (ENNReal.half_pos hε2).ne'
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (tendsto_smooth_of_compact hgc hgs hv0 hv)) (ε / 2)
    (ENNReal.half_pos hε.ne')] with n hn
  have hvn := hv0 n
  have hd : Measurable fun y => f y - g y := hfm.sub hgc.measurable
  have m1 : Measurable fun x => ‖smooth (v n) (fun y => f y - g y) x‖ₑ :=
    (measurable_smooth _ hd).enorm
  have m2 : Measurable fun x => ‖smooth (v n) g x - g x‖ₑ :=
    ((measurable_smooth _ hgc.measurable).sub hgc.measurable).enorm
  calc ∫⁻ x, ‖smooth (v n) f x - f x‖ₑ
      ≤ ∫⁻ x, (‖smooth (v n) (fun y => f y - g y) x‖ₑ + ‖smooth (v n) g x - g x‖ₑ +
          ‖f x - g x‖ₑ) := by
        refine lintegral_mono fun x => ?_
        have e : smooth (v n) f x - f x = smooth (v n) (fun y => f y - g y) x +
            (smooth (v n) g x - g x) - (f x - g x) := by
          rw [← smooth_sub hvn hfi hgi x]
          ring
        rw [e]
        exact enorm_sub_le.trans (add_le_add (enorm_add_le _ _) le_rfl)
    _ = (∫⁻ x, ‖smooth (v n) (fun y => f y - g y) x‖ₑ) +
          (∫⁻ x, ‖smooth (v n) g x - g x‖ₑ) + ∫⁻ x, ‖f x - g x‖ₑ := by
        have m12 : Measurable fun x => ‖smooth (v n) (fun y => f y - g y) x‖ₑ +
            ‖smooth (v n) g x - g x‖ₑ := m1.add m2
        rw [lintegral_add_left m12, lintegral_add_left m1]
    _ ≤ ε / 2 / 2 + ε / 2 + ε / 2 / 2 :=
        add_le_add (add_le_add ((lintegral_smooth_le hvn hd).trans hfg) hn) hfg
    _ = ε := by rw [add_right_comm, ENNReal.add_halves, ENNReal.add_halves]

private noncomputable def logConst : ℝ := Real.log (Real.sqrt (2 * Real.pi * 1))

private noncomputable def klTerm (x t : ℝ) : ℝ :=
  t * Real.log t + t * (x ^ 2 / 2) + logConst * t - t + heatKernel 1 x

private lemma log_heatKernel_one (x : ℝ) :
    Real.log (heatKernel 1 x) = -(x ^ 2 / 2 + logConst) := by
  have h1 : Real.sqrt (2 * Real.pi * 1) ≠ 0 := by positivity
  rw [heatKernel, Real.log_mul (inv_ne_zero h1) (Real.exp_pos _).ne', Real.log_inv, Real.log_exp,
    logConst]
  ring

private lemma klTerm_nonneg (x : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ klTerm x t := by
  have hφ := heatKernel_pos one_pos x
  rcases ht.eq_or_lt with rfl | ht
  · simp [klTerm, hφ.le]
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos ht hφ)
    rw [Real.log_div ht.ne' hφ.ne', log_heatKernel_one, inv_div] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 ht.le
    have e : t * (1 - heatKernel 1 x / t) = t - heatKernel 1 x := by field_simp
    rw [e] at h2
    simp only [klTerm]
    nlinarith

private lemma continuous_klTerm_comp {p : ℝ → ℝ} (hp : Continuous p) :
    Continuous fun x => klTerm x (p x) :=
  ((((Real.continuous_mul_log.comp hp).add (hp.mul ((continuous_pow 2).div_const 2))).add
    (continuous_const.mul hp)).sub hp).add (continuous_heatKernel 1)

private lemma klTerm_integral {m : Measure ℝ} [IsProbabilityMeasure m] (hac : m ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog (m.rnDeriv volume x).toReal))
    (h2 : Integrable (fun y => y ^ 2) m) :
    Integrable (fun x => klTerm x (m.rnDeriv volume x).toReal) ∧
      ∫ x, klTerm x (m.rnDeriv volume x).toReal
        = -measureDiffEntropy m + (∫ y, y ^ 2 ∂m) / 2 + logConst := by
  set t := fun x => (m.rnDeriv volume x).toReal with ht
  have i1 : Integrable fun x => t x * Real.log (t x) :=
    hf.neg.congr (ae_of_all _ fun x => by simp [Real.negMulLog, t])
  have i2 : Integrable fun x => t x * (x ^ 2 / 2) :=
    (integrable_toReal_rnDeriv_mul_iff hac).2 (h2.div_const 2)
  have i4 : Integrable t := Measure.integrable_toReal_rnDeriv
  have i3 : Integrable fun x => logConst * t x := i4.const_mul _
  have i5 : Integrable (heatKernel 1) := integrable_heatKernel' one_pos
  have e : (fun x => klTerm x (t x)) = fun x => t x * Real.log (t x) + t x * (x ^ 2 / 2) +
      logConst * t x - t x + heatKernel 1 x := rfl
  have j1 : Integrable fun x => t x * Real.log (t x) + t x * (x ^ 2 / 2) := i1.add i2
  have j2 : Integrable fun x => t x * Real.log (t x) + t x * (x ^ 2 / 2) + logConst * t x :=
    j1.add i3
  have j3 : Integrable fun x => t x * Real.log (t x) + t x * (x ^ 2 / 2) + logConst * t x - t x :=
    j2.sub i4
  refine ⟨j3.add i5, ?_⟩
  have hI1 : ∫ x, t x * Real.log (t x) = -measureDiffEntropy m := by
    rw [measureDiffEntropy, ← integral_neg]
    congr 1
    ext x
    simp [Real.negMulLog, t]
  have hI2 : ∫ x, t x * (x ^ 2 / 2) = (∫ y, y ^ 2 ∂m) / 2 := by
    rw [integral_toReal_rnDeriv_mul hac, integral_div]
  have hI4 : ∫ x, t x = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac, probReal_univ]
  rw [e, integral_add j3 i5, integral_sub j2 i4, integral_add j1 i3, integral_add i1 i2,
    integral_const_mul, hI1, hI2, hI4,
    (integral_mul_heatKernel_moment one_pos).1]
  ring

private lemma integral_sq_gaussianReal (v : ℝ≥0) : ∫ y, y ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simp only [id, integral_id_gaussianReal, sub_zero] at h
  exact h

private lemma integrable_sq_of_memLp {μ : Measure ℝ} (h : MemLp id 2 μ) :
    Integrable (fun y => y ^ 2) μ := by
  simpa using h.integrable_sq

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

private lemma lintegral_klTerm_le (h2 : Integrable (fun y => y ^ 2) μ) {c : ℝ}
    (hc : ∀ v : ℝ, 0 < v → c ≤ measureDiffEntropy (μ ∗ gaussianReal 0 v.toNNReal))
    {s : ℝ} (hs : 0 < s) :
    ∫⁻ x, ENNReal.ofReal (klTerm x (heatDensity μ s x))
        ≤ ENNReal.ofReal (-c + (∫ y, y ^ 2 ∂μ + s) / 2 + logConst) ∧
      0 ≤ -c + (∫ y, y ^ 2 ∂μ + s) / 2 + logConst := by
  have hms : μ ∗ gaussianReal 0 s.toNNReal
      = volume.withDensity fun x => ENNReal.ofReal (heatDensity μ s x) := by
    rw [Measure.conv_comm, gaussianReal_conv_eq_withDensity hs]
  have hacs : μ ∗ gaussianReal 0 s.toNNReal ≪ volume := by
    rw [hms]
    exact withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ x, ((μ ∗ gaussianReal 0 s.toNNReal).rnDeriv volume x).toReal
      = heatDensity μ s x := by
    rw [hms]
    filter_upwards [Measure.rnDeriv_withDensity volume
      (continuous_heatDensity (ν := μ) hs).measurable.ennreal_ofReal] with x hx
    rw [hx, ENNReal.toReal_ofReal (heatDensity_pos hs x).le]
  have hG2 := integrable_sq_of_memLp
    (memLp_id_gaussianReal' (μ := 0) (v := s.toNNReal) 2 (by simp))
  obtain ⟨hi, he⟩ := integrable_sq_conv h2 hG2
  obtain ⟨hKi, hK⟩ := klTerm_integral hacs (integrable_negMulLog_conv_gaussianReal h2 hs) hi
  rw [he, integral_id_gaussianReal, integral_sq_gaussianReal, Real.coe_toNNReal _ hs.le] at hK
  have hcs := hc s hs
  have hK0 : 0 ≤ ∫ x, klTerm x ((μ ∗ gaussianReal 0 s.toNNReal).rnDeriv volume x).toReal :=
    integral_nonneg fun x => klTerm_nonneg x ENNReal.toReal_nonneg
  have hle : ∫ x, klTerm x ((μ ∗ gaussianReal 0 s.toNNReal).rnDeriv volume x).toReal
      ≤ -c + (∫ y, y ^ 2 ∂μ + s) / 2 + logConst := by
    rw [hK]
    linarith
  refine ⟨?_, hK0.trans hle⟩
  calc ∫⁻ x, ENNReal.ofReal (klTerm x (heatDensity μ s x))
      = ∫⁻ x, ENNReal.ofReal
          (klTerm x ((μ ∗ gaussianReal 0 s.toNNReal).rnDeriv volume x).toReal) :=
        lintegral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
    _ = ENNReal.ofReal
          (∫ x, klTerm x ((μ ∗ gaussianReal 0 s.toNNReal).rnDeriv volume x).toReal) :=
        (ofReal_integral_eq_lintegral_ofReal hKi
          (ae_of_all _ fun x => klTerm_nonneg x ENNReal.toReal_nonneg)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

theorem le_measureDiffEntropy_of_le_conv_gaussianReal (hac : μ ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog (μ.rnDeriv volume x).toReal))
    (h2 : Integrable (fun y => y ^ 2) μ) {c : ℝ}
    (hc : ∀ v : ℝ, 0 < v → c ≤ measureDiffEntropy (μ ∗ gaussianReal 0 v.toNNReal)) :
    c ≤ measureDiffEntropy μ := by
  set f := fun x => (μ.rnDeriv volume x).toReal with hfdef
  have hfm : Measurable f := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hfi : Integrable f := Measure.integrable_toReal_rnDeriv
  set v : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hv0 : ∀ n, 0 < v n := fun n => by positivity
  have hv : Tendsto v atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsm : ∀ s, heatDensity μ s = smooth s f := fun s => by
    ext x
    simp only [heatDensity, smooth]
    rw [← integral_rnDeriv_smul hac]
    rfl
  have hmeas : TendstoInMeasure volume (fun n => heatDensity μ (v n)) atTop f := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero ?_
    refine (tendsto_smooth hfm hfi hv0 hv).congr fun n => ?_
    rw [eLpNorm_one_eq_lintegral_enorm ((continuous_heatDensity (hv0 n)).aestronglyMeasurable.sub
      hfm.aestronglyMeasurable), hsm]
    rfl
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  set M := ∫ y, y ^ 2 ∂μ
  set b : ℝ → ℝ := fun s => -c + (M + s) / 2 + logConst
  have hb : Tendsto (fun k => b (v (ns k))) atTop (𝓝 (b 0)) :=
    ((((hv.comp hns.tendsto_atTop).const_add M).div_const 2).const_add (-c)).add_const logConst
  have hb0 : 0 ≤ b 0 :=
    ge_of_tendsto' hb fun k => (lintegral_klTerm_le h2 hc (hv0 (ns k))).2
  obtain ⟨hKi, hK⟩ := klTerm_integral hac hf h2
  have hlim : ∀ᵐ x, Tendsto (fun k => ENNReal.ofReal (klTerm x (heatDensity μ (v (ns k)) x)))
      atTop (𝓝 (ENNReal.ofReal (klTerm x (f x)))) := by
    filter_upwards [hae] with x hx
    have hcont : Continuous fun t => klTerm x t :=
      (((Real.continuous_mul_log.add (continuous_id.mul continuous_const)).add
        (continuous_const.mul continuous_id)).sub continuous_id).add continuous_const
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((hcont.tendsto _).comp hx)
  have hF := lintegral_liminf_le' (μ := volume) (u := atTop)
    (f := fun k x => ENNReal.ofReal (klTerm x (heatDensity μ (v (ns k)) x)))
    (fun k => (continuous_klTerm_comp
      (continuous_heatDensity (hv0 (ns k)))).measurable.ennreal_ofReal.aemeasurable)
  have hmain : ENNReal.ofReal (∫ x, klTerm x (f x)) ≤ ENNReal.ofReal (b 0) := by
    calc ENNReal.ofReal (∫ x, klTerm x (f x))
        = ∫⁻ x, ENNReal.ofReal (klTerm x (f x)) :=
          ofReal_integral_eq_lintegral_ofReal hKi
            (ae_of_all _ fun x => klTerm_nonneg x ENNReal.toReal_nonneg)
      _ = ∫⁻ x, liminf (fun k => ENNReal.ofReal (klTerm x (heatDensity μ (v (ns k)) x))) atTop :=
          lintegral_congr_ae (hlim.mono fun x hx => hx.liminf_eq.symm)
      _ ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal (klTerm x (heatDensity μ (v (ns k)) x))) atTop :=
          hF
      _ ≤ liminf (fun k => ENNReal.ofReal (b (v (ns k)))) atTop :=
          liminf_le_liminf
            (Eventually.of_forall fun k => (lintegral_klTerm_le h2 hc (hv0 (ns k))).1)
      _ = ENNReal.ofReal (b 0) := (ENNReal.tendsto_ofReal hb).liminf_eq
  rw [ENNReal.ofReal_le_ofReal_iff hb0, hK] at hmain
  simp only [b] at hmain
  linarith

theorem entropyPowerInequality : EntropyPowerInequality := by
  intro ν ρ _ _ hν hρ h2ν h2ρ hfν hfρ hfνρ
  set A := Real.exp (2 * measureDiffEntropy ν) + Real.exp (2 * measureDiffEntropy ρ)
  have hA : 0 < A := by positivity
  have hac : ν ∗ ρ ≪ volume := by
    rw [Measure.conv_comm]
    exact Measure.conv_absolutelyContinuous hν
  have h2 := (integrable_sq_conv (integrable_sq_of_memLp h2ν) (integrable_sq_of_memLp h2ρ)).1
  have key : Real.log A / 2 ≤ measureDiffEntropy (ν ∗ ρ) := by
    refine le_measureDiffEntropy_of_le_conv_gaussianReal hac hfνρ h2 fun s hs => ?_
    have hsv : s.toNNReal ≠ 0 := by simp [hs]
    have h := entropyPowerInequality_conv_conv_gaussianReal hν h2ν hfν hρ h2ρ hfρ hsv
    rw [← Measure.conv_assoc] at h
    have := Real.log_le_log hA h
    rw [Real.log_exp] at this
    linarith
  calc A = Real.exp (Real.log A) := (Real.exp_log hA).symm
    _ ≤ Real.exp (2 * measureDiffEntropy (ν ∗ ρ)) := Real.exp_le_exp.2 (by linarith)

end Meat
