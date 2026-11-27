import Meat.Continuous.EPIVec
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

variable {n : ℕ}

private noncomputable def smoothVec (v : ℝ) (h : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y, h y * heatKernelVec v (x - y)

private lemma lintegral_heatKernelVec {v : ℝ} (hv : 0 < v) (y : Fin n → ℝ) :
    ∫⁻ x, ENNReal.ofReal (heatKernelVec v (x - y)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_heatKernelVec hv).comp_sub_right y)
    (ae_of_all _ fun x => (heatKernelVec_pos hv _).le),
    integral_sub_right_eq_self (heatKernelVec v) y, integral_heatKernelVec hv, ENNReal.ofReal_one]

private lemma lintegral_heatKernelVec' {v : ℝ} (hv : 0 < v) :
    ∫⁻ x, ENNReal.ofReal (heatKernelVec (n := n) v x) = 1 := by
  simpa using lintegral_heatKernelVec (n := n) hv 0

private lemma measurable_smoothVec (v : ℝ) {h : (Fin n → ℝ) → ℝ} (hh : Measurable h) :
    Measurable (smoothVec v h) :=
  ((hh.comp measurable_snd).mul ((continuous_heatKernelVec v).measurable.comp
    (measurable_fst.sub measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable

private lemma integrable_mul_heatKernelVec_sub {h : (Fin n → ℝ) → ℝ} (hh : Integrable h) {v : ℝ}
    (hv : 0 < v) (x : Fin n → ℝ) : Integrable fun y => h y * heatKernelVec v (x - y) :=
  hh.mul_bdd
    ((continuous_heatKernelVec v).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (heatKernelVec_pos hv _)]
      exact heatKernelVec_le_const hv _)

private lemma smoothVec_sub {v : ℝ} (hv : 0 < v) {f g : (Fin n → ℝ) → ℝ} (hf : Integrable f)
    (hg : Integrable g) (x : Fin n → ℝ) :
    smoothVec v f x - smoothVec v g x = smoothVec v (fun y => f y - g y) x := by
  simp only [smoothVec]
  rw [← integral_sub (integrable_mul_heatKernelVec_sub hf hv x)
    (integrable_mul_heatKernelVec_sub hg hv x)]
  congr 1
  ext y
  ring

private lemma lintegral_smoothVec_le {v : ℝ} (hv : 0 < v) {h : (Fin n → ℝ) → ℝ}
    (hh : Measurable h) :
    ∫⁻ x, ‖smoothVec v h x‖ₑ ≤ ∫⁻ y, ‖h y‖ₑ := by
  calc ∫⁻ x, ‖smoothVec v h x‖ₑ
      ≤ ∫⁻ x, ∫⁻ y, ‖h y‖ₑ * ENNReal.ofReal (heatKernelVec v (x - y)) := by
        refine lintegral_mono fun x => (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        refine lintegral_congr fun y => ?_
        rw [enorm_mul, Real.enorm_of_nonneg (heatKernelVec_pos hv _).le]
    _ = ∫⁻ y, ∫⁻ x, ‖h y‖ₑ * ENNReal.ofReal (heatKernelVec v (x - y)) :=
        lintegral_lintegral_swap ((hh.comp measurable_snd).enorm.mul
          ((continuous_heatKernelVec v).measurable.comp
            (measurable_fst.sub measurable_snd)).ennreal_ofReal).aemeasurable
    _ = ∫⁻ y, ‖h y‖ₑ := by
        refine lintegral_congr fun y => ?_
        have hm : Measurable fun x => ENNReal.ofReal (heatKernelVec v (x - y)) :=
          ((continuous_heatKernelVec v).comp
            (continuous_id.sub continuous_const)).measurable.ennreal_ofReal
        rw [lintegral_const_mul _ hm, lintegral_heatKernelVec hv y, mul_one]

private lemma tendsto_translateVec {g : (Fin n → ℝ) → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) :
    Tendsto (fun z => ∫⁻ x, ‖g (x - z) - g x‖ₑ) (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  set S := Metric.cthickening 1 (tsupport g)
  have hS : IsCompact S := hgs.isCompact.cthickening
  have hgC : ∀ y, ‖g y‖ₑ ≤ ENNReal.ofReal C := fun y => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC y)
  have h0 : ∫⁻ _ : Fin n → ℝ, (0 : ℝ≥0∞) = 0 := lintegral_zero
  rw [← h0]
  refine tendsto_lintegral_filter_of_dominated_convergence
    (S.indicator fun _ => 2 * ENNReal.ofReal C)
    (Eventually.of_forall fun z =>
      ((hgc.comp (continuous_id.sub continuous_const)).sub hgc).measurable.enorm) ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℝ) one_pos] with z hz
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

private lemma sq_le_sum_sq_of_norm {z : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ) (hz : δ ≤ ‖z‖) :
    δ ^ 2 ≤ ∑ i, z i ^ 2 := by
  have hS : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h : ‖z‖ ≤ Real.sqrt (∑ i, z i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => z j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have h2 := (hz.trans h)
  calc δ ^ 2 ≤ Real.sqrt (∑ i, z i ^ 2) ^ 2 := pow_le_pow_left₀ hδ.le h2 2
    _ = _ := Real.sq_sqrt hS

private lemma tendsto_smoothVec_of_compact {g : (Fin n → ℝ) → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) {v : ℕ → ℝ} (hv0 : ∀ k, 0 < v k) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ x, ‖smoothVec (v k) g x - g x‖ₑ) atTop (𝓝 0) := by
  set ω : (Fin n → ℝ) → ℝ≥0∞ := fun z => ∫⁻ x, ‖g (x - z) - g x‖ₑ
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
  have hpt : ∀ k, ∫⁻ x, ‖smoothVec (v k) g x - g x‖ₑ
      ≤ ∫⁻ z, ENNReal.ofReal (heatKernelVec (v k) z) * ω z := by
    intro k
    have hvk := hv0 k
    have hk := integral_heatKernelVec (n := n) hvk
    have hki := integrable_heatKernelVec (n := n) hvk
    have key : ∀ x, smoothVec (v k) g x - g x
        = ∫ z, (g (x - z) - g x) * heatKernelVec (v k) z := by
      intro x
      have e1 : smoothVec (v k) g x = ∫ z, g (x - z) * heatKernelVec (v k) z := by
        simp only [smoothVec]
        rw [← integral_sub_left_eq_self _ volume x]
        simp only [sub_sub_cancel]
      have i1 : Integrable fun z => g (x - z) * heatKernelVec (v k) z :=
        hki.bdd_mul (hgc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
          (ae_of_all _ fun z => hC _)
      rw [e1, show (fun z => (g (x - z) - g x) * heatKernelVec (v k) z)
          = fun z => g (x - z) * heatKernelVec (v k) z - g x * heatKernelVec (v k) z by
            ext z
            ring,
        integral_sub i1 (hki.const_mul _), integral_const_mul, hk, mul_one]
    calc ∫⁻ x, ‖smoothVec (v k) g x - g x‖ₑ
        ≤ ∫⁻ x, ∫⁻ z, ‖g (x - z) - g x‖ₑ * ENNReal.ofReal (heatKernelVec (v k) z) := by
          refine lintegral_mono fun x => ?_
          rw [key x]
          refine (enorm_integral_le_lintegral_enorm _).trans_eq (lintegral_congr fun z => ?_)
          rw [enorm_mul, Real.enorm_of_nonneg (heatKernelVec_pos hvk z).le]
      _ = ∫⁻ z, ∫⁻ x, ‖g (x - z) - g x‖ₑ * ENNReal.ofReal (heatKernelVec (v k) z) :=
          lintegral_lintegral_swap ((((hgc.comp (continuous_fst.sub continuous_snd)).sub
            (hgc.comp continuous_fst)).measurable.enorm).mul
            ((continuous_heatKernelVec _).measurable.comp
              measurable_snd).ennreal_ofReal).aemeasurable
      _ = ∫⁻ z, ENNReal.ofReal (heatKernelVec (v k) z) * ω z := by
          refine lintegral_congr fun z => ?_
          have hm : Measurable fun x => ‖g (x - z) - g x‖ₑ :=
            ((hgc.comp (continuous_id.sub continuous_const)).sub hgc).measurable.enorm
          rw [lintegral_mul_const _ hm, mul_comm]
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨δ, hδ, hδω⟩ := Metric.eventually_nhds_iff.1
    ((ENNReal.tendsto_nhds_zero.1 (tendsto_translateVec hgc hgs)) (ε / 2) hε2)
  have hωb : ∀ z, ω z ≤ ε / 2 + B * ENNReal.ofReal ((∑ i, z i ^ 2) / δ ^ 2) := by
    intro z
    by_cases hz : dist z 0 < δ
    · exact (hδω hz).trans le_self_add
    · have h1 : 1 ≤ (∑ i, z i ^ 2) / δ ^ 2 := by
        rw [dist_zero_right, not_lt] at hz
        rw [one_le_div (by positivity)]
        exact sq_le_sum_sq_of_norm hδ hz
      calc ω z ≤ B := hωB z
        _ = B * ENNReal.ofReal 1 := by simp
        _ ≤ B * ENNReal.ofReal ((∑ i, z i ^ 2) / δ ^ 2) := by gcongr
        _ ≤ _ := le_add_self
  have hlim : Tendsto (fun k => B * ENNReal.ofReal (n * v k / δ ^ 2)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_ofReal ((hv.const_mul (n : ℝ)).div_const (δ ^ 2))) (Or.inr hB)
    simpa using this
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hlim) (ε / 2) hε2] with k hk
  have hvk := hv0 k
  have hmi : Integrable fun z : Fin n → ℝ => (∑ i, z i ^ 2) / δ ^ 2 * heatKernelVec (v k) z :=
    ((integrable_sum_sq_mul_heatKernelVec hvk).div_const (δ ^ 2)).congr
      (ae_of_all _ fun z => by simp only; ring)
  have hm : ∫ z : Fin n → ℝ, (∑ i, z i ^ 2) / δ ^ 2 * heatKernelVec (v k) z = n * v k / δ ^ 2 := by
    rw [← integral_sum_sq_mul_heatKernelVec hvk, ← integral_div]
    congr 1
    ext z
    ring
  have hmeas : Measurable fun z => ENNReal.ofReal (heatKernelVec (n := n) (v k) z) :=
    (continuous_heatKernelVec _).measurable.ennreal_ofReal
  have hmeas2 : Measurable fun z : Fin n → ℝ =>
      ENNReal.ofReal ((∑ i, z i ^ 2) / δ ^ 2 * heatKernelVec (v k) z) := by
    have : Continuous fun z : Fin n → ℝ => (∑ i, z i ^ 2) / δ ^ 2 * heatKernelVec (v k) z :=
      ((continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2).div_const _).mul
        (continuous_heatKernelVec _)
    exact this.measurable.ennreal_ofReal
  calc ∫⁻ x, ‖smoothVec (v k) g x - g x‖ₑ
      ≤ ∫⁻ z, ENNReal.ofReal (heatKernelVec (v k) z) * ω z := hpt k
    _ ≤ ∫⁻ z, (ENNReal.ofReal (heatKernelVec (v k) z) * (ε / 2) +
        B * ENNReal.ofReal ((∑ i, z i ^ 2) / δ ^ 2 * heatKernelVec (v k) z)) := by
        refine lintegral_mono fun z => ?_
        have hS : 0 ≤ (∑ i, z i ^ 2) / δ ^ 2 :=
          div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
        calc ENNReal.ofReal (heatKernelVec (v k) z) * ω z
            ≤ ENNReal.ofReal (heatKernelVec (v k) z) *
                (ε / 2 + B * ENNReal.ofReal ((∑ i, z i ^ 2) / δ ^ 2)) := by
              gcongr
              exact hωb z
          _ = _ := by
              rw [ENNReal.ofReal_mul hS]
              ring
    _ = ε / 2 + B * ENNReal.ofReal (n * v k / δ ^ 2) := by
        rw [lintegral_add_left (hmeas.mul_const _), lintegral_mul_const _ hmeas,
          lintegral_const_mul _ hmeas2, lintegral_heatKernelVec' hvk, one_mul,
          ← ofReal_integral_eq_lintegral_ofReal hmi
            (ae_of_all _ fun z => by
              have := heatKernelVec_pos hvk z
              have : 0 ≤ (∑ i, z i ^ 2) / δ ^ 2 :=
                div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
              positivity), hm]
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl hk
    _ = ε := ENNReal.add_halves ε

private lemma tendsto_smoothVec {f : (Fin n → ℝ) → ℝ} (hfm : Measurable f) (hfi : Integrable f)
    {v : ℕ → ℝ} (hv0 : ∀ k, 0 < v k) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ x, ‖smoothVec (v k) f x - f x‖ₑ) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  obtain ⟨g, hgs, hfg, hgc, hgi⟩ :=
    Integrable.exists_hasCompactSupport_lintegral_sub_le hfi (ENNReal.half_pos hε2).ne'
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (tendsto_smoothVec_of_compact hgc hgs hv0 hv))
    (ε / 2) (ENNReal.half_pos hε.ne')] with k hk
  have hvk := hv0 k
  have hd : Measurable fun y => f y - g y := hfm.sub hgc.measurable
  have m1 : Measurable fun x => ‖smoothVec (v k) (fun y => f y - g y) x‖ₑ :=
    (measurable_smoothVec _ hd).enorm
  have m2 : Measurable fun x => ‖smoothVec (v k) g x - g x‖ₑ :=
    ((measurable_smoothVec _ hgc.measurable).sub hgc.measurable).enorm
  calc ∫⁻ x, ‖smoothVec (v k) f x - f x‖ₑ
      ≤ ∫⁻ x, (‖smoothVec (v k) (fun y => f y - g y) x‖ₑ + ‖smoothVec (v k) g x - g x‖ₑ +
          ‖f x - g x‖ₑ) := by
        refine lintegral_mono fun x => ?_
        have e : smoothVec (v k) f x - f x = smoothVec (v k) (fun y => f y - g y) x +
            (smoothVec (v k) g x - g x) - (f x - g x) := by
          rw [← smoothVec_sub hvk hfi hgi x]
          ring
        rw [e]
        exact enorm_sub_le.trans (add_le_add (enorm_add_le _ _) le_rfl)
    _ = (∫⁻ x, ‖smoothVec (v k) (fun y => f y - g y) x‖ₑ) +
          (∫⁻ x, ‖smoothVec (v k) g x - g x‖ₑ) + ∫⁻ x, ‖f x - g x‖ₑ := by
        have m12 : Measurable fun x => ‖smoothVec (v k) (fun y => f y - g y) x‖ₑ +
            ‖smoothVec (v k) g x - g x‖ₑ := m1.add m2
        rw [lintegral_add_left m12, lintegral_add_left m1]
    _ ≤ ε / 2 / 2 + ε / 2 + ε / 2 / 2 :=
        add_le_add (add_le_add ((lintegral_smoothVec_le hvk hd).trans hfg) hk) hfg
    _ = ε := by rw [add_right_comm, ENNReal.add_halves, ENNReal.add_halves]

private noncomputable def logConstVec (n : ℕ) : ℝ := n / 2 * Real.log (2 * Real.pi * 1)

private noncomputable def klTermVec (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  t * Real.log t + t * ((∑ i, x i ^ 2) / (2 * 1)) + logConstVec n * t - t + heatKernelVec 1 x

private lemma klTermVec_nonneg (x : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ klTermVec x t := by
  have hφ := heatKernelVec_pos one_pos x
  rcases ht.eq_or_lt with rfl | ht
  · simp [klTermVec, hφ.le]
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos ht hφ)
    rw [Real.log_div ht.ne' hφ.ne', log_heatKernelVec one_pos, inv_div] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 ht.le
    have e : t * (1 - heatKernelVec 1 x / t) = t - heatKernelVec 1 x := by field_simp
    rw [e] at h2
    simp only [klTermVec, logConstVec]
    nlinarith

private lemma continuous_klTermVec_comp {p : (Fin n → ℝ) → ℝ} (hp : Continuous p) :
    Continuous fun x => klTermVec x (p x) :=
  ((((Real.continuous_mul_log.comp hp).add (hp.mul ((continuous_finsetSum _ fun i _ =>
    (continuous_apply i).pow 2).div_const _))).add (continuous_const.mul hp)).sub hp).add
    (continuous_heatKernelVec 1)

private lemma klTermVec_integral {m : Measure (Fin n → ℝ)} [IsProbabilityMeasure m]
    (hac : m ≪ volume) (hf : Integrable (fun x => Real.negMulLog (m.rnDeriv volume x).toReal))
    (h2 : Integrable (fun y => ∑ i, y i ^ 2) m) :
    Integrable (fun x => klTermVec x (m.rnDeriv volume x).toReal) ∧
      ∫ x, klTermVec x (m.rnDeriv volume x).toReal
        = -measureDiffEntropy m + (∫ y, ∑ i, y i ^ 2 ∂m) / (2 * 1) + logConstVec n := by
  set t := fun x => (m.rnDeriv volume x).toReal with ht
  have i1 : Integrable fun x => t x * Real.log (t x) :=
    hf.neg.congr (ae_of_all _ fun x => by simp [Real.negMulLog, t])
  have i2 : Integrable fun x => t x * ((∑ i, x i ^ 2) / (2 * 1)) :=
    (integrable_toReal_rnDeriv_mul_iff hac).2 (h2.div_const _)
  have i4 : Integrable t := Measure.integrable_toReal_rnDeriv
  have i3 : Integrable fun x => logConstVec n * t x := i4.const_mul _
  have i5 : Integrable (heatKernelVec (n := n) 1) := integrable_heatKernelVec one_pos
  have e : (fun x => klTermVec x (t x)) = fun x => t x * Real.log (t x) +
      t x * ((∑ i, x i ^ 2) / (2 * 1)) + logConstVec n * t x - t x + heatKernelVec 1 x := rfl
  have j1 : Integrable fun x => t x * Real.log (t x) + t x * ((∑ i, x i ^ 2) / (2 * 1)) :=
    i1.add i2
  have j2 : Integrable fun x => t x * Real.log (t x) + t x * ((∑ i, x i ^ 2) / (2 * 1)) +
      logConstVec n * t x := j1.add i3
  have j3 : Integrable fun x => t x * Real.log (t x) + t x * ((∑ i, x i ^ 2) / (2 * 1)) +
      logConstVec n * t x - t x := j2.sub i4
  refine ⟨j3.add i5, ?_⟩
  have hI1 : ∫ x, t x * Real.log (t x) = -measureDiffEntropy m := by
    rw [measureDiffEntropy, ← integral_neg]
    congr 1
    ext x
    simp [Real.negMulLog, t]
  have hI2 : ∫ x, t x * ((∑ i, x i ^ 2) / (2 * 1)) = (∫ y, ∑ i, y i ^ 2 ∂m) / (2 * 1) := by
    rw [integral_toReal_rnDeriv_mul hac, integral_div]
  have hI4 : ∫ x, t x = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac, probReal_univ]
  rw [e, integral_add j3 i5, integral_sub j2 i4, integral_add j1 i3, integral_add i1 i2,
    integral_const_mul, hI1, hI2, hI4, integral_heatKernelVec one_pos]
  ring

variable {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]

private lemma lintegral_klTermVec_le (h2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {c : ℝ}
    (hc : ∀ v : ℝ, 0 < v → c ≤ ∫ x, Real.negMulLog (heatDensityVec μ v x)) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x, ENNReal.ofReal (klTermVec x (heatDensityVec μ s x))
        ≤ ENNReal.ofReal (-c + (∫ y, ∑ i, y i ^ 2 ∂μ + n * s) / (2 * 1) + logConstVec n) ∧
      0 ≤ -c + (∫ y, ∑ i, y i ^ 2 ∂μ + n * s) / (2 * 1) + logConstVec n := by
  set P := heatDensityVec μ s
  have hP : ∀ x, 0 < P x := heatDensityVec_pos hs
  obtain ⟨hPi2, hPM⟩ := integral_sum_sq_mul_heatDensityVec h2 hs
  have i1 : Integrable fun x => P x * Real.log (P x) :=
    (integrable_negMulLog_heatDensityVec h2 hs).neg.congr
      (ae_of_all _ fun x => by simp [Real.negMulLog, P])
  have i2 : Integrable fun x => P x * ((∑ i, x i ^ 2) / (2 * 1)) :=
    (hPi2.div_const (2 * 1)).congr (ae_of_all _ fun x => by simp only [P]; ring)
  have i4 : Integrable P := integrable_heatDensityVec h2 hs
  have i3 : Integrable fun x => logConstVec n * P x := i4.const_mul _
  have i5 : Integrable (heatKernelVec (n := n) 1) := integrable_heatKernelVec one_pos
  have e : (fun x => klTermVec x (P x)) = fun x => P x * Real.log (P x) +
      P x * ((∑ i, x i ^ 2) / (2 * 1)) + logConstVec n * P x - P x + heatKernelVec 1 x := rfl
  have j1 : Integrable fun x => P x * Real.log (P x) + P x * ((∑ i, x i ^ 2) / (2 * 1)) :=
    i1.add i2
  have j2 : Integrable fun x => P x * Real.log (P x) + P x * ((∑ i, x i ^ 2) / (2 * 1)) +
      logConstVec n * P x := j1.add i3
  have j3 : Integrable fun x => P x * Real.log (P x) + P x * ((∑ i, x i ^ 2) / (2 * 1)) +
      logConstVec n * P x - P x := j2.sub i4
  have hKi : Integrable fun x => klTermVec x (P x) := e ▸ (j3.add i5)
  have hI1 : ∫ x, P x * Real.log (P x) = -∫ x, Real.negMulLog (P x) := by
    rw [← integral_neg]
    congr 1
    ext x
    simp [Real.negMulLog]
  have hI2 : ∫ x, P x * ((∑ i, x i ^ 2) / (2 * 1))
      = (∫ y, ∑ i, y i ^ 2 ∂μ + n * s) / (2 * 1) := by
    rw [← hPM, ← integral_div]
    congr 1
    ext x
    simp only [P]
    ring
  have hK : ∫ x, klTermVec x (P x)
      = -(∫ x, Real.negMulLog (P x)) + (∫ y, ∑ i, y i ^ 2 ∂μ + n * s) / (2 * 1) +
        logConstVec n := by
    rw [e, integral_add j3 i5, integral_sub j2 i4, integral_add j1 i3, integral_add i1 i2,
      integral_const_mul, hI1, hI2, integral_heatDensityVec hs, integral_heatKernelVec one_pos]
    ring
  have hcs := hc s hs
  have hK0 : 0 ≤ ∫ x, klTermVec x (P x) :=
    integral_nonneg fun x => klTermVec_nonneg x (hP x).le
  have hle : ∫ x, klTermVec x (P x)
      ≤ -c + (∫ y, ∑ i, y i ^ 2 ∂μ + n * s) / (2 * 1) + logConstVec n := by
    rw [hK]
    linarith
  refine ⟨?_, hK0.trans hle⟩
  calc ∫⁻ x, ENNReal.ofReal (klTermVec x (P x))
      = ENNReal.ofReal (∫ x, klTermVec x (P x)) :=
        (ofReal_integral_eq_lintegral_ofReal hKi
          (ae_of_all _ fun x => klTermVec_nonneg x (hP x).le)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

theorem le_measureDiffEntropy_of_le_heatEntropyVec (hac : μ ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog (μ.rnDeriv volume x).toReal))
    (h2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {c : ℝ}
    (hc : ∀ v : ℝ, 0 < v → c ≤ ∫ x, Real.negMulLog (heatDensityVec μ v x)) :
    c ≤ measureDiffEntropy μ := by
  set f := fun x => (μ.rnDeriv volume x).toReal with hfdef
  have hfm : Measurable f := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hfi : Integrable f := Measure.integrable_toReal_rnDeriv
  set v : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hv0 : ∀ k, 0 < v k := fun k => by positivity
  have hv : Tendsto v atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsm : ∀ s, heatDensityVec μ s = smoothVec s f := fun s => by
    ext x
    simp only [heatDensityVec, smoothVec]
    rw [← integral_rnDeriv_smul hac]
    rfl
  have hmeas : TendstoInMeasure volume (fun k => heatDensityVec μ (v k)) atTop f := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero ?_
    refine (tendsto_smoothVec hfm hfi hv0 hv).congr fun k => ?_
    rw [eLpNorm_one_eq_lintegral_enorm
      ((continuous_heatDensityVec (hv0 k)).aestronglyMeasurable.sub hfm.aestronglyMeasurable), hsm]
    rfl
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  set M := ∫ y, ∑ i, y i ^ 2 ∂μ
  set b : ℝ → ℝ := fun s => -c + (M + n * s) / (2 * 1) + logConstVec n
  have hb : Tendsto (fun k => b (v (ns k))) atTop (𝓝 (b 0)) := by
    have := (((((hv.comp hns.tendsto_atTop).const_mul (n : ℝ)).const_add M).div_const
      (2 * 1)).const_add (-c)).add_const (logConstVec n)
    simpa [b] using this
  have hb0 : 0 ≤ b 0 :=
    ge_of_tendsto' hb fun k => (lintegral_klTermVec_le h2 hc (hv0 (ns k))).2
  obtain ⟨hKi, hK⟩ := klTermVec_integral hac hf h2
  have hlim : ∀ᵐ x, Tendsto (fun k => ENNReal.ofReal (klTermVec x (heatDensityVec μ (v (ns k)) x)))
      atTop (𝓝 (ENNReal.ofReal (klTermVec x (f x)))) := by
    filter_upwards [hae] with x hx
    have hcont : Continuous fun t => klTermVec x t :=
      (((Real.continuous_mul_log.add (continuous_id.mul continuous_const)).add
        (continuous_const.mul continuous_id)).sub continuous_id).add continuous_const
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((hcont.tendsto _).comp hx)
  have hF := lintegral_liminf_le' (μ := volume) (u := atTop)
    (f := fun k x => ENNReal.ofReal (klTermVec x (heatDensityVec μ (v (ns k)) x)))
    (fun k => (continuous_klTermVec_comp
      (continuous_heatDensityVec (hv0 (ns k)))).measurable.ennreal_ofReal.aemeasurable)
  have hmain : ENNReal.ofReal (∫ x, klTermVec x (f x)) ≤ ENNReal.ofReal (b 0) := by
    calc ENNReal.ofReal (∫ x, klTermVec x (f x))
        = ∫⁻ x, ENNReal.ofReal (klTermVec x (f x)) :=
          ofReal_integral_eq_lintegral_ofReal hKi
            (ae_of_all _ fun x => klTermVec_nonneg x ENNReal.toReal_nonneg)
      _ = ∫⁻ x, liminf (fun k => ENNReal.ofReal
            (klTermVec x (heatDensityVec μ (v (ns k)) x))) atTop :=
          lintegral_congr_ae (hlim.mono fun x hx => hx.liminf_eq.symm)
      _ ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal
            (klTermVec x (heatDensityVec μ (v (ns k)) x))) atTop := hF
      _ ≤ liminf (fun k => ENNReal.ofReal (b (v (ns k)))) atTop :=
          liminf_le_liminf
            (Eventually.of_forall fun k => (lintegral_klTermVec_le h2 hc (hv0 (ns k))).1)
      _ = ENNReal.ofReal (b 0) := (ENNReal.tendsto_ofReal hb).liminf_eq
  rw [ENNReal.ofReal_le_ofReal_iff hb0, hK] at hmain
  simp only [b, mul_zero, add_zero] at hmain
  linarith

def EntropyPowerInequalityVec (n : ℕ) : Prop :=
  ∀ (ν ρ : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ],
    ν ≪ volume → ρ ≪ volume →
    Integrable (fun y => ∑ i, y i ^ 2) ν → Integrable (fun y => ∑ i, y i ^ 2) ρ →
    Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal) →
    Integrable (fun x => Real.negMulLog (ρ.rnDeriv volume x).toReal) →
    Integrable (fun x => Real.negMulLog ((ν ∗ ρ).rnDeriv volume x).toReal) →
    Real.exp (2 * measureDiffEntropy ν / n) + Real.exp (2 * measureDiffEntropy ρ / n)
      ≤ Real.exp (2 * measureDiffEntropy (ν ∗ ρ) / n)

theorem entropyPowerInequalityVec (hn : 0 < n) : EntropyPowerInequalityVec n := by
  intro ν ρ _ _ hν hρ h2ν h2ρ hfν hfρ hfνρ
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set A := Real.exp (2 * measureDiffEntropy ν / n) + Real.exp (2 * measureDiffEntropy ρ / n)
  have hA : 0 < A := by positivity
  have hac : ν ∗ ρ ≪ volume := by
    rw [Measure.conv_comm]
    exact Measure.conv_absolutelyContinuous hν
  have h2 := integrable_sum_sq_conv h2ν h2ρ
  have key : n / 2 * Real.log A ≤ measureDiffEntropy (ν ∗ ρ) := by
    refine le_measureDiffEntropy_of_le_heatEntropyVec hac hfνρ h2 fun s hs => ?_
    have h := entropyPowerInequalityVec_conv_gaussianVec hn hν h2ν hfν hρ h2ρ hfρ hs
    rw [measureDiffEntropy_conv_gaussianVec hs] at h
    have := Real.log_le_log hA h
    rw [Real.log_exp, le_div_iff₀ hn'] at this
    linarith
  have hlog : Real.log A ≤ 2 * measureDiffEntropy (ν ∗ ρ) / n := by
    rw [le_div_iff₀ hn']
    linarith
  calc A = Real.exp (Real.log A) := (Real.exp_log hA).symm
    _ ≤ Real.exp (2 * measureDiffEntropy (ν ∗ ρ) / n) := Real.exp_le_exp.2 hlog

theorem exp_weighted_add_le {W : Type*} [Fintype W] {p : W → ℝ} (hp0 : ∀ w, 0 ≤ p w)
    (hp1 : ∑ w, p w = 1) {x y z : W → ℝ}
    (h : ∀ w, Real.exp (x w) + Real.exp (y w) ≤ Real.exp (z w)) :
    Real.exp (∑ w, p w * x w) + Real.exp (∑ w, p w * y w) ≤ Real.exp (∑ w, p w * z w) := by
  set t : W → ℝ := fun w => Real.log (Real.exp (x w) + Real.exp (y w))
  have ht : ∀ w, Real.exp (t w) = Real.exp (x w) + Real.exp (y w) := fun w =>
    Real.exp_log (by positivity)
  have htz : ∀ w, t w ≤ z w := fun w => by
    rw [← Real.exp_le_exp, ht]
    exact h w
  have hprod : ∀ f : W → ℝ, Real.exp (∑ w, p w * f w) = ∏ w, Real.exp (f w) ^ p w := by
    intro f
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Real.exp_mul, mul_comm]
  have hamgm : ∀ f : W → ℝ, Real.exp (∑ w, p w * (f w - t w))
      ≤ ∑ w, p w * Real.exp (f w - t w) := fun f => by
    rw [hprod]
    exact Real.geom_mean_le_arith_mean_weighted Finset.univ p _ (fun w _ => hp0 w) hp1
      (fun w _ => (Real.exp_pos _).le)
  have hsplit : ∀ f : W → ℝ, Real.exp (∑ w, p w * f w)
      = Real.exp (∑ w, p w * t w) * Real.exp (∑ w, p w * (f w - t w)) := fun f => by
    rw [← Real.exp_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun w _ => by ring
  have hone : ∑ w, p w * Real.exp (x w - t w) + ∑ w, p w * Real.exp (y w - t w) = 1 := by
    rw [← Finset.sum_add_distrib, ← hp1]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.exp_sub, Real.exp_sub, ht, ← mul_add, ← add_div, div_self (by positivity), mul_one]
  have hE : 0 < Real.exp (∑ w, p w * t w) := Real.exp_pos _
  have hT : Real.exp (∑ w, p w * t w) ≤ Real.exp (∑ w, p w * z w) :=
    Real.exp_le_exp.2 (Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (htz w) (hp0 w))
  rw [hsplit x, hsplit y]
  calc Real.exp (∑ w, p w * t w) * Real.exp (∑ w, p w * (x w - t w)) +
        Real.exp (∑ w, p w * t w) * Real.exp (∑ w, p w * (y w - t w))
      ≤ Real.exp (∑ w, p w * t w) * ∑ w, p w * Real.exp (x w - t w) +
        Real.exp (∑ w, p w * t w) * ∑ w, p w * Real.exp (y w - t w) :=
        add_le_add (mul_le_mul_of_nonneg_left (hamgm x) hE.le)
          (mul_le_mul_of_nonneg_left (hamgm y) hE.le)
    _ = Real.exp (∑ w, p w * t w) := by rw [← mul_add, hone, mul_one]
    _ ≤ _ := hT

theorem conditionalEntropyPowerInequalityVec (hn : 0 < n) {W : Type*} [Fintype W] {p : W → ℝ}
    (hp0 : ∀ w, 0 ≤ p w) (hp1 : ∑ w, p w = 1) (ν ρ : W → Measure (Fin n → ℝ))
    [∀ w, IsProbabilityMeasure (ν w)] [∀ w, IsProbabilityMeasure (ρ w)]
    (hν : ∀ w, ν w ≪ volume) (hρ : ∀ w, ρ w ≪ volume)
    (h2ν : ∀ w, Integrable (fun y => ∑ i, y i ^ 2) (ν w))
    (h2ρ : ∀ w, Integrable (fun y => ∑ i, y i ^ 2) (ρ w))
    (hfν : ∀ w, Integrable (fun x => Real.negMulLog ((ν w).rnDeriv volume x).toReal))
    (hfρ : ∀ w, Integrable (fun x => Real.negMulLog ((ρ w).rnDeriv volume x).toReal))
    (hfνρ : ∀ w, Integrable (fun x => Real.negMulLog ((ν w ∗ ρ w).rnDeriv volume x).toReal)) :
    Real.exp (2 * (∑ w, p w * measureDiffEntropy (ν w)) / n) +
        Real.exp (2 * (∑ w, p w * measureDiffEntropy (ρ w)) / n)
      ≤ Real.exp (2 * (∑ w, p w * measureDiffEntropy (ν w ∗ ρ w)) / n) := by
  have e : ∀ f : W → ℝ, 2 * (∑ w, p w * f w) / n = ∑ w, p w * (2 * f w / n) := fun f => by
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [e, e, e]
  exact exp_weighted_add_le hp0 hp1 fun w =>
    entropyPowerInequalityVec hn (ν w) (ρ w) (hν w) (hρ w) (h2ν w) (h2ρ w) (hfν w) (hfρ w)
      (hfνρ w)

end Meat
