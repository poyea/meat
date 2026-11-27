import Meat.Continuous.HeatFlowVec

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

variable {n : ℕ}

theorem integral_eq_zero_of_hasDerivAt_update {F G : (Fin n → ℝ) → ℝ} (i : Fin n)
    (hd : ∀ x r, HasDerivAt (fun r => F (Function.update x i r)) (G (Function.update x i r)) r)
    (hF : Integrable F) (hG : Integrable G) : ∫ x, G x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have he : MeasurePreserving e.symm (volume.prod volume) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm
  have hG' : Integrable (fun p => G (e.symm p)) (volume.prod volume) :=
    (he.integrable_comp_emb e.symm.measurableEmbedding).2 hG
  have hF' : Integrable (fun p => F (e.symm p)) (volume.prod volume) :=
    (he.integrable_comp_emb e.symm.measurableEmbedding).2 hF
  rw [← he.integral_comp' G, integral_prod_symm _ hG']
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [hG'.prod_left_ae, hF'.prod_left_ae] with v hGv hFv
  refine integral_eq_zero_of_hasDerivAt_of_integrable (fun a => ?_) hGv hFv
  have h := hd (e.symm (a, v)) a
  have e1 : ∀ r, Function.update (e.symm (a, v)) i r = e.symm (r, v) := fun r => by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk]
    exact Fin.update_insertNth (α := fun _ => ℝ) i a r v
  simp only [e1] at h
  exact h

theorem integrable_heatKernelVec {s : ℝ} (hs : 0 < s) :
    Integrable (heatKernelVec (n := n) s) := by
  have h1 : Integrable (heatKernel s) :=
    Integrable.of_integral_ne_zero (by rw [(integral_mul_heatKernel_moment hs).1]; norm_num)
  have h := Integrable.fintype_prod (f := fun (_ : Fin n) => heatKernel s)
    (μ := fun _ => volume) fun _ => h1
  rw [← volume_pi] at h
  exact h

theorem integral_heatKernelVec {s : ℝ} (hs : 0 < s) : ∫ u, heatKernelVec (n := n) s u = 1 := by
  rw [show (fun u => heatKernelVec (n := n) s u) = fun u => ∏ i, heatKernel s (u i) from rfl,
    integral_fintype_prod_volume_eq_prod (fun (_ : Fin n) => heatKernel s),
    (integral_mul_heatKernel_moment hs).1, Finset.prod_const_one]

variable {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]

private lemma exists_ball_half (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    ∃ R : ℝ, 0 ≤ R ∧ 1 / 2 ≤ μ.real (Metric.closedBall 0 R) := by
  have hmono : Monotone fun k : ℕ => Metric.closedBall (0 : Fin n → ℝ) k := fun a b h =>
    Metric.closedBall_subset_closedBall (by exact_mod_cast h)
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [Metric.iUnion_closedBall_nat, measure_univ] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ≥0∞) < 1))).exists
  refine ⟨k, k.cast_nonneg, ?_⟩
  rw [measureReal_def]
  have h := ENNReal.toReal_mono (measure_ne_top _ _) hk.le
  simpa using h

private lemma heatKernel_ge {a b s R x y : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (hy : |y| ≤ R) :
    (Real.sqrt (2 * Real.pi * b))⁻¹ * Real.exp (-(x ^ 2 + R ^ 2) / a) ≤ heatKernel s (x - y) := by
  have hs : 0 < s := ha.trans_le has
  have hpi := Real.pi_pos
  have hy2 : y ^ 2 ≤ R ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
  unfold heatKernel
  have h1 : (Real.sqrt (2 * Real.pi * b))⁻¹ ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ := by
    have : 0 < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.2 (by positivity)
    gcongr
  have h2 : -(x ^ 2 + R ^ 2) / a ≤ -(x - y) ^ 2 / (2 * s) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    calc (x - y) ^ 2 / (2 * s) ≤ (2 * x ^ 2 + 2 * y ^ 2) / (2 * s) := by
          gcongr
          nlinarith [sq_nonneg (x + y)]
      _ = (x ^ 2 + y ^ 2) / s := by field_simp
      _ ≤ (x ^ 2 + R ^ 2) / s := by gcongr
      _ ≤ (x ^ 2 + R ^ 2) / a := div_le_div_of_nonneg_left (by positivity) ha has
  exact mul_le_mul h1 (Real.exp_le_exp.2 h2) (Real.exp_pos _).le (by positivity)

private lemma heatDensityVec_ge {a b s R : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (hR : 1 / 2 ≤ μ.real (Metric.closedBall 0 R)) (x : Fin n → ℝ) :
    1 / 2 * ((Real.sqrt (2 * Real.pi * b))⁻¹ ^ n *
      Real.exp (-(∑ i, x i ^ 2 + n * R ^ 2) / a)) ≤ heatDensityVec μ s x := by
  have hs : 0 < s := ha.trans_le has
  have hpi := Real.pi_pos
  set m := (Real.sqrt (2 * Real.pi * b))⁻¹ ^ n * Real.exp (-(∑ i, x i ^ 2 + n * R ^ 2) / a)
  have hm : 0 ≤ m := by positivity
  have hsum : ∑ i, -(x i ^ 2 + R ^ 2) / a = -(∑ i, x i ^ 2 + n * R ^ 2) / a := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_add_distrib]
    simp
  have hk : ∀ y ∈ Metric.closedBall (0 : Fin n → ℝ) R, m ≤ heatKernelVec s (x - y) := by
    intro y hy
    have hyi : ∀ i, |y i| ≤ R := fun i =>
      (Real.norm_eq_abs (y i) ▸ norm_le_pi_norm y i).trans (mem_closedBall_zero_iff.1 hy)
    calc m = ∏ i, ((Real.sqrt (2 * Real.pi * b))⁻¹ * Real.exp (-(x i ^ 2 + R ^ 2) / a)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← Real.exp_sum, hsum]
      _ ≤ ∏ i, heatKernel s (x i - y i) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity)
            fun i _ => heatKernel_ge ha has hsb (hyi i)
      _ = heatKernelVec s (x - y) := rfl
  have hint := integrable_heatKernelVec_comp (μ := μ) hs le_rfl le_rfl x
  calc 1 / 2 * m ≤ m * μ.real (Metric.closedBall 0 R) := by nlinarith
    _ ≤ ∫ y in Metric.closedBall 0 R, heatKernelVec s (x - y) ∂μ :=
        setIntegral_ge_of_const_le_real Metric.isClosed_closedBall.measurableSet
          (measure_ne_top _ _) hk hint.integrableOn
    _ ≤ heatDensityVec μ s x :=
        setIntegral_le_integral hint (ae_of_all _ fun y => (heatKernelVec_pos hs _).le)

private noncomputable def logConstVec (n : ℕ) (a b R : ℝ) : ℝ :=
  1 + |Real.log ((Real.sqrt (2 * Real.pi * a))⁻¹ ^ n)| +
    |Real.log (1 / 2 * (Real.sqrt (2 * Real.pi * b))⁻¹ ^ n)| + n * R ^ 2 / a + 1 / a

private lemma logConstVec_nonneg (a b R : ℝ) (ha : 0 < a) : 0 ≤ logConstVec n a b R := by
  unfold logConstVec
  positivity

private lemma abs_one_add_log_heatDensityVec_le {a b s R : ℝ} (ha : 0 < a) (has : a ≤ s)
    (hsb : s ≤ b) (hR : 1 / 2 ≤ μ.real (Metric.closedBall 0 R)) (x : Fin n → ℝ) :
    |1 + Real.log (heatDensityVec μ s x)| ≤ logConstVec n a b R * (1 + ∑ i, x i ^ 2) := by
  have hs : 0 < s := ha.trans_le has
  have hpi := Real.pi_pos
  have hp := heatDensityVec_pos (μ := μ) hs x
  have hup : Real.log (heatDensityVec μ s x) ≤ Real.log ((Real.sqrt (2 * Real.pi * a))⁻¹ ^ n) := by
    refine Real.log_le_log hp ((heatDensityVec_le hs x).trans ?_)
    have h0 : 0 < Real.sqrt (2 * Real.pi * a) := Real.sqrt_pos.2 (by positivity)
    gcongr
  have hlow : Real.log (1 / 2 * (Real.sqrt (2 * Real.pi * b))⁻¹ ^ n) -
      (∑ i, x i ^ 2 + n * R ^ 2) / a ≤ Real.log (heatDensityVec μ s x) := by
    have hb : 0 < b := hs.trans_le hsb
    have h := Real.log_le_log (by positivity) (heatDensityVec_ge ha has hsb hR x)
    rwa [← mul_assoc, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
      neg_div, ← sub_eq_add_neg] at h
  set S := ∑ i, x i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set c1 := Real.log ((Real.sqrt (2 * Real.pi * a))⁻¹ ^ n)
  set c2 := Real.log (1 / 2 * (Real.sqrt (2 * Real.pi * b))⁻¹ ^ n)
  have hx : (S + n * R ^ 2) / a = n * R ^ 2 / a + 1 / a * S := by field_simp; ring
  rw [hx] at hlow
  have hA : 0 ≤ 1 / a := by positivity
  have hRa : 0 ≤ n * R ^ 2 / a := by positivity
  have hL : logConstVec n a b R = 1 + |c1| + |c2| + n * R ^ 2 / a + 1 / a := rfl
  rw [hL, abs_le]
  constructor
  · nlinarith [neg_abs_le c2, abs_nonneg c1, mul_nonneg (abs_nonneg c1) hS,
      mul_nonneg (abs_nonneg c2) hS, mul_nonneg hRa hS]
  · nlinarith [le_abs_self c1, abs_nonneg c2, mul_nonneg (abs_nonneg c1) hS,
      mul_nonneg (abs_nonneg c2) hS, mul_nonneg hRa hS, mul_nonneg hA hS]

private lemma heatDensityVec_le_envelope {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (x : Fin n → ℝ) : heatDensityVec μ s x ≤ ∫ y, heatEnvelopeVec a b (x - y) ∂μ := by
  have h := abs_integral_mul_heatKernelVec_le (μ := μ) (c := fun _ => 1) ha has hsb
    (fun u => heatPolyVec_one ha u) x
  simp only [one_mul] at h
  exact (le_abs_self _).trans h

private lemma sq_heatDensityVecDeriv_div_le {s : ℝ} (hs : 0 < s) (i : Fin n) (x : Fin n → ℝ) :
    heatDensityVecDeriv μ s i x ^ 2 / heatDensityVec μ s x
      ≤ ∫ y, heatEnvelopeVec s s (x - y) ∂μ := by
  have hp := heatDensityVec_pos (μ := μ) hs x
  have hc : Continuous fun u : Fin n → ℝ => -(u i / s) := by fun_prop
  have hc2 : Continuous fun u : Fin n → ℝ => u i ^ 2 / s ^ 2 := by fun_prop
  have h2 := integrable_mul_heatKernelVec (μ := μ) hs le_rfl le_rfl hc
    (fun u => heatPolyVec_deriv hs le_rfl u i) x
  have h3 := integrable_mul_heatKernelVec (μ := μ) hs le_rfl le_rfl hc2
    (fun u => heatPolyVec_sq hs le_rfl u i) x
  have hcs := sq_integral_mul_le (μ := μ) (w := fun y => heatKernelVec s (x - y))
    (f := fun y => -((x - y) i / s)) (fun y => (heatKernelVec_pos hs _).le)
    (integrable_heatKernelVec_comp hs le_rfl le_rfl x)
    (h2.congr (ae_of_all _ fun y => by simp only; ring))
    (h3.congr (ae_of_all _ fun y => by simp only; ring))
  have e1 : heatDensityVecDeriv μ s i x
      = ∫ y, heatKernelVec s (x - y) * -((x - y) i / s) ∂μ := by
    rw [heatDensityVecDeriv]
    exact integral_congr_ae (ae_of_all _ fun y => by simp only; ring)
  have e2 : ∫ y, heatKernelVec s (x - y) * (-((x - y) i / s)) ^ 2 ∂μ
      = ∫ y, (fun u : Fin n → ℝ => u i ^ 2 / s ^ 2) (x - y) * heatKernelVec s (x - y) ∂μ :=
    integral_congr_ae (ae_of_all _ fun y => by simp only; ring)
  rw [e1, div_le_iff₀ hp]
  rw [e2] at hcs
  have hb := (le_abs_self _).trans (abs_integral_mul_heatKernelVec_le (μ := μ) hs le_rfl le_rfl
    (fun u => heatPolyVec_sq hs le_rfl u i) x)
  calc _ ≤ heatDensityVec μ s x *
        ∫ y, (fun u : Fin n → ℝ => u i ^ 2 / s ^ 2) (x - y) * heatKernelVec s (x - y) ∂μ := hcs
    _ ≤ heatDensityVec μ s x * ∫ y, heatEnvelopeVec s s (x - y) ∂μ :=
        mul_le_mul_of_nonneg_left hb hp.le
    _ = _ := mul_comm _ _

private lemma integrable_envelope_weight (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {a b : ℝ}
    (hb : 0 < b) :
    Integrable fun x => (1 + ∑ i, x i ^ 2) * ∫ y, heatEnvelopeVec a b (x - y) ∂μ :=
  integrable_mul_integral_comp_sub_vec hμ2 (continuous_heatEnvelopeVec a b).measurable
    (heatEnvelopeVec_nonneg a b) (integrable_heatEnvelopeVec hb)

omit [IsProbabilityMeasure μ] in
private lemma integral_envelope_nonneg {a b : ℝ} (x : Fin n → ℝ) :
    0 ≤ ∫ y, heatEnvelopeVec a b (x - y) ∂μ :=
  integral_nonneg fun _ => heatEnvelopeVec_nonneg _ _ _

private lemma sum_sq_nonneg' (x : Fin n → ℝ) : 0 ≤ ∑ i, x i ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem integrable_negMulLog_heatDensityVec (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ)
    {s : ℝ} (hs : 0 < s) : Integrable fun x => Real.negMulLog (heatDensityVec μ s x) := by
  obtain ⟨R, -, hR⟩ := exists_ball_half μ
  set L := logConstVec n s s R
  refine Integrable.mono' ((integrable_envelope_weight (a := s) hμ2 hs).const_mul (L + 1))
    (Real.continuous_negMulLog.comp (continuous_heatDensityVec hs)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have hp := heatDensityVec_pos (μ := μ) hs x
  have hl := abs_one_add_log_heatDensityVec_le (μ := μ) hs le_rfl le_rfl hR x
  have he := heatDensityVec_le_envelope (μ := μ) hs le_rfl le_rfl x
  have hE := integral_envelope_nonneg (μ := μ) (a := s) (b := s) x
  have hL : 0 ≤ L := logConstVec_nonneg _ _ _ hs
  have hS := sum_sq_nonneg' x
  rw [Real.norm_eq_abs, Real.negMulLog, abs_mul, abs_neg, abs_of_pos hp]
  have hlog : |Real.log (heatDensityVec μ s x)| ≤ L * (1 + ∑ i, x i ^ 2) + 1 := by
    have := abs_sub (1 + Real.log (heatDensityVec μ s x)) 1
    simp only [add_sub_cancel_left, abs_one] at this
    linarith
  calc heatDensityVec μ s x * |Real.log (heatDensityVec μ s x)|
      ≤ (∫ y, heatEnvelopeVec s s (x - y) ∂μ) * (L * (1 + ∑ i, x i ^ 2) + 1) :=
        mul_le_mul he hlog (abs_nonneg _) hE
    _ ≤ (L + 1) * ((1 + ∑ i, x i ^ 2) * ∫ y, heatEnvelopeVec s s (x - y) ∂μ) := by
        nlinarith [mul_nonneg hE hS, mul_nonneg (mul_nonneg hE hS) hL]

noncomputable def heatFisherVec (μ : Measure (Fin n → ℝ)) (s : ℝ) : ℝ :=
  ∑ i, ∫ x, heatDensityVecDeriv μ s i x ^ 2 / heatDensityVec μ s x

private lemma abs_log_mul_le {a b s R : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (hR : 1 / 2 ≤ μ.real (Metric.closedBall 0 R)) {c : (Fin n → ℝ) → ℝ}
    (hcb : ∀ u, |c u| ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2)) (x : Fin n → ℝ) :
    |(1 + Real.log (heatDensityVec μ s x)) * ∫ y, c (x - y) * heatKernelVec s (x - y) ∂μ|
      ≤ logConstVec n a b R * ((1 + ∑ i, x i ^ 2) * ∫ y, heatEnvelopeVec a b (x - y) ∂μ) := by
  rw [abs_mul]
  have h1 := abs_one_add_log_heatDensityVec_le (μ := μ) ha has hsb hR x
  have h2 := abs_integral_mul_heatKernelVec_le (μ := μ) ha has hsb hcb x
  calc _ ≤ (logConstVec n a b R * (1 + ∑ i, x i ^ 2)) * ∫ y, heatEnvelopeVec a b (x - y) ∂μ :=
        mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    _ = _ := by ring

theorem integrable_heatFisherVec (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {s : ℝ}
    (hs : 0 < s) (i : Fin n) :
    Integrable fun x => heatDensityVecDeriv μ s i x ^ 2 / heatDensityVec μ s x := by
  refine Integrable.mono' (integrable_envelope_weight (a := s) hμ2 hs)
    (((continuous_heatDensityVecDeriv hs i).pow 2).div (continuous_heatDensityVec hs)
      fun x => (heatDensityVec_pos hs x).ne').aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hp := heatDensityVec_pos (μ := μ) hs x
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hp.le)]
  have hE := integral_envelope_nonneg (μ := μ) (a := s) (b := s) x
  refine (sq_heatDensityVecDeriv_div_le hs i x).trans ?_
  nlinarith [mul_nonneg hE (sum_sq_nonneg' x)]

private lemma integrable_log_mul (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {s : ℝ}
    (hs : 0 < s) {c : (Fin n → ℝ) → ℝ} (hc : Continuous c)
    (hcb : ∀ u, |c u| ≤ (n + 1) * (1 + 1 / s) ^ 2 * (1 + ∑ j, u j ^ 2)) :
    Integrable fun x => (1 + Real.log (heatDensityVec μ s x)) *
      ∫ y, c (x - y) * heatKernelVec s (x - y) ∂μ := by
  obtain ⟨R, -, hR⟩ := exists_ball_half μ
  refine Integrable.mono' ((integrable_envelope_weight (a := s) hμ2 hs).const_mul
    (logConstVec n s s R)) ((continuous_const.add ((continuous_heatDensityVec hs).log
      fun x => (heatDensityVec_pos hs x).ne')).mul
      (continuous_integral_mul_heatKernelVec hs hc hcb)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_log_mul_le hs le_rfl le_rfl hR hcb x

private lemma sum_heatDensityVecDeriv2 {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) :
    (∑ i, heatDensityVecDeriv2 μ s i x) / 2
      = ∫ y, (∑ i, ((x - y) i ^ 2 / s ^ 2 - 1 / s)) / 2 * heatKernelVec s (x - y) ∂μ := by
  have hi : ∀ i ∈ Finset.univ, Integrable
      (fun y => ((x - y) i ^ 2 / s ^ 2 - 1 / s) * heatKernelVec s (x - y)) μ := fun i _ =>
    integrable_mul_heatKernelVec (c := fun u => u i ^ 2 / s ^ 2 - 1 / s) hs le_rfl le_rfl
      (by fun_prop) (fun u => heatPolyVec_deriv2 hs le_rfl u i) x
  rw [show (∑ i, heatDensityVecDeriv2 μ s i x) = ∑ i, ∫ y,
      ((x - y) i ^ 2 / s ^ 2 - 1 / s) * heatKernelVec s (x - y) ∂μ from rfl,
    ← integral_finsetSum _ hi, ← integral_div]
  congr 1
  ext y
  rw [← Finset.sum_mul]
  ring

theorem integral_neg_log_mul_lap (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {s : ℝ}
    (hs : 0 < s) :
    ∫ x, (-Real.log (heatDensityVec μ s x) - 1) * ((∑ i, heatDensityVecDeriv2 μ s i x) / 2)
      = heatFisherVec μ s / 2 := by
  have hG2 : ∀ i, Integrable fun x =>
      (1 + Real.log (heatDensityVec μ s x)) * heatDensityVecDeriv2 μ s i x := fun i =>
    integrable_log_mul (μ := μ) hμ2 hs (c := fun u => u i ^ 2 / s ^ 2 - 1 / s) (by fun_prop)
      (fun u => heatPolyVec_deriv2 hs le_rfl u i)
  have hparts : ∀ i, ∫ x, (1 + Real.log (heatDensityVec μ s x)) * heatDensityVecDeriv2 μ s i x
      = -∫ x, heatDensityVecDeriv μ s i x ^ 2 / heatDensityVec μ s x := by
    intro i
    have hG : Integrable fun x =>
        (1 + Real.log (heatDensityVec μ s x)) * heatDensityVecDeriv μ s i x :=
      integrable_log_mul (μ := μ) hμ2 hs (c := fun u => -(u i / s)) (by fun_prop)
        (fun u => heatPolyVec_deriv hs le_rfl u i)
    have hJ := integrable_heatFisherVec hμ2 hs i
    have h0 := integral_eq_zero_of_hasDerivAt_update (F := fun x =>
      (1 + Real.log (heatDensityVec μ s x)) * heatDensityVecDeriv μ s i x)
      (G := fun x => heatDensityVecDeriv μ s i x ^ 2 / heatDensityVec μ s x +
        (1 + Real.log (heatDensityVec μ s x)) * heatDensityVecDeriv2 μ s i x) i
      (fun x r => by
        have hl := (hasDerivAt_heatDensityVec_update (μ := μ) hs x i r).log
          (heatDensityVec_pos hs _).ne'
        convert (hl.const_add 1).mul (hasDerivAt_heatDensityVecDeriv_update (μ := μ) hs x i r)
          using 1
        ring)
      hG (hJ.add (hG2 i))
    rw [integral_add hJ (hG2 i)] at h0
    linarith
  have e : ∀ x, (-Real.log (heatDensityVec μ s x) - 1) * ((∑ i, heatDensityVecDeriv2 μ s i x) / 2)
      = ∑ i, (-1 / 2) * ((1 + Real.log (heatDensityVec μ s x)) * heatDensityVecDeriv2 μ s i x) :=
    fun x => by rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => (hG2 i).const_mul _]
  simp_rw [integral_const_mul, hparts]
  rw [heatFisherVec, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem hasDerivAt_heatEntropyVec (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, Real.negMulLog (heatDensityVec μ s x)) (heatFisherVec μ t / 2) t := by
  obtain ⟨R, -, hR⟩ := exists_ball_half μ
  have ha : 0 < t / 2 := by positivity
  have hb : 0 < 2 * t := by positivity
  have hmem : Set.Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ s ∈ Set.Ioo (t / 2) (2 * t), 0 < s := fun s h => ha.trans h.1
  have hc : Continuous fun x =>
      (-Real.log (heatDensityVec μ t x) - 1) * ((∑ i, heatDensityVecDeriv2 μ t i x) / 2) :=
    (((continuous_heatDensityVec (μ := μ) ht).log fun x => (heatDensityVec_pos ht x).ne').neg.sub
      continuous_const).mul ((continuous_finsetSum _ fun i _ =>
        continuous_heatDensityVecDeriv2 ht i).div_const 2)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t)
    (F := fun s x => Real.negMulLog (heatDensityVec μ s x))
    (F' := fun s x =>
      (-Real.log (heatDensityVec μ s x) - 1) * ((∑ i, heatDensityVecDeriv2 μ s i x) / 2))
    (bound := fun x => logConstVec n (t / 2) (2 * t) R *
      ((1 + ∑ i, x i ^ 2) * ∫ y, heatEnvelopeVec (t / 2) (2 * t) (x - y) ∂μ))
    hmem
    (Filter.mem_of_superset hmem fun s hs => (Real.continuous_negMulLog.comp
      (continuous_heatDensityVec (hpos s hs))).aestronglyMeasurable)
    (integrable_negMulLog_heatDensityVec hμ2 ht)
    hc.aestronglyMeasurable
    (ae_of_all _ fun x s hs => by
      have hb' := abs_log_mul_le (μ := μ) ha hs.1.le hs.2.le hR
        (c := fun u => (∑ i, (u i ^ 2 / s ^ 2 - 1 / s)) / 2)
        (fun u => heatPolyVec_time ha hs.1.le u) x
      rw [← sum_heatDensityVecDeriv2 (hpos s hs) x] at hb'
      have e : (-Real.log (heatDensityVec μ s x) - 1) * ((∑ i, heatDensityVecDeriv2 μ s i x) / 2)
          = -((1 + Real.log (heatDensityVec μ s x)) *
            ((∑ i, heatDensityVecDeriv2 μ s i x) / 2)) := by ring
      rw [Real.norm_eq_abs, e, abs_neg]
      exact hb')
    ((integrable_envelope_weight hμ2 hb).const_mul _)
    (ae_of_all _ fun x s hs => by
      have := (Real.hasDerivAt_negMulLog (heatDensityVec_pos (μ := μ) (hpos s hs) x).ne').comp s
        (hasDerivAt_heatDensityVec_time (μ := μ) (hpos s hs) x)
      exact this)
  rw [← integral_neg_log_mul_lap hμ2 ht]
  exact h.2

theorem integrable_heatDensityVec (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {s : ℝ}
    (hs : 0 < s) : Integrable (heatDensityVec μ s) := by
  refine Integrable.mono' (integrable_envelope_weight (a := s) hμ2 hs)
    (continuous_heatDensityVec hs).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (heatDensityVec_pos hs x)]
  have hE := integral_envelope_nonneg (μ := μ) (a := s) (b := s) x
  have := heatDensityVec_le_envelope (μ := μ) hs le_rfl le_rfl x
  nlinarith [mul_nonneg hE (sum_sq_nonneg' x)]

theorem integrable_heatDensityVecDeriv (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {s : ℝ}
    (hs : 0 < s) (i : Fin n) : Integrable (heatDensityVecDeriv μ s i) := by
  refine Integrable.mono' (integrable_envelope_weight (a := s) hμ2 hs)
    (continuous_heatDensityVecDeriv hs i).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  have hE := integral_envelope_nonneg (μ := μ) (a := s) (b := s) x
  have := abs_integral_mul_heatKernelVec_le (μ := μ) (c := fun u => -(u i / s)) hs le_rfl le_rfl
    (fun u => heatPolyVec_deriv hs le_rfl u i) x
  have e : heatDensityVecDeriv μ s i x
      = ∫ y, (fun u : Fin n → ℝ => -(u i / s)) (x - y) * heatKernelVec s (x - y) ∂μ := rfl
  rw [e]
  nlinarith [mul_nonneg hE (sum_sq_nonneg' x)]

theorem integral_heatDensityVec {s : ℝ} (hs : 0 < s) : ∫ x, heatDensityVec μ s x = 1 := by
  have hK := integrable_heatKernelVec (n := n) hs
  have hc : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => heatKernelVec s (p.1 - p.2) :=
    (continuous_heatKernelVec s).comp (continuous_fst.sub continuous_snd)
  have hG : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => heatKernelVec s (p.1 - p.2))
      (volume.prod μ) := by
    refine (integrable_prod_iff' hc.aestronglyMeasurable).2
      ⟨ae_of_all _ fun y => hK.comp_sub_right y, ?_⟩
    refine (integrable_const (1 : ℝ)).congr (ae_of_all _ fun y => ?_)
    simp only
    rw [show (fun x : Fin n → ℝ => ‖heatKernelVec s (x - y)‖) = fun x => heatKernelVec s (x - y)
      from funext fun x => by rw [Real.norm_eq_abs, abs_of_pos (heatKernelVec_pos hs _)],
      integral_sub_right_eq_self (heatKernelVec s) y, integral_heatKernelVec hs]
  rw [show (fun x => heatDensityVec μ s x) = fun x => ∫ y, heatKernelVec s (x - y) ∂μ from rfl,
    integral_integral_swap (f := fun x y => heatKernelVec s (x - y)) hG]
  have : ∀ y : Fin n → ℝ, ∫ x, heatKernelVec s (x - y) = 1 := fun y => by
    rw [integral_sub_right_eq_self (heatKernelVec s) y, integral_heatKernelVec hs]
  simp_rw [this]
  simp

theorem heatFisherVec_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ heatFisherVec μ s :=
  Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun x => div_nonneg (sq_nonneg _) (heatDensityVec_pos hs x).le

end Meat
