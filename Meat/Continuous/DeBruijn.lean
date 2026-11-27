import Meat.Continuous.HeatFlow

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {w f : α → ℝ}
    (hw : ∀ y, 0 ≤ w y) (h1 : Integrable w μ) (h2 : Integrable (fun y => w y * f y) μ)
    (h3 : Integrable (fun y => w y * f y ^ 2) μ) :
    (∫ y, w y * f y ∂μ) ^ 2 ≤ (∫ y, w y ∂μ) * ∫ y, w y * f y ^ 2 ∂μ := by
  set W := ∫ y, w y ∂μ
  set A := ∫ y, w y * f y ∂μ
  set B := ∫ y, w y * f y ^ 2 ∂μ
  have hq : ∀ c : ℝ, 0 ≤ B - 2 * c * A + c ^ 2 * W := by
    intro c
    have h0 : 0 ≤ ∫ y, w y * (f y - c) ^ 2 ∂μ :=
      integral_nonneg fun y => mul_nonneg (hw y) (sq_nonneg _)
    have e : (fun y => w y * (f y - c) ^ 2)
        = fun y => w y * f y ^ 2 - (2 * c) * (w y * f y) + c ^ 2 * w y := by
      ext y
      ring
    have i1 : Integrable (fun y => w y * f y ^ 2 - 2 * c * (w y * f y)) μ :=
      h3.sub (h2.const_mul _)
    rw [e, integral_add i1 (h1.const_mul _),
      integral_sub h3 (h2.const_mul _), integral_const_mul, integral_const_mul] at h0
    linarith
  have hW : 0 ≤ W := integral_nonneg hw
  rcases hW.eq_or_lt with h0 | hp
  · by_contra hA
    have hA0 : A ≠ 0 := by
      rintro h
      rw [h, ← h0] at hA
      simp at hA
    have := hq ((B + 1) / (2 * A))
    rw [← h0] at this
    have e : 2 * ((B + 1) / (2 * A)) * A = B + 1 := by field_simp
    nlinarith
  · have := hq (A / W)
    have e : B - 2 * (A / W) * A + (A / W) ^ 2 * W = B - A ^ 2 / W := by
      field_simp
      ring
    rw [e, sub_nonneg, div_le_iff₀ hp] at this
    linarith

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

private lemma exists_Icc_half (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ R : ℝ, 0 ≤ R ∧ 1 / 2 ≤ ν.real (Set.Icc (-R) R) := by
  have hmono : Monotone fun n : ℕ => Set.Icc (-(n : ℝ)) n := fun m n hmn =>
    Set.Icc_subset_Icc (by simpa using hmn) (by simpa using hmn)
  have hU : (⋃ n : ℕ, Set.Icc (-(n : ℝ)) n) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |y|
    exact ⟨n, (abs_le.1 hn).1, (abs_le.1 hn).2⟩
  have ht := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [hU, measure_univ] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ≥0∞) < 1))).exists
  refine ⟨n, n.cast_nonneg, ?_⟩
  rw [measureReal_def]
  have h := ENNReal.toReal_mono (measure_ne_top _ _) hn.le
  simpa using h

private lemma heatDensity_ge {a b s R : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (hR : 1 / 2 ≤ ν.real (Set.Icc (-R) R)) (x : ℝ) :
    1 / 2 * ((Real.sqrt (2 * Real.pi * b))⁻¹ * Real.exp (-(x ^ 2 + R ^ 2) / a))
      ≤ heatDensity ν s x := by
  have hs : 0 < s := ha.trans_le has
  have hpi := Real.pi_pos
  set m := (Real.sqrt (2 * Real.pi * b))⁻¹ * Real.exp (-(x ^ 2 + R ^ 2) / a)
  have hm : 0 ≤ m := by positivity
  have hk : ∀ y ∈ Set.Icc (-R) R, m ≤ heatKernel s (x - y) := by
    intro y hy
    have hy2 : y ^ 2 ≤ R ^ 2 := by
      have := abs_le.2 hy
      nlinarith [abs_nonneg y, sq_abs y]
    unfold heatKernel
    change (Real.sqrt (2 * Real.pi * b))⁻¹ * Real.exp (-(x ^ 2 + R ^ 2) / a) ≤ _
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
  have hint := integrable_heatKernel_comp (ν := ν) hs le_rfl le_rfl x
  calc 1 / 2 * m ≤ m * ν.real (Set.Icc (-R) R) := by nlinarith
    _ ≤ ∫ y in Set.Icc (-R) R, heatKernel s (x - y) ∂ν :=
        setIntegral_ge_of_const_le_real measurableSet_Icc (measure_ne_top _ _) hk
          hint.integrableOn
    _ ≤ heatDensity ν s x :=
        setIntegral_le_integral hint (ae_of_all _ fun y => (heatKernel_pos hs _).le)

private noncomputable def logConst (a b R : ℝ) : ℝ :=
  1 + |Real.log (Real.sqrt (2 * Real.pi * a))⁻¹| +
    |Real.log (1 / 2 * (Real.sqrt (2 * Real.pi * b))⁻¹)| + R ^ 2 / a + 1 / a

private lemma abs_one_add_log_heatDensity_le {a b s R : ℝ} (ha : 0 < a) (has : a ≤ s)
    (hsb : s ≤ b) (hR : 1 / 2 ≤ ν.real (Set.Icc (-R) R)) (x : ℝ) :
    |1 + Real.log (heatDensity ν s x)| ≤ logConst a b R * (1 + x ^ 2) := by
  have hs : 0 < s := ha.trans_le has
  have hb : 0 < b := hs.trans_le hsb
  have hpi := Real.pi_pos
  have hp := heatDensity_pos (ν := ν) hs x
  have hup : Real.log (heatDensity ν s x) ≤ Real.log (Real.sqrt (2 * Real.pi * a))⁻¹ := by
    refine Real.log_le_log hp ((heatDensity_le hs x).trans ?_)
    gcongr
  have hlow : Real.log (1 / 2 * (Real.sqrt (2 * Real.pi * b))⁻¹) - (x ^ 2 + R ^ 2) / a
      ≤ Real.log (heatDensity ν s x) := by
    have h := Real.log_le_log (by positivity) (heatDensity_ge ha has hsb hR x)
    rwa [← mul_assoc, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
      neg_div, ← sub_eq_add_neg] at h
  set c1 := Real.log (Real.sqrt (2 * Real.pi * a))⁻¹
  set c2 := Real.log (1 / 2 * (Real.sqrt (2 * Real.pi * b))⁻¹)
  have hx : (x ^ 2 + R ^ 2) / a = R ^ 2 / a + 1 / a * x ^ 2 := by field_simp; ring
  rw [hx] at hlow
  have hA : 0 ≤ 1 / a := by positivity
  have hRa : 0 ≤ R ^ 2 / a := by positivity
  have hL : logConst a b R = 1 + |c1| + |c2| + R ^ 2 / a + 1 / a := rfl
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  rw [abs_le]
  constructor
  · nlinarith [neg_abs_le c2, abs_nonneg c1, mul_nonneg (abs_nonneg c1) hx2,
      mul_nonneg (abs_nonneg c2) hx2, mul_nonneg hRa hx2]
  · nlinarith [le_abs_self c1, abs_nonneg c2, mul_nonneg (abs_nonneg c1) hx2,
      mul_nonneg (abs_nonneg c2) hx2, mul_nonneg hRa hx2, mul_nonneg hA hx2]

theorem heatPoly_sq {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (u : ℝ) :
    |u ^ 2 / s ^ 2| ≤ (1 + 1 / a) ^ 2 * (1 + u ^ 2) := by
  have h := heatPoly_deriv2 ha has u
  have hs : 0 < s := ha.trans_le has
  have hq : 1 / s ≤ 1 / a := one_div_le_one_div_of_le ha has
  have hq0 : 0 ≤ 1 / s := by positivity
  have hA : 0 ≤ 1 / a := by positivity
  have e : u ^ 2 / s ^ 2 = u ^ 2 * (1 / s) ^ 2 := by ring
  have hq2 : (1 / s) ^ 2 ≤ (1 / a) ^ 2 := pow_le_pow_left₀ hq0 hq 2
  rw [e, abs_of_nonneg (by positivity)]
  have : u ^ 2 * (1 / s) ^ 2 ≤ u ^ 2 * (1 / a) ^ 2 := mul_le_mul_of_nonneg_left hq2 (sq_nonneg u)
  nlinarith [sq_nonneg u, mul_nonneg hA (sq_nonneg u), sq_nonneg (1 / a)]

private lemma heatDensity_le_envelope {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (x : ℝ) : heatDensity ν s x ≤ ∫ y, heatEnvelope a b (x - y) ∂ν := by
  have h := abs_integral_mul_heatKernel_le (ν := ν) (c := fun _ => 1) ha has hsb
    (fun u => heatPoly_one ha u) x
  simp only [one_mul] at h
  exact (le_abs_self _).trans h

private lemma sq_heatDensityDeriv_div_le {s : ℝ} (hs : 0 < s) (x : ℝ) :
    heatDensityDeriv ν s x ^ 2 / heatDensity ν s x
      ≤ ∫ y, heatEnvelope s s (x - y) ∂ν := by
  have hp := heatDensity_pos (ν := ν) hs x
  have hc : Continuous fun u : ℝ => -(u / s) := (continuous_id.div_const s).neg
  have hc2 : Continuous fun u : ℝ => u ^ 2 / s ^ 2 := by fun_prop
  have h2 := integrable_mul_heatKernel (ν := ν) hs le_rfl le_rfl hc
    (fun u => heatPoly_deriv hs le_rfl u) x
  have h3 := integrable_mul_heatKernel (ν := ν) hs le_rfl le_rfl hc2
    (fun u => heatPoly_sq hs le_rfl u) x
  have hcs := sq_integral_mul_le (μ := ν) (w := fun y => heatKernel s (x - y))
    (f := fun y => -((x - y) / s)) (fun y => (heatKernel_pos hs _).le)
    (integrable_heatKernel_comp hs le_rfl le_rfl x)
    (h2.congr (ae_of_all _ fun y => by simp only; ring))
    (h3.congr (ae_of_all _ fun y => by simp only; ring))
  have e1 : heatDensityDeriv ν s x = ∫ y, heatKernel s (x - y) * -((x - y) / s) ∂ν := by
    rw [heatDensityDeriv]
    exact integral_congr_ae (ae_of_all _ fun y => by simp only; ring)
  have e2 : ∫ y, heatKernel s (x - y) * (-((x - y) / s)) ^ 2 ∂ν
      = ∫ y, (fun u => u ^ 2 / s ^ 2) (x - y) * heatKernel s (x - y) ∂ν :=
    integral_congr_ae (ae_of_all _ fun y => by simp only; ring)
  rw [e1, div_le_iff₀ hp]
  rw [e2] at hcs
  have hb := (le_abs_self _).trans (abs_integral_mul_heatKernel_le (ν := ν) hs le_rfl le_rfl
    (fun u => heatPoly_sq hs le_rfl u) x)
  calc _ ≤ heatDensity ν s x * ∫ y, (fun u => u ^ 2 / s ^ 2) (x - y) * heatKernel s (x - y) ∂ν :=
        hcs
    _ ≤ heatDensity ν s x * ∫ y, heatEnvelope s s (x - y) ∂ν :=
        mul_le_mul_of_nonneg_left hb hp.le
    _ = _ := mul_comm _ _

private lemma integrable_envelope_weight (hν2 : Integrable (fun y => y ^ 2) ν) {a b : ℝ}
    (hb : 0 < b) : Integrable fun x => (1 + x ^ 2) * ∫ y, heatEnvelope a b (x - y) ∂ν :=
  integrable_mul_integral_comp_sub hν2 (continuous_heatEnvelope a b).measurable
    (heatEnvelope_nonneg a b) (integrable_heatEnvelope hb)

omit [IsProbabilityMeasure ν] in
private lemma integral_envelope_nonneg {a b : ℝ} (x : ℝ) :
    0 ≤ ∫ y, heatEnvelope a b (x - y) ∂ν :=
  integral_nonneg fun _ => heatEnvelope_nonneg _ _ _

theorem integrable_negMulLog_heatDensity (hν2 : Integrable (fun y => y ^ 2) ν) {s : ℝ}
    (hs : 0 < s) : Integrable fun x => Real.negMulLog (heatDensity ν s x) := by
  obtain ⟨R, -, hR⟩ := exists_Icc_half ν
  set L := logConst s s R
  refine Integrable.mono' ((integrable_envelope_weight (a := s) hν2 hs).const_mul (L + 1))
    (Real.continuous_negMulLog.comp (continuous_heatDensity hs)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have hp := heatDensity_pos (ν := ν) hs x
  have hl := abs_one_add_log_heatDensity_le (ν := ν) hs le_rfl le_rfl hR x
  have he := heatDensity_le_envelope (ν := ν) hs le_rfl le_rfl x
  have hE := integral_envelope_nonneg (ν := ν) (a := s) (b := s) x
  have hL : 0 ≤ L := by
    simp only [L, logConst]
    positivity
  rw [Real.norm_eq_abs, Real.negMulLog, abs_mul, abs_neg, abs_of_pos hp]
  have hlog : |Real.log (heatDensity ν s x)| ≤ L * (1 + x ^ 2) + 1 := by
    have := abs_sub (1 + Real.log (heatDensity ν s x)) 1
    simp only [add_sub_cancel_left, abs_one] at this
    linarith
  calc heatDensity ν s x * |Real.log (heatDensity ν s x)|
      ≤ (∫ y, heatEnvelope s s (x - y) ∂ν) * (L * (1 + x ^ 2) + 1) :=
        mul_le_mul he hlog (abs_nonneg _) hE
    _ ≤ (L + 1) * ((1 + x ^ 2) * ∫ y, heatEnvelope s s (x - y) ∂ν) := by
        nlinarith [sq_nonneg x, mul_nonneg hE (sq_nonneg x)]

noncomputable def heatFisher (ν : Measure ℝ) (s : ℝ) : ℝ :=
  ∫ x, heatDensityDeriv ν s x ^ 2 / heatDensity ν s x

private lemma abs_log_mul_le {a b s R : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (hR : 1 / 2 ≤ ν.real (Set.Icc (-R) R)) {c : ℝ → ℝ}
    (hcb : ∀ u, |c u| ≤ (1 + 1 / a) ^ 2 * (1 + u ^ 2)) (x : ℝ) :
    |(1 + Real.log (heatDensity ν s x)) * ∫ y, c (x - y) * heatKernel s (x - y) ∂ν|
      ≤ logConst a b R * ((1 + x ^ 2) * ∫ y, heatEnvelope a b (x - y) ∂ν) := by
  rw [abs_mul]
  have h1 := abs_one_add_log_heatDensity_le (ν := ν) ha has hsb hR x
  have h2 := abs_integral_mul_heatKernel_le (ν := ν) ha has hsb hcb x
  calc _ ≤ (logConst a b R * (1 + x ^ 2)) * ∫ y, heatEnvelope a b (x - y) ∂ν :=
        mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    _ = _ := by ring

theorem integrable_heatFisher (hν2 : Integrable (fun y => y ^ 2) ν) {s : ℝ} (hs : 0 < s) :
    Integrable fun x => heatDensityDeriv ν s x ^ 2 / heatDensity ν s x := by
  refine Integrable.mono' (integrable_envelope_weight (a := s) hν2 hs)
    (((continuous_heatDensityDeriv hs).pow 2).div (continuous_heatDensity hs)
      fun x => (heatDensity_pos hs x).ne').aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hp := heatDensity_pos (ν := ν) hs x
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hp.le)]
  have hE := integral_envelope_nonneg (ν := ν) (a := s) (b := s) x
  refine (sq_heatDensityDeriv_div_le hs x).trans ?_
  nlinarith [mul_nonneg hE (sq_nonneg x)]

private lemma integrable_log_mul (hν2 : Integrable (fun y => y ^ 2) ν) {s : ℝ} (hs : 0 < s)
    {c : ℝ → ℝ} (hc : Continuous c) (hcb : ∀ u, |c u| ≤ (1 + 1 / s) ^ 2 * (1 + u ^ 2)) :
    Integrable fun x => (1 + Real.log (heatDensity ν s x)) *
      ∫ y, c (x - y) * heatKernel s (x - y) ∂ν := by
  obtain ⟨R, -, hR⟩ := exists_Icc_half ν
  have hmeas : Continuous fun x => ∫ y, c (x - y) * heatKernel s (x - y) ∂ν := by
    refine continuous_of_dominated (bound := fun _ =>
      (Real.sqrt (2 * Real.pi * s))⁻¹ * (1 + 1 / s) ^ 2 * (1 + 2 * s))
      (fun x => (integrable_mul_heatKernel hs le_rfl le_rfl hc hcb x).aestronglyMeasurable)
      (fun x => ae_of_all _ fun y => by
        rw [Real.norm_eq_abs]
        exact (abs_mul_heatKernel_le hs le_rfl le_rfl (hcb _)).trans (heatEnvelope_le hs _))
      (integrable_const _) (ae_of_all _ fun y => ?_)
    exact (hc.comp (continuous_id.sub continuous_const)).mul
      ((continuous_heatKernel s).comp (continuous_id.sub continuous_const))
  refine Integrable.mono' ((integrable_envelope_weight (a := s) hν2 hs).const_mul
    (logConst s s R)) ((continuous_const.add ((continuous_heatDensity hs).log
      fun x => (heatDensity_pos hs x).ne')).mul hmeas).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_log_mul_le hs le_rfl le_rfl hR hcb x

theorem integral_neg_log_mul_heatDensityDeriv2 (hν2 : Integrable (fun y => y ^ 2) ν) {s : ℝ}
    (hs : 0 < s) :
    ∫ x, (-Real.log (heatDensity ν s x) - 1) * (heatDensityDeriv2 ν s x / 2)
      = heatFisher ν s / 2 := by
  have hc1 : Continuous fun u : ℝ => -(u / s) := (continuous_id.div_const s).neg
  have hc2 : Continuous fun u : ℝ => u ^ 2 / s ^ 2 - 1 / s := by fun_prop
  have hG : Integrable fun x => (1 + Real.log (heatDensity ν s x)) * heatDensityDeriv ν s x :=
    integrable_log_mul (ν := ν) hν2 hs hc1 (fun u => heatPoly_deriv hs le_rfl u)
  have hG2 : Integrable fun x => (1 + Real.log (heatDensity ν s x)) * heatDensityDeriv2 ν s x :=
    integrable_log_mul (ν := ν) hν2 hs hc2 (fun u => heatPoly_deriv2 hs le_rfl u)
  have hJ := integrable_heatFisher (ν := ν) hν2 hs
  have hderiv : ∀ x, HasDerivAt (fun x => (1 + Real.log (heatDensity ν s x)) *
      heatDensityDeriv ν s x) (heatDensityDeriv ν s x ^ 2 / heatDensity ν s x +
      (1 + Real.log (heatDensity ν s x)) * heatDensityDeriv2 ν s x) x := by
    intro x
    have hl := (hasDerivAt_heatDensity (ν := ν) hs x).log (heatDensity_pos hs x).ne'
    convert (hl.const_add 1).mul (hasDerivAt_heatDensityDeriv (ν := ν) hs x) using 1
    ring
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hderiv (hJ.add hG2) hG
  rw [integral_add hJ hG2] at h0
  have e : ∀ x, (-Real.log (heatDensity ν s x) - 1) * (heatDensityDeriv2 ν s x / 2)
      = (-1 / 2) * ((1 + Real.log (heatDensity ν s x)) * heatDensityDeriv2 ν s x) :=
    fun x => by ring
  simp_rw [e]
  rw [integral_const_mul]
  have : ∫ x, (1 + Real.log (heatDensity ν s x)) * heatDensityDeriv2 ν s x
      = -heatFisher ν s := by
    rw [heatFisher]
    linarith
  rw [this]
  ring

theorem hasDerivAt_heatEntropy (hν2 : Integrable (fun y => y ^ 2) ν) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, Real.negMulLog (heatDensity ν s x)) (heatFisher ν t / 2) t := by
  obtain ⟨R, -, hR⟩ := exists_Icc_half ν
  have ha : 0 < t / 2 := by positivity
  have hb : 0 < 2 * t := by positivity
  have hmem : Set.Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ s ∈ Set.Ioo (t / 2) (2 * t), 0 < s := fun s h => ha.trans h.1
  have hc : Continuous fun x =>
      (-Real.log (heatDensity ν t x) - 1) * (heatDensityDeriv2 ν t x / 2) :=
    ((((continuous_heatDensity (ν := ν) ht).log fun x => (heatDensity_pos ht x).ne').neg.sub
      continuous_const).mul ((continuous_heatDensityDeriv2 ht).div_const 2))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t)
    (F := fun s x => Real.negMulLog (heatDensity ν s x))
    (F' := fun s x => (-Real.log (heatDensity ν s x) - 1) * (heatDensityDeriv2 ν s x / 2))
    (bound := fun x => logConst (t / 2) (2 * t) R *
      ((1 + x ^ 2) * ∫ y, heatEnvelope (t / 2) (2 * t) (x - y) ∂ν))
    hmem
    (Filter.mem_of_superset hmem fun s hs => (Real.continuous_negMulLog.comp
      (continuous_heatDensity (hpos s hs))).aestronglyMeasurable)
    (integrable_negMulLog_heatDensity hν2 ht)
    hc.aestronglyMeasurable
    (ae_of_all _ fun x s hs => by
      have hb' := abs_log_mul_le (ν := ν) ha hs.1.le hs.2.le hR
        (fun u => heatPoly_deriv2 ha hs.1.le u) x
      have e : (-Real.log (heatDensity ν s x) - 1) * (heatDensityDeriv2 ν s x / 2)
          = -((1 + Real.log (heatDensity ν s x)) * heatDensityDeriv2 ν s x) / 2 := by ring
      rw [Real.norm_eq_abs, e, abs_div, abs_neg, abs_two]
      have := abs_nonneg ((1 + Real.log (heatDensity ν s x)) * heatDensityDeriv2 ν s x)
      have h' : |(1 + Real.log (heatDensity ν s x)) * heatDensityDeriv2 ν s x|
          ≤ logConst (t / 2) (2 * t) R *
            ((1 + x ^ 2) * ∫ y, heatEnvelope (t / 2) (2 * t) (x - y) ∂ν) := hb'
      linarith)
    ((integrable_envelope_weight hν2 hb).const_mul _)
    (ae_of_all _ fun x s hs => by
      have := (Real.hasDerivAt_negMulLog (heatDensity_pos (ν := ν) (hpos s hs) x).ne').comp s
        (hasDerivAt_heatDensity_time (ν := ν) (hpos s hs) x)
      exact this)
  rw [← integral_neg_log_mul_heatDensityDeriv2 hν2 ht]
  exact h.2

theorem integrable_heatDensity (hν2 : Integrable (fun y => y ^ 2) ν) {s : ℝ} (hs : 0 < s) :
    Integrable (heatDensity ν s) := by
  refine Integrable.mono' (integrable_envelope_weight (a := s) hν2 hs)
    (continuous_heatDensity hs).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (heatDensity_pos hs x)]
  have hE := integral_envelope_nonneg (ν := ν) (a := s) (b := s) x
  have := heatDensity_le_envelope (ν := ν) hs le_rfl le_rfl x
  nlinarith [mul_nonneg hE (sq_nonneg x)]

theorem integrable_heatDensityDeriv (hν2 : Integrable (fun y => y ^ 2) ν) {s : ℝ} (hs : 0 < s) :
    Integrable (heatDensityDeriv ν s) := by
  refine Integrable.mono' (integrable_envelope_weight (a := s) hν2 hs)
    (continuous_heatDensityDeriv hs).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  have hE := integral_envelope_nonneg (ν := ν) (a := s) (b := s) x
  have := abs_integral_mul_heatKernel_le (ν := ν) hs le_rfl le_rfl
    (fun u => heatPoly_deriv hs le_rfl u) x
  have e : heatDensityDeriv ν s x = ∫ y, (fun u => -(u / s)) (x - y) * heatKernel s (x - y) ∂ν :=
    rfl
  rw [e]
  nlinarith [mul_nonneg hE (sq_nonneg x)]

theorem integral_heatDensity (hν2 : Integrable (fun y => y ^ 2) ν) {s : ℝ} (hs : 0 < s) :
    ∫ x, heatDensity ν s x = 1 := by
  have h := measure_univ (μ := gaussianReal 0 s.toNNReal ∗ ν)
  rw [gaussianReal_conv_eq_withDensity hs, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (integrable_heatDensity hν2 hs)
      (ae_of_all _ fun x => (heatDensity_pos hs x).le), ← ENNReal.ofReal_one] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => (heatDensity_pos hs x).le)
    zero_le_one).1 h

theorem heatFisher_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ heatFisher ν s :=
  integral_nonneg fun x => div_nonneg (sq_nonneg _) (heatDensity_pos hs x).le

end Meat
