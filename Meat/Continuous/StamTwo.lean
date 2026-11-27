import Meat.Continuous.Stam

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

variable {ν ρ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

private lemma integrable_id_of_sq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : Integrable (fun y => y ^ 2) μ) : Integrable (fun y : ℝ => y) μ := by
  refine (h.add (integrable_const 1)).mono' (by fun_prop) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [abs_nonneg y, sq_abs y, sq_nonneg (|y| - 1)]

theorem integrable_sq_conv (hν2 : Integrable (fun y => y ^ 2) ν)
    (hρ2 : Integrable (fun y => y ^ 2) ρ) :
    Integrable (fun y => y ^ 2) (ν ∗ ρ) ∧
      ∫ y, y ^ 2 ∂(ν ∗ ρ)
        = ∫ y, y ^ 2 ∂ν + 2 * (∫ y, y ∂ν) * (∫ y, y ∂ρ) + ∫ y, y ^ 2 ∂ρ := by
  have i1 := hν2.comp_fst ρ
  have i2 := ((integrable_id_of_sq hν2).mul_prod (integrable_id_of_sq hρ2)).const_mul 2
  have i3 := hρ2.comp_snd ν
  have hi : Integrable (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2) (ν.prod ρ) :=
    ((i1.add i2).add i3).congr (ae_of_all _ fun p => by simp only [Pi.add_apply]; ring)
  have hm : AEStronglyMeasurable (fun y : ℝ => y ^ 2) (Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
      (ν.prod ρ)) := by fun_prop
  refine ⟨(integrable_map_measure hm (by fun_prop)).2 hi, ?_⟩
  change ∫ y, y ^ 2 ∂(Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (ν.prod ρ)) = _
  rw [integral_map (by fun_prop) hm]
  have e : (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2)
      = fun p => p.1 ^ 2 + 2 * (p.1 * p.2) + p.2 ^ 2 := by
    ext p
    ring
  have i12 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 + 2 * (p.1 * p.2)) (ν.prod ρ) := i1.add i2
  have hpm : ∫ p : ℝ × ℝ, p.1 * p.2 ∂(ν.prod ρ) = (∫ y, y ∂ν) * ∫ y, y ∂ρ :=
    integral_prod_mul (fun y : ℝ => y) (fun y : ℝ => y)
  rw [e, integral_add i12 i3, integral_add i1 i2, integral_const_mul, hpm,
    integral_fun_fst (fun y : ℝ => y ^ 2), integral_fun_snd (fun y : ℝ => y ^ 2)]
  simp only [probReal_univ, one_smul]
  ring

private lemma abs_heatDensityDeriv_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {s : ℝ}
    (hs : 0 < s) (x : ℝ) :
    |heatDensityDeriv μ s x| ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * (1 + 1 / s) ^ 2 * (1 + 2 * s) := by
  have h := abs_integral_mul_heatKernel_le (ν := μ) (c := fun u => -(u / s)) hs le_rfl le_rfl
    (fun u => heatPoly_deriv hs le_rfl u) x
  refine h.trans ?_
  calc ∫ y, heatEnvelope s s (x - y) ∂μ
      ≤ ∫ _, (Real.sqrt (2 * Real.pi * s))⁻¹ * (1 + 1 / s) ^ 2 * (1 + 2 * s) ∂μ :=
        integral_mono (integrable_heatEnvelope_comp hs x) (integrable_const _)
          fun y => heatEnvelope_le hs _
    _ = _ := by simp

private lemma abs_heatDensity_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {s : ℝ}
    (hs : 0 < s) (x : ℝ) : |heatDensity μ s x| ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ := by
  rw [abs_of_pos (heatDensity_pos hs x)]
  exact heatDensity_le hs x

private lemma integrable_mul_comp_sub {a b : ℝ → ℝ} (ha : Integrable a) (hbc : Continuous b)
    {C : ℝ} (hC : ∀ v, |b v| ≤ C) (x : ℝ) : Integrable fun z => a z * b (x - z) :=
  ha.mul_bdd (hbc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)

private theorem heatDensity_conv (hν2 : Integrable (fun y => y ^ 2) ν)
    (hρ2 : Integrable (fun y => y ^ 2) ρ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (x : ℝ) :
    heatDensity (ν ∗ ρ) (s + u) x = ∫ z, heatDensity ν s z * heatDensity ρ u (x - z) := by
  set P := heatDensity ν s
  set Q := heatDensity ρ u
  have hP0 : ∀ z, 0 < P z := heatDensity_pos hs
  have hQ0 : ∀ z, 0 < Q z := heatDensity_pos hu
  have hPi : Integrable P := integrable_heatDensity hν2 hs
  have hQi : Integrable Q := integrable_heatDensity hρ2 hu
  have hPc : Continuous P := continuous_heatDensity hs
  have hQc : Continuous Q := continuous_heatDensity hu
  have hsu : 0 < s + u := by positivity
  set R : ℝ → ℝ := fun x => ∫ z, P z * Q (x - z)
  have hRc : Continuous R := by
    refine continuous_of_dominated (bound := fun z => P z * (Real.sqrt (2 * Real.pi * u))⁻¹)
      (fun x => (hPc.mul (hQc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (fun x => ae_of_all _ fun z => ?_) (hPi.mul_const _) (ae_of_all _ fun z => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hP0 z)]
      exact mul_le_mul_of_nonneg_left (abs_heatDensity_le hu _) (hP0 z).le
    · exact continuous_const.mul (hQc.comp (continuous_id.sub continuous_const))
  have hR0 : ∀ x, 0 ≤ R x := fun x =>
    integral_nonneg fun z => mul_nonneg (hP0 z).le (hQ0 _).le
  have hmeas : gaussianReal 0 (s + u).toNNReal ∗ (ν ∗ ρ)
      = (gaussianReal 0 s.toNNReal ∗ ν) ∗ (gaussianReal 0 u.toNNReal ∗ ρ) := by
    have hg : gaussianReal 0 (s + u).toNNReal
        = gaussianReal 0 s.toNNReal ∗ gaussianReal 0 u.toNNReal := by
      rw [gaussianReal_conv_gaussianReal, add_zero, Real.toNNReal_add hs.le hu.le]
    rw [hg, Measure.conv_assoc (gaussianReal 0 s.toNNReal) (gaussianReal 0 u.toNNReal) (ν ∗ ρ),
      Measure.conv_assoc (gaussianReal 0 s.toNNReal) ν (gaussianReal 0 u.toNNReal ∗ ρ),
      ← Measure.conv_assoc (gaussianReal 0 u.toNNReal) ν ρ,
      Measure.conv_comm (gaussianReal 0 u.toNNReal) ν,
      Measure.conv_assoc ν (gaussianReal 0 u.toNNReal) ρ]
  have hint : ∀ x, ∫⁻ y, ENNReal.ofReal (P (x - y)) ∂(volume.withDensity
      fun x => ENNReal.ofReal (Q x)) = ENNReal.ofReal (R x) := by
    intro x
    have hm : Measurable fun y => ENNReal.ofReal (P (x - y)) :=
      (hPc.measurable.comp (measurable_const.sub measurable_id)).ennreal_ofReal
    rw [lintegral_withDensity_eq_lintegral_mul _ hQc.measurable.ennreal_ofReal hm]
    have hi : Integrable fun y => Q y * P (x - y) :=
      integrable_mul_comp_sub hQi hPc (abs_heatDensity_le hs) x
    have hR : R x = ∫ y, Q y * P (x - y) := by
      simp only [R]
      rw [← integral_sub_left_eq_self _ volume x]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [sub_sub_cancel]
      ring
    rw [hR, ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun y => mul_nonneg (hQ0 y).le (hP0 _).le)]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hQ0 y).le]
  have hL := gaussianReal_conv_eq_withDensity (ν := ν ∗ ρ) hsu
  rw [hmeas, gaussianReal_conv_eq_withDensity hs, gaussianReal_conv_eq_withDensity hu,
    withDensity_conv_eq hPc.measurable.ennreal_ofReal, funext hint] at hL
  have h1 := Measure.rnDeriv_withDensity volume
    (continuous_heatDensity (ν := ν ∗ ρ) hsu).measurable.ennreal_ofReal
  have h2 := Measure.rnDeriv_withDensity volume hRc.measurable.ennreal_ofReal
  rw [← hL] at h1
  have hae : heatDensity (ν ∗ ρ) (s + u) =ᵐ[volume] R := by
    filter_upwards [h1, h2] with y hy1 hy2
    rw [hy1] at hy2
    exact (ENNReal.ofReal_eq_ofReal_iff (heatDensity_pos hsu y).le (hR0 y)).1 hy2
  rw [((continuous_heatDensity hsu).ae_eq_iff_eq volume hRc).1 hae]

private theorem heatDensityDeriv_conv (hν2 : Integrable (fun y => y ^ 2) ν)
    (hρ2 : Integrable (fun y => y ^ 2) ρ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (x : ℝ) :
    heatDensityDeriv (ν ∗ ρ) (s + u) x
      = ∫ z, heatDensity ν s z * heatDensityDeriv ρ u (x - z) := by
  set P := heatDensity ν s
  set Q := heatDensity ρ u
  set E := heatDensityDeriv ρ u
  have hP0 : ∀ z, 0 < P z := heatDensity_pos hs
  have hPi : Integrable P := integrable_heatDensity hν2 hs
  have hPc : Continuous P := continuous_heatDensity hs
  have hQc : Continuous Q := continuous_heatDensity hu
  have hEc : Continuous E := continuous_heatDensityDeriv hu
  have hR : HasDerivAt (fun x => ∫ z, P z * Q (x - z)) (∫ z, P z * E (x - z)) x := by
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := x)
      (F := fun x z => P z * Q (x - z)) (F' := fun x z => P z * E (x - z))
      (bound := fun z => P z * ((Real.sqrt (2 * Real.pi * u))⁻¹ * (1 + 1 / u) ^ 2 *
        (1 + 2 * u))) Filter.univ_mem
      (Eventually.of_forall fun x' =>
        (hPc.mul (hQc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (integrable_mul_comp_sub hPi hQc (abs_heatDensity_le hu) x)
      (hPc.mul (hEc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (ae_of_all _ fun z x' _ => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hP0 z)]
        exact mul_le_mul_of_nonneg_left (abs_heatDensityDeriv_le hu _) (hP0 z).le)
      (hPi.mul_const _)
      (ae_of_all _ fun z x' _ =>
        ((hasDerivAt_heatDensity (ν := ρ) hu (x' - z)).comp_sub_const x' z).const_mul (P z))
    exact h.2
  have h0 := hasDerivAt_heatDensity (ν := ν ∗ ρ) (by positivity : 0 < s + u) x
  rw [funext (heatDensity_conv hν2 hρ2 hs hu)] at h0
  exact h0.unique hR

private theorem heatDensityDeriv_conv' (hν2 : Integrable (fun y => y ^ 2) ν)
    (hρ2 : Integrable (fun y => y ^ 2) ρ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (x : ℝ) :
    heatDensityDeriv (ν ∗ ρ) (s + u) x
      = ∫ z, heatDensityDeriv ν s z * heatDensity ρ u (x - z) := by
  rw [Measure.conv_comm, add_comm s u, heatDensityDeriv_conv hρ2 hν2 hu hs x,
    ← integral_sub_left_eq_self _ volume x]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [sub_sub_cancel]
  ring

private theorem integral_heatDensityDeriv (hν2 : Integrable (fun y => y ^ 2) ν) {s : ℝ}
    (hs : 0 < s) :
    ∫ x, heatDensityDeriv ν s x = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable (fun x => hasDerivAt_heatDensity hs x)
    (integrable_heatDensityDeriv hν2 hs) (integrable_heatDensity hν2 hs)

private lemma integrable_prod_comp_sub {a b : ℝ → ℝ} (ha : Integrable a) (hac : Continuous a)
    (hb : Integrable b) (hbc : Continuous b) :
    Integrable (fun p : ℝ × ℝ => a p.2 * b (p.1 - p.2)) (volume.prod volume) := by
  refine (integrable_prod_iff' ((hac.comp continuous_snd).mul
    (hbc.comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable).2
    ⟨ae_of_all _ fun z => (hb.comp_sub_right z).const_mul (a z), ?_⟩
  refine (ha.norm.mul_const (∫ v, ‖b v‖)).congr (ae_of_all _ fun z => ?_)
  change ‖a z‖ * ∫ v, ‖b v‖ = ∫ x, ‖a z * b (x - z)‖
  simp only [norm_mul]
  rw [integral_const_mul, integral_sub_right_eq_self (fun v => ‖b v‖) z]

theorem heatFisher_conv_le (hν2 : Integrable (fun y => y ^ 2) ν)
    (hρ2 : Integrable (fun y => y ^ 2) ρ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (l : ℝ) :
    heatFisher (ν ∗ ρ) (s + u) ≤ l ^ 2 * heatFisher ν s + (1 - l) ^ 2 * heatFisher ρ u := by
  set P := heatDensity ν s
  set D := heatDensityDeriv ν s
  set Q := heatDensity ρ u
  set E := heatDensityDeriv ρ u
  have hP : ∀ z, 0 < P z := heatDensity_pos hs
  have hQ : ∀ z, 0 < Q z := heatDensity_pos hu
  have hPi : Integrable P := integrable_heatDensity hν2 hs
  have hDi : Integrable D := integrable_heatDensityDeriv hν2 hs
  have hFi : Integrable fun z => D z ^ 2 / P z := integrable_heatFisher hν2 hs
  have hQi : Integrable Q := integrable_heatDensity hρ2 hu
  have hEi : Integrable E := integrable_heatDensityDeriv hρ2 hu
  have hGi : Integrable fun z => E z ^ 2 / Q z := integrable_heatFisher hρ2 hu
  have hPc : Continuous P := continuous_heatDensity hs
  have hDc : Continuous D := continuous_heatDensityDeriv hs
  have hFc : Continuous fun z => D z ^ 2 / P z := (hDc.pow 2).div hPc fun z => (hP z).ne'
  have hQc : Continuous Q := continuous_heatDensity hu
  have hEc : Continuous E := continuous_heatDensityDeriv hu
  have hGc : Continuous fun z => E z ^ 2 / Q z := (hEc.pow 2).div hQc fun z => (hQ z).ne'
  have hE0 : ∫ v, E v = 0 := integral_heatDensityDeriv hρ2 hu
  have hQ1 : ∫ v, Q v = 1 := integral_heatDensity hρ2 hu
  set H : ℝ × ℝ → ℝ := fun p => l ^ 2 * (D p.2 ^ 2 / P p.2 * Q (p.1 - p.2)) +
    2 * l * (1 - l) * (D p.2 * E (p.1 - p.2)) +
    (1 - l) ^ 2 * (P p.2 * (E (p.1 - p.2) ^ 2 / Q (p.1 - p.2)))
  have hH : Integrable H (volume.prod volume) :=
    ((((integrable_prod_comp_sub hFi hFc hQi hQc).const_mul (l ^ 2)).add
      ((integrable_prod_comp_sub hDi hDc hEi hEc).const_mul (2 * l * (1 - l)))).add
      ((integrable_prod_comp_sub hPi hPc hGi hGc).const_mul ((1 - l) ^ 2)))
  have hpt : ∀ᵐ x, heatDensityDeriv (ν ∗ ρ) (s + u) x ^ 2 / heatDensity (ν ∗ ρ) (s + u) x
      ≤ ∫ z, H (x, z) := by
    filter_upwards [hH.prod_right_ae] with x hHx
    set w : ℝ → ℝ := fun z => P z * Q (x - z)
    set g : ℝ → ℝ := fun z => l * (D z / P z) + (1 - l) * (E (x - z) / Q (x - z))
    have hw0 : ∀ z, 0 ≤ w z := fun z => mul_nonneg (hP z).le (hQ _).le
    have hwi : Integrable w := integrable_mul_comp_sub hPi hQc (abs_heatDensity_le hu) x
    have hi1 : Integrable fun z => D z * Q (x - z) :=
      integrable_mul_comp_sub hDi hQc (abs_heatDensity_le hu) x
    have hi2 : Integrable fun z => P z * E (x - z) :=
      integrable_mul_comp_sub hPi hEc (abs_heatDensityDeriv_le hu) x
    have hwg : (fun z => w z * g z)
        = fun z => l * (D z * Q (x - z)) + (1 - l) * (P z * E (x - z)) := by
      ext z
      have := (hP z).ne'
      have := (hQ (x - z)).ne'
      simp only [w, g]
      field_simp
    have hwg2 : (fun z => w z * g z ^ 2) = fun z => H (x, z) := by
      ext z
      have := (hP z).ne'
      have := (hQ (x - z)).ne'
      simp only [w, g, H]
      field_simp
      ring
    have hcs := sq_integral_mul_le hw0 hwi (hwg ▸ ((hi1.const_mul l).add (hi2.const_mul (1 - l))))
      (hwg2 ▸ hHx)
    have hW : ∫ z, w z = heatDensity (ν ∗ ρ) (s + u) x := (heatDensity_conv hν2 hρ2 hs hu x).symm
    have hA : ∫ z, w z * g z = heatDensityDeriv (ν ∗ ρ) (s + u) x := by
      rw [hwg, integral_add (hi1.const_mul l) (hi2.const_mul (1 - l)), integral_const_mul,
        integral_const_mul, ← heatDensityDeriv_conv' hν2 hρ2 hs hu x,
        ← heatDensityDeriv_conv hν2 hρ2 hs hu x]
      ring
    rw [hW, hA, hwg2] at hcs
    rw [div_le_iff₀ (heatDensity_pos (by positivity) x)]
    linarith
  have hS2 := (integrable_sq_conv hν2 hρ2).1
  have hmono := integral_mono_ae (integrable_heatFisher hS2 (by positivity))
    hH.integral_prod_left hpt
  have hswap : ∫ x, ∫ z, H (x, z) = ∫ z, ∫ x, H (x, z) :=
    integral_integral_swap (f := fun x z => H (x, z)) hH
  have hinner : ∀ z, ∫ x, H (x, z)
      = l ^ 2 * (D z ^ 2 / P z) + (1 - l) ^ 2 * heatFisher ρ u * P z := by
    intro z
    have i1 := (hQi.comp_sub_right z).const_mul (D z ^ 2 / P z)
    have i2 := (hEi.comp_sub_right z).const_mul (D z)
    have i3 := (hGi.comp_sub_right z).const_mul (P z)
    have j1 : Integrable fun x => l ^ 2 * (D z ^ 2 / P z * Q (x - z)) +
        2 * l * (1 - l) * (D z * E (x - z)) := (i1.const_mul _).add (i2.const_mul _)
    simp only [H]
    rw [integral_add j1 (i3.const_mul _),
      integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sub_right_eq_self Q z, integral_sub_right_eq_self E z,
      integral_sub_right_eq_self (fun v => E v ^ 2 / Q v) z, hQ1, hE0]
    simp only [heatFisher, E, Q]
    ring
  simp_rw [hinner] at hswap
  rw [integral_add (hFi.const_mul _) (hPi.const_mul _), integral_const_mul, integral_const_mul,
    integral_heatDensity hν2 hs] at hswap
  calc heatFisher (ν ∗ ρ) (s + u) ≤ ∫ x, ∫ z, H (x, z) := hmono
    _ = l ^ 2 * heatFisher ν s + (1 - l) ^ 2 * heatFisher ρ u := by
      rw [hswap]
      simp only [heatFisher, D, P]
      ring

end Meat
