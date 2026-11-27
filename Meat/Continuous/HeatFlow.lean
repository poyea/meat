import Meat.Continuous.Gaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

noncomputable def heatKernel (s u : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-u ^ 2 / (2 * s))

theorem heatKernel_pos {s : ℝ} (hs : 0 < s) (u : ℝ) : 0 < heatKernel s u := by
  have := Real.pi_pos
  unfold heatKernel
  positivity

theorem gaussianPDFReal_eq_heatKernel {s : ℝ} (hs : 0 ≤ s) (m u : ℝ) :
    gaussianPDFReal m s.toNNReal u = heatKernel s (u - m) := by
  simp [gaussianPDFReal, heatKernel, Real.coe_toNNReal _ hs]

theorem integral_heatKernel {s : ℝ} (hs : 0 < s) (m : ℝ) :
    ∫ u, heatKernel s (u - m) = 1 := by
  simp_rw [← gaussianPDFReal_eq_heatKernel hs.le m]
  exact integral_gaussianPDFReal_eq_one m (by simp [hs])

theorem hasDerivAt_heatKernel (s u : ℝ) :
    HasDerivAt (heatKernel s) (-(u / s) * heatKernel s u) u := by
  have h : HasDerivAt (fun y : ℝ => -y ^ 2 / (2 * s)) (-(2 * u) / (2 * s)) u := by
    simpa using ((hasDerivAt_pow 2 u).neg).div_const (2 * s)
  have h2 := (h.exp).const_mul (Real.sqrt (2 * Real.pi * s))⁻¹
  unfold heatKernel
  convert h2 using 1
  ring

theorem hasDerivAt_heatKernel_deriv (s u : ℝ) :
    HasDerivAt (fun u => -(u / s) * heatKernel s u) ((u ^ 2 / s ^ 2 - 1 / s) * heatKernel s u)
      u := by
  have h1 := ((hasDerivAt_id' u).div_const s).neg
  convert h1.mul (hasDerivAt_heatKernel s u) using 1
  simp only [Pi.neg_apply]
  ring

theorem hasDerivAt_heatKernel_time {s : ℝ} (hs : 0 < s) (u : ℝ) :
    HasDerivAt (fun s => heatKernel s u) ((u ^ 2 / s ^ 2 - 1 / s) / 2 * heatKernel s u) s := by
  have hpi := Real.pi_pos
  have hc : 0 < 2 * Real.pi * s := by positivity
  have hr := Real.sqrt_pos.2 hc
  have hr2 := Real.sq_sqrt hc.le
  have hsq : HasDerivAt (fun s => Real.sqrt (2 * Real.pi * s))
      (1 / (2 * Real.sqrt (2 * Real.pi * s)) * (2 * Real.pi)) s := by
    have := ((hasDerivAt_id s).const_mul (2 * Real.pi))
    simp only [id, mul_one] at this
    exact (Real.hasDerivAt_sqrt hc.ne').comp s this
  have hinv := hsq.inv hr.ne'
  have he : HasDerivAt (fun s : ℝ => -u ^ 2 / (2 * s)) (u ^ 2 / (2 * s ^ 2)) s := by
    have := ((hasDerivAt_id s).const_mul 2).inv (by simp [hs.ne'])
    convert this.const_mul (-u ^ 2) using 1
    · ext t
      simp [div_eq_mul_inv]
    · simp only [id]
      field_simp
  have h := hinv.mul he.exp
  unfold heatKernel
  convert h using 1
  simp only [Pi.inv_apply]
  generalize Real.sqrt (2 * Real.pi * s) = r at hr hr2 ⊢
  field_simp
  linear_combination (-s) * hr2

theorem continuous_heatKernel (s : ℝ) : Continuous (heatKernel s) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_heatKernel s u).continuousAt

theorem heatKernel_le {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b) (u : ℝ) :
    heatKernel s u ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (-(1 / (2 * b)) * u ^ 2) := by
  have hpi := Real.pi_pos
  have hs : 0 < s := ha.trans_le has
  unfold heatKernel
  gcongr
  rw [neg_div, neg_mul, neg_le_neg_iff, one_div, inv_mul_eq_div]
  exact div_le_div_of_nonneg_left (sq_nonneg u) (by positivity) (by linarith)

noncomputable def heatEnvelope (a b u : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * a))⁻¹ * (1 + 1 / a) ^ 2 * (1 + u ^ 2) *
    Real.exp (-(1 / (2 * b)) * u ^ 2)

theorem heatEnvelope_nonneg (a b u : ℝ) : 0 ≤ heatEnvelope a b u := by
  unfold heatEnvelope
  positivity

theorem abs_mul_heatKernel_le {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b) {c u : ℝ}
    (hc : |c| ≤ (1 + 1 / a) ^ 2 * (1 + u ^ 2)) : |c * heatKernel s u| ≤ heatEnvelope a b u := by
  have hk := heatKernel_pos (ha.trans_le has) u
  rw [abs_mul, abs_of_pos hk, heatEnvelope]
  have := heatKernel_le ha has hsb u
  calc |c| * heatKernel s u
      ≤ ((1 + 1 / a) ^ 2 * (1 + u ^ 2)) *
        ((Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (-(1 / (2 * b)) * u ^ 2)) :=
        mul_le_mul hc this hk.le (by positivity)
    _ = _ := by ring

theorem heatPoly_one {a : ℝ} (ha : 0 < a) (u : ℝ) : |(1 : ℝ)| ≤ (1 + 1 / a) ^ 2 * (1 + u ^ 2) := by
  have : 0 ≤ 1 / a := by positivity
  rw [abs_one]
  nlinarith [sq_nonneg u, mul_nonneg this (sq_nonneg u), sq_nonneg (1 / a)]

theorem heatPoly_deriv {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (u : ℝ) :
    |-(u / s)| ≤ (1 + 1 / a) ^ 2 * (1 + u ^ 2) := by
  have hs : 0 < s := ha.trans_le has
  have hq : 1 / s ≤ 1 / a := one_div_le_one_div_of_le ha has
  have hq0 : 0 ≤ 1 / s := by positivity
  have hu : |u| ≤ 1 + u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u, sq_nonneg (|u| - 1)]
  rw [abs_neg, div_eq_mul_one_div, abs_mul, abs_of_nonneg hq0]
  have : 0 ≤ 1 / a := by positivity
  calc |u| * (1 / s) ≤ (1 + u ^ 2) * (1 / a) := mul_le_mul hu hq hq0 (by positivity)
    _ ≤ _ := by nlinarith [sq_nonneg u, mul_nonneg this (sq_nonneg u), sq_nonneg (1 / a)]

theorem heatPoly_deriv2 {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (u : ℝ) :
    |u ^ 2 / s ^ 2 - 1 / s| ≤ (1 + 1 / a) ^ 2 * (1 + u ^ 2) := by
  have hs : 0 < s := ha.trans_le has
  have hq : 1 / s ≤ 1 / a := one_div_le_one_div_of_le ha has
  have hq0 : 0 ≤ 1 / s := by positivity
  have hA : 0 ≤ 1 / a := by positivity
  have e : u ^ 2 / s ^ 2 - 1 / s = u ^ 2 * (1 / s) ^ 2 - 1 / s := by ring
  have hq2 : (1 / s) ^ 2 ≤ (1 / a) ^ 2 := pow_le_pow_left₀ hq0 hq 2
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (by positivity), abs_of_nonneg hq0]
  have : u ^ 2 * (1 / s) ^ 2 ≤ u ^ 2 * (1 / a) ^ 2 := mul_le_mul_of_nonneg_left hq2 (sq_nonneg u)
  nlinarith [sq_nonneg u, mul_nonneg hA (sq_nonneg u), sq_nonneg (1 / a)]

theorem heatPoly_time {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (u : ℝ) :
    |(u ^ 2 / s ^ 2 - 1 / s) / 2| ≤ (1 + 1 / a) ^ 2 * (1 + u ^ 2) := by
  have h := heatPoly_deriv2 ha has u
  rw [abs_div, abs_two]
  have := abs_nonneg (u ^ 2 / s ^ 2 - 1 / s)
  linarith

theorem heatEnvelope_le {a b : ℝ} (hb : 0 < b) (u : ℝ) :
    heatEnvelope a b u ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ * (1 + 1 / a) ^ 2 * (1 + 2 * b) := by
  unfold heatEnvelope
  have hx : u ^ 2 * Real.exp (-(1 / (2 * b)) * u ^ 2) ≤ 2 * b := by
    have h := Real.add_one_le_exp (1 / (2 * b) * u ^ 2)
    have hpos := Real.exp_pos (1 / (2 * b) * u ^ 2)
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
    have e : u ^ 2 = 2 * b * (1 / (2 * b) * u ^ 2) := by field_simp
    calc u ^ 2 = 2 * b * (1 / (2 * b) * u ^ 2) := e
      _ ≤ 2 * b * Real.exp (1 / (2 * b) * u ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
  have he : Real.exp (-(1 / (2 * b)) * u ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 1 / (2 * b) * u ^ 2 := by positivity
    linarith
  have hC : 0 ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ * (1 + 1 / a) ^ 2 := by positivity
  calc (Real.sqrt (2 * Real.pi * a))⁻¹ * (1 + 1 / a) ^ 2 * (1 + u ^ 2) *
        Real.exp (-(1 / (2 * b)) * u ^ 2)
      = (Real.sqrt (2 * Real.pi * a))⁻¹ * (1 + 1 / a) ^ 2 *
        (Real.exp (-(1 / (2 * b)) * u ^ 2) + u ^ 2 * Real.exp (-(1 / (2 * b)) * u ^ 2)) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hC

theorem integrable_pow_mul_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Integrable fun u : ℝ => u ^ n * Real.exp (-c * u ^ 2) := by
  have := integrable_rpow_mul_exp_neg_mul_sq hc (s := n)
    (by have := n.cast_nonneg (α := ℝ); linarith)
  simpa [Real.rpow_natCast] using this

theorem integrable_heatEnvelope {a b : ℝ} (hb : 0 < b) :
    Integrable fun u => (1 + u ^ 2) * heatEnvelope a b u := by
  have hc : 0 < 1 / (2 * b) := by positivity
  have h := ((integrable_pow_mul_exp_neg_mul_sq hc 0).add
    ((integrable_pow_mul_exp_neg_mul_sq hc 2).const_mul 2)).add
    (integrable_pow_mul_exp_neg_mul_sq hc 4)
  refine (h.const_mul ((Real.sqrt (2 * Real.pi * a))⁻¹ * (1 + 1 / a) ^ 2)).congr
    (ae_of_all _ fun u => ?_)
  simp only [heatEnvelope, Pi.add_apply]
  ring

noncomputable def heatDensity (ν : Measure ℝ) (s x : ℝ) : ℝ :=
  ∫ y, heatKernel s (x - y) ∂ν

noncomputable def heatDensityDeriv (ν : Measure ℝ) (s x : ℝ) : ℝ :=
  ∫ y, -((x - y) / s) * heatKernel s (x - y) ∂ν

noncomputable def heatDensityDeriv2 (ν : Measure ℝ) (s x : ℝ) : ℝ :=
  ∫ y, ((x - y) ^ 2 / s ^ 2 - 1 / s) * heatKernel s (x - y) ∂ν

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

theorem integrable_mul_heatKernel {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    {c : ℝ → ℝ} (hc : Continuous c) (hcb : ∀ u, |c u| ≤ (1 + 1 / a) ^ 2 * (1 + u ^ 2)) (x : ℝ) :
    Integrable (fun y => c (x - y) * heatKernel s (x - y)) ν := by
  have hb : 0 < b := ha.trans_le (has.trans hsb)
  refine Integrable.mono' (integrable_const
    ((Real.sqrt (2 * Real.pi * a))⁻¹ * (1 + 1 / a) ^ 2 * (1 + 2 * b))) ?_
    (ae_of_all _ fun y => ?_)
  · exact ((hc.comp (continuous_const.sub continuous_id)).mul
      ((continuous_heatKernel s).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact (abs_mul_heatKernel_le ha has hsb (hcb _)).trans (heatEnvelope_le hb _)

theorem integrable_heatKernel_comp {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (x : ℝ) : Integrable (fun y => heatKernel s (x - y)) ν := by
  simpa using integrable_mul_heatKernel (ν := ν) (c := fun _ => 1) ha has hsb continuous_const
    (fun u => heatPoly_one ha u) x

theorem heatDensity_pos {s : ℝ} (hs : 0 < s) (x : ℝ) : 0 < heatDensity ν s x := by
  have hi : Integrable (fun y => heatKernel s (x - y)) ν :=
    integrable_heatKernel_comp hs le_rfl le_rfl x
  rw [heatDensity, integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun y => (heatKernel_pos hs _).le) hi]
  have : Function.support (fun y => heatKernel s (x - y)) = Set.univ :=
    Set.eq_univ_of_forall fun y => (heatKernel_pos hs _).ne'
  simp [this]

theorem heatDensity_le {s : ℝ} (hs : 0 < s) (x : ℝ) :
    heatDensity ν s x ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ := by
  have h : ∀ y, heatKernel s (x - y) ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ := by
    intro y
    refine (heatKernel_le hs le_rfl le_rfl _).trans ?_
    have : Real.exp (-(1 / (2 * s)) * (x - y) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ 1 / (2 * s) * (x - y) ^ 2 := by positivity
      linarith
    have := Real.pi_pos
    calc _ ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  calc heatDensity ν s x ≤ ∫ _, (Real.sqrt (2 * Real.pi * s))⁻¹ ∂ν :=
        integral_mono_of_nonneg (ae_of_all _ fun y => (heatKernel_pos hs _).le)
          (integrable_const _) (ae_of_all _ h)
    _ = _ := by simp

theorem hasDerivAt_heatDensity {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (heatDensity ν s) (heatDensityDeriv ν s x) x := by
  have hc : Continuous fun u : ℝ => -(u / s) := (continuous_id.div_const s).neg
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := x)
    (F := fun x y => heatKernel s (x - y))
    (F' := fun x y => -((x - y) / s) * heatKernel s (x - y))
    (bound := fun _ => (Real.sqrt (2 * Real.pi * s))⁻¹ * (1 + 1 / s) ^ 2 * (1 + 2 * s))
    Filter.univ_mem
    (Eventually.of_forall fun x' => ((continuous_heatKernel s).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (integrable_heatKernel_comp hs le_rfl le_rfl x)
    (integrable_mul_heatKernel hs le_rfl le_rfl hc (fun u => heatPoly_deriv hs le_rfl u)
      x).aestronglyMeasurable
    (ae_of_all _ fun y x' _ => by
      rw [Real.norm_eq_abs]
      exact (abs_mul_heatKernel_le hs le_rfl le_rfl (heatPoly_deriv hs le_rfl _)).trans
        (heatEnvelope_le hs _))
    (integrable_const _)
    (ae_of_all _ fun y x' _ => (hasDerivAt_heatKernel s (x' - y)).comp_sub_const x' y)
  exact h.2

theorem hasDerivAt_heatDensityDeriv {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (heatDensityDeriv ν s) (heatDensityDeriv2 ν s x) x := by
  have hc : Continuous fun u : ℝ => -(u / s) := (continuous_id.div_const s).neg
  have hc2 : Continuous fun u : ℝ => u ^ 2 / s ^ 2 - 1 / s := by fun_prop
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := x)
    (F := fun x y => -((x - y) / s) * heatKernel s (x - y))
    (F' := fun x y => ((x - y) ^ 2 / s ^ 2 - 1 / s) * heatKernel s (x - y))
    (bound := fun _ => (Real.sqrt (2 * Real.pi * s))⁻¹ * (1 + 1 / s) ^ 2 * (1 + 2 * s))
    Filter.univ_mem
    (Eventually.of_forall fun x' => (integrable_mul_heatKernel hs le_rfl le_rfl hc
      (fun u => heatPoly_deriv hs le_rfl u) x').aestronglyMeasurable)
    (integrable_mul_heatKernel hs le_rfl le_rfl hc (fun u => heatPoly_deriv hs le_rfl u) x)
    (integrable_mul_heatKernel hs le_rfl le_rfl hc2 (fun u => heatPoly_deriv2 hs le_rfl u)
      x).aestronglyMeasurable
    (ae_of_all _ fun y x' _ => by
      rw [Real.norm_eq_abs]
      exact (abs_mul_heatKernel_le hs le_rfl le_rfl (heatPoly_deriv2 hs le_rfl _)).trans
        (heatEnvelope_le hs _))
    (integrable_const _)
    (ae_of_all _ fun y x' _ => (hasDerivAt_heatKernel_deriv s (x' - y)).comp_sub_const x' y)
  exact h.2

theorem hasDerivAt_heatDensity_time {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (fun s => heatDensity ν s x) (heatDensityDeriv2 ν s x / 2) s := by
  have ha : 0 < s / 2 := by positivity
  have hb : 0 < 2 * s := by positivity
  have hmem : Set.Ioo (s / 2) (2 * s) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hc0 : ∀ s' ∈ Set.Ioo (s / 2) (2 * s), Integrable (fun y => heatKernel s' (x - y)) ν :=
    fun s' h => integrable_heatKernel_comp ha h.1.le h.2.le x
  have hc2 : Continuous fun u : ℝ => (u ^ 2 / s ^ 2 - 1 / s) / 2 := by fun_prop
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s)
    (F := fun s y => heatKernel s (x - y))
    (F' := fun s y => ((x - y) ^ 2 / s ^ 2 - 1 / s) / 2 * heatKernel s (x - y))
    (bound := fun _ => (Real.sqrt (2 * Real.pi * (s / 2)))⁻¹ * (1 + 1 / (s / 2)) ^ 2 *
      (1 + 2 * (2 * s)))
    hmem
    (Filter.mem_of_superset hmem fun s' h => (hc0 s' h).aestronglyMeasurable)
    (hc0 s ⟨by linarith, by linarith⟩)
    (integrable_mul_heatKernel hs le_rfl le_rfl hc2 (fun u => heatPoly_time hs le_rfl u)
      x).aestronglyMeasurable
    (ae_of_all _ fun y s' h => by
      rw [Real.norm_eq_abs]
      exact (abs_mul_heatKernel_le ha h.1.le h.2.le (heatPoly_time ha h.1.le _)).trans
        (heatEnvelope_le hb _))
    (integrable_const _)
    (ae_of_all _ fun y s' h => hasDerivAt_heatKernel_time (ha.trans h.1) (x - y))
  convert h.2 using 1
  · rfl
  rw [show heatDensityDeriv2 ν s x
      = ∫ y, ((x - y) ^ 2 / s ^ 2 - 1 / s) * heatKernel s (x - y) ∂ν from rfl, ← integral_div]
  congr 1
  ext y
  ring

theorem continuous_heatDensity {s : ℝ} (hs : 0 < s) : Continuous (heatDensity ν s) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_heatDensity hs x).continuousAt

theorem continuous_heatDensityDeriv {s : ℝ} (hs : 0 < s) : Continuous (heatDensityDeriv ν s) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_heatDensityDeriv hs x).continuousAt

theorem withDensity_conv_eq {F : ℝ → ℝ≥0∞} (hF : Measurable F) (ρ : Measure ℝ) [SFinite ρ] :
    volume.withDensity F ∗ ρ = volume.withDensity (fun x => ∫⁻ y, F (x - y) ∂ρ) := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hG : Measurable fun x => ∫⁻ y, F (x - y) ∂ρ :=
    (hF.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'
  rw [Measure.conv_comm, Measure.lintegral_conv hφ, lintegral_withDensity_eq_lintegral_mul _ hG hφ]
  have h1 : ∀ y, ∫⁻ x, φ (y + x) ∂(volume.withDensity F) = ∫⁻ x, F (x - y) * φ x := by
    intro y
    have hy : Measurable fun x => φ (y + x) := hφ.comp (measurable_const_add y)
    rw [lintegral_withDensity_eq_lintegral_mul _ hF hy, ← lintegral_sub_right_eq_self _ y]
    simp
  simp_rw [h1]
  rw [lintegral_lintegral_swap ((hF.comp (measurable_snd.sub measurable_fst)).mul
    (hφ.comp measurable_snd)).aemeasurable]
  refine lintegral_congr fun x => ?_
  have hx : Measurable fun y => F (x - y) := hF.comp (measurable_const.sub measurable_id)
  rw [Pi.mul_apply, lintegral_mul_const _ hx]

theorem gaussianReal_conv_eq_withDensity {s : ℝ} (hs : 0 < s) :
    gaussianReal 0 s.toNNReal ∗ ν
      = volume.withDensity (fun x => ENNReal.ofReal (heatDensity ν s x)) := by
  rw [gaussianReal_of_var_ne_zero 0 (by simp [hs]),
    withDensity_conv_eq (measurable_gaussianPDF 0 _)]
  congr 1
  ext x
  rw [heatDensity, ofReal_integral_eq_lintegral_ofReal
    (integrable_heatKernel_comp hs le_rfl le_rfl x)
    (ae_of_all _ fun y => (heatKernel_pos hs _).le)]
  refine lintegral_congr fun y => ?_
  rw [gaussianPDF, gaussianPDFReal_eq_heatKernel hs.le, sub_zero]

theorem measureDiffEntropy_conv_gaussianReal {s : ℝ} (hs : 0 < s) :
    measureDiffEntropy (ν ∗ gaussianReal 0 s.toNNReal)
      = ∫ x, Real.negMulLog (heatDensity ν s x) := by
  rw [Measure.conv_comm, gaussianReal_conv_eq_withDensity hs, measureDiffEntropy]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity volume
    (continuous_heatDensity (ν := ν) hs).measurable.ennreal_ofReal] with x hx
  rw [hx, ENNReal.toReal_ofReal (heatDensity_pos hs x).le]

theorem continuous_heatEnvelope (a b : ℝ) : Continuous (heatEnvelope a b) := by
  unfold heatEnvelope
  fun_prop

theorem integrable_heatEnvelope_comp {a b : ℝ} (hb : 0 < b) (x : ℝ) :
    Integrable (fun y => heatEnvelope a b (x - y)) ν :=
  Integrable.mono' (integrable_const
    ((Real.sqrt (2 * Real.pi * a))⁻¹ * (1 + 1 / a) ^ 2 * (1 + 2 * b)))
    ((continuous_heatEnvelope a b).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (heatEnvelope_nonneg _ _ _)]
      exact heatEnvelope_le hb _)

theorem abs_integral_mul_heatKernel_le {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    {c : ℝ → ℝ} (hcb : ∀ u, |c u| ≤ (1 + 1 / a) ^ 2 * (1 + u ^ 2)) (x : ℝ) :
    |∫ y, c (x - y) * heatKernel s (x - y) ∂ν| ≤ ∫ y, heatEnvelope a b (x - y) ∂ν :=
  (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    (integrable_heatEnvelope_comp (ha.trans_le (has.trans hsb)) x)
    (ae_of_all _ fun _ => abs_mul_heatKernel_le ha has hsb (hcb _)))

theorem continuous_heatDensityDeriv2 {s : ℝ} (hs : 0 < s) :
    Continuous (heatDensityDeriv2 ν s) := by
  have hc2 : Continuous fun u : ℝ => u ^ 2 / s ^ 2 - 1 / s := by fun_prop
  refine continuous_of_dominated (bound := fun _ =>
    (Real.sqrt (2 * Real.pi * s))⁻¹ * (1 + 1 / s) ^ 2 * (1 + 2 * s))
    (fun x => (integrable_mul_heatKernel hs le_rfl le_rfl hc2
      (fun u => heatPoly_deriv2 hs le_rfl u) x).aestronglyMeasurable)
    (fun x => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact (abs_mul_heatKernel_le hs le_rfl le_rfl (heatPoly_deriv2 hs le_rfl _)).trans
        (heatEnvelope_le hs _))
    (integrable_const _) (ae_of_all _ fun _ => ?_)
  exact (hc2.comp (continuous_id.sub continuous_const)).mul
    ((continuous_heatKernel s).comp (continuous_id.sub continuous_const))

theorem integrable_mul_integral_comp_sub (hν2 : Integrable (fun y => y ^ 2) ν) {g : ℝ → ℝ}
    (hgm : Measurable g) (hg0 : ∀ u, 0 ≤ g u) (hg : Integrable fun u => (1 + u ^ 2) * g u) :
    Integrable fun x => (1 + x ^ 2) * ∫ y, g (x - y) ∂ν := by
  set h : ℝ → ℝ := fun u => (1 + u ^ 2) * g u
  have hh0 : ∀ u, 0 ≤ h u := fun u => mul_nonneg (by positivity) (hg0 u)
  have hhm : Measurable h := (by fun_prop : Measurable fun u : ℝ => 1 + u ^ 2).mul hgm
  set D : ℝ × ℝ → ℝ := fun p => 2 * (1 + p.2 ^ 2) * h (p.1 - p.2)
  have hDm : Measurable D :=
    ((by fun_prop : Measurable fun p : ℝ × ℝ => 2 * (1 + p.2 ^ 2))).mul
      (hhm.comp (measurable_fst.sub measurable_snd))
  have hD : Integrable D (volume.prod ν) := by
    refine (integrable_prod_iff' hDm.aestronglyMeasurable).2 ⟨ae_of_all _ fun y =>
      (hg.comp_sub_right y).const_mul (2 * (1 + y ^ 2)), ?_⟩
    have e : ∀ y, ∫ x, ‖D (x, y)‖ = 2 * (1 + y ^ 2) * ∫ u, h u := by
      intro y
      have : ∀ x, ‖D (x, y)‖ = 2 * (1 + y ^ 2) * h (x - y) := fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hh0 _))]
      simp_rw [this]
      rw [integral_const_mul, integral_sub_right_eq_self h y]
    simp_rw [e]
    exact (((integrable_const 1).add hν2).const_mul 2).mul_const _ |>.congr
      (ae_of_all _ fun y => by simp only [Pi.add_apply]; ring)
  have hH : Integrable (fun p : ℝ × ℝ => (1 + p.1 ^ 2) * g (p.1 - p.2)) (volume.prod ν) := by
    refine hD.mono' (((by fun_prop : Measurable fun p : ℝ × ℝ => 1 + p.1 ^ 2)).mul
      (hgm.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    obtain ⟨x, y⟩ := p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hg0 _))]
    simp only [D, h]
    have hw : 1 + x ^ 2 ≤ 2 * (1 + y ^ 2) * (1 + (x - y) ^ 2) := by
      nlinarith [sq_nonneg (x - y - y), mul_nonneg (sq_nonneg y) (sq_nonneg (x - y))]
    calc (1 + x ^ 2) * g (x - y) ≤ (2 * (1 + y ^ 2) * (1 + (x - y) ^ 2)) * g (x - y) :=
          mul_le_mul_of_nonneg_right hw (hg0 _)
      _ = _ := by ring
  refine hH.integral_prod_left.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [integral_const_mul]

end Meat
