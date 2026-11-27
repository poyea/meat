import Meat.Continuous.DeBruijn

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

theorem heatKernel_mul_heatKernel {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (w z : ℝ) :
    heatKernel t z * heatKernel u (w - z)
      = heatKernel (t + u) w * heatKernel (t * u / (t + u)) (z - t * w / (t + u)) := by
  have hpi := Real.pi_pos
  have htu : 0 < t + u := by positivity
  unfold heatKernel
  have hsq : Real.sqrt (2 * Real.pi * t) * Real.sqrt (2 * Real.pi * u)
      = Real.sqrt (2 * Real.pi * (t + u)) * Real.sqrt (2 * Real.pi * (t * u / (t + u))) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hexp : -z ^ 2 / (2 * t) + -(w - z) ^ 2 / (2 * u)
      = -w ^ 2 / (2 * (t + u)) + -(z - t * w / (t + u)) ^ 2 / (2 * (t * u / (t + u))) := by
    field_simp
    ring
  calc (Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-z ^ 2 / (2 * t)) *
        ((Real.sqrt (2 * Real.pi * u))⁻¹ * Real.exp (-(w - z) ^ 2 / (2 * u)))
      = (Real.sqrt (2 * Real.pi * t) * Real.sqrt (2 * Real.pi * u))⁻¹ *
        Real.exp (-z ^ 2 / (2 * t) + -(w - z) ^ 2 / (2 * u)) := by
        rw [Real.exp_add, mul_inv]
        ring
    _ = _ := by
        rw [hsq, hexp, Real.exp_add, mul_inv]
        ring

theorem integrable_mul_heatKernel_volume {s : ℝ} (hs : 0 < s) {c : ℝ → ℝ} (hc : Continuous c)
    (hcb : ∀ u, |c u| ≤ (1 + 1 / s) ^ 2 * (1 + u ^ 2)) :
    Integrable fun v => c v * heatKernel s v := by
  refine (integrable_heatEnvelope (a := s) hs).mono'
    (hc.mul (continuous_heatKernel s)).aestronglyMeasurable (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_mul_heatKernel_le hs le_rfl le_rfl (hcb v)).trans ?_
  have := heatEnvelope_nonneg s s v
  nlinarith [sq_nonneg v]

theorem integral_mul_heatKernel_moment {s : ℝ} (hs : 0 < s) :
    ∫ v, heatKernel s v = 1 ∧ ∫ v, v * heatKernel s v = 0 ∧ ∫ v, v ^ 2 * heatKernel s v = s := by
  have hv : s.toNNReal ≠ 0 := by simp [hs]
  have e : ∀ f : ℝ → ℝ, ∫ v, f v * heatKernel s v = ∫ v, f v ∂gaussianReal 0 s.toNNReal := by
    intro f
    rw [integral_gaussianReal_eq_integral_smul hv]
    congr 1
    ext v
    rw [gaussianPDFReal_eq_heatKernel hs.le, sub_zero, smul_eq_mul, mul_comm]
  refine ⟨by simpa using integral_heatKernel hs 0, ?_, ?_⟩
  · rw [e (fun v => v)]
    exact integral_id_gaussianReal
  · rw [e (fun v => v ^ 2)]
    have := variance_fun_id_gaussianReal (μ := 0) (v := s.toNNReal)
    rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at this
    simpa [Real.coe_toNNReal _ hs.le] using this

private lemma moments_shift {s : ℝ} (hs : 0 < s) (m : ℝ) :
    ∫ v, heatKernel s (v - m) = 1 ∧ ∫ v, (v - m) * heatKernel s (v - m) = 0 ∧
      Integrable (fun v => heatKernel s (v - m)) ∧
      Integrable (fun v => (v - m) * heatKernel s (v - m)) := by
  obtain ⟨h0, h1, -⟩ := integral_mul_heatKernel_moment hs
  have i0 := integrable_mul_heatKernel_volume (c := fun _ => 1) hs continuous_const
    (fun u => heatPoly_one hs u)
  have i1 := integrable_mul_heatKernel_volume (c := fun v => v) hs continuous_id
    (fun u => by
      have h1 : 1 ≤ (1 + 1 / s) ^ 2 := by
        have : 0 ≤ 1 / s := by positivity
        nlinarith
      nlinarith [abs_nonneg u, sq_abs u, sq_nonneg (|u| - 1), sq_nonneg u])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [integral_sub_right_eq_self (fun v => heatKernel s v) m, h0]
  · rw [integral_sub_right_eq_self (fun v => v * heatKernel s v) m, h1]
  · simpa using i0.comp_sub_right m
  · exact i1.comp_sub_right m

theorem integral_heatKernel_mul_heatKernel {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (w : ℝ) :
    ∫ z, heatKernel t z * heatKernel u (w - z) = heatKernel (t + u) w := by
  have hσ : 0 < t * u / (t + u) := by positivity
  simp_rw [heatKernel_mul_heatKernel ht hu w]
  rw [integral_const_mul, (moments_shift hσ _).1, mul_one]

theorem integral_heatKernel_deriv_mul_heatKernel {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (w : ℝ) :
    ∫ z, -(z / t) * heatKernel t z * heatKernel u (w - z)
      = -(w / (t + u)) * heatKernel (t + u) w := by
  have hσ : 0 < t * u / (t + u) := by positivity
  have htu : 0 < t + u := by positivity
  set σ := t * u / (t + u)
  set c := t * w / (t + u)
  obtain ⟨h0, h1, i0, i1⟩ := moments_shift hσ c
  have e : ∀ z, -(z / t) * heatKernel t z * heatKernel u (w - z)
      = (-(heatKernel (t + u) w) / t) * ((z - c) * heatKernel σ (z - c))
        + (-(heatKernel (t + u) w) / t * c) * heatKernel σ (z - c) := by
    intro z
    rw [mul_assoc, heatKernel_mul_heatKernel ht hu w z]
    ring
  simp_rw [e]
  rw [integral_add (i1.const_mul _) (i0.const_mul _), integral_const_mul, integral_const_mul,
    h0, h1]
  simp only [c]
  field_simp
  ring

theorem integral_heatKernel_mul_heatKernel_deriv {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (w : ℝ) :
    ∫ z, heatKernel t z * (-((w - z) / u) * heatKernel u (w - z))
      = -(w / (t + u)) * heatKernel (t + u) w := by
  have hσ : 0 < t * u / (t + u) := by positivity
  have htu : 0 < t + u := by positivity
  set σ := t * u / (t + u)
  set c := t * w / (t + u)
  obtain ⟨h0, h1, i0, i1⟩ := moments_shift hσ c
  have e : ∀ z, heatKernel t z * (-((w - z) / u) * heatKernel u (w - z))
      = (heatKernel (t + u) w / u) * ((z - c) * heatKernel σ (z - c))
        + (-(heatKernel (t + u) w) / u * (w - c)) * heatKernel σ (z - c) := by
    intro z
    rw [mul_left_comm, heatKernel_mul_heatKernel ht hu w z]
    ring
  simp_rw [e]
  rw [integral_add (i1.const_mul _) (i0.const_mul _), integral_const_mul, integral_const_mul,
    h0, h1]
  simp only [c]
  field_simp
  ring

theorem heatKernel_le_const {s : ℝ} (hs : 0 < s) (v : ℝ) :
    heatKernel s v ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ := by
  refine (heatKernel_le hs le_rfl le_rfl v).trans ?_
  have : Real.exp (-(1 / (2 * s)) * v ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 1 / (2 * s) * v ^ 2 := by positivity
    linarith
  have := Real.pi_pos
  calc _ ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

private lemma abs_heatKernel_le {s : ℝ} (hs : 0 < s) (v : ℝ) :
    |heatKernel s v| ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ :=
  (abs_of_pos (heatKernel_pos hs v)).trans_le (heatKernel_le_const hs v)

private lemma abs_heatKernel_deriv_le {s : ℝ} (hs : 0 < s) (v : ℝ) :
    |-(v / s) * heatKernel s v| ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * (1 + 1 / s) ^ 2 * (1 + 2 * s) :=
  (abs_mul_heatKernel_le hs le_rfl le_rfl (heatPoly_deriv hs le_rfl v)).trans (heatEnvelope_le hs v)

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

private lemma integral_heatConv {t : ℝ} (ht : 0 < t) {c : ℝ → ℝ} (hc : Continuous c)
    (hcb : ∀ v, |c v| ≤ (1 + 1 / t) ^ 2 * (1 + v ^ 2)) {e : ℝ → ℝ} (he : Continuous e) {E : ℝ}
    (heb : ∀ v, |e v| ≤ E) (x : ℝ) :
    ∫ z, (∫ y, c (z - y) * heatKernel t (z - y) ∂ν) * e (x - z)
      = ∫ y, (∫ z, c z * heatKernel t z * e (x - y - z)) ∂ν := by
  set a : ℝ → ℝ := fun v => c v * heatKernel t v
  have ha : Integrable a := integrable_mul_heatKernel_volume ht hc hcb
  have hac : Continuous a := hc.mul (continuous_heatKernel t)
  set G : ℝ × ℝ → ℝ := fun p => a (p.1 - p.2) * e (x - p.1)
  have hGc : Continuous G :=
    (hac.comp (continuous_fst.sub continuous_snd)).mul
      (he.comp (continuous_const.sub continuous_fst))
  have hsec : ∀ y, Integrable (fun z => G (z, y)) := fun y =>
    (ha.comp_sub_right y).mul_bdd
      (he.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact heb _)
  have hG : Integrable G (volume.prod ν) := by
    refine (integrable_prod_iff' hGc.aestronglyMeasurable).2 ⟨ae_of_all _ hsec, ?_⟩
    refine Integrable.mono' (integrable_const (E * ∫ v, |a v|))
      (hGc.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z => norm_nonneg _)]
    calc ∫ z, ‖G (z, y)‖ ≤ ∫ z, E * |a (z - y)| :=
          integral_mono (hsec y).norm ((ha.comp_sub_right y).abs.const_mul E) fun z => by
            simp only [G, Real.norm_eq_abs, abs_mul]
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (heb _) (abs_nonneg _)
      _ = E * ∫ v, |a v| := by rw [integral_const_mul, integral_sub_right_eq_self (|a ·|) y]
  have e1 : ∀ z, (∫ y, c (z - y) * heatKernel t (z - y) ∂ν) * e (x - z) = ∫ y, G (z, y) ∂ν :=
    fun z => (integral_mul_const _ _).symm
  simp_rw [e1]
  rw [integral_integral_swap (f := fun z y => G (z, y)) hG]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  rw [← integral_add_right_eq_self (fun z => G (z, y)) y]
  congr 1
  ext z
  simp only [G, a, add_sub_cancel_right]
  rw [show x - (z + y) = x - y - z by ring]

theorem heatDensity_add {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (x : ℝ) :
    heatDensity ν (t + u) x = ∫ z, heatDensity ν t z * heatKernel u (x - z) := by
  have h := integral_heatConv (ν := ν) (c := fun _ => 1) ht continuous_const
    (fun v => heatPoly_one ht v) (continuous_heatKernel u) (abs_heatKernel_le hu) x
  simp only [one_mul] at h
  have h2 : ∫ y, heatKernel (t + u) (x - y) ∂ν
      = ∫ y, (∫ z, heatKernel t z * heatKernel u (x - y - z)) ∂ν := by
    congr 1
    ext y
    exact (integral_heatKernel_mul_heatKernel ht hu (x - y)).symm
  exact h2.trans h.symm

theorem heatDensityDeriv_add {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (x : ℝ) :
    heatDensityDeriv ν (t + u) x = ∫ z, heatDensityDeriv ν t z * heatKernel u (x - z) := by
  have h := integral_heatConv (ν := ν) (c := fun v => -(v / t)) ht
    (continuous_id.div_const t).neg (fun v => heatPoly_deriv ht le_rfl v)
    (continuous_heatKernel u) (abs_heatKernel_le hu) x
  have h2 : ∫ y, -((x - y) / (t + u)) * heatKernel (t + u) (x - y) ∂ν
      = ∫ y, (∫ z, -(z / t) * heatKernel t z * heatKernel u (x - y - z)) ∂ν := by
    congr 1
    ext y
    exact (integral_heatKernel_deriv_mul_heatKernel ht hu (x - y)).symm
  exact h2.trans h.symm

theorem heatDensityDeriv_add' {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (x : ℝ) :
    heatDensityDeriv ν (t + u) x
      = ∫ z, heatDensity ν t z * (-((x - z) / u) * heatKernel u (x - z)) := by
  have hc : Continuous fun v : ℝ => -(v / u) * heatKernel u v :=
    (continuous_id.div_const u).neg.mul (continuous_heatKernel u)
  have h := integral_heatConv (ν := ν) (c := fun _ => 1) ht continuous_const
    (fun v => heatPoly_one ht v) hc (abs_heatKernel_deriv_le hu) x
  simp only [one_mul] at h
  have h2 : ∫ y, -((x - y) / (t + u)) * heatKernel (t + u) (x - y) ∂ν
      = ∫ y, (∫ z, heatKernel t z * (-((x - y - z) / u) * heatKernel u (x - y - z))) ∂ν := by
    congr 1
    ext y
    exact (integral_heatKernel_mul_heatKernel_deriv ht hu (x - y)).symm
  exact h2.trans h.symm

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

theorem heatFisher_add_le (hν2 : Integrable (fun y => y ^ 2) ν) {t u : ℝ} (ht : 0 < t)
    (hu : 0 < u) : heatFisher ν (t + u) ≤ heatFisher ν t / (1 + u * heatFisher ν t) := by
  set J := heatFisher ν t
  have hJ0 : 0 ≤ J := heatFisher_nonneg ht
  have hden : 0 < 1 + u * J := by positivity
  set l := 1 / (1 + u * J)
  set P := heatDensity ν t
  set D := heatDensityDeriv ν t
  have hP : ∀ z, 0 < P z := heatDensity_pos ht
  have hPi : Integrable P := integrable_heatDensity hν2 ht
  have hDi : Integrable D := integrable_heatDensityDeriv hν2 ht
  have hFi : Integrable fun z => D z ^ 2 / P z := integrable_heatFisher hν2 ht
  have hPc : Continuous P := continuous_heatDensity ht
  have hDc : Continuous D := continuous_heatDensityDeriv ht
  have hFc : Continuous fun z => D z ^ 2 / P z := (hDc.pow 2).div hPc fun z => (hP z).ne'
  set b1 : ℝ → ℝ := fun v => heatKernel u v
  set b2 : ℝ → ℝ := fun v => -(v / u) * heatKernel u v
  set b3 : ℝ → ℝ := fun v => v ^ 2 / u ^ 2 * heatKernel u v
  have hb1c : Continuous b1 := continuous_heatKernel u
  have hb2c : Continuous b2 := (continuous_id.div_const u).neg.mul (continuous_heatKernel u)
  have hb3c : Continuous b3 := (by fun_prop : Continuous fun v : ℝ => v ^ 2 / u ^ 2).mul
    (continuous_heatKernel u)
  have hb1 : Integrable b1 := by
    simpa [b1] using integrable_mul_heatKernel_volume (c := fun _ => 1) hu continuous_const
      (fun v => heatPoly_one hu v)
  have hb2 : Integrable b2 := integrable_mul_heatKernel_volume hu
    (continuous_id.div_const u).neg (fun v => heatPoly_deriv hu le_rfl v)
  have hb3 : Integrable b3 := integrable_mul_heatKernel_volume hu
    (by fun_prop : Continuous fun v : ℝ => v ^ 2 / u ^ 2) (fun v => heatPoly_sq hu le_rfl v)
  obtain ⟨m0, m1, m2⟩ := integral_mul_heatKernel_moment hu
  have hm1 : ∫ v, b1 v = 1 := m0
  have hm2 : ∫ v, b2 v = 0 := by
    have : ∀ v, b2 v = (-(1 / u)) * (v * heatKernel u v) := fun v => by simp only [b2]; ring
    simp_rw [this]
    rw [integral_const_mul, m1, mul_zero]
  have hm3 : ∫ v, b3 v = 1 / u := by
    have : ∀ v, b3 v = (1 / u ^ 2) * (v ^ 2 * heatKernel u v) := fun v => by simp only [b3]; ring
    simp_rw [this]
    rw [integral_const_mul, m2]
    field_simp
  have hC : ∀ v, |b1 v| ≤ (Real.sqrt (2 * Real.pi * u))⁻¹ := abs_heatKernel_le hu
  have hC2 : ∀ v, |b2 v| ≤ (Real.sqrt (2 * Real.pi * u))⁻¹ * (1 + 1 / u) ^ 2 * (1 + 2 * u) :=
    abs_heatKernel_deriv_le hu
  set H : ℝ × ℝ → ℝ := fun p => l ^ 2 * (D p.2 ^ 2 / P p.2 * b1 (p.1 - p.2)) +
    2 * l * (1 - l) * (D p.2 * b2 (p.1 - p.2)) + (1 - l) ^ 2 * (P p.2 * b3 (p.1 - p.2))
  have hH : Integrable H (volume.prod volume) :=
    ((((integrable_prod_comp_sub hFi hFc hb1 hb1c).const_mul (l ^ 2)).add
      ((integrable_prod_comp_sub hDi hDc hb2 hb2c).const_mul (2 * l * (1 - l)))).add
      ((integrable_prod_comp_sub hPi hPc hb3 hb3c).const_mul ((1 - l) ^ 2)))
  have hpt : ∀ᵐ x, heatDensityDeriv ν (t + u) x ^ 2 / heatDensity ν (t + u) x
      ≤ ∫ z, H (x, z) := by
    filter_upwards [hH.prod_right_ae] with x hHx
    have hcont : ∀ {f : ℝ → ℝ}, Continuous f → Continuous fun z => f (x - z) :=
      fun hf => hf.comp (continuous_const.sub continuous_id)
    set w : ℝ → ℝ := fun z => P z * b1 (x - z)
    set g : ℝ → ℝ := fun z => l * (D z / P z) + (1 - l) * (-((x - z) / u))
    have hw0 : ∀ z, 0 ≤ w z := fun z => mul_nonneg (hP z).le (heatKernel_pos hu _).le
    have hwi : Integrable w := hPi.mul_bdd (hcont hb1c).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)
    have hi1 : Integrable fun z => D z * b1 (x - z) := hDi.mul_bdd (hcont hb1c).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)
    have hi2 : Integrable fun z => P z * b2 (x - z) := hPi.mul_bdd (hcont hb2c).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC2 _)
    have hwg : (fun z => w z * g z)
        = fun z => l * (D z * b1 (x - z)) + (1 - l) * (P z * b2 (x - z)) := by
      ext z
      have := (hP z).ne'
      simp only [w, g, b1, b2]
      field_simp
    have hwg2 : (fun z => w z * g z ^ 2) = fun z => H (x, z) := by
      ext z
      have := (hP z).ne'
      simp only [w, g, b1, b2, b3, H]
      field_simp
      ring
    have hcs := sq_integral_mul_le hw0 hwi (hwg ▸ ((hi1.const_mul l).add (hi2.const_mul (1 - l))))
      (hwg2 ▸ hHx)
    have hW : ∫ z, w z = heatDensity ν (t + u) x := (heatDensity_add ht hu x).symm
    have hA : ∫ z, w z * g z = heatDensityDeriv ν (t + u) x := by
      rw [hwg, integral_add (hi1.const_mul l) (hi2.const_mul (1 - l)), integral_const_mul,
        integral_const_mul]
      have e1 : ∫ z, D z * b1 (x - z) = heatDensityDeriv ν (t + u) x :=
        (heatDensityDeriv_add ht hu x).symm
      have e2 : ∫ z, P z * b2 (x - z) = heatDensityDeriv ν (t + u) x :=
        (heatDensityDeriv_add' ht hu x).symm
      rw [e1, e2]
      ring
    rw [hW, hA, hwg2] at hcs
    rw [div_le_iff₀ (heatDensity_pos (by positivity) x)]
    linarith
  have hmono := integral_mono_ae (integrable_heatFisher hν2 (by positivity))
    hH.integral_prod_left hpt
  have hswap : ∫ x, ∫ z, H (x, z) = ∫ z, ∫ x, H (x, z) :=
    integral_integral_swap (f := fun x z => H (x, z)) hH
  have hinner : ∀ z, ∫ x, H (x, z) = l ^ 2 * (D z ^ 2 / P z) + (1 - l) ^ 2 / u * P z := by
    intro z
    have i1 := (hb1.comp_sub_right z).const_mul (D z ^ 2 / P z)
    have i2 := (hb2.comp_sub_right z).const_mul (D z)
    have i3 := (hb3.comp_sub_right z).const_mul (P z)
    have j1 : Integrable fun x => l ^ 2 * (D z ^ 2 / P z * b1 (x - z)) +
        2 * l * (1 - l) * (D z * b2 (x - z)) := (i1.const_mul _).add (i2.const_mul _)
    simp only [H]
    rw [integral_add j1 (i3.const_mul _),
      integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sub_right_eq_self b1 z, integral_sub_right_eq_self b2 z,
      integral_sub_right_eq_self b3 z, hm1, hm2, hm3]
    ring
  simp_rw [hinner] at hswap
  rw [integral_add (hFi.const_mul _) (hPi.const_mul _), integral_const_mul, integral_const_mul,
    integral_heatDensity hν2 ht] at hswap
  have hJdef : ∫ z, D z ^ 2 / P z = J := rfl
  rw [hJdef] at hswap
  have hfin : l ^ 2 * J + (1 - l) ^ 2 / u * 1 = J / (1 + u * J) := by
    simp only [l]
    field_simp
    ring
  calc heatFisher ν (t + u) ≤ ∫ x, ∫ z, H (x, z) := hmono
    _ = J / (1 + u * J) := by rw [hswap, hfin]

end Meat
