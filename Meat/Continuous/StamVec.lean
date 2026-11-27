import Meat.Continuous.DeBruijnVec

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

variable {n : ℕ}

private lemma prod_compl_eq (F : Fin n → ℝ) (i : Fin n) : ∏ j, F j = F i * ∏ j ∈ {i}ᶜ, F j := by
  classical
  exact Fintype.prod_eq_mul_prod_compl i F

private lemma integral_mul_prod_compl (F : Fin n → ℝ → ℝ) (i : Fin n) (G : ℝ → ℝ) :
    ∫ z : Fin n → ℝ, G (z i) * ∏ j ∈ {i}ᶜ, F j (z j) = (∫ r, G r) * ∏ j ∈ {i}ᶜ, ∫ r, F j r := by
  classical
  set f : Fin n → ℝ → ℝ := Function.update F i G
  have h1 : ∀ z : Fin n → ℝ, G (z i) * ∏ j ∈ {i}ᶜ, F j (z j) = ∏ j, f j (z j) := fun z => by
    rw [prod_compl_eq (fun j => f j (z j)) i]
    simp only [f, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (by simpa using hj : j ≠ i)]
  simp_rw [h1]
  rw [integral_fintype_prod_volume_eq_prod, prod_compl_eq (fun j => ∫ r, f j r) i]
  simp only [f, Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (by simpa using hj : j ≠ i)]

private lemma heatKernelVec_eq_mul (s : ℝ) (u : Fin n → ℝ) (i : Fin n) :
    heatKernelVec s u = heatKernel s (u i) * ∏ j ∈ {i}ᶜ, heatKernel s (u j) :=
  prod_compl_eq (fun j => heatKernel s (u j)) i

theorem integral_comp_mul_heatKernelVec {u : ℝ} (hu : 0 < u) (g : ℝ → ℝ) (i : Fin n) :
    ∫ v : Fin n → ℝ, g (v i) * heatKernelVec u v = ∫ r, g r * heatKernel u r := by
  have e : ∀ v : Fin n → ℝ, g (v i) * heatKernelVec u v
      = (fun r => g r * heatKernel u r) (v i) * ∏ j ∈ {i}ᶜ, heatKernel u (v j) := fun v => by
    rw [heatKernelVec_eq_mul u v i]
    ring
  refine (integral_congr_ae (ae_of_all _ e)).trans
    ((integral_mul_prod_compl (fun _ => heatKernel u) i (fun r => g r * heatKernel u r)).trans ?_)
  rw [(integral_mul_heatKernel_moment hu).1]
  simp

theorem integral_heatKernelVec_mul_heatKernelVec {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (w : Fin n → ℝ) :
    ∫ z, heatKernelVec t z * heatKernelVec u (w - z) = heatKernelVec (t + u) w := by
  have e : ∀ z : Fin n → ℝ, heatKernelVec t z * heatKernelVec u (w - z)
      = ∏ j, heatKernel t (z j) * heatKernel u (w j - z j) := fun z => by
    rw [heatKernelVec, heatKernelVec, ← Finset.prod_mul_distrib]
    rfl
  simp_rw [e]
  rw [integral_fintype_prod_volume_eq_prod (fun j r => heatKernel t r * heatKernel u (w j - r))]
  exact Finset.prod_congr rfl fun j _ => integral_heatKernel_mul_heatKernel ht hu (w j)

theorem integral_heatKernelVec_deriv_mul {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (w : Fin n → ℝ)
    (i : Fin n) :
    ∫ z, -(z i / t) * heatKernelVec t z * heatKernelVec u (w - z)
      = -(w i / (t + u)) * heatKernelVec (t + u) w := by
  have e : ∀ z : Fin n → ℝ, -(z i / t) * heatKernelVec t z * heatKernelVec u (w - z)
      = (fun r => -(r / t) * heatKernel t r * heatKernel u (w i - r)) (z i) *
        ∏ j ∈ {i}ᶜ, (fun r => heatKernel t r * heatKernel u (w j - r)) (z j) := fun z => by
    rw [heatKernelVec_eq_mul t z i, heatKernelVec_eq_mul u (w - z) i, Finset.prod_mul_distrib]
    simp only [Pi.sub_apply]
    ring
  refine (integral_congr_ae (ae_of_all _ e)).trans
    ((integral_mul_prod_compl (fun j r => heatKernel t r * heatKernel u (w j - r)) i
      (fun r => -(r / t) * heatKernel t r * heatKernel u (w i - r))).trans ?_)
  rw [integral_heatKernel_deriv_mul_heatKernel ht hu, heatKernelVec_eq_mul (t + u) w i]
  rw [Finset.prod_congr rfl fun j _ => integral_heatKernel_mul_heatKernel ht hu (w j)]
  ring

theorem integral_heatKernelVec_mul_deriv {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (w : Fin n → ℝ)
    (i : Fin n) :
    ∫ z, heatKernelVec t z * (-((w - z) i / u) * heatKernelVec u (w - z))
      = -(w i / (t + u)) * heatKernelVec (t + u) w := by
  have e : ∀ z : Fin n → ℝ, heatKernelVec t z * (-((w - z) i / u) * heatKernelVec u (w - z))
      = (fun r => heatKernel t r * (-((w i - r) / u) * heatKernel u (w i - r))) (z i) *
        ∏ j ∈ {i}ᶜ, (fun r => heatKernel t r * heatKernel u (w j - r)) (z j) := fun z => by
    rw [heatKernelVec_eq_mul t z i, heatKernelVec_eq_mul u (w - z) i, Finset.prod_mul_distrib]
    simp only [Pi.sub_apply]
    ring
  refine (integral_congr_ae (ae_of_all _ e)).trans
    ((integral_mul_prod_compl (fun j r => heatKernel t r * heatKernel u (w j - r)) i
      (fun r => heatKernel t r * (-((w i - r) / u) * heatKernel u (w i - r)))).trans ?_)
  rw [integral_heatKernel_mul_heatKernel_deriv ht hu, heatKernelVec_eq_mul (t + u) w i]
  rw [Finset.prod_congr rfl fun j _ => integral_heatKernel_mul_heatKernel ht hu (w j)]
  ring

theorem integrable_mul_heatKernelVec_volume {s : ℝ} (hs : 0 < s) {c : (Fin n → ℝ) → ℝ}
    (hc : Continuous c)
    (hcb : ∀ u, |c u| ≤ (n + 1) * (1 + 1 / s) ^ 2 * (1 + ∑ j, u j ^ 2)) :
    Integrable fun v => c v * heatKernelVec s v := by
  refine (integrable_heatEnvelopeVec (a := s) hs).mono'
    (hc.mul (continuous_heatKernelVec s)).aestronglyMeasurable (ae_of_all _ fun v => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_mul_heatKernelVec_le hs le_rfl le_rfl (hcb v)).trans ?_
  have := heatEnvelopeVec_nonneg s s v
  have h0 : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

variable {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]

private lemma integral_heatConvVec {t : ℝ} (ht : 0 < t) {c : (Fin n → ℝ) → ℝ}
    (hc : Continuous c)
    (hcb : ∀ v, |c v| ≤ (n + 1) * (1 + 1 / t) ^ 2 * (1 + ∑ j, v j ^ 2))
    {e : (Fin n → ℝ) → ℝ} (he : Continuous e) {E : ℝ} (heb : ∀ v, |e v| ≤ E)
    (x : Fin n → ℝ) :
    ∫ z, (∫ y, c (z - y) * heatKernelVec t (z - y) ∂μ) * e (x - z)
      = ∫ y, (∫ z, c z * heatKernelVec t z * e (x - y - z)) ∂μ := by
  set a : (Fin n → ℝ) → ℝ := fun v => c v * heatKernelVec t v
  have ha : Integrable a := integrable_mul_heatKernelVec_volume ht hc hcb
  have hac : Continuous a := hc.mul (continuous_heatKernelVec t)
  set G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => a (p.1 - p.2) * e (x - p.1)
  have hGc : Continuous G :=
    (hac.comp (continuous_fst.sub continuous_snd)).mul
      (he.comp (continuous_const.sub continuous_fst))
  have hsec : ∀ y, Integrable (fun z => G (z, y)) := fun y =>
    (ha.comp_sub_right y).mul_bdd
      (he.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact heb _)
  have hG : Integrable G (volume.prod μ) := by
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
  have e1 : ∀ z, (∫ y, c (z - y) * heatKernelVec t (z - y) ∂μ) * e (x - z)
      = ∫ y, G (z, y) ∂μ := fun z => (integral_mul_const _ _).symm
  simp_rw [e1]
  rw [integral_integral_swap (f := fun z y => G (z, y)) hG]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  rw [← integral_add_right_eq_self (fun z => G (z, y)) y]
  congr 1
  ext z
  simp only [G, a, add_sub_cancel_right]
  rw [show x - (z + y) = x - y - z by abel]

private lemma abs_heatKernelVec_le {u : ℝ} (hu : 0 < u) (v : Fin n → ℝ) :
    |heatKernelVec u v| ≤ (Real.sqrt (2 * Real.pi * u))⁻¹ ^ n :=
  (abs_of_pos (heatKernelVec_pos hu v)).trans_le (heatKernelVec_le_const hu v)

private lemma abs_heatKernelVec_deriv_le {u : ℝ} (hu : 0 < u) (i : Fin n) (v : Fin n → ℝ) :
    |-(v i / u) * heatKernelVec u v|
      ≤ (Real.sqrt (2 * Real.pi * u))⁻¹ ^ n * ((n + 1) * (1 + 1 / u) ^ 2) * (1 + 2 * u) :=
  (abs_mul_heatKernelVec_le hu le_rfl le_rfl (heatPolyVec_deriv hu le_rfl v i)).trans
    (heatEnvelopeVec_le hu v)

theorem heatDensityVec_add {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (x : Fin n → ℝ) :
    heatDensityVec μ (t + u) x = ∫ z, heatDensityVec μ t z * heatKernelVec u (x - z) := by
  have h := integral_heatConvVec (μ := μ) (c := fun _ => 1) ht continuous_const
    (fun v => heatPolyVec_one ht v) (continuous_heatKernelVec u) (abs_heatKernelVec_le hu) x
  simp only [one_mul] at h
  have h2 : ∫ y, heatKernelVec (t + u) (x - y) ∂μ
      = ∫ y, (∫ z, heatKernelVec t z * heatKernelVec u (x - y - z)) ∂μ := by
    congr 1
    ext y
    exact (integral_heatKernelVec_mul_heatKernelVec ht hu (x - y)).symm
  exact h2.trans h.symm

theorem heatDensityVecDeriv_add {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (i : Fin n)
    (x : Fin n → ℝ) :
    heatDensityVecDeriv μ (t + u) i x
      = ∫ z, heatDensityVecDeriv μ t i z * heatKernelVec u (x - z) := by
  have h := integral_heatConvVec (μ := μ) (c := fun v => -(v i / t)) ht (by fun_prop)
    (fun v => heatPolyVec_deriv ht le_rfl v i) (continuous_heatKernelVec u)
    (abs_heatKernelVec_le hu) x
  have h2 : ∫ y, -((x - y) i / (t + u)) * heatKernelVec (t + u) (x - y) ∂μ
      = ∫ y, (∫ z, -(z i / t) * heatKernelVec t z * heatKernelVec u (x - y - z)) ∂μ := by
    congr 1
    ext y
    exact (integral_heatKernelVec_deriv_mul ht hu (x - y) i).symm
  exact h2.trans h.symm

theorem heatDensityVecDeriv_add' {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (i : Fin n)
    (x : Fin n → ℝ) :
    heatDensityVecDeriv μ (t + u) i x
      = ∫ z, heatDensityVec μ t z * (-((x - z) i / u) * heatKernelVec u (x - z)) := by
  have hc : Continuous fun v : Fin n → ℝ => -(v i / u) * heatKernelVec u v :=
    (by fun_prop : Continuous fun v : Fin n → ℝ => -(v i / u)).mul (continuous_heatKernelVec u)
  have h := integral_heatConvVec (μ := μ) (c := fun _ => 1) ht continuous_const
    (fun v => heatPolyVec_one ht v) hc (abs_heatKernelVec_deriv_le hu i) x
  simp only [one_mul] at h
  have h2 : ∫ y, -((x - y) i / (t + u)) * heatKernelVec (t + u) (x - y) ∂μ
      = ∫ y, (∫ z, heatKernelVec t z *
          (-((x - y - z) i / u) * heatKernelVec u (x - y - z))) ∂μ := by
    congr 1
    ext y
    exact (integral_heatKernelVec_mul_deriv ht hu (x - y) i).symm
  exact h2.trans h.symm

private lemma integrable_prod_comp_sub {a b : (Fin n → ℝ) → ℝ} (ha : Integrable a)
    (hac : Continuous a) (hb : Integrable b) (hbc : Continuous b) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => a p.2 * b (p.1 - p.2))
      (volume.prod volume) := by
  refine (integrable_prod_iff' ((hac.comp continuous_snd).mul
    (hbc.comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable).2
    ⟨ae_of_all _ fun z => (hb.comp_sub_right z).const_mul (a z), ?_⟩
  refine (ha.norm.mul_const (∫ v, ‖b v‖)).congr (ae_of_all _ fun z => ?_)
  change ‖a z‖ * ∫ v, ‖b v‖ = ∫ x, ‖a z * b (x - z)‖
  simp only [norm_mul]
  rw [integral_const_mul, integral_sub_right_eq_self (fun v => ‖b v‖) z]

private lemma fisher_coord_le (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {t u : ℝ}
    (ht : 0 < t) (hu : 0 < u) (l : ℝ) (i : Fin n) :
    ∫ x, heatDensityVecDeriv μ (t + u) i x ^ 2 / heatDensityVec μ (t + u) x
      ≤ l ^ 2 * (∫ z, heatDensityVecDeriv μ t i z ^ 2 / heatDensityVec μ t z)
        + (1 - l) ^ 2 / u := by
  set P := heatDensityVec μ t
  set D := heatDensityVecDeriv μ t i
  have hP : ∀ z, 0 < P z := heatDensityVec_pos ht
  have hPi : Integrable P := integrable_heatDensityVec hμ2 ht
  have hDi : Integrable D := integrable_heatDensityVecDeriv hμ2 ht i
  have hFi : Integrable fun z => D z ^ 2 / P z := integrable_heatFisherVec hμ2 ht i
  have hPc : Continuous P := continuous_heatDensityVec ht
  have hDc : Continuous D := continuous_heatDensityVecDeriv ht i
  have hFc : Continuous fun z => D z ^ 2 / P z := (hDc.pow 2).div hPc fun z => (hP z).ne'
  set b1 : (Fin n → ℝ) → ℝ := fun v => heatKernelVec u v
  set b2 : (Fin n → ℝ) → ℝ := fun v => -(v i / u) * heatKernelVec u v
  set b3 : (Fin n → ℝ) → ℝ := fun v => v i ^ 2 / u ^ 2 * heatKernelVec u v
  have hb1c : Continuous b1 := continuous_heatKernelVec u
  have hb2c : Continuous b2 :=
    (by fun_prop : Continuous fun v : Fin n → ℝ => -(v i / u)).mul (continuous_heatKernelVec u)
  have hb3c : Continuous b3 :=
    (by fun_prop : Continuous fun v : Fin n → ℝ => v i ^ 2 / u ^ 2).mul
      (continuous_heatKernelVec u)
  have hb1 : Integrable b1 := integrable_heatKernelVec hu
  have hb2 : Integrable b2 := integrable_mul_heatKernelVec_volume hu (by fun_prop)
    (fun v => heatPolyVec_deriv hu le_rfl v i)
  have hb3 : Integrable b3 := integrable_mul_heatKernelVec_volume hu (by fun_prop)
    (fun v => heatPolyVec_sq hu le_rfl v i)
  obtain ⟨m0, m1, m2⟩ := integral_mul_heatKernel_moment hu
  have hm1 : ∫ v, b1 v = 1 := integral_heatKernelVec hu
  have hm2 : ∫ v, b2 v = 0 := by
    have h := integral_comp_mul_heatKernelVec hu (fun r => -(r / u)) i
    have e : ∫ r, -(r / u) * heatKernel u r = 0 := by
      have : ∀ r, -(r / u) * heatKernel u r = (-(1 / u)) * (r * heatKernel u r) := fun r => by
        ring
      simp_rw [this]
      rw [integral_const_mul, m1, mul_zero]
    rw [e] at h
    exact h
  have hm3 : ∫ v, b3 v = 1 / u := by
    have h := integral_comp_mul_heatKernelVec hu (fun r => r ^ 2 / u ^ 2) i
    have e : ∫ r, r ^ 2 / u ^ 2 * heatKernel u r = 1 / u := by
      have : ∀ r, r ^ 2 / u ^ 2 * heatKernel u r = (1 / u ^ 2) * (r ^ 2 * heatKernel u r) :=
        fun r => by ring
      simp_rw [this]
      rw [integral_const_mul, m2]
      field_simp
    rw [e] at h
    exact h
  have hC : ∀ v, |b1 v| ≤ (Real.sqrt (2 * Real.pi * u))⁻¹ ^ n := abs_heatKernelVec_le hu
  have hC2 := abs_heatKernelVec_deriv_le hu i
  set H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => l ^ 2 * (D p.2 ^ 2 / P p.2 * b1 (p.1 - p.2)) +
    2 * l * (1 - l) * (D p.2 * b2 (p.1 - p.2)) + (1 - l) ^ 2 * (P p.2 * b3 (p.1 - p.2))
  have hH : Integrable H (volume.prod volume) :=
    ((((integrable_prod_comp_sub hFi hFc hb1 hb1c).const_mul (l ^ 2)).add
      ((integrable_prod_comp_sub hDi hDc hb2 hb2c).const_mul (2 * l * (1 - l)))).add
      ((integrable_prod_comp_sub hPi hPc hb3 hb3c).const_mul ((1 - l) ^ 2)))
  have hpt : ∀ᵐ x, heatDensityVecDeriv μ (t + u) i x ^ 2 / heatDensityVec μ (t + u) x
      ≤ ∫ z, H (x, z) := by
    filter_upwards [hH.prod_right_ae] with x hHx
    have hcont : ∀ {f : (Fin n → ℝ) → ℝ}, Continuous f → Continuous fun z => f (x - z) :=
      fun hf => hf.comp (continuous_const.sub continuous_id)
    set w : (Fin n → ℝ) → ℝ := fun z => P z * b1 (x - z)
    set g : (Fin n → ℝ) → ℝ := fun z => l * (D z / P z) + (1 - l) * (-((x - z) i / u))
    have hw0 : ∀ z, 0 ≤ w z := fun z => mul_nonneg (hP z).le (heatKernelVec_pos hu _).le
    have hwi : Integrable w := hPi.mul_bdd (hcont hb1c).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)
    have hi1 : Integrable fun z => D z * b1 (x - z) :=
      hDi.mul_bdd (hcont hb1c).aestronglyMeasurable
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)
    have hi2 : Integrable fun z => P z * b2 (x - z) :=
      hPi.mul_bdd (hcont hb2c).aestronglyMeasurable
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
    have hcs := sq_integral_mul_le hw0 hwi
      (hwg ▸ ((hi1.const_mul l).add (hi2.const_mul (1 - l)))) (hwg2 ▸ hHx)
    have hW : ∫ z, w z = heatDensityVec μ (t + u) x := (heatDensityVec_add ht hu x).symm
    have hA : ∫ z, w z * g z = heatDensityVecDeriv μ (t + u) i x := by
      rw [hwg, integral_add (hi1.const_mul l) (hi2.const_mul (1 - l)), integral_const_mul,
        integral_const_mul]
      have e1 : ∫ z, D z * b1 (x - z) = heatDensityVecDeriv μ (t + u) i x :=
        (heatDensityVecDeriv_add ht hu i x).symm
      have e2 : ∫ z, P z * b2 (x - z) = heatDensityVecDeriv μ (t + u) i x :=
        (heatDensityVecDeriv_add' ht hu i x).symm
      rw [e1, e2]
      ring
    rw [hW, hA, hwg2] at hcs
    rw [div_le_iff₀ (heatDensityVec_pos (by positivity) x)]
    linarith
  have hmono := integral_mono_ae (integrable_heatFisherVec hμ2 (by positivity) i)
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
    integral_heatDensityVec ht] at hswap
  calc ∫ x, heatDensityVecDeriv μ (t + u) i x ^ 2 / heatDensityVec μ (t + u) x
      ≤ ∫ x, ∫ z, H (x, z) := hmono
    _ = _ := by rw [hswap]; ring

theorem heatFisherVec_add_le (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) (hn : 0 < n)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    heatFisherVec μ (t + u) ≤ heatFisherVec μ t / (1 + u * heatFisherVec μ t / n) := by
  set J := heatFisherVec μ t
  have hJ0 : 0 ≤ J := heatFisherVec_nonneg ht
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hden : 0 < 1 + u * J / n := by positivity
  set l := 1 / (1 + u * J / n)
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => fisher_coord_le hμ2 ht hu l i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  have hJ : ∑ i, ∫ z, heatDensityVecDeriv μ t i z ^ 2 / heatDensityVec μ t z = J := rfl
  rw [hJ] at h
  have hfin : l ^ 2 * J + n * ((1 - l) ^ 2 / u) = J / (1 + u * J / n) := by
    simp only [l]
    field_simp
    ring
  calc heatFisherVec μ (t + u) ≤ l ^ 2 * J + n * ((1 - l) ^ 2 / u) := h
    _ = _ := hfin

end Meat
