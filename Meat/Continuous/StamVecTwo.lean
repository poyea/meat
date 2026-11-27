import Meat.Continuous.StamVec

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

variable {n : ℕ} {ν ρ : Measure (Fin n → ℝ)} [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

private lemma sum_sq_add_le (a b : Fin n → ℝ) :
    ∑ i, (a i + b i) ^ 2 ≤ 2 * ∑ i, a i ^ 2 + 2 * ∑ i, b i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (a i - b i)]

theorem integrable_sum_sq_conv (hν2 : Integrable (fun y => ∑ i, y i ^ 2) ν)
    (hρ2 : Integrable (fun y => ∑ i, y i ^ 2) ρ) :
    Integrable (fun y => ∑ i, y i ^ 2) (ν ∗ ρ) := by
  have hm : AEStronglyMeasurable (fun y : Fin n → ℝ => ∑ i, y i ^ 2)
      (Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 + p.2) (ν.prod ρ)) :=
    (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2).aestronglyMeasurable
  change Integrable _ (Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 + p.2) (ν.prod ρ))
  refine (integrable_map_measure hm (by fun_prop)).2 ?_
  refine (((hν2.comp_fst ρ).const_mul 2).add ((hρ2.comp_snd ν).const_mul 2)).mono'
    (by fun_prop) (ae_of_all _ fun p => ?_)
  have h0 : 0 ≤ ∑ i, (p.1 i + p.2 i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp only [Function.comp_apply, Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg h0]
  exact sum_sq_add_le p.1 p.2

private lemma abs_heatKernelVec_le' {u : ℝ} (hu : 0 < u) (v : Fin n → ℝ) :
    |heatKernelVec u v| ≤ (Real.sqrt (2 * Real.pi * u))⁻¹ ^ n :=
  (abs_of_pos (heatKernelVec_pos hu v)).trans_le (heatKernelVec_le_const hu v)

private lemma abs_heatKernelVec_deriv_le' {u : ℝ} (hu : 0 < u) (i : Fin n) (v : Fin n → ℝ) :
    |-(v i / u) * heatKernelVec u v|
      ≤ (Real.sqrt (2 * Real.pi * u))⁻¹ ^ n * ((n + 1) * (1 + 1 / u) ^ 2) * (1 + 2 * u) :=
  (abs_mul_heatKernelVec_le hu le_rfl le_rfl (heatPolyVec_deriv hu le_rfl v i)).trans
    (heatEnvelopeVec_le hu v)

private lemma integral_conv_eq {a b c : (Fin n → ℝ) → ℝ} (ha : Integrable a) (hac : Continuous a)
    (hbc : Continuous b) {C : ℝ} (hC : ∀ v, |b v| ≤ C) (hcc : Continuous c)
    (habc : ∀ w, ∫ z, a z * b (w - z) = c w) (x : Fin n → ℝ) :
    ∫ w, c (x - w) ∂(ν ∗ ρ) = ∫ z, (∫ y, a (z - y) ∂ν) * ∫ y, b (x - z - y) ∂ρ := by
  have hm : AEStronglyMeasurable (fun w => c (x - w))
      (Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 + p.2) (ν.prod ρ)) :=
    (hcc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  change ∫ w, c (x - w) ∂(Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 + p.2)
    (ν.prod ρ)) = _
  rw [integral_map (by fun_prop) hm]
  set F : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) → ℝ :=
    fun q => a (q.2 - q.1.1) * b (x - q.2 - q.1.2)
  have hFc : Continuous F :=
    (hac.comp (continuous_snd.sub (continuous_fst.comp continuous_fst))).mul
      (hbc.comp ((continuous_const.sub continuous_snd).sub (continuous_snd.comp continuous_fst)))
  have hsec : ∀ p : (Fin n → ℝ) × (Fin n → ℝ), Integrable fun z => F (p, z) := fun p =>
    (ha.comp_sub_right p.1).mul_bdd
      (by fun_prop : Continuous fun z => b (x - z - p.2)).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)
  have hF : Integrable F ((ν.prod ρ).prod volume) := by
    refine (integrable_prod_iff hFc.aestronglyMeasurable).2 ⟨ae_of_all _ hsec, ?_⟩
    refine Integrable.mono' (integrable_const (C * ∫ v, |a v|))
      (hFc.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z => norm_nonneg _)]
    calc ∫ z, ‖F (p, z)‖ ≤ ∫ z, C * |a (z - p.1)| :=
          integral_mono (hsec p).norm ((ha.comp_sub_right p.1).abs.const_mul C) fun z => by
            simp only [F, Real.norm_eq_abs, abs_mul]
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)
      _ = C * ∫ v, |a v| := by rw [integral_const_mul, integral_sub_right_eq_self (|a ·|) p.1]
  have e1 : ∀ p : (Fin n → ℝ) × (Fin n → ℝ), c (x - (p.1 + p.2)) = ∫ z, F (p, z) := by
    intro p
    rw [← habc, ← integral_sub_right_eq_self (fun z => a z * b (x - (p.1 + p.2) - z)) p.1]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [F]
    congr 2
    abel
  simp_rw [e1]
  rw [integral_integral_swap (f := fun p z => F (p, z)) hF]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  exact integral_prod_mul (fun y => a (z - y)) (fun y => b (x - z - y))

private theorem heatDensityVec_conv {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (x : Fin n → ℝ) :
    heatDensityVec (ν ∗ ρ) (s + u) x
      = ∫ z, heatDensityVec ν s z * heatDensityVec ρ u (x - z) := by
  refine (integral_conv_eq (integrable_heatKernelVec hs) (continuous_heatKernelVec s)
    (continuous_heatKernelVec u) (abs_heatKernelVec_le' hu) (continuous_heatKernelVec _)
    (integral_heatKernelVec_mul_heatKernelVec hs hu) x).trans ?_
  rfl

private theorem heatDensityVecDeriv_conv {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (i : Fin n)
    (x : Fin n → ℝ) :
    heatDensityVecDeriv (ν ∗ ρ) (s + u) i x
      = ∫ z, heatDensityVec ν s z * heatDensityVecDeriv ρ u i (x - z) := by
  have hb : Continuous fun v : Fin n → ℝ => -(v i / u) * heatKernelVec u v :=
    (by fun_prop : Continuous fun v : Fin n → ℝ => -(v i / u)).mul (continuous_heatKernelVec u)
  have hc : Continuous fun w : Fin n → ℝ => -(w i / (s + u)) * heatKernelVec (s + u) w :=
    (by fun_prop : Continuous fun w : Fin n → ℝ => -(w i / (s + u))).mul
      (continuous_heatKernelVec _)
  refine (integral_conv_eq (integrable_heatKernelVec hs) (continuous_heatKernelVec s) hb
    (abs_heatKernelVec_deriv_le' hu i) hc
    (fun w => integral_heatKernelVec_mul_deriv hs hu w i) x).trans ?_
  rfl

private theorem heatDensityVecDeriv_conv' {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (i : Fin n)
    (x : Fin n → ℝ) :
    heatDensityVecDeriv (ν ∗ ρ) (s + u) i x
      = ∫ z, heatDensityVecDeriv ν s i z * heatDensityVec ρ u (x - z) := by
  have ha : Continuous fun v : Fin n → ℝ => -(v i / s) * heatKernelVec s v :=
    (by fun_prop : Continuous fun v : Fin n → ℝ => -(v i / s)).mul (continuous_heatKernelVec s)
  have hc : Continuous fun w : Fin n → ℝ => -(w i / (s + u)) * heatKernelVec (s + u) w :=
    (by fun_prop : Continuous fun w : Fin n → ℝ => -(w i / (s + u))).mul
      (continuous_heatKernelVec _)
  have hai : Integrable fun v : Fin n → ℝ => -(v i / s) * heatKernelVec s v :=
    integrable_mul_heatKernelVec_volume hs (by fun_prop) (fun v => heatPolyVec_deriv hs le_rfl v i)
  refine (integral_conv_eq hai ha (continuous_heatKernelVec u) (abs_heatKernelVec_le' hu) hc
    (fun w => integral_heatKernelVec_deriv_mul hs hu w i) x).trans ?_
  rfl

private lemma abs_heatDensityVec_le {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] {s : ℝ}
    (hs : 0 < s) (x : Fin n → ℝ) :
    |heatDensityVec μ s x| ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ ^ n := by
  rw [abs_of_pos (heatDensityVec_pos hs x)]
  exact heatDensityVec_le hs x

private lemma abs_heatDensityVecDeriv_le {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (i : Fin n) (x : Fin n → ℝ) :
    |heatDensityVecDeriv μ s i x|
      ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ ^ n * ((n + 1) * (1 + 1 / s) ^ 2) * (1 + 2 * s) := by
  have h := abs_integral_mul_heatKernelVec_le (μ := μ) (c := fun u => -(u i / s)) hs le_rfl le_rfl
    (fun u => heatPolyVec_deriv hs le_rfl u i) x
  refine h.trans ?_
  calc ∫ y, heatEnvelopeVec s s (x - y) ∂μ
      ≤ ∫ _, (Real.sqrt (2 * Real.pi * s))⁻¹ ^ n * ((n + 1) * (1 + 1 / s) ^ 2) * (1 + 2 * s) ∂μ :=
        integral_mono (integrable_const _ |>.mono' ((continuous_heatEnvelopeVec s s).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable (ae_of_all _ fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (heatEnvelopeVec_nonneg _ _ _)]
            exact heatEnvelopeVec_le hs _)) (integrable_const _)
          fun y => heatEnvelopeVec_le hs _
    _ = _ := by simp

private lemma integrable_mul_comp_sub {a b : (Fin n → ℝ) → ℝ} (ha : Integrable a)
    (hbc : Continuous b) {C : ℝ} (hC : ∀ v, |b v| ≤ C) (x : Fin n → ℝ) :
    Integrable fun z => a z * b (x - z) :=
  ha.mul_bdd (hbc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)

private theorem integral_heatDensityVecDeriv {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {s : ℝ} (hs : 0 < s) (i : Fin n) :
    ∫ x, heatDensityVecDeriv μ s i x = 0 :=
  integral_eq_zero_of_hasDerivAt_update i (fun x r => hasDerivAt_heatDensityVec_update hs x i r)
    (integrable_heatDensityVec hμ2 hs) (integrable_heatDensityVecDeriv hμ2 hs i)

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

private lemma fisher_conv_coord_le (hν2 : Integrable (fun y => ∑ i, y i ^ 2) ν)
    (hρ2 : Integrable (fun y => ∑ i, y i ^ 2) ρ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (l : ℝ)
    (i : Fin n) :
    ∫ x, heatDensityVecDeriv (ν ∗ ρ) (s + u) i x ^ 2 / heatDensityVec (ν ∗ ρ) (s + u) x
      ≤ l ^ 2 * (∫ x, heatDensityVecDeriv ν s i x ^ 2 / heatDensityVec ν s x) +
        (1 - l) ^ 2 * (∫ x, heatDensityVecDeriv ρ u i x ^ 2 / heatDensityVec ρ u x) := by
  set P := heatDensityVec ν s
  set D := heatDensityVecDeriv ν s i
  set Q := heatDensityVec ρ u
  set E := heatDensityVecDeriv ρ u i
  have hP : ∀ z, 0 < P z := heatDensityVec_pos hs
  have hQ : ∀ z, 0 < Q z := heatDensityVec_pos hu
  have hPi : Integrable P := integrable_heatDensityVec hν2 hs
  have hDi : Integrable D := integrable_heatDensityVecDeriv hν2 hs i
  have hFi : Integrable fun z => D z ^ 2 / P z := integrable_heatFisherVec hν2 hs i
  have hQi : Integrable Q := integrable_heatDensityVec hρ2 hu
  have hEi : Integrable E := integrable_heatDensityVecDeriv hρ2 hu i
  have hGi : Integrable fun z => E z ^ 2 / Q z := integrable_heatFisherVec hρ2 hu i
  have hPc : Continuous P := continuous_heatDensityVec hs
  have hDc : Continuous D := continuous_heatDensityVecDeriv hs i
  have hFc : Continuous fun z => D z ^ 2 / P z := (hDc.pow 2).div hPc fun z => (hP z).ne'
  have hQc : Continuous Q := continuous_heatDensityVec hu
  have hEc : Continuous E := continuous_heatDensityVecDeriv hu i
  have hGc : Continuous fun z => E z ^ 2 / Q z := (hEc.pow 2).div hQc fun z => (hQ z).ne'
  have hE0 : ∫ v, E v = 0 := integral_heatDensityVecDeriv hρ2 hu i
  have hQ1 : ∫ v, Q v = 1 := integral_heatDensityVec hu
  set H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => l ^ 2 * (D p.2 ^ 2 / P p.2 * Q (p.1 - p.2)) +
    2 * l * (1 - l) * (D p.2 * E (p.1 - p.2)) +
    (1 - l) ^ 2 * (P p.2 * (E (p.1 - p.2) ^ 2 / Q (p.1 - p.2)))
  have hH : Integrable H (volume.prod volume) :=
    ((((integrable_prod_comp_sub hFi hFc hQi hQc).const_mul (l ^ 2)).add
      ((integrable_prod_comp_sub hDi hDc hEi hEc).const_mul (2 * l * (1 - l)))).add
      ((integrable_prod_comp_sub hPi hPc hGi hGc).const_mul ((1 - l) ^ 2)))
  have hpt : ∀ᵐ x, heatDensityVecDeriv (ν ∗ ρ) (s + u) i x ^ 2 /
      heatDensityVec (ν ∗ ρ) (s + u) x ≤ ∫ z, H (x, z) := by
    filter_upwards [hH.prod_right_ae] with x hHx
    set w : (Fin n → ℝ) → ℝ := fun z => P z * Q (x - z)
    set g : (Fin n → ℝ) → ℝ := fun z => l * (D z / P z) + (1 - l) * (E (x - z) / Q (x - z))
    have hw0 : ∀ z, 0 ≤ w z := fun z => mul_nonneg (hP z).le (hQ _).le
    have hwi : Integrable w := integrable_mul_comp_sub hPi hQc (abs_heatDensityVec_le hu) x
    have hi1 : Integrable fun z => D z * Q (x - z) :=
      integrable_mul_comp_sub hDi hQc (abs_heatDensityVec_le hu) x
    have hi2 : Integrable fun z => P z * E (x - z) :=
      integrable_mul_comp_sub hPi hEc (abs_heatDensityVecDeriv_le hu i) x
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
    have hW : ∫ z, w z = heatDensityVec (ν ∗ ρ) (s + u) x := (heatDensityVec_conv hs hu x).symm
    have hA : ∫ z, w z * g z = heatDensityVecDeriv (ν ∗ ρ) (s + u) i x := by
      rw [hwg, integral_add (hi1.const_mul l) (hi2.const_mul (1 - l)), integral_const_mul,
        integral_const_mul, ← heatDensityVecDeriv_conv' hs hu i x,
        ← heatDensityVecDeriv_conv hs hu i x]
      ring
    rw [hW, hA, hwg2] at hcs
    rw [div_le_iff₀ (heatDensityVec_pos (by positivity) x)]
    linarith
  have hS2 := integrable_sum_sq_conv hν2 hρ2
  have hmono := integral_mono_ae (integrable_heatFisherVec hS2 (by positivity) i)
    hH.integral_prod_left hpt
  have hswap : ∫ x, ∫ z, H (x, z) = ∫ z, ∫ x, H (x, z) :=
    integral_integral_swap (f := fun x z => H (x, z)) hH
  have hinner : ∀ z, ∫ x, H (x, z)
      = l ^ 2 * (D z ^ 2 / P z) + (1 - l) ^ 2 * (∫ v, E v ^ 2 / Q v) * P z := by
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
    ring
  simp_rw [hinner] at hswap
  rw [integral_add (hFi.const_mul _) (hPi.const_mul _), integral_const_mul, integral_const_mul,
    integral_heatDensityVec hs] at hswap
  calc ∫ x, heatDensityVecDeriv (ν ∗ ρ) (s + u) i x ^ 2 / heatDensityVec (ν ∗ ρ) (s + u) x
      ≤ ∫ x, ∫ z, H (x, z) := hmono
    _ = _ := by rw [hswap]; ring

theorem heatFisherVec_conv_le (hν2 : Integrable (fun y => ∑ i, y i ^ 2) ν)
    (hρ2 : Integrable (fun y => ∑ i, y i ^ 2) ρ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (l : ℝ) :
    heatFisherVec (ν ∗ ρ) (s + u)
      ≤ l ^ 2 * heatFisherVec ν s + (1 - l) ^ 2 * heatFisherVec ρ u := by
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    fisher_conv_coord_le hν2 hρ2 hs hu l i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  exact h

end Meat
