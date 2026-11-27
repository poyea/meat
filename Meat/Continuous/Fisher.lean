import Meat.Continuous.DeBruijn

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Meat

noncomputable def fisherInfo (f : ℝ → ℝ) : ℝ :=
  ∫ x, deriv f x ^ 2 / f x

theorem hasDerivAt_gaussianPDFReal (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v) (-(x - m) / v * gaussianPDFReal m v x) x := by
  have h : HasDerivAt (fun y : ℝ => -(y - m) ^ 2 / (2 * v)) (-(2 * (x - m)) / (2 * v)) x := by
    have := ((hasDerivAt_id x).sub_const m).pow 2
    simpa using (this.neg).div_const (2 * (v : ℝ))
  have h2 := (h.exp).const_mul (√(2 * Real.pi * v))⁻¹
  rw [gaussianPDFReal_def]
  convert h2 using 1
  ring

theorem fisherInfo_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfo (gaussianPDFReal m v) = 1 / v := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have hsq : ∫ x, (x - m) ^ 2 ∂gaussianReal m v = v := by
    have := variance_fun_id_gaussianReal (μ := m) (v := v)
    rwa [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at this
  rw [integral_gaussianReal_eq_integral_smul hv] at hsq
  have hpt : ∀ x, deriv (gaussianPDFReal m v) x ^ 2 / gaussianPDFReal m v x
      = (1 / (v : ℝ) ^ 2) * (gaussianPDFReal m v x • (x - m) ^ 2) := by
    intro x
    have hp := gaussianPDFReal_pos m v x hv
    rw [(hasDerivAt_gaussianPDFReal m v x).deriv, smul_eq_mul]
    field_simp
  rw [fisherInfo, funext hpt, integral_const_mul, hsq]
  field_simp

theorem one_le_integral_sq_mul_fisherInfo {f : ℝ → ℝ} (m : ℝ) (hd : Differentiable ℝ f)
    (hnn : ∀ x, 0 ≤ f x) (h1 : ∫ x, f x = 1) (hfi : Integrable f)
    (hd1 : Integrable fun x => (x - m) * deriv f x)
    (hV : Integrable fun x => (x - m) ^ 2 * f x) (hJ : Integrable fun x => deriv f x ^ 2 / f x)
    (hbot : Tendsto (fun x => (x - m) * f x) atBot (𝓝 0))
    (htop : Tendsto (fun x => (x - m) * f x) atTop (𝓝 0)) :
    1 ≤ (∫ x, (x - m) ^ 2 * f x) * fisherInfo f := by
  have hibp : ∫ x, (f x + (x - m) * deriv f x) = 0 := by
    rw [integral_of_hasDerivAt_of_tendsto (f := fun x => (x - m) * f x)
      (f' := fun x => f x + (x - m) * deriv f x)
      (fun x => by
        convert ((hasDerivAt_id' x).sub_const m).mul (hd x).hasDerivAt using 1
        ring)
      (hfi.add hd1) hbot htop, sub_self]
  rw [integral_add hfi hd1, h1] at hibp
  set V := ∫ x, (x - m) ^ 2 * f x
  set J := fisherInfo f
  have hquad : ∀ a : ℝ, 0 ≤ a ^ 2 * V - 2 * a + J := by
    intro a
    have hpt : ∀ x, 0 ≤ a ^ 2 * ((x - m) ^ 2 * f x) + 2 * a * ((x - m) * deriv f x)
        + deriv f x ^ 2 / f x := by
      intro x
      rcases (hnn x).eq_or_lt with h0 | hp
      · have hmin : IsLocalMin f x := Filter.Eventually.of_forall fun y => h0 ▸ hnn y
        rw [hmin.deriv_eq_zero, ← h0]
        simp
      · have e : deriv f x ^ 2 / f x = (deriv f x / f x) ^ 2 * f x := by
          field_simp
        have e2 : (x - m) * deriv f x = (x - m) * (deriv f x / f x) * f x := by
          field_simp
        rw [e, e2]
        nlinarith [mul_nonneg hp.le (sq_nonneg (a * (x - m) + deriv f x / f x))]
    have hint : 0 ≤ ∫ x, (a ^ 2 * ((x - m) ^ 2 * f x) + 2 * a * ((x - m) * deriv f x)
        + deriv f x ^ 2 / f x) := integral_nonneg fun x => hpt x
    have i1 : Integrable fun x => a ^ 2 * ((x - m) ^ 2 * f x) + 2 * a * ((x - m) * deriv f x) :=
      (hV.const_mul _).add (hd1.const_mul _)
    rw [integral_add i1 hJ, integral_add (hV.const_mul (a ^ 2)) (hd1.const_mul (2 * a)),
      integral_const_mul, integral_const_mul] at hint
    have hm : ∫ x, (x - m) * deriv f x = -1 := by linarith
    rw [hm] at hint
    exact le_of_le_of_eq hint (by simp only [J, fisherInfo]; ring)
  have hV0 : 0 ≤ V := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hnn x)
  rcases hV0.eq_or_lt with h0 | hp
  · have := hquad (J / 2 + 1)
    rw [← h0] at this
    linarith
  · have := hquad (1 / V)
    have e : (1 / V) ^ 2 * V = 1 / V := by field_simp
    rw [e] at this
    have : 1 / V ≤ J := by linarith
    rwa [div_le_iff₀ hp, mul_comm] at this

theorem fisherInfo_heatDensity {ν : Measure ℝ} [IsProbabilityMeasure ν] {s : ℝ} (hs : 0 < s) :
    fisherInfo (heatDensity ν s) = heatFisher ν s := by
  unfold fisherInfo heatFisher
  simp_rw [(hasDerivAt_heatDensity (ν := ν) hs _).deriv]

end Meat
