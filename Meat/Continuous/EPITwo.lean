import Meat.Continuous.EPI
import Meat.Continuous.StamTwo

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

private lemma integral_sq_gaussianReal (v : ℝ≥0) : ∫ y, y ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simp only [id, integral_id_gaussianReal, sub_zero] at h
  exact h

private lemma integrable_sq_of_memLp {μ : Measure ℝ} (h : MemLp id 2 μ) :
    Integrable (fun y => y ^ 2) μ := by
  simpa using h.integrable_sq

private lemma log_mul_add_mul {c A k τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) (hk : 0 < A / τ + k) :
    Real.log (c * (A + k * τ)) = Real.log c + Real.log τ + Real.log (A / τ + k) := by
  rw [show c * (A + k * τ) = c * τ * (A / τ + k) by field_simp,
    Real.log_mul (by positivity) hk.ne', Real.log_mul hc.ne' hτ.ne']

variable {ν ρ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

private lemma heatEntropy_le (hν2 : Integrable (fun y => y ^ 2) ν) {s : ℝ} (hs : 0 < s) :
    ∫ x, Real.negMulLog (heatDensity ν s x)
      ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (∫ y, y ^ 2 ∂ν + s)) := by
  have hG2 := integrable_sq_of_memLp
    (memLp_id_gaussianReal' (μ := 0) (v := s.toNNReal) 2 (by simp))
  obtain ⟨hi, he⟩ := integrable_sq_conv hν2 hG2
  have hac : ν ∗ gaussianReal 0 s.toNNReal ≪ volume := by
    rw [Measure.conv_comm, gaussianReal_conv_eq_withDensity hs]
    exact withDensity_absolutelyContinuous _ _
  have hM : 0 ≤ ∫ y, y ^ 2 ∂ν := integral_nonneg fun y => sq_nonneg y
  rw [← measureDiffEntropy_conv_gaussianReal hs]
  refine measureDiffEntropy_le_of_integral_sq_le hac
    (integrable_negMulLog_conv_gaussianReal hν2 hs) 0 (by positivity) (by simpa using hi) ?_
  simp only [sub_zero]
  rw [he, integral_id_gaussianReal, integral_sq_gaussianReal, Real.coe_toNNReal _ hs.le]
  simp

private lemma heatEntropy_conv_ge (hν2 : Integrable (fun y => y ^ 2) ν)
    (hρ2 : Integrable (fun y => y ^ 2) ρ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) {l : ℝ}
    (hl0 : 0 < l) (hl1 : l < 1) :
    l * (∫ x, Real.negMulLog (heatDensity ν s x)) +
        (1 - l) * (∫ x, Real.negMulLog (heatDensity ρ u x)) +
        (1 / 2) * (Real.negMulLog l + Real.negMulLog (1 - l))
      ≤ ∫ x, Real.negMulLog (heatDensity (ν ∗ ρ) (s + u) x) := by
  set H : Measure ℝ → ℝ → ℝ := fun μ t => ∫ x, Real.negMulLog (heatDensity μ t x) with hH
  have hZ2 := (integrable_sq_conv hν2 hρ2).1
  have hl1' : 0 < 1 - l := by linarith
  set D : ℝ → ℝ := fun τ =>
    H (ν ∗ ρ) (s + u + τ) - l * H ν (s + l * τ) - (1 - l) * H ρ (u + (1 - l) * τ)
  have hDd : ∀ τ, 0 ≤ τ → HasDerivAt D (heatFisher (ν ∗ ρ) (s + u + τ) / 2 -
      l ^ 2 * (heatFisher ν (s + l * τ) / 2) -
      (1 - l) ^ 2 * (heatFisher ρ (u + (1 - l) * τ) / 2)) τ := by
    intro τ hτ
    have h1 := (hasDerivAt_heatEntropy hZ2 (by positivity : 0 < s + u + τ)).comp τ
      ((hasDerivAt_id' τ).const_add (s + u))
    have h2 := (hasDerivAt_heatEntropy hν2 (by positivity : 0 < s + l * τ)).comp τ
      (((hasDerivAt_id' τ).const_mul l).const_add s)
    have h3 := (hasDerivAt_heatEntropy hρ2 (by positivity : 0 < u + (1 - l) * τ)).comp τ
      (((hasDerivAt_id' τ).const_mul (1 - l)).const_add u)
    convert (h1.sub (h2.const_mul l)).sub (h3.const_mul (1 - l)) using 1
    · rfl
    · ring
  have hanti : AntitoneOn D (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun τ hτ => (hDd τ hτ).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ici]
      exact fun τ hτ => (hDd τ (le_of_lt hτ)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro τ hτ
      have hτ' : 0 < τ := hτ
      rw [(hDd τ hτ'.le).deriv]
      have hst := heatFisher_conv_le hν2 hρ2 (by positivity : 0 < s + l * τ)
        (by positivity : 0 < u + (1 - l) * τ) l
      rw [show s + l * τ + (u + (1 - l) * τ) = s + u + τ by ring] at hst
      linarith
  set Mν := ∫ y, y ^ 2 ∂ν
  set Mρ := ∫ y, y ^ 2 ∂ρ
  have hMν : 0 ≤ Mν := integral_nonneg fun y => sq_nonneg y
  have hMρ : 0 ≤ Mρ := integral_nonneg fun y => sq_nonneg y
  set c := 2 * Real.pi * Real.exp 1
  have hc : 0 < c := by positivity
  set L : ℝ → ℝ := fun τ => (1 / 2) * (Real.log ((s + u) / τ + 1) -
    l * Real.log ((Mν + s) / τ + l) - (1 - l) * Real.log ((Mρ + u) / τ + (1 - l)))
  have hlow : ∀ τ, 0 < τ → L τ ≤ D τ := by
    intro τ hτ
    have g1 := heatEntropy_ge hZ2 (by positivity : 0 < s + u + τ)
    have g2 := heatEntropy_le hν2 (by positivity : 0 < s + l * τ)
    have g3 := heatEntropy_le hρ2 (by positivity : 0 < u + (1 - l) * τ)
    have e1 : Real.log (c * (s + u + τ)) = Real.log c + Real.log τ + Real.log ((s + u) / τ + 1) :=
      by rw [← log_mul_add_mul hc hτ (by positivity)]; ring_nf
    have e2 : Real.log (c * (Mν + (s + l * τ))) =
        Real.log c + Real.log τ + Real.log ((Mν + s) / τ + l) :=
      by rw [← log_mul_add_mul hc hτ (by positivity)]; ring_nf
    have e3 : Real.log (c * (Mρ + (u + (1 - l) * τ))) =
        Real.log c + Real.log τ + Real.log ((Mρ + u) / τ + (1 - l)) :=
      by rw [← log_mul_add_mul hc hτ (by positivity)]; ring_nf
    rw [e1] at g1
    rw [e2] at g2
    rw [e3] at g3
    simp only [L, D, H]
    nlinarith [mul_le_mul_of_nonneg_left g2 hl0.le, mul_le_mul_of_nonneg_left g3 hl1'.le]
  have hlim : Tendsto L atTop (𝓝 ((1 / 2) * (Real.negMulLog l + Real.negMulLog (1 - l)))) := by
    have t : ∀ A k : ℝ, k ≠ 0 →
        Tendsto (fun τ : ℝ => Real.log (A / τ + k)) atTop (𝓝 (Real.log k)) := by
      intro A k hk
      have := ((tendsto_const_nhds (x := A)).div_atTop tendsto_id).add
        (tendsto_const_nhds (x := k))
      rw [zero_add] at this
      exact this.log hk
    have := (((t (s + u) 1 one_ne_zero).sub ((t (Mν + s) l hl0.ne').const_mul l)).sub
      ((t (Mρ + u) (1 - l) hl1'.ne').const_mul (1 - l))).const_mul (1 / 2)
    convert this using 2
    simp only [Real.negMulLog, Real.log_one]
    ring
  have hD0 : ∀ τ, 0 < τ → L τ ≤ D 0 := fun τ hτ =>
    (hlow τ hτ).trans (hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hτ.le) hτ.le)
  have := le_of_tendsto hlim ((eventually_gt_atTop 0).mono hD0)
  simp only [D, add_zero, mul_zero] at this
  linarith

theorem heatEntropyPowerInequality (hν2 : Integrable (fun y => y ^ 2) ν)
    (hρ2 : Integrable (fun y => y ^ 2) ρ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    Real.exp (2 * ∫ x, Real.negMulLog (heatDensity ν s x)) +
        Real.exp (2 * ∫ x, Real.negMulLog (heatDensity ρ u x))
      ≤ Real.exp (2 * ∫ x, Real.negMulLog (heatDensity (ν ∗ ρ) (s + u) x)) := by
  set X := ∫ x, Real.negMulLog (heatDensity ν s x)
  set Y := ∫ x, Real.negMulLog (heatDensity ρ u x)
  set Z := ∫ x, Real.negMulLog (heatDensity (ν ∗ ρ) (s + u) x)
  set a := Real.exp (2 * X)
  set b := Real.exp (2 * Y)
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hab : 0 < a + b := by positivity
  have hl := heatEntropy_conv_ge hν2 hρ2 hs hu (l := a / (a + b)) (div_pos ha hab)
    ((div_lt_one hab).2 (by linarith))
  have h1l : 1 - a / (a + b) = b / (a + b) := by field_simp; ring
  have hla : Real.log (a / (a + b)) = 2 * X - Real.log (a + b) := by
    rw [Real.log_div ha.ne' hab.ne']
    exact congrArg (· - Real.log (a + b)) (Real.log_exp (2 * X))
  have hlb : Real.log (b / (a + b)) = 2 * Y - Real.log (a + b) := by
    rw [Real.log_div hb.ne' hab.ne']
    exact congrArg (· - Real.log (a + b)) (Real.log_exp (2 * Y))
  rw [h1l] at hl
  have hna : Real.negMulLog (a / (a + b)) = -(a / (a + b)) * (2 * X - Real.log (a + b)) := by
    simp only [Real.negMulLog, hla]
  have hnb : Real.negMulLog (b / (a + b)) = -(b / (a + b)) * (2 * Y - Real.log (a + b)) := by
    simp only [Real.negMulLog, hlb]
  rw [hna, hnb] at hl
  have e : a / (a + b) * X + b / (a + b) * Y + 1 / 2 * (-(a / (a + b)) * (2 * X - Real.log (a + b))
      + -(b / (a + b)) * (2 * Y - Real.log (a + b))) = 1 / 2 * Real.log (a + b) := by
    field_simp
    ring
  rw [e] at hl
  calc a + b = Real.exp (Real.log (a + b)) := (Real.exp_log hab).symm
    _ ≤ Real.exp (2 * Z) := Real.exp_le_exp.2 (by linarith)

theorem entropyPowerInequality_conv_gaussianReal (hν : ν ≪ volume) (h2 : MemLp id 2 ν)
    (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal))
    (hρ : MemLp id 2 ρ) {v : ℝ≥0} (hv : v ≠ 0) :
    Real.exp (2 * measureDiffEntropy ν) + Real.exp (2 * measureDiffEntropy (ρ ∗ gaussianReal 0 v))
      ≤ Real.exp (2 * measureDiffEntropy (ν ∗ (ρ ∗ gaussianReal 0 v))) := by
  have hν2 := integrable_sq_of_memLp h2
  have hρ2 := integrable_sq_of_memLp hρ
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  set H : Measure ℝ → ℝ → ℝ := fun μ t => ∫ x, Real.negMulLog (heatDensity μ t x) with hH
  have hρv : measureDiffEntropy (ρ ∗ gaussianReal 0 v) = H ρ v := by
    have := measureDiffEntropy_conv_gaussianReal (ν := ρ) hv'
    rwa [Real.toNNReal_coe] at this
  have hZv : measureDiffEntropy (ν ∗ (ρ ∗ gaussianReal 0 v)) = H (ν ∗ ρ) v := by
    have := measureDiffEntropy_conv_gaussianReal (ν := ν ∗ ρ) hv'
    rwa [Real.toNNReal_coe, Measure.conv_assoc] at this
  rw [hρv, hZv]
  set C := Real.exp (2 * measureDiffEntropy ν)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C + Real.exp (2 * H ρ (v - ε)) ≤ Real.exp (2 * H (ν ∗ ρ) v) := by
    filter_upwards [Ioo_mem_nhdsGT hv'] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεv : 0 < (v : ℝ) - ε := sub_pos.2 hε.2
    have h1 : Real.exp (2 * H ν ε) + Real.exp (2 * H ρ (v - ε))
        ≤ Real.exp (2 * H (ν ∗ ρ) v) := by
      have := heatEntropyPowerInequality hν2 hρ2 hε0 hεv
      rwa [add_sub_cancel] at this
    have h2 : measureDiffEntropy ν ≤ H ν ε := by
      change _ ≤ ∫ x, Real.negMulLog (heatDensity ν ε x)
      rw [← measureDiffEntropy_conv_gaussianReal hε0]
      exact measureDiffEntropy_le_conv hν hf (integrable_negMulLog_conv_gaussianReal hν2 hε0)
    have h3 : C ≤ Real.exp (2 * H ν ε) := Real.exp_le_exp.2 (by linarith)
    exact (add_le_add h3 le_rfl).trans h1
  have hc : ContinuousAt (fun ε : ℝ => C + Real.exp (2 * H ρ (v - ε))) 0 := by
    have h := (hasDerivAt_heatEntropy hρ2 hv').continuousAt
    have hg : ContinuousAt (fun ε : ℝ => (v : ℝ) - ε) 0 := by fun_prop
    have hcomp := ContinuousAt.comp_of_eq h hg (by simp)
    exact continuousAt_const.add
      (Real.continuous_exp.continuousAt.comp (hcomp.const_mul 2))
  have := le_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds) hev
  simpa using this

theorem entropyPowerInequality_conv_conv_gaussianReal (hν : ν ≪ volume) (h2 : MemLp id 2 ν)
    (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal))
    (hρ : ρ ≪ volume) (hρ2 : MemLp id 2 ρ)
    (hg : Integrable (fun x => Real.negMulLog (ρ.rnDeriv volume x).toReal))
    {v : ℝ≥0} (hv : v ≠ 0) :
    Real.exp (2 * measureDiffEntropy ν) + Real.exp (2 * measureDiffEntropy ρ)
      ≤ Real.exp (2 * measureDiffEntropy (ν ∗ ρ ∗ gaussianReal 0 v)) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have hi := integrable_negMulLog_conv_gaussianReal (integrable_sq_of_memLp hρ2) hv'
  rw [Real.toNNReal_coe] at hi
  have h1 := measureDiffEntropy_le_conv hρ hg hi
  exact (add_le_add le_rfl (Real.exp_le_exp.2 (by linarith : 2 * measureDiffEntropy ρ
    ≤ 2 * measureDiffEntropy (ρ ∗ gaussianReal 0 v)))).trans
    (entropyPowerInequality_conv_gaussianReal hν h2 hf hρ2 hv)

end Meat
