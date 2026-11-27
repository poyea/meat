import Meat.Continuous.MaxEntropy
import Meat.Continuous.Stam

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Meat

noncomputable def entropyPower (ν : Measure ℝ) : ℝ :=
  Real.exp (2 * measureDiffEntropy ν) / (2 * Real.pi * Real.exp 1)

theorem entropyPower_pos (ν : Measure ℝ) : 0 < entropyPower ν := by
  unfold entropyPower
  positivity

theorem exp_two_mul_measureDiffEntropy (ν : Measure ℝ) :
    Real.exp (2 * measureDiffEntropy ν) = 2 * Real.pi * Real.exp 1 * entropyPower ν := by
  unfold entropyPower
  field_simp

theorem entropyPower_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    entropyPower (gaussianReal m v) = v := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  rw [entropyPower, measureDiffEntropy_gaussianReal m v hv, ← mul_assoc,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul, Real.exp_log (by positivity)]
  field_simp

theorem entropyPower_le_variance {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal))
    (hX : MemLp id 2 ν) : entropyPower ν ≤ Var[id; ν] := by
  have h := measureDiffEntropy_le_of_variance hν hf hX
  have hv := variance_pos_of_absolutelyContinuous hν hX
  have hc : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  unfold entropyPower
  rw [div_le_iff₀ hc]
  calc Real.exp (2 * measureDiffEntropy ν)
      ≤ Real.exp (Real.log (2 * Real.pi * Real.exp 1 * Var[id; ν])) :=
        Real.exp_le_exp.2 (by linarith)
    _ = Var[id; ν] * (2 * Real.pi * Real.exp 1) := by
        rw [Real.exp_log (by positivity)]
        ring

theorem entropyPower_gaussianReal_conv (m₁ m₂ : ℝ) {v₁ v₂ : ℝ≥0} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) :
    entropyPower (gaussianReal m₁ v₁ ∗ gaussianReal m₂ v₂)
      = entropyPower (gaussianReal m₁ v₁) + entropyPower (gaussianReal m₂ v₂) := by
  rw [gaussianReal_conv_gaussianReal, entropyPower_gaussianReal _ h₁,
    entropyPower_gaussianReal _ h₂, entropyPower_gaussianReal _ (by simp [h₁]), NNReal.coe_add]

private lemma conv_eq_withDensity {ν ρ : Measure ℝ} [IsFiniteMeasure ν] [SFinite ρ]
    (hν : ν ≪ volume) :
    ν ∗ ρ = volume.withDensity (fun x => ∫⁻ y, ν.rnDeriv volume (x - y) ∂ρ) := by
  have hF := Measure.measurable_rnDeriv ν volume
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hG : Measurable fun x => ∫⁻ y, ν.rnDeriv volume (x - y) ∂ρ :=
    (hF.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'
  rw [Measure.conv_comm, Measure.lintegral_conv hφ,
 lintegral_withDensity_eq_lintegral_mul _ hG hφ]
  have h1 : ∀ y, ∫⁻ x, φ (y + x) ∂ν = ∫⁻ x, ν.rnDeriv volume (x - y) * φ x := by
    intro y
    have hy : Measurable fun x => φ (y + x) := hφ.comp (measurable_const_add y)
    rw [← lintegral_rnDeriv_mul hν hy.aemeasurable,
      ← lintegral_sub_right_eq_self _ y]
    simp
  simp_rw [h1]
  rw [lintegral_lintegral_swap ((hF.comp (measurable_snd.sub measurable_fst)).mul
    (hφ.comp measurable_snd)).aemeasurable]
  refine lintegral_congr fun x => ?_
  have hx : Measurable fun y => ν.rnDeriv volume (x - y) :=
    hF.comp (measurable_const.sub measurable_id)
  rw [Pi.mul_apply, lintegral_mul_const _ hx]

private lemma integrable_comp_sub {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {φ : ℝ → ℝ}
    (hm : Measurable φ) (hi : Integrable φ) :
    Integrable (fun p : ℝ × ℝ => φ (p.1 - p.2)) (volume.prod ρ) := by
  have hs : Measurable fun p : ℝ × ℝ => φ (p.1 - p.2) := hm.comp (measurable_fst.sub measurable_snd)
  refine (integrable_prod_iff' hs.aestronglyMeasurable).2
    ⟨ae_of_all _ fun y => hi.comp_sub_right y, ?_⟩
  refine (integrable_const (∫ x, ‖φ x‖)).congr (ae_of_all _ fun y => ?_)
  exact (integral_sub_right_eq_self (‖φ ·‖) y).symm

theorem measureDiffEntropy_le_conv {ν ρ : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] (hν : ν ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal))
    (hg : Integrable (fun x => Real.negMulLog ((ν ∗ ρ).rnDeriv volume x).toReal)) :
    measureDiffEntropy ν ≤ measureDiffEntropy (ν ∗ ρ) := by
  set F := ν.rnDeriv volume
  have hF : Measurable F := Measure.measurable_rnDeriv ν volume
  set G : ℝ → ℝ≥0∞ := fun x => ∫⁻ y, F (x - y) ∂ρ
  have hGm : Measurable G := (hF.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'
  have hconv := conv_eq_withDensity (ρ := ρ) hν
  have hGfin : ∀ᵐ x, G x < ∞ := by
    refine ae_lt_top hGm ?_
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hconv]
    exact measure_ne_top _ _
  have hrn : (ν ∗ ρ).rnDeriv volume =ᵐ[volume] G := by
    rw [hconv]
    exact Measure.rnDeriv_withDensity volume hGm
  have hfm : Measurable fun x => (F x).toReal := hF.ennreal_toReal
  have hHm : Measurable fun x => Real.negMulLog (F x).toReal :=
    Real.continuous_negMulLog.measurable.comp hfm
  have hH := integrable_comp_sub (ρ := ρ) hHm hf
  have hfi := integrable_comp_sub (ρ := ρ) hfm Measure.integrable_toReal_rnDeriv
  have hpt : ∀ᵐ x, ∫ y, Real.negMulLog (F (x - y)).toReal ∂ρ
      ≤ Real.negMulLog ((ν ∗ ρ).rnDeriv volume x).toReal := by
    filter_upwards [hrn, hGfin, hH.prod_right_ae, hfi.prod_right_ae] with x h1 h2 h3 h4
    have hx : Measurable fun y => F (x - y) := hF.comp (measurable_const.sub measurable_id)
    have hfin : ∀ᵐ y ∂ρ, F (x - y) < ∞ := ae_lt_top' hx.aemeasurable h2.ne
    rw [h1, show G x = ∫⁻ y, F (x - y) ∂ρ from rfl, ← integral_toReal hx.aemeasurable hfin]
    exact Real.concaveOn_negMulLog.le_map_integral Real.continuous_negMulLog.continuousOn
      isClosed_Ici (ae_of_all _ fun y => ENNReal.toReal_nonneg) h4 h3
  calc measureDiffEntropy ν = ∫ y, ∫ x, Real.negMulLog (F (x - y)).toReal ∂volume ∂ρ := by
        have e : ∀ y, ∫ x, Real.negMulLog (F (x - y)).toReal = ∫ x, Real.negMulLog (F x).toReal :=
          fun y => integral_sub_right_eq_self (fun x => Real.negMulLog (F x).toReal) y
        simp_rw [e]
        rw [integral_const, probReal_univ, one_smul, measureDiffEntropy]
    _ = ∫ x, ∫ y, Real.negMulLog (F (x - y)).toReal ∂ρ := (integral_integral_swap hH).symm
    _ ≤ measureDiffEntropy (ν ∗ ρ) := integral_mono_ae hH.integral_prod_left hg hpt

theorem diffEntropy_le_diffEntropy_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : IndepFun X Y μ) (hν : μ.map X ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog ((μ.map X).rnDeriv volume x).toReal))
    (hg : Integrable (fun x => Real.negMulLog ((μ.map (X + Y)).rnDeriv volume x).toReal)) :
    diffEntropy X μ ≤ diffEntropy (X + Y) μ := by
  rw [hXY.map_add_eq_map_conv_map₀ hX hY] at hg
  rw [diffEntropy, diffEntropy, hXY.map_add_eq_map_conv_map₀ hX hY]
  exact measureDiffEntropy_le_conv hν hf hg

theorem max_entropyPower_le_conv {ν ρ : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] (hν : ν ≪ volume) (hρ : ρ ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal))
    (hf' : Integrable (fun x => Real.negMulLog (ρ.rnDeriv volume x).toReal))
    (hg : Integrable (fun x => Real.negMulLog ((ν ∗ ρ).rnDeriv volume x).toReal)) :
    max (entropyPower ν) (entropyPower ρ) ≤ entropyPower (ν ∗ ρ) := by
  have h1 := measureDiffEntropy_le_conv (ρ := ρ) hν hf hg
  have h2 := measureDiffEntropy_le_conv (ρ := ν) hρ hf' (by rwa [Measure.conv_comm])
  rw [Measure.conv_comm] at h2
  unfold entropyPower
  refine max_le ?_ ?_ <;> gcongr

theorem entropyPower_add_le_two_mul_conv {ν ρ : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] (hν : ν ≪ volume) (hρ : ρ ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal))
    (hf' : Integrable (fun x => Real.negMulLog (ρ.rnDeriv volume x).toReal))
    (hg : Integrable (fun x => Real.negMulLog ((ν ∗ ρ).rnDeriv volume x).toReal)) :
    entropyPower ν + entropyPower ρ ≤ 2 * entropyPower (ν ∗ ρ) := by
  have h := max_entropyPower_le_conv hν hρ hf hf' hg
  linarith [le_max_left (entropyPower ν) (entropyPower ρ),
    le_max_right (entropyPower ν) (entropyPower ρ)]

private lemma integrable_negMulLog_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => Real.negMulLog ((gaussianReal m v).rnDeriv volume x).toReal) := by
  have hG := gaussianReal_absolutelyContinuous m hv
  have hG2 : MemLp id 2 (gaussianReal m v) := memLp_id_gaussianReal' 2 (by simp)
  exact (integrable_negMulLog_rnDeriv_iff hG).2 (integrable_log_rnDeriv_gaussianReal hG m hv
    ((hG2.sub (memLp_const m)).integrable_sq))

def EntropyPowerInequality : Prop :=
  ∀ (ν ρ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ],
    ν ≪ volume → ρ ≪ volume → MemLp id 2 ν → MemLp id 2 ρ →
    Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal) →
    Integrable (fun x => Real.negMulLog (ρ.rnDeriv volume x).toReal) →
    Integrable (fun x => Real.negMulLog ((ν ∗ ρ).rnDeriv volume x).toReal) →
    Real.exp (2 * measureDiffEntropy ν) + Real.exp (2 * measureDiffEntropy ρ)
      ≤ Real.exp (2 * measureDiffEntropy (ν ∗ ρ))

theorem entropyPowerInequality_iff_entropyPower :
    EntropyPowerInequality ↔
      ∀ (ν ρ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ],
        ν ≪ volume → ρ ≪ volume → MemLp id 2 ν → MemLp id 2 ρ →
        Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal) →
        Integrable (fun x => Real.negMulLog (ρ.rnDeriv volume x).toReal) →
        Integrable (fun x => Real.negMulLog ((ν ∗ ρ).rnDeriv volume x).toReal) →
        entropyPower ν + entropyPower ρ ≤ entropyPower (ν ∗ ρ) := by
  have hc : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  simp only [EntropyPowerInequality, exp_two_mul_measureDiffEntropy, ← mul_add,
    mul_le_mul_iff_right₀ hc]

def GaussianEntropyPowerInequality : Prop :=
  ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : ℝ≥0), v ≠ 0 →
    ν ≪ volume → MemLp id 2 ν →
    Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal) →
    Real.exp (2 * measureDiffEntropy ν) + 2 * Real.pi * Real.exp 1 * v
      ≤ Real.exp (2 * measureDiffEntropy (ν ∗ gaussianReal 0 v))

section HeatFlow

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

theorem integrable_negMulLog_conv_gaussianReal (hν2 : Integrable (fun y => y ^ 2) ν) {s : ℝ}
    (hs : 0 < s) : Integrable (fun x =>
      Real.negMulLog ((ν ∗ gaussianReal 0 s.toNNReal).rnDeriv volume x).toReal) := by
  rw [Measure.conv_comm, gaussianReal_conv_eq_withDensity hs]
  refine (integrable_negMulLog_heatDensity hν2 hs).congr ?_
  filter_upwards [Measure.rnDeriv_withDensity volume
    (continuous_heatDensity (ν := ν) hs).measurable.ennreal_ofReal] with x hx
  rw [hx, ENNReal.toReal_ofReal (heatDensity_pos hs x).le]

theorem heatEntropy_ge (hν2 : Integrable (fun y => y ^ 2) ν) {s : ℝ} (hs : 0 < s) :
    (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * s)
      ≤ ∫ x, Real.negMulLog (heatDensity ν s x) := by
  have hv : s.toNNReal ≠ 0 := by simp [hs]
  have h := measureDiffEntropy_le_conv (ν := gaussianReal 0 s.toNNReal) (ρ := ν)
    (gaussianReal_absolutelyContinuous 0 hv) (integrable_negMulLog_gaussianReal 0 hv)
    (by rw [Measure.conv_comm]; exact integrable_negMulLog_conv_gaussianReal hν2 hs)
  rwa [measureDiffEntropy_gaussianReal 0 _ hv, Real.coe_toNNReal _ hs.le, Measure.conv_comm,
    measureDiffEntropy_conv_gaussianReal hs] at h

theorem two_pi_e_le_exp_mul_heatFisher (hν2 : Integrable (fun y => y ^ 2) ν) {t : ℝ}
    (ht : 0 < t) :
    2 * Real.pi * Real.exp 1
      ≤ Real.exp (2 * ∫ x, Real.negMulLog (heatDensity ν t x)) * heatFisher ν t := by
  set H : ℝ → ℝ := fun s => ∫ x, Real.negMulLog (heatDensity ν s x)
  set J := heatFisher ν t
  have hJ0 : 0 ≤ J := heatFisher_nonneg ht
  set Φ : ℝ → ℝ := fun τ => H (t + τ) - 1 / 2 * Real.log (1 + τ * J)
  have hΦd : ∀ τ, 0 ≤ τ →
      HasDerivAt Φ (heatFisher ν (t + τ) / 2 - 1 / 2 * (J / (1 + τ * J))) τ := by
    intro τ hτ
    have hpos : 0 < 1 + τ * J := by positivity
    have h1 := (hasDerivAt_heatEntropy hν2 (by linarith : 0 < t + τ)).comp τ
      ((hasDerivAt_id τ).const_add t)
    have h2 := ((((hasDerivAt_id τ).mul_const J).const_add 1).log hpos.ne').const_mul (1 / 2)
    convert h1.sub h2 using 1
    · rfl
    · simp only [id, one_mul, mul_one]
  have hanti : AntitoneOn Φ (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun τ hτ => (hΦd τ hτ).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ici]
      exact fun τ hτ => (hΦd τ (le_of_lt hτ)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro τ hτ
      rw [(hΦd τ (le_of_lt hτ)).deriv]
      have := heatFisher_add_le hν2 ht hτ
      have e : 1 / 2 * (J / (1 + τ * J)) = J / (1 + τ * J) / 2 := by ring
      rw [e]
      linarith
  set E := Real.exp (2 * H t)
  have hE : 0 < E := Real.exp_pos _
  have hkey : ∀ T, 0 < T → 2 * Real.pi * Real.exp 1 * (t + T) ≤ E * (1 + T * J) := by
    intro T hT
    have h1 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hT.le) hT.le
    simp only [Φ, add_zero, zero_mul, Real.log_one, mul_zero, sub_zero] at h1
    have h2 := heatEntropy_ge hν2 (by linarith : 0 < t + T)
    have hpos : 0 < 1 + T * J := by positivity
    have h3 : Real.log (2 * Real.pi * Real.exp 1 * (t + T)) ≤ Real.log (E * (1 + T * J)) := by
      rw [Real.log_mul hE.ne' hpos.ne', Real.log_exp]
      simp only [H] at h1 h2 ⊢
      linarith
    exact (Real.log_le_log_iff (by positivity) (by positivity)).1 h3
  by_contra hlt
  rw [not_le] at hlt
  set δ := 2 * Real.pi * Real.exp 1 - E * J
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hT : δ * (E / δ + 1) = E + δ := by field_simp
  have := hkey (E / δ + 1) (by positivity)
  have hpi : 0 ≤ 2 * Real.pi * Real.exp 1 * t := by positivity
  nlinarith

end HeatFlow

theorem gaussianEntropyPowerInequality : GaussianEntropyPowerInequality := by
  intro ν _ v hv hν h2 hf
  have hν2 : Integrable (fun y => y ^ 2) ν := by simpa using h2.integrable_sq
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  set H : ℝ → ℝ := fun s => ∫ x, Real.negMulLog (heatDensity ν s x)
  set c := 2 * Real.pi * Real.exp 1
  have hc : 0 < c := by positivity
  set Ψ : ℝ → ℝ := fun s => Real.exp (2 * H s) - c * s
  have hΨd : ∀ s, 0 < s →
      HasDerivAt Ψ (Real.exp (2 * H s) * (2 * (heatFisher ν s / 2)) - c * 1) s := fun s hs =>
    (((hasDerivAt_heatEntropy hν2 hs).const_mul 2).exp).sub ((hasDerivAt_id s).const_mul c)
  have hmono : MonotoneOn Ψ (Set.Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun s hs => (hΨd s hs).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ioi]
      exact fun s hs => (hΨd s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro s hs
      rw [(hΨd s hs).deriv]
      have := two_pi_e_le_exp_mul_heatFisher hν2 hs
      simp only [H] at this ⊢
      nlinarith
  have hHv : measureDiffEntropy (ν ∗ gaussianReal 0 v) = H v := by
    change _ = ∫ x, Real.negMulLog (heatDensity ν v x)
    rw [← measureDiffEntropy_conv_gaussianReal hv', Real.toNNReal_coe]
  rw [hHv]
  have hε : ∀ ε : ℝ, 0 < ε → ε < v →
      Real.exp (2 * measureDiffEntropy ν) + c * (v - ε) ≤ Real.exp (2 * H v) := by
    intro ε hε hεv
    have h1 := hmono hε hv' hεv.le
    have h2 : measureDiffEntropy ν ≤ H ε := by
      change _ ≤ ∫ x, Real.negMulLog (heatDensity ν ε x)
      rw [← measureDiffEntropy_conv_gaussianReal hε]
      exact measureDiffEntropy_le_conv hν hf (integrable_negMulLog_conv_gaussianReal hν2 hε)
    have h3 := Real.exp_le_exp.2 (by linarith : 2 * measureDiffEntropy ν ≤ 2 * H ε)
    simp only [Ψ] at h1
    nlinarith
  by_contra hlt
  rw [not_le] at hlt
  set δ := Real.exp (2 * measureDiffEntropy ν) + c * v - Real.exp (2 * H v)
  have hδ : 0 < δ := by simp only [δ]; linarith
  set ε := min ((v : ℝ) / 2) (δ / (2 * c))
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hε1 : ε < v := (min_le_left _ _).trans_lt (by linarith)
  have hε2 : c * ε ≤ δ / 2 := by
    have := min_le_right ((v : ℝ) / 2) (δ / (2 * c))
    calc c * ε ≤ c * (δ / (2 * c)) := mul_le_mul_of_nonneg_left this hc.le
      _ = δ / 2 := by field_simp
  have := hε ε hε0 hε1
  simp only [δ] at hε2
  nlinarith

theorem diffEntropy_add_gaussian_ge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Z : Ω → ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) (hX : AEMeasurable X μ) (hZ : HasLaw Z (gaussianReal 0 v) μ)
    (hXZ : IndepFun X Z μ) (h2 : MemLp X 2 μ) (hν : μ.map X ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog ((μ.map X).rnDeriv volume x).toReal)) :
    (1 / 2) * Real.log (Real.exp (2 * diffEntropy X μ) + 2 * Real.pi * Real.exp 1 * v)
      ≤ diffEntropy (X + Z) μ := by
  have hmap : μ.map (X + Z) = μ.map X ∗ gaussianReal 0 v := by
    rw [hXZ.map_add_eq_map_conv_map₀ hX hZ.aemeasurable, hZ.map_eq]
  have hid : MemLp id 2 (μ.map X) := (memLp_map_measure_iff aestronglyMeasurable_id hX).2 h2
  have h := gaussianEntropyPowerInequality (μ.map X) v hv hν hid hf
  rw [diffEntropy, diffEntropy, hmap]
  have hpos : 0 < Real.exp (2 * measureDiffEntropy (μ.map X)) +
      2 * Real.pi * Real.exp 1 * v := by
    positivity
  have := Real.log_le_log hpos h
  rw [Real.log_exp] at this
  linarith

theorem max_diffEntropy_le_add_gaussian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Z : Ω → ℝ} {v : ℝ≥0} (hv : v ≠ 0) (hX : AEMeasurable X μ)
    (hZ : HasLaw Z (gaussianReal 0 v) μ) (hXZ : IndepFun X Z μ) (hν : μ.map X ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog ((μ.map X).rnDeriv volume x).toReal))
    (hg : Integrable (fun x => Real.negMulLog ((μ.map (X + Z)).rnDeriv volume x).toReal)) :
    max (diffEntropy X μ) ((1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * v))
      ≤ diffEntropy (X + Z) μ := by
  have hmap : μ.map (X + Z) = μ.map X ∗ gaussianReal 0 v := by
    rw [hXZ.map_add_eq_map_conv_map₀ hX hZ.aemeasurable, hZ.map_eq]
  rw [hmap] at hg
  have h1 := measureDiffEntropy_le_conv hν hf hg
  have h2 := measureDiffEntropy_le_conv (ρ := μ.map X) (gaussianReal_absolutelyContinuous 0 hv)
    (integrable_negMulLog_gaussianReal 0 hv) (by rwa [Measure.conv_comm])
  rw [Measure.conv_comm, measureDiffEntropy_gaussianReal 0 v hv] at h2
  rw [diffEntropy, diffEntropy, hmap]
  exact max_le h1 h2

end Meat
