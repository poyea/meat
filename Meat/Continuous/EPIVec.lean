import Meat.Continuous.EPI
import Meat.Continuous.StamVecTwo

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

variable {n : ℕ}

private lemma integrable_coord_mul {s : ℝ} (hs : 0 < s) (i : Fin n) :
    Integrable fun v : Fin n → ℝ => v i * heatKernelVec s v := by
  have h := (integrable_mul_heatKernelVec_volume hs (c := fun v : Fin n → ℝ => -(v i / s))
    (by fun_prop) (fun v => heatPolyVec_deriv hs le_rfl v i)).const_mul (-s)
  refine h.congr (ae_of_all _ fun v => ?_)
  simp only
  field_simp

private lemma integrable_coord_sq_mul {s : ℝ} (hs : 0 < s) (i : Fin n) :
    Integrable fun v : Fin n → ℝ => v i ^ 2 * heatKernelVec s v := by
  have h := (integrable_mul_heatKernelVec_volume hs (c := fun v : Fin n → ℝ => v i ^ 2 / s ^ 2)
    (by fun_prop) (fun v => heatPolyVec_sq hs le_rfl v i)).const_mul (s ^ 2)
  refine h.congr (ae_of_all _ fun v => ?_)
  simp only
  field_simp

private lemma integral_coord_mul {s : ℝ} (hs : 0 < s) (i : Fin n) :
    ∫ v : Fin n → ℝ, v i * heatKernelVec s v = 0 := by
  rw [integral_comp_mul_heatKernelVec hs (fun r => r) i]
  exact (integral_mul_heatKernel_moment hs).2.1

private lemma integral_coord_sq_mul {s : ℝ} (hs : 0 < s) (i : Fin n) :
    ∫ v : Fin n → ℝ, v i ^ 2 * heatKernelVec s v = s := by
  rw [integral_comp_mul_heatKernelVec hs (fun r => r ^ 2) i]
  exact (integral_mul_heatKernel_moment hs).2.2

theorem integrable_sum_sq_mul_heatKernelVec {s : ℝ} (hs : 0 < s) :
    Integrable fun v : Fin n → ℝ => (∑ i, v i ^ 2) * heatKernelVec s v := by
  simp_rw [Finset.sum_mul]
  exact integrable_finsetSum _ fun i _ => integrable_coord_sq_mul hs i

theorem integral_sum_sq_mul_heatKernelVec {s : ℝ} (hs : 0 < s) :
    ∫ v : Fin n → ℝ, (∑ i, v i ^ 2) * heatKernelVec s v = n * s := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => integrable_coord_sq_mul hs i]
  simp [integral_coord_sq_mul hs]

private lemma sum_sq_shift (z y : Fin n → ℝ) (k : ℝ) :
    (∑ i, (z + y) i ^ 2) * k
      = (∑ i, z i ^ 2) * k + ∑ i, 2 * y i * (z i * k) + (∑ i, y i ^ 2) * k := by
  have e : ∑ i, (z + y) i ^ 2 = ∑ i, z i ^ 2 + ∑ i, 2 * y i * z i + ∑ i, y i ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  rw [e, show ∑ i, 2 * y i * (z i * k) = (∑ i, 2 * y i * z i) * k by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring]
  ring

private lemma integrable_sum_sq_shift {s : ℝ} (hs : 0 < s) (y : Fin n → ℝ) :
    Integrable fun z : Fin n → ℝ => (∑ i, (z + y) i ^ 2) * heatKernelVec s z := by
  simp_rw [sum_sq_shift]
  exact ((integrable_sum_sq_mul_heatKernelVec hs).add (integrable_finsetSum _ fun i _ =>
    (integrable_coord_mul hs i).const_mul (2 * y i))).add
    ((integrable_heatKernelVec hs).const_mul _)

private lemma integral_sum_sq_shift {s : ℝ} (hs : 0 < s) (y : Fin n → ℝ) :
    ∫ x, (∑ i, x i ^ 2) * heatKernelVec s (x - y) = ∑ i, y i ^ 2 + n * s := by
  rw [← integral_add_right_eq_self _ y]
  simp only [add_sub_cancel_right]
  have e : ∀ z : Fin n → ℝ, (∑ i, (z + y) i ^ 2) * heatKernelVec s z
      = (∑ i, z i ^ 2) * heatKernelVec s z + ∑ i, 2 * y i * (z i * heatKernelVec s z) +
        (∑ i, y i ^ 2) * heatKernelVec s z := fun z => sum_sq_shift z y _
  simp_rw [e]
  have i2 : Integrable fun z : Fin n → ℝ => ∑ i, 2 * y i * (z i * heatKernelVec s z) :=
    integrable_finsetSum _ fun i _ => (integrable_coord_mul hs i).const_mul (2 * y i)
  have i12 : Integrable fun z : Fin n → ℝ => (∑ i, z i ^ 2) * heatKernelVec s z +
      ∑ i, 2 * y i * (z i * heatKernelVec s z) := (integrable_sum_sq_mul_heatKernelVec hs).add i2
  rw [integral_add i12 ((integrable_heatKernelVec hs).const_mul _),
    integral_add (integrable_sum_sq_mul_heatKernelVec hs) i2, integral_const_mul,
    integral_heatKernelVec hs,
    integral_finsetSum _ fun i _ => (integrable_coord_mul hs i).const_mul (2 * y i),
    integral_sum_sq_mul_heatKernelVec hs]
  simp [integral_const_mul, integral_coord_mul hs]
  ring

private lemma sum_sq_nonneg (x : Fin n → ℝ) : 0 ≤ ∑ i, x i ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem integral_sum_sq_mul_heatDensityVec {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun x => (∑ i, x i ^ 2) * heatDensityVec μ s x) ∧
      ∫ x, (∑ i, x i ^ 2) * heatDensityVec μ s x = ∫ y, ∑ i, y i ^ 2 ∂μ + n * s := by
  set G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => (∑ i, p.1 i ^ 2) * heatKernelVec s (p.1 - p.2)
  have hGc : Continuous G := by
    refine (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_fst).pow 2).mul
      ((continuous_heatKernelVec s).comp (continuous_fst.sub continuous_snd))
  have hG0 : ∀ p, 0 ≤ G p := fun p => mul_nonneg (sum_sq_nonneg _) (heatKernelVec_pos hs _).le
  have hsec : ∀ y, Integrable fun x => G (x, y) := fun y => by
    refine ((integrable_sum_sq_shift hs y).comp_sub_right y).congr (ae_of_all _ fun x => ?_)
    simp [G]
  have hG : Integrable G (volume.prod μ) := by
    refine (integrable_prod_iff' hGc.aestronglyMeasurable).2 ⟨ae_of_all _ hsec, ?_⟩
    refine (hμ2.add (integrable_const ((n : ℝ) * s))).congr (ae_of_all _ fun y => ?_)
    simp only [Pi.add_apply]
    rw [← integral_sum_sq_shift hs y]
    exact integral_congr_ae (ae_of_all _ fun x => (Real.norm_of_nonneg (hG0 (x, y))).symm)
  have e : ∀ x, (∑ i, x i ^ 2) * heatDensityVec μ s x = ∫ y, G (x, y) ∂μ := fun x =>
    (integral_const_mul _ _).symm
  simp_rw [e]
  refine ⟨hG.integral_prod_left, ?_⟩
  rw [integral_integral_swap (f := fun x y => G (x, y)) hG]
  have e2 : ∀ y, ∫ x, G (x, y) = ∑ i, y i ^ 2 + n * s := fun y => integral_sum_sq_shift hs y
  simp_rw [e2]
  rw [integral_add hμ2 (integrable_const _)]
  simp

theorem log_heatKernelVec {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) :
    Real.log (heatKernelVec s x)
      = -(n / 2 * Real.log (2 * Real.pi * s) + (∑ i, x i ^ 2) / (2 * s)) := by
  rw [heatKernelVec, Real.log_prod fun i _ => (heatKernel_pos hs _).ne']
  have e : ∀ u : ℝ,
      Real.log (heatKernel s u) = -(Real.log (2 * Real.pi * s) / 2 + u ^ 2 / (2 * s)) := by
    intro u
    rw [heatKernel, Real.log_mul (inv_ne_zero (by positivity)) (Real.exp_pos _).ne', Real.log_inv,
      Real.log_exp, Real.log_sqrt (by positivity)]
    ring
  simp_rw [e]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div]
  ring

private lemma integrable_heatKernelVec_mul_log {s : ℝ} (hs : 0 < s) :
    Integrable fun x : Fin n → ℝ => heatKernelVec s x * Real.log (heatKernelVec s x) := by
  refine (((integrable_heatKernelVec hs).const_mul (-(n / 2 * Real.log (2 * Real.pi * s)))).add
    ((integrable_sum_sq_mul_heatKernelVec hs).const_mul (-(1 / (2 * s))))).congr
    (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply]
  rw [log_heatKernelVec hs]
  field_simp
  ring

private lemma integral_negMulLog_heatKernelVec {s : ℝ} (hs : 0 < s) :
    ∫ x : Fin n → ℝ, Real.negMulLog (heatKernelVec s x)
      = n / 2 * Real.log (2 * Real.pi * Real.exp 1 * s) := by
  have e : ∀ x : Fin n → ℝ, Real.negMulLog (heatKernelVec s x)
      = n / 2 * Real.log (2 * Real.pi * s) * heatKernelVec s x +
        1 / (2 * s) * ((∑ i, x i ^ 2) * heatKernelVec s x) := fun x => by
    rw [Real.negMulLog, log_heatKernelVec hs]
    field_simp
  simp_rw [e]
  rw [integral_add ((integrable_heatKernelVec hs).const_mul _)
    ((integrable_sum_sq_mul_heatKernelVec hs).const_mul _), integral_const_mul, integral_const_mul,
    integral_heatKernelVec hs, integral_sum_sq_mul_heatKernelVec hs,
    show 2 * Real.pi * Real.exp 1 * s = Real.exp 1 * (2 * Real.pi * s) by ring,
    Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  field_simp
  ring

noncomputable def gaussianVec (s : ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity fun x => ENNReal.ofReal (heatKernelVec s x)

instance sFinite_gaussianVec (s : ℝ) : SFinite (gaussianVec (n := n) s) := by
  unfold gaussianVec
  infer_instance

theorem isProbabilityMeasure_gaussianVec {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure (gaussianVec (n := n) s) := by
  refine ⟨?_⟩
  rw [gaussianVec, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernelVec hs)
      (ae_of_all _ fun x => (heatKernelVec_pos hs x).le),
    integral_heatKernelVec hs, ENNReal.ofReal_one]

theorem withDensity_conv_eq_vec {F : (Fin n → ℝ) → ℝ≥0∞} (hF : Measurable F)
    (ρ : Measure (Fin n → ℝ)) [SFinite ρ] :
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

variable {μ ν ρ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [IsProbabilityMeasure ρ]

theorem gaussianVec_conv_eq_withDensity {s : ℝ} (hs : 0 < s) :
    gaussianVec s ∗ μ = volume.withDensity (fun x => ENNReal.ofReal (heatDensityVec μ s x)) := by
  rw [gaussianVec, withDensity_conv_eq_vec (continuous_heatKernelVec s).measurable.ennreal_ofReal]
  congr 1
  ext x
  rw [heatDensityVec, ofReal_integral_eq_lintegral_ofReal
    (integrable_heatKernelVec_comp hs le_rfl le_rfl x)
    (ae_of_all _ fun y => (heatKernelVec_pos hs _).le)]

theorem measureDiffEntropy_conv_gaussianVec {s : ℝ} (hs : 0 < s) :
    measureDiffEntropy (μ ∗ gaussianVec s) = ∫ x, Real.negMulLog (heatDensityVec μ s x) := by
  rw [Measure.conv_comm, gaussianVec_conv_eq_withDensity hs, measureDiffEntropy]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity volume
    (continuous_heatDensityVec (μ := μ) hs).measurable.ennreal_ofReal] with x hx
  rw [hx, ENNReal.toReal_ofReal (heatDensityVec_pos hs x).le]

theorem integrable_negMulLog_conv_gaussianVec (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ)
    {s : ℝ} (hs : 0 < s) : Integrable (fun x =>
      Real.negMulLog ((μ ∗ gaussianVec s).rnDeriv volume x).toReal) := by
  rw [Measure.conv_comm, gaussianVec_conv_eq_withDensity hs]
  refine (integrable_negMulLog_heatDensityVec hμ2 hs).congr ?_
  filter_upwards [Measure.rnDeriv_withDensity volume
    (continuous_heatDensityVec (μ := μ) hs).measurable.ennreal_ofReal] with x hx
  rw [hx, ENNReal.toReal_ofReal (heatDensityVec_pos hs x).le]

omit [IsProbabilityMeasure ν] in
private lemma conv_eq_withDensity_vec [IsFiniteMeasure ν] (hν : ν ≪ volume) :
    ν ∗ ρ = volume.withDensity (fun x => ∫⁻ y, ν.rnDeriv volume (x - y) ∂ρ) := by
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq ν volume hν]
  exact withDensity_conv_eq_vec (Measure.measurable_rnDeriv ν volume) ρ

private lemma integrable_comp_sub_vec {φ : (Fin n → ℝ) → ℝ} (hm : Measurable φ)
    (hi : Integrable φ) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => φ (p.1 - p.2)) (volume.prod ρ) := by
  have hs : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => φ (p.1 - p.2) :=
    hm.comp (measurable_fst.sub measurable_snd)
  refine (integrable_prod_iff' hs.aestronglyMeasurable).2
    ⟨ae_of_all _ fun y => hi.comp_sub_right y, ?_⟩
  refine (integrable_const (∫ x, ‖φ x‖)).congr (ae_of_all _ fun y => ?_)
  exact (integral_sub_right_eq_self (‖φ ·‖) y).symm

theorem measureDiffEntropy_le_conv_vec (hν : ν ≪ volume)
    (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal))
    (hg : Integrable (fun x => Real.negMulLog ((ν ∗ ρ).rnDeriv volume x).toReal)) :
    measureDiffEntropy ν ≤ measureDiffEntropy (ν ∗ ρ) := by
  set F := ν.rnDeriv volume
  have hF : Measurable F := Measure.measurable_rnDeriv ν volume
  set G : (Fin n → ℝ) → ℝ≥0∞ := fun x => ∫⁻ y, F (x - y) ∂ρ
  have hGm : Measurable G := (hF.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'
  have hconv := conv_eq_withDensity_vec (ρ := ρ) hν
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
  have hH := integrable_comp_sub_vec (ρ := ρ) hHm hf
  have hfi := integrable_comp_sub_vec (ρ := ρ) hfm Measure.integrable_toReal_rnDeriv
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

private lemma rnDeriv_gaussianVec {s : ℝ} (hs : 0 < s) :
    ∀ᵐ x, ((gaussianVec (n := n) s).rnDeriv volume x).toReal = heatKernelVec s x := by
  rw [gaussianVec]
  filter_upwards [Measure.rnDeriv_withDensity volume
    (continuous_heatKernelVec (n := n) s).measurable.ennreal_ofReal] with x hx
  rw [hx, ENNReal.toReal_ofReal (heatKernelVec_pos hs x).le]

theorem measureDiffEntropy_gaussianVec {s : ℝ} (hs : 0 < s) :
    measureDiffEntropy (gaussianVec (n := n) s)
      = n / 2 * Real.log (2 * Real.pi * Real.exp 1 * s) := by
  rw [measureDiffEntropy, ← integral_negMulLog_heatKernelVec hs]
  exact integral_congr_ae ((rnDeriv_gaussianVec hs).mono fun x hx => by simp only [hx])

private lemma integrable_negMulLog_gaussianVec {s : ℝ} (hs : 0 < s) :
    Integrable fun x => Real.negMulLog ((gaussianVec (n := n) s).rnDeriv volume x).toReal := by
  refine (integrable_heatKernelVec_mul_log hs).neg.congr
    ((rnDeriv_gaussianVec hs).mono fun x hx => ?_)
  simp only [Pi.neg_apply, hx, Real.negMulLog]
  ring

theorem heatEntropyVec_ge (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {s : ℝ} (hs : 0 < s) :
    n / 2 * Real.log (2 * Real.pi * Real.exp 1 * s)
      ≤ ∫ x, Real.negMulLog (heatDensityVec μ s x) := by
  have := isProbabilityMeasure_gaussianVec (n := n) hs
  have hac : gaussianVec (n := n) s ≪ volume := withDensity_absolutelyContinuous _ _
  have h := measureDiffEntropy_le_conv_vec (ν := gaussianVec s) (ρ := μ) hac
    (integrable_negMulLog_gaussianVec hs)
    (by rw [Measure.conv_comm]; exact integrable_negMulLog_conv_gaussianVec hμ2 hs)
  rwa [measureDiffEntropy_gaussianVec hs, Measure.conv_comm,
    measureDiffEntropy_conv_gaussianVec hs] at h

theorem heatEntropyVec_le (hn : 0 < n) (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ) {s : ℝ}
    (hs : 0 < s) :
    ∫ x, Real.negMulLog (heatDensityVec μ s x)
      ≤ n / 2 * Real.log (2 * Real.pi * Real.exp 1 * ((∫ y, ∑ i, y i ^ 2 ∂μ) / n + s)) := by
  set M := ∫ y, ∑ i, y i ^ 2 ∂μ
  have hM : 0 ≤ M := integral_nonneg fun y => sum_sq_nonneg y
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set σ := M / n + s
  have hσ : 0 < σ := by positivity
  obtain ⟨hPi2, hPM⟩ := integral_sum_sq_mul_heatDensityVec hμ2 hs
  set P := heatDensityVec μ s
  have hP : ∀ x, 0 < P x := heatDensityVec_pos hs
  have hPi : Integrable P := integrable_heatDensityVec hμ2 hs
  set R : (Fin n → ℝ) → ℝ := fun x => n / 2 * Real.log (2 * Real.pi * σ) * P x +
    1 / (2 * σ) * ((∑ i, x i ^ 2) * P x) + heatKernelVec σ x - P x
  have hRi : Integrable R :=
    (((hPi.const_mul _).add (hPi2.const_mul _)).add (integrable_heatKernelVec hσ)).sub hPi
  have hpt : ∀ x, Real.negMulLog (P x) ≤ R x := by
    intro x
    have hk := heatKernelVec_pos hσ x
    have h1 := Real.log_le_sub_one_of_pos (div_pos hk (hP x))
    rw [Real.log_div hk.ne' (hP x).ne', log_heatKernelVec hσ] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hP x).le
    have e : P x * (heatKernelVec σ x / P x - 1) = heatKernelVec σ x - P x := by
      field_simp [(hP x).ne']
    rw [e] at h2
    have e2 : R x - Real.negMulLog (P x) = (heatKernelVec σ x - P x) -
        P x * (-(n / 2 * Real.log (2 * Real.pi * σ) + (∑ i, x i ^ 2) / (2 * σ)) -
          Real.log (P x)) := by
      simp only [R, Real.negMulLog]
      ring
    linarith
  have hle := integral_mono (integrable_negMulLog_heatDensityVec hμ2 hs) hRi hpt
  have hR : ∫ x, R x = n / 2 * Real.log (2 * Real.pi * σ) + n / 2 := by
    have hA1 : Integrable fun x => n / 2 * Real.log (2 * Real.pi * σ) * P x +
        1 / (2 * σ) * ((∑ i, x i ^ 2) * P x) := (hPi.const_mul _).add (hPi2.const_mul _)
    have hA2 : Integrable fun x => n / 2 * Real.log (2 * Real.pi * σ) * P x +
        1 / (2 * σ) * ((∑ i, x i ^ 2) * P x) + heatKernelVec σ x :=
      hA1.add (integrable_heatKernelVec hσ)
    simp only [R]
    rw [integral_sub hA2 hPi, integral_add hA1 (integrable_heatKernelVec hσ),
      integral_add (hPi.const_mul _) (hPi2.const_mul _), integral_const_mul, integral_const_mul,
      hPM, integral_heatDensityVec hs, integral_heatKernelVec hσ]
    simp only [σ]
    field_simp
    ring
  rw [hR] at hle
  calc ∫ x, Real.negMulLog (P x) ≤ n / 2 * Real.log (2 * Real.pi * σ) + n / 2 := hle
    _ = _ := by
      rw [show 2 * Real.pi * Real.exp 1 * σ = Real.exp 1 * (2 * Real.pi * σ) by ring,
        Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
      ring

private lemma log_mul_add_mul {c A k τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) (hk : 0 < A / τ + k) :
    Real.log (c * (A + k * τ)) = Real.log c + Real.log τ + Real.log (A / τ + k) := by
  rw [show c * (A + k * τ) = c * τ * (A / τ + k) by field_simp,
    Real.log_mul (by positivity) hk.ne', Real.log_mul hc.ne' hτ.ne']

private lemma heatEntropyVec_conv_ge (hn : 0 < n) (hν2 : Integrable (fun y => ∑ i, y i ^ 2) ν)
    (hρ2 : Integrable (fun y => ∑ i, y i ^ 2) ρ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) {l : ℝ}
    (hl0 : 0 < l) (hl1 : l < 1) :
    l * (∫ x, Real.negMulLog (heatDensityVec ν s x)) +
        (1 - l) * (∫ x, Real.negMulLog (heatDensityVec ρ u x)) +
        n / 2 * (Real.negMulLog l + Real.negMulLog (1 - l))
      ≤ ∫ x, Real.negMulLog (heatDensityVec (ν ∗ ρ) (s + u) x) := by
  set H : Measure (Fin n → ℝ) → ℝ → ℝ := fun μ t => ∫ x, Real.negMulLog (heatDensityVec μ t x)
    with hH
  have hZ2 := integrable_sum_sq_conv hν2 hρ2
  have hl1' : 0 < 1 - l := by linarith
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set D : ℝ → ℝ := fun τ =>
    H (ν ∗ ρ) (s + u + τ) - l * H ν (s + l * τ) - (1 - l) * H ρ (u + (1 - l) * τ)
  have hDd : ∀ τ, 0 ≤ τ → HasDerivAt D (heatFisherVec (ν ∗ ρ) (s + u + τ) / 2 -
      l ^ 2 * (heatFisherVec ν (s + l * τ) / 2) -
      (1 - l) ^ 2 * (heatFisherVec ρ (u + (1 - l) * τ) / 2)) τ := by
    intro τ hτ
    have h1 := (hasDerivAt_heatEntropyVec hZ2 (by positivity : 0 < s + u + τ)).comp τ
      ((hasDerivAt_id' τ).const_add (s + u))
    have h2 := (hasDerivAt_heatEntropyVec hν2 (by positivity : 0 < s + l * τ)).comp τ
      (((hasDerivAt_id' τ).const_mul l).const_add s)
    have h3 := (hasDerivAt_heatEntropyVec hρ2 (by positivity : 0 < u + (1 - l) * τ)).comp τ
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
      have hst := heatFisherVec_conv_le hν2 hρ2 (by positivity : 0 < s + l * τ)
        (by positivity : 0 < u + (1 - l) * τ) l
      rw [show s + l * τ + (u + (1 - l) * τ) = s + u + τ by ring] at hst
      linarith
  set Mν := (∫ y, ∑ i, y i ^ 2 ∂ν) / n
  set Mρ := (∫ y, ∑ i, y i ^ 2 ∂ρ) / n
  have hMν : 0 ≤ Mν := div_nonneg (integral_nonneg fun y => sum_sq_nonneg y) hn'.le
  have hMρ : 0 ≤ Mρ := div_nonneg (integral_nonneg fun y => sum_sq_nonneg y) hn'.le
  set c := 2 * Real.pi * Real.exp 1
  have hc : 0 < c := by positivity
  set L : ℝ → ℝ := fun τ => n / 2 * (Real.log ((s + u) / τ + 1) -
    l * Real.log ((Mν + s) / τ + l) - (1 - l) * Real.log ((Mρ + u) / τ + (1 - l)))
  have hlow : ∀ τ, 0 < τ → L τ ≤ D τ := by
    intro τ hτ
    have g1 := heatEntropyVec_ge hZ2 (by positivity : 0 < s + u + τ)
    have g2 := heatEntropyVec_le hn hν2 (by positivity : 0 < s + l * τ)
    have g3 := heatEntropyVec_le hn hρ2 (by positivity : 0 < u + (1 - l) * τ)
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
  have hlim : Tendsto L atTop (𝓝 (n / 2 * (Real.negMulLog l + Real.negMulLog (1 - l)))) := by
    have t : ∀ A k : ℝ, k ≠ 0 →
        Tendsto (fun τ : ℝ => Real.log (A / τ + k)) atTop (𝓝 (Real.log k)) := by
      intro A k hk
      have := ((tendsto_const_nhds (x := A)).div_atTop tendsto_id).add
        (tendsto_const_nhds (x := k))
      rw [zero_add] at this
      exact this.log hk
    have := (((t (s + u) 1 one_ne_zero).sub ((t (Mν + s) l hl0.ne').const_mul l)).sub
      ((t (Mρ + u) (1 - l) hl1'.ne').const_mul (1 - l))).const_mul ((n : ℝ) / 2)
    convert this using 2
    simp only [Real.negMulLog, Real.log_one]
    ring
  have hD0 : ∀ τ, 0 < τ → L τ ≤ D 0 := fun τ hτ =>
    (hlow τ hτ).trans (hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hτ.le) hτ.le)
  have := le_of_tendsto hlim ((eventually_gt_atTop 0).mono hD0)
  simp only [D, add_zero, mul_zero] at this
  linarith

theorem heatEntropyPowerInequalityVec (hn : 0 < n) (hν2 : Integrable (fun y => ∑ i, y i ^ 2) ν)
    (hρ2 : Integrable (fun y => ∑ i, y i ^ 2) ρ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    Real.exp (2 * (∫ x, Real.negMulLog (heatDensityVec ν s x)) / n) +
        Real.exp (2 * (∫ x, Real.negMulLog (heatDensityVec ρ u x)) / n)
      ≤ Real.exp (2 * (∫ x, Real.negMulLog (heatDensityVec (ν ∗ ρ) (s + u) x)) / n) := by
  set X := ∫ x, Real.negMulLog (heatDensityVec ν s x)
  set Y := ∫ x, Real.negMulLog (heatDensityVec ρ u x)
  set Z := ∫ x, Real.negMulLog (heatDensityVec (ν ∗ ρ) (s + u) x)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set a := Real.exp (2 * X / n)
  set b := Real.exp (2 * Y / n)
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hab : 0 < a + b := by positivity
  have hl := heatEntropyVec_conv_ge hn hν2 hρ2 hs hu (l := a / (a + b)) (div_pos ha hab)
    ((div_lt_one hab).2 (by linarith))
  have h1l : 1 - a / (a + b) = b / (a + b) := by field_simp; ring
  have hla : Real.log (a / (a + b)) = 2 * X / n - Real.log (a + b) := by
    rw [Real.log_div ha.ne' hab.ne']
    exact congrArg (· - Real.log (a + b)) (Real.log_exp (2 * X / n))
  have hlb : Real.log (b / (a + b)) = 2 * Y / n - Real.log (a + b) := by
    rw [Real.log_div hb.ne' hab.ne']
    exact congrArg (· - Real.log (a + b)) (Real.log_exp (2 * Y / n))
  rw [h1l] at hl
  have hna : Real.negMulLog (a / (a + b)) = -(a / (a + b)) * (2 * X / n - Real.log (a + b)) := by
    simp only [Real.negMulLog, hla]
  have hnb : Real.negMulLog (b / (a + b)) = -(b / (a + b)) * (2 * Y / n - Real.log (a + b)) := by
    simp only [Real.negMulLog, hlb]
  rw [hna, hnb] at hl
  have e : a / (a + b) * X + b / (a + b) * Y + n / 2 * (-(a / (a + b)) *
      (2 * X / n - Real.log (a + b)) + -(b / (a + b)) * (2 * Y / n - Real.log (a + b)))
      = n / 2 * Real.log (a + b) := by
    field_simp
    ring
  rw [e] at hl
  have hZ : Real.log (a + b) ≤ 2 * Z / n := by
    rw [le_div_iff₀ hn']
    linarith
  calc a + b = Real.exp (Real.log (a + b)) := (Real.exp_log hab).symm
    _ ≤ Real.exp (2 * Z / n) := Real.exp_le_exp.2 hZ

theorem measureDiffEntropy_le_heatEntropyVec (hν : ν ≪ volume)
    (hν2 : Integrable (fun y => ∑ i, y i ^ 2) ν)
    (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal)) {s : ℝ} (hs : 0 < s) :
    measureDiffEntropy ν ≤ ∫ x, Real.negMulLog (heatDensityVec ν s x) := by
  have := isProbabilityMeasure_gaussianVec (n := n) hs
  rw [← measureDiffEntropy_conv_gaussianVec hs]
  exact measureDiffEntropy_le_conv_vec hν hf (integrable_negMulLog_conv_gaussianVec hν2 hs)

theorem entropyPowerInequalityVec_conv_gaussianVec (hn : 0 < n) (hν : ν ≪ volume)
    (hν2 : Integrable (fun y => ∑ i, y i ^ 2) ν)
    (hf : Integrable (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal)) (hρ : ρ ≪ volume)
    (hρ2 : Integrable (fun y => ∑ i, y i ^ 2) ρ)
    (hg : Integrable (fun x => Real.negMulLog (ρ.rnDeriv volume x).toReal)) {v : ℝ} (hv : 0 < v) :
    Real.exp (2 * measureDiffEntropy ν / n) + Real.exp (2 * measureDiffEntropy ρ / n)
      ≤ Real.exp (2 * measureDiffEntropy ((ν ∗ ρ) ∗ gaussianVec v) / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hv2 : 0 < v / 2 := by positivity
  have h1 := measureDiffEntropy_le_heatEntropyVec hν hν2 hf hv2
  have h2 := measureDiffEntropy_le_heatEntropyVec hρ hρ2 hg hv2
  have h3 := heatEntropyPowerInequalityVec hn hν2 hρ2 hv2 hv2
  rw [add_halves] at h3
  rw [measureDiffEntropy_conv_gaussianVec hv]
  refine le_trans (add_le_add (Real.exp_le_exp.2 ?_) (Real.exp_le_exp.2 ?_)) h3
  · exact div_le_div_of_nonneg_right (by linarith) hn'.le
  · exact div_le_div_of_nonneg_right (by linarith) hn'.le

end Meat
