import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Meat.Channel.Converse

open MeasureTheory
open scoped ENNReal

namespace Meat

namespace DMC

variable {A B T : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] [MeasurableSpace T]

omit [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] in
theorem integral_comp_eq_sum {μ : Measure T} [IsFiniteMeasure μ] {Q : T → A}
    (hQ : Measurable Q) (g : A → ℝ) :
    ∫ t, g (Q t) ∂μ = ∑ x, μ.real (Q ⁻¹' {x}) * g x := by
  rw [← integral_map hQ.aemeasurable Integrable.of_finite.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  simp [map_measureReal_apply hQ (measurableSet_singleton _), smul_eq_mul]

omit [Fintype A] [Fintype B] in
private lemma jointMeasure_real_singleton' (W : DMC A B) (p : PMF A) (x : A × B) :
    (W.jointMeasure p).real {x} = (p x.1).toReal * (W x.1 x.2).toReal := by
  rw [measureReal_def, jointMeasure_eq_toMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), ← ENNReal.toReal_mul,
    ← jointPMF_apply]

theorem inputMutualInfo_eq_sum (W : DMC A B) (p : PMF A) :
    W.inputMutualInfo p = ∑ x : A × B, (p x.1).toReal * (W x.1 x.2).toReal *
      (Real.log (W x.1 x.2).toReal - Real.log (((W.jointMeasure p).map Prod.snd).real {x.2})) := by
  rw [inputMutualInfo, mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy,
    condEntropy_snd_fst_jointMeasure, entropy, measureEntropy_map_eq_neg_sum_mul_log]
  simp only [jointMeasure_real_singleton', mul_sub, Finset.sum_sub_distrib]
  ring

private lemma sub_le_mul_log {w r u : ℝ} (hw : 0 ≤ w) (hr : 0 ≤ r) (hu : 0 < u)
    (hwr : 0 < w → 0 < r) :
    w - r * u ≤ w * (Real.log w - Real.log r) - w * Real.log u := by
  rcases hw.eq_or_lt with h | h
  · subst h
    simp only [zero_sub, zero_mul, sub_zero, neg_nonpos]
    positivity
  have hr' := hwr h
  have h1 := Real.one_sub_inv_le_log_of_pos (x := w / (r * u)) (by positivity)
  rw [Real.log_div h.ne' (by positivity), Real.log_mul hr'.ne' hu.ne', inv_div] at h1
  have h2 : w * (1 - r * u / w) = w - r * u := by field_simp
  nlinarith

theorem integral_sum_mul_log_le_inputMutualInfo (W : DMC A B) (p : PMF A) {μ : Measure T}
    [IsProbabilityMeasure μ] {Q : T → A} (hQ : Measurable Q)
    (hp : ∀ x, (p x).toReal = μ.real (Q ⁻¹' {x})) (u : T → B → ℝ) (hu : ∀ t b, 0 < u t b)
    (hu1 : ∀ b, ∫ t, u t b ∂μ = 1) (hlog : ∀ b, Integrable (fun t => Real.log (u t b)) μ) :
    ∫ t, ∑ b, (W (Q t) b).toReal * Real.log (u t b) ∂μ ≤ W.inputMutualInfo p := by
  set w : A → B → ℝ := fun x b => (W x b).toReal
  set ν := W.jointMeasure p
  set r : B → ℝ := fun b => (ν.map Prod.snd).real {b}
  have hr : ∀ x b, (p x).toReal * w x b ≤ r b := fun x b => by
    have := measureReal_singleton_le_map ν Prod.snd (x, b)
    rwa [jointMeasure_real_singleton'] at this
  have hI : W.inputMutualInfo p
      = ∫ t, ∑ b, w (Q t) b * (Real.log (w (Q t) b) - Real.log (r b)) ∂μ := by
    have h := integral_comp_eq_sum (μ := μ) hQ
      (fun x => ∑ b, w x b * (Real.log (w x b) - Real.log (r b)))
    rw [inputMutualInfo_eq_sum, h, Fintype.sum_prod_type]
    simp only [hp, Finset.mul_sum, mul_assoc, w, r, ν]
  have hnull : ∀ x, ¬ 0 < (p x).toReal → μ (Q ⁻¹' {x}) = 0 := fun x hx => by
    have h0 : μ.real (Q ⁻¹' {x}) = 0 := by
      rw [← hp]
      exact le_antisymm (not_lt.1 hx) ENNReal.toReal_nonneg
    exact (measureReal_eq_zero_iff).1 h0
  have hae : ∀ᵐ t ∂μ, 0 < (p (Q t)).toReal := by
    rw [ae_iff]
    have hset : {t | ¬ 0 < (p (Q t)).toReal} = ⋃ x ∈ {x | ¬ 0 < (p x).toReal}, Q ⁻¹' {x} := by
      ext
      simp
    rw [hset]
    exact (measure_biUnion_null_iff (Set.to_countable _)).2 fun x hx => hnull x hx
  have hwm : ∀ b, Measurable fun t => w (Q t) b := fun b =>
    (measurable_of_finite fun x => w x b).comp hQ
  have hw1 : ∀ x b, ‖w x b‖ ≤ 1 := fun x b => by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (W x).coe_le_one b)
  have i1 : Integrable (fun t => ∑ b, w (Q t) b * Real.log (u t b)) μ :=
    integrable_finsetSum _ fun b _ =>
      (hlog b).bdd_mul (hwm b).aestronglyMeasurable (ae_of_all _ fun t => hw1 _ b)
  have i2 : Integrable (fun t => ∑ b, w (Q t) b * (Real.log (w (Q t) b) - Real.log (r b))) μ :=
    (Integrable.of_finite (f := fun x => ∑ b, w x b * (Real.log (w x b) - Real.log (r b)))
      (μ := μ.map Q)).comp_measurable hQ
  have hui : ∀ b, Integrable (fun t => u t b) μ := fun b =>
    Integrable.of_integral_ne_zero (by rw [hu1 b]; exact one_ne_zero)
  have i3 : Integrable (fun t => ∑ b, (w (Q t) b - r b * u t b)) μ :=
    integrable_finsetSum _ fun b _ =>
      ((Integrable.of_finite (f := fun x => w x b) (μ := μ.map Q)).comp_measurable hQ).sub
        ((hui b).const_mul _)
  have h0 : ∫ t, ∑ b, (w (Q t) b - r b * u t b) ∂μ = 0 := by
    have hs : ∀ x, ∑ b, w x b = 1 := fun x => sum_toReal_pmf_eq_one (W x)
    simp only [Finset.sum_sub_distrib, hs]
    rw [integral_sub (integrable_const _) (integrable_finsetSum _ fun b _ => (hui b).const_mul _),
      integral_finsetSum _ fun b _ => (hui b).const_mul _]
    simp only [integral_const_mul, hu1, mul_one, integral_const, probReal_univ, smul_eq_mul,
      r]
    rw [sum_measureReal_singleton_eq_one]
    simp
  have key : ∀ᵐ t ∂μ, ∑ b, (w (Q t) b - r b * u t b)
      ≤ ∑ b, w (Q t) b * (Real.log (w (Q t) b) - Real.log (r b))
        - ∑ b, w (Q t) b * Real.log (u t b) := by
    filter_upwards [hae] with t ht
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun b _ => sub_le_mul_log ENNReal.toReal_nonneg measureReal_nonneg
      (hu t b) fun hw => (mul_pos ht hw).trans_le (hr (Q t) b)
  have := integral_mono_ae i3 (i2.sub i1) key
  rw [h0, Pi.sub_def, integral_sub i2 i1, ← hI] at this
  linarith

end DMC

end Meat
