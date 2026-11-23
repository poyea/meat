import Meat.Continuous.MaxEntropy

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Meat

namespace GaussianMultiUser

theorem awgnCapacity_add {P₁ P₂ N : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N) :
    awgnCapacity P₁ N + awgnCapacity P₂ (P₁ + N) = awgnCapacity (P₁ + P₂) N := by
  unfold awgnCapacity
  have h1 : 0 < 1 + P₁ / N := by positivity
  have h2 : 0 < 1 + P₂ / (P₁ + N) := by positivity
  rw [← mul_add, ← Real.log_mul h1.ne' h2.ne']
  congr 2
  field_simp
  ring

theorem awgnCapacity_mono {P P' N : ℝ} (hP : 0 ≤ P) (hPP' : P ≤ P') (hN : 0 < N) :
    awgnCapacity P N ≤ awgnCapacity P' N := by
  unfold awgnCapacity
  have : 0 < 1 + P / N := by positivity
  have h : 1 + P / N ≤ 1 + P' / N := by
    have := div_le_div_of_nonneg_right hPP' hN.le
    linarith
  nlinarith [Real.log_le_log this h]

theorem awgnCapacity_nonneg' {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) : 0 ≤ awgnCapacity P N := by
  have := awgnCapacity_mono le_rfl hP hN
  unfold awgnCapacity at this ⊢
  simpa using this

def macRegion (P₁ P₂ N : ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ R.1 ≤ awgnCapacity P₁ N ∧ R.2 ≤ awgnCapacity P₂ N ∧
    R.1 + R.2 ≤ awgnCapacity (P₁ + P₂) N}

theorem corner_mem_macRegion {P₁ P₂ N : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N) :
    (awgnCapacity P₁ N, awgnCapacity P₂ (P₁ + N)) ∈ macRegion P₁ P₂ N ∧
      awgnCapacity P₁ N + awgnCapacity P₂ (P₁ + N) = awgnCapacity (P₁ + P₂) N := by
  have hsum := awgnCapacity_add hP₁ hP₂ hN
  have h2 : awgnCapacity P₂ (P₁ + N) ≤ awgnCapacity P₂ N := by
    unfold awgnCapacity
    have h0 : 0 < 1 + P₂ / (P₁ + N) := by positivity
    have h : 1 + P₂ / (P₁ + N) ≤ 1 + P₂ / N := by
      have := div_le_div_of_nonneg_left hP₂ hN (by linarith : N ≤ P₁ + N)
      linarith
    nlinarith [Real.log_le_log h0 h]
  exact ⟨⟨awgnCapacity_nonneg' hP₁ hN, awgnCapacity_nonneg' hP₂ (by linarith), le_rfl, h2,
    hsum.le⟩, hsum⟩

noncomputable def bcRegion (P N₁ N₂ : ℝ) : Set (ℝ × ℝ) :=
  ⋃ α ∈ Set.Icc (0 : ℝ) 1, {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ R.1 ≤ awgnCapacity (α * P) N₁ ∧
    R.2 ≤ awgnCapacity ((1 - α) * P) (α * P + N₂)}

theorem bcRegion_sum_of_eq {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) {α : ℝ} (hα : α ∈ Set.Icc 0 1) :
    (awgnCapacity (α * P) N, awgnCapacity ((1 - α) * P) (α * P + N)) ∈ bcRegion P N N ∧
      awgnCapacity (α * P) N + awgnCapacity ((1 - α) * P) (α * P + N) = awgnCapacity P N := by
  have h1 : 0 ≤ α * P := mul_nonneg hα.1 hP
  have h2 : 0 ≤ (1 - α) * P := mul_nonneg (by linarith [hα.2]) hP
  refine ⟨Set.mem_biUnion hα ⟨awgnCapacity_nonneg' h1 hN,
    awgnCapacity_nonneg' h2 (by linarith), le_rfl, le_rfl⟩, ?_⟩
  rw [awgnCapacity_add h1 h2 hN]
  congr 1
  ring

theorem diffEntropy_le_of_variance_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ) (hν : μ.map Y ≪ volume)
    (hf : Integrable fun x => Real.negMulLog ((μ.map Y).rnDeriv volume x).toReal)
    (h2 : MemLp Y 2 μ) {v : ℝ} (hv : Var[Y; μ] ≤ v) :
    diffEntropy Y μ ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * v) := by
  have hid : MemLp id 2 (μ.map Y) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hY).2 h2
  have hvar : Var[id; μ.map Y] = Var[Y; μ] := variance_map aemeasurable_id hY
  have hpos := variance_pos_of_absolutelyContinuous hν hid
  have h := measureDiffEntropy_le_of_variance hν hf hid
  rw [hvar] at h hpos
  refine h.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) (by norm_num))
  have := Real.pi_pos
  have := Real.exp_pos 1
  gcongr

theorem diffEntropy_mac_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X₁ X₂ Z : Ω → ℝ} {P₁ P₂ N : ℝ}
    (h₁ : MemLp X₁ 2 μ) (h₂ : MemLp X₂ 2 μ) (hZ : MemLp Z 2 μ)
    (hi₁₂ : IndepFun X₁ X₂ μ) (hi : IndepFun (X₁ + X₂) Z μ)
    (hv₁ : Var[X₁; μ] ≤ P₁) (hv₂ : Var[X₂; μ] ≤ P₂) (hvZ : Var[Z; μ] = N)
    (hν : μ.map (X₁ + X₂ + Z) ≪ volume)
    (hf : Integrable fun x => Real.negMulLog ((μ.map (X₁ + X₂ + Z)).rnDeriv volume x).toReal) :
    diffEntropy (X₁ + X₂ + Z) μ ≤
      (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (P₁ + P₂ + N)) := by
  have h12 := h₁.add h₂
  have hvar : Var[X₁ + X₂ + Z; μ] = Var[X₁; μ] + Var[X₂; μ] + Var[Z; μ] := by
    rw [hi.variance_add h12 hZ, hi₁₂.variance_add h₁ h₂]
  exact diffEntropy_le_of_variance_le (h12.add hZ).aemeasurable hν hf (h12.add hZ)
    (by rw [hvar, hvZ]; linarith)

theorem diffEntropy_bc_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Z : Ω → ℝ} {P N : ℝ} (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ)
    (hi : IndepFun X Z μ) (hv : Var[X; μ] ≤ P) (hvZ : Var[Z; μ] = N)
    (hν : μ.map (X + Z) ≪ volume)
    (hf : Integrable fun x => Real.negMulLog ((μ.map (X + Z)).rnDeriv volume x).toReal) :
    diffEntropy (X + Z) μ ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (P + N)) :=
  diffEntropy_le_of_variance_le (hX.add hZ).aemeasurable hν hf (hX.add hZ)
    (by rw [hi.variance_add hX hZ, hvZ]; linarith)

theorem sub_gaussian_le_awgnCapacity {h S N : ℝ} (hN : 0 < N) (hS : 0 ≤ S)
    (hh : h ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (S + N))) :
    h - measureDiffEntropy (gaussianReal 0 N.toNNReal) ≤ awgnCapacity S N := by
  have hN' : N.toNNReal ≠ 0 := by simp [hN]
  rw [measureDiffEntropy_gaussianReal 0 _ hN', Real.coe_toNNReal _ hN.le]
  unfold awgnCapacity
  have hc : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  have e : Real.log (2 * Real.pi * Real.exp 1 * (S + N)) - Real.log (2 * Real.pi * Real.exp 1 * N)
      = Real.log (1 + S / N) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  linarith

end GaussianMultiUser

end Meat
