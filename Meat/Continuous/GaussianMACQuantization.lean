import Meat.Continuous.AWGNCapacity

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Meat

namespace GaussianMAC

open AWGN

theorem abs_log_letterRatio_le {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n : ℕ) (t : ℝ)
    (b : Level n) :
    |Real.log (letterRatio θ N n t b)|
      ≤ |1 / 2 * Real.log (θ / (θ * N / (θ + N)))| + n ^ 2 / (θ * N / (θ + N))
        + (1 / (2 * θ) + 1 / (θ * N / (θ + N))) * t ^ 2 := by
  rw [log_letterRatio hθ hN]
  have hs : 0 < θ * N / (θ + N) := by positivity
  have hα0 : 0 ≤ θ / (θ + N) := by positivity
  have hα1 : θ / (θ + N) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  set s := θ * N / (θ + N)
  set α := θ / (θ + N)
  have hv : |α * value n b| ≤ n := by
    rw [abs_mul, abs_of_nonneg hα0]
    exact (mul_le_of_le_one_left (abs_nonneg _) hα1).trans (abs_value_le n b)
  have hsq : (t - α * value n b) ^ 2 ≤ 2 * t ^ 2 + 2 * n ^ 2 := by
    have h1 := sq_abs (α * value n b)
    have h2 : (α * value n b) ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [← h1]
      exact pow_le_pow_left₀ (abs_nonneg _) hv 2
    nlinarith [sq_nonneg (t + α * value n b)]
  have h3 : 0 ≤ (t - α * value n b) ^ 2 / (2 * s) := by positivity
  have h4 : (t - α * value n b) ^ 2 / (2 * s) ≤ (2 * t ^ 2 + 2 * n ^ 2) / (2 * s) :=
    div_le_div_of_nonneg_right hsq (by positivity)
  have h5 : (2 * t ^ 2 + 2 * n ^ 2) / (2 * s) = n ^ 2 / s + 1 / s * t ^ 2 := by
    field_simp
    ring
  have h6 : 0 ≤ t ^ 2 / (2 * θ) := by positivity
  have h7 : t ^ 2 / (2 * θ) = 1 / (2 * θ) * t ^ 2 := by ring
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg (1 / 2 * Real.log (θ / s)),
    le_abs_self (1 / 2 * Real.log (θ / s)),
    neg_abs_le (1 / 2 * Real.log (θ / s))]

theorem integrable_log_letterRatio {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n : ℕ) {f : α → ℝ}
    {g : α → Level n} (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun a => f a ^ 2) μ) :
    Integrable (fun a => Real.log (letterRatio θ N n (f a) (g a))) μ :=
  ((integrable_const _).add (hf2.const_mul _)).mono'
    (measurable_log_letterRatio θ N n hf hg).aestronglyMeasurable
    (ae_of_all _ fun a => by
      rw [Real.norm_eq_abs]
      exact abs_log_letterRatio_le hθ hN n (f a) (g a))

noncomputable def tinGain (θ₁ θ₂ N : ℝ) (n : ℕ) : ℝ :=
  ∫ w, Real.log (letterRatio θ₂ (θ₁ + N) n w.1.2
      (level n (value n (level n w.1.1) + value n (level n w.1.2) + w.2)))
    ∂((gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)).prod
      (gaussianReal 0 N.toNNReal)

private lemma integrable_id_gaussianReal' (v : ℝ≥0) :
    Integrable (fun t : ℝ => t) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal' 1 (by simp)).integrable le_rfl

private lemma integral_tin_limit (θ₁ θ₂ N α : ℝ) :
    ∫ w, (w.1.2 - α * (w.1.1 + w.1.2 + w.2)) ^ 2
        ∂((gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)).prod
          (gaussianReal 0 N.toNNReal)
      = (1 - α) ^ 2 * θ₂.toNNReal + α ^ 2 * (θ₁.toNNReal + N.toNNReal) := by
  set μ₁ := gaussianReal 0 θ₁.toNNReal
  set μ₂ := gaussianReal 0 θ₂.toNNReal
  set ν := gaussianReal 0 N.toNNReal
  have e : ∀ w : (ℝ × ℝ) × ℝ, (w.1.2 - α * (w.1.1 + w.1.2 + w.2)) ^ 2
      = ((1 - α) ^ 2 * w.1.2 ^ 2 + α ^ 2 * w.1.1 ^ 2 + α ^ 2 * w.2 ^ 2)
        + (2 * α ^ 2 * (w.1.1 * w.2) - 2 * α * (1 - α) * (w.1.2 * w.2)
          - 2 * α * (1 - α) * (w.1.1 * w.1.2)) :=
    fun w => by ring
  have i1 : Integrable (fun w : (ℝ × ℝ) × ℝ => w.1.1 ^ 2) ((μ₁.prod μ₂).prod ν) :=
    ((integrable_sq_gaussianReal _).comp_fst μ₂).comp_fst ν
  have i2 : Integrable (fun w : (ℝ × ℝ) × ℝ => w.1.2 ^ 2) ((μ₁.prod μ₂).prod ν) :=
    ((integrable_sq_gaussianReal _).comp_snd μ₁).comp_fst ν
  have i3 : Integrable (fun w : (ℝ × ℝ) × ℝ => w.2 ^ 2) ((μ₁.prod μ₂).prod ν) :=
    (integrable_sq_gaussianReal _).comp_snd (μ₁.prod μ₂)
  have j1 : Integrable (fun x : ℝ × ℝ => x.1) (μ₁.prod μ₂) :=
    (integrable_id_gaussianReal' _).comp_fst μ₂
  have j2 : Integrable (fun x : ℝ × ℝ => x.2) (μ₁.prod μ₂) :=
    (integrable_id_gaussianReal' _).comp_snd μ₁
  have i4 : Integrable (fun w : (ℝ × ℝ) × ℝ => w.1.1 * w.2) ((μ₁.prod μ₂).prod ν) :=
    j1.mul_prod (integrable_id_gaussianReal' _)
  have i5 : Integrable (fun w : (ℝ × ℝ) × ℝ => w.1.2 * w.2) ((μ₁.prod μ₂).prod ν) :=
    j2.mul_prod (integrable_id_gaussianReal' _)
  have i6 : Integrable (fun w : (ℝ × ℝ) × ℝ => w.1.1 * w.1.2) ((μ₁.prod μ₂).prod ν) :=
    ((integrable_id_gaussianReal' _).mul_prod (integrable_id_gaussianReal' _)).comp_fst ν
  have m1 : ∫ x : ℝ × ℝ, x.1 ∂(μ₁.prod μ₂) = 0 := by
    rw [integral_fun_fst (fun t => t)]
    simp [μ₁, integral_id_gaussianReal]
  have m2 : ∫ x : ℝ × ℝ, x.2 ∂(μ₁.prod μ₂) = 0 := by
    rw [integral_fun_snd (fun t => t)]
    simp [μ₂, integral_id_gaussianReal]
  have k1 : Integrable (fun w : (ℝ × ℝ) × ℝ => (1 - α) ^ 2 * w.1.2 ^ 2 + α ^ 2 * w.1.1 ^ 2)
      ((μ₁.prod μ₂).prod ν) := (i2.const_mul _).add (i1.const_mul _)
  have k2 : Integrable (fun w : (ℝ × ℝ) × ℝ =>
      (1 - α) ^ 2 * w.1.2 ^ 2 + α ^ 2 * w.1.1 ^ 2 + α ^ 2 * w.2 ^ 2) ((μ₁.prod μ₂).prod ν) :=
    k1.add (i3.const_mul _)
  have k3 : Integrable (fun w : (ℝ × ℝ) × ℝ =>
      2 * α ^ 2 * (w.1.1 * w.2) - 2 * α * (1 - α) * (w.1.2 * w.2)) ((μ₁.prod μ₂).prod ν) :=
    (i4.const_mul _).sub (i5.const_mul _)
  have k4 : Integrable (fun w : (ℝ × ℝ) × ℝ =>
      2 * α ^ 2 * (w.1.1 * w.2) - 2 * α * (1 - α) * (w.1.2 * w.2)
        - 2 * α * (1 - α) * (w.1.1 * w.1.2)) ((μ₁.prod μ₂).prod ν) :=
    k3.sub (i6.const_mul _)
  simp_rw [e]
  rw [integral_add k2 k4, integral_add k1 (i3.const_mul _), integral_add (i2.const_mul _)
      (i1.const_mul _), integral_sub k3 (i6.const_mul _),
    integral_sub (i4.const_mul _) (i5.const_mul _)]
  simp only [integral_const_mul]
  rw [integral_prod_mul (fun x : ℝ × ℝ => x.1) (fun t => t),
    integral_prod_mul (fun x : ℝ × ℝ => x.2) (fun t => t), m1, m2,
    integral_fun_fst (fun x : ℝ × ℝ => x.1 * x.2), integral_prod_mul (fun t => t) (fun t => t),
    integral_fun_fst (fun x : ℝ × ℝ => x.2 ^ 2), integral_fun_snd (fun t => t ^ 2),
    integral_fun_fst (fun x : ℝ × ℝ => x.1 ^ 2), integral_fun_fst (fun t => t ^ 2),
    integral_fun_snd (fun t => t ^ 2)]
  simp [μ₁, μ₂, ν, integral_sq_gaussianReal, integral_id_gaussianReal]
  ring

private lemma measurable_tin_sq (α : ℝ) (n : ℕ) :
    Measurable fun w : (ℝ × ℝ) × ℝ => (w.1.2 - α * value n (level n
      (value n (level n w.1.1) + value n (level n w.1.2) + w.2))) ^ 2 :=
  ((measurable_snd.comp measurable_fst).sub (((measurable_value_level n).comp
    ((((measurable_value_level n).comp (measurable_fst.comp measurable_fst)).add
      ((measurable_value_level n).comp (measurable_snd.comp measurable_fst))).add
        measurable_snd)).const_mul α)).pow_const 2

private lemma tin_sq_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) (w : (ℝ × ℝ) × ℝ) :
    (w.1.2 - α * value n (level n (value n (level n w.1.1) + value n (level n w.1.2) + w.2))) ^ 2
      ≤ 4 * w.1.1 ^ 2 + 16 * w.1.2 ^ 2 + 4 * w.2 ^ 2 + 36 := by
  set c := value n (level n (value n (level n w.1.1) + value n (level n w.1.2) + w.2))
  have hc1 := abs_value_level_le n w.1.1
  have hc2 := abs_value_level_le n w.1.2
  have hc : |c| ≤ |value n (level n w.1.1) + value n (level n w.1.2) + w.2| + 1 :=
    abs_value_level_le n _
  have hc3 := abs_add_le (value n (level n w.1.1) + value n (level n w.1.2)) w.2
  have hc4 := abs_add_le (value n (level n w.1.1)) (value n (level n w.1.2))
  have hαc : |α * c| ≤ |c| := by
    rw [abs_mul, abs_of_nonneg hα0]
    exact mul_le_of_le_one_left (abs_nonneg _) hα1
  have hM : |w.1.2 - α * c| ≤ |w.1.1| + 2 * |w.1.2| + |w.2| + 3 :=
    (abs_sub _ _).trans (by linarith)
  have h := pow_le_pow_left₀ (abs_nonneg _) hM 2
  rw [sq_abs] at h
  nlinarith [sq_abs w.1.1, sq_abs w.1.2, sq_abs w.2, sq_nonneg (|w.1.1| - 2 * |w.1.2|),
    sq_nonneg (|w.1.1| - |w.2|), sq_nonneg (|w.1.1| - 3), sq_nonneg (2 * |w.1.2| - |w.2|),
    sq_nonneg (2 * |w.1.2| - 3), sq_nonneg (|w.2| - 3)]

private lemma integrable_tin_bound (θ₁ θ₂ N : ℝ) :
    Integrable (fun w : (ℝ × ℝ) × ℝ => 4 * w.1.1 ^ 2 + 16 * w.1.2 ^ 2 + 4 * w.2 ^ 2 + 36)
      (((gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)).prod
        (gaussianReal 0 N.toNNReal)) :=
  (((((integrable_sq_gaussianReal _).comp_fst _).comp_fst _).const_mul 4).add
    ((((integrable_sq_gaussianReal _).comp_snd _).comp_fst _).const_mul 16) |>.add
    (((integrable_sq_gaussianReal _).comp_snd _).const_mul 4)).add (integrable_const _)

private lemma integrable_tin_sq (θ₁ θ₂ N : ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) :
    Integrable (fun w : (ℝ × ℝ) × ℝ =>
      (w.1.2 - α * value n (level n (value n (level n w.1.1) + value n (level n w.1.2) + w.2))) ^ 2)
      (((gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)).prod
        (gaussianReal 0 N.toNNReal)) :=
  (integrable_tin_bound θ₁ θ₂ N).mono' (measurable_tin_sq α n).aestronglyMeasurable
    (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact tin_sq_le hα0 hα1 n w)

private lemma tendsto_integral_tin_sq (θ₁ θ₂ N : ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    Tendsto (fun n => ∫ w, (w.1.2 - α * value n (level n (value n (level n w.1.1)
        + value n (level n w.1.2) + w.2))) ^ 2
      ∂((gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)).prod
        (gaussianReal 0 N.toNNReal)) atTop
      (𝓝 ((1 - α) ^ 2 * θ₂.toNNReal + α ^ 2 * (θ₁.toNNReal + N.toNNReal))) := by
  rw [← integral_tin_limit]
  refine tendsto_integral_of_dominated_convergence _
    (fun n => (measurable_tin_sq α n).aestronglyMeasurable) (integrable_tin_bound θ₁ θ₂ N)
    (fun n => ae_of_all _ fun w => ?_) (ae_of_all _ fun w => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact tin_sq_le hα0 hα1 n w
  · have h1 : Tendsto (fun n => value n (level n w.1.1)) atTop (𝓝 w.1.1) :=
      tendsto_value_level tendsto_const_nhds
    have h2 : Tendsto (fun n => value n (level n w.1.2)) atTop (𝓝 w.1.2) :=
      tendsto_value_level tendsto_const_nhds
    have h3 := tendsto_value_level ((h1.add h2).add_const w.2)
    exact (tendsto_const_nhds.sub (h3.const_mul α)).pow 2

theorem tinGain_eq {θ₁ θ₂ N : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hN : 0 < N) (n : ℕ) :
    tinGain θ₁ θ₂ N n = (1 / 2) * Real.log (θ₂ / (θ₂ * (θ₁ + N) / (θ₂ + (θ₁ + N)))) + 1 / 2
      - (∫ w, (w.1.2 - θ₂ / (θ₂ + (θ₁ + N)) * value n (level n (value n (level n w.1.1)
          + value n (level n w.1.2) + w.2))) ^ 2
          ∂((gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)).prod
            (gaussianReal 0 N.toNNReal))
        / (2 * (θ₂ * (θ₁ + N) / (θ₂ + (θ₁ + N)))) := by
  have hM : 0 < θ₁ + N := by linarith
  have hα0 : 0 ≤ θ₂ / (θ₂ + (θ₁ + N)) := by positivity
  have hα1 : θ₂ / (θ₂ + (θ₁ + N)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have h1 : Integrable (fun w : (ℝ × ℝ) × ℝ => w.1.2 ^ 2 / (2 * θ₂))
      (((gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)).prod
        (gaussianReal 0 N.toNNReal)) :=
    (((integrable_sq_gaussianReal _).comp_snd _).comp_fst _).div_const _
  have h2 : Integrable (fun w : (ℝ × ℝ) × ℝ =>
      (1 / 2) * Real.log (θ₂ / (θ₂ * (θ₁ + N) / (θ₂ + (θ₁ + N)))) + w.1.2 ^ 2 / (2 * θ₂))
      (((gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)).prod
        (gaussianReal 0 N.toNNReal)) :=
    (integrable_const _).add h1
  simp_rw [tinGain, log_letterRatio hθ₂ hM]
  rw [integral_sub h2 ((integrable_tin_sq θ₁ θ₂ N hα0 hα1 n).div_const _),
    integral_add (integrable_const _) h1, integral_div, integral_div,
    integral_fun_fst (fun x : ℝ × ℝ => x.2 ^ 2), integral_fun_snd (fun t => t ^ 2),
    integral_sq_gaussianReal]
  simp only [Real.coe_toNNReal _ hθ₂.le, probReal_univ, smul_eq_mul, one_mul, integral_const]
  field_simp

theorem tendsto_tinGain {θ₁ θ₂ N : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hN : 0 < N) :
    Tendsto (tinGain θ₁ θ₂ N) atTop (𝓝 (awgnCapacity θ₂ (θ₁ + N))) := by
  have hM : 0 < θ₁ + N := by linarith
  set M := θ₁ + N with hMdef
  have hα0 : 0 ≤ θ₂ / (θ₂ + M) := by positivity
  have hα1 : θ₂ / (θ₂ + M) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hL : (1 / 2) * Real.log (θ₂ / (θ₂ * M / (θ₂ + M))) + 1 / 2
      - ((1 - θ₂ / (θ₂ + M)) ^ 2 * (θ₂.toNNReal : ℝ)
        + (θ₂ / (θ₂ + M)) ^ 2 * ((θ₁.toNNReal : ℝ) + (N.toNNReal : ℝ)))
        / (2 * (θ₂ * M / (θ₂ + M))) = awgnCapacity θ₂ M := by
    rw [Real.coe_toNNReal _ hθ₁.le, Real.coe_toNNReal _ hθ₂.le, Real.coe_toNNReal _ hN.le,
      ← hMdef, awgnCapacity,
      show θ₂ / (θ₂ * M / (θ₂ + M)) = 1 + θ₂ / M by field_simp; ring,
      show ((1 - θ₂ / (θ₂ + M)) ^ 2 * θ₂ + (θ₂ / (θ₂ + M)) ^ 2 * M) / (2 * (θ₂ * M / (θ₂ + M)))
        = 1 / 2 by field_simp; ring]
    ring
  rw [← hL]
  exact Tendsto.congr (fun n => (tinGain_eq hθ₁ hθ₂ hN n).symm)
    (tendsto_const_nhds.sub ((tendsto_integral_tin_sq θ₁ θ₂ N hα0 hα1).div_const _))

private lemma integral_comp_of_measurePreserving' {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {f : α → β}
    (hf : MeasurePreserving f μ ν) {g : β → ℝ} (hg : AEStronglyMeasurable g ν) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := by
  rw [← hf.map_eq] at hg
  rw [← integral_map hf.measurable.aemeasurable hg, hf.map_eq]

private lemma abs_le_add_sq_div' {c : ℝ} (hc : 0 < c) (t : ℝ) : |t| ≤ c + t ^ 2 / c := by
  rw [← sq_abs t]
  have h : c * |t| ≤ c * c + |t| ^ 2 := by nlinarith [sq_nonneg (|t| - c), abs_nonneg t]
  rw [show c + |t| ^ 2 / c = (c * c + |t| ^ 2) / c by field_simp]
  rw [le_div_iff₀ hc]
  linarith

private lemma measurable_tinSummand (θ M : ℝ) (n L : ℕ) (P₁ P₂ : ℝ) (l : Fin L) :
    Measurable fun w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) =>
      Real.log (letterRatio θ M n (w.1.2 l)
        (level n (clipValue n L P₁ (fun k => level n (w.1.1 k)) l
          + clipValue n L P₂ (fun k => level n (w.1.2 k)) l + w.2 l))) :=
  measurable_log_letterRatio θ M n
    ((measurable_pi_apply l).comp (measurable_snd.comp measurable_fst))
    ((measurable_level n).comp (((((measurable_pi_apply l).comp
      (measurable_clipValue_level n L P₁)).comp (measurable_fst.comp measurable_fst)).add
      (((measurable_pi_apply l).comp (measurable_clipValue_level n L P₂)).comp
        (measurable_snd.comp measurable_fst))).add ((measurable_pi_apply l).comp measurable_snd)))

theorem integral_tinGain_ge {θ₁ θ₂ N : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hN : 0 < N)
    (n L : ℕ) (P₁ P₂ : ℝ) {c : ℝ} (hc : 0 < c) :
    L * tinGain θ₁ θ₂ N n - L * ((4 * n * c + 4 * n ^ 2)
        * ((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).real (badSet n L P₁)
          + (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal).real (badSet n L P₂))
        + 4 * n / c * θ₂) / (2 * (θ₂ * (θ₁ + N) / (θ₂ + (θ₁ + N))))
      ≤ ∫ t, ∫ z, ∑ l, Real.log (letterRatio θ₂ (θ₁ + N) n (t.2 l)
          (level n (clipValue n L P₁ (fun k => level n (t.1 k)) l
            + clipValue n L P₂ (fun k => level n (t.2 k)) l + z l))) ∂noise N L
        ∂((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
          (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal)) := by
  have hM : 0 < θ₁ + N := by linarith
  set M := θ₁ + N
  set μ₁ := gaussianReal 0 θ₁.toNNReal
  set μ₂ := gaussianReal 0 θ₂.toNNReal
  set ν := gaussianReal 0 N.toNNReal
  set μ₁L := Measure.pi fun _ : Fin L => μ₁
  set μ₂L := Measure.pi fun _ : Fin L => μ₂
  set νL := noise N L
  set s := θ₂ * M / (θ₂ + M)
  have hs : 0 < s := by positivity
  set A := 4 * n * c + 4 * (n : ℝ) ^ 2
  set G : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) → ℝ := fun w =>
    ∑ l, Real.log (letterRatio θ₂ M n (w.1.2 l)
      (level n (clipValue n L P₁ (fun k => level n (w.1.1 k)) l
        + clipValue n L P₂ (fun k => level n (w.1.2 k)) l + w.2 l)))
  set g : (ℝ × ℝ) × ℝ → ℝ := fun x => Real.log (letterRatio θ₂ M n x.1.2
    (level n (value n (level n x.1.1) + value n (level n x.1.2) + x.2)))
  set Gu : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) → ℝ := fun w =>
    ∑ l, g ((w.1.1 l, w.1.2 l), w.2 l)
  set ind : (Fin L → ℝ) × (Fin L → ℝ) → ℝ := fun t =>
    (badSet n L P₁).indicator 1 t.1 + (badSet n L P₂).indicator 1 t.2
  set E : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) → ℝ := fun w =>
    ∑ l, (A * ind w.1 + 4 * n / c * w.1.2 l ^ 2) / (2 * s)
  have hmp2 : ∀ l : Fin L, MeasurePreserving
      (fun w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) => ((w.1.1 l, w.1.2 l), w.2 l))
      ((μ₁L.prod μ₂L).prod νL) ((μ₁.prod μ₂).prod ν) := fun l =>
    ((measurePreserving_eval (fun _ : Fin L => μ₁) l).prod
      (measurePreserving_eval (fun _ : Fin L => μ₂) l)).prod
      (measurePreserving_eval (fun _ : Fin L => ν) l)
  have hg : Integrable g ((μ₁.prod μ₂).prod ν) :=
    integrable_log_letterRatio hθ₂ hM n (measurable_snd.comp measurable_fst)
      ((measurable_level n).comp ((((measurable_value_level n).comp
        (measurable_fst.comp measurable_fst)).add ((measurable_value_level n).comp
          (measurable_snd.comp measurable_fst))).add measurable_snd))
      (((integrable_sq_gaussianReal _).comp_snd _).comp_fst _)
  have hGu : Integrable Gu ((μ₁L.prod μ₂L).prod νL) :=
    integrable_finsetSum _ fun l _ => (hmp2 l).integrable_comp_of_integrable hg
  have hGu_eq : ∫ w, Gu w ∂((μ₁L.prod μ₂L).prod νL) = L * tinGain θ₁ θ₂ N n := by
    simp only [Gu]
    rw [integral_finsetSum (f := fun l (w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ)) =>
      g ((w.1.1 l, w.1.2 l), w.2 l)) _ fun l _ => (hmp2 l).integrable_comp_of_integrable hg]
    simp_rw [integral_comp_of_measurePreserving' (hmp2 _) hg.aestronglyMeasurable]
    simp [g, tinGain, μ₁, μ₂, ν, M]
  have hbad₁ := measurableSet_badSet n L P₁
  have hbad₂ := measurableSet_badSet n L P₂
  have hind : Integrable ind (μ₁L.prod μ₂L) :=
    (((integrable_const 1).indicator hbad₁).comp_fst μ₂L).add
      (((integrable_const 1).indicator hbad₂).comp_snd μ₁L)
  have hind_eq : ∫ t, ind t ∂(μ₁L.prod μ₂L)
      = μ₁L.real (badSet n L P₁) + μ₂L.real (badSet n L P₂) := by
    have i₁ : Integrable ((badSet n L P₁).indicator (1 : (Fin L → ℝ) → ℝ)) μ₁L :=
      (integrable_const (1 : ℝ)).indicator hbad₁
    have i₂ : Integrable ((badSet n L P₂).indicator (1 : (Fin L → ℝ) → ℝ)) μ₂L :=
      (integrable_const (1 : ℝ)).indicator hbad₂
    simp only [ind]
    rw [integral_add (i₁.comp_fst μ₂L) (i₂.comp_snd μ₁L),
      integral_fun_fst ((badSet n L P₁).indicator (1 : (Fin L → ℝ) → ℝ)),
      integral_fun_snd ((badSet n L P₂).indicator (1 : (Fin L → ℝ) → ℝ)),
      integral_indicator_one hbad₁, integral_indicator_one hbad₂]
    simp
  have hsq : ∀ l : Fin L, Integrable (fun w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) =>
      w.1.2 l ^ 2) ((μ₁L.prod μ₂L).prod νL) := fun l =>
    ((((measurePreserving_eval (fun _ : Fin L => μ₂) l).integrable_comp_of_integrable
      (integrable_sq_gaussianReal _)).comp_snd μ₁L).comp_fst νL)
  have hsq_eq : ∀ l : Fin L, ∫ w, w.1.2 l ^ 2 ∂((μ₁L.prod μ₂L).prod νL) = θ₂ := fun l => by
    rw [integral_fun_fst (fun t : (Fin L → ℝ) × (Fin L → ℝ) => t.2 l ^ 2),
      integral_fun_snd (fun t : Fin L → ℝ => t l ^ 2),
      integral_comp_of_measurePreserving' (measurePreserving_eval (fun _ : Fin L => μ₂) l)
        (by fun_prop : AEStronglyMeasurable (fun t : ℝ => t ^ 2) μ₂), integral_sq_gaussianReal]
    simp [Real.coe_toNNReal _ hθ₂.le]
  have hE : Integrable E ((μ₁L.prod μ₂L).prod νL) :=
    integrable_finsetSum _ fun l _ =>
      (((hind.comp_fst νL).const_mul _).add ((hsq l).const_mul _)).div_const _
  have hE_eq : ∫ w, E w ∂((μ₁L.prod μ₂L).prod νL)
      = L * (A * (μ₁L.real (badSet n L P₁) + μ₂L.real (badSet n L P₂)) + 4 * n / c * θ₂)
        / (2 * s) := by
    have h1 : ∀ l : Fin L, ∫ w, (A * ind w.1 + 4 * n / c * w.1.2 l ^ 2) / (2 * s)
        ∂((μ₁L.prod μ₂L).prod νL)
        = (A * (μ₁L.real (badSet n L P₁) + μ₂L.real (badSet n L P₂)) + 4 * n / c * θ₂)
          / (2 * s) := by
      intro l
      rw [integral_div, integral_add ((hind.comp_fst νL).const_mul _) ((hsq l).const_mul _),
        integral_const_mul, integral_const_mul, integral_fun_fst ind, hind_eq, hsq_eq]
      simp
    simp only [E]
    rw [integral_finsetSum (f := fun l (w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ)) =>
      (A * ind w.1 + 4 * n / c * w.1.2 l ^ 2) / (2 * s)) _ fun l _ =>
      (((hind.comp_fst νL).const_mul _).add ((hsq l).const_mul _)).div_const _]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hGm : Measurable G :=
    Finset.measurable_sum _ fun l _ => measurable_tinSummand θ₂ M n L P₁ P₂ l
  have hpt : ∀ w, |G w - Gu w| ≤ E w := by
    intro w
    simp only [G, Gu, E, g, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    have hind0 : 0 ≤ ind w.1 := add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    by_cases hw : w.1.1 ∉ badSet n L P₁ ∧ w.1.2 ∉ badSet n L P₂
    · rw [clipValue_of_notMem_badSet hw.1, clipValue_of_notMem_badSet hw.2, sub_self, abs_zero]
      positivity
    · have hi : 1 ≤ ind w.1 := by
        rcases not_and_or.1 hw with h | h
        · have := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := badSet n L P₂)
            (f := (1 : (Fin L → ℝ) → ℝ)) w.1.2
          simp only [ind, Set.indicator_of_mem (not_not.1 h), Pi.one_apply]
          linarith
        · have := Set.indicator_nonneg (fun _ _ => zero_le_one) (s := badSet n L P₁)
            (f := (1 : (Fin L → ℝ) → ℝ)) w.1.1
          simp only [ind, Set.indicator_of_mem (not_not.1 h), Pi.one_apply]
          linarith
      refine (abs_log_letterRatio_sub_le hθ₂ hM n _ _ _).trans ?_
      rw [div_le_div_iff_of_pos_right (by positivity)]
      have := abs_le_add_sq_div' hc (w.1.2 l)
      have h4 : (4 * n : ℝ) * |w.1.2 l| ≤ 4 * n * (c + w.1.2 l ^ 2 / c) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      have h5 : 4 * n / c * w.1.2 l ^ 2 = 4 * n * (w.1.2 l ^ 2 / c) := by ring
      have hA : 0 ≤ A := by positivity
      nlinarith
  have hdiff : Integrable (fun w => G w - Gu w) ((μ₁L.prod μ₂L).prod νL) :=
    hE.mono' (hGm.aestronglyMeasurable.sub hGu.aestronglyMeasurable)
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hpt w)
  have hG : Integrable G ((μ₁L.prod μ₂L).prod νL) :=
    (hGu.add hdiff).congr (ae_of_all _ fun w => by simp)
  have hprod := integral_prod G hG
  simp only [G] at hprod
  rw [← hprod, ← hGu_eq, ← hE_eq, ← integral_sub hGu hE]
  exact integral_mono (hGu.sub hE) hG fun w => by
    have := hpt w
    simp only
    linarith [neg_abs_le (G w - Gu w)]

end GaussianMAC

end Meat
