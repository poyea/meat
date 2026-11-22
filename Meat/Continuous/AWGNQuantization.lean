import Mathlib.MeasureTheory.Function.Floor
import Meat.Continuous.InfoBound
import Meat.Continuous.AWGNAchievability

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Meat

namespace AWGN

abbrev Level (n : ℕ) := {k : ℤ // k ∈ Finset.Icc (-((n : ℤ) ^ 2)) ((n : ℤ) ^ 2)}

noncomputable def level (n : ℕ) (y : ℝ) : Level n :=
  ⟨max (-((n : ℤ) ^ 2)) (min ((n : ℤ) ^ 2) ⌊y * n⌋),
    Finset.mem_Icc.2 ⟨le_max_left _ _, max_le (neg_le_self (by positivity)) (min_le_left _ _)⟩⟩

noncomputable def value (n : ℕ) (k : Level n) : ℝ := (k.1 : ℝ) / n

theorem measurable_level (n : ℕ) : Measurable (level n) :=
  ((Measurable.of_discrete (f := fun m : ℤ => max (-((n : ℤ) ^ 2)) (min ((n : ℤ) ^ 2) m))).comp
    (Int.measurable_floor.comp (measurable_id.mul_const _))).subtype_mk

theorem measurable_value_level (n : ℕ) : Measurable fun y => value n (level n y) :=
  (measurable_of_finite (value n)).comp (measurable_level n)

private lemma value_level_eq (n : ℕ) (y : ℝ) :
    value n (level n y) = max (-((n : ℝ) ^ 2)) (min ((n : ℝ) ^ 2) (⌊y * n⌋ : ℝ)) / n := by
  simp [value, level]

theorem abs_value_le (n : ℕ) (k : Level n) : |value n k| ≤ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [value]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 k.2
  have h1' : -((n : ℝ) ^ 2) ≤ (k.1 : ℝ) := by exact_mod_cast h1
  have h2' : (k.1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast h2
  rw [value, abs_div, abs_of_pos hn', div_le_iff₀ hn', abs_le]
  constructor <;> nlinarith

theorem abs_value_level_le (n : ℕ) (y : ℝ) : |value n (level n y)| ≤ |y| + 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa [value] using add_nonneg (abs_nonneg y) zero_le_one
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
  have h1 := Int.floor_le (y * n)
  have h2 := Int.lt_floor_add_one (y * n)
  have hy1 := neg_abs_le y
  have hy2 := le_abs_self y
  have hk : |max (-((n : ℝ) ^ 2)) (min ((n : ℝ) ^ 2) (⌊y * n⌋ : ℝ))| ≤ |y| * n + 1 := by
    rw [abs_le]
    constructor
    · exact le_max_of_le_right (le_min (by nlinarith [abs_nonneg y]) (by nlinarith))
    · exact max_le (by nlinarith [abs_nonneg y]) ((min_le_right _ _).trans (by nlinarith))
  rw [value_level_eq, abs_div, abs_of_pos hn', div_le_iff₀ hn']
  nlinarith [abs_nonneg y]

theorem abs_value_level_sub_le {n : ℕ} {y : ℝ} (hy : |y| + 1 ≤ n) :
    |value n (level n y) - y| ≤ 1 / n := by
  have hn1 : (1 : ℝ) ≤ n := by linarith [abs_nonneg y]
  have hn' : (0 : ℝ) < n := by linarith
  have h1 := Int.floor_le (y * n)
  have h2 := Int.lt_floor_add_one (y * n)
  have hy1 := neg_abs_le y
  have hy2 := le_abs_self y
  have hya : |y| ≤ n - 1 := by linarith
  have hlo : -((n : ℝ) ^ 2) ≤ (⌊y * n⌋ : ℝ) := by nlinarith
  have hhi : (⌊y * n⌋ : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  rw [value_level_eq, min_eq_right hhi, max_eq_right hlo,
    show (⌊y * n⌋ : ℝ) / n - y = ((⌊y * n⌋ : ℝ) - y * n) / n by field_simp, abs_div,
    abs_of_pos hn', div_le_div_iff_of_pos_right hn', abs_le]
  constructor <;> linarith

theorem tendsto_value_level {y : ℕ → ℝ} {y₀ : ℝ} (hy : Tendsto y atTop (𝓝 y₀)) :
    Tendsto (fun n => value n (level n (y n))) atTop (𝓝 y₀) := by
  have h1 : ∀ᶠ n in atTop, |y n| < |y₀| + 1 :=
    (hy.abs).eventually (gt_mem_nhds (by linarith))
  have h2 : ∀ᶠ n : ℕ in atTop, |y₀| + 2 ≤ n :=
    (eventually_ge_atTop ⌈|y₀| + 2⌉₊).mono fun n hn => (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h3 : Tendsto (fun n => value n (level n (y n)) - y n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_one_div_atTop_nhds_zero_nat
    filter_upwards [h1, h2] with n hn1 hn2
    rw [Real.norm_eq_abs]
    exact abs_value_level_sub_le (by linarith)
  simpa using h3.add hy

noncomputable def postRatio (θ s m t : ℝ) : ℝ :=
  gaussianPDFReal m s.toNNReal t / gaussianPDFReal 0 θ.toNNReal t

private lemma toNNReal_ne_zero {x : ℝ} (hx : 0 < x) : x.toNNReal ≠ 0 := by
  simpa using hx

theorem postRatio_pos {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) (m t : ℝ) : 0 < postRatio θ s m t :=
  div_pos (gaussianPDFReal_pos _ _ _ (toNNReal_ne_zero hs))
    (gaussianPDFReal_pos _ _ _ (toNNReal_ne_zero hθ))

theorem log_postRatio {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) (m t : ℝ) :
    Real.log (postRatio θ s m t)
      = (1 / 2) * Real.log (θ / s) + t ^ 2 / (2 * θ) - (t - m) ^ 2 / (2 * s) := by
  have h1 := neg_log_gaussianPDFReal m (toNNReal_ne_zero hs) t
  have h2 := neg_log_gaussianPDFReal 0 (toNNReal_ne_zero hθ) t
  rw [Real.coe_toNNReal _ hs.le] at h1
  rw [Real.coe_toNNReal _ hθ.le] at h2
  rw [postRatio, Real.log_div (gaussianPDFReal_pos _ _ _ (toNNReal_ne_zero hs)).ne'
      (gaussianPDFReal_pos _ _ _ (toNNReal_ne_zero hθ)).ne',
    Real.log_div hθ.ne' hs.ne']
  rw [Real.log_mul (by positivity) hs.ne'] at h1
  rw [Real.log_mul (by positivity) hθ.ne'] at h2
  simp only [sub_zero] at h2
  linarith

theorem integral_postRatio {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) (m : ℝ) :
    ∫ t, postRatio θ s m t ∂gaussianReal 0 θ.toNNReal = 1 := by
  rw [integral_gaussianReal_eq_integral_smul (toNNReal_ne_zero hθ)]
  simp_rw [smul_eq_mul, postRatio,
    mul_div_cancel₀ _ (gaussianPDFReal_pos _ _ _ (toNNReal_ne_zero hθ)).ne']
  exact integral_gaussianPDFReal_eq_one m (toNNReal_ne_zero hs)

private lemma integrable_sub_sq_gaussianReal (v : ℝ≥0) (m : ℝ) :
    Integrable (fun t => (t - m) ^ 2) (gaussianReal 0 v) :=
  ((memLp_id_gaussianReal' 2 (by simp)).sub (memLp_const m)).integrable_sq

theorem integrable_sq_gaussianReal (v : ℝ≥0) :
    Integrable (fun t => t ^ 2) (gaussianReal 0 v) := by
  simpa using integrable_sub_sq_gaussianReal v 0

theorem integral_sq_gaussianReal (v : ℝ≥0) : ∫ t, t ^ 2 ∂gaussianReal 0 v = v := by
  have := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at this
  simpa using this

theorem integrable_log_postRatio {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) (m : ℝ) :
    Integrable (fun t => Real.log (postRatio θ s m t)) (gaussianReal 0 θ.toNNReal) :=
  (((integrable_const _).add ((integrable_sq_gaussianReal _).div_const _)).sub
    ((integrable_sub_sq_gaussianReal _ m).div_const _)).congr
    (ae_of_all _ fun t => (log_postRatio hθ hs m t).symm)

private lemma integrable_id_gaussianReal (v : ℝ≥0) :
    Integrable (fun t : ℝ => t) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal' 1 (by simp)).integrable le_rfl

theorem tendsto_integral_sq_value_level (θ : ℝ) :
    Tendsto (fun n => ∫ t, value n (level n t) ^ 2 ∂gaussianReal 0 θ.toNNReal) atTop
      (𝓝 (θ.toNNReal : ℝ)) := by
  rw [← integral_sq_gaussianReal]
  refine tendsto_integral_of_dominated_convergence (fun t => 2 * t ^ 2 + 2)
    (fun n => ((measurable_value_level n).pow_const 2).aestronglyMeasurable)
    (((integrable_sq_gaussianReal _).const_mul 2).add (integrable_const 2))
    (fun n => ae_of_all _ fun t => ?_)
    (ae_of_all _ fun t => (tendsto_value_level tendsto_const_nhds).pow 2)
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (abs_value_level_le n t) 2
  rw [sq_abs] at h1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs t, sq_nonneg (|t| - 1)]

theorem integral_post_limit (θ N α : ℝ) :
    ∫ w, (w.1 - α * (w.1 + w.2)) ^ 2
        ∂(gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 N.toNNReal)
      = (1 - α) ^ 2 * θ.toNNReal + α ^ 2 * N.toNNReal := by
  set μ := gaussianReal 0 θ.toNNReal
  set ν := gaussianReal 0 N.toNNReal
  have e : ∀ w : ℝ × ℝ, (w.1 - α * (w.1 + w.2)) ^ 2
      = ((1 - α) ^ 2 * w.1 ^ 2 + α ^ 2 * w.2 ^ 2) - 2 * α * (1 - α) * (w.1 * w.2) :=
    fun w => by ring
  have h1 : Integrable (fun w : ℝ × ℝ => w.1 ^ 2) (μ.prod ν) :=
    (integrable_sq_gaussianReal _).comp_fst ν
  have h2 : Integrable (fun w : ℝ × ℝ => w.2 ^ 2) (μ.prod ν) :=
    (integrable_sq_gaussianReal _).comp_snd μ
  have h3 : Integrable (fun w : ℝ × ℝ => w.1 * w.2) (μ.prod ν) :=
    (integrable_id_gaussianReal _).mul_prod (integrable_id_gaussianReal _)
  have h12 : Integrable (fun w : ℝ × ℝ => (1 - α) ^ 2 * w.1 ^ 2 + α ^ 2 * w.2 ^ 2) (μ.prod ν) :=
    (h1.const_mul _).add (h2.const_mul _)
  simp_rw [e]
  rw [integral_sub h12 (h3.const_mul _),
    integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_fun_fst (fun t => t ^ 2), integral_fun_snd (fun t => t ^ 2),
    integral_prod_mul (fun t => t) (fun t => t)]
  simp [μ, ν, integral_sq_gaussianReal, integral_id_gaussianReal]

private lemma measurable_post_sq (α : ℝ) (n : ℕ) :
    Measurable fun w : ℝ × ℝ => (w.1 - α * value n (level n (value n (level n w.1) + w.2))) ^ 2 :=
  (measurable_fst.sub (((measurable_value_level n).comp
    (((measurable_value_level n).comp measurable_fst).add measurable_snd)).const_mul α)).pow_const 2

private lemma post_sq_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) (w : ℝ × ℝ) :
    (w.1 - α * value n (level n (value n (level n w.1) + w.2))) ^ 2
      ≤ 12 * w.1 ^ 2 + 3 * w.2 ^ 2 + 12 := by
  set c := value n (level n (value n (level n w.1) + w.2))
  have hc1 := abs_value_level_le n w.1
  have hc2 : |c| ≤ |value n (level n w.1) + w.2| + 1 := abs_value_level_le n _
  have hc3 := abs_add_le (value n (level n w.1)) w.2
  have hαc : |α * c| ≤ |c| := by
    rw [abs_mul, abs_of_nonneg hα0]
    exact mul_le_of_le_one_left (abs_nonneg _) hα1
  have hM : |w.1 - α * c| ≤ 2 * |w.1| + |w.2| + 2 := (abs_sub _ _).trans (by linarith)
  have h := pow_le_pow_left₀ (abs_nonneg _) hM 2
  rw [sq_abs] at h
  nlinarith [sq_abs w.1, sq_abs w.2, sq_nonneg (2 * |w.1| - |w.2|), sq_nonneg (|w.2| - 2),
    sq_nonneg (2 * |w.1| - 2)]

private lemma integrable_bound_prod (θ N : ℝ) :
    Integrable (fun w : ℝ × ℝ => 12 * w.1 ^ 2 + 3 * w.2 ^ 2 + 12)
      ((gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 N.toNNReal)) :=
  ((((integrable_sq_gaussianReal _).comp_fst _).const_mul 12).add
    (((integrable_sq_gaussianReal _).comp_snd _).const_mul 3)).add (integrable_const _)

theorem integrable_post_sq (θ N : ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) :
    Integrable (fun w : ℝ × ℝ => (w.1 - α * value n (level n (value n (level n w.1) + w.2))) ^ 2)
      ((gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 N.toNNReal)) :=
  (integrable_bound_prod θ N).mono' (measurable_post_sq α n).aestronglyMeasurable
    (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact post_sq_le hα0 hα1 n w)

theorem tendsto_integral_post_sq (θ N : ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    Tendsto (fun n => ∫ w, (w.1 - α * value n (level n (value n (level n w.1) + w.2))) ^ 2
      ∂(gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 N.toNNReal)) atTop
      (𝓝 ((1 - α) ^ 2 * θ.toNNReal + α ^ 2 * N.toNNReal)) := by
  rw [← integral_post_limit]
  refine tendsto_integral_of_dominated_convergence _
    (fun n => (measurable_post_sq α n).aestronglyMeasurable) (integrable_bound_prod θ N)
    (fun n => ae_of_all _ fun w => ?_) (ae_of_all _ fun w => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact post_sq_le hα0 hα1 n w
  · have h1 : Tendsto (fun n => value n (level n w.1)) atTop (𝓝 w.1) :=
      tendsto_value_level tendsto_const_nhds
    have h2 := tendsto_value_level (h1.add_const w.2)
    exact (tendsto_const_nhds.sub (h2.const_mul α)).pow 2

noncomputable def letterRatio (θ N : ℝ) (n : ℕ) (t : ℝ) (b : Level n) : ℝ :=
  postRatio θ (θ * N / (θ + N)) (θ / (θ + N) * value n b) t

noncomputable def letterGain (θ N : ℝ) (n : ℕ) : ℝ :=
  ∫ w, Real.log (letterRatio θ N n w.1 (level n (value n (level n w.1) + w.2)))
    ∂(gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 N.toNNReal)

theorem log_letterRatio {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n : ℕ) (t : ℝ) (b : Level n) :
    Real.log (letterRatio θ N n t b)
      = (1 / 2) * Real.log (θ / (θ * N / (θ + N))) + t ^ 2 / (2 * θ)
        - (t - θ / (θ + N) * value n b) ^ 2 / (2 * (θ * N / (θ + N))) :=
  log_postRatio hθ (by positivity) _ t

theorem letterGain_eq {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n : ℕ) :
    letterGain θ N n = (1 / 2) * Real.log (θ / (θ * N / (θ + N))) + 1 / 2
      - (∫ w, (w.1 - θ / (θ + N) * value n (level n (value n (level n w.1) + w.2))) ^ 2
          ∂(gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 N.toNNReal))
        / (2 * (θ * N / (θ + N))) := by
  have hα0 : 0 ≤ θ / (θ + N) := by positivity
  have hα1 : θ / (θ + N) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have h1 : Integrable (fun w : ℝ × ℝ => w.1 ^ 2 / (2 * θ))
      ((gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 N.toNNReal)) :=
    ((integrable_sq_gaussianReal _).comp_fst _).div_const _
  have h2 : Integrable (fun w : ℝ × ℝ => (1 / 2) * Real.log (θ / (θ * N / (θ + N)))
      + w.1 ^ 2 / (2 * θ)) ((gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 N.toNNReal)) :=
    (integrable_const _).add h1
  simp_rw [letterGain, log_letterRatio hθ hN]
  rw [integral_sub h2
      ((integrable_post_sq θ N hα0 hα1 n).div_const _),
    integral_add (integrable_const _) h1, integral_div, integral_div,
    integral_fun_fst (fun t => t ^ 2), integral_sq_gaussianReal]
  simp only [Real.coe_toNNReal _ hθ.le, probReal_univ, smul_eq_mul, one_mul, integral_const]
  field_simp

theorem tendsto_letterGain {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) :
    Tendsto (letterGain θ N) atTop (𝓝 (awgnCapacity θ N)) := by
  have hα0 : 0 ≤ θ / (θ + N) := by positivity
  have hα1 : θ / (θ + N) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hL : (1 / 2) * Real.log (θ / (θ * N / (θ + N))) + 1 / 2
      - ((1 - θ / (θ + N)) ^ 2 * (θ.toNNReal : ℝ) + (θ / (θ + N)) ^ 2 * (N.toNNReal : ℝ))
        / (2 * (θ * N / (θ + N))) = awgnCapacity θ N := by
    rw [Real.coe_toNNReal _ hθ.le, Real.coe_toNNReal _ hN.le, awgnCapacity,
      show θ / (θ * N / (θ + N)) = 1 + θ / N by field_simp; ring,
      show ((1 - θ / (θ + N)) ^ 2 * θ + (θ / (θ + N)) ^ 2 * N) / (2 * (θ * N / (θ + N)))
        = 1 / 2 by field_simp; ring]
    ring
  rw [← hL]
  exact Tendsto.congr (fun n => (letterGain_eq hθ hN n).symm)
    (tendsto_const_nhds.sub ((tendsto_integral_post_sq θ N hα0 hα1).div_const _))

end AWGN

end Meat
