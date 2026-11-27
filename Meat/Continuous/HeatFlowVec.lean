import Meat.Continuous.Stam

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Meat

variable {n : ℕ}

noncomputable def heatKernelVec (s : ℝ) (u : Fin n → ℝ) : ℝ :=
  ∏ i, heatKernel s (u i)

theorem heatKernelVec_pos {s : ℝ} (hs : 0 < s) (u : Fin n → ℝ) : 0 < heatKernelVec s u :=
  Finset.prod_pos fun i _ => heatKernel_pos hs (u i)

theorem continuous_heatKernelVec (s : ℝ) : Continuous (heatKernelVec (n := n) s) :=
  continuous_finsetProd _ fun i _ => (continuous_heatKernel s).comp (continuous_apply i)

theorem heatKernelVec_le {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (u : Fin n → ℝ) :
    heatKernelVec s u
      ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ ^ n * Real.exp (-(1 / (2 * b)) * ∑ i, u i ^ 2) := by
  have hs : 0 < s := ha.trans_le has
  calc heatKernelVec s u
      ≤ ∏ i, ((Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (-(1 / (2 * b)) * u i ^ 2)) :=
        Finset.prod_le_prod₀ (fun i _ => (heatKernel_pos hs _).le)
          fun i _ => heatKernel_le ha has hsb _
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← Real.exp_sum, Finset.mul_sum]

theorem heatKernelVec_le_const {s : ℝ} (hs : 0 < s) (u : Fin n → ℝ) :
    heatKernelVec s u ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ ^ n := by
  calc heatKernelVec s u ≤ ∏ _i : Fin n, (Real.sqrt (2 * Real.pi * s))⁻¹ :=
        Finset.prod_le_prod₀ (fun i _ => (heatKernel_pos hs _).le)
          fun i _ => heatKernel_le_const hs _
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem heatKernelVec_update (s : ℝ) (u : Fin n → ℝ) (i : Fin n) (r : ℝ) :
    heatKernelVec s (Function.update u i r)
      = heatKernel s r * ∏ j ∈ {i}ᶜ, heatKernel s (u j) := by
  classical
  rw [heatKernelVec, Fintype.prod_eq_mul_prod_compl i, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (by simpa using hj)]

theorem update_sub_eq (x y : Fin n → ℝ) (i : Fin n) (r : ℝ) :
    Function.update x i r - y = Function.update (x - y) i (r - y i) := by
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem hasDerivAt_heatKernelVec_update (s : ℝ) (x y : Fin n → ℝ) (i : Fin n) (r : ℝ) :
    HasDerivAt (fun r => heatKernelVec s (Function.update x i r - y))
      (-((Function.update x i r - y) i / s) * heatKernelVec s (Function.update x i r - y)) r := by
  classical
  simp_rw [update_sub_eq, heatKernelVec_update, Function.update_self]
  have h := ((hasDerivAt_heatKernel s (r - y i)).comp_sub_const r (y i)).mul_const
    (∏ j ∈ {i}ᶜ, heatKernel s ((x - y) j))
  convert h using 1
  ring

theorem hasDerivAt_heatKernelVec_update_deriv (s : ℝ) (x y : Fin n → ℝ) (i : Fin n) (r : ℝ) :
    HasDerivAt
      (fun r => -((Function.update x i r - y) i / s) * heatKernelVec s (Function.update x i r - y))
      (((Function.update x i r - y) i ^ 2 / s ^ 2 - 1 / s) *
        heatKernelVec s (Function.update x i r - y)) r := by
  classical
  simp_rw [update_sub_eq, heatKernelVec_update, Function.update_self]
  have h := ((hasDerivAt_heatKernel_deriv s (r - y i)).comp_sub_const r (y i)).mul_const
    (∏ j ∈ {i}ᶜ, heatKernel s ((x - y) j))
  convert h using 1
  · ext r'
    ring
  · ring

theorem hasDerivAt_heatKernelVec_time {s : ℝ} (hs : 0 < s) (u : Fin n → ℝ) :
    HasDerivAt (fun s => heatKernelVec s u)
      ((∑ i, (u i ^ 2 / s ^ 2 - 1 / s)) / 2 * heatKernelVec s u) s := by
  classical
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s => heatKernel s (u i))
    (x := s) fun i _ => hasDerivAt_heatKernel_time hs (u i)
  convert h using 1
  · rfl
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, heatKernelVec, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  ring

private lemma heatPoly_le_vec {a c : ℝ} {u : Fin n → ℝ} {i : Fin n}
    (h : |c| ≤ (1 + 1 / a) ^ 2 * (1 + u i ^ 2)) :
    |c| ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2) := by
  have h1 : u i ^ 2 ≤ ∑ j, u j ^ 2 :=
    Finset.single_le_sum (f := fun j => u j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h3 : 0 ≤ (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  calc |c| ≤ (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2) :=
        h.trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _))
    _ ≤ _ := by nlinarith

theorem heatPolyVec_one {a : ℝ} (ha : 0 < a) (u : Fin n → ℝ) :
    |(1 : ℝ)| ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2) := by
  have h0 : 0 ≤ ∑ j, u j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h := heatPoly_one ha 0
  have h2 : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h3 : 0 ≤ (1 + 1 / a) ^ 2 := sq_nonneg _
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_one] at h
  have h4 : (1 + 1 / a) ^ 2 ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2) := by
    nlinarith [mul_nonneg h3 h0, mul_nonneg (mul_nonneg h3 h0) (by linarith : (0 : ℝ) ≤ n)]
  linarith

theorem heatPolyVec_deriv {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (u : Fin n → ℝ) (i : Fin n) :
    |-(u i / s)| ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2) :=
  heatPoly_le_vec (heatPoly_deriv ha has (u i))

theorem heatPolyVec_deriv2 {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (u : Fin n → ℝ) (i : Fin n) :
    |u i ^ 2 / s ^ 2 - 1 / s| ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2) :=
  heatPoly_le_vec (heatPoly_deriv2 ha has (u i))

theorem heatPolyVec_sq {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (u : Fin n → ℝ) (i : Fin n) :
    |u i ^ 2 / s ^ 2| ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2) :=
  heatPoly_le_vec (heatPoly_sq ha has (u i))

theorem heatPolyVec_time {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (u : Fin n → ℝ) :
    |(∑ i, (u i ^ 2 / s ^ 2 - 1 / s)) / 2| ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2) := by
  have h0 : 0 ≤ ∑ j, u j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h3 : 0 ≤ (1 + 1 / a) ^ 2 := sq_nonneg _
  have hsum : |∑ i, (u i ^ 2 / s ^ 2 - 1 / s)| ≤ ∑ i, (1 + 1 / a) ^ 2 * (1 + u i ^ 2) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => heatPoly_deriv2 ha has (u i))
  have he : ∑ i, (1 + 1 / a) ^ 2 * (1 + u i ^ 2) = (1 + 1 / a) ^ 2 * (n + ∑ i, u i ^ 2) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp
  rw [he] at hsum
  rw [abs_div, abs_two]
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have h5 : (1 + 1 / a) ^ 2 * (n + ∑ i, u i ^ 2)
      ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2) := by
    nlinarith [mul_nonneg h3 h0, mul_nonneg (mul_nonneg h3 h0) hn, mul_nonneg h3 hn]
  have := abs_nonneg (∑ i, (u i ^ 2 / s ^ 2 - 1 / s))
  have h6 : 0 ≤ (1 + 1 / a) ^ 2 * (n + ∑ i, u i ^ 2) := mul_nonneg h3 (by linarith)
  linarith

noncomputable def heatEnvelopeVec (a b : ℝ) (u : Fin n → ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * a))⁻¹ ^ n * ((n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ i, u i ^ 2)) *
    Real.exp (-(1 / (2 * b)) * ∑ i, u i ^ 2)

theorem heatEnvelopeVec_nonneg (a b : ℝ) (u : Fin n → ℝ) : 0 ≤ heatEnvelopeVec a b u := by
  unfold heatEnvelopeVec
  have : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  positivity

theorem continuous_heatEnvelopeVec (a b : ℝ) : Continuous (heatEnvelopeVec (n := n) a b) := by
  unfold heatEnvelopeVec
  fun_prop

theorem abs_mul_heatKernelVec_le {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    {c : ℝ} {u : Fin n → ℝ} (hc : |c| ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2)) :
    |c * heatKernelVec s u| ≤ heatEnvelopeVec a b u := by
  have hk := heatKernelVec_pos (ha.trans_le has) u
  rw [abs_mul, abs_of_pos hk, heatEnvelopeVec]
  have := heatKernelVec_le ha has hsb u
  have h0 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  calc |c| * heatKernelVec s u
      ≤ ((n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2)) *
        ((Real.sqrt (2 * Real.pi * a))⁻¹ ^ n * Real.exp (-(1 / (2 * b)) * ∑ i, u i ^ 2)) :=
        mul_le_mul hc this hk.le (by positivity)
    _ = _ := by ring

private lemma mul_exp_neg_le {b t : ℝ} (hb : 0 < b) :
    t * Real.exp (-(1 / (2 * b)) * t) ≤ 2 * b := by
  have h := Real.add_one_le_exp (1 / (2 * b) * t)
  have hpos := Real.exp_pos (1 / (2 * b) * t)
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  have e : t = 2 * b * (1 / (2 * b) * t) := by field_simp
  calc t = 2 * b * (1 / (2 * b) * t) := e
    _ ≤ 2 * b * Real.exp (1 / (2 * b) * t) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith

theorem heatEnvelopeVec_le {a b : ℝ} (hb : 0 < b) (u : Fin n → ℝ) :
    heatEnvelopeVec a b u
      ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ ^ n * ((n + 1) * (1 + 1 / a) ^ 2) * (1 + 2 * b) := by
  unfold heatEnvelopeVec
  set S := ∑ i, u i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hx := mul_exp_neg_le (t := S) hb
  have he : Real.exp (-(1 / (2 * b)) * S) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 1 / (2 * b) * S := by positivity
    linarith
  have hC : 0 ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ ^ n * ((n + 1) * (1 + 1 / a) ^ 2) := by
    positivity
  calc (Real.sqrt (2 * Real.pi * a))⁻¹ ^ n * ((n + 1) * (1 + 1 / a) ^ 2 * (1 + S)) *
        Real.exp (-(1 / (2 * b)) * S)
      = (Real.sqrt (2 * Real.pi * a))⁻¹ ^ n * ((n + 1) * (1 + 1 / a) ^ 2) *
        (Real.exp (-(1 / (2 * b)) * S) + S * Real.exp (-(1 / (2 * b)) * S)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hC

theorem integrable_exp_neg_mul_sum_sq {c : ℝ} (hc : 0 < c) :
    Integrable fun u : Fin n → ℝ => Real.exp (-c * ∑ i, u i ^ 2) := by
  have h := Integrable.fintype_prod (f := fun (_ : Fin n) (x : ℝ) => Real.exp (-c * x ^ 2))
    (μ := fun _ => volume) fun _ => integrable_exp_neg_mul_sq hc
  rw [← volume_pi] at h
  refine h.congr (ae_of_all _ fun u => ?_)
  simp only
  rw [Finset.mul_sum, Real.exp_sum]

private lemma one_add_le_exp {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    1 + t ≤ (1 + 4 / c) * Real.exp (c / 4 * t) := by
  have h := Real.add_one_le_exp (c / 4 * t)
  have h1 : 1 ≤ Real.exp (c / 4 * t) := Real.one_le_exp (by positivity)
  have h2 : t = 4 / c * (c / 4 * t) := by field_simp
  have h3 : 0 ≤ 4 / c := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h h3]

theorem integrable_sq_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    Integrable fun u : Fin n → ℝ => (1 + ∑ i, u i ^ 2) ^ 2 * Real.exp (-c * ∑ i, u i ^ 2) := by
  refine ((integrable_exp_neg_mul_sum_sq (half_pos hc)).const_mul ((1 + 4 / c) ^ 2)).mono'
    (by fun_prop) (ae_of_all _ fun u => ?_)
  set S := ∑ i, u i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h1 := one_add_le_exp hc hS
  have hpos : 0 ≤ (1 + S) ^ 2 * Real.exp (-c * S) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hpos]
  have h2 : (1 + S) ^ 2 ≤ (1 + 4 / c) ^ 2 * Real.exp (c / 4 * S) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) h1 2
  have h3 : Real.exp (c / 4 * S) ^ 2 * Real.exp (-c * S) = Real.exp (-(c / 2) * S) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc (1 + S) ^ 2 * Real.exp (-c * S)
      ≤ (1 + 4 / c) ^ 2 * Real.exp (c / 4 * S) ^ 2 * Real.exp (-c * S) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (1 + 4 / c) ^ 2 * Real.exp (-(c / 2) * S) := by rw [mul_assoc, h3]

theorem integrable_heatEnvelopeVec {a b : ℝ} (hb : 0 < b) :
    Integrable fun u : Fin n → ℝ => (1 + ∑ i, u i ^ 2) * heatEnvelopeVec a b u := by
  have hc : 0 < 1 / (2 * b) := by positivity
  refine ((integrable_sq_mul_exp_neg hc).const_mul
    ((Real.sqrt (2 * Real.pi * a))⁻¹ ^ n * ((n + 1) * (1 + 1 / a) ^ 2))).congr
    (ae_of_all _ fun u => ?_)
  simp only [heatEnvelopeVec, neg_mul]
  ring

noncomputable def heatDensityVec (μ : Measure (Fin n → ℝ)) (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y, heatKernelVec s (x - y) ∂μ

noncomputable def heatDensityVecDeriv (μ : Measure (Fin n → ℝ)) (s : ℝ) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  ∫ y, -((x - y) i / s) * heatKernelVec s (x - y) ∂μ

noncomputable def heatDensityVecDeriv2 (μ : Measure (Fin n → ℝ)) (s : ℝ) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  ∫ y, ((x - y) i ^ 2 / s ^ 2 - 1 / s) * heatKernelVec s (x - y) ∂μ

variable {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]

theorem integrable_mul_heatKernelVec {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    {c : (Fin n → ℝ) → ℝ} (hc : Continuous c)
    (hcb : ∀ u, |c u| ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2)) (x : Fin n → ℝ) :
    Integrable (fun y => c (x - y) * heatKernelVec s (x - y)) μ := by
  have hb : 0 < b := ha.trans_le (has.trans hsb)
  refine Integrable.mono' (integrable_const
    ((Real.sqrt (2 * Real.pi * a))⁻¹ ^ n * ((n + 1) * (1 + 1 / a) ^ 2) * (1 + 2 * b))) ?_
    (ae_of_all _ fun y => ?_)
  · exact ((hc.comp (continuous_const.sub continuous_id)).mul
      ((continuous_heatKernelVec s).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact (abs_mul_heatKernelVec_le ha has hsb (hcb _)).trans (heatEnvelopeVec_le hb _)

theorem integrable_heatKernelVec_comp {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (x : Fin n → ℝ) : Integrable (fun y => heatKernelVec s (x - y)) μ := by
  simpa using integrable_mul_heatKernelVec (μ := μ) (c := fun _ => 1) ha has hsb
    continuous_const (fun u => heatPolyVec_one ha u) x

theorem heatDensityVec_pos {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) : 0 < heatDensityVec μ s x := by
  have hi := integrable_heatKernelVec_comp (μ := μ) hs le_rfl le_rfl x
  rw [heatDensityVec, integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun y => (heatKernelVec_pos hs _).le) hi]
  have : Function.support (fun y => heatKernelVec s (x - y)) = Set.univ :=
    Set.eq_univ_of_forall fun y => (heatKernelVec_pos hs _).ne'
  simp [this]

theorem heatDensityVec_le {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) :
    heatDensityVec μ s x ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ ^ n := by
  calc heatDensityVec μ s x ≤ ∫ _, (Real.sqrt (2 * Real.pi * s))⁻¹ ^ n ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun y => (heatKernelVec_pos hs _).le)
          (integrable_const _) (ae_of_all _ fun y => heatKernelVec_le_const hs _)
    _ = _ := by simp

theorem abs_integral_mul_heatKernelVec_le {a b s : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    {c : (Fin n → ℝ) → ℝ}
    (hcb : ∀ u, |c u| ≤ (n + 1) * (1 + 1 / a) ^ 2 * (1 + ∑ j, u j ^ 2)) (x : Fin n → ℝ) :
    |∫ y, c (x - y) * heatKernelVec s (x - y) ∂μ| ≤ ∫ y, heatEnvelopeVec a b (x - y) ∂μ := by
  have hb : 0 < b := ha.trans_le (has.trans hsb)
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (ae_of_all _ fun _ => abs_nonneg _) ?_
    (ae_of_all _ fun _ => abs_mul_heatKernelVec_le ha has hsb (hcb _)))
  exact Integrable.mono' (integrable_const
    ((Real.sqrt (2 * Real.pi * a))⁻¹ ^ n * ((n + 1) * (1 + 1 / a) ^ 2) * (1 + 2 * b)))
    ((continuous_heatEnvelopeVec a b).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (heatEnvelopeVec_nonneg _ _ _)]
      exact heatEnvelopeVec_le hb _)

theorem continuous_integral_mul_heatKernelVec {s : ℝ} (hs : 0 < s) {c : (Fin n → ℝ) → ℝ}
    (hc : Continuous c)
    (hcb : ∀ u, |c u| ≤ (n + 1) * (1 + 1 / s) ^ 2 * (1 + ∑ j, u j ^ 2)) :
    Continuous fun x => ∫ y, c (x - y) * heatKernelVec s (x - y) ∂μ := by
  refine continuous_of_dominated (bound := fun _ =>
    (Real.sqrt (2 * Real.pi * s))⁻¹ ^ n * ((n + 1) * (1 + 1 / s) ^ 2) * (1 + 2 * s))
    (fun x => (integrable_mul_heatKernelVec hs le_rfl le_rfl hc hcb x).aestronglyMeasurable)
    (fun x => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact (abs_mul_heatKernelVec_le hs le_rfl le_rfl (hcb _)).trans (heatEnvelopeVec_le hs _))
    (integrable_const _) (ae_of_all _ fun y => ?_)
  exact (hc.comp (continuous_id.sub continuous_const)).mul
    ((continuous_heatKernelVec s).comp (continuous_id.sub continuous_const))

theorem continuous_heatDensityVec {s : ℝ} (hs : 0 < s) : Continuous (heatDensityVec μ s) := by
  have h := continuous_integral_mul_heatKernelVec (μ := μ) (c := fun _ => 1) hs continuous_const
    (fun u => heatPolyVec_one hs u)
  simp only [one_mul] at h
  exact h

theorem continuous_heatDensityVecDeriv {s : ℝ} (hs : 0 < s) (i : Fin n) :
    Continuous (heatDensityVecDeriv μ s i) :=
  continuous_integral_mul_heatKernelVec (μ := μ) (c := fun u => -(u i / s)) hs
    (by fun_prop :
      Continuous fun u : Fin n → ℝ => -(u i / s)) (fun u => heatPolyVec_deriv hs le_rfl u i)

theorem continuous_heatDensityVecDeriv2 {s : ℝ} (hs : 0 < s) (i : Fin n) :
    Continuous (heatDensityVecDeriv2 μ s i) :=
  continuous_integral_mul_heatKernelVec (μ := μ) (c := fun u => u i ^ 2 / s ^ 2 - 1 / s) hs
    (by fun_prop) (fun u => heatPolyVec_deriv2 hs le_rfl u i)

theorem hasDerivAt_heatDensityVec_update {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) (i : Fin n)
    (r : ℝ) :
    HasDerivAt (fun r => heatDensityVec μ s (Function.update x i r))
      (heatDensityVecDeriv μ s i (Function.update x i r)) r := by
  have hc : Continuous fun u : Fin n → ℝ => -(u i / s) := (by fun_prop :
      Continuous fun u : Fin n → ℝ => -(u i / s))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := r)
    (F := fun r y => heatKernelVec s (Function.update x i r - y))
    (F' := fun r y => -((Function.update x i r - y) i / s) *
      heatKernelVec s (Function.update x i r - y))
    (bound := fun _ => (Real.sqrt (2 * Real.pi * s))⁻¹ ^ n * ((n + 1) * (1 + 1 / s) ^ 2) *
      (1 + 2 * s))
    Filter.univ_mem
    (Eventually.of_forall fun r' => ((continuous_heatKernelVec s).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (integrable_heatKernelVec_comp hs le_rfl le_rfl _)
    (integrable_mul_heatKernelVec hs le_rfl le_rfl hc (fun u => heatPolyVec_deriv hs le_rfl u i)
      _).aestronglyMeasurable
    (ae_of_all _ fun y r' _ => by
      rw [Real.norm_eq_abs]
      exact (abs_mul_heatKernelVec_le hs le_rfl le_rfl (heatPolyVec_deriv hs le_rfl _ i)).trans
        (heatEnvelopeVec_le hs _))
    (integrable_const _)
    (ae_of_all _ fun y r' _ => hasDerivAt_heatKernelVec_update s x y i r')
  exact h.2

theorem hasDerivAt_heatDensityVecDeriv_update {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) (i : Fin n)
    (r : ℝ) :
    HasDerivAt (fun r => heatDensityVecDeriv μ s i (Function.update x i r))
      (heatDensityVecDeriv2 μ s i (Function.update x i r)) r := by
  have hc : Continuous fun u : Fin n → ℝ => -(u i / s) := (by fun_prop :
      Continuous fun u : Fin n → ℝ => -(u i / s))
  have hc2 : Continuous fun u : Fin n → ℝ => u i ^ 2 / s ^ 2 - 1 / s := by fun_prop
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := r)
    (F := fun r y => -((Function.update x i r - y) i / s) *
      heatKernelVec s (Function.update x i r - y))
    (F' := fun r y => ((Function.update x i r - y) i ^ 2 / s ^ 2 - 1 / s) *
      heatKernelVec s (Function.update x i r - y))
    (bound := fun _ => (Real.sqrt (2 * Real.pi * s))⁻¹ ^ n * ((n + 1) * (1 + 1 / s) ^ 2) *
      (1 + 2 * s))
    Filter.univ_mem
    (Eventually.of_forall fun r' => (integrable_mul_heatKernelVec hs le_rfl le_rfl hc
      (fun u => heatPolyVec_deriv hs le_rfl u i) _).aestronglyMeasurable)
    (integrable_mul_heatKernelVec hs le_rfl le_rfl hc (fun u => heatPolyVec_deriv hs le_rfl u i) _)
    (integrable_mul_heatKernelVec hs le_rfl le_rfl hc2
      (fun u => heatPolyVec_deriv2 hs le_rfl u i) _).aestronglyMeasurable
    (ae_of_all _ fun y r' _ => by
      rw [Real.norm_eq_abs]
      exact (abs_mul_heatKernelVec_le hs le_rfl le_rfl (heatPolyVec_deriv2 hs le_rfl _ i)).trans
        (heatEnvelopeVec_le hs _))
    (integrable_const _)
    (ae_of_all _ fun y r' _ => hasDerivAt_heatKernelVec_update_deriv s x y i r')
  exact h.2

theorem hasDerivAt_heatDensityVec_time {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) :
    HasDerivAt (fun s => heatDensityVec μ s x) ((∑ i, heatDensityVecDeriv2 μ s i x) / 2) s := by
  have ha : 0 < s / 2 := by positivity
  have hb : 0 < 2 * s := by positivity
  have hmem : Set.Ioo (s / 2) (2 * s) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hc0 : ∀ s' ∈ Set.Ioo (s / 2) (2 * s), Integrable (fun y => heatKernelVec s' (x - y)) μ :=
    fun s' h => integrable_heatKernelVec_comp ha h.1.le h.2.le x
  have hc2 : Continuous fun u : Fin n → ℝ => (∑ i, (u i ^ 2 / s ^ 2 - 1 / s)) / 2 := by fun_prop
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s)
    (F := fun s y => heatKernelVec s (x - y))
    (F' := fun s y => (∑ i, ((x - y) i ^ 2 / s ^ 2 - 1 / s)) / 2 * heatKernelVec s (x - y))
    (bound := fun _ => (Real.sqrt (2 * Real.pi * (s / 2)))⁻¹ ^ n *
      ((n + 1) * (1 + 1 / (s / 2)) ^ 2) * (1 + 2 * (2 * s)))
    hmem
    (Filter.mem_of_superset hmem fun s' h => (hc0 s' h).aestronglyMeasurable)
    (hc0 s ⟨by linarith, by linarith⟩)
    (integrable_mul_heatKernelVec hs le_rfl le_rfl hc2 (fun u => heatPolyVec_time hs le_rfl u)
      x).aestronglyMeasurable
    (ae_of_all _ fun y s' h => by
      rw [Real.norm_eq_abs]
      exact (abs_mul_heatKernelVec_le ha h.1.le h.2.le (heatPolyVec_time ha h.1.le _)).trans
        (heatEnvelopeVec_le hb _))
    (integrable_const _)
    (ae_of_all _ fun y s' h => hasDerivAt_heatKernelVec_time (ha.trans h.1) (x - y))
  convert h.2 using 1
  · rfl
  have hi : ∀ i ∈ Finset.univ, Integrable
      (fun y => ((x - y) i ^ 2 / s ^ 2 - 1 / s) * heatKernelVec s (x - y)) μ := fun i _ =>
    integrable_mul_heatKernelVec (c := fun u => u i ^ 2 / s ^ 2 - 1 / s) hs le_rfl le_rfl
      (by fun_prop) (fun u => heatPolyVec_deriv2 hs le_rfl u i) x
  rw [show (∑ i, heatDensityVecDeriv2 μ s i x) = ∑ i, ∫ y,
      ((x - y) i ^ 2 / s ^ 2 - 1 / s) * heatKernelVec s (x - y) ∂μ from rfl,
    ← integral_finsetSum _ hi, ← integral_div]
  congr 1
  ext y
  rw [← Finset.sum_mul]
  ring

theorem integrable_mul_integral_comp_sub_vec (hμ2 : Integrable (fun y => ∑ i, y i ^ 2) μ)
    {g : (Fin n → ℝ) → ℝ} (hgm : Measurable g) (hg0 : ∀ u, 0 ≤ g u)
    (hg : Integrable fun u => (1 + ∑ i, u i ^ 2) * g u) :
    Integrable fun x => (1 + ∑ i, x i ^ 2) * ∫ y, g (x - y) ∂μ := by
  set q : (Fin n → ℝ) → ℝ := fun u => 1 + ∑ i, u i ^ 2
  have hq0 : ∀ u, 0 ≤ q u := fun u => by
    have : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    simp only [q]
    linarith
  have hqm : Measurable q := by fun_prop
  set h : (Fin n → ℝ) → ℝ := fun u => q u * g u
  have hh0 : ∀ u, 0 ≤ h u := fun u => mul_nonneg (hq0 u) (hg0 u)
  have hhm : Measurable h := hqm.mul hgm
  set D : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => 2 * q p.2 * h (p.1 - p.2)
  have hDm : Measurable D :=
    (measurable_const.mul (hqm.comp measurable_snd)).mul
      (hhm.comp (measurable_fst.sub measurable_snd))
  have hD : Integrable D (volume.prod μ) := by
    refine (integrable_prod_iff' hDm.aestronglyMeasurable).2 ⟨ae_of_all _ fun y =>
      (hg.comp_sub_right y).const_mul (2 * q y), ?_⟩
    have e : ∀ y, ∫ x, ‖D (x, y)‖ = 2 * q y * ∫ u, h u := by
      intro y
      have : ∀ x, ‖D (x, y)‖ = 2 * q y * h (x - y) := fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg zero_le_two (hq0 _))
          (hh0 _))]
      simp_rw [this]
      rw [integral_const_mul, integral_sub_right_eq_self h y]
    simp_rw [e]
    exact (((integrable_const 1).add hμ2).const_mul 2).mul_const _ |>.congr
      (ae_of_all _ fun y => by simp only [Pi.add_apply, q]; ring)
  have hH : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => q p.1 * g (p.1 - p.2))
      (volume.prod μ) := by
    refine hD.mono' ((hqm.comp measurable_fst).mul
      (hgm.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    obtain ⟨x, y⟩ := p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 _) (hg0 _))]
    simp only [D, h]
    have hw : q x ≤ 2 * q y * q (x - y) := by
      simp only [q, Pi.sub_apply]
      have h1 : ∑ i, x i ^ 2 ≤ 2 * ∑ i, y i ^ 2 + 2 * ∑ i, (x i - y i) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (x i - 2 * y i)]
      have h2 : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      have h3 : 0 ≤ ∑ i, (x i - y i) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      nlinarith [mul_nonneg h2 h3]
    calc q x * g (x - y) ≤ (2 * q y * q (x - y)) * g (x - y) :=
          mul_le_mul_of_nonneg_right hw (hg0 _)
      _ = _ := by ring
  refine hH.integral_prod_left.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [integral_const_mul]

end Meat
