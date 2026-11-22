import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

open Finset

namespace Meat

theorem sum_ite_mem_zero {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α)
    (f : α → ℝ) : ∑ x, (if x ∈ s then 0 else f x) = ∑ x, f x - ∑ x ∈ s, f x := by
  rw [← univ_inter s, ← sum_ite_mem, univ_inter, eq_sub_iff_add_eq, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by split_ifs <;> simp

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]

omit [DecidableEq ι] in
theorem exists_le_of_sum_mul_le {w f : ι → ℝ} {t : ℝ} (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) (h : ∑ i, w i * f i ≤ t) : ∃ i, f i ≤ t := by
  by_contra hc
  push Not at hc
  obtain ⟨j, hj⟩ : ∃ j, 0 < w j := by
    by_contra h0
    push Not at h0
    have : ∑ i, w i ≤ 0 := sum_nonpos fun i _ => h0 i
    linarith
  have hlt : ∑ i, w i * t < ∑ i, w i * f i :=
    sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hc i).le (hw i))
      ⟨j, mem_univ j, mul_lt_mul_of_pos_left (hc j) hj⟩
  rw [← sum_mul, h1, one_mul] at hlt
  linarith

theorem sum_prod_mul_prod (w g : ι → X → ℝ) :
    ∑ C : ι → X, (∏ i, w i (C i)) * ∏ i, g i (C i) = ∏ i, ∑ x, w i x * g i x := by
  rw [Fintype.prod_sum]
  simp [prod_mul_distrib]

theorem sum_prod (w : ι → X → ℝ) (h1 : ∀ i, ∑ x, w i x = 1) :
    ∑ C : ι → X, ∏ i, w i (C i) = 1 := by
  simpa [h1] using sum_prod_mul_prod w fun _ _ => 1

theorem sum_prod_mul_apply (w : ι → X → ℝ) (h1 : ∀ i, ∑ x, w i x = 1) (f : X → ℝ) (j : ι) :
    ∑ C : ι → X, (∏ i, w i (C i)) * f (C j) = ∑ x, w j x * f x := by
  have h := sum_prod_mul_prod w fun i x => if i = j then f x else 1
  simp only [prod_ite_eq', mem_univ, ite_true] at h
  rw [h, prod_eq_single j (fun i _ hi => by simp [hi, h1]) (by simp)]
  simp

theorem sum_prod_mul_apply_mul_apply (w : ι → X → ℝ) (h1 : ∀ i, ∑ x, w i x = 1)
    (f g : X → ℝ) {j k : ι} (hjk : j ≠ k) :
    ∑ C : ι → X, (∏ i, w i (C i)) * (f (C j) * g (C k)) =
      (∑ x, w j x * f x) * ∑ x, w k x * g x := by
  have h := sum_prod_mul_prod w fun i x => (if i = j then f x else 1) * (if i = k then g x else 1)
  simp only [prod_mul_distrib, prod_ite_eq', mem_univ, ite_true] at h
  rw [h, prod_eq_mul j k hjk (fun i _ hi => by simp [hi.1, hi.2, h1]) (by simp) (by simp)]
  simp [hjk, hjk.symm]

theorem sum_prod_mul_apply_apply (w : ι → X → ℝ) (h1 : ∀ i, ∑ x, w i x = 1) (F : X → X → ℝ)
    {j k : ι} (hjk : j ≠ k) :
    ∑ C : ι → X, (∏ i, w i (C i)) * F (C j) (C k) = ∑ x, ∑ x', w j x * w k x' * F x x' := by
  classical
  have hF : ∀ C : ι → X, F (C j) (C k) =
      ∑ x, ∑ x', ((if x = C j then (1 : ℝ) else 0) * (if x' = C k then 1 else 0)) * F x x' := by
    intro C
    simp [ite_mul]
  simp_rw [hF, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun x' _ => ?_
  have h := sum_prod_mul_apply_mul_apply w h1 (fun y => if x = y then (1 : ℝ) else 0)
    (fun y => if x' = y then (1 : ℝ) else 0) hjk
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true] at h
  simp_rw [← mul_assoc, ← sum_mul]
  rw [← h]
  refine congrArg (· * F x x') (sum_congr rfl fun C _ => ?_)
  split_ifs <;> simp

theorem sum_arrow_prod {S T : Type*} [Fintype S] [Fintype T] (f : (ι → S × T) → ℝ) :
    ∑ u, f u = ∑ a : ι → S, ∑ b : ι → T, f fun i => (a i, b i) := by
  rw [← Fintype.sum_prod_type']
  exact (Equiv.sum_comp (Equiv.arrowProdEquivProdArrow ι (fun _ => S) (fun _ => T)).symm f).symm

end Meat
