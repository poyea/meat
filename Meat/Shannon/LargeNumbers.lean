import Meat.Shannon.Typical

open Filter Topology Finset

namespace Meat

variable {A : Type*} [Fintype A]

private lemma sum_iidProb_mul_mul (p : PMF A) {n : ℕ} (Y : A → ℝ)
    (hY : ∑ a, (p a).toReal * Y a = 0) (i j : Fin n) :
    ∑ x, iidProb p x * (Y (x i) * Y (x j)) =
      if i = j then ∑ a, (p a).toReal * Y a ^ 2 else 0 := by
  have h := sum_prod_mul_prod (fun (_ : Fin n) a => (p a).toReal) fun k a =>
    (if k = i then Y a else 1) * (if k = j then Y a else 1)
  simp only [prod_mul_distrib, prod_ite_eq', mem_univ, ite_true] at h
  simp only [iidProb]
  rw [h]
  split_ifs with hij
  · subst hij
    rw [prod_eq_single i (fun k _ hk => by simp [hk, sum_toReal_pmf_eq_one]) (by simp)]
    simp [sq]
  · exact prod_eq_zero (mem_univ i) (by simp [hij, hY])

private lemma sum_iidProb_mul_sq (p : PMF A) {n : ℕ} (Y : A → ℝ)
    (hY : ∑ a, (p a).toReal * Y a = 0) :
    ∑ x : Fin n → A, iidProb p x * (∑ i, Y (x i)) ^ 2 = n * ∑ a, (p a).toReal * Y a ^ 2 := by
  simp_rw [sq, sum_mul_sum, mul_sum]
  rw [sum_comm]
  rw [Finset.sum_congr rfl fun i _ => by rw [sum_comm]]
  simp [sum_iidProb_mul_mul p Y hY, ← sq, mul_sum]

private lemma one_sub_le_sum_iidProb_sum_le (p : PMF A) (f : A → ℝ) {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    1 - (∑ a, (p a).toReal * (f a - ∑ b, (p b).toReal * f b) ^ 2) / ε ^ 2 / n ≤
      ∑ x : Fin n → A with ∑ i, f (x i) ≤ n * (∑ a, (p a).toReal * f a + ε), iidProb p x := by
  classical
  set m := ∑ a, (p a).toReal * f a
  set Y : A → ℝ := fun a => f a - m
  have hY : ∑ a, (p a).toReal * Y a = 0 := by
    simp only [Y, mul_sub, sum_sub_distrib, ← sum_mul, sum_toReal_pmf_eq_one, one_mul, m]
    exact sub_self _
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hnε : 0 < (n * ε) ^ 2 := by positivity
  have key : ∀ x : Fin n → A, (if ∑ i, f (x i) ≤ n * (m + ε) then 0 else iidProb p x)
      ≤ iidProb p x * (∑ i, Y (x i)) ^ 2 / (n * ε) ^ 2 := by
    intro x
    split_ifs with hx
    · exact div_nonneg (mul_nonneg (iidProb_nonneg p x) (sq_nonneg _)) hnε.le
    rw [not_le] at hx
    have hs : ∑ i, Y (x i) = ∑ i, f (x i) - n * m := by
      simp [Y, sum_sub_distrib]
    have hlt : n * ε < ∑ i, Y (x i) := by rw [hs]; linarith
    have hsq : (n * ε) ^ 2 < (∑ i, Y (x i)) ^ 2 :=
      pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
    rw [le_div_iff₀ hnε]
    exact mul_le_mul_of_nonneg_left hsq.le (iidProb_nonneg p x)
  have hsum := sum_le_sum fun x (_ : x ∈ univ) => key x
  rw [← sum_div, sum_iidProb_mul_sq p Y hY] at hsum
  have hc : ∑ x : Fin n → A, (if ∑ i, f (x i) ≤ n * (m + ε) then 0 else iidProb p x)
      = 1 - ∑ x : Fin n → A with ∑ i, f (x i) ≤ n * (m + ε), iidProb p x := by
    rw [← sum_iidProb p n, ← sum_filter_add_sum_filter_not univ
      (fun x : Fin n → A => ∑ i, f (x i) ≤ n * (m + ε)) (iidProb p), sum_ite]
    simp
  rw [hc] at hsum
  have he : (↑n * ∑ a, (p a).toReal * Y a ^ 2) / (↑n * ε) ^ 2
      = (∑ a, (p a).toReal * Y a ^ 2) / ε ^ 2 / n := by
    have := hn'.ne'
    have := hε.ne'
    field_simp
  change 1 - (∑ a, (p a).toReal * Y a ^ 2) / ε ^ 2 / n ≤ _
  linarith

theorem tendsto_sum_iidProb_sum_le (p : PMF A) (f : A → ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ∑ x : Fin n → A with ∑ i, f (x i) ≤ n * (∑ a, (p a).toReal * f a + ε), iidProb p x)
      atTop (𝓝 1) := by
  set V := ∑ a, (p a).toReal * (f a - ∑ b, (p b).toReal * f b) ^ 2
  have hl : Tendsto (fun n : ℕ => 1 - V / ε ^ 2 / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (V / ε ^ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact one_sub_le_sum_iidProb_sum_le p f hn hε
  · refine Eventually.of_forall fun n => ?_
    rw [← sum_iidProb p n]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => iidProb_nonneg p x

end Meat
