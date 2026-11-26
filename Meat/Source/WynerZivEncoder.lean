import Meat.Shannon.Binning
import Meat.Shannon.MarkovLemma

open MeasureTheory Finset

namespace Meat

section Codebook

variable {S U : Type*} [Fintype S] [DecidableEq S] [Fintype U] [DecidableEq U]

theorem sum_iidProb_not_mem_strongTypicalSet_le (q : PMF S) {η : ℝ} (hη : 0 < η) {n : ℕ}
    (hn : 0 < n) :
    ∑ x ∈ univ.filter (fun x : Fin n → S => x ∉ strongTypicalSet (fun a => (q a).toReal) n η),
      iidProb q x ≤ Fintype.card S / (4 * n * η ^ 2) := by
  have hx : (fun _ : Fin n => ()) ∈ strongTypicalSet (fun _ : Unit => (1 : ℝ)) n 0 := by
    rw [mem_strongTypicalSet]
    intro a
    have hc : typeCount (fun _ : Fin n => ()) a = n := by
      simp [typeCount]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [hc, div_self hn', sub_self, abs_zero]
  have h := sum_not_mem_strongTypicalSet_le (fun _ : Unit => q) (fun _ => (1 : ℝ)) hη hn hx
  have hc : ∀ x : Fin n → S, ∀ a, typeCount (fun i => ((), x i)) ((), a) = typeCount x a :=
    fun x a => by simp [typeCount]
  have he : (univ.filter fun x : Fin n → S => (fun i => ((), x i)) ∉
      strongTypicalSet (fun ab : Unit × S => (1 : ℝ) * (q ab.2).toReal) n (0 + η)) =
      univ.filter fun x : Fin n → S => x ∉ strongTypicalSet (fun a => (q a).toReal) n η := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_strongTypicalSet, one_mul, zero_add]
    constructor
    · intro h1 h2
      exact h1 fun z => by rw [hc x z.2]; exact h2 z.2
    · intro h1 h2
      exact h1 fun a => by rw [← hc x a]; exact h2 ((), a)
  rw [he, Fintype.card_unit, Nat.cast_one, one_mul] at h
  exact h

theorem sum_codebook_not_mem (q : PMF U) {n K : ℕ} (s : Finset (Fin n → U)) :
    ∑ C : Fin K → Fin n → U, (∏ l, iidProb q (C l)) * (if ∀ l, C l ∉ s then 1 else 0) =
      (1 - ∑ u ∈ s, iidProb q u) ^ K := by
  have h := sum_prod_mul_prod (fun (_ : Fin K) u => iidProb q u)
    fun (_ : Fin K) u => if u ∉ s then (1 : ℝ) else 0
  simp only [prod_boole, mem_univ, true_implies] at h
  rw [h, prod_const, card_univ, Fintype.card_fin]
  congr 1
  have h1 := sum_iidProb q n
  rw [← sum_filter_add_sum_filter_not univ (fun u => u ∈ s)] at h1
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite, sum_const_zero, add_zero]
  have e1 : (univ.filter fun u : Fin n → U => u ∉ s) = univ.filter fun u => ¬ u ∈ s := rfl
  have e2 : (univ.filter fun u : Fin n → U => u ∈ s) = s := by ext; simp
  rw [e2] at h1
  linarith

theorem sum_codebook_apply_mem (q : PMF U) {n K : ℕ} (s : Finset (Fin n → U)) (l : Fin K) :
    ∑ C : Fin K → Fin n → U, (∏ l', iidProb q (C l')) * (if C l ∈ s then 1 else 0) =
      ∑ u ∈ s, iidProb q u := by
  rw [sum_prod_mul_apply (fun (_ : Fin K) u => iidProb q u) (fun _ => sum_iidProb q n)
    (fun u => if u ∈ s then (1 : ℝ) else 0) l]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext
  simp

end Codebook

theorem sum_bins_le {K₁ K : ℕ} (hK : 0 < K) (L : Fin K₁) (A : Fin K₁ → Prop) [DecidablePred A] :
    ∑ β : Fin K₁ → Fin K, (∏ _l : Fin K₁, (K : ℝ)⁻¹) *
        (if ∃ l, l ≠ L ∧ β l = β L ∧ A l then 1 else 0) ≤
      (K : ℝ)⁻¹ * ∑ l, if A l then 1 else 0 := by
  classical
  have hw0 : (0 : ℝ) ≤ ∏ _l : Fin K₁, (K : ℝ)⁻¹ := prod_nonneg fun _ _ => by positivity
  have hind : ∀ β : Fin K₁ → Fin K, (if ∃ l, l ≠ L ∧ β l = β L ∧ A l then (1 : ℝ) else 0) ≤
      ∑ l, (if l ≠ L ∧ A l then (1 : ℝ) else 0) * (if β l = β L then 1 else 0) := by
    intro β
    split_ifs with h
    · obtain ⟨l, hl, hb, ha⟩ := h
      calc (1 : ℝ) = (if l ≠ L ∧ A l then (1 : ℝ) else 0) * (if β l = β L then 1 else 0) := by
            simp [hl, ha, hb]
        _ ≤ _ := single_le_sum (f := fun l => (if l ≠ L ∧ A l then (1 : ℝ) else 0) *
            (if β l = β L then 1 else 0)) (fun _ _ => by split_ifs <;> norm_num) (mem_univ l)
    · exact sum_nonneg fun _ _ => by split_ifs <;> norm_num
  calc ∑ β : Fin K₁ → Fin K, (∏ _l : Fin K₁, (K : ℝ)⁻¹) *
        (if ∃ l, l ≠ L ∧ β l = β L ∧ A l then 1 else 0)
      ≤ ∑ β : Fin K₁ → Fin K, (∏ _l : Fin K₁, (K : ℝ)⁻¹) *
        ∑ l, (if l ≠ L ∧ A l then (1 : ℝ) else 0) * (if β l = β L then 1 else 0) :=
        sum_le_sum fun β _ => mul_le_mul_of_nonneg_left (hind β) hw0
    _ = ∑ l, (if l ≠ L ∧ A l then (1 : ℝ) else 0) *
        ∑ β : Fin K₁ → Fin K, (∏ _l : Fin K₁, (K : ℝ)⁻¹) * (if β l = β L then 1 else 0) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun l _ => sum_congr rfl fun β _ => by ring
    _ ≤ ∑ l, (if A l then (1 : ℝ) else 0) * (K : ℝ)⁻¹ := by
        refine sum_le_sum fun l _ => ?_
        rw [sum_uniform_mul_ite_eq hK l L]
        by_cases hl : l = L
        · simp only [hl, ne_eq, not_true_eq_false, false_and, ite_false, zero_mul]
          split_ifs <;> positivity
        · simp only [ne_eq, hl, not_false_eq_true, true_and, ite_false]
          split_ifs <;> simp
    _ = _ := by rw [mul_sum]; exact sum_congr rfl fun l _ => mul_comm _ _

end Meat
