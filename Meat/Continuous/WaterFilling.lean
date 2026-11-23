import Mathlib.Topology.Order.IntermediateValue
import Meat.Continuous.Gaussian

open Finset

namespace Meat

namespace WaterFilling

variable {ι : Type*} [Fintype ι]

noncomputable def rate (N p : ι → ℝ) : ℝ :=
  ∑ i, awgnCapacity (p i) (N i)

noncomputable def fill (N : ι → ℝ) (ν : ℝ) (i : ι) : ℝ :=
  max (ν - N i) 0

def Feasible (P : ℝ) (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i ≤ P

omit [Fintype ι] in
theorem fill_nonneg (N : ι → ℝ) (ν : ℝ) (i : ι) : 0 ≤ fill N ν i :=
  le_max_right _ _

omit [Fintype ι] in
theorem fill_pos_iff (N : ι → ℝ) (ν : ℝ) (i : ι) : 0 < fill N ν i ↔ N i < ν := by
  simp only [fill, lt_max_iff, lt_irrefl, or_false, sub_pos]

omit [Fintype ι] in
theorem add_fill_of_pos {N : ι → ℝ} {ν : ℝ} {i : ι} (h : 0 < fill N ν i) :
    N i + fill N ν i = ν := by
  rw [fill, max_eq_left (le_of_lt (by simpa [fill] using h))]
  ring

omit [Fintype ι] in
theorem fill_eq_zero_iff (N : ι → ℝ) (ν : ℝ) (i : ι) : fill N ν i = 0 ↔ ν ≤ N i := by
  simp only [fill, max_eq_right_iff, sub_nonpos]

theorem continuous_sum_fill (N : ι → ℝ) : Continuous fun ν => ∑ i, fill N ν i := by
  unfold fill
  fun_prop

theorem exists_level [Nonempty ι] {N : ι → ℝ} {P : ℝ} (hP : 0 ≤ P) :
    ∃ ν, univ.inf' univ_nonempty N ≤ ν ∧ ∑ i, fill N ν i = P := by
  set a := univ.inf' univ_nonempty N
  obtain ⟨i₀, -, hi₀⟩ := exists_mem_eq_inf' (univ_nonempty (α := ι)) N
  have ha : ∑ i, fill N a i = 0 := sum_eq_zero fun i _ =>
    (fill_eq_zero_iff N a i).2 (inf'_le N (mem_univ i))
  have hb : P ≤ ∑ i, fill N (a + P) i := by
    have h := single_le_sum (f := fun i => fill N (a + P) i) (fun i _ => fill_nonneg N _ i)
      (mem_univ i₀)
    refine le_trans ?_ h
    rw [fill, ← hi₀]
    exact le_max_of_le_left (by linarith)
  obtain ⟨ν, hν, hνP⟩ := intermediate_value_Icc (by linarith : a ≤ a + P)
    (continuous_sum_fill N).continuousOn ⟨by rw [ha]; exact hP, hb⟩
  exact ⟨ν, hν.1, hνP⟩

theorem fill_feasible (N : ι → ℝ) {ν P : ℝ} (h : ∑ i, fill N ν i = P) :
    Feasible P (fill N ν) :=
  ⟨fill_nonneg N ν, h.le⟩

private lemma term_le {N p b ν : ℝ} (hN : 0 < N) (hp : 0 ≤ p) (hb : 0 ≤ b) (hν : 0 < ν)
    (hcase : (0 < b ∧ N + b = ν) ∨ (b = 0 ∧ ν ≤ N)) :
    awgnCapacity p N - awgnCapacity b N ≤ (1 / 2) * ((p - b) / ν) ∧
      (p ≠ b → awgnCapacity p N - awgnCapacity b N < (1 / 2) * ((p - b) / ν)) := by
  have hNp : 0 < N + p := by linarith
  have hNb : 0 < N + b := by linarith
  have e : awgnCapacity p N - awgnCapacity b N = (1 / 2) * Real.log ((N + p) / (N + b)) := by
    unfold awgnCapacity
    rw [show 1 + p / N = (N + p) / N by field_simp, show 1 + b / N = (N + b) / N by field_simp,
      Real.log_div hNp.ne' hN.ne', Real.log_div hNb.ne' hN.ne', Real.log_div hNp.ne' hNb.ne']
    ring
  have hfrac : (N + p) / (N + b) - 1 ≤ (p - b) / ν := by
    rw [div_sub_one hNb.ne']
    rcases hcase with ⟨-, h⟩ | ⟨rfl, h⟩
    · rw [show N + p - (N + b) = p - b by ring, h]
    · rw [add_zero, sub_zero, add_sub_cancel_left]
      exact div_le_div_of_nonneg_left hp hν h
  rw [e]
  refine ⟨?_, fun hne => ?_⟩
  · have := Real.log_le_sub_one_of_pos (div_pos hNp hNb)
    linarith
  · have hne' : (N + p) / (N + b) ≠ 1 := by
      rw [Ne, div_eq_one_iff_eq hNb.ne']
      intro h
      exact hne (by linarith)
    have := Real.log_lt_sub_one_of_pos (div_pos hNp hNb) hne'
    linarith

theorem rate_le_rate_fill {N : ι → ℝ} (hN : ∀ i, 0 < N i) {ν P : ℝ} (hν : 0 < ν)
    (hfill : ∑ i, fill N ν i = P) {p : ι → ℝ} (hp : Feasible P p) :
    rate N p ≤ rate N (fill N ν) ∧ (p ≠ fill N ν → rate N p < rate N (fill N ν)) := by
  have hcase : ∀ i, (0 < fill N ν i ∧ N i + fill N ν i = ν) ∨ (fill N ν i = 0 ∧ ν ≤ N i) := by
    intro i
    rcases (fill_nonneg N ν i).eq_or_lt with h | h
    · exact Or.inr ⟨h.symm, (fill_eq_zero_iff N ν i).1 h.symm⟩
    · exact Or.inl ⟨h, add_fill_of_pos h⟩
  have ht := fun i => term_le (hN i) (hp.1 i) (fill_nonneg N ν i) hν (hcase i)
  have hsum : ∑ i, (1 / 2) * ((p i - fill N ν i) / ν) ≤ 0 := by
    rw [← mul_sum, ← sum_div, sum_sub_distrib, hfill]
    have : (∑ i, p i - P) / ν ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hp.2]) hν.le
    linarith
  have hdiff : rate N p - rate N (fill N ν) =
      ∑ i, (awgnCapacity (p i) (N i) - awgnCapacity (fill N ν i) (N i)) := by
    rw [rate, rate, sum_sub_distrib]
  refine ⟨?_, fun hne => ?_⟩
  · have := sum_le_sum fun i (_ : i ∈ univ) => (ht i).1
    linarith
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have := sum_lt_sum (fun i (_ : i ∈ univ) => (ht i).1) ⟨j, mem_univ j, (ht j).2 hj⟩
    linarith

noncomputable def capacity (N : ι → ℝ) (P : ℝ) : ℝ :=
  sSup (rate N '' {p | Feasible P p})

theorem capacity_eq {N : ι → ℝ} (hN : ∀ i, 0 < N i) {ν P : ℝ} (hν : 0 < ν)
    (hfill : ∑ i, fill N ν i = P) : capacity N P = rate N (fill N ν) := by
  refine IsGreatest.csSup_eq ⟨⟨fill N ν, fill_feasible N hfill, rfl⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact (rate_le_rate_fill hN hν hfill hp).1

theorem rate_fill_eq {N : ι → ℝ} (hN : ∀ i, 0 < N i) (ν : ℝ) :
    rate N (fill N ν) = ∑ i, (1 / 2) * Real.log (max ν (N i) / N i) := by
  refine sum_congr rfl fun i _ => ?_
  unfold awgnCapacity fill
  congr 2
  rw [one_add_div (hN i).ne']
  congr 1
  rcases le_total ν (N i) with h | h
  · rw [max_eq_right (by linarith), max_eq_right h]
    ring
  · rw [max_eq_left (by linarith), max_eq_left h]
    ring

theorem exists_waterFilling [Nonempty ι] {N : ι → ℝ} (hN : ∀ i, 0 < N i) {P : ℝ} (hP : 0 ≤ P) :
    ∃ ν, 0 < ν ∧ Feasible P (fill N ν) ∧ ∑ i, fill N ν i = P ∧
      (∀ i, 0 < fill N ν i → N i + fill N ν i = ν) ∧ (∀ i, fill N ν i = 0 → ν ≤ N i) ∧
      capacity N P = ∑ i, (1 / 2) * Real.log (max ν (N i) / N i) ∧
      ∀ p, Feasible P p → rate N p = capacity N P → p = fill N ν := by
  obtain ⟨ν, hνa, hνP⟩ := exists_level (N := N) hP
  have hν : 0 < ν := lt_of_lt_of_le
    ((lt_inf'_iff _).2 fun i _ => hN i) hνa
  refine ⟨ν, hν, fill_feasible N hνP, hνP, fun i h => add_fill_of_pos h,
    fun i h => (fill_eq_zero_iff N ν i).1 h, ?_, fun p hp heq => ?_⟩
  · rw [capacity_eq hN hν hνP, rate_fill_eq hN ν]
  · by_contra hne
    have := (rate_le_rate_fill hN hν hνP hp).2 hne
    rw [capacity_eq hN hν hνP] at heq
    linarith

end WaterFilling

end Meat
