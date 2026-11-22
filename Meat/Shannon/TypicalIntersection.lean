import Meat.Shannon.Typical

open Filter Topology Finset

namespace Meat

theorem tendsto_sum_of_mem_iff_and {α : ℕ → Type*} [∀ n, Fintype (α n)] {w : ∀ n, α n → ℝ}
    (hw : ∀ n x, 0 ≤ w n x) (h1 : ∀ n, ∑ x, w n x ≤ 1) {s t u : ∀ n, Finset (α n)}
    (hu : ∀ n x, x ∈ u n ↔ x ∈ s n ∧ x ∈ t n)
    (hs : Tendsto (fun n => ∑ x ∈ s n, w n x) atTop (𝓝 1))
    (ht : Tendsto (fun n => ∑ x ∈ t n, w n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∑ x ∈ u n, w n x) atTop (𝓝 1) := by
  classical
  have hl : Tendsto (fun n => ∑ x ∈ s n, w n x + ∑ x ∈ t n, w n x - 1) atTop (𝓝 1) := by
    simpa using (hs.add ht).sub_const 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (fun n => ?_) fun n => ?_
  · have he : u n = s n ∩ t n := by
      ext x
      rw [hu, mem_inter]
    have hun : ∑ x ∈ s n ∪ t n, w n x ≤ 1 :=
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => hw n x).trans (h1 n)
    have := sum_union_inter (s₁ := s n) (s₂ := t n) (f := w n)
    simp only [he]
    linarith
  · exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => hw n x).trans (h1 n)

end Meat
