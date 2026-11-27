import Meat.Source.HelperAchievability

open Filter Topology

namespace Meat

namespace Helper

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] [DecidableEq S]

theorem achievable_of_mem_rateRegion {p : PMF (S × T)} {x : ℝ × ℝ} (hx : x ∈ rateRegion p)
    {R₁ R₂ : ℝ} (h₁ : x.1 < R₁) (h₂ : x.2 < R₂) : Achievable p R₁ R₂ := by
  obtain ⟨m, q, hq, hM, hX, hY⟩ := hx
  subst hq
  exact achievable_of_lt q hM (hX.trans_lt h₁) (hY.trans_lt h₂)

theorem closure_achievableRegion_eq (p : PMF (S × T)) :
    closure (achievableRegion p) = closure (rateRegion p) := by
  refine subset_antisymm (closure_achievableRegion_subset_closure_rateRegion p)
    (closure_minimal (fun x hx => ?_) isClosed_closure)
  have ht : Tendsto (fun δ : ℝ => (x.1 + δ, x.2 + δ)) (𝓝[>] 0) (𝓝 x) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : Continuous fun δ : ℝ => (x.1 + δ, x.2 + δ) := by fun_prop
    simpa using hc.tendsto 0
  exact mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ (hδ : 0 < δ) =>
    achievable_of_mem_rateRegion hx (by linarith) (by linarith))

end Helper

end Meat
