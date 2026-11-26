import Meat.Source.WynerZivAchievability

open Filter Topology

namespace Meat

namespace WynerZiv

variable {S T V : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
theorem Achievable.mono {p : PMF (S × T)} {d : S → V → ℝ} {R R' D D' : ℝ}
    (h : Achievable p d R D) (hR : R ≤ R') (hD : D ≤ D') : Achievable p d R' D' := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hn
  exact ⟨k, hk.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg n))),
    c, hc.trans (by linarith)⟩

theorem achievable_of_mem_rateRegion {p : PMF (S × T)} {d : S → V → ℝ} (hd : ∀ s v, 0 ≤ d s v)
    {x : ℝ × ℝ} (hx : x ∈ rateRegion p d) {R : ℝ} (hR : x.1 < R) : Achievable p d R x.2 := by
  obtain ⟨m, q, g, hq, hM, hD, hI⟩ := hx
  subst hq
  exact (achievable_of_lt hd q g hM (hI.trans_lt hR)).mono le_rfl hD

theorem closure_achievableRegion_eq (p : PMF (S × T)) {d : S → V → ℝ} (hd : ∀ s v, 0 ≤ d s v) :
    closure (achievableRegion p d) = closure (rateRegion p d) := by
  refine subset_antisymm (closure_achievableRegion_subset_closure_rateRegion p d)
    (closure_minimal (fun x hx => ?_) isClosed_closure)
  have ht : Tendsto (fun δ : ℝ => (x.1 + δ, x.2)) (𝓝[>] 0) (𝓝 x) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : Continuous fun δ : ℝ => (x.1 + δ, x.2) := by fun_prop
    simpa using hc.tendsto 0
  exact mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ (hδ : 0 < δ) =>
    achievable_of_mem_rateRegion hd hx (by linarith))

end WynerZiv

end Meat
