import Meat.Source.SlepianWolfAchievability
import Meat.Source.SlepianWolfConverse

open Filter Topology

namespace Meat

namespace SlepianWolf

variable {S T : Type*} [Fintype S] [Fintype T] [MeasurableSpace S] [MeasurableSpace T]

theorem isClosed_rateRegion (p : PMF (S × T)) : IsClosed (rateRegion p) :=
  (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_const (continuous_fst.add continuous_snd)))

theorem closure_achievableRegion_eq [DecidableEq S] [DecidableEq T]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] (p : PMF (S × T)) :
    closure (achievableRegion p) = rateRegion p := by
  refine subset_antisymm (closure_minimal (fun R hR => mem_rateRegion_of_achievable p hR)
    (isClosed_rateRegion p)) fun R hR => ?_
  have ht : Tendsto (fun δ : ℝ => (R.1 + δ, R.2 + δ)) (𝓝[>] 0) (𝓝 R) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : Continuous fun δ : ℝ => (R.1 + δ, R.2 + δ) :=
      (continuous_const.add continuous_id).prodMk (continuous_const.add continuous_id)
    simpa using hc.tendsto 0
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ (hδ : 0 < δ) => ?_)
  obtain ⟨h₁, h₂, h₃⟩ := hR
  exact achievable_of_lt p (by linarith) (by linarith) (by linarith)

end SlepianWolf

end Meat
