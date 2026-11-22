import Meat.Channel.Achievability
import Meat.Channel.Converse

namespace Meat

namespace DMC

theorem closure_achievable_eq {A B : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (W : DMC A B) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable W R} = Set.Icc 0 (capacity W) := by
  refine subset_antisymm (closure_minimal (fun R hR => ⟨hR.1, le_capacity_of_achievable W hR.2⟩)
    isClosed_Icc) fun R hR => ?_
  rcases (capacity_nonneg W).eq_or_lt with h | h
  · rw [← h, Set.Icc_self, Set.mem_singleton_iff] at hR
    exact subset_closure ⟨hR.symm ▸ le_rfl, hR ▸ achievable_zero W⟩
  · rw [← closure_Ico h.ne] at hR
    refine closure_mono (fun R (hR : R ∈ Set.Ico 0 (capacity W)) => ?_) hR
    exact ⟨hR.1, achievable_of_lt_capacity W hR.1 hR.2⟩

end DMC

end Meat
