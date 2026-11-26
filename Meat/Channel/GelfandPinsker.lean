import Meat.Channel.GelfandPinskerAchievability

namespace Meat

namespace GelfandPinsker

theorem closure_achievable_eq {St A B : Type*} [Fintype St] [MeasurableSpace St]
    [MeasurableSingletonClass St] [Finite A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (W : DMC (A × St) B) (pS : PMF St) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable W pS R} = Set.Icc 0 (infoCapacity W pS) := by
  classical
  refine subset_antisymm (closure_minimal (fun R hR =>
    ⟨hR.1, le_infoCapacity_of_achievable W pS hR.2⟩) isClosed_Icc) fun R hR => ?_
  rcases (infoCapacity_nonneg W pS).eq_or_lt with h | h
  · rw [← h, Set.Icc_self, Set.mem_singleton_iff] at hR
    exact subset_closure ⟨hR.symm ▸ le_rfl, hR ▸ achievable_zero W pS⟩
  · rw [← closure_Ico h.ne] at hR
    refine closure_mono (fun R (hR : R ∈ Set.Ico 0 (infoCapacity W pS)) => ?_) hR
    exact ⟨hR.1, achievable_of_lt_infoCapacity W pS hR.2⟩

end GelfandPinsker

end Meat
