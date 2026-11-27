import Meat.Channel.BroadcastKAchievability
import Meat.Open.BroadcastKConverse

namespace Meat

namespace BCK

variable {K : ℕ} [NeZero K] {A : Type*} [Finite A] [MeasurableSpace A]
  [MeasurableSingletonClass A] {B : Fin K → Type*} [∀ k, Fintype (B k)]
  [∀ k, MeasurableSpace (B k)] [∀ k, MeasurableSingletonClass (B k)]

theorem closure_achievableRegion_eq_of_isDegraded {W : DMC A (∀ k, B k)} (hW : IsDegraded W) :
    closure (achievableRegion W) = closure (superpositionUnion W) :=
  subset_antisymm
    (closure_minimal (achievableRegion_subset_of_isDegraded hW) isClosed_closure)
    (closure_minimal (superpositionUnion_subset_closure_achievableRegion hW) isClosed_closure)

end BCK

end Meat
