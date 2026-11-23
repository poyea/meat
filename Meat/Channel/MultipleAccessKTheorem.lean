import Meat.Channel.MultipleAccessKConverse

namespace Meat

namespace MACK

variable {K : ℕ} {A : Fin K → Type*} {B : Type*}
  [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)] [∀ k, MeasurableSingletonClass (A k)]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem closure_achievableRegion_eq (W : DMC (∀ k, A k) B) :
    closure (achievableRegion W) = capacityRegion W :=
  subset_antisymm
    (closure_minimal (fun _ hR => mem_capacityRegion_of_mem_achievableRegion W hR)
      isClosed_closure)
    (capacityRegion_subset_closure_achievableRegion W)

end MACK

end Meat
