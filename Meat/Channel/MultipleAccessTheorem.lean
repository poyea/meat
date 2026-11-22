import Meat.Channel.MultipleAccessAchievability
import Meat.Channel.MultipleAccessConverse

namespace Meat

namespace MAC

variable {A₁ A₂ B : Type*}
  [Fintype A₁] [MeasurableSpace A₁] [Fintype A₂] [MeasurableSpace A₂]
  [Fintype B] [MeasurableSpace B]

@[nolint unusedArguments]
theorem closure_achievableRegion_eq [Nonempty A₁] [Nonempty A₂]
    [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B]
    (W : DMC (A₁ × A₂) B) :
    closure (achievableRegion W) = capacityRegion W :=
  subset_antisymm
    (closure_minimal (fun _ hR => mem_capacityRegion_of_mem_achievableRegion W hR) isClosed_closure)
    (capacityRegion_subset_closure_achievableRegion W)

end MAC

end Meat
