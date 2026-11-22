import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Real
import Meat.Shannon.Entropy

open MeasureTheory

namespace Meat

variable {Ω S T U : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]

theorem measureEntropy_map_of_injective (ν : Measure S) {f : S → T}
    (hf : Function.Injective f) : measureEntropy (ν.map f) = measureEntropy ν := by
  refine (Fintype.sum_of_injective f hf _ _ (fun t ht => ?_) fun s => ?_).symm
  · rw [map_measureReal_apply .of_discrete (measurableSet_singleton t),
      Set.preimage_singleton_eq_empty.2 ht, measureReal_empty, Real.negMulLog_zero]
  · rw [map_measureReal_apply .of_discrete (measurableSet_singleton (f s))]
    congr 3
    ext
    simp [hf.eq_iff]

variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (μ : Measure Ω)

theorem entropy_comp_of_injective {f : S → T} (hf : Function.Injective f) :
    H[f ∘ X ; μ] = H[X ; μ] := by
  have he : MeasurableEmbedding f := ⟨hf, .of_discrete, fun _ _ => .of_discrete⟩
  by_cases hX : AEMeasurable X μ
  · rw [entropy, entropy, ← he.measurable.aemeasurable.map_map_of_aemeasurable hX,
      measureEntropy_map_of_injective _ hf]
  have hfX : ¬AEMeasurable (f ∘ X) μ := he.aemeasurable_comp_iff.not.2 hX
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp [entropy, measureEntropy]
  · simp [entropy, measureEntropy, hX, hfX, hμ, Set.indicator, apply_ite]

theorem entropy_comm : H[fun ω => (X ω, Y ω) ; μ] = H[fun ω => (Y ω, X ω) ; μ] :=
  entropy_comp_of_injective μ (X := fun ω => (Y ω, X ω)) Prod.swap_injective

theorem entropy_assoc :
    H[fun ω => ((X ω, Y ω), Z ω) ; μ] = H[fun ω => (X ω, (Y ω, Z ω)) ; μ] :=
  entropy_comp_of_injective μ (X := fun ω => (X ω, (Y ω, Z ω)))
    (Equiv.prodAssoc S T U).symm.injective

theorem entropy_pair_comp (g : S → T) : H[fun ω => (X ω, g (X ω)) ; μ] = H[X ; μ] :=
  entropy_comp_of_injective μ (X := X) (f := fun s => (s, g s)) fun _ _ h => congrArg Prod.fst h

theorem entropy_comm_left :
    H[fun ω => ((X ω, Y ω), Z ω) ; μ] = H[fun ω => ((Y ω, X ω), Z ω) ; μ] :=
  entropy_comp_of_injective μ (X := fun ω => ((Y ω, X ω), Z ω)) (f := fun p => (p.1.swap, p.2))
    fun _ _ h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Prod.swap_injective h.1) h.2

theorem entropy_pair_pair_comp (g : T → U) :
    H[fun ω => (X ω, (Y ω, g (Y ω))) ; μ] = H[fun ω => (X ω, Y ω) ; μ] :=
  entropy_comp_of_injective μ (X := fun ω => (X ω, Y ω))
    (f := fun p => (p.1, (p.2, g p.2)))
    fun _ _ h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 h.2.1

end Meat
