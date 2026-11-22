import Meat.Shannon.Markov
import Meat.Shannon.Product

open MeasureTheory

namespace Meat

variable {Ω S T U : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]

section Relabel

variable (μ : Measure Ω) {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

theorem condEntropy_comp_of_injective {f : S → T} (hf : Function.Injective f) :
    H[f ∘ X | Z ; μ] = H[X | Z ; μ] := by
  rw [condEntropy_def, condEntropy_def]
  congr 1
  exact entropy_comp_of_injective μ (X := fun ω => (X ω, Z ω)) (f := fun p => (f p.1, p.2))
    fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (hf h.1) h.2

theorem mutualInfo_comp_right_of_injective {f : T → U} (hf : Function.Injective f) :
    I[X : f ∘ Y ; μ] = I[X : Y ; μ] := by
  have h : H[fun ω => (X ω, (f ∘ Y) ω) ; μ] = H[fun ω => (X ω, Y ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Y ω)) (f := fun p => (p.1, f p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (hf h.2)
  rw [mutualInfo_def, mutualInfo_def, h, entropy_comp_of_injective μ hf]

theorem condMutualInfo_eq_condEntropy_sub_condEntropy :
    I[X : Y | Z ; μ] = H[Y | Z ; μ] - H[Y | fun ω => (X ω, Z ω) ; μ] := by
  have h : H[fun ω => ((X ω, Y ω), Z ω) ; μ] = H[fun ω => (Y ω, (X ω, Z ω)) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (Y ω, (X ω, Z ω)))
      (f := fun p => ((p.2.1, p.1), p.2.2)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.2 (Prod.ext h.1.1 h.2)
  simp only [condMutualInfo_def, condEntropy_def]
  rw [h]
  ring

end Relabel

theorem condEntropy_pi_le_sum (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    {Y : Ω → Fin n → S} {Z : Ω → U} (hY : ∀ i, Measurable fun ω => Y ω i) (hZ : Measurable Z) :
    H[Y | Z ; μ] ≤ ∑ i, H[fun ω => Y ω i | Z ; μ] := by
  induction n with
  | zero =>
    have h : H[fun ω => (Y ω, Z ω) ; μ] = H[Z ; μ] := by
      rw [← entropy_comp_of_injective μ (X := Z) (f := fun u => ((fun i => i.elim0 : Fin 0 → S), u))
        (fun a b h => congrArg Prod.snd h)]
      congr 1
      funext ω
      exact Prod.ext (funext fun i => i.elim0) rfl
    rw [condEntropy_def, h]
    simp
  | succ n ih =>
    have ht : Measurable fun ω (i : Fin n) => Y ω i.succ := measurable_pi_iff.2 fun i => hY i.succ
    have e : H[Y | Z ; μ] = H[fun ω => (Y ω 0, fun i : Fin n => Y ω i.succ) | Z ; μ] := by
      rw [← condEntropy_comp_of_injective μ (Fin.consEquiv fun _ => S).injective]
      congr 1
      funext ω i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.consEquiv_apply]
    have hsub := condMutualInfo_nonneg μ (hY 0) ht hZ
    rw [condMutualInfo_def] at hsub
    rw [e, Fin.sum_univ_succ]
    linarith [ih fun i => hY i.succ]

theorem mutualInfo_eq_zero_of_measureReal_eq_mul (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T}
    (h : ∀ s t,
      (μ.map fun ω => (X ω, Y ω)).real {(s, t)} = (μ.map X).real {s} * (μ.map Y).real {t}) :
    I[X : Y ; μ] = 0 := by
  have hP := sum_measureReal_singleton_eq_one (μ.map X)
  have hQ := sum_measureReal_singleton_eq_one (μ.map Y)
  rw [mutualInfo_def, entropy_def, entropy_def, entropy_def, Fintype.sum_prod_type]
  simp only [h, Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hP, hQ, one_mul]
  ring

end Meat
