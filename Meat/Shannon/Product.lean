import Meat.Shannon.Inequalities

open MeasureTheory

namespace Meat

variable {Ω Ω' S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]

omit [MeasurableSingletonClass S] in
theorem entropy_map (μ : Measure Ω) {g : Ω → Ω'} (hg : Measurable g) {X : Ω' → S}
    (hX : Measurable X) : H[X ; μ.map g] = H[X ∘ g ; μ] := by
  rw [entropy, entropy, Measure.map_map hX hg]

section Map

variable (μ : Measure Ω) {g : Ω → Ω'} (hg : Measurable g)
  {X : Ω' → S} {Y : Ω' → T} {Z : Ω' → U}
include hg

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem condEntropy_map (hX : Measurable X) (hY : Measurable Y) :
    H[X | Y ; μ.map g] = H[X ∘ g | Y ∘ g ; μ] := by
  rw [condEntropy_def, condEntropy_def, entropy_map μ hg (hX.prodMk hY), entropy_map μ hg hY]
  rfl

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem mutualInfo_map (hX : Measurable X) (hY : Measurable Y) :
    I[X : Y ; μ.map g] = I[X ∘ g : Y ∘ g ; μ] := by
  rw [mutualInfo_def, mutualInfo_def, entropy_map μ hg (hX.prodMk hY), entropy_map μ hg hX,
    entropy_map μ hg hY]
  rfl

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U] in
theorem condMutualInfo_map (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    I[X : Y | Z ; μ.map g] = I[X ∘ g : Y ∘ g | Z ∘ g ; μ] := by
  rw [condMutualInfo_def, condMutualInfo_def, condEntropy_map μ hg hX hZ,
    condEntropy_map μ hg hY hZ, condEntropy_map μ hg (hX.prodMk hY) hZ]
  rfl

end Map

omit [MeasurableSingletonClass S] in
theorem entropy_eq_log_card (μ : Measure Ω) {X : Ω → S}
    (h : ∀ s, (μ.map X).real {s} = (Fintype.card S : ℝ)⁻¹) :
    H[X ; μ] = Real.log (Fintype.card S) := by
  rw [entropy_def]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog, Real.log_inv]
  rcases eq_or_ne (Fintype.card S : ℝ) 0 with h0 | h0
  · simp [h0]
  · field_simp

theorem entropy_pi_le_sum (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} {Y : Ω → Fin n → S}
    (hY : ∀ i, Measurable fun ω => Y ω i) : H[Y ; μ] ≤ ∑ i, H[fun ω => Y ω i ; μ] := by
  induction n with
  | zero => simpa using entropy_le_log_card μ (X := Y)
  | succ n ih =>
    have ht : Measurable fun ω (i : Fin n) => Y ω i.succ := measurable_pi_iff.2 fun i => hY i.succ
    have e : H[Y ; μ] = H[fun ω => (Y ω 0, fun i : Fin n => Y ω i.succ) ; μ] := by
      rw [← entropy_comp_of_injective μ (Fin.consEquiv fun _ => S).injective]
      congr 1
      funext ω i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.consEquiv_apply]
    rw [e, Fin.sum_univ_succ]
    exact (entropy_pair_le_add μ (hY 0) ht).trans
      (add_le_add_right (ih fun i => hY i.succ) _)

end Meat
