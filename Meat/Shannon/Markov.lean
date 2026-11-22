import Meat.Shannon.Inequalities

open MeasureTheory

namespace Meat

section Measure

variable {A B C : Type*}
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

private lemma measureEntropy_markov_eq_zero_iff (ν : Measure ((A × C) × B))
    [IsProbabilityMeasure ν] :
    measureEntropy (ν.map fun p => (p.1.1, p.2)) + measureEntropy (ν.map fun p => (p.1.2, p.2))
        - measureEntropy ν - measureEntropy (ν.map Prod.snd) = 0
      ↔ ∀ a c b, ν.real {((a, c), b)} * (ν.map Prod.snd).real {b}
        = (ν.map fun p => (p.1.1, p.2)).real {(a, b)}
          * (ν.map fun p => (p.1.2, p.2)).real {(c, b)} := by
  set f : (A × C) × B → A × B := fun p => (p.1.1, p.2)
  set g : (A × C) × B → C × B := fun p => (p.1.2, p.2)
  set P : A × B → ℝ := fun x => (ν.map f).real {x}
  set Q : C × B → ℝ := fun x => (ν.map g).real {x}
  set R : B → ℝ := fun b => (ν.map Prod.snd).real {b}
  set N : (A × C) × B → ℝ := fun x => ν.real {x}
  let q : (A × C) × B → ℝ := fun x => P (f x) * Q (g x) / R x.2
  have hPR : ∀ a b, P (a, b) ≤ R b := fun a b => by
    have h := measureReal_singleton_le_map (ν.map f) Prod.snd (a, b)
    rwa [Measure.map_map measurable_snd (measurable_of_finite f)] at h
  have hNR : ∀ x, N x ≤ R x.2 := fun x => measureReal_singleton_le_map ν Prod.snd x
  have hsum : ∑ x, q x ≤ ∑ x, N x :=
    (sum_map_mul_map_div_map_le_one ν f g Prod.snd Prod.snd Prod.snd
      (fun x y h => by
        simp only [f, g, Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 h.2.1) h.1.2) (fun _ => rfl) (fun _ => rfl)).trans_eq
      (sum_measureReal_singleton_eq_one ν).symm
  have hq : ∀ x, 0 ≤ q x := fun x =>
    div_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) measureReal_nonneg
  have hNq : ∀ x, q x = 0 → N x = 0 := fun x h => by
    by_contra hx
    have h0 := measureReal_nonneg.lt_of_ne' hx
    exact (div_pos (mul_pos (h0.trans_le (measureReal_singleton_le_map ν f x))
      (h0.trans_le (measureReal_singleton_le_map ν g x))) (h0.trans_le (hNR x))).ne' h
  have hI : measureEntropy (ν.map f) + measureEntropy (ν.map g) - measureEntropy ν
      - measureEntropy (ν.map Prod.snd)
        = ∑ x, N x * Real.log (N x) - ∑ x, N x * Real.log (q x) := by
    have e := sum_mul_log_map_mul_map_div_map ν f g Prod.snd
    rw [measureEntropy_eq_neg_sum_mul_log ν]
    change _ = _ - ∑ x, ν.real {x} * Real.log ((ν.map f).real {f x} * (ν.map g).real {g x}
      / (ν.map Prod.snd).real {x.2})
    rw [e]
    ring
  rw [hI, sub_eq_zero, eq_comm, sum_mul_log_eq_sum_mul_log_iff Finset.univ
    (fun _ _ => measureReal_nonneg) (fun x _ => hq x) (fun x _ => hNq x) hsum]
  simp only [Finset.mem_univ, true_implies, Prod.forall]
  refine forall_congr' fun a => forall_congr' fun c => forall_congr' fun b => ?_
  change q ((a, c), b) = N ((a, c), b) ↔ N ((a, c), b) * R b = P (a, b) * Q (c, b)
  simp only [q, f, g]
  rcases eq_or_ne (R b) 0 with h | h
  · have hN : N ((a, c), b) = 0 := le_antisymm (h ▸ hNR _) measureReal_nonneg
    have hP : P (a, b) = 0 := le_antisymm (h ▸ hPR a b) measureReal_nonneg
    simp [h, hN, hP]
  · rw [div_eq_iff h, eq_comm]

end Measure

variable {Ω S T U : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]

def MarkovChain (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) : Prop :=
  I[X : Z | Y ; μ] = 0

variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U] in
theorem markovChain_def : MarkovChain X Y Z μ ↔ I[X : Z | Y ; μ] = 0 := Iff.rfl

theorem markovChain_comm : MarkovChain X Y Z μ ↔ MarkovChain Z Y X μ := by
  rw [markovChain_def, markovChain_def, condMutualInfo_comm]

theorem MarkovChain.symm (h : MarkovChain X Y Z μ) : MarkovChain Z Y X μ :=
  markovChain_comm.1 h

theorem markovChain_comp (f : T → U) : MarkovChain X Y (f ∘ Y) μ := by
  have h1 : H[fun ω => ((f ∘ Y) ω, Y ω) ; μ] = H[Y ; μ] :=
    entropy_comp_of_injective μ (X := Y) (f := fun t => (f t, t))
      fun _ _ h => congrArg Prod.snd h
  have h2 : H[fun ω => ((X ω, (f ∘ Y) ω), Y ω) ; μ] = H[fun ω => (X ω, Y ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Y ω))
      (f := fun p => ((p.1, f p.2), p.2)) fun _ _ h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.1 h.2
  rw [markovChain_def, condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def,
    h1, h2]
  ring

theorem mutualInfo_add_condMutualInfo_comm :
    I[X : Y ; μ] + I[X : Z | Y ; μ] = I[X : Z ; μ] + I[X : Y | Z ; μ] := by
  have h1 : H[fun ω => (Z ω, Y ω) ; μ] = H[fun ω => (Y ω, Z ω) ; μ] := entropy_comm μ
  have h2 : H[fun ω => ((X ω, Z ω), Y ω) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω))
      (f := fun p => ((p.1.1, p.2), p.1.2)) fun _ _ h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 h.2) h.1.2
  simp only [mutualInfo_def, condMutualInfo_def, condEntropy_def]
  rw [h1, h2]
  ring

variable [IsProbabilityMeasure μ]

theorem MarkovChain.mutualInfo_le_left (h : MarkovChain X Y Z μ) (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) : I[X : Z ; μ] ≤ I[X : Y ; μ] := by
  have h' := mutualInfo_add_condMutualInfo_comm (X := X) (Y := Y) (Z := Z) (μ := μ)
  have h0 := condMutualInfo_nonneg μ hX hY hZ
  rw [markovChain_def] at h
  linarith

theorem MarkovChain.mutualInfo_le_right (h : MarkovChain X Y Z μ) (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) : I[X : Z ; μ] ≤ I[Y : Z ; μ] := by
  rw [mutualInfo_comm μ (X := X), mutualInfo_comm μ (X := Y)]
  exact h.symm.mutualInfo_le_left hZ hY hX

theorem MarkovChain.condMutualInfo_le (h : MarkovChain X Y Z μ) (hX : Measurable X)
    (hZ : Measurable Z) : I[X : Y | Z ; μ] ≤ I[X : Y ; μ] := by
  have h' := mutualInfo_add_condMutualInfo_comm (X := X) (Y := Y) (Z := Z) (μ := μ)
  have h0 := mutualInfo_nonneg μ hX hZ
  rw [markovChain_def] at h
  linarith

theorem condEntropy_le_condEntropy_comp (hX : Measurable X) (hY : Measurable Y) (f : T → U) :
    H[X | Y ; μ] ≤ H[X | f ∘ Y ; μ] := by
  have h := condMutualInfo_nonneg μ hX hY ((measurable_of_finite f).comp hY)
  have h1 : H[fun ω => (Y ω, (f ∘ Y) ω) ; μ] = H[Y ; μ] := entropy_pair_comp μ f
  have h2 : H[fun ω => ((X ω, Y ω), (f ∘ Y) ω) ; μ] = H[fun ω => (X ω, Y ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Y ω))
      (f := fun p => (p, f p.2)) fun _ _ h => congrArg Prod.fst h
  simp only [condMutualInfo_def, condEntropy_def] at h ⊢
  rw [h1, h2] at h
  linarith

theorem markovChain_iff (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    MarkovChain X Y Z μ ↔ ∀ x y z,
      μ.real {ω | X ω = x ∧ Y ω = y ∧ Z ω = z} * μ.real {ω | Y ω = y}
        = μ.real {ω | X ω = x ∧ Y ω = y} * μ.real {ω | Y ω = y ∧ Z ω = z} := by
  let W : Ω → (S × U) × T := fun ω => ((X ω, Z ω), Y ω)
  have hW : Measurable W := (hX.prodMk hZ).prodMk hY
  have hf : (μ.map W).map (fun p => (p.1.1, p.2)) = μ.map fun ω => (X ω, Y ω) :=
    Measure.map_map (measurable_of_finite _) hW
  have hg : (μ.map W).map (fun p => (p.1.2, p.2)) = μ.map fun ω => (Z ω, Y ω) :=
    Measure.map_map (measurable_of_finite _) hW
  have hk : (μ.map W).map Prod.snd = μ.map Y := Measure.map_map measurable_snd hW
  have hI : I[X : Z | Y ; μ] = measureEntropy ((μ.map W).map fun p => (p.1.1, p.2))
      + measureEntropy ((μ.map W).map fun p => (p.1.2, p.2)) - measureEntropy (μ.map W)
      - measureEntropy ((μ.map W).map Prod.snd) := by
    rw [hf, hg, hk, condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def]
    simp only [entropy]
    ring
  rw [markovChain_def, hI, measureEntropy_markov_eq_zero_iff, hf, hg, hk]
  refine forall_congr' fun x => forall_comm.trans (forall_congr' fun y => forall_congr' fun z => ?_)
  rw [map_measureReal_apply hW (measurableSet_singleton _),
    map_measureReal_apply hY (measurableSet_singleton _),
    map_measureReal_apply (hX.prodMk hY) (measurableSet_singleton _),
    map_measureReal_apply (hZ.prodMk hY) (measurableSet_singleton _)]
  have e1 : W ⁻¹' {((x, z), y)} = {ω | X ω = x ∧ Y ω = y ∧ Z ω = z} := by
    ext
    simp only [W, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_ofPred_eq]
    tauto
  have e2 : (fun ω => (X ω, Y ω)) ⁻¹' {(x, y)} = {ω | X ω = x ∧ Y ω = y} := by
    ext
    simp
  have e3 : (fun ω => (Z ω, Y ω)) ⁻¹' {(z, y)} = {ω | Y ω = y ∧ Z ω = z} := by
    ext
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_ofPred_eq]
    tauto
  rw [e1, e2, e3]
  rfl

end Meat
