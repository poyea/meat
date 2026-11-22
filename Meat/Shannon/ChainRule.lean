import Meat.Shannon.Conditional

open MeasureTheory

namespace Meat

def seqPrefix {S : Type*} {n : ℕ} (y : Fin n → S) (i : Fin n) : Fin i → S :=
  fun j => y ⟨j, j.2.trans i.2⟩

variable {Ω S U V : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

section Relabel

variable {A B C : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] (μ : Measure Ω)

theorem condEntropy_cond_of_injective {X : Ω → A} {Z : Ω → B} {Z' : Ω → C} {e : B → C}
    (he : Function.Injective e) (hZ : ∀ ω, Z' ω = e (Z ω)) :
    H[X | Z' ; μ] = H[X | Z ; μ] := by
  obtain rfl : Z' = fun ω => e (Z ω) := funext hZ
  have h1 : H[fun ω => (X ω, e (Z ω)) ; μ] = H[fun ω => (X ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Z ω)) (f := fun p => (p.1, e p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (he h.2)
  have h2 : H[fun ω => e (Z ω) ; μ] = H[Z ; μ] := entropy_comp_of_injective μ he
  rw [condEntropy_def, condEntropy_def, h1, h2]

theorem condEntropy_pair_eq_add {X : Ω → A} {Y : Ω → B} {Z : Ω → C} :
    H[fun ω => (X ω, Y ω) | Z ; μ] = H[X | Z ; μ] + H[Y | fun ω => (X ω, Z ω) ; μ] := by
  have h : H[fun ω => (Y ω, (X ω, Z ω)) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω))
      (f := fun p => (p.1.2, (p.1.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.2.1 h.1) h.2.2
  simp only [condEntropy_def]
  rw [h]
  ring

end Relabel

theorem condEntropy_eq_sum (μ : Measure Ω) {n : ℕ} (Y : Ω → Fin n → S) (W : Ω → U) :
    H[Y | W ; μ] = ∑ i, H[fun ω => Y ω i | fun ω => (W ω, seqPrefix (Y ω) i) ; μ] := by
  induction n with
  | zero =>
    have h : H[fun ω => (Y ω, W ω) ; μ] = H[W ; μ] := by
      rw [← entropy_comp_of_injective μ (X := W) (f := fun u => ((fun i => i.elim0 : Fin 0 → S), u))
        (fun a b h => congrArg Prod.snd h)]
      congr 1
      funext ω
      exact Prod.ext (funext fun i => i.elim0) rfl
    rw [condEntropy_def, h]
    simp
  | succ n ih =>
    have hf : Function.Injective fun y : Fin (n + 1) → S => (Fin.init y, y (Fin.last n)) :=
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        rw [← Fin.snoc_init_self a, ← Fin.snoc_init_self b, h.1, h.2]
    have e1 : H[Y | W ; μ] = H[fun ω => (Fin.init (Y ω), Y ω (Fin.last n)) | W ; μ] :=
      (condEntropy_comp_of_injective μ (X := Y) hf).symm
    have e2 : H[fun ω => Y ω (Fin.last n) | fun ω => (Fin.init (Y ω), W ω) ; μ]
        = H[fun ω => Y ω (Fin.last n) | fun ω => (W ω, seqPrefix (Y ω) (Fin.last n)) ; μ] :=
      (condEntropy_cond_of_injective μ (Z := fun ω => (Fin.init (Y ω), W ω))
        (e := Prod.swap) Prod.swap_injective fun ω => rfl).symm
    rw [e1, condEntropy_pair_eq_add, e2, Fin.sum_univ_castSucc, ih fun ω => Fin.init (Y ω)]
    rfl

theorem entropy_eq_sum (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (Y : Ω → Fin n → S) :
    H[Y ; μ] = ∑ i, H[fun ω => Y ω i | fun ω => seqPrefix (Y ω) i ; μ] := by
  have h0 : H[Y | fun _ => () ; μ] = H[Y ; μ] := by
    have h1 : H[fun ω => (Y ω, ()) ; μ] = H[Y ; μ] :=
      entropy_comp_of_injective μ (X := Y) (f := fun y => (y, ())) fun a b h => congrArg Prod.fst h
    have h2 : H[fun _ : Ω => () ; μ] = 0 := by
      have := entropy_le_log_card μ (X := fun _ : Ω => ())
      simp only [Fintype.card_unit, Nat.cast_one, Real.log_one] at this
      exact le_antisymm this (entropy_nonneg μ _)
    rw [condEntropy_def, h1, h2, sub_zero]
  rw [← h0, condEntropy_eq_sum]
  exact Finset.sum_congr rfl fun i _ => condEntropy_cond_of_injective μ
    (Z := fun ω => seqPrefix (Y ω) i) (e := fun q => ((), q))
    (fun a b h => congrArg Prod.snd h) fun ω => rfl

theorem condMutualInfo_eq_sum (μ : Measure Ω) {n : ℕ} (Y : Ω → Fin n → S) (W : Ω → U)
    (Z : Ω → V) :
    I[Y : W | Z ; μ] =
      ∑ i, I[fun ω => Y ω i : W | fun ω => (Z ω, seqPrefix (Y ω) i) ; μ] := by
  rw [condMutualInfo_comm, condMutualInfo_eq_condEntropy_sub_condEntropy, condEntropy_eq_sum,
    condEntropy_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [condMutualInfo_comm, condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  exact condEntropy_cond_of_injective μ (Z := fun ω => (W ω, (Z ω, seqPrefix (Y ω) i)))
    (e := fun q => ((q.1, q.2.1), q.2.2)) (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)) fun ω => rfl

theorem mutualInfo_eq_sum (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (Y : Ω → Fin n → S)
    (W : Ω → U) :
    I[Y : W ; μ] = ∑ i, I[fun ω => Y ω i : W | fun ω => seqPrefix (Y ω) i ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy, entropy_eq_sum, condEntropy_eq_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [condMutualInfo_comm, condMutualInfo_eq_condEntropy_sub_condEntropy]

end Meat
