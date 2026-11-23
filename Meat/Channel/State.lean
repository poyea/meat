import Meat.Channel.Basic
import Meat.Shannon.Combinatorial

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

structure StateCode (M St A B : Type*) (n : ℕ) where
  enc : M → (Fin n → St) → Fin n → A
  dec : (Fin n → B) → M

namespace StateCode

variable {M St A B : Type*} {n : ℕ}

noncomputable def avgError [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : StateCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) : ℝ≥0∞ :=
  (∑ m, ∑ s : Fin n → St, (∏ i, pS (s i)) *
    ∑ y : Fin n → B, if c.dec y = m then 0 else ∏ i, W (c.enc m s i, s i) (y i)) /
    (Fintype.card M : ℝ≥0∞)

end StateCode

namespace GelfandPinsker

variable {St A B : Type*}

def Achievable [Fintype St] [Fintype B] (W : DMC (A × St) B) (pS : PMF St) (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : StateCode (Fin k) St A B n, c.avgError W pS ≤ ε

noncomputable def capacity [Fintype St] [Fintype B] (W : DMC (A × St) B) (pS : PMF St) : ℝ :=
  sSup {R | Achievable W pS R}

noncomputable def jointLaw {m : ℕ} (W : DMC (A × St) B) (q : PMF (St × Fin m × A)) :
    PMF ((St × Fin m × A) × B) :=
  q.bind fun a => (W (a.2.2, a.1)).map fun y => (a, y)

noncomputable def infoCapacity [Fintype St] [MeasurableSpace St] [MeasurableSpace A]
    [Fintype B] [MeasurableSpace B] (W : DMC (A × St) B) (pS : PMF St) : ℝ :=
  sSup {v | ∃ (m : ℕ) (q : PMF (St × Fin m × A)), q.map Prod.fst = pS ∧
    v = I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.2 ; (jointLaw W q).toMeasure] -
      I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.1.1 ; (jointLaw W q).toMeasure]}

end GelfandPinsker

section Csiszar

variable {Ω A B C D : Type*} [MeasurableSpace Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
  (μ : Measure Ω)

private lemma cmi_pair_eq {E F : Type*} [Fintype E] [MeasurableSpace E]
    [MeasurableSingletonClass E] [Fintype F] [MeasurableSpace F] [MeasurableSingletonClass F]
    {X : Ω → A} {Y : Ω → E} {Z : Ω → C} {V : Ω → F} :
    I[X : fun ω => (Y ω, V ω) | Z ; μ] =
      I[X : Y | Z ; μ] + I[X : V | fun ω => (Y ω, Z ω) ; μ] := by
  have e1 : H[fun ω => (X ω, (Y ω, Z ω)) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    (entropy_assoc μ).symm
  have e2 : H[fun ω => (V ω, (Y ω, Z ω)) ; μ] = H[fun ω => ((Y ω, V ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((Y ω, V ω), Z ω))
      (f := fun p => (p.1.2, (p.1.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.2.1 h.1) h.2.2
  have e3 : H[fun ω => ((X ω, V ω), (Y ω, Z ω)) ; μ]
      = H[fun ω => ((X ω, (Y ω, V ω)), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, (Y ω, V ω)), Z ω))
      (f := fun p => ((p.1.1, p.1.2.2), (p.1.2.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 (Prod.ext h.2.1 h.1.2)) h.2.2
  simp only [condMutualInfo_def, condEntropy_def]
  rw [e1, e2, e3]
  ring

private lemma cmi_right_inj {E F : Type*} [Fintype E] [MeasurableSpace E]
    [MeasurableSingletonClass E] [Fintype F] [MeasurableSpace F] [MeasurableSingletonClass F]
    {X : Ω → A} {Y : Ω → E} {Y' : Ω → F} {Z : Ω → C} {f : E → F} (hf : Function.Injective f)
    (hY : ∀ ω, Y' ω = f (Y ω)) : I[X : Y' | Z ; μ] = I[X : Y | Z ; μ] := by
  obtain rfl : Y' = fun ω => f (Y ω) := funext hY
  have h1 : H[fun ω => (f (Y ω), Z ω) ; μ] = H[fun ω => (Y ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (Y ω, Z ω)) (f := fun p => (f p.1, p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (hf h.1) h.2
  have h2 : H[fun ω => ((X ω, f (Y ω)), Z ω) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω))
      (f := fun p => ((p.1.1, f p.1.2), p.2)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 (hf h.1.2)) h.2
  simp only [condMutualInfo_def, condEntropy_def]
  rw [h1, h2]

private lemma cmi_cond_inj {E F : Type*} [Fintype E] [MeasurableSpace E]
    [MeasurableSingletonClass E] [Fintype F] [MeasurableSpace F] [MeasurableSingletonClass F]
    {X : Ω → A} {Y : Ω → B} {Z : Ω → E} {Z' : Ω → F} {e : E → F} (he : Function.Injective e)
    (hZ : ∀ ω, Z' ω = e (Z ω)) : I[X : Y | Z' ; μ] = I[X : Y | Z ; μ] := by
  obtain rfl : Z' = fun ω => e (Z ω) := funext hZ
  have h1 : H[fun ω => (X ω, e (Z ω)) ; μ] = H[fun ω => (X ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Z ω)) (f := fun p => (p.1, e p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (he h.2)
  have h2 : H[fun ω => (Y ω, e (Z ω)) ; μ] = H[fun ω => (Y ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (Y ω, Z ω)) (f := fun p => (p.1, e p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (he h.2)
  have h3 : H[fun ω => ((X ω, Y ω), e (Z ω)) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω)) (f := fun p => (p.1, e p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (he h.2)
  have h4 : H[fun ω => e (Z ω) ; μ] = H[Z ; μ] := entropy_comp_of_injective μ he
  simp only [condMutualInfo_def, condEntropy_def]
  rw [h1, h2, h3, h4]

private lemma cmi_const {E : Type*} [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]
    {X : Ω → A} {Z : Ω → C} (c : E) : I[X : fun _ => c | Z ; μ] = 0 := by
  have h1 : H[fun ω => (c, Z ω) ; μ] = H[Z ; μ] :=
    entropy_comp_of_injective μ (X := Z) (f := fun z => (c, z)) fun a b h => congrArg Prod.snd h
  have h2 : H[fun ω => ((X ω, c), Z ω) ; μ] = H[fun ω => (X ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Z ω)) (f := fun p => ((p.1, c), p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.1 h.2
  simp only [condMutualInfo_def, condEntropy_def]
  rw [h1, h2]
  ring

variable {n : ℕ}

omit [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
  [MeasurableSingletonClass D] in
private lemma cmi_finset_congr {X : Ω → A} {V : Ω → D} {Z : Ω → C} (S : Ω → Fin n → B)
    {A₁ A₂ : Finset (Fin n)} (h : A₁ = A₂) :
    I[X : V | fun ω => (seqRestrict (S ω) A₁, Z ω) ; μ] =
      I[X : V | fun ω => (seqRestrict (S ω) A₂, Z ω) ; μ] := by
  subst h
  rfl

theorem condMutualInfo_restrict_eq_sum_min (X : Ω → A) (S : Ω → Fin n → B) (Z : Ω → C)
    (A₀ : Finset (Fin n)) :
    I[X : fun ω => seqRestrict (S ω) A₀ | Z ; μ] =
      ∑ j ∈ A₀, I[X : fun ω => S ω j |
        fun ω => (seqRestrict (S ω) (A₀.filter fun x => j < x), Z ω) ; μ] := by
  classical
  induction A₀ using Finset.induction_on_min with
  | empty =>
    rw [sum_empty]
    have : (fun ω => seqRestrict (S ω) (∅ : Finset (Fin n))) =
        fun _ => (fun j => (Finset.notMem_empty _ j.2).elim : (∅ : Finset (Fin n)) → B) :=
      funext fun ω => funext fun j => (Finset.notMem_empty _ j.2).elim
    rw [this, cmi_const]
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have e1 : I[X : fun ω => seqRestrict (S ω) (insert a s) | Z ; μ] =
        I[X : fun ω => (seqRestrict (S ω) s, S ω a) | Z ; μ] :=
      (cmi_right_inj μ (Y := fun ω => seqRestrict (S ω) (insert a s))
        (f := fun g : ↥(insert a s) → B =>
        (fun j : s => g ⟨j, mem_insert_of_mem j.2⟩, g ⟨a, mem_insert_self a s⟩))
        (fun g g' h => by
          simp only [Prod.mk.injEq] at h
          funext j
          obtain ⟨j, hj⟩ := j
          rcases mem_insert.1 hj with rfl | hj'
          · exact h.2
          · exact congrFun h.1 ⟨j, hj'⟩) fun ω => rfl).symm
    have hfa : (insert a s).filter (fun x => a < x) = s := by
      ext x
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hx
      · exact fun hx => ⟨Or.inr hx, ha x hx⟩
    have hfj : ∀ j ∈ s, (insert a s).filter (fun x => j < x) = s.filter fun x => j < x :=
      fun j hj => by
        ext x
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hx, hlt⟩
          · exact absurd (hlt.trans (ha j hj)) (lt_irrefl _)
          · exact ⟨hx, hlt⟩
        · exact fun h => ⟨Or.inr h.1, h.2⟩
    rw [e1, cmi_pair_eq, ih, sum_insert has, cmi_finset_congr μ S hfa, add_comm]
    congr 1
    exact sum_congr rfl fun j hj => cmi_finset_congr μ S (hfj j hj).symm

theorem condMutualInfo_restrict_eq_sum_max (X : Ω → A) (S : Ω → Fin n → B) (Z : Ω → C)
    (A₀ : Finset (Fin n)) :
    I[X : fun ω => seqRestrict (S ω) A₀ | Z ; μ] =
      ∑ j ∈ A₀, I[X : fun ω => S ω j |
        fun ω => (seqRestrict (S ω) (A₀.filter fun x => x < j), Z ω) ; μ] := by
  classical
  induction A₀ using Finset.induction_on_max with
  | empty =>
    rw [sum_empty]
    have : (fun ω => seqRestrict (S ω) (∅ : Finset (Fin n))) =
        fun _ => (fun j => (Finset.notMem_empty _ j.2).elim : (∅ : Finset (Fin n)) → B) :=
      funext fun ω => funext fun j => (Finset.notMem_empty _ j.2).elim
    rw [this, cmi_const]
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have e1 : I[X : fun ω => seqRestrict (S ω) (insert a s) | Z ; μ] =
        I[X : fun ω => (seqRestrict (S ω) s, S ω a) | Z ; μ] :=
      (cmi_right_inj μ (Y := fun ω => seqRestrict (S ω) (insert a s))
        (f := fun g : ↥(insert a s) → B =>
        (fun j : s => g ⟨j, mem_insert_of_mem j.2⟩, g ⟨a, mem_insert_self a s⟩))
        (fun g g' h => by
          simp only [Prod.mk.injEq] at h
          funext j
          obtain ⟨j, hj⟩ := j
          rcases mem_insert.1 hj with rfl | hj'
          · exact h.2
          · exact congrFun h.1 ⟨j, hj'⟩) fun ω => rfl).symm
    have hfa : (insert a s).filter (fun x => x < a) = s := by
      ext x
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hx
      · exact fun hx => ⟨Or.inr hx, ha x hx⟩
    have hfj : ∀ j ∈ s, (insert a s).filter (fun x => x < j) = s.filter fun x => x < j :=
      fun j hj => by
        ext x
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hx, hlt⟩
          · exact absurd ((ha j hj).trans hlt) (lt_irrefl _)
          · exact ⟨hx, hlt⟩
        · exact fun h => ⟨Or.inr h.1, h.2⟩
    rw [e1, cmi_pair_eq, ih, sum_insert has, cmi_finset_congr μ S hfa, add_comm]
    congr 1
    exact sum_congr rfl fun j hj => cmi_finset_congr μ S (hfj j hj).symm

theorem csiszar_sum (Y : Ω → Fin n → A) (S : Ω → Fin n → B) (V : Ω → C) :
    ∑ i, I[fun ω => seqRestrict (S ω) (Ioi i) : fun ω => Y ω i |
        fun ω => (V ω, seqRestrict (Y ω) (Iio i)) ; μ] =
      ∑ j, I[fun ω => seqRestrict (Y ω) (Iio j) : fun ω => S ω j |
        fun ω => (V ω, seqRestrict (S ω) (Ioi j)) ; μ] := by
  classical
  have hL : ∀ i, I[fun ω => seqRestrict (S ω) (Ioi i) : fun ω => Y ω i |
      fun ω => (V ω, seqRestrict (Y ω) (Iio i)) ; μ] =
      ∑ j ∈ Ioi i, I[fun ω => Y ω i : fun ω => S ω j |
        fun ω => (seqRestrict (S ω) (Ioi j), (V ω, seqRestrict (Y ω) (Iio i))) ; μ] := by
    intro i
    rw [condMutualInfo_comm, condMutualInfo_restrict_eq_sum_min]
    refine sum_congr rfl fun j hj => cmi_finset_congr μ S ?_
    ext x
    simp only [mem_filter, mem_Ioi] at hj ⊢
    exact ⟨fun h => h.2, fun h => ⟨hj.trans h, h⟩⟩
  have hR : ∀ j, I[fun ω => seqRestrict (Y ω) (Iio j) : fun ω => S ω j |
      fun ω => (V ω, seqRestrict (S ω) (Ioi j)) ; μ] =
      ∑ i ∈ Iio j, I[fun ω => S ω j : fun ω => Y ω i |
        fun ω => (seqRestrict (Y ω) (Iio i), (V ω, seqRestrict (S ω) (Ioi j))) ; μ] := by
    intro j
    rw [condMutualInfo_comm, condMutualInfo_restrict_eq_sum_max]
    refine sum_congr rfl fun i hi => cmi_finset_congr μ Y ?_
    ext x
    simp only [mem_filter, mem_Iio] at hi ⊢
    exact ⟨fun h => h.2, fun h => ⟨h.trans hi, h⟩⟩
  have hT : ∀ i j, I[fun ω => Y ω i : fun ω => S ω j |
      fun ω => (seqRestrict (S ω) (Ioi j), (V ω, seqRestrict (Y ω) (Iio i))) ; μ] =
      I[fun ω => S ω j : fun ω => Y ω i |
        fun ω => (seqRestrict (Y ω) (Iio i), (V ω, seqRestrict (S ω) (Ioi j))) ; μ] := by
    intro i j
    rw [condMutualInfo_comm]
    exact cmi_cond_inj μ (e := fun q => (q.2.2, (q.2.1, q.1))) (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2.2 (Prod.ext h.2.1 h.1)) fun ω => rfl
  simp only [hL, hR, hT]
  exact sum_comm' fun i j => by simp

end Csiszar

end Meat
