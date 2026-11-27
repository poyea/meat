import Meat.Open.BroadcastConverse
import Meat.Channel.WiretapCK

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

namespace BC

variable {A B₁ B₂ : Type*}

section Info

variable {Ω E₁ E₂ E₃ E₄ E₅ E₆ E₇ : Type*} [MeasurableSpace Ω]
  [Fintype E₁] [MeasurableSpace E₁] [MeasurableSingletonClass E₁]
  [Fintype E₂] [MeasurableSpace E₂] [MeasurableSingletonClass E₂]
  [Fintype E₃] [MeasurableSpace E₃] [MeasurableSingletonClass E₃]
  [Fintype E₄] [MeasurableSpace E₄] [MeasurableSingletonClass E₄]
  [Fintype E₅] [MeasurableSpace E₅] [MeasurableSingletonClass E₅]
  [Fintype E₆] [MeasurableSpace E₆] [MeasurableSingletonClass E₆]
  [Fintype E₇] [MeasurableSpace E₇] [MeasurableSingletonClass E₇]
  (μ : Measure Ω)

private lemma cmi_pair_left {X : Ω → E₁} {Y : Ω → E₂} {Z : Ω → E₃} {V : Ω → E₄} :
    I[fun ω => (Y ω, V ω) : X | Z ; μ] =
      I[Y : X | Z ; μ] + I[V : X | fun ω => (Y ω, Z ω) ; μ] := by
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
  rw [condMutualInfo_comm, condMutualInfo_comm μ (X := Y), condMutualInfo_comm μ (X := V)]
  simp only [condMutualInfo_def, condEntropy_def]
  rw [e1, e2, e3]
  ring

private lemma cmi_left_inj {X : Ω → E₁} {Y : Ω → E₂} {Z : Ω → E₃} {X' : Ω → E₄}
    {f : E₁ → E₄} (hf : Function.Injective f) (hX : ∀ ω, X' ω = f (X ω)) :
    I[X' : Y | Z ; μ] = I[X : Y | Z ; μ] := by
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy,
    condMutualInfo_eq_condEntropy_sub_condEntropy,
    condEntropy_cond_of_injective μ (Z := fun ω => (X ω, Z ω)) (Z' := fun ω => (X' ω, Z ω))
      (e := fun p => (f p.1, p.2)) (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (hf h.1) h.2) fun ω => by rw [hX]]

omit [MeasurableSingletonClass E₅] in
private lemma rate_le_of_pair [Finite Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure μ]
    {Mx : Ω → E₁} {D : Ω → E₂}
    {Aa : Ω → E₃} {T : Ω → E₄} {K : Ω → E₅}
    (h : I[T : fun ω => ((Mx ω, Aa ω), D ω) ; μ] = I[K : T ; μ]) :
    I[Mx : T | D ; μ] + I[Aa : T | fun ω => (Mx ω, D ω) ; μ] ≤ I[K : T ; μ] := by
  have e1 := cmi_pair_left μ (X := T) (Y := Mx) (V := Aa) (Z := D)
  have e2 := mutualInfo_pair_eq_add_condMutualInfo μ (X := T)
    (Y := fun ω => (Mx ω, Aa ω)) (Z := D)
  have e3 := condMutualInfo_comm μ (X := fun ω => (Mx ω, Aa ω)) (Y := T) (Z := D)
  have n1 := mutualInfo_nonneg μ (X := T) (Y := D) (measurable_of_finite _)
    (measurable_of_finite _)
  linarith

private lemma cmi_cond_inj {X : Ω → E₁} {Y : Ω → E₂} {Z : Ω → E₃} {Z' : Ω → E₄}
    {e : E₃ → E₄} (he : Function.Injective e) (hZ : ∀ ω, Z' ω = e (Z ω)) :
    I[X : Y | Z' ; μ] = I[X : Y | Z ; μ] := by
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy, condMutualInfo_eq_condEntropy_sub_condEntropy,
    condEntropy_cond_of_injective μ he hZ]
  congr 1
  exact condEntropy_cond_of_injective μ (Z := fun ω => (X ω, Z ω))
    (e := fun p => (p.1, e p.2)) (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (he h.2)) fun ω => by rw [hZ]

private lemma mi_left_inj {X : Ω → E₁} {Y : Ω → E₂} {X' : Ω → E₃} {f : E₁ → E₃}
    (hf : Function.Injective f) (hX : ∀ ω, X' ω = f (X ω)) :
    I[X' : Y ; μ] = I[X : Y ; μ] := by
  obtain rfl : X' = fun ω => f (X ω) := funext hX
  rw [mutualInfo_comm, mutualInfo_comm μ (X := X)]
  exact mutualInfo_comp_right_of_injective μ hf

omit [MeasurableSingletonClass E₆] in
private lemma sum_le_of_relabel [Finite Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure μ]
    {Mx : Ω → E₁} {My : Ω → E₂} {Aa : Ω → E₃} {D : Ω → E₄} {S : Ω → E₅} {K : Ω → E₆}
    (hA : I[My : S | fun ω => (D ω, (Mx ω, Aa ω)) ; μ] = I[My : S | K ; μ]) :
    I[fun ω => (Mx ω, My ω) : S | Aa ; μ] - I[Mx : S | Aa ; μ] ≤
      I[D : S | fun ω => (Mx ω, Aa ω) ; μ] + I[My : S | K ; μ] := by
  have e1 := cmi_pair_left μ (X := S) (Y := Mx) (V := My) (Z := Aa)
  have e2 := cmi_pair_left μ (X := S) (Y := D) (V := My) (Z := fun ω => (Mx ω, Aa ω))
  have e3 : I[My : S | fun ω => (Mx ω, Aa ω) ; μ] ≤
      I[fun ω => (D ω, My ω) : S | fun ω => (Mx ω, Aa ω) ; μ] :=
    condMutualInfo_comp_left_le (μ := μ) (X := fun ω => (D ω, My ω)) (Y := S)
      (Z := fun ω => (Mx ω, Aa ω)) (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) Prod.snd
  linarith
end Info

section Mask

variable {n : ℕ}

private def uvMask (q : Fin n) (d : B₁ × B₂) (y : Fin n → B₁ × B₂) : Fin n → B₁ × B₂ :=
  fun j => if j = q then d else if j < q then ((y j).1, d.2) else (d.1, (y j).2)

private def maskOf (q : Fin n) (d : B₁ × B₂) (p : (↥(Iio q) → B₁) × (↥(Ioi q) → B₂)) :
    Fin n → B₁ × B₂ :=
  fun j => if h : j < q then (p.1 ⟨j, mem_Iio.2 h⟩, d.2)
    else if h' : q < j then (d.1, p.2 ⟨j, mem_Ioi.2 h'⟩) else d

private def pastOf (q : Fin n) (k : Fin n → B₁ × B₂) : ↥(Iio q) → B₁ := fun t => (k t).1

private def futureOf (q : Fin n) (k : Fin n → B₁ × B₂) : ↥(Ioi q) → B₂ := fun t => (k t).2

private lemma pastOf_maskOf (q : Fin n) (d : B₁ × B₂) (p : (↥(Iio q) → B₁) × (↥(Ioi q) → B₂)) :
    pastOf q (maskOf q d p) = p.1 := by
  funext t
  have ht : (t : Fin n) < q := mem_Iio.1 t.2
  simp [pastOf, maskOf, ht]

private lemma futureOf_maskOf (q : Fin n) (d : B₁ × B₂)
    (p : (↥(Iio q) → B₁) × (↥(Ioi q) → B₂)) : futureOf q (maskOf q d p) = p.2 := by
  funext t
  have ht : q < (t : Fin n) := mem_Ioi.1 t.2
  simp [futureOf, maskOf, ht, not_lt_of_gt ht]

private lemma maskOf_injective (q : Fin n) (d : B₁ × B₂) : Function.Injective (maskOf q d) :=
  fun p p' h => Prod.ext (by rw [← pastOf_maskOf q d p, h, pastOf_maskOf])
    (by rw [← futureOf_maskOf q d p, h, futureOf_maskOf])

private lemma uvMask_eq (q : Fin n) (d : B₁ × B₂) (y : Fin n → B₁ × B₂) :
    uvMask q d y = maskOf q d (seqRestrict (fun j => (y j).1) (Iio q),
      seqRestrict (fun j => (y j).2) (Ioi q)) := by
  funext j
  rcases lt_trichotomy j q with h | rfl | h
  · simp [uvMask, maskOf, h, h.ne, seqRestrict]
  · simp [uvMask, maskOf]
  · simp [uvMask, maskOf, h, h.ne', not_lt_of_gt h, seqRestrict]

private lemma sum_uvMask [Fintype B₁] [Fintype B₂] [DecidableEq B₁] [DecidableEq B₂]
    (g : Fin n → B₁ × B₂ → ℝ≥0∞)
    (hg : ∀ j, ∑ b, g j b = 1) (q : Fin n) (d : B₁ × B₂) (a : Fin n → B₁ × B₂)
    (y : B₁ × B₂) :
    ∑ z : Fin n → B₁ × B₂, (if uvMask q d z = a ∧ z q = y then ∏ j, g j (z j) else 0) =
      g q y * ∑ z : Fin n → B₁ × B₂, (if uvMask q d z = a then ∏ j, g j (z j) else 0) := by
  classical
  set F : Fin n → B₁ × B₂ → B₁ × B₂ := fun j b =>
    if j = q then d else if j < q then (b.1, d.2) else (d.1, b.2) with hF
  have hm : ∀ z, uvMask q d z = a ↔ ∀ j, F j (z j) = a j := fun z => by
    simp only [funext_iff, uvMask, hF]
  have e1 : ∀ z : Fin n → B₁ × B₂, (if uvMask q d z = a ∧ z q = y then ∏ j, g j (z j) else 0) =
      ∏ j : Fin n, (if F j (z j) = a j ∧ (j = q → z j = y) then g j (z j) else 0) := by
    intro z
    rw [Fintype.prod_ite_zero]
    congr 1
    rw [hm]
    exact propext ⟨fun h j => ⟨h.1 j, fun hj => hj ▸ h.2⟩, fun h => ⟨fun j => (h j).1, (h q).2 rfl⟩⟩
  have e2 : ∀ z : Fin n → B₁ × B₂, (if uvMask q d z = a then ∏ j, g j (z j) else 0) =
      ∏ j : Fin n, (if F j (z j) = a j then g j (z j) else 0) := by
    intro z
    rw [Fintype.prod_ite_zero]
    congr 1
    rw [hm]
  simp_rw [e1, e2]
  rw [← Fintype.prod_sum (fun (j : Fin n) (b : B₁ × B₂) => if F j b = a j ∧
      (j = q → b = y) then g j b else 0),
    ← Fintype.prod_sum (fun (j : Fin n) (b : B₁ × B₂) => if F j b = a j then g j b else 0),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ q),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
  have hrest : ∏ j ∈ Finset.univ.erase q, (∑ b, if F j b = a j ∧
      (j = q → b = y) then g j b else 0) =
      ∏ j ∈ Finset.univ.erase q, (∑ b, if F j b = a j then g j b else 0) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjq : j ≠ q := Finset.ne_of_mem_erase hj
    simp [hjq]
  rw [hrest, ← mul_assoc]
  congr 1
  by_cases ha : d = a q
  · simp [hF, ha, hg]
  · simp [hF, ha]

end Mask

section Letter

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂] {M₁ M₂ : Type*} [Fintype M₁] [Nonempty M₁] [MeasurableSpace M₁]
  [MeasurableSingletonClass M₁] [Fintype M₂] [Nonempty M₂] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] {n : ℕ}

omit [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B₁]
  [MeasurableSingletonClass B₁] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]
  [MeasurableSpace M₁] [MeasurableSingletonClass M₁] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] [Fintype A] in
private noncomputable def uvLetter (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n)
    (W : DMC A (B₁ × B₂)) (q : Fin n) (d : B₁ × B₂) :
    PMF (((M₁ × M₂) × (Fin n → B₁ × B₂)) × A × B₁ × B₂) :=
  (codePMF c W).map fun ω => ((ω.1, uvMask q d ω.2), c.enc ω.1 q, ω.2 q)

omit [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B₁]
  [MeasurableSingletonClass B₁] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]
  [MeasurableSpace M₁] [MeasurableSingletonClass M₁] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] [Fintype A] in
private lemma uvLetter_apply (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (q : Fin n) (d : B₁ × B₂) (u : (M₁ × M₂) × (Fin n → B₁ × B₂)) (x : A) (y : B₁ × B₂) :
    uvLetter c W q d (u, x, y) =
      ((uvLetter c W q d).map fun ω => (ω.1, ω.2.1)) (u, x) * W x y := by
  classical
  obtain ⟨u₁, u₂⟩ := u
  rw [uvLetter, PMF.map_comp, PMF.map_apply, PMF.map_apply, tsum_fintype, tsum_fintype,
    Fintype.sum_prod_type (α₁ := M₁ × M₂) (α₂ := Fin n → B₁ × B₂),
    Fintype.sum_prod_type (α₁ := M₁ × M₂) (α₂ := Fin n → B₁ × B₂), Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [codePMF, PMF.ofFintype_apply, Function.comp_def]
  by_cases hm : m = u₁ ∧ c.enc m q = x
  · obtain ⟨rfl, rfl⟩ := hm
    have e1 : ∀ (z : Fin n → B₁ × B₂) [Decidable (((m, u₂), c.enc m q, y) =
        ((m, uvMask q d z), c.enc m q, z q))], (if ((m, u₂), c.enc m q, y) =
        ((m, uvMask q d z), c.enc m q, z q) then (Fintype.card (M₁ × M₂) : ℝ≥0∞)⁻¹ *
          W.blockProb (c.enc m) z else 0) = (Fintype.card (M₁ × M₂) : ℝ≥0∞)⁻¹ *
        (if uvMask q d z = u₂ ∧ z q = y then ∏ j, W (c.enc m j) (z j) else 0) := by
      intro z _
      by_cases h : uvMask q d z = u₂ ∧ z q = y
      · simp [h, DMC.blockProb]
      · have : ((m, u₂), c.enc m q, y) ≠ ((m, uvMask q d z), c.enc m q, z q) := by
          intro h'
          simp only [Prod.mk.injEq] at h'
          exact h ⟨h'.1.2.symm, h'.2.2.symm⟩
        simp [h, this]
    have e2 : ∀ (z : Fin n → B₁ × B₂) [Decidable (((m, u₂), c.enc m q) =
        ((m, uvMask q d z), c.enc m q))], (if ((m, u₂), c.enc m q) =
        ((m, uvMask q d z), c.enc m q) then (Fintype.card (M₁ × M₂) : ℝ≥0∞)⁻¹ *
          W.blockProb (c.enc m) z else 0) = (Fintype.card (M₁ × M₂) : ℝ≥0∞)⁻¹ *
        (if uvMask q d z = u₂ then ∏ j, W (c.enc m j) (z j) else 0) := by
      intro z _
      by_cases h : uvMask q d z = u₂
      · simp [h, DMC.blockProb]
      · have : ((m, u₂), c.enc m q) ≠ ((m, uvMask q d z), c.enc m q) := by
          intro h'
          simp only [Prod.mk.injEq] at h'
          exact h h'.1.2.symm
        simp [h, this]
    simp_rw [e1, e2]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_uvMask (fun j b => W (c.enc m j) b)
      (fun j => sum_pmf_eq_one _) q d u₂ y]
    ring
  · have e1 : ∀ (z : Fin n → B₁ × B₂) [Decidable (((u₁, u₂), x, y) =
        ((m, uvMask q d z), c.enc m q, z q))],
        (if ((u₁, u₂), x, y) = ((m, uvMask q d z), c.enc m q, z q) then
        (Fintype.card (M₁ × M₂) : ℝ≥0∞)⁻¹ * W.blockProb (c.enc m) z else 0) = 0 :=
      fun z _ => by
        refine ite_eq_right_iff.2 fun h => absurd ?_ hm
        simp only [Prod.mk.injEq] at h
        exact ⟨h.1.1.symm, h.2.1.symm⟩
    have e2 : ∀ (z : Fin n → B₁ × B₂) [Decidable (((u₁, u₂), x) =
        ((m, uvMask q d z), c.enc m q))],
        (if ((u₁, u₂), x) = ((m, uvMask q d z), c.enc m q) then
        (Fintype.card (M₁ × M₂) : ℝ≥0∞)⁻¹ * W.blockProb (c.enc m) z else 0) = 0 :=
      fun z _ => by
        refine ite_eq_right_iff.2 fun h => absurd ?_ hm
        simp only [Prod.mk.injEq] at h
        exact ⟨h.1.1.symm, h.2.symm⟩
    simp_rw [e1, e2]
    simp

omit [Fintype A] [MeasurableSingletonClass A] in
private lemma uvLetter_toMeasure (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n)
    (W : DMC A (B₁ × B₂)) (q : Fin n) (d : B₁ × B₂) :
    (uvLetter c W q d).toMeasure = (c.codeMeasure W).map
      fun ω => ((ω.1, uvMask q d ω.2), c.enc ω.1 q, ω.2 q) :=
  (PMF.toMeasure_map _ _ (measurable_of_finite _)).symm

end Letter

section Rates

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂] {M₁ M₂ : Type*} [Fintype M₁] [Nonempty M₁] [MeasurableSpace M₁]
  [MeasurableSingletonClass M₁] [Fintype M₂] [Nonempty M₂] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] {n : ℕ}

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma letter_rate₁ (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (q : Fin n) (d : B₁ × B₂) :
    I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 : fun ω => (ω.2 q).1 |
        fun ω => seqRestrict (fun j => (ω.2 j).1) (Iio q) ; c.codeMeasure W] +
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => seqRestrict (fun j => (ω.2 j).2) (Ioi q) :
        fun ω => (ω.2 q).1 | fun ω => (ω.1.1, seqRestrict (fun j => (ω.2 j).1) (Iio q)) ;
        c.codeMeasure W] ≤
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.1, uvMask q d ω.2) :
        fun ω => (ω.2 q).1 ; c.codeMeasure W] := by
  refine rate_le_of_pair _ ?_
  let f : (M₁ × (↥(Ioi q) → B₂)) × (↥(Iio q) → B₁) → M₁ × (Fin n → B₁ × B₂) :=
    fun p => (p.1.1, maskOf q d (p.2, p.1.2))
  have hf : Function.Injective f := by
    rintro ⟨⟨m, a⟩, e⟩ ⟨⟨m', a'⟩, e'⟩ h
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (maskOf_injective q d h2)
    rfl
  have key : (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.1, uvMask q d ω.2)) =
      f ∘ fun ω => ((ω.1.1, seqRestrict (fun j => (ω.2 j).2) (Ioi q)),
        seqRestrict (fun j => (ω.2 j).1) (Iio q)) :=
    funext fun ω => by simp only [Function.comp, f, uvMask_eq]
  rw [key, ← mutualInfo_comp_right_of_injective _ hf, mutualInfo_comm]

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma letter_rate₂ (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (q : Fin n) (d : B₁ × B₂) :
    I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω => (ω.2 q).2 |
        fun ω => seqRestrict (fun j => (ω.2 j).2) (Ioi q) ; c.codeMeasure W] +
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => seqRestrict (fun j => (ω.2 j).1) (Iio q) :
        fun ω => (ω.2 q).2 | fun ω => (ω.1.2, seqRestrict (fun j => (ω.2 j).2) (Ioi q)) ;
        c.codeMeasure W] ≤
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.2, uvMask q d ω.2) :
        fun ω => (ω.2 q).2 ; c.codeMeasure W] := by
  refine rate_le_of_pair _ ?_
  let f : (M₂ × (↥(Iio q) → B₁)) × (↥(Ioi q) → B₂) → M₂ × (Fin n → B₁ × B₂) :=
    fun p => (p.1.1, maskOf q d (p.1.2, p.2))
  have hf : Function.Injective f := by
    rintro ⟨⟨m, e⟩, a⟩ ⟨⟨m', e'⟩, a'⟩ h
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (maskOf_injective q d h2)
    rfl
  have key : (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.2, uvMask q d ω.2)) =
      f ∘ fun ω => ((ω.1.2, seqRestrict (fun j => (ω.2 j).1) (Iio q)),
        seqRestrict (fun j => (ω.2 j).2) (Ioi q)) :=
    funext fun ω => by simp only [Function.comp, f, uvMask_eq]
  rw [key, ← mutualInfo_comp_right_of_injective _ hf, mutualInfo_comm]

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma letter_sum₁ (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (q : Fin n) (d : B₁ × B₂) :
    I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1 : fun ω => (ω.2 q).2 |
        fun ω => seqRestrict (fun j => (ω.2 j).2) (Ioi q) ; c.codeMeasure W] -
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 : fun ω => (ω.2 q).2 |
        fun ω => seqRestrict (fun j => (ω.2 j).2) (Ioi q) ; c.codeMeasure W] ≤
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => seqRestrict (fun j => (ω.2 j).1) (Iio q) :
        fun ω => (ω.2 q).2 | fun ω => (ω.1.1, seqRestrict (fun j => (ω.2 j).2) (Ioi q)) ;
        c.codeMeasure W] +
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω => (ω.2 q).2 |
        fun ω => (ω.1.1, uvMask q d ω.2) ; c.codeMeasure W] := by
  set μ := c.codeMeasure W
  let e : (↥(Iio q) → B₁) × M₁ × (↥(Ioi q) → B₂) → M₁ × (Fin n → B₁ × B₂) :=
    fun p => (p.2.1, maskOf q d (p.1, p.2.2))
  have he : Function.Injective e := by
    rintro ⟨x, m, a⟩ ⟨x', m', a'⟩ h
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (maskOf_injective q d h2)
    rfl
  have hA := cmi_cond_inj μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2)
    (Y := fun ω => (ω.2 q).2)
    (Z := fun ω => (seqRestrict (fun j => (ω.2 j).1) (Iio q),
      (ω.1.1, seqRestrict (fun j => (ω.2 j).2) (Ioi q))))
    (Z' := fun ω => (ω.1.1, uvMask q d ω.2)) he fun ω => by simp only [e, uvMask_eq]
  exact sum_le_of_relabel μ (Mx := fun ω => ω.1.1) (My := fun ω => ω.1.2) hA.symm

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma letter_sum₂ (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (q : Fin n) (d : B₁ × B₂) :
    I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1 : fun ω => (ω.2 q).1 |
        fun ω => seqRestrict (fun j => (ω.2 j).1) (Iio q) ; c.codeMeasure W] -
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω => (ω.2 q).1 |
        fun ω => seqRestrict (fun j => (ω.2 j).1) (Iio q) ; c.codeMeasure W] ≤
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => seqRestrict (fun j => (ω.2 j).2) (Ioi q) :
        fun ω => (ω.2 q).1 | fun ω => (ω.1.2, seqRestrict (fun j => (ω.2 j).1) (Iio q)) ;
        c.codeMeasure W] +
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 : fun ω => (ω.2 q).1 |
        fun ω => (ω.1.2, uvMask q d ω.2) ; c.codeMeasure W] := by
  set μ := c.codeMeasure W
  let e : (↥(Ioi q) → B₂) × M₂ × (↥(Iio q) → B₁) → M₂ × (Fin n → B₁ × B₂) :=
    fun p => (p.2.1, maskOf q d (p.2.2, p.1))
  have he : Function.Injective e := by
    rintro ⟨a, m, x⟩ ⟨a', m', x'⟩ h
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (maskOf_injective q d h2)
    rfl
  have hA := cmi_cond_inj μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1)
    (Y := fun ω => (ω.2 q).1)
    (Z := fun ω => (seqRestrict (fun j => (ω.2 j).2) (Ioi q),
      (ω.1.2, seqRestrict (fun j => (ω.2 j).1) (Iio q))))
    (Z' := fun ω => (ω.1.2, uvMask q d ω.2)) he fun ω => by simp only [e, uvMask_eq]
  have hs := cmi_left_inj μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1)
    (X' := fun ω => (ω.1.2, ω.1.1)) (Y := fun ω => (ω.2 q).1)
    (Z := fun ω => seqRestrict (fun j => (ω.2 j).1) (Iio q)) Prod.swap_injective fun ω => rfl
  rw [← hs]
  exact sum_le_of_relabel μ (Mx := fun ω => ω.1.2) (My := fun ω => ω.1.1) hA.symm
end Rates

section Sums

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂] {M₁ M₂ : Type*} [Fintype M₁] [Nonempty M₁] [MeasurableSpace M₁]
  [MeasurableSingletonClass M₁] [Fintype M₂] [Nonempty M₂] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] {n : ℕ}

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma sum_bound₁ (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (d : B₁ × B₂) :
    I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 : fun ω i => (ω.2 i).1 ;
        c.codeMeasure W] ≤
      ∑ q, I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.1, uvMask q d ω.2) :
        fun ω => (ω.2 q).1 ; c.codeMeasure W] := by
  rw [Wiretap.mutualInfo_eq_sum_Iio]
  refine Finset.sum_le_sum fun q _ => ?_
  have h1 := letter_rate₁ c W q d
  have h2 := condMutualInfo_nonneg (c.codeMeasure W)
    (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => seqRestrict (fun j => (ω.2 j).2) (Ioi q))
    (Y := fun ω => (ω.2 q).1)
    (Z := fun ω => (ω.1.1, seqRestrict (fun j => (ω.2 j).1) (Iio q)))
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
  exact le_trans (by linarith) h1

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma sum_bound₂ (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (d : B₁ × B₂) :
    I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω i => (ω.2 i).2 ;
        c.codeMeasure W] ≤
      ∑ q, I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.2, uvMask q d ω.2) :
        fun ω => (ω.2 q).2 ; c.codeMeasure W] := by
  rw [Wiretap.mutualInfo_eq_sum_Ioi]
  refine Finset.sum_le_sum fun q _ => ?_
  have h1 := letter_rate₂ c W q d
  have h2 := condMutualInfo_nonneg (c.codeMeasure W)
    (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => seqRestrict (fun j => (ω.2 j).1) (Iio q))
    (Y := fun ω => (ω.2 q).2)
    (Z := fun ω => (ω.1.2, seqRestrict (fun j => (ω.2 j).2) (Ioi q)))
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
  exact le_trans (by linarith) h1

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma sum_bound₃ (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (d : B₁ × B₂) :
    I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 : fun ω i => (ω.2 i).1 ;
        c.codeMeasure W] +
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).2 : fun ω => ω.1.2 |
        fun ω => ω.1.1 ; c.codeMeasure W] ≤
      ∑ q, I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.1, uvMask q d ω.2) :
        fun ω => (ω.2 q).1 ; c.codeMeasure W] +
      ∑ q, I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω => (ω.2 q).2 |
        fun ω => (ω.1.1, uvMask q d ω.2) ; c.codeMeasure W] := by
  set μ := c.codeMeasure W
  have e1 := mutualInfo_pair_eq_add_condMutualInfo μ
    (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).2)
    (Y := fun ω => ω.1.2) (Z := fun ω => ω.1.1)
  have e2 : I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).2 :
      fun ω => (ω.1.2, ω.1.1) ; μ] =
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1 : fun ω i => (ω.2 i).2 ; μ] :=
    (mutualInfo_comp_right_of_injective μ (Y := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1)
      (f := Prod.swap) Prod.swap_injective).trans (mutualInfo_comm _)
  have e3 := mutualInfo_comm μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) =>
    fun i => (ω.2 i).2) (Y := fun ω => ω.1.1)
  rw [Wiretap.mutualInfo_eq_sum_Ioi] at e2 e3
  rw [Wiretap.mutualInfo_eq_sum_Iio]
  have cs := csiszar_sum μ (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).1)
    (fun ω => fun i => (ω.2 i).2) fun ω => ω.1.1
  have s1 := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => letter_rate₁ c W q d
  have s2 := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => letter_sum₁ c W q d
  rw [Finset.sum_add_distrib] at s1 s2
  rw [Finset.sum_sub_distrib] at s2
  beta_reduce at e2 e3 cs ⊢
  linarith

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma sum_bound₄ (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (d : B₁ × B₂) :
    I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω i => (ω.2 i).2 ;
        c.codeMeasure W] +
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).1 : fun ω => ω.1.1 |
        fun ω => ω.1.2 ; c.codeMeasure W] ≤
      ∑ q, I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.2, uvMask q d ω.2) :
        fun ω => (ω.2 q).2 ; c.codeMeasure W] +
      ∑ q, I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 : fun ω => (ω.2 q).1 |
        fun ω => (ω.1.2, uvMask q d ω.2) ; c.codeMeasure W] := by
  set μ := c.codeMeasure W
  have e1 := mutualInfo_pair_eq_add_condMutualInfo μ
    (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).1)
    (Y := fun ω => ω.1.1) (Z := fun ω => ω.1.2)
  have e2 : I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).1 :
      fun ω => (ω.1.1, ω.1.2) ; μ] =
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1 : fun ω i => (ω.2 i).1 ; μ] :=
    mutualInfo_comm _
  have e3 := mutualInfo_comm μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) =>
    fun i => (ω.2 i).1) (Y := fun ω => ω.1.2)
  rw [Wiretap.mutualInfo_eq_sum_Iio] at e2 e3
  rw [Wiretap.mutualInfo_eq_sum_Ioi]
  have cs := csiszar_sum μ (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).1)
    (fun ω => fun i => (ω.2 i).2) fun ω => ω.1.2
  have s1 := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => letter_rate₂ c W q d
  have s2 := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => letter_sum₂ c W q d
  rw [Finset.sum_add_distrib] at s1 s2
  rw [Finset.sum_sub_distrib] at s2
  beta_reduce at e2 e3 cs ⊢
  linarith

end Sums

section Convert

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂] {M₁ M₂ : Type*} [Fintype M₁] [Nonempty M₁] [MeasurableSpace M₁]
  [MeasurableSingletonClass M₁] [Fintype M₂] [Nonempty M₂] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] {n : ℕ}

omit [Fintype A] in
private lemma letter_eq [Finite A] (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (q : Fin n) (d : B₁ × B₂) :
    I[fun ω : ((M₁ × M₂) × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => (ω.1.1.1, ω.1.2) :
        fun ω => ω.2.2.1 ; (uvLetter c W q d).toMeasure] =
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.1, uvMask q d ω.2) :
        fun ω => (ω.2 q).1 ; c.codeMeasure W] ∧
    I[fun ω : ((M₁ × M₂) × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => (ω.1.1.2, ω.1.2) :
        fun ω => ω.2.2.2 ; (uvLetter c W q d).toMeasure] =
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.2, uvMask q d ω.2) :
        fun ω => (ω.2 q).2 ; c.codeMeasure W] ∧
    I[fun ω : ((M₁ × M₂) × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.1.1.2 : fun ω => ω.2.2.2 |
        fun ω => (ω.1.1.1, ω.1.2) ; (uvLetter c W q d).toMeasure] =
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω => (ω.2 q).2 |
        fun ω => (ω.1.1, uvMask q d ω.2) ; c.codeMeasure W] ∧
    I[fun ω : ((M₁ × M₂) × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.1.1.1 : fun ω => ω.2.2.1 |
        fun ω => (ω.1.1.2, ω.1.2) ; (uvLetter c W q d).toMeasure] =
      I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 : fun ω => (ω.2 q).1 |
        fun ω => (ω.1.2, uvMask q d ω.2) ; c.codeMeasure W] := by
  rw [uvLetter_toMeasure]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
    rfl
  · rw [mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
    rfl
  · rw [condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  · rw [condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
    rfl

end Convert

section Fano

variable [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂]
  [MeasurableSpace B₂] [MeasurableSingletonClass B₂] {M₁ M₂ : Type*} [Fintype M₁] [Nonempty M₁]
  [MeasurableSpace M₁] [MeasurableSingletonClass M₁] [DecidableEq M₁] [Fintype M₂]
  [Nonempty M₂] [MeasurableSpace M₂] [MeasurableSingletonClass M₂] [DecidableEq M₂] {n : ℕ}

private lemma fano_bound (c : BCCode M₁ M₂ A B₁ B₂ n) (W : DMC A (B₁ × B₂)) :
    (1 - 2 * (c.avgError W).toReal) * Real.log (Fintype.card M₁) - Real.log 2 ≤
        I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 : fun ω i => (ω.2 i).1 ;
          (twinCode c).codeMeasure W] ∧
      (1 - 2 * (c.avgError W).toReal) * Real.log (Fintype.card M₂) - Real.log 2 ≤
        I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω i => (ω.2 i).2 ;
          (twinCode c).codeMeasure W] ∧
      (1 - 2 * (c.avgError W).toReal) * Real.log (Fintype.card M₂) - Real.log 2 ≤
        I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).2 : fun ω => ω.1.2 |
          fun ω => ω.1.1 ; (twinCode c).codeMeasure W] ∧
      (1 - 2 * (c.avgError W).toReal) * Real.log (Fintype.card M₁) - Real.log 2 ≤
        I[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).1 : fun ω => ω.1.1 |
          fun ω => ω.1.2 ; (twinCode c).codeMeasure W] := by
  set μ := (twinCode c).codeMeasure W
  set ε := (c.avgError W).toReal
  have hne : c.avgError W ≠ ∞ := by
    refine (ENNReal.div_lt_top (ENNReal.sum_ne_top.2 fun m _ => c.errorProb_ne_top W m)
      ?_).ne
    simp [Fintype.card_ne_zero]
  have herr : ∀ P : (M₁ × M₂) × (Fin n → B₁ × B₂) → Prop,
      (∀ ω, P ω → (twinCode c).dec ω.2 ≠ ω.1) → μ.real {ω | P ω} ≤ 2 * ε := by
    intro P hP
    calc μ.real {ω | P ω} ≤ μ.real {ω | (twinCode c).dec ω.2 ≠ ω.1} :=
          measureReal_mono fun ω h => hP ω h
      _ = ((twinCode c).avgError W).toReal := BlockCode.measureReal_dec_ne _ _
      _ ≤ (2 * c.avgError W).toReal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hne)
          (twinCode_avgError_le c rfl rfl)
      _ = 2 * ε := by rw [ENNReal.toReal_mul]; norm_num [ε]
  have hH : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.1, ω.1.2) ; μ] =
      Real.log (Fintype.card M₁) + Real.log (Fintype.card M₂) := by
    have := BlockCode.entropy_fst_codeMeasure (twinCode c) W
    rw [Fintype.card_prod, Nat.cast_mul, Real.log_mul (by simp [Fintype.card_ne_zero])
      (by simp [Fintype.card_ne_zero])] at this
    exact this
  have hs₁ := entropy_pair_eq_add_condEntropy
    (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1) (fun ω => ω.1.2) μ
  have hs₂ := entropy_pair_eq_add_condEntropy
    (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2) (fun ω => ω.1.1) μ
  have hc := entropy_comm μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1)
    (Y := fun ω => ω.1.2)
  have hM₁ := entropy_le_log_card μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1)
  have hM₂ := entropy_le_log_card μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2)
  have hc₁ := condEntropy_le_entropy μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1)
    (Y := fun ω => ω.1.2) (measurable_of_finite _) (measurable_of_finite _)
  have hc₂ := condEntropy_le_entropy μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2)
    (Y := fun ω => ω.1.1) (measurable_of_finite _) (measurable_of_finite _)
  have hl₁ : 0 ≤ Real.log (Fintype.card M₁) := Real.log_natCast_nonneg _
  have hl₂ : 0 ≤ Real.log (Fintype.card M₂) := Real.log_natCast_nonneg _
  have hF₁ : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 | fun ω i => (ω.2 i).1 ; μ] ≤
      Real.log 2 + μ.real {ω | c.dec₁ (fun i => (ω.2 i).1) ≠ ω.1.1} *
        Real.log (Fintype.card M₁) :=
    condEntropy_le_log_two_add_mul_log_card (measurable_of_finite _) (measurable_of_finite _)
      c.dec₁
  have hF₂ : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 | fun ω i => (ω.2 i).2 ; μ] ≤
      Real.log 2 + μ.real {ω | c.dec₂ (fun i => (ω.2 i).2) ≠ ω.1.2} *
        Real.log (Fintype.card M₂) :=
    condEntropy_le_log_two_add_mul_log_card (measurable_of_finite _) (measurable_of_finite _)
      c.dec₂
  have hP₁ := herr (fun ω => c.dec₁ (fun i => (ω.2 i).1) ≠ ω.1.1)
    fun ω h h' => h (congrArg Prod.fst h')
  have hP₂ := herr (fun ω => c.dec₂ (fun i => (ω.2 i).2) ≠ ω.1.2)
    fun ω h h' => h (congrArg Prod.snd h')
  have hm₁ := mul_le_mul_of_nonneg_right hP₁ hl₁
  have hm₂ := mul_le_mul_of_nonneg_right hP₂ hl₂
  have i1 := mutualInfo_eq_entropy_sub_condEntropy
    (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1) (fun ω i => (ω.2 i).1) μ
  have i2 := mutualInfo_eq_entropy_sub_condEntropy
    (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2) (fun ω i => (ω.2 i).2) μ
  have i3 := condMutualInfo_eq_condEntropy_sub_condEntropy μ
    (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).2)
    (Y := fun ω => ω.1.2) (Z := fun ω => ω.1.1)
  have i4 := condMutualInfo_eq_condEntropy_sub_condEntropy μ
    (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).1)
    (Y := fun ω => ω.1.1) (Z := fun ω => ω.1.2)
  have j3 : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 |
      fun ω => (fun i => (ω.2 i).2, ω.1.1) ; μ] ≤
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 | fun ω i => (ω.2 i).2 ; μ] :=
    condEntropy_le_condEntropy_comp (measurable_of_finite _) (measurable_of_finite _) Prod.fst
  have j4 : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 |
      fun ω => (fun i => (ω.2 i).1, ω.1.2) ; μ] ≤
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 | fun ω i => (ω.2 i).1 ; μ] :=
    condEntropy_le_condEntropy_comp (measurable_of_finite _) (measurable_of_finite _) Prod.fst
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end Fano

section Mixture

variable {R S T U : Type*} [Finite R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U] {n : ℕ} [NeZero n]

private lemma mixture_mutualInfo_ge (L : Fin n → PMF R) (G : R → S) (F : R → T) :
    (n : ℝ)⁻¹ * ∑ q, I[G : F ; (L q).toMeasure] ≤
      I[fun p : Fin n × R => (p.1, G p.2) : fun p => F p.2 ;
        (DMC.jointPMF L (unifPMF n)).toMeasure] := by
  rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy, condEntropy_mixture L F G]
  have b2 := entropy_mixture_ge L F
  have : ∑ q, I[G : F ; (L q).toMeasure] =
      ∑ q, H[F ; (L q).toMeasure] - ∑ q, H[F | G ; (L q).toMeasure] := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by
      rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
  rw [this, mul_sub]
  linarith

private lemma mixture_condMutualInfo (L : Fin n → PMF R) (X : R → S) (F : R → T) (G : R → U) :
    I[fun p : Fin n × R => X p.2 : fun p => F p.2 | fun p => (p.1, G p.2) ;
        (DMC.jointPMF L (unifPMF n)).toMeasure] =
      (n : ℝ)⁻¹ * ∑ q, I[X : F | G ; (L q).toMeasure] := by
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy,
    condEntropy_cond_of_injective _ (Z := fun p : Fin n × R => (p.1, (X p.2, G p.2)))
      (e := fun t => (t.2.1, (t.1, t.2.2))) (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)) fun _ => rfl,
    condEntropy_mixture L F G, condEntropy_mixture L F (fun r => (X r, G r)), ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun q _ => (condMutualInfo_eq_condEntropy_sub_condEntropy _).symm

end Mixture

private lemma factor_map {V V' : Type*} (W : DMC A (B₁ × B₂)) (σ : PMF (V × A × B₁ × B₂))
    {e : V → V'} (he : Function.Injective e)
    (h : ∀ v x y, σ (v, x, y) = (σ.map fun ω => (ω.1, ω.2.1)) (v, x) * W x y)
    (v' : V') (x : A) (y : B₁ × B₂) :
    (σ.map fun ω => (e ω.1, ω.2)) (v', x, y) =
      ((σ.map fun ω => (e ω.1, ω.2)).map fun ω => (ω.1, ω.2.1)) (v', x) * W x y := by
  rw [PMF.map_comp]
  by_cases hv : ∃ v, e v = v'
  · obtain ⟨v, rfl⟩ := hv
    have hc : ((fun ω : V' × A × B₁ × B₂ => (ω.1, ω.2.1)) ∘
        fun ω : V × A × B₁ × B₂ => (e ω.1, ω.2)) =
        (fun ω : V × A => (e ω.1, ω.2)) ∘ fun ω => (ω.1, ω.2.1) := rfl
    rw [hc, ← PMF.map_comp,
      show ((e v, x, y) : V' × A × B₁ × B₂) =
        (fun ω : V × A × B₁ × B₂ => (e ω.1, ω.2)) (v, x, y) from rfl,
      map_apply_inj _ (fun a b hab => by
        simp only [Prod.mk.injEq] at hab
        exact Prod.ext (he hab.1) hab.2),
      show ((e v, x) : V' × A) = (fun ω : V × A => (e ω.1, ω.2)) (v, x) from rfl,
      map_apply_inj _ (fun a b hab => by
        simp only [Prod.mk.injEq] at hab
        exact Prod.ext (he hab.1) hab.2), h]
  · have z1 : (σ.map fun ω => (e ω.1, ω.2)) (v', x, y) = 0 := by
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.2 fun ω => ?_
      split_ifs with hω
      · exact (hv ⟨ω.1, (congrArg Prod.fst hω).symm⟩).elim
      · rfl
    have z2 : (σ.map ((fun ω : V' × A × B₁ × B₂ => (ω.1, ω.2.1)) ∘
        fun ω : V × A × B₁ × B₂ => (e ω.1, ω.2))) (v', x) = 0 := by
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.2 fun ω => ?_
      split_ifs with hω
      · exact (hv ⟨ω.1, (congrArg Prod.fst hω).symm⟩).elim
      · rfl
    rw [z1, z2, zero_mul]

noncomputable def uvwLaw {U V T : Type*} (pU : PMF U) (pV : PMF V) (pW : U × V → PMF T) :
    PMF ((U × V) × T) :=
  pU.bind fun u => pV.bind fun v => (pW (u, v)).map fun w => ((u, v), w)

section UVWRegion

variable [Fintype A] [MeasurableSpace A] [Fintype B₁] [MeasurableSpace B₁]
  [Fintype B₂] [MeasurableSpace B₂] {U V T : Type*} [Fintype U] [MeasurableSpace U]
  [Fintype V] [MeasurableSpace V] [Fintype T] [MeasurableSpace T]

noncomputable def uvwRegionOf (W : DMC A (B₁ × B₂)) (pU : PMF U) (pV : PMF V)
    (pW : U × V → PMF T) (pX : (U × V) × T → PMF A) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧
    R.1 ≤ I[fun ω : ((U × V) × T) × A × B₁ × B₂ => (ω.1.1.1, ω.1.2) : fun ω => ω.2.2.1 ;
      jointMeasure W (uvwLaw pU pV pW) pX] ∧
    R.2 ≤ I[fun ω : ((U × V) × T) × A × B₁ × B₂ => (ω.1.1.2, ω.1.2) : fun ω => ω.2.2.2 ;
      jointMeasure W (uvwLaw pU pV pW) pX] ∧
    R.1 + R.2 ≤
      I[fun ω : ((U × V) × T) × A × B₁ × B₂ => (ω.1.1.1, ω.1.2) : fun ω => ω.2.2.1 ;
        jointMeasure W (uvwLaw pU pV pW) pX] +
      I[fun ω : ((U × V) × T) × A × B₁ × B₂ => ω.1.1.2 : fun ω => ω.2.2.2 |
        fun ω => (ω.1.1.1, ω.1.2) ; jointMeasure W (uvwLaw pU pV pW) pX] ∧
    R.1 + R.2 ≤
      I[fun ω : ((U × V) × T) × A × B₁ × B₂ => (ω.1.1.2, ω.1.2) : fun ω => ω.2.2.2 ;
        jointMeasure W (uvwLaw pU pV pW) pX] +
      I[fun ω : ((U × V) × T) × A × B₁ × B₂ => ω.1.1.1 : fun ω => ω.2.2.1 |
        fun ω => (ω.1.1.2, ω.1.2) ; jointMeasure W (uvwLaw pU pV pW) pX]}

end UVWRegion

noncomputable def uvwRegion [MeasurableSpace A] [Fintype B₁] [MeasurableSpace B₁]
    [Fintype B₂] [MeasurableSpace B₂] (W : DMC A (B₁ × B₂)) : Set (ℝ × ℝ) :=
  ⋃ (k₁ : ℕ) (k₂ : ℕ) (k₃ : ℕ) (pU : PMF (Fin k₁)) (pV : PMF (Fin k₂))
    (pW : Fin k₁ × Fin k₂ → PMF (Fin k₃)) (pX : (Fin k₁ × Fin k₂) × Fin k₃ → PMF A),
    uvwRegionOf W pU pV pW pX

section Relabel

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂] {U V T U' V' T' : Type*} [Fintype U] [MeasurableSpace U]
  [MeasurableSingletonClass U] [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype U'] [MeasurableSpace U']
  [MeasurableSingletonClass U'] [Fintype V'] [MeasurableSpace V'] [MeasurableSingletonClass V']
  [Fintype T'] [MeasurableSpace T'] [MeasurableSingletonClass T']

omit [MeasurableSpace U] [MeasurableSingletonClass U] [MeasurableSpace V]
  [MeasurableSingletonClass V] [MeasurableSpace T] [MeasurableSingletonClass T]
  [MeasurableSpace U'] [MeasurableSingletonClass U'] [MeasurableSpace V']
  [MeasurableSingletonClass V'] [MeasurableSpace T'] [MeasurableSingletonClass T']
  [Fintype U] [Fintype V] [Fintype T] [Fintype U'] [Fintype V'] [Fintype T'] in
theorem uvwLaw_map_equiv (pU : PMF U) (pV : PMF V) (pW : U × V → PMF T) (e₁ : U ≃ U')
    (e₂ : V ≃ V') (e₃ : T ≃ T') :
    uvwLaw (pU.map e₁) (pV.map e₂) (fun s => (pW (e₁.symm s.1, e₂.symm s.2)).map e₃) =
      (uvwLaw pU pV pW).map ((e₁.prodCongr e₂).prodCongr e₃) := by
  simp only [uvwLaw, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
    Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map]

omit [Fintype A] in
theorem uvwRegionOf_map_equiv [Finite A] (W : DMC A (B₁ × B₂)) (pU : PMF U) (pV : PMF V)
    (pW : U × V → PMF T) (pX : (U × V) × T → PMF A) (e₁ : U ≃ U') (e₂ : V ≃ V')
    (e₃ : T ≃ T') :
    uvwRegionOf W (pU.map e₁) (pV.map e₂) (fun s => (pW (e₁.symm s.1, e₂.symm s.2)).map e₃)
        (fun t => pX (((e₁.prodCongr e₂).prodCongr e₃).symm t)) =
      uvwRegionOf W pU pV pW pX := by
  have : IsProbabilityMeasure (jointMeasure W (uvwLaw pU pV pW) pX) := by
    rw [jointMeasure_eq_toMeasure]
    infer_instance
  rw [uvwRegionOf, uvwRegionOf, uvwLaw_map_equiv, jointMeasure_map_equiv]
  simp only [mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _), Function.comp_def,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  set ν := jointMeasure W (uvwLaw pU pV pW) pX
  have h1 : I[fun x : ((U × V) × T) × A × B₁ × B₂ => (e₁ x.1.1.1, e₃ x.1.2) :
      fun x => x.2.2.1 ; ν] = I[fun ω => (ω.1.1.1, ω.1.2) : fun ω => ω.2.2.1 ; ν] :=
    mi_left_inj ν (f := Prod.map e₁ e₃) (e₁.injective.prodMap e₃.injective) fun _ => rfl
  have h2 : I[fun x : ((U × V) × T) × A × B₁ × B₂ => (e₂ x.1.1.2, e₃ x.1.2) :
      fun x => x.2.2.2 ; ν] = I[fun ω => (ω.1.1.2, ω.1.2) : fun ω => ω.2.2.2 ; ν] :=
    mi_left_inj ν (f := Prod.map e₂ e₃) (e₂.injective.prodMap e₃.injective) fun _ => rfl
  have h3 : I[fun x : ((U × V) × T) × A × B₁ × B₂ => e₂ x.1.1.2 : fun x => x.2.2.2 |
      fun x => (e₁ x.1.1.1, e₃ x.1.2) ; ν] =
      I[fun ω => ω.1.1.2 : fun ω => ω.2.2.2 | fun ω => (ω.1.1.1, ω.1.2) ; ν] :=
    (cmi_left_inj ν (f := e₂) e₂.injective fun _ => rfl).trans
      (cmi_cond_inj ν (e := Prod.map e₁ e₃) (e₁.injective.prodMap e₃.injective) fun _ => rfl)
  have h4 : I[fun x : ((U × V) × T) × A × B₁ × B₂ => e₁ x.1.1.1 : fun x => x.2.2.1 |
      fun x => (e₂ x.1.1.2, e₃ x.1.2) ; ν] =
      I[fun ω => ω.1.1.1 : fun ω => ω.2.2.1 | fun ω => (ω.1.1.2, ω.1.2) ; ν] :=
    (cmi_left_inj ν (f := e₁) e₁.injective fun _ => rfl).trans
      (cmi_cond_inj ν (e := Prod.map e₂ e₃) (e₂.injective.prodMap e₃.injective) fun _ => rfl)
  rw [h1, h2, h3, h4]

end Relabel

private lemma exists_bind_eq {S T : Type*} [Finite S] [Finite T] (p : PMF (S × T)) :
    ∃ κ : S → PMF T, (p.map Prod.fst).bind (fun s => (κ s).map fun t => (s, t)) = p := by
  classical
  have := Fintype.ofFinite S
  have := Fintype.ofFinite T
  set m := p.map Prod.fst with hmdef
  have hm : ∀ s, m s = ∑ t, p (s, t) := by
    intro s
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
    simp only
    rw [Finset.sum_eq_single s (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  have hsum : ∀ s, m s ≠ 0 → ∑ t, p (s, t) / m s = 1 := by
    intro s hs
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← hm]
    exact ENNReal.mul_inv_cancel hs (PMF.apply_ne_top _ _)
  let κ : S → PMF T := fun s => if hs : m s = 0 then p.map Prod.snd
    else PMF.ofFintype (fun t => p (s, t) / m s) (hsum s hs)
  have hfac : ∀ s t, p (s, t) = m s * κ s t := by
    intro s t
    by_cases hs : m s = 0
    · have hle : p (s, t) ≤ m s := by
        rw [hm]
        exact Finset.single_le_sum (f := fun t => p (s, t)) (fun _ _ => zero_le)
          (Finset.mem_univ t)
      rw [hs] at hle
      rw [hs, zero_mul]
      exact le_zero_iff.1 hle
    · simp only [κ, hs, dite_false, PMF.ofFintype_apply]
      rw [div_eq_mul_inv, mul_comm (p _), ← mul_assoc,
        ENNReal.mul_inv_cancel hs (PMF.apply_ne_top _ _), one_mul]
  refine ⟨κ, ?_⟩
  ext ⟨s, t⟩
  have hz : ∀ s', s' ≠ s → ((κ s').map fun t => (s', t)) (s, t) = 0 := fun s' hs' => by
    rw [PMF.map_apply]
    exact ENNReal.tsum_eq_zero.2 fun t' => by simp [Ne.symm hs']
  rw [PMF.bind_apply, tsum_eq_single s fun s' hs' => by rw [hz s' hs', mul_zero],
    map_apply_inj _ (fun a b h => congrArg Prod.snd h) t, ← hfac]

theorem exists_uvwLaw_eq {U V T : Type*} [Finite U] [Finite V] [Finite T] [Finite A]
    (W : DMC A (B₁ × B₂)) (σ : PMF (((U × V) × T) × A × B₁ × B₂))
    (h : ∀ v x y, σ (v, x, y) = (σ.map fun ω => (ω.1, ω.2.1)) (v, x) * W x y)
    (pU : PMF U) (pV : PMF V)
    (hm : σ.map (fun ω => ω.1.1) = pU.bind fun u => pV.map fun v => (u, v)) :
    ∃ (pW : U × V → PMF T) (pX : (U × V) × T → PMF A),
      jointPMF W (uvwLaw pU pV pW) pX = σ := by
  obtain ⟨p₀, pX, hj⟩ := exists_jointPMF_eq W σ h
  obtain ⟨κ, hκ⟩ := exists_bind_eq p₀
  have hp : p₀.map Prod.fst = pU.bind fun u => pV.map fun v => (u, v) := by
    rw [← hm, ← hj]
    have hc : ∀ u : (U × V) × T, ∀ a : A,
        (W a).map (fun _ => u.1) = PMF.pure u.1 := fun u a => PMF.map_const _ _
    simp only [jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def, hc, PMF.bind_const]
    rfl
  refine ⟨κ, pX, ?_⟩
  rw [← hj]
  congr 1
  rw [← hκ, hp]
  simp only [uvwLaw, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

private noncomputable def unifMsg (M : Type*) [Fintype M] [Nonempty M] : PMF M :=
  PMF.ofFintype (fun _ => (Fintype.card M : ℝ≥0∞)⁻¹) (sum_inv_card M)

private lemma uvLetter_map_msg {M₁ M₂ : Type*} [Fintype M₁] [Nonempty M₁] [Fintype M₂]
    [Nonempty M₂] [Fintype B₁] [Fintype B₂] {n : ℕ} (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n)
    (W : DMC A (B₁ × B₂)) (q : Fin n) (d : B₁ × B₂) :
    (uvLetter c W q d).map (fun ω => ω.1.1) =
      (unifMsg M₁).bind fun u => (unifMsg M₂).map fun v => (u, v) := by
  classical
  rw [uvLetter, PMF.map_comp]
  ext ⟨a, b⟩
  change ((codePMF c W).map fun ω => ω.1) (a, b) = _
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type (α₁ := M₁ × M₂)
    (α₂ := Fin n → B₁ × B₂), Finset.sum_eq_single (a, b) (fun m _ hm => by simp [Ne.symm hm])
    (by simp), PMF.bind_apply, tsum_eq_single a fun a' ha' => by
      rw [show ((unifMsg M₂).map fun v => (a', v)) (a, b) = 0 by
        rw [PMF.map_apply]
        exact ENNReal.tsum_eq_zero.2 fun v => by simp [Ne.symm ha'], mul_zero],
    map_apply_inj _ (fun x y h => congrArg Prod.snd h) b]
  simp only [codePMF, PMF.ofFintype_apply, ite_true, ← Finset.mul_sum, DMC.sum_blockProb_eq_one,
    mul_one, unifMsg, PMF.ofFintype_apply, Fintype.card_prod, Nat.cast_mul]
  exact ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))

section Region

variable [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂] {M₁ M₂ Z : Type*} [Fintype M₁] [MeasurableSpace M₁]
  [MeasurableSingletonClass M₁] [Fintype M₂] [MeasurableSpace M₂] [MeasurableSingletonClass M₂]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {n : ℕ} [NeZero n]

private lemma mixture_mem_uvw (W : DMC A (B₁ × B₂))
    (L : Fin n → PMF (((M₁ × M₂) × Z) × A × B₁ × B₂))
    (hL : ∀ q u x y, L q (u, x, y) = ((L q).map fun ω => (ω.1, ω.2.1)) (u, x) * W x y)
    (pU : PMF M₁) (pV : PMF M₂)
    (hM : ∀ q, (L q).map (fun ω => ω.1.1) = pU.bind fun u => pV.map fun v => (u, v))
    {r₁ r₂ : ℝ} (h0₁ : 0 ≤ r₁) (h0₂ : 0 ≤ r₂)
    (h₁ : n * r₁ ≤ ∑ q, I[fun ω : ((M₁ × M₂) × Z) × A × B₁ × B₂ => (ω.1.1.1, ω.1.2) :
      fun ω => ω.2.2.1 ; (L q).toMeasure])
    (h₂ : n * r₂ ≤ ∑ q, I[fun ω : ((M₁ × M₂) × Z) × A × B₁ × B₂ => (ω.1.1.2, ω.1.2) :
      fun ω => ω.2.2.2 ; (L q).toMeasure])
    (h₃ : n * (r₁ + r₂) ≤ ∑ q, I[fun ω : ((M₁ × M₂) × Z) × A × B₁ × B₂ => (ω.1.1.1, ω.1.2) :
      fun ω => ω.2.2.1 ; (L q).toMeasure] +
      ∑ q, I[fun ω : ((M₁ × M₂) × Z) × A × B₁ × B₂ => ω.1.1.2 : fun ω => ω.2.2.2 |
        fun ω => (ω.1.1.1, ω.1.2) ; (L q).toMeasure])
    (h₄ : n * (r₁ + r₂) ≤ ∑ q, I[fun ω : ((M₁ × M₂) × Z) × A × B₁ × B₂ => (ω.1.1.2, ω.1.2) :
      fun ω => ω.2.2.2 ; (L q).toMeasure] +
      ∑ q, I[fun ω : ((M₁ × M₂) × Z) × A × B₁ × B₂ => ω.1.1.1 : fun ω => ω.2.2.1 |
        fun ω => (ω.1.1.2, ω.1.2) ; (L q).toMeasure]) :
    (r₁, r₂) ∈ uvwRegion W := by
  classical
  set ρ := DMC.jointPMF L (unifPMF n)
  let φ : Fin n × ((M₁ × M₂) × Z) × A × B₁ × B₂ → (Fin n × (M₁ × M₂) × Z) × A × B₁ × B₂ :=
    fun p => ((p.1, p.2.1), p.2.2.1, p.2.2.2)
  have hφ : Function.Injective φ := fun a b h => by
    simp only [φ, Prod.mk.injEq] at h
    exact Prod.ext h.1.1 (Prod.ext h.1.2 (Prod.ext h.2.1 h.2.2))
  have hmap : (ρ.map φ).map (fun ω => (ω.1, ω.2.1)) =
      (DMC.jointPMF (fun q => (L q).map fun ω => (ω.1, ω.2.1)) (unifPMF n)).map
        fun p => ((p.1, p.2.1), p.2.2) := by
    simp only [ρ, φ, DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hmem : ∀ v x y, ρ.map φ (v, x, y) = ((ρ.map φ).map fun ω => (ω.1, ω.2.1)) (v, x) *
      W x y := by
    rintro ⟨q, u⟩ x y
    rw [hmap, show (((q, u), x, y) : (Fin n × (M₁ × M₂) × Z) × A × B₁ × B₂) =
        φ (q, u, x, y) from rfl,
      map_apply_inj _ hφ, show (((q, u), x) : (Fin n × (M₁ × M₂) × Z) × A) =
        (fun p : Fin n × ((M₁ × M₂) × Z) × A => ((p.1, p.2.1), p.2.2)) (q, u, x) from rfl,
      map_apply_inj _ (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)),
      DMC.jointPMF_apply, DMC.jointPMF_apply, hL, mul_assoc]
  let e : Fin n × (M₁ × M₂) × Z → (M₁ × M₂) × (Fin n × Z) := fun v => (v.2.1, (v.1, v.2.2))
  have he : Function.Injective e := by
    rintro ⟨q, m, z⟩ ⟨q', m', z'⟩ h
    simp only [e, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  have hτ : ((ρ.map φ).map fun ω => (e ω.1, ω.2)).map (fun ω => ω.1.1) =
      pU.bind fun u => pV.map fun v => (u, v) := by
    have h1 : ((ρ.map φ).map fun ω => (e ω.1, ω.2)).map (fun ω => ω.1.1) =
        (unifPMF n).bind fun q => (L q).map fun ω => ω.1.1 := by
      simp only [ρ, φ, e, DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]
    rw [h1]
    simp only [hM, PMF.bind_const]
  obtain ⟨pW, pX, hj⟩ := exists_uvwLaw_eq W _ (factor_map W (ρ.map φ) he hmem) pU pV hτ
  have hν : jointMeasure W (uvwLaw pU pV pW) pX =
      ρ.toMeasure.map ((fun ω => (e ω.1, ω.2)) ∘ φ) := by
    rw [jointMeasure_eq_toMeasure, hj, PMF.map_comp, PMF.toMeasure_map _ _ (measurable_of_finite _)]
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  let f₁ : Fin n × M₁ × Z → M₁ × Fin n × Z := fun t => (t.2.1, (t.1, t.2.2))
  have hf₁ : Function.Injective f₁ := by
    rintro ⟨q, m, z⟩ ⟨q', m', z'⟩ h
    simp only [f₁, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  let f₂ : Fin n × M₂ × Z → M₂ × Fin n × Z := fun t => (t.2.1, (t.1, t.2.2))
  have hf₂ : Function.Injective f₂ := by
    rintro ⟨q, m, z⟩ ⟨q', m', z'⟩ h
    simp only [f₂, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  have q1 : (n : ℝ)⁻¹ * ∑ q, I[fun ω : ((M₁ × M₂) × Z) × A × B₁ × B₂ => (ω.1.1.1, ω.1.2) :
      fun ω => ω.2.2.1 ; (L q).toMeasure] ≤
      I[fun ω : ((M₁ × M₂) × (Fin n × Z)) × A × B₁ × B₂ => (ω.1.1.1, ω.1.2) :
        fun ω => ω.2.2.1 ; jointMeasure W (uvwLaw pU pV pW) pX] := by
    rw [hν, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
    refine (mixture_mutualInfo_ge L (fun r => (r.1.1.1, r.1.2)) fun r => r.2.2.1).trans
      (le_of_eq ?_)
    exact (mi_left_inj _ (X := fun p : Fin n × ((M₁ × M₂) × Z) × A × B₁ × B₂ =>
      (p.1, (p.2.1.1.1, p.2.1.2))) hf₁ fun _ => rfl).symm
  have q2 : (n : ℝ)⁻¹ * ∑ q, I[fun ω : ((M₁ × M₂) × Z) × A × B₁ × B₂ => (ω.1.1.2, ω.1.2) :
      fun ω => ω.2.2.2 ; (L q).toMeasure] ≤
      I[fun ω : ((M₁ × M₂) × (Fin n × Z)) × A × B₁ × B₂ => (ω.1.1.2, ω.1.2) :
        fun ω => ω.2.2.2 ; jointMeasure W (uvwLaw pU pV pW) pX] := by
    rw [hν, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
    refine (mixture_mutualInfo_ge L (fun r => (r.1.1.2, r.1.2)) fun r => r.2.2.2).trans
      (le_of_eq ?_)
    exact (mi_left_inj _ (X := fun p : Fin n × ((M₁ × M₂) × Z) × A × B₁ × B₂ =>
      (p.1, (p.2.1.1.2, p.2.1.2))) hf₂ fun _ => rfl).symm
  have q3 : I[fun ω : ((M₁ × M₂) × (Fin n × Z)) × A × B₁ × B₂ => ω.1.1.2 :
      fun ω => ω.2.2.2 | fun ω => (ω.1.1.1, ω.1.2) ; jointMeasure W (uvwLaw pU pV pW) pX] =
      (n : ℝ)⁻¹ * ∑ q, I[fun ω : ((M₁ × M₂) × Z) × A × B₁ × B₂ => ω.1.1.2 : fun ω => ω.2.2.2 |
        fun ω => (ω.1.1.1, ω.1.2) ; (L q).toMeasure] := by
    rw [hν, condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _),
      ← mixture_condMutualInfo L (fun r => r.1.1.2) (fun r => r.2.2.2) fun r => (r.1.1.1, r.1.2)]
    exact cmi_cond_inj _ (Z := fun p : Fin n × ((M₁ × M₂) × Z) × A × B₁ × B₂ =>
      (p.1, (p.2.1.1.1, p.2.1.2))) hf₁ fun _ => rfl
  have q4 : I[fun ω : ((M₁ × M₂) × (Fin n × Z)) × A × B₁ × B₂ => ω.1.1.1 :
      fun ω => ω.2.2.1 | fun ω => (ω.1.1.2, ω.1.2) ; jointMeasure W (uvwLaw pU pV pW) pX] =
      (n : ℝ)⁻¹ * ∑ q, I[fun ω : ((M₁ × M₂) × Z) × A × B₁ × B₂ => ω.1.1.1 : fun ω => ω.2.2.1 |
        fun ω => (ω.1.1.2, ω.1.2) ; (L q).toMeasure] := by
    rw [hν, condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _),
      ← mixture_condMutualInfo L (fun r => r.1.1.1) (fun r => r.2.2.1) fun r => (r.1.1.2, r.1.2)]
    exact cmi_cond_inj _ (Z := fun p : Fin n × ((M₁ × M₂) × Z) × A × B₁ × B₂ =>
      (p.1, (p.2.1.1.2, p.2.1.2))) hf₂ fun _ => rfl
  have div : ∀ {r a : ℝ}, n * r ≤ a → r ≤ (n : ℝ)⁻¹ * a := fun h => by
    rw [← div_eq_inv_mul, le_div_iff₀ hn]
    linarith
  have hR : (r₁, r₂) ∈ uvwRegionOf W pU pV pW pX := by
    refine ⟨h0₁, h0₂, (div h₁).trans q1, (div h₂).trans q2, ?_, ?_⟩
    · have := div h₃
      rw [mul_add] at this
      change r₁ + r₂ ≤ _
      linarith
    · have := div h₄
      rw [mul_add] at this
      change r₁ + r₂ ≤ _
      linarith
  rw [← uvwRegionOf_map_equiv W pU pV pW pX (Fintype.equivFin _) (Fintype.equivFin _)
    (Fintype.equivFin _)] at hR
  simp only [uvwRegion, Set.mem_iUnion]
  exact ⟨_, _, _, _, _, _, _, hR⟩

end Region

section Theorem

variable [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂]

theorem achievableRegion_subset_closure_uvwRegion (W : DMC A (B₁ × B₂)) :
    achievableRegion W ⊆ closure (uvwRegion W) := by
  classical
  rintro ⟨R₁, R₂⟩ ⟨h0₁, h0₂, hR⟩
  rw [Metric.mem_closure_iff]
  intro δ hδ
  set ε₀ := min (1 / 4) (δ / (4 * (R₁ + R₂ + 1))) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (by norm_num) (by positivity)
  obtain ⟨N, hN⟩ := hR (ENNReal.ofReal ε₀) (ENNReal.ofReal_pos.2 hε₀0)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * Real.log 2 / δ)
  set n := max N (max n₀ 1)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
  have : NeZero n := ⟨by omega⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n (le_max_left _ _)
  have hk₁0 : (0 : ℝ) < k₁ := (Real.exp_pos _).trans_le hk₁
  have hk₂0 : (0 : ℝ) < k₂ := (Real.exp_pos _).trans_le hk₂
  have : Nonempty (Fin k₁) := ⟨⟨0, by exact_mod_cast hk₁0⟩⟩
  have : Nonempty (Fin k₂) := ⟨⟨0, by exact_mod_cast hk₂0⟩⟩
  obtain ⟨d, -⟩ := (W (c.enc (Classical.arbitrary _) ⟨0, by omega⟩)).support_nonempty
  set ε' := (c.avgError W).toReal
  have hε' : ε' ≤ ε₀ := ENNReal.toReal_le_of_le_ofReal hε₀0.le hc
  have hε'0 : 0 ≤ ε' := ENNReal.toReal_nonneg
  have hε'4 : ε' ≤ 1 / 4 := hε'.trans (min_le_left _ _)
  have hl₁ : n * R₁ ≤ Real.log k₁ := (Real.le_log_iff_exp_le hk₁0).2 hk₁
  have hl₂ : n * R₂ ≤ Real.log k₂ := (Real.le_log_iff_exp_le hk₂0).2 hk₂
  have hlog2 : Real.log 2 / n < δ / 2 := by
    rw [div_lt_iff₀ hnpos]
    have : (n₀ : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 := (div_lt_iff₀ hδ).1 (hn₀.trans_le this)
    linarith
  have hlog2' : 0 ≤ Real.log 2 / n := div_nonneg (Real.log_nonneg (by norm_num)) hnpos.le
  set r₁ := max 0 ((1 - 2 * ε') * R₁ - Real.log 2 / n)
  set r₂ := max 0 ((1 - 2 * ε') * R₂ - Real.log 2 / n)
  have hc₁ : (n : ℝ) * ((1 - 2 * ε') * R₁ - Real.log 2 / n) ≤
      (1 - 2 * ε') * Real.log k₁ - Real.log 2 := by
    rw [mul_sub, mul_div_cancel₀ _ hnpos.ne']
    nlinarith
  have hc₂ : (n : ℝ) * ((1 - 2 * ε') * R₂ - Real.log 2 / n) ≤
      (1 - 2 * ε') * Real.log k₂ - Real.log 2 := by
    rw [mul_sub, mul_div_cancel₀ _ hnpos.ne']
    nlinarith
  have hR4 : ε₀ * (4 * (R₁ + R₂ + 1)) ≤ δ := by
    have := min_le_right (1 / 4 : ℝ) (δ / (4 * (R₁ + R₂ + 1)))
    rw [← hε₀, le_div_iff₀ (by positivity)] at this
    exact this
  have d₁ : |R₁ - r₁| < δ := by
    rw [abs_lt]
    constructor
    · have : r₁ ≤ R₁ := max_le h0₁ (by nlinarith)
      linarith
    · have : (1 - 2 * ε') * R₁ - Real.log 2 / n ≤ r₁ := le_max_right _ _
      nlinarith
  have d₂ : |R₂ - r₂| < δ := by
    rw [abs_lt]
    constructor
    · have : r₂ ≤ R₂ := max_le h0₂ (by nlinarith)
      linarith
    · have : (1 - 2 * ε') * R₂ - Real.log 2 / n ≤ r₂ := le_max_right _ _
      nlinarith
  have hr₁ : n * r₁ ≤ max 0 ((1 - 2 * ε') * Real.log k₁ - Real.log 2) := by
    rw [mul_max_of_nonneg _ _ hnpos.le, mul_zero]
    exact max_le_max le_rfl hc₁
  have hr₂ : n * r₂ ≤ max 0 ((1 - 2 * ε') * Real.log k₂ - Real.log 2) := by
    rw [mul_max_of_nonneg _ _ hnpos.le, mul_zero]
    exact max_le_max le_rfl hc₂
  obtain ⟨b₁, b₂, b₃, b₄⟩ := fano_bound c W
  simp only [Fintype.card_fin] at b₁ b₂ b₃ b₄
  set c' := twinCode c
  set μ := c'.codeMeasure W
  have s₁ := sum_bound₁ c' W d
  have s₂ := sum_bound₂ c' W d
  have s₃ := sum_bound₃ c' W d
  have s₄ := sum_bound₄ c' W d
  have n₁ := mutualInfo_nonneg μ
    (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1) (Y := fun ω i => (ω.2 i).1)
    (measurable_of_finite _) (measurable_of_finite _)
  have n₂ := mutualInfo_nonneg μ
    (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2) (Y := fun ω i => (ω.2 i).2)
    (measurable_of_finite _) (measurable_of_finite _)
  have n₃ := condMutualInfo_nonneg μ
    (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).2)
    (Y := fun ω => ω.1.2) (Z := fun ω => ω.1.1)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
  have n₄ := condMutualInfo_nonneg μ
    (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).1)
    (Y := fun ω => ω.1.1) (Z := fun ω => ω.1.2)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
  have t₁ := Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => (letter_eq c' W q d).1
  have t₂ := Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => (letter_eq c' W q d).2.1
  have t₃ := Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => (letter_eq c' W q d).2.2.1
  have t₄ := Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => (letter_eq c' W q d).2.2.2
  have m₁ := max_le n₁ b₁
  have m₂ := max_le n₂ b₂
  have m₃ := max_le n₃ b₃
  have m₄ := max_le n₄ b₄
  have hmem := mixture_mem_uvw W (fun q => uvLetter c' W q d)
    (fun q => uvLetter_apply c' W q d) (unifMsg _) (unifMsg _)
    (fun q => uvLetter_map_msg c' W q d) (le_max_left 0 _) (le_max_left 0 _) (r₁ := r₁) (r₂ := r₂)
    (by linarith) (by linarith) (by rw [mul_add]; linarith) (by rw [mul_add]; linarith)
  refine ⟨(r₁, r₂), hmem, ?_⟩
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt d₁ d₂

theorem closure_achievableRegion_subset_uvwRegion (W : DMC A (B₁ × B₂)) :
    closure (achievableRegion W) ⊆ closure (uvwRegion W) :=
  closure_minimal (achievableRegion_subset_closure_uvwRegion W) isClosed_closure

end Theorem

end BC

end Meat
