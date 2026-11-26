import Meat.Open.InterferenceStrongConverse

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal

namespace Meat

namespace IC

section Product

variable {A : Type*} [Fintype A] {k : ℕ}

private lemma sum_prod_eq_one (p : Fin k → PMF A) : ∑ f : Fin k → A, ∏ q, p q (f q) = 1 := by
  rw [← Fintype.prod_sum (fun q a => p q a)]
  refine prod_eq_one fun q _ => ?_
  have h := PMF.tsum_coe (p q)
  rwa [tsum_fintype] at h

private noncomputable def prodPMF (p : Fin k → PMF A) : PMF (Fin k → A) :=
  PMF.ofFintype _ (sum_prod_eq_one p)

private lemma prodPMF_map (p : Fin k → PMF A) (q : Fin k) :
    (prodPMF p).map (fun f => f q) = p q := by
  classical
  ext a
  rw [PMF.map_apply, tsum_fintype]
  set g : Fin k → A → ℝ≥0∞ := fun j b => if j = q then (if b = a then p q a else 0) else p j b
  have h1 : ∀ f : Fin k → A, (if a = f q then prodPMF p f else 0) = ∏ j, g j (f j) := by
    intro f
    rw [prodPMF, PMF.ofFintype_apply, ← mul_prod_erase univ _ (mem_univ q)]
    have e : ∀ j ∈ univ.erase q, g j (f j) = p j (f j) := fun j hj => by
      simp [g, (mem_erase.1 hj).1]
    rw [← mul_prod_erase univ (fun j => g j (f j)) (mem_univ q), prod_congr rfl e]
    by_cases hf : f q = a
    · simp [g, hf]
    · simp [g, hf, Ne.symm hf]
  rw [sum_congr rfl fun f _ => h1 f, ← Fintype.prod_sum g,
    ← mul_prod_erase univ _ (mem_univ q)]
  have e : ∀ j ∈ univ.erase q, ∑ b, g j b = 1 := fun j hj => by
    simp only [g, (mem_erase.1 hj).1, ite_false]
    have h := PMF.tsum_coe (p j)
    rwa [tsum_fintype] at h
  rw [prod_congr rfl e, prod_const_one, mul_one]
  simp [g]

end Product

section Decomp

variable {Ω T A B : Type*} [MeasurableSpace Ω] [Fintype T] [MeasurableSpace T]
  [MeasurableSingletonClass T] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

private lemma condMutualInfo_eq_sum_of_kernel (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Ω → T} {X : Ω → A} {Y : Ω → B} (hG : Measurable G) (hX : Measurable X)
    (hY : Measurable Y) (w : T → ℝ) (r : T → PMF A) (K : T → DMC A B)
    (h : ∀ g x y, μ.real {ω | G ω = g ∧ X ω = x ∧ Y ω = y} =
      w g * (r g x).toReal * (K g x y).toReal) :
    I[X : Y | G ; μ] = ∑ g, w g * (K g).inputMutualInfo (r g) := by
  classical
  have hsum : ∀ (s : PMF B), ∑ y, (s y).toReal = 1 := fun s => by
    rw [← ENNReal.toReal_sum fun _ _ => PMF.apply_ne_top _ _]
    have h := PMF.tsum_coe s
    rw [tsum_fintype] at h
    rw [h, ENNReal.toReal_one]
  have hsumA : ∀ (s : PMF A), ∑ y, (s y).toReal = 1 := fun s => by
    rw [← ENNReal.toReal_sum fun _ _ => PMF.apply_ne_top _ _]
    have h := PMF.tsum_coe s
    rw [tsum_fintype] at h
    rw [h, ENNReal.toReal_one]
  have hxg : ∀ g x, μ.real {ω | G ω = g ∧ X ω = x} = w g * (r g x).toReal := fun g x => by
    have h1 := sum_measureReal_inter (μ := μ) hY {ω | G ω = g ∧ X ω = x}
    rw [← h1]
    have e : ∀ y, μ.real {ω | Y ω = y ∧ ω ∈ {ω | G ω = g ∧ X ω = x}} =
        μ.real {ω | G ω = g ∧ X ω = x ∧ Y ω = y} := fun y => by
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq]
      tauto
    simp only [e, h, ← mul_sum, hsum, mul_one]
  have hw : ∀ g, μ.real (G ⁻¹' {g}) = w g := fun g => by
    have h1 := sum_measureReal_inter (μ := μ) hX (G ⁻¹' {g})
    rw [← h1]
    have e : ∀ x, μ.real {ω | X ω = x ∧ ω ∈ G ⁻¹' {g}} = μ.real {ω | G ω = g ∧ X ω = x} :=
      fun x => by
        congr 1
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
        tauto
    simp only [e, hxg, ← mul_sum, hsumA, mul_one]
  rw [Wiretap.condMutualInfo_eq_sum_cond μ hX hY hG]
  refine sum_congr rfl fun g _ => ?_
  rw [hw]
  rcases eq_or_ne (w g) 0 with h0 | h0
  · simp [h0]
  congr 1
  have hne : μ (G ⁻¹' {g}) ≠ 0 := fun h' => h0 (by rw [← hw, measureReal_def, h']; rfl)
  have := cond_isProbabilityMeasure (μ := μ) hne
  have hmap : (μ[|G ⁻¹' {g}]).map (fun ω => (X ω, Y ω)) = (K g).jointMeasure (r g) := by
    refine Measure.ext_of_singleton fun t => ?_
    rw [Measure.map_apply (hX.prodMk hY) (measurableSet_singleton _),
      DMC.jointMeasure_eq_toMeasure,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), DMC.jointPMF_apply,
      ← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def,
      ← ENNReal.ofReal_toReal (ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
        (PMF.apply_ne_top _ _))]
    congr 1
    rw [measureReal_def, cond_apply (hG (measurableSet_singleton g)), ENNReal.toReal_mul,
      ← measureReal_def, ENNReal.toReal_inv, ← measureReal_def, hw, ENNReal.toReal_mul]
    have e : G ⁻¹' {g} ∩ (fun ω => (X ω, Y ω)) ⁻¹' {t} =
        {ω | G ω = g ∧ X ω = t.1 ∧ Y ω = t.2} := by
      ext ω
      simp [Prod.ext_iff]
    rw [e, h]
    field_simp
  rw [DMC.inputMutualInfo, ← hmap, mutualInfo_map _ (hX.prodMk hY) measurable_fst
    measurable_snd]
  rfl

omit [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSingletonClass A]
  [MeasurableSingletonClass B] in
private lemma inputMutualInfo_comp_le [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] (K : DMC A B) (e : T → A)
    (P : PMF T) :
    K.inputMutualInfo (P.map e) ≤ DMC.inputMutualInfo (fun t => K (e t)) P := by
  have hm : (DMC.jointMeasure (fun t => K (e t)) P).map (fun ω => (e ω.1, ω.2)) =
      K.jointMeasure (P.map e) := by
    rw [DMC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _),
      DMC.jointMeasure_eq_toMeasure]
    congr 1
    simp only [DMC.jointPMF, PMF.map_bind, PMF.map_comp, PMF.bind_map]
    rfl
  rw [DMC.inputMutualInfo, ← hm, mutualInfo_map _ (measurable_of_finite _) measurable_fst
    measurable_snd, DMC.inputMutualInfo, mutualInfo_comm, mutualInfo_comm (X := Prod.fst)]
  exact mutualInfo_comp_le _ measurable_snd measurable_fst e

end Decomp

section Pair

variable {Ω P Q R S : Type*} [MeasurableSpace Ω] [Fintype P] [MeasurableSpace P]
  [MeasurableSingletonClass P] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S] (μ : Measure Ω)

private lemma condMutualInfo_pair' {X : Ω → P} {Y : Ω → Q} {Z : Ω → R} {V : Ω → S} :
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

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] in
private lemma mutualInfo_pair' {X : Ω → P} {Y : Ω → Q} {V : Ω → S} :
    I[X : fun ω => (Y ω, V ω) ; μ] = I[X : Y ; μ] + I[X : V | Y ; μ] := by
  have h := mutualInfo_pair_eq_add_condMutualInfo μ (X := X) (Y := V) (Z := Y)
  have hs := mutualInfo_comp_right_of_injective μ (X := X) (Y := fun ω => (V ω, Y ω))
    Prod.swap_injective
  rw [← h, ← hs]
  rfl

end Pair

section State

variable {A₁ A₂ B : Type*} {k : ℕ}

private noncomputable def stateMAC (V : DMC (A₁ × A₂) B) (pQ : PMF (Fin k)) :
    DMC ((Fin k → A₁) × (Fin k → A₂)) (Fin k × B) :=
  fun f => pQ.bind fun q => (V (f.1 q, f.2 q)).map fun b => (q, b)

private lemma stateMAC_apply (V : DMC (A₁ × A₂) B) (pQ : PMF (Fin k))
    (f : (Fin k → A₁) × (Fin k → A₂)) (q : Fin k) (b : B) :
    stateMAC V pQ f (q, b) = pQ q * V (f.1 q, f.2 q) b := by
  classical
  rw [stateMAC, PMF.bind_apply, tsum_fintype,
    sum_eq_single q (fun q' _ hq => by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero.2 fun b' => by simp [Ne.symm hq], mul_zero])
      (by simp)]
  rw [map_apply_inj _ (fun x y h => (Prod.ext_iff.1 h).2) b]

private lemma sum_toReal_mul_eval [Fintype A₁] (P : PMF (Fin k → A₁)) (q : Fin k)
    (h : A₁ → ℝ) :
    ∑ f, (P f).toReal * h (f q) = ∑ a, ((P.map fun f => f q) a).toReal * h a := by
  classical
  have e : ∀ a, ((P.map fun f => f q) a).toReal = ∑ f, if a = f q then (P f).toReal else 0 :=
    fun a => by
      rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun f _ => by
        split_ifs <;> simp [PMF.apply_ne_top]]
      simp only [apply_ite ENNReal.toReal, ENNReal.toReal_zero]
  simp only [e, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun f _ => ?_
  rw [sum_ite_eq' univ (f q)]
  simp

variable [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

private lemma measureReal_toMeasure_eq {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (σ : PMF α) (p : α → Prop) (a : α) (h : ∀ x, p x ↔ x = a) :
    σ.toMeasure.real {x | p x} = (σ a).toReal := by
  have e : {x | p x} = {a} := Set.ext fun x => h x
  rw [e, measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

private lemma condMutualInfo₁_eq_sum (V : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ; MAC.jointMeasure V p₁ p₂] =
      ∑ a₂, (p₂ a₂).toReal * DMC.inputMutualInfo (fun a => V (a, a₂)) p₁ := by
  refine condMutualInfo_eq_sum_of_kernel _ (G := fun ω : A₁ × A₂ × B => ω.2.1)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (fun a₂ => (p₂ a₂).toReal) (fun _ => p₁) (fun a₂ a => V (a, a₂)) fun a₂ a₁ b => ?_
  rw [MAC.jointMeasure_eq_toMeasure, measureReal_toMeasure_eq _ _ (a₁, a₂, b)
    (fun x => by simp only [Prod.ext_iff]; tauto), MAC.jointPMF_apply, ENNReal.toReal_mul,
    ENNReal.toReal_mul]
  ring

private lemma condMutualInfo₂_eq_sum (V : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ; MAC.jointMeasure V p₁ p₂] =
      ∑ a₁, (p₁ a₁).toReal * DMC.inputMutualInfo (fun a => V (a₁, a)) p₂ := by
  refine condMutualInfo_eq_sum_of_kernel _ (G := fun ω : A₁ × A₂ × B => ω.1)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (fun a₁ => (p₁ a₁).toReal) (fun _ => p₂) (fun a₁ a => V (a₁, a)) fun a₁ a₂ b => ?_
  rw [MAC.jointMeasure_eq_toMeasure, measureReal_toMeasure_eq _ _ (a₁, a₂, b)
    (fun x => by simp only [Prod.ext_iff]), MAC.jointPMF_apply, ENNReal.toReal_mul,
    ENNReal.toReal_mul]
  ring

private lemma state_bound₁ (V : DMC (A₁ × A₂) B) (pQ : PMF (Fin k)) (p₁ : Fin k → PMF A₁)
    (p₂ : Fin k → PMF A₂) :
    ∑ q, (pQ q).toReal * I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure V (p₁ q) (p₂ q)] ≤
      I[fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => ω.1 : fun ω => ω.2.2 |
        fun ω => ω.2.1 ; MAC.jointMeasure (stateMAC V pQ) (prodPMF p₁) (prodPMF p₂)] := by
  set μ := MAC.jointMeasure (stateMAC V pQ) (prodPMF p₁) (prodPMF p₂) with hμ
  have hp := condMutualInfo_pair' μ
    (X := fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => ω.1)
    (Y := fun ω => ω.2.2.1) (V := fun ω => ω.2.2.2) (Z := fun ω => ω.2.1)
  have h0 := condMutualInfo_nonneg μ
    (X := fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => ω.1)
    (Y := fun ω => ω.2.2.1) (Z := fun ω => ω.2.1) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)
  have hd := condMutualInfo_eq_sum_of_kernel μ
    (G := fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => (ω.2.2.1, ω.2.1))
    (X := fun ω => ω.1) (Y := fun ω => ω.2.2.2)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (fun g => (pQ g.1).toReal * (prodPMF p₂ g.2).toReal) (fun _ => prodPMF p₁)
    (fun g f => V (f g.1, g.2 g.1)) fun g f b => by
      rw [hμ, MAC.jointMeasure_eq_toMeasure, measureReal_toMeasure_eq _ _ (f, g.2, (g.1, b))
        (fun x => by simp only [Prod.ext_iff]; tauto), MAC.jointPMF_apply, stateMAC_apply,
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]
      ring
  have he : I[fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => ω.1 : fun ω => ω.2.2 |
      fun ω => ω.2.1 ; μ] = I[fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => ω.1 :
        fun ω => (ω.2.2.1, ω.2.2.2) | fun ω => ω.2.1 ; μ] := rfl
  rw [he, hp, hd]
  refine le_add_of_nonneg_of_le h0 ?_
  rw [Fintype.sum_prod_type]
  refine sum_le_sum fun q _ => ?_
  rw [condMutualInfo₁_eq_sum, mul_sum]
  have hm := sum_toReal_mul_eval (prodPMF p₂) q
    (fun a₂ => (pQ q).toReal * DMC.inputMutualInfo (fun a => V (a, a₂)) (p₁ q))
  rw [prodPMF_map] at hm
  calc ∑ a₂, (pQ q).toReal * ((p₂ q a₂).toReal * DMC.inputMutualInfo (fun a => V (a, a₂)) (p₁ q))
      = ∑ f₂ : Fin k → A₂, (prodPMF p₂ f₂).toReal *
          ((pQ q).toReal * DMC.inputMutualInfo (fun a => V (a, f₂ q)) (p₁ q)) := by
        rw [hm]
        exact sum_congr rfl fun a _ => by ring
    _ ≤ _ := by
        refine sum_le_sum fun f₂ _ => ?_
        rw [← mul_assoc, mul_comm (prodPMF p₂ f₂).toReal]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h := inputMutualInfo_comp_le (fun a => V (a, f₂ q)) (fun f : Fin k → A₁ => f q)
          (prodPMF p₁)
        rwa [prodPMF_map] at h

private lemma state_bound₂ (V : DMC (A₁ × A₂) B) (pQ : PMF (Fin k)) (p₁ : Fin k → PMF A₁)
    (p₂ : Fin k → PMF A₂) :
    ∑ q, (pQ q).toReal * I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
        MAC.jointMeasure V (p₁ q) (p₂ q)] ≤
      I[fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => ω.2.1 : fun ω => ω.2.2 |
        fun ω => ω.1 ; MAC.jointMeasure (stateMAC V pQ) (prodPMF p₁) (prodPMF p₂)] := by
  set μ := MAC.jointMeasure (stateMAC V pQ) (prodPMF p₁) (prodPMF p₂) with hμ
  have hp := condMutualInfo_pair' μ
    (X := fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => ω.2.1)
    (Y := fun ω => ω.2.2.1) (V := fun ω => ω.2.2.2) (Z := fun ω => ω.1)
  have h0 := condMutualInfo_nonneg μ
    (X := fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => ω.2.1)
    (Y := fun ω => ω.2.2.1) (Z := fun ω => ω.1) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)
  have hd := condMutualInfo_eq_sum_of_kernel μ
    (G := fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => (ω.2.2.1, ω.1))
    (X := fun ω => ω.2.1) (Y := fun ω => ω.2.2.2)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (fun g => (pQ g.1).toReal * (prodPMF p₁ g.2).toReal) (fun _ => prodPMF p₂)
    (fun g f => V (g.2 g.1, f g.1)) fun g f b => by
      rw [hμ, MAC.jointMeasure_eq_toMeasure, measureReal_toMeasure_eq _ _ (g.2, f, (g.1, b))
        (fun x => by simp only [Prod.ext_iff]; tauto), MAC.jointPMF_apply, stateMAC_apply,
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]
      ring
  have he : I[fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => ω.2.1 : fun ω => ω.2.2 |
      fun ω => ω.1 ; μ] = I[fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => ω.2.1 :
        fun ω => (ω.2.2.1, ω.2.2.2) | fun ω => ω.1 ; μ] := rfl
  rw [he, hp, hd]
  refine le_add_of_nonneg_of_le h0 ?_
  rw [Fintype.sum_prod_type]
  refine sum_le_sum fun q _ => ?_
  rw [condMutualInfo₂_eq_sum, mul_sum]
  have hm := sum_toReal_mul_eval (prodPMF p₁) q
    (fun a₁ => (pQ q).toReal * DMC.inputMutualInfo (fun a => V (a₁, a)) (p₂ q))
  rw [prodPMF_map] at hm
  calc ∑ a₁, (pQ q).toReal * ((p₁ q a₁).toReal * DMC.inputMutualInfo (fun a => V (a₁, a)) (p₂ q))
      = ∑ f₁ : Fin k → A₁, (prodPMF p₁ f₁).toReal *
          ((pQ q).toReal * DMC.inputMutualInfo (fun a => V (f₁ q, a)) (p₂ q)) := by
        rw [hm]
        exact sum_congr rfl fun a _ => by ring
    _ ≤ _ := by
        refine sum_le_sum fun f₁ _ => ?_
        rw [← mul_assoc, mul_comm (prodPMF p₁ f₁).toReal]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h := inputMutualInfo_comp_le (fun a => V (f₁ q, a)) (fun f : Fin k → A₂ => f q)
          (prodPMF p₂)
        rwa [prodPMF_map] at h

private lemma state_bound₃ (V : DMC (A₁ × A₂) B) (pQ : PMF (Fin k)) (p₁ : Fin k → PMF A₁)
    (p₂ : Fin k → PMF A₂) :
    ∑ q, (pQ q).toReal * I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
        MAC.jointMeasure V (p₁ q) (p₂ q)] ≤
      I[fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
        MAC.jointMeasure (stateMAC V pQ) (prodPMF p₁) (prodPMF p₂)] := by
  set μ := MAC.jointMeasure (stateMAC V pQ) (prodPMF p₁) (prodPMF p₂) with hμ
  have hp := mutualInfo_pair' μ
    (X := fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => (ω.1, ω.2.1))
    (Y := fun ω => ω.2.2.1) (V := fun ω => ω.2.2.2)
  have h0 := mutualInfo_nonneg μ
    (X := fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => (ω.1, ω.2.1))
    (Y := fun ω => ω.2.2.1) (measurable_of_finite _) (measurable_of_finite _)
  have hd := condMutualInfo_eq_sum_of_kernel μ
    (G := fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => ω.2.2.1)
    (X := fun ω => (ω.1, ω.2.1)) (Y := fun ω => ω.2.2.2)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (fun q => (pQ q).toReal) (fun _ => MAC.inputPMF (prodPMF p₁) (prodPMF p₂))
    (fun q f => V (f.1 q, f.2 q)) fun q f b => by
      rw [hμ, MAC.jointMeasure_eq_toMeasure, measureReal_toMeasure_eq _ _ (f.1, f.2, (q, b))
        (fun x => by simp only [Prod.ext_iff]; tauto), MAC.jointPMF_apply, stateMAC_apply,
        MAC.inputPMF_apply, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_mul]
      ring
  have he : I[fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => (ω.1, ω.2.1) :
      fun ω => ω.2.2 ; μ] = I[fun ω : (Fin k → A₁) × (Fin k → A₂) × (Fin k × B) => (ω.1, ω.2.1) :
        fun ω => (ω.2.2.1, ω.2.2.2) ; μ] := rfl
  rw [he, hp, hd]
  refine le_add_of_nonneg_of_le h0 (sum_le_sum fun q _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := inputMutualInfo_comp_le V
    (fun f : (Fin k → A₁) × (Fin k → A₂) => (f.1 q, f.2 q)) (MAC.inputPMF (prodPMF p₁) (prodPMF p₂))
  rwa [MAC.inputPMF_map _ _ (fun f : Fin k → A₁ => f q) (fun f : Fin k → A₂ => f q),
    prodPMF_map, prodPMF_map, MAC.inputMutualInfo_inputPMF] at h

end State

section Derandomize

variable {A₁ A₂ B₁ B₂ : Type*} {k : ℕ}

private noncomputable def stateIC (W : DMC (A₁ × A₂) (B₁ × B₂)) (pQ : PMF (Fin k)) :
    DMC ((Fin k → A₁) × (Fin k → A₂)) ((Fin k × B₁) × (Fin k × B₂)) :=
  fun f => pQ.bind fun q => (W (f.1 q, f.2 q)).map fun b => ((q, b.1), (q, b.2))

private lemma out₁_stateIC (W : DMC (A₁ × A₂) (B₁ × B₂)) (pQ : PMF (Fin k)) :
    out₁ (stateIC W pQ) = stateMAC (out₁ W) pQ := by
  funext f
  simp only [out₁, stateIC, stateMAC, PMF.map_bind, PMF.map_comp]
  rfl

private lemma out₂_stateIC (W : DMC (A₁ × A₂) (B₁ × B₂)) (pQ : PMF (Fin k)) :
    out₂ (stateIC W pQ) = stateMAC (out₂ W) pQ := by
  funext f
  simp only [out₂, stateIC, stateMAC, PMF.map_bind, PMF.map_comp]
  rfl

private def tag (z : Fin k × (B₁ × B₂)) : (Fin k × B₁) × (Fin k × B₂) :=
  ((z.1, z.2.1), (z.1, z.2.2))

private lemma stateIC_apply [Fintype B₁] [Fintype B₂] [DecidableEq B₁] [DecidableEq B₂]
    (W : DMC (A₁ × A₂) (B₁ × B₂)) (pQ : PMF (Fin k))
    (f : (Fin k → A₁) × (Fin k → A₂)) (y : (Fin k × B₁) × (Fin k × B₂)) :
    stateIC W pQ f y = ∑ z, if tag z = y then pQ z.1 * W (f.1 z.1, f.2 z.1) z.2 else 0 := by
  have e : stateIC W pQ f = (stateMAC W pQ f).map tag := by
    simp only [stateIC, stateMAC, PMF.map_bind, PMF.map_comp]
    rfl
  rw [e, PMF.map_apply, tsum_fintype]
  refine sum_congr rfl fun z _ => ?_
  rw [stateMAC_apply]
  by_cases h : tag z = y
  · simp [h]
  · simp [h, Ne.symm h]

private def fixCode {M₁ M₂ : Type*} {n : ℕ}
    (c : ICCode M₁ M₂ (Fin k → A₁) (Fin k → A₂) (Fin k × B₁) (Fin k × B₂) n)
    (s : Fin n → Fin k) : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n :=
  ⟨fun m i => c.enc₁ m i (s i), fun m i => c.enc₂ m i (s i),
    fun y => c.dec₁ fun i => (s i, y i), fun y => c.dec₂ fun i => (s i, y i)⟩

private lemma prod_ite_eq {ι α : Type*} [Fintype ι] [DecidableEq α]
    (u v : ι → α) (t : ι → ℝ≥0∞) :
    ∏ i, (if u i = v i then t i else 0) = if u = v then ∏ i, t i else 0 := by
  classical
  by_cases h : u = v
  · simp [h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    exact prod_eq_zero (mem_univ i) (ite_eq_right_of_eq_false _ _ (eq_false hi))

private lemma errorProb_stateIC [Fintype B₁] [Fintype B₂] {M₁ M₂ : Type*} [DecidableEq M₁]
    [DecidableEq M₂] {n : ℕ} (W : DMC (A₁ × A₂) (B₁ × B₂)) (pQ : PMF (Fin k))
    (c : ICCode M₁ M₂ (Fin k → A₁) (Fin k → A₂) (Fin k × B₁) (Fin k × B₂) n) (m : M₁ × M₂) :
    c.errorProb (stateIC W pQ) m =
      ∑ s : Fin n → Fin k, (∏ i, pQ (s i)) * (fixCode c s).errorProb W m := by
  classical
  set D : (Fin n → (Fin k × B₁) × (Fin k × B₂)) → M₁ × M₂ :=
    fun y => (c.dec₁ fun i => (y i).1, c.dec₂ fun i => (y i).2)
  set T : Fin n → Fin k × (B₁ × B₂) → ℝ≥0∞ :=
    fun i z => pQ z.1 * W (c.enc₁ m.1 i z.1, c.enc₂ m.2 i z.1) z.2
  have h1 : ∀ y, DMC.blockProb (stateIC W pQ) (fun i => (c.enc₁ m.1 i, c.enc₂ m.2 i)) y =
      ∑ z : Fin n → Fin k × (B₁ × B₂), if (fun i => tag (z i)) = y then ∏ i, T i (z i)
        else 0 := fun y => by
    simp only [DMC.blockProb, stateIC_apply]
    rw [Fintype.prod_sum]
    exact sum_congr rfl fun z _ => prod_ite_eq _ _ _
  have h2 : c.errorProb (stateIC W pQ) m = ∑ z : Fin n → Fin k × (B₁ × B₂),
      if D (fun i => tag (z i)) = m then 0 else ∏ i, T i (z i) := by
    rw [ICCode.errorProb]
    simp only [h1]
    have e : ∀ y : Fin n → (Fin k × B₁) × (Fin k × B₂),
        (if D y = m then 0 else ∑ z : Fin n → Fin k × (B₁ × B₂),
          if (fun i => tag (z i)) = y then ∏ i, T i (z i) else 0) =
        ∑ z : Fin n → Fin k × (B₁ × B₂), if (fun i => tag (z i)) = y then
          (if D (fun i => tag (z i)) = m then 0 else ∏ i, T i (z i)) else 0 := fun y => by
      by_cases hy : D y = m
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hy)]
        refine (sum_eq_zero fun z _ => ?_).symm
        by_cases hz : (fun i => tag (z i)) = y
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hz), hz,
            ite_eq_left_of_eq_true _ _ (eq_true hy)]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hz)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hy)]
        refine sum_congr rfl fun z _ => ?_
        by_cases hz : (fun i => tag (z i)) = y
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hz), ite_eq_left_of_eq_true _ _ (eq_true hz), hz,
            ite_eq_right_of_eq_false _ _ (eq_false hy)]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hz),
            ite_eq_right_of_eq_false _ _ (eq_false hz)]
    change (∑ y, if D y = m then 0 else _) = _
    rw [sum_congr rfl fun y _ => e y, sum_comm]
    exact sum_congr rfl fun z _ => by rw [sum_ite_eq]; simp
  rw [h2, ← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin k)
    (fun _ => B₁ × B₂)).symm.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun s _ => ?_
  rw [ICCode.errorProb, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  have hD : D (fun i => tag (((Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin k)
      (fun _ => B₁ × B₂)).symm (s, b)) i)) =
      ((fixCode c s).dec₁ fun i => (b i).1, (fixCode c s).dec₂ fun i => (b i).2) := rfl
  rw [hD]
  split_ifs
  · simp
  · simp only [T, DMC.blockProb, fixCode, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk,
      prod_mul_distrib]

private lemma exists_fixCode_avgError_le [Fintype B₁] [Fintype B₂] {M₁ M₂ : Type*}
    [Fintype M₁] [Fintype M₂] [DecidableEq M₁] [DecidableEq M₂] {n : ℕ}
    (W : DMC (A₁ × A₂) (B₁ × B₂)) (pQ : PMF (Fin k))
    (c : ICCode M₁ M₂ (Fin k → A₁) (Fin k → A₂) (Fin k × B₁) (Fin k × B₂) n) :
    ∃ s, (fixCode c s).avgError W ≤ c.avgError (stateIC W pQ) := by
  classical
  have : Nonempty (Fin k) := ⟨pQ.support_nonempty.some⟩
  obtain ⟨s₀, -, hs₀⟩ := exists_min_image univ (fun s : Fin n → Fin k => (fixCode c s).avgError W)
    univ_nonempty
  refine ⟨s₀, ?_⟩
  have hw : ∑ s : Fin n → Fin k, ∏ i, pQ (s i) = 1 := by
    rw [← Fintype.prod_sum (fun _ q => pQ q)]
    refine prod_eq_one fun i _ => ?_
    have h := PMF.tsum_coe pQ
    rwa [tsum_fintype] at h
  have e : c.avgError (stateIC W pQ) =
      ∑ s : Fin n → Fin k, (∏ i, pQ (s i)) * (fixCode c s).avgError W := by
    simp only [ICCode.avgError, errorProb_stateIC, div_eq_mul_inv, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun s _ => sum_congr rfl fun m _ => by ring
  rw [e]
  calc (fixCode c s₀).avgError W = ∑ s : Fin n → Fin k, (∏ i, pQ (s i)) *
        (fixCode c s₀).avgError W := by rw [← sum_mul, hw, one_mul]
    _ ≤ _ := sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hs₀ s (mem_univ s)) zero_le

private lemma Achievable.of_stateIC [Fintype B₁] [Fintype B₂] {W : DMC (A₁ × A₂) (B₁ × B₂)}
    {pQ : PMF (Fin k)} {R₁ R₂ : ℝ} (h : Achievable (stateIC W pQ) R₁ R₂) :
    Achievable W R₁ R₂ := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hn
  obtain ⟨s, hs⟩ := exists_fixCode_avgError_le W pQ c
  exact ⟨k₁, k₂, hk₁, hk₂, fixCode c s, hs.trans hc⟩

end Derandomize

section Main

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

theorem strongTimeSharingRegion_subset_closure_achievableRegion {W : DMC (A₁ × A₂) (B₁ × B₂)}
    (hW : StrongInterference W) {k : ℕ} (pQ : PMF (Fin k)) (p₁ : Fin k → PMF A₁)
    (p₂ : Fin k → PMF A₂) :
    strongTimeSharingRegion W pQ p₁ p₂ ⊆ closure (achievableRegion W) := by
  rintro R ⟨h1, h2, ha, hb, hc₁, hc₂⟩
  refine mem_closure_achievableRegion W h1 h2 fun δ hδ => ?_
  have hw : ∀ q, 0 ≤ (pQ q).toReal := fun q => ENNReal.toReal_nonneg
  have hb₁ := state_bound₂ (out₁ W) pQ p₁ p₂
  have hb' : ∑ q, (pQ q).toReal * I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 |
      fun ω => ω.1 ; MAC.jointMeasure (out₂ W) (p₁ q) (p₂ q)] ≤
      ∑ q, (pQ q).toReal * I[fun ω : A₁ × A₂ × B₁ => ω.2.1 : fun ω => ω.2.2 |
        fun ω => ω.1 ; MAC.jointMeasure (out₁ W) (p₁ q) (p₂ q)] :=
    sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hW (p₁ q) (p₂ q)).2 (hw q)
  have ha' : ∑ q, (pQ q).toReal * I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 |
      fun ω => ω.2.1 ; MAC.jointMeasure (out₁ W) (p₁ q) (p₂ q)] ≤
      ∑ q, (pQ q).toReal * I[fun ω : A₁ × A₂ × B₂ => ω.1 : fun ω => ω.2.2 |
        fun ω => ω.2.1 ; MAC.jointMeasure (out₂ W) (p₁ q) (p₂ q)] :=
    sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hW (p₁ q) (p₂ q)).1 (hw q)
  have ha₁ := state_bound₁ (out₁ W) pQ p₁ p₂
  have hc₁' := state_bound₃ (out₁ W) pQ p₁ p₂
  have ha₂ := state_bound₁ (out₂ W) pQ p₁ p₂
  have hb₂ := state_bound₂ (out₂ W) pQ p₁ p₂
  have hc₂' := state_bound₃ (out₂ W) pQ p₁ p₂
  refine Achievable.of_stateIC (pQ := pQ) (achievable_of_lt (stateIC W pQ) (prodPMF p₁)
    (prodPMF p₂) ?_ ?_ ?_ ?_ ?_ ?_)
  · rw [out₁_stateIC]; linarith
  · rw [out₁_stateIC]; linarith
  · rw [out₁_stateIC]; linarith
  · rw [out₂_stateIC]; linarith
  · rw [out₂_stateIC]; linarith
  · rw [out₂_stateIC]; linarith

theorem strongCapacityRegion_subset_closure_achievableRegion {W : DMC (A₁ × A₂) (B₁ × B₂)}
    (hW : StrongInterference W) : strongCapacityRegion W ⊆ closure (achievableRegion W) :=
  closure_minimal (Set.iUnion_subset fun _ => Set.iUnion_subset fun pQ =>
    Set.iUnion_subset fun p₁ => Set.iUnion_subset fun p₂ =>
      strongTimeSharingRegion_subset_closure_achievableRegion hW pQ p₁ p₂) isClosed_closure

theorem closure_achievableRegion_eq_strongCapacityRegion {W : DMC (A₁ × A₂) (B₁ × B₂)}
    (hW : StrongInterference W) : closure (achievableRegion W) = strongCapacityRegion W :=
  (closure_achievableRegion_subset_strongCapacityRegion hW).antisymm
    (strongCapacityRegion_subset_closure_achievableRegion hW)

end Main

end IC

end Meat
