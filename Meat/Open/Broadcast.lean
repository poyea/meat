import Meat.Channel.BroadcastAchievability
import Meat.Shannon.Conditional

open MeasureTheory
open scoped ENNReal

namespace Meat

section Relabel

variable {Ω S S' T T' U U' : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype S'] [MeasurableSpace S'] [MeasurableSingletonClass S']
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype T'] [MeasurableSpace T'] [MeasurableSingletonClass T']
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype U'] [MeasurableSpace U'] [MeasurableSingletonClass U']
  (μ : Measure Ω)

private lemma entropy_comp_inj {X : Ω → S} {f : S → S'} (hf : Function.Injective f) :
    H[fun ω => f (X ω) ; μ] = H[X ; μ] :=
  entropy_comp_of_injective μ hf

private lemma condMutualInfo_comp_inj {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {f : S → S'}
    {g : T → T'} {h : U → U'} (hf : Function.Injective f) (hg : Function.Injective g)
    (hh : Function.Injective h) :
    I[fun ω => f (X ω) : fun ω => g (Y ω) | fun ω => h (Z ω) ; μ] = I[X : Y | Z ; μ] := by
  have e1 : H[fun ω => (f (X ω), h (Z ω)) ; μ] = H[fun ω => (X ω, Z ω) ; μ] :=
    entropy_comp_inj μ (X := fun ω => (X ω, Z ω)) (f := Prod.map f h) (hf.prodMap hh)
  have e2 : H[fun ω => (g (Y ω), h (Z ω)) ; μ] = H[fun ω => (Y ω, Z ω) ; μ] :=
    entropy_comp_inj μ (X := fun ω => (Y ω, Z ω)) (f := Prod.map g h) (hg.prodMap hh)
  have e3 : H[fun ω => ((f (X ω), g (Y ω)), h (Z ω)) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_inj μ (X := fun ω => ((X ω, Y ω), Z ω)) (f := Prod.map (Prod.map f g) h)
      ((hf.prodMap hg).prodMap hh)
  have e4 : H[fun ω => h (Z ω) ; μ] = H[Z ; μ] := entropy_comp_inj μ hh
  simp only [condMutualInfo_def, condEntropy_def]
  rw [e1, e2, e3, e4]

private lemma mutualInfo_comp_inj {X : Ω → S} {Y : Ω → T} {f : S → S'} {g : T → T'}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    I[fun ω => f (X ω) : fun ω => g (Y ω) ; μ] = I[X : Y ; μ] := by
  have e1 : H[fun ω => (f (X ω), g (Y ω)) ; μ] = H[fun ω => (X ω, Y ω) ; μ] :=
    entropy_comp_inj μ (X := fun ω => (X ω, Y ω)) (f := Prod.map f g) (hf.prodMap hg)
  simp only [mutualInfo_def]
  rw [e1, entropy_comp_inj μ hf, entropy_comp_inj μ hg]

private lemma condMutualInfo_const_right (X : Ω → S) (Z : Ω → U) (c : T) :
    I[X : fun _ => c | Z ; μ] = 0 := by
  have h1 : H[fun ω => (X ω, c) | Z ; μ] = H[X | Z ; μ] :=
    condEntropy_comp_of_injective μ (X := X) (f := fun s => (s, c)) fun _ _ h =>
      congrArg Prod.fst h
  have h2 : H[fun ω => (c, Z ω) ; μ] = H[Z ; μ] :=
    entropy_comp_inj μ (X := Z) (f := fun u => (c, u)) fun _ _ h => congrArg Prod.snd h
  have h3 : H[fun _ => c | Z ; μ] = 0 := by
    rw [condEntropy_def, h2, sub_self]
  rw [condMutualInfo_def, h1, h3]
  ring

private lemma mutualInfo_pair_const (X : Ω → S) (Y : Ω → T) (c : U) :
    I[fun ω => (X ω, c) : Y ; μ] = I[X : Y ; μ] :=
  mutualInfo_comp_inj μ (X := X) (Y := Y) (f := fun s => (s, c)) (g := id)
    (fun _ _ h => congrArg Prod.fst h) Function.injective_id

end Relabel

namespace BC

variable {A B₁ B₂ T V V₁ V₂ : Type*}

section Regions

variable [Fintype A] [MeasurableSpace A] [Fintype B₁] [MeasurableSpace B₁]
  [Fintype B₂] [MeasurableSpace B₂] [Fintype T] [MeasurableSpace T]
  [Fintype V₁] [MeasurableSpace V₁] [Fintype V₂] [MeasurableSpace V₂]

noncomputable def martonSumRate (W : DMC A (B₁ × B₂)) (q : PMF (T × V₁ × V₂))
    (pX : T × V₁ × V₂ → PMF A) : ℝ :=
  I[fun ω : (T × V₁ × V₂) × A × B₁ × B₂ => ω.1.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1.1 ;
      jointMeasure W q pX] +
    I[fun ω : (T × V₁ × V₂) × A × B₁ × B₂ => ω.1.2.2 : fun ω => ω.2.2.2 | fun ω => ω.1.1 ;
      jointMeasure W q pX] -
    I[fun ω : (T × V₁ × V₂) × A × B₁ × B₂ => ω.1.2.1 : fun ω => ω.1.2.2 | fun ω => ω.1.1 ;
      jointMeasure W q pX]

noncomputable def martonRegionOf (W : DMC A (B₁ × B₂)) (q : PMF (T × V₁ × V₂))
    (pX : T × V₁ × V₂ → PMF A) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧
    R.1 ≤ I[fun ω : (T × V₁ × V₂) × A × B₁ × B₂ => (ω.1.1, ω.1.2.1) : fun ω => ω.2.2.1 ;
      jointMeasure W q pX] ∧
    R.2 ≤ I[fun ω : (T × V₁ × V₂) × A × B₁ × B₂ => (ω.1.1, ω.1.2.2) : fun ω => ω.2.2.2 ;
      jointMeasure W q pX] ∧
    R.1 + R.2 ≤ I[fun ω : (T × V₁ × V₂) × A × B₁ × B₂ => ω.1.1 : fun ω => ω.2.2.1 ;
      jointMeasure W q pX] + martonSumRate W q pX ∧
    R.1 + R.2 ≤ I[fun ω : (T × V₁ × V₂) × A × B₁ × B₂ => ω.1.1 : fun ω => ω.2.2.2 ;
      jointMeasure W q pX] + martonSumRate W q pX}

noncomputable def martonRegion (W : DMC A (B₁ × B₂)) : Set (ℝ × ℝ) :=
  ⋃ (k₀ : ℕ) (k₁ : ℕ) (k₂ : ℕ) (q : PMF (Fin k₀ × Fin k₁ × Fin k₂))
    (pX : Fin k₀ × Fin k₁ × Fin k₂ → PMF A), martonRegionOf W q pX

noncomputable def uvRegionOf (W : DMC A (B₁ × B₂)) (q : PMF (V₁ × V₂))
    (pX : V₁ × V₂ → PMF A) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧
    R.1 ≤ I[fun ω : (V₁ × V₂) × A × B₁ × B₂ => ω.1.1 : fun ω => ω.2.2.1 ; jointMeasure W q pX] ∧
    R.2 ≤ I[fun ω : (V₁ × V₂) × A × B₁ × B₂ => ω.1.2 : fun ω => ω.2.2.2 ; jointMeasure W q pX] ∧
    R.1 + R.2 ≤
      I[fun ω : (V₁ × V₂) × A × B₁ × B₂ => ω.1.1 : fun ω => ω.2.2.1 ; jointMeasure W q pX] +
        I[fun ω : (V₁ × V₂) × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.2 | fun ω => ω.1.1 ;
          jointMeasure W q pX] ∧
    R.1 + R.2 ≤
      I[fun ω : (V₁ × V₂) × A × B₁ × B₂ => ω.1.2 : fun ω => ω.2.2.2 ; jointMeasure W q pX] +
        I[fun ω : (V₁ × V₂) × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1.2 ;
          jointMeasure W q pX]}

noncomputable def uvRegion (W : DMC A (B₁ × B₂)) : Set (ℝ × ℝ) :=
  ⋃ (k₁ : ℕ) (k₂ : ℕ) (q : PMF (Fin k₁ × Fin k₂)) (pX : Fin k₁ × Fin k₂ → PMF A),
    uvRegionOf W q pX

noncomputable def superpositionUnion (W : DMC A (B₁ × B₂)) : Set (ℝ × ℝ) :=
  ⋃ (k : ℕ) (pU : PMF (Fin k)) (pX : Fin k → PMF A), superpositionRegion W pU pX

end Regions

section Inclusions

variable [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

noncomputable def martonLaw (pU : PMF V) (pX : V → PMF A) : PMF (V × A × Unit) :=
  pU.bind fun u => (pX u).map fun a => (u, a, ())

noncomputable def uvLaw (pU : PMF V) (pX : V → PMF A) : PMF (A × V) :=
  pU.bind fun u => (pX u).map fun a => (a, u)

omit [Fintype V] [Fintype A] [Fintype B₁] [Fintype B₂] in
theorem jointMeasure_martonLaw [Finite V] [Finite A] [Finite B₁] [Finite B₂]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    jointMeasure W (martonLaw pU pX) (fun t => PMF.pure t.2.1) =
      (jointMeasure W pU pX).map fun ω => ((ω.1, ω.2.1, ()), ω.2.1, ω.2.2) := by
  rw [jointMeasure_eq_toMeasure, jointMeasure_eq_toMeasure,
    PMF.toMeasure_map _ _ (measurable_of_finite _)]
  congr 1
  simp only [jointPMF, martonLaw, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

omit [Fintype V] [Fintype A] [Fintype B₁] [Fintype B₂] in
theorem jointMeasure_uvLaw [Finite V] [Finite A] [Finite B₁] [Finite B₂]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    jointMeasure W (uvLaw pU pX) (fun t => PMF.pure t.1) =
      (jointMeasure W pU pX).map fun ω => ((ω.2.1, ω.1), ω.2.1, ω.2.2) := by
  rw [jointMeasure_eq_toMeasure, jointMeasure_eq_toMeasure,
    PMF.toMeasure_map _ _ (measurable_of_finite _)]
  congr 1
  simp only [jointPMF, uvLaw, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

omit [Fintype V] [MeasurableSingletonClass V] [Fintype A] [MeasurableSingletonClass A]
  [Fintype B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSingletonClass B₂] in
private lemma isProbabilityMeasure_jointMeasure (W : DMC A (B₁ × B₂)) (pU : PMF V)
    (pX : V → PMF A) : IsProbabilityMeasure (jointMeasure W pU pX) := by
  rw [jointMeasure_eq_toMeasure]
  infer_instance

omit [Fintype B₂] in
private lemma mutualInfo_pair_ge [Finite B₂] (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 ; jointMeasure W pU pX] ≤
      I[fun ω : V × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.1 ; jointMeasure W pU pX] +
        I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
          jointMeasure W pU pX] ∧
    I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
        jointMeasure W pU pX] ≤
      I[fun ω : V × A × B₁ × B₂ => (ω.1, ω.2.1) : fun ω => ω.2.2.1 ; jointMeasure W pU pX] := by
  have := isProbabilityMeasure_jointMeasure W pU pX
  set ν := jointMeasure W pU pX
  have e1 := mutualInfo_pair_eq_add_condMutualInfo ν (X := fun ω : V × A × B₁ × B₂ => ω.2.2.1)
    (Y := fun ω => ω.2.1) (Z := fun ω => ω.1)
  have e2 := mutualInfo_pair_eq_add_condMutualInfo ν (X := fun ω : V × A × B₁ × B₂ => ω.2.2.1)
    (Y := fun ω => ω.1) (Z := fun ω => ω.2.1)
  have e3 : I[fun ω : V × A × B₁ × B₂ => ω.2.2.1 : fun ω => (ω.1, ω.2.1) ; ν] =
      I[fun ω : V × A × B₁ × B₂ => ω.2.2.1 : fun ω => (ω.2.1, ω.1) ; ν] :=
    mutualInfo_comp_inj ν (X := fun ω : V × A × B₁ × B₂ => ω.2.2.1)
      (Y := fun ω => (ω.2.1, ω.1)) (f := id) (g := Prod.swap) Function.injective_id
      Prod.swap_injective
  have n1 := mutualInfo_nonneg ν (X := fun ω : V × A × B₁ × B₂ => ω.2.2.1) (Y := fun ω => ω.1)
    (measurable_of_finite _) (measurable_of_finite _)
  have n2 := condMutualInfo_nonneg ν (X := fun ω : V × A × B₁ × B₂ => ω.2.2.1)
    (Y := fun ω => ω.1) (Z := fun ω => ω.2.1) (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _)
  rw [mutualInfo_comm ν (X := fun ω : V × A × B₁ × B₂ => ω.2.1),
    mutualInfo_comm ν (X := fun ω : V × A × B₁ × B₂ => ω.1),
    mutualInfo_comm ν (X := fun ω : V × A × B₁ × B₂ => (ω.1, ω.2.1)),
    condMutualInfo_comm ν (X := fun ω : V × A × B₁ × B₂ => ω.2.1)]
  constructor <;> linarith

theorem superpositionRegion_subset_martonRegionOf (W : DMC A (B₁ × B₂)) (pU : PMF V)
    (pX : V → PMF A) :
    superpositionRegion W pU pX ⊆ martonRegionOf W (martonLaw pU pX) (fun t => PMF.pure t.2.1) := by
  rintro R ⟨h0₁, h0₂, h₁, h₂, h₃⟩
  have := isProbabilityMeasure_jointMeasure W pU pX
  obtain ⟨g₁, g₂⟩ := mutualInfo_pair_ge W pU pX
  simp only [martonRegionOf, martonSumRate, jointMeasure_martonLaw, Set.mem_ofPred_eq,
    mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _), Function.comp_def]
  set ν := jointMeasure W pU pX
  rw [condMutualInfo_comm ν (X := fun _ : V × A × B₁ × B₂ => ()),
    condMutualInfo_const_right, condMutualInfo_const_right,
    mutualInfo_pair_const ν (fun x : V × A × B₁ × B₂ => x.1) (fun x => x.2.2.2)]
  exact ⟨h0₁, h0₂, h₁.trans g₂, h₂, by linarith, by linarith⟩

theorem superpositionRegion_subset_uvRegionOf (W : DMC A (B₁ × B₂)) (pU : PMF V)
    (pX : V → PMF A) :
    superpositionRegion W pU pX ⊆ uvRegionOf W (uvLaw pU pX) (fun t => PMF.pure t.1) := by
  rintro R ⟨h0₁, h0₂, h₁, h₂, h₃⟩
  have := isProbabilityMeasure_jointMeasure W pU pX
  simp only [uvRegionOf, jointMeasure_uvLaw, Set.mem_ofPred_eq,
    mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _), Function.comp_def]
  have n := condMutualInfo_nonneg (jointMeasure W pU pX)
    (X := fun ω : V × A × B₁ × B₂ => ω.2.1) (Y := fun ω => ω.2.2.2) (Z := fun ω => ω.2.1)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
  exact ⟨h0₁, h0₂, by linarith, h₂, by linarith, by linarith⟩

end Inclusions

section Relabel

variable {V' : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype V'] [MeasurableSpace V'] [MeasurableSingletonClass V']
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

omit [Fintype V] [Fintype V'] [MeasurableSingletonClass V'] [Fintype A] [Fintype B₁]
  [Fintype B₂] in
theorem jointMeasure_map_equiv [Finite V] [Finite A] [Finite B₁] [Finite B₂]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) (e : V ≃ V') :
    jointMeasure W (pU.map e) (fun v => pX (e.symm v)) =
      (jointMeasure W pU pX).map fun ω => (e ω.1, ω.2) := by
  rw [jointMeasure_eq_toMeasure, jointMeasure_eq_toMeasure,
    PMF.toMeasure_map _ _ (measurable_of_finite _)]
  congr 1
  simp only [jointPMF, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
    Equiv.symm_apply_apply]

theorem superpositionRegion_map_equiv (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A)
    (e : V ≃ V') :
    superpositionRegion W (pU.map e) (fun v => pX (e.symm v)) = superpositionRegion W pU pX := by
  have := isProbabilityMeasure_jointMeasure W pU pX
  simp only [superpositionRegion, jointMeasure_map_equiv,
    mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _), Function.comp_def]
  have h1 := condMutualInfo_comp_inj (jointMeasure W pU pX)
    (X := fun ω : V × A × B₁ × B₂ => ω.2.1) (Y := fun ω => ω.2.2.1) (Z := fun ω => ω.1)
    (f := id) (g := id) (h := e) Function.injective_id Function.injective_id e.injective
  have h2 := mutualInfo_comp_inj (jointMeasure W pU pX)
    (X := fun ω : V × A × B₁ × B₂ => ω.1) (Y := fun ω => ω.2.2.2)
    (f := e) (g := id) e.injective Function.injective_id
  simp only [id] at h1 h2
  rw [h1, h2]

omit [Fintype A] in
theorem martonRegionOf_map_equiv {T' V₁' V₂' : Type*} [Finite A] [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] [Fintype V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
    [Fintype V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂] [Fintype T']
    [MeasurableSpace T'] [MeasurableSingletonClass T'] [Fintype V₁'] [MeasurableSpace V₁']
    [MeasurableSingletonClass V₁'] [Fintype V₂'] [MeasurableSpace V₂']
    [MeasurableSingletonClass V₂'] (W : DMC A (B₁ × B₂)) (q : PMF (T × V₁ × V₂))
    (pX : T × V₁ × V₂ → PMF A) (e₀ : T ≃ T') (e₁ : V₁ ≃ V₁') (e₂ : V₂ ≃ V₂') :
    martonRegionOf W (q.map (e₀.prodCongr (e₁.prodCongr e₂)))
        (fun t => pX ((e₀.prodCongr (e₁.prodCongr e₂)).symm t)) = martonRegionOf W q pX := by
  have := isProbabilityMeasure_jointMeasure W q pX
  rw [martonRegionOf, martonRegionOf, martonSumRate, martonSumRate, jointMeasure_map_equiv]
  simp only [mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _), Function.comp_def,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  set ν := jointMeasure W q pX
  have h1 : I[fun x : (T × V₁ × V₂) × A × B₁ × B₂ => (e₀ x.1.1, e₁ x.1.2.1) : fun x => x.2.2.1 ;
      ν] = I[fun ω => (ω.1.1, ω.1.2.1) : fun ω => ω.2.2.1 ; ν] :=
    mutualInfo_comp_inj ν (X := fun ω => (ω.1.1, ω.1.2.1)) (Y := fun ω => ω.2.2.1)
      (f := Prod.map e₀ e₁) (g := id)
      (e₀.injective.prodMap e₁.injective) Function.injective_id
  have h2 : I[fun x : (T × V₁ × V₂) × A × B₁ × B₂ => (e₀ x.1.1, e₂ x.1.2.2) : fun x => x.2.2.2 ;
      ν] = I[fun ω => (ω.1.1, ω.1.2.2) : fun ω => ω.2.2.2 ; ν] :=
    mutualInfo_comp_inj ν (X := fun ω => (ω.1.1, ω.1.2.2)) (Y := fun ω => ω.2.2.2)
      (f := Prod.map e₀ e₂) (g := id)
      (e₀.injective.prodMap e₂.injective) Function.injective_id
  have h3 : I[fun x : (T × V₁ × V₂) × A × B₁ × B₂ => e₀ x.1.1 : fun x => x.2.2.1 ; ν] =
      I[fun ω => ω.1.1 : fun ω => ω.2.2.1 ; ν] :=
    mutualInfo_comp_inj ν (X := fun ω => ω.1.1) (Y := fun ω => ω.2.2.1) (f := e₀) (g := id)
      e₀.injective Function.injective_id
  have h4 : I[fun x : (T × V₁ × V₂) × A × B₁ × B₂ => e₀ x.1.1 : fun x => x.2.2.2 ; ν] =
      I[fun ω => ω.1.1 : fun ω => ω.2.2.2 ; ν] :=
    mutualInfo_comp_inj ν (X := fun ω => ω.1.1) (Y := fun ω => ω.2.2.2) (f := e₀) (g := id)
      e₀.injective Function.injective_id
  have h5 : I[fun x : (T × V₁ × V₂) × A × B₁ × B₂ => e₁ x.1.2.1 : fun x => x.2.2.1 |
      fun x => e₀ x.1.1 ; ν] = I[fun ω => ω.1.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1.1 ; ν] :=
    condMutualInfo_comp_inj ν (X := fun ω => ω.1.2.1) (Y := fun ω => ω.2.2.1)
      (Z := fun ω => ω.1.1) (f := e₁) (g := id) (h := e₀) e₁.injective Function.injective_id
      e₀.injective
  have h6 : I[fun x : (T × V₁ × V₂) × A × B₁ × B₂ => e₂ x.1.2.2 : fun x => x.2.2.2 |
      fun x => e₀ x.1.1 ; ν] = I[fun ω => ω.1.2.2 : fun ω => ω.2.2.2 | fun ω => ω.1.1 ; ν] :=
    condMutualInfo_comp_inj ν (X := fun ω => ω.1.2.2) (Y := fun ω => ω.2.2.2)
      (Z := fun ω => ω.1.1) (f := e₂) (g := id) (h := e₀) e₂.injective Function.injective_id
      e₀.injective
  have h7 : I[fun x : (T × V₁ × V₂) × A × B₁ × B₂ => e₁ x.1.2.1 : fun x => e₂ x.1.2.2 |
      fun x => e₀ x.1.1 ; ν] = I[fun ω => ω.1.2.1 : fun ω => ω.1.2.2 | fun ω => ω.1.1 ; ν] :=
    condMutualInfo_comp_inj ν (X := fun ω => ω.1.2.1) (Y := fun ω => ω.1.2.2)
      (Z := fun ω => ω.1.1) (f := e₁) (g := e₂) (h := e₀) e₁.injective e₂.injective
      e₀.injective
  rw [h1, h2, h3, h4, h5, h6, h7]

theorem uvRegionOf_map_equiv {V₁' V₂' : Type*} [Fintype V₁] [MeasurableSpace V₁]
    [MeasurableSingletonClass V₁] [Fintype V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
    [Fintype V₁'] [MeasurableSpace V₁'] [MeasurableSingletonClass V₁'] [Fintype V₂']
    [MeasurableSpace V₂'] [MeasurableSingletonClass V₂'] (W : DMC A (B₁ × B₂))
    (q : PMF (V₁ × V₂)) (pX : V₁ × V₂ → PMF A) (e₁ : V₁ ≃ V₁') (e₂ : V₂ ≃ V₂') :
    uvRegionOf W (q.map (e₁.prodCongr e₂)) (fun t => pX ((e₁.prodCongr e₂).symm t)) =
      uvRegionOf W q pX := by
  have := isProbabilityMeasure_jointMeasure W q pX
  rw [uvRegionOf, uvRegionOf, jointMeasure_map_equiv]
  simp only [mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _), Function.comp_def,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  set ν := jointMeasure W q pX
  have h1 : I[fun x : (V₁ × V₂) × A × B₁ × B₂ => e₁ x.1.1 : fun x => x.2.2.1 ; ν] =
      I[fun ω => ω.1.1 : fun ω => ω.2.2.1 ; ν] :=
    mutualInfo_comp_inj ν (X := fun ω => ω.1.1) (Y := fun ω => ω.2.2.1) (f := e₁) (g := id)
      e₁.injective Function.injective_id
  have h2 : I[fun x : (V₁ × V₂) × A × B₁ × B₂ => e₂ x.1.2 : fun x => x.2.2.2 ; ν] =
      I[fun ω => ω.1.2 : fun ω => ω.2.2.2 ; ν] :=
    mutualInfo_comp_inj ν (X := fun ω => ω.1.2) (Y := fun ω => ω.2.2.2) (f := e₂) (g := id)
      e₂.injective Function.injective_id
  have h3 : I[fun x : (V₁ × V₂) × A × B₁ × B₂ => x.2.1 : fun x => x.2.2.2 | fun x => e₁ x.1.1 ;
      ν] = I[fun ω => ω.2.1 : fun ω => ω.2.2.2 | fun ω => ω.1.1 ; ν] :=
    condMutualInfo_comp_inj ν (X := fun ω => ω.2.1) (Y := fun ω => ω.2.2.2)
      (Z := fun ω => ω.1.1) (f := id) (g := id) (h := e₁) Function.injective_id
      Function.injective_id e₁.injective
  have h4 : I[fun x : (V₁ × V₂) × A × B₁ × B₂ => x.2.1 : fun x => x.2.2.1 | fun x => e₂ x.1.2 ;
      ν] = I[fun ω => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1.2 ; ν] :=
    condMutualInfo_comp_inj ν (X := fun ω => ω.2.1) (Y := fun ω => ω.2.2.1)
      (Z := fun ω => ω.1.2) (f := id) (g := id) (h := e₂) Function.injective_id
      Function.injective_id e₂.injective
  rw [h1, h2, h3, h4]

theorem superpositionUnion_subset_martonRegion (W : DMC A (B₁ × B₂)) :
    superpositionUnion W ⊆ martonRegion W := by
  intro R hR
  simp only [superpositionUnion, Set.mem_iUnion] at hR
  obtain ⟨k, pU, pX, hR⟩ := hR
  have h := superpositionRegion_subset_martonRegionOf W pU pX hR
  rw [← martonRegionOf_map_equiv W _ _ (Equiv.refl _) (Fintype.equivFin A) finOneEquiv.symm] at h
  simp only [martonRegion, Set.mem_iUnion]
  exact ⟨k, _, 1, _, _, h⟩

theorem superpositionUnion_subset_uvRegion (W : DMC A (B₁ × B₂)) :
    superpositionUnion W ⊆ uvRegion W := by
  intro R hR
  simp only [superpositionUnion, Set.mem_iUnion] at hR
  obtain ⟨k, pU, pX, hR⟩ := hR
  have h := superpositionRegion_subset_uvRegionOf W pU pX hR
  rw [← uvRegionOf_map_equiv W _ _ (Fintype.equivFin A) (Equiv.refl _)] at h
  simp only [uvRegion, Set.mem_iUnion]
  exact ⟨_, k, _, _, h⟩

theorem superpositionUnion_subset_closure (W : DMC A (B₁ × B₂)) :
    superpositionUnion W ⊆ closure (achievableRegion W) := by
  intro R hR
  simp only [superpositionUnion, Set.mem_iUnion] at hR
  obtain ⟨k, pU, pX, hR⟩ := hR
  exact superpositionRegion_subset W pU pX hR

theorem closure_superpositionUnion_subset (W : DMC A (B₁ × B₂)) :
    closure (superpositionUnion W) ⊆ closure (achievableRegion W) :=
  closure_minimal (superpositionUnion_subset_closure W) isClosed_closure

end Relabel

def IsDegraded (W : DMC A (B₁ × B₂)) : Prop :=
  ∃ D : DMC B₁ B₂, ∀ a, channel₂ W a = (channel₁ W a).bind D

def MartonIsCapacity : Prop :=
  ∀ (a b₁ b₂ : ℕ) (W : DMC (Fin a) (Fin b₁ × Fin b₂)),
    closure (achievableRegion W) = closure (martonRegion W)

end BC

end Meat
