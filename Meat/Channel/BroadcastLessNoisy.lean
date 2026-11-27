import Meat.Open.BroadcastUV

open MeasureTheory Finset ProbabilityTheory
open scoped ENNReal

namespace Meat

namespace BC

variable {A B₁ B₂ V : Type*}

def IsMoreCapable [Fintype A] [MeasurableSpace A] [Fintype B₁] [MeasurableSpace B₁]
    [Fintype B₂] [MeasurableSpace B₂] (W : DMC A (B₁ × B₂)) : Prop :=
  ∀ p : PMF A, (channel₂ W).inputMutualInfo p ≤ (channel₁ W).inputMutualInfo p

def IsLessNoisy [Fintype B₁] [MeasurableSpace B₁]
    [Fintype B₂] [MeasurableSpace B₂] (W : DMC A (B₁ × B₂)) : Prop :=
  ∀ (k : ℕ) (pU : PMF (Fin k)) (pX : Fin k → PMF A),
    (cloudChannel₂ W pX).inputMutualInfo pU ≤ (cloudChannel₁ W pX).inputMutualInfo pU

section Kernel

variable {Ω T S Y : Type*} [MeasurableSpace Ω] [Fintype T] [MeasurableSpace T]
  [MeasurableSingletonClass T] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

private lemma condMutualInfo_eq_sum_of_kernel (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Ω → T} {X : Ω → S} {Z : Ω → Y} (hG : Measurable G) (hX : Measurable X)
    (hZ : Measurable Z) (w : T → ℝ) (r : T → PMF S) (K : T → DMC S Y)
    (h : ∀ g x y, μ.real {ω | G ω = g ∧ X ω = x ∧ Z ω = y} =
      w g * (r g x).toReal * (K g x y).toReal) :
    I[X : Z | G ; μ] = ∑ g, w g * (K g).inputMutualInfo (r g) := by
  classical
  have hsum : ∀ (s : PMF Y), ∑ y, (s y).toReal = 1 := fun s => by
    rw [← ENNReal.toReal_sum fun _ _ => PMF.apply_ne_top _ _]
    have h := PMF.tsum_coe s
    rw [tsum_fintype] at h
    rw [h, ENNReal.toReal_one]
  have hsumS : ∀ (s : PMF S), ∑ y, (s y).toReal = 1 := fun s => by
    rw [← ENNReal.toReal_sum fun _ _ => PMF.apply_ne_top _ _]
    have h := PMF.tsum_coe s
    rw [tsum_fintype] at h
    rw [h, ENNReal.toReal_one]
  have hxg : ∀ g x, μ.real {ω | G ω = g ∧ X ω = x} = w g * (r g x).toReal := fun g x => by
    have h1 := sum_measureReal_inter (μ := μ) hZ {ω | G ω = g ∧ X ω = x}
    rw [← h1]
    have e : ∀ y, μ.real {ω | Z ω = y ∧ ω ∈ {ω | G ω = g ∧ X ω = x}} =
        μ.real {ω | G ω = g ∧ X ω = x ∧ Z ω = y} := fun y => by
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
    simp only [e, hxg, ← mul_sum, hsumS, mul_one]
  rw [Wiretap.condMutualInfo_eq_sum_cond μ hX hZ hG]
  refine sum_congr rfl fun g _ => ?_
  rw [hw]
  rcases eq_or_ne (w g) 0 with h0 | h0
  · simp [h0]
  congr 1
  have hne : μ (G ⁻¹' {g}) ≠ 0 := fun h' => h0 (by rw [← hw, measureReal_def, h']; rfl)
  have := cond_isProbabilityMeasure (μ := μ) hne
  have hmap : (μ[|G ⁻¹' {g}]).map (fun ω => (X ω, Z ω)) = (K g).jointMeasure (r g) := by
    refine Measure.ext_of_singleton fun t => ?_
    rw [Measure.map_apply (hX.prodMk hZ) (measurableSet_singleton _),
      DMC.jointMeasure_eq_toMeasure,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), DMC.jointPMF_apply,
      ← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def,
      ← ENNReal.ofReal_toReal (ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
        (PMF.apply_ne_top _ _))]
    congr 1
    rw [measureReal_def, cond_apply (hG (measurableSet_singleton g)), ENNReal.toReal_mul,
      ← measureReal_def, ENNReal.toReal_inv, ← measureReal_def, hw, ENNReal.toReal_mul]
    have e : G ⁻¹' {g} ∩ (fun ω => (X ω, Z ω)) ⁻¹' {t} =
        {ω | G ω = g ∧ X ω = t.1 ∧ Z ω = t.2} := by
      ext ω
      simp [Prod.ext_iff]
    rw [e, h]
    field_simp
  rw [DMC.inputMutualInfo, ← hmap, mutualInfo_map _ (hX.prodMk hZ) measurable_fst
    measurable_snd]
  rfl

end Kernel

section Laws

variable {B : Type*}

private lemma jointPMF_map_out (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A)
    (f : B₁ × B₂ → B) :
    (jointPMF W pU pX).map (fun ω => (ω.1, ω.2.1, f ω.2.2)) =
      (DMC.jointPMF (fun ux : V × A => (W ux.2).map f) (DMC.jointPMF pX pU)).map
        fun p => (p.1.1, p.1.2, p.2) := by
  simp only [jointPMF, DMC.jointPMF, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

private lemma jointPMF_map_out_apply (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A)
    (f : B₁ × B₂ → B) (u : V) (x : A) (y : B) :
    (jointPMF W pU pX).map (fun ω => (ω.1, ω.2.1, f ω.2.2)) (u, x, y) =
      pU u * pX u x * (W x).map f y := by
  rw [jointPMF_map_out, show ((u, x, y) : V × A × B) =
      (fun p : (V × A) × B => (p.1.1, p.1.2, p.2)) ((u, x), y) from rfl,
    map_apply_inj _ (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2), DMC.jointPMF_apply, DMC.jointPMF_apply]

private lemma jointPMF_map_input_out (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A)
    (f : B₁ × B₂ → B) :
    (jointPMF W pU pX).map (fun ω => (ω.2.1, f ω.2.2)) =
      DMC.jointPMF (fun a => (W a).map f) (pU.bind pX) := by
  simp only [jointPMF, DMC.jointPMF, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

end Laws

section Info

variable [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]
  {B : Type*} [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

omit [Fintype V] [MeasurableSingletonClass V] [Fintype A] [MeasurableSingletonClass A]
  [Fintype B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSingletonClass B₂] in
private lemma isProbabilityMeasure_jointMeasure' (W : DMC A (B₁ × B₂)) (pU : PMF V)
    (pX : V → PMF A) : IsProbabilityMeasure (jointMeasure W pU pX) := by
  rw [jointMeasure_eq_toMeasure]
  infer_instance

private lemma measureReal_setOf_eq {Ω : Type*} [Finite Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {R : Type*} [MeasurableSpace R] [MeasurableSingletonClass R]
    (σ : PMF Ω) (F : Ω → R) (v : R) :
    σ.toMeasure.real {ω | F ω = v} = (σ.map F v).toReal := by
  rw [← measureReal_map_toMeasure, map_measureReal_apply (measurable_of_finite _)
    (measurableSet_singleton _)]
  rfl

omit [Fintype B₁] [Fintype B₂] in
private lemma condMutualInfo_out_eq_sum [Finite B₁] [Finite B₂]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A)
    (f : B₁ × B₂ → B) :
    I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => f ω.2.2 | fun ω => ω.1 ;
        jointMeasure W pU pX] =
      ∑ u, (pU u).toReal * DMC.inputMutualInfo (fun a => (W a).map f) (pX u) := by
  have := isProbabilityMeasure_jointMeasure' W pU pX
  refine condMutualInfo_eq_sum_of_kernel _ (G := fun ω : V × A × B₁ × B₂ => ω.1)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (fun u => (pU u).toReal) pX (fun _ a => (W a).map f) fun u x y => ?_
  have e : {ω : V × A × B₁ × B₂ | ω.1 = u ∧ ω.2.1 = x ∧ f ω.2.2 = y} =
      {ω | (ω.1, ω.2.1, f ω.2.2) = (u, x, y)} := by
    ext ω
    simp [Prod.ext_iff]
  rw [jointMeasure_eq_toMeasure, e, measureReal_setOf_eq, jointPMF_map_out_apply,
    ENNReal.toReal_mul, ENNReal.toReal_mul]

omit [MeasurableSingletonClass B] [Fintype V] [Fintype B₁] [Fintype B₂] in
private lemma mutualInfo_out_eq [Finite V] [Finite B₁] [Finite B₂]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A)
    (f : B₁ × B₂ → B) :
    I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => f ω.2.2 ; jointMeasure W pU pX] =
      DMC.inputMutualInfo (fun a => (W a).map f) (pU.bind pX) := by
  rw [DMC.inputMutualInfo, DMC.jointMeasure_eq_toMeasure, ← jointPMF_map_input_out,
    ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    mutualInfo_map _ (measurable_of_finite _) measurable_fst measurable_snd]
  rfl

omit [Fintype B₂] in
private lemma mutualInfo_cloud_add [Finite B₂] (W : DMC A (B₁ × B₂)) (pU : PMF V)
    (pX : V → PMF A) :
    I[fun ω : V × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.1 ; jointMeasure W pU pX] +
      I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
        jointMeasure W pU pX] =
      I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 ; jointMeasure W pU pX] := by
  have := Fintype.ofFinite B₂
  set σ := jointPMF W pU pX
  have hν : jointMeasure W pU pX = σ.toMeasure := rfl
  rw [hν]
  have h1 := markovChain_of_memoryless W σ (jointPMF_memoryless W pU pX)
  rw [markovChain_def] at h1
  have h1' : I[fun ω : V × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.1 | fun ω => ω.2.1 ;
      σ.toMeasure] = 0 := le_antisymm
    ((condMutualInfo_comp_right_le (μ := σ.toMeasure) (X := fun ω : V × A × B₁ × B₂ => ω.1)
      (Y := fun ω => ω.2.2) (Z := fun ω => ω.2.1) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _) Prod.fst).trans_eq h1)
    (condMutualInfo_nonneg _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _))
  have e1 := mutualInfo_pair_eq_add_condMutualInfo σ.toMeasure
    (X := fun ω : V × A × B₁ × B₂ => ω.2.2.1) (Y := fun ω => ω.2.1) (Z := fun ω => ω.1)
  have e2 := mutualInfo_pair_eq_add_condMutualInfo σ.toMeasure
    (X := fun ω : V × A × B₁ × B₂ => ω.2.2.1) (Y := fun ω => ω.1) (Z := fun ω => ω.2.1)
  have e3 : I[fun ω : V × A × B₁ × B₂ => ω.2.2.1 : fun ω => (ω.2.1, ω.1) ; σ.toMeasure] =
      I[fun ω : V × A × B₁ × B₂ => ω.2.2.1 : fun ω => (ω.1, ω.2.1) ; σ.toMeasure] :=
    mutualInfo_comp_right_of_injective σ.toMeasure (Y := fun ω : V × A × B₁ × B₂ => (ω.1, ω.2.1))
      (f := Prod.swap) Prod.swap_injective
  rw [condMutualInfo_comm] at h1'
  rw [mutualInfo_comm σ.toMeasure (X := fun ω : V × A × B₁ × B₂ => ω.2.1),
    condMutualInfo_comm σ.toMeasure (X := fun ω : V × A × B₁ × B₂ => ω.2.1),
    mutualInfo_comm σ.toMeasure (X := fun ω : V × A × B₁ × B₂ => ω.1)]
  linarith

end Info

section Single

variable [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

omit [Fintype V] [Fintype A] [Fintype B₁] [Fintype B₂] in
private lemma exists_jointMeasure_map [Finite V] [Finite A] [Finite B₁] [Finite B₂]
    {V' : Type*} [Finite V'] [MeasurableSpace V'] (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A)
    (g : V → V') :
    ∃ (pU' : PMF V') (pX' : V' → PMF A),
      jointMeasure W pU' pX' = (jointMeasure W pU pX).map fun ω => (g ω.1, ω.2) := by
  set τ := (DMC.jointPMF pX pU).map (Prod.map g id)
  have hσ : (jointPMF W pU pX).map (fun ω => (g ω.1, ω.2)) =
      (DMC.jointPMF (fun vx : V' × A => W vx.2) τ).map fun p => (p.1.1, p.1.2, p.2) := by
    simp only [τ, jointPMF, DMC.jointPMF, PMF.map, PMF.bind_bind, PMF.pure_bind,
      Function.comp_def, Prod.map, id]
  have hinj : Function.Injective fun p : (V' × A) × B₁ × B₂ => (p.1.1, p.1.2, p.2) :=
    fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2
  obtain ⟨pU', pX', h⟩ := exists_jointPMF_eq W ((jointPMF W pU pX).map fun ω => (g ω.1, ω.2))
    fun v x y => by
      rw [hσ, PMF.map_comp]
      have hm : ((fun ω : V' × A × B₁ × B₂ => (ω.1, ω.2.1)) ∘
          fun p : (V' × A) × B₁ × B₂ => (p.1.1, p.1.2, p.2)) = Prod.fst := rfl
      rw [hm, DMC.jointPMF_map_fst, show ((v, x, y) : V' × A × B₁ × B₂) =
          (fun p : (V' × A) × B₁ × B₂ => (p.1.1, p.1.2, p.2)) ((v, x), y) from rfl,
        map_apply_inj _ hinj, DMC.jointPMF_apply]
  refine ⟨pU', pX', ?_⟩
  rw [jointMeasure_eq_toMeasure, h, jointMeasure_eq_toMeasure,
    PMF.toMeasure_map _ _ (measurable_of_finite _)]

private lemma condMutualInfo_le_of_isMoreCapable {W : DMC A (B₁ × B₂)} (hW : IsMoreCapable W)
    (pU : PMF V) (pX : V → PMF A) :
    I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.2 | fun ω => ω.1 ;
        jointMeasure W pU pX] ≤
      I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
        jointMeasure W pU pX] := by
  rw [condMutualInfo_out_eq_sum W pU pX Prod.snd, condMutualInfo_out_eq_sum W pU pX Prod.fst]
  exact sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hW (pX u)) ENNReal.toReal_nonneg

private noncomputable def coin (l : ℝ) (h0 : 0 ≤ l) (h1 : l ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => cond b (ENNReal.ofReal l) (ENNReal.ofReal (1 - l))) (by
    rw [Fintype.sum_bool]
    simp only [Bool.cond_true, Bool.cond_false]
    rw [← ENNReal.ofReal_add h0 (by linarith), add_sub_cancel, ENNReal.ofReal_one])

private lemma coin_toReal {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (b : Bool) :
    (coin l h0 h1 b).toReal = cond b l (1 - l) := by
  cases b
  · simp [coin, ENNReal.toReal_ofReal (show 0 ≤ 1 - l by linarith)]
  · simp [coin, ENNReal.toReal_ofReal h0]

private lemma exists_timeShare (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) {l : ℝ}
    (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    ∃ (pU' : PMF (Bool × V)) (pX' : Bool × V → PMF A),
      l * I[fun ω : V × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ; jointMeasure W pU pX] ≤
        I[fun ω : (Bool × V) × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ;
          jointMeasure W pU' pX'] ∧
      I[fun ω : (Bool × V) × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
          jointMeasure W pU' pX'] =
        l * I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
          jointMeasure W pU pX] +
        (1 - l) * I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 ;
          jointMeasure W pU pX] ∧
      I[fun ω : (Bool × V) × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 ;
          jointMeasure W pU' pX'] =
        I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 ; jointMeasure W pU pX] := by
  classical
  set β := coin l h0 h1 with hβdef
  have hβ : ∀ b, (β b).toReal = cond b l (1 - l) := coin_toReal h0 h1
  set pU' : PMF (Bool × V) := β.bind fun b => pU.map fun u => (b, u) with hpU'
  set pX' : Bool × V → PMF A := fun t => cond t.1 (pX t.2) (pU.bind pX) with hpX'
  have hU' : ∀ b u, pU' (b, u) = β b * pU u := by
    intro b u
    have e : ∀ b' : Bool, (pU.map fun u => (b', u)) (b, u) = if b' = b then pU u else 0 := by
      intro b'
      split_ifs with hb
      · subst hb
        exact map_apply_inj _ (fun _ _ h => congrArg Prod.snd h) u
      · rw [PMF.map_apply]
        simp [Ne.symm hb]
    rw [hpU', PMF.bind_apply, tsum_fintype, Fintype.sum_bool, e, e]
    cases b <;> simp
  have hbind : pU'.bind pX' = pU.bind pX := by
    have hb : ∀ b : Bool, pU.bind (fun u => pX' (b, u)) = pU.bind pX := by
      intro b
      cases b
      · exact PMF.bind_const _ _
      · rfl
    rw [hpU', PMF.bind_bind]
    simp only [PMF.bind_map, Function.comp_def, hb, PMF.bind_const]
  have hsum : ∑ u, (pU u).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun _ _ => PMF.apply_ne_top _ _]
    have h := PMF.tsum_coe pU
    rw [tsum_fintype] at h
    rw [h, ENNReal.toReal_one]
  refine ⟨pU', pX', ?_, ?_, ?_⟩
  · have := isProbabilityMeasure_jointMeasure' W pU' pX'
    set J' := jointMeasure W pU' pX'
    have hk := condMutualInfo_eq_sum_of_kernel J'
      (G := fun ω : (Bool × V) × A × B₁ × B₂ => ω.1.1) (X := fun ω => ω.1.2)
      (Z := fun ω => ω.2.2.2) (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (fun b => (β b).toReal) (fun _ => pU)
      (fun b => cloudChannel₂ W fun u => pX' (b, u)) fun b u y => by
        have e : {ω : (Bool × V) × A × B₁ × B₂ | ω.1.1 = b ∧ ω.1.2 = u ∧ ω.2.2.2 = y} =
            {ω | (ω.1, ω.2.2.2) = ((b, u), y)} := by
          ext ω
          simp [Prod.ext_iff, and_assoc]
        rw [show J' = (jointPMF W pU' pX').toMeasure from rfl, e, measureReal_setOf_eq,
          ← jointPMF_cloudChannel₂,
          DMC.jointPMF_apply, hU', ENNReal.toReal_mul, ENNReal.toReal_mul]
        rfl
    have ht : (cloudChannel₂ W fun u => pX' (true, u)) = cloudChannel₂ W pX := rfl
    rw [Fintype.sum_bool, hβ, hβ, ht, condMutualInfo_comm] at hk
    simp only [Bool.cond_true, Bool.cond_false] at hk
    have e1 := mutualInfo_pair_eq_add_condMutualInfo J'
      (X := fun ω : (Bool × V) × A × B₁ × B₂ => ω.2.2.2) (Y := fun ω => ω.1.2)
      (Z := fun ω => ω.1.1)
    have e2 : I[fun ω : (Bool × V) × A × B₁ × B₂ => ω.2.2.2 : fun ω => (ω.1.2, ω.1.1) ; J'] =
        I[fun ω : (Bool × V) × A × B₁ × B₂ => ω.2.2.2 : fun ω => ω.1 ; J'] :=
      mutualInfo_comp_right_of_injective J' (Y := fun ω : (Bool × V) × A × B₁ × B₂ => ω.1)
        (f := Prod.swap) Prod.swap_injective
    have n1 := mutualInfo_nonneg J' (X := fun ω : (Bool × V) × A × B₁ × B₂ => ω.2.2.2)
      (Y := fun ω => ω.1.1) (measurable_of_finite _) (measurable_of_finite _)
    have n2 := mul_nonneg (show 0 ≤ 1 - l by linarith)
      (DMC.inputMutualInfo_nonneg (cloudChannel₂ W fun u => pX' (false, u)) pU)
    rw [mutualInfo_cloud_eq, mutualInfo_comm J']
    linarith
  · rw [condMutualInfo_out_eq_sum W pU' pX' Prod.fst, condMutualInfo_out_eq_sum W pU pX Prod.fst,
      mutualInfo_out_eq W pU pX Prod.fst, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [hU', ENNReal.toReal_mul, hβ, hpX', Bool.cond_true, Bool.cond_false, mul_assoc,
      ← mul_sum]
    rw [← sum_mul, hsum, one_mul]
  · rw [mutualInfo_out_eq W pU' pX' Prod.fst, mutualInfo_out_eq W pU pX Prod.fst, hbind]

private lemma mem_superpositionUnion_of_mem {V' : Type*} [Fintype V'] [MeasurableSpace V']
    [MeasurableSingletonClass V'] (W : DMC A (B₁ × B₂)) (pU : PMF V') (pX : V' → PMF A)
    {R : ℝ × ℝ} (hR : R ∈ superpositionRegion W pU pX) : R ∈ superpositionUnion W := by
  rw [← superpositionRegion_map_equiv W pU pX (Fintype.equivFin V')] at hR
  simp only [superpositionUnion, Set.mem_iUnion]
  exact ⟨_, _, _, hR⟩

theorem mem_superpositionUnion_of_le (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A)
    {R : ℝ × ℝ} (h0₁ : 0 ≤ R.1) (h0₂ : 0 ≤ R.2)
    (h₂ : R.2 ≤ I[fun ω : V × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ; jointMeasure W pU pX])
    (h₃ : R.1 + R.2 ≤
      I[fun ω : V × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ; jointMeasure W pU pX] +
        I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
          jointMeasure W pU pX])
    (h₄ : R.1 + R.2 ≤
      I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 ; jointMeasure W pU pX]) :
    R ∈ superpositionUnion W := by
  have := isProbabilityMeasure_jointMeasure' W pU pX
  set a := I[fun ω : V × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ; jointMeasure W pU pX]
  set b := I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
    jointMeasure W pU pX]
  set c := I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 ; jointMeasure W pU pX]
  have hbc : b ≤ c := by
    have h := mutualInfo_cloud_add W pU pX
    have n := mutualInfo_nonneg (jointMeasure W pU pX)
      (X := fun ω : V × A × B₁ × B₂ => ω.1) (Y := fun ω => ω.2.2.1)
      (measurable_of_finite _) (measurable_of_finite _)
    linarith
  have ha : 0 ≤ a := mutualInfo_nonneg _ (measurable_of_finite _) (measurable_of_finite _)
  by_cases hb : R.1 ≤ b
  · exact mem_superpositionUnion_of_mem W pU pX ⟨h0₁, h0₂, hb, h₂, h₄⟩
  push Not at hb
  rcases ha.eq_or_lt with ha0 | ha0
  · obtain ⟨pU', pX', g₁, g₂, g₃⟩ := exists_timeShare W pU pX le_rfl zero_le_one
    have := isProbabilityMeasure_jointMeasure' W pU' pX'
    have n := mutualInfo_nonneg (jointMeasure W pU' pX')
      (X := fun ω : (Bool × V) × A × B₁ × B₂ => ω.1) (Y := fun ω => ω.2.2.2)
      (measurable_of_finite _) (measurable_of_finite _)
    refine mem_superpositionUnion_of_mem W pU' pX' ⟨h0₁, h0₂, ?_, ?_, ?_⟩
    · rw [g₂]
      linarith
    · linarith
    · rw [g₃]
      exact h₄
  set l := R.2 / a with hl
  have hla : l * a = R.2 := div_mul_cancel₀ _ ha0.ne'
  have hl0 : 0 ≤ l := div_nonneg h0₂ ha
  have hl1 : l ≤ 1 := (div_le_one ha0).2 h₂
  obtain ⟨pU', pX', g₁, g₂, g₃⟩ := exists_timeShare W pU pX hl0 hl1
  refine mem_superpositionUnion_of_mem W pU' pX' ⟨h0₁, h0₂, ?_, ?_, ?_⟩
  · rw [g₂]
    have key : a * R.1 + R.2 * (c - b) ≤ a * c := by
      rcases le_total (a + b) c with hc | hc
      · nlinarith [mul_nonneg (sub_nonneg.2 hb.le) (sub_nonneg.2 hc),
          mul_nonneg (sub_nonneg.2 hbc) (show 0 ≤ a + b - R.1 - R.2 by linarith)]
      · nlinarith [mul_nonneg (show 0 ≤ c - R.1 by linarith) (sub_nonneg.2 hc),
          mul_nonneg (sub_nonneg.2 hbc) (show 0 ≤ c - R.1 - R.2 by linarith)]
    have e : a * (l * b + (1 - l) * c) = a * c - R.2 * (c - b) := by
      rw [← hla]
      ring
    have : a * R.1 ≤ a * (l * b + (1 - l) * c) := by linarith
    exact le_of_mul_le_mul_left this ha0
  · linarith
  · rw [g₃]
    exact h₄

private lemma inputMutualInfo_relabel {B : Type*} [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (K : DMC A B) (p : PMF A) :
    DMC.inputMutualInfo (fun i => (PMF.pure ((Fintype.equivFin A).symm i)).bind K)
        (p.map (Fintype.equivFin A)) = K.inputMutualInfo p := by
  set e := Fintype.equivFin A
  have hm : DMC.jointMeasure (fun i => (PMF.pure (e.symm i)).bind K) (p.map e) =
      (K.jointMeasure p).map fun ω => (e ω.1, ω.2) := by
    rw [DMC.jointMeasure_eq_toMeasure, DMC.jointMeasure_eq_toMeasure,
      PMF.toMeasure_map _ _ (measurable_of_finite _)]
    congr 1
    simp only [DMC.jointPMF, PMF.pure_bind, PMF.map_bind, PMF.bind_map, PMF.map_comp,
      Function.comp_def, Equiv.symm_apply_apply]
  rw [DMC.inputMutualInfo, hm, mutualInfo_map _ (measurable_of_finite _) measurable_fst
    measurable_snd]
  change I[e ∘ Prod.fst : Prod.snd ; K.jointMeasure p] = I[Prod.fst : Prod.snd ; _]
  rw [mutualInfo_comm, mutualInfo_comp_right_of_injective _ e.injective, mutualInfo_comm]

theorem IsLessNoisy.isMoreCapable {W : DMC A (B₁ × B₂)} (hW : IsLessNoisy W) :
    IsMoreCapable W := by
  intro p
  have h := hW _ (p.map (Fintype.equivFin A)) fun i => PMF.pure ((Fintype.equivFin A).symm i)
  rw [← inputMutualInfo_relabel (channel₁ W) p, ← inputMutualInfo_relabel (channel₂ W) p]
  exact h

theorem uvRegion_subset_superpositionUnion {W : DMC A (B₁ × B₂)} (hW : IsMoreCapable W) :
    uvRegion W ⊆ superpositionUnion W := by
  intro R hR
  simp only [uvRegion, Set.mem_iUnion] at hR
  obtain ⟨k₁, k₂, q, pX, h0₁, h0₂, h₁, h₂, h₃, h₄⟩ := hR
  obtain ⟨p₁, pX₁, e₁⟩ := exists_jointMeasure_map W q pX Prod.fst
  obtain ⟨p₂, pX₂, e₂⟩ := exists_jointMeasure_map W q pX Prod.snd
  have := isProbabilityMeasure_jointMeasure' W q pX
  have hI₁ := mutualInfo_cloud_add W p₁ pX₁
  have hC₁ := condMutualInfo_le_of_isMoreCapable hW p₁ pX₁
  simp only [e₁, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _), Function.comp_def] at hI₁ hC₁
  refine mem_superpositionUnion_of_le W p₂ pX₂ h0₁ h0₂ ?_ ?_ ?_
  · simp only [e₂, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _), Function.comp_def]
    exact h₂
  · simp only [e₂, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _), condMutualInfo_map _ (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
      Function.comp_def]
    exact h₄
  · simp only [e₂, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _), Function.comp_def]
    linarith

end Single

section Theorem

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

theorem closure_achievableRegion_eq_of_isMoreCapable {W : DMC A (B₁ × B₂)}
    (hW : IsMoreCapable W) :
    closure (achievableRegion W) = closure (superpositionUnion W) :=
  le_antisymm ((closure_achievableRegion_subset_uvRegion W).trans
      (closure_mono (uvRegion_subset_superpositionUnion hW)))
    (closure_superpositionUnion_subset W)

theorem closure_achievableRegion_eq_of_isLessNoisy {W : DMC A (B₁ × B₂)} (hW : IsLessNoisy W) :
    closure (achievableRegion W) = closure (superpositionUnion W) :=
  closure_achievableRegion_eq_of_isMoreCapable hW.isMoreCapable

end Theorem


end BC

end Meat
