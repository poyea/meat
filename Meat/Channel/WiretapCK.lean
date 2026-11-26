import Meat.Channel.WiretapAchievability
import Meat.Channel.State

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal

namespace Meat

namespace Wiretap

section Decomposition

variable {Ω S T U : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem condEntropy_eq_sum_cond {X : Ω → S} {V : Ω → T} (hX : Measurable X) (hV : Measurable V) :
    H[X | V ; μ] = ∑ v, μ.real (V ⁻¹' {v}) * H[X ; μ[|V ⁻¹' {v}]] := by
  classical
  have hP : ∀ x v, (μ.map fun ω => (X ω, V ω)).real {(x, v)} = μ.real {ω | X ω = x ∧ V ω = v} :=
    fun x v => by
      rw [map_measureReal_apply (hX.prodMk hV) (measurableSet_singleton _)]
      congr 1
      ext ω
      simp
  have hPv : ∀ v, (μ.map V).real {v} = μ.real (V ⁻¹' {v}) := fun v =>
    map_measureReal_apply hV (measurableSet_singleton _)
  have hsum : ∀ v, ∑ x, μ.real {ω | X ω = x ∧ V ω = v} = μ.real (V ⁻¹' {v}) := fun v => by
    have h := Interactive.measureReal_comp_eq_sum μ hX hV (fun _ => ()) () v
    rw [filter_true_of_mem fun _ _ => rfl] at h
    rw [← h]
    congr 1
    ext ω
    simp
  have hcond : ∀ x v, μ.real (V ⁻¹' {v}) ≠ 0 →
      (μ[|V ⁻¹' {v}].map X).real {x} =
        (μ.real (V ⁻¹' {v}))⁻¹ * μ.real {ω | X ω = x ∧ V ω = v} := fun x v _ => by
    rw [map_measureReal_apply hX (measurableSet_singleton _), measureReal_def,
      cond_apply (hV (measurableSet_singleton v)), ENNReal.toReal_mul, ENNReal.toReal_inv,
      ← measureReal_def, ← measureReal_def]
    congr 2
    ext ω
    simp [and_comm]
  rw [condEntropy_def, entropy_def, entropy_def, Fintype.sum_prod_type_right, ← sum_sub_distrib]
  refine sum_congr rfl fun v _ => ?_
  simp only [hP, hPv, entropy_def]
  rcases eq_or_ne (μ.real (V ⁻¹' {v})) 0 with h0 | h0
  · have hz : ∀ x, μ.real {ω | X ω = x ∧ V ω = v} = 0 := fun x =>
      le_antisymm ((measureReal_mono fun ω h => h.2).trans_eq h0) measureReal_nonneg
    simp [hz, h0]
  · simp only [hcond _ v h0]
    have hpos : 0 < μ.real (V ⁻¹' {v}) := lt_of_le_of_ne measureReal_nonneg (Ne.symm h0)
    have hx : ∀ x, μ.real {ω | X ω = x ∧ V ω = v} =
        μ.real (V ⁻¹' {v}) * ((μ.real (V ⁻¹' {v}))⁻¹ * μ.real {ω | X ω = x ∧ V ω = v}) :=
      fun x => by field_simp
    conv_lhs => rw [sum_congr rfl fun x _ => congrArg Real.negMulLog (hx x)]
    simp only [Real.negMulLog_mul, sum_add_distrib, ← sum_mul, ← mul_sum, hsum]
    rw [inv_mul_cancel₀ h0, one_mul]
    ring

theorem condMutualInfo_eq_sum_cond {X : Ω → S} {Y : Ω → U} [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] {V : Ω → T} (hX : Measurable X) (hY : Measurable Y)
    (hV : Measurable V) :
    I[X : Y | V ; μ] = ∑ v, μ.real (V ⁻¹' {v}) * I[X : Y ; μ[|V ⁻¹' {v}]] := by
  rw [condMutualInfo_def, condEntropy_eq_sum_cond μ hX hV, condEntropy_eq_sum_cond μ hY hV,
    condEntropy_eq_sum_cond μ (hX.prodMk hY) hV, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun v _ => ?_
  rw [mutualInfo_def]
  ring

end Decomposition

section Bound

variable {A B E : Type*} [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

private lemma ckRate_le_log_card (W : DMC A (B × E)) {k : ℕ} (q : PMF (Fin k × A)) :
    I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.1 ; ckMeasure W q] -
      I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.2 ; ckMeasure W q] ≤
      Real.log (Fintype.card B) := by
  have hP : IsProbabilityMeasure (ckMeasure W q) := by
    unfold ckMeasure
    infer_instance
  have h1 := mutualInfo_nonneg (ckMeasure W q) (X := fun ω : Fin k × A × (B × E) => ω.1)
    (Y := fun ω => ω.2.2.2) measurable_fst (measurable_of_finite _)
  have h2 := mutualInfo_eq_entropy_sub_condEntropy (μ := ckMeasure W q)
    (fun ω : Fin k × A × (B × E) => ω.2.2.1) (fun ω => ω.1)
  have h3 := condEntropy_nonneg (ckMeasure W q) (X := fun ω : Fin k × A × (B × E) => ω.2.2.1)
    (Y := fun ω => ω.1) (measurable_of_finite _) measurable_fst
  have h4 := entropy_le_log_card (ckMeasure W q) (X := fun ω : Fin k × A × (B × E) => ω.2.2.1)
  have h5 := mutualInfo_comm (ckMeasure W q) (X := fun ω : Fin k × A × (B × E) => ω.1)
    (Y := fun ω => ω.2.2.1)
  linarith

theorem ckRate_le_ckCapacity (W : DMC A (B × E)) {k : ℕ} (q : PMF (Fin k × A)) :
    I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.1 ; ckMeasure W q] -
      I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.2 ; ckMeasure W q] ≤
      ckCapacity W := by
  have hb : ∀ k', ⨆ q' : PMF (Fin k' × A),
      (I[fun ω : Fin k' × A × (B × E) => ω.1 : fun ω => ω.2.2.1 ; ckMeasure W q'] -
        I[fun ω : Fin k' × A × (B × E) => ω.1 : fun ω => ω.2.2.2 ; ckMeasure W q']) ≤
      Real.log (Fintype.card B) := fun k' =>
    Real.iSup_le (fun q' => ckRate_le_log_card W q') (Real.log_natCast_nonneg _)
  exact le_ciSup_of_le ⟨_, Set.forall_mem_range.2 hb⟩ k
    (le_ciSup ⟨_, Set.forall_mem_range.2 fun q' => ckRate_le_log_card W q'⟩ q)

theorem le_ckCapacity_of_kernel {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (W : DMC A (B × E)) {k : ℕ} {V : Ω → Fin k} {X : Ω → A}
    {S : Ω → B × E} (hV : Measurable V) (hX : Measurable X) (hS : Measurable S)
    (hK : ∀ v x s, ν.real {ω | V ω = v ∧ X ω = x ∧ S ω = s} =
      ν.real {ω | V ω = v ∧ X ω = x} * (W x s).toReal) :
    I[V : fun ω => (S ω).1 ; ν] - I[V : fun ω => (S ω).2 ; ν] ≤ ckCapacity W := by
  classical
  have := Fintype.ofFinite A
  have hs : ∑ vx : Fin k × A, ENNReal.ofReal (ν.real {ω | V ω = vx.1 ∧ X ω = vx.2}) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => measureReal_nonneg]
    have h := Interactive.measureReal_comp_eq_sum ν (hV.prodMk hX)
      (measurable_const (a := ())) (fun _ => ()) () ()
    rw [filter_true_of_mem fun _ _ => rfl] at h
    have h' : ν.real {ω | () = () ∧ () = ()} = 1 := by simp
    rw [h'] at h
    rw [show ∑ vx : Fin k × A, ν.real {ω | V ω = vx.1 ∧ X ω = vx.2} = 1 by
      rw [h]; refine sum_congr rfl fun vx _ => ?_; congr 1; ext ω; simp [Prod.ext_iff]]
    simp
  set q : PMF (Fin k × A) := PMF.ofFintype _ hs
  have hmap : ν.map (fun ω => (V ω, X ω, S ω)) = ckMeasure W q := by
    refine Measure.ext_of_singleton fun t => ?_
    have hE : (DMC.jointPMF (fun va : Fin k × A => W va.2) q).map
        (fun p => (p.1.1, p.1.2, p.2)) =
        q.bind fun va => (W va.2).map fun y => (va.1, va.2, y) := by
      simp only [DMC.jointPMF, PMF.map_bind, PMF.map_comp]
      rfl
    rw [ckMeasure, ← hE, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      show t = (fun p : (Fin k × A) × (B × E) => (p.1.1, p.1.2, p.2)) ((t.1, t.2.1), t.2.2)
        from rfl,
      PMF.map_apply_of_injective _ (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2),
      DMC.jointPMF_apply, Measure.map_apply ((hV.prodMk (hX.prodMk hS)))
        (measurableSet_singleton _)]
    simp only [q, PMF.ofFintype_apply]
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν _), ← measureReal_def,
      ← ENNReal.ofReal_toReal (PMF.apply_ne_top (W t.2.1) t.2.2),
      ← ENNReal.ofReal_mul measureReal_nonneg, ← hK]
    congr 2
    ext ω
    simp [Prod.ext_iff]
  have hY : I[V : fun ω => (S ω).1 ; ν] =
      I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.1 ; ckMeasure W q] := by
    rw [← hmap, mutualInfo_map _ (hV.prodMk (hX.prodMk hS)) measurable_fst
      (measurable_of_finite _)]
    rfl
  have hZ : I[V : fun ω => (S ω).2 ; ν] =
      I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.2 ; ckMeasure W q] := by
    rw [← hmap, mutualInfo_map _ (hV.prodMk (hX.prodMk hS)) measurable_fst
      (measurable_of_finite _)]
    rfl
  rw [hY, hZ]
  exact ckRate_le_ckCapacity W q

end Bound

section CondBound

variable {A B E : Type*} [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]
  {Ω T : Type*} [MeasurableSpace Ω] [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

omit [Fintype T] in
theorem kernel_comp [Finite T] (μ : Measure Ω) [IsProbabilityMeasure μ] {T' S' : Type*}
    [MeasurableSpace S'] [MeasurableSingletonClass S'] {H : Ω → T} {Sv : Ω → S'}
    (hH : Measurable H) (hS : Measurable Sv) (F : T → T') (K : T' → PMF S')
    (hK : ∀ h s, μ.real {ω | H ω = h ∧ Sv ω = s} = μ.real {ω | H ω = h} * (K (F h) s).toReal)
    (t : T') (s : S') :
    μ.real {ω | F (H ω) = t ∧ Sv ω = s} = μ.real {ω | F (H ω) = t} * (K t s).toReal := by
  classical
  have := Fintype.ofFinite T
  rw [Interactive.measureReal_comp_eq_sum μ hH hS F t s]
  have h2 := Interactive.measureReal_comp_eq_sum μ hH (measurable_const (a := ())) F t ()
  have e1 : {ω | F (H ω) = t ∧ () = ()} = {ω | F (H ω) = t} := by ext; simp
  rw [e1] at h2
  simp only [and_true] at h2
  rw [h2, sum_mul]
  refine sum_congr rfl fun h hh => ?_
  rw [hK, (mem_filter.1 hh).2]

theorem condMutualInfo_le_ckCapacity (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : DMC A (B × E)) {k : ℕ} {G : Ω → T} {V : Ω → Fin k} {X : Ω → A} {S : Ω → B × E}
    (hG : Measurable G) (hV : Measurable V) (hX : Measurable X) (hS : Measurable S)
    (hK : ∀ g v x s, μ.real {ω | (G ω, V ω, X ω) = (g, v, x) ∧ S ω = s} =
      μ.real {ω | (G ω, V ω, X ω) = (g, v, x)} * (W x s).toReal) :
    I[V : fun ω => (S ω).1 | G ; μ] - I[V : fun ω => (S ω).2 | G ; μ] ≤ ckCapacity W := by
  classical
  rw [condMutualInfo_eq_sum_cond μ hV (Y := fun ω => (S ω).1) (measurable_fst.comp hS) hG,
    condMutualInfo_eq_sum_cond μ hV (Y := fun ω => (S ω).2) (measurable_snd.comp hS) hG,
    ← sum_sub_distrib]
  have h1 : ∑ g, μ.real (G ⁻¹' {g}) = 1 := by
    have h := Interactive.measureReal_comp_eq_sum μ hG (measurable_const (a := ()))
      (fun _ => ()) () ()
    rw [filter_true_of_mem fun _ _ => rfl] at h
    have h' : μ.real {ω | () = () ∧ () = ()} = 1 := by simp
    rw [h'] at h
    rw [h]
    refine sum_congr rfl fun g _ => ?_
    congr 1
    ext ω
    simp
  calc _ ≤ ∑ g, μ.real (G ⁻¹' {g}) * ckCapacity W := by
        refine sum_le_sum fun g _ => ?_
        rw [← mul_sub]
        rcases eq_or_ne (μ.real (G ⁻¹' {g})) 0 with h0 | h0
        · simp [h0]
        refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
        have hne : μ (G ⁻¹' {g}) ≠ 0 := fun h => h0 (by rw [measureReal_def, h]; rfl)
        have := cond_isProbabilityMeasure (μ := μ) hne
        refine le_ckCapacity_of_kernel (μ[|G ⁻¹' {g}]) W hV hX hS fun v x s => ?_
        rw [measureReal_def, measureReal_def, cond_apply (hG (measurableSet_singleton g)),
          cond_apply (hG (measurableSet_singleton g)), ENNReal.toReal_mul, ENNReal.toReal_mul,
          ← measureReal_def, ← measureReal_def]
        have e1 : G ⁻¹' {g} ∩ {ω | V ω = v ∧ X ω = x ∧ S ω = s} =
            {ω | (G ω, V ω, X ω) = (g, v, x) ∧ S ω = s} := by
          ext ω
          simp [Prod.ext_iff, and_assoc]
        have e2 : G ⁻¹' {g} ∩ {ω | V ω = v ∧ X ω = x} = {ω | (G ω, V ω, X ω) = (g, v, x)} := by
          ext ω
          simp [Prod.ext_iff]
        rw [e1, e2, hK]
        ring
    _ = ckCapacity W := by rw [← sum_mul, h1, one_mul]

end CondBound

section Csiszar

variable {Ω T B E : Type*} [MeasurableSpace Ω] [Fintype T] [MeasurableSpace T]
  [MeasurableSingletonClass T] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E] (μ : Measure Ω) {n : ℕ}

private lemma ck_cmi_pair {P Q R S : Type*} [Fintype P] [MeasurableSpace P]
    [MeasurableSingletonClass P] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {X : Ω → P} {Y : Ω → Q} {Z : Ω → R} {V : Ω → S} :
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

private lemma ck_cmi_cond_inj {P Q R S : Type*} [Fintype P] [MeasurableSpace P]
    [MeasurableSingletonClass P] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {X : Ω → P} {Y : Ω → Q} {Z : Ω → R} {Z' : Ω → S} {e : R → S}
    (he : Function.Injective e) (hZ : ∀ ω, Z' ω = e (Z ω)) :
    I[X : Y | Z' ; μ] = I[X : Y | Z ; μ] := by
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy, condMutualInfo_eq_condEntropy_sub_condEntropy,
    condEntropy_cond_of_injective μ he hZ]
  congr 1
  exact condEntropy_cond_of_injective μ (Z := fun ω => (X ω, Z ω))
    (e := fun p => (p.1, e p.2)) (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (he h.2)) fun ω => by rw [hZ]

private lemma ck_cmi_right_swap {P Q R S : Type*} [Fintype P] [MeasurableSpace P]
    [MeasurableSingletonClass P] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {X : Ω → P} {Y : Ω → Q} {V : Ω → S} {Z : Ω → R} :
    I[X : fun ω => (Y ω, V ω) | Z ; μ] = I[X : fun ω => (V ω, Y ω) | Z ; μ] := by
  rw [condMutualInfo_comm, condMutualInfo_comm (X := X),
    condMutualInfo_eq_condEntropy_sub_condEntropy, condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  exact condEntropy_cond_of_injective μ (Z := fun ω => ((V ω, Y ω), Z ω))
    (e := fun p => (p.1.swap, p.2)) (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Prod.swap_injective h.1) h.2) fun ω => rfl

theorem mutualInfo_eq_sum_Iio [IsProbabilityMeasure μ] (Mv : Ω → T) (Y : Ω → Fin n → B) :
    I[Mv : Y ; μ] = ∑ i, I[Mv : fun ω => Y ω i | fun ω => seqRestrict (Y ω) (Iio i) ; μ] := by
  rw [mutualInfo_comm, mutualInfo_eq_sum μ Y Mv]
  refine sum_congr rfl fun i _ => ?_
  rw [condMutualInfo_comm]
  refine ck_cmi_cond_inj μ (Z := fun ω => seqRestrict (Y ω) (Iio i))
    (e := fun r j => r ⟨⟨j, j.2.trans i.2⟩, by simp [Fin.lt_def]⟩) (fun a b h => ?_)
    fun ω => rfl
  funext t
  have ht : (t : Fin n) < i := mem_Iio.1 t.2
  have := congrFun h ⟨t.1.1, ht⟩
  simpa using this

theorem mutualInfo_eq_sum_Ioi [IsProbabilityMeasure μ] (Mv : Ω → T) (Z : Ω → Fin n → E) :
    I[Mv : Z ; μ] = ∑ i, I[Mv : fun ω => Z ω i | fun ω => seqRestrict (Z ω) (Ioi i) ; μ] := by
  have h1 : I[Mv : fun ω j => Z ω (Fin.rev j) ; μ] = I[Mv : Z ; μ] :=
    mutualInfo_comp_right_of_injective μ (X := Mv) (Y := Z) (f := fun z j => z (Fin.rev j))
      fun a b h => funext fun j => by simpa using congrFun h (Fin.rev j)
  rw [← h1, mutualInfo_eq_sum_Iio μ Mv (fun ω j => Z ω (Fin.rev j)),
    ← Equiv.sum_comp Fin.revPerm]
  refine sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  refine ck_cmi_cond_inj μ (Z := fun ω => seqRestrict (Z ω) (Ioi i))
    (e := fun r t => r ⟨Fin.rev t.1, mem_Ioi.2 (Fin.lt_rev_iff.2 (mem_Iio.1 t.2))⟩)
    (fun a b h => ?_) fun ω => rfl
  funext s
  have hs : Fin.rev s.1 < Fin.rev i := by
    rw [Fin.rev_lt_iff, Fin.rev_rev]
    exact mem_Ioi.1 s.2
  have := congrFun h ⟨Fin.rev s.1, mem_Iio.2 hs⟩
  simpa using this

theorem mutualInfo_sub_eq_sum [IsProbabilityMeasure μ] (Mv : Ω → T) (Y : Ω → Fin n → B)
    (Z : Ω → Fin n → E) :
    I[Mv : Y ; μ] - I[Mv : Z ; μ] = ∑ i,
      (I[Mv : fun ω => Y ω i | fun ω => (seqRestrict (Y ω) (Iio i), seqRestrict (Z ω) (Ioi i)) ;
          μ] -
        I[Mv : fun ω => Z ω i |
          fun ω => (seqRestrict (Y ω) (Iio i), seqRestrict (Z ω) (Ioi i)) ; μ]) := by
  have key : ∀ i : Fin n,
      I[Mv : fun ω => Y ω i | fun ω => seqRestrict (Y ω) (Iio i) ; μ] -
        I[Mv : fun ω => Z ω i | fun ω => seqRestrict (Z ω) (Ioi i) ; μ] =
      (I[Mv : fun ω => Y ω i |
          fun ω => (seqRestrict (Y ω) (Iio i), seqRestrict (Z ω) (Ioi i)) ; μ] -
        I[Mv : fun ω => Z ω i |
          fun ω => (seqRestrict (Y ω) (Iio i), seqRestrict (Z ω) (Ioi i)) ; μ]) +
      (I[fun ω => seqRestrict (Z ω) (Ioi i) : fun ω => Y ω i |
          fun ω => ((), seqRestrict (Y ω) (Iio i)) ; μ] -
        I[fun ω => seqRestrict (Y ω) (Iio i) : fun ω => Z ω i |
          fun ω => ((), seqRestrict (Z ω) (Ioi i)) ; μ]) -
      (I[fun ω => seqRestrict (Z ω) (Ioi i) : fun ω => Y ω i |
          fun ω => (Mv ω, seqRestrict (Y ω) (Iio i)) ; μ] -
        I[fun ω => seqRestrict (Y ω) (Iio i) : fun ω => Z ω i |
          fun ω => (Mv ω, seqRestrict (Z ω) (Ioi i)) ; μ]) := by
    intro i
    set Yi : Ω → B := fun ω => Y ω i
    set Zi : Ω → E := fun ω => Z ω i
    set D : Ω → (↥(Iio i) → B) := fun ω => seqRestrict (Y ω) (Iio i)
    set Ad : Ω → (↥(Ioi i) → E) := fun ω => seqRestrict (Z ω) (Ioi i)
    have f1 := ck_cmi_pair μ (X := Yi) (Y := Mv) (Z := D) (V := Ad)
    have f2 := ck_cmi_pair μ (X := Yi) (Y := Ad) (Z := D) (V := Mv)
    have f3 := ck_cmi_right_swap μ (X := Yi) (Y := Mv) (V := Ad) (Z := D)
    have g1 := ck_cmi_pair μ (X := Zi) (Y := Mv) (Z := Ad) (V := D)
    have g2 := ck_cmi_pair μ (X := Zi) (Y := D) (Z := Ad) (V := Mv)
    have g3 := ck_cmi_right_swap μ (X := Zi) (Y := Mv) (V := D) (Z := Ad)
    have c1 := condMutualInfo_comm μ (X := Mv) (Y := Yi) (Z := D)
    have c2 : I[Yi : Ad | D ; μ] = I[Ad : Yi | fun ω => ((), D ω) ; μ] := by
      rw [condMutualInfo_comm]
      exact (ck_cmi_cond_inj μ (e := fun d => ((), d)) (fun a b h => congrArg Prod.snd h)
        fun ω => rfl).symm
    have c3 := condMutualInfo_comm μ (X := Yi) (Y := Ad) (Z := fun ω => (Mv ω, D ω))
    have c4 : I[Yi : Mv | fun ω => (Ad ω, D ω) ; μ] = I[Mv : Yi | fun ω => (D ω, Ad ω) ; μ] := by
      rw [condMutualInfo_comm]
      exact ck_cmi_cond_inj μ (e := Prod.swap) Prod.swap_injective fun ω => rfl
    have d1 := condMutualInfo_comm μ (X := Mv) (Y := Zi) (Z := Ad)
    have d2 : I[Zi : D | Ad ; μ] = I[D : Zi | fun ω => ((), Ad ω) ; μ] := by
      rw [condMutualInfo_comm]
      exact (ck_cmi_cond_inj μ (e := fun d => ((), d)) (fun a b h => congrArg Prod.snd h)
        fun ω => rfl).symm
    have d3 := condMutualInfo_comm μ (X := Zi) (Y := D) (Z := fun ω => (Mv ω, Ad ω))
    have d4 := condMutualInfo_comm μ (X := Zi) (Y := Mv) (Z := fun ω => (D ω, Ad ω))
    linarith
  rw [mutualInfo_eq_sum_Iio μ Mv Y, mutualInfo_eq_sum_Ioi μ Mv Z, ← sum_sub_distrib,
    sum_congr rfl fun i _ => key i]
  simp only [sum_sub_distrib, sum_add_distrib]
  rw [csiszar_sum μ Y Z (fun _ => ()), csiszar_sum μ Y Z Mv]
  ring

end Csiszar

section Converse

variable {A B E : Type*} [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

omit [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E] in
open Classical in
private lemma sum_ite_off {S : Type*} [Fintype S] {n : ℕ} (f : Fin n → S → ℝ≥0∞) (i : Fin n)
    (o : ↥(({i}ᶜ : Finset (Fin n))) → S) (s : S) :
    ∑ y : Fin n → S, (if seqRestrict y {i}ᶜ = o ∧ y i = s then ∏ j, f j (y j) else 0) =
      (∏ j : ↥(({i}ᶜ : Finset (Fin n))), f j (o j)) * f i s := by
  classical
  set y₀ : Fin n → S := fun j => if h : j = i then s else o ⟨j, by simp [h]⟩
  have hy₀ : seqRestrict y₀ {i}ᶜ = o ∧ y₀ i = s := by
    refine ⟨funext fun t => ?_, by simp [y₀]⟩
    have ht : (t : Fin n) ≠ i :=
      fun h => (Finset.mem_compl.1 t.2) (Finset.mem_singleton.2 h)
    simp [seqRestrict, y₀, ht]
  rw [sum_eq_single y₀ (fun y _ hy => ?_) (by simp)]
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hy₀), ← prod_mul_prod_compl {i}, prod_singleton,
      mul_comm, ← prod_coe_sort]
    congr 1
    · refine prod_congr rfl fun t _ => ?_
      have ht : (t : Fin n) ≠ i :=
        fun h => (Finset.mem_compl.1 t.2) (Finset.mem_singleton.2 h)
      simp [y₀, ht]
    · simp [y₀]
  · refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
    rintro ⟨h1, h2⟩
    apply hy
    funext j
    by_cases hj : j = i
    · subst hj
      simp [y₀, h2]
    · have := congrFun h1 ⟨j, by simp [hj]⟩
      simp only [seqRestrict] at this
      simp [y₀, hj, this]

variable {k l n : ℕ} [NeZero k] [NeZero l]

omit [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma bookMeasure_off (W : DMC A (B × E)) (C : Fin k × Fin l → Fin n → A) (i : Fin n)
    (u : Fin k × Fin l) (o : ↥(({i}ᶜ : Finset (Fin n))) → B × E) (s : B × E) :
    (bookMeasure W C).real {ω | (ω.1, seqRestrict ω.2 {i}ᶜ) = (u, o) ∧ ω.2 i = s} =
      (bookMeasure W C).real {ω | (ω.1, seqRestrict ω.2 {i}ᶜ) = (u, o)} *
        (W (C u i) s).toReal := by
  classical
  have hseq : ∀ y : Fin n → B × E, Interactive.seqProb W
      (fun (j : Fin n) (_ : Fin j → B × E) => C u j) y = ∏ j, W (C u j) (y j) := fun y => rfl
  have hs : ∑ s', W (C u i) s' = 1 := by
    have h := PMF.tsum_coe (W (C u i))
    rwa [tsum_fintype] at h
  have h1 : (bookMeasure W C) {ω | (ω.1, seqRestrict ω.2 {i}ᶜ) = (u, o) ∧ ω.2 i = s} =
      (Fintype.card (Fin k × Fin l) : ℝ≥0∞)⁻¹ *
        ((∏ j : ↥(({i}ᶜ : Finset (Fin n))), W (C u j) (o j)) * W (C u i) s) := by
    rw [bookMeasure, Interactive.codeMeasure_apply,
      sum_eq_single u (fun u' _ hu => by simp [Prod.ext_iff, hu]) (by simp)]
    rw [← sum_ite_off (fun j => W (C u j)) i o s, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    by_cases h : seqRestrict y {i}ᶜ = o ∧ y i = s
    · have h' : (u, seqRestrict y {i}ᶜ) = (u, o) ∧ y i = s := ⟨by rw [h.1], h.2⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true h),
        hseq]
    · have h' : ¬((u, seqRestrict y {i}ᶜ) = (u, o) ∧ y i = s) := fun h'' =>
        h ⟨(Prod.ext_iff.1 h''.1).2, h''.2⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false h),
        mul_zero]
  have h2 : (bookMeasure W C) {ω | (ω.1, seqRestrict ω.2 {i}ᶜ) = (u, o)} =
      (Fintype.card (Fin k × Fin l) : ℝ≥0∞)⁻¹ *
        ∏ j : ↥(({i}ᶜ : Finset (Fin n))), W (C u j) (o j) := by
    rw [bookMeasure, Interactive.codeMeasure_apply,
      sum_eq_single u (fun u' _ hu => by simp [Prod.ext_iff, hu]) (by simp)]
    have e : ∀ y : Fin n → B × E, (if (u, seqRestrict y {i}ᶜ) = (u, o) then
        (Fintype.card (Fin k × Fin l) : ℝ≥0∞)⁻¹ * Interactive.seqProb W
          (fun (j : Fin n) (_ : Fin j → B × E) => C u j) y else 0) =
        (Fintype.card (Fin k × Fin l) : ℝ≥0∞)⁻¹ * ∑ s', (if seqRestrict y {i}ᶜ = o ∧ y i = s'
          then ∏ j, W (C u j) (y j) else 0) := by
      intro y
      rw [sum_eq_single (y i) (fun s' _ hs' => by simp [Ne.symm hs']) (by simp)]
      by_cases h : seqRestrict y {i}ᶜ = o
      · have h' : (u, seqRestrict y {i}ᶜ) = (u, o) := by rw [h]
        rw [ite_eq_left_of_eq_true _ _ (eq_true h'),
          ite_eq_left_of_eq_true _ _ (eq_true ⟨h, rfl⟩), hseq]
      · have h' : ¬((u, seqRestrict y {i}ᶜ) = (u, o)) := fun h'' => h (Prod.ext_iff.1 h'').2
        rw [ite_eq_right_of_eq_false _ _ (eq_false h'),
          ite_eq_right_of_eq_false _ _ (eq_false fun h'' => h h''.1), mul_zero]
    rw [sum_congr rfl fun y _ => e y, ← mul_sum, sum_comm]
    congr 1
    rw [sum_congr rfl fun s' _ => by convert sum_ite_off (fun j => W (C u j)) i o s', ← mul_sum,
      hs, mul_one]
  rw [measureReal_def, measureReal_def, h1, h2, ← mul_assoc, ENNReal.toReal_mul]

theorem ck_letter_le (W : DMC A (B × E)) (C : Fin k × Fin l → Fin n → A) (i : Fin n) :
    I[fun ω : (Fin k × Fin l) × (Fin n → B × E) => ω.1.1 : fun ω => (ω.2 i).1 |
        fun ω => (seqRestrict (fun j => (ω.2 j).1) (Iio i),
          seqRestrict (fun j => (ω.2 j).2) (Ioi i)) ; bookMeasure W C] -
      I[fun ω : (Fin k × Fin l) × (Fin n → B × E) => ω.1.1 : fun ω => (ω.2 i).2 |
        fun ω => (seqRestrict (fun j => (ω.2 j).1) (Iio i),
          seqRestrict (fun j => (ω.2 j).2) (Ioi i)) ; bookMeasure W C] ≤ ckCapacity W := by
  classical
  set Gf : (↥(({i}ᶜ : Finset (Fin n))) → B × E) → (↥(Iio i) → B) × (↥(Ioi i) → E) :=
    fun o => (fun j => (o ⟨j.1, by simpa using ne_of_lt (mem_Iio.1 j.2)⟩).1,
      fun j => (o ⟨j.1, by simpa using ne_of_gt (mem_Ioi.1 j.2)⟩).2)
  set F : (Fin k × Fin l) × (↥(({i}ᶜ : Finset (Fin n))) → B × E) →
      ((↥(Iio i) → B) × (↥(Ioi i) → E)) × Fin k × A := fun h => (Gf h.2, h.1.1, C h.1 i)
  have hK := kernel_comp (bookMeasure W C)
    (H := fun ω : (Fin k × Fin l) × (Fin n → B × E) => (ω.1, seqRestrict ω.2 {i}ᶜ))
    (Sv := fun ω => ω.2 i) (measurable_of_finite _) (measurable_of_finite _) F
    (fun t => W t.2.2) fun h s => bookMeasure_off W C i h.1 h.2 s
  exact condMutualInfo_le_ckCapacity (bookMeasure W C) W (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite (fun ω : (Fin k × Fin l) × (Fin n → B × E) =>
      C ω.1 i)) (measurable_of_finite _) fun g v x s => hK (g, v, x) s

theorem one_sub_mul_log_card_le_ck (c : WiretapCode (Fin k) (Fin l) A B n)
    (W : DMC A (B × E)) :
    (1 - (c.avgError W).toReal) * Real.log k ≤ c.leakage W + n * ckCapacity W + Real.log 2 := by
  have hμ : Interactive.codeMeasure W (c.toFn (E := E)) = bookMeasure W c.enc := rfl
  have hH : H[fun ω : (Fin k × Fin l) × (Fin n → B × E) => ω.1.1 ; bookMeasure W c.enc] =
      Real.log k := by
    have := c.entropy_message W
    rwa [hμ, Fintype.card_fin] at this
  have hI := mutualInfo_eq_entropy_sub_condEntropy (μ := bookMeasure W c.enc)
    (fun ω : (Fin k × Fin l) × (Fin n → B × E) => ω.1.1) (fun ω i => (ω.2 i).1)
  have hF := condEntropy_le_log_two_add_mul_log_card (μ := bookMeasure W c.enc)
    (X := fun ω : (Fin k × Fin l) × (Fin n → B × E) => ω.1.1) (Y := fun ω i => (ω.2 i).1)
    (measurable_of_finite _) (measurable_of_finite _) c.dec
  have hE : (bookMeasure W c.enc).real {ω : (Fin k × Fin l) × (Fin n → B × E) |
      c.dec ((fun ω i => (ω.2 i).1) ω) ≠ ω.1.1} = (c.avgError W).toReal := by
    have := c.measureReal_dec_ne W
    rwa [hμ] at this
  rw [hE, Fintype.card_fin] at hF
  have hD := mutualInfo_sub_eq_sum (bookMeasure W c.enc)
    (fun ω : (Fin k × Fin l) × (Fin n → B × E) => ω.1.1) (fun ω i => (ω.2 i).1)
    (fun ω i => (ω.2 i).2)
  have hS := sum_le_sum fun i (_ : i ∈ univ) => ck_letter_le W c.enc i
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hS
  have hleak : c.leakage W = I[fun ω : (Fin k × Fin l) × (Fin n → B × E) => ω.1.1 :
      fun ω i => (ω.2 i).2 ; bookMeasure W c.enc] := rfl
  have hexp : (1 - (c.avgError W).toReal) * Real.log k =
      Real.log k - (c.avgError W).toReal * Real.log k := by ring
  linarith

end Converse

section Main

variable {A B E : Type*} [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

theorem ckCapacity_nonneg (W : DMC A (B × E)) : 0 ≤ ckCapacity W := by
  have hb : ∀ k', ⨆ q' : PMF (Fin k' × A),
      (I[fun ω : Fin k' × A × (B × E) => ω.1 : fun ω => ω.2.2.1 ; ckMeasure W q'] -
        I[fun ω : Fin k' × A × (B × E) => ω.1 : fun ω => ω.2.2.2 ; ckMeasure W q']) ≤
      Real.log (Fintype.card B) := fun k' =>
    Real.iSup_le (fun q' => ckRate_le_log_card W q') (Real.log_natCast_nonneg _)
  have h0 : IsEmpty (PMF (Fin 0 × A)) := ⟨fun q => q.support_nonempty.some.1.elim0⟩
  refine le_ciSup_of_le ⟨_, Set.forall_mem_range.2 hb⟩ 0 ?_
  rw [Real.iSup_of_isEmpty]

theorem le_ckCapacity_of_achievable (W : DMC A (B × E)) {R : ℝ} (h : Achievable W R) :
    R ≤ ckCapacity W := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  set C := ckCapacity W
  have hC : 0 ≤ C := ckCapacity_nonneg W
  set δ := R - C with hδ
  have hδ0 : 0 < δ := by linarith
  set e := δ / (2 * (R + 1)) with he
  have he0 : 0 < e := div_pos hδ0 (by linarith)
  have hR1 : R + 1 ≠ 0 := by linarith
  have he1 : e * (R + 1) = δ / 2 := by
    rw [he]
    field_simp
  have he2 : 0 < 1 - e := by
    have : e * (R + 1) < R + 1 := by rw [he1]; linarith
    nlinarith
  obtain ⟨N, hN⟩ := h e he0
  obtain ⟨n0, hn0⟩ := exists_nat_gt (2 * Real.log 2 / δ)
  obtain ⟨n, hNn, hn0n⟩ : ∃ n : ℕ, N ≤ n ∧ n0 ≤ n := ⟨max N n0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨k, l, _, _, hk, c, hc, hleak⟩ := hN n hNn
  have hn : 2 * Real.log 2 < n * δ := by
    rw [← div_lt_iff₀ hδ0]
    exact hn0.trans_le (by exact_mod_cast hn0n)
  have hk0 : (0 : ℝ) < k := (Real.exp_pos _).trans_le hk
  have key := one_sub_mul_log_card_le_ck c W
  have hPe : (c.avgError W).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1a : (1 - e) * Real.log k ≤ (1 - (c.avgError W).toReal) * Real.log k :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)
  have h1 : (1 - e) * Real.log k ≤ n * e + n * C + Real.log 2 := by linarith
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) - n * e = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

end Main

end Wiretap

end Meat
