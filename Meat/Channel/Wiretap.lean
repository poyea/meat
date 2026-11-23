import Meat.Channel.CodingTheorem
import Meat.Open.Interactive

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

structure WiretapCode (M L A B : Type*) (n : ℕ) where
  enc : M × L → Fin n → A
  dec : (Fin n → B) → M

namespace WiretapCode

variable {M L A B E : Type*} {n : ℕ}

noncomputable def errorProb [Fintype B] [Fintype E] [DecidableEq M] (c : WiretapCode M L A B n)
    (W : DMC A (B × E)) (m : M × L) : ℝ≥0∞ :=
  ∑ y : Fin n → B × E, if c.dec (fun i => (y i).1) = m.1 then 0
    else DMC.blockProb W (c.enc m) y

noncomputable def avgError [Fintype B] [Fintype E] [Fintype M] [Fintype L] [DecidableEq M]
    (c : WiretapCode M L A B n) (W : DMC A (B × E)) : ℝ≥0∞ :=
  (∑ m : M × L, c.errorProb W m) / ((Fintype.card M : ℝ≥0∞) * (Fintype.card L : ℝ≥0∞))

def toFn (c : WiretapCode M L A B n) : M × L → (i : Fin n) → (Fin i → B × E) → A :=
  fun m i _ => c.enc m i

noncomputable def leakage [Fintype M] [Nonempty M] [MeasurableSpace M] [Fintype L] [Nonempty L]
    [MeasurableSpace L] [Fintype B] [MeasurableSpace B] [Fintype E] [MeasurableSpace E]
    (c : WiretapCode M L A B n) (W : DMC A (B × E)) : ℝ :=
  I[fun ω : (M × L) × (Fin n → B × E) => ω.1.1 : fun ω i => (ω.2 i).2 ;
    Interactive.codeMeasure W (c.toFn (E := E))]

end WiretapCode

namespace Wiretap

variable {A B E : Type*}

def Achievable [Fintype B] [MeasurableSpace B] [Fintype E] [MeasurableSpace E]
    (W : DMC A (B × E)) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ (k l : ℕ) (_ : NeZero k) (_ : NeZero l), Real.exp (n * R) ≤ k ∧
      ∃ c : WiretapCode (Fin k) (Fin l) A B n,
        c.avgError W ≤ ENNReal.ofReal ε ∧ c.leakage W ≤ n * ε

noncomputable def degraded (W₁ : DMC A B) (D : DMC B E) : DMC A (B × E) :=
  fun a => DMC.jointPMF D (W₁ a)

variable [Fintype A] [MeasurableSpace A] [Fintype B] [MeasurableSpace B]
  [Fintype E] [MeasurableSpace E]

noncomputable def secrecyRate (W : DMC A (B × E)) (p : PMF A) : ℝ :=
  I[fun ω : A × (B × E) => ω.1 : fun ω => ω.2.1 ; W.jointMeasure p] -
    I[fun ω : A × (B × E) => ω.1 : fun ω => ω.2.2 ; W.jointMeasure p]

noncomputable def secrecyCapacity (W : DMC A (B × E)) : ℝ :=
  ⨆ p : PMF A, secrecyRate W p

noncomputable def ckMeasure {V : Type*} [MeasurableSpace V] (W : DMC A (B × E))
    (q : PMF (V × A)) : Measure (V × A × (B × E)) :=
  (q.bind fun va => (W va.2).map fun y => (va.1, va.2, y)).toMeasure

noncomputable def ckCapacity (W : DMC A (B × E)) : ℝ :=
  ⨆ (k : ℕ) (q : PMF (Fin k × A)),
    I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.1 ; ckMeasure W q] -
      I[fun ω : Fin k × A × (B × E) => ω.1 : fun ω => ω.2.2.2 ; ckMeasure W q]

end Wiretap
namespace WiretapCode

variable {M L A B E : Type*} {n : ℕ} [Fintype M] [Nonempty M] [MeasurableSpace M]
  [MeasurableSingletonClass M] [DecidableEq M] [Fintype L] [Nonempty L] [MeasurableSpace L]
  [MeasurableSingletonClass L] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

theorem measureReal_dec_ne (c : WiretapCode M L A B n) (W : DMC A (B × E)) :
    (Interactive.codeMeasure W (c.toFn (E := E))).real
      {ω | c.dec (fun i => (ω.2 i).1) ≠ ω.1.1} = (c.avgError W).toReal := by
  classical
  rw [measureReal_def, Interactive.codeMeasure_apply, avgError, Fintype.card_prod, Nat.cast_mul,
    div_eq_mul_inv, sum_mul]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [errorProb, sum_mul]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : c.dec (fun i => (y i).1) = m.1
  · simp [h]
  · simp only [h, ne_eq, not_false_eq_true, ite_true, ite_false]
    rw [mul_comm]
    rfl

omit [DecidableEq M] in
theorem entropy_message (c : WiretapCode M L A B n) (W : DMC A (B × E)) :
    H[fun ω : (M × L) × (Fin n → B × E) => ω.1.1 ;
      Interactive.codeMeasure W (c.toFn (E := E))] = Real.log (Fintype.card M) := by
  classical
  refine entropy_eq_log_card _ fun m => ?_
  rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton m),
    measureReal_def]
  have e : (fun ω : (M × L) × (Fin n → B × E) => ω.1.1) ⁻¹' {m} =
      {ω : (M × L) × (Fin n → B × E) | ω.1.1 = m} := rfl
  rw [e, Interactive.codeMeasure_apply, Fintype.sum_prod_type,
    sum_eq_single m (fun m' _ hm => by simp [hm]) (by simp)]
  simp only [ite_true, ← mul_sum, Interactive.sum_seqProb, mul_one, sum_const, card_univ,
    nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
  have hM : (Fintype.card M : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hL : (Fintype.card L : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  rw [ENNReal.mul_inv (Or.inl hM) (Or.inl (ENNReal.natCast_ne_top _)), mul_comm,
    mul_assoc, ENNReal.inv_mul_cancel hL (ENNReal.natCast_ne_top _), mul_one,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem one_sub_mul_log_card_le [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (c : WiretapCode M L A B n) (W : DMC A (B × E)) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M) ≤ c.leakage W +
      ∑ i, I[fun ω : A × (B × E) => ω.1 : fun ω => ω.2.1 | fun ω => ω.2.2 ;
        W.jointMeasure (Interactive.inputLaw W (c.toFn (E := E)) i)] + Real.log 2 := by
  classical
  set μ := Interactive.codeMeasure W (c.toFn (E := E))
  set Mm : (M × L) × (Fin n → B × E) → M := fun ω => ω.1.1
  set U : (M × L) × (Fin n → B × E) → M × L := fun ω => ω.1
  set Y : (M × L) × (Fin n → B × E) → Fin n → B := fun ω i => (ω.2 i).1
  set Z : (M × L) × (Fin n → B × E) → Fin n → E := fun ω i => (ω.2 i).2
  have hH := c.entropy_message W
  have hI := mutualInfo_eq_entropy_sub_condEntropy (μ := μ) Mm Y
  have hF := condEntropy_le_log_two_add_mul_log_card (μ := μ) (X := Mm) (Y := Y)
    (measurable_of_finite _) (measurable_of_finite _) c.dec
  have hset : {ω | c.dec (Y ω) ≠ Mm ω} = {ω : (M × L) × (Fin n → B × E) |
      c.dec (fun i => (ω.2 i).1) ≠ ω.1.1} := rfl
  rw [hset, c.measureReal_dec_ne W] at hF
  have h4 := mutualInfo_comp_le μ (X := Mm) (Y := fun ω => (Y ω, Z ω)) (measurable_of_finite _)
    (measurable_of_finite _) Prod.fst
  have h5 := mutualInfo_pair_eq_add_condMutualInfo μ (X := Mm) (Y := Y) (Z := Z)
  have h6a := condMutualInfo_eq_condEntropy_sub_condEntropy μ (X := Mm) (Y := Y) (Z := Z)
  have h6b := condEntropy_le_condEntropy_comp (μ := μ) (X := Y) (Y := fun ω => (U ω, Z ω))
    (measurable_of_finite _) (measurable_of_finite _) (fun p => (p.1.1, p.2))
  have h7i : ∀ i, H[fun ω => Y ω i | Z ; μ] ≤ H[fun ω => Y ω i | fun ω => Z ω i ; μ] :=
    fun i => condEntropy_le_condEntropy_comp (μ := μ) (X := fun ω => Y ω i) (Y := Z)
      (measurable_of_finite _) (measurable_of_finite _) (fun z : Fin n → E => z i)
  have h7p : H[Y | Z ; μ] ≤ ∑ i, H[fun ω => Y ω i | Z ; μ] :=
    condEntropy_pi_le_sum μ (Y := Y) (Z := Z) (fun i => measurable_of_finite _)
      (measurable_of_finite _)
  have h7 : H[Y | Z ; μ] ≤ ∑ i, H[fun ω => Y ω i | fun ω => Z ω i ; μ] :=
    h7p.trans (sum_le_sum fun i _ => h7i i)
  have h8a : H[fun ω => (Z ω, Y ω) | U ; μ] = H[Z | U ; μ] + H[Y | fun ω => (Z ω, U ω) ; μ] :=
    condEntropy_pair_eq_add μ
  have h8b : H[Y | fun ω => (U ω, Z ω) ; μ] = H[Y | fun ω => (Z ω, U ω) ; μ] :=
    condEntropy_cond_of_injective μ (Z := fun ω => (Z ω, U ω)) (e := Prod.swap)
      Prod.swap_injective fun ω => rfl
  have h8c : H[fun ω => (Z ω, Y ω) | U ; μ] = H[fun ω : (M × L) × (Fin n → B × E) => ω.2 | U ;
      μ] := by
    have := condEntropy_comp_of_injective μ (X := fun ω : (M × L) × (Fin n → B × E) => ω.2)
      (Z := U) (f := fun y => ((fun i => (y i).2), fun i => (y i).1)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        funext i
        exact Prod.ext (congrFun h.2 i) (congrFun h.1 i)
    exact this
  have h8d := condEntropy_eq_sum μ (fun ω : (M × L) × (Fin n → B × E) => ω.2) U
  have h8e : H[Z | U ; μ] ≤ ∑ i, H[fun ω => Z ω i | U ; μ] :=
    condEntropy_pi_le_sum μ (fun i => measurable_of_finite _) (measurable_of_finite _)
  have hν := Interactive.map_codeMeasure_letter W (c.toFn (E := E))
  have hterm : ∀ i, H[fun ω => Y ω i | fun ω => Z ω i ; μ] -
      H[fun ω : (M × L) × (Fin n → B × E) => ω.2 i | fun ω => (ω.1, seqPrefix ω.2 i) ; μ] +
      H[fun ω => Z ω i | U ; μ] ≤
      I[fun ω : A × (B × E) => ω.1 : fun ω => ω.2.1 | fun ω => ω.2.2 ;
        W.jointMeasure (Interactive.inputLaw W (c.toFn (E := E)) i)] := by
    intro i
    set ν := W.jointMeasure (Interactive.inputLaw W (c.toFn (E := E)) i)
    have e1 : H[fun ω => Y ω i | fun ω => Z ω i ; μ] =
        H[fun x : A × (B × E) => x.2.1 | fun x => x.2.2 ; ν] := by
      rw [show ν = _ from (hν i).symm,
        condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _)
        (measurable_of_finite _)]
      rfl
    have e2 := Interactive.condEntropy_prefix_eq W (c.toFn (E := E)) i id
    have e3 : H[fun ω : (M × L) × (Fin n → B × E) => id (ω.2 i) |
        fun ω => c.toFn ω.1 i (seqPrefix ω.2 i) ; μ] =
        H[fun x : A × (B × E) => x.2 | Prod.fst ; ν] := by
      rw [show ν = _ from (hν i).symm,
        condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _)
        measurable_fst]
      rfl
    have e4 : H[fun ω => Z ω i | U ; μ] ≤ H[fun x : A × (B × E) => x.2.2 | Prod.fst ; ν] := by
      have := condEntropy_le_condEntropy_comp (μ := μ) (X := fun ω => Z ω i) (Y := U)
        (measurable_of_finite _) (measurable_of_finite _) (fun ml => c.enc ml i)
      refine this.trans (le_of_eq ?_)
      rw [show ν = _ from (hν i).symm,
        condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _)
        measurable_fst]
      rfl
    have e5 := condMutualInfo_eq_condEntropy_sub_condEntropy ν
      (X := fun x : A × (B × E) => x.1) (Y := fun x => x.2.1) (Z := fun x => x.2.2)
    have e6 := condEntropy_pair_eq_add ν (X := fun x : A × (B × E) => x.2.2)
      (Y := fun x => x.2.1) (Z := fun x => x.1)
    have e7 : H[fun x : A × (B × E) => (x.2.2, x.2.1) | fun x => x.1 ; ν] =
        H[fun x : A × (B × E) => x.2 | Prod.fst ; ν] :=
      condEntropy_comp_of_injective ν (X := fun x : A × (B × E) => x.2) (Z := Prod.fst)
        (f := Prod.swap) Prod.swap_injective
    have e8 : H[fun x : A × (B × E) => x.2.1 | fun x => (x.2.2, x.1) ; ν] =
        H[fun x : A × (B × E) => x.2.1 | fun x => (x.1, x.2.2) ; ν] :=
      condEntropy_cond_of_injective ν (Z := fun x : A × (B × E) => (x.1, x.2.2))
        (e := Prod.swap) Prod.swap_injective fun ω => rfl
    have e9 : H[fun ω : (M × L) × (Fin n → B × E) => ω.2 i |
        fun ω => (ω.1, seqPrefix ω.2 i) ; μ] =
        H[fun ω : (M × L) × (Fin n → B × E) => id (ω.2 i) |
          fun ω => (ω.1, seqPrefix ω.2 i) ; μ] := rfl
    linarith
  have hsum : H[fun ω : (M × L) × (Fin n → B × E) => ω.2 | U ; μ] =
      ∑ i, H[fun ω : (M × L) × (Fin n → B × E) => ω.2 i |
        fun ω => (ω.1, seqPrefix ω.2 i) ; μ] :=
    h8d
  have htot : ∑ i, (H[fun ω => Y ω i | fun ω => Z ω i ; μ] -
      H[fun ω : (M × L) × (Fin n → B × E) => ω.2 i | fun ω => (ω.1, seqPrefix ω.2 i) ; μ] +
      H[fun ω => Z ω i | U ; μ]) ≤ ∑ i,
      I[fun ω : A × (B × E) => ω.1 : fun ω => ω.2.1 | fun ω => ω.2.2 ;
        W.jointMeasure (Interactive.inputLaw W (c.toFn (E := E)) i)] :=
    sum_le_sum fun i _ => hterm i
  simp only [sum_add_distrib, sum_sub_distrib] at htot
  have hleak : c.leakage W = I[Mm : Z ; μ] := rfl
  have hcomp : I[Mm : Prod.fst ∘ fun ω => (Y ω, Z ω) ; μ] = I[Mm : Y ; μ] := rfl
  have hexp : (1 - (c.avgError W).toReal) * Real.log (Fintype.card M) =
      Real.log (Fintype.card M) - (c.avgError W).toReal * Real.log (Fintype.card M) := by ring
  have hH' : H[Mm ; μ] = Real.log (Fintype.card M) := hH
  have h6b' : H[Y | fun ω => (U ω, Z ω) ; μ] ≤ H[Y | fun ω => (Mm ω, Z ω) ; μ] := h6b
  rw [hcomp] at h4
  linarith

end WiretapCode

namespace Wiretap

variable {A B E : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype E] [MeasurableSpace E]
  [MeasurableSingletonClass E] in
theorem jointPMF_degraded_map (W₁ : DMC A B) (D : DMC B E) (p : PMF A) :
    (DMC.jointPMF (degraded W₁ D) p).map (fun ω => (ω.1, ω.2.1)) = DMC.jointPMF W₁ p := by
  simp only [DMC.jointPMF, PMF.map_bind, PMF.map_comp]
  congr 1
  funext a
  rw [← DMC.jointPMF_map_fst D (W₁ a), PMF.map_comp, degraded]
  rfl

theorem condEntropy_degraded (W₁ : DMC A B) (D : DMC B E) (p : PMF A) :
    H[fun ω : A × (B × E) => ω.2.2 | fun ω => (ω.1, ω.2.1) ; (degraded W₁ D).jointMeasure p] =
      H[fun ω : A × (B × E) => ω.2.2 | fun ω => ω.2.1 ; (degraded W₁ D).jointMeasure p] := by
  classical
  set ν := (degraded W₁ D).jointMeasure p
  have hK : ∀ (g : A × B) (z : E), ν.real {ω | (ω.1, ω.2.1) = g ∧ ω.2.2 = z} =
      ν.real {ω | (ω.1, ω.2.1) = g} * (D g.2 z).toReal := by
    intro g z
    have e1 : {ω : A × (B × E) | (ω.1, ω.2.1) = g ∧ ω.2.2 = z} = {(g.1, (g.2, z))} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.ext_iff]
      tauto
    have e2 : ν.real {ω : A × (B × E) | (ω.1, ω.2.1) = g} =
        (ν.map fun ω => (ω.1, ω.2.1)).real {g} := by
      rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton g)]
      rfl
    rw [e1, e2, show ν = (DMC.jointPMF (degraded W₁ D) p).toMeasure from rfl,
      PMF.toMeasure_map _ _ (measurable_of_finite _),
      jointPMF_degraded_map, measureReal_def, measureReal_def,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), DMC.jointPMF_apply,
      DMC.jointPMF_apply, degraded, DMC.jointPMF_apply, ← ENNReal.toReal_mul, mul_assoc]
  exact Interactive.condEntropy_eq_comp_of_kernel ν (measurable_of_finite _)
    (measurable_of_finite _) Prod.snd D hK

theorem condMutualInfo_degraded (W₁ : DMC A B) (D : DMC B E) (p : PMF A) :
    I[fun ω : A × (B × E) => ω.1 : fun ω => ω.2.1 | fun ω => ω.2.2 ;
        (degraded W₁ D).jointMeasure p] = secrecyRate (degraded W₁ D) p := by
  set ν := (degraded W₁ D).jointMeasure p
  have h0 : I[fun ω : A × (B × E) => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ; ν] = 0 := by
    rw [condMutualInfo_eq_condEntropy_sub_condEntropy, condEntropy_degraded, sub_self]
  have h1 := mutualInfo_pair_eq_add_condMutualInfo ν (X := fun ω : A × (B × E) => ω.1)
    (Y := fun ω => ω.2.2) (Z := fun ω => ω.2.1)
  have h2 := mutualInfo_pair_eq_add_condMutualInfo ν (X := fun ω : A × (B × E) => ω.1)
    (Y := fun ω => ω.2.1) (Z := fun ω => ω.2.2)
  have h3 : I[fun ω : A × (B × E) => ω.1 : fun ω => (ω.2.2, ω.2.1) ; ν] =
      I[fun ω : A × (B × E) => ω.1 : fun ω => (ω.2.1, ω.2.2) ; ν] :=
    mutualInfo_comp_right_of_injective ν (X := fun ω : A × (B × E) => ω.1)
      (Y := fun ω => (ω.2.1, ω.2.2)) (f := Prod.swap) Prod.swap_injective
  rw [secrecyRate]
  linarith

theorem secrecyRate_le_log_card (W : DMC A (B × E)) (p : PMF A) :
    secrecyRate W p ≤ Real.log (Fintype.card B) := by
  have h1 := mutualInfo_nonneg (W.jointMeasure p) (X := fun ω : A × (B × E) => ω.1)
    (Y := fun ω => ω.2.2) measurable_fst (measurable_of_finite _)
  have h2 := mutualInfo_eq_entropy_sub_condEntropy (μ := W.jointMeasure p)
    (fun ω : A × (B × E) => ω.2.1) (fun ω => ω.1)
  have h3 := condEntropy_nonneg (W.jointMeasure p) (X := fun ω : A × (B × E) => ω.2.1)
    (Y := fun ω => ω.1) (measurable_of_finite _) measurable_fst
  have h4 := entropy_le_log_card (W.jointMeasure p) (X := fun ω : A × (B × E) => ω.2.1)
  have h5 := mutualInfo_comm (W.jointMeasure p) (X := fun ω : A × (B × E) => ω.1)
    (Y := fun ω => ω.2.1)
  rw [secrecyRate]
  linarith

theorem secrecyRate_le_secrecyCapacity (W : DMC A (B × E)) (p : PMF A) :
    secrecyRate W p ≤ secrecyCapacity W :=
  le_ciSup ⟨_, Set.forall_mem_range.2 (secrecyRate_le_log_card W)⟩ p

theorem le_secrecyCapacity_of_achievable (W₁ : DMC A B) (D : DMC B E) {R : ℝ}
    (h : Achievable (degraded W₁ D) R) : R ≤ secrecyCapacity (degraded W₁ D) := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  set C := secrecyCapacity (degraded W₁ D)
  have hC : 0 ≤ C := by
    rcases isEmpty_or_nonempty (PMF A) with hA | hA
    · simp [C, secrecyCapacity]
    · obtain ⟨p⟩ := hA
      refine le_trans ?_ (secrecyRate_le_secrecyCapacity _ p)
      rw [← condMutualInfo_degraded]
      exact condMutualInfo_nonneg _ measurable_fst (measurable_of_finite _)
        (measurable_of_finite _)
  set δ := R - C with hδ
  have hδ0 : 0 < δ := by linarith
  have hR : 0 < R := by linarith
  set e := δ / (2 * (R + 1)) with he
  have he0 : 0 < e := div_pos hδ0 (by linarith)
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
  have key := c.one_sub_mul_log_card_le (degraded W₁ D)
  rw [Fintype.card_fin] at key
  have hsum : ∑ i, I[fun ω : A × (B × E) => ω.1 : fun ω => ω.2.1 | fun ω => ω.2.2 ;
      (degraded W₁ D).jointMeasure (Interactive.inputLaw (degraded W₁ D)
        (c.toFn (E := E)) i)] ≤ n * C := by
    refine (sum_le_sum fun i _ => (condMutualInfo_degraded W₁ D _).trans_le
      (secrecyRate_le_secrecyCapacity _ _)).trans_eq ?_
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hPe : (c.avgError (degraded W₁ D)).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1a : (1 - e) * Real.log k ≤ (1 - (c.avgError (degraded W₁ D)).toReal) * Real.log k :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)
  have h1 : (1 - e) * Real.log k ≤ n * e + n * C + Real.log 2 := by linarith
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) - n * e = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

end Wiretap

end Meat
