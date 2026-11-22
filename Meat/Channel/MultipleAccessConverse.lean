import Meat.Channel.Converse
import Meat.Channel.MultipleAccessAchievability

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

namespace MAC

variable {A₁ A₂ B : Type*}

theorem inputPMF_map_fst (p₁ : PMF A₁) (p₂ : PMF A₂) : (inputPMF p₁ p₂).map Prod.fst = p₁ :=
  DMC.jointPMF_map_fst _ _

theorem inputPMF_map_snd (p₁ : PMF A₁) (p₂ : PMF A₂) : (inputPMF p₁ p₂).map Prod.snd = p₂ := by
  simp only [inputPMF, DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]
  exact (congrArg p₁.bind (funext fun _ => PMF.map_id p₂)).trans (PMF.bind_const p₁ p₂)

theorem inputPMF_map {A₁' A₂' : Type*} (p₁ : PMF A₁) (p₂ : PMF A₂) (f : A₁ → A₁')
    (g : A₂ → A₂') :
    (inputPMF p₁ p₂).map (fun a => (f a.1, g a.2)) = inputPMF (p₁.map f) (p₂.map g) := by
  simp only [inputPMF, DMC.jointPMF, PMF.map_bind, PMF.map_comp, PMF.bind_map]
  rfl

theorem jointPMF_map_input (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    (jointPMF W p₁ p₂).map (fun ω => (ω.1, ω.2.1)) = inputPMF p₁ p₂ := by
  rw [← DMC.jointPMF_map_fst W (inputPMF p₁ p₂), jointPMF_inputPMF, PMF.map_comp]
  rfl

theorem jointPMF_swap (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    jointPMF (fun a => W a.swap) p₂ p₁ = (jointPMF W p₁ p₂).map fun ω => (ω.2.1, ω.1, ω.2.2) :=
  (jointPMF_eq_sideChannel₁ _ p₂ p₁).trans (jointPMF_sideChannel₂ W p₁ p₂)

variable [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

private lemma measureReal_map_singleton_toMeasure {α β : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : PMF α) (f : α → β) (x : β) :
    (p.toMeasure.map f).real {x} = (p.map f x).toReal := by
  rw [PMF.toMeasure_map _ _ (measurable_of_finite _), measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

omit [Fintype B] in
theorem mutualInfo_inputs_eq_zero [Finite B] (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.1 ; jointMeasure W p₁ p₂] = 0 := by
  refine mutualInfo_eq_zero_of_measureReal_eq_mul _ fun a₁ a₂ => ?_
  have h₁ : (jointPMF W p₁ p₂).map (fun ω => ω.1) = p₁ := by
    rw [show (fun ω : A₁ × A₂ × B => ω.1) = Prod.fst ∘ fun ω => (ω.1, ω.2.1) from rfl,
      ← PMF.map_comp, jointPMF_map_input, inputPMF_map_fst]
  have h₂ : (jointPMF W p₁ p₂).map (fun ω => ω.2.1) = p₂ := by
    rw [show (fun ω : A₁ × A₂ × B => ω.2.1) = Prod.snd ∘ fun ω => (ω.1, ω.2.1) from rfl,
      ← PMF.map_comp, jointPMF_map_input, inputPMF_map_snd]
  rw [jointMeasure_eq_toMeasure, measureReal_map_singleton_toMeasure,
    measureReal_map_singleton_toMeasure, measureReal_map_singleton_toMeasure, jointPMF_map_input,
    h₁, h₂, inputPMF_apply, ENNReal.toReal_mul]

theorem condMutualInfo_nonneg₁ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    0 ≤ I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ; jointMeasure W p₁ p₂] :=
  condMutualInfo_nonneg _ measurable_fst (measurable_snd.comp measurable_snd)
    (measurable_fst.comp measurable_snd)

theorem condMutualInfo_nonneg₂ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    0 ≤ I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ; jointMeasure W p₁ p₂] :=
  condMutualInfo_nonneg _ (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd) measurable_fst

theorem mutualInfo_eq_add₁ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ; jointMeasure W p₁ p₂] =
      I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 ; jointMeasure W p₁ p₂] +
        I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ; jointMeasure W p₁ p₂] := by
  have h := mutualInfo_pair_eq_add_condMutualInfo (jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.2.2) (Y := fun ω => ω.1) (Z := fun ω => ω.2.1)
  rw [mutualInfo_comm, h, mutualInfo_comm, condMutualInfo_comm]

theorem mutualInfo_eq_add₂ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ; jointMeasure W p₁ p₂] =
      I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 ; jointMeasure W p₁ p₂] +
        I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ; jointMeasure W p₁ p₂] := by
  have h := mutualInfo_pair_eq_add_condMutualInfo (jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.2.2) (Y := fun ω => ω.2.1) (Z := fun ω => ω.1)
  have hs := mutualInfo_comp_right_of_injective (jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.2.2) (Y := fun ω => (ω.2.1, ω.1)) Prod.swap_injective
  rw [mutualInfo_comm]
  change I[fun ω : A₁ × A₂ × B => ω.2.2 : Prod.swap ∘ fun ω => (ω.2.1, ω.1) ;
    jointMeasure W p₁ p₂] = _
  rw [hs, h, mutualInfo_comm, condMutualInfo_comm]

theorem condMutualInfo_le_mutualInfo₁ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ; jointMeasure W p₁ p₂] ≤
      I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ; jointMeasure W p₁ p₂] := by
  have h0 := mutualInfo_nonneg (jointMeasure W p₁ p₂) (X := fun ω : A₁ × A₂ × B => ω.2.1)
    (Y := fun ω => ω.2.2) (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  linarith [mutualInfo_eq_add₁ W p₁ p₂]

theorem condMutualInfo_le_mutualInfo₂ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ; jointMeasure W p₁ p₂] ≤
      I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ; jointMeasure W p₁ p₂] := by
  have h0 := mutualInfo_nonneg (jointMeasure W p₁ p₂) (X := fun ω : A₁ × A₂ × B => ω.1)
    (Y := fun ω => ω.2.2) measurable_fst (measurable_snd.comp measurable_snd)
  linarith [mutualInfo_eq_add₂ W p₁ p₂]

theorem mutualInfo_le_add (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ; jointMeasure W p₁ p₂] ≤
      I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ; jointMeasure W p₁ p₂] +
        I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ; jointMeasure W p₁ p₂] := by
  have h := mutualInfo_add_condMutualInfo_comm (μ := jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.2.1) (Y := fun ω => ω.1) (Z := fun ω => ω.2.2)
  have h0 := condMutualInfo_nonneg (jointMeasure W p₁ p₂) (X := fun ω : A₁ × A₂ × B => ω.2.1)
    (Y := fun ω => ω.1) (Z := fun ω => ω.2.2) (measurable_fst.comp measurable_snd)
    measurable_fst (measurable_snd.comp measurable_snd)
  have hi := mutualInfo_inputs_eq_zero W p₁ p₂
  rw [mutualInfo_comm] at hi
  have hc := mutualInfo_comm (jointMeasure W p₁ p₂) (X := fun ω : A₁ × A₂ × B => ω.2.1)
    (Y := fun ω => ω.2.2)
  linarith [mutualInfo_eq_add₁ W p₁ p₂]

theorem condMutualInfo_swap (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₂ × A₁ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        jointMeasure (fun a => W a.swap) p₂ p₁] =
      I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ; jointMeasure W p₁ p₂] := by
  rw [jointMeasure_eq_toMeasure, jointPMF_swap, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (X := fun ω : A₂ × A₁ × B => ω.1)
      (Y := fun ω => ω.2.2) (Z := fun ω => ω.2.1) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
  rfl

theorem condMutualInfo_eq_condEntropy_sub (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ; jointMeasure W p₁ p₂] =
      H[Prod.snd | fun x : (A₁ × A₂) × B => x.1.2 ; W.jointMeasure (inputPMF p₁ p₂)] -
        H[Prod.snd | Prod.fst ; W.jointMeasure (inputPMF p₁ p₂)] := by
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy, DMC.jointMeasure_eq_toMeasure,
    jointPMF_inputPMF, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condEntropy_map _ (measurable_of_finite _) measurable_snd (measurable_of_finite _),
    condEntropy_map _ (measurable_of_finite _) measurable_snd measurable_fst]
  rfl

end MAC

namespace MACCode

variable {M₁ M₂ A₁ A₂ B : Type*} {n : ℕ}

def swap (c : MACCode M₁ M₂ A₁ A₂ B n) : MACCode M₂ M₁ A₂ A₁ B n :=
  ⟨c.enc₂, c.enc₁, fun y => (c.dec y).swap⟩

theorem avgError_swap [Fintype B] [Fintype M₁] [Fintype M₂] [DecidableEq M₁] [DecidableEq M₂]
    (c : MACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) :
    c.swap.avgError (fun a => W a.swap) = c.avgError W := by
  rw [avgError, avgError, mul_comm (Fintype.card M₂ : ℝ≥0∞),
    ← (Equiv.prodComm M₁ M₂).sum_comp]
  congr 1
  refine sum_congr rfl fun m _ => sum_congr rfl fun y _ => ?_
  by_cases h : c.dec y = m
  · simp [swap, h]
  · have h' : (c.dec y).swap ≠ m.swap := fun h'' => h (Prod.swap_injective h'')
    simp [swap, h, h', DMC.blockProb]

variable [Fintype M₁] [Nonempty M₁] [Fintype M₂] [Nonempty M₂]

noncomputable def inputLaw₁ (c : MACCode M₁ M₂ A₁ A₂ B n) (i : Fin n) : PMF A₁ :=
  (PMF.ofFintype _ (sum_inv_card M₁)).map fun m => c.enc₁ m i

noncomputable def inputLaw₂ (c : MACCode M₁ M₂ A₁ A₂ B n) (i : Fin n) : PMF A₂ :=
  (PMF.ofFintype _ (sum_inv_card M₂)).map fun m => c.enc₂ m i

omit [Fintype M₁] [Nonempty M₁] in
theorem inputLaw₁_swap (c : MACCode M₁ M₂ A₁ A₂ B n) (i : Fin n) :
    c.swap.inputLaw₁ i = c.inputLaw₂ i := rfl

omit [Fintype M₂] [Nonempty M₂] in
theorem inputLaw₂_swap (c : MACCode M₁ M₂ A₁ A₂ B n) (i : Fin n) :
    c.swap.inputLaw₂ i = c.inputLaw₁ i := rfl

theorem toBlockCode_inputLaw (c : MACCode M₁ M₂ A₁ A₂ B n) (i : Fin n) :
    c.toBlockCode.inputLaw i = MAC.inputPMF (c.inputLaw₁ i) (c.inputLaw₂ i) := by
  have hu : ∀ h, PMF.ofFintype (fun _ : M₁ × M₂ => ((Fintype.card (M₁ × M₂) : ℝ≥0∞))⁻¹) h =
      MAC.inputPMF (PMF.ofFintype _ (sum_inv_card M₁)) (PMF.ofFintype _ (sum_inv_card M₂)) := by
    intro h
    ext ⟨m₁, m₂⟩
    rw [MAC.inputPMF_apply, PMF.ofFintype_apply, PMF.ofFintype_apply, PMF.ofFintype_apply,
      Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inl (ENNReal.natCast_ne_top _))]
  rw [BlockCode.inputLaw, hu, inputLaw₁, inputLaw₂, ← MAC.inputPMF_map]
  rfl

variable [MeasurableSpace M₁] [MeasurableSingletonClass M₁] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] [DecidableEq M₁] [DecidableEq M₂]
  [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem one_sub_mul_log_card_le_sum_mutualInfo (c : MACCode M₁ M₂ A₁ A₂ B n)
    (W : DMC (A₁ × A₂) B) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M₁ * Fintype.card M₂) ≤
      ∑ i, I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
        MAC.jointMeasure W (c.inputLaw₁ i) (c.inputLaw₂ i)] + Real.log 2 := by
  have h1 := c.toBlockCode.mutualInfo_le_sum_inputMutualInfo W
  have h2 := c.toBlockCode.condEntropy_fst_snd_codeMeasure_le W
  have h3 := mutualInfo_eq_entropy_sub_condEntropy Prod.fst Prod.snd (c.toBlockCode.codeMeasure W)
  rw [BlockCode.entropy_fst_codeMeasure] at h3
  simp only [toBlockCode_inputLaw, MAC.inputMutualInfo_inputPMF] at h1
  rw [avgError_toBlockCode, Fintype.card_prod, Nat.cast_mul] at h2
  rw [Fintype.card_prod, Nat.cast_mul] at h3
  have h4 : (1 - (c.avgError W).toReal) * Real.log (Fintype.card M₁ * Fintype.card M₂) =
      Real.log (Fintype.card M₁ * Fintype.card M₂) -
        (c.avgError W).toReal * Real.log (Fintype.card M₁ * Fintype.card M₂) := by ring
  linarith

theorem one_sub_mul_log_card_le_sum_condMutualInfo₁ (c : MACCode M₁ M₂ A₁ A₂ B n)
    (W : DMC (A₁ × A₂) B) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M₁) ≤
      ∑ i, I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure W (c.inputLaw₁ i) (c.inputLaw₂ i)] + Real.log 2 := by
  set μ := c.toBlockCode.codeMeasure W
  have hU : H[Prod.fst ; μ] = Real.log (Fintype.card M₁) + Real.log (Fintype.card M₂) := by
    rw [BlockCode.entropy_fst_codeMeasure, Fintype.card_prod, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
        (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
  have hU₂ : H[fun ω : (M₁ × M₂) × (Fin n → B) => ω.1.2 ; μ] ≤ Real.log (Fintype.card M₂) :=
    entropy_le_log_card μ
  have hF : H[fun ω : (M₁ × M₂) × (Fin n → B) => ω.1.1 | Prod.snd ; μ] ≤
      Real.log 2 + (c.avgError W).toReal * Real.log (Fintype.card M₁) := by
    have h := condEntropy_le_log_two_add_mul_log_card (μ := μ)
      (X := fun ω : (M₁ × M₂) × (Fin n → B) => ω.1.1) (Y := Prod.snd)
      (measurable_fst.comp measurable_fst) measurable_snd (fun y => (c.dec y).1)
    have hm : μ.real {ω | (c.dec ω.2).1 ≠ ω.1.1} ≤ (c.avgError W).toReal := by
      rw [← avgError_toBlockCode, ← BlockCode.measureReal_dec_ne]
      exact measureReal_mono fun ω hω h' => hω (congrArg Prod.fst h')
    have := mul_le_mul_of_nonneg_right hm (Real.log_natCast_nonneg (Fintype.card M₁))
    linarith
  have hC : H[fun ω : (M₁ × M₂) × (Fin n → B) => ω.1.1 | fun ω => (ω.2, ω.1.2) ; μ] ≤
      H[fun ω : (M₁ × M₂) × (Fin n → B) => ω.1.1 | Prod.snd ; μ] :=
    condEntropy_le_condEntropy_comp (μ := μ) (measurable_fst.comp measurable_fst)
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)) Prod.fst
  have hN := c.toBlockCode.condEntropy_snd_fst_codeMeasure W
  have hS : H[Prod.snd | fun ω : (M₁ × M₂) × (Fin n → B) => ω.1.2 ; μ] ≤
      ∑ i, H[Prod.snd | fun x : (A₁ × A₂) × B => x.1.2 ;
        W.jointMeasure (c.toBlockCode.inputLaw i)] := by
    refine (condEntropy_pi_le_sum μ (Y := Prod.snd) (fun i => (measurable_pi_apply i).comp
      measurable_snd) (measurable_snd.comp measurable_fst)).trans (sum_le_sum fun i _ => ?_)
    rw [← BlockCode.map_codeMeasure, condEntropy_map _ (measurable_of_finite _) (X := Prod.snd)
      (Y := fun x : (A₁ × A₂) × B => x.1.2) measurable_snd (measurable_of_finite _)]
    exact condEntropy_le_condEntropy_comp (μ := μ) ((measurable_pi_apply i).comp measurable_snd)
      (measurable_snd.comp measurable_fst) (fun m₂ => c.enc₂ m₂ i)
  have hI : ∑ i, I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure W (c.inputLaw₁ i) (c.inputLaw₂ i)] =
      ∑ i, H[Prod.snd | fun x : (A₁ × A₂) × B => x.1.2 ;
        W.jointMeasure (c.toBlockCode.inputLaw i)] -
      ∑ i, H[Prod.snd | Prod.fst ; W.jointMeasure (c.toBlockCode.inputLaw i)] := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by
      rw [toBlockCode_inputLaw, MAC.condMutualInfo_eq_condEntropy_sub]
  have hR : H[fun ω : (M₁ × M₂) × (Fin n → B) => (ω.1.1, (ω.2, ω.1.2)) ; μ] =
      H[fun ω : (M₁ × M₂) × (Fin n → B) => (ω.2, ω.1) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω : (M₁ × M₂) × (Fin n → B) => (ω.2, ω.1))
      (f := fun p : (Fin n → B) × (M₁ × M₂) => (p.2.1, (p.1, p.2.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)
  have key : Real.log (Fintype.card M₁) ≤
      H[Prod.snd | fun ω : (M₁ × M₂) × (Fin n → B) => ω.1.2 ; μ] - H[Prod.snd | Prod.fst ; μ] +
        H[fun ω : (M₁ × M₂) × (Fin n → B) => ω.1.1 | fun ω => (ω.2, ω.1.2) ; μ] := by
    simp only [condEntropy_def]
    rw [hR]
    linarith
  linarith

theorem one_sub_mul_log_card_le_sum_condMutualInfo₂ (c : MACCode M₁ M₂ A₁ A₂ B n)
    (W : DMC (A₁ × A₂) B) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M₂) ≤
      ∑ i, I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
        MAC.jointMeasure W (c.inputLaw₁ i) (c.inputLaw₂ i)] + Real.log 2 := by
  have h := c.swap.one_sub_mul_log_card_le_sum_condMutualInfo₁ (fun a => W a.swap)
  rw [avgError_swap] at h
  simpa only [inputLaw₁_swap, inputLaw₂_swap, MAC.condMutualInfo_swap] using h

end MACCode

namespace MAC

theorem mem_convexHull_of_sum_le {ι : Type*} [Fintype ι] [Nonempty ι] (S : ι → Set (ℝ × ℝ))
    (a b c : ι → ℝ)
    (hS : ∀ i (R : ℝ × ℝ), 0 ≤ R.1 → 0 ≤ R.2 → R.1 ≤ a i → R.2 ≤ b i → R.1 + R.2 ≤ c i →
      R ∈ S i)
    (hac : ∀ i, a i ≤ c i) (hbc : ∀ i, b i ≤ c i) (hcab : ∀ i, c i ≤ a i + b i)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h₁ : Fintype.card ι * x ≤ ∑ i, a i)
    (h₂ : Fintype.card ι * y ≤ ∑ i, b i) (h₃ : Fintype.card ι * (x + y) ≤ ∑ i, c i) :
    (x, y) ∈ convexHull ℝ (⋃ i, S i) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN : 0 < N := Nat.cast_pos.2 Fintype.card_pos
  set A := (∑ i, a i) / N with hAdef
  set Bv := (∑ i, b i) / N with hBdef
  set Cv := (∑ i, c i) / N with hCdef
  have hNA : N * A = ∑ i, a i := mul_div_cancel₀ _ hN.ne'
  have hNB : N * Bv = ∑ i, b i := mul_div_cancel₀ _ hN.ne'
  have hNC : N * Cv = ∑ i, c i := mul_div_cancel₀ _ hN.ne'
  have hA : x ≤ A := le_of_mul_le_mul_left (by linarith) hN
  have hB : y ≤ Bv := le_of_mul_le_mul_left (by linarith) hN
  have hC : x + y ≤ Cv := le_of_mul_le_mul_left (by linarith) hN
  have hCAB : Cv ≤ A + Bv := by
    refine le_of_mul_le_mul_left ?_ hN
    rw [mul_add, hNA, hNB, hNC, ← sum_add_distrib]
    exact sum_le_sum fun i _ => hcab i
  set t := max x (Cv - Bv) with htdef
  have ht1 : Cv - Bv ≤ t := le_max_right _ _
  have ht2 : x ≤ t := le_max_left _ _
  have ht3 : t ≤ A := max_le hA (by linarith)
  have ht4 : y ≤ Cv - t := by
    rcases max_cases x (Cv - Bv) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [htdef, h] <;> linarith
  set θ := (t - (Cv - Bv)) / (A - (Cv - Bv)) with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  have hθt : θ * A + (1 - θ) * (Cv - Bv) = t := by
    rcases eq_or_lt_of_le (show Cv - Bv ≤ A by linarith) with h | h
    · have : t = Cv - Bv := le_antisymm (h ▸ ht3) ht1
      rw [hθdef, ← h, sub_self, div_zero, this]
      ring
    · rw [hθdef]
      field_simp
      ring
  set u : ι → ℝ := fun i => θ * a i + (1 - θ) * (c i - b i) with hudef
  have hu1 : ∀ i, c i - b i ≤ u i := fun i => by
    have := hcab i
    simp only [hudef]
    nlinarith
  have hu2 : ∀ i, u i ≤ a i := fun i => by
    have := hcab i
    simp only [hudef]
    nlinarith
  have hsu : ∑ i, u i = N * t := by
    rw [← hθt]
    simp only [hudef, sum_add_distrib, ← mul_sum, sum_sub_distrib]
    rw [← hNA, ← hNB, ← hNC]
    ring
  set s := x / t with hsdef
  set r := y / (Cv - t) with hrdef
  have hs : s * t = x := by
    rcases eq_or_lt_of_le (hx.trans ht2) with h | h
    · rw [hsdef, ← h, div_zero, zero_mul]
      linarith
    · exact div_mul_cancel₀ _ h.ne'
  have hr : r * (Cv - t) = y := by
    rcases eq_or_lt_of_le (hy.trans ht4) with h | h
    · rw [hrdef, ← h, div_zero, zero_mul]
      linarith
    · exact div_mul_cancel₀ _ h.ne'
  have hs0 : 0 ≤ s := div_nonneg hx (hx.trans ht2)
  have hs1 : s ≤ 1 := div_le_one_of_le₀ ht2 (hx.trans ht2)
  have hr0 : 0 ≤ r := div_nonneg hy (hy.trans ht4)
  have hr1 : r ≤ 1 := div_le_one_of_le₀ ht4 (hy.trans ht4)
  have hmem : ∀ i, (s * u i, r * (c i - u i)) ∈ S i := by
    intro i
    have hu0 : 0 ≤ u i := by linarith [hu1 i, hbc i]
    have hcu0 : 0 ≤ c i - u i := by linarith [hu2 i, hac i]
    have e1 : s * u i ≤ u i := mul_le_of_le_one_left hu0 hs1
    have e2 : r * (c i - u i) ≤ c i - u i := mul_le_of_le_one_left hcu0 hr1
    exact hS i _ (mul_nonneg hs0 hu0) (mul_nonneg hr0 hcu0) (by linarith [hu2 i])
      (by linarith [hu1 i]) (by simp only; linarith)
  have heq : (x, y) = ∑ i, (1 / N) • (s * u i, r * (c i - u i)) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      simp only [Prod.smul_fst, smul_eq_mul]
      rw [← mul_sum, ← mul_sum, hsu]
      field_simp
      linarith
    · rw [Prod.snd_sum]
      simp only [Prod.smul_snd, smul_eq_mul]
      rw [← mul_sum, ← mul_sum, sum_sub_distrib, hsu, ← hNC]
      field_simp
      linarith
  rw [heq]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => by positivity) ?_
    fun i _ => subset_convexHull ℝ _ (Set.mem_iUnion.2 ⟨i, hmem i⟩)
  rw [sum_const, card_univ, nsmul_eq_mul, ← hNdef]
  field_simp

variable {A₁ A₂ B : Type*} [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

private lemma dist_max_le {r ε l : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε) (hl : 0 ≤ l) :
    dist r (max ((1 - ε) * r - l) 0) ≤ ε * r + l := by
  rw [Real.dist_eq]
  rcases le_total ((1 - ε) * r - l) 0 with h | h
  · rw [max_eq_right h, sub_zero, abs_of_nonneg hr]
    linarith
  · rw [max_eq_left h, abs_of_nonneg (by nlinarith)]
    linarith

private lemma rate_bound {n R ε l L S : ℝ} (hn : 0 < n) (hR : 0 ≤ R) (hl : l ≤ ε)
    (hε : ε ≤ 1 / 2) (hL : n * R ≤ L) (hB : (1 - l) * L ≤ S + Real.log 2) :
    n * ((1 - ε) * R - Real.log 2 / n) ≤ S := by
  have e : n * ((1 - ε) * R - Real.log 2 / n) = (1 - ε) * (n * R) - Real.log 2 := by
    field_simp
  have h1 : (1 - ε) * (n * R) ≤ (1 - l) * L :=
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hL (by linarith))
  linarith

private lemma sum_rate_bound {n R R' ε l L L' S : ℝ} (hn : 0 < n) (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (hl : l ≤ ε) (hε : ε ≤ 1 / 2) (hL : n * R ≤ L) (hL' : n * R' ≤ L')
    (hB : (1 - l) * (L + L') ≤ S + Real.log 2) :
    n * ((1 - ε) * R - Real.log 2 / n + ((1 - ε) * R' - Real.log 2 / n)) ≤ S := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h := rate_bound (R := R + R') hn (by linarith) hl hε (by linarith) hB
  have e : n * ((1 - ε) * R - Real.log 2 / n + ((1 - ε) * R' - Real.log 2 / n)) =
      n * ((1 - ε) * (R + R') - Real.log 2 / n) - Real.log 2 := by
    field_simp
    ring
  linarith

private lemma clamp_bounds {N x y SA SB SC : ℝ} (ha : 0 ≤ SA) (hb : 0 ≤ SB)
    (hac : SA ≤ SC) (hbc : SB ≤ SC) (hx : N * x ≤ SA) (hy : N * y ≤ SB)
    (hxy : N * (x + y) ≤ SC) :
    N * max x 0 ≤ SA ∧ N * max y 0 ≤ SB ∧ N * (max x 0 + max y 0) ≤ SC := by
  rcases le_total x 0 with h | h <;> rcases le_total y 0 with h' | h' <;>
    simp only [max_eq_right, max_eq_left, h, h', mul_zero, zero_add, add_zero] <;>
    exact ⟨by linarith, by linarith, by linarith⟩

theorem mem_capacityRegion_of_mem_achievableRegion (W : DMC (A₁ × A₂) B) {R : ℝ × ℝ}
    (hR : R ∈ achievableRegion W) : R ∈ capacityRegion W := by
  classical
  obtain ⟨hR1, hR2, hA⟩ := hR
  rw [capacityRegion, Metric.mem_closure_iff]
  intro η hη
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ε * (R.1 + R.2 + 1) ≤ η / 2 := by
    refine ⟨min (1 / 2) (η / (2 * (R.1 + R.2 + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, ?_⟩
    calc min (1 / 2) (η / (2 * (R.1 + R.2 + 1))) * (R.1 + R.2 + 1)
        ≤ η / (2 * (R.1 + R.2 + 1)) * (R.1 + R.2 + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = η / 2 := by field_simp
  obtain ⟨N, hN⟩ := hA (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε0)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * Real.log 2 / η)
  obtain ⟨n, hnN, hn0, hn1⟩ : ∃ n : ℕ, N ≤ n ∧ n₀ ≤ n ∧ 1 ≤ n :=
    ⟨max (max N n₀) 1, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
  have hlogn : Real.log 2 / n < η / 2 := by
    have h1 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn0
    have h2 : 2 * Real.log 2 < η * n := by
      have := (div_lt_iff₀ hη).1 (hn₀.trans_le h1)
      linarith
    rw [div_lt_iff₀ hnpos]
    linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hnN
  have hk₁0 : (0 : ℝ) < k₁ := (Real.exp_pos _).trans_le hk₁
  have hk₂0 : (0 : ℝ) < k₂ := (Real.exp_pos _).trans_le hk₂
  have : Nonempty (Fin k₁) := ⟨⟨0, Nat.cast_pos.1 hk₁0⟩⟩
  have : Nonempty (Fin k₂) := ⟨⟨0, Nat.cast_pos.1 hk₂0⟩⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  have hlam : (c.avgError W).toReal ≤ ε := ENNReal.toReal_le_of_le_ofReal hε0.le hc
  have B1 := c.one_sub_mul_log_card_le_sum_condMutualInfo₁ W
  have B2 := c.one_sub_mul_log_card_le_sum_condMutualInfo₂ W
  have B3 := c.one_sub_mul_log_card_le_sum_mutualInfo W
  rw [Fintype.card_fin] at B1 B2
  rw [Fintype.card_fin, Fintype.card_fin, Real.log_mul hk₁0.ne' hk₂0.ne'] at B3
  have hl₁ : n * R.1 ≤ Real.log k₁ := (Real.le_log_iff_exp_le hk₁0).2 hk₁
  have hl₂ : n * R.2 ≤ Real.log k₂ := (Real.le_log_iff_exp_le hk₂0).2 hk₂
  have hx₀ := rate_bound hnpos hR1 hlam hε1 hl₁ B1
  have hy₀ := rate_bound hnpos hR2 hlam hε1 hl₂ B2
  have hxy₀ := sum_rate_bound hnpos hR1 hR2 hlam hε1 hl₁ hl₂ B3
  obtain ⟨h₁, h₂, h₃⟩ := clamp_bounds
    (sum_nonneg fun i _ => condMutualInfo_nonneg₁ W _ _)
    (sum_nonneg fun i _ => condMutualInfo_nonneg₂ W _ _)
    (sum_le_sum fun i _ => condMutualInfo_le_mutualInfo₁ W _ _)
    (sum_le_sum fun i _ => condMutualInfo_le_mutualInfo₂ W _ _) hx₀ hy₀ hxy₀
  have hcard : (Fintype.card (Fin n) : ℝ) = n := by rw [Fintype.card_fin]
  have hmem := mem_convexHull_of_sum_le
    (fun i : Fin n => pentagon W (c.inputLaw₁ i) (c.inputLaw₂ i))
    (fun i => I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
      jointMeasure W (c.inputLaw₁ i) (c.inputLaw₂ i)])
    (fun i => I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
      jointMeasure W (c.inputLaw₁ i) (c.inputLaw₂ i)])
    (fun i => I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
      jointMeasure W (c.inputLaw₁ i) (c.inputLaw₂ i)])
    (fun i R h1 h2 h3 h4 h5 => ⟨h1, h2, h3, h4, h5⟩)
    (fun i => condMutualInfo_le_mutualInfo₁ W _ _) (fun i => condMutualInfo_le_mutualInfo₂ W _ _)
    (fun i => mutualInfo_le_add W _ _) (le_max_right _ _) (le_max_right _ _)
    (by rw [hcard]; exact h₁) (by rw [hcard]; exact h₂) (by rw [hcard]; exact h₃)
  have hsub : (⋃ i : Fin n, pentagon W (c.inputLaw₁ i) (c.inputLaw₂ i)) ⊆
      ⋃ p₁ : PMF A₁, ⋃ p₂ : PMF A₂, pentagon W p₁ p₂ := fun x hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion₂.2 ⟨c.inputLaw₁ i, c.inputLaw₂ i, hi⟩
  refine ⟨(max ((1 - ε) * R.1 - Real.log 2 / n) 0, max ((1 - ε) * R.2 - Real.log 2 / n) 0),
    convexHull_mono hsub hmem, ?_⟩
  have hl0 : 0 ≤ Real.log 2 / n := div_nonneg hlog2 hnpos.le
  have d1 := dist_max_le hR1 hε0.le hl0
  have d2 := dist_max_le hR2 hε0.le hl0
  have e1 : ε * R.1 ≤ ε * (R.1 + R.2 + 1) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
  have e2 : ε * R.2 ≤ ε * (R.1 + R.2 + 1) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨d1.trans_lt (by linarith), d2.trans_lt (by linarith)⟩

end MAC

end Meat
