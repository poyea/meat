import Meat.Channel.Achievability
import Meat.Channel.MultipleAccess
import Meat.Shannon.Conditional
import Meat.Shannon.TypicalIntersection

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace MACCode

variable {M₁ M₂ A₁ A₂ B : Type*} {n : ℕ}

def toBlockCode (c : MACCode M₁ M₂ A₁ A₂ B n) : BlockCode (M₁ × M₂) (A₁ × A₂) B n :=
  ⟨fun m i => (c.enc₁ m.1 i, c.enc₂ m.2 i), c.dec⟩

theorem errorProb_toBlockCode [Fintype B] [DecidableEq M₁] [DecidableEq M₂]
    (c : MACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) (m : M₁ × M₂) :
    c.toBlockCode.errorProb W m = c.errorProb W m := rfl

theorem avgError_toBlockCode [Fintype B] [Fintype M₁] [Fintype M₂] [DecidableEq M₁]
    [DecidableEq M₂] (c : MACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) :
    c.toBlockCode.avgError W = c.avgError W := by
  rw [BlockCode.avgError, avgError, Fintype.card_prod, Nat.cast_mul]
  rfl

noncomputable def typicalCode (C₁ : M₁ → Fin n → A₁) (C₂ : M₂ → Fin n → A₂)
    (J : Finset ((Fin n → A₁ × A₂) × (Fin n → B))) (m₀ : M₁ × M₂) : MACCode M₁ M₂ A₁ A₂ B n :=
  ⟨C₁, C₂, BlockCode.typicalDecoder (fun m i => (C₁ m.1 i, C₂ m.2 i)) J m₀⟩

theorem toBlockCode_typicalCode (C₁ : M₁ → Fin n → A₁) (C₂ : M₂ → Fin n → A₂)
    (J : Finset ((Fin n → A₁ × A₂) × (Fin n → B))) (m₀ : M₁ × M₂) :
    (typicalCode C₁ C₂ J m₀).toBlockCode =
      BlockCode.typicalCode (fun m i => (C₁ m.1 i, C₂ m.2 i)) J m₀ := rfl

end MACCode

namespace MAC

variable {A₁ A₂ B : Type*}

noncomputable def inputPMF (p₁ : PMF A₁) (p₂ : PMF A₂) : PMF (A₁ × A₂) :=
  DMC.jointPMF (fun _ => p₂) p₁

theorem inputPMF_apply (p₁ : PMF A₁) (p₂ : PMF A₂) (a₁ : A₁) (a₂ : A₂) :
    inputPMF p₁ p₂ (a₁, a₂) = p₁ a₁ * p₂ a₂ :=
  DMC.jointPMF_apply _ _ _ _

theorem iidProb_inputPMF {n : ℕ} (p₁ : PMF A₁) (p₂ : PMF A₂) (x₁ : Fin n → A₁)
    (x₂ : Fin n → A₂) :
    iidProb (inputPMF p₁ p₂) (fun i => (x₁ i, x₂ i)) = iidProb p₁ x₁ * iidProb p₂ x₂ := by
  simp [iidProb, inputPMF_apply, ENNReal.toReal_mul, prod_mul_distrib]

noncomputable def sideChannel₁ (W : DMC (A₁ × A₂) B) (p₂ : PMF A₂) : DMC A₁ (A₂ × B) :=
  fun a₁ => DMC.jointPMF (fun a₂ => W (a₁, a₂)) p₂

noncomputable def sideChannel₂ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) : DMC A₂ (A₁ × B) :=
  fun a₂ => DMC.jointPMF (fun a₁ => W (a₁, a₂)) p₁

theorem blockProb_sideChannel₁ {n : ℕ} (W : DMC (A₁ × A₂) B) (p₂ : PMF A₂) (x₁ : Fin n → A₁)
    (x₂ : Fin n → A₂) (y : Fin n → B) :
    (DMC.blockProb (sideChannel₁ W p₂) x₁ (fun i => (x₂ i, y i))).toReal =
      iidProb p₂ x₂ * (DMC.blockProb W (fun i => (x₁ i, x₂ i)) y).toReal := by
  simp [DMC.blockProb, sideChannel₁, DMC.jointPMF_apply, iidProb, ENNReal.toReal_prod,
    ENNReal.toReal_mul, prod_mul_distrib]

theorem blockProb_sideChannel₂ {n : ℕ} (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (x₁ : Fin n → A₁)
    (x₂ : Fin n → A₂) (y : Fin n → B) :
    (DMC.blockProb (sideChannel₂ W p₁) x₂ (fun i => (x₁ i, y i))).toReal =
      iidProb p₁ x₁ * (DMC.blockProb W (fun i => (x₁ i, x₂ i)) y).toReal := by
  simp [DMC.blockProb, sideChannel₂, DMC.jointPMF_apply, iidProb, ENNReal.toReal_prod,
    ENNReal.toReal_mul, prod_mul_distrib]

noncomputable def jointPMF (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    PMF (A₁ × A₂ × B) :=
  p₁.bind fun a₁ => p₂.bind fun a₂ => (W (a₁, a₂)).map fun b => (a₁, a₂, b)

theorem jointMeasure_eq_toMeasure [MeasurableSpace A₁] [MeasurableSpace A₂] [MeasurableSpace B]
    (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    jointMeasure W p₁ p₂ = (jointPMF W p₁ p₂).toMeasure := rfl

theorem jointPMF_eq_sideChannel₁ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    jointPMF W p₁ p₂ = DMC.jointPMF (sideChannel₁ W p₂) p₁ := by
  simp only [jointPMF, DMC.jointPMF, sideChannel₁, PMF.map_bind, PMF.map_comp]
  rfl

theorem jointPMF_apply (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) (a₁ : A₁) (a₂ : A₂)
    (b : B) : jointPMF W p₁ p₂ (a₁, a₂, b) = p₁ a₁ * (p₂ a₂ * W (a₁, a₂) b) := by
  rw [jointPMF_eq_sideChannel₁, DMC.jointPMF_apply, sideChannel₁, DMC.jointPMF_apply]

theorem jointPMF_inputPMF (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    DMC.jointPMF W (inputPMF p₁ p₂) =
      (jointPMF W p₁ p₂).map fun ω => ((ω.1, ω.2.1), ω.2.2) := by
  ext ⟨⟨a₁, a₂⟩, b⟩
  rw [show ((a₁, a₂), b) = (fun ω : A₁ × A₂ × B => ((ω.1, ω.2.1), ω.2.2)) (a₁, a₂, b) from rfl,
    PMF.map_apply_of_injective _ (fun x y h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)),
    DMC.jointPMF_apply, inputPMF_apply, jointPMF_apply, mul_assoc]

theorem jointPMF_sideChannel₂ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    DMC.jointPMF (sideChannel₂ W p₁) p₂ =
      (jointPMF W p₁ p₂).map fun ω => (ω.2.1, ω.1, ω.2.2) := by
  ext ⟨a₂, a₁, b⟩
  rw [show (a₂, a₁, b) = (fun ω : A₁ × A₂ × B => (ω.2.1, ω.1, ω.2.2)) (a₁, a₂, b) from rfl,
    PMF.map_apply_of_injective _ (fun x y h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)),
    DMC.jointPMF_apply, sideChannel₂, DMC.jointPMF_apply, jointPMF_apply, mul_left_comm]

theorem iidProb_jointPMF_inputPMF {n : ℕ} (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂)
    (x₁ : Fin n → A₁) (x₂ : Fin n → A₂) (y : Fin n → B) :
    iidProb (DMC.jointPMF W (inputPMF p₁ p₂)) (fun i => ((x₁ i, x₂ i), y i)) =
      iidProb p₁ x₁ * iidProb p₂ x₂ * (DMC.blockProb W (fun i => (x₁ i, x₂ i)) y).toReal := by
  rw [DMC.iidProb_jointPMF W _ (fun i => (x₁ i, x₂ i)) y, iidProb_inputPMF]

theorem iidProb_jointPMF_sideChannel₁ {n : ℕ} (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁)
    (p₂ : PMF A₂) (x₁ : Fin n → A₁) (x₂ : Fin n → A₂) (y : Fin n → B) :
    iidProb (DMC.jointPMF (sideChannel₁ W p₂) p₁) (fun i => (x₁ i, (x₂ i, y i))) =
      iidProb p₁ x₁ * iidProb p₂ x₂ * (DMC.blockProb W (fun i => (x₁ i, x₂ i)) y).toReal := by
  rw [DMC.iidProb_jointPMF (sideChannel₁ W p₂) p₁ x₁ (fun i => (x₂ i, y i)),
    blockProb_sideChannel₁, mul_assoc]

theorem iidProb_jointPMF_sideChannel₂ {n : ℕ} (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁)
    (p₂ : PMF A₂) (x₁ : Fin n → A₁) (x₂ : Fin n → A₂) (y : Fin n → B) :
    iidProb (DMC.jointPMF (sideChannel₂ W p₁) p₂) (fun i => (x₂ i, (x₁ i, y i))) =
      iidProb p₁ x₁ * iidProb p₂ x₂ * (DMC.blockProb W (fun i => (x₁ i, x₂ i)) y).toReal := by
  rw [DMC.iidProb_jointPMF (sideChannel₂ W p₁) p₂ x₂ (fun i => (x₁ i, y i)),
    blockProb_sideChannel₂]
  ring

section Information

variable [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

instance isProbabilityMeasure_jointMeasure (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    IsProbabilityMeasure (jointMeasure W p₁ p₂) := by
  unfold jointMeasure
  infer_instance

theorem inputMutualInfo_inputPMF (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    W.inputMutualInfo (inputPMF p₁ p₂) =
      I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ; jointMeasure W p₁ p₂] := by
  rw [DMC.inputMutualInfo, DMC.jointMeasure_eq_toMeasure, jointPMF_inputPMF,
    ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    mutualInfo_map _ (measurable_of_finite _) measurable_fst measurable_snd]
  rfl

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B] in
theorem inputMutualInfo_sideChannel₁ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    (sideChannel₁ W p₂).inputMutualInfo p₁ =
      I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2 ; jointMeasure W p₁ p₂] := by
  rw [DMC.inputMutualInfo, DMC.jointMeasure_eq_toMeasure, ← jointPMF_eq_sideChannel₁]
  rfl

theorem inputMutualInfo_sideChannel₂ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    (sideChannel₂ W p₁).inputMutualInfo p₂ =
      I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => (ω.1, ω.2.2) ; jointMeasure W p₁ p₂] := by
  rw [DMC.inputMutualInfo, DMC.jointMeasure_eq_toMeasure, jointPMF_sideChannel₂,
    ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    mutualInfo_map _ (measurable_of_finite _) measurable_fst measurable_snd]
  rfl

theorem condMutualInfo_le_inputMutualInfo_sideChannel₁ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁)
    (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ; jointMeasure W p₁ p₂] ≤
      (sideChannel₁ W p₂).inputMutualInfo p₁ := by
  have h := mutualInfo_pair_eq_add_condMutualInfo (jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.1) (Y := fun ω => ω.2.2) (Z := fun ω => ω.2.1)
  have h0 := mutualInfo_nonneg (jointMeasure W p₁ p₂) (X := fun ω : A₁ × A₂ × B => ω.1)
    (Y := fun ω => ω.2.1) measurable_fst (measurable_fst.comp measurable_snd)
  have hs := mutualInfo_comp_right_of_injective (jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.1) (Y := fun ω => ω.2) Prod.swap_injective
  rw [inputMutualInfo_sideChannel₁, ← hs]
  change _ ≤ I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => (ω.2.2, ω.2.1) ; jointMeasure W p₁ p₂]
  linarith

theorem condMutualInfo_le_inputMutualInfo_sideChannel₂ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁)
    (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ; jointMeasure W p₁ p₂] ≤
      (sideChannel₂ W p₁).inputMutualInfo p₂ := by
  have h := mutualInfo_pair_eq_add_condMutualInfo (jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.2.1) (Y := fun ω => ω.2.2) (Z := fun ω => ω.1)
  have h0 := mutualInfo_nonneg (jointMeasure W p₁ p₂) (X := fun ω : A₁ × A₂ × B => ω.2.1)
    (Y := fun ω => ω.1) (measurable_fst.comp measurable_snd) measurable_fst
  have hs := mutualInfo_comp_right_of_injective (jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.2.1) (Y := fun ω => (ω.2.2, ω.1)) Prod.swap_injective
  rw [inputMutualInfo_sideChannel₂]
  refine le_of_le_of_eq ?_ hs.symm
  linarith

end Information


section Coding

variable [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

noncomputable def decodingSet (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) (n : ℕ)
    (ε : ℝ) : Finset ((Fin n → A₁ × A₂) × (Fin n → B)) := by
  classical
  exact {xy | xy ∈ jointlyTypicalSet (DMC.jointPMF W (inputPMF p₁ p₂)) n ε ∧
    ((fun i => (xy.1 i).1), fun i => ((xy.1 i).2, xy.2 i)) ∈
      jointlyTypicalSet (DMC.jointPMF (sideChannel₁ W p₂) p₁) n ε ∧
    ((fun i => (xy.1 i).2), fun i => ((xy.1 i).1, xy.2 i)) ∈
      jointlyTypicalSet (DMC.jointPMF (sideChannel₂ W p₁) p₂) n ε}

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B] in
theorem mem_decodingSet {W : DMC (A₁ × A₂) B} {p₁ : PMF A₁} {p₂ : PMF A₂} {n : ℕ} {ε : ℝ}
    {xy : (Fin n → A₁ × A₂) × (Fin n → B)} :
    xy ∈ decodingSet W p₁ p₂ n ε ↔
      xy ∈ jointlyTypicalSet (DMC.jointPMF W (inputPMF p₁ p₂)) n ε ∧
      ((fun i => (xy.1 i).1), fun i => ((xy.1 i).2, xy.2 i)) ∈
        jointlyTypicalSet (DMC.jointPMF (sideChannel₁ W p₂) p₁) n ε ∧
      ((fun i => (xy.1 i).2), fun i => ((xy.1 i).1, xy.2 i)) ∈
        jointlyTypicalSet (DMC.jointPMF (sideChannel₂ W p₁) p₂) n ε := by
  simp [decodingSet]

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private def splitEquiv₁ (n : ℕ) :
    (Fin n → A₁ × A₂) × (Fin n → B) ≃ (Fin n → A₁) × (Fin n → A₂ × B) where
  toFun xy := (fun i => (xy.1 i).1, fun i => ((xy.1 i).2, xy.2 i))
  invFun z := (fun i => (z.1 i, (z.2 i).1), fun i => (z.2 i).2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private def splitEquiv₂ (n : ℕ) :
    (Fin n → A₁ × A₂) × (Fin n → B) ≃ (Fin n → A₂) × (Fin n → A₁ × B) where
  toFun xy := (fun i => (xy.1 i).2, fun i => ((xy.1 i).1, xy.2 i))
  invFun z := (fun i => ((z.2 i).1, z.1 i), fun i => (z.2 i).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem tendsto_sum_iidProb_decodingSet (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => ∑ xy ∈ decodingSet W p₁ p₂ n ε,
      iidProb (DMC.jointPMF W (inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 1) := by
  classical
  set P := DMC.jointPMF W (inputPMF p₁ p₂)
  let w : ∀ n, (Fin n → A₁ × A₂) × (Fin n → B) → ℝ :=
    fun n xy => iidProb P (fun i => (xy.1 i, xy.2 i))
  have hw : ∀ n xy, 0 ≤ w n xy := fun n xy => iidProb_nonneg _ _
  have h1 : ∀ n, ∑ xy, w n xy ≤ 1 := fun n => (sum_iidProb_pair P n).le
  let s₂ := fun n => (jointlyTypicalSet (DMC.jointPMF (sideChannel₁ W p₂) p₁) n ε).map
    (splitEquiv₁ n).symm.toEmbedding
  let s₃ := fun n => (jointlyTypicalSet (DMC.jointPMF (sideChannel₂ W p₁) p₂) n ε).map
    (splitEquiv₂ n).symm.toEmbedding
  have h₂ : Tendsto (fun n => ∑ xy ∈ s₂ n, w n xy) atTop (𝓝 1) := by
    refine (tendsto_sum_iidProb_jointlyTypicalSet (DMC.jointPMF (sideChannel₁ W p₂) p₁)
      hε).congr fun n => ?_
    rw [sum_map]
    refine sum_congr rfl fun z _ => ?_
    exact (iidProb_jointPMF_sideChannel₁ W p₁ p₂ z.1 (fun i => (z.2 i).1)
      (fun i => (z.2 i).2)).trans
        (iidProb_jointPMF_inputPMF W p₁ p₂ z.1 (fun i => (z.2 i).1) (fun i => (z.2 i).2)).symm
  have h₃ : Tendsto (fun n => ∑ xy ∈ s₃ n, w n xy) atTop (𝓝 1) := by
    refine (tendsto_sum_iidProb_jointlyTypicalSet (DMC.jointPMF (sideChannel₂ W p₁) p₂)
      hε).congr fun n => ?_
    rw [sum_map]
    refine sum_congr rfl fun z _ => ?_
    exact (iidProb_jointPMF_sideChannel₂ W p₁ p₂ (fun i => (z.2 i).1) z.1
      (fun i => (z.2 i).2)).trans
        (iidProb_jointPMF_inputPMF W p₁ p₂ (fun i => (z.2 i).1) z.1 (fun i => (z.2 i).2)).symm
  have h₂₃ := tendsto_sum_of_mem_iff_and (α := fun n => (Fin n → A₁ × A₂) × (Fin n → B)) hw h1
    (u := fun n => s₂ n ∩ s₃ n) (fun n x => mem_inter) h₂ h₃
  refine tendsto_sum_of_mem_iff_and hw h1 (s := fun n => jointlyTypicalSet P n ε)
    (fun n xy => ?_) (tendsto_sum_iidProb_jointlyTypicalSet P hε) h₂₃
  rw [mem_decodingSet, mem_inter, mem_map_equiv, mem_map_equiv, Equiv.symm_symm, Equiv.symm_symm]
  rfl

private lemma ite_one_le {p q : Prop} [Decidable p] [Decidable q] (h : p → q) :
    (if p then (1 : ℝ) else 0) ≤ if q then 1 else 0 := by
  split_ifs <;> simp_all

variable [DecidableEq A₁] [DecidableEq A₂] [DecidableEq B]

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B] in
theorem sum_sum_iidProb_mul_sum_ite_decodingSet (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁)
    (p₂ : PMF A₂) (n : ℕ) (ε : ℝ) :
    ∑ a : Fin n → A₁, iidProb p₁ a * ∑ b : Fin n → A₂, iidProb p₂ b *
        ∑ y, (if ((fun i => (a i, b i)), y) ∈ decodingSet W p₁ p₂ n ε then 0
          else (DMC.blockProb W (fun i => (a i, b i)) y).toReal) =
      1 - ∑ xy ∈ decodingSet W p₁ p₂ n ε,
        iidProb (DMC.jointPMF W (inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i)) := by
  rw [← sum_iidProb_pair (DMC.jointPMF W (inputPMF p₁ p₂)) n, ← sum_ite_mem_zero,
    Fintype.sum_prod_type, sum_arrow_prod]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [iidProb_jointPMF_inputPMF]
  split_ifs <;> ring

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B] in
theorem sum_sum_mul_sum_decodingSet_le₁ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂)
    (n : ℕ) (ε : ℝ) :
    ∑ a : Fin n → A₁, ∑ a' : Fin n → A₁, iidProb p₁ a * iidProb p₁ a' *
        ∑ b : Fin n → A₂, iidProb p₂ b *
          ∑ y, (if ((fun i => (a' i, b i)), y) ∈ decodingSet W p₁ p₂ n ε then (1 : ℝ) else 0) *
            (DMC.blockProb W (fun i => (a i, b i)) y).toReal ≤
      Real.exp (-(n * ((sideChannel₁ W p₂).inputMutualInfo p₁ - 3 * ε))) := by
  refine le_trans ?_ (DMC.sum_iidProb_mul_iidProb_mul_sum_le (sideChannel₁ W p₂) p₁ n ε)
  refine sum_le_sum fun a _ => sum_le_sum fun a' _ => mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (iidProb_nonneg _ _) (iidProb_nonneg _ _))
  rw [sum_arrow_prod]
  refine sum_le_sum fun b _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun y _ => ?_
  rw [blockProb_sideChannel₁, ← mul_assoc, mul_comm (iidProb p₂ b), mul_assoc]
  refine mul_le_mul_of_nonneg_right (ite_one_le fun h => (mem_decodingSet.1 h).2.1)
    (mul_nonneg (iidProb_nonneg _ _) ENNReal.toReal_nonneg)

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B] in
theorem sum_sum_mul_sum_decodingSet_le₂ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂)
    (n : ℕ) (ε : ℝ) :
    ∑ a : Fin n → A₁, iidProb p₁ a * ∑ b : Fin n → A₂, ∑ b' : Fin n → A₂,
        iidProb p₂ b * iidProb p₂ b' *
          ∑ y, (if ((fun i => (a i, b' i)), y) ∈ decodingSet W p₁ p₂ n ε then (1 : ℝ) else 0) *
            (DMC.blockProb W (fun i => (a i, b i)) y).toReal ≤
      Real.exp (-(n * ((sideChannel₂ W p₁).inputMutualInfo p₂ - 3 * ε))) := by
  have e : ∑ a : Fin n → A₁, iidProb p₁ a * ∑ b : Fin n → A₂, ∑ b' : Fin n → A₂,
        iidProb p₂ b * iidProb p₂ b' *
          ∑ y, (if ((fun i => (a i, b' i)), y) ∈ decodingSet W p₁ p₂ n ε then (1 : ℝ) else 0) *
            (DMC.blockProb W (fun i => (a i, b i)) y).toReal =
      ∑ b : Fin n → A₂, ∑ b' : Fin n → A₂, iidProb p₂ b * iidProb p₂ b' *
        ∑ a : Fin n → A₁, iidProb p₁ a *
          ∑ y, (if ((fun i => (a i, b' i)), y) ∈ decodingSet W p₁ p₂ n ε then (1 : ℝ) else 0) *
            (DMC.blockProb W (fun i => (a i, b i)) y).toReal := by
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b' _ => sum_congr rfl fun a _ => sum_congr rfl fun y _ => ?_
    ring
  rw [e]
  refine le_trans ?_ (DMC.sum_iidProb_mul_iidProb_mul_sum_le (sideChannel₂ W p₁) p₂ n ε)
  refine sum_le_sum fun b _ => sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (iidProb_nonneg _ _) (iidProb_nonneg _ _))
  rw [sum_arrow_prod]
  refine sum_le_sum fun a _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun y _ => ?_
  rw [blockProb_sideChannel₂, ← mul_assoc, mul_comm (iidProb p₁ a), mul_assoc]
  refine mul_le_mul_of_nonneg_right (ite_one_le fun h => (mem_decodingSet.1 h).2.2)
    (mul_nonneg (iidProb_nonneg _ _) ENNReal.toReal_nonneg)

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B] in
theorem sum_sum_mul_sum_decodingSet_le₃ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂)
    (n : ℕ) (ε : ℝ) :
    ∑ a : Fin n → A₁, ∑ a' : Fin n → A₁, iidProb p₁ a * iidProb p₁ a' *
        ∑ b : Fin n → A₂, ∑ b' : Fin n → A₂, iidProb p₂ b * iidProb p₂ b' *
          ∑ y, (if ((fun i => (a' i, b' i)), y) ∈ decodingSet W p₁ p₂ n ε then (1 : ℝ) else 0) *
            (DMC.blockProb W (fun i => (a i, b i)) y).toReal ≤
      Real.exp (-(n * (W.inputMutualInfo (inputPMF p₁ p₂) - 3 * ε))) := by
  set J := jointlyTypicalSet (DMC.jointPMF W (inputPMF p₁ p₂)) n ε
  refine le_trans ?_ (DMC.sum_iidProb_mul_iidProb_mul_sum_le W (inputPMF p₁ p₂) n ε)
  calc _ ≤ ∑ a : Fin n → A₁, ∑ a' : Fin n → A₁, iidProb p₁ a * iidProb p₁ a' *
        ∑ b : Fin n → A₂, ∑ b' : Fin n → A₂, iidProb p₂ b * iidProb p₂ b' *
          ∑ y, (if ((fun i => (a' i, b' i)), y) ∈ J then (1 : ℝ) else 0) *
            (DMC.blockProb W (fun i => (a i, b i)) y).toReal := by
        refine sum_le_sum fun a _ => sum_le_sum fun a' _ => mul_le_mul_of_nonneg_left
          (sum_le_sum fun b _ => sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left
            (sum_le_sum fun y _ => mul_le_mul_of_nonneg_right
              (ite_one_le fun h => (mem_decodingSet.1 h).1) ENNReal.toReal_nonneg)
            (mul_nonneg (iidProb_nonneg _ _) (iidProb_nonneg _ _)))
          (mul_nonneg (iidProb_nonneg _ _) (iidProb_nonneg _ _))
    _ = _ := by
        symm
        rw [sum_arrow_prod (S := A₁) (T := A₂)]
        refine sum_congr rfl fun a _ => ?_
        simp_rw [mul_sum, sum_arrow_prod (S := A₁) (T := A₂)]
        conv_rhs => rw [sum_comm]
        refine sum_congr rfl fun b _ => sum_congr rfl fun a' _ => sum_congr rfl fun b' _ =>
          sum_congr rfl fun y _ => ?_
        rw [iidProb_inputPMF, iidProb_inputPMF]
        ring

end Coding

section Random

variable [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  {M₁ M₂ : Type*} [Fintype M₁] [Fintype M₂] [DecidableEq M₁] [DecidableEq M₂]

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private lemma sum_erase_prod (F : M₁ × M₂ → ℝ) (m : M₁ × M₂) :
    ∑ m' ∈ univ.erase m, F m' =
      ∑ m₁' ∈ univ.erase m.1, F (m₁', m.2) + ∑ m₂' ∈ univ.erase m.2, F (m.1, m₂') +
        ∑ m₁' ∈ univ.erase m.1, ∑ m₂' ∈ univ.erase m.2, F (m₁', m₂') := by
  obtain ⟨m₁, m₂⟩ := m
  have h : ∀ m₁', ∑ m₂', F (m₁', m₂') = F (m₁', m₂) + ∑ m₂' ∈ univ.erase m₂, F (m₁', m₂') :=
    fun m₁' => (add_sum_erase _ _ (mem_univ _)).symm
  rw [sum_erase_eq_sub (mem_univ _), Fintype.sum_prod_type, ← add_sum_erase _ _ (mem_univ m₁)]
  simp only [h, sum_add_distrib]
  ring

omit [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [MeasurableSpace A₂]
  [MeasurableSingletonClass A₂] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] in
private lemma sum_codebook {n : ℕ} (p₁ : PMF A₁) (p₂ : PMF A₂)
    (f : (M₁ → Fin n → A₁) × (M₂ → Fin n → A₂) → ℝ) :
    ∑ C, (∏ j, iidProb p₁ (C.1 j)) * (∏ j, iidProb p₂ (C.2 j)) * f C =
      ∑ C₁ : M₁ → Fin n → A₁, (∏ j, iidProb p₁ (C₁ j)) *
        ∑ C₂ : M₂ → Fin n → A₂, (∏ j, iidProb p₂ (C₂ j)) * f (C₁, C₂) := by
  rw [Fintype.sum_prod_type]
  simp_rw [mul_sum, mul_assoc]

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B] in
theorem sum_errorProb_typicalCode_le {n : ℕ} (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂)
    (ε : ℝ) (m₀ m : M₁ × M₂) :
    ∑ C : (M₁ → Fin n → A₁) × (M₂ → Fin n → A₂),
        (∏ j, iidProb p₁ (C.1 j)) * (∏ j, iidProb p₂ (C.2 j)) *
          ((MACCode.typicalCode C.1 C.2 (decodingSet W p₁ p₂ n ε) m₀).errorProb W m).toReal ≤
      (1 - ∑ xy ∈ decodingSet W p₁ p₂ n ε,
          iidProb (DMC.jointPMF W (inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i))) +
        (Fintype.card M₁ - 1) *
          Real.exp (-(n * ((sideChannel₁ W p₂).inputMutualInfo p₁ - 3 * ε))) +
        (Fintype.card M₂ - 1) *
          Real.exp (-(n * ((sideChannel₂ W p₁).inputMutualInfo p₂ - 3 * ε))) +
        (Fintype.card M₁ - 1) * (Fintype.card M₂ - 1) *
          Real.exp (-(n * (W.inputMutualInfo (inputPMF p₁ p₂) - 3 * ε))) := by
  classical
  obtain ⟨m₁, m₂⟩ := m
  set J := decodingSet W p₁ p₂ n ε
  set e₁ := Real.exp (-(n * ((sideChannel₁ W p₂).inputMutualInfo p₁ - 3 * ε)))
  set e₂ := Real.exp (-(n * ((sideChannel₂ W p₁).inputMutualInfo p₂ - 3 * ε)))
  set e₃ := Real.exp (-(n * (W.inputMutualInfo (inputPMF p₁ p₂) - 3 * ε)))
  let ω : (M₁ → Fin n → A₁) × (M₂ → Fin n → A₂) → ℝ :=
    fun C => (∏ j, iidProb p₁ (C.1 j)) * ∏ j, iidProb p₂ (C.2 j)
  have hω : ∀ C, 0 ≤ ω C := fun C => mul_nonneg (prod_nonneg fun j _ => iidProb_nonneg _ _)
    (prod_nonneg fun j _ => iidProb_nonneg _ _)
  let T0 : (Fin n → A₁ × A₂) → ℝ :=
    fun x => ∑ y, if (x, y) ∈ J then 0 else (DMC.blockProb W x y).toReal
  let T : (Fin n → A₁ × A₂) → (Fin n → A₁ × A₂) → ℝ :=
    fun x' x => ∑ y, (if (x', y) ∈ J then (1 : ℝ) else 0) * (DMC.blockProb W x y).toReal
  let Z : (M₁ → Fin n → A₁) × (M₂ → Fin n → A₂) → M₁ → M₂ → Fin n → A₁ × A₂ :=
    fun C a b i => (C.1 a i, C.2 b i)
  have hpt : ∀ C, ((MACCode.typicalCode C.1 C.2 J m₀).errorProb W (m₁, m₂)).toReal ≤
      T0 (Z C m₁ m₂) + (∑ m₁' ∈ univ.erase m₁, T (Z C m₁' m₂) (Z C m₁ m₂) +
        ∑ m₂' ∈ univ.erase m₂, T (Z C m₁ m₂') (Z C m₁ m₂) +
        ∑ m₁' ∈ univ.erase m₁, ∑ m₂' ∈ univ.erase m₂, T (Z C m₁' m₂') (Z C m₁ m₂)) := by
    intro C
    have h := BlockCode.errorProb_typicalCode_toReal_le W (fun m i => (C.1 m.1 i, C.2 m.2 i)) J
      m₀ (m₁, m₂)
    rw [← MACCode.toBlockCode_typicalCode, MACCode.errorProb_toBlockCode, sum_erase_prod] at h
    exact h
  have A0 : ∑ C, ω C * T0 (Z C m₁ m₂) =
      1 - ∑ xy ∈ J, iidProb (DMC.jointPMF W (inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i)) := by
    rw [← sum_sum_iidProb_mul_sum_ite_decodingSet W p₁ p₂ n ε, sum_codebook]
    refine (sum_congr rfl fun C₁ _ => congrArg _ (sum_prod_mul_apply (fun _ b => iidProb p₂ b)
      (fun _ => sum_iidProb p₂ n) (fun b => T0 (fun i => (C₁ m₁ i, b i))) m₂)).trans ?_
    exact sum_prod_mul_apply (fun _ a => iidProb p₁ a) (fun _ => sum_iidProb p₁ n)
      (fun a => ∑ b, iidProb p₂ b * T0 (fun i => (a i, b i))) m₁
  have A1 : ∀ m₁' ∈ univ.erase m₁, ∑ C, ω C * T (Z C m₁' m₂) (Z C m₁ m₂) ≤ e₁ := by
    intro m₁' hm₁'
    refine le_trans (le_of_eq ?_) (sum_sum_mul_sum_decodingSet_le₁ W p₁ p₂ n ε)
    rw [sum_codebook]
    refine (sum_congr rfl fun C₁ _ => congrArg _ (sum_prod_mul_apply (fun _ b => iidProb p₂ b)
      (fun _ => sum_iidProb p₂ n) (fun b => T (fun i => (C₁ m₁' i, b i)) (fun i => (C₁ m₁ i, b i)))
        m₂)).trans ?_
    exact sum_prod_mul_apply_apply (fun _ a => iidProb p₁ a) (fun _ => sum_iidProb p₁ n)
      (fun a a' => ∑ b, iidProb p₂ b * T (fun i => (a' i, b i)) (fun i => (a i, b i)))
      (Ne.symm (ne_of_mem_erase hm₁'))
  have A2 : ∀ m₂' ∈ univ.erase m₂, ∑ C, ω C * T (Z C m₁ m₂') (Z C m₁ m₂) ≤ e₂ := by
    intro m₂' hm₂'
    refine le_trans (le_of_eq ?_) (sum_sum_mul_sum_decodingSet_le₂ W p₁ p₂ n ε)
    rw [sum_codebook]
    refine (sum_congr rfl fun C₁ _ => congrArg _ (sum_prod_mul_apply_apply
      (fun _ b => iidProb p₂ b) (fun _ => sum_iidProb p₂ n)
      (fun b b' => T (fun i => (C₁ m₁ i, b' i)) (fun i => (C₁ m₁ i, b i)))
      (Ne.symm (ne_of_mem_erase hm₂')))).trans ?_
    exact sum_prod_mul_apply (fun _ a => iidProb p₁ a) (fun _ => sum_iidProb p₁ n)
      (fun a => ∑ b, ∑ b', iidProb p₂ b * iidProb p₂ b' *
        T (fun i => (a i, b' i)) (fun i => (a i, b i))) m₁
  have A3 : ∀ m₁' ∈ univ.erase m₁, ∀ m₂' ∈ univ.erase m₂,
      ∑ C, ω C * T (Z C m₁' m₂') (Z C m₁ m₂) ≤ e₃ := by
    intro m₁' hm₁' m₂' hm₂'
    refine le_trans (le_of_eq ?_) (sum_sum_mul_sum_decodingSet_le₃ W p₁ p₂ n ε)
    rw [sum_codebook]
    refine (sum_congr rfl fun C₁ _ => congrArg _ (sum_prod_mul_apply_apply
      (fun _ b => iidProb p₂ b) (fun _ => sum_iidProb p₂ n)
      (fun b b' => T (fun i => (C₁ m₁' i, b' i)) (fun i => (C₁ m₁ i, b i)))
      (Ne.symm (ne_of_mem_erase hm₂')))).trans ?_
    exact sum_prod_mul_apply_apply (fun _ a => iidProb p₁ a) (fun _ => sum_iidProb p₁ n)
      (fun a a' => ∑ b, ∑ b', iidProb p₂ b * iidProb p₂ b' *
        T (fun i => (a' i, b' i)) (fun i => (a i, b i)))
      (Ne.symm (ne_of_mem_erase hm₁'))
  have e1 : ∑ C, ω C * ∑ m₁' ∈ univ.erase m₁, T (Z C m₁' m₂) (Z C m₁ m₂) =
      ∑ m₁' ∈ univ.erase m₁, ∑ C, ω C * T (Z C m₁' m₂) (Z C m₁ m₂) := by
    simp_rw [mul_sum]
    exact sum_comm
  have e2 : ∑ C, ω C * ∑ m₂' ∈ univ.erase m₂, T (Z C m₁ m₂') (Z C m₁ m₂) =
      ∑ m₂' ∈ univ.erase m₂, ∑ C, ω C * T (Z C m₁ m₂') (Z C m₁ m₂) := by
    simp_rw [mul_sum]
    exact sum_comm
  have e3 : ∑ C, ω C * ∑ m₁' ∈ univ.erase m₁, ∑ m₂' ∈ univ.erase m₂,
        T (Z C m₁' m₂') (Z C m₁ m₂) =
      ∑ m₁' ∈ univ.erase m₁, ∑ m₂' ∈ univ.erase m₂, ∑ C, ω C * T (Z C m₁' m₂') (Z C m₁ m₂) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_comm
  have hc₁ : (1 : ℝ) ≤ Fintype.card M₁ := Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ⟨m₁⟩)
  have hc₂ : (1 : ℝ) ≤ Fintype.card M₂ := Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ⟨m₂⟩)
  calc _ ≤ ∑ C, ω C * (T0 (Z C m₁ m₂) + (∑ m₁' ∈ univ.erase m₁, T (Z C m₁' m₂) (Z C m₁ m₂) +
          ∑ m₂' ∈ univ.erase m₂, T (Z C m₁ m₂') (Z C m₁ m₂) +
          ∑ m₁' ∈ univ.erase m₁, ∑ m₂' ∈ univ.erase m₂, T (Z C m₁' m₂') (Z C m₁ m₂))) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hpt C) (hω C)
    _ = ∑ C, ω C * T0 (Z C m₁ m₂) +
        (∑ m₁' ∈ univ.erase m₁, ∑ C, ω C * T (Z C m₁' m₂) (Z C m₁ m₂) +
          ∑ m₂' ∈ univ.erase m₂, ∑ C, ω C * T (Z C m₁ m₂') (Z C m₁ m₂) +
          ∑ m₁' ∈ univ.erase m₁, ∑ m₂' ∈ univ.erase m₂,
            ∑ C, ω C * T (Z C m₁' m₂') (Z C m₁ m₂)) := by
        rw [← e1, ← e2, ← e3]
        simp only [mul_add, sum_add_distrib]
    _ ≤ (1 - ∑ xy ∈ J, iidProb (DMC.jointPMF W (inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i))) +
        (∑ m₁' ∈ univ.erase m₁, e₁ + ∑ m₂' ∈ univ.erase m₂, e₂ +
          ∑ m₁' ∈ univ.erase m₁, ∑ m₂' ∈ univ.erase m₂, e₃) :=
        add_le_add A0.le (add_le_add (add_le_add (sum_le_sum A1) (sum_le_sum A2))
          (sum_le_sum fun m₁' hm₁' => sum_le_sum fun m₂' hm₂' => A3 m₁' hm₁' m₂' hm₂'))
    _ = _ := by
        simp only [sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul,
          Nat.cast_sub (Fintype.card_pos_iff.2 ⟨m₁⟩), Nat.cast_sub (Fintype.card_pos_iff.2 ⟨m₂⟩),
          Nat.cast_one]
        ring

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B] in
theorem exists_typicalCode_avgError_le {n : ℕ} (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁)
    (p₂ : PMF A₂) (ε : ℝ) (m₀ : M₁ × M₂) :
    ∃ (C₁ : M₁ → Fin n → A₁) (C₂ : M₂ → Fin n → A₂),
      (MACCode.typicalCode C₁ C₂ (decodingSet W p₁ p₂ n ε) m₀).avgError W ≤
        ENNReal.ofReal ((1 - ∑ xy ∈ decodingSet W p₁ p₂ n ε,
            iidProb (DMC.jointPMF W (inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i))) +
          (Fintype.card M₁ - 1) *
            Real.exp (-(n * ((sideChannel₁ W p₂).inputMutualInfo p₁ - 3 * ε))) +
          (Fintype.card M₂ - 1) *
            Real.exp (-(n * ((sideChannel₂ W p₁).inputMutualInfo p₂ - 3 * ε))) +
          (Fintype.card M₁ - 1) * (Fintype.card M₂ - 1) *
            Real.exp (-(n * (W.inputMutualInfo (inputPMF p₁ p₂) - 3 * ε)))) := by
  have : Nonempty (M₁ × M₂) := ⟨m₀⟩
  set β := (1 - ∑ xy ∈ decodingSet W p₁ p₂ n ε,
      iidProb (DMC.jointPMF W (inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i))) +
    (Fintype.card M₁ - 1) * Real.exp (-(n * ((sideChannel₁ W p₂).inputMutualInfo p₁ - 3 * ε))) +
    (Fintype.card M₂ - 1) * Real.exp (-(n * ((sideChannel₂ W p₁).inputMutualInfo p₂ - 3 * ε))) +
    (Fintype.card M₁ - 1) * (Fintype.card M₂ - 1) *
      Real.exp (-(n * (W.inputMutualInfo (inputPMF p₁ p₂) - 3 * ε)))
  have h1 : ∑ C : (M₁ → Fin n → A₁) × (M₂ → Fin n → A₂),
      (∏ j, iidProb p₁ (C.1 j)) * ∏ j, iidProb p₂ (C.2 j) = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, sum_prod (fun _ x => iidProb p₂ x) (fun _ => sum_iidProb p₂ n), mul_one]
    exact sum_prod (fun _ x => iidProb p₁ x) (fun _ => sum_iidProb p₁ n)
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le
    (w := fun C : (M₁ → Fin n → A₁) × (M₂ → Fin n → A₂) =>
      (∏ j, iidProb p₁ (C.1 j)) * ∏ j, iidProb p₂ (C.2 j))
    (f := fun C => ∑ m,
      ((MACCode.typicalCode C.1 C.2 (decodingSet W p₁ p₂ n ε) m₀).errorProb W m).toReal)
    (t := Fintype.card (M₁ × M₂) * β)
    (fun C => mul_nonneg (prod_nonneg fun j _ => iidProb_nonneg _ _)
      (prod_nonneg fun j _ => iidProb_nonneg _ _)) h1 (by
      simp only [mul_sum]
      rw [sum_comm]
      calc _ ≤ ∑ m : M₁ × M₂, β := sum_le_sum fun m _ => sum_errorProb_typicalCode_le W p₁ p₂ ε m₀ m
        _ = _ := by simp)
  refine ⟨C.1, C.2, ?_⟩
  rw [← MACCode.avgError_toBlockCode]
  exact BlockCode.avgError_le_ofReal _ W hC

end Random

private lemma mul_exp_le {n : ℕ} {x R I I' η : ℝ} (hx : x ≤ Real.exp (n * R)) (hI : I ≤ I')
    (hη : 4 * η ≤ I - R) : x * Real.exp (-(n * (I' - 3 * η))) ≤ Real.exp (n * (-η)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc x * Real.exp (-(n * (I' - 3 * η))) ≤ Real.exp (n * R) * Real.exp (-(n * (I - 3 * η))) :=
        mul_le_mul hx (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (n * R - n * (I - 3 * η)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (n * (-η)) := Real.exp_le_exp.2 (by nlinarith)

theorem achievable_of_lt [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
    [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) {R₁ R₂ : ℝ}
    (h₁ : R₁ < I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
      jointMeasure W p₁ p₂])
    (h₂ : R₂ < I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
      jointMeasure W p₁ p₂])
    (h₃ : R₁ + R₂ < I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
      jointMeasure W p₁ p₂]) :
    Achievable W R₁ R₂ := by
  classical
  intro ε hε
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  set I₁ := I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ; jointMeasure W p₁ p₂]
  set I₂ := I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ; jointMeasure W p₁ p₂]
  set I₃ := I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ; jointMeasure W p₁ p₂]
  set η := min (min (I₁ - R₁) (I₂ - R₂)) (I₃ - (R₁ + R₂)) / 4 with hη
  have hm1 := min_le_left (min (I₁ - R₁) (I₂ - R₂)) (I₃ - (R₁ + R₂))
  have hm2 := min_le_right (min (I₁ - R₁) (I₂ - R₂)) (I₃ - (R₁ + R₂))
  have hm3 := min_le_left (I₁ - R₁) (I₂ - R₂)
  have hm4 := min_le_right (I₁ - R₁) (I₂ - R₂)
  have hη0 : 0 < η := by
    rw [hη]
    exact div_pos (lt_min (lt_min (by linarith) (by linarith)) (by linarith)) (by norm_num)
  have hη1 : 4 * η ≤ I₁ - R₁ := by rw [hη]; linarith
  have hη2 : 4 * η ≤ I₂ - R₂ := by rw [hη]; linarith
  have hη3 : 4 * η ≤ I₃ - (R₁ + R₂) := by rw [hη]; linarith
  have hJ : Tendsto (fun n : ℕ => 1 - ∑ xy ∈ decodingSet W p₁ p₂ n η,
      iidProb (DMC.jointPMF W (inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_decodingSet W p₁ p₂ hη0)
  have hE := tendsto_exp_nat_mul (neg_neg_of_pos hη0)
  have hsum := hJ.add (hE.const_mul 3)
  rw [mul_zero, add_zero] at hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  set k₁ := ⌈Real.exp (n * R₁)⌉₊
  set k₂ := ⌈Real.exp (n * R₂)⌉₊
  have hk₁ : 0 < k₁ := Nat.ceil_pos.2 (Real.exp_pos _)
  have hk₂ : 0 < k₂ := Nat.ceil_pos.2 (Real.exp_pos _)
  have hk₁' : (k₁ : ℝ) - 1 ≤ Real.exp (n * R₁) := by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R₁)).le]
  have hk₂' : (k₂ : ℝ) - 1 ≤ Real.exp (n * R₂) := by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R₂)).le]
  have hk₂0 : (0 : ℝ) ≤ k₂ - 1 := by
    have : (1 : ℝ) ≤ k₂ := Nat.one_le_cast.2 hk₂
    linarith
  refine ⟨k₁, k₂, Nat.le_ceil _, Nat.le_ceil _, ?_⟩
  obtain ⟨C₁, C₂, hC⟩ := exists_typicalCode_avgError_le (n := n) W p₁ p₂ η
    ((⟨0, hk₁⟩, ⟨0, hk₂⟩) : Fin k₁ × Fin k₂)
  refine ⟨_, hC.trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hδε.le)⟩
  rw [Fintype.card_fin, Fintype.card_fin]
  have b1 := mul_exp_le hk₁' (condMutualInfo_le_inputMutualInfo_sideChannel₁ W p₁ p₂) hη1
  have b2 := mul_exp_le hk₂' (condMutualInfo_le_inputMutualInfo_sideChannel₂ W p₁ p₂) hη2
  have hk : ((k₁ : ℝ) - 1) * (k₂ - 1) ≤ Real.exp (n * (R₁ + R₂)) := by
    rw [mul_add, Real.exp_add]
    exact mul_le_mul hk₁' hk₂' hk₂0 (Real.exp_pos _).le
  have b3 := mul_exp_le hk (inputMutualInfo_inputPMF W p₁ p₂).ge hη3
  linarith [hN n hn]

end MAC

namespace MACCode

variable {M₁ M₂ M₁' M₂' A₁ A₂ B : Type*} {n n' : ℕ}

def append (c : MACCode M₁ M₂ A₁ A₂ B n) (c' : MACCode M₁' M₂' A₁ A₂ B n') :
    MACCode (M₁ × M₁') (M₂ × M₂') A₁ A₂ B (n + n') where
  enc₁ m := Fin.append (c.enc₁ m.1) (c'.enc₁ m.2)
  enc₂ m := Fin.append (c.enc₂ m.1) (c'.enc₂ m.2)
  dec y :=
    (((c.dec fun i => y (Fin.castAdd n' i)).1, (c'.dec fun i => y (Fin.natAdd n i)).1),
      ((c.dec fun i => y (Fin.castAdd n' i)).2, (c'.dec fun i => y (Fin.natAdd n i)).2))

def relabel (c : MACCode M₁ M₂ A₁ A₂ B n) (e₁ : M₁ ≃ M₁') (e₂ : M₂ ≃ M₂') :
    MACCode M₁' M₂' A₁ A₂ B n where
  enc₁ m := c.enc₁ (e₁.symm m)
  enc₂ m := c.enc₂ (e₂.symm m)
  dec y := (e₁ (c.dec y).1, e₂ (c.dec y).2)

variable [Fintype B]

theorem errorProb_ne_top [DecidableEq M₁] [DecidableEq M₂] (c : MACCode M₁ M₂ A₁ A₂ B n)
    (W : DMC (A₁ × A₂) B) (m : M₁ × M₂) : c.errorProb W m ≠ ∞ :=
  c.toBlockCode.errorProb_ne_top W m

theorem errorProb_relabel [DecidableEq M₁] [DecidableEq M₂] [DecidableEq M₁'] [DecidableEq M₂']
    (c : MACCode M₁ M₂ A₁ A₂ B n) (e₁ : M₁ ≃ M₁') (e₂ : M₂ ≃ M₂') (W : DMC (A₁ × A₂) B)
    (m : M₁ × M₂) : (c.relabel e₁ e₂).errorProb W (e₁ m.1, e₂ m.2) = c.errorProb W m := by
  simp only [errorProb, relabel, Equiv.symm_apply_apply, Prod.mk.injEq, e₁.apply_eq_iff_eq,
    e₂.apply_eq_iff_eq]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : c.dec y = m
  · simp [h]
  · have h' : ¬((c.dec y).1 = m.1 ∧ (c.dec y).2 = m.2) := fun h' => h (Prod.ext h'.1 h'.2)
    rw [ite_eq_right_iff.2 fun h'' => absurd h'' h, ite_eq_right_iff.2 fun h'' => absurd h'' h']

theorem avgError_relabel [Fintype M₁] [Fintype M₂] [Fintype M₁'] [Fintype M₂'] [DecidableEq M₁]
    [DecidableEq M₂] [DecidableEq M₁'] [DecidableEq M₂'] (c : MACCode M₁ M₂ A₁ A₂ B n)
    (e₁ : M₁ ≃ M₁') (e₂ : M₂ ≃ M₂') (W : DMC (A₁ × A₂) B) :
    (c.relabel e₁ e₂).avgError W = c.avgError W := by
  rw [avgError, avgError, Fintype.card_congr e₁, Fintype.card_congr e₂,
    ← (e₁.prodCongr e₂).sum_comp]
  simp only [Equiv.prodCongr_apply, Prod.map, errorProb_relabel]

theorem sum_errorProb_toReal [Fintype M₁] [Fintype M₂] [Nonempty M₁] [Nonempty M₂]
    [DecidableEq M₁] [DecidableEq M₂] (c : MACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) :
    ∑ m, (c.errorProb W m).toReal =
      Fintype.card M₁ * Fintype.card M₂ * (c.avgError W).toReal := by
  have hK : (0 : ℝ) < Fintype.card M₁ * Fintype.card M₂ := by
    have := Fintype.card_pos (α := M₁)
    have := Fintype.card_pos (α := M₂)
    positivity
  rw [avgError, ENNReal.toReal_div, ENNReal.toReal_sum fun m _ => c.errorProb_ne_top W m,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast, mul_div_cancel₀ _ hK.ne']

theorem avgError_ne_top [Fintype M₁] [Fintype M₂] [Nonempty M₁] [Nonempty M₂] [DecidableEq M₁]
    [DecidableEq M₂] (c : MACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) : c.avgError W ≠ ∞ := by
  rw [← avgError_toBlockCode]
  refine ENNReal.div_ne_top (ENNReal.sum_ne_top.2 fun m _ => c.errorProb_ne_top W m) ?_
  simp [Fintype.card_ne_zero]

private lemma ite_mul_le {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {d m : α} {d' m' : β} {g t : γ} (hg : g = t ↔ d = m ∧ d' = m') (P P' : ℝ≥0∞) :
    (if g = t then 0 else P * P') ≤
      (if d = m then 0 else P) * P' + P * if d' = m' then 0 else P' := by
  by_cases h : d = m <;> by_cases h' : d' = m' <;> simp [hg, h, h']

theorem errorProb_append_le [DecidableEq M₁] [DecidableEq M₂] [DecidableEq M₁'] [DecidableEq M₂']
    (c : MACCode M₁ M₂ A₁ A₂ B n) (c' : MACCode M₁' M₂' A₁ A₂ B n') (W : DMC (A₁ × A₂) B)
    (m : (M₁ × M₁') × (M₂ × M₂')) :
    (c.append c').errorProb W m ≤ c.errorProb W (m.1.1, m.2.1) + c'.errorProb W (m.1.2, m.2.2) := by
  obtain ⟨⟨m₁, m₁'⟩, ⟨m₂, m₂'⟩⟩ := m
  rw [errorProb, ← (Fin.appendEquiv n n').sum_comp, Fintype.sum_prod_type]
  have hb : ∀ (y : Fin n → B) (y' : Fin n' → B),
      DMC.blockProb W (fun i => ((c.append c').enc₁ (m₁, m₁') i, (c.append c').enc₂ (m₂, m₂') i))
        (Fin.appendEquiv n n' (y, y')) =
      DMC.blockProb W (fun i => (c.enc₁ m₁ i, c.enc₂ m₂ i)) y *
        DMC.blockProb W (fun i => (c'.enc₁ m₁' i, c'.enc₂ m₂' i)) y' := by
    intro y y'
    simp [DMC.blockProb, append, Fin.prod_univ_add]
  have hd : ∀ (y : Fin n → B) (y' : Fin n' → B),
      (c.append c').dec (Fin.appendEquiv n n' (y, y')) =
        (((c.dec y).1, (c'.dec y').1), ((c.dec y).2, (c'.dec y').2)) := by
    intro y y'
    simp [append]
  calc _ ≤ ∑ y : Fin n → B, ∑ y' : Fin n' → B,
        ((if c.dec y = (m₁, m₂) then 0
          else DMC.blockProb W (fun i => (c.enc₁ m₁ i, c.enc₂ m₂ i)) y) *
          DMC.blockProb W (fun i => (c'.enc₁ m₁' i, c'.enc₂ m₂' i)) y' +
        DMC.blockProb W (fun i => (c.enc₁ m₁ i, c.enc₂ m₂ i)) y *
          if c'.dec y' = (m₁', m₂') then 0
          else DMC.blockProb W (fun i => (c'.enc₁ m₁' i, c'.enc₂ m₂' i)) y') := by
        refine sum_le_sum fun y _ => sum_le_sum fun y' _ => ?_
        rw [hb, hd]
        exact ite_mul_le (by simp only [Prod.ext_iff]; tauto) _ _
    _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, ← sum_mul, DMC.sum_blockProb_eq_one, mul_one,
          one_mul]
        rfl

theorem avgError_append_le [Fintype M₁] [Fintype M₂] [Fintype M₁'] [Fintype M₂'] [Nonempty M₁]
    [Nonempty M₂] [Nonempty M₁'] [Nonempty M₂'] [DecidableEq M₁] [DecidableEq M₂]
    [DecidableEq M₁'] [DecidableEq M₂'] (c : MACCode M₁ M₂ A₁ A₂ B n)
    (c' : MACCode M₁' M₂' A₁ A₂ B n') (W : DMC (A₁ × A₂) B) :
    (c.append c').avgError W ≤ c.avgError W + c'.avgError W := by
  rw [← avgError_toBlockCode, ← ENNReal.ofReal_toReal (c.avgError_ne_top W),
    ← ENNReal.ofReal_toReal (c'.avgError_ne_top W),
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  refine BlockCode.avgError_le_ofReal _ W ?_
  have h1 := c.sum_errorProb_toReal W
  have h2 := c'.sum_errorProb_toReal W
  have hpt : ∀ m : (M₁ × M₁') × (M₂ × M₂'), ((c.append c').errorProb W m).toReal ≤
      (c.errorProb W (m.1.1, m.2.1)).toReal + (c'.errorProb W (m.1.2, m.2.2)).toReal := by
    intro m
    rw [← ENNReal.toReal_add (c.errorProb_ne_top W _) (c'.errorProb_ne_top W _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨c.errorProb_ne_top W _,
      c'.errorProb_ne_top W _⟩) (c.errorProb_append_le c' W m)
  calc ∑ m, ((c.append c').toBlockCode.errorProb W m).toReal
      ≤ ∑ m : (M₁ × M₁') × (M₂ × M₂'),
          ((c.errorProb W (m.1.1, m.2.1)).toReal + (c'.errorProb W (m.1.2, m.2.2)).toReal) :=
        sum_le_sum fun m _ => hpt m
    _ = Fintype.card M₁' * Fintype.card M₂' * ∑ m, (c.errorProb W m).toReal +
        Fintype.card M₁ * Fintype.card M₂ * ∑ m, (c'.errorProb W m).toReal := by
        simp only [sum_add_distrib, Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul,
          mul_sum]
        rw [sum_comm (s := univ (α := M₁')), sum_comm (s := univ (α := M₁))]
        simp only [← mul_sum]
        conv_lhs => rw [sum_comm (s := univ (α := M₂)), sum_comm (s := univ (α := M₂'))]
        ring
    _ = _ := by
        rw [h1, h2, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
        push_cast
        ring

end MACCode

namespace MAC

variable {A₁ A₂ B : Type*} [Fintype B]

theorem Achievable.mono {W : DMC (A₁ × A₂) B} {R₁ R₂ R₁' R₂' : ℝ} (h : Achievable W R₁ R₂)
    (h₁ : R₁' ≤ R₁) (h₂ : R₂' ≤ R₂) : Achievable W R₁' R₂' := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hn
  exact ⟨k₁, k₂, (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg n))).trans hk₁,
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg n))).trans hk₂, c, hc⟩

theorem Achievable.max_zero {W : DMC (A₁ × A₂) B} {R₁ R₂ : ℝ} (h : Achievable W R₁ R₂) :
    Achievable W (max R₁ 0) (max R₂ 0) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hn
  exact ⟨k₁, k₂, exp_mul_max_le hk₁, exp_mul_max_le hk₂, c, hc⟩

theorem mem_closure_achievableRegion (W : DMC (A₁ × A₂) B) {R : ℝ × ℝ} (h1 : 0 ≤ R.1)
    (h2 : 0 ≤ R.2) (h : ∀ δ > 0, Achievable W (R.1 - δ) (R.2 - δ)) :
    R ∈ closure (achievableRegion W) := by
  rw [Metric.mem_closure_iff]
  intro η hη
  have key : ∀ x : ℝ, 0 ≤ x → dist x (max (x - η / 2) 0) < η := by
    intro x hx
    rw [Real.dist_eq]
    rcases le_total (x - η / 2) 0 with h | h
    · rw [max_eq_right h, sub_zero, abs_of_nonneg hx]
      linarith
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]
      linarith
  refine ⟨(max (R.1 - η / 2) 0, max (R.2 - η / 2) 0),
    ⟨le_max_right _ _, le_max_right _ _, (h (η / 2) (by positivity)).max_zero⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨key _ h1, key _ h2⟩

private lemma exists_code_of_eq {M₁ M₂ : Type*} [Fintype M₁] [Fintype M₂] [DecidableEq M₁]
    [DecidableEq M₂] {W : DMC (A₁ × A₂) B} {ε : ℝ≥0∞} {n m : ℕ} (h : n = m)
    (hc : ∃ c : MACCode M₁ M₂ A₁ A₂ B n, c.avgError W ≤ ε) :
    ∃ c : MACCode M₁ M₂ A₁ A₂ B m, c.avgError W ≤ ε := h ▸ hc

theorem Achievable.timeSharing {W : DMC (A₁ × A₂) B} {R₁ R₂ R₁' R₂' : ℝ}
    (h : Achievable W R₁ R₂) (h' : Achievable W R₁' R₂') {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) {δ : ℝ} (hδ : 0 < δ) :
    Achievable W (a * R₁ + b * R₁' - δ) (a * R₂ + b * R₂' - δ) := by
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    exact h'.mono (by linarith) (by linarith)
  rcases hb.eq_or_lt with rfl | hb'
  · obtain rfl : a = 1 := by linarith
    exact h.mono (by linarith) (by linarith)
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨N', hN'⟩ := h' (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (max (N / a) (N' / b)) ((|R₁ - R₁'| + |R₂ - R₂'|) / δ))
  refine ⟨N₀, fun n hn => ?_⟩
  have hn' : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hNa : (N : ℝ) < a * n := by
    have := (le_max_left _ _).trans ((le_max_left _ _).trans hN₀.le)
    rw [div_le_iff₀ ha'] at this
    nlinarith [le_max_left (max (N / a) (N' / b)) ((|R₁ - R₁'| + |R₂ - R₂'|) / δ),
      le_max_left (N / a) (N' / b), (div_lt_iff₀ ha').1 (((le_max_left _ _).trans
        (le_max_left _ _)).trans_lt (hN₀.trans_le hn'))]
  have hNb : (N' : ℝ) < b * n := (div_lt_iff₀' hb').1 (((le_max_right _ _).trans
    (le_max_left _ _)).trans_lt (hN₀.trans_le hn'))
  have hnδ : |R₁ - R₁'| + |R₂ - R₂'| < n * δ := (div_lt_iff₀ hδ).1 ((le_max_right _ _).trans_lt
    (hN₀.trans_le hn'))
  set n₁ := ⌊a * n⌋₊ with hn₁
  have han : 0 ≤ a * n := by positivity
  have hfl : (n₁ : ℝ) ≤ a * n := Nat.floor_le han
  have hfl' : a * n < n₁ + 1 := Nat.lt_floor_add_one _
  have hn₁n : n₁ ≤ n := by
    have : (n₁ : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hn₁N : N ≤ n₁ := Nat.le_floor hNa.le
  have hn₂N : N' ≤ n - n₁ := by
    have : (N' : ℝ) + n₁ ≤ n := by nlinarith
    have : N' + n₁ ≤ n := by exact_mod_cast this
    omega
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n₁ hn₁N
  obtain ⟨k₁', k₂', hk₁', hk₂', c', hc'⟩ := hN' (n - n₁) hn₂N
  have hcast : ((n - n₁ : ℕ) : ℝ) = n - n₁ := Nat.cast_sub hn₁n
  have hrate : ∀ {R R' : ℝ} {k k' : ℕ}, Real.exp (n₁ * R) ≤ k →
      Real.exp (((n - n₁ : ℕ) : ℝ) * R') ≤ k' → |R - R'| < n * δ →
      Real.exp (n * (a * R + b * R' - δ)) ≤ ((k * k' : ℕ) : ℝ) := by
    intro R R' k k' hk hk' hRR
    rw [Nat.cast_mul]
    refine le_trans ?_ (mul_le_mul hk hk' (Real.exp_pos _).le (Nat.cast_nonneg _))
    rw [← Real.exp_add, hcast]
    refine Real.exp_le_exp.2 ?_
    have hθ0 : 0 ≤ a * n - n₁ := by linarith
    have hθ1 : a * n - n₁ ≤ 1 := by linarith
    have habs := le_abs_self (R - R')
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_le_mul_of_nonneg_left habs hθ0,
      mul_le_mul_of_nonneg_right hθ1 (abs_nonneg (R - R'))]
  refine ⟨k₁ * k₁', k₂ * k₂', hrate hk₁ hk₁' (by linarith [abs_nonneg (R₂ - R₂')]),
    hrate hk₂ hk₂' (by linarith [abs_nonneg (R₁ - R₁')]), ?_⟩
  have hk0 : ∀ {R : ℝ} {m k : ℕ}, Real.exp (m * R) ≤ k → 0 < k := fun hk =>
    Nat.cast_pos.1 ((Real.exp_pos _).trans_le hk)
  have : NeZero k₁ := ⟨(hk0 hk₁).ne'⟩
  have : NeZero k₂ := ⟨(hk0 hk₂).ne'⟩
  have : NeZero k₁' := ⟨(hk0 hk₁').ne'⟩
  have : NeZero k₂' := ⟨(hk0 hk₂').ne'⟩
  refine exists_code_of_eq (Nat.add_sub_cancel' hn₁n)
    ⟨(c.append c').relabel finProdFinEquiv finProdFinEquiv, ?_⟩
  rw [MACCode.avgError_relabel]
  calc _ ≤ c.avgError W + c'.avgError W := c.avgError_append_le c' W
    _ ≤ ε / 2 + ε / 2 := add_le_add hc hc'
    _ = ε := ENNReal.add_halves ε

theorem convex_closure_achievableRegion (W : DMC (A₁ × A₂) B) :
    Convex ℝ (closure (achievableRegion W)) := by
  have key : ∀ x ∈ achievableRegion W, ∀ y ∈ achievableRegion W, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → a • x + b • y ∈ closure (achievableRegion W) := by
    rintro x ⟨hx1, hx2, hx⟩ y ⟨hy1, hy2, hy⟩ a b ha hb hab
    refine mem_closure_achievableRegion W ?_ ?_ fun δ hδ => ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      positivity
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      positivity
    · simpa using hx.timeSharing hy ha hb hab hδ
  intro x hx y hy a b ha hb hab
  have hf : Continuous (Function.uncurry fun x y : ℝ × ℝ => a • x + b • y) :=
    (show Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) => a • p.1 + b • p.2 from
      (continuous_fst.const_smul a).add (continuous_snd.const_smul b))
  have h := map_mem_closure₂ hf hx hy fun x' hx' y' hy' => key x' hx' y' hy' a b ha hb hab
  rwa [closure_closure] at h

variable [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [MeasurableSpace B] [MeasurableSingletonClass B]

theorem pentagon_subset_closure_achievableRegion (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁)
    (p₂ : PMF A₂) : pentagon W p₁ p₂ ⊆ closure (achievableRegion W) := by
  rintro R ⟨h1, h2, h3, h4, h5⟩
  exact mem_closure_achievableRegion W h1 h2 fun δ hδ =>
    achievable_of_lt W p₁ p₂ (by linarith) (by linarith) (by linarith)

theorem capacityRegion_subset_closure_achievableRegion (W : DMC (A₁ × A₂) B) :
    capacityRegion W ⊆ closure (achievableRegion W) :=
  closure_minimal (convexHull_min (Set.iUnion₂_subset fun p₁ p₂ =>
    pentagon_subset_closure_achievableRegion W p₁ p₂) (convex_closure_achievableRegion W))
    isClosed_closure

end MAC

end Meat
