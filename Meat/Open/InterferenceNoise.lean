import Meat.Open.Interference

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace IC

section Channels

variable {A₁ A₂ B₁ B₂ : Type*}

noncomputable def noiseChannel₁ (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₂ : PMF A₂) : DMC A₁ B₁ :=
  fun a₁ => p₂.bind fun a₂ => out₁ W (a₁, a₂)

noncomputable def noiseChannel₂ (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁) : DMC A₂ B₂ :=
  fun a₂ => p₁.bind fun a₁ => out₂ W (a₁, a₂)

variable [Fintype A₁] [MeasurableSpace A₁] [Fintype A₂] [MeasurableSpace A₂]
  [Fintype B₁] [MeasurableSpace B₁] [Fintype B₂] [MeasurableSpace B₂]

noncomputable def noiseRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧
    R.1 ≤ I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 ; MAC.jointMeasure (out₁ W) p₁ p₂] ∧
    R.2 ≤ I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 ; MAC.jointMeasure (out₂ W) p₁ p₂]}

noncomputable def timeDivisionRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ (⋃ p₁ : PMF A₁, ⋃ p₂ : PMF A₂, noiseRegion W p₁ p₂))

end Channels

section Letter

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

omit [Fintype A₂] [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂] in
private lemma mutualInfo₁_eq [Finite A₂] (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 ; MAC.jointMeasure (out₁ W) p₁ p₂] =
      (noiseChannel₁ W p₂).inputMutualInfo p₁ := by
  have hm : (MAC.jointMeasure (out₁ W) p₁ p₂).map (fun ω => (ω.1, ω.2.2)) =
      (noiseChannel₁ W p₂).jointMeasure p₁ := by
    have := Fintype.ofFinite A₂
    rw [MAC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _),
      DMC.jointMeasure_eq_toMeasure]
    congr 1
    simp only [MAC.jointPMF, DMC.jointPMF, noiseChannel₁, PMF.map_bind, PMF.map_comp]
    rfl
  rw [DMC.inputMutualInfo, ← hm, mutualInfo_map _ (measurable_of_finite _) measurable_fst
    measurable_snd]
  rfl

omit [Fintype A₁] [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁] in
private lemma mutualInfo₂_eq [Finite A₁] (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 ; MAC.jointMeasure (out₂ W) p₁ p₂] =
      (noiseChannel₂ W p₁).inputMutualInfo p₂ := by
  have hm : (MAC.jointMeasure (out₂ W) p₁ p₂).map (fun ω => (ω.2.1, ω.2.2)) =
      (noiseChannel₂ W p₁).jointMeasure p₂ := by
    have := Fintype.ofFinite A₁
    rw [MAC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _),
      DMC.jointMeasure_eq_toMeasure]
    congr 1
    simp only [MAC.jointPMF, DMC.jointPMF, noiseChannel₂, PMF.map_bind, PMF.map_comp]
    exact PMF.bind_comm _ _ _
  rw [DMC.inputMutualInfo, ← hm, mutualInfo_map _ (measurable_of_finite _) measurable_fst
    measurable_snd]
  rfl

end Letter

section Coding

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂]

omit [Fintype A₁] [Fintype B₁] [Fintype B₂] in
private lemma sum_iidProb_mul_blockProb₁ {n : ℕ} (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₂ : PMF A₂)
    (x₁ : Fin n → A₁) (y : Fin n → B₁) :
    ∑ x : Fin n → A₂, iidProb p₂ x * (DMC.blockProb (out₁ W) (fun i => (x₁ i, x i)) y).toReal =
      (DMC.blockProb (noiseChannel₁ W p₂) x₁ y).toReal := by
  simp only [iidProb, DMC.blockProb, ENNReal.toReal_prod, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a => (p₂ a).toReal * (out₁ W (x₁ i, a) (y i)).toReal)]
  refine prod_congr rfl fun i _ => ?_
  rw [noiseChannel₁, PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  simp only [ENNReal.toReal_mul]

omit [Fintype A₂] [Fintype B₁] [Fintype B₂] in
private lemma sum_iidProb_mul_blockProb₂ {n : ℕ} (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁)
    (x₂ : Fin n → A₂) (y : Fin n → B₂) :
    ∑ x : Fin n → A₁, iidProb p₁ x * (DMC.blockProb (out₂ W) (fun i => (x i, x₂ i)) y).toReal =
      (DMC.blockProb (noiseChannel₂ W p₁) x₂ y).toReal := by
  simp only [iidProb, DMC.blockProb, ENNReal.toReal_prod, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a => (p₁ a).toReal * (out₂ W (a, x₂ i) (y i)).toReal)]
  refine prod_congr rfl fun i _ => ?_
  rw [noiseChannel₂, PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  simp only [ENNReal.toReal_mul]

omit [Fintype A₁] [Fintype A₂] in
private lemma errorProb_le_add {M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂] {n : ℕ}
    (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n) (W : DMC (A₁ × A₂) (B₁ × B₂)) (m : M₁ × M₂) :
    (c.errorProb W m).toReal ≤
      ∑ y₁, (if c.dec₁ y₁ = m.1 then 0 else 1) *
        (DMC.blockProb (out₁ W) (fun i => (c.enc₁ m.1 i, c.enc₂ m.2 i)) y₁).toReal +
      ∑ y₂, (if c.dec₂ y₂ = m.2 then 0 else 1) *
        (DMC.blockProb (out₂ W) (fun i => (c.enc₁ m.1 i, c.enc₂ m.2 i)) y₂).toReal := by
  set x : Fin n → A₁ × A₂ := fun i => (c.enc₁ m.1 i, c.enc₂ m.2 i)
  have h : c.errorProb W m ≤
      ∑ y₁, (if c.dec₁ y₁ = m.1 then 0 else 1) * DMC.blockProb (out₁ W) x y₁ +
      ∑ y₂, (if c.dec₂ y₂ = m.2 then 0 else 1) * DMC.blockProb (out₂ W) x y₂ := by
    rw [← sum_mul_blockProb_out₁ W x (fun y₁ => if c.dec₁ y₁ = m.1 then 0 else 1),
      ← sum_mul_blockProb_out₂ W x (fun y₂ => if c.dec₂ y₂ = m.2 then 0 else 1),
      ← sum_add_distrib, ICCode.errorProb]
    refine sum_le_sum fun y _ => ?_
    by_cases a : c.dec₁ (fun i => (y i).1) = m.1 <;> by_cases b : c.dec₂ (fun i => (y i).2) = m.2
    · have : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) = m := Prod.ext a b
      rw [ite_eq_left_of_eq_true _ _ (eq_true this)]
      exact zero_le
    · have : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) ≠ m :=
        fun h => b (congrArg Prod.snd h)
      rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
      simp [a, b, x]
    · have : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) ≠ m :=
        fun h => a (congrArg Prod.fst h)
      rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
      simp [a, b, x]
    · have : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) ≠ m :=
        fun h => a (congrArg Prod.fst h)
      rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
      simp only [a, b, ite_false, one_mul]
      exact le_self_add (b := DMC.blockProb W x y)
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun y _ =>
    ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _),
    ENNReal.sum_ne_top.2 fun y _ =>
    ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _)⟩) h).trans_eq ?_
  rw [ENNReal.toReal_add (ENNReal.sum_ne_top.2 fun y _ =>
    ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _))
    (ENNReal.sum_ne_top.2 fun y _ =>
    ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _)),
    ENNReal.toReal_sum fun y _ =>
      ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _),
    ENNReal.toReal_sum fun y _ =>
      ENNReal.mul_ne_top (by split_ifs <;> simp) (DMC.blockProb_ne_top _ _ _)]
  simp only [ENNReal.toReal_mul, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ENNReal.toReal_one]

private lemma errorProb_typicalCode_toReal {M A B : Type*} [Fintype B] [DecidableEq M] {n : ℕ}
    (C : M → Fin n → A) (J : Finset ((Fin n → A) × (Fin n → B))) (m₀ m : M) (V : DMC A B) :
    ((BlockCode.typicalCode C J m₀).errorProb V m).toReal =
      ∑ y, (if BlockCode.typicalDecoder C J m₀ y = m then 0 else 1) *
        (DMC.blockProb V (C m) y).toReal := by
  rw [BlockCode.errorProb, ENNReal.toReal_sum fun y _ => by
    split_ifs <;> simp [DMC.blockProb_ne_top]]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : BlockCode.typicalDecoder C J m₀ y = m <;>
    simp [BlockCode.typicalCode, h]

private noncomputable def noiseCode {M₁ M₂ : Type*} {n : ℕ} (C₁ : M₁ → Fin n → A₁)
    (C₂ : M₂ → Fin n → A₂) (J₁ : Finset ((Fin n → A₁) × (Fin n → B₁)))
    (J₂ : Finset ((Fin n → A₂) × (Fin n → B₂))) (m₀ : M₁ × M₂) :
    ICCode M₁ M₂ A₁ A₂ B₁ B₂ n :=
  ⟨C₁, C₂, BlockCode.typicalDecoder C₁ J₁ m₀.1, BlockCode.typicalDecoder C₂ J₂ m₀.2⟩

variable [MeasurableSpace A₁] [MeasurableSpace A₂] [MeasurableSpace B₁] [MeasurableSpace B₂]

private lemma exists_noiseCode_avgError_le {M₁ M₂ : Type*} [Fintype M₁] [Fintype M₂]
    [DecidableEq M₁] [DecidableEq M₂] {n : ℕ} (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁)
    (p₂ : PMF A₂) (ε : ℝ) (m₀ : M₁ × M₂) :
    ∃ (C₁ : M₁ → Fin n → A₁) (C₂ : M₂ → Fin n → A₂),
      (noiseCode C₁ C₂ (jointlyTypicalSet (DMC.jointPMF (noiseChannel₁ W p₂) p₁) n ε)
        (jointlyTypicalSet (DMC.jointPMF (noiseChannel₂ W p₁) p₂) n ε) m₀).avgError W ≤
      ENNReal.ofReal
        (((1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (noiseChannel₁ W p₂) p₁) n ε,
            iidProb (DMC.jointPMF (noiseChannel₁ W p₂) p₁) (fun i => (xy.1 i, xy.2 i))) +
          (Fintype.card M₁ - 1) *
            Real.exp (-(n * ((noiseChannel₁ W p₂).inputMutualInfo p₁ - 3 * ε)))) +
        ((1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (noiseChannel₂ W p₁) p₂) n ε,
            iidProb (DMC.jointPMF (noiseChannel₂ W p₁) p₂) (fun i => (xy.1 i, xy.2 i))) +
          (Fintype.card M₂ - 1) *
            Real.exp (-(n * ((noiseChannel₂ W p₁).inputMutualInfo p₂ - 3 * ε))))) := by
  classical
  have : Nonempty (M₁ × M₂) := ⟨m₀⟩
  set J₁ := jointlyTypicalSet (DMC.jointPMF (noiseChannel₁ W p₂) p₁) n ε
  set J₂ := jointlyTypicalSet (DMC.jointPMF (noiseChannel₂ W p₁) p₂) n ε
  set β₁ := (1 - ∑ xy ∈ J₁, iidProb (DMC.jointPMF (noiseChannel₁ W p₂) p₁)
      (fun i => (xy.1 i, xy.2 i))) + (Fintype.card M₁ - 1) *
    Real.exp (-(n * ((noiseChannel₁ W p₂).inputMutualInfo p₁ - 3 * ε)))
  set β₂ := (1 - ∑ xy ∈ J₂, iidProb (DMC.jointPMF (noiseChannel₂ W p₁) p₂)
      (fun i => (xy.1 i, xy.2 i))) + (Fintype.card M₂ - 1) *
    Real.exp (-(n * ((noiseChannel₂ W p₁).inputMutualInfo p₂ - 3 * ε)))
  set w₁ := fun C : M₁ → Fin n → A₁ => ∏ j, iidProb p₁ (C j)
  set w₂ := fun C : M₂ → Fin n → A₂ => ∏ j, iidProb p₂ (C j)
  have hw₁ : ∀ C, 0 ≤ w₁ C := fun C => prod_nonneg fun j _ => iidProb_nonneg _ _
  have hw₂ : ∀ C, 0 ≤ w₂ C := fun C => prod_nonneg fun j _ => iidProb_nonneg _ _
  have h1₁ : ∑ C, w₁ C = 1 := sum_prod _ fun _ => sum_iidProb p₁ n
  have h1₂ : ∑ C, w₂ C = 1 := sum_prod _ fun _ => sum_iidProb p₂ n
  have r₁ : ∀ (m : M₁ × M₂), ∑ C₁, w₁ C₁ * ∑ C₂, w₂ C₂ * ∑ y₁,
      (if BlockCode.typicalDecoder C₁ J₁ m₀.1 y₁ = m.1 then 0 else 1) *
        (DMC.blockProb (out₁ W) (fun i => (C₁ m.1 i, C₂ m.2 i)) y₁).toReal ≤ β₁ := by
    intro m
    refine le_trans (le_of_eq (sum_congr rfl fun C₁ _ => ?_))
      (DMC.sum_errorProb_typicalCode_le (noiseChannel₁ W p₂) p₁ ε m₀.1 m.1)
    rw [errorProb_typicalCode_toReal]
    congr 1
    simp only [w₂]
    rw [sum_prod_mul_apply (fun _ x => iidProb p₂ x) (fun _ => sum_iidProb p₂ n)
      (fun x : Fin n → A₂ => ∑ y, (if BlockCode.typicalDecoder C₁ J₁ m₀.1 y = m.1 then 0 else 1) *
        (DMC.blockProb (out₁ W) (fun i => (C₁ m.1 i, x i)) y).toReal) m.2]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [← sum_iidProb_mul_blockProb₁, mul_sum]
    exact sum_congr rfl fun x _ => by ring
  have r₂ : ∀ (m : M₁ × M₂), ∑ C₂, w₂ C₂ * ∑ C₁, w₁ C₁ * ∑ y₂,
      (if BlockCode.typicalDecoder C₂ J₂ m₀.2 y₂ = m.2 then 0 else 1) *
        (DMC.blockProb (out₂ W) (fun i => (C₁ m.1 i, C₂ m.2 i)) y₂).toReal ≤ β₂ := by
    intro m
    refine le_trans (le_of_eq (sum_congr rfl fun C₂ _ => ?_))
      (DMC.sum_errorProb_typicalCode_le (noiseChannel₂ W p₁) p₂ ε m₀.2 m.2)
    rw [errorProb_typicalCode_toReal]
    congr 1
    simp only [w₁]
    rw [sum_prod_mul_apply (fun _ x => iidProb p₁ x) (fun _ => sum_iidProb p₁ n)
      (fun x : Fin n → A₁ => ∑ y, (if BlockCode.typicalDecoder C₂ J₂ m₀.2 y = m.2 then 0 else 1) *
        (DMC.blockProb (out₂ W) (fun i => (x i, C₂ m.2 i)) y).toReal) m.1]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [← sum_iidProb_mul_blockProb₂, mul_sum]
    exact sum_congr rfl fun x _ => by ring
  have hw : ∀ C : (M₁ → Fin n → A₁) × (M₂ → Fin n → A₂), 0 ≤ w₁ C.1 * w₂ C.2 :=
    fun C => mul_nonneg (hw₁ _) (hw₂ _)
  have h1 : ∑ C : (M₁ → Fin n → A₁) × (M₂ → Fin n → A₂), w₁ C.1 * w₂ C.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, h1₂, mul_one, h1₁]
  have hm : ∀ m : M₁ × M₂, ∑ C : (M₁ → Fin n → A₁) × (M₂ → Fin n → A₂), w₁ C.1 * w₂ C.2 *
      ((noiseCode C.1 C.2 J₁ J₂ m₀).errorProb W m).toReal ≤ β₁ + β₂ := by
    intro m
    calc _ ≤ ∑ C : (M₁ → Fin n → A₁) × (M₂ → Fin n → A₂), w₁ C.1 * w₂ C.2 * ((∑ y₁,
          (if BlockCode.typicalDecoder C.1 J₁ m₀.1 y₁ = m.1 then 0 else 1) *
            (DMC.blockProb (out₁ W) (fun i => (C.1 m.1 i, C.2 m.2 i)) y₁).toReal) +
          ∑ y₂, (if BlockCode.typicalDecoder C.2 J₂ m₀.2 y₂ = m.2 then 0 else 1) *
            (DMC.blockProb (out₂ W) (fun i => (C.1 m.1 i, C.2 m.2 i)) y₂).toReal) :=
          sum_le_sum fun C _ => mul_le_mul_of_nonneg_left
            (errorProb_le_add (noiseCode C.1 C.2 J₁ J₂ m₀) W m) (hw C)
      _ = (∑ C₁, w₁ C₁ * ∑ C₂, w₂ C₂ * ∑ y₁,
          (if BlockCode.typicalDecoder C₁ J₁ m₀.1 y₁ = m.1 then 0 else 1) *
            (DMC.blockProb (out₁ W) (fun i => (C₁ m.1 i, C₂ m.2 i)) y₁).toReal) +
          ∑ C₂, w₂ C₂ * ∑ C₁, w₁ C₁ * ∑ y₂,
          (if BlockCode.typicalDecoder C₂ J₂ m₀.2 y₂ = m.2 then 0 else 1) *
            (DMC.blockProb (out₂ W) (fun i => (C₁ m.1 i, C₂ m.2 i)) y₂).toReal := by
          simp only [mul_add, sum_add_distrib]
          congr 1
          · rw [Fintype.sum_prod_type]
            refine sum_congr rfl fun C₁ _ => ?_
            rw [mul_sum]
            exact sum_congr rfl fun C₂ _ => by ring
          · rw [Fintype.sum_prod_type, sum_comm]
            refine sum_congr rfl fun C₂ _ => ?_
            rw [mul_sum]
            exact sum_congr rfl fun C₁ _ => by ring
      _ ≤ β₁ + β₂ := add_le_add (r₁ m) (r₂ m)
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le (w := fun C : (M₁ → Fin n → A₁) ×
      (M₂ → Fin n → A₂) => w₁ C.1 * w₂ C.2)
    (f := fun C => ∑ m, ((noiseCode C.1 C.2 J₁ J₂ m₀).errorProb W m).toReal)
    (t := Fintype.card (M₁ × M₂) * (β₁ + β₂)) hw h1 (by
      simp only [mul_sum]
      rw [sum_comm]
      calc _ ≤ ∑ m : M₁ × M₂, (β₁ + β₂) := sum_le_sum fun m _ => hm m
        _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul])
  refine ⟨C.1, C.2, ?_⟩
  rw [← ICCode.avgError_toMACCode, ← MACCode.avgError_toBlockCode]
  exact BlockCode.avgError_le_ofReal _ W hC

end Coding

section Main

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

theorem achievable_of_lt_noise (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁) (p₂ : PMF A₂)
    {R₁ R₂ : ℝ}
    (h₁ : R₁ < I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 ; MAC.jointMeasure (out₁ W) p₁ p₂])
    (h₂ : R₂ < I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 ;
      MAC.jointMeasure (out₂ W) p₁ p₂]) :
    Achievable W R₁ R₂ := by
  classical
  rw [mutualInfo₁_eq] at h₁
  rw [mutualInfo₂_eq] at h₂
  intro ε hε
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  set I₁ := (noiseChannel₁ W p₂).inputMutualInfo p₁
  set I₂ := (noiseChannel₂ W p₁).inputMutualInfo p₂
  set η := min (I₁ - R₁) (I₂ - R₂) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hη1 : 4 * η ≤ I₁ - R₁ := by rw [hη]; linarith [min_le_left (I₁ - R₁) (I₂ - R₂)]
  have hη2 : 4 * η ≤ I₂ - R₂ := by rw [hη]; linarith [min_le_right (I₁ - R₁) (I₂ - R₂)]
  set q₁ := DMC.jointPMF (noiseChannel₁ W p₂) p₁
  set q₂ := DMC.jointPMF (noiseChannel₂ W p₁) p₂
  have hJ₁ : Tendsto (fun n : ℕ => 1 - ∑ xy ∈ jointlyTypicalSet q₁ n η,
      iidProb q₁ (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_jointlyTypicalSet q₁ hη0)
  have hJ₂ : Tendsto (fun n : ℕ => 1 - ∑ xy ∈ jointlyTypicalSet q₂ n η,
      iidProb q₂ (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_jointlyTypicalSet q₂ hη0)
  have hE := tendsto_exp_nat_mul (neg_neg_of_pos hη0)
  have hsum := (hJ₁.add hJ₂).add (hE.const_mul 2)
  rw [mul_zero, add_zero, add_zero] at hsum
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
  refine ⟨k₁, k₂, Nat.le_ceil _, Nat.le_ceil _, ?_⟩
  obtain ⟨C₁, C₂, hC⟩ := exists_noiseCode_avgError_le (n := n) W p₁ p₂ η
    ((⟨0, hk₁⟩, ⟨0, hk₂⟩) : Fin k₁ × Fin k₂)
  refine ⟨_, hC.trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hδε.le)⟩
  rw [Fintype.card_fin, Fintype.card_fin]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have b : ∀ {k : ℕ} {R I : ℝ}, (k : ℝ) - 1 ≤ Real.exp (n * R) → 4 * η ≤ I - R →
      ((k : ℝ) - 1) * Real.exp (-(n * (I - 3 * η))) ≤ Real.exp (n * (-η)) := by
    intro k R I hk hI
    calc ((k : ℝ) - 1) * Real.exp (-(n * (I - 3 * η)))
        ≤ Real.exp (n * R) * Real.exp (-(n * (I - 3 * η))) :=
          mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
      _ = Real.exp (n * R - n * (I - 3 * η)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (n * (-η)) := Real.exp_le_exp.2 (by nlinarith)
  have b₁ := b hk₁' hη1
  have b₂ := b hk₂' hη2
  linarith [hN n hn]

theorem noiseRegion_subset_closure_achievableRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁)
    (p₂ : PMF A₂) : noiseRegion W p₁ p₂ ⊆ closure (achievableRegion W) := by
  rintro R ⟨h1, h2, h3, h4⟩
  exact mem_closure_achievableRegion W h1 h2 fun δ hδ =>
    achievable_of_lt_noise W p₁ p₂ (by linarith) (by linarith)

theorem timeDivisionRegion_subset_closure_achievableRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    timeDivisionRegion W ⊆ closure (achievableRegion W) :=
  closure_minimal (convexHull_min (Set.iUnion₂_subset fun p₁ p₂ =>
    noiseRegion_subset_closure_achievableRegion W p₁ p₂) (convex_closure_achievableRegion W))
    isClosed_closure

end Main

end IC

end Meat
