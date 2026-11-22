import Meat.Channel.Achievability
import Meat.Channel.Broadcast
import Meat.Shannon.Superposition

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace DMC

variable {V A B B' : Type*}

theorem toReal_blockProb {n : ℕ} (W : DMC A B) (x : Fin n → A) (y : Fin n → B) :
    (blockProb W x y).toReal = ∏ i, (W (x i) (y i)).toReal := by
  simp [blockProb, ENNReal.toReal_prod]

theorem toReal_blockProb_bind [Fintype A] {n : ℕ} (κ : DMC V A) (W : DMC A B) (u : Fin n → V)
    (y : Fin n → B) :
    (blockProb (fun v => (κ v).bind W) u y).toReal =
      ∑ x, (blockProb κ u x).toReal * (blockProb W x y).toReal := by
  have h : ∀ i, (((κ (u i)).bind W) (y i)).toReal =
      ∑ a, (κ (u i) a).toReal * (W a (y i)).toReal := fun i => by
    rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum fun a _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    simp [ENNReal.toReal_mul]
  simp_rw [toReal_blockProb, h, ← prod_mul_distrib]
  exact Fintype.prod_sum _

theorem toReal_blockProb_map [Fintype B] [DecidableEq B'] {n : ℕ} (W : DMC A B) (g : B → B')
    (x : Fin n → A) (y' : Fin n → B') :
    (blockProb (fun a => (W a).map g) x y').toReal =
      ∑ y with (fun i => g (y i)) = y', (blockProb W x y).toReal := by
  simp only [toReal_blockProb, toReal_map_apply]
  rw [prod_univ_sum]
  refine sum_congr ?_ fun _ _ => rfl
  ext y
  simp [Fintype.mem_piFinset, funext_iff]

theorem sum_blockProb_mul_comp [Fintype B] [Fintype B'] {n : ℕ} (W : DMC A B) (g : B → B')
    (x : Fin n → A) (F : (Fin n → B') → ℝ) :
    ∑ y, (blockProb W x y).toReal * F (fun i => g (y i)) =
      ∑ y', (blockProb (fun a => (W a).map g) x y').toReal * F y' := by
  classical
  simp_rw [toReal_blockProb_map, sum_mul]
  rw [← sum_fiberwise univ (fun y : Fin n → B => fun i => g (y i))
    (fun y => (blockProb W x y).toReal * F (fun i => g (y i)))]
  refine sum_congr rfl fun y' _ => sum_congr rfl fun y hy => ?_
  rw [(mem_filter.1 hy).2]

theorem sum_iidProb_jointPMF_mul [Fintype V] [Fintype A] {n : ℕ} (κ : DMC V A) (q : PMF V)
    (F : (Fin n → V) → (Fin n → A) → ℝ) :
    ∑ w : Fin n → V × A, iidProb (jointPMF κ q) w * F (fun i => (w i).1) (fun i => (w i).2) =
      ∑ u, iidProb q u * ∑ x, (blockProb κ u x).toReal * F u x := by
  rw [← Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm
    (fun z : (Fin n → V) × (Fin n → A) => iidProb (jointPMF κ q) (fun i => (z.1 i, z.2 i)) *
      F z.1 z.2) _ fun z => rfl, Fintype.sum_prod_type]
  simp_rw [iidProb_jointPMF, mul_sum, mul_assoc]

end DMC

namespace BCCode

variable {M₁ M₂ A B₁ B₂ : Type*} {n : ℕ}

theorem errorProb_ne_top [Fintype B₁] [Fintype B₂] [DecidableEq M₁] [DecidableEq M₂]
    (c : BCCode M₁ M₂ A B₁ B₂ n) (W : DMC A (B₁ × B₂)) (m : M₁ × M₂) : c.errorProb W m ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun y _ => by split_ifs <;> simp [DMC.blockProb_ne_top]

theorem errorProb_toReal_le [Fintype B₁] [Fintype B₂] [DecidableEq M₁] [DecidableEq M₂]
    (c : BCCode M₁ M₂ A B₁ B₂ n) (W : DMC A (B₁ × B₂)) (m : M₁ × M₂) :
    (c.errorProb W m).toReal ≤
      ∑ y₁, (if c.dec₁ y₁ = m.1 then 0
        else (DMC.blockProb (fun a => (W a).map Prod.fst) (c.enc m) y₁).toReal) +
      ∑ y₂, (if c.dec₂ y₂ = m.2 then 0
        else (DMC.blockProb (fun a => (W a).map Prod.snd) (c.enc m) y₂).toReal) := by
  rw [errorProb, ENNReal.toReal_sum fun y _ => by split_ifs <;> simp [DMC.blockProb_ne_top]]
  have h1 := DMC.sum_blockProb_mul_comp W Prod.fst (c.enc m)
    fun y₁ => if c.dec₁ y₁ = m.1 then (0 : ℝ) else 1
  have h2 := DMC.sum_blockProb_mul_comp W Prod.snd (c.enc m)
    fun y₂ => if c.dec₂ y₂ = m.2 then (0 : ℝ) else 1
  simp only [mul_ite, mul_zero, mul_one] at h1 h2
  rw [← h1, ← h2, ← sum_add_distrib]
  refine sum_le_sum fun y _ => ?_
  have hb : 0 ≤ (DMC.blockProb W (c.enc m) y).toReal := ENNReal.toReal_nonneg
  by_cases h₁ : c.dec₁ (fun i => (y i).1) = m.1 <;> by_cases h₂ : c.dec₂ (fun i => (y i).2) = m.2
  · rw [ite_eq_left (Prod.ext h₁ h₂ : (c.dec₁ (fun i => (y i).1),
      c.dec₂ (fun i => (y i).2)) = m)]
    split_ifs
    simp
  all_goals
    have hne : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) ≠ m := fun h => by
      simp_all [Prod.ext_iff]
    rw [ite_eq_right hne]
    split_ifs
    all_goals linarith

theorem avgError_le_ofReal [Fintype B₁] [Fintype B₂] [Fintype M₁] [Fintype M₂] [DecidableEq M₁]
    [DecidableEq M₂] [Nonempty M₁] [Nonempty M₂] (c : BCCode M₁ M₂ A B₁ B₂ n)
    (W : DMC A (B₁ × B₂)) {δ : ℝ}
    (h : ∑ m, (c.errorProb W m).toReal ≤ Fintype.card M₁ * Fintype.card M₂ * δ) :
    c.avgError W ≤ ENNReal.ofReal δ := by
  have hpos : (0 : ℝ) < Fintype.card M₁ * Fintype.card M₂ :=
    mul_pos (Nat.cast_pos.2 Fintype.card_pos) (Nat.cast_pos.2 Fintype.card_pos)
  have hδ : 0 ≤ δ :=
    (mul_nonneg_iff_of_pos_left hpos).1 ((sum_nonneg fun m _ => ENNReal.toReal_nonneg).trans h)
  have hcard : (Fintype.card M₁ : ℝ≥0∞) * Fintype.card M₂ ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have htop : (Fintype.card M₁ : ℝ≥0∞) * Fintype.card M₂ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
  rw [avgError, ENNReal.div_le_iff hcard htop,
    ← ENNReal.ofReal_toReal (ENNReal.sum_ne_top.2 fun m _ => c.errorProb_ne_top W m),
    ENNReal.toReal_sum fun m _ => c.errorProb_ne_top W m, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul hδ]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end BCCode

namespace BC

variable {V A B₁ B₂ : Type*}

noncomputable def jointPMF (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    PMF (V × A × B₁ × B₂) :=
  pU.bind fun u => (pX u).bind fun a => (W a).map fun y => (u, a, y)

theorem jointMeasure_eq_toMeasure [MeasurableSpace A] [MeasurableSpace B₁] [MeasurableSpace B₂]
    [MeasurableSpace V]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    jointMeasure W pU pX = (jointPMF W pU pX).toMeasure := rfl

noncomputable def channel₁ (W : DMC A (B₁ × B₂)) : DMC A B₁ := fun a => (W a).map Prod.fst

noncomputable def channel₂ (W : DMC A (B₁ × B₂)) : DMC A B₂ := fun a => (W a).map Prod.snd

noncomputable def cloudChannel₁ (W : DMC A (B₁ × B₂)) (pX : V → PMF A) : DMC V B₁ :=
  fun u => (pX u).bind (channel₁ W)

noncomputable def cloudChannel₂ (W : DMC A (B₁ × B₂)) (pX : V → PMF A) : DMC V B₂ :=
  fun u => (pX u).bind (channel₂ W)

noncomputable def law₁ (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    PMF ((V × A) × B₁) :=
  DMC.jointPMF (fun ua : V × A => channel₁ W ua.2) (DMC.jointPMF pX pU)

theorem law₁_eq_map (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    law₁ W pU pX = (jointPMF W pU pX).map fun ω => ((ω.1, ω.2.1), ω.2.2.1) := by
  simp only [law₁, jointPMF, DMC.jointPMF, channel₁, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def]

theorem jointPMF_cloudChannel₂ (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    DMC.jointPMF (cloudChannel₂ W pX) pU = (jointPMF W pU pX).map fun ω => (ω.1, ω.2.2.2) := by
  simp only [cloudChannel₂, jointPMF, DMC.jointPMF, channel₂, PMF.map, PMF.bind_bind,
    PMF.pure_bind, Function.comp_def]

theorem law₁_map_fst (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    (law₁ W pU pX).map Prod.fst = DMC.jointPMF pX pU :=
  DMC.jointPMF_map_fst _ _

theorem law₁_map_cloud (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    (law₁ W pU pX).map (fun ω => ω.1.1) = pU := by
  have h : (fun ω : (V × A) × B₁ => ω.1.1) = Prod.fst ∘ Prod.fst := rfl
  rw [h, ← PMF.map_comp, law₁_map_fst, DMC.jointPMF_map_fst]

theorem law₁_map_cloud_output (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    (law₁ W pU pX).map (fun ω => (ω.1.1, ω.2)) = DMC.jointPMF (cloudChannel₁ W pX) pU := by
  simp only [law₁, cloudChannel₁, DMC.jointPMF, channel₁, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def]

section Info

variable [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B₁]
  [MeasurableSingletonClass B₁] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]
  [MeasurableSpace V] [MeasurableSingletonClass V]

theorem mutualInfo_cloud_eq [Finite A] [Finite B₁] [Fintype B₂] [Fintype V]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    mutualInfo (fun ω : V × A × B₁ × B₂ => ω.1) (fun ω => ω.2.2.2) (jointMeasure W pU pX) =
      (cloudChannel₂ W pX).inputMutualInfo pU := by
  rw [DMC.inputMutualInfo, DMC.jointMeasure_eq_toMeasure, jointPMF_cloudChannel₂,
    ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    mutualInfo_map _ (measurable_of_finite _) measurable_fst measurable_snd]
  rfl

theorem condMutualInfo_eq_law₁ [Fintype A] [Fintype B₁] [Finite B₂] [Fintype V]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    condMutualInfo (fun ω : V × A × B₁ × B₂ => ω.2.1) (fun ω => ω.2.2.1) (fun ω => ω.1)
      (jointMeasure W pU pX) =
      I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
        (law₁ W pU pX).toMeasure] := by
  rw [law₁_eq_map, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (X := fun ω : (V × A) × B₁ => ω.1.2)
      (Y := fun ω => ω.2) (Z := fun ω => ω.1.1) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
  rfl

theorem mutualInfo_eq_law₁ [Fintype A] [Fintype B₁] [Finite B₂] [Finite V]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    mutualInfo (fun ω : V × A × B₁ × B₂ => ω.2.1) (fun ω => ω.2.2.1) (jointMeasure W pU pX) =
      I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 ; (law₁ W pU pX).toMeasure] := by
  rw [law₁_eq_map, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    mutualInfo_map _ (measurable_of_finite _) (X := fun ω : (V × A) × B₁ => ω.1.2)
      (Y := fun ω => ω.2) (measurable_of_finite _) (measurable_of_finite _)]
  rfl

end Info

noncomputable def superpositionCode {M₁ M₂ : Type*} {n : ℕ} (Cu : M₂ → Fin n → V)
    (Cx : M₁ × M₂ → Fin n → A) (J₁ : Finset ((Fin n → V × A) × (Fin n → B₁)))
    (J₂ : Finset ((Fin n → V) × (Fin n → B₂))) (m₀ : M₁ × M₂) : BCCode M₁ M₂ A B₁ B₂ n :=
  ⟨Cx, fun y => (BlockCode.typicalDecoder (fun m i => (Cu m.2 i, Cx m i)) J₁ m₀ y).1,
    BlockCode.typicalDecoder Cu J₂ m₀.2⟩

theorem errorProb_superpositionCode_toReal_le {M₁ M₂ : Type*} {n : ℕ} [Fintype M₁] [Fintype M₂]
    [DecidableEq M₁] [DecidableEq M₂] [DecidableEq V] [DecidableEq A] [Fintype B₁] [Fintype B₂]
    [DecidableEq B₁] (W : DMC A (B₁ × B₂)) (Cu : M₂ → Fin n → V) (Cx : M₁ × M₂ → Fin n → A)
    (J₁ : Finset ((Fin n → V × A) × (Fin n → B₁))) (J₂ : Finset ((Fin n → V) × (Fin n → B₂)))
    (m₀ m : M₁ × M₂) :
    ((superpositionCode Cu Cx J₁ J₂ m₀).errorProb W m).toReal ≤
      ∑ y, (if ((fun i => (Cu m.2 i, Cx m i)), y) ∈ J₁ then 0
        else (DMC.blockProb (channel₁ W) (Cx m) y).toReal) +
      ∑ m' with m'.1 ≠ m.1, ∑ y, (if ((fun i => (Cu m'.2 i, Cx m' i)), y) ∈ J₁ then (1 : ℝ)
        else 0) * (DMC.blockProb (channel₁ W) (Cx m) y).toReal +
      ∑ y, (if BlockCode.typicalDecoder Cu J₂ m₀.2 y = m.2 then 0
        else (DMC.blockProb (channel₂ W) (Cx m) y).toReal) := by
  refine (BCCode.errorProb_toReal_le _ W m).trans (add_le_add ?_ le_rfl)
  rw [← sum_comm, ← sum_add_distrib]
  exact sum_le_sum fun y _ => BlockCode.ite_comp_typicalDecoder_le Prod.fst
    (fun m i => (Cu m.2 i, Cx m i)) J₁ m₀ m y ENNReal.toReal_nonneg

noncomputable def codebookWeight {M₁ M₂ : Type*} [Fintype M₁] [Fintype M₂] {n : ℕ}
    (pU : PMF V) (pX : V → PMF A) (Cu : M₂ → Fin n → V) (Cx : M₁ × M₂ → Fin n → A) : ℝ :=
  (∏ j, iidProb pU (Cu j)) * ∏ m, (DMC.blockProb pX (Cu m.2) (Cx m)).toReal

section Weight

variable {M₁ M₂ : Type*} [Fintype M₁] [Fintype M₂] [DecidableEq M₁] [DecidableEq M₂] {n : ℕ}
  [Fintype V] [Fintype A]

omit [DecidableEq M₁] [DecidableEq M₂] [Fintype V] [Fintype A] in
theorem codebookWeight_nonneg (pU : PMF V) (pX : V → PMF A) (Cu : M₂ → Fin n → V)
    (Cx : M₁ × M₂ → Fin n → A) : 0 ≤ codebookWeight pU pX Cu Cx :=
  mul_nonneg (prod_nonneg fun _ _ => iidProb_nonneg _ _)
    (prod_nonneg fun _ _ => ENNReal.toReal_nonneg)

theorem sum_codebookWeight (pU : PMF V) (pX : V → PMF A) :
    ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A, codebookWeight pU pX Cu Cx = 1 := by
  simp_rw [codebookWeight, ← mul_sum]
  calc _ = ∑ Cu : M₂ → Fin n → V, (∏ j, iidProb pU (Cu j)) * 1 := by
        refine sum_congr rfl fun Cu _ => ?_
        rw [sum_prod (fun (m : M₁ × M₂) (x : Fin n → A) =>
          (DMC.blockProb pX (Cu m.2) x).toReal) fun m => by
          rw [← ENNReal.toReal_sum fun _ _ => DMC.blockProb_ne_top _ _ _,
            DMC.sum_blockProb_eq_one, ENNReal.toReal_one]]
    _ = 1 := by
        simp only [mul_one]
        exact sum_prod (fun _ (u : Fin n → V) => iidProb pU u) (fun _ => sum_iidProb pU n)

theorem sum_codebookWeight_mul_apply (pU : PMF V) (pX : V → PMF A)
    (H : (M₂ → Fin n → V) → (Fin n → A) → ℝ) (m : M₁ × M₂) :
    ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A, codebookWeight pU pX Cu Cx * H Cu (Cx m) =
      ∑ Cu : M₂ → Fin n → V, (∏ j, iidProb pU (Cu j)) *
        ∑ x, (DMC.blockProb pX (Cu m.2) x).toReal * H Cu x := by
  refine sum_congr rfl fun Cu _ => ?_
  simp_rw [codebookWeight, mul_assoc, ← mul_sum]
  rw [sum_prod_mul_apply
    (fun (m : M₁ × M₂) (x : Fin n → A) => (DMC.blockProb pX (Cu m.2) x).toReal)
    (fun m => by rw [← ENNReal.toReal_sum fun _ _ => DMC.blockProb_ne_top _ _ _,
      DMC.sum_blockProb_eq_one, ENNReal.toReal_one]) (H Cu) m]

theorem sum_codebookWeight_mul_apply_mul_apply (pU : PMF V) (pX : V → PMF A)
    (H₁ H₂ : (M₂ → Fin n → V) → (Fin n → A) → ℝ) {m m' : M₁ × M₂} (hm : m' ≠ m) :
    ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A,
      codebookWeight pU pX Cu Cx * (H₁ Cu (Cx m') * H₂ Cu (Cx m)) =
      ∑ Cu : M₂ → Fin n → V, (∏ j, iidProb pU (Cu j)) *
        ((∑ x, (DMC.blockProb pX (Cu m'.2) x).toReal * H₁ Cu x) *
          ∑ x, (DMC.blockProb pX (Cu m.2) x).toReal * H₂ Cu x) := by
  refine sum_congr rfl fun Cu _ => ?_
  simp_rw [codebookWeight, mul_assoc, ← mul_sum]
  rw [sum_prod_mul_apply_mul_apply
    (fun (m : M₁ × M₂) (x : Fin n → A) => (DMC.blockProb pX (Cu m.2) x).toReal)
    (fun m => by rw [← ENNReal.toReal_sum fun _ _ => DMC.blockProb_ne_top _ _ _,
      DMC.sum_blockProb_eq_one, ENNReal.toReal_one]) (H₁ Cu) (H₂ Cu) hm]

end Weight

section Average

variable {M₁ M₂ : Type*} [Fintype M₁] [Fintype M₂] [DecidableEq M₁] [DecidableEq M₂] {n : ℕ}
  [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A] [Fintype B₁] [DecidableEq B₁]
  [Fintype B₂] [DecidableEq B₂]

omit [Fintype B₂] [DecidableEq B₂] in
theorem sum_codebookWeight_mul_miss (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A)
    (J₁ : Finset ((Fin n → V × A) × (Fin n → B₁))) (m : M₁ × M₂) :
    ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A, codebookWeight pU pX Cu Cx *
      ∑ y, (if ((fun i => (Cu m.2 i, Cx m i)), y) ∈ J₁ then 0
        else (DMC.blockProb (channel₁ W) (Cx m) y).toReal) =
      1 - ∑ z ∈ J₁, iidProb (law₁ W pU pX) (fun i => (z.1 i, z.2 i)) := by
  calc _ = ∑ Cu : M₂ → Fin n → V, (∏ j, iidProb pU (Cu j)) *
        ∑ x, (DMC.blockProb pX (Cu m.2) x).toReal *
          ∑ y, (if ((fun i => (Cu m.2 i, x i)), y) ∈ J₁ then 0
            else (DMC.blockProb (channel₁ W) x y).toReal) :=
        sum_codebookWeight_mul_apply pU pX (fun Cu x => ∑ y,
          if ((fun i => (Cu m.2 i, x i)), y) ∈ J₁ then 0
            else (DMC.blockProb (channel₁ W) x y).toReal) m
    _ = ∑ u, iidProb pU u * ∑ x, (DMC.blockProb pX u x).toReal *
          ∑ y, (if ((fun i => (u i, x i)), y) ∈ J₁ then 0
            else (DMC.blockProb (channel₁ W) x y).toReal) :=
        sum_prod_mul_apply (fun _ u => iidProb pU u) (fun _ => sum_iidProb pU n) (fun u =>
          ∑ x, (DMC.blockProb pX u x).toReal * ∑ y, (if ((fun i => (u i, x i)), y) ∈ J₁ then 0
            else (DMC.blockProb (channel₁ W) x y).toReal)) m.2
    _ = ∑ w, iidProb (DMC.jointPMF pX pU) w *
          ∑ y, (if (w, y) ∈ J₁ then 0
            else (DMC.blockProb (fun ua : V × A => channel₁ W ua.2) w y).toReal) := by
        rw [← DMC.sum_iidProb_jointPMF_mul]
        refine sum_congr rfl fun w _ => ?_
        simp only [Prod.mk.eta, DMC.blockProb]
    _ = _ := DMC.sum_iidProb_mul_sum_ite_jointPMF _ _ J₁

omit [DecidableEq V] [DecidableEq A] [Fintype B₁] [DecidableEq B₁] [DecidableEq B₂] in
theorem sum_codebookWeight_mul_cloud_error (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A)
    (ε : ℝ) [MeasurableSpace V] [MeasurableSpace B₂] (m₀ m : M₁ × M₂) :
    ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A, codebookWeight pU pX Cu Cx *
      ∑ y, (if BlockCode.typicalDecoder Cu
          (jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) n ε) m₀.2 y = m.2 then 0
        else (DMC.blockProb (channel₂ W) (Cx m) y).toReal) ≤
      (1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) n ε,
          iidProb (DMC.jointPMF (cloudChannel₂ W pX) pU) (fun i => (xy.1 i, xy.2 i))) +
        (Fintype.card M₂ - 1) *
          Real.exp (-(n * ((cloudChannel₂ W pX).inputMutualInfo pU - 3 * ε))) := by
  rw [sum_codebookWeight_mul_apply pU pX (fun Cu x => ∑ y,
    if BlockCode.typicalDecoder Cu
      (jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) n ε) m₀.2 y = m.2 then 0
      else (DMC.blockProb (channel₂ W) x y).toReal) m]
  refine le_trans (le_of_eq ?_)
    (DMC.sum_errorProb_typicalCode_le (cloudChannel₂ W pX) pU ε m₀.2 m.2)
  refine sum_congr rfl fun Cu _ => ?_
  congr 1
  rw [BlockCode.errorProb_toReal]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : BlockCode.typicalDecoder Cu
      (jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) n ε) m₀.2 y = m.2
  · simp [h, BlockCode.typicalCode]
  · simp only [h, BlockCode.typicalCode, ↓reduceIte]
    exact (DMC.toReal_blockProb_bind pX (channel₂ W) (Cu m.2) y).symm

private lemma sum_sum_mul_sum {α β γ : Type*} [Fintype α] [Fintype β] (s : Finset γ)
    (w : α → β → ℝ) (F : α → β → γ → ℝ) :
    ∑ a, ∑ b, w a b * ∑ c ∈ s, F a b c = ∑ c ∈ s, ∑ a, ∑ b, w a b * F a b c := by
  simp_rw [mul_sum]
  exact (sum_congr rfl fun a _ => sum_comm).trans sum_comm

omit [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A] [Fintype B₁] [DecidableEq B₁] in
private lemma iidProb_mul_blockProb_eq (pU : PMF V) (pX : V → PMF A) (K : DMC V B₁)
    (w : Fin n → V × A) (y : Fin n → B₁) :
    iidProb (DMC.jointPMF pX pU) w * (DMC.blockProb K (fun i => (w i).1) y).toReal =
      iidProb (DMC.jointPMF pX pU) w * iidProb (DMC.jointPMF K pU) (fun i => ((w i).1, y i)) /
        iidProb pU (fun i => (w i).1) := by
  rw [DMC.iidProb_jointPMF, DMC.iidProb_jointPMF]
  by_cases ha : iidProb pU (fun i => (w i).1) = 0
  · simp [ha]
  · field_simp

omit [Fintype B₂] [DecidableEq B₂] in
theorem sum_codebookWeight_mul_same_cloud [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B₁]
    [MeasurableSingletonClass B₁] (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) (ε : ℝ)
    {m m' : M₁ × M₂} (h1 : m'.1 ≠ m.1) (h2 : m'.2 = m.2) :
    ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A, codebookWeight pU pX Cu Cx *
      ∑ y, (if ((fun i => (Cu m'.2 i, Cx m' i)), y) ∈ superpositionTypicalSet (law₁ W pU pX) n ε
        then (1 : ℝ) else 0) * (DMC.blockProb (channel₁ W) (Cx m) y).toReal ≤
      Real.exp (-(n * (I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
        (law₁ W pU pX).toMeasure] - 4 * ε))) := by
  set J := superpositionTypicalSet (law₁ W pU pX) n ε
  have hm : m' ≠ m := fun h => h1 (by rw [h])
  have hJ : ∀ f : (Fin n → V × A) × (Fin n → B₁) → ℝ,
      ∑ z ∈ J, f z = ∑ z, if z ∈ J then f z else 0 := fun f => (Fintype.sum_ite_mem J f).symm
  refine le_trans (le_of_eq ?_) (sum_superpositionTypicalSet_le_condMutualInfo _ n ε)
  rw [law₁_map_fst, law₁_map_cloud, law₁_map_cloud_output, sum_sum_mul_sum]
  calc _ = ∑ y : Fin n → B₁, ∑ u, iidProb pU u *
        ((∑ x, (DMC.blockProb pX u x).toReal *
          (if ((fun i => (u i, x i)), y) ∈ J then (1 : ℝ) else 0)) *
          ∑ x, (DMC.blockProb pX u x).toReal * (DMC.blockProb (channel₁ W) x y).toReal) := by
        refine sum_congr rfl fun y _ => ?_
        rw [sum_codebookWeight_mul_apply_mul_apply pU pX
          (fun Cu x => if ((fun i => (Cu m'.2 i, x i)), y) ∈ J then (1 : ℝ) else 0)
          (fun _ x => (DMC.blockProb (channel₁ W) x y).toReal) hm]
        simp only [h2]
        exact sum_prod_mul_apply (fun _ u => iidProb pU u) (fun _ => sum_iidProb pU n) (fun u =>
          (∑ x, (DMC.blockProb pX u x).toReal *
            (if ((fun i => (u i, x i)), y) ∈ J then (1 : ℝ) else 0)) *
          ∑ x, (DMC.blockProb pX u x).toReal * (DMC.blockProb (channel₁ W) x y).toReal) m.2
    _ = ∑ u, iidProb pU u * ∑ x, (DMC.blockProb pX u x).toReal *
          ∑ y, (if ((fun i => (u i, x i)), y) ∈ J then
            (DMC.blockProb (cloudChannel₁ W pX) u y).toReal else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun u _ => ?_
        rw [← mul_sum]
        congr 1
        have hc : ∀ y, (DMC.blockProb (cloudChannel₁ W pX) u y).toReal =
            ∑ x, (DMC.blockProb pX u x).toReal * (DMC.blockProb (channel₁ W) x y).toReal :=
          fun y => DMC.toReal_blockProb_bind pX (channel₁ W) u y
        simp_rw [hc, sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun y _ => ?_
        split_ifs <;> simp
    _ = ∑ w, iidProb (DMC.jointPMF pX pU) w *
          ∑ y, (if (w, y) ∈ J then
            (DMC.blockProb (cloudChannel₁ W pX) (fun i => (w i).1) y).toReal else 0) := by
        rw [← DMC.sum_iidProb_jointPMF_mul]
    _ = _ := by
        rw [hJ, Fintype.sum_prod_type]
        refine sum_congr rfl fun w _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun y _ => ?_
        split_ifs
        · exact iidProb_mul_blockProb_eq pU pX _ w y
        · simp

omit [Fintype B₂] [DecidableEq B₂] in
theorem sum_codebookWeight_mul_other_cloud [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B₁]
    [MeasurableSingletonClass B₁] (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) (ε : ℝ)
    {m m' : M₁ × M₂} (h2 : m'.2 ≠ m.2) :
    ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A, codebookWeight pU pX Cu Cx *
      ∑ y, (if ((fun i => (Cu m'.2 i, Cx m' i)), y) ∈ superpositionTypicalSet (law₁ W pU pX) n ε
        then (1 : ℝ) else 0) * (DMC.blockProb (channel₁ W) (Cx m) y).toReal ≤
      Real.exp (-(n * (I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 ;
        (law₁ W pU pX).toMeasure] - 3 * ε))) := by
  set J := superpositionTypicalSet (law₁ W pU pX) n ε
  have hm : m' ≠ m := fun h => h2 (by rw [h])
  have hJ : ∀ f : (Fin n → V × A) × (Fin n → B₁) → ℝ,
      ∑ z ∈ J, f z = ∑ z, if z ∈ J then f z else 0 := fun f => (Fintype.sum_ite_mem J f).symm
  refine le_trans (le_of_eq ?_) (sum_superpositionTypicalSet_le_mutualInfo _ n ε)
  rw [law₁_map_fst, sum_sum_mul_sum]
  calc _ = ∑ y : Fin n → B₁,
        (∑ u, iidProb pU u * ∑ x, (DMC.blockProb pX u x).toReal *
          (if ((fun i => (u i, x i)), y) ∈ J then (1 : ℝ) else 0)) *
        ∑ u, iidProb pU u * ∑ x, (DMC.blockProb pX u x).toReal *
          (DMC.blockProb (channel₁ W) x y).toReal := by
        refine sum_congr rfl fun y _ => ?_
        rw [sum_codebookWeight_mul_apply_mul_apply pU pX
          (fun Cu x => if ((fun i => (Cu m'.2 i, x i)), y) ∈ J then (1 : ℝ) else 0)
          (fun _ x => (DMC.blockProb (channel₁ W) x y).toReal) hm]
        exact sum_prod_mul_apply_mul_apply (fun _ u => iidProb pU u) (fun _ => sum_iidProb pU n)
          (fun u => ∑ x, (DMC.blockProb pX u x).toReal *
            (if ((fun i => (u i, x i)), y) ∈ J then (1 : ℝ) else 0))
          (fun u => ∑ x, (DMC.blockProb pX u x).toReal *
            (DMC.blockProb (channel₁ W) x y).toReal) h2
    _ = ∑ y : Fin n → B₁,
        (∑ w, iidProb (DMC.jointPMF pX pU) w * (if (w, y) ∈ J then (1 : ℝ) else 0)) *
          iidProb ((law₁ W pU pX).map Prod.snd) y := by
        refine sum_congr rfl fun y _ => ?_
        rw [← DMC.sum_iidProb_jointPMF_mul, ← DMC.sum_iidProb_jointPMF_mul,
          ← sum_iidProb_pair_left (law₁ W pU pX) y]
        congr 1
        refine sum_congr rfl fun w _ => ?_
        rw [law₁, DMC.iidProb_jointPMF (fun ua : V × A => channel₁ W ua.2)
          (DMC.jointPMF pX pU) w y]
        rfl
    _ = _ := by
        rw [hJ, Fintype.sum_prod_type, sum_comm]
        refine sum_congr rfl fun y _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun w _ => ?_
        split_ifs <;> simp

private lemma sum_filter_fst_ne [Nonempty M₁] (m : M₁ × M₂) (a b : ℝ) :
    ∑ m' : M₁ × M₂ with m'.1 ≠ m.1, (if m'.2 = m.2 then a else b) =
      (Fintype.card M₁ - 1) * a + (Fintype.card M₁ - 1) * (Fintype.card M₂ - 1) * b := by
  have : Nonempty M₂ := ⟨m.2⟩
  have hF : (univ.filter fun m' : M₁ × M₂ => m'.1 ≠ m.1) = (univ.erase m.1) ×ˢ univ := by
    ext x
    simp
  have hin : ∑ y : M₂, (if y = m.2 then a else b) = a + (Fintype.card M₂ - 1) * b := by
    rw [← add_sum_erase _ _ (mem_univ m.2), ite_eq_left rfl,
      sum_congr rfl fun y hy => ite_eq_right (ne_of_mem_erase hy), sum_const,
      card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul, Nat.cast_sub Fintype.card_pos,
      Nat.cast_one]
  rw [hF, sum_product]
  simp only [hin, sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul,
    Nat.cast_sub (Fintype.card_pos (α := M₁)), Nat.cast_one]
  ring

omit [DecidableEq V] [DecidableEq A] [DecidableEq B₁] [DecidableEq B₂] in
theorem sum_errorProb_superpositionCode_le [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B₁]
    [MeasurableSingletonClass B₁] [MeasurableSpace B₂]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) (ε : ℝ) (m₀ m : M₁ × M₂) :
    ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A, codebookWeight pU pX Cu Cx *
      ((superpositionCode Cu Cx (superpositionTypicalSet (law₁ W pU pX) n ε)
        (jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) n ε) m₀).errorProb W m).toReal ≤
      (1 - ∑ z ∈ superpositionTypicalSet (law₁ W pU pX) n ε,
          iidProb (law₁ W pU pX) (fun i => (z.1 i, z.2 i))) +
        (Fintype.card M₁ - 1) *
          Real.exp (-(n * (I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
            (law₁ W pU pX).toMeasure] - 4 * ε))) +
        (Fintype.card M₁ - 1) * (Fintype.card M₂ - 1) *
          Real.exp (-(n * (I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 ;
            (law₁ W pU pX).toMeasure] - 3 * ε))) +
      ((1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) n ε,
          iidProb (DMC.jointPMF (cloudChannel₂ W pX) pU) (fun i => (xy.1 i, xy.2 i))) +
        (Fintype.card M₂ - 1) *
          Real.exp (-(n * ((cloudChannel₂ W pX).inputMutualInfo pU - 3 * ε)))) := by
  classical
  have : Nonempty M₁ := ⟨m.1⟩
  set J₁ := superpositionTypicalSet (law₁ W pU pX) n ε
  set J₂ := jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) n ε
  set eb := Real.exp (-(n * (I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
    (law₁ W pU pX).toMeasure] - 4 * ε)))
  set ec := Real.exp (-(n * (I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 ;
    (law₁ W pU pX).toMeasure] - 3 * ε)))
  have hb : ∑ m' with m'.1 ≠ m.1, ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A,
      codebookWeight pU pX Cu Cx * ∑ y, (if ((fun i => (Cu m'.2 i, Cx m' i)), y) ∈ J₁
        then (1 : ℝ) else 0) * (DMC.blockProb (channel₁ W) (Cx m) y).toReal ≤
      (Fintype.card M₁ - 1) * eb + (Fintype.card M₁ - 1) * (Fintype.card M₂ - 1) * ec := by
    rw [← sum_filter_fst_ne m eb ec]
    refine sum_le_sum fun m' hm' => ?_
    have h1 : m'.1 ≠ m.1 := (mem_filter.1 hm').2
    split_ifs with h2
    · exact sum_codebookWeight_mul_same_cloud W pU pX ε h1 h2
    · exact sum_codebookWeight_mul_other_cloud W pU pX ε h2
  calc _ ≤ ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A, codebookWeight pU pX Cu Cx *
        (∑ y, (if ((fun i => (Cu m.2 i, Cx m i)), y) ∈ J₁ then 0
          else (DMC.blockProb (channel₁ W) (Cx m) y).toReal) +
        ∑ m' with m'.1 ≠ m.1, ∑ y, (if ((fun i => (Cu m'.2 i, Cx m' i)), y) ∈ J₁ then (1 : ℝ)
          else 0) * (DMC.blockProb (channel₁ W) (Cx m) y).toReal +
        ∑ y, (if BlockCode.typicalDecoder Cu J₂ m₀.2 y = m.2 then 0
          else (DMC.blockProb (channel₂ W) (Cx m) y).toReal)) :=
        sum_le_sum fun Cu _ => sum_le_sum fun Cx _ => mul_le_mul_of_nonneg_left
          (errorProb_superpositionCode_toReal_le W Cu Cx J₁ J₂ m₀ m)
          (codebookWeight_nonneg pU pX Cu Cx)
    _ = (∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A, codebookWeight pU pX Cu Cx *
          ∑ y, (if ((fun i => (Cu m.2 i, Cx m i)), y) ∈ J₁ then 0
            else (DMC.blockProb (channel₁ W) (Cx m) y).toReal)) +
        ∑ m' with m'.1 ≠ m.1, ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A,
          codebookWeight pU pX Cu Cx * ∑ y, (if ((fun i => (Cu m'.2 i, Cx m' i)), y) ∈ J₁
            then (1 : ℝ) else 0) * (DMC.blockProb (channel₁ W) (Cx m) y).toReal +
        ∑ Cu : M₂ → Fin n → V, ∑ Cx : M₁ × M₂ → Fin n → A, codebookWeight pU pX Cu Cx *
          ∑ y, (if BlockCode.typicalDecoder Cu J₂ m₀.2 y = m.2 then 0
            else (DMC.blockProb (channel₂ W) (Cx m) y).toReal) := by
        rw [← sum_sum_mul_sum]
        simp only [mul_add, sum_add_distrib]
    _ ≤ _ := by
        rw [sum_codebookWeight_mul_miss]
        have h2 := sum_codebookWeight_mul_cloud_error W pU pX ε m₀ m (n := n) (M₁ := M₁)
        linarith

omit [DecidableEq V] [DecidableEq A] [DecidableEq B₁] [DecidableEq B₂] in
theorem exists_superpositionCode_avgError_le [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B₁]
    [MeasurableSingletonClass B₁] [MeasurableSpace B₂]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) (ε : ℝ) (m₀ : M₁ × M₂) :
    ∃ (Cu : M₂ → Fin n → V) (Cx : M₁ × M₂ → Fin n → A),
      (superpositionCode Cu Cx (superpositionTypicalSet (law₁ W pU pX) n ε)
        (jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) n ε) m₀).avgError W ≤
      ENNReal.ofReal ((1 - ∑ z ∈ superpositionTypicalSet (law₁ W pU pX) n ε,
          iidProb (law₁ W pU pX) (fun i => (z.1 i, z.2 i))) +
        (Fintype.card M₁ - 1) *
          Real.exp (-(n * (I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
            (law₁ W pU pX).toMeasure] - 4 * ε))) +
        (Fintype.card M₁ - 1) * (Fintype.card M₂ - 1) *
          Real.exp (-(n * (I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 ;
            (law₁ W pU pX).toMeasure] - 3 * ε))) +
      ((1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) n ε,
          iidProb (DMC.jointPMF (cloudChannel₂ W pX) pU) (fun i => (xy.1 i, xy.2 i))) +
        (Fintype.card M₂ - 1) *
          Real.exp (-(n * ((cloudChannel₂ W pX).inputMutualInfo pU - 3 * ε))))) := by
  classical
  have : Nonempty M₁ := ⟨m₀.1⟩
  have : Nonempty M₂ := ⟨m₀.2⟩
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le
    (w := fun C : (M₂ → Fin n → V) × (M₁ × M₂ → Fin n → A) => codebookWeight pU pX C.1 C.2)
    (f := fun C => ∑ m, ((superpositionCode C.1 C.2 (superpositionTypicalSet (law₁ W pU pX) n ε)
      (jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) n ε) m₀).errorProb W m).toReal)
    (t := Fintype.card M₁ * Fintype.card M₂ * _)
    (fun C => codebookWeight_nonneg pU pX C.1 C.2)
    (by rw [Fintype.sum_prod_type]; exact sum_codebookWeight pU pX) (by
      rw [Fintype.sum_prod_type, sum_sum_mul_sum]
      refine (sum_le_sum fun m _ => sum_errorProb_superpositionCode_le W pU pX ε m₀ m).trans
        (le_of_eq ?_)
      rw [sum_const, card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul])
  exact ⟨C.1, C.2, BCCode.avgError_le_ofReal _ W hC⟩

end Average

theorem achievable_of_lt [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁] [MeasurableSpace B₁]
    [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) {R₁ R₂ : ℝ}
    (h₁ : R₁ < condMutualInfo (fun ω : V × A × B₁ × B₂ => ω.2.1) (fun ω => ω.2.2.1)
      (fun ω => ω.1) (jointMeasure W pU pX))
    (h₂ : R₂ < mutualInfo (fun ω : V × A × B₁ × B₂ => ω.1) (fun ω => ω.2.2.2)
      (jointMeasure W pU pX))
    (h₃ : R₁ + R₂ < mutualInfo (fun ω : V × A × B₁ × B₂ => ω.2.1) (fun ω => ω.2.2.1)
      (jointMeasure W pU pX)) :
    Achievable W (max R₁ 0) (max R₂ 0) := by
  classical
  rw [condMutualInfo_eq_law₁] at h₁
  rw [mutualInfo_cloud_eq] at h₂
  rw [mutualInfo_eq_law₁] at h₃
  set I₁ := I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
    (law₁ W pU pX).toMeasure]
  set I₂ := (cloudChannel₂ W pX).inputMutualInfo pU
  set I₃ := I[fun ω : (V × A) × B₁ => ω.1.2 : fun ω => ω.2 ; (law₁ W pU pX).toMeasure]
  intro ε hε
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  set η := min (min (I₁ - R₁) (I₂ - R₂)) (I₃ - (R₁ + R₂)) / 5 with hη
  have hη0 : 0 < η := by
    rw [hη]
    have := lt_min (lt_min (sub_pos.2 h₁) (sub_pos.2 h₂)) (sub_pos.2 h₃)
    linarith
  have hm₁ : min (min (I₁ - R₁) (I₂ - R₂)) (I₃ - (R₁ + R₂)) ≤ I₁ - R₁ :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hm₂ : min (min (I₁ - R₁) (I₂ - R₂)) (I₃ - (R₁ + R₂)) ≤ I₂ - R₂ :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hm₃ : min (min (I₁ - R₁) (I₂ - R₂)) (I₃ - (R₁ + R₂)) ≤ I₃ - (R₁ + R₂) := min_le_right _ _
  have e₁ : R₁ - (I₁ - 4 * η) < 0 := by rw [hη]; linarith
  have e₂ : R₂ - (I₂ - 3 * η) < 0 := by rw [hη]; linarith
  have e₃ : R₁ + R₂ - (I₃ - 3 * η) < 0 := by rw [hη]; linarith
  have hJ₁ : Tendsto (fun n : ℕ => 1 - ∑ z ∈ superpositionTypicalSet (law₁ W pU pX) n η,
      iidProb (law₁ W pU pX) (fun i => (z.1 i, z.2 i))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_superpositionTypicalSet (law₁ W pU pX) hη0)
  have hJ₂ : Tendsto (fun n : ℕ => 1 -
      ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) n η,
        iidProb (DMC.jointPMF (cloudChannel₂ W pX) pU) (fun i => (xy.1 i, xy.2 i)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_jointlyTypicalSet (DMC.jointPMF (cloudChannel₂ W pX) pU) hη0)
  have hsum := (((hJ₁.add (tendsto_exp_nat_mul e₁)).add (tendsto_exp_nat_mul e₃)).add hJ₂).add
    (tendsto_exp_nat_mul e₂)
  simp only [add_zero] at hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  set k₁ := ⌈Real.exp (n * R₁)⌉₊
  set k₂ := ⌈Real.exp (n * R₂)⌉₊
  have hk₁ : 0 < k₁ := Nat.ceil_pos.2 (Real.exp_pos _)
  have hk₂ : 0 < k₂ := Nat.ceil_pos.2 (Real.exp_pos _)
  have hc₁ : (k₁ : ℝ) - 1 ≤ Real.exp (n * R₁) := by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R₁)).le]
  have hc₂ : (k₂ : ℝ) - 1 ≤ Real.exp (n * R₂) := by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R₂)).le]
  have hk₁' : (0 : ℝ) ≤ k₁ - 1 := by
    have : (1 : ℝ) ≤ k₁ := by exact_mod_cast hk₁
    linarith
  have hk₂' : (0 : ℝ) ≤ k₂ - 1 := by
    have : (1 : ℝ) ≤ k₂ := by exact_mod_cast hk₂
    linarith
  refine ⟨k₁, k₂, exp_mul_max_le (Nat.le_ceil _), exp_mul_max_le (Nat.le_ceil _), ?_⟩
  obtain ⟨Cu, Cx, hC⟩ := exists_superpositionCode_avgError_le (n := n) W pU pX η
    ((⟨0, hk₁⟩, ⟨0, hk₂⟩) : Fin k₁ × Fin k₂)
  refine ⟨_, hC.trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hδε.le)⟩
  rw [Fintype.card_fin, Fintype.card_fin]
  have b₁ : ((k₁ : ℝ) - 1) * Real.exp (-(n * (I₁ - 4 * η))) ≤
      Real.exp (n * (R₁ - (I₁ - 4 * η))) :=
    calc _ ≤ Real.exp (n * R₁) * Real.exp (-(n * (I₁ - 4 * η))) :=
          mul_le_mul_of_nonneg_right hc₁ (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have b₂ : ((k₂ : ℝ) - 1) * Real.exp (-(n * (I₂ - 3 * η))) ≤
      Real.exp (n * (R₂ - (I₂ - 3 * η))) :=
    calc _ ≤ Real.exp (n * R₂) * Real.exp (-(n * (I₂ - 3 * η))) :=
          mul_le_mul_of_nonneg_right hc₂ (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have b₃ : ((k₁ : ℝ) - 1) * ((k₂ : ℝ) - 1) * Real.exp (-(n * (I₃ - 3 * η))) ≤
      Real.exp (n * (R₁ + R₂ - (I₃ - 3 * η))) :=
    calc _ ≤ Real.exp (n * R₁) * Real.exp (n * R₂) * Real.exp (-(n * (I₃ - 3 * η))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hc₁ hc₂ hk₂' (Real.exp_pos _).le)
            (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  linarith [hN n hn]

theorem superpositionRegion_subset [Fintype A] [MeasurableSpace A] [Fintype B₁]
    [MeasurableSpace B₁] [Fintype B₂] [MeasurableSpace B₂] [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B₁] [MeasurableSingletonClass B₂]
    [MeasurableSingletonClass V]
    (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    superpositionRegion W pU pX ⊆ closure (achievableRegion W) := by
  rintro R ⟨h0₁, h0₂, h₁, h₂, h₃⟩
  have hf : Continuous fun t : ℝ => (max (R.1 - t) 0, max (R.2 - t) 0) :=
    (((continuous_const.sub continuous_id).max continuous_const).prodMk
      ((continuous_const.sub continuous_id).max continuous_const))
  refine mem_closure_of_tendsto (b := 𝓝[>] (0 : ℝ))
    (f := fun t : ℝ => (max (R.1 - t) 0, max (R.2 - t) 0)) ?_ ?_
  · have h := hf.tendsto 0
    simp only [sub_zero, max_eq_left h0₁, max_eq_left h0₂] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    exact ⟨le_max_right _ _, le_max_right _ _,
      achievable_of_lt W pU pX (by linarith) (by linarith) (by linarith)⟩

end BC

end Meat
