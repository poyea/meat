import Meat.Open.Interference
import Meat.Open.Interactive

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

structure TwoWayCode (M₁ M₂ A₁ A₂ B₁ B₂ : Type*) (n : ℕ) where
  enc₁ : M₁ → (i : Fin n) → (Fin i → B₁) → A₁
  enc₂ : M₂ → (i : Fin n) → (Fin i → B₂) → A₂
  dec₁ : M₁ → (Fin n → B₁) → M₂
  dec₂ : M₂ → (Fin n → B₂) → M₁

namespace TwoWayCode

variable {M₁ M₂ A₁ A₂ B₁ B₂ : Type*} {n : ℕ}

def past {B : Type*} (y : Fin n → B) (i : Fin n) : Fin i → B :=
  fun j => y ⟨j, j.2.trans i.2⟩

def input (c : TwoWayCode M₁ M₂ A₁ A₂ B₁ B₂ n) (m : M₁ × M₂) (y : Fin n → B₁ × B₂)
    (i : Fin n) : A₁ × A₂ :=
  (c.enc₁ m.1 i (past (fun j => (y j).1) i), c.enc₂ m.2 i (past (fun j => (y j).2) i))

noncomputable def outputProb (c : TwoWayCode M₁ M₂ A₁ A₂ B₁ B₂ n)
    (W : DMC (A₁ × A₂) (B₁ × B₂)) (m : M₁ × M₂) (y : Fin n → B₁ × B₂) : ℝ≥0∞ :=
  ∏ i, W (c.input m y i) (y i)

noncomputable def errorProb [Fintype B₁] [Fintype B₂] [DecidableEq M₁] [DecidableEq M₂]
    (c : TwoWayCode M₁ M₂ A₁ A₂ B₁ B₂ n) (W : DMC (A₁ × A₂) (B₁ × B₂)) (m : M₁ × M₂) :
    ℝ≥0∞ :=
  ∑ y : Fin n → B₁ × B₂,
    if (c.dec₁ m.1 (fun i => (y i).1), c.dec₂ m.2 (fun i => (y i).2)) = (m.2, m.1) then 0
    else c.outputProb W m y

noncomputable def avgError [Fintype B₁] [Fintype B₂] [Fintype M₁] [Fintype M₂]
    [DecidableEq M₁] [DecidableEq M₂]
    (c : TwoWayCode M₁ M₂ A₁ A₂ B₁ B₂ n) (W : DMC (A₁ × A₂) (B₁ × B₂)) : ℝ≥0∞ :=
  (∑ m : M₁ × M₂, c.errorProb W m) / ((Fintype.card M₁ : ℝ≥0∞) * (Fintype.card M₂ : ℝ≥0∞))

def ofICCode (c : ICCode M₁ M₂ A₁ A₂ (A₂ × B₂) (A₁ × B₁) n) : TwoWayCode M₁ M₂ A₁ A₂ B₁ B₂ n where
  enc₁ m i _ := c.enc₁ m i
  enc₂ m i _ := c.enc₂ m i
  dec₁ m₁ y₁ := c.dec₂ fun i => (c.enc₁ m₁ i, y₁ i)
  dec₂ m₂ y₂ := c.dec₁ fun i => (c.enc₂ m₂ i, y₂ i)

end TwoWayCode

namespace TwoWay

variable {A₁ A₂ B₁ B₂ : Type*}

def Achievable [Fintype B₁] [Fintype B₂] (W : DMC (A₁ × A₂) (B₁ × B₂)) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k₁ k₂ : ℕ, Real.exp (n * R₁) ≤ k₁ ∧ Real.exp (n * R₂) ≤ k₂ ∧
      ∃ c : TwoWayCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n, c.avgError W ≤ ε

def achievableRegion [Fintype B₁] [Fintype B₂] (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ Achievable W R.1 R.2}

def SingleLetterCapacity : Prop :=
  ∃ (m : ℕ) (κ : ℕ → ℕ → ℕ → ℕ → ℕ) (F : EntropicFormula m 4),
    ∀ (A₁ A₂ B₁ B₂ : Type) [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂]
      [Nonempty A₁] [Nonempty A₂] (W : DMC (A₁ × A₂) (B₁ × B₂)),
      closure (achievableRegion W) =
        F.value (EntropicFormula.letterLaw₄ (m := m)
          (k := κ (Fintype.card A₁) (Fintype.card A₂) (Fintype.card B₁) (Fintype.card B₂)) W)

noncomputable def toInterference (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    DMC (A₁ × A₂) ((A₂ × B₂) × (A₁ × B₁)) :=
  fun a => (W a).map fun y => ((a.2, y.2), (a.1, y.1))

section Info

variable {Ω S T U : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (μ : Measure Ω) {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

theorem condMutualInfo_pair_cond :
    I[X : fun ω => (Z ω, Y ω) | Z ; μ] = I[X : Y | Z ; μ] := by
  have h1 : H[fun ω => ((Z ω, Y ω), Z ω) ; μ] = H[fun ω => (Y ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (Y ω, Z ω)) (f := fun p => ((p.2, p.1), p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.2 h.2
  have h2 : H[fun ω => ((X ω, (Z ω, Y ω)), Z ω) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω))
      (f := fun p => ((p.1.1, (p.2, p.1.2)), p.2)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 h.1.2.2) h.2
  simp only [condMutualInfo_def, condEntropy_def]
  rw [h1, h2]

theorem condMutualInfo_pair_self :
    I[X : fun ω => (X ω, Y ω) | Z ; μ] = H[X | Z ; μ] := by
  have h : H[fun ω => ((X ω, (X ω, Y ω)), Z ω) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω))
      (f := fun p => ((p.1.1, p.1), p.2)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.2 h.2
  simp only [condMutualInfo_def, condEntropy_def]
  rw [h]
  ring

omit [MeasurableSingletonClass U] in
theorem mutualInfo_pair_self : I[X : fun ω => (X ω, Y ω) ; μ] = H[X ; μ] := by
  have h : H[fun ω => (X ω, (X ω, Y ω)) ; μ] = H[fun ω => (X ω, Y ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Y ω)) (f := fun p => (p.1, p)) fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact h.2
  rw [mutualInfo_def, h]
  ring

theorem condMutualInfo_le_condEntropy [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) : I[X : Y | Z ; μ] ≤ H[X | Z ; μ] := by
  rw [condMutualInfo_comm, condMutualInfo_eq_condEntropy_sub_condEntropy]
  linarith [condEntropy_nonneg μ hX (hY.prodMk hZ)]

end Info

theorem out₁_toInterference (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    IC.out₁ (toInterference W) = fun a => (W a).map fun y => (a.2, y.2) := by
  funext a
  simp only [IC.out₁, toInterference, PMF.map_comp]
  rfl

theorem out₂_toInterference (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    IC.out₂ (toInterference W) = fun a => (W a).map fun y => (a.1, y.1) := by
  funext a
  simp only [IC.out₂, toInterference, PMF.map_comp]
  rfl

section Reduction

theorem sum_mul_blockProb_map {A B C : Type*} [Fintype B] [Fintype C] {n : ℕ} (V : DMC A B)
    (φ : A → B → C) (x : Fin n → A) (f : (Fin n → C) → ℝ≥0∞) :
    ∑ z, f z * DMC.blockProb (fun a => (V a).map (φ a)) x z =
      ∑ y, f (fun i => φ (x i) (y i)) * DMC.blockProb V x y := by
  classical
  have hb : ∀ z, DMC.blockProb (fun a => (V a).map (φ a)) x z =
      ∑ y : Fin n → B, if z = (fun i => φ (x i) (y i)) then DMC.blockProb V x y else 0 := by
    intro z
    simp only [DMC.blockProb, PMF.map_apply, tsum_fintype]
    rw [Fintype.prod_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [Finset.prod_ite_zero]
    simp [funext_iff]
  simp only [hb, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  simp

variable [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂]

theorem errorProb_ofICCode {M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂] {n : ℕ}
    (c : ICCode M₁ M₂ A₁ A₂ (A₂ × B₂) (A₁ × B₁) n) (W : DMC (A₁ × A₂) (B₁ × B₂))
    (m : M₁ × M₂) :
    (TwoWayCode.ofICCode c).errorProb W m = c.errorProb (toInterference W) m := by
  classical
  have e : c.errorProb (toInterference W) m = ∑ z : Fin n → (A₂ × B₂) × (A₁ × B₁),
      (if (c.dec₁ (fun i => (z i).1), c.dec₂ (fun i => (z i).2)) = m then 0 else 1) *
        DMC.blockProb (toInterference W) (fun i => (c.enc₁ m.1 i, c.enc₂ m.2 i)) z := by
    refine sum_congr rfl fun z _ => ?_
    split_ifs <;> simp
  rw [e, show toInterference W = fun a => (W a).map ((fun a y => ((a.2, y.2), (a.1, y.1))) a)
    from rfl, sum_mul_blockProb_map]
  refine sum_congr rfl fun y _ => ?_
  have hc : ((TwoWayCode.ofICCode c).dec₁ m.1 (fun i => (y i).1),
        (TwoWayCode.ofICCode c).dec₂ m.2 (fun i => (y i).2)) = (m.2, m.1) ↔
      (c.dec₁ (fun i => (c.enc₂ m.2 i, (y i).2)), c.dec₂ (fun i => (c.enc₁ m.1 i, (y i).1))) =
        m := by
    simp only [TwoWayCode.ofICCode, Prod.ext_iff]
    tauto
  by_cases h : (c.dec₁ (fun i => (c.enc₂ m.2 i, (y i).2)),
    c.dec₂ (fun i => (c.enc₁ m.1 i, (y i).1))) = m
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hc.2 h)), ite_eq_left_of_eq_true _ _ (eq_true h),
      zero_mul]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (hc.1 h')),
      ite_eq_right_of_eq_false _ _ (eq_false h), one_mul]
    rfl

theorem avgError_ofICCode {M₁ M₂ : Type*} [Fintype M₁] [Fintype M₂] [DecidableEq M₁]
    [DecidableEq M₂] {n : ℕ} (c : ICCode M₁ M₂ A₁ A₂ (A₂ × B₂) (A₁ × B₁) n)
    (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    (TwoWayCode.ofICCode c).avgError W = c.avgError (toInterference W) := by
  simp only [TwoWayCode.avgError, ICCode.avgError, errorProb_ofICCode]

theorem Achievable.of_interference {W : DMC (A₁ × A₂) (B₁ × B₂)} {R₁ R₂ : ℝ}
    (h : IC.Achievable (toInterference W) R₁ R₂) : Achievable W R₁ R₂ := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hn
  exact ⟨k₁, k₂, hk₁, hk₂, TwoWayCode.ofICCode c, (avgError_ofICCode c W).trans_le hc⟩

theorem achievableRegion_interference_subset (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    IC.achievableRegion (toInterference W) ⊆ achievableRegion W :=
  fun _ ⟨h1, h2, h⟩ => ⟨h1, h2, Achievable.of_interference h⟩

end Reduction

variable [Fintype A₁] [MeasurableSpace A₁] [Fintype A₂] [MeasurableSpace A₂]
  [Fintype B₁] [MeasurableSpace B₁] [Fintype B₂] [MeasurableSpace B₂]

noncomputable def rectangle (W : DMC (A₁ × A₂) (B₁ × B₂)) (p : PMF (A₁ × A₂)) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧
    R.1 ≤ I[fun ω : (A₁ × A₂) × (B₁ × B₂) => ω.1.1 : fun ω => ω.2.2 | fun ω => ω.1.2 ;
      W.jointMeasure p] ∧
    R.2 ≤ I[fun ω : (A₁ × A₂) × (B₁ × B₂) => ω.1.2 : fun ω => ω.2.1 | fun ω => ω.1.1 ;
      W.jointMeasure p]}

noncomputable def innerBound (W : DMC (A₁ × A₂) (B₁ × B₂)) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ (⋃ p₁ : PMF A₁, ⋃ p₂ : PMF A₂, rectangle W (MAC.inputPMF p₁ p₂)))

noncomputable def outerBound (W : DMC (A₁ × A₂) (B₁ × B₂)) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ (⋃ p : PMF (A₁ × A₂), rectangle W p))

theorem innerBound_subset_outerBound (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    innerBound W ⊆ outerBound W :=
  closure_mono (convexHull_mono (Set.iUnion₂_subset fun p₁ p₂ =>
    Set.subset_iUnion (fun p => rectangle W p) (MAC.inputPMF p₁ p₂)))

variable [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂]
  [MeasurableSingletonClass B₁] [MeasurableSingletonClass B₂]

omit [Fintype A₁] [Fintype A₂] in
theorem jointMeasure_map [Finite A₁] [Finite A₂] {B C : Type*} [Finite B] [MeasurableSpace B]
    [MeasurableSingletonClass B] [MeasurableSpace C]
    (W : DMC (A₁ × A₂) B) (g : A₁ × A₂ → B → C) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    MAC.jointMeasure (fun a => (W a).map (g a)) p₁ p₂ =
      (MAC.jointMeasure W p₁ p₂).map fun ω => (ω.1, ω.2.1, g (ω.1, ω.2.1) ω.2.2) := by
  rw [MAC.jointMeasure, MAC.jointMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _)]
  congr 1
  simp only [PMF.map_bind, PMF.map_comp]
  rfl

omit [Fintype B₁] in
theorem condMutualInfo_rectangle₁ [Finite B₁] (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁)
    (p₂ : PMF A₂) :
    I[fun ω : (A₁ × A₂) × (B₁ × B₂) => ω.1.1 : fun ω => ω.2.2 | fun ω => ω.1.2 ;
        W.jointMeasure (MAC.inputPMF p₁ p₂)] =
      I[fun ω : A₁ × A₂ × (B₁ × B₂) => ω.1 : fun ω => ω.2.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure W p₁ p₂] := by
  rw [DMC.jointMeasure_eq_toMeasure, MAC.jointPMF_inputPMF,
    ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _), MAC.jointMeasure_eq_toMeasure]
  rfl

omit [Fintype B₂] in
theorem condMutualInfo_rectangle₂ [Finite B₂] (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁)
    (p₂ : PMF A₂) :
    I[fun ω : (A₁ × A₂) × (B₁ × B₂) => ω.1.2 : fun ω => ω.2.1 | fun ω => ω.1.1 ;
        W.jointMeasure (MAC.inputPMF p₁ p₂)] =
      I[fun ω : A₁ × A₂ × (B₁ × B₂) => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
        MAC.jointMeasure W p₁ p₂] := by
  rw [DMC.jointMeasure_eq_toMeasure, MAC.jointPMF_inputPMF,
    ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _), MAC.jointMeasure_eq_toMeasure]
  rfl

theorem rectangle_subset_closure_achievableRegion_interference (W : DMC (A₁ × A₂) (B₁ × B₂))
    (p₁ : PMF A₁) (p₂ : PMF A₂) :
    rectangle W (MAC.inputPMF p₁ p₂) ⊆ closure (IC.achievableRegion (toInterference W)) := by
  rintro R ⟨h1, h2, h3, h4⟩
  rw [condMutualInfo_rectangle₁] at h3
  rw [condMutualInfo_rectangle₂] at h4
  set ν := MAC.jointMeasure W p₁ p₂
  have ha := jointMeasure_map W (fun a y => (a.2, y.2)) p₁ p₂
  have hb := jointMeasure_map W (fun a y => (a.1, y.1)) p₁ p₂
  rw [← out₁_toInterference] at ha
  rw [← out₂_toInterference] at hb
  have q1 : I[fun ω : A₁ × A₂ × (A₂ × B₂) => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
      MAC.jointMeasure (IC.out₁ (toInterference W)) p₁ p₂] =
      I[fun ω : A₁ × A₂ × (B₁ × B₂) => ω.1 : fun ω => ω.2.2.2 | fun ω => ω.2.1 ; ν] := by
    rw [ha, condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
    exact condMutualInfo_pair_cond ν
  have q2 : I[fun ω : A₁ × A₂ × (A₂ × B₂) => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
      MAC.jointMeasure (IC.out₁ (toInterference W)) p₁ p₂] =
      H[fun ω : A₁ × A₂ × (B₁ × B₂) => ω.2.1 | fun ω => ω.1 ; ν] := by
    rw [ha, condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
    exact condMutualInfo_pair_self ν
  have q3 : I[fun ω : A₁ × A₂ × (A₂ × B₂) => ω.2.1 : fun ω => ω.2.2 ;
      MAC.jointMeasure (IC.out₁ (toInterference W)) p₁ p₂] =
      H[fun ω : A₁ × A₂ × (B₁ × B₂) => ω.2.1 ; ν] := by
    rw [ha, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
    exact mutualInfo_pair_self ν
  have q4 : I[fun ω : A₁ × A₂ × (A₁ × B₁) => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
      MAC.jointMeasure (IC.out₂ (toInterference W)) p₁ p₂] =
      H[fun ω : A₁ × A₂ × (B₁ × B₂) => ω.1 | fun ω => ω.2.1 ; ν] := by
    rw [hb, condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
    exact condMutualInfo_pair_self ν
  have q5 : I[fun ω : A₁ × A₂ × (A₁ × B₁) => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
      MAC.jointMeasure (IC.out₂ (toInterference W)) p₁ p₂] =
      I[fun ω : A₁ × A₂ × (B₁ × B₂) => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ; ν] := by
    rw [hb, condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
    exact condMutualInfo_pair_cond ν
  have q6 : I[fun ω : A₁ × A₂ × (A₁ × B₁) => ω.1 : fun ω => ω.2.2 ;
      MAC.jointMeasure (IC.out₂ (toInterference W)) p₁ p₂] =
      H[fun ω : A₁ × A₂ × (B₁ × B₂) => ω.1 ; ν] := by
    rw [hb, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
    exact mutualInfo_pair_self ν
  have s3 := MAC.mutualInfo_eq_add₁ (IC.out₁ (toInterference W)) p₁ p₂
  have s6 := MAC.mutualInfo_eq_add₂ (IC.out₂ (toInterference W)) p₁ p₂
  have c2 := condMutualInfo_le_condEntropy ν (X := fun ω : A₁ × A₂ × (B₁ × B₂) => ω.2.1)
    (Y := fun ω => ω.2.2.1) (Z := fun ω => ω.1)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
  have c4 := condMutualInfo_le_condEntropy ν (X := fun ω : A₁ × A₂ × (B₁ × B₂) => ω.1)
    (Y := fun ω => ω.2.2.2) (Z := fun ω => ω.2.1)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
  have e2 := condEntropy_le_entropy ν (X := fun ω : A₁ × A₂ × (B₁ × B₂) => ω.2.1)
    (Y := fun ω => ω.1) (measurable_of_finite _) (measurable_of_finite _)
  have e4 := condEntropy_le_entropy ν (X := fun ω : A₁ × A₂ × (B₁ × B₂) => ω.1)
    (Y := fun ω => ω.2.1) (measurable_of_finite _) (measurable_of_finite _)
  refine IC.mem_closure_achievableRegion _ h1 h2 fun δ hδ =>
    IC.achievable_of_lt _ p₁ p₂ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [q1]; linarith
  · rw [q2]; linarith
  · rw [s3, q1, q3]; linarith
  · rw [q4]; linarith
  · rw [q5]; linarith
  · rw [s6, q5, q6]; linarith

theorem innerBound_subset_closure_achievableRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    innerBound W ⊆ closure (achievableRegion W) :=
  (closure_minimal (convexHull_min (Set.iUnion₂_subset fun p₁ p₂ =>
    rectangle_subset_closure_achievableRegion_interference W p₁ p₂)
    (IC.convex_closure_achievableRegion _)) isClosed_closure).trans
    (closure_mono (achievableRegion_interference_subset W))
end TwoWay

namespace TwoWayCode

variable {M₁ M₂ A₁ A₂ B₁ B₂ : Type*} {n : ℕ}

def toFn (c : TwoWayCode M₁ M₂ A₁ A₂ B₁ B₂ n) :
    M₁ × M₂ → (i : Fin n) → (Fin i → B₁ × B₂) → A₁ × A₂ :=
  fun m i q => (c.enc₁ m.1 i fun j => (q j).1, c.enc₂ m.2 i fun j => (q j).2)

theorem outputProb_eq (c : TwoWayCode M₁ M₂ A₁ A₂ B₁ B₂ n) (W : DMC (A₁ × A₂) (B₁ × B₂))
    (m : M₁ × M₂) (y : Fin n → B₁ × B₂) :
    c.outputProb W m y = Interactive.seqProb W (c.toFn m) y :=
  rfl

variable [Fintype M₁] [Nonempty M₁] [Fintype M₂] [Nonempty M₂] [DecidableEq M₁] [DecidableEq M₂]
  [MeasurableSpace M₁] [MeasurableSingletonClass M₁] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

theorem measureReal_dec_ne (c : TwoWayCode M₁ M₂ A₁ A₂ B₁ B₂ n) (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    (Interactive.codeMeasure W c.toFn).real
      {ω | (c.dec₁ ω.1.1 (fun i => (ω.2 i).1), c.dec₂ ω.1.2 (fun i => (ω.2 i).2)) ≠
        (ω.1.2, ω.1.1)} = (c.avgError W).toReal := by
  classical
  rw [measureReal_def, Interactive.codeMeasure_apply, avgError, Fintype.card_prod, Nat.cast_mul,
    div_eq_mul_inv, sum_mul]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [errorProb, sum_mul]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : (c.dec₁ m.1 (fun i => (y i).1), c.dec₂ m.2 (fun i => (y i).2)) = (m.2, m.1)
  · simp [h]
  · simp only [h, ne_eq, not_false_eq_true, ite_true, ite_false]
    rw [mul_comm]
    rfl

end TwoWayCode

namespace TwoWay

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

private lemma one_sub_le {l l' L : ℝ} (hl : l' ≤ l) (hL : 0 ≤ L) : (1 - l) * L ≤ (1 - l') * L :=
  mul_le_mul_of_nonneg_right (by linarith) hL

omit [Fintype B₁] [MeasurableSingletonClass B₁] in
theorem condMutualInfo_eq_sub₁ (ν : Measure ((A₁ × A₂) × (B₁ × B₂))) :
    I[fun x : (A₁ × A₂) × (B₁ × B₂) => x.1.1 : fun x => x.2.2 | fun x => x.1.2 ; ν] =
      H[fun x : (A₁ × A₂) × (B₁ × B₂) => x.2.2 | fun x => x.1.2 ; ν] -
        H[fun x : (A₁ × A₂) × (B₁ × B₂) => x.2.2 | Prod.fst ; ν] :=
  condMutualInfo_eq_condEntropy_sub_condEntropy ν

omit [Fintype B₂] [MeasurableSingletonClass B₂] in
theorem condMutualInfo_eq_sub₂ (ν : Measure ((A₁ × A₂) × (B₁ × B₂))) :
    I[fun x : (A₁ × A₂) × (B₁ × B₂) => x.1.2 : fun x => x.2.1 | fun x => x.1.1 ; ν] =
      H[fun x : (A₁ × A₂) × (B₁ × B₂) => x.2.1 | fun x => x.1.1 ; ν] -
        H[fun x : (A₁ × A₂) × (B₁ × B₂) => x.2.1 | Prod.fst ; ν] := by
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  exact condEntropy_cond_of_injective ν (Z := Prod.fst) (e := Prod.swap) Prod.swap_injective
    fun ω => rfl

variable {M₁ M₂ : Type*} [Fintype M₁] [Nonempty M₁] [Fintype M₂] [Nonempty M₂] [DecidableEq M₁]
  [DecidableEq M₂] [MeasurableSpace M₁] [MeasurableSingletonClass M₁] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] {n : ℕ}

theorem one_sub_mul_log_card_le₁ (c : TwoWayCode M₁ M₂ A₁ A₂ B₁ B₂ n)
    (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M₁) ≤
      ∑ i, I[fun x : (A₁ × A₂) × (B₁ × B₂) => x.1.1 : fun x => x.2.2 | fun x => x.1.2 ;
        W.jointMeasure (Interactive.inputLaw W c.toFn i)] + Real.log 2 := by
  have h := Interactive.one_sub_mul_log_card_le_sum W c.toFn (Equiv.refl _) Prod.snd Prod.snd
    (fun m₂ i q => c.enc₂ m₂ i q) (fun _ _ _ => rfl) (fun m₂ z => c.dec₂ m₂ z)
  have hm : (Interactive.codeMeasure W c.toFn).real
      {ω | (fun m₂ z => c.dec₂ m₂ z : M₂ → (Fin n → B₂) → M₁) ((Equiv.refl _) ω.1).2
        (Prod.snd ∘ ω.2) ≠ ((Equiv.refl (M₁ × M₂)) ω.1).1} ≤ (c.avgError W).toReal := by
    rw [← c.measureReal_dec_ne W]
    exact measureReal_mono fun ω hω h' => hω (congrArg Prod.snd h')
  refine (one_sub_le hm (Real.log_natCast_nonneg _)).trans (h.trans_eq ?_)
  congr 1
  exact sum_congr rfl fun i _ => (condMutualInfo_eq_sub₁ _).symm

theorem one_sub_mul_log_card_le₂ (c : TwoWayCode M₁ M₂ A₁ A₂ B₁ B₂ n)
    (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M₂) ≤
      ∑ i, I[fun x : (A₁ × A₂) × (B₁ × B₂) => x.1.2 : fun x => x.2.1 | fun x => x.1.1 ;
        W.jointMeasure (Interactive.inputLaw W c.toFn i)] + Real.log 2 := by
  have h := Interactive.one_sub_mul_log_card_le_sum W c.toFn (Equiv.prodComm _ _) Prod.fst
    Prod.fst (fun m₁ i q => c.enc₁ m₁ i q) (fun _ _ _ => rfl) (fun m₁ z => c.dec₁ m₁ z)
  have hm : (Interactive.codeMeasure W c.toFn).real
      {ω | (fun m₁ z => c.dec₁ m₁ z : M₁ → (Fin n → B₁) → M₂) ((Equiv.prodComm _ _) ω.1).2
        (Prod.fst ∘ ω.2) ≠ ((Equiv.prodComm M₁ M₂) ω.1).1} ≤ (c.avgError W).toReal := by
    rw [← c.measureReal_dec_ne W]
    exact measureReal_mono fun ω hω h' => hω (congrArg Prod.fst h')
  refine (one_sub_le hm (Real.log_natCast_nonneg _)).trans (h.trans_eq ?_)
  congr 1
  exact sum_congr rfl fun i _ => (condMutualInfo_eq_sub₂ _).symm

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

theorem mem_outerBound_of_mem_achievableRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) {R : ℝ × ℝ}
    (hR : R ∈ achievableRegion W) : R ∈ outerBound W := by
  classical
  obtain ⟨hR1, hR2, hA⟩ := hR
  rw [outerBound, Metric.mem_closure_iff]
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
  have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
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
  have hlam : (c.avgError W).toReal ≤ ε := ENNReal.toReal_le_of_le_ofReal hε0.le hc
  set p := Interactive.inputLaw W c.toFn
  set a : Fin n → ℝ := fun i => I[fun x : (A₁ × A₂) × (B₁ × B₂) => x.1.1 : fun x => x.2.2 |
    fun x => x.1.2 ; W.jointMeasure (p i)]
  set b : Fin n → ℝ := fun i => I[fun x : (A₁ × A₂) × (B₁ × B₂) => x.1.2 : fun x => x.2.1 |
    fun x => x.1.1 ; W.jointMeasure (p i)]
  have ha : ∀ i, 0 ≤ a i := fun i => condMutualInfo_nonneg _ (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)
  have hb : ∀ i, 0 ≤ b i := fun i => condMutualInfo_nonneg _ (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)
  have B1 := one_sub_mul_log_card_le₁ c W
  have B2 := one_sub_mul_log_card_le₂ c W
  rw [Fintype.card_fin] at B1 B2
  have hl₁ : n * R.1 ≤ Real.log k₁ := (Real.le_log_iff_exp_le hk₁0).2 hk₁
  have hl₂ : n * R.2 ≤ Real.log k₂ := (Real.le_log_iff_exp_le hk₂0).2 hk₂
  have hx₀ := rate_bound (S := ∑ i, a i) hnpos hR1 hlam hε1 hl₁ B1
  have hy₀ := rate_bound (S := ∑ i, b i) hnpos hR2 hlam hε1 hl₂ B2
  set x₀ := (1 - ε) * R.1 - Real.log 2 / n
  set y₀ := (1 - ε) * R.2 - Real.log 2 / n
  have sa : 0 ≤ ∑ i, a i := sum_nonneg fun i _ => ha i
  have sb : 0 ≤ ∑ i, b i := sum_nonneg fun i _ => hb i
  have hx : (Fintype.card (Fin n) : ℝ) * max x₀ 0 ≤ ∑ i, a i := by
    rw [Fintype.card_fin]
    rcases le_total x₀ 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact sa
    · rw [max_eq_left h]
      exact hx₀
  have hy : (Fintype.card (Fin n) : ℝ) * max y₀ 0 ≤ ∑ i, b i := by
    rw [Fintype.card_fin]
    rcases le_total y₀ 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact sb
    · rw [max_eq_left h]
      exact hy₀
  have hmem := MAC.mem_convexHull_of_sum_le (fun i : Fin n => rectangle W (p i)) a b
    (fun i => a i + b i) (fun i R h1 h2 h3 h4 _ => ⟨h1, h2, h3, h4⟩)
    (fun i => le_add_of_nonneg_right (hb i)) (fun i => le_add_of_nonneg_left (ha i))
    (fun i => le_rfl) (le_max_right _ _) (le_max_right _ _) hx hy
    (by rw [mul_add, sum_add_distrib]; exact add_le_add hx hy)
  have hsub : (⋃ i : Fin n, rectangle W (p i)) ⊆ ⋃ q : PMF (A₁ × A₂), rectangle W q :=
    fun x hx => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact Set.mem_iUnion.2 ⟨p i, hi⟩
  refine ⟨(max x₀ 0, max y₀ 0), convexHull_mono hsub hmem, ?_⟩
  have hl0 : 0 ≤ Real.log 2 / n := div_nonneg hlog2 hnpos.le
  have d1 := dist_max_le hR1 hε0.le hl0
  have d2 := dist_max_le hR2 hε0.le hl0
  have e1 : ε * R.1 ≤ ε * (R.1 + R.2 + 1) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
  have e2 : ε * R.2 ≤ ε * (R.1 + R.2 + 1) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨d1.trans_lt (by linarith), d2.trans_lt (by linarith)⟩

theorem closure_achievableRegion_subset_outerBound (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    closure (achievableRegion W) ⊆ outerBound W :=
  closure_minimal (fun _ hR => mem_outerBound_of_mem_achievableRegion W hR) isClosed_closure

end TwoWay

end Meat
