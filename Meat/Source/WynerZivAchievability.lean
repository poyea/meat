import Meat.Shannon.Covering
import Meat.Shannon.StrongCovering
import Meat.Source.WynerZivEncoder
import Meat.Source.WynerZiv

open MeasureTheory Finset Filter Topology
open scoped ENNReal

namespace Meat

namespace WynerZiv

open RateDistortion

section Typical

variable {A U B : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
  [Fintype B] [DecidableEq B]

theorem strongTypicalSet_mono {r : A → ℝ} {n : ℕ} {ε ε' : ℝ} (h : ε ≤ ε') :
    strongTypicalSet r n ε ⊆ strongTypicalSet r n ε' :=
  fun _ hx => mem_strongTypicalSet.2 fun a => (mem_strongTypicalSet.1 hx a).trans h

theorem mem_strongTypicalSet_swap {n : ℕ} {x : Fin n → A} {u : Fin n → U} {p : A × U → ℝ}
    {ε : ℝ} : (fun i => (x i, u i)) ∈ strongTypicalSet p n ε ↔
      (fun i => (u i, x i)) ∈ strongTypicalSet (fun z => p (z.2, z.1)) n ε := by
  have hc : ∀ a b, typeCount (fun i => (u i, x i)) (b, a) =
      typeCount (fun i => (x i, u i)) (a, b) :=
    fun a b => by simp only [typeCount, Prod.mk.injEq, and_comm]
  simp only [mem_strongTypicalSet]
  constructor
  · rintro h ⟨b, a⟩
    rw [hc]
    exact h (a, b)
  · rintro h ⟨a, b⟩
    rw [← hc]
    exact h (b, a)

theorem mem_strongTypicalSet_marginal {n : ℕ} {u : Fin n → U} {x : Fin n → A} {y : Fin n → B}
    {r : (U × A) × B → ℝ} {ε : ℝ}
    (h : (fun i => ((u i, x i), y i)) ∈ strongTypicalSet r n ε) :
    (fun i => (y i, u i)) ∈ strongTypicalSet (fun z => ∑ a, r ((z.2, a), z.1)) n
      (Fintype.card A * ε) := by
  rw [mem_strongTypicalSet] at h ⊢
  rintro ⟨b, c⟩
  have hc : (typeCount (fun i => (y i, u i)) (b, c) : ℝ) =
      ∑ a, (typeCount (fun i => ((u i, x i), y i)) ((c, a), b) : ℝ) := by
    rw [← Nat.cast_sum]
    congr 1
    unfold typeCount
    rw [card_eq_sum_card_fiberwise (f := x) (t := univ) fun _ _ => mem_univ _]
    refine sum_congr rfl fun a _ => ?_
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq]
    tauto
  rw [hc, sum_div, ← sum_sub_distrib]
  calc |∑ a, ((typeCount (fun i => ((u i, x i), y i)) ((c, a), b) : ℝ) / n - r ((c, a), b))|
      ≤ ∑ a, |(typeCount (fun i => ((u i, x i), y i)) ((c, a), b) : ℝ) / n - r ((c, a), b)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : A, ε := sum_le_sum fun a _ => h ((c, a), b)
    _ = Fintype.card A * ε := by rw [sum_const, card_univ, nsmul_eq_mul]

end Typical

section Laws

variable {S T : Type*} {m : ℕ}

noncomputable def lawXU [Fintype T] (q : PMF (S × T × Fin m)) (z : S × Fin m) : ℝ :=
  ∑ y, (q (z.1, y, z.2)).toReal

noncomputable def lawYU [Fintype S] (q : PMF (S × T × Fin m)) (z : T × Fin m) : ℝ :=
  ∑ x, (q (x, z.1, z.2)).toReal

private noncomputable def lawX [Fintype T] (q : PMF (S × T × Fin m)) (x : S) : ℝ :=
  ∑ y, ∑ u, (q (x, y, u)).toReal

private noncomputable def lawXY (q : PMF (S × T × Fin m)) (x : S) (y : T) : ℝ :=
  ∑ u, (q (x, y, u)).toReal

private lemma lawXY_nonneg (q : PMF (S × T × Fin m)) (x : S) (y : T) : 0 ≤ lawXY q x y :=
  sum_nonneg fun _ _ => ENNReal.toReal_nonneg

private lemma sum_lawXY [Fintype T] (q : PMF (S × T × Fin m)) (x : S) :
    ∑ y, lawXY q x y = lawX q x := rfl

private lemma lawX_nonneg [Fintype T] (q : PMF (S × T × Fin m)) (x : S) : 0 ≤ lawX q x :=
  sum_nonneg fun y _ => lawXY_nonneg q x y

private lemma le_lawX [Fintype T] (q : PMF (S × T × Fin m)) (x : S) (y : T) (u : Fin m) :
    (q (x, y, u)).toReal ≤ lawX q x :=
  (single_le_sum (f := fun u' => (q (x, y, u')).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (mem_univ u)).trans (single_le_sum (f := fun y' => lawXY q x y')
      (fun y' _ => lawXY_nonneg q x y') (mem_univ y))

private lemma sum_lawYU [Fintype S] [Fintype T] (q : PMF (S × T × Fin m)) (u : Fin m) :
    ∑ y, lawYU q (y, u) = ∑ x, lawXU q (x, u) := by
  simp only [lawYU, lawXU]
  exact sum_comm

private lemma sum_lawXU [Fintype T] (q : PMF (S × T × Fin m)) (x : S) :
    ∑ u, lawXU q (x, u) = lawX q x := by
  simp only [lawXU, lawX]
  exact sum_comm

private lemma sum_fst_eq [Fintype S] [DecidableEq S] [Fintype T] (x : S)
    (F : S × T × Fin m → ℝ) :
    ∑ ω : S × T × Fin m, (if ω.1 = x then F ω else 0) = ∑ y, ∑ u, F (x, y, u) := by
  rw [Fintype.sum_prod_type, sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
  simp [Fintype.sum_prod_type]

private lemma c_xu [Fintype S] [DecidableEq S] [Fintype T] (F : S × T × Fin m → ℝ) (x : S)
    (u : Fin m) :
    ∑ ω : S × T × Fin m, (if (ω.1, ω.2.2) = (x, u) then F ω else 0) = ∑ y, F (x, y, u) := by
  rw [sum_congr rfl fun ω _ => show (if (ω.1, ω.2.2) = (x, u) then F ω else 0) =
      if ω.1 = x then (if ω.2.2 = u then F ω else 0) else 0 by
    by_cases h1 : ω.1 = x <;> by_cases h2 : ω.2.2 = u <;> simp [h1, h2]]
  rw [sum_fst_eq]
  simp

private lemma c_u [Fintype S] [Fintype T] (F : S × T × Fin m → ℝ) (u : Fin m) :
    ∑ ω : S × T × Fin m, (if ω.2.2 = u then F ω else 0) = ∑ x, ∑ y, F (x, y, u) := by
  simp [Fintype.sum_prod_type]

private lemma c_y [Fintype S] [Fintype T] [DecidableEq T] (F : S × T × Fin m → ℝ) (y : T) :
    ∑ ω : S × T × Fin m, (if ω.2.1 = y then F ω else 0) = ∑ x, ∑ u, F (x, y, u) := by
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
  simp

private lemma c_yu [Fintype S] [Fintype T] [DecidableEq T] (F : S × T × Fin m → ℝ) (y : T)
    (u : Fin m) :
    ∑ ω : S × T × Fin m, (if (ω.2.1, ω.2.2) = (y, u) then F ω else 0) = ∑ x, F (x, y, u) := by
  simp only [Fintype.sum_prod_type, Prod.mk.injEq]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
  simp

private lemma toReal_map_U [Fintype S] [Fintype T] (q : PMF (S × T × Fin m)) (u : Fin m) :
    ((q.map fun a => a.2.2) u).toReal = ∑ x, lawXU q (x, u) := by
  classical
  rw [toReal_map_apply, sum_filter, c_u]
  rfl

private lemma toReal_map_fst_pair [Finite S] [Fintype T] (q : PMF (S × T × Fin m)) (x : S) :
    (((q.map fun a => (a.1, a.2.1)).map Prod.fst) x).toReal = lawX q x := by
  classical
  have := Fintype.ofFinite S
  rw [PMF.map_comp, toReal_map_apply, sum_filter]
  exact sum_fst_eq x _

theorem toReal_map_pair [Finite S] [Finite T] (q : PMF (S × T × Fin m)) (x : S) (y : T) :
    ((q.map fun a => (a.1, a.2.1)) (x, y)).toReal = ∑ u, (q (x, y, u)).toReal := by
  classical
  have := Fintype.ofFinite S
  have := Fintype.ofFinite T
  rw [toReal_map_apply, sum_filter]
  rw [sum_congr rfl fun ω _ => show (if (ω.1, ω.2.1) = (x, y) then (q ω).toReal else 0) =
      if ω.1 = x then (if ω.2.1 = y then (q ω).toReal else 0) else 0 by
    by_cases h1 : ω.1 = x <;> by_cases h2 : ω.2.1 = y <;> simp [h1, h2]]
  rw [sum_fst_eq, sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
  simp

noncomputable def condChannel [Fintype T] (q : PMF (S × T × Fin m)) (t₀ : T) (x : S) :
    PMF T := by
  classical
  exact if h : lawX q x = 0 then PMF.pure t₀ else
    PMF.ofFintype (fun y => ENNReal.ofReal (lawXY q x y / lawX q x)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun y _ =>
        div_nonneg (lawXY_nonneg q x y) (lawX_nonneg q x), ← sum_div,
        sum_lawXY, div_self h, ENNReal.ofReal_one])

private lemma condChannel_toReal [Fintype T] [DecidableEq T] (q : PMF (S × T × Fin m)) (t₀ : T)
    (x : S) (y : T) :
    (condChannel q t₀ x y).toReal =
      if lawX q x = 0 then (if y = t₀ then 1 else 0) else lawXY q x y / lawX q x := by
  unfold condChannel
  split_ifs with h h'
  · simp [h']
  · simp [PMF.pure_apply, h']
  · rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal
      (div_nonneg (lawXY_nonneg q x y) (lawX_nonneg q x))]

private lemma lawXY_eq_mul [Fintype T] (q : PMF (S × T × Fin m)) (t₀ : T) (x : S) (y : T) :
    lawXY q x y = lawX q x * (condChannel q t₀ x y).toReal := by
  classical
  rw [condChannel_toReal]
  by_cases h : lawX q x = 0
  · have : lawXY q x y ≤ 0 := h ▸ single_le_sum (f := fun y' => lawXY q x y')
      (fun y' _ => lawXY_nonneg q x y') (mem_univ y)
    rw [le_antisymm this (lawXY_nonneg q x y), h, zero_mul]
  · simp only [h, ite_false]
    rw [mul_div_cancel₀ _ h]

private lemma iidProb_pair_eq [Finite S] [Fintype T] (q : PMF (S × T × Fin m)) (t₀ : T)
    {n : ℕ} (x : Fin n → S) (y : Fin n → T) :
    iidProb (q.map fun a => (a.1, a.2.1)) (fun i => (x i, y i)) =
      iidProb ((q.map fun a => (a.1, a.2.1)).map Prod.fst) x *
        ∏ i, (condChannel q t₀ (x i) (y i)).toReal := by
  simp only [iidProb, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [toReal_map_pair, toReal_map_fst_pair, ← lawXY_eq_mul q t₀]
  rfl

private noncomputable def law3 (q : PMF (S × T × Fin m)) (t : (Fin m × S) × T) : ℝ :=
  (q (t.1.2, t.2, t.1.1)).toReal

end Laws

section Measure

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {m : ℕ}

private lemma real_setOf (q : PMF (S × T × Fin m)) (P : S × T × Fin m → Prop)
    [DecidablePred P] :
    q.toMeasure.real {ω | P ω} = ∑ ω, if P ω then (q ω).toReal else 0 := by
  rw [measureReal_def, PMF.toMeasure_apply_fintype, ENNReal.toReal_sum fun _ _ =>
    ne_top_of_le_ne_top (PMF.apply_ne_top _ _) (Set.indicator_le_self _ _ _)]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : P ω
  · simp [h]
  · simp [h]

private lemma entropy_eq_sum {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] [DecidableEq W] (q : PMF (S × T × Fin m))
    (f : S × T × Fin m → W) :
    H[f ; q.toMeasure] = ∑ w, Real.negMulLog (∑ ω, if f ω = w then (q ω).toReal else 0) := by
  rw [entropy_def]
  refine sum_congr rfl fun w _ => congrArg _ ?_
  rw [measureReal_map_singleton, sum_filter]
  refine sum_congr rfl fun ω _ => ?_
  split_ifs
  · rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  · rfl

private lemma markov_factor (q : PMF (S × T × Fin m))
    (hM : MarkovChain (fun a : S × T × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) (x : S) (y : T) (u : Fin m) :
    (q (x, y, u)).toReal * lawX q x = lawXU q (x, u) * lawXY q x y := by
  classical
  have h := (markovChain_iff (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _)).1 hM u x y
  have m1 : q.toMeasure.real {ω : S × T × Fin m | ω.2.2 = u ∧ ω.1 = x ∧ ω.2.1 = y} =
      (q (x, y, u)).toReal := by
    have : {ω : S × T × Fin m | ω.2.2 = u ∧ ω.1 = x ∧ ω.2.1 = y} = {(x, y, u)} := by
      ext ⟨a, b, c⟩
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
      tauto
    rw [this, measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have m2 : q.toMeasure.real {ω : S × T × Fin m | ω.1 = x} = lawX q x := by
    rw [real_setOf, sum_fst_eq]
    rfl
  have m3 : q.toMeasure.real {ω : S × T × Fin m | ω.2.2 = u ∧ ω.1 = x} = lawXU q (x, u) := by
    rw [real_setOf]
    rw [sum_congr rfl fun ω _ => show (if ω.2.2 = u ∧ ω.1 = x then (q ω).toReal else 0) =
      if ω.1 = x then (if ω.2.2 = u then (q ω).toReal else 0) else 0 by
        by_cases h1 : ω.1 = x <;> by_cases h2 : ω.2.2 = u <;> simp [h1, h2]]
    rw [sum_fst_eq]
    simp [lawXU]
  have m4 : q.toMeasure.real {ω : S × T × Fin m | ω.1 = x ∧ ω.2.1 = y} = lawXY q x y := by
    rw [real_setOf]
    rw [sum_congr rfl fun ω _ => show (if ω.1 = x ∧ ω.2.1 = y then (q ω).toReal else 0) =
      if ω.1 = x then (if ω.2.1 = y then (q ω).toReal else 0) else 0 by
        by_cases h1 : ω.1 = x <;> by_cases h2 : ω.2.1 = y <;> simp [h1, h2]]
    rw [sum_fst_eq, sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
    simp [lawXY]
  rw [m1, m2, m3, m4] at h
  exact h

private lemma eq_lawXU_mul_condChannel (q : PMF (S × T × Fin m))
    (hM : MarkovChain (fun a : S × T × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) (t₀ : T) (x : S) (y : T) (u : Fin m) :
    (q (x, y, u)).toReal = lawXU q (x, u) * (condChannel q t₀ x y).toReal := by
  classical
  rw [condChannel_toReal]
  by_cases h : lawX q x = 0
  · have h1 : (q (x, y, u)).toReal ≤ 0 := h ▸ le_lawX q x y u
    have h2 : lawXU q (x, u) ≤ 0 := h ▸ by
      rw [lawXU, lawX, sum_comm]
      exact single_le_sum (f := fun u' => ∑ y', (q (x, y', u')).toReal)
        (fun _ _ => sum_nonneg fun _ _ => ENNReal.toReal_nonneg) (mem_univ u)
    rw [le_antisymm h1 ENNReal.toReal_nonneg, le_antisymm h2
      (sum_nonneg fun _ _ => ENNReal.toReal_nonneg), zero_mul]
  · simp only [h, ite_false]
    have := markov_factor q hM x y u
    field_simp
    linarith

private lemma law3_eq (q : PMF (S × T × Fin m))
    (hM : MarkovChain (fun a : S × T × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) (t₀ : T) :
    (fun t : (Fin m × S) × T => lawXU q (t.1.2, t.1.1) * (condChannel q t₀ t.1.2 t.2).toReal) =
      law3 q :=
  funext fun _ => (eq_lawXU_mul_condChannel q hM t₀ _ _ _).symm

private lemma entropy_X (q : PMF (S × T × Fin m)) :
    H[fun a : S × T × Fin m => a.1 ; q.toMeasure] =
      ∑ x, Real.negMulLog (∑ u, lawXU q (x, u)) := by
  classical
  rw [entropy_eq_sum]
  refine sum_congr rfl fun x _ => congrArg _ ?_
  rw [sum_fst_eq]
  simp only [lawXU]
  exact sum_comm

private lemma entropy_U (q : PMF (S × T × Fin m)) :
    H[fun a : S × T × Fin m => a.2.2 ; q.toMeasure] =
      ∑ u, Real.negMulLog (∑ x, lawXU q (x, u)) := by
  classical
  rw [entropy_eq_sum]
  exact sum_congr rfl fun u _ => congrArg _ (c_u _ u)

private lemma entropy_XU (q : PMF (S × T × Fin m)) :
    H[fun a : S × T × Fin m => (a.1, a.2.2) ; q.toMeasure] =
      ∑ z, Real.negMulLog (lawXU q z) := by
  classical
  rw [entropy_eq_sum]
  exact sum_congr rfl fun z _ => congrArg _ (c_xu _ z.1 z.2)

private lemma entropy_Y (q : PMF (S × T × Fin m)) :
    H[fun a : S × T × Fin m => a.2.1 ; q.toMeasure] =
      ∑ y, Real.negMulLog (∑ u, lawYU q (y, u)) := by
  classical
  rw [entropy_eq_sum]
  refine sum_congr rfl fun y _ => congrArg _ ?_
  rw [c_y]
  simp only [lawYU]
  exact sum_comm

private lemma entropy_YU (q : PMF (S × T × Fin m)) :
    H[fun a : S × T × Fin m => (a.2.1, a.2.2) ; q.toMeasure] =
      ∑ z, Real.negMulLog (lawYU q z) := by
  classical
  rw [entropy_eq_sum]
  exact sum_congr rfl fun z _ => congrArg _ (c_yu _ z.1 z.2)

theorem mutualInfo_eq_jointInfo (q : PMF (S × T × Fin m)) :
    I[fun a : S × T × Fin m => a.1 : fun a => a.2.2 ; q.toMeasure] = jointInfo (lawXU q) := by
  rw [mutualInfo_def, entropy_X, entropy_U, entropy_XU, jointInfo]

theorem condMutualInfo_eq_jointInfo_sub (q : PMF (S × T × Fin m))
    (hM : MarkovChain (fun a : S × T × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) :
    I[fun a : S × T × Fin m => a.1 : fun a => a.2.2 | fun a => a.2.1 ; q.toMeasure] =
      jointInfo (lawXU q) - jointInfo (lawYU q) := by
  set μ := q.toMeasure
  set X : S × T × Fin m → S := fun a => a.1
  set Y : S × T × Fin m → T := fun a => a.2.1
  set U : S × T × Fin m → Fin m := fun a => a.2.2
  have hm := hM
  rw [markovChain_def, condMutualInfo_def, condEntropy_def, condEntropy_def,
    condEntropy_def] at hm
  have r1 : H[fun ω => (U ω, X ω) ; μ] = H[fun ω => (X ω, U ω) ; μ] := entropy_comm μ
  have r2 : H[fun ω => (Y ω, X ω) ; μ] = H[fun ω => (X ω, Y ω) ; μ] := entropy_comm μ
  have r3 : H[fun ω => ((U ω, Y ω), X ω) ; μ] = H[fun ω => ((X ω, U ω), Y ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, U ω), Y ω))
      (f := fun t => ((t.1.2, t.2), t.1.1)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.2 h.1.1) h.1.2
  have r4 : H[fun ω => (U ω, Y ω) ; μ] = H[fun ω => (Y ω, U ω) ; μ] := entropy_comm μ
  have hU' : H[U ; μ] = ∑ u, Real.negMulLog (∑ y, lawYU q (y, u)) := by
    rw [entropy_U]
    simp only [sum_lawYU]
  have hX := entropy_X q
  have hU := entropy_U q
  have hXU := entropy_XU q
  have hY := entropy_Y q
  have hYU := entropy_YU q
  rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def]
  simp only [jointInfo]
  rw [← hX, ← hU, ← hXU, ← hY, ← hU', ← hYU]
  rw [r1, r2, r3] at hm
  rw [r4] at *
  linarith

theorem jointInfo_lawXU_nonneg (q : PMF (S × T × Fin m)) : 0 ≤ jointInfo (lawXU q) :=
  mutualInfo_eq_jointInfo q ▸ mutualInfo_nonneg _ (measurable_of_finite _)
    (measurable_of_finite _)

end Measure

section Code

variable {S T V : Type*} {m n K k : ℕ}

private noncomputable def coverIndex (Tc : Finset (Fin n → S × Fin m))
    (C : Fin K → Fin n → Fin m) (l₀ : Fin K) (x : Fin n → S) : Fin K := by
  classical
  exact if h : ∃ l, (fun i => (x i, C l i)) ∈ Tc then h.choose else l₀

private noncomputable def binIndex (Tp : Finset (Fin n → T × Fin m))
    (C : Fin K → Fin n → Fin m) (β : Fin K → Fin k) (l₀ : Fin K) (b : Fin k) (y : Fin n → T) :
    Fin K := by
  classical
  exact if h : ∃ l, β l = b ∧ (fun i => (y i, C l i)) ∈ Tp then h.choose else l₀

private noncomputable def binCode (g : Fin m × T → V) (Tc : Finset (Fin n → S × Fin m))
    (Tp : Finset (Fin n → T × Fin m)) (C : Fin K → Fin n → Fin m) (β : Fin K → Fin k)
    (l₀ : Fin K) : WZCode S T V n k :=
  ⟨fun x => β (coverIndex Tc C l₀ x),
    fun b i => g (C (binIndex Tp C β l₀ b.1 b.2) i, b.2 i)⟩

private lemma coverIndex_mem {Tc : Finset (Fin n → S × Fin m)} {C : Fin K → Fin n → Fin m}
    (l₀ : Fin K) {x : Fin n → S} (h : ∃ l, (fun i => (x i, C l i)) ∈ Tc) :
    (fun i => (x i, C (coverIndex Tc C l₀ x) i)) ∈ Tc := by
  simp only [coverIndex, h, dite_true]
  exact h.choose_spec

private lemma binIndex_spec {Tp : Finset (Fin n → T × Fin m)} {C : Fin K → Fin n → Fin m}
    {β : Fin K → Fin k} (l₀ : Fin K) {b : Fin k} {y : Fin n → T}
    (h : ∃ l, β l = b ∧ (fun i => (y i, C l i)) ∈ Tp) :
    β (binIndex Tp C β l₀ b y) = b ∧ (fun i => (y i, C (binIndex Tp C β l₀ b y) i)) ∈ Tp := by
  simp only [binIndex, h, dite_true]
  exact h.choose_spec

private lemma blockDist_binCode_le (d : S → V → ℝ)
    (g : Fin m × T → V) {Tc : Finset (Fin n → S × Fin m)} {Tp : Finset (Fin n → T × Fin m)}
    {T3 : Finset (Fin n → (Fin m × S) × T)} {E M : ℝ} (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hmarg : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      (fun i => ((u i, x i), y i)) ∈ T3 → (fun i => (y i, u i)) ∈ Tp)
    (hdist : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      (fun i => ((u i, x i), y i)) ∈ T3 → blockDist d x (fun i => g (u i, y i)) ≤ E)
    (hbd : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      blockDist d x (fun i => g (u i, y i)) ≤ M)
    (C : Fin K → Fin n → Fin m) (β : Fin K → Fin k) (l₀ : Fin K) (x : Fin n → S)
    (y : Fin n → T) [Decidable (∀ l, (fun i => (x i, C l i)) ∉ Tc)]
    [Decidable ((∃ l, (fun i => (x i, C l i)) ∈ Tc) ∧
      (fun i => ((C (coverIndex Tc C l₀ x) i, x i), y i)) ∉ T3)]
    [Decidable (∃ l, l ≠ coverIndex Tc C l₀ x ∧ β l = β (coverIndex Tc C l₀ x) ∧
      (fun i => (y i, C l i)) ∈ Tp)] :
    blockDist d x ((binCode g Tc Tp C β l₀).dec ((binCode g Tc Tp C β l₀).enc x, y)) ≤
      E + M * ((if ∀ l, (fun i => (x i, C l i)) ∉ Tc then 1 else 0) +
        (if (∃ l, (fun i => (x i, C l i)) ∈ Tc) ∧
          (fun i => ((C (coverIndex Tc C l₀ x) i, x i), y i)) ∉ T3 then 1 else 0) +
        (if ∃ l, l ≠ coverIndex Tc C l₀ x ∧ β l = β (coverIndex Tc C l₀ x) ∧
          (fun i => (y i, C l i)) ∈ Tp then 1 else 0)) := by
  change blockDist d x
    (fun i => g (C (binIndex Tp C β l₀ (β (coverIndex Tc C l₀ x)) y) i, y i)) ≤ _
  have hb := hbd (C (binIndex Tp C β l₀ (β (coverIndex Tc C l₀ x)) y)) x y
  split_ifs with h1 <;> try linarith
  rename_i h2 h3
  have h1' : ∃ l, (fun i => (x i, C l i)) ∈ Tc := by simpa using h1
  have h2' : (fun i => ((C (coverIndex Tc C l₀ x) i, x i), y i)) ∈ T3 := by
    by_contra h
    exact h2 ⟨h1', h⟩
  have hs := binIndex_spec (β := β) l₀ ⟨coverIndex Tc C l₀ x, rfl, hmarg _ _ _ h2'⟩
  have hL : binIndex Tp C β l₀ (β (coverIndex Tc C l₀ x)) y = coverIndex Tc C l₀ x := by
    by_contra hne
    exact h3 ⟨_, hne, hs.1, hs.2⟩
  rw [hL]
  simpa using hdist _ _ _ h2'

end Code

section Average

variable {S T V : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T] {m n K k : ℕ}

omit [Fintype S] [Fintype T] in
private lemma avg_bins (d : S → V → ℝ) (g : Fin m × T → V) {Tc : Finset (Fin n → S × Fin m)}
    {Tp : Finset (Fin n → T × Fin m)} {T3 : Finset (Fin n → (Fin m × S) × T)} {E M : ℝ}
    (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hmarg : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      (fun i => ((u i, x i), y i)) ∈ T3 → (fun i => (y i, u i)) ∈ Tp)
    (hdist : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      (fun i => ((u i, x i), y i)) ∈ T3 → blockDist d x (fun i => g (u i, y i)) ≤ E)
    (hbd : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      blockDist d x (fun i => g (u i, y i)) ≤ M)
    (hk : 0 < k) (C : Fin K → Fin n → Fin m) (l₀ : Fin K) (x : Fin n → S) (y : Fin n → T) :
    ∑ β : Fin K → Fin k, (∏ _l : Fin K, (k : ℝ)⁻¹) *
        blockDist d x ((binCode g Tc Tp C β l₀).dec ((binCode g Tc Tp C β l₀).enc x, y)) ≤
      E + M * ((if ∀ l, (fun i => (x i, C l i)) ∉ Tc then 1 else 0) +
        (if (∃ l, (fun i => (x i, C l i)) ∈ Tc) ∧
          (fun i => ((C (coverIndex Tc C l₀ x) i, x i), y i)) ∉ T3 then 1 else 0) +
        (k : ℝ)⁻¹ * ∑ l, if (fun i => (y i, C l i)) ∈ Tp then 1 else 0) := by
  set F1 : ℝ := if ∀ l, (fun i => (x i, C l i)) ∉ Tc then 1 else 0
  set F2 : ℝ := if (∃ l, (fun i => (x i, C l i)) ∈ Tc) ∧
    (fun i => ((C (coverIndex Tc C l₀ x) i, x i), y i)) ∉ T3 then 1 else 0
  have hw0 : (0 : ℝ) ≤ ∏ _l : Fin K, (k : ℝ)⁻¹ := prod_nonneg fun _ _ => by positivity
  have hbins := sum_bins_le hk (coverIndex Tc C l₀ x) (fun l => (fun i => (y i, C l i)) ∈ Tp)
  have h1 := sum_uniform (ι := Fin K) hk
  calc _ ≤ ∑ β : Fin K → Fin k, (∏ _l : Fin K, (k : ℝ)⁻¹) * (E + M * (F1 + F2 +
          (if ∃ l, l ≠ coverIndex Tc C l₀ x ∧ β l = β (coverIndex Tc C l₀ x) ∧
            (fun i => (y i, C l i)) ∈ Tp then 1 else 0))) :=
        sum_le_sum fun β _ => mul_le_mul_of_nonneg_left
          (blockDist_binCode_le d g hE hM hmarg hdist hbd C β l₀ x y) hw0
    _ = (E + M * (F1 + F2)) * ∑ β : Fin K → Fin k, (∏ _l : Fin K, (k : ℝ)⁻¹) +
        M * ∑ β : Fin K → Fin k, (∏ _l : Fin K, (k : ℝ)⁻¹) *
          (if ∃ l, l ≠ coverIndex Tc C l₀ x ∧ β l = β (coverIndex Tc C l₀ x) ∧
            (fun i => (y i, C l i)) ∈ Tp then 1 else 0) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun β _ => by ring
    _ ≤ _ := by
        rw [h1]
        nlinarith [mul_le_mul_of_nonneg_left hbins hM]

omit [Fintype S] [Fintype T] in
private lemma avg_codebook (d : S → V → ℝ) (g : Fin m × T → V)
    {Tc : Finset (Fin n → S × Fin m)} {Tp : Finset (Fin n → T × Fin m)}
    {T3 : Finset (Fin n → (Fin m × S) × T)} {E M : ℝ} (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hmarg : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      (fun i => ((u i, x i), y i)) ∈ T3 → (fun i => (y i, u i)) ∈ Tp)
    (hdist : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      (fun i => ((u i, x i), y i)) ∈ T3 → blockDist d x (fun i => g (u i, y i)) ≤ E)
    (hbd : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      blockDist d x (fun i => g (u i, y i)) ≤ M)
    (hk : 0 < k) (qU : PMF (Fin m)) (l₀ : Fin K) (x : Fin n → S) (y : Fin n → T) :
    ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb qU (C l)) *
      ∑ β : Fin K → Fin k, (∏ _l : Fin K, (k : ℝ)⁻¹) *
        blockDist d x ((binCode g Tc Tp C β l₀).dec ((binCode g Tc Tp C β l₀).enc x, y)) ≤
      E + M * ((1 - ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (x i, u i)) ∈ Tc),
          iidProb qU u) ^ K +
        ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb qU (C l)) *
          (if (∃ l, (fun i => (x i, C l i)) ∈ Tc) ∧
            (fun i => ((C (coverIndex Tc C l₀ x) i, x i), y i)) ∉ T3 then 1 else 0) +
        (k : ℝ)⁻¹ * (K * ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tp),
          iidProb qU u)) := by
  set w : (Fin K → Fin n → Fin m) → ℝ := fun C => ∏ l, iidProb qU (C l) with hw
  have hw0 : ∀ C, 0 ≤ w C := fun C => prod_nonneg fun _ _ => iidProb_nonneg _ _
  have hw1 : ∑ C, w C = 1 := sum_prod _ fun _ => sum_iidProb qU n
  have e1 : ∑ C, w C * (if ∀ l, (fun i => (x i, C l i)) ∉ Tc then 1 else 0) =
      (1 - ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (x i, u i)) ∈ Tc),
        iidProb qU u) ^ K := by
    rw [← sum_codebook_not_mem]
    exact sum_congr rfl fun C _ => by simp [w]
  have e3 : ∀ l : Fin K, ∑ C, w C * (if (fun i => (y i, C l i)) ∈ Tp then 1 else 0) =
      ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tp), iidProb qU u :=
    fun l => by
      rw [← sum_codebook_apply_mem qU _ l]
      exact sum_congr rfl fun C _ => by simp [w]
  have e4 : ∑ C, w C * ((k : ℝ)⁻¹ * ∑ l, if (fun i => (y i, C l i)) ∈ Tp then 1 else 0) =
      (k : ℝ)⁻¹ * (K * ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tp),
        iidProb qU u) := by
    have h : ∀ C, w C * ((k : ℝ)⁻¹ * ∑ l, if (fun i => (y i, C l i)) ∈ Tp then 1 else 0) =
        (k : ℝ)⁻¹ * ∑ l, w C * (if (fun i => (y i, C l i)) ∈ Tp then 1 else 0) := fun C => by
      rw [mul_sum, mul_sum, mul_sum]
      exact sum_congr rfl fun l _ => by ring
    rw [sum_congr rfl fun C _ => h C, ← mul_sum, sum_comm, sum_congr rfl fun l _ => e3 l,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc _ ≤ ∑ C, w C * (E + M * ((if ∀ l, (fun i => (x i, C l i)) ∉ Tc then 1 else 0) +
          (if (∃ l, (fun i => (x i, C l i)) ∈ Tc) ∧
            (fun i => ((C (coverIndex Tc C l₀ x) i, x i), y i)) ∉ T3 then 1 else 0) +
          (k : ℝ)⁻¹ * ∑ l, if (fun i => (y i, C l i)) ∈ Tp then 1 else 0)) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left
          (avg_bins d g hE hM hmarg hdist hbd hk C l₀ x y) (hw0 C)
    _ = _ := by
        simp only [mul_add, sum_add_distrib, mul_left_comm (w _) M, ← mul_sum,
          mul_comm (w _) E, hw1, e1, e4]
        ring

private lemma sum_mul_sum_sum_comm {α X Y : Type*} [Fintype α] [Fintype X] [Fintype Y]
    (w : α → ℝ) (P : X → Y → ℝ) (f : α → X → Y → ℝ) :
    ∑ a, w a * ∑ x, ∑ y, P x y * f a x y = ∑ x, ∑ y, P x y * ∑ a, w a * f a x y := by
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_congr rfl fun a _ => by ring

private lemma exists_binCode (p : PMF (S × T)) (d : S → V → ℝ) (g : Fin m × T → V)
    {Tc : Finset (Fin n → S × Fin m)} {Tp : Finset (Fin n → T × Fin m)}
    {T3 : Finset (Fin n → (Fin m × S) × T)} {E M : ℝ} (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hmarg : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      (fun i => ((u i, x i), y i)) ∈ T3 → (fun i => (y i, u i)) ∈ Tp)
    (hdist : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      (fun i => ((u i, x i), y i)) ∈ T3 → blockDist d x (fun i => g (u i, y i)) ≤ E)
    (hbd : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      blockDist d x (fun i => g (u i, y i)) ≤ M)
    (hk : 0 < k) (qU : PMF (Fin m)) (l₀ : Fin K) {a₁ a₂ a₃ : ℝ}
    (hA : ∑ x : Fin n → S, ∑ y : Fin n → T, iidProb p (fun i => (x i, y i)) *
      (1 - ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (x i, u i)) ∈ Tc),
        iidProb qU u) ^ K ≤ a₁)
    (hB : ∑ x : Fin n → S, ∑ y : Fin n → T, iidProb p (fun i => (x i, y i)) *
      ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb qU (C l)) *
        (if (∃ l, (fun i => (x i, C l i)) ∈ Tc) ∧
          (fun i => ((C (coverIndex Tc C l₀ x) i, x i), y i)) ∉ T3 then 1 else 0) ≤ a₂)
    (hC : ∀ y : Fin n → T,
      ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tp), iidProb qU u ≤ a₃) :
    ∃ c : WZCode S T V n k, c.distortion p d ≤ E + M * (a₁ + a₂ + (k : ℝ)⁻¹ * (K * a₃)) := by
  set P : (Fin n → S) → (Fin n → T) → ℝ := fun x y => iidProb p (fun i => (x i, y i)) with hP
  have hP0 : ∀ x y, 0 ≤ P x y := fun x y => iidProb_nonneg _ _
  have hP1 : ∑ x, ∑ y, P x y = 1 := by
    rw [← sum_iidProb p n, sum_arrow_prod]
  have hdist' : ∀ (C : Fin K → Fin n → Fin m) (β : Fin K → Fin k),
      (binCode g Tc Tp C β l₀).distortion p d = ∑ x, ∑ y, P x y *
        blockDist d x ((binCode g Tc Tp C β l₀).dec ((binCode g Tc Tp C β l₀).enc x, y)) :=
    fun C β => by
      rw [WZCode.distortion, sum_arrow_prod]
  have hwC0 : ∀ C : Fin K → Fin n → Fin m, 0 ≤ ∏ l, iidProb qU (C l) :=
    fun C => prod_nonneg fun _ _ => iidProb_nonneg _ _
  have hwC1 : ∑ C : Fin K → Fin n → Fin m, ∏ l, iidProb qU (C l) = 1 :=
    sum_prod _ fun _ => sum_iidProb qU n
  have hwβ0 : ∀ β : Fin K → Fin k, (0 : ℝ) ≤ ∏ _l : Fin K, (k : ℝ)⁻¹ :=
    fun _ => prod_nonneg fun _ _ => by positivity
  have hwβ1 := sum_uniform (ι := Fin K) hk
  have hCsum : ∑ x, ∑ y, P x y * ((k : ℝ)⁻¹ * (K *
      ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tp), iidProb qU u)) ≤
      (k : ℝ)⁻¹ * (K * a₃) := by
    calc _ ≤ ∑ x, ∑ y, P x y * ((k : ℝ)⁻¹ * (K * a₃)) :=
          sum_le_sum fun x _ => sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC y) (Nat.cast_nonneg K))
              (by positivity)) (hP0 x y)
      _ = _ := by rw [← sum_congr rfl fun x _ => sum_mul .., ← sum_mul, hP1, one_mul]
  set A : (Fin n → S) → ℝ := fun x => (1 - ∑ u ∈ univ.filter (fun u : Fin n → Fin m =>
    (fun i => (x i, u i)) ∈ Tc), iidProb qU u) ^ K
  set B : (Fin n → S) → (Fin n → T) → ℝ := fun x y => ∑ C : Fin K → Fin n → Fin m,
    (∏ l, iidProb qU (C l)) * (if (∃ l, (fun i => (x i, C l i)) ∈ Tc) ∧
      (fun i => ((C (coverIndex Tc C l₀ x) i, x i), y i)) ∉ T3 then 1 else 0)
  set G : (Fin n → T) → ℝ := fun y => (k : ℝ)⁻¹ * (K * ∑ u ∈ univ.filter
    (fun u : Fin n → Fin m => (fun i => (y i, u i)) ∈ Tp), iidProb qU u)
  have htot : ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb qU (C l)) *
      ∑ β : Fin K → Fin k, (∏ _l : Fin K, (k : ℝ)⁻¹) * (binCode g Tc Tp C β l₀).distortion p d ≤
      E + M * (a₁ + a₂ + (k : ℝ)⁻¹ * (K * a₃)) := by
    simp only [hdist']
    rw [sum_congr rfl fun C _ => by rw [sum_mul_sum_sum_comm], sum_mul_sum_sum_comm]
    calc _ ≤ ∑ x, ∑ y, P x y * (E + M * (A x + B x y + G y)) :=
          sum_le_sum fun x _ => sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
            (avg_codebook d g hE hM hmarg hdist hbd hk qU l₀ x y) (hP0 x y)
      _ = ∑ x, ∑ y, (E * P x y + M * (P x y * A x) + M * (P x y * B x y) +
          M * (P x y * G y)) :=
          sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
      _ = E * ∑ x, ∑ y, P x y + M * (∑ x, ∑ y, P x y * A x) + M * (∑ x, ∑ y, P x y * B x y) +
          M * (∑ x, ∑ y, P x y * G y) := by
          simp only [sum_add_distrib, ← mul_sum]
      _ ≤ _ := by
          rw [hP1, mul_one]
          have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hA hB) hCsum) hM
          linarith
  obtain ⟨C, hC'⟩ := exists_le_of_sum_mul_le hwC0 hwC1 htot
  obtain ⟨β, hβ⟩ := exists_le_of_sum_mul_le hwβ0 hwβ1 hC'
  exact ⟨binCode g Tc Tp C β l₀, hβ⟩

end Average

section Bounds

variable {S T : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [Fintype T] [DecidableEq T] [MeasurableSpace T]
  [MeasurableSingletonClass T] {m n : ℕ}

omit [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq T] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma cover_part (q : PMF (S × T × Fin m)) (K : ℕ) (hn : 0 < n)
    (Tc : Finset (Fin n → S × Fin m)) {ε a : ℝ} (hε : 0 < ε) (ha1 : a ≤ 1)
    (hcov : ∀ x : Fin n → S, (∀ s, |(typeCount x s : ℝ) / n - ∑ u, lawXU q (s, u)| ≤ ε) →
      (∀ s, ∑ u, lawXU q (s, u) = 0 → typeCount x s = 0) →
      a ≤ ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (x i, u i)) ∈ Tc),
        iidProb (q.map fun a => a.2.2) u) :
    ∑ x : Fin n → S, ∑ y : Fin n → T, iidProb (q.map fun a => (a.1, a.2.1))
        (fun i => (x i, y i)) *
      (1 - ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (x i, u i)) ∈ Tc),
        iidProb (q.map fun a => a.2.2) u) ^ K ≤
      Real.exp (-(K * a)) + Fintype.card S / (4 * n * ε ^ 2) := by
  set pX := (q.map fun a => (a.1, a.2.1)).map Prod.fst
  set qU := q.map fun a => a.2.2
  set σ : (Fin n → S) → ℝ := fun x =>
    ∑ u ∈ univ.filter (fun u : Fin n → Fin m => (fun i => (x i, u i)) ∈ Tc), iidProb qU u
  set Ty := strongTypicalSet (fun s => (pX s).toReal) n ε
  have hpX : ∀ s, (pX s).toReal = ∑ u, lawXU q (s, u) := fun s => by
    rw [toReal_map_fst_pair, sum_lawXU]
  have hσ0 : ∀ x, 0 ≤ σ x := fun x => sum_nonneg fun u _ => iidProb_nonneg _ _
  have hσ1 : ∀ x, σ x ≤ 1 := fun x => (sum_le_sum_of_subset_of_nonneg (subset_univ _)
    fun u _ _ => iidProb_nonneg _ _).trans_eq (sum_iidProb qU n)
  have hE0 : 0 ≤ Real.exp (-(K * a)) := (Real.exp_pos _).le
  have hbound : ∀ x, iidProb pX x * (1 - σ x) ^ K ≤
      iidProb pX x * Real.exp (-(K * a)) + (if x ∈ Ty then 0 else iidProb pX x) := by
    intro x
    have hp0 := iidProb_nonneg pX x
    have hpow1 : (1 - σ x) ^ K ≤ 1 := pow_le_one₀ (by linarith [hσ1 x]) (by linarith [hσ0 x])
    by_cases hT : x ∈ Ty
    · simp only [hT, ↓reduceIte, add_zero]
      by_cases hx0 : iidProb pX x = 0
      · rw [hx0, zero_mul, zero_mul]
      refine mul_le_mul_of_nonneg_left ?_ hp0
      have hsupp : ∀ s, ∑ u, lawXU q (s, u) = 0 → typeCount x s = 0 := fun s hs => by
        by_contra hc
        obtain ⟨i, hi⟩ : ∃ i, x i = s := by
          by_contra hne
          push Not at hne
          exact hc (by simp [typeCount, hne])
        exact hx0 (prod_eq_zero (mem_univ i) (by rw [hi, hpX, hs]))
      have ha := hcov x (fun s => by rw [← hpX]; exact mem_strongTypicalSet.1 hT s) hsupp
      have h1 := one_sub_mul_pow_le ha1 zero_le_one le_rfl K
      rw [mul_one, sub_self, zero_add] at h1
      exact (pow_le_pow_left₀ (by linarith [hσ1 x]) (by linarith) K).trans h1
    · simp only [hT, ↓reduceIte]
      nlinarith [mul_le_mul_of_nonneg_left hpow1 hp0]
  have hnot : ∑ x : Fin n → S, (if x ∈ Ty then 0 else iidProb pX x) ≤
      Fintype.card S / (4 * n * ε ^ 2) := by
    refine le_trans (le_of_eq ?_) (sum_iidProb_not_mem_strongTypicalSet_le pX hε hn)
    rw [sum_filter]
    exact sum_congr rfl fun x _ => by split_ifs <;> rfl
  calc _ = ∑ x, iidProb pX x * (1 - σ x) ^ K := by
        refine sum_congr rfl fun x _ => ?_
        rw [← sum_mul, sum_iidProb_pair_right]
    _ ≤ ∑ x, (iidProb pX x * Real.exp (-(K * a)) + (if x ∈ Ty then 0 else iidProb pX x)) :=
        sum_le_sum fun x _ => hbound x
    _ ≤ _ := by
        rw [sum_add_distrib, ← sum_mul, sum_iidProb, one_mul]
        linarith

private lemma markov_part (q : PMF (S × T × Fin m))
    (hM : MarkovChain (fun a : S × T × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) (t₀ : T) (hn : 0 < n) {δ η : ℝ} (hη : 0 < η) (x : Fin n → S)
    (u : Fin n → Fin m) (hu : (fun i => (x i, u i)) ∈ strongTypicalSet (lawXU q) n δ) :
    ∑ y : Fin n → T, (∏ i, (condChannel q t₀ (x i) (y i)).toReal) *
      (if (fun i => ((u i, x i), y i)) ∉ strongTypicalSet (law3 q) n (δ + η) then 1 else 0) ≤
      Fintype.card (Fin m × S) * Fintype.card T / (4 * n * η ^ 2) := by
  have hux := mem_strongTypicalSet_swap.1 hu
  have h := markov_lemma (condChannel q t₀) (fun z : Fin m × S => lawXU q (z.2, z.1)) hη hn hux
  beta_reduce at h
  rw [law3_eq q hM t₀] at h
  refine le_trans (le_of_eq ?_) h
  rw [sum_filter]
  refine sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

private lemma bin_part (q : PMF (S × T × Fin m))
    (hM : MarkovChain (fun a : S × T × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) (t₀ : T) (hn : 0 < n) {δ η : ℝ} (hη : 0 < η) {K : ℕ} (l₀ : Fin K) :
    ∑ x : Fin n → S, ∑ y : Fin n → T, iidProb (q.map fun a => (a.1, a.2.1))
        (fun i => (x i, y i)) *
      ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb (q.map fun a => a.2.2) (C l)) *
        (if (∃ l, (fun i => (x i, C l i)) ∈ strongTypicalSet (lawXU q) n δ) ∧
          (fun i => ((C (coverIndex (strongTypicalSet (lawXU q) n δ) C l₀ x) i, x i), y i)) ∉
            strongTypicalSet (law3 q) n (δ + η) then 1 else 0) ≤
      Fintype.card (Fin m × S) * Fintype.card T / (4 * n * η ^ 2) := by
  set pX := (q.map fun a => (a.1, a.2.1)).map Prod.fst
  set qU := q.map fun a => a.2.2
  set Tc := strongTypicalSet (lawXU q) n δ
  set T3 := strongTypicalSet (law3 q) n (δ + η)
  set Bm : ℝ := Fintype.card (Fin m × S) * Fintype.card T / (4 * n * η ^ 2)
  set W : (Fin n → S) → (Fin n → T) → ℝ := fun x y => ∏ i, (condChannel q t₀ (x i) (y i)).toReal
  set F : (Fin n → S) → (Fin K → Fin n → Fin m) → (Fin n → T) → ℝ := fun x C y =>
    if (∃ l, (fun i => (x i, C l i)) ∈ Tc) ∧
      (fun i => ((C (coverIndex Tc C l₀ x) i, x i), y i)) ∉ T3 then 1 else 0
  have hBm : 0 ≤ Bm := by positivity
  have hW0 : ∀ x y, 0 ≤ W x y := fun x y => prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hwC0 : ∀ C : Fin K → Fin n → Fin m, 0 ≤ ∏ l, iidProb qU (C l) :=
    fun C => prod_nonneg fun _ _ => iidProb_nonneg _ _
  have hwC1 : ∑ C : Fin K → Fin n → Fin m, ∏ l, iidProb qU (C l) = 1 :=
    sum_prod _ fun _ => sum_iidProb qU n
  have hinner : ∀ x C, ∑ y, W x y * F x C y ≤ Bm := by
    intro x C
    by_cases h : ∃ l, (fun i => (x i, C l i)) ∈ Tc
    · refine le_trans (le_of_eq (sum_congr rfl fun y _ => ?_))
        (markov_part q hM t₀ hn hη x _ (coverIndex_mem l₀ h))
      simp only [F, W, h, true_and]
      rfl
    · simp only [F, h, false_and, ↓reduceIte, mul_zero, sum_const_zero]
      exact hBm
  calc _ = ∑ x, iidProb pX x * ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb qU (C l)) *
        ∑ y, W x y * F x C y := by
        refine sum_congr rfl fun x _ => ?_
        simp only [iidProb_pair_eq q t₀, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun C _ => sum_congr rfl fun y _ => by ring
    _ ≤ ∑ x, iidProb pX x * ∑ C : Fin K → Fin n → Fin m, (∏ l, iidProb qU (C l)) * Bm :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (sum_le_sum fun C _ =>
          mul_le_mul_of_nonneg_left (hinner x C) (hwC0 C)) (iidProb_nonneg _ _)
    _ = Bm := by
        rw [← sum_mul (f := fun C : Fin K → Fin n → Fin m => ∏ l, iidProb qU (C l)), hwC1,
          one_mul, ← sum_mul, sum_iidProb, one_mul]

end Bounds

private lemma half_le_floor {z : ℝ} (hz : 1 ≤ z) : z / 2 ≤ ⌊z⌋₊ := by
  have hlt := Nat.lt_floor_add_one z
  have hge : (1 : ℝ) ≤ ⌊z⌋₊ := Nat.one_le_cast.2 (Nat.le_floor (by simpa using hz))
  linarith

section Main

variable {S T V : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {m : ℕ}

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma sum_law3_mul (q : PMF (S × T × Fin m)) (d : S → V → ℝ) (g : Fin m × T → V) :
    ∑ t : (Fin m × S) × T, law3 q t * d t.1.2 (g (t.1.1, t.2)) =
      ∑ a, (q a).toReal * d a.1 (g (a.2.2, a.2.1)) :=
  Fintype.sum_equiv ⟨fun t => (t.1.2, t.2, t.1.1), fun a => ((a.2.2, a.1), a.2.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => rfl

private lemma exists_code_le [DecidableEq S] [DecidableEq T] {d : S → V → ℝ}
    (hd : ∀ s v, 0 ≤ d s v) (q : PMF (S × T × Fin m)) (g : Fin m × T → V)
    (hM : MarkovChain (fun a : S × T × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) (t₀ : T) {n K k : ℕ} (hn : 0 < n) (hK : 0 < K) (hk : 0 < k)
    {δ εp εc a b : ℝ} (hδ : 0 < δ) (hεc : 0 < εc)
    (hδp : Fintype.card S * (δ + δ) ≤ εp) (ha1 : a ≤ 1)
    (hcov : ∀ x : Fin n → S, (∀ s, |(typeCount x s : ℝ) / n - ∑ u, lawXU q (s, u)| ≤ εc) →
      (∀ s, ∑ u, lawXU q (s, u) = 0 → typeCount x s = 0) →
      a ≤ ∑ u ∈ univ.filter (fun u : Fin n → Fin m =>
        (fun i => (x i, u i)) ∈ strongTypicalSet (lawXU q) n δ),
        iidProb (q.map fun a => a.2.2) u)
    (hpack : ∀ y : Fin n → T, ∑ u ∈ univ.filter (fun u : Fin n → Fin m =>
        (fun i => (y i, u i)) ∈ strongTypicalSet (lawYU q) n εp),
        iidProb (q.map fun a => a.2.2) u ≤ b) :
    ∃ c : WZCode S T V n k, c.distortion (q.map fun a => (a.1, a.2.1)) d ≤
      ∑ a, (q a).toReal * d a.1 (g (a.2.2, a.2.1)) +
        (δ + δ) * ∑ t : (Fin m × S) × T, |d t.1.2 (g (t.1.1, t.2))| +
        (∑ t : (Fin m × S) × T, d t.1.2 (g (t.1.1, t.2))) *
          (Real.exp (-(K * a)) + Fintype.card S / (4 * n * εc ^ 2) +
            Fintype.card (Fin m × S) * Fintype.card T / (4 * n * δ ^ 2) +
            (k : ℝ)⁻¹ * (K * b)) := by
  set f : (Fin m × S) × T → ℝ := fun t => d t.1.2 (g (t.1.1, t.2))
  have hf0 : ∀ t, 0 ≤ f t := fun t => hd _ _
  have hM0 : 0 ≤ ∑ t, f t := sum_nonneg fun t _ => hf0 t
  have hFs0 : 0 ≤ ∑ t, |f t| := sum_nonneg fun t _ => abs_nonneg _
  have hE0 : 0 ≤ ∑ a, (q a).toReal * d a.1 (g (a.2.2, a.2.1)) :=
    sum_nonneg fun a _ => mul_nonneg ENNReal.toReal_nonneg (hd _ _)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hmarg : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      (fun i => ((u i, x i), y i)) ∈ strongTypicalSet (law3 q) n (δ + δ) →
        (fun i => (y i, u i)) ∈ strongTypicalSet (lawYU q) n εp := fun u x y h => by
    have hm := mem_strongTypicalSet_marginal h
    have e : (fun z : T × Fin m => ∑ a, law3 q ((z.2, a), z.1)) = lawYU q := rfl
    rw [e] at hm
    exact strongTypicalSet_mono hδp hm
  have hdist : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      (fun i => ((u i, x i), y i)) ∈ strongTypicalSet (law3 q) n (δ + δ) →
        blockDist d x (fun i => g (u i, y i)) ≤
          ∑ a, (q a).toReal * d a.1 (g (a.2.2, a.2.1)) + (δ + δ) * ∑ t, |f t| :=
    fun u x y h => by
      have h1 := abs_avg_sub_le_of_mem_strongTypicalSet hn h f
      rw [sum_law3_mul] at h1
      rw [blockDist]
      linarith [le_abs_self ((∑ i, f ((u i, x i), y i)) / n -
        ∑ a, (q a).toReal * d a.1 (g (a.2.2, a.2.1)))]
  have hbd : ∀ (u : Fin n → Fin m) (x : Fin n → S) (y : Fin n → T),
      blockDist d x (fun i => g (u i, y i)) ≤ ∑ t, f t := fun u x y => by
    rw [blockDist, div_le_iff₀ hn']
    calc ∑ i, d (x i) (g (u i, y i)) ≤ ∑ _i : Fin n, ∑ t, f t := sum_le_sum fun i _ =>
          single_le_sum (f := f) (fun t _ => hf0 t) (mem_univ ((u i, x i), y i))
      _ = (∑ t, f t) * n := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  have hA := cover_part q K hn (strongTypicalSet (lawXU q) n δ) hεc ha1 hcov
  have hB := bin_part q hM t₀ hn (δ := δ) hδ ⟨0, hK⟩
  have hA' : ∑ x : Fin n → S, ∑ y : Fin n → T, iidProb (q.map fun a => (a.1, a.2.1))
      (fun i => (x i, y i)) *
      (1 - ∑ u ∈ univ.filter (fun u : Fin n → Fin m =>
        (fun i => (x i, u i)) ∈ strongTypicalSet (lawXU q) n δ),
        iidProb (q.map fun a => a.2.2) u) ^ K ≤
      Real.exp (-(K * a)) + Fintype.card S / (4 * n * εc ^ 2) := hA
  have k0 := @exists_binCode S T V _ _ _ _ m n K k (q.map fun a => (a.1, a.2.1)) d g
    (strongTypicalSet (lawXU q) n δ) (strongTypicalSet (lawYU q) n εp)
    (strongTypicalSet (law3 q) n (δ + δ))
    (∑ a, (q a).toReal * d a.1 (g (a.2.2, a.2.1)) + (δ + δ) * ∑ t, |f t|) (∑ t, f t)
    (add_nonneg hE0 (mul_nonneg (add_pos hδ hδ).le hFs0)) hM0
  have k1 := k0 hmarg
  have k2 := k1 hdist
  have k3 := k2 hbd hk (q.map fun a => a.2.2) ⟨0, hK⟩
    (a₁ := Real.exp (-(K * a)) + Fintype.card S / (4 * n * εc ^ 2))
    (a₂ := Fintype.card (Fin m × S) * Fintype.card T / (4 * n * δ ^ 2)) (a₃ := b)
  have k4 := k3 hA'
  have k5 := k4 hB
  obtain ⟨c, hc⟩ := k5 hpack
  exact ⟨c, hc.trans_eq (by ring)⟩

theorem achievable_of_lt {d : S → V → ℝ} (hd : ∀ s v, 0 ≤ d s v) (q : PMF (S × T × Fin m))
    (g : Fin m × T → V)
    (hM : MarkovChain (fun a : S × T × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1)
      q.toMeasure) {R : ℝ}
    (hR : I[fun a : S × T × Fin m => a.1 : fun a => a.2.2 | fun a => a.2.1 ; q.toMeasure] < R) :
    Achievable (q.map fun a => (a.1, a.2.1)) d R
      (∑ a, (q a).toReal * d a.1 (g (a.2.2, a.2.1))) := by
  classical
  obtain ⟨⟨s₀, t₀, u₀⟩, -⟩ := q.support_nonempty
  have hI := condMutualInfo_eq_jointInfo_sub q hM
  have hI0 := condMutualInfo_nonneg q.toMeasure (X := fun a : S × T × Fin m => a.1)
    (Y := fun a => a.2.2) (Z := fun a => a.2.1) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)
  have hJ₁ := jointInfo_lawXU_nonneg q
  have hqU : ∀ u, ((q.map fun a => a.2.2) u).toReal = ∑ a, lawXU q (a, u) := toReal_map_U q
  have hqU' : ∀ u, ((q.map fun a => a.2.2) u).toReal = ∑ b, lawYU q (b, u) := fun u => by
    rw [hqU, sum_lawYU]
  set J₁ := jointInfo (lawXU q)
  set J₂ := jointInfo (lawYU q)
  set M := ∑ t : (Fin m × S) × T, d t.1.2 (g (t.1.1, t.2))
  set Fs := ∑ t : (Fin m × S) × T, |d t.1.2 (g (t.1.1, t.2))|
  have hM0 : 0 ≤ M := sum_nonneg fun t _ => hd _ _
  have hFs0 : 0 ≤ Fs := sum_nonneg fun t _ => abs_nonneg _
  intro ε hε
  set δ' := (R - (J₁ - J₂)) / 4 with hδ'
  have hδ'0 : 0 < δ' := by rw [hδ']; linarith
  obtain ⟨εp, hεp, hpack⟩ := strong_packing (lawYU q) _ hqU' hδ'0
  set δ := min δ' (min (εp / (2 * (Fintype.card S + 1))) (ε / (4 * (Fs + 1)))) with hδdef
  have hcS : (0 : ℝ) ≤ Fintype.card S := Nat.cast_nonneg _
  have hδ0 : 0 < δ := lt_min hδ'0 (lt_min (by positivity) (by positivity))
  have hδδ' : δ ≤ δ' := min_le_left _ _
  have hδp : Fintype.card S * (δ + δ) ≤ εp := by
    have h1 : δ ≤ εp / (2 * (Fintype.card S + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hδε : (δ + δ) * Fs ≤ ε / 2 := by
    have h1 : δ ≤ ε / (4 * (Fs + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  obtain ⟨εc, hεc, hcov⟩ := strong_covering (lawXU q) (fun _ => sum_nonneg fun _ _ =>
    ENNReal.toReal_nonneg) _ hqU hδ0
  set R₁ := J₁ + 2 * δ'
  have hR0 : 0 ≤ R := by linarith
  have hR₁0 : 0 ≤ R₁ := by positivity
  have hexp1 : ∀ n : ℕ, ∀ r : ℝ, 0 ≤ r → 1 ≤ Real.exp (n * r) := fun n r hr =>
    Real.one_le_exp (mul_nonneg (Nat.cast_nonneg n) hr)
  set K₁ : ℕ → ℕ := fun n => ⌊Real.exp (n * R₁)⌋₊
  set kk : ℕ → ℕ := fun n => ⌊Real.exp (n * R)⌋₊
  set a : ℕ → ℝ := fun n => Real.exp (-(n * (J₁ + δ)))
  have hK₁ : ∀ n, 0 < K₁ n := fun n => Nat.floor_pos.2 (hexp1 n R₁ hR₁0)
  have hkk : ∀ n, 0 < kk n := fun n => Nat.floor_pos.2 (hexp1 n R hR0)
  have ha1 : ∀ n, a n ≤ 1 := fun n => Real.exp_le_one_iff.2 (by
    have : 0 ≤ (n : ℝ) * (J₁ + δ) := mul_nonneg (Nat.cast_nonneg n) (by linarith)
    linarith)
  have t1 : Tendsto (fun n => Real.exp (-(K₁ n * a n))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_exp_nat_mul (show -(δ' / 2) < 0 by linarith)) (fun n => (Real.exp_pos _).le)
      fun n => Real.exp_le_exp.2 ?_
    have h1 := half_le_floor (hexp1 n R₁ hR₁0)
    have h2 : Real.exp (n * R₁) * a n = Real.exp (n * (2 * δ' - δ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : (n : ℝ) * δ' ≤ Real.exp (n * (2 * δ' - δ)) := by
      have := Real.add_one_le_exp (n * (2 * δ' - δ))
      have : (n : ℝ) * δ' ≤ n * (2 * δ' - δ) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
      linarith
    have h4 : (n : ℝ) * δ' / 2 ≤ K₁ n * a n := by
      calc (n : ℝ) * δ' / 2 ≤ Real.exp (n * R₁) / 2 * a n := by
            rw [div_mul_eq_mul_div, h2]
            linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    linarith
  have t2 : ∀ c e : ℝ, Tendsto (fun n : ℕ => c / (4 * n * e)) atTop (𝓝 0) := fun c e => by
    refine (tendsto_const_div_atTop_nhds_zero_nat (c / (4 * e))).congr fun n => ?_
    rw [div_div]
    ring
  have t4 : Tendsto (fun n => (kk n : ℝ)⁻¹ * (K₁ n * Real.exp (-(n * (J₂ - δ'))))) atTop
      (𝓝 0) := by
    have hc := (tendsto_exp_nat_mul (show -δ' < 0 by linarith)).const_mul 2
    rw [mul_zero] at hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun n => by positivity) fun n => ?_
    have hk2 := half_le_floor (hexp1 n R hR0)
    have hkpos : (0 : ℝ) < kk n := Nat.cast_pos.2 (hkk n)
    have hinv : (kk n : ℝ)⁻¹ ≤ 2 * Real.exp (-(n * R)) := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hkpos]
      have := Real.exp_pos (n * R)
      have h := mul_le_mul_of_nonneg_left hk2
        (by positivity : (0 : ℝ) ≤ 2 * (Real.exp (n * R))⁻¹)
      rw [show 2 * (Real.exp (n * R))⁻¹ * (Real.exp (n * R) / 2) = 1 by field_simp] at h
      linarith
    have hK : (K₁ n : ℝ) ≤ Real.exp (n * R₁) := Nat.floor_le (Real.exp_pos _).le
    calc (kk n : ℝ)⁻¹ * (K₁ n * Real.exp (-(n * (J₂ - δ'))))
        ≤ 2 * Real.exp (-(n * R)) * (Real.exp (n * R₁) * Real.exp (-(n * (J₂ - δ')))) :=
          mul_le_mul hinv (mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le)
            (by positivity) (by positivity)
      _ = 2 * Real.exp (n * -δ') := by
          rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
          congr 2
          rw [hδ']
          ring
  have hB := (((t1.add (t2 (Fintype.card S) (εc ^ 2))).add
    (t2 (Fintype.card (Fin m × S) * Fintype.card T) (δ ^ 2))).add t4).const_mul M
  simp only [add_zero, mul_zero] at hB
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hB.eventually (gt_mem_nhds
    (show (0 : ℝ) < ε / 2 by linarith))).and ((hcov.and hpack).and (eventually_gt_atTop 0)))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hBn, ⟨hcovn, hpackn⟩, hn0⟩ := hN n hn
  obtain ⟨c, hc⟩ := exists_code_le hd q g hM t₀ hn0 (hK₁ n) (hkk n) hδ0 hεc hδp (ha1 n)
    hcovn hpackn
  refine ⟨kk n, Nat.floor_le (Real.exp_pos _).le, c, hc.trans ?_⟩
  have : M * (Real.exp (-(K₁ n * a n)) + Fintype.card S / (4 * n * εc ^ 2) +
      Fintype.card (Fin m × S) * Fintype.card T / (4 * n * δ ^ 2) +
      (kk n : ℝ)⁻¹ * (K₁ n * Real.exp (-(n * (J₂ - δ'))))) < ε / 2 := hBn
  linarith

end Main

end WynerZiv

end Meat
