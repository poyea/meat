import Meat.Channel.Wiretap
import Meat.Shannon.Iid

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace Wiretap

variable {A B E : Type*}

noncomputable def toB (W : DMC A (B × E)) : DMC A B := fun a => (W a).map Prod.fst

noncomputable def toE (W : DMC A (B × E)) : DMC A E := fun a => (W a).map Prod.snd

section Marginal

variable [Fintype B] [Fintype E]

omit [Fintype B] in
theorem toB_apply [Finite B] (W : DMC A (B × E)) (a : A) (b : B) :
    toB W a b = ∑ e, W a (b, e) := by
  classical
  have := Fintype.ofFinite B
  rw [toB, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Finset.sum_eq_single b (fun b' _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

omit [Fintype E] in
theorem toE_apply [Finite E] (W : DMC A (B × E)) (a : A) (e : E) :
    toE W a e = ∑ b, W a (b, e) := by
  classical
  have := Fintype.ofFinite E
  rw [toE, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp

theorem sum_mul_blockProb_toB {n : ℕ} (W : DMC A (B × E)) (x : Fin n → A)
    (f : (Fin n → B) → ℝ≥0∞) :
    ∑ y : Fin n → B × E, f (fun i => (y i).1) * DMC.blockProb W x y =
      ∑ y₁, f y₁ * DMC.blockProb (toB W) x y₁ := by
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => B) (fun _ => E)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine sum_congr rfl fun y₁ _ => ?_
  rw [DMC.blockProb]
  simp only [toB_apply]
  rw [Fintype.prod_sum, mul_sum]
  rfl

theorem sum_mul_blockProb_toE {n : ℕ} (W : DMC A (B × E)) (x : Fin n → A)
    (f : (Fin n → E) → ℝ≥0∞) :
    ∑ y : Fin n → B × E, f (fun i => (y i).2) * DMC.blockProb W x y =
      ∑ z, f z * DMC.blockProb (toE W) x z := by
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => B) (fun _ => E)).symm.sum_comp,
    Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [DMC.blockProb]
  simp only [toE_apply]
  rw [Fintype.prod_sum, mul_sum]
  rfl

end Marginal

section Entropy

variable {S : Type*} [Fintype S]

noncomputable def pmfH (q : PMF S) : ℝ := ∑ s, Real.negMulLog (q s).toReal

theorem sum_negMulLog_blockProb {n : ℕ} (V : DMC A S) (x : Fin n → A) :
    ∑ z : Fin n → S, Real.negMulLog (DMC.blockProb V x z).toReal = ∑ i, pmfH (V (x i)) := by
  have hb : ∀ z : Fin n → S, (DMC.blockProb V x z).toReal = ∏ i, (V (x i) (z i)).toReal :=
    fun z => by rw [DMC.blockProb, ENNReal.toReal_prod]
  have hn : ∀ z : Fin n → S, Real.negMulLog (∏ i, (V (x i) (z i)).toReal) =
      (∏ i, (V (x i) (z i)).toReal) * ∑ i, -Real.log (V (x i) (z i)).toReal := by
    intro z
    rcases (prod_nonneg fun i _ => ENNReal.toReal_nonneg (a := V (x i) (z i))).eq_or_lt
      with h | h
    · rw [← h]
      simp
    rw [Real.negMulLog, Real.log_prod fun i _ => prod_ne_zero_iff.1 h.ne' i (mem_univ i),
      sum_neg_distrib]
    ring
  simp_rw [hb, hn, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_prod_mul_apply (fun j s => (V (x j) s).toReal) (fun j => sum_toReal_pmf_eq_one _)
    (fun s => -Real.log (V (x i) s).toReal) i, pmfH]
  refine sum_congr rfl fun s _ => ?_
  rw [Real.negMulLog]
  ring

theorem sum_iidProb_mul_apply {n : ℕ} (p : PMF A) [Fintype A] (h : A → ℝ) (i : Fin n) :
    ∑ x : Fin n → A, iidProb p x * h (x i) = ∑ a, (p a).toReal * h a :=
  sum_prod_mul_apply (fun _ a => (p a).toReal) (fun _ => sum_toReal_pmf_eq_one p) h i

theorem pmfH_concave {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) (P : ι → S → ℝ) (hP : ∀ i s, 0 ≤ P i s) :
    ∑ i, w i * ∑ s, Real.negMulLog (P i s) ≤ ∑ s, Real.negMulLog (∑ i, w i * P i s) := by
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_le_sum fun s _ => ?_
  have := Real.concaveOn_negMulLog.le_map_sum (t := univ) (w := w) (p := fun i => P i s)
    (fun i _ => hw i) h1 (fun i _ => hP i s)
  simpa [smul_eq_mul] using this

end Entropy

section Codebook

variable {M L : Type*} [Fintype M] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M]
  [DecidableEq M] [Fintype L] [Nonempty L] [MeasurableSpace L] [MeasurableSingletonClass L]
  [DecidableEq L] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E] {n : ℕ}

noncomputable def bookCode (C : M × L → Fin n → A) (J : Finset ((Fin n → A) × (Fin n → B)))
    (u₀ : M × L) : WiretapCode M L A B n :=
  ⟨C, fun y => (BlockCode.typicalDecoder C J u₀ y).1⟩

omit [Fintype M] [Fintype L] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M]
  [Nonempty L] [MeasurableSpace L] [MeasurableSingletonClass L] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem errorProb_bookCode_le (W : DMC A (B × E)) (C : M × L → Fin n → A)
    (J : Finset ((Fin n → A) × (Fin n → B))) (u₀ u : M × L) :
    (bookCode C J u₀).errorProb W u ≤ (BlockCode.typicalCode C J u₀).errorProb (toB W) u := by
  classical
  have e : (BlockCode.typicalCode C J u₀).errorProb (toB W) u = ∑ y₁ : Fin n → B,
      (if BlockCode.typicalDecoder C J u₀ y₁ = u then 0 else 1) *
        DMC.blockProb (toB W) (C u) y₁ := by
    refine sum_congr rfl fun y _ => ?_
    by_cases h : BlockCode.typicalDecoder C J u₀ y = u <;> simp [BlockCode.typicalCode, h]
  rw [e, ← sum_mul_blockProb_toB W (C u)
    (fun y₁ => if BlockCode.typicalDecoder C J u₀ y₁ = u then 0 else 1)]
  refine sum_le_sum fun y _ => ?_
  by_cases h : BlockCode.typicalDecoder C J u₀ (fun i => (y i).1) = u
  · have h' : (bookCode C J u₀).dec (fun i => (y i).1) = u.1 := by
      change (BlockCode.typicalDecoder C J u₀ _).1 = u.1
      rw [h]
    simp [h, h']
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), one_mul]
    split_ifs
    · exact zero_le
    · exact le_rfl

noncomputable def bookMeasure (W : DMC A (B × E)) (C : M × L → Fin n → A) :
    Measure ((M × L) × (Fin n → B × E)) :=
  Interactive.codeMeasure W (fun u (i : Fin n) (_ : Fin i → B × E) => C u i)

omit [DecidableEq M] [DecidableEq L] in
instance isProbabilityMeasure_bookMeasure (W : DMC A (B × E)) (C : M × L → Fin n → A) :
    IsProbabilityMeasure (bookMeasure W C) :=
  Interactive.isProbabilityMeasure_codeMeasure W _

noncomputable def eveDec (C : M × L → Fin n → A) (J : Finset ((Fin n → A) × (Fin n → E)))
    (l₀ : L) (p : (Fin n → E) × M) : L :=
  BlockCode.typicalDecoder (fun l => C (p.2, l)) J l₀ p.1

omit [DecidableEq M] in
theorem measureReal_eveDec_ne (W : DMC A (B × E)) (C : M × L → Fin n → A)
    (J : Finset ((Fin n → A) × (Fin n → E))) (l₀ : L) :
    (bookMeasure W C).real
      {ω | eveDec C J l₀ ((fun i => (ω.2 i).2), ω.1.1) ≠ ω.1.2} =
      (Fintype.card (M × L) : ℝ)⁻¹ * ∑ u : M × L,
        ((BlockCode.typicalCode (fun l => C (u.1, l)) J l₀).errorProb (toE W) u.2).toReal := by
  classical
  rw [measureReal_def, bookMeasure, Interactive.codeMeasure_apply, ENNReal.toReal_sum fun u _ =>
    ENNReal.sum_ne_top.2 fun y _ => by split_ifs <;> simp [Interactive.seqProb,
      ENNReal.mul_ne_top, ENNReal.prod_ne_top, PMF.apply_ne_top]]
  rw [mul_sum]
  refine sum_congr rfl fun u _ => ?_
  have e : ∑ y : Fin n → B × E, (if eveDec C J l₀ ((fun i => (y i).2), u.1) ≠ u.2 then
      (Fintype.card (M × L) : ℝ≥0∞)⁻¹ * Interactive.seqProb W
        (fun (i : Fin n) (_ : Fin i → B × E) => C u i) y else 0) = (Fintype.card (M × L) : ℝ≥0∞)⁻¹ *
      ∑ y : Fin n → B × E, (fun z => if BlockCode.typicalDecoder (fun l => C (u.1, l)) J l₀ z
        = u.2 then 0 else 1) (fun i => (y i).2) * DMC.blockProb W (C u) y := by
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    by_cases hd : BlockCode.typicalDecoder (fun l => C (u.1, l)) J l₀ (fun i => (y i).2) = u.2
    <;> simp [eveDec, hd, Interactive.seqProb, DMC.blockProb]
  rw [e, sum_mul_blockProb_toE W (C u)
    (fun z => if BlockCode.typicalDecoder (fun l => C (u.1, l)) J l₀ z = u.2 then 0 else 1),
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 2
  refine sum_congr rfl fun z _ => ?_
  by_cases hd : BlockCode.typicalDecoder (fun l => C (u.1, l)) J l₀ z = u.2 <;>
    simp [BlockCode.typicalCode, hd]

omit [DecidableEq M] [DecidableEq L] in
theorem bookMeasure_pair (W : DMC A (B × E)) (C : M × L → Fin n → A) (z : Fin n → E)
    (u : M × L) :
    (bookMeasure W C).real {ω | ((fun i => (ω.2 i).2), ω.1) = (z, u)} =
      (Fintype.card (M × L) : ℝ)⁻¹ * (DMC.blockProb (toE W) (C u) z).toReal := by
  classical
  rw [measureReal_def, bookMeasure, Interactive.codeMeasure_apply,
    sum_eq_single u (fun u' _ hu => by simp [hu]) (by simp)]
  have e : ∑ y : Fin n → B × E, (if ((fun i => (y i).2), u) = (z, u) then
      (Fintype.card (M × L) : ℝ≥0∞)⁻¹ * Interactive.seqProb W
        (fun (i : Fin n) (_ : Fin i → B × E) => C u i) y else 0) =
      (Fintype.card (M × L) : ℝ≥0∞)⁻¹ * ∑ y : Fin n → B × E,
        (fun z' => if z' = z then (1 : ℝ≥0∞) else 0) (fun i => (y i).2) *
          DMC.blockProb W (C u) y := by
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    by_cases hz : (fun i => (y i).2) = z <;> simp [hz, Interactive.seqProb, DMC.blockProb]
  rw [e, sum_mul_blockProb_toE W (C u) (fun z' => if z' = z then (1 : ℝ≥0∞) else 0)]
  simp [ENNReal.toReal_mul]

omit [DecidableEq M] [DecidableEq L] in
theorem bookMeasure_out (W : DMC A (B × E)) (C : M × L → Fin n → A) (z : Fin n → E) :
    (bookMeasure W C).real {ω | (fun i => (ω.2 i).2) = z} =
      ∑ u : M × L, (Fintype.card (M × L) : ℝ)⁻¹ * (DMC.blockProb (toE W) (C u) z).toReal := by
  classical
  rw [← sum_congr rfl fun u _ => bookMeasure_pair W C z u]
  rw [← measureReal_biUnion_finset (h := fun u _ => measure_ne_top _ _)]
  · congr 1
    ext ω
    simp [Prod.ext_iff]
  · intro a _ b _ hab
    exact Set.disjoint_left.2 fun ω h1 h2 => hab ((Prod.ext_iff.1 h1).2.symm.trans
      (Prod.ext_iff.1 h2).2)
  · intro u _
    exact (measurable_of_finite (fun ω : (M × L) × (Fin n → B × E) =>
      ((fun i => (ω.2 i).2), ω.1))) (measurableSet_singleton _)

omit [DecidableEq M] [DecidableEq L] in
theorem entropy_out_bookMeasure (W : DMC A (B × E)) (C : M × L → Fin n → A) :
    H[fun ω : (M × L) × (Fin n → B × E) => fun i => (ω.2 i).2 ; bookMeasure W C] =
      ∑ z, Real.negMulLog (∑ u : M × L,
        (Fintype.card (M × L) : ℝ)⁻¹ * (DMC.blockProb (toE W) (C u) z).toReal) := by
  rw [entropy_def]
  refine sum_congr rfl fun z _ => ?_
  rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton z)]
  exact congrArg Real.negMulLog (bookMeasure_out W C z)

omit [DecidableEq M] [DecidableEq L] in
theorem condEntropy_out_bookMeasure (W : DMC A (B × E)) (C : M × L → Fin n → A) :
    H[fun ω : (M × L) × (Fin n → B × E) => fun i => (ω.2 i).2 | Prod.fst ; bookMeasure W C] =
      (Fintype.card (M × L) : ℝ)⁻¹ * ∑ u : M × L, ∑ i, pmfH (toE W (C u i)) := by
  have hc : (0 : ℝ) < Fintype.card (M × L) := Nat.cast_pos.2 Fintype.card_pos
  have hU : H[Prod.fst ; bookMeasure W C] = Real.log (Fintype.card (M × L)) :=
    Interactive.entropy_fst_codeMeasure W _
  have hJ : H[fun ω : (M × L) × (Fin n → B × E) => ((fun i => (ω.2 i).2), ω.1) ;
      bookMeasure W C] = ∑ x : (Fin n → E) × (M × L), Real.negMulLog
        ((Fintype.card (M × L) : ℝ)⁻¹ * (DMC.blockProb (toE W) (C x.2) x.1).toReal) := by
    rw [entropy_def]
    refine sum_congr rfl fun x _ => ?_
    rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton x)]
    exact congrArg Real.negMulLog (bookMeasure_pair W C x.1 x.2)
  have hs : ∀ u : M × L, ∑ z, (DMC.blockProb (toE W) (C u) z).toReal = 1 := fun u => by
    rw [← ENNReal.toReal_sum fun z _ => DMC.blockProb_ne_top _ _ _, DMC.sum_blockProb_eq_one,
      ENNReal.toReal_one]
  rw [condEntropy_def, hJ, hU, Fintype.sum_prod_type, sum_comm]
  simp only [Real.negMulLog_mul, sum_add_distrib, ← sum_mul, hs, one_mul,
    sum_negMulLog_blockProb, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
  rw [Real.negMulLog, Real.log_inv]
  field_simp
  ring

omit [DecidableEq M] [DecidableEq L] in
theorem leakage_bookCode_le (W : DMC A (B × E)) (C : M × L → Fin n → A)
    (J : Finset ((Fin n → A) × (Fin n → B))) (u₀ : M × L)
    (JE : Finset ((Fin n → A) × (Fin n → E))) (l₀ : L) :
    (bookCode C J u₀).leakage W ≤
      H[fun ω : (M × L) × (Fin n → B × E) => fun i => (ω.2 i).2 ; bookMeasure W C] -
        H[fun ω : (M × L) × (Fin n → B × E) => fun i => (ω.2 i).2 | Prod.fst ;
          bookMeasure W C] - Real.log (Fintype.card L) + Real.log 2 +
        (bookMeasure W C).real {ω | eveDec C JE l₀ ((fun i => (ω.2 i).2), ω.1.1) ≠ ω.1.2} *
          Real.log (Fintype.card L) := by
  have hleak : (bookCode C J u₀).leakage W =
      I[fun ω : (M × L) × (Fin n → B × E) => ω.1.1 : fun ω i => (ω.2 i).2 ;
        bookMeasure W C] := rfl
  have i1 := mutualInfo_def (fun ω : (M × L) × (Fin n → B × E) => ω.1.1)
    (fun ω i => (ω.2 i).2) (bookMeasure W C)
  have i2 := condEntropy_def (fun ω : (M × L) × (Fin n → B × E) => fun i => (ω.2 i).2)
    Prod.fst (bookMeasure W C)
  have i3 : H[Prod.fst ; bookMeasure W C] = Real.log (Fintype.card (M × L)) :=
    Interactive.entropy_fst_codeMeasure W _
  have i4 : H[fun ω : (M × L) × (Fin n → B × E) => ω.1.1 ; bookMeasure W C] =
      Real.log (Fintype.card M) := (bookCode C J u₀).entropy_message W
  have i5 := condEntropy_le_log_two_add_mul_log_card (μ := bookMeasure W C)
    (X := fun ω : (M × L) × (Fin n → B × E) => ω.1.2)
    (Y := fun ω => ((fun i => (ω.2 i).2), ω.1.1)) (measurable_of_finite _)
    (measurable_of_finite _) (eveDec C JE l₀)
  have i6 := condEntropy_def (fun ω : (M × L) × (Fin n → B × E) => ω.1.2)
    (fun ω => ((fun i => (ω.2 i).2), ω.1.1)) (bookMeasure W C)
  have i7 : H[fun ω : (M × L) × (Fin n → B × E) => (ω.1.2, ((fun i => (ω.2 i).2), ω.1.1)) ;
      bookMeasure W C] = H[fun ω : (M × L) × (Fin n → B × E) => ((fun i => (ω.2 i).2), ω.1) ;
      bookMeasure W C] :=
    entropy_comp_of_injective _ (X := fun ω : (M × L) × (Fin n → B × E) =>
      ((fun i => (ω.2 i).2), ω.1)) (f := fun p => (p.2.2, (p.1, p.2.1))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 (Prod.ext h.2.2 h.1)
  have i8 := entropy_comm (bookMeasure W C)
    (X := fun ω : (M × L) × (Fin n → B × E) => ω.1.1) (Y := fun ω i => (ω.2 i).2)
  have hcard : Real.log (Fintype.card (M × L)) =
      Real.log (Fintype.card M) + Real.log (Fintype.card L) := by
    rw [Fintype.card_prod, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
      (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
  rw [hleak]
  linarith

end Codebook

section Average

variable [Fintype A] [MeasurableSpace A] {M L : Type*} [Fintype M] [Nonempty M]
  [MeasurableSpace M]
  [MeasurableSingletonClass M] [DecidableEq M] [Fintype L] [Nonempty L] [MeasurableSpace L]
  [DecidableEq L]
  [MeasurableSingletonClass L] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E] {n : ℕ}

omit [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M] [Nonempty L]
  [MeasurableSpace L] [MeasurableSingletonClass L] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem sum_prod_mul_row {X : Type*} [Fintype X] (f : X → ℝ) (hf : ∑ x, f x = 1)
    (G : (L → X) → ℝ) (m : M) :
    ∑ C : M × L → X, (∏ u, f (C u)) * G (fun l => C (m, l)) =
      ∑ D : L → X, (∏ l, f (D l)) * G D := by
  rw [← (Equiv.curry M L X).symm.sum_comp]
  have h1 : ∀ _ : M, ∑ D : L → X, ∏ l, f (D l) = 1 := fun _ => sum_prod (fun _ => f) fun _ => hf
  have := sum_prod_mul_apply (fun _ (D : L → X) => ∏ l, f (D l)) h1 G m
  refine Eq.trans ?_ this
  refine sum_congr rfl fun D _ => ?_
  rw [Fintype.prod_prod_type]
  rfl

omit [MeasurableSpace A] in
theorem sum_condEntropy_out (W : DMC A (B × E)) (p : PMF A) :
    ∑ C : M × L → Fin n → A, (∏ u, iidProb p (C u)) *
        H[fun ω : (M × L) × (Fin n → B × E) => fun i => (ω.2 i).2 | Prod.fst ;
          bookMeasure W C] =
      n * ∑ a, (p a).toReal * pmfH (toE W a) := by
  have hc : (Fintype.card (M × L) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h : ∀ (u : M × L) (i : Fin n), ∑ C : M × L → Fin n → A,
      (∏ u', iidProb p (C u')) * pmfH (toE W (C u i)) = ∑ a, (p a).toReal * pmfH (toE W a) :=
    fun u i => (sum_prod_mul_apply (fun _ x => iidProb p x) (fun _ => sum_iidProb p n)
      (fun x => pmfH (toE W (x i))) u).trans
        (sum_iidProb_mul_apply p (fun a => pmfH (toE W a)) i)
  have hs : ∑ C : M × L → Fin n → A, (∏ u, iidProb p (C u)) *
      ∑ u : M × L, ∑ i, pmfH (toE W (C u i)) =
      ∑ u : M × L, ∑ i, ∑ C : M × L → Fin n → A,
        (∏ u', iidProb p (C u')) * pmfH (toE W (C u i)) := by
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun u _ => sum_comm
  simp only [condEntropy_out_bookMeasure]
  rw [show ∑ C : M × L → Fin n → A, (∏ u, iidProb p (C u)) *
      ((Fintype.card (M × L) : ℝ)⁻¹ * ∑ u : M × L, ∑ i, pmfH (toE W (C u i))) =
      (Fintype.card (M × L) : ℝ)⁻¹ * ∑ C : M × L → Fin n → A, (∏ u, iidProb p (C u)) *
        ∑ u : M × L, ∑ i, pmfH (toE W (C u i)) by
      rw [mul_sum]; exact sum_congr rfl fun C _ => by ring, hs]
  simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

omit [MeasurableSpace A] in
theorem sum_entropy_out_le (W : DMC A (B × E)) (p : PMF A) :
    ∑ C : M × L → Fin n → A, (∏ u, iidProb p (C u)) *
        H[fun ω : (M × L) × (Fin n → B × E) => fun i => (ω.2 i).2 ; bookMeasure W C] ≤
      n * measureEntropy ((DMC.jointPMF (toE W) p).map Prod.snd).toMeasure := by
  have hc : (Fintype.card (M × L) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [entropy_out_bookMeasure]
  refine (pmfH_concave (fun C : M × L → Fin n → A => ∏ u, iidProb p (C u))
    (fun C => prod_nonneg fun u _ => iidProb_nonneg p _)
    (sum_prod (fun _ x => iidProb p x) fun _ => sum_iidProb p n) _
    (fun C z => sum_nonneg fun u _ => mul_nonneg (by positivity) ENNReal.toReal_nonneg)).trans
    (le_of_eq ?_)
  rw [← sum_negMulLog_iidProb]
  refine sum_congr rfl fun z _ => congrArg Real.negMulLog ?_
  rw [← sum_iidProb_pair_left]
  have hr : ∀ u : M × L, ∑ C : M × L → Fin n → A, (∏ u', iidProb p (C u')) *
      (DMC.blockProb (toE W) (C u) z).toReal =
      ∑ x : Fin n → A, iidProb (DMC.jointPMF (toE W) p) (fun i => (x i, z i)) := fun u => by
    rw [sum_prod_mul_apply (fun _ x => iidProb p x) (fun _ => sum_iidProb p n)
      (fun x => (DMC.blockProb (toE W) x z).toReal) u]
    exact sum_congr rfl fun x _ => (DMC.iidProb_jointPMF _ _ _ _).symm
  calc ∑ C : M × L → Fin n → A, (∏ u, iidProb p (C u)) * ∑ u : M × L,
        (Fintype.card (M × L) : ℝ)⁻¹ * (DMC.blockProb (toE W) (C u) z).toReal
      = ∑ u : M × L, (Fintype.card (M × L) : ℝ)⁻¹ * ∑ C : M × L → Fin n → A,
          (∏ u', iidProb p (C u')) * (DMC.blockProb (toE W) (C u) z).toReal := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun u _ => sum_congr rfl fun C _ => by ring
    _ = _ := by
        simp only [hr, sum_const, card_univ, nsmul_eq_mul]
        field_simp

theorem sum_eveError_le (W : DMC A (B × E)) (p : PMF A) (γ : ℝ) (l₀ : L) :
    ∑ C : M × L → Fin n → A, (∏ u, iidProb p (C u)) * (bookMeasure W C).real
        {ω | eveDec C (jointlyTypicalSet (DMC.jointPMF (toE W) p) n γ) l₀
          ((fun i => (ω.2 i).2), ω.1.1) ≠ ω.1.2} ≤
      (1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (toE W) p) n γ,
          iidProb (DMC.jointPMF (toE W) p) (fun i => (xy.1 i, xy.2 i))) +
        (Fintype.card L - 1) * Real.exp (-(n * ((toE W).inputMutualInfo p - 3 * γ))) := by
  have hc : (Fintype.card (M × L) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  set J := jointlyTypicalSet (DMC.jointPMF (toE W) p) n γ
  set β := (1 - ∑ xy ∈ J, iidProb (DMC.jointPMF (toE W) p) (fun i => (xy.1 i, xy.2 i))) +
    (Fintype.card L - 1) * Real.exp (-(n * ((toE W).inputMutualInfo p - 3 * γ)))
  simp only [measureReal_eveDec_ne]
  have hu : ∀ u : M × L, ∑ C : M × L → Fin n → A, (∏ u', iidProb p (C u')) *
      ((BlockCode.typicalCode (fun l => C (u.1, l)) J l₀).errorProb (toE W) u.2).toReal ≤ β :=
    fun u => (sum_prod_mul_row (fun x => iidProb p x) (sum_iidProb p n)
      (fun D => ((BlockCode.typicalCode D J l₀).errorProb (toE W) u.2).toReal) u.1).trans_le
      (DMC.sum_errorProb_typicalCode_le (toE W) p γ l₀ u.2)
  calc _ = (Fintype.card (M × L) : ℝ)⁻¹ * ∑ u : M × L, ∑ C : M × L → Fin n → A,
        (∏ u', iidProb p (C u')) *
          ((BlockCode.typicalCode (fun l => C (u.1, l)) J l₀).errorProb (toE W) u.2).toReal := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun u _ => sum_congr rfl fun C _ => by ring
    _ ≤ (Fintype.card (M × L) : ℝ)⁻¹ * ∑ _u : M × L, β :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun u _ => hu u) (by positivity)
    _ = β := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        field_simp

omit [MeasurableSpace A] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M]
  [Nonempty L] [MeasurableSpace L] [MeasurableSingletonClass L] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem sum_bobError_le [MeasurableSpace A] (W : DMC A (B × E)) (p : PMF A) (γ : ℝ)
    (u₀ : M × L) :
    ∑ C : M × L → Fin n → A, (∏ u, iidProb p (C u)) *
        ∑ u, ((BlockCode.typicalCode C (jointlyTypicalSet (DMC.jointPMF (toB W) p) n γ)
          u₀).errorProb (toB W) u).toReal ≤
      Fintype.card (M × L) * ((1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (toB W) p) n γ,
          iidProb (DMC.jointPMF (toB W) p) (fun i => (xy.1 i, xy.2 i))) +
        (Fintype.card (M × L) - 1) *
          Real.exp (-(n * ((toB W).inputMutualInfo p - 3 * γ)))) := by
  simp only [mul_sum]
  rw [sum_comm]
  calc _ ≤ ∑ _u : M × L, ((1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (toB W) p) n γ,
          iidProb (DMC.jointPMF (toB W) p) (fun i => (xy.1 i, xy.2 i))) +
        (Fintype.card (M × L) - 1) *
          Real.exp (-(n * ((toB W).inputMutualInfo p - 3 * γ)))) :=
        sum_le_sum fun u _ => DMC.sum_errorProb_typicalCode_le (toB W) p γ u₀ u
    _ = _ := by simp; ring

end Average

section Information

theorem jointPMF_toB (W : DMC A (B × E)) (p : PMF A) :
    DMC.jointPMF (toB W) p = (DMC.jointPMF W p).map fun ω => (ω.1, ω.2.1) := by
  simp only [DMC.jointPMF, toB, PMF.map_bind, PMF.map_comp]
  rfl

theorem jointPMF_toE (W : DMC A (B × E)) (p : PMF A) :
    DMC.jointPMF (toE W) p = (DMC.jointPMF W p).map fun ω => (ω.1, ω.2.2) := by
  simp only [DMC.jointPMF, toE, PMF.map_bind, PMF.map_comp]
  rfl


variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

omit [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] in
theorem inputMutualInfo_toE (W : DMC A (B × E)) (p : PMF A) :
    (toE W).inputMutualInfo p =
      measureEntropy ((DMC.jointPMF (toE W) p).map Prod.snd).toMeasure -
        ∑ a, (p a).toReal * pmfH (toE W a) := by
  have h1 : (toE W).inputMutualInfo p = H[Prod.snd ; (toE W).jointMeasure p] -
      H[Prod.snd | Prod.fst ; (toE W).jointMeasure p] := by
    rw [DMC.inputMutualInfo, mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
  have h2 : H[Prod.snd ; (toE W).jointMeasure p] =
      measureEntropy ((DMC.jointPMF (toE W) p).map Prod.snd).toMeasure := by
    rw [entropy, DMC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ measurable_snd]
  have h3 : H[Prod.snd | Prod.fst ; (toE W).jointMeasure p] =
      ∑ a, (p a).toReal * pmfH (toE W a) := by
    rw [DMC.condEntropy_snd_fst_jointMeasure, Fintype.sum_prod_type, ← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [pmfH, mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun e _ => ?_
    rw [DMC.jointMeasure_eq_toMeasure, measureReal_def,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), DMC.jointPMF_apply,
      ENNReal.toReal_mul, Real.negMulLog]
    ring
  rw [h1, h2, h3]

theorem secrecyRate_eq (W : DMC A (B × E)) (p : PMF A) :
    secrecyRate W p = (toB W).inputMutualInfo p - (toE W).inputMutualInfo p := by
  have hB : (toB W).inputMutualInfo p =
      I[fun ω : A × (B × E) => ω.1 : fun ω => ω.2.1 ; W.jointMeasure p] := by
    rw [DMC.inputMutualInfo, DMC.jointMeasure_eq_toMeasure, jointPMF_toB,
      ← PMF.toMeasure_map _ _ (measurable_of_finite _),
      mutualInfo_map _ (measurable_of_finite _) measurable_fst measurable_snd]
    rfl
  have hE : (toE W).inputMutualInfo p =
      I[fun ω : A × (B × E) => ω.1 : fun ω => ω.2.2 ; W.jointMeasure p] := by
    rw [DMC.inputMutualInfo, DMC.jointMeasure_eq_toMeasure, jointPMF_toE,
      ← PMF.toMeasure_map _ _ (measurable_of_finite _),
      mutualInfo_map _ (measurable_of_finite _) measurable_fst measurable_snd]
    rfl
  rw [secrecyRate, hB, hE]

end Information

section Main

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

theorem exists_book (W : DMC A (B × E)) (p : PMF A) (γ : ℝ) {n k l : ℕ} (hn : 0 < n)
    [NeZero k] [NeZero l] (u₀ : Fin k × Fin l) (l₀ : Fin l) :
    ∃ C : Fin k × Fin l → Fin n → A,
      (∑ u, ((BlockCode.typicalCode C (jointlyTypicalSet (DMC.jointPMF (toB W) p) n γ)
          u₀).errorProb (toB W) u).toReal) / (Fintype.card (Fin k × Fin l)) +
        (bookCode C (jointlyTypicalSet (DMC.jointPMF (toB W) p) n γ) u₀).leakage W / n ≤
      ((1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (toB W) p) n γ,
          iidProb (DMC.jointPMF (toB W) p) (fun i => (xy.1 i, xy.2 i))) +
        (Fintype.card (Fin k × Fin l) - 1) *
          Real.exp (-(n * ((toB W).inputMutualInfo p - 3 * γ)))) +
      (n * (toE W).inputMutualInfo p - Real.log l + Real.log 2 +
        ((1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (toE W) p) n γ,
          iidProb (DMC.jointPMF (toE W) p) (fun i => (xy.1 i, xy.2 i))) +
        (Fintype.card (Fin l) - 1) * Real.exp (-(n * ((toE W).inputMutualInfo p - 3 * γ)))) *
          Real.log l) / n := by
  have hE1 := sum_entropy_out_le (M := Fin k) (L := Fin l) (n := n) W p
  have hE2 := sum_condEntropy_out (M := Fin k) (L := Fin l) (n := n) W p
  have hE3 := sum_eveError_le (M := Fin k) (L := Fin l) (n := n) W p γ l₀
  have hE4 := sum_bobError_le (E := E) (M := Fin k) (L := Fin l) (n := n) W p γ u₀
  have hI := inputMutualInfo_toE W p
  set JB := jointlyTypicalSet (DMC.jointPMF (toB W) p) n γ
  set JE := jointlyTypicalSet (DMC.jointPMF (toE W) p) n γ
  set βB := (1 - ∑ xy ∈ JB, iidProb (DMC.jointPMF (toB W) p) (fun i => (xy.1 i, xy.2 i))) +
    (Fintype.card (Fin k × Fin l) - 1) * Real.exp (-(n * ((toB W).inputMutualInfo p - 3 * γ)))
  set βE := (1 - ∑ xy ∈ JE, iidProb (DMC.jointPMF (toE W) p) (fun i => (xy.1 i, xy.2 i))) +
    (Fintype.card (Fin l) - 1) * Real.exp (-(n * ((toE W).inputMutualInfo p - 3 * γ)))
  set w : (Fin k × Fin l → Fin n → A) → ℝ := fun C => ∏ u, iidProb p (C u)
  have hw : ∀ C, 0 ≤ w C := fun C => prod_nonneg fun u _ => iidProb_nonneg p _
  have h1 : ∑ C, w C = 1 := sum_prod (fun _ x => iidProb p x) fun _ => sum_iidProb p n
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hc : (0 : ℝ) < Fintype.card (Fin k × Fin l) := Nat.cast_pos.2 Fintype.card_pos
  have hlogl : 0 ≤ Real.log l := Real.log_natCast_nonneg l
  have hcl : Fintype.card (Fin l) = l := Fintype.card_fin l
  have hleak : ∀ C, (bookCode C JB u₀).leakage W ≤
      H[fun ω : (Fin k × Fin l) × (Fin n → B × E) => fun i => (ω.2 i).2 ; bookMeasure W C] -
        H[fun ω : (Fin k × Fin l) × (Fin n → B × E) => fun i => (ω.2 i).2 | Prod.fst ;
          bookMeasure W C] - Real.log l + Real.log 2 +
        (bookMeasure W C).real {ω | eveDec C JE l₀ ((fun i => (ω.2 i).2), ω.1.1) ≠ ω.1.2} *
          Real.log l := fun C => by
    have := leakage_bookCode_le W C JB u₀ JE l₀
    rwa [hcl] at this
  have hL : ∑ C, w C * (bookCode C JB u₀).leakage W ≤
      n * (toE W).inputMutualInfo p - Real.log l + Real.log 2 + βE * Real.log l := by
    set a : (Fin k × Fin l → Fin n → A) → ℝ := fun C =>
      H[fun ω : (Fin k × Fin l) × (Fin n → B × E) => fun i => (ω.2 i).2 ; bookMeasure W C]
    set b : (Fin k × Fin l → Fin n → A) → ℝ := fun C =>
      H[fun ω : (Fin k × Fin l) × (Fin n → B × E) => fun i => (ω.2 i).2 | Prod.fst ;
        bookMeasure W C]
    set P : (Fin k × Fin l → Fin n → A) → ℝ := fun C =>
      (bookMeasure W C).real {ω | eveDec C JE l₀ ((fun i => (ω.2 i).2), ω.1.1) ≠ ω.1.2}
    have s1 : ∑ C, w C * (bookCode C JB u₀).leakage W ≤
        ∑ C, w C * (a C - b C - Real.log l + Real.log 2 + P C * Real.log l) :=
      sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hleak C) (hw C)
    have s2 : ∑ C, w C * (a C - b C - Real.log l + Real.log 2 + P C * Real.log l) =
        ∑ C, w C * a C - ∑ C, w C * b C + (∑ C, w C) * (Real.log 2 - Real.log l) +
          (∑ C, w C * P C) * Real.log l := by
      rw [sum_mul, sum_mul, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun C _ => by ring
    have s3 := mul_le_mul_of_nonneg_right hE3 hlogl
    rw [h1] at s2
    have e1 : ∑ C, w C * a C = ∑ C : Fin k × Fin l → Fin n → A, (∏ u, iidProb p (C u)) *
        H[fun ω : (Fin k × Fin l) × (Fin n → B × E) => fun i => (ω.2 i).2 ;
          bookMeasure W C] := rfl
    have e2 : ∑ C, w C * b C = ∑ C : Fin k × Fin l → Fin n → A, (∏ u, iidProb p (C u)) *
        H[fun ω : (Fin k × Fin l) × (Fin n → B × E) => fun i => (ω.2 i).2 | Prod.fst ;
          bookMeasure W C] := rfl
    have e3 : ∑ C, w C * P C = ∑ C : Fin k × Fin l → Fin n → A, (∏ u, iidProb p (C u)) *
        (bookMeasure W C).real {ω | eveDec C JE l₀ ((fun i => (ω.2 i).2), ω.1.1) ≠ ω.1.2} :=
      rfl
    rw [e1, e2, e3] at s2
    have hnI : n * (toE W).inputMutualInfo p =
        n * measureEntropy ((DMC.jointPMF (toE W) p).map Prod.snd).toMeasure -
          n * ∑ a, (p a).toReal * pmfH (toE W a) := by rw [hI]; ring
    linarith
  have hBob : ∑ C, w C * ((∑ u, ((BlockCode.typicalCode C JB u₀).errorProb (toB W) u).toReal) /
      (Fintype.card (Fin k × Fin l))) ≤ βB := by
    rw [show ∑ C, w C * ((∑ u, ((BlockCode.typicalCode C JB u₀).errorProb (toB W) u).toReal) /
        (Fintype.card (Fin k × Fin l))) = (∑ C, w C *
          ∑ u, ((BlockCode.typicalCode C JB u₀).errorProb (toB W) u).toReal) /
        (Fintype.card (Fin k × Fin l)) by
      rw [sum_div]; exact sum_congr rfl fun C _ => by ring]
    rw [div_le_iff₀ hc]
    linarith [hE4]
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le (w := w)
    (f := fun C => (∑ u, ((BlockCode.typicalCode C JB u₀).errorProb (toB W) u).toReal) /
      (Fintype.card (Fin k × Fin l)) + (bookCode C JB u₀).leakage W / n)
    (t := βB + (n * (toE W).inputMutualInfo p - Real.log l + Real.log 2 + βE * Real.log l) / n)
    hw h1 (by
      simp only [mul_add, sum_add_distrib]
      refine add_le_add hBob ?_
      rw [show ∑ C, w C * ((bookCode C JB u₀).leakage W / n) =
          (∑ C, w C * (bookCode C JB u₀).leakage W) / n by
        rw [sum_div]; exact sum_congr rfl fun C _ => by ring]
      exact div_le_div_of_nonneg_right hL hn'.le)
  exact ⟨C, hC⟩

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E] in
private lemma ceil_exp_bounds {a : ℝ} (ha : 0 ≤ a) :
    0 < ⌈Real.exp a⌉₊ ∧ Real.exp a ≤ ⌈Real.exp a⌉₊ ∧ (⌈Real.exp a⌉₊ : ℝ) ≤ 2 * Real.exp a ∧
      (⌈Real.exp a⌉₊ : ℝ) - 1 ≤ Real.exp a := by
  have h1 : 1 ≤ Real.exp a := Real.one_le_exp ha
  have hlt : (⌈Real.exp a⌉₊ : ℝ) < Real.exp a + 1 := Nat.ceil_lt_add_one (Real.exp_pos a).le
  exact ⟨Nat.ceil_pos.2 (Real.exp_pos a), Nat.le_ceil _, by linarith, by linarith⟩

omit [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableSpace E] [MeasurableSingletonClass E] in
private lemma typical_gap_nonneg {X Y : Type*} [Fintype X] [Fintype Y] [MeasurableSpace X]
    [MeasurableSpace Y] (q : PMF (X × Y)) (n : ℕ) (γ : ℝ) :
    0 ≤ 1 - ∑ xy ∈ jointlyTypicalSet q n γ, iidProb q (fun i => (xy.1 i, xy.2 i)) := by
  have h := sum_le_univ_sum_of_nonneg (s := jointlyTypicalSet q n γ)
    (f := fun xy : (Fin n → X) × (Fin n → Y) => iidProb q (fun i => (xy.1 i, xy.2 i)))
    (fun xy => iidProb_nonneg q _)
  rw [sum_iidProb_pair] at h
  linarith

theorem achievable_of_lt (W : DMC A (B × E)) (p : PMF A) {R : ℝ} (hR0 : 0 ≤ R)
    (h : R < secrecyRate W p) : Achievable W R := by
  intro ε hε
  rw [secrecyRate_eq] at h
  set IB := (toB W).inputMutualInfo p
  set IE := (toE W).inputMutualInfo p
  have hIE : 0 ≤ IE := DMC.inputMutualInfo_nonneg _ _
  set g := IB - IE - R
  have hg : 0 < g := by linarith
  set η := min (g / 16) (ε / 16)
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hηg : 16 * η ≤ g := by
    have := min_le_left (g / 16) (ε / 16)
    linarith
  have hηε : 16 * η ≤ ε := by
    have := min_le_right (g / 16) (ε / 16)
    linarith
  set RL := max (IE - 4 * η) 0
  have hRL0 : 0 ≤ RL := le_max_right _ _
  have hRLE : RL ≤ IE := max_le (by linarith) hIE
  have hRB : R + RL ≤ IB - 4 * η := by
    rcases le_total (IE - 4 * η) 0 with h' | h'
    · rw [show RL = 0 from max_eq_right h']
      linarith
    · rw [show RL = IE - 4 * η from max_eq_left h']
      linarith
  have tJB := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_sum_iidProb_jointlyTypicalSet (DMC.jointPMF (toB W) p) hη0)
  have tJE := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_sum_iidProb_jointlyTypicalSet (DMC.jointPMF (toE W) p) hη0)
  have tX := tendsto_exp_nat_mul (neg_neg_of_pos hη0)
  have tB := tJB.add (tX.const_mul 4)
  have tE := (tJE.add tX).const_mul (1 + IE)
  rw [sub_self, mul_zero, add_zero] at tB
  rw [sub_self, zero_add, mul_zero] at tE
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((tB.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4
    by linarith))).and (tE.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by linarith))))
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (4 * Real.log 2 / ε + Real.log 2 + 1)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn2 : (N₂ : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq : 0 ≤ 4 * Real.log 2 / ε := div_nonneg (by linarith) hε.le
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℝ) < N₂ := by linarith [hN₂]
    linarith
  have hnpos' : 0 < n := by exact_mod_cast hnpos
  have hl2 : Real.log 2 / n ≤ ε / 4 := by
    rw [div_le_iff₀ hnpos]
    have : 4 * Real.log 2 / ε < n := by linarith [hN₂]
    rw [div_lt_iff₀ hε] at this
    linarith
  have hl1 : Real.log 2 / n ≤ 1 := by
    rw [div_le_iff₀ hnpos]
    linarith [hN₂]
  obtain ⟨hk0, hk1, hk2, -⟩ := ceil_exp_bounds (mul_nonneg hnpos.le hR0)
  obtain ⟨hl0, hl1', hl2', hl3⟩ := ceil_exp_bounds (mul_nonneg hnpos.le hRL0)
  set k := ⌈Real.exp (n * R)⌉₊
  set l := ⌈Real.exp (n * RL)⌉₊
  have : NeZero k := ⟨hk0.ne'⟩
  have : NeZero l := ⟨hl0.ne'⟩
  obtain ⟨C, hC⟩ := exists_book W p η hnpos' ((⟨0, hk0⟩, ⟨0, hl0⟩) : Fin k × Fin l)
    (⟨0, hl0⟩ : Fin l)
  set JB := jointlyTypicalSet (DMC.jointPMF (toB W) p) n η
  set c := bookCode C JB ((⟨0, hk0⟩, ⟨0, hl0⟩) : Fin k × Fin l)
  refine ⟨k, l, inferInstance, inferInstance, hk1, c, ?_⟩
  obtain ⟨hB, hE⟩ := hN₁ n hn1
  have hcard : (Fintype.card (Fin k × Fin l) : ℝ) = k * l := by simp
  have hkl : (Fintype.card (Fin k × Fin l) : ℝ) - 1 ≤
      4 * Real.exp (n * (R + RL)) := by
    rw [hcard, mul_add, Real.exp_add]
    nlinarith [Real.exp_pos (n * R), Real.exp_pos (n * RL), Nat.cast_nonneg (α := ℝ) k,
      Nat.cast_nonneg (α := ℝ) l]
  have hβB : (Fintype.card (Fin k × Fin l) - 1 : ℝ) *
      Real.exp (-(n * (IB - 3 * η))) ≤ 4 * Real.exp (n * -η) := by
    calc _ ≤ 4 * Real.exp (n * (R + RL)) * Real.exp (-(n * (IB - 3 * η))) :=
          mul_le_mul_of_nonneg_right hkl (Real.exp_pos _).le
      _ = 4 * Real.exp (n * (R + RL) - n * (IB - 3 * η)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ _ := by
          gcongr
          nlinarith
  have hβE : (Fintype.card (Fin l) - 1 : ℝ) * Real.exp (-(n * (IE - 3 * η))) ≤
      Real.exp (n * -η) := by
    rw [Fintype.card_fin]
    rcases le_total (IE - 4 * η) 0 with h' | h'
    · have hRL : RL = 0 := max_eq_right h'
      have hl : l = 1 := by
        simp only [l, hRL, mul_zero, Real.exp_zero, Nat.ceil_one]
      rw [hl]
      simp only [Nat.cast_one, sub_self, zero_mul]
      exact (Real.exp_pos _).le
    · have hRL : RL = IE - 4 * η := max_eq_left h'
      calc _ ≤ Real.exp (n * RL) * Real.exp (-(n * (IE - 3 * η))) :=
            mul_le_mul_of_nonneg_right hl3 (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add, hRL]; ring_nf
  have hlogl1 : n * (IE - 4 * η) ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_max_left _ _) hnpos.le)).trans hl1'
  have hlogl2 : Real.log l ≤ Real.log 2 + n * IE := by
    calc Real.log l ≤ Real.log (2 * Real.exp (n * RL)) :=
          Real.log_le_log (by positivity) hl2'
      _ = Real.log 2 + n * RL := by
          rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ _ := by nlinarith
  have hlogl0 : 0 ≤ Real.log l := Real.log_natCast_nonneg l
  have gB := typical_gap_nonneg (DMC.jointPMF (toB W) p) n η
  have gE := typical_gap_nonneg (DMC.jointPMF (toE W) p) n η
  set tE' := (1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (toE W) p) n η,
      iidProb (DMC.jointPMF (toE W) p) (fun i => (xy.1 i, xy.2 i))) + Real.exp (n * -η)
  have htE0 : 0 ≤ tE' := add_nonneg gE (Real.exp_pos _).le
  set βE := (1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (toE W) p) n η,
      iidProb (DMC.jointPMF (toE W) p) (fun i => (xy.1 i, xy.2 i))) +
    (Fintype.card (Fin l) - 1) * Real.exp (-(n * (IE - 3 * η)))
  have hβE' : βE ≤ tE' := by linarith
  have hβE0 : 0 ≤ βE := add_nonneg gE (mul_nonneg (by
    rw [Fintype.card_fin]; exact sub_nonneg.2 (Nat.one_le_cast.2 hl0)) (Real.exp_pos _).le)
  have hT2 : (n * IE - Real.log l + Real.log 2 + βE * Real.log l) / n ≤
      4 * η + Real.log 2 / n + tE' * (Real.log 2 / n + IE) := by
    rw [div_le_iff₀ hnpos]
    have e1 : βE * Real.log l ≤ tE' * (Real.log 2 + n * IE) :=
      mul_le_mul hβE' hlogl2 hlogl0 htE0
    have e2 : (4 * η + Real.log 2 / n + tE' * (Real.log 2 / n + IE)) * n =
        4 * η * n + Real.log 2 + tE' * (Real.log 2 + n * IE) := by
      field_simp
    rw [e2]
    linarith
  have hT3 : tE' * (Real.log 2 / n + IE) ≤ tE' * (1 + IE) :=
    mul_le_mul_of_nonneg_left (by linarith) htE0
  have hBlt : (1 - ∑ xy ∈ JB, iidProb (DMC.jointPMF (toB W) p) (fun i => (xy.1 i, xy.2 i))) +
      4 * Real.exp (n * -η) < ε / 4 := hB
  have hElt : (1 + IE) * tE' < ε / 4 := hE
  have hleak0 : 0 ≤ c.leakage W := mutualInfo_nonneg _ (measurable_of_finite _)
    (measurable_of_finite _)
  have herr0 : 0 ≤ (∑ u, ((BlockCode.typicalCode C JB
      ((⟨0, hk0⟩, ⟨0, hl0⟩) : Fin k × Fin l)).errorProb (toB W) u).toReal) /
        (Fintype.card (Fin k × Fin l)) :=
    div_nonneg (sum_nonneg fun u _ => ENNReal.toReal_nonneg) (Nat.cast_nonneg _)
  have hT : (∑ u, ((BlockCode.typicalCode C JB ((⟨0, hk0⟩, ⟨0, hl0⟩) : Fin k × Fin l)).errorProb
      (toB W) u).toReal) / (Fintype.card (Fin k × Fin l)) + c.leakage W / n ≤ ε := by
    refine hC.trans ?_
    linarith [hβB, hBlt, hT2, hT3, hElt, hl2, hηε]
  constructor
  · have hb : c.avgError W ≤ (BlockCode.typicalCode C JB
        ((⟨0, hk0⟩, ⟨0, hl0⟩) : Fin k × Fin l)).avgError (toB W) := by
      rw [WiretapCode.avgError, BlockCode.avgError, Fintype.card_prod, Nat.cast_mul]
      gcongr with u
      exact errorProb_bookCode_le W C JB _ u
    refine hb.trans (BlockCode.avgError_le_ofReal _ _ ?_)
    have hc : (0 : ℝ) < Fintype.card (Fin k × Fin l) := Nat.cast_pos.2 Fintype.card_pos
    have h3 := (div_le_iff₀ hc).1 (show (∑ u, ((BlockCode.typicalCode C JB
        ((⟨0, hk0⟩, ⟨0, hl0⟩) : Fin k × Fin l)).errorProb (toB W) u).toReal) /
        (Fintype.card (Fin k × Fin l)) ≤ ε by
      have := div_nonneg hleak0 hnpos.le
      linarith)
    linarith
  · have h3 : c.leakage W / n ≤ ε := by linarith
    rwa [div_le_iff₀ hnpos, mul_comm] at h3

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem achievable_zero [Nonempty A] (W : DMC A (B × E)) : Achievable W 0 := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨1, 1, inferInstance, inferInstance, by simp,
    ⟨fun _ _ => Classical.arbitrary A, fun _ => 0⟩, ?_, ?_⟩⟩
  · have h0 : ∀ m : Fin 1 × Fin 1, (WiretapCode.errorProb (n := n)
        ⟨fun _ _ => Classical.arbitrary A, fun _ => 0⟩ W m : ℝ≥0∞) = 0 := fun m => by
      simp [WiretapCode.errorProb, Subsingleton.elim (0 : Fin 1) m.1]
    simp [WiretapCode.avgError, h0]
  · set c : WiretapCode (Fin 1) (Fin 1) A B n := ⟨fun _ _ => Classical.arbitrary A, fun _ => 0⟩
    set μ := Interactive.codeMeasure W (c.toFn (E := E))
    have h1 := mutualInfo_eq_entropy_sub_condEntropy (μ := μ)
      (fun ω : (Fin 1 × Fin 1) × (Fin n → B × E) => ω.1.1) (fun ω i => (ω.2 i).2)
    have h2 := condEntropy_nonneg μ (X := fun ω : (Fin 1 × Fin 1) × (Fin n → B × E) => ω.1.1)
      (Y := fun ω i => (ω.2 i).2) (measurable_of_finite _) (measurable_of_finite _)
    have h3 := entropy_le_log_card μ (X := fun ω : (Fin 1 × Fin 1) × (Fin n → B × E) => ω.1.1)
    simp only [Fintype.card_fin, Nat.cast_one, Real.log_one] at h3
    have h4 : c.leakage W ≤ 0 := by
      change I[fun ω : (Fin 1 × Fin 1) × (Fin n → B × E) => ω.1.1 : fun ω i => (ω.2 i).2 ;
        μ] ≤ 0
      linarith
    exact h4.trans (mul_nonneg (Nat.cast_nonneg n) hε.le)

theorem closure_achievable_eq [Nonempty A] (W₁ : DMC A B) (D : DMC B E) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable (degraded W₁ D) R} =
      Set.Icc 0 (secrecyCapacity (degraded W₁ D)) := by
  refine subset_antisymm (closure_minimal
    (fun R hR => ⟨hR.1, le_secrecyCapacity_of_achievable W₁ D hR.2⟩) isClosed_Icc) ?_
  intro R hR
  rcases (hR.1.trans hR.2).eq_or_lt with h | h
  · rw [← h, Set.Icc_self, Set.mem_singleton_iff] at hR
    exact subset_closure ⟨hR.symm ▸ le_rfl, hR ▸ achievable_zero _⟩
  · rw [← closure_Ico h.ne] at hR
    refine closure_mono (fun R (hR : R ∈ Set.Ico 0 (secrecyCapacity (degraded W₁ D))) => ?_) hR
    obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup hR.2
    exact ⟨hR.1, achievable_of_lt _ p hR.1 hp⟩

end Main

end Wiretap

end Meat
