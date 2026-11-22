import Meat.Shannon.Product
import Meat.Shannon.Typical

open MeasureTheory Filter Topology Finset

namespace Meat

section Marginal

variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

omit [Fintype Ω'] in
theorem iidProb_map [DecidableEq Ω'] {n : ℕ} (p : PMF Ω) (g : Ω → Ω') (y : Fin n → Ω') :
    iidProb (p.map g) y = ∑ w with (fun i => g (w i)) = y, iidProb p w := by
  simp only [iidProb, toReal_map_apply]
  rw [prod_univ_sum]
  refine sum_congr ?_ fun _ _ => rfl
  ext w
  simp [Fintype.mem_piFinset, funext_iff]

theorem sum_iidProb_mul_comp {n : ℕ} (p : PMF Ω) (g : Ω → Ω') (F : (Fin n → Ω') → ℝ) :
    ∑ w, iidProb p w * F (fun i => g (w i)) = ∑ y, iidProb (p.map g) y * F y := by
  classical
  simp_rw [iidProb_map, sum_mul]
  rw [← sum_fiberwise univ (fun w : Fin n → Ω => fun i => g (w i))
    (fun w => iidProb p w * F (fun i => g (w i)))]
  refine sum_congr rfl fun y _ => sum_congr rfl fun w hw => ?_
  rw [(mem_filter.1 hw).2]

theorem sum_ite_comp_eq {n : ℕ} (p : PMF Ω) (g : Ω → Ω')
    (P : (Fin n → Ω') → Prop) [DecidablePred P] :
    ∑ w, (if P (fun i => g (w i)) then 0 else iidProb p w) =
      1 - ∑ y, (if P y then iidProb (p.map g) y else 0) := by
  have h := sum_iidProb_mul_comp p g fun y => if P y then (0 : ℝ) else 1
  simp only [mul_ite, mul_zero, mul_one] at h
  rw [h, eq_sub_iff_add_eq, ← sum_add_distrib, ← sum_iidProb (p.map g) n]
  exact sum_congr rfl fun y _ => by split_ifs <;> simp

end Marginal

section Transfer

variable {Ω S : Type*} [Finite Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype S] [MeasurableSpace S]

theorem entropy_toMeasure (p : PMF Ω) (X : Ω → S) :
    H[X ; p.toMeasure] = measureEntropy (p.map X).toMeasure := by
  rw [entropy, PMF.toMeasure_map (p := p) (hf := measurable_of_finite X)]

end Transfer

variable {S T R : Type*}
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]

noncomputable def superpositionTypicalSet (p : PMF ((S × T) × R)) (n : ℕ) (ε : ℝ) :
    Finset ((Fin n → S × T) × (Fin n → R)) := by
  classical
  exact {z | z ∈ jointlyTypicalSet p n ε ∧
    (fun i => (z.1 i).1) ∈ typicalSet (p.map fun ω => ω.1.1) n ε ∧
    (fun i => ((z.1 i).1, z.2 i)) ∈ typicalSet (p.map fun ω => (ω.1.1, ω.2)) n ε ∧
    ((fun i => (z.1 i).2), z.2) ∈ jointlyTypicalSet (p.map fun ω => (ω.1.2, ω.2)) n ε}

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass R] in
theorem mem_superpositionTypicalSet {p : PMF ((S × T) × R)} {n : ℕ} {ε : ℝ}
    {z : (Fin n → S × T) × (Fin n → R)} :
    z ∈ superpositionTypicalSet p n ε ↔ z ∈ jointlyTypicalSet p n ε ∧
      (fun i => (z.1 i).1) ∈ typicalSet (p.map fun ω => ω.1.1) n ε ∧
      (fun i => ((z.1 i).1, z.2 i)) ∈ typicalSet (p.map fun ω => (ω.1.1, ω.2)) n ε ∧
      ((fun i => (z.1 i).2), z.2) ∈ jointlyTypicalSet (p.map fun ω => (ω.1.2, ω.2)) n ε := by
  simp [superpositionTypicalSet]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass R] in
theorem superpositionTypicalSet_subset (p : PMF ((S × T) × R)) (n : ℕ) (ε : ℝ) :
    superpositionTypicalSet p n ε ⊆ jointlyTypicalSet p n ε :=
  fun _ hz => (mem_superpositionTypicalSet.1 hz).1

theorem tendsto_sum_iidProb_superpositionTypicalSet (p : PMF ((S × T) × R)) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun n => ∑ z ∈ superpositionTypicalSet p n ε,
      iidProb p (fun i => (z.1 i, z.2 i))) atTop (𝓝 1) := by
  classical
  have hl := ((((tendsto_sum_iidProb_jointlyTypicalSet p hε).add
    (tendsto_sum_iidProb_typicalSet (p.map fun ω => ω.1.1) hε)).add
    (tendsto_sum_iidProb_typicalSet (p.map fun ω => (ω.1.1, ω.2)) hε)).add
    (tendsto_sum_iidProb_jointlyTypicalSet (p.map fun ω => (ω.1.2, ω.2)) hε)).sub_const 3
  norm_num at hl
  have htot : ∀ n, ∑ z : (Fin n → S × T) × (Fin n → R),
      iidProb p (fun i => (z.1 i, z.2 i)) = 1 :=
    fun n => sum_iidProb_pair p n
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (fun n => ?_) fun n => ?_
  · set f : (Fin n → S × T) × (Fin n → R) → ℝ := fun z => iidProb p fun i => (z.1 i, z.2 i)
    have hf : ∀ z, 0 ≤ f z := fun z => iidProb_nonneg _ _
    have h0 : ∑ z, (if z ∈ jointlyTypicalSet p n ε then 0 else f z) =
        1 - ∑ z ∈ jointlyTypicalSet p n ε, f z := by
      rw [sum_ite_mem_zero, htot]
    have h1 : ∑ z, (if (fun i => (z.1 i).1) ∈ typicalSet (p.map fun ω => ω.1.1) n ε then 0
        else f z) = 1 - ∑ y ∈ typicalSet (p.map fun ω => ω.1.1) n ε,
          iidProb (p.map fun ω => ω.1.1) y := by
      rw [← Fintype.sum_ite_mem (typicalSet _ n ε), ← sum_ite_comp_eq p (fun ω => ω.1.1)]
      exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun z => rfl
    have h2 : ∑ z, (if (fun i => ((z.1 i).1, z.2 i)) ∈
          typicalSet (p.map fun ω => (ω.1.1, ω.2)) n ε then 0 else f z) =
        1 - ∑ y ∈ typicalSet (p.map fun ω => (ω.1.1, ω.2)) n ε,
          iidProb (p.map fun ω => (ω.1.1, ω.2)) y := by
      rw [← Fintype.sum_ite_mem (typicalSet _ n ε), ← sum_ite_comp_eq p (fun ω => (ω.1.1, ω.2))]
      exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun z => rfl
    have h3 : ∑ z, (if ((fun i => (z.1 i).2), z.2) ∈
          jointlyTypicalSet (p.map fun ω => (ω.1.2, ω.2)) n ε then 0 else f z) =
        1 - ∑ xy ∈ jointlyTypicalSet (p.map fun ω => (ω.1.2, ω.2)) n ε,
          iidProb (p.map fun ω => (ω.1.2, ω.2)) (fun i => (xy.1 i, xy.2 i)) := by
      have e : ∑ xy : (Fin n → T) × (Fin n → R),
          (if xy ∈ jointlyTypicalSet (p.map fun ω => (ω.1.2, ω.2)) n ε then
            iidProb (p.map fun ω => (ω.1.2, ω.2)) (fun i => (xy.1 i, xy.2 i)) else 0) =
          ∑ y : Fin n → T × R, (if ((fun i => (y i).1), fun i => (y i).2) ∈
            jointlyTypicalSet (p.map fun ω => (ω.1.2, ω.2)) n ε then
              iidProb (p.map fun ω => (ω.1.2, ω.2)) y else 0) :=
        Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun z => rfl
      rw [← Fintype.sum_ite_mem (jointlyTypicalSet _ n ε), e,
        ← sum_ite_comp_eq p (fun ω => (ω.1.2, ω.2))]
      exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun z => rfl
    have hJ : ∑ z, (if z ∈ superpositionTypicalSet p n ε then 0 else f z) ≤
        ∑ z, ((if z ∈ jointlyTypicalSet p n ε then 0 else f z) +
          (if (fun i => (z.1 i).1) ∈ typicalSet (p.map fun ω => ω.1.1) n ε then 0 else f z) +
          (if (fun i => ((z.1 i).1, z.2 i)) ∈ typicalSet (p.map fun ω => (ω.1.1, ω.2)) n ε
            then 0 else f z) +
          (if ((fun i => (z.1 i).2), z.2) ∈
            jointlyTypicalSet (p.map fun ω => (ω.1.2, ω.2)) n ε then 0 else f z)) := by
      refine sum_le_sum fun z _ => ?_
      have hi : ∀ (q : Prop) [Decidable q], 0 ≤ (if q then 0 else f z) :=
        fun q _ => by split_ifs <;> simp [hf z]
      have a0 := hi (z ∈ jointlyTypicalSet p n ε)
      have a1 := hi ((fun i => (z.1 i).1) ∈ typicalSet (p.map fun ω => ω.1.1) n ε)
      have a2 := hi ((fun i => ((z.1 i).1, z.2 i)) ∈
        typicalSet (p.map fun ω => (ω.1.1, ω.2)) n ε)
      have a3 := hi (((fun i => (z.1 i).2), z.2) ∈
        jointlyTypicalSet (p.map fun ω => (ω.1.2, ω.2)) n ε)
      by_cases hz : z ∈ superpositionTypicalSet p n ε
      · rw [ite_eq_left hz]
        linarith
      rw [ite_eq_right hz]
      simp only [mem_superpositionTypicalSet, not_and_or] at hz
      rcases hz with h | h | h | h
      · rw [ite_eq_right h] at a0 ⊢
        linarith
      · rw [ite_eq_right h] at a1 ⊢
        linarith
      · rw [ite_eq_right h] at a2 ⊢
        linarith
      · rw [ite_eq_right h] at a3 ⊢
        linarith
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, h0, h1, h2, h3, sum_ite_mem_zero,
      htot] at hJ
    linarith
  · rw [← htot n]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => iidProb_nonneg _ _

theorem sum_superpositionTypicalSet_le_condMutualInfo (p : PMF ((S × T) × R)) (n : ℕ)
    (ε : ℝ) :
    ∑ z ∈ superpositionTypicalSet p n ε,
      iidProb (p.map Prod.fst) z.1 *
        iidProb (p.map fun ω => (ω.1.1, ω.2)) (fun i => ((z.1 i).1, z.2 i)) /
          iidProb (p.map fun ω => ω.1.1) (fun i => (z.1 i).1) ≤
      Real.exp (-(n * (I[fun ω : (S × T) × R => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
        p.toMeasure] - 4 * ε))) := by
  set HUX := measureEntropy (p.map Prod.fst).toMeasure
  set HUY := measureEntropy (p.map fun ω : (S × T) × R => (ω.1.1, ω.2)).toMeasure
  set HU := measureEntropy (p.map fun ω : (S × T) × R => ω.1.1).toMeasure
  set H := measureEntropy p.toMeasure
  set c := Real.exp (-(n * (HUX - ε))) * Real.exp (-(n * (HUY - ε))) /
    Real.exp (-(n * (HU + ε)))
  have hI : I[fun ω : (S × T) × R => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ; p.toMeasure] =
      HUX + HUY - HU - H := by
    have e1 : H[fun ω : (S × T) × R => (ω.1.2, ω.1.1) ; p.toMeasure] = HUX := by
      rw [entropy_comm, entropy_toMeasure]
    have e2 : H[fun ω : (S × T) × R => (ω.2, ω.1.1) ; p.toMeasure] = HUY := by
      rw [entropy_comm, entropy_toMeasure]
    have e3 : H[fun ω : (S × T) × R => ω.1.1 ; p.toMeasure] = HU := entropy_toMeasure _ _
    have e4 : H[fun ω : (S × T) × R => ((ω.1.2, ω.2), ω.1.1) ; p.toMeasure] = H := by
      have h := entropy_comp_of_injective p.toMeasure (X := id)
        (f := fun ω : (S × T) × R => ((ω.1.2, ω.2), ω.1.1)) fun a b h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext (Prod.ext h.2 h.1.1) h.1.2
      refine h.trans ?_
      rw [entropy, Measure.map_id]
    simp only [condMutualInfo, condEntropy]
    rw [e1, e2, e3, e4]
    ring
  have hterm : ∀ z ∈ superpositionTypicalSet p n ε,
      iidProb (p.map Prod.fst) z.1 *
        iidProb (p.map fun ω => (ω.1.1, ω.2)) (fun i => ((z.1 i).1, z.2 i)) /
          iidProb (p.map fun ω => ω.1.1) (fun i => (z.1 i).1) ≤ c := by
    intro z hz
    obtain ⟨hJ, hU, hUY, -⟩ := mem_superpositionTypicalSet.1 hz
    simp only [jointlyTypicalSet, typicalSet, mem_filter, mem_univ, true_and] at hJ hU hUY
    exact div_le_div₀ (by positivity)
      (mul_le_mul hJ.1.2 hUY.2 (iidProb_nonneg _ _) (Real.exp_pos _).le) (Real.exp_pos _) hU.1
  have hcard : ((superpositionTypicalSet p n ε).card : ℝ) ≤ Real.exp (n * (H + ε)) :=
    (Nat.cast_le.2 (card_le_card (superpositionTypicalSet_subset p n ε))).trans
      (card_jointlyTypicalSet_le p n ε)
  calc _ ≤ ∑ z ∈ superpositionTypicalSet p n ε, c := sum_le_sum hterm
    _ = (superpositionTypicalSet p n ε).card * c := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (n * (H + ε)) * c := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      rw [hI]
      simp only [c, ← Real.exp_add, ← Real.exp_sub]
      congr 1
      ring

theorem sum_superpositionTypicalSet_le_mutualInfo (p : PMF ((S × T) × R)) (n : ℕ) (ε : ℝ) :
    ∑ z ∈ superpositionTypicalSet p n ε,
      iidProb (p.map Prod.fst) z.1 * iidProb (p.map Prod.snd) z.2 ≤
      Real.exp (-(n * (I[fun ω : (S × T) × R => ω.1.2 : fun ω => ω.2 ; p.toMeasure] -
        3 * ε))) := by
  classical
  set q := p.map fun ω : (S × T) × R => (ω.1.2, ω.2)
  have hB := sum_iidProb_mul_iidProb_jointlyTypicalSet_le q n ε
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    mutualInfo_map _ (measurable_of_finite _) measurable_fst measurable_snd] at hB
  refine le_trans ?_ hB
  have hq1 : q.map Prod.fst = (p.map Prod.fst).map Prod.snd := by
    simp [q, PMF.map_comp, Function.comp_def]
  have hq2 : q.map Prod.snd = p.map Prod.snd := by
    simp [q, PMF.map_comp, Function.comp_def]
  rw [hq1, hq2]
  have hF : ∀ z : (Fin n → S × T) × (Fin n → R),
      0 ≤ iidProb (p.map Prod.fst) z.1 * iidProb (p.map Prod.snd) z.2 :=
    fun z => mul_nonneg (iidProb_nonneg _ _) (iidProb_nonneg _ _)
  calc _ ≤ ∑ z : (Fin n → S × T) × (Fin n → R),
        if ((fun i => (z.1 i).2), z.2) ∈ jointlyTypicalSet q n ε then
          iidProb (p.map Prod.fst) z.1 * iidProb (p.map Prod.snd) z.2 else 0 := by
        rw [← Fintype.sum_ite_mem (superpositionTypicalSet p n ε)]
        refine sum_le_sum fun z _ => ?_
        by_cases hz : z ∈ superpositionTypicalSet p n ε
        · rw [ite_eq_left hz, ite_eq_left (mem_superpositionTypicalSet.1 hz).2.2.2]
        · rw [ite_eq_right hz]
          split_ifs <;> simp [hF z]
    _ = ∑ x : Fin n → T, ∑ y : Fin n → R, if (x, y) ∈ jointlyTypicalSet q n ε then
          (∑ u : Fin n → S, iidProb (p.map Prod.fst) (fun i => (u i, x i))) *
            iidProb (p.map Prod.snd) y else 0 := by
        rw [Fintype.sum_prod_type, sum_arrow_prod, sum_comm]
        refine sum_congr rfl fun x _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun y _ => ?_
        by_cases h : (x, y) ∈ jointlyTypicalSet q n ε <;> simp [h, sum_mul]
    _ = _ := by
        rw [← Fintype.sum_ite_mem (jointlyTypicalSet q n ε), Fintype.sum_prod_type]
        simp_rw [sum_iidProb_pair_left]

end Meat
