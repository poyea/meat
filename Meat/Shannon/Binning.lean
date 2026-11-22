import Meat.Shannon.Typical

open MeasureTheory Finset

namespace Meat

theorem sum_uniform {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} (hk : 0 < k) :
    ∑ _f : ι → Fin k, ∏ _i : ι, (k : ℝ)⁻¹ = 1 :=
  sum_prod (fun _ _ => (k : ℝ)⁻¹) fun _ => by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hk.ne')]

theorem sum_uniform_mul_ite_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} (hk : 0 < k)
    (a b : ι) :
    ∑ f : ι → Fin k, (∏ _i : ι, (k : ℝ)⁻¹) * (if f a = f b then 1 else 0)
      = if a = b then 1 else (k : ℝ)⁻¹ := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h1 : ∑ _m : Fin k, (k : ℝ)⁻¹ = 1 := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hk']
  by_cases hab : a = b
  · subst hab
    simpa using sum_uniform (ι := ι) hk
  simp only [hab, ↓reduceIte]
  have he : ∀ f : ι → Fin k, (if f a = f b then (1 : ℝ) else 0)
      = ∑ m : Fin k, (if f a = m then (1 : ℝ) else 0) * (if f b = m then 1 else 0) := fun f => by
    simp
  simp_rw [he, mul_sum]
  rw [sum_comm]
  have hm : ∀ m : Fin k, ∑ f : ι → Fin k, (∏ _i : ι, (k : ℝ)⁻¹) *
      ((if f a = m then (1 : ℝ) else 0) * (if f b = m then 1 else 0)) = (k : ℝ)⁻¹ * (k : ℝ)⁻¹ :=
    fun m => by
      have h := sum_prod_mul_apply_mul_apply (fun (_ : ι) (_ : Fin k) => (k : ℝ)⁻¹)
        (fun _ => h1)
        (fun x => if x = m then (1 : ℝ) else 0) (fun x => if x = m then (1 : ℝ) else 0) hab
      simpa using h
  rw [sum_congr rfl fun m _ => hm m, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hk', one_mul]

variable {S T : Type*}
  [Fintype S] [MeasurableSpace S] [Fintype T] [MeasurableSpace T]

theorem card_filter_snd_jointlyTypicalSet_le [DecidableEq T] (p : PMF (S × T)) (n : ℕ) (ε : ℝ)
    (y : Fin n → T) :
    (((jointlyTypicalSet p n ε).filter fun xy : (Fin n → S) × (Fin n → T) => xy.2 = y).card : ℝ)
      ≤ Real.exp (n * (measureEntropy p.toMeasure - measureEntropy (p.map Prod.snd).toMeasure
        + 2 * ε)) := by
  set F := (jointlyTypicalSet p n ε).filter fun xy : (Fin n → S) × (Fin n → T) => xy.2 = y
  rcases F.eq_empty_or_nonempty with hF | ⟨z, hz⟩
  · rw [hF, card_empty, Nat.cast_zero]
    exact (Real.exp_pos _).le
  have hz' := mem_filter.1 hz
  have hy : iidProb (p.map Prod.snd) y
      ≤ Real.exp (-(n * (measureEntropy (p.map Prod.snd).toMeasure - ε))) := by
    have h := hz'.1
    simp only [jointlyTypicalSet, typicalSet, mem_filter, mem_univ, true_and] at h
    exact hz'.2 ▸ h.2.1.2
  have hlow : ∑ w ∈ F, Real.exp (-(n * (measureEntropy p.toMeasure + ε)))
      ≤ ∑ w ∈ F, iidProb p (fun i => (w.1 i, w.2 i)) := sum_le_sum fun w hw => by
    have h := (mem_filter.1 hw).1
    simp only [jointlyTypicalSet, typicalSet, mem_filter, mem_univ, true_and] at h
    exact h.2.2.1
  have hup : ∑ w ∈ F, iidProb p (fun i => (w.1 i, w.2 i)) ≤ iidProb (p.map Prod.snd) y := by
    rw [← sum_iidProb_pair_left p y, sum_filter]
    calc _ ≤ ∑ w : (Fin n → S) × (Fin n → T),
          if w.2 = y then iidProb p (fun i => (w.1 i, w.2 i)) else 0 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun w _ _ => by
            split_ifs
            · exact iidProb_nonneg _ _
            · exact le_rfl
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp
  rw [sum_const, nsmul_eq_mul] at hlow
  have h := (hlow.trans hup).trans hy
  rw [← le_div_iff₀ (Real.exp_pos _), ← Real.exp_sub] at h
  refine h.trans_eq (congrArg Real.exp ?_)
  ring

theorem card_filter_fst_jointlyTypicalSet_le [DecidableEq S] (p : PMF (S × T)) (n : ℕ) (ε : ℝ)
    (x : Fin n → S) :
    (((jointlyTypicalSet p n ε).filter fun xy : (Fin n → S) × (Fin n → T) => xy.1 = x).card : ℝ)
      ≤ Real.exp (n * (measureEntropy p.toMeasure - measureEntropy (p.map Prod.fst).toMeasure
        + 2 * ε)) := by
  set F := (jointlyTypicalSet p n ε).filter fun xy : (Fin n → S) × (Fin n → T) => xy.1 = x
  rcases F.eq_empty_or_nonempty with hF | ⟨z, hz⟩
  · rw [hF, card_empty, Nat.cast_zero]
    exact (Real.exp_pos _).le
  have hz' := mem_filter.1 hz
  have hx : iidProb (p.map Prod.fst) x
      ≤ Real.exp (-(n * (measureEntropy (p.map Prod.fst).toMeasure - ε))) := by
    have h := hz'.1
    simp only [jointlyTypicalSet, typicalSet, mem_filter, mem_univ, true_and] at h
    exact hz'.2 ▸ h.1.2
  have hlow : ∑ w ∈ F, Real.exp (-(n * (measureEntropy p.toMeasure + ε)))
      ≤ ∑ w ∈ F, iidProb p (fun i => (w.1 i, w.2 i)) := sum_le_sum fun w hw => by
    have h := (mem_filter.1 hw).1
    simp only [jointlyTypicalSet, typicalSet, mem_filter, mem_univ, true_and] at h
    exact h.2.2.1
  have hup : ∑ w ∈ F, iidProb p (fun i => (w.1 i, w.2 i)) ≤ iidProb (p.map Prod.fst) x := by
    rw [← sum_iidProb_pair_right p x, sum_filter]
    calc _ ≤ ∑ w : (Fin n → S) × (Fin n → T),
          if w.1 = x then iidProb p (fun i => (w.1 i, w.2 i)) else 0 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun w _ _ => by
            split_ifs
            · exact iidProb_nonneg _ _
            · exact le_rfl
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp
  rw [sum_const, nsmul_eq_mul] at hlow
  have h := (hlow.trans hup).trans hx
  rw [← le_div_iff₀ (Real.exp_pos _), ← Real.exp_sub] at h
  refine h.trans_eq (congrArg Real.exp ?_)
  ring

end Meat
