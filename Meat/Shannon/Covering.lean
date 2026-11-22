import Meat.Shannon.Inequalities
import Meat.Shannon.Typical

open MeasureTheory Finset

namespace Meat

theorem one_sub_mul_pow_le {a b : ℝ} (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (k : ℕ) : (1 - a * b) ^ k ≤ 1 - b + Real.exp (-(k * a)) := by
  have hc := (convexOn_pow k).2 (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 (sub_nonneg.2 ha1))
    (sub_nonneg.2 hb1) hb0 (by ring)
  simp only [smul_eq_mul, one_pow, mul_one] at hc
  have e : 1 - b + b * (1 - a) = 1 - a * b := by ring
  rw [e] at hc
  have h1 : (1 - a) ^ k ≤ Real.exp (-(k * a)) := by
    calc (1 - a) ^ k ≤ Real.exp (-a) ^ k :=
          pow_le_pow_left₀ (sub_nonneg.2 ha1) (by linarith [Real.add_one_le_exp (-a)]) k
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : b * (1 - a) ^ k ≤ (1 - a) ^ k :=
    mul_le_of_le_one_left (pow_nonneg (sub_nonneg.2 ha1) k) hb1
  linarith

variable {S T : Type*}
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
private lemma mutualInfo_fst_snd (p : PMF (S × T)) :
    mutualInfo (fun ω : S × T => ω.1) (fun ω => ω.2) p.toMeasure
      = measureEntropy (p.map Prod.fst).toMeasure + measureEntropy (p.map Prod.snd).toMeasure
        - measureEntropy p.toMeasure := by
  simp only [mutualInfo, entropy]
  have h : p.toMeasure.map (fun ω : S × T => (ω.1, ω.2)) = p.toMeasure := Measure.map_id'
  rw [h, PMF.toMeasure_map (f := Prod.fst) (p := p) (hf := measurable_fst),
    PMF.toMeasure_map (f := Prod.snd) (p := p) (hf := measurable_snd)]

theorem sum_iidProb_mul_one_sub_pow_le [DecidableEq S] [DecidableEq T] (p : PMF (S × T)) {n : ℕ}
    {ε : ℝ} (hε : 0 ≤ ε)
    {J : Finset ((Fin n → S) × (Fin n → T))} (hJ : J ⊆ jointlyTypicalSet p n ε) (k : ℕ) :
    ∑ x, iidProb (p.map Prod.fst) x *
        (1 - ∑ y : Fin n → T with (x, y) ∈ J, iidProb (p.map Prod.snd) y) ^ k ≤
      (1 - ∑ xy ∈ J, iidProb p (fun i => (xy.1 i, xy.2 i))) +
        Real.exp (-(k * Real.exp (-(n * (mutualInfo (fun ω : S × T => ω.1) (fun ω => ω.2)
          p.toMeasure + 3 * ε))))) := by
  set I := mutualInfo (fun ω : S × T => ω.1) (fun ω => ω.2) p.toMeasure with hI
  set a := Real.exp (-(n * (I + 3 * ε)))
  set e := Real.exp (-(k * a))
  have hI0 : 0 ≤ I := mutualInfo_nonneg _ measurable_fst measurable_snd
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ (n : ℝ) * (I + 3 * ε) := mul_nonneg (Nat.cast_nonneg n) (by linarith)
    linarith)
  set P1 : (Fin n → S) → ℝ := fun x => iidProb (p.map Prod.fst) x
  set Q : (Fin n → S) → ℝ := fun x =>
    ∑ y : Fin n → T with (x, y) ∈ J, iidProb (p.map Prod.snd) y
  set B : (Fin n → S) → ℝ := fun x =>
    ∑ y : Fin n → T with (x, y) ∈ J, iidProb p (fun i => (x i, y i))
  have hpair : ∀ x y, (x, y) ∈ J →
      a * iidProb p (fun i => (x i, y i)) ≤ P1 x * iidProb (p.map Prod.snd) y := by
    intro x y hxy
    have h := hJ hxy
    simp only [jointlyTypicalSet, typicalSet, mem_filter, mem_univ, true_and] at h
    have e1 : a * Real.exp (-(n * (measureEntropy p.toMeasure - ε))) =
        Real.exp (-(n * (measureEntropy (p.map Prod.fst).toMeasure + ε))) *
          Real.exp (-(n * (measureEntropy (p.map Prod.snd).toMeasure + ε))) := by
      simp only [a, ← Real.exp_add, hI, mutualInfo_fst_snd]
      congr 1
      ring
    calc a * iidProb p (fun i => (x i, y i))
        ≤ a * Real.exp (-(n * (measureEntropy p.toMeasure - ε))) :=
          mul_le_mul_of_nonneg_left h.2.2.2 ha0
      _ = _ := e1
      _ ≤ _ := mul_le_mul h.1.1 h.2.1.1 (Real.exp_pos _).le (iidProb_nonneg _ _)
  have hB0 : ∀ x, 0 ≤ B x := fun x => sum_nonneg fun y _ => iidProb_nonneg _ _
  have hBle : ∀ x, B x ≤ P1 x := fun x => by
    simp only [B, P1]
    rw [← sum_iidProb_pair_right p x]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun y _ _ => iidProb_nonneg _ _
  have hQ0 : ∀ x, 0 ≤ Q x := fun x => sum_nonneg fun y _ => iidProb_nonneg _ _
  have hQ1 : ∀ x, Q x ≤ 1 := fun x => by
    simp only [Q]
    rw [← sum_iidProb (p.map Prod.snd) n]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun y _ _ => iidProb_nonneg _ _
  have hBQ : ∀ x, a * B x ≤ P1 x * Q x := fun x => by
    simp only [B, Q, mul_sum]
    exact sum_le_sum fun y hy => hpair x y (mem_filter.1 hy).2
  have key : ∀ x, P1 x * (1 - Q x) ^ k ≤ P1 x - B x + P1 x * e := by
    intro x
    rcases (iidProb_nonneg (p.map Prod.fst) x).eq_or_lt with h0 | h0
    · have hB : B x = 0 := le_antisymm ((hBle x).trans_eq h0.symm) (hB0 x)
      simp only [P1] at h0 ⊢
      rw [← h0, hB]
      simp
    · have hb0 : 0 ≤ B x / P1 x := div_nonneg (hB0 x) h0.le
      have hb1 : B x / P1 x ≤ 1 := (div_le_one h0).2 (hBle x)
      have hab : a * (B x / P1 x) ≤ Q x := by
        rw [← mul_div_assoc, div_le_iff₀ h0, mul_comm (Q x)]
        exact hBQ x
      have h1 : (1 - Q x) ^ k ≤ (1 - a * (B x / P1 x)) ^ k :=
        pow_le_pow_left₀ (sub_nonneg.2 (hQ1 x)) (by linarith) k
      have h2 := one_sub_mul_pow_le ha1 hb0 hb1 k
      have hP : P1 x ≠ 0 := h0.ne'
      have h3 : P1 x * (1 - B x / P1 x + e) = P1 x - B x + P1 x * e := by
        field_simp
      calc P1 x * (1 - Q x) ^ k ≤ P1 x * (1 - B x / P1 x + e) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) h0.le
        _ = _ := h3
  have hsumB : ∑ x, B x = ∑ xy ∈ J, iidProb p (fun i => (xy.1 i, xy.2 i)) := by
    rw [eq_comm, ← Fintype.sum_ite_mem J, Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    simp only [B]
    rw [sum_filter]
  calc _ ≤ ∑ x, (P1 x - B x + P1 x * e) := sum_le_sum fun x _ => key x
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, hsumB]
      simp only [P1]
      rw [sum_iidProb, one_mul]

end Meat
