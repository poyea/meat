import Meat.Shannon.Types

open MeasureTheory Filter Topology Finset

namespace Meat

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

open Classical in
theorem sum_iidProb_seqType_mem_le (q : PMF S) (E : Set (Measure S)) {c : ℝ}
    (hc : ∀ P ∈ E, IsProbabilityMeasure P → P ≪ q.toMeasure → c ≤ klDiv P q.toMeasure) (n : ℕ) :
    ∑ x : Fin n → S with seqType x ∈ E, iidProb q x
      ≤ (n + 1) ^ Fintype.card S * Real.exp (-(n * c)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, zero_add, one_pow, zero_mul, neg_zero, Real.exp_zero, one_mul]
    rw [← sum_iidProb q 0]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => iidProb_nonneg q x
  rw [sum_filter, ← sum_typeSet_sum_typeClass]
  have hP : ∀ P ∈ typeSet (S := S) n,
      ∑ x ∈ typeClass P n, (if seqType x ∈ E then iidProb q x else 0) ≤ Real.exp (-(n * c)) := by
    intro P hP
    obtain ⟨y, rfl⟩ := mem_typeSet.1 hP
    rw [sum_congr rfl fun x hx => by rw [mem_typeClass.1 hx]]
    split_ifs with hE
    · by_cases hac : seqType y ≪ q.toMeasure
      · have := isProbabilityMeasure_seqType hn y
        refine (sum_iidProb_typeClass_le q _ n).trans (Real.exp_le_exp.2 ?_)
        have := hc _ hE this hac
        have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      · rw [sum_eq_zero fun x hx => iidProb_eq_zero q x ((mem_typeClass.1 hx).symm ▸ hac)]
        exact (Real.exp_pos _).le
    · rw [sum_const_zero]
      exact (Real.exp_pos _).le
  refine (sum_le_sum hP).trans ?_
  rw [sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact_mod_cast card_typeSet_le n

open Classical in
theorem le_sum_iidProb_seqType_mem (q : PMF S) (E : Set (Measure S)) {P : Measure S}
    [IsProbabilityMeasure P] (hPq : P ≪ q.toMeasure)
    (hE : ∃ δ > 0, ∀ Q : Measure S, IsProbabilityMeasure Q →
      (∀ s, |Q.real {s} - P.real {s}| < δ) → Q ∈ E) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(n * (klDiv P q.toMeasure + η)))
      ≤ ∑ x : Fin n → S with seqType x ∈ E, iidProb q x := by
  obtain ⟨δ, hδ, hE⟩ := hE
  obtain ⟨x, hx0, hx⟩ := exists_seq_typeCount_tendsto (fun s => P.real {s})
    (fun _ => measureReal_nonneg) (sum_measureReal_singleton_eq_one P)
  have hreal : ∀ s, Tendsto (fun n => (seqType (x n)).real {s}) atTop (𝓝 (P.real {s})) :=
    fun s => (hx s).congr fun n => (seqType_real (x n) s).symm
  have hac : ∀ n, seqType (x n) ≪ q.toMeasure := fun n => by
    rw [seqType_absolutelyContinuous_iff]
    intro i hi
    have hP0 : P.real {x n i} = 0 := by
      have := hPq (q.toMeasure_apply_singleton _ (measurableSet_singleton _) ▸ hi :
        q.toMeasure {x n i} = 0)
      simp [Measure.real, this]
    have := hx0 n _ hP0
    exact (card_pos.2 ⟨i, by simp⟩ : 0 < typeCount (x n) (x n i)).ne' this
  have hD := tendsto_klDiv hac hreal
  rw [← klDiv_eq_sum_sub hPq] at hD
  have h1 := hD.eventually (gt_mem_nhds (show klDiv P q.toMeasure < klDiv P q.toMeasure + η / 2
    by linarith))
  have h2 : ∀ᶠ n in atTop, ∀ s, |(seqType (x n)).real {s} - P.real {s}| < δ :=
    eventually_all.2 fun s => (Metric.tendsto_nhds.1 (hreal s)) δ hδ
  filter_upwards [h1, h2, eventually_pow_le_exp (Fintype.card S) (half_pos hη),
    eventually_gt_atTop 0] with n hn1 hn2 hn3 hn4
  have hQ : seqType (x n) ∈ E := hE _ (isProbabilityMeasure_seqType hn4 _) hn2
  have hsub : typeClass (seqType (x n)) n ⊆ ({y : Fin n → S | seqType y ∈ E} : Finset _) :=
    fun y hy => by simp [mem_typeClass.1 hy, hQ]
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => iidProb_nonneg q y)
  refine le_trans ?_ (le_sum_iidProb_typeClass q (mem_typeSet.2 ⟨x n, rfl⟩) (hac n))
  rw [le_div_iff₀ (by positivity)]
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc Real.exp (-(n * (klDiv P q.toMeasure + η))) * (n + 1) ^ Fintype.card S
      ≤ Real.exp (-(n * (klDiv P q.toMeasure + η))) * Real.exp (n * (η / 2)) :=
        mul_le_mul_of_nonneg_left hn3 (Real.exp_pos _).le
    _ = Real.exp (-(n * (klDiv P q.toMeasure + η / 2))) := by
        rw [← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(n * klDiv (seqType (x n)) q.toMeasure)) :=
        Real.exp_le_exp.2 (by nlinarith)

noncomputable def sanovExponent (q : PMF S) (E : Set (Measure S)) : ℝ :=
  sInf {d | ∃ P ∈ E, IsProbabilityMeasure P ∧ P ≪ q.toMeasure ∧ klDiv P q.toMeasure = d}

open Classical in
theorem tendsto_sanov (q : PMF S) (E : Set (Measure S))
    (hE : ∀ P ∈ E, ∃ δ > 0, ∀ Q : Measure S, IsProbabilityMeasure Q →
      (∀ s, |Q.real {s} - P.real {s}| < δ) → Q ∈ E)
    (hne : ∃ P ∈ E, IsProbabilityMeasure P ∧ P ≪ q.toMeasure) :
    Tendsto (fun n : ℕ => -Real.log (∑ x : Fin n → S with seqType x ∈ E, iidProb q x) / n) atTop
      (𝓝 (sanovExponent q E)) := by
  set D := sanovExponent q E
  set T := {d | ∃ P ∈ E, IsProbabilityMeasure P ∧ P ≪ q.toMeasure ∧ klDiv P q.toMeasure = d}
  have hT : T.Nonempty := by
    obtain ⟨P, hP, hp, hac⟩ := hne
    exact ⟨_, P, hP, hp, hac, rfl⟩
  have hbdd : BddBelow T := ⟨0, by
    rintro _ ⟨P, -, hp, hac, rfl⟩
    exact klDiv_nonneg hac⟩
  have hlow : ∀ P ∈ E, IsProbabilityMeasure P → P ≪ q.toMeasure → ∀ η > 0,
      ∀ᶠ n : ℕ in atTop, Real.exp (-(n * (klDiv P q.toMeasure + η)))
        ≤ ∑ x : Fin n → S with seqType x ∈ E, iidProb q x :=
    fun P hP hp hac η hη => le_sum_iidProb_seqType_mem q E hac (hE P hP) hη
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ∑ x : Fin n → S with seqType x ∈ E, iidProb q x := by
    obtain ⟨P, hP, hp, hac⟩ := hne
    filter_upwards [hlow P hP hp hac 1 one_pos] with n hn
    exact (Real.exp_pos _).trans_le hn
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hc : ∀ P ∈ E, IsProbabilityMeasure P → P ≪ q.toMeasure → D ≤ klDiv P q.toMeasure :=
      fun P hP hp hac => csInf_le hbdd ⟨P, hP, hp, hac, rfl⟩
    filter_upwards [hpos, eventually_pow_le_exp (Fintype.card S) (half_pos (sub_pos.2 ha)),
      eventually_gt_atTop 0] with n hn hn2 hn3
    refine lt_of_lt_of_le (show a < D - (D - a) / 2 by linarith) (le_neg_log_div_of_le_exp hn3 hn
      ((sum_iidProb_seqType_mem_le q E hc n).trans ?_))
    calc ((n : ℝ) + 1) ^ Fintype.card S * Real.exp (-(n * D))
        ≤ Real.exp (n * ((D - a) / 2)) * Real.exp (-(n * D)) :=
          mul_le_mul_of_nonneg_right hn2 (Real.exp_pos _).le
      _ = Real.exp (-(n * (D - (D - a) / 2))) := by
          rw [← Real.exp_add]
          ring_nf
  · obtain ⟨_, ⟨P, hP, hp, hac, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hT hb
    filter_upwards [hlow P hP hp hac ((b - klDiv P q.toMeasure) / 2) (by linarith),
      eventually_gt_atTop 0] with n hn hn2
    exact (neg_log_div_le_of_exp_le hn2 hn).trans_lt (by linarith)

end Meat
