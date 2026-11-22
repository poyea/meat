import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Meat.Shannon.Markov

open MeasureTheory

namespace Meat

variable {Ω S T : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  {X X' : Ω → S} {Y : Ω → T} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem condEntropy_le_binEntropy_add_mul_log (hX : Measurable X) (hX' : Measurable X') :
    H[X | X' ; μ] ≤ Real.binEntropy (μ.real {ω | X' ω ≠ X ω})
      + μ.real {ω | X' ω ≠ X ω} * Real.log (Fintype.card S - 1) := by
  classical
  set p := μ.real {ω | X' ω ≠ X ω}
  set n : ℝ := Fintype.card S - 1
  let W : Ω → S × S := fun ω => (X ω, X' ω)
  have hW : Measurable W := hX.prodMk hX'
  set ν := μ.map W
  let N : S × S → ℝ := fun a => ν.real {a}
  let R : S → ℝ := fun s => (ν.map Prod.snd).real {s}
  let c : S × S → ℝ := fun a => if a.1 = a.2 then 1 - p else p / n
  let q : S × S → ℝ := fun a => R a.2 * c a
  have hN1 : ∑ a, N a = 1 := sum_measureReal_singleton_eq_one ν
  have hN0 : ∀ a, 0 ≤ N a := fun _ => measureReal_nonneg
  have hoff : ∑ a with a.1 ≠ a.2, N a = p := by
    simp only [N]
    rw [sum_measureReal_singleton, map_measureReal_apply hW (Finset.measurableSet _)]
    congr 1
    ext ω
    simp [W, eq_comm]
  have hdiag : ∑ a with a.1 = a.2, N a = 1 - p := by
    rw [← hoff, ← hN1, ← Finset.sum_filter_add_sum_filter_not Finset.univ fun a : S × S =>
      a.1 = a.2]
    ring
  have hNdiag : ∀ a : S × S, a.1 = a.2 → N a ≤ 1 - p := fun a h =>
    hdiag ▸ Finset.single_le_sum (fun b _ => hN0 b) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hNoff : ∀ a : S × S, a.1 ≠ a.2 → N a ≤ p := fun a h =>
    hoff ▸ Finset.single_le_sum (fun b _ => hN0 b) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hNR : ∀ a : S × S, N a ≤ R a.2 := fun a => measureReal_singleton_le_map ν Prod.snd a
  have hn : ∀ a : S × S, a.1 ≠ a.2 → 0 < n := fun a h => by
    have : (1 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.one_lt_card_iff.2 ⟨a.1, a.2, h⟩
    simp only [n]
    linarith
  have hpos : ∀ a, N a ≠ 0 → 0 < R a.2 ∧ 0 < c a := fun a ha => by
    have h := (hN0 a).lt_of_ne' ha
    refine ⟨h.trans_le (hNR a), ?_⟩
    by_cases had : a.1 = a.2
    · simpa [c, had] using h.trans_le (hNdiag a had)
    · simpa [c, had] using div_pos (h.trans_le (hNoff a had)) (hn a had)
  have hc0 : ∀ a, 0 ≤ c a := fun a => by
    by_cases had : a.1 = a.2
    · simpa [c, had] using (hN0 a).trans (hNdiag a had)
    · simpa [c, had] using div_nonneg measureReal_nonneg (hn a had).le
  have hq0 : ∀ a, 0 ≤ q a := fun a => mul_nonneg measureReal_nonneg (hc0 a)
  have hNq : ∀ a, q a = 0 → N a = 0 := fun a h => by
    by_contra ha
    obtain ⟨h1, h2⟩ := hpos a ha
    exact (mul_pos h1 h2).ne' h
  have hsum : ∑ a, q a ≤ ∑ a, N a := by
    rw [hN1, Fintype.sum_prod_type_right, ← sum_measureReal_singleton_eq_one (ν.map Prod.snd)]
    refine Finset.sum_le_sum fun s _ => ?_
    simp only [q, ← Finset.mul_sum]
    refine mul_le_of_le_one_right measureReal_nonneg ?_
    have hcard : 1 ≤ Fintype.card S := Fintype.card_pos_iff.2 ⟨s⟩
    have h1 : (Finset.univ.filter fun x : S => x = s).card = 1 :=
      Finset.card_eq_one.2 ⟨s, by ext; simp⟩
    simp only [c, Finset.sum_ite, Finset.sum_const, Finset.filter_ne', Finset.mem_univ,
      Finset.card_erase_of_mem, Finset.card_univ, nsmul_eq_mul, Nat.cast_sub hcard, Nat.cast_one]
    rw [h1, Nat.cast_one, one_mul]
    change 1 - p + n * (p / n) ≤ 1
    rcases eq_or_ne n 0 with h | h
    · rw [h]
      linarith [measureReal_nonneg (μ := μ) (s := {ω | X' ω ≠ X ω})]
    · rw [mul_div_cancel₀ _ h]
      linarith
  have hgibbs := sum_mul_log_le_sum_mul_log Finset.univ (fun a _ => hN0 a) (fun a _ => hq0 a)
    (fun a _ => hNq a) hsum
  have hlog : ∀ a, N a * Real.log (q a) = N a * Real.log (R a.2)
      + if a.1 = a.2 then N a * Real.log (1 - p) else N a * Real.log (p / n) := fun a => by
    by_cases ha : N a = 0
    · simp [ha]
    obtain ⟨h1, h2⟩ := hpos a ha
    simp only [q]
    rw [Real.log_mul h1.ne' h2.ne', mul_add]
    by_cases had : a.1 = a.2 <;> simp [c, had]
  simp only [hlog, Finset.sum_add_distrib, Finset.sum_ite, ← Finset.sum_mul, hdiag, hoff] at hgibbs
  have hplog : p * Real.log (p / n) = p * Real.log p - p * Real.log n := by
    rcases eq_or_ne p 0 with h | h
    · simp [h]
    obtain ⟨a, ha, hNa⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hoff ▸ h)
    have hp' : 0 < p := (measureReal_nonneg).lt_of_ne' h
    rw [Real.log_div hp'.ne' (hn a (Finset.mem_filter.1 ha).2).ne', mul_sub]
  have hH : H[X | X' ; μ] = measureEntropy ν - measureEntropy (ν.map Prod.snd) := by
    rw [condEntropy_def, Measure.map_map measurable_snd hW]
    rfl
  have hent := measureEntropy_map_eq_neg_sum_mul_log ν Prod.snd
  have hent' := measureEntropy_eq_neg_sum_mul_log ν
  rw [hH, Real.binEntropy, Real.log_inv, Real.log_inv]
  change measureEntropy ν = -∑ a, N a * Real.log (N a) at hent'
  change measureEntropy (ν.map Prod.snd) = -∑ a, N a * Real.log (R a.2) at hent
  linarith

theorem condEntropy_le_binEntropy_add_mul_log_of_comp (hX : Measurable X) (hY : Measurable Y)
    (g : T → S) :
    H[X | Y ; μ] ≤ Real.binEntropy (μ.real {ω | g (Y ω) ≠ X ω})
      + μ.real {ω | g (Y ω) ≠ X ω} * Real.log (Fintype.card S - 1) :=
  (condEntropy_le_condEntropy_comp hX hY g).trans
    (condEntropy_le_binEntropy_add_mul_log hX ((measurable_of_finite g).comp hY))

theorem condEntropy_le_log_two_add_mul_log_card (hX : Measurable X) (hY : Measurable Y)
    (g : T → S) :
    H[X | Y ; μ] ≤ Real.log 2 + μ.real {ω | g (Y ω) ≠ X ω} * Real.log (Fintype.card S) := by
  refine (condEntropy_le_binEntropy_add_mul_log_of_comp hX hY g).trans (add_le_add
    Real.binEntropy_le_log_two (mul_le_mul_of_nonneg_left ?_ measureReal_nonneg))
  rcases Nat.lt_or_ge 1 (Fintype.card S) with h | h
  · have : (1 : ℝ) < Fintype.card S := by exact_mod_cast h
    exact Real.log_le_log (by linarith) (by linarith)
  · obtain h0 | h1 : Fintype.card S = 0 ∨ Fintype.card S = 1 := by omega
    · simp [h0]
    · simp [h1]

end Meat
