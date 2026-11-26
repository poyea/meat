import Meat.Continuous.AWGN

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Meat

namespace GaussianBroadcast

structure Code (P : ℝ) (n k₁ k₂ : ℕ) where
  enc : Fin k₁ × Fin k₂ → Fin n → ℝ
  power : ∀ m, ∑ i, enc m i ^ 2 ≤ n * P
  dec₁ : (Fin n → ℝ) → Fin k₁
  dec₂ : (Fin n → ℝ) → Fin k₂
  measurable_dec₁ : Measurable dec₁
  measurable_dec₂ : Measurable dec₂

namespace Code

variable {P : ℝ} {n k₁ k₂ : ℕ}

noncomputable def errorProb (c : Code P n k₁ k₂) (N₁ N₂ : ℝ) (m : Fin k₁ × Fin k₂) : ℝ≥0∞ :=
  ((AWGN.noise N₁ n).prod (AWGN.noise N₂ n))
    {z | (c.dec₁ (c.enc m + z.1), c.dec₂ (c.enc m + z.2)) ≠ m}

noncomputable def avgError (c : Code P n k₁ k₂) (N₁ N₂ : ℝ) : ℝ≥0∞ :=
  (∑ m, c.errorProb N₁ N₂ m) / (k₁ * k₂)

theorem errorProb_le (c : Code P n k₁ k₂) (N₁ N₂ : ℝ) (m : Fin k₁ × Fin k₂) :
    c.errorProb N₁ N₂ m ≤ AWGN.noise N₁ n {z | c.dec₁ (c.enc m + z) ≠ m.1}
      + AWGN.noise N₂ n {z | c.dec₂ (c.enc m + z) ≠ m.2} := by
  have hs : {z : (Fin n → ℝ) × (Fin n → ℝ) | (c.dec₁ (c.enc m + z.1), c.dec₂ (c.enc m + z.2)) ≠ m}
      ⊆ {z | c.dec₁ (c.enc m + z) ≠ m.1} ×ˢ Set.univ
        ∪ Set.univ ×ˢ {z | c.dec₂ (c.enc m + z) ≠ m.2} := by
    intro z hz
    by_contra h
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, Set.mem_ofPred_eq,
      not_or, not_not] at h
    exact hz (Prod.ext h.1 h.2)
  refine (measure_mono hs).trans ((measure_union_le _ _).trans ?_)
  rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one, one_mul]

end Code

def Achievable (P N₁ N₂ R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ k₁ k₂ : ℕ, Real.exp (n * R₁) ≤ k₁ ∧ Real.exp (n * R₂) ≤ k₂ ∧
      ∃ c : Code P n k₁ k₂, c.avgError N₁ N₂ ≤ ε

theorem achievable_zero_left {P N₁ N₂ R : ℝ} (h : AWGN.Achievable P N₂ R) :
    Achievable P N₁ N₂ 0 R := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hn₀ n hn
  refine ⟨1, k, by simp, hk, ⟨fun m => c.enc m.2, fun m => c.power m.2, fun _ => 0, c.dec,
    measurable_const, c.measurable_dec⟩, le_trans ?_ hc⟩
  simp only [Code.avgError, AWGN.Code.avgError, Fintype.sum_prod_type, Finset.univ_unique,
    Finset.sum_singleton, Nat.cast_one, one_mul]
  refine ENNReal.div_le_div_right
    (Finset.sum_le_sum fun m _ => (Code.errorProb_le _ _ _ _).trans ?_) _
  simp [AWGN.Code.errorProb, Subsingleton.elim _ (0 : Fin 1)]

theorem achievable_zero_right {P N₁ N₂ R : ℝ} (h : AWGN.Achievable P N₁ R) :
    Achievable P N₁ N₂ R 0 := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hn₀ n hn
  refine ⟨k, 1, hk, by simp, ⟨fun m => c.enc m.1, fun m => c.power m.1, c.dec, fun _ => 0,
    c.measurable_dec, measurable_const⟩, le_trans ?_ hc⟩
  simp only [Code.avgError, AWGN.Code.avgError, Fintype.sum_prod_type, Finset.univ_unique,
    Finset.sum_singleton, Nat.cast_one, mul_one]
  refine ENNReal.div_le_div_right
    (Finset.sum_le_sum fun m _ => (Code.errorProb_le _ _ _ _).trans ?_) _
  simp [AWGN.Code.errorProb, Subsingleton.elim _ (0 : Fin 1)]

end GaussianBroadcast

end Meat
