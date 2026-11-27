import Meat.Continuous.AWGNConverse

open MeasureTheory
open scoped ENNReal

namespace Meat

namespace DirtyPaper

structure Code (P : ℝ) (n k : ℕ) where
  enc : Fin k → (Fin n → ℝ) → Fin n → ℝ
  power : ∀ m s, ∑ i, enc m s i ^ 2 ≤ n * P
  measurable_enc : ∀ m, Measurable (enc m)
  dec : (Fin n → ℝ) → Fin k
  measurable_dec : Measurable dec

namespace Code

variable {P : ℝ} {n k : ℕ}

noncomputable def errorProb (c : Code P n k) (Q N : ℝ) (m : Fin k) : ℝ≥0∞ :=
  ∫⁻ s, AWGN.noise N n {z | c.dec (c.enc m s + s + z) ≠ m} ∂AWGN.noise Q n

noncomputable def avgError (c : Code P n k) (Q N : ℝ) : ℝ≥0∞ :=
  (∑ m, c.errorProb Q N m) / k

def toAWGN (c : Code P n k) (s : Fin n → ℝ) : AWGN.Code P n k where
  enc m := c.enc m s
  power m := c.power m s
  dec y := c.dec (y + s)
  measurable_dec := c.measurable_dec.comp (measurable_add_const s)

private theorem errorProb_toAWGN (c : Code P n k) (N : ℝ) (s : Fin n → ℝ) (m : Fin k) :
    (c.toAWGN s).errorProb N m = AWGN.noise N n {z | c.dec (c.enc m s + s + z) ≠ m} := by
  simp only [AWGN.Code.errorProb, toAWGN, add_right_comm]

private lemma measurable_errorSet (c : Code P n k) (N : ℝ) (m : Fin k) :
    Measurable fun s => AWGN.noise N n {z | c.dec (c.enc m s + s + z) ≠ m} := by
  have hs : MeasurableSet {p : (Fin n → ℝ) × (Fin n → ℝ) |
      c.dec (c.enc m p.1 + p.1 + p.2) ≠ m} :=
    (measurableSet_singleton m).compl.preimage (c.measurable_dec.comp
      (((c.measurable_enc m).comp measurable_fst).add measurable_fst |>.add measurable_snd))
  exact measurable_measure_prodMk_left hs

private theorem avgError_eq_lintegral (c : Code P n k) (Q N : ℝ) :
    c.avgError Q N = ∫⁻ s, (c.toAWGN s).avgError N ∂AWGN.noise Q n := by
  simp only [avgError, AWGN.Code.avgError, errorProb, errorProb_toAWGN, div_eq_mul_inv]
  rw [lintegral_mul_const _ (Finset.measurable_sum _ fun m _ => measurable_errorSet c N m),
    lintegral_finsetSum _ fun m _ => measurable_errorSet c N m]

theorem exists_avgError_toAWGN_le (c : Code P n k) (Q N : ℝ) :
    ∃ s, (c.toAWGN s).avgError N ≤ c.avgError Q N := by
  rw [avgError_eq_lintegral]
  refine exists_le_lintegral (Measurable.aemeasurable ?_)
  simp only [AWGN.Code.avgError, errorProb_toAWGN]
  exact (Finset.measurable_sum _ fun m _ => measurable_errorSet c N m).div_const _

end Code

def Achievable (P Q N R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : Code P n k, c.avgError Q N ≤ ε

theorem Achievable.awgn {P Q N R : ℝ} (h : Achievable P Q N R) : AWGN.Achievable P N R := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hn₀ n hn
  obtain ⟨s, hs⟩ := c.exists_avgError_toAWGN_le Q N
  exact ⟨k, hk, c.toAWGN s, hs.trans hc⟩

theorem le_awgnCapacity_of_achievable {P Q N R : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (h : Achievable P Q N R) : R ≤ awgnCapacity P N :=
  AWGN.le_awgnCapacity_of_achievable hP hN h.awgn

theorem achievable_zero {P : ℝ} (hP : 0 ≤ P) (Q N : ℝ) : Achievable P Q N 0 := by
  intro ε _
  refine ⟨0, fun n _ => ⟨1, by simp, ⟨fun _ _ _ => 0, fun _ _ => by
    simpa using mul_nonneg n.cast_nonneg hP, fun _ => measurable_const,
    fun _ => 0, measurable_const⟩, ?_⟩⟩
  simp [Code.avgError, Code.errorProb, Subsingleton.elim _ (0 : Fin 1)]

theorem closure_achievable_eq_of {P Q N : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (hach : ∀ R, 0 ≤ R → R < awgnCapacity P N → Achievable P Q N R) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable P Q N R} = Set.Icc 0 (awgnCapacity P N) := by
  refine subset_antisymm (closure_minimal (fun R hR =>
    ⟨hR.1, le_awgnCapacity_of_achievable hP hN hR.2⟩) isClosed_Icc) fun R hR => ?_
  rcases (AWGN.awgnCapacity_nonneg hP hN).eq_or_lt with h | h
  · rw [← h, Set.Icc_self, Set.mem_singleton_iff] at hR
    exact subset_closure ⟨hR.symm ▸ le_rfl, hR ▸ achievable_zero hP Q N⟩
  · rw [← closure_Ico h.ne] at hR
    refine closure_mono (fun R (hR : R ∈ Set.Ico 0 (awgnCapacity P N)) => ?_) hR
    exact ⟨hR.1, hach R hR.1 hR.2⟩

end DirtyPaper

end Meat
