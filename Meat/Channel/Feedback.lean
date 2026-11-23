import Meat.Channel.CodingTheorem
import Meat.Open.Interactive

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

structure FeedbackCode (M A B : Type*) (n : ℕ) where
  enc : M → (i : Fin n) → (Fin i → B) → A
  dec : (Fin n → B) → M

namespace FeedbackCode

variable {M A B : Type*} {n : ℕ}

noncomputable def errorProb [Fintype B] [DecidableEq M] (c : FeedbackCode M A B n)
    (W : DMC A B) (m : M) : ℝ≥0∞ :=
  ∑ y : Fin n → B, if c.dec y = m then 0 else Interactive.seqProb W (c.enc m) y

noncomputable def avgError [Fintype B] [Fintype M] [DecidableEq M] (c : FeedbackCode M A B n)
    (W : DMC A B) : ℝ≥0∞ :=
  (∑ m, c.errorProb W m) / (Fintype.card M : ℝ≥0∞)

def ofBlockCode (c : BlockCode M A B n) : FeedbackCode M A B n :=
  ⟨fun m i _ => c.enc m i, c.dec⟩

theorem errorProb_ofBlockCode [Fintype B] [DecidableEq M] (c : BlockCode M A B n) (W : DMC A B)
    (m : M) : (ofBlockCode c).errorProb W m = c.errorProb W m := rfl

theorem avgError_ofBlockCode [Fintype B] [Fintype M] [DecidableEq M] (c : BlockCode M A B n)
    (W : DMC A B) : (ofBlockCode c).avgError W = c.avgError W := rfl

variable [Fintype M] [Nonempty M] [DecidableEq M] [MeasurableSpace M]
  [MeasurableSingletonClass M] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem measureReal_dec_ne (c : FeedbackCode M A B n) (W : DMC A B) :
    (Interactive.codeMeasure W c.enc).real {ω | c.dec ω.2 ≠ ω.1} = (c.avgError W).toReal := by
  classical
  rw [measureReal_def, Interactive.codeMeasure_apply, avgError, div_eq_mul_inv, sum_mul]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [errorProb, sum_mul]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : c.dec y = m
  · simp [h]
  · simp only [h, ne_eq, not_false_eq_true, ite_true, ite_false]
    rw [mul_comm]

theorem one_sub_mul_log_card_le [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (c : FeedbackCode M A B n) (W : DMC A B) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M) ≤ n * W.capacity + Real.log 2 := by
  have h := Interactive.one_sub_mul_log_card_le_sum_mutualInfo W c.enc c.dec
  rw [c.measureReal_dec_ne W] at h
  refine h.trans (add_le_add_left ?_ _)
  have hi : ∀ i, H[Prod.snd ; W.jointMeasure (Interactive.inputLaw W c.enc i)] -
      H[Prod.snd | Prod.fst ; W.jointMeasure (Interactive.inputLaw W c.enc i)] ≤ W.capacity :=
    fun i => by
      have e : W.inputMutualInfo (Interactive.inputLaw W c.enc i) =
          H[Prod.snd ; W.jointMeasure (Interactive.inputLaw W c.enc i)] -
            H[Prod.snd | Prod.fst ; W.jointMeasure (Interactive.inputLaw W c.enc i)] := by
        rw [DMC.inputMutualInfo, mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
      rw [← e]
      exact W.inputMutualInfo_le_capacity _
  refine (sum_le_sum fun i _ => hi i).trans_eq ?_
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

end FeedbackCode

namespace DMC

variable {A B : Type*}

def FeedbackAchievable [Fintype B] (W : DMC A B) (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : FeedbackCode (Fin k) A B n, c.avgError W ≤ ε

theorem Achievable.feedback [Fintype B] {W : DMC A B} {R : ℝ} (h : W.Achievable R) :
    W.FeedbackAchievable R := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hn
  exact ⟨k, hk, FeedbackCode.ofBlockCode c, hc⟩

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem le_capacity_of_feedbackAchievable (W : DMC A B) {R : ℝ} (h : W.FeedbackAchievable R) :
    R ≤ W.capacity := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hC := W.capacity_nonneg
  set C := W.capacity
  set δ := R - C with hδ
  have hδ0 : 0 < δ := by linarith
  have hR : 0 < R := by linarith
  set e := δ / (2 * R) with he
  have he0 : 0 < e := by positivity
  have he1 : e * R = δ / 2 := by
    rw [he]
    field_simp
  have he2 : 0 < 1 - e := by nlinarith
  obtain ⟨N, hN⟩ := h (ENNReal.ofReal e) (ENNReal.ofReal_pos.2 he0)
  obtain ⟨n0, hn0⟩ := exists_nat_gt (2 * Real.log 2 / δ)
  obtain ⟨n, hNn, hn0n⟩ : ∃ n : ℕ, N ≤ n ∧ n0 ≤ n := ⟨max N n0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hNn
  have hn : 2 * Real.log 2 < n * δ := by
    rw [← div_lt_iff₀ hδ0]
    exact hn0.trans_le (by exact_mod_cast hn0n)
  have hk0 : (0 : ℝ) < k := (Real.exp_pos _).trans_le hk
  have : Nonempty (Fin k) := ⟨⟨0, by exact_mod_cast hk0⟩⟩
  have key := c.one_sub_mul_log_card_le W
  rw [Fintype.card_fin] at key
  have hPe : (c.avgError W).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1 : (1 - e) * Real.log k ≤ n * C + Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)).trans key
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

theorem closure_feedbackAchievable_eq [Nonempty A] (W : DMC A B) :
    closure {R : ℝ | 0 ≤ R ∧ FeedbackAchievable W R} = Set.Icc 0 (capacity W) := by
  refine subset_antisymm (closure_minimal
    (fun R hR => ⟨hR.1, le_capacity_of_feedbackAchievable W hR.2⟩) isClosed_Icc) ?_
  rw [← closure_achievable_eq W]
  exact closure_mono fun R hR => ⟨hR.1, hR.2.feedback⟩

end DMC

end Meat
