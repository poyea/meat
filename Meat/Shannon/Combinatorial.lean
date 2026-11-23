import Meat.Shannon.ChainRule

open MeasureTheory Finset

namespace Meat

def seqRestrict {S : Type*} {n : ℕ} (y : Fin n → S) (A : Finset (Fin n)) : A → S :=
  fun j => y j

variable {Ω S : Type*} [MeasurableSpace Ω] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

theorem sum_condEntropy_le_entropy_restrict (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    {Y : Ω → Fin n → S} (hY : Measurable Y) (A : Finset (Fin n)) :
    ∑ i ∈ A, H[fun ω => Y ω i | fun ω => seqPrefix (Y ω) i ; μ]
      ≤ H[fun ω => seqRestrict (Y ω) A ; μ] := by
  induction A using Finset.induction_on_max with
  | empty =>
    rw [sum_empty]
    exact entropy_nonneg μ _
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hYa : Measurable fun ω => Y ω a := (measurable_pi_apply a).comp hY
    have hYs : Measurable fun ω => seqRestrict (Y ω) s :=
      (measurable_of_finite (fun y : Fin n → S => seqRestrict y s)).comp hY
    have e1 : H[fun ω => seqRestrict (Y ω) (insert a s) ; μ] =
        H[fun ω => (Y ω a, seqRestrict (Y ω) s) ; μ] := by
      refine (entropy_comp_of_injective μ (X := fun ω => seqRestrict (Y ω) (insert a s))
        (f := fun g => (g ⟨a, mem_insert_self a s⟩, fun j : s => g ⟨j, mem_insert_of_mem j.2⟩))
        fun g g' h => ?_).symm
      simp only [Prod.mk.injEq] at h
      funext j
      obtain ⟨j, hj⟩ := j
      rcases mem_insert.1 hj with rfl | hj'
      · exact h.1
      · exact congrFun h.2 ⟨j, hj'⟩
    have e2 := entropy_pair_eq_add_condEntropy (fun ω => Y ω a)
      (fun ω => seqRestrict (Y ω) s) μ
    have e3 : H[fun ω => Y ω a | fun ω => seqPrefix (Y ω) a ; μ] ≤
        H[fun ω => Y ω a | fun ω => seqRestrict (Y ω) s ; μ] :=
      condEntropy_le_condEntropy_comp (μ := μ) hYa
        ((measurable_of_finite (fun y : Fin n → S => seqPrefix y a)).comp hY)
        (fun τ (j : s) => τ ⟨j, hlt j j.2⟩)
    rw [sum_insert ha, e1, e2]
    linarith

theorem shearer (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} {Y : Ω → Fin n → S}
    (hY : Measurable Y) {ι : Type*} [Fintype ι] (A : ι → Finset (Fin n)) (k : ℕ)
    (hk : ∀ i, k ≤ (univ.filter fun t => i ∈ A t).card) :
    k * H[Y ; μ] ≤ ∑ t, H[fun ω => seqRestrict (Y ω) (A t) ; μ] := by
  classical
  set c : Fin n → ℝ := fun i => H[fun ω => Y ω i | fun ω => seqPrefix (Y ω) i ; μ]
  have hc : ∀ i, 0 ≤ c i := fun i =>
    condEntropy_nonneg μ ((measurable_pi_apply i).comp hY)
      ((measurable_of_finite (fun y : Fin n → S => seqPrefix y i)).comp hY)
  have hH : H[Y ; μ] = ∑ i, c i := entropy_eq_sum μ Y
  have hswap : ∑ t, ∑ i ∈ A t, c i =
      ∑ i, ((univ.filter fun t => i ∈ A t).card : ℝ) * c i := by
    have h1 : ∀ t, ∑ i ∈ A t, c i = ∑ i, if i ∈ A t then c i else 0 := fun t => by
      rw [← sum_filter]
      congr 1
      ext
      simp
    rw [sum_congr rfl fun t _ => h1 t, sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  calc (k : ℝ) * H[Y ; μ] = ∑ i, (k : ℝ) * c i := by rw [hH, mul_sum]
    _ ≤ ∑ i, ((univ.filter fun t => i ∈ A t).card : ℝ) * c i :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hk i) (hc i)
    _ = ∑ t, ∑ i ∈ A t, c i := hswap.symm
    _ ≤ _ := sum_le_sum fun t _ => sum_condEntropy_le_entropy_restrict μ hY (A t)

theorem han (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} {Y : Ω → Fin n → S}
    (hY : Measurable Y) :
    ((n : ℝ) - 1) * H[Y ; μ] ≤ ∑ i, H[fun ω => seqRestrict (Y ω) (univ.erase i) ; μ] := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_sub, univ_eq_empty, sum_empty]
    nlinarith [entropy_nonneg μ Y]
  have h := shearer μ hY (fun t : Fin n => univ.erase t) (n - 1) fun i => by
    have : (univ.filter fun t : Fin n => i ∈ univ.erase t) = univ.erase i := by
      ext t
      simp [eq_comm]
    rw [this, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  rwa [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hn.ne'), Nat.cast_one] at h

end Meat
