import Meat.Channel.StateIid

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

namespace StateIid

variable {M St A B : Type*} {n : ℕ}

structure NoncausalCode (M St A B : Type*) (n : ℕ) where
  enc : M → (Fin n → St) → Fin n → A
  dec : (Fin n → B) → (Fin n → St) → M

namespace NoncausalCode

noncomputable def avgError [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : NoncausalCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) : ℝ≥0∞ :=
  (∑ m, ∑ s : Fin n → St, ∑ y : Fin n → B, if c.dec y s = m then 0 else
    ∏ i, pS (s i) * W (c.enc m s i, s i) (y i)) / (Fintype.card M : ℝ≥0∞)

def ofBothCode (c : BothCode M St A B n) : NoncausalCode M St A B n :=
  ⟨fun m s i => c.enc m i (seqPrefix s i) (s i), c.dec⟩

theorem avgError_ofBothCode [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : BothCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) :
    (ofBothCode c).avgError W pS = c.avgError W pS := rfl

def slice (c : NoncausalCode M St A B n) (s : Fin n → St) : BlockCode M (A × St) B n :=
  ⟨fun m i => (c.enc m s i, s i), fun y => c.dec y s⟩

theorem avgError_eq_sum_slice [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : NoncausalCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) :
    c.avgError W pS = ∑ s, (∏ i, pS (s i)) * (c.slice s).avgError W := by
  rw [avgError, sum_comm, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun s _ => ?_
  rw [BlockCode.avgError, div_eq_mul_inv, ← mul_assoc, mul_sum]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [BlockCode.errorProb, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : c.dec y s = m <;> simp [h, slice, DMC.blockProb, prod_mul_distrib]

end NoncausalCode

def NoncausalAchievable [Fintype St] [Fintype B] (W : DMC (A × St) B) (pS : PMF St) (R : ℝ) :
    Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : NoncausalCode (Fin k) St A B n, c.avgError W pS ≤ ε

section Converse

variable [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

private lemma one_sub_mul_log_card_le_sum [Fintype M] [Nonempty M] [MeasurableSpace M]
    [MeasurableSingletonClass M] [DecidableEq M] {A' : Type*} [Fintype A'] [MeasurableSpace A']
    [MeasurableSingletonClass A'] (c : BlockCode M A' B n) (W : DMC A' B) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M) ≤
      ∑ i, W.inputMutualInfo (c.inputLaw i) + Real.log 2 := by
  have h1 := c.mutualInfo_le_sum_inputMutualInfo W
  have h2 := c.condEntropy_fst_snd_codeMeasure_le W
  have h3 := mutualInfo_eq_entropy_sub_condEntropy Prod.fst Prod.snd (c.codeMeasure W)
  rw [BlockCode.entropy_fst_codeMeasure] at h3
  have h4 : (1 - (c.avgError W).toReal) * Real.log (Fintype.card M)
      = Real.log (Fintype.card M) - (c.avgError W).toReal * Real.log (Fintype.card M) := by ring
  linarith

omit [Fintype St] in
private lemma slice_le [Finite St] [Fintype M] [Nonempty M] [MeasurableSpace M]
    [MeasurableSingletonClass M] [DecidableEq M] (c : NoncausalCode M St A B n)
    (W : DMC (A × St) B) (s : Fin n → St) :
    (1 - ((c.slice s).avgError W).toReal) * Real.log (Fintype.card M) ≤
      ∑ i, DMC.capacity (fun a => W (a, s i)) + Real.log 2 := by
  have := Fintype.ofFinite St
  refine (one_sub_mul_log_card_le_sum (c.slice s) W).trans (add_le_add_left
    (sum_le_sum fun i _ => ?_) _)
  have hl : (c.slice s).inputLaw i = ((PMF.ofFintype _ (sum_inv_card M)).map
      fun m => c.enc m s i).map fun a => (a, s i) := by
    simp only [BlockCode.inputLaw, NoncausalCode.slice, PMF.map_comp, Function.comp_def]
  rw [hl, ← inputMutualInfo_comp]
  exact DMC.inputMutualInfo_le_capacity _ _

private lemma one_sub_mul_log_card_le [Fintype M] [Nonempty M] [MeasurableSpace M]
    [MeasurableSingletonClass M] [DecidableEq M] (c : NoncausalCode M St A B n)
    (W : DMC (A × St) B) (pS : PMF St) :
    (1 - (c.avgError W pS).toReal) * Real.log (Fintype.card M) ≤
      n * ∑ x, (pS x).toReal * DMC.capacity (fun a => W (a, x)) + Real.log 2 := by
  have hK : (Fintype.card M : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hfin : ∀ s, (c.slice s).avgError W ≠ ∞ := fun s =>
    ENNReal.div_ne_top (ENNReal.sum_ne_top.2 fun m _ => (c.slice s).errorProb_ne_top W m) hK
  have hP : (c.avgError W pS).toReal =
      ∑ s, iidProb pS s * ((c.slice s).avgError W).toReal := by
    rw [c.avgError_eq_sum_slice, ENNReal.toReal_sum fun s _ =>
      ENNReal.mul_ne_top (ENNReal.prod_ne_top fun i _ => PMF.apply_ne_top _ _) (hfin s)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_prod, iidProb]
  have hw : ∑ s : Fin n → St, iidProb pS s = 1 := sum_iidProb pS n
  have hmarg : ∀ i, ∑ s : Fin n → St, iidProb pS s * DMC.capacity (fun a => W (a, s i)) =
      ∑ x, (pS x).toReal * DMC.capacity (fun a => W (a, x)) := fun i =>
    sum_prod_mul_apply (fun _ x => (pS x).toReal) (fun _ => sum_toReal_pmf_eq_one pS)
      (fun x => DMC.capacity (fun a => W (a, x))) i
  calc (1 - (c.avgError W pS).toReal) * Real.log (Fintype.card M)
      = ∑ s, iidProb pS s * ((1 - ((c.slice s).avgError W).toReal) *
          Real.log (Fintype.card M)) := by
        rw [hP]
        simp only [mul_sub, sum_sub_distrib, ← mul_assoc, ← sum_mul, sub_mul, hw,
          one_mul]
    _ ≤ ∑ s, iidProb pS s * (∑ i, DMC.capacity (fun a => W (a, s i)) + Real.log 2) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (slice_le c W s) (iidProb_nonneg pS s)
    _ = _ := by
        rw [sum_congr rfl fun s _ => mul_add _ _ _, sum_add_distrib, ← sum_mul, hw, one_mul,
          sum_congr rfl fun s _ => mul_sum _ _ _, sum_comm]
        simp only [hmarg, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem le_of_noncausalAchievable (W : DMC (A × St) B) (pS : PMF St) {R : ℝ}
    (h : NoncausalAchievable W pS R) :
    R ≤ ∑ x, (pS x).toReal * DMC.capacity (fun a => W (a, x)) := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  set C := ∑ x, (pS x).toReal * DMC.capacity (fun a => W (a, x))
  have hC : 0 ≤ C := sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (DMC.capacity_nonneg _)
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
  have key := one_sub_mul_log_card_le c W pS
  rw [Fintype.card_fin] at key
  have hPe : (c.avgError W pS).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1 : (1 - e) * Real.log k ≤ n * C + Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)).trans key
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

end Converse

theorem closure_noncausalAchievable_eq [Fintype St] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (W : DMC (A × St) B) (pS : PMF St) :
    closure {R : ℝ | 0 ≤ R ∧ NoncausalAchievable W pS R} =
      Set.Icc 0 (∑ s, (pS s).toReal * DMC.capacity (fun a => W (a, s))) := by
  let : MeasurableSpace St := ⊤
  have : MeasurableSingletonClass St := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  refine subset_antisymm (closure_minimal
    (fun R hR => ⟨hR.1, le_of_noncausalAchievable W pS hR.2⟩) isClosed_Icc) ?_
  rw [← closure_bothAchievable_eq W pS]
  refine closure_mono fun R hR => ⟨hR.1, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hR.2 ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hn
  exact ⟨k, hk, NoncausalCode.ofBothCode c, (NoncausalCode.avgError_ofBothCode c W pS).trans_le hc⟩

end StateIid

end Meat
