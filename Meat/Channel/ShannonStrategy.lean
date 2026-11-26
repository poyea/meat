import Meat.Channel.StateIid

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

namespace ShannonStrategy

open StateIid

variable {M St A B : Type*} {n : ℕ}

noncomputable def strategyChannel (W : DMC (A × St) B) (pS : PMF St) : DMC (St → A) B :=
  avgChannel (lift W) pS

structure CausalCode (M St A B : Type*) (n : ℕ) where
  enc : M → (i : Fin n) → (Fin i → St) → St → A
  dec : (Fin n → B) → M

namespace CausalCode

noncomputable def avgError [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : CausalCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) : ℝ≥0∞ :=
  (∑ m, ∑ s : Fin n → St, ∑ y : Fin n → B, if c.dec y = m then 0 else
    ∏ i, pS (s i) * W (c.enc m i (seqPrefix s i) (s i), s i) (y i)) / (Fintype.card M : ℝ≥0∞)

def toBothCode (c : CausalCode M St A B n) : BothCode M St A B n :=
  ⟨c.enc, fun y _ => c.dec y⟩

theorem avgError_toBothCode [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : CausalCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) :
    c.toBothCode.avgError W pS = c.avgError W pS := rfl

def ofBlockCode (c : BlockCode M (St → A) B n) : CausalCode M St A B n :=
  ⟨fun m i _ s => c.enc m i s, c.dec⟩

theorem avgError_ofBlockCode [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : BlockCode M (St → A) B n) (W : DMC (A × St) B) (pS : PMF St) :
    (ofBlockCode c).avgError W pS = c.avgError (strategyChannel W pS) := by
  rw [strategyChannel, ← avgError_uninformed (St := St) c (lift W) pS, avgError,
    StateCode.avgError]
  congr 1
  refine sum_congr rfl fun m _ => sum_congr rfl fun s _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : c.dec y = m <;> simp [h, ofBlockCode, uninformed, lift, prod_mul_distrib]

end CausalCode

def CausalAchievable [Fintype St] [Fintype B] (W : DMC (A × St) B) (pS : PMF St) (R : ℝ) :
    Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : CausalCode (Fin k) St A B n, c.avgError W pS ≤ ε

section Converse

variable [Fintype St] [DecidableEq St] [MeasurableSpace St] [MeasurableSingletonClass St]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

private lemma term_eq (W : DMC (A × St) B) (pS : PMF St) (p : PMF (St → A)) :
    H[fun x : (St → A) × (B × St) => x.2.1 | fun _ => () ; (bothChannel W pS).jointMeasure p] -
      H[fun x : (St → A) × (B × St) => x.2.1 | Prod.fst ; (bothChannel W pS).jointMeasure p] =
      (strategyChannel W pS).inputMutualInfo p := by
  have hmap : ((bothChannel W pS).jointMeasure p).map (fun x => (x.1, x.2.1)) =
      (strategyChannel W pS).jointMeasure p := by
    rw [DMC.jointMeasure_eq_toMeasure, DMC.jointMeasure_eq_toMeasure,
      PMF.toMeasure_map _ _ (measurable_of_finite _)]
    congr 1
    simp only [DMC.jointPMF, PMF.map_bind, bothChannel, rxChannel, strategyChannel, avgChannel,
      lift, PMF.map_comp, Function.comp_def]
  rw [Interactive.condEntropy_const, DMC.inputMutualInfo, mutualInfo_comm,
    mutualInfo_eq_entropy_sub_condEntropy, ← hmap,
    entropy_map _ (measurable_of_finite _) measurable_snd,
    condEntropy_map _ (measurable_of_finite _) measurable_snd measurable_fst]
  rfl

private lemma one_sub_mul_log_card_le [Fintype M] [Nonempty M] [DecidableEq M]
    [MeasurableSpace M] [MeasurableSingletonClass M] (c : CausalCode M St A B n)
    (W : DMC (A × St) B) (pS : PMF St) :
    (1 - (c.avgError W pS).toReal) * Real.log (Fintype.card M) ≤
      n * (strategyChannel W pS).capacity + Real.log 2 := by
  set fb := c.toBothCode.toFeedbackCode
  have h := Interactive.one_sub_mul_log_card_le_sum (bothChannel W pS) fb.enc
    (Equiv.prodPUnit.{0} M).symm Prod.fst (fun _ => ()) (fun _ _ _ => ()) (fun _ _ _ => rfl)
    (fun _ y => c.dec y)
  have hP : (c.avgError W pS).toReal =
      (Interactive.codeMeasure (bothChannel W pS) fb.enc).real {ω | fb.dec ω.2 ≠ ω.1} := by
    rw [FeedbackCode.measureReal_dec_ne, BothCode.avgError_toFeedbackCode,
      CausalCode.avgError_toBothCode]
  calc (1 - (c.avgError W pS).toReal) * Real.log (Fintype.card M)
      = (1 - (Interactive.codeMeasure (bothChannel W pS) fb.enc).real
          {ω | fb.dec ω.2 ≠ ω.1}) * Real.log (Fintype.card M) := by rw [hP]
    _ ≤ _ := h
    _ ≤ n * (strategyChannel W pS).capacity + Real.log 2 := by
      gcongr ?_ + _
      calc _ ≤ ∑ _i : Fin n, (strategyChannel W pS).capacity := sum_le_sum fun i _ =>
            (le_of_eq (term_eq W pS _)).trans (DMC.inputMutualInfo_le_capacity _ _)
        _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem le_capacity_of_causalAchievable (W : DMC (A × St) B) (pS : PMF St) {R : ℝ}
    (h : CausalAchievable W pS R) : R ≤ (strategyChannel W pS).capacity := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hC := (strategyChannel W pS).capacity_nonneg
  set C := (strategyChannel W pS).capacity
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

theorem closure_causalAchievable_eq [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B]
    (W : DMC (A × St) B) (pS : PMF St) :
    closure {R : ℝ | 0 ≤ R ∧ CausalAchievable W pS R} =
      Set.Icc 0 (strategyChannel W pS).capacity := by
  let : MeasurableSpace St := ⊤
  have : MeasurableSingletonClass St := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  refine subset_antisymm (closure_minimal
    (fun R hR => ⟨hR.1, le_capacity_of_causalAchievable W pS hR.2⟩) isClosed_Icc) ?_
  rw [← DMC.closure_achievable_eq (strategyChannel W pS)]
  refine closure_mono fun R hR => ⟨hR.1, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hR.2 ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hn
  exact ⟨k, hk, CausalCode.ofBlockCode c, (CausalCode.avgError_ofBlockCode c W pS).trans_le hc⟩

end ShannonStrategy

end Meat
