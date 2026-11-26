import Meat.Channel.State
import Meat.Channel.Feedback
import Meat.Channel.ErrorExponent
import Meat.Channel.MultipleAccessK

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

namespace StateIid

variable {M St A B : Type*} {n : ℕ}

noncomputable def avgChannel (W : DMC (A × St) B) (pS : PMF St) : DMC A B :=
  fun a => pS.bind fun s => W (a, s)

noncomputable def rxChannel (W : DMC (A × St) B) (pS : PMF St) : DMC A (B × St) :=
  fun a => pS.bind fun s => (W (a, s)).map fun b => (b, s)

def lift (W : DMC (A × St) B) : DMC ((St → A) × St) B :=
  fun ts => W (ts.1 ts.2, ts.2)

noncomputable def bothChannel (W : DMC (A × St) B) (pS : PMF St) : DMC (St → A) (B × St) :=
  rxChannel (lift W) pS

theorem avgChannel_apply [Fintype St] (W : DMC (A × St) B) (pS : PMF St) (a : A) (b : B) :
    avgChannel W pS a b = ∑ s, pS s * W (a, s) b := by
  rw [avgChannel, PMF.bind_apply, tsum_fintype]

theorem rxChannel_apply (W : DMC (A × St) B) (pS : PMF St) (a : A) (bs : B × St) :
    rxChannel W pS a bs = pS bs.2 * W (a, bs.2) bs.1 := by
  classical
  rw [rxChannel, PMF.bind_apply, tsum_eq_single bs.2 fun s hs => by
    rw [PMF.map_apply, ENNReal.tsum_eq_zero.2 fun b => by
      simp only [ite_eq_right_iff]
      exact fun h => absurd (congrArg Prod.snd h).symm hs, mul_zero]]
  congr 1
  exact PMF.map_apply_of_injective _ (fun b b' h => (Prod.mk.inj h).1) bs.1

private lemma sum_unzip [Fintype St] [Fintype B] (F : (Fin n → B) → (Fin n → St) → ℝ≥0∞) :
    ∑ z : Fin n → B × St, F (fun i => (z i).1) (fun i => (z i).2) = ∑ s, ∑ y, F y s := by
  calc ∑ z : Fin n → B × St, F (fun i => (z i).1) (fun i => (z i).2)
      = ∑ z : Fin n → B × St, (fun p : (Fin n → B) × (Fin n → St) => F p.1 p.2)
          (Equiv.arrowProdEquivProdArrow _ _ _ z) := rfl
    _ = ∑ p : (Fin n → B) × (Fin n → St), F p.1 p.2 :=
        Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => B) fun _ => St)
          fun p => F p.1 p.2
    _ = _ := by rw [Fintype.sum_prod_type, sum_comm]

def uninformed (c : BlockCode M A B n) : StateCode M St A B n :=
  ⟨fun m _ => c.enc m, c.dec⟩

theorem avgError_uninformed [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : BlockCode M A B n) (W : DMC (A × St) B) (pS : PMF St) :
    (uninformed c : StateCode M St A B n).avgError W pS = c.avgError (avgChannel W pS) := by
  rw [StateCode.avgError, BlockCode.avgError]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [BlockCode.errorProb]
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  simp only [uninformed]
  by_cases h : c.dec y = m
  · simp [h]
  · simp only [h, ↓reduceIte, DMC.blockProb, avgChannel_apply, ← prod_mul_distrib]
    exact (Fintype.prod_sum fun i s => pS s * W (c.enc m i, s) (y i)).symm

def UninformedAchievable [Fintype St] [Fintype B] (W : DMC (A × St) B) (pS : PMF St)
    (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : BlockCode (Fin k) A B n,
      (uninformed c : StateCode (Fin k) St A B n).avgError W pS ≤ ε

theorem uninformedAchievable_iff [Fintype St] [Fintype B] (W : DMC (A × St) B) (pS : PMF St)
    (R : ℝ) : UninformedAchievable W pS R ↔ (avgChannel W pS).Achievable R := by
  simp only [UninformedAchievable, DMC.Achievable, avgError_uninformed]

theorem closure_uninformedAchievable_eq [Fintype St] [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (W : DMC (A × St) B) (pS : PMF St) :
    closure {R : ℝ | 0 ≤ R ∧ UninformedAchievable W pS R} =
      Set.Icc 0 (avgChannel W pS).capacity := by
  simp only [uninformedAchievable_iff]
  exact DMC.closure_achievable_eq _

structure ReceiverCode (M St A B : Type*) (n : ℕ) where
  enc : M → Fin n → A
  dec : (Fin n → B) → (Fin n → St) → M

namespace ReceiverCode

noncomputable def avgError [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : ReceiverCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) : ℝ≥0∞ :=
  (∑ m, ∑ s : Fin n → St, ∑ y : Fin n → B,
    if c.dec y s = m then 0 else ∏ i, pS (s i) * W (c.enc m i, s i) (y i)) /
    (Fintype.card M : ℝ≥0∞)

def toBlockCode (c : ReceiverCode M St A B n) : BlockCode M A (B × St) n :=
  ⟨c.enc, fun z => c.dec (fun i => (z i).1) fun i => (z i).2⟩

def ofBlockCode (c : BlockCode M A (B × St) n) : ReceiverCode M St A B n :=
  ⟨c.enc, fun y s => c.dec fun i => (y i, s i)⟩

theorem avgError_toBlockCode [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : ReceiverCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) :
    c.toBlockCode.avgError (rxChannel W pS) = c.avgError W pS := by
  rw [BlockCode.avgError, avgError]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [BlockCode.errorProb]
  simp only [DMC.blockProb, rxChannel_apply, toBlockCode]
  exact sum_unzip fun y s => if c.dec y s = m then 0 else ∏ i, pS (s i) * W (c.enc m i, s i) (y i)

end ReceiverCode

def ReceiverAchievable [Fintype St] [Fintype B] (W : DMC (A × St) B) (pS : PMF St)
    (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : ReceiverCode (Fin k) St A B n, c.avgError W pS ≤ ε

theorem receiverAchievable_iff [Fintype St] [Fintype B] (W : DMC (A × St) B) (pS : PMF St)
    (R : ℝ) : ReceiverAchievable W pS R ↔ (rxChannel W pS).Achievable R := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, hk, c, hc⟩ := hN n hn
    exact ⟨k, hk, c.toBlockCode, (c.avgError_toBlockCode W pS).trans_le hc⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, hk, c, hc⟩ := hN n hn
    exact ⟨k, hk, ReceiverCode.ofBlockCode c,
      ((ReceiverCode.ofBlockCode c).avgError_toBlockCode W pS).symm.trans_le hc⟩

section Info

variable [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem inputMutualInfo_rxChannel (W : DMC (A × St) B) (pS : PMF St) (p : PMF A) :
    (rxChannel W pS).inputMutualInfo p =
      ∑ s, (pS s).toReal * DMC.inputMutualInfo (fun a => W (a, s)) p := by
  have key : ∀ x y : ℝ, x * y * Real.log (x * y) =
      y * (x * Real.log x) + x * (y * Real.log y) := fun x y => by
    have h := Real.negMulLog_mul x y
    simp only [Real.negMulLog] at h
    linarith
  have hW : ∀ a s, ∑ b, (W (a, s) b).toReal = 1 := fun a s => sum_toReal_pmf_eq_one _
  have hp : ∑ a, (p a).toReal = 1 := sum_toReal_pmf_eq_one p
  set P : A → ℝ := fun a => (p a).toReal
  set u : St → ℝ := fun s => (pS s).toReal
  set O : St → B → ℝ := fun s => DMC.outputLaw (fun a => W (a, s)) P
  have hout : ∀ bs : B × St, DMC.outputLaw (rxChannel W pS) P bs = u bs.2 * O bs.2 bs.1 :=
    fun bs => by
      simp only [O, DMC.outputLaw, rxChannel_apply, ENNReal.toReal_mul, mul_sum]
      exact sum_congr rfl fun a _ => by ring
  have hO : ∀ s, ∑ b, O s b = 1 := fun s => by
    simp only [O, DMC.outputLaw]
    rw [sum_comm]
    simp only [← mul_sum, hW, mul_one, P, hp]
  have E1 : ∑ a, ∑ bs : B × St, P a * ((rxChannel W pS a bs).toReal *
      Real.log (rxChannel W pS a bs).toReal) = ∑ s, u s * Real.log (u s) +
        ∑ s, u s * ∑ a, ∑ b, P a * ((W (a, s) b).toReal * Real.log (W (a, s) b).toReal) := by
    simp only [Fintype.sum_prod_type_right, rxChannel_apply, ENNReal.toReal_mul, key, mul_add,
      sum_add_distrib]
    congr 1
    · rw [sum_comm]
      refine sum_congr rfl fun s _ => ?_
      calc ∑ a, ∑ b, P a * ((W (a, s) b).toReal * (u s * Real.log (u s)))
          = ∑ a, P a * (u s * Real.log (u s)) * ∑ b, (W (a, s) b).toReal :=
            sum_congr rfl fun a _ => by
              rw [mul_sum]
              exact sum_congr rfl fun b _ => by ring
        _ = _ := by simp only [hW, mul_one, ← sum_mul, P, hp, one_mul]
    · rw [sum_comm]
      refine sum_congr rfl fun s _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun b _ => by ring
  have E2 : ∑ bs : B × St, DMC.outputLaw (rxChannel W pS) P bs *
      Real.log (DMC.outputLaw (rxChannel W pS) P bs) = ∑ s, u s * Real.log (u s) +
        ∑ s, u s * ∑ b, O s b * Real.log (O s b) := by
    simp only [Fintype.sum_prod_type_right, hout, key, sum_add_distrib]
    congr 1
    · exact sum_congr rfl fun s _ => by rw [← sum_mul, hO, one_mul]
    · exact sum_congr rfl fun s _ => by rw [mul_sum]
  rw [DMC.inputMutualInfo_eq_sub, E1, E2]
  simp only [DMC.inputMutualInfo_eq_sub, mul_sub, sum_sub_distrib]
  ring

omit [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St] in
theorem inputMutualInfo_comp {A' : Type*} [Fintype A'] [MeasurableSpace A']
    [MeasurableSingletonClass A'] (W : DMC A B) (f : A' → A) (p : PMF A') :
    DMC.inputMutualInfo (fun a' => W (f a')) p = W.inputMutualInfo (p.map f) := by
  classical
  have hsum : ∀ g : A → ℝ, ∑ a', (p a').toReal * g (f a') =
      ∑ a, ((p.map f) a).toReal * g a := fun g => by
    simp only [toReal_map_apply, sum_mul]
    rw [← sum_fiberwise univ f (fun a' => (p a').toReal * g (f a'))]
    refine sum_congr rfl fun a _ => sum_congr rfl fun a' ha' => ?_
    rw [(mem_filter.1 ha').2]
  have hO : ∀ b, DMC.outputLaw (fun a' => W (f a')) (fun a' => (p a').toReal) b =
      DMC.outputLaw W (fun a => (p.map f a).toReal) b := fun b =>
    hsum fun a => (W a b).toReal
  rw [DMC.inputMutualInfo_eq_sub, DMC.inputMutualInfo_eq_sub]
  simp only [hO, ← mul_sum]
  rw [hsum fun a => ∑ b, (W a b).toReal * Real.log (W a b).toReal]

theorem inputMutualInfo_bothChannel [DecidableEq St] (W : DMC (A × St) B) (pS : PMF St)
    (p : PMF (St → A)) :
    (bothChannel W pS).inputMutualInfo p =
      ∑ s, (pS s).toReal * DMC.inputMutualInfo (fun a => W (a, s)) (p.map fun t => t s) := by
  rw [bothChannel, inputMutualInfo_rxChannel]
  refine sum_congr rfl fun s _ => ?_
  rw [← inputMutualInfo_comp]
  rfl

omit [MeasurableSpace St] [MeasurableSingletonClass St] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] in
private lemma map_piPMF_eval [DecidableEq St] (q : St → PMF A) (s : St) :
    (piPMF (A := fun _ => A) q).map (fun t => t s) = q s := by
  classical
  ext a
  rw [PMF.map_apply, tsum_fintype]
  simp only [piPMF, PMF.ofFintype_apply]
  have h : ∀ t : St → A, (if a = t s then ∏ i, q i (t i) else 0) =
      ∏ i, (if i = s then (if a = t i then q i (t i) else 0) else q i (t i)) := by
    intro t
    by_cases ha : a = t s
    · simp only [ha, ↓reduceIte]
      refine prod_congr rfl fun i _ => ?_
      by_cases hi : i = s
      · subst hi
        simp
      · simp [hi]
    · simp only [ha, ↓reduceIte]
      exact (prod_eq_zero (mem_univ s) (by simp [ha])).symm
  rw [sum_congr rfl fun t _ => h t]
  rw [← Fintype.prod_sum (fun i x => if i = s then (if a = x then q i x else 0) else q i x)]
  rw [prod_eq_single s (fun i _ hi => by simp [hi, sum_pmf_eq_one]) (by simp)]
  simp

theorem capacity_bothChannel [Nonempty A] [DecidableEq St] (W : DMC (A × St) B) (pS : PMF St) :
    (bothChannel W pS).capacity = ∑ s, (pS s).toReal * DMC.capacity (fun a => W (a, s)) := by
  have : Nonempty (PMF (St → A)) := ⟨PMF.pure fun _ => Classical.arbitrary A⟩
  have : Nonempty (PMF A) := ⟨PMF.pure (Classical.arbitrary A)⟩
  refine le_antisymm (ciSup_le fun p => ?_) (le_of_forall_pos_lt_add fun δ hδ => ?_)
  · rw [inputMutualInfo_bothChannel]
    exact sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (DMC.inputMutualInfo_le_capacity _ _) ENNReal.toReal_nonneg
  · have hq : ∀ s, ∃ q : PMF A, DMC.capacity (fun a => W (a, s)) - δ / 2 <
        DMC.inputMutualInfo (fun a => W (a, s)) q := fun s => by
      have h : DMC.capacity (fun a => W (a, s)) - δ / 2 < DMC.capacity (fun a => W (a, s)) := by
        linarith
      exact exists_lt_of_lt_ciSup h
    choose q hq using hq
    have hle := DMC.inputMutualInfo_le_capacity (bothChannel W pS) (piPMF (A := fun _ => A) q)
    rw [inputMutualInfo_bothChannel] at hle
    simp only [map_piPMF_eval] at hle
    have hu : ∑ s, (pS s).toReal = 1 := sum_toReal_pmf_eq_one pS
    have h1 : ∑ s, (pS s).toReal * DMC.capacity (fun a => W (a, s)) ≤
        ∑ s, (pS s).toReal * DMC.inputMutualInfo (fun a => W (a, s)) (q s) + δ / 2 := by
      have h2 : ∑ s, (pS s).toReal * (DMC.capacity (fun a => W (a, s)) - δ / 2) ≤
          ∑ s, (pS s).toReal * DMC.inputMutualInfo (fun a => W (a, s)) (q s) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hq s).le ENNReal.toReal_nonneg
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hu, one_mul] at h2
      linarith
    linarith

end Info

theorem closure_receiverAchievable_eq [Fintype St] [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (W : DMC (A × St) B) (pS : PMF St) :
    closure {R : ℝ | 0 ≤ R ∧ ReceiverAchievable W pS R} =
      Set.Icc 0 (⨆ p : PMF A, ∑ s, (pS s).toReal * DMC.inputMutualInfo (fun a => W (a, s)) p) := by
  let : MeasurableSpace St := ⊤
  have : MeasurableSingletonClass St := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  simp only [receiverAchievable_iff, ← inputMutualInfo_rxChannel]
  exact DMC.closure_achievable_eq _

structure BothCode (M St A B : Type*) (n : ℕ) where
  enc : M → (i : Fin n) → (Fin i → St) → St → A
  dec : (Fin n → B) → (Fin n → St) → M

namespace BothCode

noncomputable def avgError [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : BothCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) : ℝ≥0∞ :=
  (∑ m, ∑ s : Fin n → St, ∑ y : Fin n → B, if c.dec y s = m then 0 else
    ∏ i, pS (s i) * W (c.enc m i (seqPrefix s i) (s i), s i) (y i)) / (Fintype.card M : ℝ≥0∞)

def toFeedbackCode (c : BothCode M St A B n) : FeedbackCode M (St → A) (B × St) n :=
  ⟨fun m i q => c.enc m i fun j => (q j).2, fun z => c.dec (fun i => (z i).1) fun i => (z i).2⟩

def ofBlockCode (c : BlockCode M (St → A) (B × St) n) : BothCode M St A B n :=
  ⟨fun m i _ s => c.enc m i s, fun y s => c.dec fun i => (y i, s i)⟩

theorem avgError_toFeedbackCode [Fintype M] [DecidableEq M] [Fintype St] [Fintype B]
    (c : BothCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) :
    c.toFeedbackCode.avgError (bothChannel W pS) = c.avgError W pS := by
  rw [FeedbackCode.avgError, avgError]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [FeedbackCode.errorProb]
  simp only [Interactive.seqProb, bothChannel, rxChannel_apply, toFeedbackCode, lift]
  exact sum_unzip fun y s => if c.dec y s = m then 0 else
    ∏ i, pS (s i) * W (c.enc m i (seqPrefix s i) (s i), s i) (y i)

end BothCode

def BothAchievable [Fintype St] [Fintype B] (W : DMC (A × St) B) (pS : PMF St) (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : BothCode (Fin k) St A B n, c.avgError W pS ≤ ε

theorem closure_bothAchievable_eq [Fintype St] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (W : DMC (A × St) B) (pS : PMF St) :
    closure {R : ℝ | 0 ≤ R ∧ BothAchievable W pS R} =
      Set.Icc 0 (∑ s, (pS s).toReal * DMC.capacity (fun a => W (a, s))) := by
  classical
  let : MeasurableSpace St := ⊤
  have : MeasurableSingletonClass St := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  rw [← capacity_bothChannel]
  refine subset_antisymm (closure_minimal (fun R hR => ⟨hR.1,
    DMC.le_capacity_of_feedbackAchievable _ fun ε hε => ?_⟩) isClosed_Icc) ?_
  · obtain ⟨N, hN⟩ := hR.2 ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, hk, c, hc⟩ := hN n hn
    exact ⟨k, hk, c.toFeedbackCode, (c.avgError_toFeedbackCode W pS).trans_le hc⟩
  · rw [← DMC.closure_achievable_eq (bothChannel W pS)]
    refine closure_mono fun R hR => ⟨hR.1, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hR.2 ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, hk, c, hc⟩ := hN n hn
    exact ⟨k, hk, BothCode.ofBlockCode c,
      ((BothCode.ofBlockCode c).avgError_toFeedbackCode W pS).symm.trans_le hc⟩

end StateIid

end Meat
