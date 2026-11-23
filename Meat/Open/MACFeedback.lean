import Meat.Channel.MultipleAccessTheorem
import Meat.Open.EntropicFormula
import Meat.Open.Interactive

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

structure FeedbackMACCode (M₁ M₂ A₁ A₂ B : Type*) (n : ℕ) where
  enc₁ : M₁ → (i : Fin n) → (Fin i → B) → A₁
  enc₂ : M₂ → (i : Fin n) → (Fin i → B) → A₂
  dec : (Fin n → B) → M₁ × M₂

namespace FeedbackMACCode

variable {M₁ M₂ A₁ A₂ B : Type*} {n : ℕ}

def past (y : Fin n → B) (i : Fin n) : Fin i → B :=
  fun j => y ⟨j, j.2.trans i.2⟩

def input (c : FeedbackMACCode M₁ M₂ A₁ A₂ B n) (m : M₁ × M₂) (y : Fin n → B) (i : Fin n) :
    A₁ × A₂ :=
  (c.enc₁ m.1 i (past y i), c.enc₂ m.2 i (past y i))

noncomputable def outputProb (c : FeedbackMACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B)
    (m : M₁ × M₂) (y : Fin n → B) : ℝ≥0∞ :=
  ∏ i, W (c.input m y i) (y i)

noncomputable def errorProb [Fintype B] [DecidableEq M₁] [DecidableEq M₂]
    (c : FeedbackMACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) (m : M₁ × M₂) : ℝ≥0∞ :=
  ∑ y : Fin n → B, if c.dec y = m then 0 else c.outputProb W m y

noncomputable def avgError [Fintype B] [Fintype M₁] [Fintype M₂] [DecidableEq M₁]
    [DecidableEq M₂] (c : FeedbackMACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) : ℝ≥0∞ :=
  (∑ m : M₁ × M₂, c.errorProb W m) / ((Fintype.card M₁ : ℝ≥0∞) * (Fintype.card M₂ : ℝ≥0∞))

def ofMACCode (c : MACCode M₁ M₂ A₁ A₂ B n) : FeedbackMACCode M₁ M₂ A₁ A₂ B n :=
  ⟨fun m i _ => c.enc₁ m i, fun m i _ => c.enc₂ m i, c.dec⟩

theorem errorProb_ofMACCode [Fintype B] [DecidableEq M₁] [DecidableEq M₂]
    (c : MACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) (m : M₁ × M₂) :
    (ofMACCode c).errorProb W m = c.errorProb W m := rfl

theorem avgError_ofMACCode [Fintype B] [Fintype M₁] [Fintype M₂] [DecidableEq M₁]
    [DecidableEq M₂] (c : MACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) :
    (ofMACCode c).avgError W = c.avgError W := rfl

end FeedbackMACCode

namespace FeedbackMAC

variable {A₁ A₂ B : Type*}

def Achievable [Fintype B] (W : DMC (A₁ × A₂) B) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k₁ k₂ : ℕ, Real.exp (n * R₁) ≤ k₁ ∧ Real.exp (n * R₂) ≤ k₂ ∧
      ∃ c : FeedbackMACCode (Fin k₁) (Fin k₂) A₁ A₂ B n, c.avgError W ≤ ε

def achievableRegion [Fintype B] (W : DMC (A₁ × A₂) B) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ Achievable W R.1 R.2}

def SingleLetterCapacity : Prop :=
  ∃ (m : ℕ) (κ : ℕ → ℕ → ℕ → ℕ) (F : EntropicFormula m 3),
    ∀ (A₁ A₂ B : Type) [Fintype A₁] [Fintype A₂] [Fintype B] [Nonempty A₁] [Nonempty A₂]
      (W : DMC (A₁ × A₂) B),
      closure (achievableRegion W) =
        F.value (EntropicFormula.letterLaw₃ (m := m)
          (k := κ (Fintype.card A₁) (Fintype.card A₂) (Fintype.card B)) W)

theorem Achievable.of_MAC [Fintype B] {W : DMC (A₁ × A₂) B} {R₁ R₂ : ℝ}
    (h : MAC.Achievable W R₁ R₂) : Achievable W R₁ R₂ := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hn
  exact ⟨k₁, k₂, hk₁, hk₂, FeedbackMACCode.ofMACCode c, hc⟩

theorem achievableRegion_MAC_subset [Fintype B] (W : DMC (A₁ × A₂) B) :
    MAC.achievableRegion W ⊆ achievableRegion W :=
  fun _ ⟨h1, h2, h⟩ => ⟨h1, h2, Achievable.of_MAC h⟩

variable [Fintype A₁] [MeasurableSpace A₁] [Fintype A₂] [MeasurableSpace A₂]
  [Fintype B] [MeasurableSpace B]

theorem capacityRegion_subset_closure_achievableRegion [MeasurableSingletonClass A₁]
    [MeasurableSingletonClass A₂] [MeasurableSingletonClass B] (W : DMC (A₁ × A₂) B) :
    MAC.capacityRegion W ⊆ closure (achievableRegion W) :=
  (MAC.capacityRegion_subset_closure_achievableRegion W).trans
    (closure_mono (achievableRegion_MAC_subset W))

noncomputable def cutSetPentagon (W : DMC (A₁ × A₂) B) (p : PMF (A₁ × A₂)) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧
    R.1 ≤ I[fun ω : (A₁ × A₂) × B => ω.1.1 : fun ω => ω.2 | fun ω => ω.1.2 ; W.jointMeasure p] ∧
    R.2 ≤ I[fun ω : (A₁ × A₂) × B => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ; W.jointMeasure p] ∧
    R.1 + R.2 ≤ I[fun ω : (A₁ × A₂) × B => ω.1 : fun ω => ω.2 ; W.jointMeasure p]}

noncomputable def cutSetBound (W : DMC (A₁ × A₂) B) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ (⋃ p : PMF (A₁ × A₂), cutSetPentagon W p))

section CoverLeung

variable {V : Type*} [Fintype V] [MeasurableSpace V]

noncomputable def coverLeungMeasure (W : DMC (A₁ × A₂) B) (pU : PMF V) (p₁ : V → PMF A₁)
    (p₂ : V → PMF A₂) : Measure (V × A₁ × A₂ × B) :=
  (pU.bind fun u => (p₁ u).bind fun a₁ => (p₂ u).bind fun a₂ =>
    (W (a₁, a₂)).map fun b => (u, a₁, a₂, b)).toMeasure

noncomputable def coverLeungPentagon (W : DMC (A₁ × A₂) B) (pU : PMF V) (p₁ : V → PMF A₁)
    (p₂ : V → PMF A₂) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧
    R.1 ≤ I[fun ω : V × A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2.2 | fun ω => (ω.2.2.1, ω.1) ;
      coverLeungMeasure W pU p₁ p₂] ∧
    R.2 ≤ I[fun ω : V × A₁ × A₂ × B => ω.2.2.1 : fun ω => ω.2.2.2 | fun ω => (ω.2.1, ω.1) ;
      coverLeungMeasure W pU p₁ p₂] ∧
    R.1 + R.2 ≤ I[fun ω : V × A₁ × A₂ × B => (ω.2.1, ω.2.2.1) : fun ω => ω.2.2.2 ;
      coverLeungMeasure W pU p₁ p₂]}

end CoverLeung

noncomputable def coverLeungRegion (W : DMC (A₁ × A₂) B) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ (⋃ (k : ℕ) (pU : PMF (Fin k)) (p₁ : Fin k → PMF A₁)
    (p₂ : Fin k → PMF A₂), coverLeungPentagon W pU p₁ p₂))

variable [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B]

theorem pentagon_eq_cutSetPentagon (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    MAC.pentagon W p₁ p₂ = cutSetPentagon W (MAC.inputPMF p₁ p₂) := by
  have hμ : W.jointMeasure (MAC.inputPMF p₁ p₂) = (MAC.jointMeasure W p₁ p₂).map
      fun ω => ((ω.1, ω.2.1), ω.2.2) := by
    rw [DMC.jointMeasure_eq_toMeasure, MAC.jointPMF_inputPMF,
      ← PMF.toMeasure_map _ _ (measurable_of_finite _), MAC.jointMeasure_eq_toMeasure]
  have e₁ : I[fun ω : (A₁ × A₂) × B => ω.1.1 : fun ω => ω.2 | fun ω => ω.1.2 ;
      W.jointMeasure (MAC.inputPMF p₁ p₂)] =
      I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure W p₁ p₂] := by
    rw [hμ, condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  have e₂ : I[fun ω : (A₁ × A₂) × B => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
      W.jointMeasure (MAC.inputPMF p₁ p₂)] =
      I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
        MAC.jointMeasure W p₁ p₂] := by
    rw [hμ, condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  have e₃ : I[fun ω : (A₁ × A₂) × B => ω.1 : fun ω => ω.2 ;
      W.jointMeasure (MAC.inputPMF p₁ p₂)] =
      I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ; MAC.jointMeasure W p₁ p₂] := by
    rw [hμ, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
    rfl
  ext R
  simp only [MAC.pentagon, cutSetPentagon, Set.mem_ofPred_eq, e₁, e₂, e₃]

theorem capacityRegion_subset_cutSetBound (W : DMC (A₁ × A₂) B) :
    MAC.capacityRegion W ⊆ cutSetBound W :=
  closure_mono (convexHull_mono (Set.iUnion₂_subset fun p₁ p₂ => by
    rw [pentagon_eq_cutSetPentagon]
    exact Set.subset_iUnion (fun p => cutSetPentagon W p) (MAC.inputPMF p₁ p₂)))

end FeedbackMAC

namespace FeedbackMACCode

variable {M₁ M₂ A₁ A₂ B : Type*} {n : ℕ}

def toFn (c : FeedbackMACCode M₁ M₂ A₁ A₂ B n) : M₁ × M₂ → (i : Fin n) → (Fin i → B) → A₁ × A₂ :=
  fun m i q => (c.enc₁ m.1 i q, c.enc₂ m.2 i q)

theorem outputProb_eq (c : FeedbackMACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B)
    (m : M₁ × M₂) (y : Fin n → B) : c.outputProb W m y = Interactive.seqProb W (c.toFn m) y :=
  rfl

variable [Fintype M₁] [Nonempty M₁] [Fintype M₂] [Nonempty M₂] [DecidableEq M₁] [DecidableEq M₂]
  [MeasurableSpace M₁] [MeasurableSingletonClass M₁] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem measureReal_dec_ne (c : FeedbackMACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) :
    (Interactive.codeMeasure W c.toFn).real {ω | c.dec ω.2 ≠ ω.1} = (c.avgError W).toReal := by
  classical
  rw [measureReal_def, Interactive.codeMeasure_apply, avgError, Fintype.card_prod, Nat.cast_mul,
    div_eq_mul_inv, sum_mul]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [errorProb, sum_mul]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : c.dec y = m
  · simp [h]
  · simp only [h, ne_eq, not_false_eq_true, ite_true, ite_false]
    rw [mul_comm]
    rfl

end FeedbackMACCode

namespace FeedbackMAC

variable {A₁ A₂ B : Type*} [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

private lemma one_sub_le {l l' L : ℝ} (hl : l' ≤ l) (hL : 0 ≤ L) : (1 - l) * L ≤ (1 - l') * L :=
  mul_le_mul_of_nonneg_right (by linarith) hL

theorem condMutualInfo_eq_sub₁ (ν : Measure ((A₁ × A₂) × B)) :
    I[fun x : (A₁ × A₂) × B => x.1.1 : Prod.snd | fun x => x.1.2 ; ν] =
      H[Prod.snd | fun x : (A₁ × A₂) × B => x.1.2 ; ν] - H[Prod.snd | Prod.fst ; ν] :=
  condMutualInfo_eq_condEntropy_sub_condEntropy ν

theorem condMutualInfo_eq_sub₂ (ν : Measure ((A₁ × A₂) × B)) :
    I[fun x : (A₁ × A₂) × B => x.1.2 : Prod.snd | fun x => x.1.1 ; ν] =
      H[Prod.snd | fun x : (A₁ × A₂) × B => x.1.1 ; ν] - H[Prod.snd | Prod.fst ; ν] := by
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  exact condEntropy_cond_of_injective ν (Z := Prod.fst) (e := Prod.swap) Prod.swap_injective
    fun ω => rfl

theorem mutualInfo_eq_sub (ν : Measure ((A₁ × A₂) × B)) :
    I[Prod.fst : Prod.snd ; ν] = H[Prod.snd ; ν] - H[Prod.snd | Prod.fst ; ν] := by
  rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]

variable {M₁ M₂ : Type*} [Fintype M₁] [Nonempty M₁] [Fintype M₂] [Nonempty M₂] [DecidableEq M₁]
  [DecidableEq M₂] [MeasurableSpace M₁] [MeasurableSingletonClass M₁] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] {n : ℕ}

theorem one_sub_mul_log_card_le₁ (c : FeedbackMACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M₁) ≤
      ∑ i, I[fun x : (A₁ × A₂) × B => x.1.1 : Prod.snd | fun x => x.1.2 ;
        W.jointMeasure (Interactive.inputLaw W c.toFn i)] + Real.log 2 := by
  have h := Interactive.one_sub_mul_log_card_le_sum W c.toFn (Equiv.refl _) id Prod.snd
    (fun m₂ i q => c.enc₂ m₂ i q) (fun _ _ _ => rfl) (fun _ y => (c.dec y).1)
  have hm : (Interactive.codeMeasure W c.toFn).real
      {ω | (fun _ y => (c.dec y).1 : M₂ → (Fin n → B) → M₁) ((Equiv.refl _) ω.1).2 (id ∘ ω.2) ≠
        ((Equiv.refl (M₁ × M₂)) ω.1).1} ≤ (c.avgError W).toReal := by
    rw [← c.measureReal_dec_ne W]
    exact measureReal_mono fun ω hω h' => hω (show (c.dec ω.2).1 = ω.1.1 by rw [h'])
  refine (one_sub_le hm (Real.log_natCast_nonneg _)).trans (h.trans_eq ?_)
  congr 1
  exact sum_congr rfl fun i _ => (condMutualInfo_eq_sub₁ _).symm

theorem one_sub_mul_log_card_le₂ (c : FeedbackMACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M₂) ≤
      ∑ i, I[fun x : (A₁ × A₂) × B => x.1.2 : Prod.snd | fun x => x.1.1 ;
        W.jointMeasure (Interactive.inputLaw W c.toFn i)] + Real.log 2 := by
  have h := Interactive.one_sub_mul_log_card_le_sum W c.toFn (Equiv.prodComm _ _) id Prod.fst
    (fun m₁ i q => c.enc₁ m₁ i q) (fun _ _ _ => rfl) (fun _ y => (c.dec y).2)
  have hm : (Interactive.codeMeasure W c.toFn).real
      {ω | (fun _ y => (c.dec y).2 : M₁ → (Fin n → B) → M₂) ((Equiv.prodComm _ _) ω.1).2
        (id ∘ ω.2) ≠ ((Equiv.prodComm M₁ M₂) ω.1).1} ≤ (c.avgError W).toReal := by
    rw [← c.measureReal_dec_ne W]
    exact measureReal_mono fun ω hω h' => hω (show (c.dec ω.2).2 = ω.1.2 by rw [h'])
  refine (one_sub_le hm (Real.log_natCast_nonneg _)).trans (h.trans_eq ?_)
  congr 1
  exact sum_congr rfl fun i _ => (condMutualInfo_eq_sub₂ _).symm

theorem one_sub_mul_log_card_le₃ (c : FeedbackMACCode M₁ M₂ A₁ A₂ B n) (W : DMC (A₁ × A₂) B) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M₁ * Fintype.card M₂) ≤
      ∑ i, I[Prod.fst : Prod.snd ; W.jointMeasure (Interactive.inputLaw W c.toFn i)] +
        Real.log 2 := by
  have h := Interactive.one_sub_mul_log_card_le_sum_mutualInfo W c.toFn c.dec
  rw [c.measureReal_dec_ne W, Fintype.card_prod, Nat.cast_mul] at h
  refine h.trans_eq ?_
  congr 1
  exact sum_congr rfl fun i _ => (mutualInfo_eq_sub _).symm

omit [Nonempty M₁] [Nonempty M₂] [DecidableEq M₁] [DecidableEq M₂] [MeasurableSpace M₁]
  [MeasurableSingletonClass M₁] [MeasurableSpace M₂] [MeasurableSingletonClass M₂] in
theorem sum_le_mul_avg (W : DMC (A₁ × A₂) B) [NeZero n] (p : Fin n → PMF (A₁ × A₂))
    {G : Type*} [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
    {D : Measure ((A₁ × A₂) × B) → ℝ} {g : (A₁ × A₂) × B → G}
    (hD : ∀ r : PMF (A₁ × A₂),
      D (W.jointMeasure r) = H[Prod.snd | g ; W.jointMeasure r] -
        H[Prod.snd | Prod.fst ; W.jointMeasure r]) :
    ∑ i, D (W.jointMeasure (p i)) ≤ n * D (W.jointMeasure ((Interactive.uniformPMF n).bind p)) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hc := Interactive.sum_condEntropy_le (fun i => DMC.jointPMF W (p i)) Prod.snd g
  have hl := Interactive.condEntropy_jointMeasure_avg W p
  rw [← Interactive.jointPMF_bind] at hc
  simp only [hD, sum_sub_distrib]
  change (n : ℝ)⁻¹ * ∑ i, H[Prod.snd | g ; W.jointMeasure (p i)] ≤ _ at hc
  have e1 : ∑ i, H[Prod.snd | g ; W.jointMeasure (p i)] ≤
      n * H[Prod.snd | g ; W.jointMeasure ((Interactive.uniformPMF n).bind p)] := by
    rw [inv_mul_le_iff₀ hn] at hc
    exact hc
  have e2 : ∑ i, H[Prod.snd | Prod.fst ; W.jointMeasure (p i)] =
      n * H[Prod.snd | Prod.fst ; W.jointMeasure ((Interactive.uniformPMF n).bind p)] := by
    rw [← hl, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  linarith

private lemma dist_max_le {r ε l : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε) (hl : 0 ≤ l) :
    dist r (max ((1 - ε) * r - l) 0) ≤ ε * r + l := by
  rw [Real.dist_eq]
  rcases le_total ((1 - ε) * r - l) 0 with h | h
  · rw [max_eq_right h, sub_zero, abs_of_nonneg hr]
    linarith
  · rw [max_eq_left h, abs_of_nonneg (by nlinarith)]
    linarith

private lemma rate_bound {n R ε l L S : ℝ} (hn : 0 < n) (hR : 0 ≤ R) (hl : l ≤ ε)
    (hε : ε ≤ 1 / 2) (hL : n * R ≤ L) (hB : (1 - l) * L ≤ S + Real.log 2) :
    n * ((1 - ε) * R - Real.log 2 / n) ≤ S := by
  have e : n * ((1 - ε) * R - Real.log 2 / n) = (1 - ε) * (n * R) - Real.log 2 := by
    field_simp
  have h1 : (1 - ε) * (n * R) ≤ (1 - l) * L :=
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hL (by linarith))
  linarith

private lemma sum_rate_bound {n R R' ε l L L' S : ℝ} (hn : 0 < n) (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (hl : l ≤ ε) (hε : ε ≤ 1 / 2) (hL : n * R ≤ L) (hL' : n * R' ≤ L')
    (hB : (1 - l) * (L + L') ≤ S + Real.log 2) :
    n * ((1 - ε) * R - Real.log 2 / n + ((1 - ε) * R' - Real.log 2 / n)) ≤ S := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h := rate_bound (R := R + R') hn (by linarith) hl hε (by linarith) hB
  have e : n * ((1 - ε) * R - Real.log 2 / n + ((1 - ε) * R' - Real.log 2 / n)) =
      n * ((1 - ε) * (R + R') - Real.log 2 / n) - Real.log 2 := by
    field_simp
    ring
  linarith

theorem mem_cutSetBound_of_mem_achievableRegion (W : DMC (A₁ × A₂) B) {R : ℝ × ℝ}
    (hR : R ∈ achievableRegion W) : R ∈ cutSetBound W := by
  classical
  obtain ⟨hR1, hR2, hA⟩ := hR
  refine closure_mono (subset_convexHull ℝ _) ?_
  rw [Metric.mem_closure_iff]
  intro η hη
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ε * (R.1 + R.2 + 1) ≤ η / 2 := by
    refine ⟨min (1 / 2) (η / (2 * (R.1 + R.2 + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, ?_⟩
    calc min (1 / 2) (η / (2 * (R.1 + R.2 + 1))) * (R.1 + R.2 + 1)
        ≤ η / (2 * (R.1 + R.2 + 1)) * (R.1 + R.2 + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = η / 2 := by field_simp
  obtain ⟨N, hN⟩ := hA (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε0)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * Real.log 2 / η)
  obtain ⟨n, hnN, hn0, hn1⟩ : ∃ n : ℕ, N ≤ n ∧ n₀ ≤ n ∧ 1 ≤ n :=
    ⟨max (max N n₀) 1, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
  have : NeZero n := ⟨by omega⟩
  have hlogn : Real.log 2 / n < η / 2 := by
    have h1 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn0
    have h2 : 2 * Real.log 2 < η * n := by
      have := (div_lt_iff₀ hη).1 (hn₀.trans_le h1)
      linarith
    rw [div_lt_iff₀ hnpos]
    linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hnN
  have hk₁0 : (0 : ℝ) < k₁ := (Real.exp_pos _).trans_le hk₁
  have hk₂0 : (0 : ℝ) < k₂ := (Real.exp_pos _).trans_le hk₂
  have : Nonempty (Fin k₁) := ⟨⟨0, Nat.cast_pos.1 hk₁0⟩⟩
  have : Nonempty (Fin k₂) := ⟨⟨0, Nat.cast_pos.1 hk₂0⟩⟩
  have hlam : (c.avgError W).toReal ≤ ε := ENNReal.toReal_le_of_le_ofReal hε0.le hc
  set p := Interactive.inputLaw W c.toFn
  set ν := W.jointMeasure ((Interactive.uniformPMF n).bind p)
  have A1 := sum_le_mul_avg W p (D := fun ν =>
      I[fun x : (A₁ × A₂) × B => x.1.1 : Prod.snd | fun x => x.1.2 ; ν])
    (g := fun x => x.1.2) fun r => condMutualInfo_eq_sub₁ _
  have A2 := sum_le_mul_avg W p (D := fun ν =>
      I[fun x : (A₁ × A₂) × B => x.1.2 : Prod.snd | fun x => x.1.1 ; ν])
    (g := fun x => x.1.1) fun r => condMutualInfo_eq_sub₂ _
  have A3 := sum_le_mul_avg W p (D := fun ν => I[Prod.fst : Prod.snd ; ν])
    (g := fun _ => ()) fun r => by
      rw [mutualInfo_eq_sub, DMC.jointMeasure_eq_toMeasure, Interactive.condEntropy_const]
  beta_reduce at A1 A2 A3
  have B1 := FeedbackMAC.one_sub_mul_log_card_le₁ c W
  have B2 := FeedbackMAC.one_sub_mul_log_card_le₂ c W
  have B3 := FeedbackMAC.one_sub_mul_log_card_le₃ c W
  rw [Fintype.card_fin] at B1 B2
  rw [Fintype.card_fin, Fintype.card_fin, Real.log_mul hk₁0.ne' hk₂0.ne'] at B3
  have hl₁ : n * R.1 ≤ Real.log k₁ := (Real.le_log_iff_exp_le hk₁0).2 hk₁
  have hl₂ : n * R.2 ≤ Real.log k₂ := (Real.le_log_iff_exp_le hk₂0).2 hk₂
  set I₁ := I[fun x : (A₁ × A₂) × B => x.1.1 : Prod.snd | fun x => x.1.2 ; ν]
  set I₂ := I[fun x : (A₁ × A₂) × B => x.1.2 : Prod.snd | fun x => x.1.1 ; ν]
  set I₃ := I[Prod.fst : Prod.snd ; ν]
  have hx₀ := rate_bound (S := n * I₁) hnpos hR1 hlam hε1 hl₁ (by linarith [A1])
  have hy₀ := rate_bound (S := n * I₂) hnpos hR2 hlam hε1 hl₂ (by linarith [A2])
  have hxy₀ := sum_rate_bound (S := n * I₃) hnpos hR1 hR2 hlam hε1 hl₁ hl₂ (by linarith [A3])
  have hI₁ : 0 ≤ I₁ := condMutualInfo_nonneg ν (measurable_of_finite _) measurable_snd
    (measurable_of_finite _)
  have hI₂ : 0 ≤ I₂ := condMutualInfo_nonneg ν (measurable_of_finite _) measurable_snd
    (measurable_of_finite _)
  have hI₃₁ : I₁ ≤ I₃ := by
    have h := mutualInfo_pair_eq_add_condMutualInfo ν (X := Prod.snd)
      (Y := fun x : (A₁ × A₂) × B => x.1.1) (Z := fun x => x.1.2)
    have h0 := mutualInfo_nonneg ν (X := Prod.snd) (Y := fun x : (A₁ × A₂) × B => x.1.2)
      measurable_snd (measurable_of_finite _)
    have e1 : I₃ = I[Prod.snd : fun x : (A₁ × A₂) × B => (x.1.1, x.1.2) ; ν] :=
      mutualInfo_comm ν
    have e2 : I₁ = I[Prod.snd : fun x : (A₁ × A₂) × B => x.1.1 | fun x => x.1.2 ; ν] :=
      condMutualInfo_comm ν
    linarith
  have hI₃₂ : I₂ ≤ I₃ := by
    have h := mutualInfo_pair_eq_add_condMutualInfo ν (X := Prod.snd)
      (Y := fun x : (A₁ × A₂) × B => x.1.2) (Z := fun x => x.1.1)
    have h0 := mutualInfo_nonneg ν (X := Prod.snd) (Y := fun x : (A₁ × A₂) × B => x.1.1)
      measurable_snd (measurable_of_finite _)
    have e1 : I₃ = I[Prod.snd : fun x : (A₁ × A₂) × B => (x.1.2, x.1.1) ; ν] := by
      refine (mutualInfo_comm ν).trans ?_
      exact (mutualInfo_comp_right_of_injective ν (X := Prod.snd) (Y := Prod.fst)
        Prod.swap_injective).symm
    have e2 : I₂ = I[Prod.snd : fun x : (A₁ × A₂) × B => x.1.2 | fun x => x.1.1 ; ν] :=
      condMutualInfo_comm ν
    linarith
  set x₀ := (1 - ε) * R.1 - Real.log 2 / n
  set y₀ := (1 - ε) * R.2 - Real.log 2 / n
  have hx : max x₀ 0 ≤ I₁ := max_le (le_of_mul_le_mul_left (by linarith) hnpos) hI₁
  have hy : max y₀ 0 ≤ I₂ := max_le (le_of_mul_le_mul_left (by linarith) hnpos) hI₂
  have hxy : max x₀ 0 + max y₀ 0 ≤ I₃ := by
    have h3 : x₀ + y₀ ≤ I₃ := le_of_mul_le_mul_left (by linarith) hnpos
    have h1 : x₀ ≤ I₁ := le_of_mul_le_mul_left (by linarith) hnpos
    have h2 : y₀ ≤ I₂ := le_of_mul_le_mul_left (by linarith) hnpos
    rcases le_total x₀ 0 with a | a <;> rcases le_total y₀ 0 with b | b <;>
      simp only [max_eq_right, max_eq_left, a, b] <;> linarith
  refine ⟨(max x₀ 0, max y₀ 0), Set.mem_iUnion.2 ⟨(Interactive.uniformPMF n).bind p,
    le_max_right _ _, le_max_right _ _, hx, hy, hxy⟩, ?_⟩
  have hl0 : 0 ≤ Real.log 2 / n := div_nonneg hlog2 hnpos.le
  have d1 := dist_max_le hR1 hε0.le hl0
  have d2 := dist_max_le hR2 hε0.le hl0
  have e1 : ε * R.1 ≤ ε * (R.1 + R.2 + 1) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
  have e2 : ε * R.2 ≤ ε * (R.1 + R.2 + 1) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨d1.trans_lt (by linarith), d2.trans_lt (by linarith)⟩

theorem closure_achievableRegion_subset_cutSetBound (W : DMC (A₁ × A₂) B) :
    closure (achievableRegion W) ⊆ cutSetBound W :=
  closure_minimal (fun _ hR => mem_cutSetBound_of_mem_achievableRegion W hR) isClosed_closure

end FeedbackMAC

end Meat
