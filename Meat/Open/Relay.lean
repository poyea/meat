import Meat.Channel.BroadcastAchievability
import Meat.Channel.CodingTheorem
import Meat.Shannon.Conditional

open MeasureTheory
open scoped ENNReal

namespace Meat

section Markov

variable {Ω S T U : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

private lemma sum_measureReal_inter (hX : Measurable X) (s : Set Ω) :
    ∑ x, μ.real {ω | X ω = x ∧ ω ∈ s} = μ.real s := by
  have h := sum_measureReal_preimage_singleton (μ := μ.restrict s) Finset.univ (f := X)
    fun x _ => hX (measurableSet_singleton x)
  simp only [Finset.coe_univ, Set.preimage_univ, measureReal_restrict_apply_univ] at h
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [measureReal_restrict_apply (hX (measurableSet_singleton x))]
  rfl

private lemma markovChain_of_factor (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (κ : T → U → ℝ)
    (h : ∀ x y z, μ.real {ω | X ω = x ∧ Y ω = y ∧ Z ω = z} =
      μ.real {ω | X ω = x ∧ Y ω = y} * κ y z) :
    MarkovChain X Y Z μ := by
  rw [markovChain_iff hX hY hZ]
  intro x y z
  have s1 : ∑ x', μ.real {ω | X ω = x' ∧ Y ω = y ∧ Z ω = z} = μ.real {ω | Y ω = y ∧ Z ω = z} :=
    sum_measureReal_inter hX _
  have s2 : ∑ x', μ.real {ω | X ω = x' ∧ Y ω = y} = μ.real {ω | Y ω = y} :=
    sum_measureReal_inter hX _
  have e1 : μ.real {ω | Y ω = y ∧ Z ω = z} = μ.real {ω | Y ω = y} * κ y z := by
    rw [← s1, ← s2, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x' _ => h x' y z
  rw [h, e1]
  ring

omit [IsProbabilityMeasure μ] in
private lemma condMutualInfo_pair {T' : Type*} [Fintype T'] [MeasurableSpace T']
    [MeasurableSingletonClass T'] {Y' : Ω → T'} :
    I[X : fun ω => (Y ω, Y' ω) | Z ; μ] =
      I[X : Y' | Z ; μ] + I[X : Y | fun ω => (Y' ω, Z ω) ; μ] := by
  have e1 : H[fun ω => ((X ω, Y' ω), Z ω) ; μ] = H[fun ω => (X ω, (Y' ω, Z ω)) ; μ] :=
    Eq.symm <| entropy_comp_of_injective μ (X := fun ω => ((X ω, Y' ω), Z ω))
      (f := fun p => (p.1.1, (p.1.2, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2
  have e2 : H[fun ω => ((Y ω, Y' ω), Z ω) ; μ] = H[fun ω => (Y ω, (Y' ω, Z ω)) ; μ] :=
    Eq.symm <| entropy_comp_of_injective μ (X := fun ω => ((Y ω, Y' ω), Z ω))
      (f := fun p => (p.1.1, (p.1.2, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2
  have e3 : H[fun ω => ((X ω, (Y ω, Y' ω)), Z ω) ; μ] =
      H[fun ω => ((X ω, Y ω), (Y' ω, Z ω)) ; μ] :=
    Eq.symm <| entropy_comp_of_injective μ (X := fun ω => ((X ω, (Y ω, Y' ω)), Z ω))
      (f := fun p => ((p.1.1, p.1.2.1), (p.1.2.2, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 (Prod.ext h.1.2 h.2.1)) h.2.2
  simp only [condMutualInfo_def, condEntropy_def]
  rw [e1, e2, e3]
  ring

private lemma condMutualInfo_le_pair {T' : Type*} [Fintype T'] [MeasurableSpace T']
    [MeasurableSingletonClass T'] {Y' : Ω → T'} (hX : Measurable X) (hY : Measurable Y)
    (hY' : Measurable Y') (hZ : Measurable Z) :
    I[X : Y' | Z ; μ] ≤ I[X : fun ω => (Y ω, Y' ω) | Z ; μ] := by
  rw [condMutualInfo_pair]
  linarith [condMutualInfo_nonneg μ hX hY (hY'.prodMk hZ)]

end Markov

structure RelayCode (M A A₁ B B₁ : Type*) (n : ℕ) where
  enc : M → Fin n → A
  relay : Fin n → (Fin n → B₁) → A₁
  causal : ∀ i y y', (∀ j, j < i → y j = y' j) → relay i y = relay i y'
  dec : (Fin n → B) → M

namespace RelayCode

variable {M A A₁ B B₁ : Type*} {n : ℕ}

noncomputable def seqProb (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁)) (m : M)
    (y : Fin n → B × B₁) : ℝ≥0∞ :=
  ∏ i, W (c.enc m i, c.relay i fun j => (y j).2) (y i)

noncomputable def errorProb [Fintype B] [Fintype B₁] [DecidableEq M]
    (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁)) (m : M) : ℝ≥0∞ :=
  ∑ y : Fin n → B × B₁, if c.dec (fun i => (y i).1) = m then 0 else c.seqProb W m y

noncomputable def avgError [Fintype B] [Fintype B₁] [Fintype M] [DecidableEq M]
    (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁)) : ℝ≥0∞ :=
  (∑ m, c.errorProb W m) / (Fintype.card M : ℝ≥0∞)

end RelayCode

namespace Relay

variable {A A₁ B B₁ : Type*}

def Achievable [Fintype B] [Fintype B₁] (W : DMC (A × A₁) (B × B₁)) (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : RelayCode (Fin k) A A₁ B B₁ n, c.avgError W ≤ ε

def achievableRates [Fintype B] [Fintype B₁] (W : DMC (A × A₁) (B × B₁)) : Set ℝ :=
  {R | 0 ≤ R ∧ Achievable W R}

def IsDegraded (W : DMC (A × A₁) (B × B₁)) : Prop :=
  ∃ K : DMC (A₁ × B₁) B, ∀ a y y₁, W a (y, y₁) = (W a).map Prod.snd y₁ * K (a.2, y₁) y

section Direct

noncomputable def directChannel (W : DMC (A × A₁) (B × B₁)) (x₁ : A₁) : DMC A B :=
  fun a => (W (a, x₁)).map Prod.fst

def directCode {M : Type*} {n : ℕ} (c : BlockCode M A B n) (x₁ : A₁) : RelayCode M A A₁ B B₁ n :=
  ⟨c.enc, fun _ _ => x₁, fun _ _ _ _ => rfl, c.dec⟩

theorem errorProb_directCode [Fintype B] [Fintype B₁] {M : Type*} [DecidableEq M] {n : ℕ}
    (c : BlockCode M A B n) (W : DMC (A × A₁) (B × B₁)) (x₁ : A₁) (m : M) :
    (directCode c x₁).errorProb W m = c.errorProb (directChannel W x₁) m := by
  have h := DMC.sum_blockProb_mul_comp (fun a => W (a, x₁)) Prod.fst (c.enc m)
    fun y => if c.dec y = m then (0 : ℝ) else 1
  simp only [mul_ite, mul_zero, mul_one] at h
  rw [RelayCode.errorProb, BlockCode.errorProb,
    ← ENNReal.toReal_eq_toReal_iff' (ENNReal.sum_ne_top.2
      fun y _ => by split_ifs <;> simp [RelayCode.seqProb, ENNReal.prod_ne_top, PMF.apply_ne_top])
    (ENNReal.sum_ne_top.2 fun y _ => by split_ifs <;> simp [DMC.blockProb_ne_top]),
    ENNReal.toReal_sum fun y _ => by
      split_ifs <;> simp [RelayCode.seqProb, ENNReal.prod_ne_top, PMF.apply_ne_top],
    ENNReal.toReal_sum fun y _ => by split_ifs <;> simp [DMC.blockProb_ne_top]]
  convert h using 2 with y _ y _
  · simp only [directCode]
    by_cases hy : c.dec (fun i => (y i).1) = m <;>
      simp [hy, RelayCode.seqProb, DMC.blockProb, ENNReal.toReal_prod]
  · split_ifs <;> rfl

theorem achievable_of_directChannel [Fintype B] [Fintype B₁] (W : DMC (A × A₁) (B × B₁))
    (x₁ : A₁) {R : ℝ} (h : (directChannel W x₁).Achievable R) : Achievable W R := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hn
  refine ⟨k, hk, directCode c x₁, ?_⟩
  simpa [RelayCode.avgError, BlockCode.avgError, errorProb_directCode] using hc

theorem Icc_capacity_directChannel_subset [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [Fintype B₁] (W : DMC (A × A₁) (B × B₁)) (x₁ : A₁) :
    Set.Icc 0 (directChannel W x₁).capacity ⊆ closure (achievableRates W) := by
  rw [← DMC.closure_achievable_eq]
  exact closure_mono fun R hR => ⟨hR.1, achievable_of_directChannel W x₁ hR.2⟩

end Direct

section Rates

variable [Fintype A] [MeasurableSpace A] [Fintype A₁] [MeasurableSpace A₁]
  [Fintype B] [MeasurableSpace B] [Fintype B₁] [MeasurableSpace B₁]

noncomputable def cutSetRate (W : DMC (A × A₁) (B × B₁)) (p : PMF (A × A₁)) : ℝ :=
  min (I[fun ω : (A × A₁) × B × B₁ => ω.1 : fun ω => ω.2.1 ; W.jointMeasure p])
    (I[fun ω : (A × A₁) × B × B₁ => ω.1.1 : fun ω => ω.2 | fun ω => ω.1.2 ; W.jointMeasure p])

noncomputable def decodeForwardRate (W : DMC (A × A₁) (B × B₁)) (p : PMF (A × A₁)) : ℝ :=
  min (I[fun ω : (A × A₁) × B × B₁ => ω.1 : fun ω => ω.2.1 ; W.jointMeasure p])
    (I[fun ω : (A × A₁) × B × B₁ => ω.1.1 : fun ω => ω.2.2 | fun ω => ω.1.2 ; W.jointMeasure p])

noncomputable def cutSetBound (W : DMC (A × A₁) (B × B₁)) : ℝ :=
  ⨆ p : PMF (A × A₁), cutSetRate W p

noncomputable def decodeForwardBound (W : DMC (A × A₁) (B × B₁)) : ℝ :=
  ⨆ p : PMF (A × A₁), decodeForwardRate W p

def CutSetTight (W : DMC (A × A₁) (B × B₁)) : Prop :=
  closure (achievableRates W) = Set.Icc 0 (cutSetBound W)

end Rates

theorem jointPMF_map_relayOutput (W : DMC (A × A₁) (B × B₁)) (p : PMF (A × A₁)) :
    (DMC.jointPMF W p).map (fun ω => (ω.1, ω.2.2)) =
      DMC.jointPMF (fun a => (W a).map Prod.snd) p := by
  simp only [DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]

section Bounds

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]

theorem decodeForwardRate_le_cutSetRate (W : DMC (A × A₁) (B × B₁)) (p : PMF (A × A₁)) :
    decodeForwardRate W p ≤ cutSetRate W p :=
  min_le_min le_rfl (condMutualInfo_le_pair (Y := fun ω : (A × A₁) × B × B₁ => ω.2.1)
    (Y' := fun ω => ω.2.2) (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _))

theorem cutSetRate_le_log_card (W : DMC (A × A₁) (B × B₁)) (p : PMF (A × A₁)) :
    cutSetRate W p ≤ Real.log (Fintype.card B) := by
  refine (min_le_left _ _).trans ?_
  have h1 := condEntropy_nonneg (W.jointMeasure p) (X := fun ω : (A × A₁) × B × B₁ => ω.2.1)
    (Y := fun ω => ω.1) (measurable_of_finite _) (measurable_of_finite _)
  have h2 := entropy_le_log_card (W.jointMeasure p) (X := fun ω : (A × A₁) × B × B₁ => ω.2.1)
  rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
  linarith

theorem decodeForwardBound_le_cutSetBound (W : DMC (A × A₁) (B × B₁)) :
    decodeForwardBound W ≤ cutSetBound W :=
  ciSup_mono ⟨_, Set.forall_mem_range.2 (cutSetRate_le_log_card W)⟩
    (decodeForwardRate_le_cutSetRate W)

theorem markovChain_of_isDegraded {W : DMC (A × A₁) (B × B₁)} (h : IsDegraded W)
    (p : PMF (A × A₁)) :
    MarkovChain (fun ω : (A × A₁) × B × B₁ => ω.1.1) (fun ω => (ω.2.2, ω.1.2))
      (fun ω => ω.2.1) (W.jointMeasure p) := by
  classical
  obtain ⟨K, hK⟩ := h
  refine markovChain_of_factor (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _) (fun t y => (K (t.2, t.1) y).toReal) fun x t y => ?_
  have s1 : {ω : (A × A₁) × B × B₁ | ω.1.1 = x ∧ (ω.2.2, ω.1.2) = t ∧ ω.2.1 = y} =
      {((x, t.2), (y, t.1))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.ext_iff]
    tauto
  have s2 : {ω : (A × A₁) × B × B₁ | ω.1.1 = x ∧ (ω.2.2, ω.1.2) = t} =
      (fun ω : (A × A₁) × B × B₁ => (ω.1, ω.2.2)) ⁻¹' {((x, t.2), t.1)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff]
    tauto
  rw [s1, s2, ← map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _),
    DMC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _),
    jointPMF_map_relayOutput, measureReal_def, measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), DMC.jointPMF_apply,
    DMC.jointPMF_apply, hK, ← ENNReal.toReal_mul, mul_assoc]

theorem cutSetRate_eq_decodeForwardRate {W : DMC (A × A₁) (B × B₁)} (h : IsDegraded W)
    (p : PMF (A × A₁)) : cutSetRate W p = decodeForwardRate W p := by
  have hm := markovChain_of_isDegraded h p
  rw [markovChain_def] at hm
  have e := condMutualInfo_pair (μ := W.jointMeasure p) (X := fun ω : (A × A₁) × B × B₁ => ω.1.1)
    (Y := fun ω => ω.2.1) (Y' := fun ω => ω.2.2) (Z := fun ω => ω.1.2)
  rw [hm, add_zero] at e
  rw [cutSetRate, decodeForwardRate, ← e]

theorem cutSetBound_eq_decodeForwardBound {W : DMC (A × A₁) (B × B₁)} (h : IsDegraded W) :
    cutSetBound W = decodeForwardBound W := by
  simp only [cutSetBound, decodeForwardBound, cutSetRate_eq_decodeForwardRate h]

end Bounds

noncomputable def lawEntropy {k a a₁ b b₁ : ℕ} (S : Finset (Fin 5))
    (q : PMF (Fin k × (Fin a × Fin a₁) × Fin b × Fin b₁)) : ℝ :=
  H[fun ω (i : Fin 5) => if i ∈ S then
      Fin.ofNat (k + a + a₁ + b + b₁ + 1)
        ((![(ω.1 : ℕ), ω.2.1.1, ω.2.1.2, ω.2.2.1, ω.2.2.2] : Fin 5 → ℕ) i)
    else 0 ; q.toMeasure]

def IsLaw {k a a₁ b b₁ : ℕ} (W : DMC (Fin a × Fin a₁) (Fin b × Fin b₁))
    (q : PMF (Fin k × (Fin a × Fin a₁) × Fin b × Fin b₁)) : Prop :=
  q.map (fun ω => ω.2) = DMC.jointPMF W (q.map fun ω => ω.2.1)

def SingleLetterCapacity : Prop :=
  ∃ (K : ℕ → ℕ → ℕ → ℕ → ℕ) (J J' : ℕ) (c : Fin J → Finset (Fin 5) → ℤ)
    (d : Fin J' → Finset (Fin 5) → ℤ),
    ∀ (a a₁ b b₁ : ℕ) (W : DMC (Fin (a + 1) × Fin (a₁ + 1)) (Fin (b + 1) × Fin (b₁ + 1))),
      closure (achievableRates W) = Set.Icc 0
        (⨆ q : {q : PMF (Fin (K a a₁ b b₁) × (Fin (a + 1) × Fin (a₁ + 1)) × Fin (b + 1) ×
            Fin (b₁ + 1)) // IsLaw W q ∧ ∀ j, ∑ S, (d j S : ℝ) * lawEntropy S q = 0},
          ⨅ j, ∑ S, (c j S : ℝ) * lawEntropy S q.1)

end Relay

end Meat
