import Meat.Channel.Converse
import Meat.Shannon.ChainRule

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

namespace Interactive

variable {A B : Type*}

noncomputable def seqProb {n : ℕ} (W : DMC A B) (φ : (i : Fin n) → (Fin i → B) → A)
    (y : Fin n → B) : ℝ≥0∞ :=
  ∏ i, W (φ i (seqPrefix y i)) (y i)

def restrict {n : ℕ} (φ : (i : Fin n) → (Fin i → B) → A) (i : Fin n) :
    (j : Fin i) → (Fin j → B) → A :=
  fun j q => φ ⟨j, j.2.trans i.2⟩ q

def tail {n : ℕ} (φ : (i : Fin (n + 1)) → (Fin i → B) → A) (b : B) :
    (i : Fin n) → (Fin i → B) → A :=
  fun i q => φ i.succ (Fin.cons b q)

def emptyPrefix {n : ℕ} : Fin ((0 : Fin (n + 1)) : ℕ) → B :=
  fun k => absurd k.2 (Nat.not_lt_zero _)

theorem seqPrefix_cons {n : ℕ} (b : B) (z : Fin n → B) (i : Fin n) :
    seqPrefix (Fin.cons b z : Fin (n + 1) → B) i.succ = Fin.cons b (seqPrefix z i) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · rfl

theorem seqProb_cons {n : ℕ} (W : DMC A B) (φ : (i : Fin (n + 1)) → (Fin i → B) → A) (b : B)
    (z : Fin n → B) :
    seqProb W φ (Fin.cons b z) = W (φ 0 emptyPrefix) b * seqProb W (tail φ b) z := by
  rw [seqProb, Fin.prod_univ_succ]
  congr 1
  · exact congrArg (fun q => W (φ 0 q) b) (funext fun k => absurd k.2 (Nat.not_lt_zero _))
  · refine prod_congr rfl fun i _ => ?_
    rw [seqPrefix_cons]
    rfl

theorem sum_seqProb [Fintype B] {n : ℕ} (W : DMC A B) (φ : (i : Fin n) → (Fin i → B) → A) :
    ∑ y, seqProb W φ y = 1 := by
  induction n with
  | zero => simp [seqProb]
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ => B).sum_comp, Fintype.sum_prod_type]
    change ∑ x, ∑ y, seqProb W φ (Fin.cons x y) = 1
    simp only [seqProb_cons, ← mul_sum, ih, mul_one]
    have h := PMF.tsum_coe (W (φ 0 emptyPrefix))
    rwa [tsum_fintype] at h

theorem sum_mul_seqProb [Fintype B] {n : ℕ} (W : DMC A B) (φ : (i : Fin n) → (Fin i → B) → A)
    (i : Fin n) (F : (Fin i → B) → B → ℝ≥0∞) :
    ∑ y, F (seqPrefix y i) (y i) * seqProb W φ y =
      ∑ p : Fin i → B, ∑ b, F p b * (seqProb W (restrict φ i) p * W (φ i p) b) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ => B).sum_comp, Fintype.sum_prod_type]
    change ∑ b, ∑ z, F (seqPrefix (Fin.cons b z : Fin (n + 1) → B) i)
      ((Fin.cons b z : Fin (n + 1) → B) i) * seqProb W φ (Fin.cons b z) = _
    simp only [seqProb_cons]
    revert F
    refine Fin.cases (fun F => ?_) (fun i F => ?_) i
    · have h0 : ∀ q : Fin (0 : Fin (n + 1)) → B, q = emptyPrefix :=
        fun q => funext fun k => absurd k.2 (Nat.not_lt_zero _)
      have : Unique (Fin ((0 : Fin (n + 1)) : ℕ) → B) := ⟨⟨emptyPrefix⟩, h0⟩
      conv_rhs => rw [Fintype.sum_unique]
      refine sum_congr rfl fun b _ => ?_
      simp only [Fin.cons_zero, h0 (seqPrefix _ _), h0 default]
      have : IsEmpty (Fin ((0 : Fin (n + 1)) : ℕ)) := Fin.isEmpty'
      simp only [← mul_sum, sum_seqProb, mul_one]
      simp only [seqProb, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    · have hL : ∀ b, ∑ z, F (seqPrefix (Fin.cons b z : Fin (n + 1) → B) i.succ)
            ((Fin.cons b z : Fin (n + 1) → B) i.succ) *
            (W (φ 0 emptyPrefix) b * seqProb W (tail φ b) z) =
          W (φ 0 emptyPrefix) b * ∑ q : Fin i → B, ∑ c, F (Fin.cons b q) c *
            (seqProb W (restrict (tail φ b) i) q * W (tail φ b i q) c) := by
        intro b
        rw [← ih (tail φ b) i (fun q c => F (Fin.cons b q) c), mul_sum]
        refine sum_congr rfl fun z _ => ?_
        rw [seqPrefix_cons, Fin.cons_succ]
        ring
      rw [sum_congr rfl fun b _ => hL b]
      change _ = ∑ p : Fin ((i : ℕ) + 1) → B, ∑ c, F p c *
        (seqProb W (restrict φ i.succ) p * W (φ i.succ p) c)
      rw [← (Fin.consEquiv fun _ : Fin ((i : ℕ) + 1) => B).sum_comp, Fintype.sum_prod_type]
      refine sum_congr rfl fun b _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun q _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun c _ => ?_
      change _ = F (Fin.cons b q) c * (seqProb W (restrict φ i.succ) (Fin.cons b q) *
        W (φ i.succ (Fin.cons b q)) c)
      rw [seqProb_cons]
      change W (φ 0 emptyPrefix) b * _ = F (Fin.cons b q) c * (W (φ 0 emptyPrefix) b *
        seqProb W (restrict (tail φ b) i) q * W (tail φ b i q) c)
      ring

section Kernel

variable {Ω T S U : Type*} [MeasurableSpace Ω]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [Fintype S] [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U] in
theorem measureReal_comp_eq_sum [DecidableEq U] {G : Ω → T} {Y : Ω → S} (hG : Measurable G)
    (hY : Measurable Y) (f : T → U) (u : U) (s : S) :
    μ.real {ω | f (G ω) = u ∧ Y ω = s} =
      ∑ g ∈ univ.filter (fun g => f g = u), μ.real {ω | G ω = g ∧ Y ω = s} := by
  classical
  rw [← measureReal_biUnion_finset]
  · congr 1
    ext ω
    simp
  · intro a _ b _ hab
    exact Set.disjoint_left.2 fun ω h1 h2 => hab (h1.1.symm.trans h2.1)
  · intro g _
    exact (hG (measurableSet_singleton g)).inter (hY (measurableSet_singleton s))

theorem condEntropy_eq_comp_of_kernel {G : Ω → T} {Y : Ω → S} (hG : Measurable G)
    (hY : Measurable Y) (f : T → U) (K : U → PMF S)
    (hK : ∀ g s, μ.real {ω | G ω = g ∧ Y ω = s} = μ.real {ω | G ω = g} * (K (f g) s).toReal) :
    H[Y | G ; μ] = H[Y | f ∘ G ; μ] := by
  classical
  have hfG : Measurable (f ∘ G) := (measurable_of_finite f).comp hG
  have hU : ∀ u s, μ.real {ω | f (G ω) = u ∧ Y ω = s} =
      μ.real {ω | f (G ω) = u} * (K u s).toReal := fun u s => by
    have h1 := measureReal_comp_eq_sum μ hG hY f u s
    have h2 := measureReal_comp_eq_sum μ hG (measurable_const (a := ())) f u ()
    simp only [and_true] at h2
    rw [h1, h2, sum_mul]
    refine sum_congr rfl fun g hg => ?_
    have hgu : f g = u := (mem_filter.1 hg).2
    rw [hK, hgu]
  have hm : MarkovChain G (f ∘ G) Y μ := by
    refine (markovChain_iff hG hfG hY).2 fun g u s => ?_
    by_cases hu : f g = u
    · subst hu
      have e1 : {ω | G ω = g ∧ (f ∘ G) ω = f g ∧ Y ω = s} = {ω | G ω = g ∧ Y ω = s} := by
        ext ω
        simp only [Function.comp, Set.mem_ofPred_eq]
        constructor
        · exact fun h => ⟨h.1, h.2.2⟩
        · exact fun h => ⟨h.1, by rw [h.1], h.2⟩
      have e2 : {ω | G ω = g ∧ (f ∘ G) ω = f g} = {ω | G ω = g} := by
        ext ω
        simp only [Function.comp, Set.mem_ofPred_eq]
        exact ⟨fun h => h.1, fun h => ⟨h, by rw [h]⟩⟩
      rw [e1, e2, hK]
      simp only [Function.comp]
      rw [hU]
      ring
    · have e1 : {ω | G ω = g ∧ (f ∘ G) ω = u ∧ Y ω = s} = ∅ := by
        ext ω
        simp only [Function.comp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hu (h.1 ▸ h.2.1)
      have e2 : {ω | G ω = g ∧ (f ∘ G) ω = u} = ∅ := by
        ext ω
        simp only [Function.comp, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hu (h.1 ▸ h.2)
      rw [e1, e2]
      simp
  have h1 := condMutualInfo_eq_condEntropy_sub_condEntropy μ (X := G) (Y := Y) (Z := f ∘ G)
  rw [markovChain_def.1 hm] at h1
  have h2 : H[Y | fun ω => (G ω, (f ∘ G) ω) ; μ] = H[Y | G ; μ] :=
    condEntropy_cond_of_injective μ (Z := G) (e := fun g => (g, f g))
      (fun a b h => congrArg Prod.fst h) fun ω => rfl
  linarith

end Kernel

section Mixture

variable {Z S T : Type*} [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {k : ℕ} [NeZero k]

theorem entropy_toMeasure (P : PMF Z) (X : Z → S) :
    H[X ; P.toMeasure] = ∑ s, Real.negMulLog ((P.map X s).toReal) := by
  rw [entropy_def]
  refine sum_congr rfl fun s _ => ?_
  rw [PMF.toMeasure_map _ _ (measurable_of_finite _), measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

omit [Finite Z] [MeasurableSingletonClass Z] in
theorem condEntropy_const (μ : Measure Z) [IsProbabilityMeasure μ] (X : Z → S) :
    H[X | fun _ => () ; μ] = H[X ; μ] := by
  have h1 : H[fun ω => (X ω, ()) ; μ] = H[X ; μ] :=
    entropy_comp_of_injective μ (X := X) (f := fun y => (y, ())) fun a b h => congrArg Prod.fst h
  have h2 : H[fun _ : Z => () ; μ] = 0 := by
    have := entropy_le_log_card μ (X := fun _ : Z => ())
    simp only [Fintype.card_unit, Nat.cast_one, Real.log_one] at this
    exact le_antisymm this (entropy_nonneg μ _)
  rw [condEntropy_def, h1, h2, sub_zero]

noncomputable def uniformPMF (k : ℕ) [NeZero k] : PMF (Fin k) :=
  PMF.ofFintype _ (sum_inv_card (Fin k))

noncomputable def mixture (P : Fin k → PMF Z) : PMF (Fin k × Z) :=
  (uniformPMF k).bind fun q => (P q).map fun z => (q, z)

omit [MeasurableSpace Z] [MeasurableSingletonClass Z] in
theorem mixture_apply (P : Fin k → PMF Z) (q : Fin k) (z : Z) :
    mixture P (q, z) = (k : ℝ≥0∞)⁻¹ * P q z := by
  classical
  have := Fintype.ofFinite Z
  rw [mixture, PMF.bind_apply, tsum_fintype, sum_eq_single q]
  · rw [uniformPMF, PMF.ofFintype_apply, Fintype.card_fin,
      PMF.map_apply_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
  · intro q' _ hq
    rw [PMF.map_apply, tsum_fintype]
    simp [Ne.symm hq]
  · simp

omit [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
theorem map_mixture (P : Fin k → PMF Z) (F : Z → S) :
    (mixture P).map (fun ω => (ω.1, F ω.2)) = mixture fun q => (P q).map F := by
  simp only [mixture, PMF.map_bind, PMF.map_comp]
  rfl

omit [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
theorem map_snd_mixture (P : Fin k → PMF Z) :
    (mixture P).map Prod.snd = (uniformPMF k).bind P := by
  simp only [mixture, PMF.map_bind, PMF.map_comp]
  congr 1
  funext q
  exact PMF.map_id (P q)

theorem entropy_mixture (P : Fin k → PMF Z) (F : Z → S) :
    H[fun ω : Fin k × Z => (ω.1, F ω.2) ; (mixture P).toMeasure] =
      Real.log k + (k : ℝ)⁻¹ * ∑ q, H[F ; (P q).toMeasure] := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne k))
  rw [entropy_toMeasure, map_mixture, Fintype.sum_prod_type]
  simp only [mixture_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Real.negMulLog_mul, sum_add_distrib, ← mul_sum, entropy_toMeasure]
  have hs : ∀ q, ∑ s, ((P q).map F s).toReal = 1 := fun q => by
    rw [← ENNReal.toReal_sum fun s _ => PMF.apply_ne_top _ s]
    have h := PMF.tsum_coe ((P q).map F)
    rw [tsum_fintype] at h
    rw [h, ENNReal.toReal_one]
  simp only [← sum_mul, hs, one_mul, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.negMulLog, Real.log_inv]
  field_simp

theorem condEntropy_mixture (P : Fin k → PMF Z) (f : Z → S) (g : Z → T) :
    H[fun ω : Fin k × Z => f ω.2 | fun ω => (ω.1, g ω.2) ; (mixture P).toMeasure] =
      (k : ℝ)⁻¹ * ∑ q, H[f | g ; (P q).toMeasure] := by
  have h1 : H[fun ω : Fin k × Z => (f ω.2, (ω.1, g ω.2)) ; (mixture P).toMeasure] =
      H[fun ω : Fin k × Z => (ω.1, (f ω.2, g ω.2)) ; (mixture P).toMeasure] :=
    entropy_comp_of_injective _ (X := fun ω : Fin k × Z => (ω.1, (f ω.2, g ω.2)))
      (f := fun p => (p.2.1, (p.1, p.2.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)
  rw [condEntropy_def, h1, entropy_mixture P (fun z => (f z, g z)), entropy_mixture P g]
  simp only [condEntropy_def, sum_sub_distrib]
  ring

theorem sum_condEntropy_le (P : Fin k → PMF Z) (f : Z → S) (g : Z → T) :
    (k : ℝ)⁻¹ * ∑ q, H[f | g ; (P q).toMeasure] ≤
      H[f | g ; ((uniformPMF k).bind P).toMeasure] := by
  rw [← condEntropy_mixture, ← map_snd_mixture, ← PMF.toMeasure_map _ _ measurable_snd,
    condEntropy_map _ measurable_snd (measurable_of_finite _) (measurable_of_finite _)]
  exact condEntropy_le_condEntropy_comp (measurable_of_finite _) (measurable_of_finite _)
    (fun p : Fin k × T => p.2)

theorem sum_entropy_le (P : Fin k → PMF Z) (f : Z → S) :
    (k : ℝ)⁻¹ * ∑ q, H[f ; (P q).toMeasure] ≤
      H[f ; ((uniformPMF k).bind P).toMeasure] := by
  have h := sum_condEntropy_le P f fun _ => ()
  simp only [condEntropy_const] at h
  exact h

end Mixture

section Average

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] {k : ℕ} [NeZero k]

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B]
  [MeasurableSpace B] [MeasurableSingletonClass B] in
theorem jointPMF_bind (W : DMC A B) (p : Fin k → PMF A) :
    DMC.jointPMF W ((uniformPMF k).bind p) =
      (uniformPMF k).bind fun q => DMC.jointPMF W (p q) := by
  simp only [DMC.jointPMF, PMF.bind_bind]

theorem condEntropy_jointMeasure_avg (W : DMC A B) (p : Fin k → PMF A) :
    (k : ℝ)⁻¹ * ∑ q, H[Prod.snd | Prod.fst ; W.jointMeasure (p q)] =
      H[Prod.snd | Prod.fst ; W.jointMeasure ((uniformPMF k).bind p)] := by
  have hr : ∀ (r : PMF A) (x : A × B), (W.jointMeasure r).real {x} = (r x.1 * W x.1 x.2).toReal :=
    fun r x => by
      rw [DMC.jointMeasure_eq_toMeasure, measureReal_def,
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), ← DMC.jointPMF_apply]
  have hb : ∀ a, ((uniformPMF k).bind p) a = ∑ q, (k : ℝ≥0∞)⁻¹ * p q a := fun a => by
    rw [PMF.bind_apply, tsum_fintype]
    simp only [uniformPMF, PMF.ofFintype_apply, Fintype.card_fin]
  have ht : ∀ x : A × B, (∑ i, (k : ℝ≥0∞)⁻¹ * p i x.1 * W x.1 x.2).toReal =
      ∑ i, (k : ℝ)⁻¹ * ((p i x.1).toReal * (W x.1 x.2).toReal) := fun x => by
    have hk0 : (k : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 (NeZero.ne k))
    rw [ENNReal.toReal_sum fun i _ => ENNReal.mul_ne_top (ENNReal.mul_ne_top hk0
      (PMF.apply_ne_top _ _)) (PMF.apply_ne_top _ _)]
    simp [ENNReal.toReal_mul, mul_assoc]
  simp only [DMC.condEntropy_snd_fst_jointMeasure, hr, hb, sum_mul, ht, ENNReal.toReal_mul]
  simp only [mul_sum, ← sum_neg_distrib]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun q _ => by ring

end Average

section Code

variable {M : Type*} [Fintype M] [Nonempty M] [Fintype B] {n : ℕ}

theorem sum_codeMass (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A) :
    ∑ ω : M × (Fin n → B), (Fintype.card M : ℝ≥0∞)⁻¹ * seqProb W (φ ω.1) ω.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [← mul_sum, sum_seqProb, mul_one]
  exact sum_inv_card M

noncomputable def codePMF (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A) :
    PMF (M × (Fin n → B)) :=
  PMF.ofFintype _ (sum_codeMass W φ)

theorem sum_codePMF_mul (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A) (i : Fin n)
    (F : M → (Fin i → B) → B → ℝ≥0∞) :
    ∑ ω, codePMF W φ ω * F ω.1 (seqPrefix ω.2 i) (ω.2 i) =
      ∑ m, (Fintype.card M : ℝ≥0∞)⁻¹ *
        ∑ p : Fin i → B, ∑ b, F m p b * (seqProb W (restrict (φ m) i) p * W (φ m i p) b) := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun m _ => ?_
  rw [← sum_mul_seqProb, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp only [codePMF, PMF.ofFintype_apply]
  ring

noncomputable def inputLaw (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A) (i : Fin n) :
    PMF A :=
  (codePMF W φ).map fun ω => φ ω.1 i (seqPrefix ω.2 i)

theorem map_codePMF_letter (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A) (i : Fin n) :
    (codePMF W φ).map (fun ω => (φ ω.1 i (seqPrefix ω.2 i), ω.2 i)) =
      DMC.jointPMF W (inputLaw W φ i) := by
  classical
  ext ⟨a, b⟩
  rw [DMC.jointPMF_apply, inputLaw, PMF.map_apply, PMF.map_apply, tsum_fintype, tsum_fintype]
  have h1 := sum_codePMF_mul W φ i fun m p c => if a = φ m i p ∧ b = c then 1 else 0
  have h2 := sum_codePMF_mul W φ i fun m p c => if a = φ m i p then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at h1 h2
  simp only [Prod.mk.injEq]
  rw [h1, h2, sum_mul]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_assoc, sum_mul]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  by_cases ha : a = φ m i p
  · subst ha
    simp only [true_and, ite_true]
    rw [sum_ite_eq]
    simp only [mem_univ, ite_true]
    have hs : ∑ c, W (φ m i p) c = 1 := by
      have h := PMF.tsum_coe (W (φ m i p))
      rwa [tsum_fintype] at h
    simp only [← mul_sum, hs, mul_one]
  · simp [ha]

variable [MeasurableSpace M] [MeasurableSingletonClass M] [MeasurableSpace B]
  [MeasurableSingletonClass B]

noncomputable def codeMeasure (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A) :
    Measure (M × (Fin n → B)) :=
  (codePMF W φ).toMeasure

instance isProbabilityMeasure_codeMeasure (W : DMC A B)
    (φ : M → (i : Fin n) → (Fin i → B) → A) : IsProbabilityMeasure (codeMeasure W φ) := by
  unfold codeMeasure
  infer_instance

theorem codeMeasure_apply (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A)
    (P : M × (Fin n → B) → Prop) [DecidablePred P] :
    codeMeasure W φ {ω | P ω} = ∑ m, ∑ y,
      if P (m, y) then (Fintype.card M : ℝ≥0∞)⁻¹ * seqProb W (φ m) y else 0 := by
  rw [codeMeasure, PMF.toMeasure_apply_fintype, Fintype.sum_prod_type]
  refine sum_congr rfl fun m _ => sum_congr rfl fun y _ => ?_
  by_cases h : P (m, y) <;> simp [Set.indicator, h, codePMF]

theorem codeMeasure_prefix (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A) (i : Fin n)
    (m : M) (p : Fin i → B) (s : Set B) [DecidablePred (· ∈ s)] :
    codeMeasure W φ {ω | ω.1 = m ∧ seqPrefix ω.2 i = p ∧ ω.2 i ∈ s} =
      (Fintype.card M : ℝ≥0∞)⁻¹ *
        (seqProb W (restrict (φ m) i) p * ∑ b, if b ∈ s then W (φ m i p) b else 0) := by
  classical
  rw [codeMeasure_apply, sum_eq_single m (fun m' _ hm => by simp [hm]) (by simp)]
  have h := sum_mul_seqProb W (φ m) i (fun q c => if q = p ∧ c ∈ s then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  simp only [true_and]
  rw [show (∑ y : Fin n → B, if seqPrefix y i = p ∧ y i ∈ s then
      (Fintype.card M : ℝ≥0∞)⁻¹ * seqProb W (φ m) y else 0) =
      (Fintype.card M : ℝ≥0∞)⁻¹ * ∑ y : Fin n → B, if seqPrefix y i = p ∧ y i ∈ s then
      seqProb W (φ m) y else 0 by
        rw [mul_sum]; exact sum_congr rfl fun y _ => by split_ifs <;> simp,
    h, sum_eq_single p (fun q _ hq => by simp [hq]) (by simp)]
  simp only [true_and, mul_sum, mul_ite, mul_zero]

theorem map_codeMeasure_letter [MeasurableSpace A]
    (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A) (i : Fin n) :
    (codeMeasure W φ).map (fun ω => (φ ω.1 i (seqPrefix ω.2 i), ω.2 i)) =
      W.jointMeasure (inputLaw W φ i) := by
  rw [codeMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _), map_codePMF_letter]
  rfl

theorem codeMeasure_kernel {C : Type*} (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A)
    (i : Fin n) (h : B → C) (g : M × (Fin i → B)) (c : C) :
    codeMeasure W φ {ω | (ω.1, seqPrefix ω.2 i) = g ∧ h (ω.2 i) = c} =
      codeMeasure W φ {ω | (ω.1, seqPrefix ω.2 i) = g} * (W (φ g.1 i g.2)).map h c := by
  classical
  have e1 : {ω : M × (Fin n → B) | (ω.1, seqPrefix ω.2 i) = g ∧ h (ω.2 i) = c} =
      {ω | ω.1 = g.1 ∧ seqPrefix ω.2 i = g.2 ∧ ω.2 i ∈ {b | h b = c}} := by
    ext ω
    simp only [Prod.ext_iff, Set.mem_ofPred_eq, and_assoc]
  have e2 : {ω : M × (Fin n → B) | (ω.1, seqPrefix ω.2 i) = g} =
      {ω | ω.1 = g.1 ∧ seqPrefix ω.2 i = g.2 ∧ ω.2 i ∈ (Set.univ : Set B)} := by
    ext ω
    simp only [Prod.ext_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true]
  have hs : ∑ b, W (φ g.1 i g.2) b = 1 := by
    have h := PMF.tsum_coe (W (φ g.1 i g.2))
    rwa [tsum_fintype] at h
  rw [e1, e2, codeMeasure_prefix, codeMeasure_prefix, PMF.map_apply, tsum_fintype]
  simp only [Set.mem_univ, ite_true, hs, mul_one, Set.mem_ofPred_eq]
  rw [mul_assoc]
  congr 2
  refine sum_congr rfl fun b _ => ?_
  by_cases hb : h b = c
  · simp [hb]
  · simp [hb, Ne.symm hb]

theorem condEntropy_prefix_eq {C : Type*} [Fintype C] [MeasurableSpace C]
    [MeasurableSingletonClass C] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A) (i : Fin n) (h : B → C) :
    H[fun ω : M × (Fin n → B) => h (ω.2 i) | fun ω => (ω.1, seqPrefix ω.2 i) ;
        codeMeasure W φ] =
      H[fun ω : M × (Fin n → B) => h (ω.2 i) | fun ω => φ ω.1 i (seqPrefix ω.2 i) ;
        codeMeasure W φ] := by
  have hK : ∀ (g : M × (Fin i → B)) (c : C),
      (codeMeasure W φ).real {ω | (ω.1, seqPrefix ω.2 i) = g ∧ h (ω.2 i) = c} =
        (codeMeasure W φ).real {ω | (ω.1, seqPrefix ω.2 i) = g} *
          (((fun a => (W a).map h) ((fun g : M × (Fin i → B) => φ g.1 i g.2) g)) c).toReal :=
    fun g c => by rw [measureReal_def, measureReal_def, codeMeasure_kernel, ENNReal.toReal_mul]
  have hG : Measurable fun ω : M × (Fin n → B) => (ω.1, seqPrefix ω.2 i) :=
    measurable_of_finite _
  have hY : Measurable fun ω : M × (Fin n → B) => h (ω.2 i) := measurable_of_finite _
  have := condEntropy_eq_comp_of_kernel (codeMeasure W φ) (T := M × (Fin i → B)) (S := C)
    (U := A) hG hY (fun g => φ g.1 i g.2) (fun a => (W a).map h) hK
  exact this

theorem entropy_fst_codeMeasure (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A) :
    H[Prod.fst ; codeMeasure W φ] = Real.log (Fintype.card M) := by
  classical
  refine entropy_eq_log_card _ fun m => ?_
  rw [map_measureReal_apply measurable_fst (measurableSet_singleton m), measureReal_def]
  have e : Prod.fst ⁻¹' {m} = {ω : M × (Fin n → B) | ω.1 = m} := rfl
  rw [e, codeMeasure_apply, sum_eq_single m (fun m' _ hm => by simp [hm]) (by simp)]
  simp only [ite_true, ← mul_sum, sum_seqProb, mul_one, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

end Code
section Converse

variable {M J K C A' : Type*} [Fintype M] [Nonempty M] [MeasurableSpace M]
  [MeasurableSingletonClass M] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [Finite K] [MeasurableSpace K] [MeasurableSingletonClass K]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype A'] [MeasurableSpace A'] [MeasurableSingletonClass A'] {n : ℕ}

theorem one_sub_mul_log_card_le_sum (W : DMC A B) (φ : M → (i : Fin n) → (Fin i → B) → A)
    (e : M ≃ J × K) (h : B → C) (π : A → A') (ψ : K → (i : Fin n) → (Fin i → C) → A')
    (hψ : ∀ m i q, π (φ m i q) = ψ (e m).2 i (h ∘ q)) (d : K → (Fin n → C) → J) :
    (1 - (codeMeasure W φ).real {ω | d (e ω.1).2 (h ∘ ω.2) ≠ (e ω.1).1}) *
        Real.log (Fintype.card J) ≤
      ∑ i, (H[fun x : A × B => h x.2 | fun x => π x.1 ; W.jointMeasure (inputLaw W φ i)] -
        H[fun x : A × B => h x.2 | Prod.fst ; W.jointMeasure (inputLaw W φ i)]) + Real.log 2 := by
  have := Fintype.ofFinite K
  set μ := codeMeasure W φ
  set Uj : M × (Fin n → B) → J := fun ω => (e ω.1).1
  set Uk : M × (Fin n → B) → K := fun ω => (e ω.1).2
  set Z : M × (Fin n → B) → Fin n → C := fun ω => h ∘ ω.2
  have : Nonempty J := ⟨(e (Classical.arbitrary M)).1⟩
  have : Nonempty K := ⟨(e (Classical.arbitrary M)).2⟩
  have hcard : Real.log (Fintype.card M) =
      Real.log (Fintype.card J) + Real.log (Fintype.card K) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
        (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
  have hU : H[fun ω : M × (Fin n → B) => (Uj ω, Uk ω) ; μ] = Real.log (Fintype.card M) := by
    rw [← entropy_fst_codeMeasure W φ]
    exact entropy_comp_of_injective μ (X := Prod.fst) (f := fun m => ((e m).1, (e m).2))
      fun a b hab => e.injective (Prod.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab))
  have hK : H[Uk ; μ] ≤ Real.log (Fintype.card K) := entropy_le_log_card μ
  have hc := condMutualInfo_eq_condEntropy_sub_condEntropy μ (X := Z) (Y := Uj) (Z := Uk)
  have hF := condEntropy_le_log_two_add_mul_log_card (μ := μ) (X := Uj)
    (Y := fun ω => (Z ω, Uk ω)) (measurable_of_finite _) (measurable_of_finite _)
    (fun p => d p.2 p.1)
  have hsum := condMutualInfo_eq_sum μ Z Uj Uk
  have hterm : ∀ i, I[fun ω => Z ω i : Uj | fun ω => (Uk ω, seqPrefix (Z ω) i) ; μ] ≤
      H[fun x : A × B => h x.2 | fun x => π x.1 ; W.jointMeasure (inputLaw W φ i)] -
        H[fun x : A × B => h x.2 | Prod.fst ; W.jointMeasure (inputLaw W φ i)] := by
    intro i
    rw [condMutualInfo_comm, condMutualInfo_eq_condEntropy_sub_condEntropy]
    have h1 : H[fun ω => Z ω i | fun ω => (Uk ω, seqPrefix (Z ω) i) ; μ] ≤
        H[fun ω : M × (Fin n → B) => h (ω.2 i) | fun ω => π (φ ω.1 i (seqPrefix ω.2 i)) ; μ] := by
      have := condEntropy_le_condEntropy_comp (μ := μ) (X := fun ω => Z ω i)
        (Y := fun ω => (Uk ω, seqPrefix (Z ω) i)) (measurable_of_finite _)
        (measurable_of_finite _) (fun p => ψ p.1 i p.2)
      refine this.trans (le_of_eq ?_)
      congr 1
      funext ω
      exact (hψ ω.1 i (seqPrefix ω.2 i)).symm
    have h2 : H[fun ω : M × (Fin n → B) => h (ω.2 i) | fun ω => (ω.1, seqPrefix ω.2 i) ; μ] ≤
        H[fun ω => Z ω i | fun ω => (Uj ω, (Uk ω, seqPrefix (Z ω) i)) ; μ] :=
      condEntropy_le_condEntropy_comp (μ := μ) (X := fun ω : M × (Fin n → B) => h (ω.2 i))
        (Y := fun ω => (ω.1, seqPrefix ω.2 i)) (measurable_of_finite _) (measurable_of_finite _)
        (fun p => ((e p.1).1, ((e p.1).2, h ∘ p.2)))
    have h3 := condEntropy_prefix_eq W φ i h
    have hν := map_codeMeasure_letter W φ i
    have h4 : H[fun ω : M × (Fin n → B) => h (ω.2 i) | fun ω => π (φ ω.1 i (seqPrefix ω.2 i)) ;
        μ] = H[fun x : A × B => h x.2 | fun x => π x.1 ; W.jointMeasure (inputLaw W φ i)] := by
      rw [← hν, condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _)
        (measurable_of_finite _)]
      rfl
    have h5 : H[fun ω : M × (Fin n → B) => h (ω.2 i) | fun ω => φ ω.1 i (seqPrefix ω.2 i) ;
        μ] = H[fun x : A × B => h x.2 | Prod.fst ; W.jointMeasure (inputLaw W φ i)] := by
      rw [← hν, condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _)
        measurable_fst]
      rfl
    linarith
  have hs : I[Z : Uj | Uk ; μ] ≤ ∑ i,
      (H[fun x : A × B => h x.2 | fun x => π x.1 ; W.jointMeasure (inputLaw W φ i)] -
        H[fun x : A × B => h x.2 | Prod.fst ; W.jointMeasure (inputLaw W φ i)]) :=
    hsum ▸ sum_le_sum fun i _ => hterm i
  have hdef : H[Uj | Uk ; μ] = H[fun ω : M × (Fin n → B) => (Uj ω, Uk ω) ; μ] - H[Uk ; μ] := rfl
  have hset : {ω : M × (Fin n → B) | (fun p : (Fin n → C) × K => d p.2 p.1)
      ((fun ω => (Z ω, Uk ω)) ω) ≠ Uj ω} = {ω | d (e ω.1).2 (h ∘ ω.2) ≠ (e ω.1).1} := rfl
  rw [hset] at hF
  nlinarith

theorem one_sub_mul_log_card_le_sum_mutualInfo (W : DMC A B)
    (φ : M → (i : Fin n) → (Fin i → B) → A) (d : (Fin n → B) → M) :
    (1 - (codeMeasure W φ).real {ω | d ω.2 ≠ ω.1}) * Real.log (Fintype.card M) ≤
      ∑ i, (H[Prod.snd ; W.jointMeasure (inputLaw W φ i)] -
        H[Prod.snd | Prod.fst ; W.jointMeasure (inputLaw W φ i)]) + Real.log 2 := by
  set μ := codeMeasure W φ
  have hU := entropy_fst_codeMeasure W φ
  have hI := mutualInfo_eq_entropy_sub_condEntropy (μ := μ) Prod.fst Prod.snd
  have hF := condEntropy_le_log_two_add_mul_log_card (μ := μ) (X := Prod.fst) (Y := Prod.snd)
    measurable_fst measurable_snd d
  have hsum := mutualInfo_eq_sum μ (fun ω : M × (Fin n → B) => ω.2) Prod.fst
  rw [mutualInfo_comm] at hsum
  have hterm : ∀ i, I[fun ω : M × (Fin n → B) => ω.2 i : Prod.fst |
      fun ω => seqPrefix ω.2 i ; μ] ≤ H[Prod.snd ; W.jointMeasure (inputLaw W φ i)] -
        H[Prod.snd | Prod.fst ; W.jointMeasure (inputLaw W φ i)] := by
    intro i
    rw [condMutualInfo_comm, condMutualInfo_eq_condEntropy_sub_condEntropy]
    have h1 := condEntropy_le_entropy μ (X := fun ω : M × (Fin n → B) => ω.2 i)
      (Y := fun ω => seqPrefix ω.2 i) (measurable_of_finite _) (measurable_of_finite _)
    have h3 := condEntropy_prefix_eq W φ i id
    have hν := map_codeMeasure_letter W φ i
    have h4 : H[fun ω : M × (Fin n → B) => ω.2 i ; μ] =
        H[Prod.snd ; W.jointMeasure (inputLaw W φ i)] := by
      rw [← hν, entropy_map _ (measurable_of_finite _) measurable_snd]
      rfl
    have h5 : H[fun ω : M × (Fin n → B) => id (ω.2 i) | fun ω => φ ω.1 i (seqPrefix ω.2 i) ;
        μ] = H[Prod.snd | Prod.fst ; W.jointMeasure (inputLaw W φ i)] := by
      rw [← hν, condEntropy_map _ (measurable_of_finite _) measurable_snd measurable_fst]
      rfl
    have h6 : H[fun ω : M × (Fin n → B) => ω.2 i | fun ω => (ω.1, seqPrefix ω.2 i) ; μ] =
        H[fun ω : M × (Fin n → B) => id (ω.2 i) | fun ω => (ω.1, seqPrefix ω.2 i) ; μ] := rfl
    linarith
  have hs := hsum ▸ sum_le_sum fun i (_ : i ∈ univ) => hterm i
  nlinarith

end Converse

end Interactive

end Meat
