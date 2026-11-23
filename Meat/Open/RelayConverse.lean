import Meat.Open.Relay
import Meat.Open.BroadcastConverse

open MeasureTheory
open scoped ENNReal

namespace Meat

section Causal

variable {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}

private lemma sum_prefix_split (F : (Fin n → S) → ℝ≥0∞) (k : Fin n) (a : Fin n → S) :
    ∑ z, (if ∀ l : Fin n, (l : ℕ) < k → z l = a l then F z else 0) =
      ∑ s, ∑ z, (if ∀ l : Fin n, (l : ℕ) < k + 1 → z l = Function.update a k s l then F z
        else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single (z k) (fun s _ hs => ite_eq_right_iff.2 fun h =>
    absurd ((h k (by omega)).trans (by simp)).symm hs) (by simp)]
  congr 1
  apply propext
  constructor
  · intro h l hl
    by_cases hlk : l = k
    · subst hlk
      simp
    · have : (l : ℕ) < k := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h' | h'
        · exact h'
        · exact absurd (Fin.ext h') hlk
      rw [Function.update_of_ne hlk]
      exact h l this
  · intro h l hl
    have hlk : l ≠ k := fun e => by subst e; omega
    rw [h l (by omega), Function.update_of_ne hlk]

omit [Fintype S] [DecidableEq S] in
theorem prod_prefix_update (f : Fin n → (Fin n → S) → S → ℝ≥0∞)
    (hcausal : ∀ j z z', (∀ l : Fin n, l < j → z l = z' l) → f j z = f j z') (k : Fin n)
    (a : Fin n → S) (s : S) :
    ∏ j : Fin n, (if (j : ℕ) < k + 1 then f j (Function.update a k s)
        (Function.update a k s j) else 1) =
      f k a s * ∏ j : Fin n, (if (j : ℕ) < k then f j a (a j) else 1) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ
      (fun j : Fin n => if (j : ℕ) < k then f j a (a j) else 1) (Finset.mem_univ k)]
  simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, ite_true, lt_irrefl, ite_false,
    one_mul, Function.update_self]
  congr 1
  · exact congrFun (hcausal _ _ _ fun l hl => Function.update_of_ne (ne_of_lt hl) _ _) s
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    have hjk' : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
    by_cases hj : (j : ℕ) < k
    · simp only [show (j : ℕ) < k + 1 by omega, hj, ite_true]
      rw [Function.update_of_ne hjk]
      exact congrFun (hcausal _ _ _ fun l hl => Function.update_of_ne
        (ne_of_lt (hl.trans (Fin.lt_def.2 hj))) _ _) _
    · simp only [show ¬(j : ℕ) < k + 1 by omega, hj, ite_false]

theorem sum_causal_prefix (f : Fin n → (Fin n → S) → S → ℝ≥0∞)
    (hsum : ∀ j z, ∑ s, f j z s = 1)
    (hcausal : ∀ j z z', (∀ l : Fin n, l < j → z l = z' l) → f j z = f j z') :
    ∀ (m k : ℕ), k + m = n → ∀ a : Fin n → S,
      ∑ z, (if ∀ l : Fin n, (l : ℕ) < k → z l = a l then ∏ j, f j z (z j) else 0) =
        ∏ j : Fin n, (if (j : ℕ) < k then f j a (a j) else 1) := by
  intro m
  induction m with
  | zero =>
    intro k hk a
    rw [Finset.sum_eq_single a (fun z _ hz => ite_eq_right_iff.2 fun h =>
      absurd (funext fun l => h l (by omega)) hz) (by simp)]
    simp only [show ∀ l : Fin n, (l : ℕ) < k from fun l => by omega, implies_true, ite_true]
  | succ m ih =>
    intro k hk a
    have hkn : k < n := by omega
    rw [sum_prefix_split _ ⟨k, hkn⟩ a]
    simp only []
    have e : ∀ s, ∑ z, (if ∀ l : Fin n, (l : ℕ) < k + 1 →
        z l = Function.update a ⟨k, hkn⟩ s l then ∏ j, f j z (z j) else 0) =
        ∏ j : Fin n, (if (j : ℕ) < k + 1 then f j (Function.update a ⟨k, hkn⟩ s)
          (Function.update a ⟨k, hkn⟩ s j) else 1) := fun s => ih (k + 1) (by omega) _
    simp_rw [e]
    have e2 := fun s => prod_prefix_update f hcausal ⟨k, hkn⟩ a s
    simp_rw [e2]
    rw [← Finset.sum_mul, hsum, one_mul]

end Causal

section Input

variable {U X Z : Type*} [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

omit [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype X] [MeasurableSpace X]
  [MeasurableSingletonClass X] [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
theorem jointPMF_comp_input_map (K : DMC X Z) (p : PMF U) (g : U → X) :
    (DMC.jointPMF (fun u => K (g u)) p).map (fun ω => (g ω.1, ω.2)) =
      DMC.jointPMF K (p.map g) := by
  simp only [DMC.jointPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]

theorem condEntropy_comp_input (K : DMC X Z) (p : PMF U) (g : U → X) :
    H[Prod.snd | Prod.fst ; DMC.jointMeasure (fun u => K (g u)) p] =
      H[Prod.snd | Prod.fst ; K.jointMeasure (p.map g)] := by
  rw [DMC.condEntropy_snd_fst_jointMeasure, DMC.condEntropy_snd_fst_jointMeasure]
  congr 1
  have h := sum_measureReal_mul_comp (DMC.jointMeasure (fun u => K (g u)) p)
    (fun ω => (g ω.1, ω.2)) (fun x => Real.log (K x.1 x.2).toReal)
  rw [DMC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _),
    jointPMF_comp_input_map] at h
  exact h

end Input

namespace RelayCode

variable {M A A₁ B B₁ : Type*} {n : ℕ} [Fintype B] [Fintype B₁]

omit [Fintype B] [Fintype B₁] in
theorem causal_seq (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁)) (m : M) (j : Fin n)
    (z z' : Fin n → B × B₁) (h : ∀ l : Fin n, l < j → z l = z' l) :
    W (c.enc m j, c.relay j fun l => (z l).2) = W (c.enc m j, c.relay j fun l => (z' l).2) := by
  rw [c.causal j _ _ fun l hl => by rw [h l hl]]

theorem sum_seqProb [Nonempty B] [Nonempty B₁] (c : RelayCode M A A₁ B B₁ n)
    (W : DMC (A × A₁) (B × B₁)) (m : M) :
    ∑ y, c.seqProb W m y = 1 := by
  classical
  have h := sum_causal_prefix (fun j z s => W (c.enc m j, c.relay j fun l => (z l).2) s)
    (fun j z => sum_pmf_eq_one _) (fun j z z' h => funext fun s =>
      congrFun (congrArg DFunLike.coe (c.causal_seq W m j z z' h)) s) n 0 (by omega)
    (fun _ => Classical.arbitrary _)
  simpa [seqProb] using h

variable [Fintype M] [Nonempty M] [Nonempty B] [Nonempty B₁]

theorem sum_codeMass (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁)) :
    ∑ ω : M × (Fin n → B × B₁), (Fintype.card M : ℝ≥0∞)⁻¹ * c.seqProb W ω.1 ω.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, sum_seqProb, mul_one]
  exact sum_inv_card M

noncomputable def codePMF (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁)) :
    PMF (M × (Fin n → B × B₁)) :=
  PMF.ofFintype _ (c.sum_codeMass W)

theorem measureReal_dec_ne [MeasurableSpace M] [MeasurableSingletonClass M] [MeasurableSpace B]
    [MeasurableSingletonClass B] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
    [DecidableEq M] (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁)) :
    (c.codePMF W).toMeasure.real {ω | c.dec (fun i => (ω.2 i).1) ≠ ω.1} =
      (c.avgError W).toReal := by
  rw [measureReal_def, PMF.toMeasure_apply_fintype, avgError, div_eq_mul_inv, mul_comm,
    Finset.mul_sum, Fintype.sum_prod_type]
  refine congrArg ENNReal.toReal (Finset.sum_congr rfl fun m _ => ?_)
  rw [errorProb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : c.dec (fun i => (y i).1) = m <;> simp [Set.indicator, h, codePMF]

noncomputable def letterPMF (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁))
    (i : Fin n) (d : B × B₁) : PMF ((M × (Fin n → B × B₁)) × B × B₁) :=
  (c.codePMF W).map fun ω => ((ω.1, BC.padPrefix ω.2 i d), ω.2 i)

def letterInput (c : RelayCode M A A₁ B B₁ n) (i : Fin n) (u : M × (Fin n → B × B₁)) : A × A₁ :=
  (c.enc u.1 i, c.relay i fun j => (u.2 j).2)

theorem letterPMF_apply (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁)) (i : Fin n)
    (d : B × B₁) (u : M × (Fin n → B × B₁)) (z : B × B₁) :
    c.letterPMF W i d (u, z) = ((c.letterPMF W i d).map Prod.fst) u * W (c.letterInput i u) z := by
  classical
  obtain ⟨m₀, a⟩ := u
  set f : Fin n → (Fin n → B × B₁) → B × B₁ → ℝ≥0∞ :=
    fun j z s => W (c.enc m₀ j, c.relay j fun l => (z l).2) s
  have hf : ∀ j z z', (∀ l : Fin n, l < j → z l = z' l) → f j z = f j z' := fun j z z' h =>
    funext fun s => congrFun (congrArg DFunLike.coe (c.causal_seq W m₀ j z z' h)) s
  rw [letterPMF, PMF.map_comp, PMF.map_apply, PMF.map_apply, tsum_fintype, tsum_fintype,
    Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_mul]
  simp only [Function.comp_def, codePMF, PMF.ofFintype_apply]
  rw [Finset.sum_eq_single m₀, Finset.sum_eq_single m₀]
  rotate_left
  · intro m _ hm
    simp [Ne.symm hm]
  · simp
  · intro m _ hm
    simp [Ne.symm hm]
  · simp
  by_cases hC : ∀ l : Fin n, ¬(l : ℕ) < i → d = a l
  · have e1 : ∀ y : Fin n → B × B₁, ((m₀, a), z) = ((m₀, BC.padPrefix y i d), y i) ↔
        ∀ l : Fin n, (l : ℕ) < i + 1 → y l = Function.update a i z l := by
      intro y
      simp only [Prod.mk.injEq, true_and, funext_iff, BC.padPrefix, seqPrefix]
      constructor
      · rintro ⟨h1, h2⟩ l hl
        by_cases hli : l = i
        · subst hli
          simp [h2]
        · have : (l : ℕ) < i := by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h' | h'
            · exact h'
            · exact absurd (Fin.ext h') hli
          rw [Function.update_of_ne hli, h1 l]
          simp [this]
      · intro h
        refine ⟨fun l => ?_, by rw [h i (by omega)]; simp⟩
        by_cases hl : (l : ℕ) < i
        · have hli : l ≠ i := fun e => by subst e; omega
          simp [hl, h l (by omega), Function.update_of_ne hli]
        · simp [hl, hC l hl]
    have e2 : ∀ y : Fin n → B × B₁, (m₀, a) = (m₀, BC.padPrefix y i d) ↔
        ∀ l : Fin n, (l : ℕ) < i → y l = a l := by
      intro y
      simp only [Prod.mk.injEq, true_and, funext_iff, BC.padPrefix, seqPrefix]
      constructor
      · intro h l hl
        rw [h l]
        simp [hl]
      · intro h l
        by_cases hl : (l : ℕ) < i
        · simp [hl, h l hl]
        · simp [hl, hC l hl]
    have s1 : ∀ (y : Fin n → B × B₁) [Decidable (((m₀, a), z) =
        ((m₀, BC.padPrefix y i d), y i))], (if ((m₀, a), z) = ((m₀, BC.padPrefix y i d), y i) then
        (Fintype.card M : ℝ≥0∞)⁻¹ * c.seqProb W m₀ y else 0) = (Fintype.card M : ℝ≥0∞)⁻¹ *
        (if ∀ l : Fin n, (l : ℕ) < i + 1 → y l = Function.update a i z l then
          ∏ j, f j y (y j) else 0) := fun y _ => by
      by_cases h : ∀ l : Fin n, (l : ℕ) < i + 1 → y l = Function.update a i z l
      · rw [ite_eq_left ((e1 y).2 h), ite_eq_left h]
        rfl
      · rw [ite_eq_right (fun h' => h ((e1 y).1 h')), ite_eq_right h, mul_zero]
    have s2 : ∀ (y : Fin n → B × B₁) [Decidable ((m₀, a) = (m₀, BC.padPrefix y i d))],
        (if (m₀, a) = (m₀, BC.padPrefix y i d) then
        (Fintype.card M : ℝ≥0∞)⁻¹ * c.seqProb W m₀ y else 0) = (Fintype.card M : ℝ≥0∞)⁻¹ *
        (if ∀ l : Fin n, (l : ℕ) < i → y l = a l then ∏ j, f j y (y j) else 0) := fun y _ => by
      by_cases h : ∀ l : Fin n, (l : ℕ) < i → y l = a l
      · rw [ite_eq_left ((e2 y).2 h), ite_eq_left h]
        rfl
      · rw [ite_eq_right (fun h' => h ((e2 y).1 h')), ite_eq_right h, mul_zero]
    simp_rw [s1, s2]
    rw [← Finset.mul_sum, ← Finset.mul_sum,
      sum_causal_prefix f (fun j z => sum_pmf_eq_one _) hf (n - (i + 1)) (i + 1) (by omega),
      sum_causal_prefix f (fun j z => sum_pmf_eq_one _) hf (n - i) i (by omega),
      prod_prefix_update f hf i a z]
    simp only [f, letterInput]
    ring
  · have hne : ∀ y : Fin n → B × B₁, a ≠ BC.padPrefix y i d := fun y h => hC fun l hl => by
      rw [h]
      simp [BC.padPrefix, hl]
    simp [hne]

theorem letterPMF_eq (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁)) (i : Fin n)
    (d : B × B₁) :
    c.letterPMF W i d = DMC.jointPMF (fun u => W (c.letterInput i u))
      ((c.letterPMF W i d).map Prod.fst) := by
  ext ⟨u, z⟩
  rw [DMC.jointPMF_apply, letterPMF_apply]

noncomputable def letterLaw (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁))
    (i : Fin n) (d : B × B₁) : PMF (A × A₁) :=
  ((c.letterPMF W i d).map Prod.fst).map (c.letterInput i)

section Laws

variable [MeasurableSpace M] [MeasurableSingletonClass M] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [MeasurableSpace B] [MeasurableSingletonClass B] [MeasurableSpace B₁]
  [MeasurableSingletonClass B₁]

omit [Fintype A] [MeasurableSingletonClass A] [Fintype A₁] [MeasurableSingletonClass A₁] in
theorem map_codePMF_input (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁)) (i : Fin n)
    (d : B × B₁) :
    (c.codePMF W).toMeasure.map (fun ω => (c.letterInput i (ω.1, BC.padPrefix ω.2 i d), ω.2 i)) =
      W.jointMeasure (c.letterLaw W i d) := by
  rw [PMF.toMeasure_map _ _ (measurable_of_finite _), DMC.jointMeasure_eq_toMeasure, letterLaw,
    ← jointPMF_comp_input_map, ← letterPMF_eq, letterPMF, PMF.map_comp]
  rfl

theorem condEntropy_letter (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁))
    (i : Fin n) (d : B × B₁) :
    H[fun ω : M × (Fin n → B × B₁) => ω.2 i | fun ω => (ω.1, BC.padPrefix ω.2 i d) ;
        (c.codePMF W).toMeasure] =
      H[fun ω : (A × A₁) × B × B₁ => ω.2 | fun ω => ω.1 ; W.jointMeasure (c.letterLaw W i d)] := by
  have h := condEntropy_comp_input W ((c.letterPMF W i d).map Prod.fst) (c.letterInput i)
  rw [DMC.jointMeasure_eq_toMeasure, ← letterPMF_eq, letterPMF,
    ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condEntropy_map _ (measurable_of_finite _) measurable_snd measurable_fst] at h
  exact h

theorem condEntropy_letter_fst (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁))
    (i : Fin n) (d : B × B₁) :
    H[fun ω : M × (Fin n → B × B₁) => (ω.2 i).1 | fun ω => (ω.1, BC.padPrefix ω.2 i d) ;
        (c.codePMF W).toMeasure] =
      H[fun ω : (A × A₁) × B × B₁ => ω.2.1 | fun ω => ω.1 ;
        W.jointMeasure (c.letterLaw W i d)] := by
  have h := condEntropy_comp_input (fun x => (W x).map Prod.fst)
    ((c.letterPMF W i d).map Prod.fst) (c.letterInput i)
  have e1 : DMC.jointMeasure (fun u => (W (c.letterInput i u)).map Prod.fst)
      ((c.letterPMF W i d).map Prod.fst) = (c.codePMF W).toMeasure.map
        (fun ω => ((ω.1, BC.padPrefix ω.2 i d), (ω.2 i).1)) := by
    have e1a : DMC.jointPMF (fun u => (W (c.letterInput i u)).map Prod.fst)
        ((c.letterPMF W i d).map Prod.fst) = (DMC.jointPMF (fun u => W (c.letterInput i u))
          ((c.letterPMF W i d).map Prod.fst)).map (fun ω => (ω.1, ω.2.1)) := by
      simp only [DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]
    rw [← letterPMF_eq] at e1a
    rw [PMF.toMeasure_map _ _ (measurable_of_finite _), DMC.jointMeasure_eq_toMeasure, e1a,
      letterPMF, PMF.map_comp]
    rfl
  have e2 : DMC.jointMeasure (fun x => (W x).map Prod.fst) (c.letterLaw W i d) =
      (W.jointMeasure (c.letterLaw W i d)).map (fun ω => (ω.1, ω.2.1)) := by
    rw [DMC.jointMeasure_eq_toMeasure, DMC.jointMeasure_eq_toMeasure,
      PMF.toMeasure_map _ _ (measurable_of_finite _)]
    congr 1
    simp only [DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [e1, condEntropy_map _ (measurable_of_finite _) measurable_snd measurable_fst] at h
  rw [letterLaw] at e2
  rw [e2, condEntropy_map _ (measurable_of_finite _) measurable_snd measurable_fst] at h
  exact h

end Laws

end RelayCode

private lemma condEntropy_seq_pad {M S T : Type*} {n : ℕ} [Fintype M] [MeasurableSpace M]
    [MeasurableSingletonClass M] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {K : Type*}
    [MeasurableSpace K] (μ : Measure (K × (Fin n → S)))
    (κ : K → M) (F : K × (Fin n → S) → T) (q : Fin n) (d : S) :
    H[F | fun ω => (κ ω.1, seqPrefix ω.2 q) ; μ] =
      H[F | fun ω => (κ ω.1, BC.padPrefix ω.2 q d) ; μ] :=
  (condEntropy_cond_of_injective μ (Z := fun ω => (κ ω.1, seqPrefix ω.2 q))
    (Z' := fun ω => (κ ω.1, BC.padPrefix ω.2 q d))
    (e := Prod.map id fun p : Fin q → S => fun j : Fin n =>
      if h : (j : ℕ) < q then p ⟨j, h⟩ else d)
    (Function.injective_id.prodMap (BC.padPrefix_injective q d)) fun _ => rfl).symm

namespace RelayCode

variable {M A A₁ B B₁ : Type*} {n : ℕ} [Fintype M] [Nonempty M] [MeasurableSpace M]
  [MeasurableSingletonClass M] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype B] [Nonempty B]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype B₁] [Nonempty B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁]

theorem mutualInfo_le_sum₁ (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁))
    (d : B × B₁) :
    I[fun ω : M × (Fin n → B × B₁) => ω.1 : fun ω j => (ω.2 j).1 ; (c.codePMF W).toMeasure] ≤
      ∑ i, I[fun ω : (A × A₁) × B × B₁ => ω.1 : fun ω => ω.2.1 ;
        W.jointMeasure (c.letterLaw W i d)] := by
  set μ := (c.codePMF W).toMeasure
  rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
  have h1 := entropy_pi_le_sum μ (Y := fun ω : M × (Fin n → B × B₁) => fun j => (ω.2 j).1)
    fun i => measurable_of_finite _
  have h2 := condEntropy_eq_sum μ (fun ω : M × (Fin n → B × B₁) => fun j => (ω.2 j).1)
    (fun ω => ω.1)
  have h3 : ∀ i, H[fun ω : M × (Fin n → B × B₁) => (ω.2 i).1 |
      fun ω => (ω.1, BC.padPrefix ω.2 i d) ; μ] ≤
      H[fun ω : M × (Fin n → B × B₁) => (ω.2 i).1 |
        fun ω => (ω.1, seqPrefix (fun j => (ω.2 j).1) i) ; μ] := fun i => by
    rw [← condEntropy_seq_pad μ (fun m => m) _ i d]
    exact condEntropy_le_condEntropy_comp (μ := μ) (measurable_of_finite _)
      (measurable_of_finite _) fun p : M × (Fin i → B × B₁) => (p.1, fun j => (p.2 j).1)
  have h4 : ∀ i, I[fun ω : (A × A₁) × B × B₁ => ω.1 : fun ω => ω.2.1 ;
      W.jointMeasure (c.letterLaw W i d)] =
      H[fun ω : M × (Fin n → B × B₁) => (ω.2 i).1 ; μ] -
        H[fun ω : M × (Fin n → B × B₁) => (ω.2 i).1 |
          fun ω => (ω.1, BC.padPrefix ω.2 i d) ; μ] := fun i => by
    rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy, condEntropy_letter_fst,
      ← map_codePMF_input c W i d, entropy_map _ (measurable_of_finite _)
        (measurable_of_finite _)]
    rfl
  simp_rw [h4, Finset.sum_sub_distrib]
  have h5 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h3 i
  linarith

theorem mutualInfo_le_sum₂ (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁))
    (d : B × B₁) :
    I[fun ω : M × (Fin n → B × B₁) => ω.1 : fun ω j => (ω.2 j).1 ; (c.codePMF W).toMeasure] ≤
      ∑ i, I[fun ω : (A × A₁) × B × B₁ => ω.1.1 : fun ω => ω.2 | fun ω => ω.1.2 ;
        W.jointMeasure (c.letterLaw W i d)] := by
  set μ := (c.codePMF W).toMeasure
  have h0 := mutualInfo_comp_le μ (X := fun ω : M × (Fin n → B × B₁) => ω.1)
    (Y := fun ω => ω.2) (measurable_of_finite _) (measurable_of_finite _)
    (fun z : Fin n → B × B₁ => fun j => (z j).1)
  refine le_trans h0 ?_
  rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
  have h1 := entropy_eq_sum μ (fun ω : M × (Fin n → B × B₁) => ω.2)
  have h2 := condEntropy_eq_sum μ (fun ω : M × (Fin n → B × B₁) => ω.2) (fun ω => ω.1)
  have h3 : ∀ i, H[fun ω : M × (Fin n → B × B₁) => ω.2 i | fun ω => seqPrefix ω.2 i ; μ] ≤
      H[fun ω : M × (Fin n → B × B₁) => ω.2 i |
        fun ω => (c.letterInput i (ω.1, BC.padPrefix ω.2 i d)).2 ; μ] := fun i =>
    condEntropy_le_condEntropy_comp (μ := μ) (measurable_of_finite _) (measurable_of_finite _)
      fun p : Fin i → B × B₁ => c.relay i fun j =>
        (if h : (j : ℕ) < i then p ⟨j, h⟩ else d).2
  have h4 : ∀ i, I[fun ω : (A × A₁) × B × B₁ => ω.1.1 : fun ω => ω.2 | fun ω => ω.1.2 ;
      W.jointMeasure (c.letterLaw W i d)] =
      H[fun ω : M × (Fin n → B × B₁) => ω.2 i |
        fun ω => (c.letterInput i (ω.1, BC.padPrefix ω.2 i d)).2 ; μ] -
      H[fun ω : M × (Fin n → B × B₁) => ω.2 i | fun ω => (ω.1, seqPrefix ω.2 i) ; μ] :=
    fun i => by
    rw [condMutualInfo_eq_condEntropy_sub_condEntropy, condEntropy_seq_pad μ (fun m => m) _ i d,
      condEntropy_letter, ← map_codePMF_input c W i d,
      condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _)
        (measurable_of_finite _)]
    rfl
  simp_rw [h4, Finset.sum_sub_distrib]
  have h5 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h3 i
  linarith

end RelayCode

section Mixture

variable {A A₁ B B₁ : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype B]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype B₁] [MeasurableSpace B₁]
  [MeasurableSingletonClass B₁] {n : ℕ} [NeZero n]

private lemma condMutualInfo_comp_right_le' {Ω S T U U' : Type*} [MeasurableSpace Ω]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    [Fintype U'] [MeasurableSpace U'] [MeasurableSingletonClass U']
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (f : T → U') :
    I[X : fun ω => f (Y ω) | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  rw [condMutualInfo_comm, condMutualInfo_eq_condEntropy_sub_condEntropy,
    condMutualInfo_comm, condMutualInfo_eq_condEntropy_sub_condEntropy]
  have := condEntropy_le_condEntropy_comp (μ := μ) hX (hY.prodMk hZ)
    (fun p : T × U => (f p.1, p.2))
  have e : ((fun p : T × U => (f p.1, p.2)) ∘ fun ω => (Y ω, Z ω)) =
      fun ω => (f (Y ω), Z ω) := rfl
  rw [e] at this
  linarith

theorem cutSet_mixture (W : DMC (A × A₁) (B × B₁)) (p : Fin n → PMF (A × A₁)) :
    (n : ℝ)⁻¹ * ∑ q, I[fun ω : (A × A₁) × B × B₁ => ω.1 : fun ω => ω.2.1 ;
        W.jointMeasure (p q)] ≤
      I[fun ω : (A × A₁) × B × B₁ => ω.1 : fun ω => ω.2.1 ;
        W.jointMeasure ((DMC.jointPMF p (BC.unifPMF n)).map Prod.snd)] ∧
    (n : ℝ)⁻¹ * ∑ q, I[fun ω : (A × A₁) × B × B₁ => ω.1.1 : fun ω => ω.2 | fun ω => ω.1.2 ;
        W.jointMeasure (p q)] ≤
      I[fun ω : (A × A₁) × B × B₁ => ω.1.1 : fun ω => ω.2 | fun ω => ω.1.2 ;
        W.jointMeasure ((DMC.jointPMF p (BC.unifPMF n)).map Prod.snd)] := by
  set L : Fin n → PMF ((A × A₁) × B × B₁) := fun q => DMC.jointPMF W (p q)
  set ρ := DMC.jointPMF L (BC.unifPMF n)
  have hsnd : W.jointMeasure ((DMC.jointPMF p (BC.unifPMF n)).map Prod.snd) =
      ρ.toMeasure.map Prod.snd := by
    rw [DMC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ measurable_snd]
    congr 1
    simp only [ρ, L, DMC.jointPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def,
      PMF.bind_bind]
  have hm : MarkovChain (fun ω : Fin n × (A × A₁) × B × B₁ => ω.1) (fun ω => ω.2.1)
      (fun ω => ω.2.2) ρ.toMeasure := by
    refine BC.markovChain_of_pmf ρ _ _ _ (fun x z => W x z) fun q x z => ?_
    have h1 : ρ.map (fun ω : Fin n × (A × A₁) × B × B₁ => (ω.1, ω.2.1, ω.2.2)) = ρ :=
      PMF.map_id ρ
    have h2 : ρ.map (fun ω : Fin n × (A × A₁) × B × B₁ => (ω.1, ω.2.1)) =
        DMC.jointPMF p (BC.unifPMF n) := by
      have hc : ∀ (q : Fin n) (a : A × A₁), (W a).map (fun _ => (q, a)) = PMF.pure (q, a) :=
        fun q a => PMF.map_const _ _
      simp only [ρ, L, DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def, hc]
      rfl
    rw [h1, h2, DMC.jointPMF_apply, DMC.jointPMF_apply, DMC.jointPMF_apply, mul_assoc]
  rw [markovChain_def] at hm
  have hm0 := hm
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy] at hm
  have hmY : I[fun ω : Fin n × (A × A₁) × B × B₁ => ω.1 : fun ω => ω.2.2.1 |
      fun ω => ω.2.1 ; ρ.toMeasure] = 0 := by
    have h := condMutualInfo_comp_right_le' (μ := ρ.toMeasure)
      (X := fun ω : Fin n × (A × A₁) × B × B₁ => ω.1) (Y := fun ω => ω.2.2)
      (Z := fun ω => ω.2.1) (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) Prod.fst
    rw [hm0] at h
    exact le_antisymm h (condMutualInfo_nonneg _ (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _))
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy] at hmY
  rw [hsnd, mutualInfo_map _ measurable_snd (measurable_of_finite _) (measurable_of_finite _),
    condMutualInfo_map _ measurable_snd (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
  have a1 := BC.condEntropy_mixture L (fun r : (A × A₁) × B × B₁ => r.2.1) (fun r => r.1)
  have a2 := BC.entropy_mixture_ge L (fun r : (A × A₁) × B × B₁ => r.2.1)
  have a3 := BC.condEntropy_mixture L (fun r : (A × A₁) × B × B₁ => r.2) (fun r => r.1)
  have a4 := BC.condEntropy_mixture L (fun r : (A × A₁) × B × B₁ => r.2) (fun r => r.1.2)
  have a5 := condEntropy_le_condEntropy_comp (μ := ρ.toMeasure)
    (X := fun ω : Fin n × (A × A₁) × B × B₁ => ω.2.2) (Y := fun ω => (ω.1, ω.2.1.2))
    (measurable_of_finite _) (measurable_of_finite _) Prod.snd
  constructor
  · rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
    have e : ∑ q, I[fun ω : (A × A₁) × B × B₁ => ω.1 : fun ω => ω.2.1 ; (L q).toMeasure] =
        ∑ q, H[fun r : (A × A₁) × B × B₁ => r.2.1 ; (L q).toMeasure] -
          ∑ q, H[fun r : (A × A₁) × B × B₁ => r.2.1 | fun r => r.1 ; (L q).toMeasure] := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ => by
        rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
    change (n : ℝ)⁻¹ * ∑ q, I[fun ω : (A × A₁) × B × B₁ => ω.1 : fun ω => ω.2.1 ;
      (L q).toMeasure] ≤ _
    rw [e, mul_sub]
    change _ ≤ H[fun p : Fin n × (A × A₁) × B × B₁ => p.2.2.1 ; ρ.toMeasure] -
      H[fun p : Fin n × (A × A₁) × B × B₁ => p.2.2.1 | fun p => p.2.1 ; ρ.toMeasure]
    have : H[fun p : Fin n × (A × A₁) × B × B₁ => p.2.2.1 | fun p => p.2.1 ; ρ.toMeasure] =
        H[fun p : Fin n × (A × A₁) × B × B₁ => p.2.2.1 | fun p => (p.1, p.2.1) ;
          ρ.toMeasure] := by linarith
    rw [this, a1]
    linarith
  · rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
    have e : ∑ q, I[fun ω : (A × A₁) × B × B₁ => ω.1.1 : fun ω => ω.2 | fun ω => ω.1.2 ;
        (L q).toMeasure] =
        ∑ q, H[fun r : (A × A₁) × B × B₁ => r.2 | fun r => r.1.2 ; (L q).toMeasure] -
          ∑ q, H[fun r : (A × A₁) × B × B₁ => r.2 | fun r => r.1 ; (L q).toMeasure] := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ => condMutualInfo_eq_condEntropy_sub_condEntropy _
    change (n : ℝ)⁻¹ * ∑ q, I[fun ω : (A × A₁) × B × B₁ => ω.1.1 : fun ω => ω.2 |
      fun ω => ω.1.2 ; (L q).toMeasure] ≤ _
    rw [e, mul_sub]
    change _ ≤ H[fun p : Fin n × (A × A₁) × B × B₁ => p.2.2 | fun p => p.2.1.2 ; ρ.toMeasure] -
      H[fun p : Fin n × (A × A₁) × B × B₁ => p.2.2 | fun p => p.2.1 ; ρ.toMeasure]
    have : H[fun p : Fin n × (A × A₁) × B × B₁ => p.2.2 | fun p => p.2.1 ; ρ.toMeasure] =
        H[fun p : Fin n × (A × A₁) × B × B₁ => p.2.2 | fun p => (p.1, p.2.1) ;
          ρ.toMeasure] := by linarith
    rw [this, a3]
    have a5' : H[fun p : Fin n × (A × A₁) × B × B₁ => p.2.2 | fun p => (p.1, p.2.1.2) ;
        ρ.toMeasure] ≤ H[fun p : Fin n × (A × A₁) × B × B₁ => p.2.2 | fun p => p.2.1.2 ;
          ρ.toMeasure] := a5
    rw [a4] at a5'
    linarith

end Mixture

namespace Relay

variable {A A₁ B B₁ : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype B] [Nonempty B]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype B₁] [Nonempty B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁]

omit [Nonempty B] [Nonempty B₁] in
theorem cutSetBound_nonneg (W : DMC (A × A₁) (B × B₁)) : 0 ≤ cutSetBound W :=
  Real.iSup_nonneg fun _ => le_min (mutualInfo_nonneg _ (measurable_of_finite _)
    (measurable_of_finite _)) (condMutualInfo_nonneg _ (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _))

theorem one_sub_mul_log_card_le {k n : ℕ} [NeZero k] [NeZero n] (W : DMC (A × A₁) (B × B₁))
    (c : RelayCode (Fin k) A A₁ B B₁ n) :
    (1 - (c.avgError W).toReal) * Real.log k ≤ n * cutSetBound W + Real.log 2 := by
  classical
  have d : B × B₁ := Classical.arbitrary _
  set μ := (c.codePMF W).toMeasure
  have hk : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne k))
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hH : H[fun ω : Fin k × (Fin n → B × B₁) => ω.1 ; μ] = Real.log k := by
    have := entropy_eq_log_card μ (X := fun ω : Fin k × (Fin n → B × B₁) => ω.1) fun m => by
      rw [PMF.toMeasure_map _ _ (measurable_of_finite _), measureReal_def,
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.map_apply,
        tsum_fintype, Fintype.sum_prod_type, Finset.sum_eq_single m (fun b _ hb => by
          simp [Ne.symm hb]) (by simp)]
      simp only [ite_true, RelayCode.codePMF, PMF.ofFintype_apply, ← Finset.mul_sum,
        RelayCode.sum_seqProb, mul_one, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    simpa using this
  have hF := condEntropy_le_log_two_add_mul_log_card (μ := μ)
    (X := fun ω : Fin k × (Fin n → B × B₁) => ω.1) (Y := fun ω j => (ω.2 j).1)
    (measurable_of_finite _) (measurable_of_finite _) c.dec
  rw [RelayCode.measureReal_dec_ne, Fintype.card_fin] at hF
  have hI := mutualInfo_eq_entropy_sub_condEntropy
    (fun ω : Fin k × (Fin n → B × B₁) => ω.1) (fun ω j => (ω.2 j).1) μ
  have h1 := RelayCode.mutualInfo_le_sum₁ c W d
  have h2 := RelayCode.mutualInfo_le_sum₂ c W d
  obtain ⟨m1, m2⟩ := cutSet_mixture W (fun i => c.letterLaw W i d)
  set pm := (DMC.jointPMF (fun i => c.letterLaw W i d) (BC.unifPMF n)).map Prod.snd
  have hle : cutSetRate W pm ≤ cutSetBound W :=
    le_ciSup ⟨_, Set.forall_mem_range.2 (cutSetRate_le_log_card W)⟩ pm
  rw [← div_eq_inv_mul, div_le_iff₀ hn] at m1 m2
  have hmin : I[fun ω : Fin k × (Fin n → B × B₁) => ω.1 : fun ω j => (ω.2 j).1 ; μ] ≤
      n * cutSetRate W pm := by
    rw [cutSetRate, mul_min_of_nonneg _ _ hn.le]
    exact le_min (h1.trans (by linarith)) (h2.trans (by linarith))
  have := mul_le_mul_of_nonneg_left hle hn.le
  have e : (1 - (c.avgError W).toReal) * Real.log k =
      Real.log k - (c.avgError W).toReal * Real.log k := by ring
  linarith

theorem le_cutSetBound_of_achievable (W : DMC (A × A₁) (B × B₁)) {R : ℝ} (h : Achievable W R) :
    R ≤ cutSetBound W := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hC := cutSetBound_nonneg W
  set C := cutSetBound W
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
  obtain ⟨n, hNn, hn0n, hn1⟩ : ∃ n : ℕ, N ≤ n ∧ n0 ≤ n ∧ 1 ≤ n :=
    ⟨max N (max n0 1), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hNn
  have hn : 2 * Real.log 2 < n * δ := by
    rw [← div_lt_iff₀ hδ0]
    exact hn0.trans_le (by exact_mod_cast hn0n)
  have hk0 : (0 : ℝ) < k := (Real.exp_pos _).trans_le hk
  have : NeZero k := ⟨by exact_mod_cast hk0.ne'⟩
  have : NeZero n := ⟨by omega⟩
  have key := one_sub_mul_log_card_le W c
  have hPe : (c.avgError W).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1 : (1 - e) * Real.log k ≤ n * C + Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)).trans key
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

theorem closure_achievableRates_subset (W : DMC (A × A₁) (B × B₁)) :
    closure (achievableRates W) ⊆ Set.Icc 0 (cutSetBound W) :=
  closure_minimal (fun _ hR => ⟨hR.1, le_cutSetBound_of_achievable W hR.2⟩) isClosed_Icc

theorem closure_achievableRates_subset_of_isDegraded {W : DMC (A × A₁) (B × B₁)}
    (h : IsDegraded W) : closure (achievableRates W) ⊆ Set.Icc 0 (decodeForwardBound W) := by
  rw [← cutSetBound_eq_decodeForwardBound h]
  exact closure_achievableRates_subset W

end Relay

end Meat
