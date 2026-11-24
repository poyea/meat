import Meat.Open.RelayConverse

open MeasureTheory
open scoped ENNReal

namespace Meat


namespace DMN

variable {V M A B : Type*}

structure Code (V M A B : Type*) (s d : V) (n : ℕ) where
  node : V → Fin n → M → (Fin n → B) → A
  msgFree : ∀ v, v ≠ s → ∀ i m m' y, node v i m y = node v i m' y
  causal : ∀ v i m y y', (∀ j : Fin n, j < i → y j = y' j) → node v i m y = node v i m y'
  dec : (Fin n → B) → M

namespace Code

variable {s d : V} {n : ℕ}

def input (c : Code V M A B s d n) (m : M) (i : Fin n) (z : Fin n → V → B) : V → A :=
  fun v => c.node v i m fun j => z j v

theorem isCausal (c : Code V M A B s d n) : Causal.IsCausal c.input := by
  intro m i z z' h
  funext v
  exact c.causal v i m _ _ fun j hj => by rw [h j hj]

noncomputable def errorProb [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq M]
    (c : Code V M A B s d n) (W : DMC (V → A) (V → B)) (m : M) : ℝ≥0∞ :=
  ∑ z : Fin n → V → B, if c.dec (fun j => z j d) = m then 0 else Causal.seqProb W c.input m z

noncomputable def avgError [Fintype V] [DecidableEq V] [Fintype B] [Fintype M] [DecidableEq M]
    (c : Code V M A B s d n) (W : DMC (V → A) (V → B)) : ℝ≥0∞ :=
  (∑ m, c.errorProb W m) / (Fintype.card M : ℝ≥0∞)

end Code

def Achievable [Fintype V] [DecidableEq V] [Fintype B] (W : DMC (V → A) (V → B)) (s d : V)
    (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : Code V (Fin k) A B s d n, c.avgError W ≤ ε

def achievableRates [Fintype V] [DecidableEq V] [Fintype B] (W : DMC (V → A) (V → B))
    (s d : V) : Set ℝ :=
  {R | 0 ≤ R ∧ Achievable W s d R}

section Rates

variable [Fintype V] [DecidableEq V] [Fintype A] [MeasurableSpace A] [Fintype B]
  [MeasurableSpace B]

noncomputable def cutRate (W : DMC (V → A) (V → B)) (p : PMF (V → A)) (S : Finset V) : ℝ :=
  I[fun ω : (V → A) × (V → B) => fun v : ↥S => ω.1 v : fun ω => fun v : ↥Sᶜ => ω.2 v |
    fun ω => fun v : ↥Sᶜ => ω.1 v ; W.jointMeasure p]

noncomputable def cutSetBound (W : DMC (V → A) (V → B)) (s d : V) : ℝ :=
  ⨆ p : PMF (V → A), ⨅ S : {S : Finset V // s ∈ S ∧ d ∉ S}, cutRate W p S.1

end Rates

end DMN

namespace DMN

variable {V M A B : Type*} [Fintype V] [DecidableEq V] [Fintype M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Fintype B] [Nonempty B] [MeasurableSpace B]
  [MeasurableSingletonClass B] {s d : V} {n : ℕ}

omit [Nonempty B] in
theorem cutRate_eq (W : DMC (V → A) (V → B)) (p : PMF (V → A)) (S : Finset V) :
    cutRate W p S =
      H[fun ω : (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2 v | fun ω => fun v : ↥Sᶜ => ω.1 v ;
        W.jointMeasure p] -
      H[fun ω : (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2 v | fun ω => ω.1 ; W.jointMeasure p] := by
  rw [cutRate, condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  refine condEntropy_cond_of_injective _ (Z := fun ω : (V → A) × (V → B) => ω.1)
    (e := fun x => (fun v : ↥S => x v, fun v : ↥Sᶜ => x v)) (fun x y h => ?_) fun _ => rfl
  simp only [Prod.mk.injEq] at h
  funext v
  by_cases hv : v ∈ S
  · exact congrFun h.1 ⟨v, hv⟩
  · exact congrFun h.2 ⟨v, Finset.mem_compl.2 hv⟩

theorem mutualInfo_le_sum_cut (c : Code V M A B s d n) (W : DMC (V → A) (V → B)) (b₀ : V → B)
    {S : Finset V} (hs : s ∈ S) (hd : d ∉ S) :
    I[fun ω : M × (Fin n → V → B) => ω.1 : fun ω j => ω.2 j d ;
        (Causal.codePMF W c.isCausal).toMeasure] ≤
      ∑ i, cutRate W (Causal.letterLaw W c.isCausal i b₀) S := by
  classical
  set μ := (Causal.codePMF W c.isCausal).toMeasure
  have hdS : d ∈ Sᶜ := Finset.mem_compl.2 hd
  have m₀ : M := Classical.arbitrary M
  have h0 := mutualInfo_comp_le μ (X := fun ω : M × (Fin n → V → B) => ω.1)
    (Y := fun ω j (v : ↥Sᶜ) => ω.2 j v) (measurable_of_finite _) (measurable_of_finite _)
    (fun z : Fin n → ↥Sᶜ → B => fun j => z j ⟨d, hdS⟩)
  refine le_trans h0 ?_
  rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
  have h1 := entropy_eq_sum μ (fun ω : M × (Fin n → V → B) => fun j (v : ↥Sᶜ) => ω.2 j v)
  have h3 := condEntropy_eq_sum μ (fun ω : M × (Fin n → V → B) => fun j (v : ↥Sᶜ) => ω.2 j v)
    (fun ω => ω.1)
  have h2 : ∀ i, H[fun ω : M × (Fin n → V → B) => fun v : ↥Sᶜ => ω.2 i v |
      fun ω => seqPrefix (fun j (v : ↥Sᶜ) => ω.2 j v) i ; μ] ≤
      H[fun ω : M × (Fin n → V → B) => fun v : ↥Sᶜ => ω.2 i v |
        fun ω => fun v : ↥Sᶜ => c.input ω.1 i ω.2 v ; μ] := fun i => by
    have h := condEntropy_le_condEntropy_comp (μ := μ)
      (X := fun ω : M × (Fin n → V → B) => fun v : ↥Sᶜ => ω.2 i v)
      (Y := fun ω => seqPrefix (fun j (v : ↥Sᶜ) => ω.2 j v) i) (measurable_of_finite _)
      (measurable_of_finite _) fun p (v : ↥Sᶜ) =>
        c.node v i m₀ fun j => if hj : (j : ℕ) < i then p ⟨j, hj⟩ v else b₀ v
    have e : ((fun p : Fin i → ↥Sᶜ → B => fun v : ↥Sᶜ =>
        c.node v i m₀ fun j => if hj : (j : ℕ) < i then p ⟨j, hj⟩ v else b₀ v) ∘
        fun ω : M × (Fin n → V → B) => seqPrefix (fun j (v : ↥Sᶜ) => ω.2 j v) i) =
        fun ω => fun v : ↥Sᶜ => c.input ω.1 i ω.2 v := by
      funext ω v
      have hvs : (v : V) ≠ s := fun h => (Finset.mem_compl.1 v.2) (h ▸ hs)
      simp only [Function.comp_apply, Code.input]
      rw [c.msgFree v hvs i ω.1 m₀]
      exact c.causal v i m₀ _ _ fun j hj => by
        simp [seqPrefix, show (j : ℕ) < i from hj]
    rwa [e] at h
  have h4 : ∀ i, H[fun ω : M × (Fin n → V → B) => fun v : ↥Sᶜ => ω.2 i v |
      fun ω => (ω.1, BC.padPrefix ω.2 i b₀) ; μ] ≤
      H[fun ω : M × (Fin n → V → B) => fun v : ↥Sᶜ => ω.2 i v |
        fun ω => (ω.1, seqPrefix (fun j (v : ↥Sᶜ) => ω.2 j v) i) ; μ] := fun i => by
    rw [← BC.condEntropy_seq_pad μ (fun m => m) _ i b₀]
    exact condEntropy_le_condEntropy_comp (μ := μ) (measurable_of_finite _)
      (measurable_of_finite _) fun p : M × (Fin i → V → B) => (p.1, fun j (v : ↥Sᶜ) => p.2 j v)
  have h5 : ∀ i, H[fun ω : M × (Fin n → V → B) => fun v : ↥Sᶜ => ω.2 i v |
      fun ω => (ω.1, BC.padPrefix ω.2 i b₀) ; μ] =
      H[fun ω : (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2 v | fun ω => ω.1 ;
        W.jointMeasure (Causal.letterLaw W c.isCausal i b₀)] := fun i =>
    Causal.condEntropy_letter W c.isCausal i b₀ fun y (v : ↥Sᶜ) => y v
  have h6 : ∀ i, H[fun ω : M × (Fin n → V → B) => fun v : ↥Sᶜ => ω.2 i v |
      fun ω => fun v : ↥Sᶜ => c.input ω.1 i ω.2 v ; μ] =
      H[fun ω : (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2 v | fun ω => fun v : ↥Sᶜ => ω.1 v ;
        W.jointMeasure (Causal.letterLaw W c.isCausal i b₀)] := fun i => by
    rw [← Causal.map_codePMF_input W c.isCausal i b₀,
      condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _)
        (measurable_of_finite _)]
    rfl
  simp_rw [cutRate_eq, Finset.sum_sub_distrib]
  have s2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
  have s4 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h4 i
  simp only [h6] at s2
  simp only [h5] at s4
  linarith

end DMN

namespace DMN

variable {V A B : Type*} [Fintype V] [DecidableEq V] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  {n : ℕ} [NeZero n]

theorem cutRate_mixture (W : DMC (V → A) (V → B)) (p : Fin n → PMF (V → A)) (S : Finset V) :
    (n : ℝ)⁻¹ * ∑ q, cutRate W (p q) S ≤
      cutRate W ((DMC.jointPMF p (BC.unifPMF n)).map Prod.snd) S := by
  set L : Fin n → PMF ((V → A) × (V → B)) := fun q => DMC.jointPMF W (p q)
  set ρ := DMC.jointPMF L (BC.unifPMF n)
  have hsnd : W.jointMeasure ((DMC.jointPMF p (BC.unifPMF n)).map Prod.snd) =
      ρ.toMeasure.map Prod.snd := by
    rw [DMC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ measurable_snd]
    congr 1
    simp only [ρ, L, DMC.jointPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def,
      PMF.bind_bind]
  have hm : MarkovChain (fun ω : Fin n × (V → A) × (V → B) => ω.1) (fun ω => ω.2.1)
      (fun ω => ω.2.2) ρ.toMeasure := by
    refine BC.markovChain_of_pmf ρ _ _ _ (fun x z => W x z) fun q x z => ?_
    have h1 : ρ.map (fun ω : Fin n × (V → A) × (V → B) => (ω.1, ω.2.1, ω.2.2)) = ρ :=
      PMF.map_id ρ
    have h2 : ρ.map (fun ω : Fin n × (V → A) × (V → B) => (ω.1, ω.2.1)) =
        DMC.jointPMF p (BC.unifPMF n) := by
      have hc : ∀ (q : Fin n) (a : V → A), (W a).map (fun _ => (q, a)) = PMF.pure (q, a) :=
        fun q a => PMF.map_const _ _
      simp only [ρ, L, DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def, hc]
      rfl
    rw [h1, h2, DMC.jointPMF_apply, DMC.jointPMF_apply, DMC.jointPMF_apply, mul_assoc]
  rw [markovChain_def] at hm
  have hmY : I[fun ω : Fin n × (V → A) × (V → B) => ω.1 :
      fun ω => fun v : ↥Sᶜ => ω.2.2 v | fun ω => ω.2.1 ; ρ.toMeasure] = 0 := by
    have h := condMutualInfo_comp_right_le (μ := ρ.toMeasure)
      (X := fun ω : Fin n × (V → A) × (V → B) => ω.1) (Y := fun ω => ω.2.2)
      (Z := fun ω => ω.2.1) (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) fun y (v : ↥Sᶜ) => y v
    rw [hm] at h
    exact le_antisymm h (condMutualInfo_nonneg _ (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _))
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy] at hmY
  rw [cutRate_eq, hsnd, condEntropy_map _ measurable_snd (measurable_of_finite _)
      (measurable_of_finite _),
    condEntropy_map _ measurable_snd (measurable_of_finite _) (measurable_of_finite _)]
  have a3 := BC.condEntropy_mixture L (fun r : (V → A) × (V → B) => fun v : ↥Sᶜ => r.2 v)
    (fun r => r.1)
  have a4 := BC.condEntropy_mixture L (fun r : (V → A) × (V → B) => fun v : ↥Sᶜ => r.2 v)
    (fun r => fun v : ↥Sᶜ => r.1 v)
  have a5 := condEntropy_le_condEntropy_comp (μ := ρ.toMeasure)
    (X := fun ω : Fin n × (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2.2 v)
    (Y := fun ω => (ω.1, fun v : ↥Sᶜ => ω.2.1 v))
    (measurable_of_finite _) (measurable_of_finite _) Prod.snd
  have e : ∑ q, cutRate W (p q) S =
      ∑ q, H[fun r : (V → A) × (V → B) => fun v : ↥Sᶜ => r.2 v |
        fun r => fun v : ↥Sᶜ => r.1 v ; (L q).toMeasure] -
      ∑ q, H[fun r : (V → A) × (V → B) => fun v : ↥Sᶜ => r.2 v | fun r => r.1 ;
        (L q).toMeasure] := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => cutRate_eq W (p q) S
  rw [e, mul_sub]
  change _ ≤ H[fun ω : Fin n × (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2.2 v |
      fun ω => fun v : ↥Sᶜ => ω.2.1 v ; ρ.toMeasure] -
    H[fun ω : Fin n × (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2.2 v | fun ω => ω.2.1 ;
      ρ.toMeasure]
  have : H[fun ω : Fin n × (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2.2 v | fun ω => ω.2.1 ;
      ρ.toMeasure] = H[fun ω : Fin n × (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2.2 v |
        fun ω => (ω.1, ω.2.1) ; ρ.toMeasure] := by linarith
  rw [this, a3]
  have a5' : H[fun ω : Fin n × (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2.2 v |
      fun ω => (ω.1, fun v : ↥Sᶜ => ω.2.1 v) ; ρ.toMeasure] ≤
      H[fun ω : Fin n × (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2.2 v |
        fun ω => fun v : ↥Sᶜ => ω.2.1 v ; ρ.toMeasure] := a5
  rw [a4] at a5'
  linarith

end DMN

namespace DMN

variable {V A B : Type*} [Fintype V] [DecidableEq V] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Fintype B] [Nonempty B] [MeasurableSpace B]
  [MeasurableSingletonClass B] {s d : V}

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem measureReal_dec_ne {M : Type*} [Fintype M] [Nonempty M] [DecidableEq M]
    [MeasurableSpace M] [MeasurableSingletonClass M] {n : ℕ} (c : Code V M A B s d n)
    (W : DMC (V → A) (V → B)) :
    (Causal.codePMF W c.isCausal).toMeasure.real {ω | c.dec (fun j => ω.2 j d) ≠ ω.1} =
      (c.avgError W).toReal := by
  rw [measureReal_def, PMF.toMeasure_apply_fintype, Code.avgError, div_eq_mul_inv, mul_comm,
    Finset.mul_sum, Fintype.sum_prod_type]
  refine congrArg ENNReal.toReal (Finset.sum_congr rfl fun m _ => ?_)
  rw [Code.errorProb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : c.dec (fun j => y j d) = m <;> simp [Set.indicator, h, Causal.codePMF]

omit [Nonempty B] in
theorem cutRate_nonneg (W : DMC (V → A) (V → B)) (p : PMF (V → A)) (S : Finset V) :
    0 ≤ cutRate W p S :=
  condMutualInfo_nonneg _ (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _)

omit [Nonempty B] in
theorem cutRate_le_log_card (W : DMC (V → A) (V → B)) (p : PMF (V → A)) (S : Finset V) :
    cutRate W p S ≤ Real.log (Fintype.card (↥Sᶜ → B)) := by
  rw [cutRate_eq]
  have h1 := condEntropy_nonneg (W.jointMeasure p)
    (X := fun ω : (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2 v) (Y := fun ω => ω.1)
    (measurable_of_finite _) (measurable_of_finite _)
  have h2 := condEntropy_le_entropy (W.jointMeasure p)
    (X := fun ω : (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2 v) (Y := fun ω => fun v : ↥Sᶜ => ω.1 v)
    (measurable_of_finite _) (measurable_of_finite _)
  have h3 := entropy_le_log_card (W.jointMeasure p)
    (X := fun ω : (V → A) × (V → B) => fun v : ↥Sᶜ => ω.2 v)
  linarith

omit [Nonempty B] in
theorem cutSetBound_nonneg (W : DMC (V → A) (V → B)) : 0 ≤ cutSetBound W s d :=
  Real.iSup_nonneg fun p => Real.iInf_nonneg fun S => cutRate_nonneg W p S.1

theorem one_sub_mul_log_card_le {k n : ℕ} [NeZero k] [NeZero n] (hsd : s ≠ d)
    (W : DMC (V → A) (V → B)) (c : Code V (Fin k) A B s d n) :
    (1 - (c.avgError W).toReal) * Real.log k ≤ n * cutSetBound W s d + Real.log 2 := by
  classical
  have b₀ : V → B := fun _ => Classical.arbitrary B
  set μ := (Causal.codePMF W c.isCausal).toMeasure
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hH : H[fun ω : Fin k × (Fin n → V → B) => ω.1 ; μ] = Real.log k := by
    have := entropy_eq_log_card μ (X := fun ω : Fin k × (Fin n → V → B) => ω.1) fun m => by
      rw [PMF.toMeasure_map _ _ (measurable_of_finite _), measureReal_def,
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.map_apply,
        tsum_fintype, Fintype.sum_prod_type, Finset.sum_eq_single m (fun b _ hb => by
          simp [Ne.symm hb]) (by simp)]
      simp only [ite_true, Causal.codePMF, PMF.ofFintype_apply, ← Finset.mul_sum,
        Causal.sum_seqProb W c.isCausal, mul_one, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    simpa using this
  have hF := condEntropy_le_log_two_add_mul_log_card (μ := μ)
    (X := fun ω : Fin k × (Fin n → V → B) => ω.1) (Y := fun ω j => ω.2 j d)
    (measurable_of_finite _) (measurable_of_finite _) c.dec
  rw [measureReal_dec_ne, Fintype.card_fin] at hF
  have hI := mutualInfo_eq_entropy_sub_condEntropy
    (fun ω : Fin k × (Fin n → V → B) => ω.1) (fun ω j => ω.2 j d) μ
  set pm := (DMC.jointPMF (fun i => Causal.letterLaw W c.isCausal i b₀) (BC.unifPMF n)).map
    Prod.snd
  have hcut : ∀ S : {S : Finset V // s ∈ S ∧ d ∉ S},
      I[fun ω : Fin k × (Fin n → V → B) => ω.1 : fun ω j => ω.2 j d ; μ] / n ≤
        cutRate W pm S.1 := fun S => by
    have h1 := mutualInfo_le_sum_cut c W b₀ S.2.1 S.2.2
    have h2 := cutRate_mixture W (fun i => Causal.letterLaw W c.isCausal i b₀) S.1
    rw [div_le_iff₀ hn]
    rw [← div_eq_inv_mul, div_le_iff₀ hn] at h2
    linarith
  have hne : Nonempty {S : Finset V // s ∈ S ∧ d ∉ S} :=
    ⟨⟨{s}, Finset.mem_singleton_self s, fun h => hsd (Finset.mem_singleton.1 h).symm⟩⟩
  have hinf := le_ciInf hcut
  have hle : (⨅ S : {S : Finset V // s ∈ S ∧ d ∉ S}, cutRate W pm S.1) ≤ cutSetBound W s d := by
    refine le_ciSup (f := fun p : PMF (V → A) =>
      ⨅ S : {S : Finset V // s ∈ S ∧ d ∉ S}, cutRate W p S.1)
      ⟨Real.log (Fintype.card (↥hne.some.1ᶜ → B)), ?_⟩ pm
    rintro _ ⟨p, rfl⟩
    exact (ciInf_le ⟨0, by rintro _ ⟨S, rfl⟩; exact cutRate_nonneg W p S.1⟩ hne.some).trans
      (cutRate_le_log_card W p hne.some.1)
  rw [div_le_iff₀ hn] at hinf
  have e : (1 - (c.avgError W).toReal) * Real.log k =
      Real.log k - (c.avgError W).toReal * Real.log k := by ring
  nlinarith

theorem le_cutSetBound_of_achievable (hsd : s ≠ d) (W : DMC (V → A) (V → B)) {R : ℝ}
    (h : Achievable W s d R) : R ≤ cutSetBound W s d := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hC := cutSetBound_nonneg (s := s) (d := d) W
  set C := cutSetBound W s d
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
  have key := one_sub_mul_log_card_le hsd W c
  have hPe : (c.avgError W).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1 : (1 - e) * Real.log k ≤ n * C + Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)).trans key
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

theorem closure_achievableRates_subset (hsd : s ≠ d) (W : DMC (V → A) (V → B)) :
    closure (achievableRates W s d) ⊆ Set.Icc 0 (cutSetBound W s d) :=
  closure_minimal (fun _ hR => ⟨hR.1, le_cutSetBound_of_achievable hsd W hR.2⟩) isClosed_Icc

end DMN

end Meat
