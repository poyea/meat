import Meat.Shannon.Fano
import Meat.Source.TimeSharing

open MeasureTheory Finset Filter Topology
open scoped ENNReal

namespace Meat

structure HelperCode (S T : Type*) (n k₁ k₂ : ℕ) where
  enc : (Fin n → S) → Fin k₁
  help : (Fin n → T) → Fin k₂
  dec : Fin k₁ × Fin k₂ → Fin n → S

noncomputable def HelperCode.errorProb {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S]
    {n k₁ k₂ : ℕ} (c : HelperCode S T n k₁ k₂) (p : PMF (S × T)) : ℝ :=
  ∑ ω : Fin n → S × T, iidProb p ω *
    if c.dec (c.enc fun i => (ω i).1, c.help fun i => (ω i).2) = (fun i => (ω i).1) then 0
    else 1

namespace Helper

section Defs

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S]

def Achievable (p : PMF (S × T)) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k₁ k₂ : ℕ, (k₁ : ℝ) ≤ Real.exp (n * R₁) ∧ (k₂ : ℝ) ≤ Real.exp (n * R₂) ∧
      ∃ c : HelperCode S T n k₁ k₂, c.errorProb p ≤ ε

def achievableRegion (p : PMF (S × T)) : Set (ℝ × ℝ) :=
  {x | Achievable p x.1 x.2}

variable [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T]

noncomputable def rateRegion (p : PMF (S × T)) : Set (ℝ × ℝ) :=
  {x | ∃ m : ℕ, ∃ q : PMF (T × S × Fin m),
    q.map (fun a => (a.2.1, a.1)) = p ∧
    MarkovChain (fun a : T × S × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1) q.toMeasure ∧
    H[fun a : T × S × Fin m => a.2.1 | fun a => a.2.2 ; q.toMeasure] ≤ x.1 ∧
    I[fun a : T × S × Fin m => a.1 : fun a => a.2.2 ; q.toMeasure] ≤ x.2}

end Defs

open RateDistortion

@[instance_reducible]
private def optMS (α : Type*) : MeasurableSpace (Option α) := ⊤

attribute [local instance] optMS

private lemma optMSC (α : Type*) : MeasurableSingletonClass (Option α) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

attribute [local instance] optMSC

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {n k₁ k₂ : ℕ}

private def msgY (c : HelperCode S T n k₁ k₂) (ω : Fin n → S × T) : Fin k₂ :=
  c.help fun j => (ω j).2

private def maskX (i : Fin n) (ω : Fin n → S × T) : Fin n → Option S :=
  fun j => if j < i then some (ω j).1 else none

private def auxH (c : HelperCode S T n k₁ k₂) (i : Fin n) (ω : Fin n → S × T) :
    Fin k₂ × (Fin n → Option S) :=
  (msgY c ω, maskX i ω)

private lemma map_snd_eval (p : PMF (S × T)) (i : Fin n) :
    (iidMeasure p n).map (fun ω : Fin n → S × T => (ω i).2) = p.toMeasure.map Prod.snd := by
  rw [← map_eval_iidMeasure p i, Measure.map_map measurable_snd (measurable_of_finite _)]
  rfl

private lemma real_error [DecidableEq S] (p : PMF (S × T)) (c : HelperCode S T n k₁ k₂) :
    (iidMeasure p n).real {ω | c.dec (c.enc (fun j => (ω j).1), msgY c ω) ≠
      fun j => (ω j).1} = c.errorProb p := by
  rw [measureReal_def, iidMeasure, PMF.toMeasure_apply_fintype, ENNReal.toReal_sum fun _ _ =>
    ne_top_of_le_ne_top (PMF.apply_ne_top _ _) (Set.indicator_le_self _ _ _),
    HelperCode.errorProb]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : c.dec (c.enc (fun j => (ω j).1), msgY c ω) = fun j => (ω j).1
  · simp only [msgY] at h
    simp [Set.indicator, h, msgY]
  · simp only [msgY] at h
    simp [Set.indicator, h, msgY, PMF.ofFintype_apply, ENNReal.toReal_prod, iidProb]

omit [MeasurableSingletonClass T] in
private lemma condEntropy_letter_eq (c : HelperCode S T n k₁ k₂) (p : PMF (S × T)) (i : Fin n) :
    H[fun ω : Fin n → S × T => (ω i).1 |
      fun ω => (msgY c ω, seqPrefix (fun j => (ω j).1) i) ; iidMeasure p n] =
      H[fun ω : Fin n → S × T => (ω i).1 | auxH c i ; iidMeasure p n] := by
  refine (condEntropy_cond_of_injective _ (Z := fun ω => (msgY c ω,
    seqPrefix (fun j => (ω j).1) i))
    (e := fun q : Fin k₂ × (Fin i → S) => (q.1, fun j : Fin n =>
      if h : j < i then some (q.2 ⟨j, h⟩) else none)) (fun a b h => ?_) fun ω => ?_).symm
  · simp only [Prod.mk.injEq] at h
    refine Prod.ext h.1 (funext fun j => ?_)
    have := congrFun h.2 ⟨j, j.2.trans i.2⟩
    have hj : (⟨j, j.2.trans i.2⟩ : Fin n) < i := j.2
    simp only [hj, dite_true, Option.some.injEq] at this
    exact this
  · refine Prod.ext rfl (funext fun j => ?_)
    by_cases h : j < i
    · simp [auxH, maskX, h, seqPrefix]
    · simp [auxH, maskX, h]

private lemma sum_condEntropy_X_le [DecidableEq S] (c : HelperCode S T n k₁ k₂)
    (p : PMF (S × T)) :
    ∑ i, H[fun ω : Fin n → S × T => (ω i).1 | auxH c i ; iidMeasure p n] ≤
      Real.log k₁ + Real.log 2 + c.errorProb p * (n * Real.log (Fintype.card S)) := by
  set μ := iidMeasure p n
  set X : (Fin n → S × T) → Fin n → S := fun ω j => (ω j).1
  have hchain : H[X | msgY c ; μ] =
      ∑ i, H[fun ω : Fin n → S × T => (ω i).1 | auxH c i ; iidMeasure p n] :=
    (condEntropy_eq_sum μ X (msgY c)).trans (sum_congr rfl fun i _ => condEntropy_letter_eq c p i)
  rw [← hchain]
  have hF := condEntropy_le_log_two_add_mul_log_card (μ := μ) (X := X)
    (Y := fun ω => (c.enc (X ω), msgY c ω)) (measurable_of_finite _) (measurable_of_finite _)
    c.dec
  rw [real_error, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] at hF
  have h1 : H[fun ω => (X ω, (c.enc (X ω), msgY c ω)) ; μ] = H[fun ω => (X ω, msgY c ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, msgY c ω))
      (f := fun q => (q.1, (c.enc q.1, q.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 h.2.2
  have h2 := entropy_pair_le_add μ (X := fun ω => c.enc (X ω)) (Y := msgY c)
    (measurable_of_finite _) (measurable_of_finite _)
  have h3 := entropy_le_log_card μ (X := fun ω => c.enc (X ω))
  rw [Fintype.card_fin] at h3
  rw [condEntropy_def, h1] at hF
  rw [condEntropy_def]
  linarith

private lemma condEntropy_pair_le (c : HelperCode S T n k₁ k₂) (p : PMF (S × T)) (i : Fin n) :
    H[fun ω : Fin n → S × T => ω i | auxH c i ; iidMeasure p n] ≤
      H[fun ω : Fin n → S × T => (ω i).2 | auxH c i ; iidMeasure p n] +
        H[fun ω : Fin n → S × T => (ω i).1 | fun ω => (ω i).2 ; iidMeasure p n] := by
  set μ := iidMeasure p n
  have e1 : H[fun ω : Fin n → S × T => ((ω i).2, (ω i).1) | auxH c i ; μ] =
      H[fun ω : Fin n → S × T => ω i | auxH c i ; μ] :=
    condEntropy_comp_of_injective μ (X := fun ω : Fin n → S × T => ω i) Prod.swap_injective
  have e2 := condEntropy_pair_eq_add μ (X := fun ω : Fin n → S × T => (ω i).2)
    (Y := fun ω => (ω i).1) (Z := auxH c i)
  have e3 := condEntropy_le_condEntropy_comp (μ := μ)
    (X := fun ω : Fin n → S × T => (ω i).1) (measurable_of_finite _)
    (measurable_of_finite fun ω : Fin n → S × T => ((ω i).2, auxH c i ω))
    (Prod.fst : T × (Fin k₂ × (Fin n → Option S)) → T)
  have e4 : (Prod.fst : T × (Fin k₂ × (Fin n → Option S)) → T) ∘
      (fun ω : Fin n → S × T => ((ω i).2, auxH c i ω)) = fun ω => (ω i).2 := rfl
  rw [e4] at e3
  linarith

private lemma condEntropy_seq_le (c : HelperCode S T n k₁ k₂) (p : PMF (S × T)) (i : Fin n) :
    H[fun ω : Fin n → S × T => ω i |
      fun ω => (msgY c ω, seqPrefix ω i) ; iidMeasure p n] ≤
      H[fun ω : Fin n → S × T => ω i | auxH c i ; iidMeasure p n] := by
  have h := condEntropy_le_condEntropy_comp (μ := iidMeasure p n)
    (X := fun ω : Fin n → S × T => ω i) (measurable_of_finite _)
    (measurable_of_finite fun ω : Fin n → S × T => (msgY c ω, seqPrefix ω i))
    (fun q : Fin k₂ × (Fin i → S × T) => (q.1, fun j : Fin n =>
      if h : j < i then some (q.2 ⟨j, h⟩).1 else none))
  have e : ((fun q : Fin k₂ × (Fin i → S × T) => (q.1, fun j : Fin n =>
      if h : j < i then some (q.2 ⟨j, h⟩).1 else none)) ∘
      fun ω : Fin n → S × T => (msgY c ω, seqPrefix ω i)) = auxH c i := by
    funext ω
    refine Prod.ext rfl (funext fun j => ?_)
    by_cases h : j < i
    · simp [auxH, maskX, h, seqPrefix]
    · simp [auxH, maskX, h]
  rw [e] at h
  exact h

private lemma sum_info_Y_le (c : HelperCode S T n k₁ k₂) (p : PMF (S × T)) :
    ∑ i, (H[fun ω : Fin n → S × T => (ω i).2 ; iidMeasure p n] -
      H[fun ω : Fin n → S × T => (ω i).2 | auxH c i ; iidMeasure p n]) ≤ Real.log k₂ := by
  set μ := iidMeasure p n
  have hchain := condEntropy_eq_sum μ (fun ω : Fin n → S × T => ω) (msgY c)
  have hsum : ∑ i, H[fun ω : Fin n → S × T => ω i ; μ] = H[fun ω => ω ; μ] := by
    simp only [entropy_eval_iidMeasure, entropy_iidMeasure, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, μ]
  have hpair : H[fun ω : Fin n → S × T => (ω, msgY c ω) ; μ] = H[fun ω => ω ; μ] :=
    entropy_pair_comp μ (X := fun ω : Fin n → S × T => ω) (msgY c)
  have hM := entropy_le_log_card μ (X := msgY c)
  rw [Fintype.card_fin] at hM
  have hi : ∀ i, H[fun ω : Fin n → S × T => ω i ; μ] =
      H[fun ω : Fin n → S × T => (ω i).2 ; μ] +
        H[fun ω : Fin n → S × T => (ω i).1 | fun ω => (ω i).2 ; μ] := fun i => by
    rw [condEntropy_def]
    ring
  have hle := sum_le_sum fun i (_ : i ∈ univ) =>
    (condEntropy_seq_le c p i).trans (condEntropy_pair_le c p i)
  rw [condEntropy_def, hpair] at hchain
  simp only [hi, sum_add_distrib] at hsum
  rw [sum_add_distrib, ← hchain] at hle
  rw [sum_sub_distrib]
  linarith

private lemma markov_letter (c : HelperCode S T n k₁ k₂) (p : PMF (S × T)) (i : Fin n) :
    MarkovChain (auxH c i) (fun ω : Fin n → S × T => (ω i).2) (fun ω => (ω i).1)
      (iidMeasure p n) := by
  classical
  refine markovChain_of_indep _ (R := fun ω : Fin n → S × T => fun j : {j // j ≠ i} => ω j)
    (fun y ρ => (c.help (fun j => if h : j = i then y else (ρ ⟨j, h⟩).2),
      fun j => if h : j < i then some (ρ ⟨j, ne_of_lt h⟩).1 else none))
    (fun ω => ?_) (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _) ?_
  · refine Prod.ext (congrArg c.help (funext fun j => ?_)) (funext fun j => ?_)
    · by_cases h : j = i
      · subst h
        simp
      · simp [h]
    · by_cases h : j < i
      · simp [auxH, maskX, h]
      · simp [auxH, maskX, h]
  · have h := mutualInfo_comp_right_of_injective (iidMeasure p n)
      (X := fun ω : Fin n → S × T => fun j : {j // j ≠ i} => ω j) (Y := fun ω => ω i)
      Prod.swap_injective
    rw [mutualInfo_rest_iidMeasure] at h
    exact h

private abbrev AuxH (n k₂ : ℕ) (S : Type*) := Fin n × (Fin k₂ × (Fin n → Option S))

private noncomputable def tsMap (c : HelperCode S T n k₁ k₂) (x : Fin n × (Fin n → S × T)) :
    T × S × Fin (Fintype.card (AuxH n k₂ S)) :=
  ((x.2 x.1).2, (x.2 x.1).1, Fintype.equivFin _ (x.1, auxH c x.1 x.2))

private noncomputable def tsPMF (p : PMF (S × T)) (hn : 0 < n) (c : HelperCode S T n k₁ k₂) :
    PMF (T × S × Fin (Fintype.card (AuxH n k₂ S))) :=
  (iidMix p hn).map (tsMap c)

private lemma tsPMF_toMeasure (p : PMF (S × T)) (hn : 0 < n) (c : HelperCode S T n k₁ k₂) :
    (tsPMF p hn c).toMeasure = (iidMix p hn).toMeasure.map (tsMap c) :=
  (PMF.toMeasure_map _ _ (measurable_of_finite _)).symm

private lemma ts_marginal (p : PMF (S × T)) (hn : 0 < n) (c : HelperCode S T n k₁ k₂) :
    (tsPMF p hn c).map (fun a => (a.2.1, a.1)) = p := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _), tsPMF_toMeasure,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  exact map_iidMix_const p hn (G := fun i ω => ω i) p.toMeasure fun i => map_eval_iidMeasure p i

private lemma ts_markov (p : PMF (S × T)) (hn : 0 < n) (c : HelperCode S T n k₁ k₂) :
    MarkovChain (fun a : T × S × Fin (Fintype.card (AuxH n k₂ S)) => a.2.2) (fun a => a.1)
      (fun a => a.2.1) (tsPMF p hn c).toMeasure := by
  set ν := (iidMix p hn).toMeasure
  set μ := iidMeasure p n
  set e₁ := Fintype.equivFin (AuxH n k₂ S)
  rw [markovChain_def, tsPMF_toMeasure, condMutualInfo_map _ (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  change I[fun x => e₁ (x.1, auxH c x.1 x.2) : fun x => (x.2 x.1).1 |
    fun x => (x.2 x.1).2 ; ν] = 0
  have h1 : H[fun x => (e₁ (x.1, auxH c x.1 x.2), (x.2 x.1).2) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => (auxH c i ω, (ω i).2) ; μ] :=
    entropy_iidMix p hn _ (fun q => (e₁ (q.1, q.2.1), q.2.2)) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)) (fun i ω => (auxH c i ω, (ω i).2))
      fun x => rfl
  have h2 : H[fun x : Fin n × (Fin n → S × T) => ((x.2 x.1).1, (x.2 x.1).2) ; ν] =
      measureEntropy p.toMeasure := by
    rw [entropy, map_iidMix_const p hn (G := fun i ω => ((ω i).1, (ω i).2)) _
      fun i => map_eval_iidMeasure p i]
  have h3 : H[fun x => ((e₁ (x.1, auxH c x.1 x.2), (x.2 x.1).1), (x.2 x.1).2) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => ((auxH c i ω, (ω i).1), (ω i).2) ; μ] :=
    entropy_iidMix p hn _ (fun q => ((e₁ (q.1, q.2.1.1), q.2.1.2), q.2.2)) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1.1 (Prod.ext (Prod.ext h.1.1.2 h.1.2) h.2))
      (fun i ω => ((auxH c i ω, (ω i).1), (ω i).2)) fun x => rfl
  have h4 : H[fun x : Fin n × (Fin n → S × T) => (x.2 x.1).2 ; ν] =
      measureEntropy (p.toMeasure.map Prod.snd) := by
    rw [entropy, map_iidMix_const p hn (G := fun i ω => (ω i).2) _ fun i => map_snd_eval p i]
  have hi : ∀ i, H[fun ω => (auxH c i ω, (ω i).2) ; μ] -
      H[fun ω => ((auxH c i ω, (ω i).1), (ω i).2) ; μ] =
      measureEntropy (p.toMeasure.map Prod.snd) - measureEntropy p.toMeasure :=
    fun i => by
      have hm := markov_letter c p i
      have hY : H[fun ω : Fin n → S × T => ((ω i).1, (ω i).2) ; μ] =
          measureEntropy p.toMeasure := by rw [entropy, ← map_eval_iidMeasure p i]
      have hX : H[fun ω : Fin n → S × T => (ω i).2 ; μ] =
          measureEntropy (p.toMeasure.map Prod.snd) := by rw [entropy, map_snd_eval]
      rw [markovChain_def, condMutualInfo_def, condEntropy_def, condEntropy_def,
        condEntropy_def] at hm
      rw [hY, hX] at hm
      linarith
  have hsum : (n : ℝ)⁻¹ * ∑ i, H[fun ω => (auxH c i ω, (ω i).2) ; μ] -
      (n : ℝ)⁻¹ * ∑ i, H[fun ω => ((auxH c i ω, (ω i).1), (ω i).2) ; μ] =
      measureEntropy (p.toMeasure.map Prod.snd) - measureEntropy p.toMeasure := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [← mul_sub, ← sum_sub_distrib, sum_congr rfl fun i _ => hi i, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ this, one_mul]
  rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def, h1, h2, h3, h4]
  linarith

private lemma ts_condEntropy (p : PMF (S × T)) (hn : 0 < n) (c : HelperCode S T n k₁ k₂) :
    H[fun a : T × S × Fin (Fintype.card (AuxH n k₂ S)) => a.2.1 | fun a => a.2.2 ;
      (tsPMF p hn c).toMeasure] =
      (n : ℝ)⁻¹ * ∑ i, H[fun ω : Fin n → S × T => (ω i).1 | auxH c i ; iidMeasure p n] := by
  set ν := (iidMix p hn).toMeasure
  set μ := iidMeasure p n
  set e₁ := Fintype.equivFin (AuxH n k₂ S)
  rw [tsPMF_toMeasure, condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _)]
  change H[fun x : Fin n × (Fin n → S × T) => (x.2 x.1).1 |
    fun x => e₁ (x.1, auxH c x.1 x.2) ; ν] = _
  have t1 : H[fun x => ((x.2 x.1).1, e₁ (x.1, auxH c x.1 x.2)) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => ((ω i).1, auxH c i ω) ; μ] :=
    entropy_iidMix p hn _ (fun q => (q.2.1, e₁ (q.1, q.2.2))) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)) (fun i ω => ((ω i).1, auxH c i ω))
      fun x => rfl
  have t2 : H[fun x => e₁ (x.1, auxH c x.1 x.2) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[auxH c i ; μ] :=
    entropy_iidMix p hn _ e₁ e₁.injective (fun i ω => auxH c i ω) fun x => rfl
  rw [condEntropy_def, t1, t2]
  simp only [condEntropy_def, sum_sub_distrib, mul_sub]
  ring

private lemma ts_info (p : PMF (S × T)) (hn : 0 < n) (c : HelperCode S T n k₁ k₂) :
    I[fun a : T × S × Fin (Fintype.card (AuxH n k₂ S)) => a.1 : fun a => a.2.2 ;
      (tsPMF p hn c).toMeasure] =
      (n : ℝ)⁻¹ * ∑ i, (H[fun ω : Fin n → S × T => (ω i).2 ; iidMeasure p n] -
        H[fun ω : Fin n → S × T => (ω i).2 | auxH c i ; iidMeasure p n]) := by
  set ν := (iidMix p hn).toMeasure
  set μ := iidMeasure p n
  set e₁ := Fintype.equivFin (AuxH n k₂ S)
  rw [tsPMF_toMeasure, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _)]
  change I[fun x : Fin n × (Fin n → S × T) => (x.2 x.1).2 :
    fun x => e₁ (x.1, auxH c x.1 x.2) ; ν] = _
  have t1 : H[fun x => ((x.2 x.1).2, e₁ (x.1, auxH c x.1 x.2)) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => ((ω i).2, auxH c i ω) ; μ] :=
    entropy_iidMix p hn _ (fun q => (q.2.1, e₁ (q.1, q.2.2))) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)) (fun i ω => ((ω i).2, auxH c i ω))
      fun x => rfl
  have t2 : H[fun x => e₁ (x.1, auxH c x.1 x.2) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[auxH c i ; μ] :=
    entropy_iidMix p hn _ e₁ e₁.injective (fun i ω => auxH c i ω) fun x => rfl
  have t3 : H[fun x : Fin n × (Fin n → S × T) => (x.2 x.1).2 ; ν] =
      measureEntropy (p.toMeasure.map Prod.snd) := by
    rw [entropy, map_iidMix_const p hn (G := fun i ω => (ω i).2) _ fun i => map_snd_eval p i]
  have t4 : ∀ i, H[fun ω : Fin n → S × T => (ω i).2 ; μ] =
      measureEntropy (p.toMeasure.map Prod.snd) := fun i => by rw [entropy, map_snd_eval]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [mutualInfo_def, t1, t2, t3]
  simp only [condEntropy_def, t4, sum_sub_distrib, mul_sub, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  ring

theorem code_mem_rateRegion [DecidableEq S] (p : PMF (S × T)) (c : HelperCode S T n k₁ k₂)
    (hn : 0 < n) :
    ((Real.log k₁ + Real.log 2) / n + c.errorProb p * Real.log (Fintype.card S),
      Real.log k₂ / n) ∈ rateRegion p := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨_, tsPMF p hn c, ts_marginal p hn c, ts_markov p hn c, ?_, ?_⟩
  · rw [ts_condEntropy]
    have h := mul_le_mul_of_nonneg_left (sum_condEntropy_X_le c p) (inv_nonneg.2 hn'.le)
    refine h.trans_eq ?_
    field_simp
  · change _ ≤ Real.log k₂ / n
    rw [ts_info, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (sum_info_Y_le c p) (inv_nonneg.2 hn'.le)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem rateRegion_mono {p : PMF (S × T)} {x y : ℝ × ℝ} (h : x ∈ rateRegion p)
    (h₁ : x.1 ≤ y.1) (h₂ : x.2 ≤ y.2) : y ∈ rateRegion p := by
  obtain ⟨m, q, hq, hm, hX, hY⟩ := h
  exact ⟨m, q, hq, hm, hX.trans h₁, hY.trans h₂⟩

theorem mem_rateRegion_of_achievable [DecidableEq S] {p : PMF (S × T)} {R₁ R₂ : ℝ}
    (h : Achievable p R₁ R₂) {δ : ℝ} (hδ : 0 < δ) : (R₁ + δ, R₂) ∈ rateRegion p := by
  obtain ⟨st, -⟩ := p.support_nonempty
  set L := Real.log (Fintype.card S)
  have hL : 0 ≤ L := Real.log_natCast_nonneg _
  set e := δ / (2 * (L + 1)) with he
  have he0 : 0 < e := by positivity
  have heL : e * L ≤ δ / 2 := by
    have : e * (L + 1) = δ / 2 := by rw [he]; field_simp
    nlinarith
  obtain ⟨N, hN⟩ := h e he0
  obtain ⟨n0, hn0⟩ := exists_nat_gt (2 * Real.log 2 / δ)
  set n := max (max N n0) 1
  have hNn : N ≤ n := (le_max_left _ _).trans (le_max_left _ _)
  have hn0n : n0 ≤ n := (le_max_right _ _).trans (le_max_left _ _)
  have hn : 0 < n := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hNn
  have hk₁0 : (0 : ℝ) < k₁ := Nat.cast_pos.2 (Fin.pos (c.enc fun _ => st.1))
  have hk₂0 : (0 : ℝ) < k₂ := Nat.cast_pos.2 (Fin.pos (c.help fun _ => st.2))
  have hl₁ : Real.log k₁ ≤ n * R₁ := (Real.log_le_iff_le_exp hk₁0).2 hk₁
  have hl₂ : Real.log k₂ ≤ n * R₂ := (Real.log_le_iff_le_exp hk₂0).2 hk₂
  have h2 : Real.log 2 / n ≤ δ / 2 := by
    have : 2 * Real.log 2 / δ < n := hn0.trans_le (by exact_mod_cast hn0n)
    rw [div_lt_iff₀ hδ] at this
    rw [div_le_iff₀ hn']
    linarith
  have hPe : c.errorProb p * L ≤ δ / 2 := (mul_le_mul_of_nonneg_right hc hL).trans heL
  refine rateRegion_mono (code_mem_rateRegion p c hn) ?_ ?_
  · change (Real.log k₁ + Real.log 2) / n + c.errorProb p * L ≤ R₁ + δ
    have : Real.log k₁ / n ≤ R₁ := by rw [div_le_iff₀ hn']; linarith
    rw [add_div]
    linarith
  · change Real.log k₂ / n ≤ R₂
    rw [div_le_iff₀ hn']
    linarith

theorem achievableRegion_subset_closure_rateRegion [DecidableEq S] (p : PMF (S × T)) :
    achievableRegion p ⊆ closure (rateRegion p) := by
  intro x hx
  have ht : Tendsto (fun δ : ℝ => (x.1 + δ, x.2)) (𝓝[>] 0) (𝓝 x) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : Continuous fun δ : ℝ => (x.1 + δ, x.2) := by fun_prop
    simpa using hc.tendsto 0
  exact mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ =>
    mem_rateRegion_of_achievable hx hδ)

theorem closure_achievableRegion_subset_closure_rateRegion [DecidableEq S] (p : PMF (S × T)) :
    closure (achievableRegion p) ⊆ closure (rateRegion p) :=
  closure_minimal (achievableRegion_subset_closure_rateRegion p) isClosed_closure

end Helper

end Meat
