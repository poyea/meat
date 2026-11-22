import Meat.Shannon.ChainRule
import Meat.Open.DistributedLossy

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

namespace DistributedLossy

open RateDistortion

section Info

variable {Ω A B C D : Type*} [MeasurableSpace Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
  (μ : Measure Ω)

private lemma cmi_fun_le [IsProbabilityMeasure μ] {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (f : A → C → D) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    I[fun ω => f (X ω) (Z ω) : Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  have hf : Measurable fun ω => (f (X ω) (Z ω), Z ω) :=
    (measurable_of_finite (fun q : A × C => (f q.1 q.2, q.2))).comp (hX.prodMk hZ)
  have h0 := condMutualInfo_nonneg μ hX hY hf
  have r1 : H[fun ω => (X ω, (f (X ω) (Z ω), Z ω)) ; μ] = H[fun ω => (X ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Z ω))
      (f := fun p => (p.1, (f p.1 p.2, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 h.2.2
  have r2 : H[fun ω => (Y ω, (f (X ω) (Z ω), Z ω)) ; μ]
      = H[fun ω => ((f (X ω) (Z ω), Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((f (X ω) (Z ω), Y ω), Z ω))
      (f := fun p => (p.1.2, (p.1.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.2.1 h.1) h.2.2
  have r3 : H[fun ω => ((X ω, Y ω), (f (X ω) (Z ω), Z ω)) ; μ]
      = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω))
      (f := fun p => (p.1, (f p.1.1 p.2, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 h.2.2
  simp only [condMutualInfo_def, condEntropy_def] at h0 ⊢
  rw [r1, r2, r3] at h0
  linarith

private lemma markov_of_indep [IsProbabilityMeasure μ] {R : Ω → D} {X : Ω → A} {Y : Ω → B}
    {U : Ω → C} (f : A → D → C) (hU : ∀ ω, U ω = f (X ω) (R ω)) (hX : Measurable X)
    (hY : Measurable Y) (hR : Measurable R) (h : I[R : fun ω => (X ω, Y ω) ; μ] = 0) :
    MarkovChain U X Y μ := by
  obtain rfl : U = fun ω => f (X ω) (R ω) := funext hU
  have h1 : I[fun ω => f (X ω) (R ω) : Y | X ; μ] ≤ I[R : Y | X ; μ] :=
    cmi_fun_le μ (fun r a => f a r) hR hY hX
  have h2 := mutualInfo_pair_eq_add_condMutualInfo μ (X := R) (Y := Y) (Z := X)
  have h3 : I[R : fun ω => (Y ω, X ω) ; μ] = I[R : fun ω => (X ω, Y ω) ; μ] :=
    mutualInfo_comp_right_of_injective μ (X := R) (Y := fun ω => (X ω, Y ω))
      (f := Prod.swap) Prod.swap_injective
  have h4 := mutualInfo_nonneg μ hR hX
  have h5 := condMutualInfo_nonneg μ
    ((measurable_of_finite (fun q : A × D => f q.1 q.2)).comp (hX.prodMk hR)) hY hX
  exact le_antisymm (by linarith) h5

private lemma cmi_mask {P : Ω → B} {W : Ω → C} {M : Ω → D} {X : Ω → A} {E : Type*} [Fintype E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {e : B → E} (he : Function.Injective e) :
    I[X : fun ω => (W ω, e (P ω)) | fun ω => (M ω, e (P ω)) ; μ]
      = I[X : W | fun ω => (M ω, P ω) ; μ] := by
  have r1 : H[fun ω => (X ω, (M ω, e (P ω))) ; μ] = H[fun ω => (X ω, (M ω, P ω)) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, (M ω, P ω)))
      (f := fun q => (q.1, (q.2.1, e q.2.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (Prod.ext h.2.1 (he h.2.2))
  have r2 : H[fun ω => ((W ω, e (P ω)), (M ω, e (P ω))) ; μ]
      = H[fun ω => (W ω, (M ω, P ω)) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (W ω, (M ω, P ω)))
      (f := fun q => ((q.1, e q.2.2), (q.2.1, e q.2.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.1 (Prod.ext h.2.1 (he h.2.2))
  have r3 : H[fun ω => ((X ω, (W ω, e (P ω))), (M ω, e (P ω))) ; μ]
      = H[fun ω => ((X ω, W ω), (M ω, P ω)) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, W ω), (M ω, P ω)))
      (f := fun q => ((q.1.1, (q.1.2, e q.2.2)), (q.2.1, e q.2.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 h.1.2.1) (Prod.ext h.2.1 (he h.2.2))
  have r4 : H[fun ω => (M ω, e (P ω)) ; μ] = H[fun ω => (M ω, P ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (M ω, P ω))
      (f := fun q => (q.1, e q.2)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (he h.2)
  simp only [condMutualInfo_def, condEntropy_def]
  rw [r1, r2, r3, r4]

end Info

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

private lemma indep_rest (p : PMF (S × T)) {n : ℕ} (i : Fin n) :
    I[fun ω : Fin n → S × T => fun j : {j // j ≠ i} => ω j : fun ω => ω i ;
      iidMeasure p n] = 0 := by
  classical
  set μ := iidMeasure p n
  set e := Equiv.piSplitAt i (fun _ : Fin n => S × T)
  have hm : ∀ b, (μ.map e).real {b} = iidProb p (e.symm b) := fun b => by
    rw [measureReal_map_singleton, sum_filter]
    rw [← Equiv.sum_comp e.symm]
    simp only [Equiv.apply_symm_apply, sum_ite_eq', mem_univ, ite_true]
    exact iidMeasure_real_singleton p _
  have hprod : ∀ b : (S × T) × ({j // j ≠ i} → S × T),
      iidProb p (e.symm b) = (p b.1).toReal * ∏ j, (p (b.2 j)).toReal := fun b => by
    rw [iidProb, Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [e, Equiv.piSplitAt_symm_apply]
    congr 1
    exact prod_congr rfl fun x _ => by simp [x.2]
  have h1 : (μ.map fun ω => ω i) = (μ.map e).map Prod.fst :=
    by rw [Measure.map_map measurable_fst (measurable_of_finite _)]; rfl
  have h2 : (μ.map fun ω : Fin n → S × T => fun j : {j // j ≠ i} => ω j) = (μ.map e).map Prod.snd :=
    by rw [Measure.map_map measurable_snd (measurable_of_finite _)]; rfl
  have h3 : (μ.map fun ω => (ω i, fun j : {j // j ≠ i} => ω j)) = μ.map e := rfl
  rw [mutualInfo_comm]
  refine mutualInfo_eq_zero_of_measureReal_eq_mul μ fun a ρ => ?_
  rw [h1, h2, h3, DMC.measureReal_map_fst, DMC.measureReal_map_snd]
  simp only [hm, hprod, ← sum_mul, ← mul_sum, sum_toReal_pmf_eq_one, one_mul]
  rw [← Fintype.prod_sum fun (j : {j // j ≠ i}) s => (p s).toReal]
  simp [sum_toReal_pmf_eq_one]

private noncomputable def mixPMF (p : PMF (S × T)) {n : ℕ} (hn : 0 < n) :
    PMF (Fin n × (Fin n → S × T)) :=
  PMF.ofFintype (fun x => (n : ℝ≥0∞)⁻¹ * ∏ j, p (x.2 j)) (by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, ← Fintype.prod_sum, sum_pmf_eq_one, prod_const_one, mul_one,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n))

private lemma mix_real (p : PMF (S × T)) {n : ℕ} (hn : 0 < n) (x : Fin n × (Fin n → S × T)) :
    (mixPMF p hn).toMeasure.real {x} = (n : ℝ)⁻¹ * iidProb p x.2 := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mixPMF,
    PMF.ofFintype_apply, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rfl

section Mix

variable {W W' : Type*} [MeasurableSpace W] [MeasurableSingletonClass W]
  [Fintype W'] [MeasurableSpace W'] [MeasurableSingletonClass W']
  (p : PMF (S × T)) {n : ℕ} (hn : 0 < n)

private lemma mix_mass (G : Fin n → (Fin n → S × T) → W) (i : Fin n) (w : W) :
    ((mixPMF p hn).toMeasure.map fun x => (x.1, G x.1 x.2)).real {(i, w)} =
      (n : ℝ)⁻¹ * ((iidMeasure p n).map (G i)).real {w} := by
  classical
  rw [measureReal_map_singleton, measureReal_map_singleton, sum_filter, sum_filter,
    Fintype.sum_prod_type, sum_eq_single i, mul_sum]
  · refine sum_congr rfl fun ω _ => ?_
    simp only [Prod.mk.injEq, true_and, mix_real, iidMeasure_real_singleton]
    split_ifs <;> simp
  · intro j _ hj
    exact sum_eq_zero fun ω _ => by simp [hj]
  · simp

private lemma map_mix_const [Finite W] (G : Fin n → (Fin n → S × T) → W) (ρ : Measure W)
    [IsFiniteMeasure ρ] (hG : ∀ i, (iidMeasure p n).map (G i) = ρ) :
    (mixPMF p hn).toMeasure.map (fun x => G x.1 x.2) = ρ := by
  classical
  have := Fintype.ofFinite W
  refine Measure.ext_of_singleton fun w => ?_
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top ρ _)]
  congr 1
  have h : ∀ i, ∑ ω : Fin n → S × T,
      (if G i ω = w then (mixPMF p hn).toMeasure.real {(i, ω)} else 0) = (n : ℝ)⁻¹ * ρ.real {w} :=
    fun i => by
      rw [← hG i, measureReal_map_singleton, sum_filter, mul_sum]
      refine sum_congr rfl fun ω _ => ?_
      split_ifs <;> simp [mix_real, iidMeasure_real_singleton]
  rw [measureReal_map_singleton, sum_filter, Fintype.sum_prod_type]
  simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

private lemma entropy_mix [Fintype W] (V : Fin n × (Fin n → S × T) → W') (e : Fin n × W → W')
    (he : Function.Injective e) (G : Fin n → (Fin n → S × T) → W)
    (hV : ∀ x, V x = e (x.1, G x.1 x.2)) :
    H[V ; (mixPMF p hn).toMeasure] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[G i ; iidMeasure p n] := by
  obtain rfl : V = fun x => e (x.1, G x.1 x.2) := funext hV
  have h0 : H[fun x => e (x.1, G x.1 x.2) ; (mixPMF p hn).toMeasure] =
      H[fun x => (x.1, G x.1 x.2) ; (mixPMF p hn).toMeasure] :=
    entropy_comp_of_injective _ he
  have hi : ∀ i, ∑ w, Real.negMulLog ((n : ℝ)⁻¹ * ((iidMeasure p n).map (G i)).real {w}) =
      (n : ℝ)⁻¹ * Real.log n + (n : ℝ)⁻¹ * H[G i ; iidMeasure p n] := fun i => by
    simp only [Real.negMulLog_mul, sum_add_distrib, ← sum_mul, ← mul_sum,
      sum_measureReal_singleton_eq_one, one_mul, entropy_def]
    rw [Real.negMulLog, Real.log_inv]
    ring
  rw [h0, entropy_def, Fintype.sum_prod_type]
  simp only [mix_mass, hi, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_sum]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end Mix

@[instance_reducible]
private def optMS (α : Type*) : MeasurableSpace (Option α) := ⊤

attribute [local instance] optMS

private lemma optMSC (α : Type*) : MeasurableSingletonClass (Option α) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

attribute [local instance] optMSC

variable {U V : Type*} {n k₁ k₂ : ℕ}

private def msg₁ (c : DLCode S T U V n k₁ k₂) (ω : Fin n → S × T) : Fin k₁ :=
  c.enc₁ fun j => (ω j).1

private def msg₂ (c : DLCode S T U V n k₁ k₂) (ω : Fin n → S × T) : Fin k₂ :=
  c.enc₂ fun j => (ω j).2

private def maskOf (i : Fin n) (τ : Fin i → S × T) : Fin n → Option (S × T) :=
  fun j => if h : j.val < i.val then some (τ ⟨j, h⟩) else none

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype T]
  [MeasurableSpace T] [MeasurableSingletonClass T] in
private lemma maskOf_injective (i : Fin n) : Function.Injective (maskOf (S := S) (T := T) i) :=
  fun a b h => funext fun j => by
    have := congrFun h ⟨j, j.2.trans i.2⟩
    simpa [maskOf, j.2] using this

private def aux₁ (c : DLCode S T U V n k₁ k₂) (i : Fin n) (ω : Fin n → S × T) :
    Fin k₁ × (Fin n → Option (S × T)) :=
  (msg₁ c ω, maskOf i (seqPrefix ω i))

private def aux₂ (c : DLCode S T U V n k₁ k₂) (i : Fin n) (ω : Fin n → S × T) :
    Fin k₂ × (Fin n → Option (S × T)) :=
  (msg₂ c ω, maskOf i (seqPrefix ω i))

private lemma sum_rate₁_le (p : PMF (S × T)) (c : DLCode S T U V n k₁ k₂) :
    ∑ i, I[fun ω : Fin n → S × T => ω i : aux₁ c i | aux₂ c i ; iidMeasure p n]
      ≤ Real.log k₁ := by
  set μ := iidMeasure p n
  have e1 : ∀ i, I[fun ω : Fin n → S × T => ω i : aux₁ c i | aux₂ c i ; μ]
      = I[fun ω : Fin n → S × T => ω i : msg₁ c | fun ω => (msg₂ c ω, seqPrefix ω i) ; μ] :=
    fun i => cmi_mask μ (X := fun ω : Fin n → S × T => ω i) (W := msg₁ c) (M := msg₂ c)
      (P := fun ω => seqPrefix ω i) (maskOf_injective i)
  have e2 := condMutualInfo_eq_sum μ (fun ω : Fin n → S × T => ω) (msg₁ c) (msg₂ c)
  have e3 := condMutualInfo_eq_condEntropy_sub_condEntropy μ
    (X := fun ω : Fin n → S × T => ω) (Y := msg₁ c) (Z := msg₂ c)
  have h1 := condEntropy_nonneg μ (X := msg₁ c)
    (Y := fun ω : Fin n → S × T => (ω, msg₂ c ω)) (measurable_of_finite _)
    (measurable_of_finite _)
  have h2 := condEntropy_le_entropy μ (X := msg₁ c) (Y := msg₂ c) (measurable_of_finite _)
    (measurable_of_finite _)
  have h3 := entropy_le_log_card μ (X := msg₁ c)
  rw [Fintype.card_fin] at h3
  simp only [e1]
  linarith

private lemma sum_rate₂_le (p : PMF (S × T)) (c : DLCode S T U V n k₁ k₂) :
    ∑ i, I[fun ω : Fin n → S × T => ω i : aux₂ c i | aux₁ c i ; iidMeasure p n]
      ≤ Real.log k₂ := by
  set μ := iidMeasure p n
  have e1 : ∀ i, I[fun ω : Fin n → S × T => ω i : aux₂ c i | aux₁ c i ; μ]
      = I[fun ω : Fin n → S × T => ω i : msg₂ c | fun ω => (msg₁ c ω, seqPrefix ω i) ; μ] :=
    fun i => cmi_mask μ (X := fun ω : Fin n → S × T => ω i) (W := msg₂ c) (M := msg₁ c)
      (P := fun ω => seqPrefix ω i) (maskOf_injective i)
  have e2 := condMutualInfo_eq_sum μ (fun ω : Fin n → S × T => ω) (msg₂ c) (msg₁ c)
  have e3 := condMutualInfo_eq_condEntropy_sub_condEntropy μ
    (X := fun ω : Fin n → S × T => ω) (Y := msg₂ c) (Z := msg₁ c)
  have h1 := condEntropy_nonneg μ (X := msg₂ c)
    (Y := fun ω : Fin n → S × T => (ω, msg₁ c ω)) (measurable_of_finite _)
    (measurable_of_finite _)
  have h2 := condEntropy_le_entropy μ (X := msg₂ c) (Y := msg₁ c) (measurable_of_finite _)
    (measurable_of_finite _)
  have h3 := entropy_le_log_card μ (X := msg₂ c)
  rw [Fintype.card_fin] at h3
  simp only [e1]
  linarith

private lemma sum_rate_le (p : PMF (S × T)) (c : DLCode S T U V n k₁ k₂) :
    ∑ i, I[fun ω : Fin n → S × T => ω i : fun ω => (aux₁ c i ω, aux₂ c i ω) ; iidMeasure p n]
      ≤ Real.log k₁ + Real.log k₂ := by
  set μ := iidMeasure p n
  set M : (Fin n → S × T) → Fin k₁ × Fin k₂ := fun ω => (msg₁ c ω, msg₂ c ω)
  have e1 : ∀ i, I[fun ω : Fin n → S × T => ω i : fun ω => (aux₁ c i ω, aux₂ c i ω) ; μ]
      = H[fun ω : Fin n → S × T => ω i ; μ]
        - H[fun ω : Fin n → S × T => ω i | fun ω => (M ω, seqPrefix ω i) ; μ] := fun i => by
    rw [← mutualInfo_eq_entropy_sub_condEntropy]
    exact mutualInfo_comp_right_of_injective μ (X := fun ω : Fin n → S × T => ω i)
      (Y := fun ω => (M ω, seqPrefix ω i))
      (f := fun q => ((q.1.1, maskOf i q.2), (q.1.2, maskOf i q.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 h.2.1) (maskOf_injective i h.1.2)
  have e2 := condEntropy_eq_sum μ (fun ω : Fin n → S × T => ω) M
  have e3 : ∑ i, H[fun ω : Fin n → S × T => ω i ; μ] = H[fun ω : Fin n → S × T => ω ; μ] := by
    simp only [μ, entropy_eval_iidMeasure, entropy_iidMeasure, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have e4 := mutualInfo_eq_entropy_sub_condEntropy (fun ω : Fin n → S × T => ω) M μ
  have e5 := mutualInfo_eq_entropy_sub_condEntropy M (fun ω : Fin n → S × T => ω) μ
  have e6 := mutualInfo_comm μ (X := fun ω : Fin n → S × T => ω) (Y := M)
  have h1 := condEntropy_nonneg μ (X := M) (Y := fun ω : Fin n → S × T => ω)
    (measurable_of_finite _) (measurable_of_finite _)
  have h2 := entropy_pair_le_add μ (X := msg₁ c) (Y := msg₂ c) (measurable_of_finite _)
    (measurable_of_finite _)
  have h3 := entropy_le_log_card μ (X := msg₁ c)
  have h4 := entropy_le_log_card μ (X := msg₂ c)
  rw [Fintype.card_fin] at h3 h4
  simp only [e1, sum_sub_distrib, e3]
  linarith

private lemma markov₁ (p : PMF (S × T)) (c : DLCode S T U V n k₁ k₂) (i : Fin n) :
    MarkovChain (aux₁ c i) (fun ω : Fin n → S × T => (ω i).1) (fun ω => (ω i).2)
      (iidMeasure p n) := by
  classical
  refine markov_of_indep _ (R := fun ω : Fin n → S × T => fun j : {j // j ≠ i} => ω j)
    (fun a ρ => (c.enc₁ (fun j => if h : j = i then a else (ρ ⟨j, h⟩).1),
      maskOf i (fun j : Fin i => ρ ⟨⟨j, j.2.trans i.2⟩,
        fun h => absurd (congrArg Fin.val h) (Nat.ne_of_lt j.2)⟩)))
    (fun ω => ?_) (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (indep_rest p i)
  refine Prod.ext (congrArg c.enc₁ (funext fun j => ?_)) rfl
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

private lemma markov₂ (p : PMF (S × T)) (c : DLCode S T U V n k₁ k₂) (i : Fin n) :
    MarkovChain (aux₂ c i) (fun ω : Fin n → S × T => (ω i).2) (fun ω => (ω i).1)
      (iidMeasure p n) := by
  classical
  have hind : I[fun ω : Fin n → S × T => fun j : {j // j ≠ i} => ω j :
      fun ω => ((ω i).2, (ω i).1) ; iidMeasure p n] = 0 := by
    rw [← indep_rest p i]
    exact mutualInfo_comp_right_of_injective _ (X := fun ω : Fin n → S × T =>
      fun j : {j // j ≠ i} => ω j) (Y := fun ω => ω i) (f := Prod.swap) Prod.swap_injective
  refine markov_of_indep _ (R := fun ω : Fin n → S × T => fun j : {j // j ≠ i} => ω j)
    (fun a ρ => (c.enc₂ (fun j => if h : j = i then a else (ρ ⟨j, h⟩).2),
      maskOf i (fun j : Fin i => ρ ⟨⟨j, j.2.trans i.2⟩,
        fun h => absurd (congrArg Fin.val h) (Nat.ne_of_lt j.2)⟩)))
    (fun ω => ?_) (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    hind
  refine Prod.ext (congrArg c.enc₂ (funext fun j => ?_)) rfl
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

private abbrev Aux (n k : ℕ) (S T : Type*) := Fin n × (Fin k × (Fin n → Option (S × T)))

private noncomputable def tsMap (c : DLCode S T U V n k₁ k₂) (x : Fin n × (Fin n → S × T)) :
    S × T × Fin (Fintype.card (Aux n k₁ S T)) × Fin (Fintype.card (Aux n k₂ S T)) :=
  ((x.2 x.1).1, (x.2 x.1).2, Fintype.equivFin _ (x.1, aux₁ c x.1 x.2),
    Fintype.equivFin _ (x.1, aux₂ c x.1 x.2))

private noncomputable def tsPMF (p : PMF (S × T)) (hn : 0 < n) (c : DLCode S T U V n k₁ k₂) :
    PMF (S × T × Fin (Fintype.card (Aux n k₁ S T)) × Fin (Fintype.card (Aux n k₂ S T))) :=
  (mixPMF p hn).map (tsMap c)

private lemma tsPMF_toMeasure (p : PMF (S × T)) (hn : 0 < n) (c : DLCode S T U V n k₁ k₂) :
    (tsPMF p hn c).toMeasure = (mixPMF p hn).toMeasure.map (tsMap c) :=
  (PMF.toMeasure_map _ _ (measurable_of_finite _)).symm

private lemma map_swap_eval (p : PMF (S × T)) (i : Fin n) :
    (iidMeasure p n).map (fun ω : Fin n → S × T => ((ω i).2, (ω i).1)) =
      p.toMeasure.map Prod.swap := by
  rw [← map_eval_iidMeasure p i, Measure.map_map measurable_swap (measurable_of_finite _)]
  rfl

private lemma map_fst_eval (p : PMF (S × T)) (i : Fin n) :
    (iidMeasure p n).map (fun ω : Fin n → S × T => (ω i).1) = p.toMeasure.map Prod.fst := by
  rw [← map_eval_iidMeasure p i, Measure.map_map measurable_fst (measurable_of_finite _)]
  rfl

private lemma map_snd_eval (p : PMF (S × T)) (i : Fin n) :
    (iidMeasure p n).map (fun ω : Fin n → S × T => (ω i).2) = p.toMeasure.map Prod.snd := by
  rw [← map_eval_iidMeasure p i, Measure.map_map measurable_snd (measurable_of_finite _)]
  rfl

private lemma ts_marginal (p : PMF (S × T)) (hn : 0 < n) (c : DLCode S T U V n k₁ k₂) :
    (tsPMF p hn c).map (fun ω => (ω.1, ω.2.1)) = p := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _), tsPMF_toMeasure,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  exact map_mix_const p hn (G := fun i ω => ω i) p.toMeasure fun i => map_eval_iidMeasure p i

private lemma ts_markov₁ (p : PMF (S × T)) (hn : 0 < n) (c : DLCode S T U V n k₁ k₂) :
    MarkovChain (fun ω : S × T × Fin (Fintype.card (Aux n k₁ S T)) ×
      Fin (Fintype.card (Aux n k₂ S T)) => ω.2.2.1) (fun ω => ω.1) (fun ω => ω.2.1)
      (tsPMF p hn c).toMeasure := by
  set ν := (mixPMF p hn).toMeasure
  set μ := iidMeasure p n
  set e₁ := Fintype.equivFin (Aux n k₁ S T)
  rw [markovChain_def, tsPMF_toMeasure, condMutualInfo_map _ (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  change I[fun x => e₁ (x.1, aux₁ c x.1 x.2) : fun x => (x.2 x.1).2 |
    fun x => (x.2 x.1).1 ; ν] = 0
  have h1 : H[fun x => (e₁ (x.1, aux₁ c x.1 x.2), (x.2 x.1).1) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => (aux₁ c i ω, (ω i).1) ; μ] :=
    entropy_mix p hn _ (fun q => (e₁ (q.1, q.2.1), q.2.2)) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)) (fun i ω => (aux₁ c i ω, (ω i).1))
      fun x => rfl
  have h2 : H[fun x : Fin n × (Fin n → S × T) => ((x.2 x.1).2, (x.2 x.1).1) ; ν] =
      measureEntropy (p.toMeasure.map Prod.swap) := by
    rw [entropy, map_mix_const p hn (G := fun i ω => ((ω i).2, (ω i).1)) _
      fun i => map_swap_eval p i]
  have h3 : H[fun x => ((e₁ (x.1, aux₁ c x.1 x.2), (x.2 x.1).2), (x.2 x.1).1) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => ((aux₁ c i ω, (ω i).2), (ω i).1) ; μ] :=
    entropy_mix p hn _ (fun q => ((e₁ (q.1, q.2.1.1), q.2.1.2), q.2.2)) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1.1 (Prod.ext (Prod.ext h.1.1.2 h.1.2) h.2))
      (fun i ω => ((aux₁ c i ω, (ω i).2), (ω i).1)) fun x => rfl
  have h4 : H[fun x : Fin n × (Fin n → S × T) => (x.2 x.1).1 ; ν] =
      measureEntropy (p.toMeasure.map Prod.fst) := by
    rw [entropy, map_mix_const p hn (G := fun i ω => (ω i).1) _ fun i => map_fst_eval p i]
  have hi : ∀ i, H[fun ω => (aux₁ c i ω, (ω i).1) ; μ] -
      H[fun ω => ((aux₁ c i ω, (ω i).2), (ω i).1) ; μ] =
      measureEntropy (p.toMeasure.map Prod.fst) - measureEntropy (p.toMeasure.map Prod.swap) :=
    fun i => by
      have hm := markov₁ p c i
      have hY : H[fun ω : Fin n → S × T => ((ω i).2, (ω i).1) ; μ] =
          measureEntropy (p.toMeasure.map Prod.swap) := by rw [entropy, map_swap_eval]
      have hX : H[fun ω : Fin n → S × T => (ω i).1 ; μ] =
          measureEntropy (p.toMeasure.map Prod.fst) := by rw [entropy, map_fst_eval]
      rw [markovChain_def, condMutualInfo_def, condEntropy_def, condEntropy_def,
        condEntropy_def] at hm
      rw [hY, hX] at hm
      linarith
  have hsum : (n : ℝ)⁻¹ * ∑ i, H[fun ω => (aux₁ c i ω, (ω i).1) ; μ] -
      (n : ℝ)⁻¹ * ∑ i, H[fun ω => ((aux₁ c i ω, (ω i).2), (ω i).1) ; μ] =
      measureEntropy (p.toMeasure.map Prod.fst) - measureEntropy (p.toMeasure.map Prod.swap) := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [← mul_sub, ← sum_sub_distrib, sum_congr rfl fun i _ => hi i, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ this, one_mul]
  rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def, h1, h2, h3, h4]
  linarith

private lemma ts_markov₂ (p : PMF (S × T)) (hn : 0 < n) (c : DLCode S T U V n k₁ k₂) :
    MarkovChain (fun ω : S × T × Fin (Fintype.card (Aux n k₁ S T)) ×
      Fin (Fintype.card (Aux n k₂ S T)) => ω.2.2.2) (fun ω => ω.2.1) (fun ω => ω.1)
      (tsPMF p hn c).toMeasure := by
  set ν := (mixPMF p hn).toMeasure
  set μ := iidMeasure p n
  set e₂ := Fintype.equivFin (Aux n k₂ S T)
  rw [markovChain_def, tsPMF_toMeasure, condMutualInfo_map _ (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  change I[fun x => e₂ (x.1, aux₂ c x.1 x.2) : fun x => (x.2 x.1).1 |
    fun x => (x.2 x.1).2 ; ν] = 0
  have h1 : H[fun x => (e₂ (x.1, aux₂ c x.1 x.2), (x.2 x.1).2) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => (aux₂ c i ω, (ω i).2) ; μ] :=
    entropy_mix p hn _ (fun q => (e₂ (q.1, q.2.1), q.2.2)) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)) (fun i ω => (aux₂ c i ω, (ω i).2))
      fun x => rfl
  have h2 : H[fun x : Fin n × (Fin n → S × T) => ((x.2 x.1).1, (x.2 x.1).2) ; ν] =
      measureEntropy p.toMeasure := by
    rw [entropy, map_mix_const p hn (G := fun i ω => ω i) _
      fun i => map_eval_iidMeasure p i]
  have h3 : H[fun x => ((e₂ (x.1, aux₂ c x.1 x.2), (x.2 x.1).1), (x.2 x.1).2) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => ((aux₂ c i ω, (ω i).1), (ω i).2) ; μ] :=
    entropy_mix p hn _ (fun q => ((e₂ (q.1, q.2.1.1), q.2.1.2), q.2.2)) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1.1 (Prod.ext (Prod.ext h.1.1.2 h.1.2) h.2))
      (fun i ω => ((aux₂ c i ω, (ω i).1), (ω i).2)) fun x => rfl
  have h4 : H[fun x : Fin n × (Fin n → S × T) => (x.2 x.1).2 ; ν] =
      measureEntropy (p.toMeasure.map Prod.snd) := by
    rw [entropy, map_mix_const p hn (G := fun i ω => (ω i).2) _ fun i => map_snd_eval p i]
  have hi : ∀ i, H[fun ω => (aux₂ c i ω, (ω i).2) ; μ] -
      H[fun ω => ((aux₂ c i ω, (ω i).1), (ω i).2) ; μ] =
      measureEntropy (p.toMeasure.map Prod.snd) - measureEntropy p.toMeasure :=
    fun i => by
      have hm := markov₂ p c i
      have hY : H[fun ω : Fin n → S × T => ((ω i).1, (ω i).2) ; μ] =
          measureEntropy p.toMeasure := by rw [entropy, ← map_eval_iidMeasure p i]
      have hX : H[fun ω : Fin n → S × T => (ω i).2 ; μ] =
          measureEntropy (p.toMeasure.map Prod.snd) := by rw [entropy, map_snd_eval]
      rw [markovChain_def, condMutualInfo_def, condEntropy_def, condEntropy_def,
        condEntropy_def] at hm
      rw [hY, hX] at hm
      linarith
  have hsum : (n : ℝ)⁻¹ * ∑ i, H[fun ω => (aux₂ c i ω, (ω i).2) ; μ] -
      (n : ℝ)⁻¹ * ∑ i, H[fun ω => ((aux₂ c i ω, (ω i).1), (ω i).2) ; μ] =
      measureEntropy (p.toMeasure.map Prod.snd) - measureEntropy p.toMeasure := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [← mul_sub, ← sum_sub_distrib, sum_congr rfl fun i _ => hi i, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ this, one_mul]
  rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def, h1, h2, h3, h4]
  linarith

private noncomputable def recon₁ (c : DLCode S T U V n k₁ k₂)
    (a : Fin (Fintype.card (Aux n k₁ S T)) × Fin (Fintype.card (Aux n k₂ S T))) : U :=
  (c.dec (((Fintype.equivFin _).symm a.1).2.1, ((Fintype.equivFin _).symm a.2).2.1)).1
    ((Fintype.equivFin _).symm a.1).1

private noncomputable def recon₂ (c : DLCode S T U V n k₁ k₂)
    (a : Fin (Fintype.card (Aux n k₁ S T)) × Fin (Fintype.card (Aux n k₂ S T))) : V :=
  (c.dec (((Fintype.equivFin _).symm a.1).2.1, ((Fintype.equivFin _).symm a.2).2.1)).2
    ((Fintype.equivFin _).symm a.1).1

private lemma pmf_toReal_eq {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (q : PMF α) (a : α) : (q a).toReal = q.toMeasure.real {a} := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

private lemma ts_dist₁ (p : PMF (S × T)) (hn : 0 < n) (c : DLCode S T U V n k₁ k₂)
    (d₁ : S → U → ℝ) :
    ∑ ω, ((tsPMF p hn c) ω).toReal * d₁ ω.1 (recon₁ c ω.2.2) = c.distortion₁ p d₁ := by
  have hR : c.distortion₁ p d₁ = ∑ ω : Fin n → S × T,
      iidProb p ω * blockDist d₁ (fun j => (ω j).1) (c.dec (msg₁ c ω, msg₂ c ω)).1 := by
    rw [DLCode.distortion₁,
      ← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => S) fun _ => T)]
    rfl
  simp only [pmf_toReal_eq]
  rw [tsPMF_toMeasure, ← sum_measureReal_mul_comp (mixPMF p hn).toMeasure (tsMap c)
    (fun ω => d₁ ω.1 (recon₁ c ω.2.2)), hR, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  simp only [mix_real, tsMap, recon₁, aux₁, aux₂, Equiv.symm_apply_apply, blockDist,
    div_eq_mul_inv]
  rw [sum_mul, mul_sum]
  exact sum_congr rfl fun i _ => by ring

private lemma ts_dist₂ (p : PMF (S × T)) (hn : 0 < n) (c : DLCode S T U V n k₁ k₂)
    (d₂ : T → V → ℝ) :
    ∑ ω, ((tsPMF p hn c) ω).toReal * d₂ ω.2.1 (recon₂ c ω.2.2) = c.distortion₂ p d₂ := by
  have hR : c.distortion₂ p d₂ = ∑ ω : Fin n → S × T,
      iidProb p ω * blockDist d₂ (fun j => (ω j).2) (c.dec (msg₁ c ω, msg₂ c ω)).2 := by
    rw [DLCode.distortion₂,
      ← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => S) fun _ => T)]
    rfl
  simp only [pmf_toReal_eq]
  rw [tsPMF_toMeasure, ← sum_measureReal_mul_comp (mixPMF p hn).toMeasure (tsMap c)
    (fun ω => d₂ ω.2.1 (recon₂ c ω.2.2)), hR, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  simp only [mix_real, tsMap, recon₂, aux₁, aux₂, Equiv.symm_apply_apply, blockDist,
    div_eq_mul_inv]
  rw [sum_mul, mul_sum]
  exact sum_congr rfl fun i _ => by ring

private lemma ts_rate₁ (p : PMF (S × T)) (hn : 0 < n) (c : DLCode S T U V n k₁ k₂) :
    I[fun ω : S × T × Fin (Fintype.card (Aux n k₁ S T)) × Fin (Fintype.card (Aux n k₂ S T)) =>
      (ω.1, ω.2.1) : fun ω => ω.2.2.1 | fun ω => ω.2.2.2 ; (tsPMF p hn c).toMeasure]
      ≤ Real.log k₁ / n := by
  set ν := (mixPMF p hn).toMeasure
  set μ := iidMeasure p n
  set e₁ := Fintype.equivFin (Aux n k₁ S T)
  set e₂ := Fintype.equivFin (Aux n k₂ S T)
  rw [tsPMF_toMeasure, condMutualInfo_map _ (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  change I[fun x : Fin n × (Fin n → S × T) => x.2 x.1 : fun x => e₁ (x.1, aux₁ c x.1 x.2) |
    fun x => e₂ (x.1, aux₂ c x.1 x.2) ; ν] ≤ _
  have t1 : H[fun x : Fin n × (Fin n → S × T) => (x.2 x.1, e₂ (x.1, aux₂ c x.1 x.2)) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω : Fin n → S × T => (ω i, aux₂ c i ω) ; μ] :=
    entropy_mix p hn _ (fun q => (q.2.1, e₂ (q.1, q.2.2))) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)) (fun i ω => (ω i, aux₂ c i ω)) fun x => rfl
  have t2 : H[fun x => (e₁ (x.1, aux₁ c x.1 x.2), e₂ (x.1, aux₂ c x.1 x.2)) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => (aux₁ c i ω, aux₂ c i ω) ; μ] :=
    entropy_mix p hn _ (fun q => (e₁ (q.1, q.2.1), e₂ (q.1, q.2.2))) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2.2)) (fun i ω => (aux₁ c i ω, aux₂ c i ω))
      fun x => rfl
  have t3 : H[fun x : Fin n × (Fin n → S × T) =>
      ((x.2 x.1, e₁ (x.1, aux₁ c x.1 x.2)), e₂ (x.1, aux₂ c x.1 x.2)) ; ν] =
      Real.log n + (n : ℝ)⁻¹ *
        ∑ i, H[fun ω : Fin n → S × T => ((ω i, aux₁ c i ω), aux₂ c i ω) ; μ] :=
    entropy_mix p hn _ (fun q => ((q.2.1.1, e₁ (q.1, q.2.1.2)), e₂ (q.1, q.2.2)))
      (fun a b h => by
        simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
        exact Prod.ext h.1.2.1 (Prod.ext (Prod.ext h.1.1 h.1.2.2) h.2.2))
      (fun i ω => ((ω i, aux₁ c i ω), aux₂ c i ω)) fun x => rfl
  have t4 : H[fun x => e₂ (x.1, aux₂ c x.1 x.2) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[aux₂ c i ; μ] :=
    entropy_mix p hn _ (fun q => e₂ q) e₂.injective (fun i ω => aux₂ c i ω) fun x => rfl
  have hI : ∀ i, I[fun ω : Fin n → S × T => ω i : aux₁ c i | aux₂ c i ; μ] =
      H[fun ω : Fin n → S × T => (ω i, aux₂ c i ω) ; μ] +
        H[fun ω => (aux₁ c i ω, aux₂ c i ω) ; μ] -
        H[fun ω : Fin n → S × T => ((ω i, aux₁ c i ω), aux₂ c i ω) ; μ] - H[aux₂ c i ; μ] :=
    fun i => by
      rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def]
      ring
  have hb := mul_le_mul_of_nonneg_left (sum_rate₁_le p c)
    (inv_nonneg.2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  rw [show iidMeasure p n = μ from rfl] at hb
  simp only [hI, sum_add_distrib, sum_sub_distrib, mul_add, mul_sub] at hb
  rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def, t1, t2, t3, t4,
    div_eq_inv_mul]
  linarith

private lemma ts_rate₂ (p : PMF (S × T)) (hn : 0 < n) (c : DLCode S T U V n k₁ k₂) :
    I[fun ω : S × T × Fin (Fintype.card (Aux n k₁ S T)) × Fin (Fintype.card (Aux n k₂ S T)) =>
      (ω.1, ω.2.1) : fun ω => ω.2.2.2 | fun ω => ω.2.2.1 ; (tsPMF p hn c).toMeasure]
      ≤ Real.log k₂ / n := by
  set ν := (mixPMF p hn).toMeasure
  set μ := iidMeasure p n
  set e₁ := Fintype.equivFin (Aux n k₁ S T)
  set e₂ := Fintype.equivFin (Aux n k₂ S T)
  rw [tsPMF_toMeasure, condMutualInfo_map _ (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  change I[fun x : Fin n × (Fin n → S × T) => x.2 x.1 : fun x => e₂ (x.1, aux₂ c x.1 x.2) |
    fun x => e₁ (x.1, aux₁ c x.1 x.2) ; ν] ≤ _
  have t1 : H[fun x : Fin n × (Fin n → S × T) => (x.2 x.1, e₁ (x.1, aux₁ c x.1 x.2)) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω : Fin n → S × T => (ω i, aux₁ c i ω) ; μ] :=
    entropy_mix p hn _ (fun q => (q.2.1, e₁ (q.1, q.2.2))) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)) (fun i ω => (ω i, aux₁ c i ω)) fun x => rfl
  have t2 : H[fun x => (e₂ (x.1, aux₂ c x.1 x.2), e₁ (x.1, aux₁ c x.1 x.2)) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => (aux₂ c i ω, aux₁ c i ω) ; μ] :=
    entropy_mix p hn _ (fun q => (e₂ (q.1, q.2.1), e₁ (q.1, q.2.2))) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2.2)) (fun i ω => (aux₂ c i ω, aux₁ c i ω))
      fun x => rfl
  have t3 : H[fun x : Fin n × (Fin n → S × T) =>
      ((x.2 x.1, e₂ (x.1, aux₂ c x.1 x.2)), e₁ (x.1, aux₁ c x.1 x.2)) ; ν] =
      Real.log n + (n : ℝ)⁻¹ *
        ∑ i, H[fun ω : Fin n → S × T => ((ω i, aux₂ c i ω), aux₁ c i ω) ; μ] :=
    entropy_mix p hn _ (fun q => ((q.2.1.1, e₂ (q.1, q.2.1.2)), e₁ (q.1, q.2.2)))
      (fun a b h => by
        simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
        exact Prod.ext h.1.2.1 (Prod.ext (Prod.ext h.1.1 h.1.2.2) h.2.2))
      (fun i ω => ((ω i, aux₂ c i ω), aux₁ c i ω)) fun x => rfl
  have t4 : H[fun x => e₁ (x.1, aux₁ c x.1 x.2) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[aux₁ c i ; μ] :=
    entropy_mix p hn _ (fun q => e₁ q) e₁.injective (fun i ω => aux₁ c i ω) fun x => rfl
  have hI : ∀ i, I[fun ω : Fin n → S × T => ω i : aux₂ c i | aux₁ c i ; μ] =
      H[fun ω : Fin n → S × T => (ω i, aux₁ c i ω) ; μ] +
        H[fun ω => (aux₂ c i ω, aux₁ c i ω) ; μ] -
        H[fun ω : Fin n → S × T => ((ω i, aux₂ c i ω), aux₁ c i ω) ; μ] - H[aux₁ c i ; μ] :=
    fun i => by
      rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def]
      ring
  have hb := mul_le_mul_of_nonneg_left (sum_rate₂_le p c)
    (inv_nonneg.2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  rw [show iidMeasure p n = μ from rfl] at hb
  simp only [hI, sum_add_distrib, sum_sub_distrib, mul_add, mul_sub] at hb
  rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def, t1, t2, t3, t4,
    div_eq_inv_mul]
  linarith

private lemma ts_rate (p : PMF (S × T)) (hn : 0 < n) (c : DLCode S T U V n k₁ k₂) :
    I[fun ω : S × T × Fin (Fintype.card (Aux n k₁ S T)) × Fin (Fintype.card (Aux n k₂ S T)) =>
      (ω.1, ω.2.1) : fun ω => ω.2.2 ; (tsPMF p hn c).toMeasure]
      ≤ Real.log k₁ / n + Real.log k₂ / n := by
  set ν := (mixPMF p hn).toMeasure
  set μ := iidMeasure p n
  set e₁ := Fintype.equivFin (Aux n k₁ S T)
  set e₂ := Fintype.equivFin (Aux n k₂ S T)
  rw [tsPMF_toMeasure, mutualInfo_map _ (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)]
  change I[fun x : Fin n × (Fin n → S × T) => x.2 x.1 :
    fun x => (e₁ (x.1, aux₁ c x.1 x.2), e₂ (x.1, aux₂ c x.1 x.2)) ; ν] ≤ _
  have s1 : H[fun x : Fin n × (Fin n → S × T) => x.2 x.1 ; ν] = measureEntropy p.toMeasure := by
    rw [entropy, map_mix_const p hn (G := fun i ω => ω i) _ fun i => map_eval_iidMeasure p i]
  have t2 : H[fun x => (e₁ (x.1, aux₁ c x.1 x.2), e₂ (x.1, aux₂ c x.1 x.2)) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => (aux₁ c i ω, aux₂ c i ω) ; μ] :=
    entropy_mix p hn _ (fun q => (e₁ (q.1, q.2.1), e₂ (q.1, q.2.2))) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2.2)) (fun i ω => (aux₁ c i ω, aux₂ c i ω))
      fun x => rfl
  have t3 : H[fun x : Fin n × (Fin n → S × T) =>
      (x.2 x.1, (e₁ (x.1, aux₁ c x.1 x.2), e₂ (x.1, aux₂ c x.1 x.2))) ; ν] =
      Real.log n + (n : ℝ)⁻¹ *
        ∑ i, H[fun ω : Fin n → S × T => (ω i, (aux₁ c i ω, aux₂ c i ω)) ; μ] :=
    entropy_mix p hn _ (fun q => (q.2.1, (e₁ (q.1, q.2.2.1), e₂ (q.1, q.2.2.2))))
      (fun a b h => by
        simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
        exact Prod.ext h.2.1.1 (Prod.ext h.1 (Prod.ext h.2.1.2 h.2.2.2)))
      (fun i ω => (ω i, (aux₁ c i ω, aux₂ c i ω))) fun x => rfl
  have hI : ∀ i, I[fun ω : Fin n → S × T => ω i : fun ω => (aux₁ c i ω, aux₂ c i ω) ; μ] =
      measureEntropy p.toMeasure + H[fun ω => (aux₁ c i ω, aux₂ c i ω) ; μ] -
        H[fun ω : Fin n → S × T => (ω i, (aux₁ c i ω, aux₂ c i ω)) ; μ] := fun i => by
    rw [mutualInfo_def, show H[fun ω : Fin n → S × T => ω i ; μ] = measureEntropy p.toMeasure
      from entropy_eval_iidMeasure p i]
  have hb := mul_le_mul_of_nonneg_left (sum_rate_le p c)
    (inv_nonneg.2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  rw [show iidMeasure p n = μ from rfl] at hb
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [hI, sum_add_distrib, sum_sub_distrib, mul_add, mul_sub, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul] at hb
  rw [mutualInfo_def, s1, t2, t3, div_eq_inv_mul, div_eq_inv_mul]
  linarith

theorem code_mem_bergerTungOuter (p : PMF (S × T)) (d₁ : S → U → ℝ) (d₂ : T → V → ℝ)
    (c : DLCode S T U V n k₁ k₂) (hn : 0 < n) :
    ((Real.log k₁ / n, Real.log k₂ / n), c.distortion₁ p d₁, c.distortion₂ p d₂) ∈
      bergerTungOuter p d₁ d₂ :=
  ⟨_, _, tsPMF p hn c, recon₁ c, recon₂ c, ts_marginal p hn c, ts_markov₁ p hn c,
    ts_markov₂ p hn c, (ts_dist₁ p hn c d₁).le, (ts_dist₂ p hn c d₂).le, ts_rate₁ p hn c,
    ts_rate₂ p hn c, ts_rate p hn c⟩

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem bergerTungOuter_mono {p : PMF (S × T)} {d₁ : S → U → ℝ} {d₂ : T → V → ℝ}
    {x y : (ℝ × ℝ) × ℝ × ℝ} (h : x ∈ bergerTungOuter p d₁ d₂) (h₁ : x.1.1 ≤ y.1.1)
    (h₂ : x.1.2 ≤ y.1.2) (h₃ : x.2.1 ≤ y.2.1) (h₄ : x.2.2 ≤ y.2.2) :
    y ∈ bergerTungOuter p d₁ d₂ := by
  obtain ⟨m₁, m₂, q, φ₁, φ₂, hq, hm₁, hm₂, hd₁, hd₂, hr₁, hr₂, hr⟩ := h
  exact ⟨m₁, m₂, q, φ₁, φ₂, hq, hm₁, hm₂, hd₁.trans h₃, hd₂.trans h₄, hr₁.trans h₁,
    hr₂.trans h₂, hr.trans (add_le_add h₁ h₂)⟩

theorem mem_bergerTungOuter_of_achievable {p : PMF (S × T)} {d₁ : S → U → ℝ}
    {d₂ : T → V → ℝ} {R₁ R₂ D₁ D₂ : ℝ} (h : Achievable p d₁ d₂ R₁ R₂ D₁ D₂) {δ : ℝ}
    (hδ : 0 < δ) : ((R₁, R₂), D₁ + δ, D₂ + δ) ∈ bergerTungOuter p d₁ d₂ := by
  obtain ⟨st, -⟩ := p.support_nonempty
  obtain ⟨N, hN⟩ := h δ hδ
  obtain ⟨k₁, k₂, hk₁, hk₂, c, h₁, h₂⟩ := hN (max N 1) (le_max_left _ _)
  have hn : 0 < max N 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hn' : (0 : ℝ) < (max N 1 : ℕ) := Nat.cast_pos.2 hn
  have hk₁0 : (0 : ℝ) < k₁ := Nat.cast_pos.2 (Fin.pos (c.enc₁ fun _ => st.1))
  have hk₂0 : (0 : ℝ) < k₂ := Nat.cast_pos.2 (Fin.pos (c.enc₂ fun _ => st.2))
  have hl₁ := (Real.log_le_iff_le_exp hk₁0).2 hk₁
  have hl₂ := (Real.log_le_iff_le_exp hk₂0).2 hk₂
  refine bergerTungOuter_mono (code_mem_bergerTungOuter p d₁ d₂ c hn) ?_ ?_ h₁ h₂
  · rw [div_le_iff₀ hn']
    linarith
  · rw [div_le_iff₀ hn']
    linarith

theorem achievableRegion_subset_closure_bergerTungOuter (p : PMF (S × T)) (d₁ : S → U → ℝ)
    (d₂ : T → V → ℝ) : achievableRegion p d₁ d₂ ⊆ closure (bergerTungOuter p d₁ d₂) := by
  intro x hx
  have ht : Filter.Tendsto (fun δ : ℝ => (x.1, x.2.1 + δ, x.2.2 + δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : Continuous fun δ : ℝ => (x.1, x.2.1 + δ, x.2.2 + δ) := by fun_prop
    simpa using hc.tendsto 0
  exact mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ =>
    mem_bergerTungOuter_of_achievable hx hδ)

theorem closure_achievableRegion_subset_closure_bergerTungOuter (p : PMF (S × T))
    (d₁ : S → U → ℝ) (d₂ : T → V → ℝ) :
    closure (achievableRegion p d₁ d₂) ⊆ closure (bergerTungOuter p d₁ d₂) :=
  closure_minimal (achievableRegion_subset_closure_bergerTungOuter p d₁ d₂) isClosed_closure

end DistributedLossy

end Meat
