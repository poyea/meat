import Meat.Shannon.ChainRule
import Meat.Source.RateDistortionConverse

open MeasureTheory Finset Filter Topology
open scoped ENNReal

namespace Meat

structure WZCode (S T V : Type*) (n k : ℕ) where
  enc : (Fin n → S) → Fin k
  dec : Fin k × (Fin n → T) → Fin n → V

noncomputable def WZCode.distortion {S T V : Type*} [Fintype S] [Fintype T] {n k : ℕ}
    (c : WZCode S T V n k) (p : PMF (S × T)) (d : S → V → ℝ) : ℝ :=
  ∑ ω : Fin n → S × T, iidProb p ω *
    RateDistortion.blockDist d (fun i => (ω i).1) (c.dec (c.enc fun i => (ω i).1, fun i => (ω i).2))

namespace WynerZiv

section Defs

variable {S T V : Type*} [Fintype S] [Fintype T]

def Achievable (p : PMF (S × T)) (d : S → V → ℝ) (R D : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (n * R) ∧ ∃ c : WZCode S T V n k, c.distortion p d ≤ D + ε

def achievableRegion (p : PMF (S × T)) (d : S → V → ℝ) : Set (ℝ × ℝ) :=
  {x | Achievable p d x.1 x.2}

variable [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T]

noncomputable def rateRegion (p : PMF (S × T)) (d : S → V → ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ m : ℕ, ∃ q : PMF (S × T × Fin m), ∃ g : Fin m × T → V,
    q.map (fun a => (a.1, a.2.1)) = p ∧
    MarkovChain (fun a : S × T × Fin m => a.2.2) (fun a => a.1) (fun a => a.2.1) q.toMeasure ∧
    ∑ a, (q a).toReal * d a.1 (g (a.2.2, a.2.1)) ≤ x.2 ∧
    I[fun a : S × T × Fin m => a.1 : fun a => a.2.2 | fun a => a.2.1 ; q.toMeasure] ≤ x.1}

end Defs

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

variable {n : ℕ}

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


private lemma pmf_toReal_eq {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (q : PMF α) (a : α) : (q a).toReal = q.toMeasure.real {a} := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]


variable {V : Type*} {k : ℕ}

private def msgW (c : WZCode S T V n k) (ω : Fin n → S × T) : Fin k := c.enc fun j => (ω j).1

private def maskY (i : Fin n) (ω : Fin n → S × T) : Fin n → Option T :=
  fun j => if j = i then none else some (ω j).2

private def auxW (c : WZCode S T V n k) (i : Fin n) (ω : Fin n → S × T) :
    Fin k × (Fin n → Option T) :=
  (msgW c ω, maskY i ω)

private def unmask (τ : Fin n → Option T) (y : T) : Fin n → T := fun j => (τ j).getD y

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype T]
  [MeasurableSpace T] [MeasurableSingletonClass T] in
private lemma unmask_maskY (i : Fin n) (ω : Fin n → S × T) :
    unmask (maskY i ω) (ω i).2 = fun j => (ω j).2 := funext fun j => by
  by_cases h : j = i
  · subst h
    simp [unmask, maskY]
  · simp [unmask, maskY, h]

private lemma condEntropy_letter (p : PMF (S × T)) (i : Fin n) :
    H[fun ω : Fin n → S × T => (ω i).1 |
      fun ω => (fun j : {j // j ≠ i} => ω j, (ω i).2) ; iidMeasure p n] =
      H[fun ω : Fin n → S × T => (ω i).1 | fun ω => (ω i).2 ; iidMeasure p n] := by
  set μ := iidMeasure p n
  set R : (Fin n → S × T) → {j // j ≠ i} → S × T := fun ω j => ω j
  have h0 : I[R : fun ω => ((ω i).1, (ω i).2) ; μ] = 0 := indep_rest p i
  have h1 := mutualInfo_pair_eq_add_condMutualInfo μ (X := R) (Y := fun ω => (ω i).1)
    (Z := fun ω => (ω i).2)
  have h2 := mutualInfo_nonneg μ (X := R) (Y := fun ω => (ω i).2) (measurable_of_finite _)
    (measurable_of_finite _)
  have h3 := condMutualInfo_nonneg μ (X := R) (Y := fun ω => (ω i).1) (Z := fun ω => (ω i).2)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
  have h4 := condMutualInfo_eq_condEntropy_sub_condEntropy μ (X := R)
    (Y := fun ω => (ω i).1) (Z := fun ω => (ω i).2)
  linarith

private lemma rate_letter (p : PMF (S × T)) (c : WZCode S T V n k) (i : Fin n) :
    I[fun ω : Fin n → S × T => (ω i).1 : auxW c i | fun ω => (ω i).2 ; iidMeasure p n] ≤
      I[fun ω : Fin n → S × T => (ω i).1 : msgW c |
        fun ω => ((fun j => (ω j).2), seqPrefix (fun j => (ω j).1) i) ; iidMeasure p n] := by
  classical
  set μ := iidMeasure p n
  set R : (Fin n → S × T) → {j // j ≠ i} → S × T := fun ω j => ω j
  have hX : Measurable fun ω : Fin n → S × T => (ω i).1 := measurable_of_finite _
  have e1 := condMutualInfo_comm μ (X := fun ω : Fin n → S × T => (ω i).1) (Y := auxW c i)
    (Z := fun ω => (ω i).2)
  have e2 := condMutualInfo_eq_condEntropy_sub_condEntropy μ (X := auxW c i)
    (Y := fun ω : Fin n → S × T => (ω i).1) (Z := fun ω => (ω i).2)
  have e3 := condMutualInfo_comm μ (X := fun ω : Fin n → S × T => (ω i).1) (Y := msgW c)
    (Z := fun ω => ((fun j => (ω j).2), seqPrefix (fun j => (ω j).1) i))
  have e4 := condMutualInfo_eq_condEntropy_sub_condEntropy μ (X := msgW c)
    (Y := fun ω : Fin n → S × T => (ω i).1)
    (Z := fun ω => ((fun j => (ω j).2), seqPrefix (fun j => (ω j).1) i))
  have c1 := condEntropy_le_condEntropy_comp (μ := μ) hX
    (measurable_of_finite fun ω : Fin n → S × T => (R ω, (ω i).2))
    (fun q : ({j // j ≠ i} → S × T) × T =>
      ((fun j => if h : j = i then q.2 else (q.1 ⟨j, h⟩).2),
        fun j : Fin i => (q.1 ⟨⟨j, j.2.trans i.2⟩,
          fun h => absurd (congrArg Fin.val h) (Nat.ne_of_lt j.2)⟩).1))
  have hc1 : ((fun q : ({j // j ≠ i} → S × T) × T =>
      ((fun j => if h : j = i then q.2 else (q.1 ⟨j, h⟩).2),
        fun j : Fin i => (q.1 ⟨⟨j, j.2.trans i.2⟩,
          fun h => absurd (congrArg Fin.val h) (Nat.ne_of_lt j.2)⟩).1)) ∘
      fun ω : Fin n → S × T => (R ω, (ω i).2)) =
      fun ω => ((fun j => (ω j).2), seqPrefix (fun j => (ω j).1) i) := by
    funext ω
    refine Prod.ext (funext fun j => ?_) rfl
    by_cases h : j = i
    · subst h
      simp
    · simp [h, R]
  rw [hc1] at c1
  have c2 := condEntropy_letter p i
  have c3 := condEntropy_le_condEntropy_comp (μ := μ) hX
    (measurable_of_finite fun ω : Fin n → S × T =>
      (msgW c ω, ((fun j => (ω j).2), seqPrefix (fun j => (ω j).1) i)))
    (fun q : Fin k × ((Fin n → T) × (Fin i → S)) =>
      ((q.1, fun j => if j = i then none else some (q.2.1 j)), q.2.1 i))
  have hc3 : ((fun q : Fin k × ((Fin n → T) × (Fin i → S)) =>
      ((q.1, fun j => if j = i then none else some (q.2.1 j)), q.2.1 i)) ∘
      fun ω : Fin n → S × T =>
        (msgW c ω, ((fun j => (ω j).2), seqPrefix (fun j => (ω j).1) i))) =
      fun ω => (auxW c i ω, (ω i).2) := rfl
  rw [hc3] at c3
  linarith

private lemma sum_rate_le (p : PMF (S × T)) (c : WZCode S T V n k) :
    ∑ i, I[fun ω : Fin n → S × T => (ω i).1 : auxW c i | fun ω => (ω i).2 ; iidMeasure p n]
      ≤ Real.log k := by
  set μ := iidMeasure p n
  have hA := condMutualInfo_eq_sum μ (fun ω : Fin n → S × T => fun j => (ω j).1) (msgW c)
    (fun ω => fun j => (ω j).2)
  have hB := condMutualInfo_eq_condEntropy_sub_condEntropy μ
    (X := fun ω : Fin n → S × T => fun j => (ω j).1) (Y := msgW c)
    (Z := fun ω => fun j => (ω j).2)
  have h1 := condEntropy_nonneg μ (X := msgW c)
    (Y := fun ω : Fin n → S × T => ((fun j => (ω j).1), fun j => (ω j).2))
    (measurable_of_finite _) (measurable_of_finite _)
  have h2 := condEntropy_le_entropy μ (X := msgW c) (Y := fun ω : Fin n → S × T =>
    fun j => (ω j).2) (measurable_of_finite _) (measurable_of_finite _)
  have h3 := entropy_le_log_card μ (X := msgW c)
  rw [Fintype.card_fin] at h3
  have h4 := sum_le_sum fun i (_ : i ∈ univ) => rate_letter p c i
  linarith

private lemma markov_letter (p : PMF (S × T)) (c : WZCode S T V n k) (i : Fin n) :
    MarkovChain (auxW c i) (fun ω : Fin n → S × T => (ω i).1) (fun ω => (ω i).2)
      (iidMeasure p n) := by
  classical
  refine markov_of_indep _ (R := fun ω : Fin n → S × T => fun j : {j // j ≠ i} => ω j)
    (fun a ρ => (c.enc (fun j => if h : j = i then a else (ρ ⟨j, h⟩).1),
      fun j => if h : j = i then none else some (ρ ⟨j, h⟩).2))
    (fun ω => ?_) (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    (indep_rest p i)
  refine Prod.ext (congrArg c.enc (funext fun j => ?_)) (funext fun j => ?_)
  · by_cases h : j = i
    · subst h
      simp
    · simp [h]
  · by_cases h : j = i
    · subst h
      simp [auxW, maskY]
    · simp [auxW, maskY, h]

private abbrev AuxW (n k : ℕ) (T : Type*) := Fin n × (Fin k × (Fin n → Option T))

private noncomputable def tsMap (c : WZCode S T V n k) (x : Fin n × (Fin n → S × T)) :
    S × T × Fin (Fintype.card (AuxW n k T)) :=
  ((x.2 x.1).1, (x.2 x.1).2, Fintype.equivFin _ (x.1, auxW c x.1 x.2))

private noncomputable def tsPMF (p : PMF (S × T)) (hn : 0 < n) (c : WZCode S T V n k) :
    PMF (S × T × Fin (Fintype.card (AuxW n k T))) :=
  (mixPMF p hn).map (tsMap c)

private lemma tsPMF_toMeasure (p : PMF (S × T)) (hn : 0 < n) (c : WZCode S T V n k) :
    (tsPMF p hn c).toMeasure = (mixPMF p hn).toMeasure.map (tsMap c) :=
  (PMF.toMeasure_map _ _ (measurable_of_finite _)).symm

private lemma ts_marginal (p : PMF (S × T)) (hn : 0 < n) (c : WZCode S T V n k) :
    (tsPMF p hn c).map (fun ω => (ω.1, ω.2.1)) = p := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _), tsPMF_toMeasure,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  exact map_mix_const p hn (G := fun i ω => ω i) p.toMeasure fun i => map_eval_iidMeasure p i

private lemma ts_markov (p : PMF (S × T)) (hn : 0 < n) (c : WZCode S T V n k) :
    MarkovChain (fun ω : S × T × Fin (Fintype.card (AuxW n k T)) => ω.2.2) (fun ω => ω.1)
      (fun ω => ω.2.1) (tsPMF p hn c).toMeasure := by
  set ν := (mixPMF p hn).toMeasure
  set μ := iidMeasure p n
  set e₁ := Fintype.equivFin (AuxW n k T)
  rw [markovChain_def, tsPMF_toMeasure, condMutualInfo_map _ (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  change I[fun x => e₁ (x.1, auxW c x.1 x.2) : fun x => (x.2 x.1).2 |
    fun x => (x.2 x.1).1 ; ν] = 0
  have h1 : H[fun x => (e₁ (x.1, auxW c x.1 x.2), (x.2 x.1).1) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => (auxW c i ω, (ω i).1) ; μ] :=
    entropy_mix p hn _ (fun q => (e₁ (q.1, q.2.1), q.2.2)) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)) (fun i ω => (auxW c i ω, (ω i).1))
      fun x => rfl
  have h2 : H[fun x : Fin n × (Fin n → S × T) => ((x.2 x.1).2, (x.2 x.1).1) ; ν] =
      measureEntropy (p.toMeasure.map Prod.swap) := by
    rw [entropy, map_mix_const p hn (G := fun i ω => ((ω i).2, (ω i).1)) _
      fun i => map_swap_eval p i]
  have h3 : H[fun x => ((e₁ (x.1, auxW c x.1 x.2), (x.2 x.1).2), (x.2 x.1).1) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => ((auxW c i ω, (ω i).2), (ω i).1) ; μ] :=
    entropy_mix p hn _ (fun q => ((e₁ (q.1, q.2.1.1), q.2.1.2), q.2.2)) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1.1 (Prod.ext (Prod.ext h.1.1.2 h.1.2) h.2))
      (fun i ω => ((auxW c i ω, (ω i).2), (ω i).1)) fun x => rfl
  have h4 : H[fun x : Fin n × (Fin n → S × T) => (x.2 x.1).1 ; ν] =
      measureEntropy (p.toMeasure.map Prod.fst) := by
    rw [entropy, map_mix_const p hn (G := fun i ω => (ω i).1) _ fun i => map_fst_eval p i]
  have hi : ∀ i, H[fun ω => (auxW c i ω, (ω i).1) ; μ] -
      H[fun ω => ((auxW c i ω, (ω i).2), (ω i).1) ; μ] =
      measureEntropy (p.toMeasure.map Prod.fst) - measureEntropy (p.toMeasure.map Prod.swap) :=
    fun i => by
      have hm := markov_letter p c i
      have hY : H[fun ω : Fin n → S × T => ((ω i).2, (ω i).1) ; μ] =
          measureEntropy (p.toMeasure.map Prod.swap) := by rw [entropy, map_swap_eval]
      have hX : H[fun ω : Fin n → S × T => (ω i).1 ; μ] =
          measureEntropy (p.toMeasure.map Prod.fst) := by rw [entropy, map_fst_eval]
      rw [markovChain_def, condMutualInfo_def, condEntropy_def, condEntropy_def,
        condEntropy_def] at hm
      rw [hY, hX] at hm
      linarith
  have hsum : (n : ℝ)⁻¹ * ∑ i, H[fun ω => (auxW c i ω, (ω i).1) ; μ] -
      (n : ℝ)⁻¹ * ∑ i, H[fun ω => ((auxW c i ω, (ω i).2), (ω i).1) ; μ] =
      measureEntropy (p.toMeasure.map Prod.fst) - measureEntropy (p.toMeasure.map Prod.swap) := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [← mul_sub, ← sum_sub_distrib, sum_congr rfl fun i _ => hi i, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ this, one_mul]
  rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def, h1, h2, h3, h4]
  linarith

private lemma ts_rate (p : PMF (S × T)) (hn : 0 < n) (c : WZCode S T V n k) :
    I[fun ω : S × T × Fin (Fintype.card (AuxW n k T)) => ω.1 : fun ω => ω.2.2 |
      fun ω => ω.2.1 ; (tsPMF p hn c).toMeasure] ≤ Real.log k / n := by
  set ν := (mixPMF p hn).toMeasure
  set μ := iidMeasure p n
  set e₁ := Fintype.equivFin (AuxW n k T)
  rw [tsPMF_toMeasure, condMutualInfo_map _ (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  change I[fun x : Fin n × (Fin n → S × T) => (x.2 x.1).1 : fun x => e₁ (x.1, auxW c x.1 x.2) |
    fun x => (x.2 x.1).2 ; ν] ≤ _
  have t1 : H[fun x : Fin n × (Fin n → S × T) => ((x.2 x.1).1, (x.2 x.1).2) ; ν] =
      measureEntropy p.toMeasure := by
    rw [entropy, map_mix_const p hn (G := fun i ω => ω i) _ fun i => map_eval_iidMeasure p i]
  have t2 : H[fun x => (e₁ (x.1, auxW c x.1 x.2), (x.2 x.1).2) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => (auxW c i ω, (ω i).2) ; μ] :=
    entropy_mix p hn _ (fun q => (e₁ (q.1, q.2.1), q.2.2)) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)) (fun i ω => (auxW c i ω, (ω i).2))
      fun x => rfl
  have t3 : H[fun x => (((x.2 x.1).1, e₁ (x.1, auxW c x.1 x.2)), (x.2 x.1).2) ; ν] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[fun ω => (((ω i).1, auxW c i ω), (ω i).2) ; μ] :=
    entropy_mix p hn _ (fun q => ((q.2.1.1, e₁ (q.1, q.2.1.2)), q.2.2)) (fun a b h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1.2.1 (Prod.ext (Prod.ext h.1.1 h.1.2.2) h.2))
      (fun i ω => (((ω i).1, auxW c i ω), (ω i).2)) fun x => rfl
  have t4 : H[fun x : Fin n × (Fin n → S × T) => (x.2 x.1).2 ; ν] =
      measureEntropy (p.toMeasure.map Prod.snd) := by
    rw [entropy, map_mix_const p hn (G := fun i ω => (ω i).2) _ fun i => map_snd_eval p i]
  have hI : ∀ i, I[fun ω : Fin n → S × T => (ω i).1 : auxW c i | fun ω => (ω i).2 ; μ] =
      measureEntropy p.toMeasure + H[fun ω => (auxW c i ω, (ω i).2) ; μ] -
        H[fun ω => (((ω i).1, auxW c i ω), (ω i).2) ; μ] -
        measureEntropy (p.toMeasure.map Prod.snd) := fun i => by
    have hP : H[fun ω : Fin n → S × T => ((ω i).1, (ω i).2) ; μ] = measureEntropy p.toMeasure := by
      rw [entropy, ← map_eval_iidMeasure p i]
    have hY : H[fun ω : Fin n → S × T => (ω i).2 ; μ] =
        measureEntropy (p.toMeasure.map Prod.snd) := by rw [entropy, map_snd_eval]
    rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def, hP, hY]
    ring
  have hb := mul_le_mul_of_nonneg_left (sum_rate_le p c)
    (inv_nonneg.2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  rw [show iidMeasure p n = μ from rfl] at hb
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [hI, sum_add_distrib, sum_sub_distrib, mul_add, mul_sub, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul] at hb
  rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def, t1, t2, t3, t4,
    div_eq_inv_mul]
  linarith

private noncomputable def recon (c : WZCode S T V n k)
    (a : Fin (Fintype.card (AuxW n k T)) × T) : V :=
  c.dec (((Fintype.equivFin _).symm a.1).2.1,
    unmask ((Fintype.equivFin _).symm a.1).2.2 a.2) ((Fintype.equivFin _).symm a.1).1

private lemma ts_dist (p : PMF (S × T)) (hn : 0 < n) (c : WZCode S T V n k) (d : S → V → ℝ) :
    ∑ a, ((tsPMF p hn c) a).toReal * d a.1 (recon c (a.2.2, a.2.1)) = c.distortion p d := by
  simp only [pmf_toReal_eq]
  rw [tsPMF_toMeasure, ← sum_measureReal_mul_comp (mixPMF p hn).toMeasure (tsMap c)
    (fun a => d a.1 (recon c (a.2.2, a.2.1))), WZCode.distortion, Fintype.sum_prod_type,
    sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  simp only [mix_real, tsMap, recon, auxW, Equiv.symm_apply_apply, unmask_maskY, blockDist,
    div_eq_mul_inv]
  rw [sum_mul, mul_sum]
  exact sum_congr rfl fun i _ => by simp only [msgW]; ring

theorem code_mem_rateRegion (p : PMF (S × T)) (d : S → V → ℝ) (c : WZCode S T V n k)
    (hn : 0 < n) : (Real.log k / n, c.distortion p d) ∈ rateRegion p d :=
  ⟨_, tsPMF p hn c, recon c, ts_marginal p hn c, ts_markov p hn c, (ts_dist p hn c d).le,
    ts_rate p hn c⟩

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem rateRegion_mono {p : PMF (S × T)} {d : S → V → ℝ} {x y : ℝ × ℝ}
    (h : x ∈ rateRegion p d) (h₁ : x.1 ≤ y.1) (h₂ : x.2 ≤ y.2) : y ∈ rateRegion p d := by
  obtain ⟨m, q, g, hq, hm, hd, hr⟩ := h
  exact ⟨m, q, g, hq, hm, hd.trans h₂, hr.trans h₁⟩

theorem mem_rateRegion_of_achievable {p : PMF (S × T)} {d : S → V → ℝ} {R D : ℝ}
    (h : Achievable p d R D) {δ : ℝ} (hδ : 0 < δ) : (R, D + δ) ∈ rateRegion p d := by
  obtain ⟨st, -⟩ := p.support_nonempty
  obtain ⟨N, hN⟩ := h δ hδ
  obtain ⟨k, hk, c, hc⟩ := hN (max N 1) (le_max_left _ _)
  have hn : 0 < max N 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hn' : (0 : ℝ) < (max N 1 : ℕ) := Nat.cast_pos.2 hn
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (Fin.pos (c.enc fun _ => st.1))
  have hl := (Real.log_le_iff_le_exp hk0).2 hk
  refine rateRegion_mono (code_mem_rateRegion p d c hn) ?_ hc
  rw [div_le_iff₀ hn']
  linarith

theorem achievableRegion_subset_closure_rateRegion (p : PMF (S × T)) (d : S → V → ℝ) :
    achievableRegion p d ⊆ closure (rateRegion p d) := by
  intro x hx
  have ht : Tendsto (fun δ : ℝ => (x.1, x.2 + δ)) (𝓝[>] 0) (𝓝 x) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : Continuous fun δ : ℝ => (x.1, x.2 + δ) := by fun_prop
    simpa using hc.tendsto 0
  exact mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ =>
    mem_rateRegion_of_achievable hx hδ)

theorem closure_achievableRegion_subset_closure_rateRegion (p : PMF (S × T)) (d : S → V → ℝ) :
    closure (achievableRegion p d) ⊆ closure (rateRegion p d) :=
  closure_minimal (achievableRegion_subset_closure_rateRegion p d) isClosed_closure

end WynerZiv

end Meat
