import Meat.Shannon.ChainRule
import Meat.Source.RateDistortionConverse

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

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

theorem markovChain_of_indep [IsProbabilityMeasure μ] {R : Ω → D} {X : Ω → A} {Y : Ω → B}
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

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

theorem mutualInfo_rest_iidMeasure (p : PMF A) {n : ℕ} (i : Fin n) :
    I[fun ω : Fin n → A => fun j : {j // j ≠ i} => ω j : fun ω => ω i ; iidMeasure p n] = 0 := by
  classical
  set μ := iidMeasure p n
  set e := Equiv.piSplitAt i (fun _ : Fin n => A)
  have hm : ∀ b, (μ.map e).real {b} = iidProb p (e.symm b) := fun b => by
    rw [measureReal_map_singleton, sum_filter]
    rw [← Equiv.sum_comp e.symm]
    simp only [Equiv.apply_symm_apply, sum_ite_eq', mem_univ, ite_true]
    exact iidMeasure_real_singleton p _
  have hprod : ∀ b : A × ({j // j ≠ i} → A),
      iidProb p (e.symm b) = (p b.1).toReal * ∏ j, (p (b.2 j)).toReal := fun b => by
    rw [iidProb, Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [e, Equiv.piSplitAt_symm_apply]
    congr 1
    exact prod_congr rfl fun x _ => by simp [x.2]
  have h1 : (μ.map fun ω => ω i) = (μ.map e).map Prod.fst :=
    by rw [Measure.map_map measurable_fst (measurable_of_finite _)]; rfl
  have h2 : (μ.map fun ω : Fin n → A => fun j : {j // j ≠ i} => ω j) = (μ.map e).map Prod.snd :=
    by rw [Measure.map_map measurable_snd (measurable_of_finite _)]; rfl
  have h3 : (μ.map fun ω => (ω i, fun j : {j // j ≠ i} => ω j)) = μ.map e := rfl
  rw [mutualInfo_comm]
  refine mutualInfo_eq_zero_of_measureReal_eq_mul μ fun a ρ => ?_
  rw [h1, h2, h3, DMC.measureReal_map_fst, DMC.measureReal_map_snd]
  simp only [hm, hprod, ← sum_mul, ← mul_sum, sum_toReal_pmf_eq_one, one_mul]
  rw [← Fintype.prod_sum fun (j : {j // j ≠ i}) s => (p s).toReal]
  simp [sum_toReal_pmf_eq_one]

theorem condEntropy_letter_iidMeasure {S T : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (p : PMF (S × T)) {n : ℕ} (i : Fin n) :
    H[fun ω : Fin n → S × T => (ω i).1 |
      fun ω => (fun j : {j // j ≠ i} => ω j, (ω i).2) ; iidMeasure p n] =
      H[fun ω : Fin n → S × T => (ω i).1 | fun ω => (ω i).2 ; iidMeasure p n] := by
  set μ := iidMeasure p n
  set R : (Fin n → S × T) → {j // j ≠ i} → S × T := fun ω j => ω j
  have h0 : I[R : fun ω => ((ω i).1, (ω i).2) ; μ] = 0 := mutualInfo_rest_iidMeasure p i
  have h1 := mutualInfo_pair_eq_add_condMutualInfo μ (X := R) (Y := fun ω => (ω i).1)
    (Z := fun ω => (ω i).2)
  have h2 := mutualInfo_nonneg μ (X := R) (Y := fun ω => (ω i).2) (measurable_of_finite _)
    (measurable_of_finite _)
  have h3 := condMutualInfo_nonneg μ (X := R) (Y := fun ω => (ω i).1) (Z := fun ω => (ω i).2)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
  have h4 := condMutualInfo_eq_condEntropy_sub_condEntropy μ (X := R)
    (Y := fun ω => (ω i).1) (Z := fun ω => (ω i).2)
  linarith

noncomputable def iidMix (p : PMF A) {n : ℕ} (hn : 0 < n) : PMF (Fin n × (Fin n → A)) :=
  PMF.ofFintype (fun x => (n : ℝ≥0∞)⁻¹ * ∏ j, p (x.2 j)) (by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, ← Fintype.prod_sum, sum_pmf_eq_one, prod_const_one, mul_one,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n))

private lemma mix_real (p : PMF A) {n : ℕ} (hn : 0 < n) (x : Fin n × (Fin n → A)) :
    (iidMix p hn).toMeasure.real {x} = (n : ℝ)⁻¹ * iidProb p x.2 := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), iidMix,
    PMF.ofFintype_apply, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rfl

section Mix

variable {W W' : Type*} [MeasurableSpace W] [MeasurableSingletonClass W]
  [Fintype W'] [MeasurableSpace W'] [MeasurableSingletonClass W']
  (p : PMF A) {n : ℕ} (hn : 0 < n)

private lemma mix_mass (G : Fin n → (Fin n → A) → W) (i : Fin n) (w : W) :
    ((iidMix p hn).toMeasure.map fun x => (x.1, G x.1 x.2)).real {(i, w)} =
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

theorem map_iidMix_const [Finite W] (G : Fin n → (Fin n → A) → W) (ρ : Measure W)
    [IsFiniteMeasure ρ] (hG : ∀ i, (iidMeasure p n).map (G i) = ρ) :
    (iidMix p hn).toMeasure.map (fun x => G x.1 x.2) = ρ := by
  classical
  have := Fintype.ofFinite W
  refine Measure.ext_of_singleton fun w => ?_
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top ρ _)]
  congr 1
  have h : ∀ i, ∑ ω : Fin n → A,
      (if G i ω = w then (iidMix p hn).toMeasure.real {(i, ω)} else 0) =
        (n : ℝ)⁻¹ * ρ.real {w} :=
    fun i => by
      rw [← hG i, measureReal_map_singleton, sum_filter, mul_sum]
      refine sum_congr rfl fun ω _ => ?_
      split_ifs <;> simp [mix_real, iidMeasure_real_singleton]
  rw [measureReal_map_singleton, sum_filter, Fintype.sum_prod_type]
  simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem entropy_iidMix [Fintype W] (V : Fin n × (Fin n → A) → W') (e : Fin n × W → W')
    (he : Function.Injective e) (G : Fin n → (Fin n → A) → W)
    (hV : ∀ x, V x = e (x.1, G x.1 x.2)) :
    H[V ; (iidMix p hn).toMeasure] =
      Real.log n + (n : ℝ)⁻¹ * ∑ i, H[G i ; iidMeasure p n] := by
  obtain rfl : V = fun x => e (x.1, G x.1 x.2) := funext hV
  have h0 : H[fun x => e (x.1, G x.1 x.2) ; (iidMix p hn).toMeasure] =
      H[fun x => (x.1, G x.1 x.2) ; (iidMix p hn).toMeasure] :=
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

end Meat
