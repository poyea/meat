import Meat.Shannon.Conditional
import Meat.Shannon.Iid
import Meat.Source.RateDistortion

open MeasureTheory Finset Filter Topology

namespace Meat

namespace RateDistortion

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
private lemma sum_prod_pmf (p : PMF S) (n : ℕ) : ∑ x : Fin n → S, ∏ i, p (x i) = 1 := by
  rw [← Fintype.prod_sum, sum_pmf_eq_one, prod_const_one]

omit [MeasurableSingletonClass S] in
noncomputable def iidMeasure (p : PMF S) (n : ℕ) : Measure (Fin n → S) :=
  (PMF.ofFintype _ (sum_prod_pmf p n)).toMeasure

omit [MeasurableSingletonClass S] in
instance isProbabilityMeasure_iidMeasure (p : PMF S) (n : ℕ) :
    IsProbabilityMeasure (iidMeasure p n) := by
  unfold iidMeasure
  infer_instance

theorem iidMeasure_real_singleton (p : PMF S) {n : ℕ} (x : Fin n → S) :
    (iidMeasure p n).real {x} = iidProb p x := by
  rw [measureReal_def, iidMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.ofFintype_apply, ENNReal.toReal_prod]
  rfl

theorem entropy_iidMeasure (p : PMF S) (n : ℕ) :
    H[fun x => x ; iidMeasure p n] = n * measureEntropy p.toMeasure := by
  rw [entropy_def, ← sum_negMulLog_iidProb p n]
  simp_rw [Measure.map_id', iidMeasure_real_singleton]

theorem map_eval_iidMeasure (p : PMF S) {n : ℕ} (i : Fin n) :
    (iidMeasure p n).map (fun x => x i) = p.toMeasure := by
  classical
  refine Measure.ext_of_singleton fun s => ?_
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top _ _)]
  congr 1
  rw [measureReal_map_singleton, measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), sum_filter]
  simp_rw [iidMeasure_real_singleton]
  have h := sum_prod_mul_apply (fun (_ : Fin n) a => (p a).toReal)
    (fun _ => sum_toReal_pmf_eq_one p) (fun a => if a = s then (1 : ℝ) else 0) i
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h
  rw [← h]
  rfl

theorem entropy_eval_iidMeasure (p : PMF S) {n : ℕ} (i : Fin n) :
    H[fun x => x i ; iidMeasure p n] = measureEntropy p.toMeasure := by
  rw [entropy, map_eval_iidMeasure]

theorem exists_inputMutualInfo_eq [Nonempty T] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T} (hX : Measurable X) (hY : Measurable Y)
    (p : PMF S) (hp : μ.map X = p.toMeasure) (d : S → T → ℝ) :
    ∃ W : DMC S T, W.inputMutualInfo p = I[X : Y ; μ] ∧
      expDist p d W = ∑ z : S × T, (μ.map fun ω => (X ω, Y ω)).real {z} * d z.1 z.2 := by
  set ν := μ.map fun ω => (X ω, Y ω)
  have : IsProbabilityMeasure ν := inferInstance
  have hν : ν.map Prod.fst = p.toMeasure := by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    exact hp
  obtain ⟨W, hW⟩ := DMC.exists_jointMeasure_eq p ν hν
  refine ⟨W, ?_, ?_⟩
  · change I[fun ω : S × T => ω.1 : fun ω => ω.2 ; W.jointMeasure p] = _
    rw [hW, mutualInfo_map μ (hX.prodMk hY) measurable_fst measurable_snd]
    rfl
  · rw [expDist, Fintype.sum_prod_type]
    refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
    rw [← hW, DMC.jointMeasure_real_singleton]

end RateDistortion

namespace LossyCode

open RateDistortion

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {n k : ℕ}

private noncomputable def letterDist (c : LossyCode S T n k) (p : PMF S) (d : S → T → ℝ)
    (i : Fin n) : ℝ :=
  ∑ x, iidProb p x * d (x i) (c.dec (c.enc x) i)

omit [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype T] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma distortion_eq_sum (c : LossyCode S T n k) (p : PMF S) (d : S → T → ℝ) :
    c.distortion p d = ∑ i, (n : ℝ)⁻¹ * c.letterDist p d i := by
  simp only [distortion, blockDist, letterDist, div_eq_mul_inv, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun x _ => by ring

private lemma exists_letter [Nonempty T] (c : LossyCode S T n k) (p : PMF S) (d : S → T → ℝ)
    (i : Fin n) : ∃ W : DMC S T,
      W.inputMutualInfo p = I[fun x => x i : fun x => c.dec (c.enc x) i ; iidMeasure p n] ∧
      expDist p d W = c.letterDist p d i := by
  obtain ⟨W, hI, hE⟩ := exists_inputMutualInfo_eq (iidMeasure p n)
    (X := fun x => x i) (Y := fun x => c.dec (c.enc x) i) (measurable_of_finite _)
    (measurable_of_finite _) p (map_eval_iidMeasure p i) d
  refine ⟨W, hI, hE.trans ?_⟩
  rw [← sum_measureReal_mul_comp (iidMeasure p n) (fun x => (x i, c.dec (c.enc x) i))
    (fun z => d z.1 z.2)]
  simp_rw [iidMeasure_real_singleton]
  rfl

omit [Fintype T] in
theorem minDist_le_distortion [Finite T] [Nonempty T] (c : LossyCode S T n k) (p : PMF S)
    (d : S → T → ℝ) (hn : 0 < n) : minDist p d ≤ c.distortion p d := by
  have := Fintype.ofFinite T
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [distortion_eq_sum]
  calc minDist p d = ∑ _i : Fin n, (n : ℝ)⁻¹ * minDist p d := by
        rw [← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hn'.ne', one_mul]
    _ ≤ _ := sum_le_sum fun i _ => by
        obtain ⟨W, -, hE⟩ := c.exists_letter p d i
        exact mul_le_mul_of_nonneg_left (hE ▸ minDist_le_expDist p d W) (by positivity)

private lemma sum_mutualInfo_le_log (c : LossyCode S T n k) (p : PMF S) :
    ∑ i, I[fun x => x i : fun x => c.dec (c.enc x) i ; iidMeasure p n] ≤ Real.log k := by
  set μ := iidMeasure p n
  have hX : ∀ i : Fin n, Measurable fun x : Fin n → S => x i := fun i => measurable_of_finite _
  have hY : Measurable (c.dec ∘ c.enc) := measurable_of_finite _
  have h1 : H[fun x => x | c.dec ∘ c.enc ; μ] ≤ ∑ i, H[fun x => x i | c.dec ∘ c.enc ; μ] :=
    condEntropy_pi_le_sum μ hX hY
  have h2 : ∀ i, H[fun x => x i | c.dec ∘ c.enc ; μ]
      ≤ H[fun x => x i | (fun y : Fin n → T => y i) ∘ (c.dec ∘ c.enc) ; μ] :=
    fun i => condEntropy_le_condEntropy_comp (hX i) hY _
  have h3 : ∀ i, I[fun x => x i : fun x => c.dec (c.enc x) i ; μ]
      = measureEntropy p.toMeasure
        - H[fun x => x i | (fun y : Fin n → T => y i) ∘ (c.dec ∘ c.enc) ; μ] := fun i => by
    rw [mutualInfo_eq_entropy_sub_condEntropy, entropy_eval_iidMeasure]
    rfl
  have h4 : I[fun x => x : c.dec ∘ c.enc ; μ]
      = n * measureEntropy p.toMeasure - H[fun x => x | c.dec ∘ c.enc ; μ] := by
    rw [mutualInfo_eq_entropy_sub_condEntropy, entropy_iidMeasure]
  have h5 : I[fun x => x : c.dec ∘ c.enc ; μ] ≤ Real.log k := by
    rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
    have := condEntropy_nonneg μ hY (measurable_of_finite (fun x : Fin n → S => x))
    have h6 : H[c.dec ∘ c.enc ; μ] ≤ H[c.enc ; μ] :=
      entropy_comp_le μ (measurable_of_finite _) c.dec
    have h7 : H[c.enc ; μ] ≤ Real.log k := by
      simpa using entropy_le_log_card μ (X := c.enc)
    linarith
  have h8 : ∑ i, I[fun x => x i : fun x => c.dec (c.enc x) i ; μ]
      ≤ I[fun x => x : c.dec ∘ c.enc ; μ] := by
    simp only [h3, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, h4]
    linarith [sum_le_sum fun i (_ : i ∈ univ) => h2 i]
  linarith

theorem mul_rdf_le_log [Nonempty T] (c : LossyCode S T n k) (p : PMF S) (d : S → T → ℝ)
    (hn : 0 < n) : n * rdf p d (c.distortion p d) ≤ Real.log k := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  choose W hI hE using c.exists_letter p d
  have hmem : ∀ i ∈ (univ : Finset (Fin n)), c.letterDist p d i ∈ Set.Ici (minDist p d) :=
    fun i _ => Set.mem_Ici.2 (hE i ▸ minDist_le_expDist p d (W i))
  have hJ := (convexOn_rdf p d).map_sum_le (t := univ) (w := fun _ => (n : ℝ)⁻¹)
    (p := c.letterDist p d) (fun _ _ => by positivity)
    (by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hn'.ne'])
    hmem
  simp only [smul_eq_mul, ← distortion_eq_sum] at hJ
  have hle : ∀ i, rdf p d (c.letterDist p d i)
      ≤ I[fun x => x i : fun x => c.dec (c.enc x) i ; iidMeasure p n] := fun i =>
    (hI i) ▸ rdf_le_inputMutualInfo (hE i).le
  calc (n : ℝ) * rdf p d (c.distortion p d)
      ≤ n * ∑ i, (n : ℝ)⁻¹ * rdf p d (c.letterDist p d i) :=
        mul_le_mul_of_nonneg_left hJ hn'.le
    _ = ∑ i, rdf p d (c.letterDist p d i) := by
        rw [mul_sum]
        exact sum_congr rfl fun i _ => by rw [← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
    _ ≤ _ := (sum_le_sum fun i _ => hle i).trans (c.sum_mutualInfo_le_log p)

end LossyCode

namespace RateDistortion

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem mem_rateRegion_of_achievable [Nonempty T] {p : PMF S} {d : S → T → ℝ} {R D : ℝ}
    (h : Achievable p d R D) : (R, D) ∈ rateRegion p d := by
  obtain ⟨s₀, -⟩ := p.support_nonempty
  have hsub : ∀ ε : ℝ, 0 < ε → (R, D + ε) ∈ rateRegion p d := by
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    obtain ⟨k, hk, c, hc⟩ := hN (max N 1) (le_max_left _ _)
    have hn : 0 < max N 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hn' : (0 : ℝ) < (max N 1 : ℕ) := Nat.cast_pos.2 hn
    have h1 := c.minDist_le_distortion p d hn
    have h2 := c.mul_rdf_le_log p d hn
    have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (Fin.pos (c.enc fun _ => s₀))
    have hlog : Real.log k ≤ (max N 1 : ℕ) * R := (Real.log_le_iff_le_exp hk0).2 hk
    have h3 := rdf_le_rdf h1 hc
    refine ⟨h1.trans hc, ?_⟩
    have h4 : ((max N 1 : ℕ) : ℝ) * rdf p d (D + ε) ≤ (max N 1 : ℕ) * R :=
      (mul_le_mul_of_nonneg_left h3 hn'.le).trans (h2.trans hlog)
    exact le_of_mul_le_mul_left h4 hn'
  have ht : Tendsto (fun ε : ℝ => (R, D + ε)) (𝓝[>] 0) (𝓝 (R, D)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : Continuous fun ε : ℝ => (R, D + ε) :=
      continuous_const.prodMk (continuous_const.add continuous_id)
    simpa using hc.tendsto 0
  have hcl := mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall hsub)
  rwa [(isClosed_rateRegion p d).closure_eq] at hcl

end RateDistortion

end Meat
