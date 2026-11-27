import Meat.Continuous.AWGNCapacity
import Meat.Continuous.DirtyPaperAchievability

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace Meat

namespace DirtyPaper

section Bound

variable {Ω St V B T : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
  [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St]
  [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

omit [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St] [Fintype V]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private lemma integrable_prob {X : Ω → T} (hX : Measurable X) (f : T → ℝ) :
    Integrable (fun ω => f (X ω)) ν :=
  (Integrable.of_finite (f := f) (μ := ν.map X)).comp_measurable hX

omit [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St] [Fintype V]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private lemma integral_log_prob {X : Ω → T} (hX : Measurable X) :
    ∫ ω, Real.log (ν.real (X ⁻¹' {X ω})) ∂ν = -H[X ; ν] := by
  rw [DMC.integral_comp_eq_sum hX (fun x => Real.log (ν.real (X ⁻¹' {x}))), entropy_def,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_measureReal_apply hX (measurableSet_singleton _), Real.negMulLog]
  ring

omit [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St] [Fintype V]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableSpace T] [MeasurableSingletonClass T] in
private lemma ae_prob_pos (X : Ω → T) :
    ∀ᵐ ω ∂ν, 0 < ν.real (X ⁻¹' {X ω}) := by
  rw [ae_iff]
  have hsub : {ω | ¬ 0 < ν.real (X ⁻¹' {X ω})} ⊆
      ⋃ x ∈ {x | ν.real (X ⁻¹' {x}) = 0}, X ⁻¹' {x} := fun ω h => by
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, exists_prop,
      exists_eq_right']
    exact le_antisymm (not_lt.1 h) measureReal_nonneg
  exact measure_mono_null hsub ((measure_biUnion_null_iff (Set.to_countable _)).2
    fun x hx => (measureReal_eq_zero_iff).1 hx)

omit [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St] [Fintype V]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [IsProbabilityMeasure ν] in
private lemma lintegral_eq_sum_cells {X : Ω → T} (hX : Measurable X) (f : Ω → ℝ≥0∞) :
    ∫⁻ ω, f ω ∂ν = ∑ i, ∫⁻ ω in X ⁻¹' {i}, f ω ∂ν := by
  have h := lintegral_iUnion (μ := ν) (f := f) (fun i => hX (measurableSet_singleton i))
    (fun i j hij => Set.disjoint_left.2 fun ω h1 h2 => hij (h1.symm.trans h2))
  rw [tsum_fintype] at h
  rw [← h, ← Set.preimage_iUnion, Set.iUnion_of_singleton, Set.preimage_univ,
    Measure.restrict_univ]

omit [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] in
theorem integral_log_le_mutualInfo_sub {Sv : Ω → St} {U : Ω → V} {Y : Ω → B}
    (hS : Measurable Sv) (hU : Measurable U) (hY : Measurable Y) {g : Ω → ℝ}
    (hgm : Measurable g) (hg : ∀ ω, 0 < g ω) (hlog : Integrable (fun ω => Real.log (g ω)) ν)
    (Ψ : V → B → ℝ) (hΨ0 : ∀ u y, 0 ≤ Ψ u y) (hΨ : ∀ y, ∑ u, Ψ u y ≤ 1)
    (hcell : ∀ σ u y,
      (∫⁻ ω in {ω | Sv ω = σ ∧ U ω = u ∧ Y ω = y}, ENNReal.ofReal (g ω) ∂ν) *
        ν {ω | U ω = u ∧ Sv ω = σ} ≤
          ENNReal.ofReal (Ψ u y) * ν {ω | Sv ω = σ ∧ U ω = u ∧ Y ω = y} * ν {ω | Sv ω = σ}) :
    ∫ ω, Real.log (g ω) ∂ν ≤ I[U : Y ; ν] - I[U : Sv ; ν] := by
  classical
  set US : Ω → V × St := fun ω => (U ω, Sv ω)
  set UY : Ω → V × B := fun ω => (U ω, Y ω)
  set X3 : Ω → St × V × B := fun ω => (Sv ω, U ω, Y ω)
  have hUS : Measurable US := hU.prodMk hS
  have hUY : Measurable UY := hU.prodMk hY
  have hX3 : Measurable X3 := hS.prodMk (hU.prodMk hY)
  set pS : St → ℝ := fun σ => ν.real (Sv ⁻¹' {σ})
  set pY : B → ℝ := fun y => ν.real (Y ⁻¹' {y})
  set pUS : V × St → ℝ := fun p => ν.real (US ⁻¹' {p})
  set pUY : V × B → ℝ := fun p => ν.real (UY ⁻¹' {p})
  set p3 : St × V × B → ℝ := fun p => ν.real (X3 ⁻¹' {p})
  set F : Ω → ℝ := fun ω => Real.log (pUY (UY ω)) - Real.log (pY (Y ω))
    - Real.log (pUS (US ω)) + Real.log (pS (Sv ω))
  have i1 := integrable_prob ν hUY (fun p => Real.log (pUY p))
  have i2 := integrable_prob ν hY (fun p => Real.log (pY p))
  have i3 := integrable_prob ν hUS (fun p => Real.log (pUS p))
  have i4 := integrable_prob ν hS (fun p => Real.log (pS p))
  have hFi : Integrable F ν := ((i1.sub i2).sub i3).add i4
  have hF : ∫ ω, F ω ∂ν = I[U : Y ; ν] - I[U : Sv ; ν] := by
    simp only [F]
    have i12 : Integrable (fun ω => Real.log (pUY (UY ω)) - Real.log (pY (Y ω))) ν := i1.sub i2
    have i123 : Integrable (fun ω => Real.log (pUY (UY ω)) - Real.log (pY (Y ω))
        - Real.log (pUS (US ω))) ν := i12.sub i3
    rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2]
    simp only [pUY, pY, pUS, pS]
    rw [integral_log_prob ν hUY, integral_log_prob ν hY, integral_log_prob ν hUS,
      integral_log_prob ν hS, mutualInfo_def, mutualInfo_def]
    ring
  set c : St × V × B → ℝ := fun i => pUS (i.2.1, i.1) * pY i.2.2 / (pS i.1 * pUY (i.2.1, i.2.2))
  have hc0 : ∀ i, 0 ≤ c i := fun i =>
    div_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)
      (mul_nonneg measureReal_nonneg measureReal_nonneg)
  set k : Ω → ℝ := fun ω => g ω * c (X3 ω)
  have hk0 : ∀ ω, 0 ≤ k ω := fun ω => mul_nonneg (hg ω).le (hc0 _)
  have hkm : Measurable k := hgm.mul ((measurable_of_finite c).comp hX3)
  have hcell' : ∀ i : St × V × B, ENNReal.ofReal (c i) *
      ∫⁻ ω in X3 ⁻¹' {i}, ENNReal.ofReal (g ω) ∂ν ≤
        ENNReal.ofReal (Ψ i.2.1 i.2.2 * p3 i * pY i.2.2 / pUY (i.2.1, i.2.2)) := by
    rintro ⟨σ, u, y⟩
    have hset : X3 ⁻¹' {(σ, u, y)} = {ω | Sv ω = σ ∧ U ω = u ∧ Y ω = y} := by
      ext ω
      simp [X3]
    by_cases h0 : pUS (u, σ) = 0
    · simp [c, h0]
    have hUS0 : 0 < pUS (u, σ) := lt_of_le_of_ne measureReal_nonneg (Ne.symm h0)
    have hS0 : 0 < pS σ := hUS0.trans_le (measureReal_mono
      fun ω (hω : US ω = (u, σ)) => show Sv ω = σ from (Prod.ext_iff.1 hω).2)
    have hJ : ∫⁻ ω in X3 ⁻¹' {(σ, u, y)}, ENNReal.ofReal (g ω) ∂ν ≤
        ENNReal.ofReal (Ψ u y * p3 (σ, u, y) * pS σ / pUS (u, σ)) := by
      have h := hcell σ u y
      rw [← hset] at h
      have e1 : ν {ω | U ω = u ∧ Sv ω = σ} = ENNReal.ofReal (pUS (u, σ)) := by
        rw [ofReal_measureReal]
        congr 1
        ext ω
        simp [US]
      have e2 : ν {ω | Sv ω = σ} = ENNReal.ofReal (pS σ) := by
        rw [ofReal_measureReal]
        rfl
      have e3 : ν (X3 ⁻¹' {(σ, u, y)}) = ENNReal.ofReal (p3 (σ, u, y)) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
      rw [e1, e2, e3, ← ENNReal.ofReal_mul (hΨ0 u y),
        ← ENNReal.ofReal_mul (mul_nonneg (hΨ0 u y) measureReal_nonneg)] at h
      rw [ENNReal.ofReal_div_of_pos hUS0]
      exact (ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hUS0))
        (Or.inl ENNReal.ofReal_ne_top)).2 h
    calc ENNReal.ofReal (c (σ, u, y)) * ∫⁻ ω in X3 ⁻¹' {(σ, u, y)}, ENNReal.ofReal (g ω) ∂ν
        ≤ ENNReal.ofReal (c (σ, u, y)) *
            ENNReal.ofReal (Ψ u y * p3 (σ, u, y) * pS σ / pUS (u, σ)) := by gcongr
      _ = ENNReal.ofReal (c (σ, u, y) * (Ψ u y * p3 (σ, u, y) * pS σ / pUS (u, σ))) :=
          (ENNReal.ofReal_mul (hc0 _)).symm
      _ = ENNReal.ofReal (Ψ u y * p3 (σ, u, y) * pY y / pUY (u, y)) := by
          congr 1
          simp only [c]
          by_cases hy : pUY (u, y) = 0
          · simp [hy]
          · field_simp
  have hY1 : ∑ y, pY y = 1 := by
    have h := sum_measureReal_singleton_eq_one (ν.map Y)
    simpa [map_measureReal_apply hY (measurableSet_singleton _)] using h
  have hmarg : ∀ j : V × B, ∑ σ, p3 (σ, j) = pUY j := by
    intro j
    simp only [p3, pUY]
    rw [← measureReal_biUnion_finset (fun σ _ σ' _ h => Set.disjoint_left.2 fun ω h1 h2 => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff, X3, Prod.ext_iff] at h1 h2
        exact h (h1.1.symm.trans h2.1))
      fun σ _ => hX3 (measurableSet_singleton _)]
    congr 1
    ext ω
    simp [X3, UY, Prod.ext_iff]
  have hsum : ∑ i : St × V × B, Ψ i.2.1 i.2.2 * p3 i * pY i.2.2 / pUY (i.2.1, i.2.2) ≤ 1 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc ∑ j : V × B, ∑ σ, Ψ j.1 j.2 * p3 (σ, j) * pY j.2 / pUY (j.1, j.2)
        = ∑ j : V × B, Ψ j.1 j.2 * pY j.2 * (pUY j / pUY j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Prod.mk.eta]
          calc ∑ σ, Ψ j.1 j.2 * p3 (σ, j) * pY j.2 / pUY j
              = (∑ σ, p3 (σ, j)) * (Ψ j.1 j.2 * pY j.2 / pUY j) := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun σ _ => ?_
                ring
            _ = Ψ j.1 j.2 * pY j.2 * (pUY j / pUY j) := by
                rw [hmarg j]
                ring
      _ ≤ ∑ j : V × B, Ψ j.1 j.2 * pY j.2 := Finset.sum_le_sum fun j _ =>
          mul_le_of_le_one_right (mul_nonneg (hΨ0 _ _) measureReal_nonneg) (div_self_le_one _)
      _ = ∑ y, pY y * ∑ u, Ψ u y := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => mul_comm _ _
      _ ≤ ∑ y, pY y := Finset.sum_le_sum fun y _ =>
          mul_le_of_le_one_right measureReal_nonneg (hΨ y)
      _ = 1 := hY1
  have hlint : ∫⁻ ω, ENNReal.ofReal (k ω) ∂ν ≤ 1 := by
    rw [lintegral_eq_sum_cells ν hX3]
    calc ∑ i, ∫⁻ ω in X3 ⁻¹' {i}, ENNReal.ofReal (k ω) ∂ν
        = ∑ i, ENNReal.ofReal (c i) * ∫⁻ ω in X3 ⁻¹' {i}, ENNReal.ofReal (g ω) ∂ν := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [setLIntegral_congr_fun (hX3 (measurableSet_singleton i)) (g := fun ω =>
            ENNReal.ofReal (c i) * ENNReal.ofReal (g ω)) fun ω hω => by
              rw [Set.mem_preimage, Set.mem_singleton_iff] at hω
              simp only [k, hω]
              rw [mul_comm, ENNReal.ofReal_mul (hc0 i)]]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∑ i, ENNReal.ofReal (Ψ i.2.1 i.2.2 * p3 i * pY i.2.2 / pUY (i.2.1, i.2.2)) :=
          Finset.sum_le_sum fun i _ => hcell' i
      _ = ENNReal.ofReal (∑ i, Ψ i.2.1 i.2.2 * p3 i * pY i.2.2 / pUY (i.2.1, i.2.2)) :=
          (ENNReal.ofReal_sum_of_nonneg fun i _ => div_nonneg (mul_nonneg (mul_nonneg
            (hΨ0 _ _) measureReal_nonneg) measureReal_nonneg) measureReal_nonneg).symm
      _ ≤ 1 := ENNReal.ofReal_le_one.2 hsum
  have hki : Integrable k ν := ⟨hkm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hk0)).2 (hlint.trans_lt ENNReal.one_lt_top)⟩
  have hk1 : ∫ ω, k ω ∂ν ≤ 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hk0) hkm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (hlint.trans ENNReal.ofReal_one.ge)
  have hpt : ∀ᵐ ω ∂ν, Real.log (g ω) ≤ F ω + (k ω - 1) := by
    filter_upwards [ae_prob_pos ν US, ae_prob_pos ν UY, ae_prob_pos ν Sv, ae_prob_pos ν Y]
      with ω h1 h2 h3 h4
    have hkpos : 0 < k ω := mul_pos (hg ω) (div_pos (mul_pos h1 h4) (mul_pos h3 h2))
    have hkω : Real.log (k ω) = Real.log (g ω) + Real.log (pUS (US ω)) + Real.log (pY (Y ω))
        - Real.log (pS (Sv ω)) - Real.log (pUY (UY ω)) := by
      change Real.log (g ω * (pUS (US ω) * pY (Y ω) / (pS (Sv ω) * pUY (UY ω)))) = _
      rw [Real.log_mul (hg ω).ne' (div_pos (mul_pos h1 h4) (mul_pos h3 h2)).ne',
        Real.log_div (mul_pos h1 h4).ne' (mul_pos h3 h2).ne', Real.log_mul h1.ne' h4.ne',
        Real.log_mul h3.ne' h2.ne']
      ring
    have := Real.log_le_sub_one_of_pos hkpos
    simp only [F]
    linarith
  have hk1' : Integrable (fun ω => k ω - 1) ν := hki.sub (integrable_const 1)
  calc ∫ ω, Real.log (g ω) ∂ν ≤ ∫ ω, F ω + (k ω - 1) ∂ν :=
        integral_mono_ae hlog (hFi.add hk1') hpt
    _ = ∫ ω, F ω ∂ν + (∫ ω, k ω ∂ν - 1) := by
        rw [integral_add hFi hk1', integral_sub hki (integrable_const 1)]
        simp
    _ ≤ I[U : Y ; ν] - I[U : Sv ; ν] := by rw [hF]; linarith

end Bound

section Letter

private noncomputable def sHat (n : ℕ) (s : ℝ) : ℝ := AWGN.value n (AWGN.level n s)

private noncomputable def xIn (α : ℝ) (n : ℕ) (t s : ℝ) : ℝ :=
  AWGN.value n (AWGN.level n (t + α * sHat n s)) - α * sHat n s

private noncomputable def mOut (α : ℝ) (n : ℕ) (x s z : ℝ) : ℝ :=
  α * AWGN.value n (AWGN.level n (x + s + z)) - α * sHat n s

private lemma measurable_sHat (n : ℕ) : Measurable (sHat n) := AWGN.measurable_value_level n

private lemma measurable_xIn (α : ℝ) (n : ℕ) {β : Type*} [MeasurableSpace β] {f g : β → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun b => xIn α n (f b) (g b) :=
  ((AWGN.measurable_value_level n).comp (hf.add (((measurable_sHat n).comp hg).const_mul α))).sub
    (((measurable_sHat n).comp hg).const_mul α)

private lemma measurable_mOut (α : ℝ) (n : ℕ) {β : Type*} [MeasurableSpace β] {f g h : β → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable fun b => mOut α n (f b) (g b) (h b) :=
  (((AWGN.measurable_value_level n).comp ((hf.add hg).add hh)).const_mul α).sub
    (((measurable_sHat n).comp hg).const_mul α)

private lemma abs_mul_le_of_le_one {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (x : ℝ) : |α * x| ≤ |x| := by
  rw [abs_mul, abs_of_nonneg h0]
  exact mul_le_of_le_one_left (abs_nonneg _) h1

private lemma abs_xIn_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (n : ℕ) (t s : ℝ) :
    |xIn α n t s| ≤ |t| + 2 * |s| + 3 := by
  have e1 := AWGN.abs_value_level_le n s
  have e2 := abs_mul_le_of_le_one h0 h1 (sHat n s)
  have e3 := AWGN.abs_value_level_le n (t + α * sHat n s)
  have e4 := abs_add_le t (α * sHat n s)
  have e5 := abs_sub (AWGN.value n (AWGN.level n (t + α * sHat n s))) (α * sHat n s)
  simp only [xIn, sHat] at *
  linarith

private lemma abs_mOut_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (n : ℕ) (x s z : ℝ) :
    |mOut α n x s z| ≤ |x| + 2 * |s| + |z| + 2 := by
  have e1 := AWGN.abs_value_level_le n s
  have e2 := abs_mul_le_of_le_one h0 h1 (sHat n s)
  have e3 := AWGN.abs_value_level_le n (x + s + z)
  have e4 := abs_mul_le_of_le_one h0 h1 (AWGN.value n (AWGN.level n (x + s + z)))
  have e5 := abs_sub (α * AWGN.value n (AWGN.level n (x + s + z))) (α * sHat n s)
  have e6 := abs_add_le (x + s) z
  have e7 := abs_add_le x s
  simp only [mOut, sHat] at *
  linarith

private lemma abs_mOut_le_n {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (n : ℕ) (x s z : ℝ) :
    |mOut α n x s z| ≤ 2 * n := by
  have e1 := (abs_mul_le_of_le_one h0 h1 (sHat n s)).trans (AWGN.abs_value_le n _)
  have e2 := (abs_mul_le_of_le_one h0 h1 _).trans (AWGN.abs_value_le n (AWGN.level n (x + s + z)))
  have e3 := abs_sub (α * AWGN.value n (AWGN.level n (x + s + z))) (α * sHat n s)
  simp only [mOut] at *
  linarith

private noncomputable def letterSq (α : ℝ) (n : ℕ) (w : ℝ × ℝ × ℝ) : ℝ :=
  (w.1 - mOut α n (xIn α n w.1 w.2.1) w.2.1 w.2.2) ^ 2

private lemma measurable_letterSq (α : ℝ) (n : ℕ) : Measurable (letterSq α n) :=
  (measurable_fst.sub (measurable_mOut α n (measurable_xIn α n measurable_fst
    (measurable_fst.comp measurable_snd)) (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd))).pow_const 2

private lemma letterSq_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (n : ℕ) (w : ℝ × ℝ × ℝ) :
    letterSq α n w ≤ 16 * w.1 ^ 2 + 64 * w.2.1 ^ 2 + 4 * w.2.2 ^ 2 + 100 := by
  have e1 := abs_xIn_le h0 h1 n w.1 w.2.1
  have e2 := abs_mOut_le h0 h1 n (xIn α n w.1 w.2.1) w.2.1 w.2.2
  have e3 := abs_sub w.1 (mOut α n (xIn α n w.1 w.2.1) w.2.1 w.2.2)
  have hM : |w.1 - mOut α n (xIn α n w.1 w.2.1) w.2.1 w.2.2|
      ≤ 2 * |w.1| + 4 * |w.2.1| + |w.2.2| + 5 := by linarith
  have h := pow_le_pow_left₀ (abs_nonneg _) hM 2
  rw [sq_abs] at h
  unfold letterSq
  nlinarith [sq_abs w.1, sq_abs w.2.1, sq_abs w.2.2, abs_nonneg w.1, abs_nonneg w.2.1,
    abs_nonneg w.2.2, sq_nonneg (2 * |w.1| - 4 * |w.2.1|), sq_nonneg (2 * |w.1| - |w.2.2|),
    sq_nonneg (2 * |w.1| - 5), sq_nonneg (4 * |w.2.1| - |w.2.2|), sq_nonneg (4 * |w.2.1| - 5),
    sq_nonneg (|w.2.2| - 5)]

variable (θ Q N : ℝ)

private noncomputable abbrev ρ : Measure (ℝ × ℝ × ℝ) :=
  (gaussianReal 0 θ.toNNReal).prod ((gaussianReal 0 Q.toNNReal).prod (gaussianReal 0 N.toNNReal))

private lemma integrable_letterBound :
    Integrable (fun w : ℝ × ℝ × ℝ => 16 * w.1 ^ 2 + 64 * w.2.1 ^ 2 + 4 * w.2.2 ^ 2 + 100)
      (ρ θ Q N) :=
  (((((AWGN.integrable_sq_gaussianReal _).comp_fst _).const_mul 16).add
    ((((AWGN.integrable_sq_gaussianReal _).comp_fst _).comp_snd _).const_mul 64)).add
    ((((AWGN.integrable_sq_gaussianReal _).comp_snd _).comp_snd _).const_mul 4)).add
    (integrable_const _)

private lemma integrable_letterSq {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (n : ℕ) :
    Integrable (letterSq α n) (ρ θ Q N) :=
  (integrable_letterBound θ Q N).mono' (measurable_letterSq α n).aestronglyMeasurable
    (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact letterSq_le h0 h1 n w)

private lemma integral_letterSq_limit (α : ℝ) :
    ∫ w, (w.1 - α * (w.1 + w.2.2)) ^ 2 ∂(ρ θ Q N)
      = (1 - α) ^ 2 * θ.toNNReal + α ^ 2 * N.toNNReal := by
  have hmp : MeasurePreserving (Prod.map id Prod.snd) (ρ θ Q N)
      ((gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 N.toNNReal)) :=
    (MeasurePreserving.id _).prod measurePreserving_snd
  rw [← AWGN.integral_post_limit θ N α, ← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by fun_prop)]
  rfl

private lemma tendsto_integral_letterSq {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    Tendsto (fun n => ∫ w, letterSq α n w ∂(ρ θ Q N)) atTop
      (𝓝 ((1 - α) ^ 2 * θ.toNNReal + α ^ 2 * N.toNNReal)) := by
  rw [← integral_letterSq_limit θ Q N α]
  refine tendsto_integral_of_dominated_convergence _
    (fun n => (measurable_letterSq α n).aestronglyMeasurable) (integrable_letterBound θ Q N)
    (fun n => ae_of_all _ fun w => ?_) (ae_of_all _ fun w => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact letterSq_le h0 h1 n w
  · have hs : Tendsto (fun n => sHat n w.2.1) atTop (𝓝 w.2.1) :=
      AWGN.tendsto_value_level tendsto_const_nhds
    have hx : Tendsto (fun n => xIn α n w.1 w.2.1) atTop (𝓝 w.1) := by
      have := (AWGN.tendsto_value_level ((tendsto_const_nhds (x := w.1)).add
        (hs.const_mul α))).sub (hs.const_mul α)
      simpa [xIn] using this
    have hm : Tendsto (fun n => mOut α n (xIn α n w.1 w.2.1) w.2.1 w.2.2) atTop
        (𝓝 (α * (w.1 + w.2.1 + w.2.2) - α * w.2.1)) :=
      ((AWGN.tendsto_value_level ((hx.add_const _).add_const _)).const_mul α).sub
        (hs.const_mul α)
    have := (tendsto_const_nhds (x := w.1).sub hm).pow 2
    rwa [show (w.1 - (α * (w.1 + w.2.1 + w.2.2) - α * w.2.1)) ^ 2
      = (w.1 - α * (w.1 + w.2.2)) ^ 2 by ring] at this

private noncomputable def letterLog (θ N : ℝ) (n : ℕ) (w : ℝ × ℝ × ℝ) : ℝ :=
  Real.log (AWGN.postRatio θ (θ * N / (θ + N))
    (mOut (θ / (θ + N)) n (xIn (θ / (θ + N)) n w.1 w.2.1) w.2.1 w.2.2) w.1)

private noncomputable def letterGain (n : ℕ) : ℝ := ∫ w, letterLog θ N n w ∂(ρ θ Q N)

private lemma letterLog_eq {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n : ℕ) (w : ℝ × ℝ × ℝ) :
    letterLog θ N n w = (1 / 2) * Real.log (θ / (θ * N / (θ + N))) + w.1 ^ 2 / (2 * θ)
      - letterSq (θ / (θ + N)) n w / (2 * (θ * N / (θ + N))) :=
  AWGN.log_postRatio hθ (by positivity) _ _

private lemma integrable_letterLog {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n : ℕ) :
    Integrable (letterLog θ N n) (ρ θ Q N) := by
  have hα0 : 0 ≤ θ / (θ + N) := by positivity
  have hα1 : θ / (θ + N) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have h2 : Integrable (fun w : ℝ × ℝ × ℝ => (1 / 2) * Real.log (θ / (θ * N / (θ + N)))
      + w.1 ^ 2 / (2 * θ)) (ρ θ Q N) :=
    (integrable_const _).add (((AWGN.integrable_sq_gaussianReal _).comp_fst _).div_const _)
  simp_rw [funext (letterLog_eq hθ hN n)]
  exact h2.sub ((integrable_letterSq θ Q N hα0 hα1 n).div_const _)

private lemma letterGain_eq {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n : ℕ) :
    letterGain θ Q N n = (1 / 2) * Real.log (θ / (θ * N / (θ + N))) + 1 / 2
      - (∫ w, letterSq (θ / (θ + N)) n w ∂(ρ θ Q N)) / (2 * (θ * N / (θ + N))) := by
  have hα0 : 0 ≤ θ / (θ + N) := by positivity
  have hα1 : θ / (θ + N) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have h1 : Integrable (fun w : ℝ × ℝ × ℝ => w.1 ^ 2 / (2 * θ)) (ρ θ Q N) :=
    ((AWGN.integrable_sq_gaussianReal _).comp_fst _).div_const _
  have h2 : Integrable (fun w : ℝ × ℝ × ℝ => (1 / 2) * Real.log (θ / (θ * N / (θ + N)))
      + w.1 ^ 2 / (2 * θ)) (ρ θ Q N) := (integrable_const _).add h1
  simp_rw [letterGain, letterLog_eq hθ hN]
  rw [integral_sub h2 ((integrable_letterSq θ Q N hα0 hα1 n).div_const _),
    integral_add (integrable_const _) h1, integral_div, integral_div,
    integral_fun_fst (fun t => t ^ 2), AWGN.integral_sq_gaussianReal]
  simp only [Real.coe_toNNReal _ hθ.le, probReal_univ, smul_eq_mul, one_mul, integral_const]
  field_simp

private lemma tendsto_letterGain {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) :
    Tendsto (letterGain θ Q N) atTop (𝓝 (awgnCapacity θ N)) := by
  have hα0 : 0 ≤ θ / (θ + N) := by positivity
  have hα1 : θ / (θ + N) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hL : (1 / 2) * Real.log (θ / (θ * N / (θ + N))) + 1 / 2
      - ((1 - θ / (θ + N)) ^ 2 * (θ.toNNReal : ℝ) + (θ / (θ + N)) ^ 2 * (N.toNNReal : ℝ))
        / (2 * (θ * N / (θ + N))) = awgnCapacity θ N := by
    rw [Real.coe_toNNReal _ hθ.le, Real.coe_toNNReal _ hN.le, awgnCapacity,
      show θ / (θ * N / (θ + N)) = 1 + θ / N by field_simp; ring,
      show ((1 - θ / (θ + N)) ^ 2 * θ + (θ / (θ + N)) ^ 2 * N) / (2 * (θ * N / (θ + N)))
        = 1 / 2 by field_simp; ring]
    ring
  rw [← hL]
  exact Tendsto.congr (fun n => (letterGain_eq Q hθ hN n).symm)
    (tendsto_const_nhds.sub ((tendsto_integral_letterSq θ Q N hα0 hα1).div_const _))

end Letter

section Cell

private noncomputable abbrev Kc (n L : ℕ) : ℕ := Fintype.card (Fin L → AWGN.Level n)

private noncomputable abbrev eK (n L : ℕ) : (Fin L → AWGN.Level n) ≃ Fin (Kc n L) :=
  Fintype.equivFin (Fin L → AWGN.Level n)

private lemma eK_symm_blockQuant (n L : ℕ) (y : Fin L → ℝ) (l : Fin L) :
    (eK n L).symm (AWGN.blockQuant n L y) l = AWGN.level n (y l) := by
  simp [AWGN.blockQuant]

private lemma blockQuant_eq_iff {n L : ℕ} (y : Fin L → ℝ) (u : Fin (Kc n L)) :
    AWGN.blockQuant n L y = u ↔ ∀ l, AWGN.level n (y l) = (eK n L).symm u l := by
  rw [AWGN.blockQuant, ← Equiv.eq_symm_apply, funext_iff]

private lemma toNNReal_ne_zero' {x : ℝ} (hx : 0 < x) : x.toNNReal ≠ 0 := by
  simpa using hx

private lemma integrable_postRatio {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) (m : ℝ) :
    Integrable (AWGN.postRatio θ s m) (gaussianReal 0 θ.toNNReal) :=
  Integrable.of_integral_ne_zero (by rw [AWGN.integral_postRatio hθ hs]; exact one_ne_zero)

private lemma integral_indicator_postRatio {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) (m c : ℝ)
    {K : Set ℝ} (hK : MeasurableSet K) :
    ∫ t, {t | t + c ∈ K}.indicator (AWGN.postRatio θ s (m - c)) t ∂gaussianReal 0 θ.toNNReal
      = (gaussianReal m s.toNNReal K).toReal := by
  have hI : MeasurableSet {t : ℝ | t + c ∈ K} := (measurable_id.add_const c) hK
  rw [integral_gaussianReal_eq_integral_smul (toNNReal_ne_zero' hθ)]
  have e : ∀ t, gaussianPDFReal 0 θ.toNNReal t •
      {t | t + c ∈ K}.indicator (AWGN.postRatio θ s (m - c)) t
      = {t | t + c ∈ K}.indicator (gaussianPDFReal (m - c) s.toNNReal) t := by
    intro t
    by_cases ht : t ∈ {t : ℝ | t + c ∈ K}
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, AWGN.postRatio,
        mul_div_cancel₀ _ (gaussianPDFReal_pos _ _ _ (toNNReal_ne_zero' hθ)).ne']
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  simp_rw [e]
  rw [integral_indicator hI]
  have h1 := gaussianReal_apply_eq_integral (m - c) (toNNReal_ne_zero' hs) {t | t + c ∈ K}
  have h2 : gaussianReal (m - c) s.toNNReal {t | t + c ∈ K} = gaussianReal m s.toNNReal K := by
    rw [show {t : ℝ | t + c ∈ K} = (· + c) ⁻¹' K from rfl,
      ← Measure.map_apply (measurable_add_const c) hK, gaussianReal_map_add_const, sub_add_cancel]
  rw [← h2, h1, ENNReal.toReal_ofReal (setIntegral_nonneg hI fun t _ =>
    gaussianPDFReal_nonneg _ _ _)]

private lemma setLIntegral_cell {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) (n L : ℕ)
    (c m : Fin L → ℝ) (u : Fin (Kc n L)) :
    ∫⁻ t in {t | AWGN.blockQuant n L (fun l => t l + c l) = u},
        ENNReal.ofReal (∏ l, AWGN.postRatio θ s (m l - c l) (t l)) ∂AWGN.noise θ L
      = ENNReal.ofReal (∏ l, (gaussianReal (m l) s.toNNReal
          (AWGN.level n ⁻¹' {(eK n L).symm u l})).toReal) := by
  set I : Fin L → Set ℝ := fun l => {x | x + c l ∈ AWGN.level n ⁻¹' {(eK n L).symm u l}}
  have hI : ∀ l, MeasurableSet (I l) := fun l =>
    (measurable_id.add_const (c l)) ((AWGN.measurable_level n) (measurableSet_singleton _))
  have hC : {t : Fin L → ℝ | AWGN.blockQuant n L (fun l => t l + c l) = u} = Set.pi Set.univ I := by
    ext t
    simp [blockQuant_eq_iff, I]
  set F : (Fin L → ℝ) → ℝ := fun t => ∏ l, (I l).indicator (AWGN.postRatio θ s (m l - c l)) (t l)
  have hF0 : ∀ t, 0 ≤ F t := fun t => Finset.prod_nonneg fun l _ =>
    Set.indicator_nonneg (fun x _ => (AWGN.postRatio_pos hθ hs _ _).le) _
  have hind : ∀ t, (Set.pi Set.univ I).indicator
      (fun t => ENNReal.ofReal (∏ l, AWGN.postRatio θ s (m l - c l) (t l))) t
      = ENNReal.ofReal (F t) := by
    intro t
    by_cases ht : t ∈ Set.pi Set.univ I
    · rw [Set.indicator_of_mem ht]
      congr 1
      exact Finset.prod_congr rfl fun l _ =>
        (Set.indicator_of_mem (ht l (Set.mem_univ l)) _).symm
    · rw [Set.indicator_of_notMem ht]
      obtain ⟨l, hl⟩ : ∃ l, t l ∉ I l := by simpa [Set.mem_pi] using ht
      simp only [F]
      rw [Finset.prod_eq_zero (i := l) (Finset.mem_univ l) (Set.indicator_of_notMem hl _),
        ENNReal.ofReal_zero]
  have hFi : Integrable F (AWGN.noise θ L) :=
    Integrable.fintype_prod fun l => (integrable_postRatio hθ hs _).indicator (hI l)
  rw [hC, ← lintegral_indicator (MeasurableSet.univ_pi hI), funext hind,
    ← ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF0)]
  congr 1
  simp only [F, AWGN.noise]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl fun l _ => integral_indicator_postRatio hθ hs _ _
    ((AWGN.measurable_level n) (measurableSet_singleton _))

private lemma sum_cell_le (n L : ℕ) (m : Fin L → ℝ) (s : ℝ≥0) :
    ∑ u : Fin (Kc n L), ∏ l, (gaussianReal (m l) s
      (AWGN.level n ⁻¹' {(eK n L).symm u l})).toReal ≤ 1 := by
  rw [← (eK n L).sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [← Fintype.prod_sum (fun l k => (gaussianReal (m l) s (AWGN.level n ⁻¹' {k})).toReal)]
  refine le_of_eq (Finset.prod_eq_one fun l _ => ?_)
  have h := sum_measureReal_singleton_eq_one ((gaussianReal (m l) s).map (AWGN.level n))
  simpa [map_measureReal_apply (AWGN.measurable_level n) (measurableSet_singleton _),
    measureReal_def] using h

end Cell

section Kernel

variable {St A B : Type*} [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [MeasurableSpace B]
  [MeasurableSingletonClass B] {L : ℕ}

omit [DecidableEq A] [DecidableEq B] in
private lemma letter_toMeasure (Q N : ℝ) {qs : (Fin L → ℝ) → St} (hqs : Measurable qs)
    (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B} (hq : Measurable q) :
    (letter Q N hqs a hq).toMeasure = ((AWGN.noise Q L).prod (AWGN.noise N L)).map
      fun w => (qs w.1, fun x => q (a x + w.1 + w.2)) := by
  unfold letter
  rw [Measure.toPMF_toMeasure]

omit [Fintype St] [MeasurableSingletonClass St] [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B] [MeasurableSingletonClass B] in
private lemma measurable_letterMap' {qs : (Fin L → ℝ) → St} (hqs : Measurable qs)
    (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B} (hq : Measurable q) :
    Measurable fun w : (Fin L → ℝ) × (Fin L → ℝ) => (qs w.1, fun x => q (a x + w.1 + w.2)) :=
  (hqs.comp measurable_fst).prodMk (measurable_pi_iff.2 fun _ =>
    hq.comp ((measurable_const.add measurable_fst).add measurable_snd))

omit [DecidableEq A] [DecidableEq B] in
private lemma stateLaw_eq (Q N : ℝ) {qs : (Fin L → ℝ) → St} (hqs : Measurable qs)
    (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B} (hq : Measurable q) (σ : St) :
    stateLaw Q N hqs a hq σ = ((AWGN.noise Q L).prod (AWGN.noise N L)) {w | qs w.1 = σ} := by
  have hF := measurable_letterMap' hqs a hq
  rw [← PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton σ), stateLaw,
    PMF.toMeasure_map_apply _ _ _ measurable_fst (measurableSet_singleton σ), letter_toMeasure,
    Measure.map_apply hF (measurable_fst (measurableSet_singleton σ))]
  rfl

private lemma out_eq (Q N : ℝ) {qs : (Fin L → ℝ) → St} (hqs : Measurable qs)
    (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B} (hq : Measurable q) (x : A) (σ : St) (y : B) :
    ((AWGN.noise Q L).prod (AWGN.noise N L)) {w | qs w.1 = σ ∧ q (a x + w.1 + w.2) = y}
      = stateLaw Q N hqs a hq σ * chan Q N hqs a hq (x, σ) y := by
  have hF := measurable_letterMap' hqs a hq
  rw [stateLaw_mul_chan]
  have e : ∀ f, letter Q N hqs a hq (σ, f) = (((AWGN.noise Q L).prod (AWGN.noise N L)).map
      fun w => (qs w.1, fun x => q (a x + w.1 + w.2))) {(σ, f)} := fun f => by
    rw [← PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), letter_toMeasure]
  simp_rw [e]
  rw [← measure_biUnion_finset (fun f _ g _ h => Set.disjoint_singleton.2 fun e =>
      h (Prod.ext_iff.1 e).2) (fun _ _ => measurableSet_singleton _),
    Measure.map_apply hF (Finset.measurableSet_biUnion _ fun _ _ => measurableSet_singleton _)]
  congr 1
  ext w
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff,
    Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff, exists_prop]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, h1, rfl⟩
  · rintro ⟨f, hf, h1, rfl⟩
    exact ⟨h1, hf⟩

end Kernel

section Vars

variable (α P : ℝ) (n L : ℕ)

private noncomputable def sv (σ : Fin (Kc n L)) : Fin L → ℝ :=
  fun l => AWGN.value n ((eK n L).symm σ l)

private noncomputable def clip (w : Fin L → ℝ) : Fin L → ℝ :=
  if ∑ l, w l ^ 2 ≤ L * P then w else 0

private noncomputable def inp (x : Fin (Kc n L * Kc n L)) : Fin L → ℝ :=
  clip P L fun l => AWGN.value n ((eK n L).symm (finProdFinEquiv.symm x).1 l)
    - α * sv n L (finProdFinEquiv.symm x).2 l

private noncomputable def svar (ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ)) : Fin (Kc n L) :=
  AWGN.blockQuant n L ω.2.1

private noncomputable def uvar (ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ)) : Fin (Kc n L) :=
  AWGN.blockQuant n L fun l => ω.1 l + α * sv n L (svar n L ω) l

private noncomputable def xvar (ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ)) :
    Fin (Kc n L * Kc n L) :=
  finProdFinEquiv (uvar α n L ω, svar n L ω)

private noncomputable def yvar (ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ)) : Fin (Kc n L) :=
  AWGN.blockQuant n L (inp α P n L (xvar α n L ω) + ω.2.1 + ω.2.2)

private noncomputable def gvar (θ s : ℝ) (ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ)) : ℝ :=
  ∏ l, AWGN.postRatio θ s (α * AWGN.value n ((eK n L).symm (yvar α P n L ω) l)
    - α * sv n L (svar n L ω) l) (ω.1 l)

private lemma sum_sq_clip_le {P : ℝ} (hP : 0 ≤ P) (w : Fin L → ℝ) :
    ∑ l, clip P L w l ^ 2 ≤ L * P := by
  unfold clip
  split_ifs with h
  · exact h
  · simpa using mul_nonneg (Nat.cast_nonneg L) hP

private lemma measurable_svar : Measurable (svar n L) :=
  (AWGN.measurable_blockQuant n L).comp (measurable_fst.comp measurable_snd)

private lemma measurable_sv_svar (l : Fin L) : Measurable fun ω => sv n L (svar n L ω) l :=
  (measurable_of_finite fun σ => sv n L σ l).comp (measurable_svar n L)

private lemma measurable_uvar : Measurable (uvar α n L) :=
  (AWGN.measurable_blockQuant n L).comp (measurable_pi_iff.2 fun l =>
    ((measurable_pi_apply l).comp measurable_fst).add ((measurable_sv_svar n L l).const_mul α))

private lemma measurable_xvar : Measurable (xvar α n L) :=
  (measurable_of_finite fun p : Fin (Kc n L) × Fin (Kc n L) => finProdFinEquiv p).comp
    ((measurable_uvar α n L).prodMk (measurable_svar n L))

private lemma measurable_yvar : Measurable (yvar α P n L) :=
  (AWGN.measurable_blockQuant n L).comp ((((measurable_of_finite (inp α P n L)).comp
    (measurable_xvar α n L)).add (measurable_fst.comp measurable_snd)).add
    (measurable_snd.comp measurable_snd))

private lemma measurable_postRatio (θ s : ℝ) {β : Type*} [MeasurableSpace β] {f g : β → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => AWGN.postRatio θ s (f b) (g b) :=
  (measurable_uncurry_gaussianPDFReal.comp (hf.prodMk (measurable_const.prodMk hg))).div
    ((measurable_gaussianPDFReal _ _).comp hg)

private lemma measurable_gvar (θ s : ℝ) : Measurable (gvar α P n L θ s) :=
  Finset.measurable_prod _ fun l _ => measurable_postRatio θ s
    ((((measurable_of_finite fun y : Fin (Kc n L) =>
      AWGN.value n ((eK n L).symm y l)).comp (measurable_yvar α P n L)).const_mul α).sub
      ((measurable_sv_svar n L l).const_mul α))
    ((measurable_pi_apply l).comp measurable_fst)

private lemma sv_svar (ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ)) (l : Fin L) :
    sv n L (svar n L ω) l = sHat n (ω.2.1 l) := by
  simp [sv, svar, eK_symm_blockQuant, sHat]

private lemma inp_xvar (ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ)) :
    inp α P n L (xvar α n L ω) = clip P L fun l => xIn α n (ω.1 l) (ω.2.1 l) := by
  simp [inp, xvar, uvar, eK_symm_blockQuant, sv_svar, xIn]

private lemma log_gvar {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s)
    (ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ)) :
    Real.log (gvar α P n L θ s ω) = ∑ l, Real.log (AWGN.postRatio θ s
      (mOut α n (clip P L (fun l => xIn α n (ω.1 l) (ω.2.1 l)) l) (ω.2.1 l) (ω.2.2 l))
        (ω.1 l)) := by
  rw [gvar, Real.log_prod fun l _ => (AWGN.postRatio_pos hθ hs _ _).ne']
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [yvar, eK_symm_blockQuant, sv_svar, inp_xvar, mOut, Pi.add_apply]

end Vars

section Capacity

variable (α P : ℝ) (n L : ℕ)

private lemma set_cell (σ u : Fin (Kc n L)) (y : Fin (Kc n L)) :
    {ω | svar n L ω = σ ∧ uvar α n L ω = u ∧ yvar α P n L ω = y} =
      {t | AWGN.blockQuant n L (fun l => t l + α * sv n L σ l) = u} ×ˢ
        {w | AWGN.blockQuant n L w.1 = σ ∧
          AWGN.blockQuant n L (inp α P n L (finProdFinEquiv (u, σ)) + w.1 + w.2) = y} := by
  ext ⟨t, w⟩
  simp only [Set.mem_prod, svar, uvar, yvar, xvar]
  constructor
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨hu, hσ, hy⟩
    subst hσ
    subst hu
    exact ⟨rfl, rfl, hy⟩

private lemma set_cell' (σ u : Fin (Kc n L)) (y : Fin (Kc n L)) :
    {ω | (svar n L ω, uvar α n L ω, xvar α n L ω) = (σ, u, finProdFinEquiv (u, σ)) ∧
      yvar α P n L ω = y} =
      {t | AWGN.blockQuant n L (fun l => t l + α * sv n L σ l) = u} ×ˢ
        {w | AWGN.blockQuant n L w.1 = σ ∧
          AWGN.blockQuant n L (inp α P n L (finProdFinEquiv (u, σ)) + w.1 + w.2) = y} := by
  rw [← set_cell]
  ext ω
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, xvar]
  constructor
  · rintro ⟨⟨h1, h2, -⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, by rw [h1, h2]⟩, h3⟩

private lemma set_state (σ u : Fin (Kc n L)) :
    {ω | uvar α n L ω = u ∧ svar n L ω = σ} =
      {t | AWGN.blockQuant n L (fun l => t l + α * sv n L σ l) = u} ×ˢ
        {w : (Fin L → ℝ) × (Fin L → ℝ) | AWGN.blockQuant n L w.1 = σ} := by
  ext ⟨t, w⟩
  simp only [Set.mem_prod, svar, uvar]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨hu, hσ⟩
    subst hσ
    exact ⟨hu, rfl⟩

private lemma set_state' (σ u : Fin (Kc n L)) :
    {ω | (svar n L ω, uvar α n L ω, xvar α n L ω) = (σ, u, finProdFinEquiv (u, σ))} =
      {t | AWGN.blockQuant n L (fun l => t l + α * sv n L σ l) = u} ×ˢ
        {w : (Fin L → ℝ) × (Fin L → ℝ) | AWGN.blockQuant n L w.1 = σ} := by
  rw [← set_state]
  ext ω
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq, xvar]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨h1, h2, by rw [h1, h2]⟩

private lemma set_svar (σ : Fin (Kc n L)) :
    {ω | svar n L ω = σ} = Set.univ ×ˢ
      {w : (Fin L → ℝ) × (Fin L → ℝ) | AWGN.blockQuant n L w.1 = σ} := by
  ext ⟨t, w⟩
  simp [svar]

private lemma measurableSet_C (σ u : Fin (Kc n L)) :
    MeasurableSet {t : Fin L → ℝ | AWGN.blockQuant n L (fun l => t l + α * sv n L σ l) = u} :=
  ((AWGN.measurable_blockQuant n L).comp (measurable_pi_iff.2 fun l =>
    (measurable_pi_apply l).add_const _)) (measurableSet_singleton u)

private lemma measurableSet_D (σ u y : Fin (Kc n L)) :
    MeasurableSet {w : (Fin L → ℝ) × (Fin L → ℝ) | AWGN.blockQuant n L w.1 = σ ∧
      AWGN.blockQuant n L (inp α P n L (finProdFinEquiv (u, σ)) + w.1 + w.2) = y} :=
  (((AWGN.measurable_blockQuant n L).comp measurable_fst) (measurableSet_singleton σ)).inter
    (((AWGN.measurable_blockQuant n L).comp ((measurable_const.add measurable_fst).add
      measurable_snd)) (measurableSet_singleton y))

private lemma integral_log_gvar_le {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) (Q N : ℝ)
    (hlog : Integrable (fun ω => Real.log (gvar α P n L θ s ω))
      ((AWGN.noise θ L).prod ((AWGN.noise Q L).prod (AWGN.noise N L)))) :
    ∫ ω, Real.log (gvar α P n L θ s ω)
        ∂(AWGN.noise θ L).prod ((AWGN.noise Q L).prod (AWGN.noise N L))
      ≤ GelfandPinsker.infoCapacity
          (chan Q N (AWGN.measurable_blockQuant n L) (inp α P n L)
            (AWGN.measurable_blockQuant n L))
          (stateLaw Q N (AWGN.measurable_blockQuant n L) (inp α P n L)
            (AWGN.measurable_blockQuant n L)) := by
  set ν := (AWGN.noise θ L).prod ((AWGN.noise Q L).prod (AWGN.noise N L))
  set ν₂ := (AWGN.noise Q L).prod (AWGN.noise N L)
  have hq := AWGN.measurable_blockQuant n L
  set Ψ : Fin (Kc n L) → Fin (Kc n L) → ℝ := fun u y => ∏ l,
    (gaussianReal (α * AWGN.value n ((eK n L).symm y l)) s.toNNReal
      (AWGN.level n ⁻¹' {(eK n L).symm u l})).toReal
  have hΨ0 : ∀ u y, 0 ≤ Ψ u y := fun u y =>
    Finset.prod_nonneg fun l _ => ENNReal.toReal_nonneg
  have hΨ : ∀ y, ∑ u, Ψ u y ≤ 1 := fun y => sum_cell_le n L _ _
  have hcell : ∀ σ u y,
      (∫⁻ ω in {ω | svar n L ω = σ ∧ uvar α n L ω = u ∧ yvar α P n L ω = y},
        ENNReal.ofReal (gvar α P n L θ s ω) ∂ν) * ν {ω | uvar α n L ω = u ∧ svar n L ω = σ} ≤
          ENNReal.ofReal (Ψ u y) *
            ν {ω | svar n L ω = σ ∧ uvar α n L ω = u ∧ yvar α P n L ω = y} *
              ν {ω | svar n L ω = σ} := by
    intro σ u y
    have hC := measurableSet_C α n L σ u
    have hD := measurableSet_D α P n L σ u y
    have hJ : ∫⁻ ω in {ω | svar n L ω = σ ∧ uvar α n L ω = u ∧ yvar α P n L ω = y},
        ENNReal.ofReal (gvar α P n L θ s ω) ∂ν =
          ENNReal.ofReal (Ψ u y) * ν₂ {w | AWGN.blockQuant n L w.1 = σ ∧
            AWGN.blockQuant n L (inp α P n L (finProdFinEquiv (u, σ)) + w.1 + w.2) = y} := by
      rw [setLIntegral_congr_fun ((set_cell α P n L σ u y).symm ▸ hC.prod hD)
        (g := fun ω => ENNReal.ofReal (∏ l, AWGN.postRatio θ s
          (α * AWGN.value n ((eK n L).symm y l) - α * sv n L σ l) (ω.1 l)))
        fun ω hω => by
          obtain ⟨h1, -, h3⟩ := hω
          simp only [gvar, h1, h3]]
      rw [set_cell, setLIntegral_prod (fun ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ) =>
        ENNReal.ofReal (∏ l, AWGN.postRatio θ s
          (α * AWGN.value n ((eK n L).symm y l) - α * sv n L σ l) (ω.1 l)))
        (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun l _ =>
          measurable_postRatio θ s measurable_const
            ((measurable_pi_apply l).comp measurable_fst))).aemeasurable]
      simp only [setLIntegral_const]
      rw [lintegral_mul_const' _ _ (measure_ne_top _ _),
        setLIntegral_cell hθ hs n L (fun l => α * sv n L σ l)
          (fun l => α * AWGN.value n ((eK n L).symm y l)) u]
    rw [hJ, set_cell, set_state, set_svar, Measure.prod_prod, Measure.prod_prod,
      Measure.prod_prod, measure_univ, one_mul]
    exact le_of_eq (by ring)
  refine (integral_log_le_mutualInfo_sub ν (measurable_svar n L) (measurable_uvar α n L)
    (measurable_yvar α P n L) (measurable_gvar α P n L θ s)
    (fun ω => Finset.prod_pos fun l _ => AWGN.postRatio_pos hθ hs _ _) hlog Ψ hΨ0 hΨ
    hcell).trans ?_
  refine GelfandPinsker.le_infoCapacity_of_kernel ν _ _ (measurable_svar n L)
    (measurable_uvar α n L) (measurable_xvar α n L) (measurable_yvar α P n L) (fun σ => ?_) ?_
  · rw [set_svar, measureReal_def, Measure.prod_prod, measure_univ, one_mul, stateLaw_eq]
  · rintro ⟨σ, u, x⟩ y
    by_cases hx : x = finProdFinEquiv (u, σ)
    · subst hx
      rw [set_cell', set_state', measureReal_def, measureReal_def, Measure.prod_prod,
        Measure.prod_prod, out_eq Q N hq (inp α P n L) hq, ← stateLaw_eq Q N hq (inp α P n L) hq]
      simp only [ENNReal.toReal_mul, mul_assoc]
    · have h0 : ∀ ω, (svar n L ω, uvar α n L ω, xvar α n L ω) ≠ (σ, u, x) := fun ω h => by
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3⟩ := h
        exact hx (by rw [← h1, ← h2, ← h3]; rfl)
      simp [h0]

end Capacity

section Gain

private lemma integral_comp_mp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν) {g : β → ℝ}
    (hg : AEStronglyMeasurable g ν) : ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := by
  rw [← hf.map_eq] at hg
  rw [← integral_map hf.measurable.aemeasurable hg, hf.map_eq]

private lemma abs_le_add_sq_div' {c : ℝ} (hc : 0 < c) (t : ℝ) : |t| ≤ c + t ^ 2 / c := by
  rw [← sq_abs t, show c + |t| ^ 2 / c = (c * c + |t| ^ 2) / c by field_simp, le_div_iff₀ hc]
  nlinarith [sq_nonneg (|t| - c), abs_nonneg t]

private lemma abs_log_postRatio_sub_le {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) {n : ℕ}
    {m m' : ℝ} (hm : |m| ≤ 2 * n) (hm' : |m'| ≤ 2 * n) (t : ℝ) :
    |Real.log (AWGN.postRatio θ s m t) - Real.log (AWGN.postRatio θ s m' t)|
      ≤ (8 * n * |t| + 16 * n ^ 2) / (2 * s) := by
  rw [AWGN.log_postRatio hθ hs, AWGN.log_postRatio hθ hs,
    show ∀ A B C D E : ℝ, (A + B - C / E) - (A + B - D / E) = (D - C) / E from
      fun _ _ _ _ _ => by ring,
    show (t - m') ^ 2 - (t - m) ^ 2 = (m - m') * (2 * t - m - m') by ring,
    abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * s),
    div_le_div_iff_of_pos_right (by positivity), abs_mul]
  have h1 : |m - m'| ≤ 4 * n := (abs_sub _ _).trans (by linarith)
  have h2 : |2 * t - m - m'| ≤ 2 * |t| + 4 * n := by
    refine (abs_sub _ _).trans ?_
    have := abs_sub (2 * t) m
    rw [abs_mul, abs_two] at this
    linarith
  calc |m - m'| * |2 * t - m - m'| ≤ (4 * n) * (2 * |t| + 4 * n) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 8 * n * |t| + 16 * n ^ 2 := by ring

private lemma measurable_clip (P : ℝ) (L : ℕ) : Measurable (clip P L) :=
  Measurable.ite (measurableSet_le (Finset.measurable_sum _ fun l _ =>
    (measurable_pi_apply l).pow_const 2) measurable_const) measurable_id measurable_const

private lemma clip_of_le {P : ℝ} {L : ℕ} {w : Fin L → ℝ} (h : ∑ l, w l ^ 2 ≤ L * P) :
    clip P L w = w := by
  simp [clip, h]

private def badSet (α P : ℝ) (n L : ℕ) : Set ((Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ)) :=
  {ω | L * P < ∑ l, xIn α n (ω.1 l) (ω.2.1 l) ^ 2}

private lemma measurable_xv (α : ℝ) (n L : ℕ) :
    Measurable fun ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ) =>
      fun l => xIn α n (ω.1 l) (ω.2.1 l) :=
  measurable_pi_iff.2 fun l => measurable_xIn α n ((measurable_pi_apply l).comp measurable_fst)
    ((measurable_pi_apply l).comp (measurable_fst.comp measurable_snd))

private lemma measurableSet_badSet (α P : ℝ) (n L : ℕ) : MeasurableSet (badSet α P n L) :=
  measurableSet_lt measurable_const (Finset.measurable_sum _ fun l _ =>
    ((measurable_pi_apply l).comp (measurable_xv α n L)).pow_const 2)

private lemma integral_log_gvar_ge {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (Q P : ℝ) (n L : ℕ)
    {c : ℝ} (hc : 0 < c) :
    Integrable (fun ω => Real.log (gvar (θ / (θ + N)) P n L θ (θ * N / (θ + N)) ω))
        ((AWGN.noise θ L).prod ((AWGN.noise Q L).prod (AWGN.noise N L))) ∧
      L * letterGain θ Q N n - L * ((8 * n * c + 16 * n ^ 2)
        * ((AWGN.noise θ L).prod ((AWGN.noise Q L).prod (AWGN.noise N L))).real
          (badSet (θ / (θ + N)) P n L) + 8 * n / c * θ) / (2 * (θ * N / (θ + N)))
      ≤ ∫ ω, Real.log (gvar (θ / (θ + N)) P n L θ (θ * N / (θ + N)) ω)
          ∂(AWGN.noise θ L).prod ((AWGN.noise Q L).prod (AWGN.noise N L)) := by
  set α := θ / (θ + N)
  set s := θ * N / (θ + N)
  have hs : 0 < s := by positivity
  have hα0 : 0 ≤ α := by positivity
  have hα1 : α ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  set μ := gaussianReal 0 θ.toNNReal
  set ν := (AWGN.noise θ L).prod ((AWGN.noise Q L).prod (AWGN.noise N L))
  set G : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ) → ℝ := fun ω => ∑ l, Real.log
    (AWGN.postRatio θ s (mOut α n (clip P L (fun l => xIn α n (ω.1 l) (ω.2.1 l)) l)
      (ω.2.1 l) (ω.2.2 l)) (ω.1 l))
  have hGeq : (fun ω => Real.log (gvar α P n L θ s ω)) = G :=
    funext fun ω => log_gvar α P n L hθ hs ω
  set Gu : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ) → ℝ := fun ω =>
    ∑ l, letterLog θ N n (ω.1 l, ω.2.1 l, ω.2.2 l)
  set bad := badSet α P n L
  set ind : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ) → ℝ := bad.indicator 1
  set E : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ) → ℝ := fun ω =>
    ∑ l, ((8 * n * c + 16 * n ^ 2) * ind ω + 8 * n / c * ω.1 l ^ 2) / (2 * s)
  have hmp3 : ∀ l : Fin L, MeasurePreserving
      (fun ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ) => (ω.1 l, ω.2.1 l, ω.2.2 l))
      ν (ρ θ Q N) := fun l =>
    (measurePreserving_eval (fun _ : Fin L => μ) l).prod
      ((measurePreserving_eval (fun _ : Fin L => gaussianReal 0 Q.toNNReal) l).prod
        (measurePreserving_eval (fun _ : Fin L => gaussianReal 0 N.toNNReal) l))
  have hmp1 : ∀ l : Fin L, MeasurePreserving
      (fun ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ) => ω.1 l) ν μ := fun l =>
    (measurePreserving_eval (fun _ : Fin L => μ) l).comp measurePreserving_fst
  have hg : Integrable (letterLog θ N n) (ρ θ Q N) := integrable_letterLog Q hθ hN n
  have hGu : Integrable Gu ν :=
    integrable_finsetSum _ fun l _ => (hmp3 l).integrable_comp_of_integrable hg
  have hGu_eq : ∫ ω, Gu ω ∂ν = L * letterGain θ Q N n := by
    simp only [Gu]
    rw [integral_finsetSum (f := fun l (ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ)) =>
      letterLog θ N n (ω.1 l, ω.2.1 l, ω.2.2 l)) _
      fun l _ => (hmp3 l).integrable_comp_of_integrable hg]
    rw [Finset.sum_congr rfl fun l _ => integral_comp_mp (hmp3 l) hg.aestronglyMeasurable]
    simp [letterGain]
  have hbad := measurableSet_badSet α P n L
  have hind : Integrable ind ν := (integrable_const 1).indicator hbad
  have hsq : ∀ l : Fin L, Integrable
      (fun ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ) => ω.1 l ^ 2) ν := fun l =>
    (hmp1 l).integrable_comp_of_integrable (AWGN.integrable_sq_gaussianReal _)
  have hEl : ∀ l : Fin L, Integrable (fun ω : (Fin L → ℝ) × (Fin L → ℝ) × (Fin L → ℝ) =>
      ((8 * n * c + 16 * n ^ 2) * ind ω + 8 * n / c * ω.1 l ^ 2) / (2 * s)) ν := fun l =>
    ((hind.const_mul _).add ((hsq l).const_mul _)).div_const _
  have hE : Integrable E ν := integrable_finsetSum _ fun l _ => hEl l
  have hE_eq : ∫ ω, E ω ∂ν
      = L * ((8 * n * c + 16 * n ^ 2) * ν.real bad + 8 * n / c * θ) / (2 * s) := by
    have h1 : ∀ l : Fin L, ∫ ω, ((8 * n * c + 16 * n ^ 2) * ind ω + 8 * n / c * ω.1 l ^ 2)
        / (2 * s) ∂ν = ((8 * n * c + 16 * n ^ 2) * ν.real bad + 8 * n / c * θ) / (2 * s) := by
      intro l
      rw [integral_div, integral_add (hind.const_mul _) ((hsq l).const_mul _),
        integral_const_mul, integral_const_mul, integral_indicator_one hbad,
        integral_comp_mp (hmp1 l) (by fun_prop : AEStronglyMeasurable (fun t : ℝ => t ^ 2) μ),
        AWGN.integral_sq_gaussianReal]
      simp [Real.coe_toNNReal _ hθ.le]
      rfl
    simp only [E]
    rw [integral_finsetSum _ fun l _ => hEl l]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hGm : Measurable G := Finset.measurable_sum _ fun l _ => Real.measurable_log.comp
    (measurable_postRatio θ s (measurable_mOut α n ((measurable_pi_apply l).comp
      ((measurable_clip P L).comp (measurable_xv α n L)))
      ((measurable_pi_apply l).comp (measurable_fst.comp measurable_snd))
      ((measurable_pi_apply l).comp (measurable_snd.comp measurable_snd)))
      ((measurable_pi_apply l).comp measurable_fst))
  have hpt : ∀ ω, |G ω - Gu ω| ≤ E ω := by
    intro ω
    by_cases hw : ω ∈ bad
    · have hi : ind ω = 1 := by simp [ind, hw]
      simp only [G, Gu, E, hi, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      refine (abs_log_postRatio_sub_le hθ hs (abs_mOut_le_n hα0 hα1 n _ _ _)
        (abs_mOut_le_n hα0 hα1 n _ _ _) _).trans ?_
      rw [div_le_div_iff_of_pos_right (by positivity)]
      have h4 : (8 * n : ℝ) * |ω.1 l| ≤ 8 * n * (c + ω.1 l ^ 2 / c) :=
        mul_le_mul_of_nonneg_left (abs_le_add_sq_div' hc _) (by positivity)
      have h5 : 8 * n / c * ω.1 l ^ 2 = 8 * n * (ω.1 l ^ 2 / c) := by ring
      nlinarith
    · have hcl : clip P L (fun l => xIn α n (ω.1 l) (ω.2.1 l))
          = fun l => xIn α n (ω.1 l) (ω.2.1 l) := clip_of_le (not_lt.1 hw)
      have hGG : G ω = Gu ω := by simp only [G, Gu, hcl]; rfl
      rw [hGG, sub_self, abs_zero]
      have : 0 ≤ ind ω := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      exact Finset.sum_nonneg fun l _ => by positivity
  have hdiff : Integrable (fun ω => G ω - Gu ω) ν :=
    hE.mono' (hGm.aestronglyMeasurable.sub hGu.aestronglyMeasurable)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hpt ω)
  have hG : Integrable G ν := (hGu.add hdiff).congr (ae_of_all _ fun ω => by simp)
  rw [hGeq]
  refine ⟨hG, ?_⟩
  rw [← hGu_eq, ← hE_eq, ← integral_sub hGu hE]
  exact integral_mono (hGu.sub hE) hG fun ω => by
    have := hpt ω
    linarith [neg_abs_le (G ω - Gu ω)]

end Gain

section Final

private lemma measureReal_sum_gt_le {β : Type*} [MeasurableSpace β] (ρ : Measure β)
    [IsProbabilityMeasure ρ] {Y : β → ℝ} (hYm : Measurable Y) (hY : MemLp Y 2 ρ) {L : ℕ}
    (hL : 0 < L) {P : ℝ} (hm : ∫ a, Y a ∂ρ < P) :
    (Measure.pi fun _ : Fin L => ρ).real {f | L * P < ∑ l, Y (f l)}
      ≤ Var[Y; ρ] / (L * (P - ∫ a, Y a ∂ρ) ^ 2) := by
  set μL := Measure.pi fun _ : Fin L => ρ
  set m := ∫ a, Y a ∂ρ
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  have hPm : 0 < P - m := sub_pos.2 hm
  have hmp : ∀ l : Fin L, MeasurePreserving (fun f : Fin L → β => f l) μL ρ :=
    fun l => measurePreserving_eval _ l
  set S : (Fin L → β) → ℝ := ∑ l : Fin L, fun f => Y (f l)
  have hSapp : ∀ f, S f = ∑ l, Y (f l) := fun f => by simp [S, Finset.sum_apply]
  have hS : MemLp S 2 μL := memLp_finsetSum' _ fun l _ => hY.comp_measurePreserving (hmp l)
  have hVar : Var[S; μL] = L * Var[Y; ρ] := by
    rw [variance_sum_pi (fun _ => hY)]
    simp
  have hmean : μL[S] = L * m := by
    simp_rw [hSapp]
    rw [integral_finsetSum (f := fun l (f : Fin L → β) => Y (f l)) _ fun l _ =>
      (hmp l).integrable_comp_of_integrable (hY.integrable one_le_two)]
    simp_rw [integral_comp_mp (hmp _) hYm.aestronglyMeasurable]
    simp [m]
  have hsub : {f : Fin L → β | L * P < ∑ l, Y (f l)} ⊆ {f | L * (P - m) ≤ |S f - μL[S]|} :=
    fun f hf => by
      have hf' : L * P < ∑ l, Y (f l) := hf
      change L * (P - m) ≤ |S f - μL[S]|
      rw [hmean, hSapp, abs_of_pos (by nlinarith)]
      nlinarith
  have hcheb := meas_ge_le_variance_div_sq hS (mul_pos hL' hPm)
  have hV : 0 ≤ Var[S; μL] / (L * (P - m)) ^ 2 :=
    div_nonneg (variance_nonneg _ _) (by positivity)
  calc μL.real {f | L * P < ∑ l, Y (f l)} ≤ μL.real {f | L * (P - m) ≤ |S f - μL[S]|} :=
        measureReal_mono hsub
    _ ≤ Var[S; μL] / (L * (P - m)) ^ 2 := ENNReal.toReal_le_of_le_ofReal hV hcheb
    _ = Var[Y; ρ] / (L * (P - m) ^ 2) := by
      rw [hVar]
      field_simp

private lemma measurable_xSq (α : ℝ) (n : ℕ) : Measurable fun x : ℝ × ℝ => xIn α n x.1 x.2 ^ 2 :=
  (measurable_xIn α n measurable_fst measurable_snd).pow_const 2

private lemma abs_xIn_le_n {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (n : ℕ) (t s : ℝ) :
    |xIn α n t s| ≤ 2 * n := by
  have e1 := (abs_mul_le_of_le_one h0 h1 (sHat n s)).trans (AWGN.abs_value_le n _)
  have e2 := AWGN.abs_value_le n (AWGN.level n (t + α * sHat n s))
  have e3 := abs_sub (AWGN.value n (AWGN.level n (t + α * sHat n s))) (α * sHat n s)
  simp only [xIn] at *
  linarith

private lemma measureReal_badSet_le {θ Q N α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (n : ℕ) {L : ℕ}
    (hL : 0 < L) {P : ℝ} (hm : ∫ x, xIn α n x.1 x.2 ^ 2
      ∂(gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 Q.toNNReal) < P) :
    ((AWGN.noise θ L).prod ((AWGN.noise Q L).prod (AWGN.noise N L))).real (badSet α P n L)
      ≤ Var[fun x : ℝ × ℝ => xIn α n x.1 x.2 ^ 2;
          (gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 Q.toNNReal)]
        / (L * (P - ∫ x, xIn α n x.1 x.2 ^ 2
          ∂(gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 Q.toNNReal)) ^ 2) := by
  have hY : MemLp (fun x : ℝ × ℝ => xIn α n x.1 x.2 ^ 2) 2
      ((gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 Q.toNNReal)) :=
    MemLp.of_bound (measurable_xSq α n).aestronglyMeasurable ((2 * n : ℝ) ^ 2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_xIn_le_n h0 h1 n _ _) 2)
  have hmp1 : MeasurePreserving (Prod.map id Prod.fst)
      ((AWGN.noise θ L).prod ((AWGN.noise Q L).prod (AWGN.noise N L)))
      ((AWGN.noise θ L).prod (AWGN.noise Q L)) :=
    (MeasurePreserving.id _).prod measurePreserving_fst
  have hmp2 : MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin L)).symm
      ((AWGN.noise θ L).prod (AWGN.noise Q L))
      (Measure.pi fun _ : Fin L => (gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 Q.toNNReal)) :=
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin L)
      (fun _ => gaussianReal 0 θ.toNNReal) (fun _ => gaussianReal 0 Q.toNNReal)).symm
  have hS : MeasurableSet {f : Fin L → ℝ × ℝ | L * P < ∑ l, xIn α n (f l).1 (f l).2 ^ 2} :=
    measurableSet_lt measurable_const (Finset.measurable_sum _ fun l _ =>
      (measurable_xSq α n).comp (measurable_pi_apply l))
  have he : badSet α P n L = ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin L)).symm ∘
      Prod.map id Prod.fst) ⁻¹' {f : Fin L → ℝ × ℝ | L * P < ∑ l, xIn α n (f l).1 (f l).2 ^ 2} :=
    rfl
  rw [he, (hmp2.comp hmp1).measureReal_preimage hS.nullMeasurableSet]
  exact measureReal_sum_gt_le _ (measurable_xSq α n) hY hL hm

private lemma tendsto_integral_xSq {θ : ℝ} (hθ : 0 < θ) (Q : ℝ) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1) :
    Tendsto (fun n => ∫ x, xIn α n x.1 x.2 ^ 2
      ∂(gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 Q.toNNReal)) atTop (𝓝 θ) := by
  set μ₁ := gaussianReal 0 θ.toNNReal
  set μ₂ := gaussianReal 0 Q.toNNReal
  have i1 : Integrable (fun x : ℝ × ℝ => x.1 ^ 2) (μ₁.prod μ₂) :=
    (AWGN.integrable_sq_gaussianReal _).comp_fst μ₂
  have i2 : Integrable (fun x : ℝ × ℝ => x.2 ^ 2) (μ₁.prod μ₂) :=
    (AWGN.integrable_sq_gaussianReal _).comp_snd μ₁
  have hlim : ∫ x, x.1 ^ 2 ∂(μ₁.prod μ₂) = θ := by
    rw [integral_fun_fst (fun t => t ^ 2), AWGN.integral_sq_gaussianReal,
      Real.coe_toNNReal _ hθ.le]
    simp
  rw [← hlim]
  refine tendsto_integral_of_dominated_convergence
    (fun x : ℝ × ℝ => 3 * x.1 ^ 2 + 12 * x.2 ^ 2 + 27)
    (fun n => (measurable_xSq α n).aestronglyMeasurable)
    (((i1.const_mul 3).add (i2.const_mul 12)).add (integrable_const _))
    (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg _) (abs_xIn_le h0 h1 n x.1 x.2) 2
    rw [sq_abs] at h
    nlinarith [sq_abs x.1, sq_abs x.2, abs_nonneg x.1, abs_nonneg x.2,
      sq_nonneg (|x.1| - 2 * |x.2|), sq_nonneg (|x.1| - 3), sq_nonneg (2 * |x.2| - 3)]
  · have hs : Tendsto (fun n => sHat n x.2) atTop (𝓝 x.2) :=
      AWGN.tendsto_value_level tendsto_const_nhds
    have hx := (AWGN.tendsto_value_level ((tendsto_const_nhds (x := x.1)).add
      (hs.const_mul α))).sub (hs.const_mul α)
    simp only [add_sub_cancel_right] at hx
    exact hx.pow 2

private lemma exists_blockQuantization {P Q N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) (R : ℝ)
    (hR : 0 ≤ R) (hRC : R < awgnCapacity P N) :
    ∃ (L s₁ s₂ s₃ : ℕ) (qs : (Fin L → ℝ) → Fin s₁) (hqs : Measurable qs)
      (a : Fin s₂ → Fin L → ℝ) (q : (Fin L → ℝ) → Fin s₃) (hq : Measurable q),
      0 < L ∧ 0 < s₂ ∧ (∀ x, ∑ l, a x l ^ 2 ≤ L * P) ∧
        L * R < GelfandPinsker.infoCapacity (chan Q N hqs a hq) (stateLaw Q N hqs a hq) := by
  have hPpos : 0 < P := by
    refine hP.lt_of_ne fun h => ?_
    subst h
    simp [awgnCapacity] at hRC
    linarith
  have hcont : ContinuousAt (fun θ => awgnCapacity θ N) P := by
    unfold awgnCapacity
    exact continuousAt_const.mul ((continuousAt_const.add (continuousAt_id.div_const N)).log
      (ne_of_gt (by have := div_nonneg hP hN.le; simp only [Pi.add_apply, id]; linarith)))
  obtain ⟨θ, hθC, hθ0, hθP⟩ : ∃ θ, R < awgnCapacity θ N ∧ 0 < θ ∧ θ < P := by
    have h1 : ∀ᶠ θ in 𝓝[<] P, R < awgnCapacity θ N :=
      nhdsWithin_le_nhds (hcont.eventually (lt_mem_nhds hRC))
    have h2 : ∀ᶠ θ in 𝓝[<] P, θ ∈ Set.Ioo 0 P := Ioo_mem_nhdsLT hPpos
    exact (h1.and h2).exists.imp fun θ h => ⟨h.1, h.2.1, h.2.2⟩
  set α := θ / (θ + N)
  set s := θ * N / (θ + N)
  have hs : 0 < s := by positivity
  have hα0 : 0 ≤ α := by positivity
  have hα1 : α ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  set η := (awgnCapacity θ N - R) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨n, hn1, hn2⟩ := (((tendsto_letterGain Q hθ0 hN).eventually
    (lt_mem_nhds (show R + 3 * η < awgnCapacity θ N by linarith))).and
    ((tendsto_integral_xSq hθ0 Q hα0 hα1).eventually (gt_mem_nhds hθP))).exists
  set m := ∫ x, xIn α n x.1 x.2 ^ 2 ∂(gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 Q.toNNReal)
  set V := Var[fun x : ℝ × ℝ => xIn α n x.1 x.2 ^ 2;
    (gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 Q.toNNReal)]
  have hPm : 0 < P - m := sub_pos.2 hn2
  set c := 8 * n * θ / (2 * s * η) + 1
  have hc : 0 < c := by positivity
  have h5 : 8 * n / c * θ / (2 * s) < η := by
    have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * s * η)).1
      (lt_add_one (8 * n * θ / (2 * s * η)))
    rw [show 8 * n / c * θ / (2 * s) = 8 * n * θ / (c * (2 * s)) by field_simp,
      div_lt_iff₀ (by positivity)]
    nlinarith
  set A := 8 * n * c + 16 * (n : ℝ) ^ 2
  have hA : 0 ≤ A := by positivity
  set K := A * V / (P - m) ^ 2 / (2 * s)
  set L := ⌈K / η⌉₊ + 1
  have hL : 0 < L := Nat.succ_pos _
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  have h4 : K < L * η := by
    have := Nat.le_ceil (K / η)
    have h' : K / η < L := by
      simp only [L, Nat.cast_add, Nat.cast_one]
      linarith
    rwa [div_lt_iff₀ hη0] at h'
  set ν := (AWGN.noise θ L).prod ((AWGN.noise Q L).prod (AWGN.noise N L))
  have hβ : ν.real (badSet α P n L) ≤ V / (L * (P - m) ^ 2) :=
    measureReal_badSet_le hα0 hα1 n hL hn2
  have hV : 0 ≤ V := variance_nonneg _ _
  have h2 : L * (A * ν.real (badSet α P n L)) / (2 * s) ≤ K := by
    calc L * (A * ν.real (badSet α P n L)) / (2 * s)
        ≤ L * (A * (V / (L * (P - m) ^ 2))) / (2 * s) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hβ hA) hL'.le) (by positivity)
      _ = K := by
          simp only [K]
          field_simp
  obtain ⟨hlog, hge⟩ := integral_log_gvar_ge hθ0 hN Q P n L hc
  have hle := integral_log_gvar_le α P n L hθ0 hs Q N hlog
  have : Nonempty (AWGN.Level n) :=
    ⟨⟨0, Finset.mem_Icc.2 ⟨neg_nonpos.2 (sq_nonneg _), sq_nonneg _⟩⟩⟩
  have hpos : 0 < Kc n L * Kc n L := Nat.mul_pos Fintype.card_pos Fintype.card_pos
  refine ⟨L, _, _, _, AWGN.blockQuant n L, AWGN.measurable_blockQuant n L, inp α P n L,
    AWGN.blockQuant n L, AWGN.measurable_blockQuant n L, hL, hpos,
    fun x => sum_sq_clip_le L hP _, ?_⟩
  have e1 : L * (A * ν.real (badSet α P n L) + 8 * n / c * θ) / (2 * s)
      = L * (A * ν.real (badSet α P n L)) / (2 * s) + L * (8 * n / c * θ / (2 * s)) := by ring
  have e3 := mul_lt_mul_of_pos_left h5 hL'
  have e4 := mul_lt_mul_of_pos_left hn1 hL'
  have e5 := mul_pos hL' hη0
  have hge' : L * letterGain θ Q N n - L * (A * ν.real (badSet α P n L) + 8 * n / c * θ) / (2 * s)
      ≤ GelfandPinsker.infoCapacity
          (chan Q N (AWGN.measurable_blockQuant n L) (inp α P n L)
            (AWGN.measurable_blockQuant n L))
          (stateLaw Q N (AWGN.measurable_blockQuant n L) (inp α P n L)
            (AWGN.measurable_blockQuant n L)) := hge.trans hle
  linarith

end Final

theorem closure_achievable_eq {P Q N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable P Q N R} = Set.Icc 0 (awgnCapacity P N) :=
  closure_achievable_eq_of_quantization hP hN fun R hR hRC =>
    exists_blockQuantization hP hN R hR hRC

end DirtyPaper

end Meat
