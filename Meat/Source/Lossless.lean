import Meat.Shannon.Typical

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

structure SourceCode (M S : Type*) (n : ℕ) where
  enc : (Fin n → S) → M
  dec : M → (Fin n → S)

namespace SourceCode

variable {M S : Type*} {n : ℕ}

noncomputable def errorProb [Fintype S] [DecidableEq S] (c : SourceCode M S n) (p : PMF S) :
    ℝ≥0∞ :=
  ∑ x : Fin n → S, if c.dec (c.enc x) = x then 0 else ∏ i, p (x i)

noncomputable def correctSet [Fintype S] [DecidableEq S] (c : SourceCode M S n) :
    Finset (Fin n → S) :=
  {x | c.dec (c.enc x) = x}

theorem card_correctSet_le [Fintype S] [DecidableEq S] [Fintype M] (c : SourceCode M S n) :
    c.correctSet.card ≤ Fintype.card M := by
  refine card_le_card_of_injOn c.enc (fun _ _ => mem_coe.2 (mem_univ _)) fun x hx y hy h => ?_
  simp only [correctSet, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
  rw [← hx, ← hy, h]

theorem errorProb_ne_top [Fintype S] [DecidableEq S] (c : SourceCode M S n) (p : PMF S) :
    c.errorProb p ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun x _ => by
    split_ifs
    · exact ENNReal.zero_ne_top
    · exact ENNReal.prod_ne_top fun i _ => p.apply_ne_top _

theorem errorProb_toReal [Fintype S] [DecidableEq S] (c : SourceCode M S n) (p : PMF S) :
    (c.errorProb p).toReal = 1 - ∑ x ∈ c.correctSet, iidProb p x := by
  rw [errorProb, ENNReal.toReal_sum fun x _ => by
    split_ifs
    · exact ENNReal.zero_ne_top
    · exact ENNReal.prod_ne_top fun i _ => p.apply_ne_top _, ← sum_iidProb p n,
    ← sum_ite_mem_zero]
  refine sum_congr rfl fun x _ => ?_
  by_cases h : c.dec (c.enc x) = x
  · simp [correctSet, h]
  · simp [correctSet, h, iidProb, ENNReal.toReal_prod]

theorem errorProb_le_one [Fintype S] [DecidableEq S] (c : SourceCode M S n) (p : PMF S) :
    c.errorProb p ≤ 1 := by
  rw [← ENNReal.ofReal_toReal (c.errorProb_ne_top p), ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [errorProb_toReal]
  linarith [sum_nonneg fun x (_ : x ∈ c.correctSet) => iidProb_nonneg p x]

noncomputable def ofFinset (A : Finset (Fin n → S)) {k : ℕ} (hA : A.card ≤ k) (hk : 0 < k)
    (d : Fin n → S) : SourceCode (Fin k) S n := by
  classical
  exact ⟨fun x => if hx : x ∈ A then Fin.castLE hA (A.equivFin ⟨x, hx⟩) else ⟨0, hk⟩,
    fun m => if hm : (m : ℕ) < A.card then (A.equivFin.symm ⟨m, hm⟩ : Fin n → S) else d⟩

theorem ofFinset_dec_enc (A : Finset (Fin n → S)) {k : ℕ} (hA : A.card ≤ k) (hk : 0 < k)
    (d : Fin n → S) {x : Fin n → S} (hx : x ∈ A) :
    (ofFinset A hA hk d).dec ((ofFinset A hA hk d).enc x) = x := by
  classical
  have hlt : ((A.equivFin ⟨x, hx⟩ : Fin A.card) : ℕ) < A.card := Fin.is_lt _
  simp only [ofFinset, hx, dite_true, Fin.val_castLE, hlt]
  simp

theorem subset_correctSet_ofFinset [Fintype S] [DecidableEq S] (A : Finset (Fin n → S)) {k : ℕ}
    (hA : A.card ≤ k) (hk : 0 < k) (d : Fin n → S) :
    A ⊆ (ofFinset A hA hk d).correctSet := fun x hx => by
  simp only [correctSet, mem_filter, mem_univ, true_and]
  exact ofFinset_dec_enc A hA hk d hx

theorem errorProb_ofFinset_le [Fintype S] [DecidableEq S] (A : Finset (Fin n → S)) {k : ℕ}
    (hA : A.card ≤ k) (hk : 0 < k) (d : Fin n → S) (p : PMF S) :
    (ofFinset A hA hk d).errorProb p ≤ ENNReal.ofReal (1 - ∑ x ∈ A, iidProb p x) := by
  rw [← ENNReal.ofReal_toReal (errorProb_ne_top _ p), errorProb_toReal]
  exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (sum_le_sum_of_subset_of_nonneg
    (subset_correctSet_ofFinset A hA hk d) fun x _ _ => iidProb_nonneg p x) 1)

end SourceCode

namespace Lossless

open SourceCode

variable {S : Type*} [Fintype S] [DecidableEq S]

def Achievable (p : PMF S) (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (n * R) ∧ ∃ c : SourceCode (Fin k) S n, c.errorProb p ≤ ε

def achievableRates (p : PMF S) : Set ℝ :=
  {R | Achievable p R}

variable [MeasurableSpace S]

omit [DecidableEq S] in
theorem sum_iidProb_le_card_mul_add (p : PMF S) {n : ℕ} (ε : ℝ) (A : Finset (Fin n → S)) :
    ∑ x ∈ A, iidProb p x ≤ A.card * Real.exp (-(n * (measureEntropy p.toMeasure - ε)))
      + (1 - ∑ x ∈ typicalSet p n ε, iidProb p x) := by
  classical
  set T := typicalSet p n ε
  have h1 : ∑ x ∈ A with x ∈ T, iidProb p x
      ≤ A.card * Real.exp (-(n * (measureEntropy p.toMeasure - ε))) := by
    refine (sum_le_sum (g := fun _ => Real.exp (-(n * (measureEntropy p.toMeasure - ε))))
      fun x hx => ?_).trans ((sum_const _).trans_le ?_)
    · have hxT := (mem_filter.1 hx).2
      simp only [T, typicalSet, mem_filter, mem_univ, true_and] at hxT
      exact hxT.2
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le A _)
        (Real.exp_pos _).le
  have h2 : ∑ x ∈ A with x ∉ T, iidProb p x ≤ 1 - ∑ x ∈ T, iidProb p x := by
    rw [← sum_iidProb p n, ← sum_ite_mem_zero]
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (subset_univ A)) fun x _ _ =>
      iidProb_nonneg p x).trans_eq ?_
    rw [sum_filter]
    exact sum_congr rfl fun x _ => by by_cases hx : x ∈ T <;> simp [hx]
  rw [← sum_filter_add_sum_filter_not A (· ∈ T)]
  exact add_le_add h1 h2

omit [DecidableEq S] in
theorem eventually_sum_iidProb_le [MeasurableSingletonClass S] (p : PMF S) {R δ : ℝ}
    (hR : R < measureEntropy p.toMeasure) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset (Fin n → S), (A.card : ℝ) ≤ Real.exp (n * R) →
      ∑ x ∈ A, iidProb p x ≤ δ := by
  set H := measureEntropy p.toMeasure
  set ε := (H - R) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have h1 : Tendsto (fun n : ℕ => Real.exp (n * (R - H + ε))
      + (1 - ∑ x ∈ typicalSet p n ε, iidProb p x)) atTop (𝓝 0) := by
    have h := (tendsto_exp_nat_mul (show R - H + ε < 0 by rw [hε]; linarith)).add
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_sum_iidProb_typicalSet p hε0))
    simpa using h
  filter_upwards [h1.eventually (ge_mem_nhds hδ)] with n hn A hA
  refine (sum_iidProb_le_card_mul_add p ε A).trans (le_trans ?_ hn)
  refine add_le_add_left ((mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le).trans_eq ?_) _
  rw [← Real.exp_add]
  congr 1
  ring

theorem eventually_one_sub_le_errorProb [MeasurableSingletonClass S] (p : PMF S) {R δ : ℝ}
    (hR : R < measureEntropy p.toMeasure) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ Real.exp (n * R) →
      ∀ c : SourceCode (Fin k) S n, 1 - δ ≤ (c.errorProb p).toReal := by
  filter_upwards [eventually_sum_iidProb_le p hR hδ] with n hn k hk c
  rw [errorProb_toReal]
  have hc : (c.correctSet.card : ℝ) ≤ k := by
    exact_mod_cast (card_correctSet_le c).trans_eq (Fintype.card_fin k)
  linarith [hn c.correctSet (hc.trans hk)]

theorem tendsto_errorProb_one [MeasurableSingletonClass S] (p : PMF S) {R : ℝ}
    (hR : R < measureEntropy p.toMeasure) (k : ℕ → ℕ) (hk : ∀ n, (k n : ℝ) ≤ Real.exp (n * R))
    (c : ∀ n, SourceCode (Fin (k n)) S n) :
    Tendsto (fun n => (c n).errorProb p) atTop (𝓝 1) := by
  have hr : Tendsto (fun n => ((c n).errorProb p).toReal) atTop (𝓝 1) := by
    refine Metric.tendsto_atTop.2 fun δ hδ => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_one_sub_le_errorProb p hR (half_pos hδ))
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn (k n) (hk n) (c n)
    have h2 : ((c n).errorProb p).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (c n).errorProb_le_one p)
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  have h := ENNReal.tendsto_ofReal hr
  rw [ENNReal.ofReal_one] at h
  exact h.congr fun n => ENNReal.ofReal_toReal ((c n).errorProb_ne_top p)

theorem le_of_achievable [MeasurableSingletonClass S] (p : PMF S) {R : ℝ}
    (h : Achievable p R) : measureEntropy p.toMeasure ≤ R := by
  by_contra hlt
  push Not at hlt
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (eventually_one_sub_le_errorProb p hlt (show (0 : ℝ) < 1 / 2 by norm_num))
  obtain ⟨N₂, hN₂⟩ := h (ENNReal.ofReal (1 / 4)) (by norm_num)
  obtain ⟨k, hk, c, hc⟩ := hN₂ (max N₁ N₂) (le_max_right _ _)
  have h1 := hN₁ (max N₁ N₂) (le_max_left _ _) k hk c
  have h2 := ENNReal.toReal_le_of_le_ofReal (by norm_num) hc
  linarith

theorem achievable_of_lt [MeasurableSingletonClass S] (p : PMF S) {R : ℝ}
    (hR : measureEntropy p.toMeasure < R) : Achievable p R := by
  intro ε hε
  set H := measureEntropy p.toMeasure
  set γ := (R - H) / 2 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hH : 0 ≤ H := by
    rw [show H = _ from measureEntropy_toMeasure p]
    exact sum_nonneg fun s _ => Real.negMulLog_nonneg ENNReal.toReal_nonneg
      (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using p.coe_le_one s))
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨s, -⟩ := p.support_nonempty
  have ht := ENNReal.tendsto_ofReal
    (tendsto_const_nhds.sub (tendsto_sum_iidProb_typicalSet p hγ0) :
      Tendsto (fun n => 1 - ∑ x ∈ typicalSet p n γ, iidProb p x) atTop (𝓝 (1 - 1)))
  rw [sub_self, ENNReal.ofReal_zero] at ht
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hε))
  refine ⟨N, fun n hn => ⟨⌊Real.exp (n * R)⌋₊, Nat.floor_le (Real.exp_pos _).le, ?_⟩⟩
  have hT : (typicalSet p n γ).card ≤ ⌊Real.exp (n * R)⌋₊ := by
    refine Nat.le_floor ((card_typicalSet_le p n γ).trans (Real.exp_le_exp.2 ?_))
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    rw [hγ]
    linarith
  have hk : 0 < ⌊Real.exp (n * R)⌋₊ :=
    Nat.floor_pos.2 (Real.one_le_exp (mul_nonneg (Nat.cast_nonneg n) hR0))
  exact ⟨ofFinset _ hT hk fun _ => s, (errorProb_ofFinset_le _ hT hk _ p).trans (hN n hn).le⟩

theorem closure_achievableRates_eq [MeasurableSingletonClass S] (p : PMF S) :
    closure (achievableRates p) = Set.Ici (measureEntropy p.toMeasure) := by
  refine subset_antisymm (closure_minimal (fun R hR => le_of_achievable p hR) isClosed_Ici) ?_
  rw [← closure_Ioi]
  exact closure_mono fun R hR => achievable_of_lt p hR

end Lossless

end Meat
