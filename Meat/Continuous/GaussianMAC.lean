import Meat.Continuous.AWGNConverse
import Meat.Continuous.GaussianMultiUser

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Meat

namespace GaussianMAC

structure Code (P₁ P₂ : ℝ) (n k₁ k₂ : ℕ) where
  enc₁ : Fin k₁ → Fin n → ℝ
  enc₂ : Fin k₂ → Fin n → ℝ
  power₁ : ∀ m, ∑ i, enc₁ m i ^ 2 ≤ n * P₁
  power₂ : ∀ m, ∑ i, enc₂ m i ^ 2 ≤ n * P₂
  dec : (Fin n → ℝ) → Fin k₁ × Fin k₂
  measurable_dec : Measurable dec

namespace Code

variable {P₁ P₂ : ℝ} {n k₁ k₂ : ℕ}

noncomputable def errorProb (c : Code P₁ P₂ n k₁ k₂) (N : ℝ) (m : Fin k₁ × Fin k₂) : ℝ≥0∞ :=
  AWGN.noise N n {z | c.dec (c.enc₁ m.1 + c.enc₂ m.2 + z) ≠ m}

noncomputable def avgError (c : Code P₁ P₂ n k₁ k₂) (N : ℝ) : ℝ≥0∞ :=
  (∑ m, c.errorProb N m) / (k₁ * k₂)

def swap (c : Code P₁ P₂ n k₁ k₂) : Code P₂ P₁ n k₂ k₁ where
  enc₁ := c.enc₂
  enc₂ := c.enc₁
  power₁ := c.power₂
  power₂ := c.power₁
  dec y := (c.dec y).swap
  measurable_dec := measurable_swap.comp c.measurable_dec

theorem errorProb_swap (c : Code P₁ P₂ n k₁ k₂) (N : ℝ) (m : Fin k₂ × Fin k₁) :
    c.swap.errorProb N m = c.errorProb N m.swap := by
  simp only [errorProb, swap, add_comm (c.enc₂ m.1) (c.enc₁ m.2)]
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, ne_eq]
  rw [← Prod.swap_inj]
  simp

theorem avgError_swap (c : Code P₁ P₂ n k₁ k₂) (N : ℝ) : c.swap.avgError N = c.avgError N := by
  simp only [avgError, errorProb_swap, mul_comm (k₂ : ℝ≥0∞)]
  rw [← (Equiv.prodComm (Fin k₂) (Fin k₁)).symm.sum_comp]
  rfl

private lemma exists_sum_errorProb_le (c : Code P₁ P₂ n k₁ k₂) (N : ℝ) (hk₂ : 0 < k₂) :
    ∃ m₂, (∑ m₁, c.errorProb N (m₁, m₂)) / k₁ ≤ c.avgError N := by
  obtain ⟨m₂, -, hm⟩ := Finset.exists_min_image Finset.univ
    (fun m₂ => ∑ m₁, c.errorProb N (m₁, m₂)) ⟨⟨0, hk₂⟩, Finset.mem_univ _⟩
  refine ⟨m₂, ?_⟩
  have hk : (k₂ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk₂.ne'
  have hle : (k₂ : ℝ≥0∞) * ∑ m₁, c.errorProb N (m₁, m₂) ≤ ∑ m, c.errorProb N m := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have := Finset.card_nsmul_le_sum Finset.univ (fun m₂ => ∑ m₁, c.errorProb N (m₁, m₂))
      (∑ m₁, c.errorProb N (m₁, m₂)) fun x _ => hm x (Finset.mem_univ _)
    simpa [nsmul_eq_mul] using this
  rw [avgError, ← ENNReal.mul_div_mul_left _ _ hk (ENNReal.natCast_ne_top k₂),
    mul_comm (k₂ : ℝ≥0∞) k₁]
  exact ENNReal.div_le_div_right hle _

theorem exists_awgnCode (c : Code P₁ P₂ n k₁ k₂) (N : ℝ) (hk₂ : 0 < k₂) :
    ∃ c' : AWGN.Code P₁ n k₁, c'.avgError N ≤ c.avgError N := by
  obtain ⟨m₂, hm⟩ := c.exists_sum_errorProb_le N hk₂
  refine ⟨⟨c.enc₁, c.power₁, fun y => (c.dec (y + c.enc₂ m₂)).1,
    (measurable_fst.comp c.measurable_dec).comp (measurable_add_const _)⟩, le_trans ?_ hm⟩
  refine ENNReal.div_le_div_right (Finset.sum_le_sum fun m₁ _ => measure_mono fun z hz => ?_) _
  simp only [Set.mem_ofPred_eq, add_right_comm _ z] at hz ⊢
  exact fun h => hz (by rw [h])

end Code

def Achievable (P₁ P₂ N R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ k₁ k₂ : ℕ, Real.exp (n * R₁) ≤ k₁ ∧ Real.exp (n * R₂) ≤ k₂ ∧
      ∃ c : Code P₁ P₂ n k₁ k₂, c.avgError N ≤ ε

theorem Achievable.swap {P₁ P₂ N R₁ R₂ : ℝ} (h : Achievable P₁ P₂ N R₁ R₂) :
    Achievable P₂ P₁ N R₂ R₁ := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hn₀ n hn
  exact ⟨k₂, k₁, hk₂, hk₁, c.swap, by rwa [Code.avgError_swap]⟩

theorem Achievable.awgn₁ {P₁ P₂ N R₁ R₂ : ℝ} (h : Achievable P₁ P₂ N R₁ R₂) :
    AWGN.Achievable P₁ N R₁ := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hn₀ n hn
  obtain ⟨c', hc'⟩ := c.exists_awgnCode N (Nat.cast_pos.1 ((Real.exp_pos _).trans_le hk₂))
  exact ⟨k₁, hk₁, c', hc'.trans hc⟩

theorem Achievable.awgn₂ {P₁ P₂ N R₁ R₂ : ℝ} (h : Achievable P₁ P₂ N R₁ R₂) :
    AWGN.Achievable P₂ N R₂ :=
  h.swap.awgn₁

section Fano

open AWGN AWGN.Code

variable {P' P : ℝ} {n k : ℕ}

private def toBlockCode (k : ℕ) : BlockCode (Fin k) (Fin k) (Fin k) 1 :=
  ⟨fun m _ => m, fun y => y 0⟩

private lemma avgError_toBlockCode (c : AWGN.Code P' n k) (N : ℝ) :
    (toBlockCode k).avgError (c.channel N) = c.avgError N := by
  classical
  simp only [BlockCode.avgError, avgError, Fintype.card_fin]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [BlockCode.errorProb, ← (Equiv.funUnique (Fin 1) (Fin k)).symm.sum_comp]
  simp only [DMC.blockProb, toBlockCode, Fin.prod_univ_one]
  have h : ∀ j : Fin k, (Equiv.funUnique (Fin 1) (Fin k)).symm j 0 = j := fun j => rfl
  simp only [h, channel, Measure.toPMF_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, sum_measure_singleton,
    Measure.map_apply (c.measurable_dec_add m) (Finset.measurableSet _), errorProb]
  congr 1
  ext z
  simp

private lemma inputLaw_toBlockCode (hk : 0 < k) (a : Fin k) :
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    ((toBlockCode k).inputLaw 0 a).toReal = (k : ℝ)⁻¹ := by
  simp only [BlockCode.inputLaw, toBlockCode, PMF.map_apply, PMF.ofFintype_apply, Fintype.card_fin]
  rw [tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
  simp

private lemma inputMutualInfo_channel_le_of_sum (c : AWGN.Code P' n k) {N : ℝ} (hN : 0 < N)
    (hpow : ∑ m, ∑ i, c.enc m i ^ 2 ≤ k * (n * P)) (p : PMF (Fin k))
    (hp : ∀ a, (p a).toReal = (k : ℝ)⁻¹) :
    (c.channel N).inputMutualInfo p ≤ n * awgnCapacity P N := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact absurd (p.tsum_coe) (by simp)
  set Pb : Fin n → ℝ := fun i => (∑ m, c.enc m i ^ 2) / k
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hPb : ∀ i, 0 ≤ Pb i := fun i => div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hk'.le
  set S : Fin n → ℝ := fun i => Pb i + N
  have hS : ∀ i, 0 < S i := fun i => by simp only [S]; linarith [hPb i]
  set ρ := Measure.pi fun i => gaussianReal 0 (S i).toNNReal
  set r : Fin k → ℝ := fun j => ρ.real (c.dec ⁻¹' {j})
  have hV : ∀ m j, (c.channel N m j).toReal
      = ((noise N n).map fun z => c.enc m + z).real (c.dec ⁻¹' {j}) := fun m j => by
    rw [channel_apply]
    rfl
  have hsum : ∑ j, r j = 1 := by
    have h : ∀ j, r j = (ρ.map c.dec).real {j} := fun j =>
      (map_measureReal_apply c.measurable_dec (measurableSet_singleton j)).symm
    simp only [h]
    exact sum_measureReal_singleton_eq_one _
  have hz : ∀ a j, r j = 0 → (c.channel N a j).toReal = 0 := by
    intro a j hj
    rw [hV, measureReal_def, map_noise_add_absolutelyContinuous hN (c.enc a) S hS
      ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 hj), ENNReal.toReal_zero]
  refine (DMC.inputMutualInfo_le_sum_mul_log_sub _ p (fun _ => measureReal_nonneg)
    hsum.le hz).trans ?_
  have hper : ∀ a, ∑ j, (c.channel N a j).toReal
      * (Real.log (c.channel N a j).toReal - Real.log (r j))
      ≤ ∑ i, (1 / 2 * Real.log (S i / N) - 1 / 2 + (c.enc a i ^ 2 + N) / (2 * S i)) := by
    intro a
    simp only [hV]
    exact sum_mul_log_sub_log_le hN (c.enc a) S hS c.measurable_dec
  refine (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hper a)
    (by rw [hp]; positivity)).trans ?_
  have havg : ∑ a, (p a).toReal
      * ∑ i, (1 / 2 * Real.log (S i / N) - 1 / 2 + (c.enc a i ^ 2 + N) / (2 * S i))
      = ∑ i, 1 / 2 * Real.log (S i / N) := by
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hSi := (hS i).ne'
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_div,
      Finset.sum_add_distrib, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, S, Pb] at hSi ⊢
    field_simp
    ring
  rw [havg, ← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hlog := sum_log_le_mul_log_div (fun i => S i / N) fun i => div_pos (hS i) hN
  have hpow : ∑ i, Pb i ≤ n * P := by
    simp only [Pb, ← Finset.sum_div]
    rw [Finset.sum_comm, div_le_iff₀ hk']
    linarith
  have hmean : (∑ i, S i / N) / n ≤ 1 + P / N := by
    rw [div_le_iff₀ hn', ← Finset.sum_div, div_le_iff₀ hN]
    simp only [S, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    nlinarith
  have hpos : 0 < (∑ i, S i / N) / n :=
    div_pos (Finset.sum_pos (fun i _ => div_pos (hS i) hN)
      (@Finset.univ_nonempty _ _ ⟨⟨0, hn⟩⟩)) hn'
  have h2 := Real.log_le_log hpos hmean
  unfold awgnCapacity
  nlinarith

private lemma one_sub_mul_log_le_of_sum (c : AWGN.Code P' n k) {N : ℝ} (hN : 0 < N) (hk : 0 < k)
    (hpow : ∑ m, ∑ i, c.enc m i ^ 2 ≤ k * (n * P)) :
    (1 - (c.avgError N).toReal) * Real.log k ≤ n * awgnCapacity P N + Real.log 2 := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h1 := (toBlockCode k).mutualInfo_le_sum_inputMutualInfo (c.channel N)
  rw [Fin.sum_univ_one] at h1
  have h2 := (toBlockCode k).condEntropy_fst_snd_codeMeasure_le (c.channel N)
  have h3 := mutualInfo_eq_entropy_sub_condEntropy Prod.fst Prod.snd
    ((toBlockCode k).codeMeasure (c.channel N))
  rw [BlockCode.entropy_fst_codeMeasure] at h3
  rw [avgError_toBlockCode] at h2
  have h4 := inputMutualInfo_channel_le_of_sum c hN hpow _ (inputLaw_toBlockCode hk)
  rw [Fintype.card_fin] at h2 h3
  nlinarith

end Fano

namespace Code

variable {P₁ P₂ : ℝ} {n k₁ k₂ : ℕ}

private noncomputable def mean {k : ℕ} (x : Fin k → Fin n → ℝ) : Fin n → ℝ :=
  fun i => (∑ m, x m i) / k

private lemma sum_sub_mean {k : ℕ} (x : Fin k → Fin n → ℝ) (i : Fin n) :
    ∑ m, (x m i - mean x i) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mean]
  field_simp
  ring

private lemma sum_sq_sub_mean_le {k : ℕ} (x : Fin k → Fin n → ℝ) (i : Fin n) :
    ∑ m, (x m i - mean x i) ^ 2 ≤ ∑ m, x m i ^ 2 := by
  have h : ∑ m, (x m i - mean x i) ^ 2 = ∑ m, x m i ^ 2 - mean x i * ∑ m, x m i := by
    have e : ∀ m, (x m i - mean x i) ^ 2
        = x m i ^ 2 - mean x i * x m i - mean x i * (x m i - mean x i) := fun m => by ring
    rw [Finset.sum_congr rfl fun m _ => e m, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, sum_sub_mean, mul_zero, sub_zero]
  rw [h]
  have : 0 ≤ mean x i * ∑ m, x m i := by
    simp only [mean]
    rw [div_mul_eq_mul_div]
    exact div_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)
  linarith

private noncomputable def sumEnc (c : Code P₁ P₂ n k₁ k₂) (j : Fin (k₁ * k₂)) : Fin n → ℝ :=
  (c.enc₁ (finProdFinEquiv.symm j).1 - mean c.enc₁)
    + (c.enc₂ (finProdFinEquiv.symm j).2 - mean c.enc₂)

private noncomputable def sumCode (c : Code P₁ P₂ n k₁ k₂) :
    AWGN.Code (∑ j, ∑ i, c.sumEnc j i ^ 2) n (k₁ * k₂) where
  enc := c.sumEnc
  power j := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have h0 : 0 ≤ ∑ j, ∑ i, c.sumEnc j i ^ 2 := by positivity
    calc ∑ i, c.sumEnc j i ^ 2 ≤ ∑ j, ∑ i, c.sumEnc j i ^ 2 :=
          Finset.single_le_sum (f := fun j => ∑ i, c.sumEnc j i ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ n * ∑ j, ∑ i, c.sumEnc j i ^ 2 :=
          le_mul_of_one_le_left h0 (Nat.one_le_cast.2 hn)
  dec y := finProdFinEquiv (c.dec (y + (mean c.enc₁ + mean c.enc₂)))
  measurable_dec := (measurable_of_finite _).comp (c.measurable_dec.comp (measurable_add_const _))

private lemma errorProb_sumCode (c : Code P₁ P₂ n k₁ k₂) (N : ℝ) (j : Fin (k₁ * k₂)) :
    c.sumCode.errorProb N j = c.errorProb N (finProdFinEquiv.symm j) := by
  simp only [AWGN.Code.errorProb, errorProb, sumCode, sumEnc]
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, ne_eq, ← Equiv.eq_symm_apply]
  have e : c.enc₁ (finProdFinEquiv.symm j).1 - mean c.enc₁
      + (c.enc₂ (finProdFinEquiv.symm j).2 - mean c.enc₂) + z + (mean c.enc₁ + mean c.enc₂)
      = c.enc₁ (finProdFinEquiv.symm j).1 + c.enc₂ (finProdFinEquiv.symm j).2 + z := by abel
  rw [e]

private lemma avgError_sumCode (c : Code P₁ P₂ n k₁ k₂) (N : ℝ) :
    c.sumCode.avgError N = c.avgError N := by
  simp only [AWGN.Code.avgError, avgError, errorProb_sumCode, Nat.cast_mul]
  rw [(finProdFinEquiv (m := k₁) (n := k₂)).symm.sum_comp (fun m => c.errorProb N m)]

private lemma sum_sumEnc_le (c : Code P₁ P₂ n k₁ k₂) :
    ∑ j, ∑ i, c.sumEnc j i ^ 2 ≤ ((k₁ * k₂ : ℕ) : ℝ) * (n * (P₁ + P₂)) := by
  set a := fun m i => c.enc₁ m i - mean c.enc₁ i
  set b := fun m i => c.enc₂ m i - mean c.enc₂ i
  have h1 : ∑ j, ∑ i, c.sumEnc j i ^ 2 = ∑ i, ∑ m₁, ∑ m₂, (a m₁ i + b m₂ i) ^ 2 := by
    rw [← (finProdFinEquiv (m := k₁) (n := k₂)).sum_comp, Fintype.sum_prod_type]
    simp only [sumEnc, Equiv.symm_apply_apply, Pi.add_apply, Pi.sub_apply]
    rw [Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm, Finset.sum_comm]
  have h2 : ∀ i, ∑ m₁, ∑ m₂, (a m₁ i + b m₂ i) ^ 2
      = k₂ * ∑ m₁, a m₁ i ^ 2 + k₁ * ∑ m₂, b m₂ i ^ 2 := by
    intro i
    have e : ∀ m₁ m₂, (a m₁ i + b m₂ i) ^ 2
        = a m₁ i ^ 2 + b m₂ i ^ 2 + 2 * a m₁ i * b m₂ i := fun _ _ => by ring
    have hb : ∑ m₂, b m₂ i = 0 := sum_sub_mean c.enc₂ i
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hb, mul_zero, add_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h3 : ∑ i, ∑ m, c.enc₁ m i ^ 2 ≤ k₁ * (n * P₁) := by
    rw [Finset.sum_comm]
    calc ∑ m, ∑ i, c.enc₁ m i ^ 2 ≤ ∑ _m : Fin k₁, (n * P₁) :=
          Finset.sum_le_sum fun m _ => c.power₁ m
      _ = k₁ * (n * P₁) := by simp
  have h4 : ∑ i, ∑ m, c.enc₂ m i ^ 2 ≤ k₂ * (n * P₂) := by
    rw [Finset.sum_comm]
    calc ∑ m, ∑ i, c.enc₂ m i ^ 2 ≤ ∑ _m : Fin k₂, (n * P₂) :=
          Finset.sum_le_sum fun m _ => c.power₂ m
      _ = k₂ * (n * P₂) := by simp
  have h5 : ∑ i, (k₂ * ∑ m₁, a m₁ i ^ 2 + k₁ * ∑ m₂, b m₂ i ^ 2)
      ≤ k₂ * ∑ i, ∑ m, c.enc₁ m i ^ 2 + k₁ * ∑ i, ∑ m, c.enc₂ m i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => add_le_add
      (mul_le_mul_of_nonneg_left (sum_sq_sub_mean_le c.enc₁ i) (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left (sum_sq_sub_mean_le c.enc₂ i) (Nat.cast_nonneg _))
  rw [h1, Finset.sum_congr rfl fun i _ => h2 i]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg (α := ℝ) k₂),
    mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg (α := ℝ) k₁)]

theorem one_sub_mul_log_le (c : Code P₁ P₂ n k₁ k₂) {N : ℝ} (hN : 0 < N) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) :
    (1 - (c.avgError N).toReal) * (Real.log k₁ + Real.log k₂)
      ≤ n * awgnCapacity (P₁ + P₂) N + Real.log 2 := by
  have h := one_sub_mul_log_le_of_sum c.sumCode hN (Nat.mul_pos hk₁ hk₂) c.sum_sumEnc_le
  rwa [avgError_sumCode, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)] at h

end Code

theorem Achievable.add_le {P₁ P₂ N R₁ R₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N)
    (h : Achievable P₁ P₂ N R₁ R₂) : R₁ + R₂ ≤ awgnCapacity (P₁ + P₂) N := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hC := AWGN.awgnCapacity_nonneg (add_nonneg hP₁ hP₂) hN
  set C := awgnCapacity (P₁ + P₂) N
  set δ := R₁ + R₂ - C with hδ
  have hδ0 : 0 < δ := by linarith
  have hR : 0 < R₁ + R₂ := by linarith
  set e := δ / (2 * (R₁ + R₂)) with he
  have he0 : 0 < e := by positivity
  have he1 : e * (R₁ + R₂) = δ / 2 := by
    rw [he]
    field_simp
  have he2 : 0 < 1 - e := by nlinarith
  obtain ⟨n₀, hn₀⟩ := h (ENNReal.ofReal e) (ENNReal.ofReal_pos.2 he0)
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (2 * Real.log 2 / δ)
  obtain ⟨n, hNn, hn0n⟩ : ∃ n : ℕ, n₀ ≤ n ∧ m₀ ≤ n :=
    ⟨max n₀ m₀, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hn₀ n hNn
  have hn : 2 * Real.log 2 < n * δ := by
    rw [← div_lt_iff₀ hδ0]
    exact hm₀.trans_le (by exact_mod_cast hn0n)
  have hk₁0 : (0 : ℝ) < k₁ := (Real.exp_pos _).trans_le hk₁
  have hk₂0 : (0 : ℝ) < k₂ := (Real.exp_pos _).trans_le hk₂
  have key := c.one_sub_mul_log_le hN (by exact_mod_cast hk₁0) (by exact_mod_cast hk₂0)
  have hPe : (c.avgError N).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog₁ : n * R₁ ≤ Real.log k₁ := (Real.le_log_iff_exp_le hk₁0).2 hk₁
  have hlog₂ : n * R₂ ≤ Real.log k₂ := (Real.le_log_iff_exp_le hk₂0).2 hk₂
  have hlogk : 0 ≤ Real.log k₁ + Real.log k₂ :=
    add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have h1 : (1 - e) * (Real.log k₁ + Real.log k₂) ≤ n * C + Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) hlogk).trans key
  have h2 : (1 - e) * (n * (R₁ + R₂)) ≤ (1 - e) * (Real.log k₁ + Real.log k₂) :=
    mul_le_mul_of_nonneg_left (by linarith) he2.le
  have h3 : (1 - e) * (n * (R₁ + R₂)) = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

theorem Achievable.mem_macRegion {P₁ P₂ N R₁ R₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N)
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (h : Achievable P₁ P₂ N R₁ R₂) :
    (R₁, R₂) ∈ GaussianMultiUser.macRegion P₁ P₂ N :=
  ⟨hR₁, hR₂, AWGN.le_awgnCapacity_of_achievable hP₁ hN h.awgn₁,
    AWGN.le_awgnCapacity_of_achievable hP₂ hN h.awgn₂, h.add_le hP₁ hP₂ hN⟩

end GaussianMAC

end Meat
