import Meat.Continuous.GaussianMACAchievability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Meat

namespace GaussianIC

structure Code (P₁ P₂ : ℝ) (n k₁ k₂ : ℕ) where
  enc₁ : Fin k₁ → Fin n → ℝ
  enc₂ : Fin k₂ → Fin n → ℝ
  power₁ : ∀ m, ∑ i, enc₁ m i ^ 2 ≤ n * P₁
  power₂ : ∀ m, ∑ i, enc₂ m i ^ 2 ≤ n * P₂
  dec₁ : (Fin n → ℝ) → Fin k₁
  dec₂ : (Fin n → ℝ) → Fin k₂
  measurable_dec₁ : Measurable dec₁
  measurable_dec₂ : Measurable dec₂

namespace Code

variable {P₁ P₂ : ℝ} {n k₁ k₂ : ℕ}

noncomputable def errorProb (c : Code P₁ P₂ n k₁ k₂) (a b N : ℝ) (m : Fin k₁ × Fin k₂) :
    ℝ≥0∞ :=
  ((AWGN.noise N n).prod (AWGN.noise N n))
    {z | c.dec₁ (c.enc₁ m.1 + a • c.enc₂ m.2 + z.1) ≠ m.1 ∨
      c.dec₂ (b • c.enc₁ m.1 + c.enc₂ m.2 + z.2) ≠ m.2}

noncomputable def avgError (c : Code P₁ P₂ n k₁ k₂) (a b N : ℝ) : ℝ≥0∞ :=
  (∑ m, c.errorProb a b N m) / (k₁ * k₂)

def swap (c : Code P₁ P₂ n k₁ k₂) : Code P₂ P₁ n k₂ k₁ :=
  ⟨c.enc₂, c.enc₁, c.power₂, c.power₁, c.dec₂, c.dec₁, c.measurable_dec₂, c.measurable_dec₁⟩

private lemma measurableSet_error (c : Code P₁ P₂ n k₁ k₂) (a b : ℝ) (m : Fin k₁ × Fin k₂) :
    MeasurableSet {z : (Fin n → ℝ) × (Fin n → ℝ) |
      c.dec₁ (c.enc₁ m.1 + a • c.enc₂ m.2 + z.1) ≠ m.1 ∨
        c.dec₂ (b • c.enc₁ m.1 + c.enc₂ m.2 + z.2) ≠ m.2} :=
  MeasurableSet.union
    ((measurableSet_singleton m.1).compl.preimage
      (c.measurable_dec₁.comp (measurable_const.add measurable_fst)))
    ((measurableSet_singleton m.2).compl.preimage
      (c.measurable_dec₂.comp (measurable_const.add measurable_snd)))

theorem errorProb_swap (c : Code P₁ P₂ n k₁ k₂) (a b N : ℝ) (m : Fin k₂ × Fin k₁) :
    c.swap.errorProb b a N m = c.errorProb a b N m.swap := by
  rw [errorProb, ← Measure.prod_swap, Measure.map_apply measurable_swap
    (c.swap.measurableSet_error b a m), errorProb]
  congr 1
  ext z
  simp only [swap, Set.mem_preimage, Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap]
  rw [or_comm, add_comm (c.enc₂ m.1) (b • c.enc₁ m.2), add_comm (a • c.enc₂ m.1) (c.enc₁ m.2)]

theorem avgError_swap (c : Code P₁ P₂ n k₁ k₂) (a b N : ℝ) :
    c.swap.avgError b a N = c.avgError a b N := by
  simp only [avgError, errorProb_swap, mul_comm (k₂ : ℝ≥0∞)]
  rw [← (Equiv.prodComm (Fin k₂) (Fin k₁)).symm.sum_comp]
  rfl

theorem noise_le_errorProb₁ (c : Code P₁ P₂ n k₁ k₂) (a b N : ℝ) (m : Fin k₁ × Fin k₂) :
    AWGN.noise N n {z | c.dec₁ (c.enc₁ m.1 + a • c.enc₂ m.2 + z) ≠ m.1} ≤ c.errorProb a b N m := by
  rw [← mul_one (AWGN.noise N n _), ← measure_univ (μ := AWGN.noise N n), ← Measure.prod_prod]
  exact measure_mono fun z hz => Or.inl hz.1

theorem noise_le_errorProb₂ (c : Code P₁ P₂ n k₁ k₂) (a b N : ℝ) (m : Fin k₁ × Fin k₂) :
    AWGN.noise N n {z | c.dec₂ (b • c.enc₁ m.1 + c.enc₂ m.2 + z) ≠ m.2} ≤ c.errorProb a b N m := by
  rw [← one_mul (AWGN.noise N n _), ← measure_univ (μ := AWGN.noise N n), ← Measure.prod_prod]
  exact measure_mono fun z hz => Or.inr hz.2

end Code

def Achievable (P₁ P₂ a b N R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ k₁ k₂ : ℕ, Real.exp (n * R₁) ≤ k₁ ∧ Real.exp (n * R₂) ≤ k₂ ∧
      ∃ c : Code P₁ P₂ n k₁ k₂, c.avgError a b N ≤ ε

def achievableRegion (P₁ P₂ a b N : ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ Achievable P₁ P₂ a b N R.1 R.2}

def strongRegion (P₁ P₂ a b N : ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ R.1 ≤ awgnCapacity P₁ N ∧ R.2 ≤ awgnCapacity P₂ N ∧
    R.1 + R.2 ≤ awgnCapacity (P₁ + a ^ 2 * P₂) N ∧ R.1 + R.2 ≤ awgnCapacity (b ^ 2 * P₁ + P₂) N}

theorem Achievable.swap {P₁ P₂ a b N R₁ R₂ : ℝ} (h : Achievable P₁ P₂ a b N R₁ R₂) :
    Achievable P₂ P₁ b a N R₂ R₁ := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hn₀ n hn
  exact ⟨k₂, k₁, hk₂, hk₁, c.swap, by rwa [Code.avgError_swap]⟩

private lemma map_gaussianReal_smul_add {c V₁ V₂ : ℝ} (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂) :
    ((gaussianReal 0 V₁.toNNReal).prod (gaussianReal 0 V₂.toNNReal)).map
      (fun q : ℝ × ℝ => c * q.1 + q.2) = gaussianReal 0 (c ^ 2 * V₁ + V₂).toNNReal := by
  have e : (fun q : ℝ × ℝ => c * q.1 + q.2)
      = (fun q : ℝ × ℝ => q.1 + q.2) ∘ Prod.map (c * ·) id := rfl
  rw [e, ← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_prod_map _ _
    (by fun_prop) measurable_id, Measure.map_id]
  change (gaussianReal 0 V₁.toNNReal).map (c * ·) ∗ gaussianReal 0 V₂.toNNReal = _
  rw [gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · ext
    simp [Real.coe_toNNReal _ hV₁, Real.coe_toNNReal _ hV₂,
      Real.coe_toNNReal _ (by positivity : 0 ≤ c ^ 2 * V₁ + V₂)]

theorem map_noise_smul_add {c V₁ V₂ : ℝ} (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂) (n : ℕ) :
    ((AWGN.noise V₁ n).prod (AWGN.noise V₂ n)).map (fun p => c • p.1 + p.2)
      = AWGN.noise (c ^ 2 * V₁ + V₂) n := by
  have hp := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => gaussianReal 0 V₁.toNNReal) (fun _ => gaussianReal 0 V₂.toNNReal)).map_eq
  rw [AWGN.noise, AWGN.noise, ← hp, Measure.map_map (by fun_prop)
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).measurable]
  have e : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => c • p.1 + p.2) ∘
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
      = fun w i => (fun q : ℝ × ℝ => c * q.1 + q.2) (w i) := by
    funext w i
    rfl
  rw [e]
  refine (Measure.pi_map_pi (f := fun _ (q : ℝ × ℝ) => c * q.1 + q.2)
    (fun _ => by fun_prop)).trans ?_
  rw [AWGN.noise]
  congr 1
  funext i
  exact map_gaussianReal_smul_add hV₁ hV₂

section Converse

variable {P₁ P₂ : ℝ} {n k₁ k₂ : ℕ}

private noncomputable def macDec (c : Code P₁ P₂ n k₁ k₂) (a b : ℝ) (z' y : Fin n → ℝ) :
    Fin k₁ × Fin k₂ :=
  (c.dec₁ y, c.dec₂ (b • c.enc₁ (c.dec₁ y) + a⁻¹ • (y - c.enc₁ (c.dec₁ y)) + z'))

private lemma measurable_macDec (c : Code P₁ P₂ n k₁ k₂) (a b : ℝ) (z' : Fin n → ℝ) :
    Measurable (macDec c a b z') := by
  have hF : Measurable fun p : Fin k₁ × (Fin n → ℝ) =>
      c.dec₂ (b • c.enc₁ p.1 + a⁻¹ • (p.2 - c.enc₁ p.1) + z') :=
    measurable_from_prod_countable_right fun j => c.measurable_dec₂.comp (by fun_prop)
  exact c.measurable_dec₁.prodMk (hF.comp (c.measurable_dec₁.prodMk measurable_id))

private noncomputable def toMACCode (c : Code P₁ P₂ n k₁ k₂) (a b : ℝ) (z' : Fin n → ℝ) :
    GaussianMAC.Code P₁ (a ^ 2 * P₂) n k₁ k₂ where
  enc₁ := c.enc₁
  enc₂ m := a • c.enc₂ m
  power₁ := c.power₁
  power₂ m := by
    calc ∑ i, (a • c.enc₂ m) i ^ 2 = a ^ 2 * ∑ i, c.enc₂ m i ^ 2 := by
          simp [mul_pow, Finset.mul_sum]
      _ ≤ a ^ 2 * (n * P₂) := mul_le_mul_of_nonneg_left (c.power₂ m) (sq_nonneg a)
      _ = n * (a ^ 2 * P₂) := by ring
  dec := macDec c a b z'
  measurable_dec := measurable_macDec c a b z'

private lemma errorProb_toMACCode_le (c : Code P₁ P₂ n k₁ k₂) {a : ℝ} (ha : a ≠ 0) (b N : ℝ)
    (z' : Fin n → ℝ) (m : Fin k₁ × Fin k₂) :
    (toMACCode c a b z').errorProb N m
      ≤ AWGN.noise N n {z | c.dec₁ (c.enc₁ m.1 + a • c.enc₂ m.2 + z) ≠ m.1} +
        AWGN.noise N n {z | c.dec₂ (b • c.enc₁ m.1 + c.enc₂ m.2 + (a⁻¹ • z + z')) ≠ m.2} := by
  refine (measure_mono fun z hz => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, toMACCode, macDec] at hz
  by_cases h1 : c.dec₁ (c.enc₁ m.1 + a • c.enc₂ m.2 + z) = m.1
  · right
    have key : b • c.enc₁ m.1 + a⁻¹ • (c.enc₁ m.1 + a • c.enc₂ m.2 + z - c.enc₁ m.1) + z'
        = b • c.enc₁ m.1 + c.enc₂ m.2 + (a⁻¹ • z + z') := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    rw [h1, key] at hz
    exact fun h2 => hz (Prod.ext rfl h2)
  · exact Or.inl h1

private lemma lintegral_noise_shift (c : Code P₁ P₂ n k₁ k₂) {a : ℝ} (ha : 1 ≤ a ^ 2) (b : ℝ)
    {N : ℝ} (hN : 0 < N) (m : Fin k₁ × Fin k₂) :
    ∫⁻ z', AWGN.noise N n {z | c.dec₂ (b • c.enc₁ m.1 + c.enc₂ m.2 + (a⁻¹ • z + z')) ≠ m.2}
        ∂AWGN.noise (N - N / a ^ 2) n
      = AWGN.noise N n {z | c.dec₂ (b • c.enc₁ m.1 + c.enc₂ m.2 + z) ≠ m.2} := by
  have ha0 : 0 < a ^ 2 := by linarith
  have hM : 0 ≤ N - N / a ^ 2 := by
    rw [sub_nonneg, div_le_iff₀ ha0]
    nlinarith
  set T : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {p | c.dec₂ (b • c.enc₁ m.1 + c.enc₂ m.2 + (a⁻¹ • p.1 + p.2)) ≠ m.2}
  have hg : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => a⁻¹ • p.1 + p.2 := by fun_prop
  have hS : MeasurableSet {w : Fin n → ℝ | c.dec₂ (b • c.enc₁ m.1 + c.enc₂ m.2 + w) ≠ m.2} :=
    (measurableSet_singleton m.2).compl.preimage
      (c.measurable_dec₂.comp (measurable_const.add measurable_id))
  have hT : MeasurableSet T := hS.preimage hg
  refine (Measure.prod_apply_symm (μ := AWGN.noise N n) (ν := AWGN.noise (N - N / a ^ 2) n)
    hT).symm.trans ?_
  change ((AWGN.noise N n).prod (AWGN.noise (N - N / a ^ 2) n))
    ((fun p : (Fin n → ℝ) × (Fin n → ℝ) => a⁻¹ • p.1 + p.2) ⁻¹'
      {w | c.dec₂ (b • c.enc₁ m.1 + c.enc₂ m.2 + w) ≠ m.2}) = _
  rw [← Measure.map_apply hg hS, map_noise_smul_add hN.le hM]
  congr 2
  rw [inv_pow]
  field_simp
  ring

theorem Achievable.gaussianMAC {P₁ P₂ a b N R₁ R₂ : ℝ} (hN : 0 < N) (ha : 1 ≤ a ^ 2)
    (h : Achievable P₁ P₂ a b N R₁ R₂) : GaussianMAC.Achievable P₁ (a ^ 2 * P₂) N R₁ R₂ := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    norm_num at ha
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hn₀ n hn
  set e₁ : Fin k₁ × Fin k₂ → ℝ≥0∞ :=
    fun m => AWGN.noise N n {z | c.dec₁ (c.enc₁ m.1 + a • c.enc₂ m.2 + z) ≠ m.1}
  set g : Fin k₁ × Fin k₂ → (Fin n → ℝ) → ℝ≥0∞ := fun m z' =>
    AWGN.noise N n {z | c.dec₂ (b • c.enc₁ m.1 + c.enc₂ m.2 + (a⁻¹ • z + z')) ≠ m.2}
  have hgm : ∀ m, Measurable (g m) := fun m => by
    have hT : MeasurableSet {p : (Fin n → ℝ) × (Fin n → ℝ) |
        c.dec₂ (b • c.enc₁ m.1 + c.enc₂ m.2 + (a⁻¹ • p.1 + p.2)) ≠ m.2} :=
      (measurableSet_singleton m.2).compl.preimage
        (c.measurable_dec₂.comp (measurable_const.add (by fun_prop)))
    exact measurable_measure_prodMk_right hT
  set F : (Fin n → ℝ) → ℝ≥0∞ := fun z' => ∑ m, (e₁ m + g m z')
  have hF : Measurable F := Finset.measurable_sum _ fun m _ => measurable_const.add (hgm m)
  obtain ⟨z', hz'⟩ := exists_le_lintegral (μ := AWGN.noise (N - N / a ^ 2) n) hF.aemeasurable
  have hint : ∫⁻ z'', F z'' ∂AWGN.noise (N - N / a ^ 2) n ≤ 2 * ∑ m, c.errorProb a b N m := by
    simp only [F]
    rw [lintegral_finsetSum (f := fun m z'' => e₁ m + g m z'') _
      fun m _ => measurable_const.add (hgm m), Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_noise_shift c ha b hN m, two_mul]
    exact add_le_add (c.noise_le_errorProb₁ a b N m) (c.noise_le_errorProb₂ a b N m)
  refine ⟨k₁, k₂, hk₁, hk₂, toMACCode c a b z', ?_⟩
  have hsum : ∑ m, (toMACCode c a b z').errorProb N m ≤ 2 * ∑ m, c.errorProb a b N m :=
    ((Finset.sum_le_sum fun m _ => errorProb_toMACCode_le c ha0 b N z' m).trans hz').trans hint
  calc (toMACCode c a b z').avgError N
      ≤ (2 * ∑ m, c.errorProb a b N m) / (k₁ * k₂) := ENNReal.div_le_div_right hsum _
    _ = 2 * c.avgError a b N := by rw [Code.avgError, mul_div_assoc]
    _ ≤ 2 * (ε / 2) := by gcongr
    _ = ε := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top

theorem Achievable.mem_strongRegion {P₁ P₂ a b N R₁ R₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hN : 0 < N) (ha : 1 ≤ a ^ 2) (hb : 1 ≤ b ^ 2) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (h : Achievable P₁ P₂ a b N R₁ R₂) : (R₁, R₂) ∈ strongRegion P₁ P₂ a b N := by
  obtain ⟨-, -, h₁, -, h₁₂⟩ := (h.gaussianMAC hN ha).mem_macRegion hP₁ (by positivity) hN hR₁ hR₂
  obtain ⟨-, -, h₂, -, h₂₁⟩ :=
    (h.swap.gaussianMAC hN hb).mem_macRegion hP₂ (by positivity) hN hR₂ hR₁
  exact ⟨hR₁, hR₂, h₁, h₂, h₁₂, by simpa [add_comm] using h₂₁⟩

end Converse

private lemma isClosed_strongRegion (P₁ P₂ a b N : ℝ) : IsClosed (strongRegion P₁ P₂ a b N) := by
  simp only [strongRegion, Set.ofPred_and]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_fst continuous_const).inter
        ((isClosed_le continuous_snd continuous_const).inter
          ((isClosed_le (continuous_fst.add continuous_snd) continuous_const).inter
            (isClosed_le (continuous_fst.add continuous_snd) continuous_const)))))

theorem closure_achievableRegion_subset_strongRegion {P₁ P₂ a b N : ℝ} (hP₁ : 0 ≤ P₁)
    (hP₂ : 0 ≤ P₂) (hN : 0 < N) (ha : 1 ≤ a ^ 2) (hb : 1 ≤ b ^ 2) :
    closure (achievableRegion P₁ P₂ a b N) ⊆ strongRegion P₁ P₂ a b N :=
  closure_minimal (fun _ hR => hR.2.2.mem_strongRegion hP₁ hP₂ hN ha hb hR.1 hR.2.1)
    (isClosed_strongRegion P₁ P₂ a b N)

section Unit

variable {P₁ P₂ : ℝ} {n k₁ k₂ : ℕ}

def ofMACCode (c : GaussianMAC.Code P₁ P₂ n k₁ k₂) : Code P₁ P₂ n k₁ k₂ :=
  ⟨c.enc₁, c.enc₂, c.power₁, c.power₂, fun y => (c.dec y).1, fun y => (c.dec y).2,
    measurable_fst.comp c.measurable_dec, measurable_snd.comp c.measurable_dec⟩

theorem errorProb_ofMACCode_le (c : GaussianMAC.Code P₁ P₂ n k₁ k₂) (N : ℝ)
    (m : Fin k₁ × Fin k₂) : (ofMACCode c).errorProb 1 1 N m ≤ 2 * c.errorProb N m := by
  have hS : MeasurableSet {z : Fin n → ℝ | c.dec (c.enc₁ m.1 + c.enc₂ m.2 + z) ≠ m} :=
    (measurableSet_singleton m).compl.preimage
      (c.measurable_dec.comp (measurable_const.add measurable_id))
  rw [two_mul]
  refine (measure_mono (t := {z : Fin n → ℝ | c.dec (c.enc₁ m.1 + c.enc₂ m.2 + z) ≠ m} ×ˢ
      Set.univ ∪ Set.univ ×ˢ {z : Fin n → ℝ | c.dec (c.enc₁ m.1 + c.enc₂ m.2 + z) ≠ m})
    fun z hz => ?_).trans ((measure_union_le _ _).trans ?_)
  · simp only [Set.mem_ofPred_eq, ofMACCode, one_smul] at hz
    rcases hz with h | h
    · exact Or.inl ⟨fun h' => h (by rw [h']), Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, fun h' => h (by rw [h'])⟩
  · rw [Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, one_mul]
    rfl

theorem achievable_of_gaussianMAC {P₁ P₂ N R₁ R₂ : ℝ}
    (h : GaussianMAC.Achievable P₁ P₂ N R₁ R₂) : Achievable P₁ P₂ 1 1 N R₁ R₂ := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hn₀ n hn
  refine ⟨k₁, k₂, hk₁, hk₂, ofMACCode c, ?_⟩
  calc (ofMACCode c).avgError 1 1 N ≤ (2 * ∑ m, c.errorProb N m) / (k₁ * k₂) := by
        rw [Finset.mul_sum]
        exact ENNReal.div_le_div_right
          (Finset.sum_le_sum fun m _ => errorProb_ofMACCode_le c N m) _
    _ = 2 * c.avgError N := by rw [GaussianMAC.Code.avgError, mul_div_assoc]
    _ ≤ 2 * (ε / 2) := by gcongr
    _ = ε := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top

theorem strongRegion_one_one (P₁ P₂ N : ℝ) :
    strongRegion P₁ P₂ 1 1 N = GaussianMultiUser.macRegion P₁ P₂ N := by
  ext R
  simp only [strongRegion, GaussianMultiUser.macRegion, Set.mem_ofPred_eq, one_pow, one_mul,
    and_self]

theorem closure_achievableRegion_one_one {P₁ P₂ N : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hN : 0 < N) :
    closure (achievableRegion P₁ P₂ 1 1 N) = GaussianMultiUser.macRegion P₁ P₂ N := by
  refine subset_antisymm ?_ ?_
  · rw [← strongRegion_one_one]
    exact closure_achievableRegion_subset_strongRegion hP₁ hP₂ hN (by norm_num) (by norm_num)
  · rw [← GaussianMAC.closure_achievable_eq hP₁ hP₂ hN]
    exact closure_mono fun R hR => ⟨hR.1, hR.2.1, achievable_of_gaussianMAC hR.2.2⟩

end Unit

end GaussianIC

end Meat
