import Meat.Continuous.GaussianMAC
import Meat.Continuous.GaussianMACQuantization
import Meat.Channel.MultipleAccessConverse

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Meat

namespace GaussianMAC

open AWGN

variable {A B : Type*} [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

private def blockEquiv {n m L r : ℕ} (h : m * L + r = n) : (Fin m × Fin L) ⊕ Fin r ≃ Fin n :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans (finSumFinEquiv.trans (finCongr h))

private def blocks {n m L r : ℕ} (h : m * L + r = n) (z : Fin n → ℝ) : Fin m → Fin L → ℝ :=
  fun t l => z (blockEquiv h (.inl (t, l)))

private lemma measurable_blocks {n m L r : ℕ} (h : m * L + r = n) : Measurable (blocks h) := by
  unfold blocks
  fun_prop

private lemma map_noise_blocks (N : ℝ) {n m L r : ℕ} (h : m * L + r = n) :
    (noise N n).map (blocks h) = Measure.pi fun _ : Fin m => noise N L := by
  set γ := gaussianReal 0 N.toNNReal
  set e := blockEquiv h
  have h1 := measurePreserving_piCongrLeft (fun _ : (Fin m × Fin L) ⊕ Fin r => γ) e.symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : (Fin m × Fin L) ⊕ Fin r => γ)
  have h4 := Measure.infinitePi_map_curry (fun (_ : Fin m) (_ : Fin L) => γ)
  simp_rw [Measure.infinitePi_eq_pi] at h4
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin m) (Fin L) ℝ) _ _ :=
    ⟨(MeasurableEquiv.curry (Fin m) (Fin L) ℝ).measurable, h4⟩
  have hfst : MeasurePreserving Prod.fst ((Measure.pi fun _ : Fin m × Fin L => γ).prod
      (Measure.pi fun _ : Fin r => γ)) (Measure.pi fun _ : Fin m × Fin L => γ) :=
    ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
  have hf : blocks h = MeasurableEquiv.curry (Fin m) (Fin L) ℝ ∘ Prod.fst
      ∘ MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin m × Fin L) ⊕ Fin r => ℝ)
      ∘ MeasurableEquiv.piCongrLeft (fun _ => ℝ) e.symm := by
    funext z t l
    simp [blocks, e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
      MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.curry]
  rw [hf]
  exact (hc.comp (hfst.comp (h2.comp h1))).map_eq

private def embed {n m L r : ℕ} (h : m * L + r = n) (w : Fin m → Fin L → ℝ) : Fin n → ℝ :=
  fun i => Sum.elim (fun p => w p.1 p.2) (fun _ => 0) ((blockEquiv h).symm i)

private lemma blocks_embed {n m L r : ℕ} (h : m * L + r = n) (w : Fin m → Fin L → ℝ) :
    blocks h (embed h w) = w := by
  funext t l
  simp [blocks, embed]

private lemma blocks_add {n m L r : ℕ} (h : m * L + r = n) (x z : Fin n → ℝ) :
    blocks h (x + z) = blocks h x + blocks h z := rfl

private lemma sum_sq_embed {n m L r : ℕ} (h : m * L + r = n) (w : Fin m → Fin L → ℝ) :
    ∑ i, embed h w i ^ 2 = ∑ t, ∑ l, w t l ^ 2 := by
  rw [← (blockEquiv h).sum_comp]
  simp [embed, Fintype.sum_sum_type, Fintype.sum_prod_type]

private lemma embed_add {n m L r : ℕ} (h : m * L + r = n) (w w' : Fin m → Fin L → ℝ) :
    embed h (w + w') = embed h w + embed h w' := by
  funext i
  simp only [embed, Pi.add_apply]
  rcases (blockEquiv h).symm i with p | p <;> simp

private lemma sum_sq_embed_le {P : ℝ} (hP : 0 ≤ P) {n m L r : ℕ} (h : m * L + r = n)
    (a : A → Fin L → ℝ) (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P) (x : Fin m → A) :
    ∑ i, embed h (fun t => a (x t)) i ^ 2 ≤ n * P := by
  rw [sum_sq_embed]
  calc ∑ t, ∑ l, a (x t) l ^ 2 ≤ ∑ _t : Fin m, (L * P) :=
        Finset.sum_le_sum fun t _ => ha _
    _ = m * L * P := by simp [mul_assoc]
    _ ≤ n * P := mul_le_mul_of_nonneg_right (by exact_mod_cast h ▸ Nat.le_add_right _ _) hP

private lemma noise_blockError {M : Type*} [DecidableEq M] (N : ℝ) {n m L r : ℕ}
    (h : m * L + r = n) (a : A → Fin L → ℝ) (q : (Fin L → ℝ) → B) (hq : Measurable q)
    (c : BlockCode M A B m) (i : M) :
    noise N n {z | c.dec (fun t => q (blocks h (embed h (fun t => a (c.enc i t)) + z) t)) ≠ i}
      = c.errorProb (blockChannel N a q) i := by
  classical
  set G : (Fin m → Fin L → ℝ) → Fin m → B := fun w t => q (a (c.enc i t) + w t)
  have hG : Measurable G :=
    measurable_pi_iff.2 fun t => hq.comp ((measurable_const_add _).comp (measurable_pi_apply t))
  set T : Set (Fin m → B) := ↑(Finset.univ.filter fun v => c.dec v ≠ i)
  have hset : {z | c.dec (fun t => q (blocks h (embed h (fun t => a (c.enc i t)) + z) t)) ≠ i}
      = blocks h ⁻¹' (G ⁻¹' T) := by
    ext z
    simp [T, G, blocks_add, blocks_embed]
  have hT : MeasurableSet T := Finset.measurableSet _
  rw [hset, ← Measure.map_apply (measurable_blocks h) (hG hT),
    map_noise_blocks, ← Measure.map_apply hG hT,
    Measure.pi_map_pi (f := fun t u => q (a (c.enc i t) + u)) fun t =>
      (hq.comp (measurable_const_add _)).aemeasurable, ← sum_measure_singleton,
    BlockCode.errorProb, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : c.dec v = i
  · simp [hv]
  · rw [ite_eq_left hv, ite_eq_right hv, ← Set.univ_pi_singleton, Measure.pi_pi, DMC.blockProb]
    rfl

section Reduction

variable {A₁ A₂ : Type*}

private noncomputable def toCode {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) {n m L r k₁ k₂ : ℕ}
    (h : m * L + r = n) (a₁ : A₁ → Fin L → ℝ) (a₂ : A₂ → Fin L → ℝ)
    (ha₁ : ∀ x, ∑ l, a₁ x l ^ 2 ≤ L * P₁) (ha₂ : ∀ x, ∑ l, a₂ x l ^ 2 ≤ L * P₂)
    (q : (Fin L → ℝ) → B) (hq : Measurable q) (c : MACCode (Fin k₁) (Fin k₂) A₁ A₂ B m) :
    Code P₁ P₂ n k₁ k₂ where
  enc₁ i := embed h fun t => a₁ (c.enc₁ i t)
  enc₂ i := embed h fun t => a₂ (c.enc₂ i t)
  power₁ _ := sum_sq_embed_le hP₁ h a₁ ha₁ _
  power₂ _ := sum_sq_embed_le hP₂ h a₂ ha₂ _
  dec y := c.dec fun t => q (blocks h y t)
  measurable_dec := (measurable_of_finite c.dec).comp
    (measurable_pi_iff.2 fun t => hq.comp ((measurable_pi_apply t).comp (measurable_blocks h)))

private lemma avgError_toCode {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (N : ℝ) {n m L r k₁ k₂ : ℕ}
    (h : m * L + r = n) (a₁ : A₁ → Fin L → ℝ) (a₂ : A₂ → Fin L → ℝ)
    (ha₁ : ∀ x, ∑ l, a₁ x l ^ 2 ≤ L * P₁) (ha₂ : ∀ x, ∑ l, a₂ x l ^ 2 ≤ L * P₂)
    (q : (Fin L → ℝ) → B) (hq : Measurable q) (c : MACCode (Fin k₁) (Fin k₂) A₁ A₂ B m) :
    (toCode hP₁ hP₂ h a₁ a₂ ha₁ ha₂ q hq c).avgError N
      = c.avgError (blockChannel N (fun x : A₁ × A₂ => a₁ x.1 + a₂ x.2) q) := by
  have he : ∀ i : Fin k₁ × Fin k₂, (toCode hP₁ hP₂ h a₁ a₂ ha₁ ha₂ q hq c).errorProb N i
      = c.errorProb (blockChannel N (fun x : A₁ × A₂ => a₁ x.1 + a₂ x.2) q) i := by
    intro i
    have e : (toCode hP₁ hP₂ h a₁ a₂ ha₁ ha₂ q hq c).enc₁ i.1
        + (toCode hP₁ hP₂ h a₁ a₂ ha₁ ha₂ q hq c).enc₂ i.2
        = embed h fun t => (fun x : A₁ × A₂ => a₁ x.1 + a₂ x.2) (c.toBlockCode.enc i t) := by
      rw [show (fun t => (fun x : A₁ × A₂ => a₁ x.1 + a₂ x.2) (c.toBlockCode.enc i t))
          = (fun t => a₁ (c.enc₁ i.1 t)) + (fun t => a₂ (c.enc₂ i.2 t)) from rfl, embed_add]
      rfl
    rw [Code.errorProb, e]
    exact noise_blockError N h (fun x : A₁ × A₂ => a₁ x.1 + a₂ x.2) q hq c.toBlockCode i
  simp only [Code.avgError, MACCode.avgError, he, Fintype.card_fin]

private lemma rate_le {n m L r : ℕ} (hn : (n : ℝ) = m * L + r) (hr : (r : ℝ) ≤ L) {R δ : ℝ}
    (hR : 0 ≤ R) (hm : R ≤ m * δ) : n * R ≤ m * (L * (R + δ)) := by
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  rw [hn]
  nlinarith [mul_le_mul_of_nonneg_right hr hR, mul_le_mul_of_nonneg_left hm hL]

theorem achievable_of_lt_blockChannel [Fintype A₁] [MeasurableSpace A₁]
    [MeasurableSingletonClass A₁] [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
    {P₁ P₂ N R₁ R₂ : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) {L : ℕ} (hL : 0 < L)
    (a₁ : A₁ → Fin L → ℝ) (a₂ : A₂ → Fin L → ℝ) (ha₁ : ∀ x, ∑ l, a₁ x l ^ 2 ≤ L * P₁)
    (ha₂ : ∀ x, ∑ l, a₂ x l ^ 2 ≤ L * P₂) (q : (Fin L → ℝ) → B) (hq : Measurable q)
    (p₁ : PMF A₁) (p₂ : PMF A₂)
    (h₁ : L * R₁ < I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
      MAC.jointMeasure (blockChannel N (fun x : A₁ × A₂ => a₁ x.1 + a₂ x.2) q) p₁ p₂])
    (h₂ : L * R₂ < I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
      MAC.jointMeasure (blockChannel N (fun x : A₁ × A₂ => a₁ x.1 + a₂ x.2) q) p₁ p₂])
    (h₃ : L * (R₁ + R₂) < I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
      MAC.jointMeasure (blockChannel N (fun x : A₁ × A₂ => a₁ x.1 + a₂ x.2) q) p₁ p₂]) :
    Achievable P₁ P₂ N R₁ R₂ := by
  set W := blockChannel N (fun x : A₁ × A₂ => a₁ x.1 + a₂ x.2) q
  set I₁ := I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
    MAC.jointMeasure W p₁ p₂]
  set I₂ := I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
    MAC.jointMeasure W p₁ p₂]
  set I₃ := I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ; MAC.jointMeasure W p₁ p₂]
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  set δ := min (min (I₁ - L * R₁) (I₂ - L * R₂)) (I₃ - L * (R₁ + R₂)) / (4 * L) with hδ
  have hm1 := min_le_left (min (I₁ - L * R₁) (I₂ - L * R₂)) (I₃ - L * (R₁ + R₂))
  have hm2 := min_le_right (min (I₁ - L * R₁) (I₂ - L * R₂)) (I₃ - L * (R₁ + R₂))
  have hm3 := min_le_left (I₁ - L * R₁) (I₂ - L * R₂)
  have hm4 := min_le_right (I₁ - L * R₁) (I₂ - L * R₂)
  have hδ0 : 0 < δ := div_pos (lt_min (lt_min (by linarith) (by linarith)) (by linarith))
    (by positivity)
  have hLδ : 4 * L * δ = min (min (I₁ - L * R₁) (I₂ - L * R₂)) (I₃ - L * (R₁ + R₂)) := by
    rw [hδ]
    field_simp
  have hW : MAC.Achievable W (L * (R₁ + δ)) (L * (R₂ + δ)) :=
    MAC.achievable_of_lt W p₁ p₂ (by nlinarith) (by nlinarith) (by nlinarith)
  intro ε hε
  obtain ⟨n₁, hn₁⟩ := hW ε hε
  obtain ⟨m₁, hm₁⟩ := exists_nat_gt ((R₁ + R₂) / δ)
  refine ⟨L * max n₁ m₁, fun n hn => ?_⟩
  have h : n / L * L + n % L = n := by rw [mul_comm]; exact Nat.div_add_mod n L
  have hm : max n₁ m₁ ≤ n / L := (Nat.le_div_iff_mul_le hL).2 (by rw [mul_comm]; exact hn)
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hn₁ (n / L) (le_of_max_le_left hm)
  have hr : ((n % L : ℕ) : ℝ) ≤ L := by exact_mod_cast (Nat.mod_lt n hL).le
  have hn' : (n : ℝ) = (n / L : ℕ) * L + (n % L : ℕ) := by exact_mod_cast h.symm
  have hmδ : R₁ + R₂ ≤ (n / L : ℕ) * δ := by
    have := (div_lt_iff₀ hδ0).1 (hm₁.trans_le (Nat.cast_le.2 (le_of_max_le_right hm)))
    linarith
  refine ⟨k₁, k₂, le_trans (Real.exp_le_exp.2 (rate_le hn' hr hR₁ (by linarith))) hk₁,
    le_trans (Real.exp_le_exp.2 (rate_le hn' hr hR₂ (by linarith))) hk₂,
    toCode hP₁ hP₂ h a₁ a₂ ha₁ ha₂ q hq c, ?_⟩
  rw [avgError_toCode]
  exact hc

end Reduction

section Quantized

private abbrev Blk (n L : ℕ) : Type := Fin (Fintype.card (Fin L → Level n))

private abbrev Out (n L : ℕ) : Type := Blk n L × (Blk n L → Blk n L) × (Blk n L → Blk n L)

private noncomputable def quant (n L : ℕ) (P₁ P₂ : ℝ) (y : Fin L → ℝ) : Out n L :=
  (blockQuant n L y, fun x₂ => blockQuant n L (y - blockInput n L P₂ x₂),
    fun x₁ => blockQuant n L (y - blockInput n L P₁ x₁))

private lemma measurable_quant (n L : ℕ) (P₁ P₂ : ℝ) : Measurable (quant n L P₁ P₂) :=
  (measurable_blockQuant n L).prodMk
    ((measurable_pi_iff.2 fun _ => (measurable_blockQuant n L).comp (measurable_sub_const _)).prodMk
      (measurable_pi_iff.2 fun _ => (measurable_blockQuant n L).comp (measurable_sub_const _)))

private noncomputable def chan (N : ℝ) (n L : ℕ) (P₁ P₂ : ℝ) : DMC (Blk n L × Blk n L) (Out n L) :=
  blockChannel N (fun x => blockInput n L P₁ x.1 + blockInput n L P₂ x.2) (quant n L P₁ P₂)

private noncomputable def uGen (θ N : ℝ) (n L : ℕ) (t : Fin L → ℝ) (b : Blk n L) : ℝ :=
  ∏ l, letterRatio θ N n (t l) ((Fintype.equivFin (Fin L → Level n)).symm b l)

variable {θ N : ℝ}

private lemma uGen_pos (hθ : 0 < θ) (hN : 0 < N) (n L : ℕ) (t : Fin L → ℝ) (b : Blk n L) :
    0 < uGen θ N n L t b :=
  Finset.prod_pos fun _ _ => postRatio_pos hθ (by positivity) _ _

private lemma log_uGen (hθ : 0 < θ) (hN : 0 < N) (n L : ℕ) (t : Fin L → ℝ) (b : Blk n L) :
    Real.log (uGen θ N n L t b)
      = ∑ l, Real.log (letterRatio θ N n (t l) ((Fintype.equivFin (Fin L → Level n)).symm b l)) :=
  Real.log_prod fun _ _ => (postRatio_pos hθ (by positivity) _ _).ne'

private lemma integral_uGen (hθ : 0 < θ) (hN : 0 < N) (n L : ℕ) (b : Blk n L) :
    ∫ t, uGen θ N n L t b ∂(Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal) = 1 := by
  simp only [uGen]
  rw [integral_fintype_prod_eq_prod (fun l t =>
    letterRatio θ N n t ((Fintype.equivFin (Fin L → Level n)).symm b l))]
  exact Finset.prod_eq_one fun l _ => integral_postRatio hθ (by positivity) _

private lemma integrable_log_uGen {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] (hθ : 0 < θ) (hN : 0 < N) (n L : ℕ) {f : X → Fin L → ℝ}
    {g : X → Blk n L} (hf : Measurable f) (hg : Measurable g)
    (hf2 : ∀ l, Integrable (fun x => f x l ^ 2) μ) :
    Integrable (fun x => Real.log (uGen θ N n L (f x) (g x))) μ := by
  simp_rw [log_uGen hθ hN]
  exact integrable_finsetSum _ fun l _ => integrable_log_letterRatio hθ hN n
    ((measurable_pi_apply l).comp hf)
    ((measurable_of_finite fun b : Blk n L =>
      (Fintype.equivFin (Fin L → Level n)).symm b l).comp hg)
    (hf2 l)

private lemma integrable_sq_eval (θ : ℝ) {L : ℕ} (l : Fin L) :
    Integrable (fun t : Fin L → ℝ => t l ^ 2)
      (Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal) :=
  (measurePreserving_eval (fun _ : Fin L => gaussianReal 0 θ.toNNReal) l
    ).integrable_comp_of_integrable
    (integrable_sq_gaussianReal _)

private lemma blockLaw_toReal (θ : ℝ) (n L : ℕ) (x : Blk n L) :
    (blockLaw θ n L x).toReal
      = (Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal).real (blockQuant n L ⁻¹' {x}) := by
  rw [blockLaw, Measure.toPMF_apply,
    Measure.map_apply (measurable_blockQuant n L) (measurableSet_singleton _), measureReal_def]

private lemma blockInput_blockQuant (n L : ℕ) (P : ℝ) (t : Fin L → ℝ) :
    blockInput n L P (blockQuant n L t) = clipValue n L P fun k => level n (t k) := by
  simp [blockInput, blockQuant]

private lemma log_uGen_blockQuant (hθ : 0 < θ) (hN : 0 < N) (n L : ℕ) (t y : Fin L → ℝ) :
    Real.log (uGen θ N n L t (blockQuant n L y))
      = ∑ l, Real.log (letterRatio θ N n (t l) (level n (y l))) := by
  simp [log_uGen hθ hN, blockQuant]

end Quantized

section Information

variable {A₁ A₂ : Type*} [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]

private lemma condMutualInfo_eq₁ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ; MAC.jointMeasure W p₁ p₂] =
      (MAC.sideChannel₁ W p₂).inputMutualInfo p₁ := by
  have h := mutualInfo_pair_eq_add_condMutualInfo (MAC.jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.1) (Y := fun ω => ω.2.2) (Z := fun ω => ω.2.1)
  have hs := mutualInfo_comp_right_of_injective (MAC.jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.1) (Y := fun ω => ω.2) Prod.swap_injective
  have h0 := MAC.mutualInfo_inputs_eq_zero W p₁ p₂
  rw [MAC.inputMutualInfo_sideChannel₁, ← hs]
  change _ = I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => (ω.2.2, ω.2.1) ; MAC.jointMeasure W p₁ p₂]
  linarith

private lemma condMutualInfo_eq₂ (W : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ; MAC.jointMeasure W p₁ p₂] =
      (MAC.sideChannel₂ W p₁).inputMutualInfo p₂ := by
  have h := mutualInfo_pair_eq_add_condMutualInfo (MAC.jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.2.1) (Y := fun ω => ω.2.2) (Z := fun ω => ω.1)
  have hs := mutualInfo_comp_right_of_injective (MAC.jointMeasure W p₁ p₂)
    (X := fun ω : A₁ × A₂ × B => ω.2.1) (Y := fun ω => (ω.2.2, ω.1)) Prod.swap_injective
  have h0 := MAC.mutualInfo_inputs_eq_zero W p₁ p₂
  rw [mutualInfo_comm] at h0
  rw [MAC.inputMutualInfo_sideChannel₂]
  refine Eq.trans ?_ hs.symm
  linarith

end Information

section Bounds

variable {θ₁ θ₂ N : ℝ}

private lemma integral_le_condMutualInfo₁ (hθ₁ : 0 < θ₁) (hN : 0 < N) (n L : ℕ) (P₁ P₂ : ℝ) :
    ∫ t, ∫ z, ∑ l, Real.log (letterRatio θ₁ N n (t l)
        (level n (clipValue n L P₁ (fun k => level n (t k)) l + z l))) ∂noise N L
      ∂Measure.pi (fun _ : Fin L => gaussianReal 0 θ₁.toNNReal)
      ≤ I[fun ω : Blk n L × Blk n L × Out n L => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure (chan N n L P₁ P₂) (blockLaw θ₁ n L) (blockLaw θ₂ n L)] := by
  rw [condMutualInfo_eq₁]
  refine le_of_eq_of_le ?_ (DMC.integral_sum_mul_log_le_inputMutualInfo
    (MAC.sideChannel₁ (chan N n L P₁ P₂) (blockLaw θ₂ n L)) (blockLaw θ₁ n L)
    (measurable_blockQuant n L) (blockLaw_toReal θ₁ n L)
    (fun t (b : Blk n L × Out n L) => uGen θ₁ N n L t (b.2.2.1 b.1))
    (fun t (b : Blk n L × Out n L) => uGen_pos hθ₁ hN n L t (b.2.2.1 b.1))
    (fun (b : Blk n L × Out n L) => integral_uGen hθ₁ hN n L (b.2.2.1 b.1))
    (fun b => integrable_log_uGen hθ₁ hN n L measurable_id measurable_const
      (integrable_sq_eval θ₁)))
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  rw [Fintype.sum_prod_type]
  have hx : ∀ x₂ : Blk n L, ∑ y : Out n L,
      (MAC.sideChannel₁ (chan N n L P₁ P₂) (blockLaw θ₂ n L) (blockQuant n L t) (x₂, y)).toReal
        * Real.log (uGen θ₁ N n L t (y.2.1 x₂))
      = (blockLaw θ₂ n L x₂).toReal * ∫ z, ∑ l, Real.log (letterRatio θ₁ N n (t l)
        (level n (clipValue n L P₁ (fun k => level n (t k)) l + z l))) ∂noise N L := by
    intro x₂
    simp only [MAC.sideChannel₁, DMC.jointPMF_apply, ENNReal.toReal_mul, mul_assoc,
      ← Finset.mul_sum]
    congr 1
    rw [chan, sum_blockChannel_toReal_mul N _ (measurable_quant n L P₁ P₂)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [quant]
    rw [show ∀ a b z : Fin L → ℝ, a + b + z - b = a + z from fun a b z => by abel,
      log_uGen_blockQuant hθ₁ hN, blockInput_blockQuant]
    rfl
  simp only [hx, ← Finset.sum_mul, sum_toReal_pmf_eq_one, one_mul]

private lemma integral_le_condMutualInfo₂ (hθ₂ : 0 < θ₂) (hN : 0 < N) (n L : ℕ) (P₁ P₂ : ℝ) :
    ∫ t, ∫ z, ∑ l, Real.log (letterRatio θ₂ N n (t l)
        (level n (clipValue n L P₂ (fun k => level n (t k)) l + z l))) ∂noise N L
      ∂Measure.pi (fun _ : Fin L => gaussianReal 0 θ₂.toNNReal)
      ≤ I[fun ω : Blk n L × Blk n L × Out n L => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
        MAC.jointMeasure (chan N n L P₁ P₂) (blockLaw θ₁ n L) (blockLaw θ₂ n L)] := by
  rw [condMutualInfo_eq₂]
  refine le_of_eq_of_le ?_ (DMC.integral_sum_mul_log_le_inputMutualInfo
    (MAC.sideChannel₂ (chan N n L P₁ P₂) (blockLaw θ₁ n L)) (blockLaw θ₂ n L)
    (measurable_blockQuant n L) (blockLaw_toReal θ₂ n L)
    (fun t (b : Blk n L × Out n L) => uGen θ₂ N n L t (b.2.2.2 b.1))
    (fun t (b : Blk n L × Out n L) => uGen_pos hθ₂ hN n L t (b.2.2.2 b.1))
    (fun (b : Blk n L × Out n L) => integral_uGen hθ₂ hN n L (b.2.2.2 b.1))
    (fun b => integrable_log_uGen hθ₂ hN n L measurable_id measurable_const
      (integrable_sq_eval θ₂)))
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  rw [Fintype.sum_prod_type]
  have hx : ∀ x₁ : Blk n L, ∑ y : Out n L,
      (MAC.sideChannel₂ (chan N n L P₁ P₂) (blockLaw θ₁ n L) (blockQuant n L t) (x₁, y)).toReal
        * Real.log (uGen θ₂ N n L t (y.2.2 x₁))
      = (blockLaw θ₁ n L x₁).toReal * ∫ z, ∑ l, Real.log (letterRatio θ₂ N n (t l)
        (level n (clipValue n L P₂ (fun k => level n (t k)) l + z l))) ∂noise N L := by
    intro x₁
    simp only [MAC.sideChannel₂, DMC.jointPMF_apply, ENNReal.toReal_mul, mul_assoc,
      ← Finset.mul_sum]
    congr 1
    rw [chan, sum_blockChannel_toReal_mul N _ (measurable_quant n L P₁ P₂)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [quant]
    rw [show ∀ a b z : Fin L → ℝ, a + b + z - a = b + z from fun a b z => by abel,
      log_uGen_blockQuant hθ₂ hN, blockInput_blockQuant]
    rfl
  simp only [hx, ← Finset.sum_mul, sum_toReal_pmf_eq_one, one_mul]

private lemma integral_le_mutualInfo (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hN : 0 < N) (n L : ℕ)
    (P₁ P₂ : ℝ) :
    (∫ t, ∫ z, ∑ l, Real.log (letterRatio θ₂ (θ₁ + N) n (t.2 l)
          (level n (clipValue n L P₁ (fun k => level n (t.1 k)) l
            + clipValue n L P₂ (fun k => level n (t.2 k)) l + z l))) ∂noise N L
        ∂((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
          (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal)))
      + ∫ t, ∫ z, ∑ l, Real.log (letterRatio θ₁ N n (t l)
          (level n (clipValue n L P₁ (fun k => level n (t k)) l + z l))) ∂noise N L
        ∂Measure.pi (fun _ : Fin L => gaussianReal 0 θ₁.toNNReal)
      ≤ I[fun ω : Blk n L × Blk n L × Out n L => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
        MAC.jointMeasure (chan N n L P₁ P₂) (blockLaw θ₁ n L) (blockLaw θ₂ n L)] := by
  have hM : 0 < θ₁ + N := by linarith
  set M := θ₁ + N
  set μ₁L := Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal
  set μ₂L := Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal
  set W := chan N n L P₁ P₂
  set Q : (Fin L → ℝ) × (Fin L → ℝ) → Blk n L × Blk n L :=
    fun t => (blockQuant n L t.1, blockQuant n L t.2)
  have hQ : Measurable Q :=
    ((measurable_blockQuant n L).comp measurable_fst).prodMk
      ((measurable_blockQuant n L).comp measurable_snd)
  have hp : ∀ x, (MAC.inputPMF (blockLaw θ₁ n L) (blockLaw θ₂ n L) x).toReal
      = (μ₁L.prod μ₂L).real (Q ⁻¹' {x}) := by
    rintro ⟨x₁, x₂⟩
    have hs : Q ⁻¹' {(x₁, x₂)} = (blockQuant n L ⁻¹' {x₁}) ×ˢ (blockQuant n L ⁻¹' {x₂}) := by
      ext t
      simp [Q, Prod.ext_iff]
    rw [MAC.inputPMF_apply, ENNReal.toReal_mul, blockLaw_toReal, blockLaw_toReal, hs,
      measureReal_prod_prod]
  set u₂ : (Fin L → ℝ) × (Fin L → ℝ) → Out n L → ℝ := fun t b => uGen θ₂ M n L t.2 b.1
  set u₁ : (Fin L → ℝ) × (Fin L → ℝ) → Out n L → ℝ :=
    fun t b => uGen θ₁ N n L t.1 (b.2.1 (blockQuant n L t.2))
  have hu₂ : ∀ t b, 0 < u₂ t b := fun t b => uGen_pos hθ₂ hM n L _ _
  have hu₁ : ∀ t b, 0 < u₁ t b := fun t b => uGen_pos hθ₁ hN n L _ _
  have hf2₁ : ∀ l, Integrable (fun t : (Fin L → ℝ) × (Fin L → ℝ) => t.1 l ^ 2) (μ₁L.prod μ₂L) :=
    fun l => (integrable_sq_eval θ₁ l).comp_fst μ₂L
  have hf2₂ : ∀ l, Integrable (fun t : (Fin L → ℝ) × (Fin L → ℝ) => t.2 l ^ 2) (μ₁L.prod μ₂L) :=
    fun l => (integrable_sq_eval θ₂ l).comp_snd μ₁L
  have hl₂ : ∀ b, Integrable (fun t => Real.log (u₂ t b)) (μ₁L.prod μ₂L) := fun b =>
    integrable_log_uGen hθ₂ hM n L measurable_snd measurable_const hf2₂
  have hl₁ : ∀ b, Integrable (fun t => Real.log (u₁ t b)) (μ₁L.prod μ₂L) := fun b =>
    integrable_log_uGen hθ₁ hN n L measurable_fst
      ((measurable_of_finite b.2.1).comp ((measurable_blockQuant n L).comp measurable_snd)) hf2₁
  have hm : ∀ x₂ : Blk n L, MeasurableSet (blockQuant n L ⁻¹' {x₂}) := fun x₂ =>
    measurable_blockQuant n L (measurableSet_singleton _)
  have hi₁ : ∀ c, Integrable (fun t => uGen θ₁ N n L t c) μ₁L := fun c =>
    Integrable.of_integral_ne_zero (by rw [integral_uGen hθ₁ hN]; exact one_ne_zero)
  have hi₂ : ∀ c, Integrable (fun t => uGen θ₂ M n L t c) μ₂L := fun c =>
    Integrable.of_integral_ne_zero (by rw [integral_uGen hθ₂ hM]; exact one_ne_zero)
  have hu1 : ∀ b : Out n L, ∫ t, u₂ t b * u₁ t b ∂(μ₁L.prod μ₂L) = 1 := by
    intro b
    have hpt : ∀ t : (Fin L → ℝ) × (Fin L → ℝ), u₂ t b * u₁ t b = ∑ x₂ : Blk n L,
        uGen θ₁ N n L t.1 (b.2.1 x₂)
          * (blockQuant n L ⁻¹' {x₂}).indicator (fun t₂ => uGen θ₂ M n L t₂ b.1) t.2 := by
      intro t
      rw [Finset.sum_eq_single (blockQuant n L t.2)]
      · rw [Set.indicator_of_mem (by simp)]
        exact mul_comm _ _
      · intro x₂ _ hx
        rw [Set.indicator_of_notMem (by simpa [eq_comm] using hx), mul_zero]
      · exact fun h => absurd (Finset.mem_univ _) h
    have hsum : ∀ t₂ : Fin L → ℝ, ∑ x₂ : Blk n L,
        (blockQuant n L ⁻¹' {x₂}).indicator (fun t₂ => uGen θ₂ M n L t₂ b.1) t₂
          = uGen θ₂ M n L t₂ b.1 := by
      intro t₂
      rw [Finset.sum_eq_single (blockQuant n L t₂)]
      · rw [Set.indicator_of_mem (by simp)]
      · intro x₂ _ hx
        rw [Set.indicator_of_notMem (by simpa [eq_comm] using hx)]
      · exact fun h => absurd (Finset.mem_univ _) h
    rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun x₂ _ =>
      (hi₁ _).mul_prod ((hi₂ _).indicator (hm x₂))]
    rw [Finset.sum_congr rfl fun x₂ _ => integral_prod_mul (μ := μ₁L) (ν := μ₂L)
      (fun t₁ => uGen θ₁ N n L t₁ (b.2.1 x₂))
      ((blockQuant n L ⁻¹' {x₂}).indicator (fun t₂ => uGen θ₂ M n L t₂ b.1))]
    simp only [μ₁L, integral_uGen hθ₁ hN, one_mul]
    rw [← integral_finsetSum _ fun x₂ _ => (hi₂ _).indicator (hm x₂), integral_congr_ae
      (ae_of_all _ hsum)]
    exact integral_uGen hθ₂ hM n L b.1
  have key := DMC.integral_sum_mul_log_le_inputMutualInfo W
    (MAC.inputPMF (blockLaw θ₁ n L) (blockLaw θ₂ n L)) hQ hp (fun t b => u₂ t b * u₁ t b)
    (fun t b => mul_pos (hu₂ t b) (hu₁ t b)) hu1
    (fun b => ((hl₂ b).add (hl₁ b)).congr (ae_of_all _ fun t =>
      (Real.log_mul (hu₂ t b).ne' (hu₁ t b).ne').symm))
  rw [← MAC.inputMutualInfo_inputPMF]
  refine le_of_eq_of_le ?_ key
  have hw1 : ∀ x b, ‖(W x b).toReal‖ ≤ 1 := fun x b => by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (W x).coe_le_one b)
  have hwm : ∀ b, Measurable fun t => (W (Q t) b).toReal := fun b =>
    (measurable_of_finite fun x => (W x b).toReal).comp hQ
  have i₂ : Integrable (fun t => ∑ b, (W (Q t) b).toReal * Real.log (u₂ t b)) (μ₁L.prod μ₂L) :=
    integrable_finsetSum _ fun b _ =>
      (hl₂ b).bdd_mul (hwm b).aestronglyMeasurable (ae_of_all _ fun t => hw1 _ b)
  have i₁ : Integrable (fun t => ∑ b, (W (Q t) b).toReal * Real.log (u₁ t b)) (μ₁L.prod μ₂L) :=
    integrable_finsetSum _ fun b _ =>
      (hl₁ b).bdd_mul (hwm b).aestronglyMeasurable (ae_of_all _ fun t => hw1 _ b)
  have hsplit : ∀ t, ∑ b, (W (Q t) b).toReal * Real.log (u₂ t b * u₁ t b)
      = ∑ b, (W (Q t) b).toReal * Real.log (u₂ t b)
        + ∑ b, (W (Q t) b).toReal * Real.log (u₁ t b) := fun t => by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Real.log_mul (hu₂ t b).ne' (hu₁ t b).ne', mul_add]
  rw [integral_congr_ae (ae_of_all _ hsplit), integral_add i₂ i₁]
  congr 1
  · refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [u₂, W, chan]
    rw [sum_blockChannel_toReal_mul N _ (measurable_quant n L P₁ P₂)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [quant, Q]
    rw [log_uGen_blockQuant hθ₂ hM, blockInput_blockQuant, blockInput_blockQuant]
    rfl
  · have hf : ∀ t : (Fin L → ℝ) × (Fin L → ℝ), ∑ b, (W (Q t) b).toReal * Real.log (u₁ t b)
        = ∫ z, ∑ l, Real.log (letterRatio θ₁ N n (t.1 l)
          (level n (clipValue n L P₁ (fun k => level n (t.1 k)) l + z l))) ∂noise N L := by
      intro t
      simp only [u₁, W, chan]
      rw [sum_blockChannel_toReal_mul N _ (measurable_quant n L P₁ P₂)]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [quant, Q]
      rw [show ∀ a b z : Fin L → ℝ, a + b + z - b = a + z from fun a b z => by abel,
        log_uGen_blockQuant hθ₁ hN, blockInput_blockQuant]
      rfl
    rw [integral_congr_ae (ae_of_all _ hf),
      integral_fun_fst (fun t : Fin L → ℝ => ∫ z, ∑ l, Real.log (letterRatio θ₁ N n (t l)
        (level n (clipValue n L P₁ (fun k => level n (t k)) l + z l))) ∂noise N L)]
    simp

end Bounds

private lemma tendsto_badSet {θ : ℝ} (n : ℕ) {P : ℝ}
    (hm : ∫ t, value n (level n t) ^ 2 ∂gaussianReal 0 θ.toNNReal < P) :
    Tendsto (fun L : ℕ => (Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal).real
      (badSet n L P)) atTop (𝓝 0) := by
  have hPm : 0 < P - ∫ t, value n (level n t) ^ 2 ∂gaussianReal 0 θ.toNNReal := sub_pos.2 hm
  have hlim : Tendsto (fun L : ℕ => Var[fun t => value n (level n t) ^ 2; gaussianReal 0 θ.toNNReal]
      / (L * (P - ∫ t, value n (level n t) ^ 2 ∂gaussianReal 0 θ.toNNReal) ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity))
  refine squeeze_zero' (Eventually.of_forall fun L => measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with L hL
  exact measureReal_badSet_le n hL hm

private lemma tendsto_cTerm (n : ℕ) (θ s : ℝ) :
    Tendsto (fun c : ℝ => 4 * n / c * θ / (2 * s)) atTop (𝓝 0) := by
  have h := ((tendsto_const_nhds (x := (4 * n : ℝ))).div_atTop tendsto_id).mul_const θ
    |>.div_const (2 * s)
  simpa using h

private lemma eventually_lt_awgnCapacity {P R N : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (h : R < awgnCapacity P N) : ∀ᶠ τ in 𝓝[<] (1 : ℝ), R < awgnCapacity (τ * P) N := by
  have hcont : ContinuousAt (fun τ => awgnCapacity (τ * P) N) 1 := by
    unfold awgnCapacity
    exact continuousAt_const.mul ((continuousAt_const.add
      ((continuousAt_id.mul continuousAt_const).div_const N)).log
      (ne_of_gt (by have := div_nonneg hP hN.le; norm_num; linarith)))
  exact nhdsWithin_le_nhds (hcont.eventually (lt_mem_nhds (by simpa using h)))

private lemma final_lt {L R C g X Y η I : ℝ} (hL : 0 < L) (hb : L * g - L * X / Y ≤ I)
    (he : X / Y < η) (hg : C - η < g) (hk : 8 * η ≤ C - R) (hη : 0 < η) : L * R < I := by
  have h := mul_lt_mul_of_pos_left he hL
  rw [← mul_div_assoc] at h
  nlinarith [mul_lt_mul_of_pos_left hg hL, mul_le_mul_of_nonneg_left hk hL.le, mul_pos hL hη]

private lemma final_lt₂ {L R C C' g g' X Y X' Y' η I : ℝ} (hL : 0 < L)
    (hb : L * g' - L * X' / Y' + (L * g - L * X / Y) ≤ I) (he' : X' / Y' < η) (he : X / Y < η)
    (hg' : C' - η < g') (hg : C - η < g) (hk : 8 * η ≤ C + C' - R) (hη : 0 < η) :
    L * R < I := by
  have h := mul_lt_mul_of_pos_left he hL
  have h' := mul_lt_mul_of_pos_left he' hL
  rw [← mul_div_assoc] at h h'
  nlinarith [mul_lt_mul_of_pos_left hg hL, mul_lt_mul_of_pos_left hg' hL,
    mul_le_mul_of_nonneg_left hk hL.le, mul_pos hL hη]

private lemma achievable_of_chan {P₁ P₂ N R₁ R₂ θ₁ θ₂ : ℝ} (hP₁ : 0 < P₁) (hP₂ : 0 < P₂)
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) {n L : ℕ} (hL : 0 < L)
    (h₁ : L * R₁ < I[fun ω : Blk n L × Blk n L × Out n L => ω.1 : fun ω => ω.2.2 |
      fun ω => ω.2.1 ; MAC.jointMeasure (chan N n L P₁ P₂) (blockLaw θ₁ n L) (blockLaw θ₂ n L)])
    (h₂ : L * R₂ < I[fun ω : Blk n L × Blk n L × Out n L => ω.2.1 : fun ω => ω.2.2 |
      fun ω => ω.1 ; MAC.jointMeasure (chan N n L P₁ P₂) (blockLaw θ₁ n L) (blockLaw θ₂ n L)])
    (h₃ : L * (R₁ + R₂) < I[fun ω : Blk n L × Blk n L × Out n L => (ω.1, ω.2.1) :
      fun ω => ω.2.2 ; MAC.jointMeasure (chan N n L P₁ P₂) (blockLaw θ₁ n L) (blockLaw θ₂ n L)]) :
    Achievable P₁ P₂ N R₁ R₂ :=
  achievable_of_lt_blockChannel hP₁.le hP₂.le hR₁ hR₂ hL (blockInput n L P₁)
    (blockInput n L P₂) (fun _ => sum_sq_clipValue_le hP₁.le n L _)
    (fun _ => sum_sq_clipValue_le hP₂.le n L _) (quant n L P₁ P₂) (measurable_quant n L P₁ P₂)
    (blockLaw θ₁ n L) (blockLaw θ₂ n L) h₁ h₂ h₃

theorem achievable_of_lt {P₁ P₂ N R₁ R₂ : ℝ} (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) (hN : 0 < N)
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (h₁ : R₁ < awgnCapacity P₁ N) (h₂ : R₂ < awgnCapacity P₂ N)
    (h₃ : R₁ + R₂ < awgnCapacity (P₁ + P₂) N) : Achievable P₁ P₂ N R₁ R₂ := by
  obtain ⟨τ, ⟨hτ₁, hτ₂, hτ₃⟩, hτ0, hτ1⟩ := (((eventually_lt_awgnCapacity hP₁.le hN h₁).and
    ((eventually_lt_awgnCapacity hP₂.le hN h₂).and
      (eventually_lt_awgnCapacity (by positivity) hN h₃))).and
    (Ioo_mem_nhdsLT zero_lt_one)).exists
  have hθ₁ : 0 < τ * P₁ := mul_pos hτ0 hP₁
  have hθ₂ : 0 < τ * P₂ := mul_pos hτ0 hP₂
  have hθP₁ : τ * P₁ < P₁ := by nlinarith
  have hθP₂ : τ * P₂ < P₂ := by nlinarith
  have hadd := GaussianMultiUser.awgnCapacity_add hθ₁.le hθ₂.le hN
  rw [mul_add, ← hadd] at hτ₃
  generalize τ * P₁ = θ₁ at *
  generalize τ * P₂ = θ₂ at *
  have hM : 0 < θ₁ + N := by linarith
  set η := min (min (awgnCapacity θ₁ N - R₁) (awgnCapacity θ₂ N - R₂))
    (awgnCapacity θ₁ N + awgnCapacity θ₂ (θ₁ + N) - (R₁ + R₂)) / 8 with hη
  have hm1 := min_le_left (min (awgnCapacity θ₁ N - R₁) (awgnCapacity θ₂ N - R₂))
    (awgnCapacity θ₁ N + awgnCapacity θ₂ (θ₁ + N) - (R₁ + R₂))
  have hm2 := min_le_right (min (awgnCapacity θ₁ N - R₁) (awgnCapacity θ₂ N - R₂))
    (awgnCapacity θ₁ N + awgnCapacity θ₂ (θ₁ + N) - (R₁ + R₂))
  have hm3 := min_le_left (awgnCapacity θ₁ N - R₁) (awgnCapacity θ₂ N - R₂)
  have hm4 := min_le_right (awgnCapacity θ₁ N - R₁) (awgnCapacity θ₂ N - R₂)
  have hη0 : 0 < η := by
    rw [hη]
    exact div_pos (lt_min (lt_min (by linarith) (by linarith)) (by linarith)) (by norm_num)
  have hT1 := tendsto_integral_sq_value_level θ₁
  have hT2 := tendsto_integral_sq_value_level θ₂
  rw [Real.coe_toNNReal _ hθ₁.le] at hT1
  rw [Real.coe_toNNReal _ hθ₂.le] at hT2
  obtain ⟨n, hn1, hn2, hnT, hq1, hq2⟩ := ((tendsto_letterGain hθ₁ hN).eventually
    (lt_mem_nhds (show awgnCapacity θ₁ N - η < awgnCapacity θ₁ N by linarith))).and
    (((tendsto_letterGain hθ₂ hN).eventually
      (lt_mem_nhds (show awgnCapacity θ₂ N - η < awgnCapacity θ₂ N by linarith))).and
    (((tendsto_tinGain hθ₁ hθ₂ hN).eventually
      (lt_mem_nhds (show awgnCapacity θ₂ (θ₁ + N) - η < awgnCapacity θ₂ (θ₁ + N) by linarith))).and
    ((hT1.eventually (gt_mem_nhds hθP₁)).and (hT2.eventually (gt_mem_nhds hθP₂))))) |>.exists
  obtain ⟨c, hc0, hc1, hc2, hcT⟩ := ((eventually_gt_atTop 0).and
    (((tendsto_cTerm n θ₁ (θ₁ * N / (θ₁ + N))).eventually (gt_mem_nhds hη0)).and
    (((tendsto_cTerm n θ₂ (θ₂ * N / (θ₂ + N))).eventually (gt_mem_nhds hη0)).and
    ((tendsto_cTerm n θ₂ (θ₂ * (θ₁ + N) / (θ₂ + (θ₁ + N)))).eventually
      (gt_mem_nhds hη0))))).exists
  have hβ₁ := tendsto_badSet n hq1
  have hβ₂ := tendsto_badSet n hq2
  have he₁ := ((hβ₁.const_mul (4 * n * c + 4 * n ^ 2)).add_const (4 * n / c * θ₁)).div_const
    (2 * (θ₁ * N / (θ₁ + N)))
  have he₂ := ((hβ₂.const_mul (4 * n * c + 4 * n ^ 2)).add_const (4 * n / c * θ₂)).div_const
    (2 * (θ₂ * N / (θ₂ + N)))
  have heT := (((hβ₁.add hβ₂).const_mul (4 * n * c + 4 * n ^ 2)).add_const
    (4 * n / c * θ₂)).div_const (2 * (θ₂ * (θ₁ + N) / (θ₂ + (θ₁ + N))))
  rw [mul_zero, zero_add] at he₁ he₂
  rw [add_zero, mul_zero, zero_add] at heT
  obtain ⟨L, hL0, hL1, hL2, hLT⟩ := ((eventually_gt_atTop 0).and
    ((he₁.eventually (gt_mem_nhds hc1)).and
      ((he₂.eventually (gt_mem_nhds hc2)).and (heT.eventually (gt_mem_nhds hcT))))).exists
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL0
  have b1 := (integral_blockGain_ge hθ₁ hN n L P₁ hc0).trans
    (integral_le_condMutualInfo₁ (θ₂ := θ₂) hθ₁ hN n L P₁ P₂)
  have b2 := (integral_blockGain_ge hθ₂ hN n L P₂ hc0).trans
    (integral_le_condMutualInfo₂ (θ₁ := θ₁) hθ₂ hN n L P₁ P₂)
  have b3 := (add_le_add (integral_tinGain_ge hθ₁ hθ₂ hN n L P₁ P₂ hc0)
    (integral_blockGain_ge hθ₁ hN n L P₁ hc0)).trans
    (integral_le_mutualInfo hθ₁ hθ₂ hN n L P₁ P₂)
  have k1 : 8 * η ≤ awgnCapacity θ₁ N - R₁ := by linarith
  have k2 : 8 * η ≤ awgnCapacity θ₂ N - R₂ := by linarith
  have k3 : 8 * η ≤ awgnCapacity θ₁ N + awgnCapacity θ₂ (θ₁ + N) - (R₁ + R₂) := by linarith
  exact achievable_of_chan hP₁ hP₂ hR₁ hR₂ hL0 (final_lt hL' b1 hL1 hn1 k1 hη0)
    (final_lt hL' b2 hL2 hn2 k2 hη0) (final_lt₂ hL' b3 hLT hL1 hnT hn1 k3 hη0)

theorem achievable_zero_left {P₁ P₂ N R : ℝ} (hP₁ : 0 ≤ P₁) (h : AWGN.Achievable P₂ N R) :
    Achievable P₁ P₂ N 0 R := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hn₀ n hn
  refine ⟨1, k, by simp, hk, ⟨fun _ => 0, c.enc,
    fun _ => by simpa using mul_nonneg n.cast_nonneg hP₁, c.power,
    fun y => (0, c.dec y), measurable_const.prodMk c.measurable_dec⟩, le_trans (le_of_eq ?_) hc⟩
  simp only [Code.avgError, Code.errorProb, AWGN.Code.avgError, AWGN.Code.errorProb,
    Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  ext z
  simp [Prod.ext_iff, Subsingleton.elim _ (0 : Fin 1)]

theorem achievable_zero_right {P₁ P₂ N R : ℝ} (hP₂ : 0 ≤ P₂) (h : AWGN.Achievable P₁ N R) :
    Achievable P₁ P₂ N R 0 :=
  (achievable_zero_left hP₂ h).swap
private lemma isClosed_macRegion (P₁ P₂ N : ℝ) :
    IsClosed (GaussianMultiUser.macRegion P₁ P₂ N) := by
  simp only [GaussianMultiUser.macRegion, Set.ofPred_and]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_fst continuous_const).inter
        ((isClosed_le continuous_snd continuous_const).inter
          (isClosed_le (continuous_fst.add continuous_snd) continuous_const))))

private lemma awgnCapacity_pos {P N : ℝ} (hP : 0 < P) (hN : 0 < N) : 0 < awgnCapacity P N := by
  unfold awgnCapacity
  have := div_pos hP hN
  exact mul_pos (by norm_num) (Real.log_pos (by linarith))

private lemma dist_max_lt {x η : ℝ} (hx : 0 ≤ x) (hη : 0 < η) : dist x (max (x - η / 2) 0) < η := by
  rw [Real.dist_eq]
  rcases le_total (x - η / 2) 0 with h | h
  · rw [max_eq_right h, sub_zero, abs_of_nonneg hx]
    linarith
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]
    linarith

theorem closure_achievable_eq {P₁ P₂ N : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N) :
    closure {R : ℝ × ℝ | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ Achievable P₁ P₂ N R.1 R.2}
      = GaussianMultiUser.macRegion P₁ P₂ N := by
  refine subset_antisymm (closure_minimal (fun R hR => hR.2.2.mem_macRegion hP₁ hP₂ hN hR.1 hR.2.1)
    (isClosed_macRegion P₁ P₂ N)) ?_
  rintro ⟨R₁, R₂⟩ ⟨h0₁, h0₂, h₁, h₂, h₃⟩
  rcases hP₁.eq_or_lt with rfl | hP₁'
  · have hR₁ : R₁ = 0 := le_antisymm (by simpa [awgnCapacity] using h₁) h0₁
    subst hR₁
    have hm : R₂ ∈ closure {R : ℝ | 0 ≤ R ∧ AWGN.Achievable P₂ N R} := by
      rw [AWGN.closure_achievable_eq hP₂ hN]
      exact ⟨h0₂, h₂⟩
    exact map_mem_closure (f := fun r : ℝ => ((0 : ℝ), r)) (continuous_const.prodMk continuous_id)
      hm fun R hR => ⟨le_rfl, hR.1, achievable_zero_left le_rfl hR.2⟩
  rcases hP₂.eq_or_lt with rfl | hP₂'
  · have hR₂ : R₂ = 0 := le_antisymm (by simpa [awgnCapacity] using h₂) h0₂
    subst hR₂
    have hm : R₁ ∈ closure {R : ℝ | 0 ≤ R ∧ AWGN.Achievable P₁ N R} := by
      rw [AWGN.closure_achievable_eq hP₁ hN]
      exact ⟨h0₁, h₁⟩
    exact map_mem_closure (f := fun r : ℝ => (r, (0 : ℝ))) (continuous_id.prodMk continuous_const)
      hm fun R hR => ⟨hR.1, le_rfl, achievable_zero_right le_rfl hR.2⟩
  have hC₁ := awgnCapacity_pos hP₁' hN
  have hC₂ := awgnCapacity_pos hP₂' hN
  have hC₁₂ := GaussianMultiUser.awgnCapacity_mono hP₁ (le_add_of_nonneg_right hP₂) hN
  have hC₂₁ := GaussianMultiUser.awgnCapacity_mono hP₂ (le_add_of_nonneg_left hP₁) hN
  rw [Metric.mem_closure_iff]
  intro η hη
  refine ⟨(max (R₁ - η / 2) 0, max (R₂ - η / 2) 0), ⟨le_max_right _ _, le_max_right _ _,
    achievable_of_lt hP₁' hP₂' hN (le_max_right _ _) (le_max_right _ _)
      (max_lt (by simp only at h₁; linarith) hC₁)
      (max_lt (by simp only at h₂; linarith) hC₂) ?_⟩, ?_⟩
  · simp only at h₁ h₂ h₃
    rcases le_total (R₁ - η / 2) 0 with h | h <;> rcases le_total (R₂ - η / 2) 0 with h' | h' <;>
      simp only [max_eq_right, max_eq_left, h, h'] <;> linarith
  · rw [Prod.dist_eq, max_lt_iff]
    exact ⟨dist_max_lt h0₁ hη, dist_max_lt h0₂ hη⟩

end GaussianMAC

end Meat
