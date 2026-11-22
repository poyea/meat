import Mathlib.Probability.ProductMeasure
import Meat.Continuous.AWGNConverse
import Meat.Channel.Achievability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Meat

namespace AWGN

variable {A B : Type*} [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

noncomputable def blockChannel (N : ℝ) {L : ℕ} (a : A → Fin L → ℝ) (q : (Fin L → ℝ) → B) :
    DMC A B :=
  fun x => ((noise N L).map fun z => q (a x + z)).toPMF

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

private noncomputable def toCode {P : ℝ} (hP : 0 ≤ P) {n m L r k : ℕ} (h : m * L + r = n)
    (a : A → Fin L → ℝ) (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P) (q : (Fin L → ℝ) → B)
    (hq : Measurable q) (c : BlockCode (Fin k) A B m) : Code P n k where
  enc i := embed h fun t => a (c.enc i t)
  power i := by
    rw [sum_sq_embed]
    calc ∑ t, ∑ l, a (c.enc i t) l ^ 2 ≤ ∑ _t : Fin m, (L * P) :=
          Finset.sum_le_sum fun t _ => ha _
      _ = m * L * P := by simp [mul_assoc]
      _ ≤ n * P := mul_le_mul_of_nonneg_right (by exact_mod_cast h ▸ Nat.le_add_right _ _) hP
  dec y := c.dec fun t => q (blocks h y t)
  measurable_dec := (measurable_of_finite c.dec).comp
    (measurable_pi_iff.2 fun t => hq.comp ((measurable_pi_apply t).comp (measurable_blocks h)))

private lemma errorProb_toCode {P N : ℝ} (hP : 0 ≤ P) {n m L r k : ℕ} (h : m * L + r = n)
    (a : A → Fin L → ℝ) (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P) (q : (Fin L → ℝ) → B)
    (hq : Measurable q) (c : BlockCode (Fin k) A B m) (i : Fin k) :
    (toCode hP h a ha q hq c).errorProb N i = c.errorProb (blockChannel N a q) i := by
  classical
  set G : (Fin m → Fin L → ℝ) → Fin m → B := fun w t => q (a (c.enc i t) + w t)
  have hG : Measurable G :=
    measurable_pi_iff.2 fun t => hq.comp ((measurable_const_add _).comp (measurable_pi_apply t))
  set T : Set (Fin m → B) := ↑(Finset.univ.filter fun v => c.dec v ≠ i)
  have hset : {z | (toCode hP h a ha q hq c).dec ((toCode hP h a ha q hq c).enc i + z) ≠ i}
      = blocks h ⁻¹' (G ⁻¹' T) := by
    ext z
    simp [toCode, T, G, blocks_add, blocks_embed]
  have hT : MeasurableSet T := Finset.measurableSet _
  rw [Code.errorProb, hset, ← Measure.map_apply (measurable_blocks h) (hG hT),
    map_noise_blocks, ← Measure.map_apply hG hT,
    Measure.pi_map_pi (f := fun t u => q (a (c.enc i t) + u)) fun t =>
      (hq.comp (measurable_const_add _)).aemeasurable, ← sum_measure_singleton,
    BlockCode.errorProb, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : c.dec v = i
  · simp [hv]
  · rw [ite_eq_left hv, ite_eq_right hv, ← Set.univ_pi_singleton, Measure.pi_pi, DMC.blockProb]
    rfl

private lemma avgError_toCode {P N : ℝ} (hP : 0 ≤ P) {n m L r k : ℕ} (h : m * L + r = n)
    (a : A → Fin L → ℝ) (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P) (q : (Fin L → ℝ) → B)
    (hq : Measurable q) (c : BlockCode (Fin k) A B m) :
    (toCode hP h a ha q hq c).avgError N = c.avgError (blockChannel N a q) := by
  simp only [Code.avgError, BlockCode.avgError, errorProb_toCode, Fintype.card_fin]

theorem achievable_of_lt_inputMutualInfo_blockChannel [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] {P N R : ℝ} (hP : 0 ≤ P) (hR : 0 ≤ R) {L : ℕ} (hL : 0 < L)
    (a : A → Fin L → ℝ) (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P) (q : (Fin L → ℝ) → B)
    (hq : Measurable q) (p : PMF A) (h : L * R < (blockChannel N a q).inputMutualInfo p) :
    Achievable P N R := by
  set I := (blockChannel N a q).inputMutualInfo p
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  set R₁ := (R + I / L) / 2
  have hRI : R < I / L := by rw [lt_div_iff₀ hL']; linarith
  have hR₁ : R < R₁ := by simp only [R₁]; linarith
  have hW : (blockChannel N a q).Achievable (L * R₁) :=
    DMC.achievable_of_lt_inputMutualInfo _ p (by
      have : L * R₁ < L * (I / L) := mul_lt_mul_of_pos_left (by simp only [R₁]; linarith) hL'
      rwa [mul_div_cancel₀ _ hL'.ne'] at this)
  intro ε hε
  obtain ⟨n₁, hn₁⟩ := hW ε hε
  obtain ⟨m₁, hm₁⟩ := exists_nat_gt (R / (R₁ - R))
  refine ⟨L * max n₁ m₁, fun n hn => ?_⟩
  have h : n / L * L + n % L = n := by rw [mul_comm]; exact Nat.div_add_mod n L
  have hm : max n₁ m₁ ≤ n / L := (Nat.le_div_iff_mul_le hL).2 (by rw [mul_comm]; exact hn)
  obtain ⟨k, hk, c, hc⟩ := hn₁ (n / L) (le_of_max_le_left hm)
  refine ⟨k, ?_, toCode hP h a ha q hq c, by rw [avgError_toCode]; exact hc⟩
  have hr : ((n % L : ℕ) : ℝ) ≤ L := by exact_mod_cast (Nat.mod_lt n hL).le
  have hn' : (n : ℝ) = (n / L : ℕ) * L + (n % L : ℕ) := by exact_mod_cast h.symm
  have hmR : R ≤ (n / L : ℕ) * (R₁ - R) := by
    have := (div_lt_iff₀ (sub_pos.2 hR₁)).1
      (hm₁.trans_le (Nat.cast_le.2 (le_of_max_le_right hm)))
    linarith
  refine le_trans (Real.exp_le_exp.2 ?_) hk
  rw [hn']
  nlinarith [mul_le_mul_of_nonneg_right hr hR, mul_le_mul_of_nonneg_left hmR hL'.le]

theorem closure_achievable_eq_of_quantization {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (hquant : ∀ R, 0 ≤ R → R < awgnCapacity P N →
      ∃ (L s t : ℕ) (a : Fin s → Fin L → ℝ) (q : (Fin L → ℝ) → Fin t) (p : PMF (Fin s)),
        0 < L ∧ (∀ x, ∑ l, a x l ^ 2 ≤ L * P) ∧ Measurable q ∧
          L * R < (blockChannel N a q).inputMutualInfo p) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable P N R} = Set.Icc 0 (awgnCapacity P N) := by
  refine closure_achievable_eq_of hP hN (fun R hR hRC => ?_)
    fun R hR => le_awgnCapacity_of_achievable hP hN hR
  obtain ⟨L, s, t, a, q, p, hL, ha, hq, hI⟩ := hquant R hR hRC
  exact achievable_of_lt_inputMutualInfo_blockChannel hP hR hL a ha q hq p hI

end AWGN

end Meat
