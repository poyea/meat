import Meat.Continuous.GaussianBroadcast
import Meat.Continuous.GaussianMultiUser
import Meat.Continuous.GaussianBroadcastQuantization
import Meat.Channel.BroadcastAchievability
import Meat.Channel.MultipleAccessConverse

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Meat

namespace GaussianBroadcast

open AWGN GaussianMAC

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

variable {B₁ B₂ : Type*} [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

noncomputable def blockChannel₂ (N₁ N₂ : ℝ) {L : ℕ} (a : A → Fin L → ℝ)
    (q₁ : (Fin L → ℝ) → B₁) (q₂ : (Fin L → ℝ) → B₂) : DMC A (B₁ × B₂) :=
  fun x => (blockChannel N₁ a q₁ x).bind fun b₁ => (blockChannel N₂ a q₂ x).map fun b₂ => (b₁, b₂)

theorem map_fst_blockChannel₂ (N₁ N₂ : ℝ) {L : ℕ} (a : A → Fin L → ℝ)
    (q₁ : (Fin L → ℝ) → B₁) (q₂ : (Fin L → ℝ) → B₂) (x : A) :
    (blockChannel₂ N₁ N₂ a q₁ q₂ x).map Prod.fst = blockChannel N₁ a q₁ x := by
  simp only [blockChannel₂, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hc : ∀ b : B₁, PMF.map (fun _ : B₂ => b) (blockChannel N₂ a q₂ x) = PMF.pure b :=
    fun b => PMF.map_const _ b
  simp only [hc, PMF.bind_pure]

theorem map_snd_blockChannel₂ (N₁ N₂ : ℝ) {L : ℕ} (a : A → Fin L → ℝ)
    (q₁ : (Fin L → ℝ) → B₁) (q₂ : (Fin L → ℝ) → B₂) (x : A) :
    (blockChannel₂ N₁ N₂ a q₁ q₂ x).map Prod.snd = blockChannel N₂ a q₂ x := by
  simp only [blockChannel₂, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
  exact PMF.map_id _

omit [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂] in
private lemma marginal_le {M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂] {m : ℕ}
    (W : DMC A (B₁ × B₂)) (W' : DMC A B₁) (hW : ∀ x, (W x).map Prod.fst = W' x)
    (c : BCCode M₁ M₂ A B₁ B₂ m) (i : M₁ × M₂) :
    (BlockCode.errorProb ⟨c.enc, fun y => (c.dec₁ y, i.2)⟩ W' i) ≤ c.errorProb W i := by
  classical
  have hW' : W' = fun x => (W x).map Prod.fst := funext fun x => (hW x).symm
  set F : (Fin m → B₁) → ℝ := fun y₁ => if c.dec₁ y₁ = i.1 then 0 else 1
  have e1 : (BlockCode.errorProb ⟨c.enc, fun y => (c.dec₁ y, i.2)⟩ W' i).toReal
      = ∑ y₁, (DMC.blockProb W' (c.enc i) y₁).toReal * F y₁ := by
    rw [BlockCode.errorProb, ENNReal.toReal_sum fun y _ => by
      split_ifs <;> simp [DMC.blockProb_ne_top]]
    refine Finset.sum_congr rfl fun y₁ _ => ?_
    by_cases h : c.dec₁ y₁ = i.1
    · simp [F, h]
    · have h' : (c.dec₁ y₁, i.2) ≠ i := fun h' => h (congrArg Prod.fst h')
      simp [F, h, h']
  have e2 := DMC.sum_blockProb_mul_comp W Prod.fst (c.enc i) F
  have e3 : ∑ y, (DMC.blockProb W (c.enc i) y).toReal * F (fun t => (y t).1)
      ≤ (c.errorProb W i).toReal := by
    rw [BCCode.errorProb, ENNReal.toReal_sum fun y _ => by
      split_ifs <;> simp [DMC.blockProb_ne_top]]
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases h : c.dec₁ (fun t => (y t).1) = i.1
    · simp only [F, h, ite_true, mul_zero]
      positivity
    · have h' : (c.dec₁ (fun t => (y t).1), c.dec₂ (fun t => (y t).2)) ≠ i :=
        fun h' => h (congrArg Prod.fst h')
      simp [F, h, h']
  refine (ENNReal.toReal_le_toReal (BlockCode.errorProb_ne_top _ _ _)
    (BCCode.errorProb_ne_top _ _ _)).1 ?_
  rw [e1, hW', ← e2]
  exact e3

omit [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂] in
private lemma marginal_le₂ {M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂] {m : ℕ}
    (W : DMC A (B₁ × B₂)) (W' : DMC A B₂) (hW : ∀ x, (W x).map Prod.snd = W' x)
    (c : BCCode M₁ M₂ A B₁ B₂ m) (i : M₁ × M₂) :
    (BlockCode.errorProb ⟨c.enc, fun y => (i.1, c.dec₂ y)⟩ W' i) ≤ c.errorProb W i := by
  classical
  have hW' : W' = fun x => (W x).map Prod.snd := funext fun x => (hW x).symm
  set F : (Fin m → B₂) → ℝ := fun y₂ => if c.dec₂ y₂ = i.2 then 0 else 1
  have e1 : (BlockCode.errorProb ⟨c.enc, fun y => (i.1, c.dec₂ y)⟩ W' i).toReal
      = ∑ y₂, (DMC.blockProb W' (c.enc i) y₂).toReal * F y₂ := by
    rw [BlockCode.errorProb, ENNReal.toReal_sum fun y _ => by
      split_ifs <;> simp [DMC.blockProb_ne_top]]
    refine Finset.sum_congr rfl fun y₂ _ => ?_
    by_cases h : c.dec₂ y₂ = i.2
    · simp [F, h]
    · have h' : (i.1, c.dec₂ y₂) ≠ i := fun h' => h (congrArg Prod.snd h')
      simp [F, h, h']
  have e2 := DMC.sum_blockProb_mul_comp W Prod.snd (c.enc i) F
  have e3 : ∑ y, (DMC.blockProb W (c.enc i) y).toReal * F (fun t => (y t).2)
      ≤ (c.errorProb W i).toReal := by
    rw [BCCode.errorProb, ENNReal.toReal_sum fun y _ => by
      split_ifs <;> simp [DMC.blockProb_ne_top]]
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases h : c.dec₂ (fun t => (y t).2) = i.2
    · simp only [F, h, ite_true, mul_zero]
      positivity
    · have h' : (c.dec₁ (fun t => (y t).1), c.dec₂ (fun t => (y t).2)) ≠ i :=
        fun h' => h (congrArg Prod.snd h')
      simp [F, h, h']
  refine (ENNReal.toReal_le_toReal (BlockCode.errorProb_ne_top _ _ _)
    (BCCode.errorProb_ne_top _ _ _)).1 ?_
  rw [e1, hW', ← e2]
  exact e3

private noncomputable def toCode {P : ℝ} (hP : 0 ≤ P) {n m L r k₁ k₂ : ℕ}
    (h : m * L + r = n) (a : A → Fin L → ℝ) (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P)
    (q₁ : (Fin L → ℝ) → B₁) (q₂ : (Fin L → ℝ) → B₂) (hq₁ : Measurable q₁)
    (hq₂ : Measurable q₂) (c : BCCode (Fin k₁) (Fin k₂) A B₁ B₂ m) : Code P n k₁ k₂ where
  enc i := embed h fun t => a (c.enc i t)
  power _ := sum_sq_embed_le hP h a ha _
  dec₁ y := c.dec₁ fun t => q₁ (blocks h y t)
  dec₂ y := c.dec₂ fun t => q₂ (blocks h y t)
  measurable_dec₁ := (measurable_of_finite c.dec₁).comp
    (measurable_pi_iff.2 fun t => hq₁.comp ((measurable_pi_apply t).comp (measurable_blocks h)))
  measurable_dec₂ := (measurable_of_finite c.dec₂).comp
    (measurable_pi_iff.2 fun t => hq₂.comp ((measurable_pi_apply t).comp (measurable_blocks h)))

private lemma avgError_toCode_le {P : ℝ} (hP : 0 ≤ P) (N₁ N₂ : ℝ) {n m L r k₁ k₂ : ℕ}
    (h : m * L + r = n) (a : A → Fin L → ℝ) (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P)
    (q₁ : (Fin L → ℝ) → B₁) (q₂ : (Fin L → ℝ) → B₂) (hq₁ : Measurable q₁)
    (hq₂ : Measurable q₂) (c : BCCode (Fin k₁) (Fin k₂) A B₁ B₂ m) :
    (toCode hP h a ha q₁ q₂ hq₁ hq₂ c).avgError N₁ N₂
      ≤ 2 * c.avgError (blockChannel₂ N₁ N₂ a q₁ q₂) := by
  have he : ∀ i, (toCode hP h a ha q₁ q₂ hq₁ hq₂ c).errorProb N₁ N₂ i
      ≤ 2 * c.errorProb (blockChannel₂ N₁ N₂ a q₁ q₂) i := by
    intro i
    refine (Code.errorProb_le _ _ _ _).trans ?_
    rw [two_mul]
    refine add_le_add ?_ ?_
    · have e := noise_blockError N₁ h a q₁ hq₁ ⟨c.enc, fun y => (c.dec₁ y, i.2)⟩ i
      refine le_of_eq_of_le ?_ (e.trans_le (marginal_le _ _ (map_fst_blockChannel₂ N₁ N₂ a q₁ q₂)
        c i))
      congr 1
      ext z
      simp only [Set.mem_ofPred_eq, ne_eq, Prod.ext_iff, not_and_or, not_true_eq_false, or_false]
      rfl
    · have e := noise_blockError N₂ h a q₂ hq₂ ⟨c.enc, fun y => (i.1, c.dec₂ y)⟩ i
      refine le_of_eq_of_le ?_ (e.trans_le (marginal_le₂ _ _ (map_snd_blockChannel₂ N₁ N₂ a q₁ q₂)
        c i))
      congr 1
      ext z
      simp only [Set.mem_ofPred_eq, ne_eq, Prod.ext_iff, not_and_or, not_true_eq_false, false_or]
      rfl
  simp only [Code.avgError, BCCode.avgError, Fintype.card_fin]
  rw [mul_div_assoc', Finset.mul_sum]
  exact ENNReal.div_le_div_right (Finset.sum_le_sum fun i _ => he i) _

private lemma rate_le {n m L r : ℕ} (hn : (n : ℝ) = m * L + r) (hr : (r : ℝ) ≤ L) {R δ : ℝ}
    (hR : 0 ≤ R) (hm : R ≤ m * δ) : n * R ≤ m * (L * (R + δ)) := by
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  rw [hn]
  nlinarith [mul_le_mul_of_nonneg_right hr hR, mul_le_mul_of_nonneg_left hm hL]

theorem achievable_of_lt_blockChannel {V : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    {P N₁ N₂ R₁ R₂ : ℝ} (hP : 0 ≤ P) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) {L : ℕ} (hL : 0 < L)
    (a : A → Fin L → ℝ) (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P) (q₁ : (Fin L → ℝ) → B₁)
    (q₂ : (Fin L → ℝ) → B₂) (hq₁ : Measurable q₁) (hq₂ : Measurable q₂) (pU : PMF V)
    (pX : V → PMF A)
    (h₁ : L * R₁ < condMutualInfo (fun ω : V × A × B₁ × B₂ => ω.2.1) (fun ω => ω.2.2.1)
      (fun ω => ω.1) (BC.jointMeasure (blockChannel₂ N₁ N₂ a q₁ q₂) pU pX))
    (h₂ : L * R₂ < mutualInfo (fun ω : V × A × B₁ × B₂ => ω.1) (fun ω => ω.2.2.2)
      (BC.jointMeasure (blockChannel₂ N₁ N₂ a q₁ q₂) pU pX))
    (h₃ : L * (R₁ + R₂) < mutualInfo (fun ω : V × A × B₁ × B₂ => ω.2.1) (fun ω => ω.2.2.1)
      (BC.jointMeasure (blockChannel₂ N₁ N₂ a q₁ q₂) pU pX)) :
    Achievable P N₁ N₂ R₁ R₂ := by
  set W := blockChannel₂ N₁ N₂ a q₁ q₂
  set I₁ := condMutualInfo (fun ω : V × A × B₁ × B₂ => ω.2.1) (fun ω => ω.2.2.1)
    (fun ω => ω.1) (BC.jointMeasure W pU pX)
  set I₂ := mutualInfo (fun ω : V × A × B₁ × B₂ => ω.1) (fun ω => ω.2.2.2)
    (BC.jointMeasure W pU pX)
  set I₃ := mutualInfo (fun ω : V × A × B₁ × B₂ => ω.2.1) (fun ω => ω.2.2.1)
    (BC.jointMeasure W pU pX)
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
  have hW := BC.achievable_of_lt W pU pX (R₁ := L * (R₁ + δ)) (R₂ := L * (R₂ + δ))
    (by nlinarith) (by nlinarith) (by nlinarith)
  rw [max_eq_left (by positivity), max_eq_left (by positivity)] at hW
  intro ε hε
  obtain ⟨n₁, hn₁⟩ := hW (ε / 2) (ENNReal.half_pos hε.ne')
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
    toCode hP h a ha q₁ q₂ hq₁ hq₂ c, ?_⟩
  refine (avgError_toCode_le hP N₁ N₂ h a ha q₁ q₂ hq₁ hq₂ c).trans ?_
  calc 2 * c.avgError W ≤ 2 * (ε / 2) := by gcongr
    _ = ε := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top

end Reduction

section Information

variable {V U Y : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

private lemma condMutualInfo_pair_left {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → V) (Z : Ω → U) (W : Ω → Y) :
    I[fun ω => (X ω, Z ω) : W | Z ; μ] = I[X : W | Z ; μ] := by
  have h1 : H[fun ω => ((X ω, Z ω), Z ω) ; μ] = H[fun ω => (X ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Z ω)) (f := fun p => ((p.1, p.2), p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.1 h.1.2
  have h2 : H[fun ω => (((X ω, Z ω), W ω), Z ω) ; μ] = H[fun ω => ((X ω, W ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, W ω), Z ω))
      (f := fun p => (((p.1.1, p.2), p.1.2), p.2)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1.1 h.1.2) h.2
  simp only [condMutualInfo_def, condEntropy_def]
  rw [h1, h2]

private lemma condMutualInfo_eq₁ (W : DMC (V × U) Y) (p₁ : PMF V) (p₂ : PMF U) :
    I[fun ω : V × U × Y => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ; MAC.jointMeasure W p₁ p₂] =
      (MAC.sideChannel₁ W p₂).inputMutualInfo p₁ := by
  have h := mutualInfo_pair_eq_add_condMutualInfo (MAC.jointMeasure W p₁ p₂)
    (X := fun ω : V × U × Y => ω.1) (Y := fun ω => ω.2.2) (Z := fun ω => ω.2.1)
  have hs := mutualInfo_comp_right_of_injective (MAC.jointMeasure W p₁ p₂)
    (X := fun ω : V × U × Y => ω.1) (Y := fun ω => ω.2) Prod.swap_injective
  have h0 := MAC.mutualInfo_inputs_eq_zero W p₁ p₂
  rw [MAC.inputMutualInfo_sideChannel₁, ← hs]
  change _ = I[fun ω : V × U × Y => ω.1 : fun ω => (ω.2.2, ω.2.1) ; MAC.jointMeasure W p₁ p₂]
  linarith

private lemma jointPMF_map_snd' {A' B' C : Type*} (K : A' → PMF C) (p : PMF (B' × A')) :
    (DMC.jointPMF (fun ua : B' × A' => K ua.2) p).map (fun ω => (ω.1.2, ω.2))
      = DMC.jointPMF K (p.map Prod.snd) := by
  simp only [DMC.jointPMF, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]

private lemma bind_swap {V' U' : Type*} (pV : PMF V') (pU : PMF U') :
    pU.bind (fun u => pV.map fun v => (v, u)) = MAC.inputPMF pV pU := by
  simp only [MAC.inputPMF, DMC.jointPMF, ← PMF.bind_pure_comp, Function.comp_def]
  exact PMF.bind_comm _ _ _

end Information

private lemma law₁_eq {V U B₁ B₂ : Type*} (W : DMC (V × U) (B₁ × B₂)) (pV : PMF V)
    (pU : PMF U) :
    BC.law₁ W pU (fun u => pV.map fun v => (v, u)) =
      (MAC.jointPMF (BC.channel₁ W) pV pU).map fun ω => ((ω.2.1, (ω.1, ω.2.1)), ω.2.2) := by
  simp only [BC.law₁, DMC.jointPMF, MAC.jointPMF, PMF.map_bind, PMF.bind_map, PMF.bind_bind,
    Function.comp_def, PMF.map_comp]
  rw [PMF.bind_comm]

section Quantized

private abbrev Blk (n L : ℕ) : Type := Fin (Fintype.card (Fin L → Level n))

private noncomputable def val (n L : ℕ) (b : Blk n L) : Fin L → ℝ :=
  fun l => value n ((Fintype.equivFin (Fin L → Level n)).symm b l)

private lemma val_blockQuant (n L : ℕ) (t : Fin L → ℝ) :
    val n L (blockQuant n L t) = fun l => value n (level n (t l)) := by
  funext l
  simp only [val, blockQuant, Equiv.symm_apply_apply]

private noncomputable def sig (n L : ℕ) (P : ℝ) (x : Blk n L × Blk n L) : Fin L → ℝ :=
  sumClip L P (val n L x.1 + val n L x.2)

private lemma sig_blockQuant (n L : ℕ) (P : ℝ) (t : (Fin L → ℝ) × (Fin L → ℝ)) :
    sig n L P (blockQuant n L t.1, blockQuant n L t.2) = sumSignal n L P t := by
  simp only [sig, val_blockQuant, sumSignal]
  rfl

private noncomputable def quant₁ (n L : ℕ) (y : Fin L → ℝ) : Blk n L × (Blk n L → Blk n L) :=
  (blockQuant n L y, fun u => blockQuant n L (y - val n L u))

private lemma measurable_quant₁ (n L : ℕ) : Measurable (quant₁ n L) :=
  (measurable_blockQuant n L).prodMk
    (measurable_pi_iff.2 fun _ => (measurable_blockQuant n L).comp (measurable_sub_const _))

private noncomputable def chan (N₁ N₂ : ℝ) (n L : ℕ) (P : ℝ) :
    DMC (Blk n L × Blk n L) ((Blk n L × (Blk n L → Blk n L)) × Blk n L) :=
  blockChannel₂ N₁ N₂ (sig n L P) (quant₁ n L) (blockQuant n L)

private noncomputable def satLaw (θ : ℝ) (n L : ℕ) (u : Blk n L) : PMF (Blk n L × Blk n L) :=
  (blockLaw θ n L).map fun v => (v, u)

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
    ).integrable_comp_of_integrable (integrable_sq_gaussianReal _)

private lemma blockLaw_toReal (θ : ℝ) (n L : ℕ) (x : Blk n L) :
    (blockLaw θ n L x).toReal
      = (Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal).real (blockQuant n L ⁻¹' {x}) := by
  rw [blockLaw, Measure.toPMF_apply,
    Measure.map_apply (measurable_blockQuant n L) (measurableSet_singleton _), measureReal_def]

private lemma log_uGen_blockQuant (hθ : 0 < θ) (hN : 0 < N) (n L : ℕ) (t y : Fin L → ℝ) :
    Real.log (uGen θ N n L t (blockQuant n L y))
      = ∑ l, Real.log (letterRatio θ N n (t l) (level n (y l))) := by
  simp [log_uGen hθ hN, blockQuant]

private lemma norm_toReal_le_one {α β : Type*} (p : α → PMF β) (x : α) (b : β) :
    ‖(p x b).toReal‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (p x).coe_le_one b)

end Quantized

section Bounds

variable {θ₁ θ₂ N₁ N₂ : ℝ}

private lemma channel₁_chan (N₁ N₂ : ℝ) (n L : ℕ) (P : ℝ) :
    BC.channel₁ (chan N₁ N₂ n L P) = blockChannel N₁ (sig n L P) (quant₁ n L) :=
  funext fun x => map_fst_blockChannel₂ N₁ N₂ _ _ _ x

private lemma channel₂_chan (N₁ N₂ : ℝ) (n L : ℕ) (P : ℝ) :
    BC.channel₂ (chan N₁ N₂ n L P) = blockChannel N₂ (sig n L P) (blockQuant n L) :=
  funext fun x => map_snd_blockChannel₂ N₁ N₂ _ _ _ x

private lemma integral_le_condMutualInfo (hθ₁ : 0 < θ₁) (hN₁ : 0 < N₁) (n L : ℕ) (P : ℝ) :
    ∫ t, ∫ z, ∑ l, Real.log (letterRatio θ₁ N₁ n (t.1 l)
        (level n (sumSignal n L P t l - value n (level n (t.2 l)) + z l))) ∂noise N₁ L
      ∂((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
        (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal))
      ≤ condMutualInfo (fun ω : Blk n L × (Blk n L × Blk n L) ×
          (Blk n L × (Blk n L → Blk n L)) × Blk n L => ω.2.1) (fun ω => ω.2.2.1) (fun ω => ω.1)
        (BC.jointMeasure (chan N₁ N₂ n L P) (blockLaw θ₂ n L) (satLaw θ₁ n L)) := by
  set μ₁L := Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal
  set μ₂L := Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal
  set K := BC.channel₁ (chan N₁ N₂ n L P)
  rw [BC.condMutualInfo_eq_law₁]
  unfold satLaw
  rw [law₁_eq, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _)
      (X := fun ω : (Blk n L × (Blk n L × Blk n L)) × (Blk n L × (Blk n L → Blk n L)) => ω.1.2)
      (Y := fun ω => ω.2) (Z := fun ω => ω.1.1) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
  change _ ≤ I[fun ω : Blk n L × Blk n L × (Blk n L × (Blk n L → Blk n L)) => (ω.1, ω.2.1) :
    fun ω => ω.2.2 | fun ω => ω.2.1 ; MAC.jointMeasure K (blockLaw θ₁ n L) (blockLaw θ₂ n L)]
  rw [condMutualInfo_pair_left, condMutualInfo_eq₁]
  set Φ : (Fin L → ℝ) → Blk n L → ℝ := fun t u =>
    ∑ y : Blk n L × (Blk n L → Blk n L), (K (blockQuant n L t, u) y).toReal
      * Real.log (uGen θ₁ N₁ n L t (y.2 u))
  have hΦ : ∀ t : (Fin L → ℝ) × (Fin L → ℝ), Φ t.1 (blockQuant n L t.2)
      = ∫ z, ∑ l, Real.log (letterRatio θ₁ N₁ n (t.1 l)
        (level n (sumSignal n L P t l - value n (level n (t.2 l)) + z l))) ∂noise N₁ L := by
    intro t
    simp only [Φ, K, channel₁_chan]
    rw [sum_blockChannel_toReal_mul N₁ _ (measurable_quant₁ n L)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [quant₁]
    rw [log_uGen_blockQuant hθ₁ hN₁, sig_blockQuant, val_blockQuant]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.sub_apply, Pi.add_apply]
    ring_nf
  have hH : Integrable (fun t : (Fin L → ℝ) × (Fin L → ℝ) => Φ t.1 (blockQuant n L t.2))
      (μ₁L.prod μ₂L) :=
    integrable_finsetSum _ fun y _ =>
      (integrable_log_uGen hθ₁ hN₁ n L measurable_fst
        ((measurable_of_finite y.2).comp ((measurable_blockQuant n L).comp measurable_snd))
        fun l => (integrable_sq_eval θ₁ l).comp_fst μ₂L).bdd_mul
      ((measurable_of_finite fun x => (K x y).toReal).comp
        (((measurable_blockQuant n L).comp measurable_fst).prodMk
          ((measurable_blockQuant n L).comp measurable_snd))).aestronglyMeasurable
      (ae_of_all _ fun t => norm_toReal_le_one K _ y)
  calc _ = ∫ t, Φ t.1 (blockQuant n L t.2) ∂(μ₁L.prod μ₂L) :=
        integral_congr_ae (ae_of_all _ fun t => (hΦ t).symm)
    _ = ∫ t₁, ∫ t₂, Φ t₁ (blockQuant n L t₂) ∂μ₂L ∂μ₁L := integral_prod _ hH
    _ = ∫ t₁, ∑ b : Blk n L × (Blk n L × (Blk n L → Blk n L)),
          (MAC.sideChannel₁ K (blockLaw θ₂ n L) (blockQuant n L t₁) b).toReal
            * Real.log (uGen θ₁ N₁ n L t₁ (b.2.2 b.1)) ∂μ₁L := by
        refine integral_congr_ae (ae_of_all _ fun t₁ => ?_)
        dsimp only
        rw [DMC.integral_comp_eq_sum (measurable_blockQuant n L) (fun u => Φ t₁ u),
          Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [Φ, MAC.sideChannel₁, DMC.jointPMF_apply, ENNReal.toReal_mul, mul_assoc,
          ← Finset.mul_sum]
        rw [blockLaw_toReal]
    _ ≤ _ := DMC.integral_sum_mul_log_le_inputMutualInfo
        (MAC.sideChannel₁ K (blockLaw θ₂ n L)) (blockLaw θ₁ n L)
        (measurable_blockQuant n L) (blockLaw_toReal θ₁ n L)
        (fun t (b : Blk n L × (Blk n L × (Blk n L → Blk n L))) => uGen θ₁ N₁ n L t (b.2.2 b.1))
        (fun t (b : Blk n L × (Blk n L × (Blk n L → Blk n L))) =>
          uGen_pos hθ₁ hN₁ n L t (b.2.2 b.1))
        (fun (b : Blk n L × (Blk n L × (Blk n L → Blk n L))) =>
          integral_uGen hθ₁ hN₁ n L (b.2.2 b.1))
        (fun b => integrable_log_uGen hθ₁ hN₁ n L measurable_id measurable_const
          (integrable_sq_eval θ₁))

private lemma integral_le_mutualInfo_cloud (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hN₂ : 0 < N₂)
    (n L : ℕ) (P : ℝ) :
    ∫ t, ∫ z, ∑ l, Real.log (letterRatio θ₂ (θ₁ + N₂) n (t.2 l)
        (level n (sumSignal n L P t l + z l))) ∂noise N₂ L
      ∂((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
        (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal))
      ≤ mutualInfo (fun ω : Blk n L × (Blk n L × Blk n L) ×
          (Blk n L × (Blk n L → Blk n L)) × Blk n L => ω.1) (fun ω => ω.2.2.2)
        (BC.jointMeasure (chan N₁ N₂ n L P) (blockLaw θ₂ n L) (satLaw θ₁ n L)) := by
  have hM : 0 < θ₁ + N₂ := by linarith
  set M := θ₁ + N₂
  set μ₁L := Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal
  set μ₂L := Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal
  set K := BC.channel₂ (chan N₁ N₂ n L P)
  rw [BC.mutualInfo_cloud_eq]
  set Ψ : Blk n L → (Fin L → ℝ) → ℝ := fun v t =>
    ∑ y : Blk n L, (K (v, blockQuant n L t) y).toReal * Real.log (uGen θ₂ M n L t y)
  have hΨ : ∀ t : (Fin L → ℝ) × (Fin L → ℝ), Ψ (blockQuant n L t.1) t.2
      = ∫ z, ∑ l, Real.log (letterRatio θ₂ M n (t.2 l)
        (level n (sumSignal n L P t l + z l))) ∂noise N₂ L := by
    intro t
    simp only [Ψ, K, channel₂_chan]
    rw [sum_blockChannel_toReal_mul N₂ _ (measurable_blockQuant n L)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [log_uGen_blockQuant hθ₂ hM, sig_blockQuant]
    rfl
  have hH : Integrable (fun t : (Fin L → ℝ) × (Fin L → ℝ) => Ψ (blockQuant n L t.1) t.2)
      (μ₁L.prod μ₂L) :=
    integrable_finsetSum _ fun y _ =>
      (integrable_log_uGen hθ₂ hM n L measurable_snd measurable_const
        fun l => (integrable_sq_eval θ₂ l).comp_snd μ₁L).bdd_mul
      ((measurable_of_finite fun x => (K x y).toReal).comp
        (((measurable_blockQuant n L).comp measurable_fst).prodMk
          ((measurable_blockQuant n L).comp measurable_snd))).aestronglyMeasurable
      (ae_of_all _ fun t => norm_toReal_le_one K _ y)
  have hcl : ∀ u (b : Blk n L), (BC.cloudChannel₂ (chan N₁ N₂ n L P) (satLaw θ₁ n L) u b).toReal
      = ∑ v, (blockLaw θ₁ n L v).toReal * (K (v, u) b).toReal := by
    intro u b
    simp only [BC.cloudChannel₂, satLaw, PMF.bind_map, Function.comp_def]
    rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum fun _ _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    simp only [ENNReal.toReal_mul]
    rfl
  calc _ = ∫ t, Ψ (blockQuant n L t.1) t.2 ∂(μ₁L.prod μ₂L) :=
        integral_congr_ae (ae_of_all _ fun t => (hΨ t).symm)
    _ = ∫ t₂, ∫ t₁, Ψ (blockQuant n L t₁) t₂ ∂μ₁L ∂μ₂L := integral_prod_symm _ hH
    _ = ∫ t₂, ∑ b : Blk n L,
          (BC.cloudChannel₂ (chan N₁ N₂ n L P) (satLaw θ₁ n L) (blockQuant n L t₂) b).toReal
            * Real.log (uGen θ₂ M n L t₂ b) ∂μ₂L := by
        refine integral_congr_ae (ae_of_all _ fun t₂ => ?_)
        dsimp only
        rw [DMC.integral_comp_eq_sum (measurable_blockQuant n L) (fun v => Ψ v t₂)]
        simp only [hcl, Finset.sum_mul, Ψ, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun v _ => ?_
        rw [blockLaw_toReal]
        ring
    _ ≤ _ := DMC.integral_sum_mul_log_le_inputMutualInfo
        (BC.cloudChannel₂ (chan N₁ N₂ n L P) (satLaw θ₁ n L)) (blockLaw θ₂ n L)
        (measurable_blockQuant n L) (blockLaw_toReal θ₂ n L)
        (fun t (b : Blk n L) => uGen θ₂ M n L t b)
        (fun t (b : Blk n L) => uGen_pos hθ₂ hM n L t b)
        (fun (b : Blk n L) => integral_uGen hθ₂ hM n L b)
        (fun b => integrable_log_uGen hθ₂ hM n L measurable_id measurable_const
          (integrable_sq_eval θ₂))

private lemma integral_le_mutualInfo (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hN : 0 < N₁) (n L : ℕ)
    (P : ℝ) :
    (∫ t, ∫ z, ∑ l, Real.log (letterRatio θ₂ (θ₁ + N₁) n (t.2 l)
          (level n (sumSignal n L P t l + z l))) ∂noise N₁ L
        ∂((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
          (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal)))
      + ∫ t, ∫ z, ∑ l, Real.log (letterRatio θ₁ N₁ n (t.1 l)
          (level n (sumSignal n L P t l - value n (level n (t.2 l)) + z l))) ∂noise N₁ L
        ∂((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
          (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal))
      ≤ mutualInfo (fun ω : Blk n L × (Blk n L × Blk n L) ×
          (Blk n L × (Blk n L → Blk n L)) × Blk n L => ω.2.1) (fun ω => ω.2.2.1)
        (BC.jointMeasure (chan N₁ N₂ n L P) (blockLaw θ₂ n L) (satLaw θ₁ n L)) := by
  have hpx : (DMC.jointPMF (fun u => (blockLaw θ₁ n L).map fun v => (v, u)) (blockLaw θ₂ n L)).map
      Prod.snd = MAC.inputPMF (blockLaw θ₁ n L) (blockLaw θ₂ n L) := by
    rw [← bind_swap]
    simp [DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hI : mutualInfo (fun ω : Blk n L × (Blk n L × Blk n L) ×
          (Blk n L × (Blk n L → Blk n L)) × Blk n L => ω.2.1) (fun ω => ω.2.2.1)
        (BC.jointMeasure (chan N₁ N₂ n L P) (blockLaw θ₂ n L) (satLaw θ₁ n L))
      = (BC.channel₁ (chan N₁ N₂ n L P)).inputMutualInfo
          (MAC.inputPMF (blockLaw θ₁ n L) (blockLaw θ₂ n L)) := by
    rw [BC.mutualInfo_eq_law₁, DMC.inputMutualInfo, DMC.jointMeasure_eq_toMeasure, ← hpx]
    unfold satLaw
    rw [BC.law₁, ← jointPMF_map_snd', ← PMF.toMeasure_map _ _ (measurable_of_finite _),
      mutualInfo_map _ (measurable_of_finite _) measurable_fst measurable_snd]
    rfl
  rw [hI]
  have hM : 0 < θ₁ + N₁ := by linarith
  set M := θ₁ + N₁
  set μ₁L := Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal
  set μ₂L := Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal
  set W := BC.channel₁ (chan N₁ N₂ n L P)
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
  set u₂ : (Fin L → ℝ) × (Fin L → ℝ) → (Blk n L × (Blk n L → Blk n L)) → ℝ :=
    fun t b => uGen θ₂ M n L t.2 b.1
  set u₁ : (Fin L → ℝ) × (Fin L → ℝ) → (Blk n L × (Blk n L → Blk n L)) → ℝ :=
    fun t b => uGen θ₁ N₁ n L t.1 (b.2 (blockQuant n L t.2))
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
      ((measurable_of_finite b.2).comp ((measurable_blockQuant n L).comp measurable_snd)) hf2₁
  have hm : ∀ x₂ : Blk n L, MeasurableSet (blockQuant n L ⁻¹' {x₂}) := fun x₂ =>
    measurable_blockQuant n L (measurableSet_singleton _)
  have hi₁ : ∀ c, Integrable (fun t => uGen θ₁ N₁ n L t c) μ₁L := fun c =>
    Integrable.of_integral_ne_zero (by rw [integral_uGen hθ₁ hN]; exact one_ne_zero)
  have hi₂ : ∀ c, Integrable (fun t => uGen θ₂ M n L t c) μ₂L := fun c =>
    Integrable.of_integral_ne_zero (by rw [integral_uGen hθ₂ hM]; exact one_ne_zero)
  have hu1 : ∀ b : Blk n L × (Blk n L → Blk n L), ∫ t, u₂ t b * u₁ t b ∂(μ₁L.prod μ₂L) = 1 := by
    intro b
    have hpt : ∀ t : (Fin L → ℝ) × (Fin L → ℝ), u₂ t b * u₁ t b = ∑ x₂ : Blk n L,
        uGen θ₁ N₁ n L t.1 (b.2 x₂)
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
      (fun t₁ => uGen θ₁ N₁ n L t₁ (b.2 x₂))
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
    simp only [u₂, W, channel₁_chan]
    rw [sum_blockChannel_toReal_mul N₁ _ (measurable_quant₁ n L)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    simp only [quant₁, Q]
    rw [log_uGen_blockQuant hθ₂ hM, sig_blockQuant]
    rfl
  · refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [u₁, W, channel₁_chan]
    rw [sum_blockChannel_toReal_mul N₁ _ (measurable_quant₁ n L)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    simp only [quant₁, Q]
    rw [log_uGen_blockQuant hθ₁ hN, sig_blockQuant, val_blockQuant]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.sub_apply, Pi.add_apply]
    ring_nf

end Bounds

private lemma tendsto_cTerm (n : ℕ) (θ s : ℝ) :
    Tendsto (fun c : ℝ => 4 * n / c * θ / (2 * s)) atTop (𝓝 0) := by
  have h := ((tendsto_const_nhds (x := (4 * n : ℝ))).div_atTop tendsto_id).mul_const θ
    |>.div_const (2 * s)
  simpa using h

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

private lemma awgnCapacity_anti {P N N' : ℝ} (hP : 0 ≤ P) (hN : 0 < N) (hNN : N ≤ N') :
    awgnCapacity P N' ≤ awgnCapacity P N := by
  unfold awgnCapacity
  have h0 : 0 < 1 + P / N' := by have := div_nonneg hP (hN.trans_le hNN).le; linarith
  have h : 1 + P / N' ≤ 1 + P / N := by
    have := div_le_div_of_nonneg_left hP hN hNN
    linarith
  nlinarith [Real.log_le_log h0 h]

private lemma achievable_of_chan {P N₁ N₂ R₁ R₂ θ₁ θ₂ : ℝ} (hP : 0 ≤ P) (hR₁ : 0 ≤ R₁)
    (hR₂ : 0 ≤ R₂) {n L : ℕ} (hL : 0 < L)
    (h₁ : L * R₁ < condMutualInfo (fun ω : Blk n L × (Blk n L × Blk n L) ×
      (Blk n L × (Blk n L → Blk n L)) × Blk n L => ω.2.1) (fun ω => ω.2.2.1) (fun ω => ω.1)
        (BC.jointMeasure (chan N₁ N₂ n L P) (blockLaw θ₂ n L) (satLaw θ₁ n L)))
    (h₂ : L * R₂ < mutualInfo (fun ω : Blk n L × (Blk n L × Blk n L) ×
      (Blk n L × (Blk n L → Blk n L)) × Blk n L => ω.1) (fun ω => ω.2.2.2)
        (BC.jointMeasure (chan N₁ N₂ n L P) (blockLaw θ₂ n L) (satLaw θ₁ n L)))
    (h₃ : L * (R₁ + R₂) < mutualInfo (fun ω : Blk n L × (Blk n L × Blk n L) ×
      (Blk n L × (Blk n L → Blk n L)) × Blk n L => ω.2.1) (fun ω => ω.2.2.1)
        (BC.jointMeasure (chan N₁ N₂ n L P) (blockLaw θ₂ n L) (satLaw θ₁ n L))) :
    Achievable P N₁ N₂ R₁ R₂ :=
  achievable_of_lt_blockChannel hP hR₁ hR₂ hL (sig n L P) (fun _ => sum_sq_sumClip_le hP L _)
    (quant₁ n L) (blockQuant n L) (measurable_quant₁ n L) (measurable_blockQuant n L)
    (blockLaw θ₂ n L) (satLaw θ₁ n L) h₁ h₂ h₃

theorem achievable_of_lt {P N₁ N₂ R₁ R₂ θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hθ : θ₁ + θ₂ < P) (hN₁ : 0 < N₁) (hN : N₁ ≤ N₂) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (h₁ : R₁ < awgnCapacity θ₁ N₁) (h₂ : R₂ < awgnCapacity θ₂ (θ₁ + N₂)) :
    Achievable P N₁ N₂ R₁ R₂ := by
  have hN₂ : 0 < N₂ := hN₁.trans_le hN
  have hP : 0 ≤ P := by linarith
  have hC := awgnCapacity_anti (P := θ₂) hθ₂.le (by linarith : 0 < θ₁ + N₁)
    (by linarith : θ₁ + N₁ ≤ θ₁ + N₂)
  set η := min (min (awgnCapacity θ₁ N₁ - R₁) (awgnCapacity θ₂ (θ₁ + N₂) - R₂))
    (awgnCapacity θ₁ N₁ + awgnCapacity θ₂ (θ₁ + N₁) - (R₁ + R₂)) / 8 with hη
  have hm1 := min_le_left (min (awgnCapacity θ₁ N₁ - R₁) (awgnCapacity θ₂ (θ₁ + N₂) - R₂))
    (awgnCapacity θ₁ N₁ + awgnCapacity θ₂ (θ₁ + N₁) - (R₁ + R₂))
  have hm2 := min_le_right (min (awgnCapacity θ₁ N₁ - R₁) (awgnCapacity θ₂ (θ₁ + N₂) - R₂))
    (awgnCapacity θ₁ N₁ + awgnCapacity θ₂ (θ₁ + N₁) - (R₁ + R₂))
  have hm3 := min_le_left (awgnCapacity θ₁ N₁ - R₁) (awgnCapacity θ₂ (θ₁ + N₂) - R₂)
  have hm4 := min_le_right (awgnCapacity θ₁ N₁ - R₁) (awgnCapacity θ₂ (θ₁ + N₂) - R₂)
  have hη0 : 0 < η := by
    rw [hη]
    exact div_pos (lt_min (lt_min (by linarith) (by linarith)) (by linarith)) (by norm_num)
  obtain ⟨n, hn1, hn2, hnT, hβ⟩ := ((tendsto_letterGain hθ₁ hN₁).eventually
    (lt_mem_nhds (show awgnCapacity θ₁ N₁ - η < awgnCapacity θ₁ N₁ by linarith))).and
    (((tendsto_tinGain hθ₁ hθ₂ hN₂).eventually
      (lt_mem_nhds (show awgnCapacity θ₂ (θ₁ + N₂) - η < awgnCapacity θ₂ (θ₁ + N₂) by
        linarith))).and
    (((tendsto_tinGain hθ₁ hθ₂ hN₁).eventually
      (lt_mem_nhds (show awgnCapacity θ₂ (θ₁ + N₁) - η < awgnCapacity θ₂ (θ₁ + N₁) by
        linarith))).and
    (eventually_tendsto_sumBad hθ₁ hθ₂ hθ))) |>.exists
  obtain ⟨c, hc0, hc1, hc2, hcT⟩ := ((eventually_gt_atTop 0).and
    (((tendsto_cTerm n θ₁ (θ₁ * N₁ / (θ₁ + N₁))).eventually (gt_mem_nhds hη0)).and
    (((tendsto_cTerm n θ₂ (θ₂ * (θ₁ + N₂) / (θ₂ + (θ₁ + N₂)))).eventually
      (gt_mem_nhds hη0)).and
    ((tendsto_cTerm n θ₂ (θ₂ * (θ₁ + N₁) / (θ₂ + (θ₁ + N₁)))).eventually
      (gt_mem_nhds hη0))))).exists
  have he₁ := ((hβ.const_mul (4 * n * c + 4 * n ^ 2)).add_const (4 * n / c * θ₁)).div_const
    (2 * (θ₁ * N₁ / (θ₁ + N₁)))
  have he₂ := ((hβ.const_mul (4 * n * c + 4 * n ^ 2)).add_const (4 * n / c * θ₂)).div_const
    (2 * (θ₂ * (θ₁ + N₂) / (θ₂ + (θ₁ + N₂))))
  have heT := ((hβ.const_mul (4 * n * c + 4 * n ^ 2)).add_const (4 * n / c * θ₂)).div_const
    (2 * (θ₂ * (θ₁ + N₁) / (θ₂ + (θ₁ + N₁))))
  rw [mul_zero, zero_add] at he₁ he₂ heT
  obtain ⟨L, hL0, hL1, hL2, hLT⟩ := ((eventually_gt_atTop 0).and
    ((he₁.eventually (gt_mem_nhds hc1)).and
      ((he₂.eventually (gt_mem_nhds hc2)).and (heT.eventually (gt_mem_nhds hcT))))).exists
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL0
  have b1 := (integral_satGain_ge (θ₂ := θ₂) hθ₁ hN₁ n L P hc0).trans
    (integral_le_condMutualInfo (N₂ := N₂) hθ₁ hN₁ n L P)
  have b2 := (integral_cloudGain_ge hθ₁ hθ₂ hN₂ n L P hc0).trans
    (integral_le_mutualInfo_cloud (N₁ := N₁) hθ₁ hθ₂ hN₂ n L P)
  have b3 := (add_le_add (integral_cloudGain_ge hθ₁ hθ₂ hN₁ n L P hc0)
    (integral_satGain_ge hθ₁ hN₁ n L P hc0)).trans
    (integral_le_mutualInfo (N₂ := N₂) hθ₁ hθ₂ hN₁ n L P)
  have k1 : 8 * η ≤ awgnCapacity θ₁ N₁ - R₁ := by linarith
  have k2 : 8 * η ≤ awgnCapacity θ₂ (θ₁ + N₂) - R₂ := by linarith
  have k3 : 8 * η ≤ awgnCapacity θ₁ N₁ + awgnCapacity θ₂ (θ₁ + N₁) - (R₁ + R₂) := by linarith
  exact achievable_of_chan hP hR₁ hR₂ hL0 (final_lt hL' b1 hL1 hn1 k1 hη0)
    (final_lt hL' b2 hL2 hn2 k2 hη0) (final_lt₂ hL' b3 hLT hL1 hnT hn1 k3 hη0)

private lemma dist_max_lt {x η : ℝ} (hx : 0 ≤ x) (hη : 0 < η) :
    dist x (max (x - η / 2) 0) < η := by
  rw [Real.dist_eq]
  rcases le_total (x - η / 2) 0 with h | h
  · rw [max_eq_right h, sub_zero, abs_of_nonneg hx]
    linarith
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]
    linarith

private lemma awgnCapacity_pos {P N : ℝ} (hP : 0 < P) (hN : 0 < N) : 0 < awgnCapacity P N := by
  unfold awgnCapacity
  have := div_pos hP hN
  exact mul_pos (by norm_num) (Real.log_pos (by linarith))

private lemma eventually_lt_cap {a b c R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (h : R < awgnCapacity a (b + c)) :
    ∀ᶠ τ in 𝓝[<] (1 : ℝ), R < awgnCapacity (τ * a) (τ * b + c) := by
  have hd : (0 : ℝ) < 1 * b + c := by linarith
  have hcont : ContinuousAt (fun τ => awgnCapacity (τ * a) (τ * b + c)) 1 := by
    unfold awgnCapacity
    refine continuousAt_const.mul ((continuousAt_const.add
      ((continuousAt_id.mul continuousAt_const).div
        ((continuousAt_id.mul continuousAt_const).add continuousAt_const) ?_)).log ?_)
    · exact hd.ne'
    · have := div_nonneg (mul_nonneg zero_le_one ha) hd.le
      exact (by linarith : (0 : ℝ) < 1 + 1 * a / (1 * b + c)).ne'
  exact nhdsWithin_le_nhds (hcont.eventually (lt_mem_nhds (by simpa using h)))

theorem bcRegion_subset_closure {P N₁ N₂ : ℝ} (hP : 0 ≤ P) (hN₁ : 0 < N₁) (hN : N₁ ≤ N₂) :
    GaussianMultiUser.bcRegion P N₁ N₂
      ⊆ closure {R : ℝ × ℝ | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ Achievable P N₁ N₂ R.1 R.2} := by
  have hN₂ : 0 < N₂ := hN₁.trans_le hN
  rintro ⟨R₁, R₂⟩ hR
  obtain ⟨α, hα, h0₁, h0₂, h₁, h₂⟩ := Set.mem_iUnion₂.1 hR
  simp only at h0₁ h0₂ h₁ h₂
  have hαP : 0 ≤ α * P := mul_nonneg hα.1 hP
  have hαP' : 0 ≤ (1 - α) * P := mul_nonneg (by linarith [hα.2]) hP
  rcases hαP.eq_or_lt with h | hpos₁
  · rw [← h] at h₁ h₂
    have hR₁ : R₁ = 0 := le_antisymm (by simpa [awgnCapacity] using h₁) h0₁
    subst hR₁
    have h₂' : R₂ ≤ awgnCapacity P N₂ := h₂.trans (by
      rw [zero_add]
      exact GaussianMultiUser.awgnCapacity_mono hαP'
        (by nlinarith [hα.1]) hN₂)
    have hm : R₂ ∈ closure {R : ℝ | 0 ≤ R ∧ AWGN.Achievable P N₂ R} := by
      rw [AWGN.closure_achievable_eq hP hN₂]
      exact ⟨h0₂, h₂'⟩
    exact map_mem_closure (f := fun r : ℝ => ((0 : ℝ), r)) (continuous_const.prodMk continuous_id)
      hm fun R hR => ⟨le_rfl, hR.1, achievable_zero_left hR.2⟩
  rcases hαP'.eq_or_lt with h | hpos₂
  · rw [← h] at h₂
    have hR₂ : R₂ = 0 := le_antisymm (by simpa [awgnCapacity] using h₂) h0₂
    subst hR₂
    have h₁' : R₁ ≤ awgnCapacity P N₁ :=
      h₁.trans (GaussianMultiUser.awgnCapacity_mono hαP (by nlinarith [hα.2]) hN₁)
    have hm : R₁ ∈ closure {R : ℝ | 0 ≤ R ∧ AWGN.Achievable P N₁ R} := by
      rw [AWGN.closure_achievable_eq hP hN₁]
      exact ⟨h0₁, h₁'⟩
    exact map_mem_closure (f := fun r : ℝ => (r, (0 : ℝ))) (continuous_id.prodMk continuous_const)
      hm fun R hR => ⟨hR.1, le_rfl, achievable_zero_right hR.2⟩
  have hPpos : 0 < P := by nlinarith [hα.1, hα.2]
  rw [Metric.mem_closure_iff]
  intro η hη
  have e₁ := eventually_lt_cap (R := R₁ - η / 2) hαP le_rfl hN₁ (by
    rw [zero_add]
    linarith)
  have e₂ := eventually_lt_cap (R := R₂ - η / 2) (a := (1 - α) * P) (b := α * P) hαP' hαP hN₂
    (by linarith)
  obtain ⟨τ, ⟨hτ₁, hτ₂⟩, hτ0, hτ1⟩ :=
    ((e₁.and e₂).and (Ioo_mem_nhdsLT zero_lt_one)).exists
  simp only [mul_zero, zero_add] at hτ₁
  have hθ₁ : 0 < τ * (α * P) := mul_pos hτ0 hpos₁
  have hθ₂ : 0 < τ * ((1 - α) * P) := mul_pos hτ0 hpos₂
  refine ⟨(max (R₁ - η / 2) 0, max (R₂ - η / 2) 0), ⟨le_max_right _ _, le_max_right _ _,
    achievable_of_lt hθ₁ hθ₂ (by nlinarith) hN₁ hN (le_max_right _ _) (le_max_right _ _)
      (max_lt hτ₁ (awgnCapacity_pos hθ₁ hN₁))
      (max_lt hτ₂ (awgnCapacity_pos hθ₂ (by linarith)))⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨dist_max_lt h0₁ hη, dist_max_lt h0₂ hη⟩

end GaussianBroadcast

end Meat
