import Meat.Continuous.AWGNAchievability
import Meat.Continuous.DirtyPaper
import Meat.Channel.GelfandPinsker

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal

namespace Meat

namespace DirtyPaper

section Blocks

private def blockEquiv {n m L r : ℕ} (h : m * L + r = n) : (Fin m × Fin L) ⊕ Fin r ≃ Fin n :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans (finSumFinEquiv.trans (finCongr h))

private def blocks {n m L r : ℕ} (h : m * L + r = n) (z : Fin n → ℝ) : Fin m → Fin L → ℝ :=
  fun t l => z (blockEquiv h (.inl (t, l)))

private lemma measurable_blocks {n m L r : ℕ} (h : m * L + r = n) : Measurable (blocks h) := by
  unfold blocks
  fun_prop

private lemma map_noise_blocks (N : ℝ) {n m L r : ℕ} (h : m * L + r = n) :
    (AWGN.noise N n).map (blocks h) = Measure.pi fun _ : Fin m => AWGN.noise N L := by
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

private lemma measurable_embed {n m L r : ℕ} (h : m * L + r = n) : Measurable (embed h) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold embed
  rcases hi : (blockEquiv h).symm i with p | p
  · simp only [Sum.elim_inl]
    fun_prop
  · simp only [Sum.elim_inr]
    exact measurable_const

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

end Blocks

section Letter

variable {St A B : Type*} [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [MeasurableSpace B]
  [MeasurableSingletonClass B] {L : ℕ}

omit [Fintype St] [MeasurableSingletonClass St] [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B] [MeasurableSingletonClass B] in
private lemma measurable_letterMap {qs : (Fin L → ℝ) → St} (hqs : Measurable qs)
    (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B} (hq : Measurable q) :
    Measurable fun w : (Fin L → ℝ) × (Fin L → ℝ) => (qs w.1, fun x => q (a x + w.1 + w.2)) :=
  (hqs.comp measurable_fst).prodMk (measurable_pi_iff.2 fun _ =>
    hq.comp ((measurable_const.add measurable_fst).add measurable_snd))

noncomputable def letter (Q N : ℝ) {qs : (Fin L → ℝ) → St} (hqs : Measurable qs)
    (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B} (hq : Measurable q) : PMF (St × (A → B)) :=
  haveI := (Measure.isProbabilityMeasure_map_iff (μ := (AWGN.noise Q L).prod (AWGN.noise N L))
    (measurable_letterMap hqs a hq).aemeasurable).2 inferInstance
  (((AWGN.noise Q L).prod (AWGN.noise N L)).map
    fun w => (qs w.1, fun x => q (a x + w.1 + w.2))).toPMF

noncomputable def stateLaw (Q N : ℝ) {qs : (Fin L → ℝ) → St} (hqs : Measurable qs)
    (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B} (hq : Measurable q) : PMF St :=
  (letter Q N hqs a hq).map Prod.fst

omit [DecidableEq B] in
private lemma stateLaw_apply (Q N : ℝ) {qs : (Fin L → ℝ) → St} (hqs : Measurable qs)
    (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B} (hq : Measurable q) (σ : St) :
    stateLaw Q N hqs a hq σ = ∑ f, letter Q N hqs a hq (σ, f) := by
  classical
  rw [stateLaw, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    sum_eq_single σ (fun σ' _ h => sum_eq_zero fun f _ => by simp [Ne.symm h]) (by simp)]
  simp

noncomputable def chan (Q N : ℝ) {qs : (Fin L → ℝ) → St} (hqs : Measurable qs)
    (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B} (hq : Measurable q) : DMC (A × St) B :=
  fun p => @dite _ (stateLaw Q N hqs a hq p.2 = 0) (Classical.dec _)
    (fun _ => (letter Q N hqs a hq).map fun v => v.2 p.1)
  fun h => PMF.ofFintype (fun y => (∑ f ∈ univ.filter (fun f : A → B => f p.1 = y),
    letter Q N hqs a hq (p.2, f)) / stateLaw Q N hqs a hq p.2) (by
      rw [← ENNReal.sum_div, Finset.sum_fiberwise univ (fun f : A → B => f p.1),
        ← stateLaw_apply]
      exact ENNReal.div_self h (PMF.apply_ne_top _ _))

theorem stateLaw_mul_chan (Q N : ℝ) {qs : (Fin L → ℝ) → St} (hqs : Measurable qs)
    (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B} (hq : Measurable q) (x : A) (σ : St) (y : B) :
    stateLaw Q N hqs a hq σ * chan Q N hqs a hq (x, σ) y =
      ∑ f ∈ univ.filter (fun f : A → B => f x = y), letter Q N hqs a hq (σ, f) := by
  by_cases h : stateLaw Q N hqs a hq σ = 0
  · rw [h, zero_mul]
    rw [stateLaw_apply] at h
    exact (sum_eq_zero fun f _ => (sum_eq_zero_iff.1 h) f (mem_univ f)).symm
  · rw [chan, dite_eq_right_of_eq_false (eq_false h), PMF.ofFintype_apply]
    exact ENNReal.mul_div_cancel h (PMF.apply_ne_top _ _)

end Letter

section Lift

variable {St A B : Type*} [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [MeasurableSpace B]
  [MeasurableSingletonClass B] {L : ℕ} {P : ℝ}

omit [MeasurableSpace St] [MeasurableSingletonClass St] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private lemma sum_functional {m : ℕ} (ℓ : St × (A → B) → ℝ≥0∞)
    (x : (Fin m → St) → Fin m → A) (D : (Fin m → B) → Prop) [DecidablePred D] :
    ∑ v : Fin m → St × (A → B),
        (if D (fun t => (v t).2 (x (fun t' => (v t').1) t)) then ∏ t, ℓ (v t) else 0) =
      ∑ σ : Fin m → St, ∑ y : Fin m → B, (if D y then
        ∏ t, ∑ f ∈ univ.filter (fun f : A → B => f (x σ t) = y t), ℓ (σ t, f) else 0) := by
  rw [← (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => St) (fun _ => A → B)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine sum_congr rfl fun σ _ => ?_
  simp_rw [prod_univ_sum]
  have e : ∀ y : Fin m → B, (if D y then ∑ F ∈ Fintype.piFinset fun t =>
      univ.filter (fun f : A → B => f (x σ t) = y t), ∏ t, ℓ (σ t, F t) else 0) =
      ∑ F : Fin m → A → B, if (fun t => F t (x σ t)) = y then
        (if D y then ∏ t, ℓ (σ t, F t) else 0) else 0 := by
    intro y
    split_ifs with hD
    · rw [← sum_filter]
      refine sum_congr ?_ fun F _ => rfl
      ext F
      simp [Fintype.mem_piFinset, funext_iff]
    · simp
  rw [sum_congr rfl fun y _ => e y, sum_comm]
  refine sum_congr rfl fun F _ => ?_
  rw [sum_ite_eq]
  simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, mem_univ, ite_true]
  rfl

noncomputable def toCode (hP : 0 ≤ P) {n m r k : ℕ} (h : m * L + r = n)
    {qs : (Fin L → ℝ) → St} (hqs : Measurable qs) (a : A → Fin L → ℝ)
    (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P) {q : (Fin L → ℝ) → B} (hq : Measurable q)
    (c : StateCode (Fin k) St A B m) : Code P n k where
  enc i s := embed h fun t => a (c.enc i (fun t' => qs (blocks h s t')) t)
  power i s := by
    rw [sum_sq_embed]
    calc ∑ t, ∑ l, a (c.enc i (fun t' => qs (blocks h s t')) t) l ^ 2
        ≤ ∑ _t : Fin m, (L * P) := Finset.sum_le_sum fun t _ => ha _
      _ = m * L * P := by simp [mul_assoc]
      _ ≤ n * P := mul_le_mul_of_nonneg_right (by exact_mod_cast h ▸ Nat.le_add_right _ _) hP
  measurable_enc i := (measurable_embed h).comp
    ((measurable_of_finite (fun σ : Fin m → St => fun t => a (c.enc i σ t))).comp
      (measurable_pi_iff.2 fun t' => hqs.comp ((measurable_pi_apply t').comp
        (measurable_blocks h))))
  dec y := c.dec fun t => q (blocks h y t)
  measurable_dec := (measurable_of_finite c.dec).comp
    (measurable_pi_iff.2 fun t => hq.comp ((measurable_pi_apply t).comp (measurable_blocks h)))

omit [DecidableEq A] [DecidableEq B] in
private lemma map_letter (Q N : ℝ) {m n r : ℕ} (h : m * L + r = n) {qs : (Fin L → ℝ) → St}
    (hqs : Measurable qs) (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B} (hq : Measurable q) :
    ((AWGN.noise Q n).prod (AWGN.noise N n)).map
      (fun p t => (qs (blocks h p.1 t), fun x => q (a x + blocks h p.1 t + blocks h p.2 t))) =
      Measure.pi fun _ : Fin m => (letter Q N hqs a hq).toMeasure := by
  set g := fun w : (Fin L → ℝ) × (Fin L → ℝ) => (qs w.1, fun x => q (a x + w.1 + w.2))
  have hg : Measurable g := measurable_letterMap hqs a hq
  set e := MeasurableEquiv.arrowProdEquivProdArrow (Fin L → ℝ) (Fin L → ℝ) (Fin m)
  have hf : (fun (p : (Fin n → ℝ) × (Fin n → ℝ)) t =>
      (qs (blocks h p.1 t), fun x => q (a x + blocks h p.1 t + blocks h p.2 t))) =
      (fun w t => g (w t)) ∘ e.symm ∘ Prod.map (blocks h) (blocks h) := rfl
  have h1 : ((AWGN.noise Q n).prod (AWGN.noise N n)).map (Prod.map (blocks h) (blocks h)) =
      (Measure.pi fun _ : Fin m => AWGN.noise Q L).prod
        (Measure.pi fun _ : Fin m => AWGN.noise N L) := by
    rw [← Measure.map_prod_map _ _ (measurable_blocks h) (measurable_blocks h),
      map_noise_blocks, map_noise_blocks]
  have h2 := (measurePreserving_arrowProdEquivProdArrow (Fin L → ℝ) (Fin L → ℝ) (Fin m)
    (fun _ => AWGN.noise Q L) (fun _ => AWGN.noise N L)).symm
  have hl : ((AWGN.noise Q L).prod (AWGN.noise N L)).map g = (letter Q N hqs a hq).toMeasure := by
    unfold letter
    rw [Measure.toPMF_toMeasure]
  have hG : Measurable fun (w : Fin m → (Fin L → ℝ) × (Fin L → ℝ)) t => g (w t) :=
    measurable_pi_iff.2 fun t => hg.comp (measurable_pi_apply t)
  rw [hf, ← Measure.map_map hG
    (e.symm.measurable.comp ((measurable_blocks h).prodMap (measurable_blocks h))),
    ← Measure.map_map e.symm.measurable ((measurable_blocks h).prodMap (measurable_blocks h)),
    h1, h2.map_eq, Measure.pi_map_pi fun _ => hg.aemeasurable]
  simp_rw [hl]

private theorem errorProb_toCode (hP : 0 ≤ P) (Q N : ℝ) {n m r k : ℕ} (h : m * L + r = n)
    {qs : (Fin L → ℝ) → St} (hqs : Measurable qs) (a : A → Fin L → ℝ)
    (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P) {q : (Fin L → ℝ) → B} (hq : Measurable q)
    (c : StateCode (Fin k) St A B m) (i : Fin k) :
    (toCode hP h hqs a ha hq c).errorProb Q N i = ∑ σ : Fin m → St,
      (∏ t, stateLaw Q N hqs a hq (σ t)) * ∑ y : Fin m → B,
        (if c.dec y = i then 0 else ∏ t, chan Q N hqs a hq (c.enc i σ t, σ t) (y t)) := by
  set Gf : (Fin n → ℝ) × (Fin n → ℝ) → Fin m → St × (A → B) :=
    fun p t => (qs (blocks h p.1 t), fun x => q (a x + blocks h p.1 t + blocks h p.2 t))
  have hG : Measurable Gf := by
    refine measurable_pi_iff.2 fun t => ?_
    have hb : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (blocks h p.1 t, blocks h p.2 t) :=
      ((measurable_pi_apply t).comp ((measurable_blocks h).comp measurable_fst)).prodMk
        ((measurable_pi_apply t).comp ((measurable_blocks h).comp measurable_snd))
    exact (measurable_letterMap hqs a hq).comp hb
  set T : Finset (Fin m → St × (A → B)) := univ.filter
    fun v => c.dec (fun t => (v t).2 (c.enc i (fun t' => (v t').1) t)) ≠ i
  have hT : MeasurableSet (↑T : Set (Fin m → St × (A → B))) := T.measurableSet
  have hset : ∀ s, {z | (toCode hP h hqs a ha hq c).dec
      ((toCode hP h hqs a ha hq c).enc i s + s + z) ≠ i} = Prod.mk s ⁻¹' (Gf ⁻¹' ↑T) := by
    intro s
    ext z
    simp [toCode, T, Gf, blocks_add, blocks_embed]
  rw [Code.errorProb, lintegral_congr fun s => by rw [hset s],
    ← Measure.prod_apply (hG hT), ← Measure.map_apply hG hT, map_letter Q N h hqs a hq,
    ← sum_measure_singleton]
  have hpt : ∀ v : Fin m → St × (A → B),
      (Measure.pi fun _ : Fin m => (letter Q N hqs a hq).toMeasure) {v} =
        ∏ t, letter Q N hqs a hq (v t) := fun v => by
    rw [← Set.univ_pi_singleton, Measure.pi_pi]
    exact prod_congr rfl fun t _ => PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
  simp_rw [hpt]
  rw [sum_filter, sum_functional (letter Q N hqs a hq) (c.enc i) (fun y => c.dec y ≠ i)]
  refine sum_congr rfl fun σ _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : c.dec y = i
  · simp [hy]
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hy), ite_eq_right_of_eq_false _ _ (eq_false hy),
      ← prod_mul_distrib]
    exact prod_congr rfl fun t _ => (stateLaw_mul_chan Q N hqs a hq _ _ _).symm

theorem avgError_toCode (hP : 0 ≤ P) (Q N : ℝ) {n m r k : ℕ} (h : m * L + r = n)
    {qs : (Fin L → ℝ) → St} (hqs : Measurable qs) (a : A → Fin L → ℝ)
    (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P) {q : (Fin L → ℝ) → B} (hq : Measurable q)
    (c : StateCode (Fin k) St A B m) :
    (toCode hP h hqs a ha hq c).avgError Q N =
      c.avgError (chan Q N hqs a hq) (stateLaw Q N hqs a hq) := by
  simp only [Code.avgError, StateCode.avgError, errorProb_toCode, Fintype.card_fin]

theorem achievable_of_lt_infoCapacity_block [MeasurableSpace A] [MeasurableSingletonClass A]
    [Nonempty A] {Q N R : ℝ} (hP : 0 ≤ P) (hR : 0 ≤ R) (hL : 0 < L)
    {qs : (Fin L → ℝ) → St} (hqs : Measurable qs) (a : A → Fin L → ℝ)
    (ha : ∀ x, ∑ l, a x l ^ 2 ≤ L * P) {q : (Fin L → ℝ) → B} (hq : Measurable q)
    (hI : L * R < GelfandPinsker.infoCapacity (chan Q N hqs a hq) (stateLaw Q N hqs a hq)) :
    Achievable P Q N R := by
  set I := GelfandPinsker.infoCapacity (chan Q N hqs a hq) (stateLaw Q N hqs a hq)
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  set R₁ := (R + I / L) / 2
  have hRI : R < I / L := by rw [lt_div_iff₀ hL']; linarith
  have hR₁ : R < R₁ := by simp only [R₁]; linarith
  have hW : GelfandPinsker.Achievable (chan Q N hqs a hq) (stateLaw Q N hqs a hq) (L * R₁) :=
    GelfandPinsker.achievable_of_lt_infoCapacity _ _ (by
      have : L * R₁ < L * (I / L) := mul_lt_mul_of_pos_left (by simp only [R₁]; linarith) hL'
      rwa [mul_div_cancel₀ _ hL'.ne'] at this)
  intro ε hε
  obtain ⟨n₁, hn₁⟩ := hW ε hε
  obtain ⟨m₁, hm₁⟩ := exists_nat_gt (R / (R₁ - R))
  refine ⟨L * max n₁ m₁, fun n hn => ?_⟩
  have h : n / L * L + n % L = n := by rw [mul_comm]; exact Nat.div_add_mod n L
  have hm : max n₁ m₁ ≤ n / L := (Nat.le_div_iff_mul_le hL).2 (by rw [mul_comm]; exact hn)
  obtain ⟨k, hk, c, hc⟩ := hn₁ (n / L) (le_of_max_le_left hm)
  refine ⟨k, ?_, toCode hP h hqs a ha hq c, by rw [avgError_toCode]; exact hc⟩
  have hr : ((n % L : ℕ) : ℝ) ≤ L := by exact_mod_cast (Nat.mod_lt n hL).le
  have hn' : (n : ℝ) = (n / L : ℕ) * L + (n % L : ℕ) := by exact_mod_cast h.symm
  have hmR : R ≤ (n / L : ℕ) * (R₁ - R) := by
    have := (div_lt_iff₀ (sub_pos.2 hR₁)).1
      (hm₁.trans_le (Nat.cast_le.2 (le_of_max_le_right hm)))
    linarith
  refine le_trans (Real.exp_le_exp.2 ?_) hk
  rw [hn']
  nlinarith [mul_le_mul_of_nonneg_right hr hR, mul_le_mul_of_nonneg_left hmR hL'.le]

end Lift

theorem closure_achievable_eq_of_quantization {P Q N : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (hquant : ∀ R, 0 ≤ R → R < awgnCapacity P N →
      ∃ (L s₁ s₂ s₃ : ℕ) (qs : (Fin L → ℝ) → Fin s₁) (hqs : Measurable qs)
        (a : Fin s₂ → Fin L → ℝ) (q : (Fin L → ℝ) → Fin s₃) (hq : Measurable q),
        0 < L ∧ 0 < s₂ ∧ (∀ x, ∑ l, a x l ^ 2 ≤ L * P) ∧
          L * R < GelfandPinsker.infoCapacity (chan Q N hqs a hq) (stateLaw Q N hqs a hq)) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable P Q N R} = Set.Icc 0 (awgnCapacity P N) := by
  refine closure_achievable_eq_of hP hN fun R hR hRC => ?_
  obtain ⟨L, s₁, s₂, s₃, qs, hqs, a, q, hq, hL, hs₂, ha, hI⟩ := hquant R hR hRC
  have : Nonempty (Fin s₂) := ⟨⟨0, hs₂⟩⟩
  exact achievable_of_lt_infoCapacity_block hP hR hL hqs a ha hq hI

end DirtyPaper

end Meat
