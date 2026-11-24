import Meat.Open.Broadcast
import Meat.Channel.Converse
import Meat.Shannon.ChainRule

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Meat

namespace BC

variable {A B₁ B₂ V : Type*}

noncomputable def degradedTwin (W : DMC A (B₁ × B₂)) (D : DMC B₁ B₂) : DMC A (B₁ × B₂) :=
  fun a => (channel₁ W a).bind fun y₁ => (D y₁).map fun y₂ => (y₁, y₂)

theorem channel₁_degradedTwin (W : DMC A (B₁ × B₂)) (D : DMC B₁ B₂) :
    channel₁ (degradedTwin W D) = channel₁ W := by
  funext a
  have h : ∀ y : B₁, (D y).map (fun _ => y) = PMF.pure y := fun y => PMF.map_const _ _
  simp only [channel₁, degradedTwin, PMF.map_bind, PMF.map_comp, Function.comp_def, h,
    PMF.bind_pure]

theorem channel₂_degradedTwin (W : DMC A (B₁ × B₂)) (D : DMC B₁ B₂)
    (hD : ∀ a, channel₂ W a = (channel₁ W a).bind D) :
    channel₂ (degradedTwin W D) = channel₂ W := by
  funext a
  rw [hD]
  have h : ∀ y : B₁, (D y).map (fun x => x) = D y := fun y => PMF.map_id _
  simp only [channel₂, degradedTwin, PMF.map_bind, PMF.map_comp, Function.comp_def, h]

theorem superpositionRegion_congr [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂]
    [MeasurableSpace B₂] [MeasurableSingletonClass B₂] [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {W W' : DMC A (B₁ × B₂)} (h₁ : channel₁ W = channel₁ W')
    (h₂ : channel₂ W = channel₂ W') (pU : PMF V) (pX : V → PMF A) :
    superpositionRegion W pU pX = superpositionRegion W' pU pX := by
  have e1 : law₁ W pU pX = law₁ W' pU pX := by rw [law₁, law₁, h₁]
  have e2 : cloudChannel₂ W pX = cloudChannel₂ W' pX := by
    unfold cloudChannel₂
    rw [h₂]
  simp only [superpositionRegion, condMutualInfo_eq_law₁, mutualInfo_cloud_eq,
    mutualInfo_eq_law₁, e1, e2]

def twinCode {M₁ M₂ : Type*} {n : ℕ} (c : BCCode M₁ M₂ A B₁ B₂ n) :
    BlockCode (M₁ × M₂) A (B₁ × B₂) n :=
  ⟨c.enc, fun y => (c.dec₁ fun i => (y i).1, c.dec₂ fun i => (y i).2)⟩

section Error

variable {M₁ M₂ : Type*} {n : ℕ} [Fintype B₁] [Fintype B₂] [DecidableEq M₁] [DecidableEq M₂]

theorem sum_error₁_le (c : BCCode M₁ M₂ A B₁ B₂ n) (W : DMC A (B₁ × B₂)) (m : M₁ × M₂) :
    ∑ y₁, (if c.dec₁ y₁ = m.1 then 0
      else (DMC.blockProb (channel₁ W) (c.enc m) y₁).toReal) ≤ (c.errorProb W m).toReal := by
  have h := DMC.sum_blockProb_mul_comp W Prod.fst (c.enc m)
    fun y₁ => if c.dec₁ y₁ = m.1 then (0 : ℝ) else 1
  simp only [mul_ite, mul_zero, mul_one] at h
  rw [show channel₁ W = fun a => (W a).map Prod.fst from rfl, ← h, BCCode.errorProb,
    ENNReal.toReal_sum fun y _ => by split_ifs <;> simp [DMC.blockProb_ne_top]]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases h1 : c.dec₁ (fun i => (y i).1) = m.1
  · simp only [h1, ite_true]
    split_ifs <;> simp
  · have hne : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) ≠ m := fun h =>
      h1 (congrArg Prod.fst h)
    simp [h1, hne]

theorem sum_error₂_le (c : BCCode M₁ M₂ A B₁ B₂ n) (W : DMC A (B₁ × B₂)) (m : M₁ × M₂) :
    ∑ y₂, (if c.dec₂ y₂ = m.2 then 0
      else (DMC.blockProb (channel₂ W) (c.enc m) y₂).toReal) ≤ (c.errorProb W m).toReal := by
  have h := DMC.sum_blockProb_mul_comp W Prod.snd (c.enc m)
    fun y₂ => if c.dec₂ y₂ = m.2 then (0 : ℝ) else 1
  simp only [mul_ite, mul_zero, mul_one] at h
  rw [show channel₂ W = fun a => (W a).map Prod.snd from rfl, ← h, BCCode.errorProb,
    ENNReal.toReal_sum fun y _ => by split_ifs <;> simp [DMC.blockProb_ne_top]]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases h1 : c.dec₂ (fun i => (y i).2) = m.2
  · simp only [h1, ite_true]
    split_ifs <;> simp
  · have hne : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) ≠ m := fun h =>
      h1 (congrArg Prod.snd h)
    simp [h1, hne]

theorem twinCode_errorProb_le (c : BCCode M₁ M₂ A B₁ B₂ n) {W W' : DMC A (B₁ × B₂)}
    (h₁ : channel₁ W' = channel₁ W) (h₂ : channel₂ W' = channel₂ W) (m : M₁ × M₂) :
    ((twinCode c).errorProb W' m) ≤ 2 * c.errorProb W m := by
  have h := c.errorProb_toReal_le W' m
  change _ ≤ ∑ y₁, (if c.dec₁ y₁ = m.1 then 0
      else (DMC.blockProb (channel₁ W') (c.enc m) y₁).toReal) + ∑ y₂, (if c.dec₂ y₂ = m.2 then 0
      else (DMC.blockProb (channel₂ W') (c.enc m) y₂).toReal) at h
  rw [h₁, h₂] at h
  have hr : ((twinCode c).errorProb W' m).toReal ≤ (2 * c.errorProb W m).toReal := by
    rw [ENNReal.toReal_mul]
    have := sum_error₁_le c W m
    have := sum_error₂_le c W m
    change (c.errorProb W' m).toReal ≤ _
    norm_num
    linarith
  exact (ENNReal.toReal_le_toReal (c.errorProb_ne_top W' m)
    (ENNReal.mul_ne_top (by simp) (c.errorProb_ne_top W m))).1 hr

theorem twinCode_avgError_le [Fintype M₁] [Fintype M₂] (c : BCCode M₁ M₂ A B₁ B₂ n)
    {W W' : DMC A (B₁ × B₂)} (h₁ : channel₁ W' = channel₁ W) (h₂ : channel₂ W' = channel₂ W) :
    (twinCode c).avgError W' ≤ 2 * c.avgError W := by
  rw [BlockCode.avgError, BCCode.avgError, Fintype.card_prod, Nat.cast_mul, ← mul_div_assoc,
    Finset.mul_sum]
  exact ENNReal.div_le_div_right (Finset.sum_le_sum fun m _ => twinCode_errorProb_le c h₁ h₂ m) _

end Error

def padPrefix {S : Type*} {n : ℕ} (y : Fin n → S) (q : Fin n) (d : S) : Fin n → S :=
  fun j => if h : (j : ℕ) < q then seqPrefix y q ⟨j, h⟩ else d

theorem padPrefix_injective {S : Type*} {n : ℕ} (q : Fin n) (d : S) :
    Function.Injective fun p : Fin q → S => fun j : Fin n =>
      if h : (j : ℕ) < q then p ⟨j, h⟩ else d := by
  intro p p' h
  funext j
  have := congrFun h ⟨j, j.2.trans q.2⟩
  simpa using this

private lemma padPrefix_eq_iff {S : Type*} {n : ℕ} (z : Fin n → S) (q : Fin n) (d : S)
    (a : Fin n → S) :
    padPrefix z q d = a ↔ ∀ j : Fin n, (if (j : ℕ) < q then z j else d) = a j := by
  simp only [funext_iff, padPrefix, seqPrefix]
  refine forall_congr' fun j => ?_
  by_cases h : (j : ℕ) < q <;> simp [h]

theorem sum_padPrefix {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ} (g : Fin n → S → ℝ≥0∞)
    (hg : ∀ j, ∑ b, g j b = 1) (q : Fin n) (d : S) (a : Fin n → S) (y : S) :
    ∑ z : Fin n → S, (if padPrefix z q d = a ∧ z q = y then ∏ j, g j (z j) else 0) =
      g q y * ∑ z : Fin n → S, (if padPrefix z q d = a then ∏ j, g j (z j) else 0) := by
  classical
  have e1 : ∀ z : Fin n → S, (if padPrefix z q d = a ∧ z q = y then ∏ j, g j (z j) else 0) =
      ∏ j : Fin n, (if (if (j : ℕ) < q then z j else d) = a j ∧ (j = q → z j = y)
        then g j (z j) else 0) := by
    intro z
    rw [Fintype.prod_ite_zero]
    congr 1
    rw [padPrefix_eq_iff]
    exact propext ⟨fun h j => ⟨h.1 j, fun hj => hj ▸ h.2⟩, fun h => ⟨fun j => (h j).1, (h q).2 rfl⟩⟩
  have e2 : ∀ z : Fin n → S, (if padPrefix z q d = a then ∏ j, g j (z j) else 0) =
      ∏ j : Fin n, (if (if (j : ℕ) < q then z j else d) = a j
        then g j (z j) else 0) := by
    intro z
    rw [Fintype.prod_ite_zero]
    congr 1
    rw [padPrefix_eq_iff]
  simp_rw [e1, e2]
  rw [← Fintype.prod_sum (fun (j : Fin n) (b : S) => if (if (j : ℕ) < q then b else d) = a j ∧
      (j = q → b = y) then g j b else 0),
    ← Fintype.prod_sum (fun (j : Fin n) (b : S) => if (if (j : ℕ) < q then b else d) = a j
      then g j b else 0),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ q),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
  have hrest : ∏ j ∈ Finset.univ.erase q, (∑ b, if (if (j : ℕ) < q then b else d) = a j ∧
      (j = q → b = y) then g j b else 0) =
      ∏ j ∈ Finset.univ.erase q, (∑ b, if (if (j : ℕ) < q then b else d) = a j
        then g j b else 0) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjq : j ≠ q := Finset.ne_of_mem_erase hj
    simp [hjq]
  rw [hrest, ← mul_assoc]
  congr 1
  simp only [lt_irrefl, ite_false, true_implies]
  by_cases ha : d = a q
  · simp [ha, hg]
  · simp [ha]

section Letter

variable {M K B : Type*} {n : ℕ} [Fintype M] [Nonempty M] [Fintype B]

theorem sum_codeMass (c : BlockCode M A B n) (W : DMC A B) :
    ∑ ω : M × (Fin n → B), (Fintype.card M : ℝ≥0∞)⁻¹ * W.blockProb (c.enc ω.1) ω.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, DMC.sum_blockProb_eq_one, mul_one]
  exact sum_inv_card M

noncomputable def codePMF (c : BlockCode M A B n) (W : DMC A B) : PMF (M × (Fin n → B)) :=
  PMF.ofFintype _ (sum_codeMass c W)

theorem codeMeasure_eq [MeasurableSpace M] [MeasurableSpace B] (c : BlockCode M A B n)
    (W : DMC A B) : c.codeMeasure W = (codePMF c W).toMeasure := rfl

noncomputable def letterPMF (c : BlockCode M A B n) (W : DMC A B) (κ : M → K) (q : Fin n) (d : B) :
    PMF ((K × (Fin n → B)) × A × B) :=
  (codePMF c W).map fun ω => ((κ ω.1, padPrefix ω.2 q d), c.enc ω.1 q, ω.2 q)

theorem letterPMF_apply (c : BlockCode M A B n)
    (W : DMC A B) (κ : M → K) (q : Fin n) (d : B) (u : K × (Fin n → B)) (x : A) (y : B) :
    letterPMF c W κ q d (u, x, y) =
      ((letterPMF c W κ q d).map fun ω => (ω.1, ω.2.1)) (u, x) * W x y := by
  classical
  rw [letterPMF, PMF.map_comp, PMF.map_apply, PMF.map_apply, tsum_fintype, tsum_fintype,
    Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [codePMF, PMF.ofFintype_apply, Function.comp_def]
  by_cases hm : κ m = u.1 ∧ c.enc m q = x
  · obtain ⟨u₁, u₂⟩ := u
    obtain ⟨h1, rfl⟩ := hm
    subst h1
    have e1 : ∀ (z : Fin n → B) [Decidable (((κ m, u₂), c.enc m q, y) =
        ((κ m, padPrefix z q d), c.enc m q, z q))], (if ((κ m, u₂), c.enc m q, y) =
        ((κ m, padPrefix z q d), c.enc m q, z q) then (Fintype.card M : ℝ≥0∞)⁻¹ *
          W.blockProb (c.enc m) z else 0) = (Fintype.card M : ℝ≥0∞)⁻¹ *
        (if padPrefix z q d = u₂ ∧ z q = y then ∏ j, W (c.enc m j) (z j) else 0) := by
      intro z _
      by_cases h : padPrefix z q d = u₂ ∧ z q = y
      · simp [h, DMC.blockProb]
      · have : ((κ m, u₂), c.enc m q, y) ≠ ((κ m, padPrefix z q d), c.enc m q, z q) := by
          intro h'
          simp only [Prod.mk.injEq] at h'
          exact h ⟨h'.1.2.symm, h'.2.2.symm⟩
        simp [h, this]
    have e2 : ∀ (z : Fin n → B) [Decidable (((κ m, u₂), c.enc m q) =
        ((κ m, padPrefix z q d), c.enc m q))], (if ((κ m, u₂), c.enc m q) =
        ((κ m, padPrefix z q d), c.enc m q) then (Fintype.card M : ℝ≥0∞)⁻¹ *
          W.blockProb (c.enc m) z else 0) = (Fintype.card M : ℝ≥0∞)⁻¹ *
        (if padPrefix z q d = u₂ then ∏ j, W (c.enc m j) (z j) else 0) := by
      intro z _
      by_cases h : padPrefix z q d = u₂
      · simp [h, DMC.blockProb]
      · have : ((κ m, u₂), c.enc m q) ≠ ((κ m, padPrefix z q d), c.enc m q) := by
          intro h'
          simp only [Prod.mk.injEq] at h'
          exact h h'.1.2.symm
        simp [h, this]
    simp_rw [e1, e2]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_padPrefix (fun j b => W (c.enc m j) b)
      (fun j => sum_pmf_eq_one _) q d u₂ y]
    ring
  · have e1 : ∀ (z : Fin n → B) [Decidable ((u, x, y) = ((κ m, padPrefix z q d), c.enc m q, z q))],
        (if (u, x, y) = ((κ m, padPrefix z q d), c.enc m q, z q) then
        (Fintype.card M : ℝ≥0∞)⁻¹ * W.blockProb (c.enc m) z else 0) = 0 := fun z _ => by
      refine ite_eq_right_iff.2 fun h => absurd ?_ hm
      simp only [Prod.mk.injEq] at h
      exact ⟨(congrArg Prod.fst h.1).symm, h.2.1.symm⟩
    have e2 : ∀ (z : Fin n → B) [Decidable ((u, x) = ((κ m, padPrefix z q d), c.enc m q))],
        (if (u, x) = ((κ m, padPrefix z q d), c.enc m q) then
        (Fintype.card M : ℝ≥0∞)⁻¹ * W.blockProb (c.enc m) z else 0) = 0 := fun z _ => by
      refine ite_eq_right_iff.2 fun h => absurd ?_ hm
      simp only [Prod.mk.injEq] at h
      exact ⟨(congrArg Prod.fst h.1).symm, h.2.symm⟩
    simp_rw [e1, e2]
    simp

end Letter

noncomputable def unifPMF (n : ℕ) [NeZero n] : PMF (Fin n) :=
  PMF.ofFintype (fun _ => (Fintype.card (Fin n) : ℝ≥0∞)⁻¹) (sum_inv_card (Fin n))

section Mixture

variable {R S T : Type*} [Finite R] [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {n : ℕ} [NeZero n]

theorem entropy_mixture (L : Fin n → PMF R) (Z : R → T) :
    H[fun p : Fin n × R => (p.1, Z p.2) ; (DMC.jointPMF L (unifPMF n)).toMeasure] =
      Real.log n + (n : ℝ)⁻¹ * ∑ q, H[Z ; (L q).toMeasure] := by
  have hmap : (DMC.jointPMF L (unifPMF n)).map (fun p : Fin n × R => (p.1, Z p.2)) =
      DMC.jointPMF (fun q => (L q).map Z) (unifPMF n) := by
    simp only [DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  rw [entropy_def]
  simp_rw [measureReal_map_toMeasure]
  rw [hmap]
  simp only [entropy_def, measureReal_map_toMeasure, Fintype.sum_prod_type,
    DMC.jointPMF_apply, unifPMF, PMF.ofFintype_apply, Fintype.card_fin, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  have h1 : ∀ q, ∑ t, ((L q).map Z t).toReal = 1 := fun q => by
    rw [← ENNReal.toReal_sum fun t _ => PMF.apply_ne_top _ _, sum_pmf_eq_one, ENNReal.toReal_one]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Real.negMulLog, Real.log_inv]
  field_simp

theorem condEntropy_mixture (L : Fin n → PMF R) (F : R → S) (G : R → T) :
    H[fun p : Fin n × R => F p.2 | fun p => (p.1, G p.2) ;
        (DMC.jointPMF L (unifPMF n)).toMeasure] =
      (n : ℝ)⁻¹ * ∑ q, H[F | G ; (L q).toMeasure] := by
  have e : H[fun p : Fin n × R => (F p.2, (p.1, G p.2)) ;
      (DMC.jointPMF L (unifPMF n)).toMeasure] =
      H[fun p : Fin n × R => (p.1, (fun r => (F r, G r)) p.2) ;
        (DMC.jointPMF L (unifPMF n)).toMeasure] :=
    entropy_comp_of_injective _ (X := fun p : Fin n × R => (p.1, (F p.2, G p.2)))
      (f := fun t => (t.2.1, (t.1, t.2.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)
  rw [condEntropy_def, e, entropy_mixture L (fun r => (F r, G r)), entropy_mixture L G]
  simp only [condEntropy_def, Finset.sum_sub_distrib]
  ring

theorem entropy_mixture_ge (L : Fin n → PMF R) (F : R → S) :
    (n : ℝ)⁻¹ * ∑ q, H[F ; (L q).toMeasure] ≤
      H[fun p : Fin n × R => F p.2 ; (DMC.jointPMF L (unifPMF n)).toMeasure] := by
  have hc : ∀ (μ : Measure R) [IsProbabilityMeasure μ], H[F | fun _ => () ; μ] = H[F ; μ] := by
    intro μ _
    have h1 : H[fun r => (F r, ()) ; μ] = H[F ; μ] :=
      entropy_comp_of_injective μ (X := F) (f := fun y => (y, ())) fun a b h => congrArg Prod.fst h
    have h2 : H[fun _ : R => () ; μ] = 0 := by
      have := entropy_le_log_card μ (X := fun _ : R => ())
      simp only [Fintype.card_unit, Nat.cast_one, Real.log_one] at this
      exact le_antisymm this (entropy_nonneg μ _)
    rw [condEntropy_def, h1, h2, sub_zero]
  have h := condEntropy_mixture L F (fun _ => ())
  simp only [hc] at h
  rw [← h]
  exact condEntropy_le_entropy _ (measurable_of_finite _) (measurable_of_finite _)

end Mixture

section Markov

variable {Ω S T U : Type*} [Finite Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]

private lemma measureReal_setOf {V : Type*} [MeasurableSpace V]
    [MeasurableSingletonClass V] (σ : PMF Ω) (F : Ω → V) (v : V) :
    σ.toMeasure.real {ω | F ω = v} = (σ.map F v).toReal := by
  rw [← measureReal_map_toMeasure, map_measureReal_apply (measurable_of_finite _)
    (measurableSet_singleton _)]
  rfl

theorem markovChain_of_pmf (σ : PMF Ω) (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (κ : T → U → ℝ≥0∞)
    (h : ∀ x y z, σ.map (fun ω => (X ω, Y ω, Z ω)) (x, y, z) =
      σ.map (fun ω => (X ω, Y ω)) (x, y) * κ y z) :
    MarkovChain X Y Z σ.toMeasure := by
  rw [markovChain_iff (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  have e3 : ∀ x y z, σ.toMeasure.real {ω | X ω = x ∧ Y ω = y ∧ Z ω = z} =
      (σ.map (fun ω => (X ω, Y ω, Z ω)) (x, y, z)).toReal := fun x y z => by
    rw [← measureReal_setOf]
    congr 1
    ext ω
    simp [Prod.ext_iff]
  have e2 : ∀ x y, σ.toMeasure.real {ω | X ω = x ∧ Y ω = y} =
      (σ.map (fun ω => (X ω, Y ω)) (x, y)).toReal := fun x y => by
    rw [← measureReal_setOf]
    congr 1
    ext ω
    simp [Prod.ext_iff]
  intro x y z
  have s1 : ∑ x', σ.toMeasure.real {ω | X ω = x' ∧ Y ω = y ∧ Z ω = z} =
      σ.toMeasure.real {ω | Y ω = y ∧ Z ω = z} := sum_measureReal_inter (measurable_of_finite _) _
  have s2 : ∑ x', σ.toMeasure.real {ω | X ω = x' ∧ Y ω = y} = σ.toMeasure.real {ω | Y ω = y} :=
    sum_measureReal_inter (measurable_of_finite _) _
  have f : ∀ x', σ.toMeasure.real {ω | X ω = x' ∧ Y ω = y ∧ Z ω = z} =
      σ.toMeasure.real {ω | X ω = x' ∧ Y ω = y} * (κ y z).toReal := fun x' => by
    rw [e3, e2, h, ENNReal.toReal_mul]
  rw [← s1, ← s2, f x]
  simp_rw [f, ← Finset.sum_mul]
  ring

end Markov


section Factor

theorem jointPMF_eq_map (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    jointPMF W pU pX = (DMC.jointPMF (fun ua : V × A => W ua.2) (DMC.jointPMF pX pU)).map
      fun p => (p.1.1, p.1.2, p.2) := by
  simp only [jointPMF, DMC.jointPMF, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

theorem jointPMF_apply' (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) (u : V) (x : A)
    (y : B₁ × B₂) : jointPMF W pU pX (u, x, y) = pU u * pX u x * W x y := by
  rw [jointPMF_eq_map, show ((u, x, y) : V × A × B₁ × B₂) =
      (fun p : (V × A) × B₁ × B₂ => (p.1.1, p.1.2, p.2)) ((u, x), y) from rfl,
    map_apply_inj _ (fun p p' h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2), DMC.jointPMF_apply, DMC.jointPMF_apply]

theorem jointPMF_map_input (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) :
    (jointPMF W pU pX).map (fun ω => (ω.1, ω.2.1)) = DMC.jointPMF pX pU := by
  rw [jointPMF_eq_map, PMF.map_comp]
  exact DMC.jointPMF_map_fst _ _

theorem exists_jointPMF_eq [Finite V] [Finite A] (W : DMC A (B₁ × B₂))
    (σ : PMF (V × A × B₁ × B₂))
    (h : ∀ v x y, σ (v, x, y) = (σ.map fun ω => (ω.1, ω.2.1)) (v, x) * W x y) :
    ∃ (pU : PMF V) (pX : V → PMF A), jointPMF W pU pX = σ := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite A
  set τ := σ.map fun ω => (ω.1, ω.2.1) with hτdef
  have hτ : ∀ v, (τ.map Prod.fst) v = ∑ x, τ (v, x) := by
    intro v
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
    simp only
    rw [Finset.sum_eq_single v (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  have hsum : ∀ v, (τ.map Prod.fst) v ≠ 0 → ∑ x, τ (v, x) / (τ.map Prod.fst) v = 1 := by
    intro v hv
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← hτ]
    exact ENNReal.mul_inv_cancel hv (PMF.apply_ne_top _ _)
  let pX : V → PMF A := fun v => if hv : (τ.map Prod.fst) v = 0 then τ.map Prod.snd
    else PMF.ofFintype (fun x => τ (v, x) / (τ.map Prod.fst) v) (hsum v hv)
  have hfac : ∀ v x, τ (v, x) = (τ.map Prod.fst) v * pX v x := by
    intro v x
    by_cases hv : (τ.map Prod.fst) v = 0
    · have hle : τ (v, x) ≤ (τ.map Prod.fst) v := by
        rw [hτ]
        exact Finset.single_le_sum (f := fun x => τ (v, x)) (fun _ _ => zero_le)
          (Finset.mem_univ x)
      rw [hv] at hle
      rw [hv, zero_mul]
      exact le_zero_iff.1 hle
    · simp only [pX, hv, dite_false, PMF.ofFintype_apply]
      rw [div_eq_mul_inv, mul_comm (τ _), ← mul_assoc,
        ENNReal.mul_inv_cancel hv (PMF.apply_ne_top _ _), one_mul]
  refine ⟨τ.map Prod.fst, pX, ?_⟩
  ext ⟨v, x, y⟩
  rw [jointPMF_apply', h, ← hfac]

theorem markovChain_of_memoryless [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
    [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
    [MeasurableSingletonClass B₂] (W : DMC A (B₁ × B₂)) (σ : PMF (V × A × B₁ × B₂))
    (h : ∀ v x y, σ (v, x, y) = (σ.map fun ω => (ω.1, ω.2.1)) (v, x) * W x y) :
    MarkovChain (fun ω : V × A × B₁ × B₂ => ω.1) (fun ω => ω.2.1) (fun ω => ω.2.2)
      σ.toMeasure := by
  refine markovChain_of_pmf σ _ _ _ (fun x y => W x y) fun v x y => ?_
  rw [← h]
  exact congrFun (congrArg DFunLike.coe (PMF.map_id σ)) _

end Factor

section Degraded

theorem degradedTwin_apply (W : DMC A (B₁ × B₂)) (D : DMC B₁ B₂) (x : A) (y₁ : B₁) (y₂ : B₂) :
    degradedTwin W D x (y₁, y₂) = channel₁ W x y₁ * D y₁ y₂ := by
  classical
  rw [degradedTwin, PMF.bind_apply, tsum_eq_single y₁ fun a ha => by
    rw [PMF.map_apply, ENNReal.tsum_eq_zero.2 fun b => by simp [Ne.symm ha], mul_zero]]
  congr 1
  exact map_apply_inj (D y₁) (f := fun y₂ => (y₁, y₂)) (fun a b h => congrArg Prod.snd h) y₂

theorem jointPMF_memoryless (W : DMC A (B₁ × B₂)) (pU : PMF V) (pX : V → PMF A) (v : V) (x : A)
    (y : B₁ × B₂) :
    jointPMF W pU pX (v, x, y) = ((jointPMF W pU pX).map fun ω => (ω.1, ω.2.1)) (v, x) * W x y := by
  rw [jointPMF_map_input, DMC.jointPMF_apply, jointPMF_apply']

variable [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂]

theorem sum_le_of_degradedTwin (W : DMC A (B₁ × B₂)) (D : DMC B₁ B₂) (pU : PMF V)
    (pX : V → PMF A) :
    I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
        jointMeasure (degradedTwin W D) pU pX] +
      I[fun ω : V × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ;
        jointMeasure (degradedTwin W D) pU pX] ≤
      I[fun ω : V × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 ;
        jointMeasure (degradedTwin W D) pU pX] := by
  set W' := degradedTwin W D
  set σ := jointPMF W' pU pX
  have hν : jointMeasure W' pU pX = σ.toMeasure := rfl
  rw [hν]
  have h1 := markovChain_of_memoryless W' σ (jointPMF_memoryless W' pU pX)
  rw [markovChain_def] at h1
  have h1' : I[fun ω : V × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.1 | fun ω => ω.2.1 ;
      σ.toMeasure] = 0 := le_antisymm
    ((condMutualInfo_comp_right_le (μ := σ.toMeasure) (X := fun ω : V × A × B₁ × B₂ => ω.1)
      (Y := fun ω => ω.2.2) (Z := fun ω => ω.2.1) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _) Prod.fst).trans_eq h1)
    (condMutualInfo_nonneg _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _))
  have h2 : MarkovChain (fun ω : V × A × B₁ × B₂ => (ω.1, ω.2.1)) (fun ω => ω.2.2.1)
      (fun ω => ω.2.2.2) σ.toMeasure := by
    refine markovChain_of_pmf σ _ _ _ (fun y₁ y₂ => D y₁ y₂) fun ux y₁ y₂ => ?_
    obtain ⟨u, x⟩ := ux
    have hl : σ.map (fun ω => ((ω.1, ω.2.1), ω.2.2.1)) = law₁ W' pU pX := (law₁_eq_map _ _ _).symm
    rw [hl, show (((u, x), y₁, y₂) : (V × A) × B₁ × B₂) =
        (fun ω : V × A × B₁ × B₂ => ((ω.1, ω.2.1), ω.2.2.1, ω.2.2.2)) (u, x, y₁, y₂) from rfl,
      map_apply_inj _ (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.1 (Prod.ext h.1.2 (Prod.ext h.2.1 h.2.2))),
      jointPMF_apply', law₁, DMC.jointPMF_apply, DMC.jointPMF_apply, channel₁_degradedTwin,
      degradedTwin_apply]
    ring
  rw [markovChain_def] at h2
  have h2' : MarkovChain (fun ω : V × A × B₁ × B₂ => ω.1) (fun ω => ω.2.2.1)
      (fun ω => ω.2.2.2) σ.toMeasure := le_antisymm
    ((condMutualInfo_comp_left_le (μ := σ.toMeasure)
      (X := fun ω : V × A × B₁ × B₂ => (ω.1, ω.2.1)) (Y := fun ω => ω.2.2.2)
      (Z := fun ω => ω.2.2.1) (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) Prod.fst).trans_eq h2)
    (condMutualInfo_nonneg _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _))
  have h3 := h2'.mutualInfo_le_left (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)
  have e1 := mutualInfo_pair_eq_add_condMutualInfo σ.toMeasure
    (X := fun ω : V × A × B₁ × B₂ => ω.2.2.1) (Y := fun ω => ω.2.1) (Z := fun ω => ω.1)
  have e2 := mutualInfo_pair_eq_add_condMutualInfo σ.toMeasure
    (X := fun ω : V × A × B₁ × B₂ => ω.2.2.1) (Y := fun ω => ω.1) (Z := fun ω => ω.2.1)
  have e3 : I[fun ω : V × A × B₁ × B₂ => ω.2.2.1 : fun ω => (ω.2.1, ω.1) ; σ.toMeasure] =
      I[fun ω : V × A × B₁ × B₂ => ω.2.2.1 : fun ω => (ω.1, ω.2.1) ; σ.toMeasure] :=
    mutualInfo_comp_right_of_injective σ.toMeasure (Y := fun ω : V × A × B₁ × B₂ => (ω.1, ω.2.1))
      (f := Prod.swap) Prod.swap_injective
  rw [condMutualInfo_comm] at h1'
  rw [mutualInfo_comm σ.toMeasure (X := fun ω : V × A × B₁ × B₂ => ω.2.1),
    condMutualInfo_comm σ.toMeasure (X := fun ω : V × A × B₁ × B₂ => ω.2.1)]
  rw [mutualInfo_comm σ.toMeasure (X := fun ω : V × A × B₁ × B₂ => ω.1)] at h3 ⊢
  rw [mutualInfo_comm σ.toMeasure (X := fun ω : V × A × B₁ × B₂ => ω.1)] at h3
  linarith

end Degraded

section Letters

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂]

theorem condEntropy_twin_letter (W : DMC A (B₁ × B₂)) (D : DMC B₁ B₂) (p : PMF A) :
    H[fun ω : A × B₁ × B₂ => ω.2.2 | fun ω => (ω.2.1, ω.1) ;
        (degradedTwin W D).jointMeasure p] =
      H[fun ω : A × B₁ × B₂ => ω.2.2 | fun ω => ω.2.1 ; (degradedTwin W D).jointMeasure p] := by
  set σ := DMC.jointPMF (degradedTwin W D) p
  have hν : (degradedTwin W D).jointMeasure p = σ.toMeasure := rfl
  rw [hν]
  have hm : MarkovChain (fun ω : A × B₁ × B₂ => ω.1) (fun ω => ω.2.1) (fun ω => ω.2.2)
      σ.toMeasure := by
    refine markovChain_of_pmf σ _ _ _ (fun y₁ y₂ => D y₁ y₂) fun x y₁ y₂ => ?_
    have h1 : σ.map (fun ω : A × B₁ × B₂ => (ω.1, ω.2.1, ω.2.2)) = σ := PMF.map_id σ
    have h2 : σ.map (fun ω : A × B₁ × B₂ => (ω.1, ω.2.1)) =
        DMC.jointPMF (channel₁ (degradedTwin W D)) p := by
      simp only [σ, DMC.jointPMF, channel₁, PMF.map_bind, PMF.map_comp, Function.comp_def]
    rw [h1, h2, DMC.jointPMF_apply, DMC.jointPMF_apply, degradedTwin_apply,
      channel₁_degradedTwin, mul_assoc]
  rw [markovChain_def, condMutualInfo_eq_condEntropy_sub_condEntropy] at hm
  rw [condEntropy_cond_of_injective σ.toMeasure (Z := fun ω : A × B₁ × B₂ => (ω.1, ω.2.1))
    (Z' := fun ω => (ω.2.1, ω.1)) (e := Prod.swap) Prod.swap_injective fun ω => rfl]
  linarith

variable {M₁ M₂ : Type*} [Fintype M₁] [Nonempty M₁] [MeasurableSpace M₁]
  [MeasurableSingletonClass M₁] [Fintype M₂] [Nonempty M₂] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] {n : ℕ}

omit [Fintype A] [MeasurableSingletonClass A] in
theorem letterPMF_toMeasure (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (q : Fin n) (d : B₁ × B₂) :
    (letterPMF c W Prod.snd q d).toMeasure = (c.codeMeasure W).map
      fun ω => ((ω.1.2, padPrefix ω.2 q d), c.enc ω.1 q, ω.2 q) :=
  (PMF.toMeasure_map _ _ (measurable_of_finite _)).symm

theorem letter_bound₁ (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (D : DMC B₁ B₂) (q : Fin n) (d : B₁ × B₂) :
    H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2 q | fun ω => (ω.1.2, padPrefix ω.2 q d) ;
        c.codeMeasure (degradedTwin W D)] -
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2 q | fun ω => c.enc ω.1 q ;
        c.codeMeasure (degradedTwin W D)] ≤
      I[fun ω : ((M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂) => ω.2.1 :
        fun ω => ω.2.2.1 | fun ω => ω.1 ;
        (letterPMF c (degradedTwin W D) Prod.snd q d).toMeasure] := by
  classical
  set W' := degradedTwin W D
  set μ := c.codeMeasure W'
  set L := letterPMF c W' Prod.snd q d
  have hmem := markovChain_of_memoryless W' L (letterPMF_apply c W' Prod.snd q d)
  rw [markovChain_def] at hmem
  have hm0 : I[fun ω : ((M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂) => ω.1 :
      fun ω => ω.2.2.1 | fun ω => ω.2.1 ; L.toMeasure] = 0 := le_antisymm
    ((condMutualInfo_comp_right_le (μ := L.toMeasure) (X := fun ω => ω.1)
      (Y := fun ω => ω.2.2) (Z := fun ω => ω.2.1) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _) Prod.fst).trans_eq hmem)
    (condMutualInfo_nonneg _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _))
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy] at hm0
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy]
  have hμ : IsProbabilityMeasure μ := BlockCode.isProbabilityMeasure_codeMeasure c W'
  have hL : L.toMeasure = μ.map fun ω => ((ω.1.2, padPrefix ω.2 q d), c.enc ω.1 q, ω.2 q) :=
    letterPMF_toMeasure c W' q d
  have t1 : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2 q |
      fun ω => (ω.1.2, padPrefix ω.2 q d) ; μ] =
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).1 |
        fun ω => (ω.1.2, padPrefix ω.2 q d) ; μ] +
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 |
        fun ω => ((ω.2 q).1, (ω.1.2, padPrefix ω.2 q d)) ; μ] :=
    condEntropy_pair_eq_add μ
  have t2 := condEntropy_le_condEntropy_comp (μ := μ)
    (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2)
    (Y := fun ω => ((ω.2 q).1, (ω.1.2, padPrefix ω.2 q d))) (measurable_of_finite _)
    (measurable_of_finite _) Prod.fst
  have t3 : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2 q | fun ω => c.enc ω.1 q ; μ] =
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).1 | fun ω => c.enc ω.1 q ; μ] +
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 |
        fun ω => ((ω.2 q).1, c.enc ω.1 q) ; μ] :=
    condEntropy_pair_eq_add μ
  have t4 : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 |
      fun ω => ((ω.2 q).1, c.enc ω.1 q) ; μ] =
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 | fun ω => (ω.2 q).1 ; μ] := by
    have h := condEntropy_twin_letter W D (c.inputLaw q)
    rw [← BlockCode.map_codeMeasure c W' q,
      condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
      condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _)
        (measurable_of_finite _)] at h
    exact h
  have t5 : H[fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.2.2.1 | fun ω => ω.1 ;
      L.toMeasure] = H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).1 |
        fun ω => (ω.1.2, padPrefix ω.2 q d) ; μ] := by
    rw [hL, condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
    rfl
  have t6 : H[fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.2.2.1 | fun ω => ω.2.1 ;
      L.toMeasure] = H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).1 |
        fun ω => c.enc ω.1 q ; μ] := by
    rw [hL, condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
    rfl
  have t7 : H[fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.2.2.1 |
      fun ω => (ω.2.1, ω.1) ; L.toMeasure] =
      H[fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.2.2.1 |
        fun ω => (ω.1, ω.2.1) ; L.toMeasure] :=
    condEntropy_cond_of_injective L.toMeasure
      (Z := fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => (ω.1, ω.2.1))
      (Z' := fun ω => (ω.2.1, ω.1)) (e := Prod.swap) Prod.swap_injective fun ω => rfl
  change _ ≤ _ - H[fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.2.2.1 |
      fun ω => (ω.2.1, ω.1) ; L.toMeasure]
  have t2' : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 |
      fun ω => ((ω.2 q).1, (ω.1.2, padPrefix ω.2 q d)) ; μ] ≤
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 | fun ω => (ω.2 q).1 ; μ] := t2
  linarith

omit [Fintype A] in
theorem letter_eq₂ [Finite A] (c : BlockCode (M₁ × M₂) A (B₁ × B₂) n) (W : DMC A (B₁ × B₂))
    (q : Fin n) (d : B₁ × B₂) :
    I[fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ;
        (letterPMF c W Prod.snd q d).toMeasure] =
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 ; c.codeMeasure W] -
        H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 |
          fun ω => (ω.1.2, padPrefix ω.2 q d) ; c.codeMeasure W] := by
  rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy, letterPMF_toMeasure,
    entropy_map _ (measurable_of_finite _) (measurable_of_finite _),
    condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  rfl

end Letters

theorem condEntropy_seq_pad {M S T : Type*} {n : ℕ} [Fintype M] [MeasurableSpace M]
    [MeasurableSingletonClass M] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] {K : Type*}
    [MeasurableSpace K] (μ : Measure (K × (Fin n → S)))
    (κ : K → M) (F : K × (Fin n → S) → T) (q : Fin n) (d : S) :
    H[F | fun ω => (κ ω.1, seqPrefix ω.2 q) ; μ] =
      H[F | fun ω => (κ ω.1, padPrefix ω.2 q d) ; μ] :=
  (condEntropy_cond_of_injective μ (Z := fun ω => (κ ω.1, seqPrefix ω.2 q))
    (Z' := fun ω => (κ ω.1, padPrefix ω.2 q d))
    (e := Prod.map id fun p : Fin q → S => fun j : Fin n =>
      if h : (j : ℕ) < q then p ⟨j, h⟩ else d)
    (Function.injective_id.prodMap (padPrefix_injective q d)) fun _ => rfl).symm

section Code

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂]
  {M₁ M₂ : Type*} [Fintype M₁] [Nonempty M₁] [MeasurableSpace M₁]
  [MeasurableSingletonClass M₁] [DecidableEq M₁] [Fintype M₂] [Nonempty M₂] [MeasurableSpace M₂]
  [MeasurableSingletonClass M₂] [DecidableEq M₂] {n : ℕ}

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private lemma error_le (W : DMC A (B₁ × B₂)) (D : DMC B₁ B₂)
    (hD : ∀ a, channel₂ W a = (channel₁ W a).bind D) (c : BCCode M₁ M₂ A B₁ B₂ n)
    (P : (M₁ × M₂) × (Fin n → B₁ × B₂) → Prop)
    (hP : ∀ ω, P ω → (twinCode c).dec ω.2 ≠ ω.1) :
    ((twinCode c).codeMeasure (degradedTwin W D)).real {ω | P ω} ≤
      2 * (c.avgError W).toReal := by
  have hne : c.avgError W ≠ ∞ := by
    refine (ENNReal.div_lt_top (ENNReal.sum_ne_top.2 fun m _ => c.errorProb_ne_top W m)
      ?_).ne
    simp [Fintype.card_ne_zero]
  calc _ ≤ ((twinCode c).codeMeasure (degradedTwin W D)).real
        {ω | (twinCode c).dec ω.2 ≠ ω.1} := measureReal_mono fun ω h => hP ω h
    _ = ((twinCode c).avgError (degradedTwin W D)).toReal := BlockCode.measureReal_dec_ne _ _
    _ ≤ (2 * c.avgError W).toReal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hne)
        (twinCode_avgError_le c (channel₁_degradedTwin W D) (channel₂_degradedTwin W D hD))
    _ = 2 * (c.avgError W).toReal := by rw [ENNReal.toReal_mul]; norm_num

theorem code_bounds (W : DMC A (B₁ × B₂)) (D : DMC B₁ B₂)
    (hD : ∀ a, channel₂ W a = (channel₁ W a).bind D) (c : BCCode M₁ M₂ A B₁ B₂ n)
    (d : B₁ × B₂) :
    (1 - 2 * (c.avgError W).toReal) * Real.log (Fintype.card M₁) - Real.log 2 ≤
        ∑ q, I[fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 |
          fun ω => ω.1 ;
          (letterPMF (twinCode c) (degradedTwin W D) Prod.snd q d).toMeasure] ∧
      (1 - 2 * (c.avgError W).toReal) * Real.log (Fintype.card M₂) - Real.log 2 ≤
        ∑ q, I[fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ;
          (letterPMF (twinCode c) (degradedTwin W D) Prod.snd q d).toMeasure] := by
  set W' := degradedTwin W D
  set c' := twinCode c
  set μ := c'.codeMeasure W'
  have hμ : IsProbabilityMeasure μ := BlockCode.isProbabilityMeasure_codeMeasure c' W'
  set ε := (c.avgError W).toReal
  have hH : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.1.1, ω.1.2) ; μ] =
      Real.log (Fintype.card M₁) + Real.log (Fintype.card M₂) := by
    have := BlockCode.entropy_fst_codeMeasure c' W'
    rw [Fintype.card_prod, Nat.cast_mul, Real.log_mul (by simp [Fintype.card_ne_zero])
      (by simp [Fintype.card_ne_zero])] at this
    exact this
  have hsplit := entropy_pair_eq_add_condEntropy
    (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1) (fun ω => ω.1.2) μ
  have hM₂ := entropy_le_log_card μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2)
  have hM₁ := entropy_le_log_card μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1)
  have hM₁₂ := condEntropy_le_entropy μ
    (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1) (Y := fun ω => ω.1.2)
    (measurable_of_finite _) (measurable_of_finite _)
  have hA : Real.log (Fintype.card M₁) ≤
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 | fun ω => ω.1.2 ; μ] := by linarith
  have hB : Real.log (Fintype.card M₂) ≤
      H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2 ; μ] := by linarith
  have hl₁ : 0 ≤ Real.log (Fintype.card M₁) := Real.log_natCast_nonneg _
  have hl₂ : 0 ≤ Real.log (Fintype.card M₂) := Real.log_natCast_nonneg _
  have hF₁ := condEntropy_le_log_two_add_mul_log_card (μ := μ)
    (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1)
    (Y := fun ω => fun i => (ω.2 i).1) (measurable_of_finite _) (measurable_of_finite _) c.dec₁
  have hF₂ := condEntropy_le_log_two_add_mul_log_card (μ := μ)
    (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2)
    (Y := fun ω => fun i => (ω.2 i).2) (measurable_of_finite _) (measurable_of_finite _) c.dec₂
  have hP₁ := error_le W D hD c (fun ω => c.dec₁ (fun i => (ω.2 i).1) ≠ ω.1.1)
    fun ω h h' => h (congrArg Prod.fst h')
  have hP₂ := error_le W D hD c (fun ω => c.dec₂ (fun i => (ω.2 i).2) ≠ ω.1.2)
    fun ω h h' => h (congrArg Prod.snd h')
  have hm₁ : μ.real {ω | c.dec₁ (fun i => (ω.2 i).1) ≠ ω.1.1} * Real.log (Fintype.card M₁) ≤
      2 * ε * Real.log (Fintype.card M₁) := mul_le_mul_of_nonneg_right hP₁ hl₁
  have hm₂ : μ.real {ω | c.dec₂ (fun i => (ω.2 i).2) ≠ ω.1.2} * Real.log (Fintype.card M₂) ≤
      2 * ε * Real.log (Fintype.card M₂) := mul_le_mul_of_nonneg_right hP₂ hl₂
  constructor
  · have e1 := condMutualInfo_eq_condEntropy_sub_condEntropy μ
      (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2) (Y := fun ω => ω.1.1)
      (Z := fun ω => ω.1.2)
    have e2 := condMutualInfo_eq_condEntropy_sub_condEntropy μ
      (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1) (Y := fun ω => ω.2)
      (Z := fun ω => ω.1.2)
    have e12 := condMutualInfo_comm μ
      (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2) (Y := fun ω => ω.1.1)
      (Z := fun ω => ω.1.2)
    have e3 := condEntropy_le_condEntropy_comp (μ := μ)
      (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1) (Y := fun ω => (ω.2, ω.1.2))
      (measurable_of_finite _) (measurable_of_finite _) fun p => fun i => (p.1 i).1
    have e4 : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2 | fun ω => (ω.1.1, ω.1.2) ; μ] =
        ∑ q, H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2 q | fun ω => c.enc ω.1 q ; μ] := by
      have h := BlockCode.condEntropy_snd_fst_codeMeasure c' W'
      refine h.trans (Finset.sum_congr rfl fun q _ => ?_)
      rw [← BlockCode.map_codeMeasure c' W' q,
        condEntropy_map _ (measurable_of_finite _) measurable_snd measurable_fst]
      rfl
    have e5 : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2 | fun ω => ω.1.2 ; μ] =
        ∑ q, H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2 q |
          fun ω => (ω.1.2, padPrefix ω.2 q d) ; μ] := by
      rw [condEntropy_eq_sum]
      exact Finset.sum_congr rfl fun q _ => condEntropy_seq_pad μ Prod.snd _ q d
    have e6 := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => letter_bound₁ c' W D q d
    rw [Finset.sum_sub_distrib] at e6
    have e3' : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 | fun ω => (ω.2, ω.1.2) ; μ] ≤
        H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.1 | fun ω => fun i => (ω.2 i).1 ; μ] :=
      e3
    change _ ≤ ∑ q, I[fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.2.1 :
      fun ω => ω.2.2.1 | fun ω => ω.1 ; (letterPMF c' W' Prod.snd q d).toMeasure]
    have e4' : H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2 | fun ω => (ω.1.1, ω.1.2) ; μ] =
        ∑ q, H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.2 q | fun ω => c'.enc ω.1 q ; μ] := e4
    nlinarith
  · have f1 := mutualInfo_eq_entropy_sub_condEntropy
      (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2) (fun ω => fun i => (ω.2 i).2) μ
    have f2 := mutualInfo_eq_entropy_sub_condEntropy
      (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => fun i => (ω.2 i).2) (fun ω => ω.1.2) μ
    have f12 := mutualInfo_comm μ (X := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => ω.1.2)
      (Y := fun ω => fun i => (ω.2 i).2)
    have f3 := entropy_pi_le_sum μ (Y := fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) =>
      fun i => (ω.2 i).2) fun i => measurable_of_finite _
    have f4 := condEntropy_eq_sum μ (fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) =>
      fun i => (ω.2 i).2) (fun ω => ω.1.2)
    have f5 : ∀ q : Fin n, H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 |
        fun ω => (ω.1.2, padPrefix ω.2 q d) ; μ] ≤
        H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 |
          fun ω => (ω.1.2, seqPrefix (fun i => (ω.2 i).2) q) ; μ] := fun q => by
      rw [← condEntropy_seq_pad μ Prod.snd _ q d]
      exact condEntropy_le_condEntropy_comp (μ := μ) (measurable_of_finite _)
        (measurable_of_finite _) fun p : M₂ × (Fin q → B₁ × B₂) => (p.1, fun j => (p.2 j).2)
    have f6 := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => f5 q
    have f7 : ∑ q, I[fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.1 :
        fun ω => ω.2.2.2 ; (letterPMF c' W' Prod.snd q d).toMeasure] =
        ∑ q, H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 ; μ] -
          ∑ q, H[fun ω : (M₁ × M₂) × (Fin n → B₁ × B₂) => (ω.2 q).2 |
            fun ω => (ω.1.2, padPrefix ω.2 q d) ; μ] := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ => letter_eq₂ c' W' q d
    change _ ≤ ∑ q, I[fun ω : (M₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.1 :
      fun ω => ω.2.2.2 ; (letterPMF c' W' Prod.snd q d).toMeasure]
    rw [f7]
    nlinarith

end Code

section Single

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂] {K : Type*} [Fintype K] [MeasurableSpace K]
  [MeasurableSingletonClass K] {n : ℕ} [NeZero n]

theorem mixture_mem (W : DMC A (B₁ × B₂)) (D : DMC B₁ B₂)
    (hD : ∀ a, channel₂ W a = (channel₁ W a).bind D) (L : Fin n → PMF (K × A × B₁ × B₂))
    (hL : ∀ q u x y, L q (u, x, y) = ((L q).map fun ω => (ω.1, ω.2.1)) (u, x) *
      degradedTwin W D x y)
    {r₁ r₂ : ℝ} (h0₁ : 0 ≤ r₁) (h0₂ : 0 ≤ r₂)
    (h₁ : n * r₁ ≤ ∑ q, I[fun ω : K × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
      (L q).toMeasure])
    (h₂ : n * r₂ ≤ ∑ q, I[fun ω : K × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ; (L q).toMeasure]) :
    (r₁, r₂) ∈ superpositionUnion W := by
  classical
  set W' := degradedTwin W D
  set ρ := DMC.jointPMF L (unifPMF n)
  let φ : Fin n × K × A × B₁ × B₂ → (Fin n × K) × A × B₁ × B₂ :=
    fun p => ((p.1, p.2.1), p.2.2.1, p.2.2.2)
  have hφ : Function.Injective φ := fun a b h => by
    simp only [φ, Prod.mk.injEq] at h
    exact Prod.ext h.1.1 (Prod.ext h.1.2 (Prod.ext h.2.1 h.2.2))
  have hmap : (ρ.map φ).map (fun ω => (ω.1, ω.2.1)) =
      (DMC.jointPMF (fun q => (L q).map fun ω => (ω.1, ω.2.1)) (unifPMF n)).map
        fun p => ((p.1, p.2.1), p.2.2) := by
    simp only [ρ, φ, DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hmem : ∀ v x y, ρ.map φ (v, x, y) = ((ρ.map φ).map fun ω => (ω.1, ω.2.1)) (v, x) *
      W' x y := by
    rintro ⟨q, u⟩ x y
    rw [hmap, show (((q, u), x, y) : (Fin n × K) × A × B₁ × B₂) = φ (q, u, x, y) from rfl,
      map_apply_inj _ hφ, show (((q, u), x) : (Fin n × K) × A) =
        (fun p : Fin n × K × A => ((p.1, p.2.1), p.2.2)) (q, u, x) from rfl,
      map_apply_inj _ (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)),
      DMC.jointPMF_apply, DMC.jointPMF_apply, hL, mul_assoc]
  obtain ⟨pU, pX, hj⟩ := exists_jointPMF_eq W' (ρ.map φ) hmem
  have hν : jointMeasure W' pU pX = ρ.toMeasure.map φ := by
    rw [jointMeasure_eq_toMeasure, hj, PMF.toMeasure_map _ _ (measurable_of_finite _)]
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hI₁ : I[fun ω : (Fin n × K) × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 |
      fun ω => ω.1 ; jointMeasure W' pU pX] = (n : ℝ)⁻¹ * ∑ q,
        I[fun ω : K × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 | fun ω => ω.1 ;
          (L q).toMeasure] := by
    rw [hν, condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _),
      condMutualInfo_eq_condEntropy_sub_condEntropy]
    have a1 := condEntropy_mixture L (fun r : K × A × B₁ × B₂ => r.2.2.1) (fun r => r.1)
    have a2 := condEntropy_mixture L (fun r : K × A × B₁ × B₂ => r.2.2.1) (fun r => (r.2.1, r.1))
    have a3 : H[fun p : Fin n × K × A × B₁ × B₂ => p.2.2.2.1 |
        fun p => (p.2.2.1, (p.1, p.2.1)) ; ρ.toMeasure] =
        H[fun p : Fin n × K × A × B₁ × B₂ => p.2.2.2.1 |
          fun p => (p.1, (p.2.2.1, p.2.1)) ; ρ.toMeasure] :=
      condEntropy_cond_of_injective ρ.toMeasure
        (Z := fun p : Fin n × K × A × B₁ × B₂ => (p.1, (p.2.2.1, p.2.1)))
        (Z' := fun p => (p.2.2.1, (p.1, p.2.1))) (e := fun t => (t.2.1, (t.1, t.2.2)))
        (fun a b h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)) fun _ => rfl
    change H[fun p : Fin n × K × A × B₁ × B₂ => p.2.2.2.1 | fun p => (p.1, p.2.1) ;
      ρ.toMeasure] - H[fun p : Fin n × K × A × B₁ × B₂ => p.2.2.2.1 |
        fun p => (p.2.2.1, (p.1, p.2.1)) ; ρ.toMeasure] = _
    rw [a3, a1, a2, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun q _ =>
      (condMutualInfo_eq_condEntropy_sub_condEntropy _).symm
  have hI₂ : (n : ℝ)⁻¹ * ∑ q, I[fun ω : K × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ;
      (L q).toMeasure] ≤ I[fun ω : (Fin n × K) × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ;
        jointMeasure W' pU pX] := by
    rw [hν, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _), mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
    have b1 := condEntropy_mixture L (fun r : K × A × B₁ × B₂ => r.2.2.2) (fun r => r.1)
    have b2 := entropy_mixture_ge L (fun r : K × A × B₁ × B₂ => r.2.2.2)
    change _ ≤ H[fun p : Fin n × K × A × B₁ × B₂ => p.2.2.2.2 ; ρ.toMeasure] -
      H[fun p : Fin n × K × A × B₁ × B₂ => p.2.2.2.2 | fun p => (p.1, p.2.1) ; ρ.toMeasure]
    rw [b1]
    have : ∑ q, I[fun ω : K × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ; (L q).toMeasure] =
        ∑ q, H[fun r : K × A × B₁ × B₂ => r.2.2.2 ; (L q).toMeasure] -
          ∑ q, H[fun r : K × A × B₁ × B₂ => r.2.2.2 | fun r => r.1 ; (L q).toMeasure] := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ => by
        rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
    rw [this, mul_sub]
    linarith
  have hsum := sum_le_of_degradedTwin W D pU pX
  have hx : r₁ ≤ I[fun ω : (Fin n × K) × A × B₁ × B₂ => ω.2.1 : fun ω => ω.2.2.1 |
      fun ω => ω.1 ; jointMeasure W' pU pX] := by
    rw [hI₁, ← div_eq_inv_mul, le_div_iff₀ hn]
    linarith
  have hy : r₂ ≤ I[fun ω : (Fin n × K) × A × B₁ × B₂ => ω.1 : fun ω => ω.2.2.2 ;
      jointMeasure W' pU pX] := by
    refine le_trans ?_ hI₂
    rw [← div_eq_inv_mul, le_div_iff₀ hn]
    linarith
  have hR : (r₁, r₂) ∈ superpositionRegion W pU pX := by
    rw [superpositionRegion_congr (channel₁_degradedTwin W D).symm
      (channel₂_degradedTwin W D hD).symm]
    exact ⟨h0₁, h0₂, hx, hy, by linarith⟩
  rw [← superpositionRegion_map_equiv W pU pX (Fintype.equivFin (Fin n × K))] at hR
  simp only [superpositionUnion, Set.mem_iUnion]
  exact ⟨_, _, _, hR⟩

end Single

section Theorem

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B₁]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂]

theorem achievableRegion_subset_of_isDegraded {W : DMC A (B₁ × B₂)} (hW : IsDegraded W) :
    achievableRegion W ⊆ closure (superpositionUnion W) := by
  classical
  obtain ⟨D, hD⟩ := hW
  rintro ⟨R₁, R₂⟩ ⟨h0₁, h0₂, hR⟩
  rw [Metric.mem_closure_iff]
  intro δ hδ
  set ε₀ := min (1 / 4) (δ / (4 * (R₁ + R₂ + 1))) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (by norm_num) (by positivity)
  obtain ⟨N, hN⟩ := hR (ENNReal.ofReal ε₀) (ENNReal.ofReal_pos.2 hε₀0)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * Real.log 2 / δ)
  set n := max N (max n₀ 1)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
  have : NeZero n := ⟨by omega⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n (le_max_left _ _)
  have hk₁0 : (0 : ℝ) < k₁ := (Real.exp_pos _).trans_le hk₁
  have hk₂0 : (0 : ℝ) < k₂ := (Real.exp_pos _).trans_le hk₂
  have : Nonempty (Fin k₁) := ⟨⟨0, by exact_mod_cast hk₁0⟩⟩
  have : Nonempty (Fin k₂) := ⟨⟨0, by exact_mod_cast hk₂0⟩⟩
  obtain ⟨d, -⟩ := (W (c.enc (Classical.arbitrary _) ⟨0, by omega⟩)).support_nonempty
  set ε' := (c.avgError W).toReal
  have hε' : ε' ≤ ε₀ := ENNReal.toReal_le_of_le_ofReal hε₀0.le hc
  have hε'0 : 0 ≤ ε' := ENNReal.toReal_nonneg
  have hε'4 : ε' ≤ 1 / 4 := hε'.trans (min_le_left _ _)
  obtain ⟨b₁, b₂⟩ := code_bounds W D hD c d
  simp only [Fintype.card_fin] at b₁ b₂
  have hl₁ : n * R₁ ≤ Real.log k₁ := (Real.le_log_iff_exp_le hk₁0).2 hk₁
  have hl₂ : n * R₂ ≤ Real.log k₂ := (Real.le_log_iff_exp_le hk₂0).2 hk₂
  have hlog2 : Real.log 2 / n < δ / 2 := by
    rw [div_lt_iff₀ hnpos]
    have : (n₀ : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 := (div_lt_iff₀ hδ).1 (hn₀.trans_le this)
    linarith
  have hlog2' : 0 ≤ Real.log 2 / n := div_nonneg (Real.log_nonneg (by norm_num)) hnpos.le
  set r₁ := max 0 ((1 - 2 * ε') * R₁ - Real.log 2 / n)
  set r₂ := max 0 ((1 - 2 * ε') * R₂ - Real.log 2 / n)
  have hS₁ := Finset.sum_nonneg fun q (_ : q ∈ Finset.univ) => condMutualInfo_nonneg
    (letterPMF (twinCode c) (degradedTwin W D) Prod.snd q d).toMeasure
    (X := fun ω : (Fin k₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.2.1) (Y := fun ω => ω.2.2.1)
    (Z := fun ω => ω.1) (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
  have hS₂ := Finset.sum_nonneg fun q (_ : q ∈ Finset.univ) => mutualInfo_nonneg
    (letterPMF (twinCode c) (degradedTwin W D) Prod.snd q d).toMeasure
    (X := fun ω : (Fin k₂ × (Fin n → B₁ × B₂)) × A × B₁ × B₂ => ω.1) (Y := fun ω => ω.2.2.2)
    (measurable_of_finite _) (measurable_of_finite _)
  have hc₁ : (n : ℝ) * ((1 - 2 * ε') * R₁ - Real.log 2 / n) ≤
      (1 - 2 * ε') * Real.log k₁ - Real.log 2 := by
    rw [mul_sub, mul_div_cancel₀ _ hnpos.ne']
    nlinarith
  have hc₂ : (n : ℝ) * ((1 - 2 * ε') * R₂ - Real.log 2 / n) ≤
      (1 - 2 * ε') * Real.log k₂ - Real.log 2 := by
    rw [mul_sub, mul_div_cancel₀ _ hnpos.ne']
    nlinarith
  have hmem := mixture_mem W D hD
    (fun q => letterPMF (twinCode c) (degradedTwin W D) Prod.snd q d)
    (fun q => letterPMF_apply (twinCode c) (degradedTwin W D) Prod.snd q d)
    (le_max_left 0 _) (le_max_left 0 _) (r₁ := r₁) (r₂ := r₂)
    (by rw [mul_max_of_nonneg _ _ hnpos.le, mul_zero]; exact max_le hS₁ (hc₁.trans b₁))
    (by rw [mul_max_of_nonneg _ _ hnpos.le, mul_zero]; exact max_le hS₂ (hc₂.trans b₂))
  refine ⟨(r₁, r₂), hmem, ?_⟩
  have hR4 : ε₀ * (4 * (R₁ + R₂ + 1)) ≤ δ := by
    have := min_le_right (1 / 4 : ℝ) (δ / (4 * (R₁ + R₂ + 1)))
    rw [← hε₀, le_div_iff₀ (by positivity)] at this
    exact this
  have d₁ : |R₁ - r₁| < δ := by
    rw [abs_lt]
    constructor
    · have : r₁ ≤ R₁ := max_le h0₁ (by nlinarith)
      linarith
    · have : (1 - 2 * ε') * R₁ - Real.log 2 / n ≤ r₁ := le_max_right _ _
      nlinarith
  have d₂ : |R₂ - r₂| < δ := by
    rw [abs_lt]
    constructor
    · have : r₂ ≤ R₂ := max_le h0₂ (by nlinarith)
      linarith
    · have : (1 - 2 * ε') * R₂ - Real.log 2 / n ≤ r₂ := le_max_right _ _
      nlinarith
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt d₁ d₂

theorem closure_achievableRegion_eq_of_isDegraded {W : DMC A (B₁ × B₂)} (hW : IsDegraded W) :
    closure (achievableRegion W) = closure (superpositionUnion W) :=
  le_antisymm (closure_minimal (achievableRegion_subset_of_isDegraded hW) isClosed_closure)
    (closure_superpositionUnion_subset W)

end Theorem

end BC

end Meat
