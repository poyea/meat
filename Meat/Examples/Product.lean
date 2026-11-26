import Meat.Examples.Noiseless
import Meat.Channel.ErrorExponent
import Meat.Shannon.Conditional

open MeasureTheory Finset
open scoped ENNReal

namespace Meat.Examples

variable {A₁ A₂ B₁ B₂ : Type*}

noncomputable def prodPMF (p₁ : PMF A₁) (p₂ : PMF A₂) : PMF (A₁ × A₂) :=
  p₁.bind fun a₁ => p₂.map fun a₂ => (a₁, a₂)

noncomputable def prodChannel (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) : DMC (A₁ × A₂) (B₁ × B₂) :=
  fun a => prodPMF (W₁ a.1) (W₂ a.2)

theorem prodPMF_apply (p₁ : PMF A₁) (p₂ : PMF A₂) (a : A₁ × A₂) :
    prodPMF p₁ p₂ a = p₁ a.1 * p₂ a.2 :=
  DMC.jointPMF_apply (fun _ => p₂) p₁ a.1 a.2

theorem map_fst_prodPMF (p₁ : PMF A₁) (p₂ : PMF A₂) : (prodPMF p₁ p₂).map Prod.fst = p₁ :=
  DMC.jointPMF_map_fst (fun _ => p₂) p₁

theorem map_snd_prodPMF (p₁ : PMF A₁) (p₂ : PMF A₂) : (prodPMF p₁ p₂).map Prod.snd = p₂ := by
  simp only [prodPMF, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
  exact PMF.map_id p₂

private lemma map_const' {α β : Type*} (q : PMF α) (c : β) : q.map (fun _ => c) = PMF.pure c :=
  PMF.map_const q c

private lemma jointPMF_map_left (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) (p : PMF (A₁ × A₂)) :
    (DMC.jointPMF (prodChannel W₁ W₂) p).map (fun x => (x.1.1, x.2.1)) =
      DMC.jointPMF W₁ (p.map Prod.fst) := by
  simp only [DMC.jointPMF, prodChannel, prodPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def, map_const']
  rfl

private lemma jointPMF_map_right (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) (p : PMF (A₁ × A₂)) :
    (DMC.jointPMF (prodChannel W₁ W₂) p).map (fun x => (x.1.2, x.2.2)) =
      DMC.jointPMF W₂ (p.map Prod.snd) := by
  simp only [DMC.jointPMF, prodChannel, prodPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def, PMF.bind_const]

private lemma jointPMF_map_out (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    (DMC.jointPMF (prodChannel W₁ W₂) (prodPMF p₁ p₂)).map Prod.snd =
      prodPMF ((DMC.jointPMF W₁ p₁).map Prod.snd) ((DMC.jointPMF W₂ p₂).map Prod.snd) := by
  simp only [DMC.jointPMF, prodChannel, prodPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def, PMF.bind_bind]
  exact congrArg p₁.bind (funext fun a => PMF.bind_comm _ _ _)

section Info

variable [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

omit [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂] in
private lemma map_left [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) (p : PMF (A₁ × A₂)) :
    ((prodChannel W₁ W₂).jointMeasure p).map (fun x => (x.1.1, x.2.1)) =
      W₁.jointMeasure (p.map Prod.fst) := by
  rw [DMC.jointMeasure_eq_toMeasure, DMC.jointMeasure_eq_toMeasure,
    PMF.toMeasure_map _ _ (measurable_of_finite _), jointPMF_map_left]

omit [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂] in
private lemma map_right [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) (p : PMF (A₁ × A₂)) :
    ((prodChannel W₁ W₂).jointMeasure p).map (fun x => (x.1.2, x.2.2)) =
      W₂.jointMeasure (p.map Prod.snd) := by
  rw [DMC.jointMeasure_eq_toMeasure, DMC.jointMeasure_eq_toMeasure,
    PMF.toMeasure_map _ _ (measurable_of_finite _), jointPMF_map_right]

private lemma condEntropy_prod (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) (p : PMF (A₁ × A₂)) :
    H[Prod.snd | Prod.fst ; (prodChannel W₁ W₂).jointMeasure p] =
      H[Prod.snd | Prod.fst ; W₁.jointMeasure (p.map Prod.fst)] +
        H[Prod.snd | Prod.fst ; W₂.jointMeasure (p.map Prod.snd)] := by
  set ν := (prodChannel W₁ W₂).jointMeasure p
  rw [DMC.condEntropy_snd_fst_jointMeasure, DMC.condEntropy_snd_fst_jointMeasure,
    DMC.condEntropy_snd_fst_jointMeasure, ← map_left W₁ W₂ p, ← map_right W₁ W₂ p,
    ← sum_measureReal_mul_comp ν (fun x => (x.1.1, x.2.1)) (fun y => Real.log (W₁ y.1 y.2).toReal),
    ← sum_measureReal_mul_comp ν (fun x => (x.1.2, x.2.2)) (fun y => Real.log (W₂ y.1 y.2).toReal),
    ← neg_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [← mul_add]
  rcases eq_or_ne (ν.real {x}) 0 with h | h
  · rw [h, zero_mul, zero_mul]
  obtain ⟨a, b⟩ := x
  have hx : ν.real {(a, b)} = (p a).toReal * ((W₁ a.1 b.1).toReal * (W₂ a.2 b.2).toReal) := by
    rw [DMC.jointMeasure_real_singleton, prodChannel, prodPMF_apply, ENNReal.toReal_mul]
  rw [hx] at h
  have h1 : (W₁ a.1 b.1).toReal ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have h2 : (W₂ a.2 b.2).toReal ≠ 0 := fun h0 => h (by rw [h0]; ring)
  rw [prodChannel, prodPMF_apply, ENNReal.toReal_mul, Real.log_mul h1 h2]

omit [Fintype A₁] [Fintype A₂] [Fintype B₂] in
private lemma entropy_left [Finite A₁] [Finite A₂] [Finite B₂]
    (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) (p : PMF (A₁ × A₂)) :
    H[fun x : (A₁ × A₂) × (B₁ × B₂) => x.2.1 ; (prodChannel W₁ W₂).jointMeasure p] =
      H[Prod.snd ; W₁.jointMeasure (p.map Prod.fst)] := by
  rw [← map_left W₁ W₂ p, entropy_map _ (measurable_of_finite _) measurable_snd]
  rfl

omit [Fintype A₁] [Fintype A₂] [Fintype B₁] in
private lemma entropy_right [Finite A₁] [Finite A₂] [Finite B₁]
    (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) (p : PMF (A₁ × A₂)) :
    H[fun x : (A₁ × A₂) × (B₁ × B₂) => x.2.2 ; (prodChannel W₁ W₂).jointMeasure p] =
      H[Prod.snd ; W₂.jointMeasure (p.map Prod.snd)] := by
  rw [← map_right W₁ W₂ p, entropy_map _ (measurable_of_finite _) measurable_snd]
  rfl

theorem inputMutualInfo_prodChannel_le (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) (p : PMF (A₁ × A₂)) :
    (prodChannel W₁ W₂).inputMutualInfo p ≤
      W₁.inputMutualInfo (p.map Prod.fst) + W₂.inputMutualInfo (p.map Prod.snd) := by
  have h := entropy_pair_le_add ((prodChannel W₁ W₂).jointMeasure p)
    (X := fun x : (A₁ × A₂) × (B₁ × B₂) => x.2.1) (Y := fun x => x.2.2)
    (measurable_of_finite _) (measurable_of_finite _)
  rw [entropy_left, entropy_right] at h
  rw [inputMutualInfo_eq, inputMutualInfo_eq, inputMutualInfo_eq, condEntropy_prod]
  have e : H[Prod.snd ; (prodChannel W₁ W₂).jointMeasure p] =
      H[fun x : (A₁ × A₂) × (B₁ × B₂) => (x.2.1, x.2.2) ; (prodChannel W₁ W₂).jointMeasure p] :=
    rfl
  linarith

private lemma real_map {α β : Type*} [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] (q : PMF α) (g : α → β) (y : β) :
    (q.toMeasure.map g).real {y} = ((q.map g) y).toReal := by
  rw [PMF.toMeasure_map _ _ (measurable_of_finite _), measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

theorem inputMutualInfo_prodChannel_prodPMF (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) (p₁ : PMF A₁)
    (p₂ : PMF A₂) :
    (prodChannel W₁ W₂).inputMutualInfo (prodPMF p₁ p₂) =
      W₁.inputMutualInfo p₁ + W₂.inputMutualInfo p₂ := by
  set J := DMC.jointPMF (prodChannel W₁ W₂) (prodPMF p₁ p₂)
  have hO := jointPMF_map_out W₁ W₂ p₁ p₂
  have e1 : J.map (fun x => x.2.1) = (DMC.jointPMF W₁ p₁).map Prod.snd := by
    rw [show (fun x : (A₁ × A₂) × (B₁ × B₂) => x.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← PMF.map_comp, hO, map_fst_prodPMF]
  have e2 : J.map (fun x => x.2.2) = (DMC.jointPMF W₂ p₂).map Prod.snd := by
    rw [show (fun x : (A₁ × A₂) × (B₁ × B₂) => x.2.2) = Prod.snd ∘ Prod.snd from rfl,
      ← PMF.map_comp, hO, map_snd_prodPMF]
  have h0 := mutualInfo_eq_zero_of_measureReal_eq_mul ((prodChannel W₁ W₂).jointMeasure
    (prodPMF p₁ p₂)) (X := fun x : (A₁ × A₂) × (B₁ × B₂) => x.2.1) (Y := fun x => x.2.2)
    fun s t => by
      rw [DMC.jointMeasure_eq_toMeasure, real_map, real_map, real_map, e1, e2,
        show J.map (fun x => (x.2.1, x.2.2)) = J.map Prod.snd from rfl, hO, prodPMF_apply,
        ENNReal.toReal_mul]
  rw [mutualInfo_def, entropy_left, entropy_right, map_fst_prodPMF, map_snd_prodPMF] at h0
  have e : H[Prod.snd ; (prodChannel W₁ W₂).jointMeasure (prodPMF p₁ p₂)] =
      H[fun x : (A₁ × A₂) × (B₁ × B₂) => (x.2.1, x.2.2) ;
        (prodChannel W₁ W₂).jointMeasure (prodPMF p₁ p₂)] := rfl
  rw [inputMutualInfo_eq, inputMutualInfo_eq, inputMutualInfo_eq, condEntropy_prod,
    map_fst_prodPMF, map_snd_prodPMF]
  linarith

theorem capacity_prodChannel [Nonempty A₁] [Nonempty A₂] (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) :
    (prodChannel W₁ W₂).capacity = W₁.capacity + W₂.capacity := by
  have : Nonempty (PMF (A₁ × A₂)) := ⟨PMF.pure (Classical.arbitrary _)⟩
  have : Nonempty (PMF A₁) := ⟨PMF.pure (Classical.arbitrary _)⟩
  have : Nonempty (PMF A₂) := ⟨PMF.pure (Classical.arbitrary _)⟩
  refine le_antisymm (ciSup_le fun p => (inputMutualInfo_prodChannel_le W₁ W₂ p).trans
    (add_le_add (W₁.inputMutualInfo_le_capacity _) (W₂.inputMutualInfo_le_capacity _)))
    (le_of_forall_pos_lt_add fun δ hδ => ?_)
  have l₁ : W₁.capacity - δ / 2 < W₁.capacity := by linarith
  have l₂ : W₂.capacity - δ / 2 < W₂.capacity := by linarith
  obtain ⟨p₁, h₁⟩ := exists_lt_of_lt_ciSup l₁
  obtain ⟨p₂, h₂⟩ := exists_lt_of_lt_ciSup l₂
  have h := (prodChannel W₁ W₂).inputMutualInfo_le_capacity (prodPMF p₁ p₂)
  rw [inputMutualInfo_prodChannel_prodPMF] at h
  linarith

end Info

instance measurableSingletonClass_sum [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
    [MeasurableSpace A₂] [MeasurableSingletonClass A₂] : MeasurableSingletonClass (A₁ ⊕ A₂) :=
  ⟨fun _ => measurableSet_sum_iff.2
    ⟨(Set.subsingleton_singleton.preimage Sum.inl_injective).measurableSet,
      (Set.subsingleton_singleton.preimage Sum.inr_injective).measurableSet⟩⟩

noncomputable def sumChannel (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂) : DMC (A₁ ⊕ A₂) (B₁ ⊕ B₂) :=
  Sum.elim (fun a => (W₁ a).map Sum.inl) (fun a => (W₂ a).map Sum.inr)

section Sum

variable (W₁ : DMC A₁ B₁) (W₂ : DMC A₂ B₂)

private lemma sumChannel_inl_inl (a : A₁) (b : B₁) :
    sumChannel W₁ W₂ (Sum.inl a) (Sum.inl b) = W₁ a b :=
  PMF.map_apply_of_injective _ Sum.inl_injective b

private lemma sumChannel_inr_inr (a : A₂) (b : B₂) :
    sumChannel W₁ W₂ (Sum.inr a) (Sum.inr b) = W₂ a b :=
  PMF.map_apply_of_injective _ Sum.inr_injective b

private lemma sumChannel_inl_inr (a : A₁) (b : B₂) :
    sumChannel W₁ W₂ (Sum.inl a) (Sum.inr b) = 0 := by
  rw [sumChannel, Sum.elim_inl, PMF.map_apply]
  exact ENNReal.tsum_eq_zero.2 fun x => by simp

private lemma sumChannel_inr_inl (a : A₂) (b : B₁) :
    sumChannel W₁ W₂ (Sum.inr a) (Sum.inl b) = 0 := by
  rw [sumChannel, Sum.elim_inr, PMF.map_apply]
  exact ENNReal.tsum_eq_zero.2 fun x => by simp

private lemma mul_log_mul (x y : ℝ) :
    x * y * Real.log (x * y) = y * (x * Real.log x) + x * (y * Real.log y) := by
  have h := Real.negMulLog_mul x y
  simp only [Real.negMulLog] at h
  linarith

variable [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

private lemma inputMutualInfo_sumChannel_eq (p : PMF (A₁ ⊕ A₂)) (l : ℝ) (p₁ : PMF A₁)
    (p₂ : PMF A₂) (h₁ : ∀ a, (p (Sum.inl a)).toReal = l * (p₁ a).toReal)
    (h₂ : ∀ a, (p (Sum.inr a)).toReal = (1 - l) * (p₂ a).toReal) :
    (sumChannel W₁ W₂).inputMutualInfo p = Real.negMulLog l + Real.negMulLog (1 - l) +
      l * W₁.inputMutualInfo p₁ + (1 - l) * W₂.inputMutualInfo p₂ := by
  have hO₁ : ∀ b, DMC.outputLaw (sumChannel W₁ W₂) (fun a => (p a).toReal) (Sum.inl b) =
      l * DMC.outputLaw W₁ (fun a => (p₁ a).toReal) b := fun b => by
    simp only [DMC.outputLaw, Fintype.sum_sum_type, sumChannel_inl_inl, sumChannel_inr_inl,
      ENNReal.toReal_zero, mul_zero, sum_const_zero, add_zero, h₁, mul_sum]
    exact sum_congr rfl fun a _ => by ring
  have hO₂ : ∀ b, DMC.outputLaw (sumChannel W₁ W₂) (fun a => (p a).toReal) (Sum.inr b) =
      (1 - l) * DMC.outputLaw W₂ (fun a => (p₂ a).toReal) b := fun b => by
    simp only [DMC.outputLaw, Fintype.sum_sum_type, sumChannel_inr_inr, sumChannel_inl_inr,
      ENNReal.toReal_zero, mul_zero, sum_const_zero, zero_add, h₂, mul_sum]
    exact sum_congr rfl fun a _ => by ring
  have hS₁ : ∑ b, DMC.outputLaw W₁ (fun a => (p₁ a).toReal) b = 1 := by
    simp only [DMC.outputLaw]
    rw [sum_comm]
    simp only [← mul_sum, sum_toReal_pmf_eq_one, mul_one]
  have hS₂ : ∑ b, DMC.outputLaw W₂ (fun a => (p₂ a).toReal) b = 1 := by
    simp only [DMC.outputLaw]
    rw [sum_comm]
    simp only [← mul_sum, sum_toReal_pmf_eq_one, mul_one]
  rw [DMC.inputMutualInfo_eq_sub, DMC.inputMutualInfo_eq_sub, DMC.inputMutualInfo_eq_sub]
  simp only [Fintype.sum_sum_type, sumChannel_inl_inl, sumChannel_inr_inr, sumChannel_inl_inr,
    sumChannel_inr_inl, ENNReal.toReal_zero, zero_mul, mul_zero, sum_const_zero, add_zero,
    zero_add, h₁, h₂, hO₁, hO₂, mul_log_mul, sum_add_distrib, ← sum_mul, hS₁, hS₂, one_mul]
  simp only [mul_assoc, ← mul_sum, Real.negMulLog]
  ring

omit [MeasurableSpace A₁] [MeasurableSingletonClass A₁] in
private lemma exists_pmf_mul [Nonempty A₁] (w : A₁ → ℝ) (hw : ∀ a, 0 ≤ w a) :
    ∃ q : PMF A₁, ∀ a, w a = (∑ a, w a) * (q a).toReal := by
  set c := ∑ a, w a
  by_cases hc : c = 0
  · refine ⟨PMF.pure (Classical.arbitrary A₁), fun a => ?_⟩
    rw [hc, zero_mul]
    exact (sum_eq_zero_iff_of_nonneg fun a _ => hw a).1 hc a (mem_univ a)
  · have hc0 : 0 < c := lt_of_le_of_ne (sum_nonneg fun a _ => hw a) (Ne.symm hc)
    refine ⟨PMF.ofFintype (fun a => ENNReal.ofReal (w a / c)) ?_, fun a => ?_⟩
    · rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => div_nonneg (hw a) hc0.le, ← sum_div,
        div_self hc, ENNReal.ofReal_one]
    · rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (div_nonneg (hw a) hc0.le)]
      field_simp

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] in
private lemma exists_split [Finite A₁] [Finite A₂] [Nonempty A₁] [Nonempty A₂]
    (p : PMF (A₁ ⊕ A₂)) :
    ∃ (l : ℝ) (p₁ : PMF A₁) (p₂ : PMF A₂), 0 ≤ l ∧ l ≤ 1 ∧
      (∀ a, (p (Sum.inl a)).toReal = l * (p₁ a).toReal) ∧
      (∀ a, (p (Sum.inr a)).toReal = (1 - l) * (p₂ a).toReal) := by
  have := Fintype.ofFinite A₁
  have := Fintype.ofFinite A₂
  obtain ⟨p₁, h₁⟩ := exists_pmf_mul (fun a => (p (Sum.inl a)).toReal) fun _ => ENNReal.toReal_nonneg
  obtain ⟨p₂, h₂⟩ := exists_pmf_mul (fun a => (p (Sum.inr a)).toReal) fun _ => ENNReal.toReal_nonneg
  have hs := sum_toReal_pmf_eq_one p
  rw [Fintype.sum_sum_type] at hs
  have hn₂ : 0 ≤ ∑ a, (p (Sum.inr a)).toReal := sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  refine ⟨∑ a, (p (Sum.inl a)).toReal, p₁, p₂, sum_nonneg fun _ _ => ENNReal.toReal_nonneg,
    by linarith, h₁, fun a => ?_⟩
  rw [h₂ a, show 1 - ∑ a, (p (Sum.inl a)).toReal = ∑ a, (p (Sum.inr a)).toReal by linarith]

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] in
private lemma exists_join [Finite A₁] [Finite A₂] (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (p₁ : PMF A₁) (p₂ : PMF A₂) :
    ∃ p : PMF (A₁ ⊕ A₂), (∀ a, (p (Sum.inl a)).toReal = l * (p₁ a).toReal) ∧
      (∀ a, (p (Sum.inr a)).toReal = (1 - l) * (p₂ a).toReal) := by
  have := Fintype.ofFinite A₁
  have := Fintype.ofFinite A₂
  set f : A₁ ⊕ A₂ → ℝ := Sum.elim (fun a => l * (p₁ a).toReal) (fun a => (1 - l) * (p₂ a).toReal)
  have hf : ∀ x, 0 ≤ f x := fun x => by
    cases x with
    | inl a => exact mul_nonneg hl0 ENNReal.toReal_nonneg
    | inr a => exact mul_nonneg (by linarith) ENNReal.toReal_nonneg
  refine ⟨PMF.ofFintype (fun x => ENNReal.ofReal (f x)) ?_, fun a => ?_, fun a => ?_⟩
  · rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => hf x, Fintype.sum_sum_type]
    simp only [f, Sum.elim_inl, Sum.elim_inr, ← mul_sum, sum_toReal_pmf_eq_one]
    norm_num
  · rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hf _)]
    rfl
  · rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hf _)]
    rfl

omit W₁ W₂ in
private lemma negMulLog_add_le (l c₁ c₂ : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    Real.negMulLog l + Real.negMulLog (1 - l) + l * c₁ + (1 - l) * c₂ ≤
      Real.log (Real.exp c₁ + Real.exp c₂) := by
  set S := Real.exp c₁ + Real.exp c₂
  have hS : 0 < S := by positivity
  have h := sum_mul_log_le_sum_mul_log (univ : Finset Bool)
    (p := fun b => if b then l else 1 - l) (q := fun b => if b then Real.exp c₁ / S
      else Real.exp c₂ / S)
    (fun b _ => by cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith)
    (fun b _ => by cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity)
    (fun b _ h => by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;>
        exact absurd h (by positivity))
    (by
      simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
      rw [← add_div, div_self hS.ne']
      linarith)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at h
  rw [Real.log_div (Real.exp_pos _).ne' hS.ne', Real.log_div (Real.exp_pos _).ne' hS.ne',
    Real.log_exp, Real.log_exp] at h
  simp only [Real.negMulLog]
  nlinarith

omit W₁ W₂ in
private lemma negMulLog_add_eq (c₁ c₂ : ℝ) :
    Real.negMulLog (Real.exp c₁ / (Real.exp c₁ + Real.exp c₂)) +
      Real.negMulLog (1 - Real.exp c₁ / (Real.exp c₁ + Real.exp c₂)) +
      Real.exp c₁ / (Real.exp c₁ + Real.exp c₂) * c₁ +
      (1 - Real.exp c₁ / (Real.exp c₁ + Real.exp c₂)) * c₂ =
      Real.log (Real.exp c₁ + Real.exp c₂) := by
  set S := Real.exp c₁ + Real.exp c₂
  have hS : 0 < S := by positivity
  have h1 : 1 - Real.exp c₁ / S = Real.exp c₂ / S := by
    field_simp
    ring
  rw [h1]
  simp only [Real.negMulLog]
  rw [Real.log_div (Real.exp_pos _).ne' hS.ne', Real.log_div (Real.exp_pos _).ne' hS.ne',
    Real.log_exp, Real.log_exp]
  field_simp
  ring

theorem capacity_sumChannel [Nonempty A₁] [Nonempty A₂] :
    (sumChannel W₁ W₂).capacity = Real.log (Real.exp W₁.capacity + Real.exp W₂.capacity) := by
  have : Nonempty (PMF (A₁ ⊕ A₂)) := ⟨PMF.pure (Sum.inl (Classical.arbitrary _))⟩
  have : Nonempty (PMF A₁) := ⟨PMF.pure (Classical.arbitrary _)⟩
  have : Nonempty (PMF A₂) := ⟨PMF.pure (Classical.arbitrary _)⟩
  refine le_antisymm (ciSup_le fun p => ?_) (le_of_forall_pos_lt_add fun δ hδ => ?_)
  · obtain ⟨l, p₁, p₂, hl0, hl1, h₁, h₂⟩ := exists_split p
    rw [inputMutualInfo_sumChannel_eq W₁ W₂ p l p₁ p₂ h₁ h₂]
    have e₁ := mul_le_mul_of_nonneg_left (W₁.inputMutualInfo_le_capacity p₁) hl0
    have e₂ := mul_le_mul_of_nonneg_left (W₂.inputMutualInfo_le_capacity p₂)
      (sub_nonneg.2 hl1)
    linarith [negMulLog_add_le l W₁.capacity W₂.capacity hl0 hl1]
  · have l₁ : W₁.capacity - δ / 2 < W₁.capacity := by linarith
    have l₂ : W₂.capacity - δ / 2 < W₂.capacity := by linarith
    obtain ⟨p₁, h₁⟩ := exists_lt_of_lt_ciSup l₁
    obtain ⟨p₂, h₂⟩ := exists_lt_of_lt_ciSup l₂
    set S := Real.exp W₁.capacity + Real.exp W₂.capacity
    set l := Real.exp W₁.capacity / S
    have hS : 0 < S := by positivity
    have hl0 : 0 ≤ l := by positivity
    have hl1 : l ≤ 1 := by
      rw [div_le_one hS]
      linarith [Real.exp_pos W₂.capacity]
    obtain ⟨p, hp₁, hp₂⟩ := exists_join l hl0 hl1 p₁ p₂
    have h := (sumChannel W₁ W₂).inputMutualInfo_le_capacity p
    rw [inputMutualInfo_sumChannel_eq W₁ W₂ p l p₁ p₂ hp₁ hp₂] at h
    have e := negMulLog_add_eq W₁.capacity W₂.capacity
    have e₁ := mul_le_mul_of_nonneg_left h₁.le hl0
    have e₂ := mul_le_mul_of_nonneg_left h₂.le (sub_nonneg.2 hl1)
    nlinarith

end Sum

end Meat.Examples
