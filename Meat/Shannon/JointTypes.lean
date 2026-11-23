import Meat.Shannon.Types

open MeasureTheory Finset

namespace Meat

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

noncomputable def countEntropy (k : A → ℕ) : ℝ :=
  ∑ a, (k a : ℝ) * Real.log ((∑ a', k a' : ℕ) / k a)

def condTypeClass {n : ℕ} (y : Fin n → B) (k : B → A → ℕ) : Finset (Fin n → A) :=
  univ.filter fun x => ∀ b a, typeCount (fun i => (y i, x i)) (b, a) = k b a

theorem mem_condTypeClass {n : ℕ} {y : Fin n → B} {k : B → A → ℕ} {x : Fin n → A} :
    x ∈ condTypeClass y k ↔ ∀ b a, typeCount (fun i => (y i, x i)) (b, a) = k b a := by
  simp [condTypeClass]

section Block

variable [MeasurableSpace A] [MeasurableSingletonClass A]

theorem mul_measureEntropy_seqType {m : ℕ} (z : Fin m → A) :
    m * measureEntropy (seqType z) = countEntropy (typeCount z) := by
  rw [countEntropy, sum_typeCount, measureEntropy, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [seqType_real]
  have hc := typeCount_le z a
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Nat.le_zero.1 hc]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Real.negMulLog, ← inv_div, Real.log_inv]
  field_simp

theorem card_typeCount_le_exp (m : ℕ) (k : A → ℕ) (hk : ∑ a, k a = m) :
    (#{z : Fin m → A | typeCount z = k} : ℝ) ≤ Real.exp (countEntropy k) := by
  obtain ⟨z, hz⟩ := exists_typeCount_eq m k hk
  have he : (univ.filter fun z' : Fin m → A => typeCount z' = k) = typeClass (seqType z) m := by
    ext z'
    rw [mem_typeClass, seqType_eq_seqType_iff, hz]
    simp
  rw [he, ← hz, ← mul_measureEntropy_seqType]
  exact card_typeClass_le _ m

theorem exp_div_le_card_typeCount (m : ℕ) (k : A → ℕ) (hk : ∑ a, k a = m) :
    Real.exp (countEntropy k) / (m + 1) ^ Fintype.card A ≤
      (#{z : Fin m → A | typeCount z = k} : ℝ) := by
  obtain ⟨z, hz⟩ := exists_typeCount_eq m k hk
  have he : (univ.filter fun z' : Fin m → A => typeCount z' = k) = typeClass (seqType z) m := by
    ext z'
    rw [mem_typeClass, seqType_eq_seqType_iff, hz]
    simp
  rw [he, ← hz, ← mul_measureEntropy_seqType]
  exact card_typeClass_ge (mem_typeSet.2 ⟨z, rfl⟩)

end Block

section Decomposition

variable {n : ℕ} (y : Fin n → B)

omit [Fintype B] in
private lemma card_subtype_eq (b : B) : Fintype.card {i // y i = b} = typeCount y b := by
  rw [Fintype.card_subtype]
  rfl

private noncomputable def blockEquiv (b : B) : {i // y i = b} ≃ Fin (typeCount y b) :=
  Fintype.equivFinOfCardEq (card_subtype_eq y b)

private noncomputable def splitEquiv :
    (Fin n → A) ≃ ((b : B) → Fin (typeCount y b) → A) :=
  ((Equiv.sigmaFiberEquiv y).symm.arrowCongr (Equiv.refl A)).trans
    ((Equiv.piCurry fun b (_ : {i // y i = b}) => A).trans
      (Equiv.piCongrRight fun b => (blockEquiv y b).arrowCongr (Equiv.refl A)))

omit [Fintype A] [DecidableEq A] [Fintype B] in
private lemma splitEquiv_apply (x : Fin n → A) (b : B) (j : Fin (typeCount y b)) :
    splitEquiv y x b j = x ((blockEquiv y b).symm j).1 := rfl

omit [Fintype A] [Fintype B] in
private lemma typeCount_split (x : Fin n → A) (b : B) (a : A) :
    typeCount (splitEquiv y x b) a = typeCount (fun i => (y i, x i)) (b, a) := by
  have h1 : typeCount (splitEquiv y x b) a = Fintype.card {j // splitEquiv y x b j = a} := by
    rw [Fintype.card_subtype]
    rfl
  have h2 : typeCount (fun i => (y i, x i)) (b, a) =
      Fintype.card {i // (y i, x i) = (b, a)} := by
    rw [Fintype.card_subtype]
    rfl
  rw [h1, h2]
  refine Fintype.card_congr (((blockEquiv y b).symm.subtypeEquiv fun j => ?_).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter (fun i => y i = b) fun i => x i = a).trans
      (Equiv.subtypeEquivRight fun i => by simp [Prod.ext_iff])))
  rw [splitEquiv_apply]

theorem card_condTypeClass (k : B → A → ℕ) :
    #(condTypeClass y k) = ∏ b, #{z : Fin (typeCount y b) → A | typeCount z = k b} := by
  rw [← Fintype.card_piFinset]
  refine card_equiv (splitEquiv y) fun x => ?_
  rw [mem_condTypeClass, Fintype.mem_piFinset]
  simp only [mem_filter, mem_univ, true_and, funext_iff, typeCount_split]

variable [MeasurableSpace A] [MeasurableSingletonClass A]

theorem card_condTypeClass_le (k : B → A → ℕ) (hk : ∀ b, ∑ a, k b a = typeCount y b) :
    (#(condTypeClass y k) : ℝ) ≤ Real.exp (∑ b, countEntropy (k b)) := by
  rw [card_condTypeClass, Nat.cast_prod, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun b _ =>
    card_typeCount_le_exp _ (k b) (hk b)

theorem exp_div_le_card_condTypeClass (k : B → A → ℕ) (hk : ∀ b, ∑ a, k b a = typeCount y b) :
    Real.exp (∑ b, countEntropy (k b)) / (n + 1) ^ (Fintype.card A * Fintype.card B) ≤
      (#(condTypeClass y k) : ℝ) := by
  rw [card_condTypeClass, Nat.cast_prod]
  have hpow : ∏ b, ((typeCount y b : ℝ) + 1) ^ Fintype.card A ≤
      ((n : ℝ) + 1) ^ (Fintype.card A * Fintype.card B) := by
    calc ∏ b, ((typeCount y b : ℝ) + 1) ^ Fintype.card A
        ≤ ∏ _b : B, ((n : ℝ) + 1) ^ Fintype.card A :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) fun b _ =>
            pow_le_pow_left₀ (by positivity)
              (by exact_mod_cast Nat.add_le_add_right (typeCount_le y b) 1) _
      _ = _ := by rw [prod_const, card_univ, ← pow_mul]
  calc Real.exp (∑ b, countEntropy (k b)) / (n + 1) ^ (Fintype.card A * Fintype.card B)
      ≤ (∏ b, Real.exp (countEntropy (k b))) / ∏ b, ((typeCount y b : ℝ) + 1) ^ Fintype.card A := by
        rw [← Real.exp_sum]
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le (prod_pos fun _ _ => by positivity)
          hpow
    _ = ∏ b, Real.exp (countEntropy (k b)) / ((typeCount y b : ℝ) + 1) ^ Fintype.card A := by
        rw [prod_div_distrib]
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) fun b _ =>
        exp_div_le_card_typeCount _ (k b) (hk b)

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem typeCount_eq_sum_pair (x : Fin n → A) (a : A) :
    typeCount x a = ∑ b, typeCount (fun i => (y i, x i)) (b, a) := by
  unfold typeCount
  rw [card_eq_sum_card_fiberwise (f := y) (t := univ) fun _ _ => mem_univ _]
  refine sum_congr rfl fun b _ => ?_
  congr 1
  ext i
  simp [and_comm]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem sum_iidProb_condTypeClass (q : PMF A) (k : B → A → ℕ) :
    ∑ x ∈ condTypeClass y k, iidProb q x =
      #(condTypeClass y k) * ∏ a, (q a).toReal ^ (∑ b, k b a) := by
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun x hx => ?_
  rw [iidProb, prod_comp_eq_prod_pow x fun a => (q a).toReal]
  refine prod_congr rfl fun a _ => ?_
  rw [typeCount_eq_sum_pair y x a]
  simp only [(mem_condTypeClass.1 hx) _ a]

theorem sum_iidProb_condTypeClass_le (q : PMF A) (k : B → A → ℕ)
    (hk : ∀ b, ∑ a, k b a = typeCount y b) :
    ∑ x ∈ condTypeClass y k, iidProb q x ≤
      Real.exp (∑ b, countEntropy (k b)) * ∏ a, (q a).toReal ^ (∑ b, k b a) := by
  rw [sum_iidProb_condTypeClass]
  exact mul_le_mul_of_nonneg_right (card_condTypeClass_le y k hk)
    (prod_nonneg fun _ _ => pow_nonneg ENNReal.toReal_nonneg _)

theorem le_sum_iidProb_condTypeClass (q : PMF A) (k : B → A → ℕ)
    (hk : ∀ b, ∑ a, k b a = typeCount y b) :
    Real.exp (∑ b, countEntropy (k b)) / (n + 1) ^ (Fintype.card A * Fintype.card B) *
        ∏ a, (q a).toReal ^ (∑ b, k b a) ≤
      ∑ x ∈ condTypeClass y k, iidProb q x := by
  rw [sum_iidProb_condTypeClass]
  exact mul_le_mul_of_nonneg_right (exp_div_le_card_condTypeClass y k hk)
    (prod_nonneg fun _ _ => pow_nonneg ENNReal.toReal_nonneg _)

end Decomposition

end Meat
