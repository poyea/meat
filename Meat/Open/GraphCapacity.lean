import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Computability.Partrec
import Mathlib.Data.Matrix.Mul

open Finset

namespace Meat

variable {V W : Type*}

def strongProd (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) where
  Adj p q := p ≠ q ∧ (p.1 = q.1 ∨ G.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ H.Adj p.2 q.2)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.1.imp Eq.symm fun h => h.symm,
    h.2.2.imp Eq.symm fun h => h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def strongPow (G : SimpleGraph V) (n : ℕ) : SimpleGraph (Fin n → V) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun i => (h.2 i).imp Eq.symm fun h => h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def shannonCapacity (G : SimpleGraph V) : ℝ :=
  ⨆ n : ℕ, ((strongPow G (n + 1)).indepNum : ℝ) ^ (((n + 1 : ℕ) : ℝ)⁻¹)

def ShannonCapacityCycleSeven : Prop :=
  shannonCapacity (SimpleGraph.cycleGraph 7)
    = 7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7))

def graphOfCode (m : ℕ) (E : List (ℕ × ℕ)) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i j => ((i : ℕ), (j : ℕ)) ∈ E

def ShannonCapacityComputable : Prop :=
  ∃ f : ℕ × List (ℕ × ℕ) × ℕ → ℤ × ℕ, Computable f ∧ ∀ m E k,
    |((f (m, E, k)).1 : ℝ) / ((f (m, E, k)).2 + 1) - shannonCapacity (graphOfCode m E)|
      ≤ 1 / ((k : ℝ) + 1)

structure OrthoRep (G : SimpleGraph V) (d : ℕ) where
  vec : V → Fin d → ℝ
  handle : Fin d → ℝ
  vec_self : ∀ v, vec v ⬝ᵥ vec v = 1
  handle_self : handle ⬝ᵥ handle = 1
  vec_orth : ∀ v w, v ≠ w → ¬G.Adj v w → vec v ⬝ᵥ vec w = 0

noncomputable def lovaszTheta (G : SimpleGraph V) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ (d : ℕ) (R : OrthoRep G d), ∀ v, 1 ≤ t * (R.vec v ⬝ᵥ R.handle) ^ 2}

theorem mul_indepNum_le_strongProd [Finite V] [Finite W] (G : SimpleGraph V)
    (H : SimpleGraph W) : G.indepNum * H.indepNum ≤ (strongProd G H).indepNum := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨t, ht⟩ := H.exists_isNIndepSet_indepNum
  have hst : (strongProd G H).IsIndepSet (s ×ˢ t : Finset (V × W)) := by
    intro p hp q hq hpq hadj
    simp only [coe_product, Set.mem_prod, mem_coe] at hp hq
    obtain ⟨-, h1, h2⟩ := hadj
    by_cases e1 : p.1 = q.1
    · have e2 : p.2 ≠ q.2 := fun e2 => hpq (Prod.ext e1 e2)
      exact ht.isIndepSet hp.2 hq.2 e2 (h2.resolve_left e2)
    · exact hs.isIndepSet hp.1 hq.1 e1 (h1.resolve_left e1)
  have := hst.card_le_indepNum
  rwa [card_product, hs.card_eq, ht.card_eq] at this

theorem pow_indepNum_le_strongPow [Finite V] (G : SimpleGraph V) (n : ℕ) :
    G.indepNum ^ n ≤ (strongPow G n).indepNum := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hst : (strongPow G n).IsIndepSet (Fintype.piFinset fun _ : Fin n => s : Finset _) := by
    intro x hx y hy hxy hadj
    simp only [mem_coe, Fintype.mem_piFinset] at hx hy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    exact hs.isIndepSet (hx i) (hy i) hi ((hadj.2 i).resolve_left hi)
  have := hst.card_le_indepNum
  rwa [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, hs.card_eq] at this

theorem indepNum_strongPow_le [Fintype V] (G : SimpleGraph V) (n : ℕ) :
    (strongPow G n).indepNum ≤ Fintype.card V ^ n := by
  classical
  obtain ⟨s, hs⟩ := (strongPow G n).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  exact (card_le_univ s).trans_eq (by simp)

private lemma rpow_le_card [Fintype V] (G : SimpleGraph V) (n : ℕ) :
    ((strongPow G (n + 1)).indepNum : ℝ) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤ Fintype.card V := by
  calc ((strongPow G (n + 1)).indepNum : ℝ) ^ (((n + 1 : ℕ) : ℝ)⁻¹)
      ≤ ((Fintype.card V : ℝ) ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        exact_mod_cast indepNum_strongPow_le G (n + 1)
    _ = Fintype.card V := Real.pow_rpow_inv_natCast (by positivity) (by omega)

private lemma bddAbove_capacity [Finite V] (G : SimpleGraph V) :
    BddAbove (Set.range fun n : ℕ =>
      ((strongPow G (n + 1)).indepNum : ℝ) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) := by
  have := Fintype.ofFinite V
  exact ⟨Fintype.card V, by
    rintro _ ⟨n, rfl⟩
    exact rpow_le_card G n⟩

theorem rpow_indepNum_le_shannonCapacity [Finite V] (G : SimpleGraph V) (n : ℕ) :
    ((strongPow G (n + 1)).indepNum : ℝ) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤ shannonCapacity G :=
  le_ciSup (bddAbove_capacity G) n

theorem shannonCapacity_le_card [Fintype V] (G : SimpleGraph V) :
    shannonCapacity G ≤ Fintype.card V :=
  ciSup_le fun n => rpow_le_card G n

theorem indepNum_le_shannonCapacity [Finite V] (G : SimpleGraph V) :
    (G.indepNum : ℝ) ≤ shannonCapacity G := by
  have h := rpow_indepNum_le_shannonCapacity G 0
  have h1 : (G.indepNum : ℝ) ≤ (strongPow G 1).indepNum := by
    exact_mod_cast (pow_one G.indepNum).symm.trans_le (pow_indepNum_le_strongPow G 1)
  simp only [zero_add, Nat.cast_one, inv_one, Real.rpow_one] at h
  exact h1.trans h

private def c5Set : Finset (Fin 2 → Fin 5) := {![0, 0], ![1, 2], ![2, 4], ![3, 1], ![4, 3]}

private lemma c5Set_indep : (strongPow (SimpleGraph.cycleGraph 5) 2).IsIndepSet c5Set := by
  let _ : DecidableRel (strongPow (SimpleGraph.cycleGraph 5) 2).Adj := fun x y =>
    inferInstanceAs (Decidable (x ≠ y ∧ ∀ i, _))
  unfold c5Set
  decide

theorem sqrt_five_le_shannonCapacity_cycleGraph_five :
    √5 ≤ shannonCapacity (SimpleGraph.cycleGraph 5) := by
  have h5 : 5 ≤ (strongPow (SimpleGraph.cycleGraph 5) 2).indepNum := by
    have := c5Set_indep.card_le_indepNum
    rwa [show c5Set.card = 5 by decide] at this
  have h := rpow_indepNum_le_shannonCapacity (SimpleGraph.cycleGraph 5) 1
  refine le_trans ?_ h
  rw [Real.sqrt_eq_rpow, show (((1 + 1 : ℕ) : ℝ)⁻¹) = 1 / 2 by norm_num]
  exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast h5) (by norm_num)

private lemma dotProduct_prod {n d : ℕ} (a b : Fin n → Fin d → ℝ) :
    (fun j : Fin n → Fin d => ∏ i, a i (j i)) ⬝ᵥ (fun j => ∏ i, b i (j i))
      = ∏ i, a i ⬝ᵥ b i := by
  simp only [dotProduct, ← prod_mul_distrib]
  rw [Finset.prod_univ_sum]
  simp

private lemma bessel {ι α : Type*} [Fintype ι] [DecidableEq α] (S : Finset α) (U : α → ι → ℝ)
    (C : ι → ℝ) (hU : ∀ a ∈ S, ∀ b ∈ S, U a ⬝ᵥ U b = if a = b then 1 else 0) :
    ∑ a ∈ S, (U a ⬝ᵥ C) ^ 2 ≤ C ⬝ᵥ C := by
  set P : ι → ℝ := ∑ a ∈ S, (U a ⬝ᵥ C) • U a
  have hCP : C ⬝ᵥ P = ∑ a ∈ S, (U a ⬝ᵥ C) ^ 2 := by
    rw [dotProduct_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm C, sq]
  have hPP : P ⬝ᵥ P = ∑ a ∈ S, (U a ⬝ᵥ C) ^ 2 := by
    simp only [P, dotProduct_sum, sum_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    refine sum_congr rfl fun a ha => ?_
    rw [sum_eq_single_of_mem a ha fun b hb hba => by simp [hU b hb a ha, hba], hU a ha a ha]
    simp [sq]
  have h0 : 0 ≤ (C - P) ⬝ᵥ (C - P) := by
    simp only [dotProduct]
    exact sum_nonneg fun i _ => mul_self_nonneg _
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm P C, hCP, hPP] at h0
  linarith

theorem indepNum_strongPow_le_of_orthoRep {d : ℕ} {G : SimpleGraph V} (R : OrthoRep G d) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : ∀ v, 1 ≤ t * (R.vec v ⬝ᵥ R.handle) ^ 2) (n : ℕ) :
    ((strongPow G n).indepNum : ℝ) ≤ t ^ n := by
  classical
  obtain ⟨S, hS⟩ := (strongPow G n).exists_isNIndepSet_indepNum
  let U : (Fin n → V) → (Fin n → Fin d) → ℝ := fun x j => ∏ i, R.vec (x i) (j i)
  let C : (Fin n → Fin d) → ℝ := fun j => ∏ i, R.handle (j i)
  have hU : ∀ x ∈ S, ∀ y ∈ S, U x ⬝ᵥ U y = if x = y then 1 else 0 := by
    intro x hx y hy
    rw [dotProduct_prod]
    split_ifs with hxy
    · subst hxy
      simp [R.vec_self]
    · have hna := hS.isIndepSet hx hy hxy
      simp only [strongPow, not_and, not_forall, not_or] at hna
      obtain ⟨i, hi, hi'⟩ := hna hxy
      exact prod_eq_zero (mem_univ i) (R.vec_orth _ _ hi hi')
  have hB := bessel S U C hU
  have hUC : ∀ x, U x ⬝ᵥ C = ∏ i, R.vec (x i) ⬝ᵥ R.handle := fun x => dotProduct_prod _ _
  have hCC : C ⬝ᵥ C = 1 := by
    rw [dotProduct_prod]
    simp [R.handle_self]
  rw [hCC] at hB
  rw [← hS.card_eq]
  calc (S.card : ℝ) = ∑ x ∈ S, 1 := by simp
    _ ≤ ∑ x ∈ S, t ^ n * (U x ⬝ᵥ C) ^ 2 := by
        refine sum_le_sum fun x _ => ?_
        have e : ∏ i, t * (R.vec (x i) ⬝ᵥ R.handle) ^ 2
            = t ^ n * ∏ i, (R.vec (x i) ⬝ᵥ R.handle) ^ 2 := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
        rw [hUC, ← prod_pow, ← e]
        exact one_le_prod₀ fun i _ => ht (x i)
    _ = t ^ n * ∑ x ∈ S, (U x ⬝ᵥ C) ^ 2 := by rw [mul_sum]
    _ ≤ t ^ n * 1 := by gcongr
    _ = t ^ n := mul_one _

theorem shannonCapacity_le_of_orthoRep {d : ℕ} {G : SimpleGraph V} (R : OrthoRep G d)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ∀ v, 1 ≤ t * (R.vec v ⬝ᵥ R.handle) ^ 2) :
    shannonCapacity G ≤ t := by
  refine ciSup_le fun n => ?_
  calc ((strongPow G (n + 1)).indepNum : ℝ) ^ (((n + 1 : ℕ) : ℝ)⁻¹)
      ≤ (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) (indepNum_strongPow_le_of_orthoRep R ht0 ht _)
          (by positivity)
    _ = t := Real.pow_rpow_inv_natCast ht0 (by omega)

private noncomputable def standardRep [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    OrthoRep G (Fintype.card V) where
  vec v := Pi.single (Fintype.equivFin V v) 1
  handle _ := (√(Fintype.card V : ℝ))⁻¹
  vec_self v := by simp
  handle_self := by
    have h : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    simp only [dotProduct, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← sq, inv_pow, Real.sq_sqrt h.le, mul_inv_cancel₀ h.ne']
  vec_orth v w hvw _ := by
    simp [(Fintype.equivFin V).injective.ne hvw.symm]

theorem shannonCapacity_le_lovaszTheta [Finite V] [Nonempty V] (G : SimpleGraph V) :
    shannonCapacity G ≤ lovaszTheta G := by
  have := Fintype.ofFinite V
  refine le_csInf ⟨Fintype.card V, by positivity, _, standardRep G, fun v => ?_⟩ ?_
  · have h : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    simp only [standardRep, single_dotProduct, one_mul]
    rw [inv_pow, Real.sq_sqrt h.le, mul_inv_cancel₀ h.ne']
  · rintro t ⟨ht0, d, R, ht⟩
    exact shannonCapacity_le_of_orthoRep R ht0 ht

private noncomputable def umbR : ℝ := √5
private noncomputable def umbS : ℝ := √(1 - umbR / 5)
private noncomputable def umbT : ℝ := √(umbR / 5)
private noncomputable def umbW : ℝ := √(10 + 2 * umbR)
private noncomputable def umbV : ℝ := √(10 - 2 * umbR)

private lemma umbR_sq : umbR ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma umbR_nonneg : 0 ≤ umbR := Real.sqrt_nonneg _

private lemma umbR_le : umbR ≤ 5 := by nlinarith [umbR_sq, umbR_nonneg]

private lemma umbS_sq : umbS ^ 2 = 1 - umbR / 5 := Real.sq_sqrt (by linarith [umbR_le])

private lemma umbT_sq : umbT ^ 2 = umbR / 5 := Real.sq_sqrt (by linarith [umbR_nonneg])

private lemma umbW_sq : umbW ^ 2 = 10 + 2 * umbR := Real.sq_sqrt (by linarith [umbR_nonneg])

private lemma umbV_sq : umbV ^ 2 = 10 - 2 * umbR := Real.sq_sqrt (by linarith [umbR_le])

private lemma umbW_mul_umbV : umbW * umbV = 4 * umbR := by
  rw [umbW, umbV, ← Real.sqrt_mul (by linarith [umbR_nonneg]),
    show (10 + 2 * umbR) * (10 - 2 * umbR) = 4 ^ 2 * 5 by nlinarith [umbR_sq],
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rfl

private lemma umb_facts :
    umbS ^ 2 * umbR = umbR - 1 ∧ umbS ^ 2 * umbR ^ 2 = 5 - umbR ∧
      umbS ^ 2 * (umbW * umbV) = 4 * umbR - 4 ∧ umbS ^ 2 * umbW ^ 2 = 8 ∧
      umbS ^ 2 * umbV ^ 2 = 12 - 4 * umbR ∧ umbT ^ 2 * umbR = 1 := by
  rw [umbW_mul_umbV, umbW_sq, umbV_sq, umbS_sq, umbT_sq]
  have h := umbR_sq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (-1 / 5 : ℝ) * h
  · linear_combination (1 - umbR / 5) * h
  · linear_combination (-4 / 5 : ℝ) * h
  · linear_combination (-2 / 5 : ℝ) * h
  · linear_combination (2 / 5 : ℝ) * h
  · linear_combination (1 / 5 : ℝ) * h

private noncomputable def umbVec : Fin 5 → Fin 3 → ℝ :=
  ![![umbS, 0, umbT], ![umbS * (umbR - 1) / 4, umbS * umbW / 4, umbT],
    ![-(umbS * (umbR + 1) / 4), umbS * umbV / 4, umbT],
    ![-(umbS * (umbR + 1) / 4), -(umbS * umbV / 4), umbT],
    ![umbS * (umbR - 1) / 4, -(umbS * umbW / 4), umbT]]

private lemma umbVec_self (i : Fin 5) : umbVec i ⬝ᵥ umbVec i = 1 := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := umb_facts
  have hS := umbS_sq
  have hT := umbT_sq
  fin_cases i <;> simp [umbVec, dotProduct, Fin.sum_univ_three] <;> linarith

private lemma umbVec_orth (i j : Fin 5) (hij : i ≠ j) (hadj : ¬(SimpleGraph.cycleGraph 5).Adj i j) :
    umbVec i ⬝ᵥ umbVec j = 0 := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := umb_facts
  have hS := umbS_sq
  have hT := umbT_sq
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact absurd (by decide) hadj
    | (simp [umbVec, dotProduct, Fin.sum_univ_three]; linarith)

private noncomputable def umbrella : OrthoRep (SimpleGraph.cycleGraph 5) 3 where
  vec := umbVec
  handle := ![0, 0, 1]
  vec_self := umbVec_self
  handle_self := by simp [dotProduct, Fin.sum_univ_three]
  vec_orth := umbVec_orth

private lemma umbrella_handle (i : Fin 5) :
    1 ≤ √5 * (umbrella.vec i ⬝ᵥ umbrella.handle) ^ 2 := by
  obtain ⟨-, -, -, -, -, f6⟩ := umb_facts
  have e : √5 = umbR := rfl
  rw [e]
  fin_cases i <;> simp [umbrella, umbVec, dotProduct, Fin.sum_univ_three] <;> linarith

theorem shannonCapacity_cycleGraph_five : shannonCapacity (SimpleGraph.cycleGraph 5) = √5 :=
  le_antisymm (shannonCapacity_le_of_orthoRep umbrella (Real.sqrt_nonneg _) umbrella_handle)
    sqrt_five_le_shannonCapacity_cycleGraph_five

theorem lovaszTheta_cycleGraph_five_le : lovaszTheta (SimpleGraph.cycleGraph 5) ≤ √5 :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨Real.sqrt_nonneg _, 3, umbrella, umbrella_handle⟩

theorem lovaszTheta_cycleGraph_five : lovaszTheta (SimpleGraph.cycleGraph 5) = √5 :=
  le_antisymm lovaszTheta_cycleGraph_five_le
    (sqrt_five_le_shannonCapacity_cycleGraph_five.trans (shannonCapacity_le_lovaszTheta _))

end Meat
