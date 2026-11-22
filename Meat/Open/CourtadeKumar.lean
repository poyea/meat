import Meat.Shannon.Average
import Meat.Shannon.Bits
import Meat.Shannon.Product
import Meat.Source.RateDistortion
import Meat.Source.SlepianWolfConverse

open MeasureTheory Finset

namespace Meat

namespace CourtadeKumar

def bscWeight (α : ℝ) (b c : Bool) : ℝ := if b = c then 1 - α else α

theorem bscWeight_nonneg {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (b c : Bool) :
    0 ≤ bscWeight α b c := by
  unfold bscWeight
  split_ifs <;> linarith

theorem sum_bscWeight (α : ℝ) (c : Bool) : ∑ b, bscWeight α b c = 1 := by
  cases c <;> simp [bscWeight]

theorem sum_negMulLog_bscWeight (α : ℝ) (c : Bool) :
    ∑ b, Real.negMulLog (bscWeight α b c) = Real.binEntropy α := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  cases c <;> simp [bscWeight, add_comm]

noncomputable def bscPair (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) : PMF (Bool × Bool) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (bscWeight α z.1 z.2 / 2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun z _ => div_nonneg (bscWeight_nonneg h0 h1 _ _)
      zero_le_two, Fintype.sum_prod_type_right]
    simp only [← sum_div, sum_bscWeight]
    norm_num)

theorem bscPair_toReal {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (b c : Bool) :
    (bscPair α h0 h1 (b, c)).toReal = bscWeight α b c / 2 := by
  rw [bscPair, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (div_nonneg (bscWeight_nonneg h0 h1 _ _) zero_le_two)]

end CourtadeKumar

open CourtadeKumar in
def CourtadeKumarConjecture : Prop :=
  ∀ (n : ℕ) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (f : (Fin n → Bool) → Bool),
    I[fun ω : (Fin n → Bool) × (Fin n → Bool) => f ω.1 : fun ω => ω.2 ;
      SlepianWolf.seqMeasure (bscPair α h0 h1) n] ≤ Real.log 2 - Real.binEntropy α

namespace CourtadeKumar

variable {n : ℕ} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1)

private lemma prod_half (x y : Fin n → Bool) :
    iidProb (bscPair α h0 h1) (fun j => (x j, y j)) =
      (1 / 2) ^ n * ∏ j, bscWeight α (x j) (y j) := by
  simp only [iidProb, bscPair_toReal, div_eq_mul_inv, mul_one, mul_comm _ (2 : ℝ)⁻¹,
    prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]

theorem measureReal_dictator_pair (i : Fin n) (b : Bool) (y : Fin n → Bool) :
    ((SlepianWolf.seqMeasure (bscPair α h0 h1) n).map fun ω => (ω.1 i, ω.2)).real {(b, y)} =
      (1 / 2) ^ n * bscWeight α b (y i) := by
  classical
  rw [measureReal_map_singleton, sum_filter, Fintype.sum_prod_type]
  simp only [Prod.mk.injEq, SlepianWolf.seqMeasure_real_singleton, prod_half h0 h1]
  have e : ∀ x : Fin n → Bool, (∑ y' : Fin n → Bool, if x i = b ∧ y' = y then
      (1 / 2) ^ n * ∏ j, bscWeight α (x j) (y' j) else 0) =
      (1 / 2) ^ n * ((∏ j, bscWeight α (x j) (y j)) * if x i = b then 1 else 0) := fun x => by
    by_cases hx : x i = b <;> simp [hx]
  simp only [e, ← mul_sum]
  rw [sum_prod_mul_apply (fun j a => bscWeight α a (y j)) (fun j => sum_bscWeight α (y j))
    (fun a => if a = b then 1 else 0) i]
  simp

theorem entropy_dictator_pair (i : Fin n) :
    H[fun ω : (Fin n → Bool) × (Fin n → Bool) => (ω.1 i, ω.2) ;
      SlepianWolf.seqMeasure (bscPair α h0 h1) n] = Real.binEntropy α + n * Real.log 2 := by
  rw [entropy_def, Fintype.sum_prod_type, sum_comm]
  simp only [measureReal_dictator_pair h0 h1, Real.negMulLog_mul, sum_add_distrib, ← mul_sum,
    ← sum_mul, sum_negMulLog_bscWeight, sum_bscWeight, one_mul, sum_const, card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.negMulLog, one_div, inv_pow, Real.log_inv, Real.log_pow]
  push_cast
  field_simp
  ring

theorem entropy_dictator (i : Fin n) :
    H[fun ω : (Fin n → Bool) × (Fin n → Bool) => ω.1 i ;
      SlepianWolf.seqMeasure (bscPair α h0 h1) n] = Real.log 2 := by
  have hm : (SlepianWolf.seqMeasure (bscPair α h0 h1) n).map (fun ω => ω.1 i) =
      ((SlepianWolf.seqMeasure (bscPair α h0 h1) n).map fun ω => (ω.1 i, ω.2)).map Prod.fst :=
    by rw [Measure.map_map measurable_fst (measurable_of_finite _)]; rfl
  have := entropy_eq_log_card (SlepianWolf.seqMeasure (bscPair α h0 h1) n)
    (X := fun ω : (Fin n → Bool) × (Fin n → Bool) => ω.1 i) fun b => by
      rw [hm, DMC.measureReal_map_fst]
      simp only [measureReal_dictator_pair h0 h1, Fintype.card_bool]
      have h := sum_prod_mul_apply (fun (_ : Fin n) (_ : Bool) => (1 / 2 : ℝ))
        (fun _ => by simp) (fun a => bscWeight α b a) i
      simp only [prod_const, card_univ, Fintype.card_fin] at h
      rw [h]
      cases b <;> simp [bscWeight] <;> ring
  simpa using this

theorem entropy_output :
    H[fun ω : (Fin n → Bool) × (Fin n → Bool) => ω.2 ;
      SlepianWolf.seqMeasure (bscPair α h0 h1) n] = n * Real.log 2 := by
  classical
  have := entropy_eq_log_card (SlepianWolf.seqMeasure (bscPair α h0 h1) n)
    (X := fun ω : (Fin n → Bool) × (Fin n → Bool) => ω.2) fun y => by
      rw [measureReal_map_singleton, sum_filter, Fintype.sum_prod_type]
      simp only [SlepianWolf.seqMeasure_real_singleton, prod_half h0 h1, sum_ite_eq',
        mem_univ, ite_true, ← mul_sum]
      rw [← Fintype.prod_sum fun j a => bscWeight α a (y j)]
      simp only [sum_bscWeight, prod_const_one, mul_one]
      simp
  rw [this, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  norm_num

theorem mutualInfo_dictator (i : Fin n) :
    I[fun ω : (Fin n → Bool) × (Fin n → Bool) => ω.1 i : fun ω => ω.2 ;
      SlepianWolf.seqMeasure (bscPair α h0 h1) n] = Real.log 2 - Real.binEntropy α := by
  rw [mutualInfo_def, entropy_dictator h0 h1, entropy_output h0 h1, entropy_dictator_pair h0 h1]
  ring

theorem mutualInfoBits_dictator (i : Fin n) :
    I₂[fun ω : (Fin n → Bool) × (Fin n → Bool) => ω.1 i : fun ω => ω.2 ;
      SlepianWolf.seqMeasure (bscPair α h0 h1) n] = 1 - Real.binEntropy α / Real.log 2 := by
  rw [mutualInfoBits_def, mutualInfo_dictator h0 h1, sub_div, div_self log_two_ne_zero]

end CourtadeKumar

end Meat
