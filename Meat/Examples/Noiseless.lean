import Meat.Examples.Uniform
import Meat.Source.RateDistortion

open MeasureTheory

namespace Meat.Examples

variable {A B : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

omit [Fintype B] in
theorem outputLaw_real [Finite B] (W : DMC A B) (p : PMF A) (b : B) :
    ((W.jointMeasure p).map Prod.snd).real {b} = ∑ a, (p a).toReal * (W a b).toReal := by
  simp only [DMC.measureReal_map_snd, DMC.jointMeasure_real_singleton]

theorem condEntropy_of_rows (W : DMC A B) (p : PMF A) {c : ℝ}
    (h : ∀ a, ∑ b, Real.negMulLog (W a b).toReal = c) :
    H[Prod.snd | Prod.fst ; W.jointMeasure p] = c := by
  rw [DMC.condEntropy_snd_fst_jointMeasure, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  simp only [DMC.jointMeasure_real_singleton]
  have e : ∀ a, -∑ b, (p a).toReal * (W a b).toReal * Real.log (W a b).toReal =
      (p a).toReal * c := fun a => by
    rw [← h a, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [Real.negMulLog]; ring
  rw [Finset.sum_congr rfl fun a _ => e a, ← Finset.sum_mul, sum_toReal_pmf_eq_one, one_mul]

theorem inputMutualInfo_eq (W : DMC A B) (p : PMF A) :
    W.inputMutualInfo p =
      H[Prod.snd ; W.jointMeasure p] - H[Prod.snd | Prod.fst ; W.jointMeasure p] := by
  rw [DMC.inputMutualInfo, mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]

theorem capacity_eq_of_le (W : DMC A B) {C : ℝ} (hle : ∀ p, W.inputMutualInfo p ≤ C)
    (p₀ : PMF A) (h₀ : W.inputMutualInfo p₀ = C) : W.capacity = C :=
  have : Nonempty (PMF A) := ⟨p₀⟩
  le_antisymm (ciSup_le hle) (h₀ ▸ W.inputMutualInfo_le_capacity p₀)

noncomputable def noiseless (A : Type*) : DMC A A := fun a => PMF.pure a

theorem capacity_noiseless [Nonempty A] : (noiseless A).capacity = Real.log (Fintype.card A) := by
  classical
  refine capacity_eq_of_le _ (DMC.inputMutualInfo_le_log_card _) (uniformPMF A) ?_
  have hY : H[Prod.snd ; (noiseless A).jointMeasure (uniformPMF A)] =
      Real.log (Fintype.card A) :=
    entropy_eq_log_card _ fun b => by
      simp [outputLaw_real, noiseless, uniformPMF_toReal, apply_ite ENNReal.toReal]
  have hYX : H[Prod.snd | Prod.fst ; (noiseless A).jointMeasure (uniformPMF A)] = 0 :=
    condEntropy_of_rows _ _ fun a => by simp [noiseless, PMF.pure_apply, apply_ite]
  rw [inputMutualInfo_eq, hY, hYX, sub_zero]

noncomputable def constChannel (A : Type*) (w : PMF B) : DMC A B := fun _ => w

theorem inputMutualInfo_constChannel (w : PMF B) (p : PMF A) :
    (constChannel A w).inputMutualInfo p = 0 := by
  have hYX := condEntropy_of_rows (constChannel A w) p (c := ∑ b, Real.negMulLog (w b).toReal)
    fun _ => rfl
  rw [inputMutualInfo_eq, hYX, entropy_def, sub_eq_zero]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [outputLaw_real]
  simp only [constChannel]
  rw [← Finset.sum_mul, sum_toReal_pmf_eq_one, one_mul]

theorem capacity_constChannel (w : PMF B) : (constChannel A w).capacity = 0 := by
  simp [DMC.capacity, inputMutualInfo_constChannel]

end Meat.Examples
