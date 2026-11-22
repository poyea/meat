import Meat.Shannon.Relabel
import Meat.Shannon.Typical

open MeasureTheory Finset

namespace Meat

variable {S T : Type*}
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem condEntropy_fst_snd_toMeasure (p : PMF (S × T)) :
    condEntropy (fun ω : S × T => ω.1) (fun ω => ω.2) p.toMeasure
      = measureEntropy p.toMeasure - measureEntropy (p.map Prod.snd).toMeasure := by
  have h : p.toMeasure.map (fun ω : S × T => (ω.1, ω.2)) = p.toMeasure := Measure.map_id'
  rw [condEntropy_def, entropy, entropy, h,
    PMF.toMeasure_map (f := Prod.snd) (p := p) (hf := measurable_snd)]

theorem condEntropy_snd_fst_toMeasure (p : PMF (S × T)) :
    condEntropy (fun ω : S × T => ω.2) (fun ω => ω.1) p.toMeasure
      = measureEntropy p.toMeasure - measureEntropy (p.map Prod.fst).toMeasure := by
  have h : p.toMeasure.map (fun ω : S × T => (ω.2, ω.1)) = p.toMeasure.map Prod.swap := rfl
  rw [condEntropy_def, entropy, entropy, h, measureEntropy_map_of_injective _ Prod.swap_injective,
    PMF.toMeasure_map (f := Prod.fst) (p := p) (hf := measurable_fst)]

theorem sum_negMulLog_iidProb (q : PMF S) (n : ℕ) :
    ∑ x : Fin n → S, Real.negMulLog (iidProb q x) = n * measureEntropy q.toMeasure := by
  simp_rw [negMulLog_iidProb, mul_sum]
  rw [sum_comm]
  have h : ∀ i : Fin n, ∑ x : Fin n → S, iidProb q x * -Real.log (q (x i)).toReal
      = measureEntropy q.toMeasure := fun i =>
    (sum_prod_mul_apply (fun _ s => (q s).toReal) (fun _ => sum_toReal_pmf_eq_one q)
      (fun s => -Real.log (q s).toReal) i).trans (sum_toReal_mul_neg_log q)
  rw [sum_congr rfl fun i _ => h i, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

end Meat
