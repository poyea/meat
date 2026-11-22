import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.UniformOn
import Meat.Shannon.Inequalities

open MeasureTheory

namespace Meat

variable {Ω S T : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S]
  [Fintype T] [MeasurableSpace T]

noncomputable def klDiv (ν ρ : Measure S) : ℝ :=
  ∑ s, ν.real {s} * Real.log (ν.real {s} / ρ.real {s})

noncomputable def condKLDiv (ν ρ : Measure S) (f : S → T) : ℝ :=
  ∑ s, ν.real {s} *
    Real.log (ν.real {s} * (ρ.map f).real {f s} / (ρ.real {s} * (ν.map f).real {f s}))

theorem klDiv_self (ν : Measure S) : klDiv ν ν = 0 :=
  Finset.sum_eq_zero fun s _ => by
    by_cases h : ν.real {s} = 0 <;> simp [h]

private lemma sum_mul_log_div_eq {ι : Type*} (s : Finset ι) {p q : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpq : ∀ i ∈ s, q i = 0 → p i = 0) :
    ∑ i ∈ s, p i * Real.log (p i / q i)
      = ∑ i ∈ s, p i * Real.log (p i) - ∑ i ∈ s, p i * Real.log (q i) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases (hp i hi).eq_or_lt with h0 | h0
  · simp [← h0]
  have hq0 : q i ≠ 0 := fun h' => h0.ne' (hpq i hi h')
  rw [Real.log_div h0.ne' hq0, mul_sub]

private lemma sum_mul_log_div_nonneg {ι : Type*} (s : Finset ι) {p q : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i) (hpq : ∀ i ∈ s, q i = 0 → p i = 0)
    (hsum : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    0 ≤ ∑ i ∈ s, p i * Real.log (p i / q i) := by
  rw [sum_mul_log_div_eq s hp hpq]
  linarith [sum_mul_log_le_sum_mul_log s hp hq hpq hsum]

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

omit [Fintype S] [MeasurableSingletonClass S] in
private lemma measureReal_eq_zero_of_ac {ν ρ : Measure S} [IsFiniteMeasure ρ] (h : ν ≪ ρ)
    {s : S} (hs : ρ.real {s} = 0) : ν.real {s} = 0 := by
  rw [measureReal_eq_zero_iff] at hs
  simp [Measure.real, h hs]

theorem klDiv_nonneg {ν ρ : Measure S} [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (h : ν ≪ ρ) : 0 ≤ klDiv ν ρ :=
  sum_mul_log_div_nonneg Finset.univ (fun _ _ => measureReal_nonneg)
    (fun _ _ => measureReal_nonneg) (fun _ _ hs => measureReal_eq_zero_of_ac h hs)
    (by rw [sum_measureReal_singleton_eq_one, sum_measureReal_singleton_eq_one])

theorem klDiv_eq_zero_iff {ν ρ : Measure S} [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (h : ν ≪ ρ) : klDiv ν ρ = 0 ↔ ν = ρ := by
  refine ⟨fun h0 => ?_, fun e => e ▸ klDiv_self ν⟩
  have hp : ∀ s ∈ Finset.univ, 0 ≤ ν.real {s} := fun _ _ => measureReal_nonneg
  have hpq : ∀ s ∈ Finset.univ, ρ.real {s} = 0 → ν.real {s} = 0 := fun _ _ hs =>
    measureReal_eq_zero_of_ac h hs
  rw [klDiv, sum_mul_log_div_eq Finset.univ hp hpq, sub_eq_zero, eq_comm] at h0
  have hs := (sum_mul_log_eq_sum_mul_log_iff Finset.univ hp (fun _ _ => measureReal_nonneg) hpq
    (by rw [sum_measureReal_singleton_eq_one, sum_measureReal_singleton_eq_one])).1 h0
  refine Measure.ext_of_singleton fun s => ?_
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
    (hs s (Finset.mem_univ s)).symm

theorem klDiv_eq_klDiv_map_add_condKLDiv {ν ρ : Measure S} [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ] (h : ν ≪ ρ) (f : S → T) :
    klDiv ν ρ = klDiv (ν.map f) (ρ.map f) + condKLDiv ν ρ f := by
  rw [klDiv, klDiv, condKLDiv, ← sum_measureReal_mul_comp ν f, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases (measureReal_nonneg (μ := ν) (s := {s})).eq_or_lt with h0 | h0
  · simp [← h0]
  have hρ : 0 < ρ.real {s} :=
    measureReal_nonneg.lt_of_ne fun h' => h0.ne' (measureReal_eq_zero_of_ac h h'.symm)
  have hN := h0.trans_le (measureReal_singleton_le_map ν f s)
  have hR := hρ.trans_le (measureReal_singleton_le_map ρ f s)
  rw [← mul_add, ← Real.log_mul (by positivity) (by positivity)]
  congr 2
  field_simp

omit [Fintype T] in
theorem condKLDiv_nonneg [Finite T] {ν ρ : Measure S} [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    (h : ν ≪ ρ) (f : S → T) : 0 ≤ condKLDiv ν ρ f := by
  have := Fintype.ofFinite T
  let N : T → ℝ := fun t => (ν.map f).real {t}
  let R : T → ℝ := fun t => (ρ.map f).real {t}
  have hle := sum_mul_log_div_nonneg Finset.univ (p := fun s => ν.real {s})
    (q := fun s => ρ.real {s} * (N (f s) / R (f s))) (fun _ _ => measureReal_nonneg)
    (fun _ _ => mul_nonneg measureReal_nonneg (div_nonneg measureReal_nonneg measureReal_nonneg))
    (fun s _ hs => by
      rcases mul_eq_zero.1 hs with hs | hs
      · exact measureReal_eq_zero_of_ac h hs
      rcases div_eq_zero_iff.1 hs with hs | hs
      · exact le_antisymm (hs ▸ measureReal_singleton_le_map ν f s) measureReal_nonneg
      · exact measureReal_eq_zero_of_ac h
          (le_antisymm (hs ▸ measureReal_singleton_le_map ρ f s) measureReal_nonneg))
    (by
      rw [sum_measureReal_mul_comp ρ f (fun t => N t / R t),
        show ∑ s, ν.real {s} = ∑ s, ν.real {s} * (fun _ => (1 : ℝ)) (f s) by simp,
        sum_measureReal_mul_comp ν f (fun _ => 1)]
      refine Finset.sum_le_sum fun t _ => ?_
      change R t * (N t / R t) ≤ N t * 1
      rcases (measureReal_nonneg (μ := ρ.map f) (s := {t})).eq_or_lt with h0 | h0
      · change 0 = R t at h0
        rw [← h0, zero_mul, mul_one]
        exact measureReal_nonneg
      · rw [mul_div_cancel₀ _ h0.ne', mul_one])
  refine hle.trans_eq (Finset.sum_congr rfl fun s _ => ?_)
  simp only [N, R]
  rw [mul_div_assoc', div_div_eq_mul_div]

theorem klDiv_map_le {ν ρ : Measure S} [IsFiniteMeasure ν] [IsFiniteMeasure ρ] (h : ν ≪ ρ)
    (f : S → T) : klDiv (ν.map f) (ρ.map f) ≤ klDiv ν ρ := by
  rw [klDiv_eq_klDiv_map_add_condKLDiv h f]
  linarith [condKLDiv_nonneg h f]

theorem measureEntropy_eq_log_card_sub_klDiv (ν : Measure S) [IsProbabilityMeasure ν] :
    measureEntropy ν
      = Real.log (Fintype.card S) - klDiv ν (ProbabilityTheory.uniformOn Set.univ) := by
  have hu : ∀ s : S, (ProbabilityTheory.uniformOn (Set.univ : Set S)).real {s}
      = ((Fintype.card S : ℝ))⁻¹ := fun s => by
    simp [measureReal_def, ProbabilityTheory.uniformOn_univ, ENNReal.toReal_inv]
  have e : klDiv ν (ProbabilityTheory.uniformOn Set.univ)
      = ∑ s, ν.real {s} * Real.log (ν.real {s}) + ∑ s, ν.real {s} * Real.log (Fintype.card S) := by
    rw [klDiv, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hu, div_inv_eq_mul, ← mul_add]
    by_cases h0 : ν.real {s} = 0
    · simp [h0]
    rw [Real.log_mul h0 (Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨s⟩).ne')]
  rw [e, ← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul,
    measureEntropy_eq_neg_sum_mul_log]
  ring

theorem entropy_eq_log_card_sub_klDiv (X : Ω → S) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    H[X ; μ]
      = Real.log (Fintype.card S) - klDiv (μ.map X) (ProbabilityTheory.uniformOn Set.univ) :=
  measureEntropy_eq_log_card_sub_klDiv _

theorem mutualInfo_eq_klDiv {X : Ω → S} {Y : Ω → T} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) :
    I[X : Y ; μ] = klDiv (μ.map (fun ω => (X ω, Y ω))) ((μ.map X).prod (μ.map Y)) := by
  set ν := μ.map fun ω => (X ω, Y ω)
  have h1 : ν.map Prod.fst = μ.map X := by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    rfl
  have h2 : ν.map Prod.snd = μ.map Y := by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    rfl
  have e1 := measureEntropy_map_eq_neg_sum_mul_log ν Prod.fst
  have e2 := measureEntropy_map_eq_neg_sum_mul_log ν Prod.snd
  rw [h1] at e1
  rw [h2] at e2
  have e3 := measureEntropy_eq_neg_sum_mul_log ν
  have hp : ∀ x : S × T, ((μ.map X).prod (μ.map Y)).real {x}
      = (μ.map X).real {x.1} * (μ.map Y).real {x.2} := fun x => by
    rw [← Set.singleton_prod_singleton, measureReal_prod_prod]
  have e : klDiv ν ((μ.map X).prod (μ.map Y))
      = ∑ x, ν.real {x} * Real.log (ν.real {x})
        - ∑ x, ν.real {x} * Real.log ((μ.map X).real {x.1})
        - ∑ x, ν.real {x} * Real.log ((μ.map Y).real {x.2}) := by
    rw [klDiv, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hp]
    rcases (measureReal_nonneg (μ := ν) (s := {x})).eq_or_lt with h0 | h0
    · simp [← h0]
    have hx := h0.trans_le (measureReal_singleton_le_map ν Prod.fst x)
    have hy := h0.trans_le (measureReal_singleton_le_map ν Prod.snd x)
    rw [h1] at hx
    rw [h2] at hy
    rw [Real.log_div h0.ne' (by positivity), Real.log_mul hx.ne' hy.ne']
    ring
  rw [e, mutualInfo, entropy, entropy, entropy, e1, e2, e3]
  ring

end Meat
