import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Meat.Shannon.Relabel

open MeasureTheory

namespace Meat

private lemma mul_log_sub_mul_log_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : q = 0 → p = 0) :
    p * Real.log q - p * Real.log p ≤ q - p := by
  rcases hp.eq_or_lt with h | h
  · simpa [← h] using hq
  have hq' : 0 < q := hq.lt_of_ne fun h' => h.ne' (hpq h'.symm)
  have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hq' h)) h.le
  rw [Real.log_div hq'.ne' h.ne', mul_sub, mul_sub, mul_div_cancel₀ _ h.ne'] at this
  linarith

theorem sum_mul_log_le_sum_mul_log {ι : Type*} (s : Finset ι) {p q : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i) (hpq : ∀ i ∈ s, q i = 0 → p i = 0)
    (hsum : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    ∑ i ∈ s, p i * Real.log (q i) ≤ ∑ i ∈ s, p i * Real.log (p i) := by
  have := Finset.sum_le_sum fun i hi => mul_log_sub_mul_log_le (hp i hi) (hq i hi) (hpq i hi)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at this
  linarith

theorem sum_mul_log_eq_sum_mul_log_iff {ι : Type*} (s : Finset ι) {p q : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i) (hpq : ∀ i ∈ s, q i = 0 → p i = 0)
    (hsum : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    ∑ i ∈ s, p i * Real.log (q i) = ∑ i ∈ s, p i * Real.log (p i) ↔ ∀ i ∈ s, q i = p i := by
  refine ⟨fun h => ?_, fun h => Finset.sum_congr rfl fun i hi => by rw [h i hi]⟩
  let d : ι → ℝ := fun i => q i - p i - (p i * Real.log (q i) - p i * Real.log (p i))
  have hd : ∀ i ∈ s, 0 ≤ d i := fun i hi =>
    sub_nonneg.2 (mul_log_sub_mul_log_le (hp i hi) (hq i hi) (hpq i hi))
  have hd0 : ∑ i ∈ s, d i = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg hd)
    simp only [d, Finset.sum_sub_distrib]
    linarith
  intro i hi
  have hdi : d i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hd).1 hd0 i hi
  simp only [d] at hdi
  rcases (hp i hi).eq_or_lt with h0 | h0
  · simpa [← h0] using hdi
  have hqi : 0 < q i := (hq i hi).lt_of_ne fun h' => h0.ne' (hpq i hi h'.symm)
  by_contra hne
  have hlt := Real.log_lt_sub_one_of_pos (div_pos hqi h0)
    fun h1 => hne ((div_eq_one_iff_eq h0.ne').1 h1)
  have := mul_lt_mul_of_pos_left hlt h0
  rw [Real.log_div hqi.ne' h0.ne', mul_sub, mul_sub, mul_div_cancel₀ _ h0.ne'] at this
  linarith

section Measure

variable {A B C D : Type*}
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]

theorem sum_measureReal_singleton_eq_one (ν : Measure A) [IsProbabilityMeasure ν] :
    ∑ a, ν.real {a} = 1 := by
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

omit [Fintype B] in
theorem measureReal_map_singleton [DecidableEq B] (ν : Measure A) [IsFiniteMeasure ν]
    (f : A → B) (b : B) : (ν.map f).real {b} = ∑ a with f a = b, ν.real {a} := by
  rw [map_measureReal_apply (measurable_of_finite f) (measurableSet_singleton b),
    sum_measureReal_singleton]
  congr 1
  ext a
  simp

omit [Fintype A] [Fintype B] in
theorem measureReal_singleton_le_map [Finite A] (ν : Measure A) [IsFiniteMeasure ν]
    (f : A → B) (a : A) : ν.real {a} ≤ (ν.map f).real {f a} := by
  rw [map_measureReal_apply (measurable_of_finite f) (measurableSet_singleton _)]
  exact measureReal_mono (by simp)

theorem sum_measureReal_mul_comp (ν : Measure A) [IsFiniteMeasure ν] (f : A → B) (g : B → ℝ) :
    ∑ a, ν.real {a} * g (f a) = ∑ b, (ν.map f).real {b} * g b := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ f]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_congr rfl (g := fun a => ν.real {a} * g b)
    fun a ha => by rw [(Finset.mem_filter.1 ha).2], ← Finset.sum_mul, measureReal_map_singleton]

omit [MeasurableSingletonClass A] in
theorem measureEntropy_eq_neg_sum_mul_log (ν : Measure A) :
    measureEntropy ν = -∑ a, ν.real {a} * Real.log (ν.real {a}) := by
  simp [measureEntropy, Real.negMulLog, Finset.sum_neg_distrib]

theorem measureEntropy_map_eq_neg_sum_mul_log (ν : Measure A) [IsFiniteMeasure ν] (f : A → B) :
    measureEntropy (ν.map f) = -∑ a, ν.real {a} * Real.log ((ν.map f).real {f a}) := by
  rw [measureEntropy_eq_neg_sum_mul_log,
    sum_measureReal_mul_comp ν f fun b => Real.log ((ν.map f).real {b})]

omit [MeasurableSingletonClass A] in
theorem measureEntropy_nonneg (ν : Measure A) [IsProbabilityMeasure ν] :
    0 ≤ measureEntropy ν :=
  Finset.sum_nonneg fun _ _ => Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one

theorem measureEntropy_map_le (ν : Measure A) [IsFiniteMeasure ν] (f : A → B) :
    measureEntropy (ν.map f) ≤ measureEntropy ν := by
  rw [measureEntropy_map_eq_neg_sum_mul_log, measureEntropy_eq_neg_sum_mul_log, neg_le_neg_iff]
  refine Finset.sum_le_sum fun a _ => ?_
  rcases (measureReal_nonneg (μ := ν) (s := {a})).eq_or_lt with h | h
  · simp [← h]
  exact mul_le_mul_of_nonneg_left (Real.log_le_log h (measureReal_singleton_le_map ν f a)) h.le

theorem sum_mul_log_map_mul_map_div_map (ν : Measure A) [IsFiniteMeasure ν]
    (f : A → B) (g : A → C) (k : A → D) :
    ∑ a, ν.real {a} * Real.log ((ν.map f).real {f a} * (ν.map g).real {g a}
        / (ν.map k).real {k a})
      = measureEntropy (ν.map k) - measureEntropy (ν.map f) - measureEntropy (ν.map g) := by
  have h : ∀ a, ν.real {a} * Real.log ((ν.map f).real {f a} * (ν.map g).real {g a}
      / (ν.map k).real {k a})
      = ν.real {a} * Real.log ((ν.map f).real {f a}) + ν.real {a} * Real.log ((ν.map g).real {g a})
        - ν.real {a} * Real.log ((ν.map k).real {k a}) := fun a => by
    rcases (measureReal_nonneg (μ := ν) (s := {a})).eq_or_lt with h0 | h0
    · simp [← h0]
    have h1 := h0.trans_le (measureReal_singleton_le_map ν f a)
    have h2 := h0.trans_le (measureReal_singleton_le_map ν g a)
    have h3 := h0.trans_le (measureReal_singleton_le_map ν k a)
    rw [Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']
    ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [measureEntropy_map_eq_neg_sum_mul_log, measureEntropy_map_eq_neg_sum_mul_log,
    measureEntropy_map_eq_neg_sum_mul_log]
  ring

omit [Fintype B] [Fintype C] [Fintype D] in
theorem sum_map_mul_map_div_map_le_one [Finite B] [Finite C] (ν : Measure A)
    [IsProbabilityMeasure ν]
    (f : A → B) (g : A → C) (k : A → D) (φ : B → D) (ψ : C → D)
    (hfg : Function.Injective fun a => (f a, g a)) (hf : ∀ a, φ (f a) = k a)
    (hg : ∀ a, ψ (g a) = k a) :
    ∑ a, (ν.map f).real {f a} * (ν.map g).real {g a} / (ν.map k).real {k a} ≤ 1 := by
  classical
  have := Fintype.ofFinite B
  have := Fintype.ofFinite C
  let P : B → ℝ := fun b => (ν.map f).real {b}
  let Q : C → ℝ := fun c => (ν.map g).real {c}
  let R : D → ℝ := fun d => (ν.map k).real {d}
  let F : B × C → ℝ := fun x => if ψ x.2 = φ x.1 then P x.1 * Q x.2 / R (φ x.1) else 0
  have hF : ∀ x, 0 ≤ F x := fun x => by
    simp only [F]
    split_ifs
    · exact div_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) measureReal_nonneg
    · exact le_rfl
  have hR : ∀ d, ∑ c with ψ c = d, Q c = R d := fun d => by
    change ∑ c with ψ c = d, (ν.map g).real {c} = (ν.map k).real {d}
    rw [← show ψ ∘ g = k from funext hg,
      ← Measure.map_map (measurable_of_finite ψ) (measurable_of_finite g)]
    exact (measureReal_map_singleton _ ψ d).symm
  calc ∑ a, (ν.map f).real {f a} * (ν.map g).real {g a} / (ν.map k).real {k a}
      = ∑ a, F (f a, g a) := Finset.sum_congr rfl fun a _ => by simp [F, P, Q, R, hf, hg]
    _ = ∑ x ∈ Finset.univ.image fun a => (f a, g a), F x :=
      (Finset.sum_image fun a _ b _ h => hfg h).symm
    _ ≤ ∑ x, F x := Finset.sum_le_univ_sum_of_nonneg hF
    _ ≤ 1 := by
      rw [Fintype.sum_prod_type, ← sum_measureReal_singleton_eq_one (ν.map f)]
      refine Finset.sum_le_sum fun b _ => ?_
      rw [← Finset.sum_filter, Finset.sum_congr rfl
        (g := fun c => P b / R (φ b) * Q c) fun c _ => by ring, ← Finset.mul_sum]
      change P b / R (φ b) * ∑ c with ψ c = φ b, Q c ≤ _
      rw [hR]
      rcases (measureReal_nonneg (μ := ν.map k) (s := {φ b})).eq_or_lt with h | h
      · simp only [R, ← h, mul_zero]
        exact measureReal_nonneg
      · exact (div_mul_cancel₀ _ h.ne').le

private lemma measureEntropy_add_le (ν : Measure A) [IsProbabilityMeasure ν]
    (f : A → B) (g : A → C) (k : A → D) (φ : B → D) (ψ : C → D)
    (hfg : Function.Injective fun a => (f a, g a)) (hf : ∀ a, φ (f a) = k a)
    (hg : ∀ a, ψ (g a) = k a) :
    measureEntropy ν + measureEntropy (ν.map k)
      ≤ measureEntropy (ν.map f) + measureEntropy (ν.map g) := by
  have hgibbs := sum_mul_log_le_sum_mul_log Finset.univ (p := fun a => ν.real {a})
    (q := fun a => (ν.map f).real {f a} * (ν.map g).real {g a} / (ν.map k).real {k a})
    (fun _ _ => measureReal_nonneg)
    (fun _ _ => div_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) measureReal_nonneg)
    (fun a _ h => by
      by_contra ha
      have h0 := measureReal_nonneg.lt_of_ne' ha
      exact (div_pos (mul_pos (h0.trans_le (measureReal_singleton_le_map ν f a))
        (h0.trans_le (measureReal_singleton_le_map ν g a)))
        (h0.trans_le (measureReal_singleton_le_map ν k a))).ne' h)
    ((sum_map_mul_map_div_map_le_one ν f g k φ ψ hfg hf hg).trans_eq
      (sum_measureReal_singleton_eq_one ν).symm)
  rw [sum_mul_log_map_mul_map_div_map, ← neg_neg (∑ a, _ * Real.log _),
    ← measureEntropy_eq_neg_sum_mul_log] at hgibbs
  linarith

end Measure

private lemma entropy_comp {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass A] [Finite A]
    (μ : Measure Ω) {W : Ω → A} (hW : Measurable W) (f : A → B) :
    H[fun ω => f (W ω) ; μ] = measureEntropy ((μ.map W).map f) := by
  rw [Measure.map_map (measurable_of_finite f) hW]
  rfl

variable {Ω S T U : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]

variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [MeasurableSingletonClass S] in
theorem entropy_nonneg (X : Ω → S) : 0 ≤ H[X ; μ] :=
  measureEntropy_nonneg _

theorem entropy_le_log_card : H[X ; μ] ≤ Real.log (Fintype.card S) := by
  have hgibbs := sum_mul_log_le_sum_mul_log Finset.univ (p := fun s => (μ.map X).real {s})
    (q := fun _ => ((Fintype.card S : ℝ))⁻¹) (fun _ _ => measureReal_nonneg)
    (fun _ _ => by positivity)
    (fun s _ h => absurd h (inv_ne_zero (Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨s⟩).ne')))
    (by
      rw [sum_measureReal_singleton_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_le_one)
  rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, Real.log_inv, one_mul] at hgibbs
  rw [entropy, measureEntropy_eq_neg_sum_mul_log]
  linarith

theorem condEntropy_nonneg (hX : Measurable X) (hY : Measurable Y) : 0 ≤ H[X | Y ; μ] := by
  have h : H[Y ; μ] = measureEntropy ((μ.map fun ω => (X ω, Y ω)).map Prod.snd) :=
    entropy_comp μ (hX.prodMk hY) Prod.snd
  rw [condEntropy, h, sub_nonneg]
  exact measureEntropy_map_le _ _

theorem mutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) : 0 ≤ I[X : Y ; μ] := by
  have hXY := hX.prodMk hY
  have h1 : H[X ; μ] = measureEntropy ((μ.map fun ω => (X ω, Y ω)).map Prod.fst) :=
    entropy_comp μ hXY Prod.fst
  have h2 : H[Y ; μ] = measureEntropy ((μ.map fun ω => (X ω, Y ω)).map Prod.snd) :=
    entropy_comp μ hXY Prod.snd
  have h3 : H[fun ω => (X ω, Y ω) ; μ] = measureEntropy (μ.map fun ω => (X ω, Y ω)) := rfl
  have h := measureEntropy_add_le (μ.map fun ω => (X ω, Y ω)) Prod.fst Prod.snd (fun _ => ())
    (fun _ => ()) (fun _ => ()) (fun _ _ h => Prod.ext (congrArg Prod.fst h)
      (congrArg Prod.snd h)) (fun _ => rfl) (fun _ => rfl)
  have h0 := measureEntropy_nonneg ((μ.map fun ω => (X ω, Y ω)).map fun _ => ())
  rw [mutualInfo, h1, h2, h3]
  linarith

theorem condMutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    0 ≤ I[X : Y | Z ; μ] := by
  have hW := (hX.prodMk hY).prodMk hZ
  have h1 : H[fun ω => (X ω, Z ω) ; μ]
      = measureEntropy ((μ.map fun ω => ((X ω, Y ω), Z ω)).map fun a => (a.1.1, a.2)) :=
    entropy_comp μ hW fun a => (a.1.1, a.2)
  have h2 : H[fun ω => (Y ω, Z ω) ; μ]
      = measureEntropy ((μ.map fun ω => ((X ω, Y ω), Z ω)).map fun a => (a.1.2, a.2)) :=
    entropy_comp μ hW fun a => (a.1.2, a.2)
  have h3 : H[Z ; μ] = measureEntropy ((μ.map fun ω => ((X ω, Y ω), Z ω)).map Prod.snd) :=
    entropy_comp μ hW Prod.snd
  have h4 : H[fun ω => ((X ω, Y ω), Z ω) ; μ]
      = measureEntropy (μ.map fun ω => ((X ω, Y ω), Z ω)) := rfl
  have h := measureEntropy_add_le (μ.map fun ω => ((X ω, Y ω), Z ω))
    (fun a => (a.1.1, a.2)) (fun a => (a.1.2, a.2)) Prod.snd Prod.snd Prod.snd
    (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Prod.ext h.1.1 h.2.1) h.1.2) (fun _ => rfl) (fun _ => rfl)
  simp only [condMutualInfo, condEntropy]
  rw [h1, h2, h3, h4]
  linarith

omit [IsProbabilityMeasure μ] in
theorem mutualInfo_comm : I[X : Y ; μ] = I[Y : X ; μ] := by
  rw [mutualInfo, mutualInfo, entropy_comm μ (X := X) (Y := Y)]
  ring

omit [IsProbabilityMeasure μ] in
theorem condMutualInfo_comm : I[X : Y | Z ; μ] = I[Y : X | Z ; μ] := by
  simp only [condMutualInfo, condEntropy]
  rw [entropy_comm_left μ (X := X) (Y := Y) (Z := Z)]
  ring

theorem condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) :
    H[X | Y ; μ] ≤ H[X ; μ] := by
  have h := mutualInfo_nonneg μ hX hY
  rw [mutualInfo_eq_entropy_sub_condEntropy] at h
  linarith

theorem entropy_pair_le_add (hX : Measurable X) (hY : Measurable Y) :
    H[fun ω => (X ω, Y ω) ; μ] ≤ H[X ; μ] + H[Y ; μ] := by
  have h := mutualInfo_nonneg μ hX hY
  rw [mutualInfo] at h
  linarith

theorem entropy_le_entropy_pair (hX : Measurable X) (hY : Measurable Y) :
    H[X ; μ] ≤ H[fun ω => (X ω, Y ω) ; μ] := by
  have h := condEntropy_nonneg μ hY hX
  rw [condEntropy, entropy_comm μ (X := Y) (Y := X)] at h
  linarith

theorem entropy_submodular (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[fun ω => ((X ω, Y ω), Z ω) ; μ] + H[Z ; μ]
      ≤ H[fun ω => (X ω, Z ω) ; μ] + H[fun ω => (Y ω, Z ω) ; μ] := by
  have h := condMutualInfo_nonneg μ hX hY hZ
  simp only [condMutualInfo, condEntropy] at h
  linarith

theorem entropy_comp_le (hX : Measurable X) (f : S → T) : H[f ∘ X ; μ] ≤ H[X ; μ] := by
  have h := condEntropy_nonneg μ hX ((measurable_of_finite f).comp hX)
  have h' : H[fun ω => (X ω, (f ∘ X) ω) ; μ] = H[X ; μ] := entropy_pair_comp μ f
  rw [condEntropy, h'] at h
  linarith

omit [IsProbabilityMeasure μ] in
theorem mutualInfo_pair_eq_add_condMutualInfo :
    I[X : (fun ω => (Y ω, Z ω)) ; μ] = I[X : Z ; μ] + I[X : Y | Z ; μ] := by
  simp only [mutualInfo, condMutualInfo, condEntropy]
  rw [entropy_assoc μ (X := X) (Y := Y) (Z := Z)]
  ring

theorem mutualInfo_comp_le (hX : Measurable X) (hY : Measurable Y) (f : T → U) :
    I[X : f ∘ Y ; μ] ≤ I[X : Y ; μ] := by
  have h := condMutualInfo_nonneg μ hX hY ((measurable_of_finite f).comp hY)
  have hc := mutualInfo_pair_eq_add_condMutualInfo μ (X := X) (Y := Y) (Z := f ∘ Y)
  have h1 : H[fun ω => (Y ω, (f ∘ Y) ω) ; μ] = H[Y ; μ] := entropy_pair_comp μ f
  have h2 : H[fun ω => (X ω, (Y ω, (f ∘ Y) ω)) ; μ] = H[fun ω => (X ω, Y ω) ; μ] :=
    entropy_pair_pair_comp μ f
  rw [mutualInfo, h1, h2] at hc
  linarith [mutualInfo_def X Y μ]

end Meat
