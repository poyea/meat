import Meat.Source.RateDistortionTheorem

open MeasureTheory Finset

namespace Meat

structure MDCode (S T : Type*) (n k₁ k₂ : ℕ) where
  enc₁ : (Fin n → S) → Fin k₁
  enc₂ : (Fin n → S) → Fin k₂
  dec₀ : Fin k₁ × Fin k₂ → Fin n → T
  dec₁ : Fin k₁ → Fin n → T
  dec₂ : Fin k₂ → Fin n → T

namespace MDCode

variable {S T : Type*} {n k₁ k₂ : ℕ}

def side₁ (c : MDCode S T n k₁ k₂) : LossyCode S T n k₁ := ⟨c.enc₁, c.dec₁⟩

def side₂ (c : MDCode S T n k₁ k₂) : LossyCode S T n k₂ := ⟨c.enc₂, c.dec₂⟩

def central (c : MDCode S T n k₁ k₂) : LossyCode S T n (k₁ * k₂) :=
  ⟨fun x => finProdFinEquiv (c.enc₁ x, c.enc₂ x), fun m => c.dec₀ (finProdFinEquiv.symm m)⟩

theorem central_distortion [Fintype S] (c : MDCode S T n k₁ k₂) (p : PMF S) (d : S → T → ℝ) :
    c.central.distortion p d =
      ∑ x, iidProb p x * RateDistortion.blockDist d x (c.dec₀ (c.enc₁ x, c.enc₂ x)) := by
  simp only [central, LossyCode.distortion, Equiv.symm_apply_apply]

end MDCode

namespace MultipleDescriptions

open RateDistortion

variable {S T : Type*}

def Achievable [Fintype S] (p : PMF S) (d : S → T → ℝ) (R₁ R₂ D₀ D₁ D₂ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k₁ k₂ : ℕ, (k₁ : ℝ) ≤ Real.exp (n * R₁) ∧ (k₂ : ℝ) ≤ Real.exp (n * R₂) ∧
      ∃ c : MDCode S T n k₁ k₂, c.central.distortion p d ≤ D₀ + ε ∧
        c.side₁.distortion p d ≤ D₁ + ε ∧ c.side₂.distortion p d ≤ D₂ + ε

def achievableRegion [Fintype S] (p : PMF S) (d : S → T → ℝ) : Set ((ℝ × ℝ) × ℝ × ℝ × ℝ) :=
  {x | Achievable p d x.1.1 x.1.2 x.2.1 x.2.2.1 x.2.2.2}

variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

noncomputable def expectedDist {V : Type*} [Fintype V] (q : PMF (S × V)) (d : S → T → ℝ)
    (f : V → T) : ℝ :=
  ∑ ω, (q ω).toReal * d ω.1 (f ω.2)

noncomputable def elGamalCoverRegion (p : PMF S) (d : S → T → ℝ) :
    Set ((ℝ × ℝ) × ℝ × ℝ × ℝ) :=
  {x | ∃ q : PMF (S × T × T × T), q.map Prod.fst = p ∧
    expectedDist q d (fun v => v.1) ≤ x.2.1 ∧
    expectedDist q d (fun v => v.2.1) ≤ x.2.2.1 ∧
    expectedDist q d (fun v => v.2.2) ≤ x.2.2.2 ∧
    I[fun ω : S × T × T × T => ω.1 : fun ω => ω.2.2.1 ; q.toMeasure] ≤ x.1.1 ∧
    I[fun ω : S × T × T × T => ω.1 : fun ω => ω.2.2.2 ; q.toMeasure] ≤ x.1.2 ∧
    I[fun ω : S × T × T × T => ω.1 : fun ω => ω.2 ; q.toMeasure] +
      I[fun ω : S × T × T × T => ω.2.2.1 : fun ω => ω.2.2.2 ; q.toMeasure] ≤ x.1.1 + x.1.2}

noncomputable def zhangBergerRegion (p : PMF S) (d : S → T → ℝ) :
    Set ((ℝ × ℝ) × ℝ × ℝ × ℝ) :=
  {x | ∃ m : ℕ, ∃ q : PMF (S × Fin m × T × T × T), q.map Prod.fst = p ∧
    expectedDist q d (fun v => v.2.1) ≤ x.2.1 ∧
    expectedDist q d (fun v => v.2.2.1) ≤ x.2.2.1 ∧
    expectedDist q d (fun v => v.2.2.2) ≤ x.2.2.2 ∧
    I[fun ω : S × Fin m × T × T × T => ω.1 : fun ω => (ω.2.1, ω.2.2.2.1) ; q.toMeasure]
      ≤ x.1.1 ∧
    I[fun ω : S × Fin m × T × T × T => ω.1 : fun ω => (ω.2.1, ω.2.2.2.2) ; q.toMeasure]
      ≤ x.1.2 ∧
    2 * I[fun ω : S × Fin m × T × T × T => ω.1 : fun ω => ω.2.1 ; q.toMeasure] +
      I[fun ω : S × Fin m × T × T × T => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        q.toMeasure] +
      I[fun ω : S × Fin m × T × T × T => ω.2.2.2.1 : fun ω => ω.2.2.2.2 | fun ω => ω.2.1 ;
        q.toMeasure] ≤ x.1.1 + x.1.2}

noncomputable def outerRegion (p : PMF S) (d : S → T → ℝ) : Set ((ℝ × ℝ) × ℝ × ℝ × ℝ) :=
  {x | (x.1.1, x.2.2.1) ∈ rateRegion p d ∧ (x.1.2, x.2.2.2) ∈ rateRegion p d ∧
    (x.1.1 + x.1.2, x.2.1) ∈ rateRegion p d}

end MultipleDescriptions

def MultipleDescriptionsProblem : Prop :=
  ∀ (S T : Type) [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] (p : PMF S)
    (d : S → T → ℝ), (∀ s t, 0 ≤ d s t) →
    closure (MultipleDescriptions.achievableRegion p d) =
      closure (MultipleDescriptions.zhangBergerRegion p d)

namespace MultipleDescriptions

open RateDistortion

variable {S T : Type*} [Fintype S]

theorem Achievable.side₁ {p : PMF S} {d : S → T → ℝ} {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h : Achievable p d R₁ R₂ D₀ D₁ D₂) : RateDistortion.Achievable p d R₁ D₁ := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, -, c, -, h₁, -⟩ := hN n hn
  exact ⟨k₁, hk₁, c.side₁, h₁⟩

theorem Achievable.side₂ {p : PMF S} {d : S → T → ℝ} {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h : Achievable p d R₁ R₂ D₀ D₁ D₂) : RateDistortion.Achievable p d R₂ D₂ := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, -, hk₂, c, -, -, h₂⟩ := hN n hn
  exact ⟨k₂, hk₂, c.side₂, h₂⟩

theorem Achievable.central {p : PMF S} {d : S → T → ℝ} {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h : Achievable p d R₁ R₂ D₀ D₁ D₂) : RateDistortion.Achievable p d (R₁ + R₂) D₀ := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, h₀, -⟩ := hN n hn
  refine ⟨k₁ * k₂, ?_, c.central, h₀⟩
  rw [Nat.cast_mul, mul_add, Real.exp_add]
  exact mul_le_mul hk₁ hk₂ (Nat.cast_nonneg _) (Real.exp_pos _).le

variable [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem achievableRegion_subset_outerRegion [Nonempty T] (p : PMF S) (d : S → T → ℝ) :
    achievableRegion p d ⊆ outerRegion p d := fun _ h =>
  ⟨mem_rateRegion_of_achievable (Achievable.side₁ h),
    mem_rateRegion_of_achievable (Achievable.side₂ h),
    mem_rateRegion_of_achievable (Achievable.central h)⟩

theorem isClosed_outerRegion [Nonempty T] (p : PMF S) (d : S → T → ℝ) :
    IsClosed (outerRegion p d) := by
  have h := isClosed_rateRegion p d
  refine (h.preimage ?_).inter ((h.preimage ?_).inter (h.preimage ?_)) <;> fun_prop

theorem closure_achievableRegion_subset_outerRegion [Nonempty T] (p : PMF S)
    (d : S → T → ℝ) : closure (achievableRegion p d) ⊆ outerRegion p d :=
  closure_minimal (achievableRegion_subset_outerRegion p d) (isClosed_outerRegion p d)

theorem mem_rateRegion_of_pmf [Nonempty T] {V : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {p : PMF S} {d : S → T → ℝ} (q : PMF (S × V))
    (hq : q.map Prod.fst = p) (f : V → T) {R D : ℝ} (hD : expectedDist q d f ≤ D)
    (hR : I[fun ω : S × V => ω.1 : fun ω => f ω.2 ; q.toMeasure] ≤ R) :
    (R, D) ∈ rateRegion p d := by
  have hp : q.toMeasure.map Prod.fst = p.toMeasure := by
    rw [PMF.toMeasure_map _ _ measurable_fst, hq]
  obtain ⟨W, hI, hE⟩ := exists_inputMutualInfo_eq q.toMeasure (X := fun ω : S × V => ω.1)
    (Y := fun ω => f ω.2) measurable_fst (measurable_of_finite _) p hp d
  rw [rateRegion_eq]
  refine ⟨W, ?_, hI ▸ hR⟩
  rw [hE, ← sum_measureReal_mul_comp q.toMeasure (fun ω : S × V => (ω.1, f ω.2))
    (fun z => d z.1 z.2)]
  refine le_of_eq_of_le (sum_congr rfl fun ω _ => ?_) hD
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

theorem elGamalCoverRegion_subset_outerRegion [Nonempty T] (p : PMF S) (d : S → T → ℝ) :
    elGamalCoverRegion p d ⊆ outerRegion p d := by
  rintro x ⟨q, hq, h₀, h₁, h₂, hR₁, hR₂, hR⟩
  refine ⟨mem_rateRegion_of_pmf q hq _ h₁ hR₁, mem_rateRegion_of_pmf q hq _ h₂ hR₂,
    mem_rateRegion_of_pmf q hq _ h₀ ?_⟩
  have hm : I[fun ω : S × T × T × T => ω.1 : (fun v : T × T × T => v.1) ∘ fun ω => ω.2 ;
      q.toMeasure] ≤ I[fun ω : S × T × T × T => ω.1 : fun ω => ω.2 ; q.toMeasure] :=
    mutualInfo_comp_le q.toMeasure measurable_fst measurable_snd _
  have h0 := mutualInfo_nonneg q.toMeasure
    (X := fun ω : S × T × T × T => ω.2.2.1) (Y := fun ω => ω.2.2.2)
    (measurable_of_finite _) (measurable_of_finite _)
  exact hm.trans (by linarith)

end MultipleDescriptions

end Meat
