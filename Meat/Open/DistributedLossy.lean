import Meat.Source.RateDistortionTheorem

open MeasureTheory Finset

namespace Meat

structure DLCode (S T U V : Type*) (n k₁ k₂ : ℕ) where
  enc₁ : (Fin n → S) → Fin k₁
  enc₂ : (Fin n → T) → Fin k₂
  dec : Fin k₁ × Fin k₂ → (Fin n → U) × (Fin n → V)

namespace DLCode

open RateDistortion

variable {S T U V : Type*} {n k₁ k₂ : ℕ}

noncomputable def distortion₁ [Fintype S] [Fintype T] (c : DLCode S T U V n k₁ k₂)
    (p : PMF (S × T)) (d₁ : S → U → ℝ) : ℝ :=
  ∑ xy : (Fin n → S) × (Fin n → T), iidProb p (fun i => (xy.1 i, xy.2 i)) *
    blockDist d₁ xy.1 (c.dec (c.enc₁ xy.1, c.enc₂ xy.2)).1

noncomputable def distortion₂ [Fintype S] [Fintype T] (c : DLCode S T U V n k₁ k₂)
    (p : PMF (S × T)) (d₂ : T → V → ℝ) : ℝ :=
  ∑ xy : (Fin n → S) × (Fin n → T), iidProb p (fun i => (xy.1 i, xy.2 i)) *
    blockDist d₂ xy.2 (c.dec (c.enc₁ xy.1, c.enc₂ xy.2)).2

def joint (c : DLCode S T U V n k₁ k₂) : LossyCode (S × T) (U × V) n (k₁ * k₂) :=
  ⟨fun z => finProdFinEquiv (c.enc₁ fun i => (z i).1, c.enc₂ fun i => (z i).2),
    fun m i => ((c.dec (finProdFinEquiv.symm m)).1 i, (c.dec (finProdFinEquiv.symm m)).2 i)⟩

theorem joint_distortion [Fintype S] [Fintype T] (c : DLCode S T U V n k₁ k₂)
    (p : PMF (S × T)) (d₁ : S → U → ℝ) (d₂ : T → V → ℝ) (a b : ℝ) :
    c.joint.distortion p (fun (z : S × T) (w : U × V) => a * d₁ z.1 w.1 + b * d₂ z.2 w.2) =
      a * c.distortion₁ p d₁ + b * c.distortion₂ p d₂ := by
  rw [LossyCode.distortion, ← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow _ _ _).symm,
    distortion₁, distortion₂, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun xy _ => ?_
  have he : ∀ i, (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => S) fun _ => T).symm xy i
      = (xy.1 i, xy.2 i) := fun i => rfl
  have he' : (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => S) fun _ => T).symm xy
      = fun i => (xy.1 i, xy.2 i) := rfl
  simp only [joint, Equiv.symm_apply_apply, blockDist, sum_add_distrib, ← mul_sum, he, he']
  ring

end DLCode

namespace DistributedLossy

open RateDistortion

variable {S T U V : Type*}

def Achievable [Fintype S] [Fintype T] (p : PMF (S × T)) (d₁ : S → U → ℝ) (d₂ : T → V → ℝ)
    (R₁ R₂ D₁ D₂ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k₁ k₂ : ℕ, (k₁ : ℝ) ≤ Real.exp (n * R₁) ∧ (k₂ : ℝ) ≤ Real.exp (n * R₂) ∧
      ∃ c : DLCode S T U V n k₁ k₂, c.distortion₁ p d₁ ≤ D₁ + ε ∧ c.distortion₂ p d₂ ≤ D₂ + ε

def achievableRegion [Fintype S] [Fintype T] (p : PMF (S × T)) (d₁ : S → U → ℝ)
    (d₂ : T → V → ℝ) : Set ((ℝ × ℝ) × ℝ × ℝ) :=
  {x | Achievable p d₁ d₂ x.1.1 x.1.2 x.2.1 x.2.2}

variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

noncomputable def bergerTungOuter (p : PMF (S × T)) (d₁ : S → U → ℝ) (d₂ : T → V → ℝ) :
    Set ((ℝ × ℝ) × ℝ × ℝ) :=
  {x | ∃ m₁ m₂ : ℕ, ∃ q : PMF (S × T × Fin m₁ × Fin m₂),
    ∃ φ₁ : Fin m₁ × Fin m₂ → U, ∃ φ₂ : Fin m₁ × Fin m₂ → V,
    q.map (fun ω => (ω.1, ω.2.1)) = p ∧
    MarkovChain (fun ω : S × T × Fin m₁ × Fin m₂ => ω.2.2.1) (fun ω => ω.1) (fun ω => ω.2.1)
      q.toMeasure ∧
    MarkovChain (fun ω : S × T × Fin m₁ × Fin m₂ => ω.2.2.2) (fun ω => ω.2.1) (fun ω => ω.1)
      q.toMeasure ∧
    ∑ ω, (q ω).toReal * d₁ ω.1 (φ₁ ω.2.2) ≤ x.2.1 ∧
    ∑ ω, (q ω).toReal * d₂ ω.2.1 (φ₂ ω.2.2) ≤ x.2.2 ∧
    I[fun ω : S × T × Fin m₁ × Fin m₂ => (ω.1, ω.2.1) : fun ω => ω.2.2.1 | fun ω => ω.2.2.2 ;
      q.toMeasure] ≤ x.1.1 ∧
    I[fun ω : S × T × Fin m₁ × Fin m₂ => (ω.1, ω.2.1) : fun ω => ω.2.2.2 | fun ω => ω.2.2.1 ;
      q.toMeasure] ≤ x.1.2 ∧
    I[fun ω : S × T × Fin m₁ × Fin m₂ => (ω.1, ω.2.1) : fun ω => ω.2.2 ; q.toMeasure]
      ≤ x.1.1 + x.1.2}

noncomputable def bergerTungInner (p : PMF (S × T)) (d₁ : S → U → ℝ) (d₂ : T → V → ℝ) :
    Set ((ℝ × ℝ) × ℝ × ℝ) :=
  {x | ∃ m₁ m₂ : ℕ, ∃ q : PMF (S × T × Fin m₁ × Fin m₂),
    ∃ φ₁ : Fin m₁ × Fin m₂ → U, ∃ φ₂ : Fin m₁ × Fin m₂ → V,
    q.map (fun ω => (ω.1, ω.2.1)) = p ∧
    MarkovChain (fun ω : S × T × Fin m₁ × Fin m₂ => ω.2.2.1) (fun ω => ω.1)
      (fun ω => (ω.2.1, ω.2.2.2)) q.toMeasure ∧
    MarkovChain (fun ω : S × T × Fin m₁ × Fin m₂ => ω.2.2.2) (fun ω => ω.2.1)
      (fun ω => (ω.1, ω.2.2.1)) q.toMeasure ∧
    ∑ ω, (q ω).toReal * d₁ ω.1 (φ₁ ω.2.2) ≤ x.2.1 ∧
    ∑ ω, (q ω).toReal * d₂ ω.2.1 (φ₂ ω.2.2) ≤ x.2.2 ∧
    I[fun ω : S × T × Fin m₁ × Fin m₂ => (ω.1, ω.2.1) : fun ω => ω.2.2.1 | fun ω => ω.2.2.2 ;
      q.toMeasure] ≤ x.1.1 ∧
    I[fun ω : S × T × Fin m₁ × Fin m₂ => (ω.1, ω.2.1) : fun ω => ω.2.2.2 | fun ω => ω.2.2.1 ;
      q.toMeasure] ≤ x.1.2 ∧
    I[fun ω : S × T × Fin m₁ × Fin m₂ => (ω.1, ω.2.1) : fun ω => ω.2.2 ; q.toMeasure]
      ≤ x.1.1 + x.1.2}

variable [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

noncomputable def cooperativeRegion (p : PMF (S × T)) (d₁ : S → U → ℝ) (d₂ : T → V → ℝ) :
    Set ((ℝ × ℝ) × ℝ × ℝ) :=
  {x | ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
    (x.1.1 + x.1.2, a * x.2.1 + b * x.2.2) ∈
      rateRegion p (fun (z : S × T) (w : U × V) => a * d₁ z.1 w.1 + b * d₂ z.2 w.2)}

end DistributedLossy

def DistributedLossyProblem : Prop :=
  ∀ (S T U V : Type) [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] (p : PMF (S × T))
    (d₁ : S → U → ℝ) (d₂ : T → V → ℝ), (∀ s u, 0 ≤ d₁ s u) → (∀ t v, 0 ≤ d₂ t v) →
    closure (DistributedLossy.achievableRegion p d₁ d₂) =
      closure (DistributedLossy.bergerTungInner p d₁ d₂)

namespace DistributedLossy

open RateDistortion

variable {Ω A B C D : Type*} [MeasurableSpace Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]

private lemma condMutualInfo_le_pair (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → A}
    {Y : Ω → B} {Z : Ω → C} {W : Ω → D} (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hW : Measurable W) :
    I[X : Y | Z ; μ] ≤ I[X : fun ω => (Y ω, W ω) | Z ; μ] := by
  have h0 := condMutualInfo_nonneg μ hX hW (hY.prodMk hZ)
  have e1 : H[fun ω => (X ω, (Y ω, Z ω)) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    (entropy_assoc μ).symm
  have e2 : H[fun ω => (W ω, (Y ω, Z ω)) ; μ] = H[fun ω => ((Y ω, W ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((Y ω, W ω), Z ω))
      (f := fun p => (p.1.2, (p.1.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.2.1 h.1) h.2.2
  have e3 : H[fun ω => ((X ω, W ω), (Y ω, Z ω)) ; μ]
      = H[fun ω => ((X ω, (Y ω, W ω)), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, (Y ω, W ω)), Z ω))
      (f := fun p => ((p.1.1, p.1.2.2), (p.1.2.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 (Prod.ext h.2.1 h.1.2)) h.2.2
  simp only [condMutualInfo_def, condEntropy_def] at h0 ⊢
  rw [e1, e2, e3] at h0
  linarith

private lemma MarkovChain.of_pair (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → A}
    {Y : Ω → B} {Z : Ω → C} {W : Ω → D} (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hW : Measurable W) (h : MarkovChain X Y (fun ω => (Z ω, W ω)) μ) :
    MarkovChain X Y Z μ :=
  le_antisymm ((condMutualInfo_le_pair μ hX hZ hY hW).trans h.le)
    (condMutualInfo_nonneg μ hX hZ hY)

theorem bergerTungInner_subset_bergerTungOuter {S T U V : Type*}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (p : PMF (S × T)) (d₁ : S → U → ℝ) (d₂ : T → V → ℝ) :
    bergerTungInner p d₁ d₂ ⊆ bergerTungOuter p d₁ d₂ := by
  rintro x ⟨m₁, m₂, q, φ₁, φ₂, hq, h₁, h₂, rest⟩
  exact ⟨m₁, m₂, q, φ₁, φ₂, hq,
    MarkovChain.of_pair q.toMeasure (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _) h₁,
    MarkovChain.of_pair q.toMeasure (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _) h₂, rest⟩

variable {S T U V : Type*} [Fintype S] [Fintype T]

theorem Achievable.joint {p : PMF (S × T)} {d₁ : S → U → ℝ} {d₂ : T → V → ℝ}
    {R₁ R₂ D₁ D₂ a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Achievable p d₁ d₂ R₁ R₂ D₁ D₂) :
    RateDistortion.Achievable p
      (fun (z : S × T) (w : U × V) => a * d₁ z.1 w.1 + b * d₂ z.2 w.2) (R₁ + R₂)
      (a * D₁ + b * D₂) := by
  intro ε hε
  have hc : 0 < a + b + 1 := by linarith
  obtain ⟨N, hN⟩ := h (ε / (a + b + 1)) (div_pos hε hc)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, h₁, h₂⟩ := hN n hn
  refine ⟨k₁ * k₂, ?_, c.joint, ?_⟩
  · rw [Nat.cast_mul, mul_add, Real.exp_add]
    exact mul_le_mul hk₁ hk₂ (Nat.cast_nonneg _) (Real.exp_pos _).le
  · have hab : (a + b) * (ε / (a + b + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hc]
      nlinarith
    rw [c.joint_distortion]
    nlinarith [mul_le_mul_of_nonneg_left h₁ ha, mul_le_mul_of_nonneg_left h₂ hb]

variable [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

theorem achievableRegion_subset_cooperativeRegion [Nonempty U] [Nonempty V] (p : PMF (S × T))
    (d₁ : S → U → ℝ) (d₂ : T → V → ℝ) :
    achievableRegion p d₁ d₂ ⊆ cooperativeRegion p d₁ d₂ := fun _ h _ _ ha hb =>
  mem_rateRegion_of_achievable (Achievable.joint ha hb h)

theorem isClosed_cooperativeRegion [Nonempty U] [Nonempty V] (p : PMF (S × T))
    (d₁ : S → U → ℝ) (d₂ : T → V → ℝ) : IsClosed (cooperativeRegion p d₁ d₂) := by
  have e : cooperativeRegion p d₁ d₂ = ⋂ a : ℝ, ⋂ b : ℝ, ⋂ (_ : 0 ≤ a), ⋂ (_ : 0 ≤ b),
      (fun x : (ℝ × ℝ) × ℝ × ℝ => (x.1.1 + x.1.2, a * x.2.1 + b * x.2.2)) ⁻¹'
        rateRegion p (fun (z : S × T) (w : U × V) => a * d₁ z.1 w.1 + b * d₂ z.2 w.2) := by
    ext x
    simp [cooperativeRegion]
  rw [e]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => (isClosed_rateRegion _ _).preimage (by fun_prop)

theorem closure_achievableRegion_subset_cooperativeRegion [Nonempty U] [Nonempty V]
    (p : PMF (S × T)) (d₁ : S → U → ℝ) (d₂ : T → V → ℝ) :
    closure (achievableRegion p d₁ d₂) ⊆ cooperativeRegion p d₁ d₂ :=
  closure_minimal (achievableRegion_subset_cooperativeRegion p d₁ d₂)
    (isClosed_cooperativeRegion p d₁ d₂)

end DistributedLossy

end Meat
