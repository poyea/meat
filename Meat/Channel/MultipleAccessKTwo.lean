import Meat.Channel.MultipleAccessKTheorem
import Meat.Channel.MultipleAccessTheorem

open MeasureTheory Finset

namespace Meat

namespace MACK

variable {A : Fin 2 → Type*} {B : Type*}

def twoChannel (W : DMC (∀ k, A k) B) : DMC (A 0 × A 1) B :=
  fun a => W ((piFinTwoEquiv A).symm a)

def twoMap (ω : (∀ k, A k) × B) : A 0 × A 1 × B :=
  (ω.1 0, ω.1 1, ω.2)

theorem twoMap_injective : Function.Injective (twoMap (A := A) (B := B)) := by
  intro ω ω' h
  simp only [twoMap, Prod.mk.injEq] at h
  refine Prod.ext (funext fun k => ?_) h.2.2
  fin_cases k
  · exact h.1
  · exact h.2.1

theorem jointPMF_map_twoMap [∀ k, Fintype (A k)] (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    (DMC.jointPMF W (piPMF p)).map twoMap = MAC.jointPMF (twoChannel W) (p 0) (p 1) := by
  ext ⟨a₀, a₁, b⟩
  have he : ((a₀, a₁, b) : A 0 × A 1 × B) = twoMap ((piFinTwoEquiv A).symm (a₀, a₁), b) := by
    simp [twoMap]
  rw [he, PMF.map_apply_of_injective _ twoMap_injective, DMC.jointPMF_apply, ← he,
    MAC.jointPMF_apply, piPMF_apply, Fin.prod_univ_two]
  simp [twoChannel, mul_assoc]

private def mask₀ (a : A 0) : Masked A :=
  fun k => Fin.cases (motive := fun k => Option (A k)) (some a) (fun _ => none) k

private def mask₁ (a : A 1) : Masked A :=
  fun k => Fin.cases (motive := fun k => Option (A k)) none
    (fun j => Fin.cases (motive := fun j => Option (A j.succ)) (some a) (fun j => j.elim0) j) k

private def mask₀₁ (q : A 0 × A 1) : Masked A :=
  fun k => some ((piFinTwoEquiv A).symm q k)

private lemma mask₀_injective : Function.Injective (mask₀ (A := A)) := fun a a' h => by
  simpa [mask₀] using congrFun h 0

private lemma mask₁_injective : Function.Injective (mask₁ (A := A)) := fun a a' h => by
  have h1 : (some a : Option (A 1)) = some a' := congrFun h 1
  exact Option.some.inj h1

private lemma mask₀₁_injective : Function.Injective (mask₀₁ (A := A)) := fun q q' h => by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [mask₀₁, Option.some.injEq, piFinTwoEquiv_symm_apply] at h0 h1
  exact Prod.ext h0 h1

private lemma mask_compl_zero (x : ∀ k, A k) : mask ({0} : Finset (Fin 2))ᶜ x = mask₁ (x 1) := by
  funext k
  fin_cases k
  · simp [mask, mask₁]
  · simp only [mask]
    simp
    rfl

private lemma mask_compl_one (x : ∀ k, A k) : mask ({1} : Finset (Fin 2))ᶜ x = mask₀ (x 0) := by
  funext k
  fin_cases k
  · simp [mask, mask₀]
  · simp only [mask]
    simp
    rfl

private lemma mask_univ_two (x : ∀ k, A k) : mask univ x = mask₀₁ (x 0, x 1) := by
  funext k
  fin_cases k <;> simp [mask, mask₀₁]

private lemma mask_univ_two' (x : ∀ k, A k) : mask univ x = (mask₀₁ ∘ Prod.swap) (x 1, x 0) := by
  rw [mask_univ_two]
  rfl

variable [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)] [∀ k, MeasurableSingletonClass (A k)]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

omit [Fintype B] in
theorem map_jointMeasure_twoMap [Finite B] (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    (W.jointMeasure (piPMF p)).map twoMap = MAC.jointMeasure (twoChannel W) (p 0) (p 1) := by
  have := Fintype.ofFinite B
  rw [DMC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _),
    jointPMF_map_twoMap]
  rfl

theorem residual_univ_two (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    residual W p univ = H[Prod.snd | fun ω : (∀ k, A k) × B => (ω.1 0, ω.1 1) ;
      W.jointMeasure (piPMF p)] :=
  condEntropy_cond_of_injective _ mask₀₁_injective fun ω => mask_univ_two ω.1

theorem residual_univ_two' (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    residual W p univ = H[Prod.snd | fun ω : (∀ k, A k) × B => (ω.1 1, ω.1 0) ;
      W.jointMeasure (piPMF p)] :=
  condEntropy_cond_of_injective _ (mask₀₁_injective.comp Prod.swap_injective)
    fun ω => mask_univ_two' ω.1

theorem residual_compl_zero (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    residual W p ({0} : Finset (Fin 2))ᶜ =
      H[Prod.snd | fun ω : (∀ k, A k) × B => ω.1 1 ; W.jointMeasure (piPMF p)] :=
  condEntropy_cond_of_injective _ mask₁_injective fun ω => mask_compl_zero ω.1

theorem residual_compl_one (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    residual W p ({1} : Finset (Fin 2))ᶜ =
      H[Prod.snd | fun ω : (∀ k, A k) × B => ω.1 0 ; W.jointMeasure (piPMF p)] :=
  condEntropy_cond_of_injective _ mask₀_injective fun ω => mask_compl_one ω.1

omit [∀ k, MeasurableSingletonClass (A k)] in
theorem residual_empty_two (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    residual W p ∅ = H[Prod.snd ; W.jointMeasure (piPMF p)] := by
  set μ := W.jointMeasure (piPMF p)
  have h1 : residual W p ∅ = H[Prod.snd | fun _ : (∀ k, A k) × B => () ; μ] :=
    condEntropy_cond_of_injective _ (e := fun (_ : Unit) => (fun _ => none : Masked A))
      (fun _ _ _ => rfl) fun ω => by
        funext k
        simp [mask]
  have h2 : H[fun ω : (∀ k, A k) × B => (ω.2, ()) ; μ] = H[Prod.snd ; μ] :=
    entropy_comp_of_injective μ (X := Prod.snd) (f := fun b : B => (b, ()))
      fun _ _ h => congrArg Prod.fst h
  have h3 : H[fun _ : (∀ k, A k) × B => () ; μ] = 0 := by
    have := entropy_le_log_card μ (X := fun _ : (∀ k, A k) × B => ())
    have h0 := entropy_nonneg μ (fun _ : (∀ k, A k) × B => ())
    simp only [Fintype.card_unit, Nat.cast_one, Real.log_one] at this
    linarith
  rw [h1, condEntropy_def, h2, h3, sub_zero]

theorem subsetInfo_zero_two (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    subsetInfo W p {0} = I[fun ω : A 0 × A 1 × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
      MAC.jointMeasure (twoChannel W) (p 0) (p 1)] := by
  rw [subsetInfo_eq_residual, residual_compl_zero, residual_univ_two,
    condMutualInfo_eq_condEntropy_sub_condEntropy, ← map_jointMeasure_twoMap,
    condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
    condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  rfl

theorem subsetInfo_one_two (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    subsetInfo W p {1} = I[fun ω : A 0 × A 1 × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
      MAC.jointMeasure (twoChannel W) (p 0) (p 1)] := by
  rw [subsetInfo_eq_residual, residual_compl_one, residual_univ_two',
    condMutualInfo_eq_condEntropy_sub_condEntropy, ← map_jointMeasure_twoMap,
    condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
    condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  rfl

theorem subsetInfo_univ_two (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    subsetInfo W p univ = I[fun ω : A 0 × A 1 × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
      MAC.jointMeasure (twoChannel W) (p 0) (p 1)] := by
  rw [subsetInfo_eq_residual, compl_univ, residual_empty_two, residual_univ_two, mutualInfo_comm,
    mutualInfo_eq_entropy_sub_condEntropy, ← map_jointMeasure_twoMap,
    entropy_map _ (measurable_of_finite _) (measurable_of_finite _),
    condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  rfl

theorem mem_polymatroid_two_iff (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) (R : Fin 2 → ℝ) :
    R ∈ polymatroid W p ↔ (R 0, R 1) ∈ MAC.pentagon (twoChannel W) (p 0) (p 1) := by
  have hS : ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = univ := by decide
  constructor
  · rintro ⟨h0, h⟩
    have h₀ := h {0}
    have h₁ := h {1}
    have h₂ := h univ
    rw [sum_singleton, subsetInfo_zero_two] at h₀
    rw [sum_singleton, subsetInfo_one_two] at h₁
    rw [Fin.sum_univ_two, subsetInfo_univ_two] at h₂
    exact ⟨h0 0, h0 1, h₀, h₁, h₂⟩
  · rintro ⟨h0, h1, h₀, h₁, h₂⟩
    refine ⟨fun k => ?_, fun S => ?_⟩
    · fin_cases k
      · exact h0
      · exact h1
    · rcases hS S with rfl | rfl | rfl | rfl
      · rw [sum_empty, subsetInfo_empty]
      · rw [sum_singleton, subsetInfo_zero_two]
        exact h₀
      · rw [sum_singleton, subsetInfo_one_two]
        exact h₁
      · rw [Fin.sum_univ_two, subsetInfo_univ_two]
        exact h₂

theorem capacityRegion_two (W : DMC (∀ k, A k) B) :
    capacityRegion W = (fun R : Fin 2 → ℝ => (R 0, R 1)) ⁻¹' MAC.capacityRegion (twoChannel W) := by
  set L := ContinuousLinearEquiv.piFinTwo ℝ fun _ : Fin 2 => ℝ
  have hL : ∀ R : Fin 2 → ℝ, L R = (R 0, R 1) := fun R => rfl
  have hU : L '' (⋃ p : ∀ k, PMF (A k), polymatroid W p) =
      ⋃ p₁ : PMF (A 0), ⋃ p₂ : PMF (A 1), MAC.pentagon (twoChannel W) p₁ p₂ := by
    ext x
    simp only [Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨R, ⟨p, hR⟩, rfl⟩
      exact ⟨p 0, p 1, by rw [hL]; exact (mem_polymatroid_two_iff W p R).1 hR⟩
    · rintro ⟨p₁, p₂, hx⟩
      refine ⟨L.symm x, ⟨(piFinTwoEquiv fun k => PMF (A k)).symm (p₁, p₂), ?_⟩,
        L.apply_symm_apply x⟩
      rw [mem_polymatroid_two_iff]
      have e : ((L.symm x) 0, (L.symm x) 1) = x := by rw [← hL, L.apply_symm_apply]
      simpa [e] using hx
  have himg : L '' capacityRegion W = MAC.capacityRegion (twoChannel W) := by
    have h1 : L '' convexHull ℝ (⋃ p : ∀ k, PMF (A k), polymatroid W p) =
        convexHull ℝ (L '' ⋃ p : ∀ k, PMF (A k), polymatroid W p) :=
      L.toLinearEquiv.toLinearMap.image_convexHull _
    have h2 : L '' closure (convexHull ℝ (⋃ p : ∀ k, PMF (A k), polymatroid W p)) =
        closure (L '' convexHull ℝ (⋃ p : ∀ k, PMF (A k), polymatroid W p)) :=
      L.toHomeomorph.image_closure _
    rw [capacityRegion, MAC.capacityRegion, h2, h1, hU]
  ext R
  simp only [Set.mem_preimage, ← hL, ← himg]
  exact (L.injective.mem_set_image).symm

end MACK

end Meat
