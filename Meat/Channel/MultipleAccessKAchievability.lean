import Meat.Channel.Converse
import Meat.Channel.MultipleAccessK
import Meat.Channel.MultipleAccessAchievability
import Meat.Shannon.Conditional
import Meat.Shannon.TypicalIntersection

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

section PiPMF

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]

theorem piPMF_apply (p : ∀ i, PMF (A i)) (x : ∀ i, A i) : piPMF p x = ∏ i, p i (x i) :=
  PMF.ofFintype_apply _ _

theorem iidProb_piPMF {n : ℕ} (p : ∀ i, PMF (A i)) (x : Fin n → ∀ i, A i) :
    iidProb (piPMF p) x = ∏ i, iidProb (p i) (fun j => x j i) := by
  simp only [iidProb, piPMF_apply, ENNReal.toReal_prod]
  exact prod_comm

theorem piPMF_map (p : ∀ i, PMF (A i)) {A' : ι → Type*} [∀ i, Fintype (A' i)]
    (f : ∀ i, A i → A' i) :
    (piPMF p).map (fun x i => f i (x i)) = piPMF fun i => (p i).map (f i) := by
  classical
  ext a
  rw [PMF.map_apply, tsum_fintype, piPMF_apply]
  simp only [PMF.map_apply, tsum_fintype]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [piPMF_apply]
  by_cases h : ∀ i, a i = f i (x i)
  · rw [ite_eq_left (funext h)]
    exact prod_congr rfl fun i _ => (ite_eq_left (h i)).symm
  · obtain ⟨i, hi⟩ := not_forall.1 h
    rw [ite_eq_right fun h' => hi (congrFun h' i)]
    exact (prod_eq_zero (mem_univ i) (ite_eq_right hi)).symm

abbrev splitEquiv (S : Finset ι) :
    (∀ i, A i) ≃ (∀ i : {i // i ∈ S}, A i) × (∀ i : {i // i ∉ S}, A i) :=
  Equiv.piEquivPiSubtypeProd (· ∈ S) A

theorem piPMF_split (S : Finset ι) (p : ∀ i, PMF (A i)) (x : ∀ i, A i) :
    piPMF p x = piPMF (fun i : {i // i ∈ S} => p i) (splitEquiv S x).1 *
      piPMF (fun i : {i // i ∉ S} => p i) (splitEquiv S x).2 := by
  simp only [piPMF_apply]
  convert (Fintype.prod_subtype_mul_prod_subtype (· ∈ S) fun i => p i (x i)).symm using 3 <;>
    first | rfl | exact congrArg _ (Subsingleton.elim _ _)

end PiPMF

theorem tendsto_sum_filter_forall {α : ℕ → Type*} [∀ n, Fintype (α n)] {w : ∀ n, α n → ℝ}
    (hw : ∀ n x, 0 ≤ w n x) (h1 : ∀ n, ∑ x, w n x = 1) {ι : Type*} (T : Finset ι)
    (P : ι → ∀ n, α n → Prop) [∀ i n, DecidablePred (P i n)]
    (hP : ∀ i ∈ T, Tendsto (fun n => ∑ x ∈ univ.filter (P i n), w n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∑ x ∈ univ.filter (fun x => ∀ i ∈ T, P i n x), w n x) atTop (𝓝 1) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [h1]
  | insert a T ha ih =>
    refine tendsto_sum_of_mem_iff_and hw (fun n => (h1 n).le) (fun n x => ?_)
      (hP a (mem_insert_self a T)) (ih fun i hi => hP i (mem_insert_of_mem hi))
    simp

namespace MACK

variable {K : ℕ} {A : Fin K → Type*} {B : Type*}

abbrev Inside (A : Fin K → Type*) (S : Finset (Fin K)) := ∀ k : {k // k ∈ S}, A k

abbrev Outside (A : Fin K → Type*) (S : Finset (Fin K)) := ∀ k : {k // k ∉ S}, A k

instance [∀ k, DecidableEq (A k)] (S : Finset (Fin K)) (n : ℕ) :
    DecidableEq (Fin n → Inside A S) :=
  inferInstance

instance [∀ k, DecidableEq (A k)] [DecidableEq B] (S : Finset (Fin K))
    (n : ℕ) : DecidableEq (Fin n → Outside A S × B) :=
  inferInstance

section Side

variable [∀ k, Fintype (A k)]

noncomputable def sideChannel (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) (S : Finset (Fin K)) :
    DMC (Inside A S) (Outside A S × B) :=
  fun u => DMC.jointPMF (fun v => W ((splitEquiv S).symm (u, v)))
    (piPMF fun k : {k // k ∉ S} => p k)

noncomputable def sidePMF (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) (S : Finset (Fin K)) :
    PMF (Inside A S × (Outside A S × B)) :=
  DMC.jointPMF (sideChannel W p S) (piPMF fun k : {k // k ∈ S} => p k)

theorem sidePMF_apply (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) (S : Finset (Fin K))
    (u : Inside A S) (v : Outside A S) (b : B) :
    sidePMF W p S (u, (v, b)) =
      piPMF p ((splitEquiv S).symm (u, v)) * W ((splitEquiv S).symm (u, v)) b := by
  rw [sidePMF, DMC.jointPMF_apply, sideChannel, DMC.jointPMF_apply,
    piPMF_split S p ((splitEquiv S).symm (u, v)), Equiv.apply_symm_apply, mul_assoc]

theorem sidePMF_eq_map (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) (S : Finset (Fin K)) :
    sidePMF W p S = (DMC.jointPMF W (piPMF p)).map
      fun ω => ((splitEquiv S ω.1).1, ((splitEquiv S ω.1).2, ω.2)) := by
  ext ⟨u, v, b⟩
  have he : (u, (v, b)) = (fun ω : (∀ k, A k) × B =>
      ((splitEquiv S ω.1).1, ((splitEquiv S ω.1).2, ω.2))) ((splitEquiv S).symm (u, v), b) := by
    simp
  rw [he, PMF.map_apply_of_injective _ (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext ((splitEquiv S).injective (Prod.ext h.1 h.2.1)) h.2.2),
    ← he, sidePMF_apply, DMC.jointPMF_apply]

theorem iidProb_sidePMF {n : ℕ} (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k))
    (S : Finset (Fin K)) (x : Fin n → ∀ k, A k) (y : Fin n → B) :
    iidProb (sidePMF W p S) (fun i => ((splitEquiv S (x i)).1, ((splitEquiv S (x i)).2, y i))) =
      iidProb (DMC.jointPMF W (piPMF p)) (fun i => (x i, y i)) := by
  simp only [iidProb]
  refine prod_congr rfl fun i _ => ?_
  rw [sidePMF_apply, DMC.jointPMF_apply, Prod.mk.eta, Equiv.symm_apply_apply]

theorem blockProb_sideChannel {n : ℕ} (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k))
    (S : Finset (Fin K)) (u : Fin n → Inside A S) (v : Fin n → Outside A S) (y : Fin n → B) :
    (DMC.blockProb (sideChannel W p S) u (fun i => (v i, y i))).toReal =
      iidProb (piPMF fun k : {k // k ∉ S} => p k) v *
        (DMC.blockProb W (fun i => (splitEquiv S).symm (u i, v i)) y).toReal := by
  simp [DMC.blockProb, sideChannel, DMC.jointPMF_apply, iidProb, ENNReal.toReal_prod,
    ENNReal.toReal_mul, prod_mul_distrib]

end Side

section Masks

private def insideMask (S : Finset (Fin K)) (u : Inside A S) : Masked A :=
  fun k => if h : k ∈ S then some (u ⟨k, h⟩) else none

private def outsideMask (S : Finset (Fin K)) (v : Outside A S × B) : B × Masked A :=
  (v.2, fun k => if h : k ∉ S then some (v.1 ⟨k, h⟩) else none)

private lemma insideMask_injective (S : Finset (Fin K)) :
    Function.Injective (insideMask (A := A) S) := fun u u' h => by
  funext k
  have := congrFun h k
  simpa [insideMask, k.2] using this

private lemma outsideMask_injective (S : Finset (Fin K)) :
    Function.Injective (outsideMask (A := A) (B := B) S) := fun v v' h => by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [outsideMask] at h1 h2
  refine Prod.ext (funext fun k => ?_) h1
  have := congrFun h2 k
  simpa [k.2] using this

end Masks

section Information

variable [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)] [∀ k, MeasurableSingletonClass (A k)]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem subsetInfo_le_inputMutualInfo (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k))
    (S : Finset (Fin K)) :
    subsetInfo W p S ≤
      (sideChannel W p S).inputMutualInfo (piPMF fun k : {k // k ∈ S} => p k) := by
  set μ := W.jointMeasure (piPMF p)
  have hmap : (sideChannel W p S).inputMutualInfo (piPMF fun k : {k // k ∈ S} => p k) =
      I[fun ω : (∀ k, A k) × B => (splitEquiv S ω.1).1 :
        fun ω => ((splitEquiv S ω.1).2, ω.2) ; μ] := by
    rw [DMC.inputMutualInfo, DMC.jointMeasure_eq_toMeasure]
    change I[_ : _ ; (sidePMF W p S).toMeasure] = _
    rw [sidePMF_eq_map, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
      mutualInfo_map _ (measurable_of_finite _) measurable_fst measurable_snd]
    rfl
  have h1 : I[fun ω : (∀ k, A k) × B => (splitEquiv S ω.1).1 :
        fun ω => ((splitEquiv S ω.1).2, ω.2) ; μ] =
      I[fun ω : (∀ k, A k) × B => mask S ω.1 : fun ω => (ω.2, mask Sᶜ ω.1) ; μ] := by
    have hl : (fun ω : (∀ k, A k) × B => mask S ω.1) =
        insideMask S ∘ fun ω => (splitEquiv S ω.1).1 := by
      funext ω k
      by_cases hk : k ∈ S <;> simp [mask, insideMask, hk]
    have hr : (fun ω : (∀ k, A k) × B => (ω.2, mask Sᶜ ω.1)) =
        outsideMask S ∘ fun ω => ((splitEquiv S ω.1).2, ω.2) := by
      funext ω
      refine Prod.ext rfl (funext fun k => ?_)
      by_cases hk : k ∈ S <;> simp [mask, outsideMask, hk]
    rw [hl, hr, mutualInfo_comp_right_of_injective μ (outsideMask_injective S),
      mutualInfo_comm μ (X := insideMask S ∘ _),
      mutualInfo_comp_right_of_injective μ (insideMask_injective S), mutualInfo_comm μ]
  have h2 := mutualInfo_pair_eq_add_condMutualInfo μ
    (X := fun ω : (∀ k, A k) × B => mask S ω.1) (Y := Prod.snd) (Z := fun ω => mask Sᶜ ω.1)
  have h0 := mutualInfo_nonneg μ (X := fun ω : (∀ k, A k) × B => mask S ω.1)
    (Y := fun ω => mask Sᶜ ω.1) (measurable_of_finite _) (measurable_of_finite _)
  rw [hmap, h1]
  change _ ≤ I[_ : fun ω : (∀ k, A k) × B => (ω.2, mask Sᶜ ω.1) ; μ]
  rw [h2]
  unfold subsetInfo
  linarith

end Information

section Decoding

variable [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)] [Fintype B] [MeasurableSpace B]

def splitSeq (S : Finset (Fin K)) (n : ℕ) :
    (Fin n → ∀ k, A k) × (Fin n → B) ≃ (Fin n → Inside A S) × (Fin n → Outside A S × B) where
  toFun xy := (fun i => (splitEquiv S (xy.1 i)).1, fun i => ((splitEquiv S (xy.1 i)).2, xy.2 i))
  invFun z := (fun i => (splitEquiv S).symm (z.1 i, (z.2 i).1), fun i => (z.2 i).2)
  left_inv xy := Prod.ext (funext fun i => (splitEquiv S).symm_apply_apply (xy.1 i)) rfl
  right_inv z := by simp

noncomputable def decodingSet (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) (n : ℕ) (ε : ℝ) :
    Finset ((Fin n → ∀ k, A k) × (Fin n → B)) := by
  classical
  exact {xy | ∀ S : Finset (Fin K), splitSeq S n xy ∈ jointlyTypicalSet (sidePMF W p S) n ε}

theorem mem_decodingSet {W : DMC (∀ k, A k) B} {p : ∀ k, PMF (A k)} {n : ℕ} {ε : ℝ}
    {xy : (Fin n → ∀ k, A k) × (Fin n → B)} :
    xy ∈ decodingSet W p n ε ↔
      ∀ S : Finset (Fin K), splitSeq S n xy ∈ jointlyTypicalSet (sidePMF W p S) n ε := by
  simp [decodingSet]

variable [∀ k, MeasurableSingletonClass (A k)] [MeasurableSingletonClass B]

theorem tendsto_sum_iidProb_decodingSet (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun n => ∑ xy ∈ decodingSet W p n ε,
      iidProb (DMC.jointPMF W (piPMF p)) (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 1) := by
  classical
  have hS : ∀ S : Finset (Fin K), Tendsto (fun n => ∑ xy ∈ univ.filter
      (fun xy => splitSeq S n xy ∈ jointlyTypicalSet (sidePMF W p S) n ε),
      iidProb (DMC.jointPMF W (piPMF p)) (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 1) := by
    intro S
    refine (tendsto_sum_iidProb_jointlyTypicalSet (sidePMF W p S) hε).congr fun n => ?_
    symm
    refine sum_equiv (splitSeq S n) (fun xy => by simp) fun xy _ => ?_
    exact (iidProb_sidePMF W p S xy.1 xy.2).symm
  have h := tendsto_sum_filter_forall
    (w := fun n (xy : (Fin n → ∀ k, A k) × (Fin n → B)) =>
      iidProb (DMC.jointPMF W (piPMF p)) (fun i => (xy.1 i, xy.2 i)))
    (fun n xy => iidProb_nonneg _ _) (fun n => sum_iidProb_pair _ n) univ
    (fun S n xy => splitSeq S n xy ∈ jointlyTypicalSet (sidePMF W p S) n ε)
    (fun S _ => hS S)
  refine h.congr fun n => sum_congr ?_ fun _ _ => rfl
  ext xy
  simp [mem_decodingSet]

end Decoding

section Random

variable {M : Fin K → Type*} {n : ℕ} [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]

noncomputable def codebookWeight (p : ∀ k, PMF (A k)) (C : ∀ k, M k → Fin n → A k) : ℝ :=
  ∏ k, ∏ j, iidProb (p k) (C k j)

def codeInput (C : ∀ k, M k → Fin n → A k) (m : ∀ k, M k) : Fin n → ∀ k, A k :=
  fun i k => C k (m k) i

theorem sum_mul_comp_eq {Γ Δ : Type*} [Fintype Γ] [Fintype Δ] [DecidableEq Δ] (w : Γ → ℝ)
    (φ : Γ → Δ) (G : Δ → ℝ) :
    ∑ C, w C * G (φ C) = ∑ d, (∑ C, if φ C = d then w C else 0) * G d := by
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun C _ => ?_
  simp [ite_mul]

private lemma ite_forall_eq_prod {ι : Type*} [Fintype ι] {P : ι → Prop} [∀ i, Decidable (P i)]
    [Decidable (∀ i, P i)] (f : ι → ℝ) :
    (if ∀ i, P i then ∏ i, f i else 0) = ∏ i, if P i then f i else 0 := by
  by_cases h : ∀ i, P i
  · rw [ite_eq_left h]
    exact prod_congr rfl fun i _ => (ite_eq_left (h i)).symm
  · obtain ⟨i, hi⟩ := not_forall.1 h
    rw [ite_eq_right h]
    exact (prod_eq_zero (mem_univ i) (ite_eq_right hi)).symm

variable [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]

private lemma sum_ite_apply {k : Fin K} (q : PMF (A k)) (m₀ : M k) (a : Fin n → A k) :
    ∑ c : M k → Fin n → A k, (if c m₀ = a then ∏ j, iidProb q (c j) else 0) =
      iidProb q a := by
  classical
  have h := sum_prod_mul_apply (fun _ x => iidProb q x) (fun _ => sum_iidProb q n)
    (fun y => if y = a then (1 : ℝ) else 0) m₀
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h
  rw [← h]

private lemma sum_ite_apply_apply {k : Fin K} (q : PMF (A k)) {m₀ m₁ : M k} (hm : m₀ ≠ m₁)
    (a a' : Fin n → A k) :
    ∑ c : M k → Fin n → A k, (if c m₀ = a ∧ c m₁ = a' then ∏ j, iidProb q (c j) else 0) =
      iidProb q a * iidProb q a' := by
  classical
  have h := sum_prod_mul_apply_apply (fun _ x => iidProb q x) (fun _ => sum_iidProb q n)
    (fun y y' => if y = a ∧ y' = a' then (1 : ℝ) else 0) hm
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h, sum_eq_single a (fun b _ hb => sum_eq_zero fun b' _ => by simp [hb]) (by simp),
    sum_eq_single a' (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem sum_ite_codeInput_eq (p : ∀ k, PMF (A k)) (m : ∀ k, M k) (x : Fin n → ∀ k, A k) :
    ∑ C : ∀ k, M k → Fin n → A k, (if codeInput C m = x then codebookWeight p C else 0) =
      iidProb (piPMF p) x := by
  classical
  have hc : ∀ C : ∀ k, M k → Fin n → A k, (if codeInput C m = x then codebookWeight p C else 0) =
      ∏ k, if C k (m k) = (fun i => x i k) then ∏ j, iidProb (p k) (C k j) else 0 := by
    intro C
    rw [← ite_forall_eq_prod]
    refine if_congr ⟨fun h k => ?_, fun h => ?_⟩ (by unfold codebookWeight; rfl) rfl
    · rw [← h]
      rfl
    · funext i k
      exact congrFun (h k) i
  simp_rw [hc]
  calc _ = ∏ k, ∑ c : M k → Fin n → A k,
        (if c (m k) = (fun i => x i k) then ∏ j, iidProb (p k) (c j) else 0) :=
        (Fintype.prod_sum _).symm
    _ = _ := by
        rw [iidProb_piPMF]
        exact prod_congr rfl fun k _ => sum_ite_apply (p k) (m k) _

theorem sum_ite_pattern_eq (p : ∀ k, PMF (A k)) (S : Finset (Fin K)) (m m' : ∀ k, M k)
    (hS : ∀ k ∈ S, m k ≠ m' k) (u u' : Fin n → Inside A S) (v : Fin n → Outside A S) :
    ∑ C : ∀ k, M k → Fin n → A k,
      (if (((fun i (k : {k // k ∈ S}) => C k (m k) i), fun i (k : {k // k ∈ S}) => C k (m' k) i),
          fun i (k : {k // k ∉ S}) => C k (m k) i) = ((u, u'), v)
        then codebookWeight p C else 0) =
      iidProb (piPMF fun k : {k // k ∈ S} => p k) u *
        iidProb (piPMF fun k : {k // k ∈ S} => p k) u' *
          iidProb (piPMF fun k : {k // k ∉ S} => p k) v := by
  classical
  set cond : ∀ k, (M k → Fin n → A k) → Prop := fun k c =>
    if h : k ∈ S then c (m k) = (fun i => u i ⟨k, h⟩) ∧ c (m' k) = (fun i => u' i ⟨k, h⟩)
    else c (m k) = fun i => v i ⟨k, h⟩ with hcond
  have hc : ∀ C : ∀ k, M k → Fin n → A k,
      (if (((fun i (k : {k // k ∈ S}) => C k (m k) i), fun i (k : {k // k ∈ S}) => C k (m' k) i),
          fun i (k : {k // k ∉ S}) => C k (m k) i) = ((u, u'), v)
        then codebookWeight p C else 0) =
      ∏ k, if cond k (C k) then ∏ j, iidProb (p k) (C k j) else 0 := by
    intro C
    rw [← ite_forall_eq_prod]
    refine if_congr ⟨fun h k => ?_, fun h => ?_⟩ (by unfold codebookWeight; rfl) rfl
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      by_cases hk : k ∈ S <;> simp [hcond, hk]
    · refine Prod.ext (Prod.ext (funext fun i => funext fun k => ?_)
        (funext fun i => funext fun k => ?_)) (funext fun i => funext fun k => ?_)
      · have := h k
        simp only [hcond, k.2, dite_true] at this
        exact congrFun this.1 i
      · have := h k
        simp only [hcond, k.2, dite_true] at this
        exact congrFun this.2 i
      · have := h k
        simp only [hcond, k.2, dite_false] at this
        exact congrFun this i
  have hk : ∀ k, ∑ c : M k → Fin n → A k, (if cond k c then ∏ j, iidProb (p k) (c j) else 0) =
      if h : k ∈ S then iidProb (p k) (fun i => u i ⟨k, h⟩) * iidProb (p k) (fun i => u' i ⟨k, h⟩)
      else iidProb (p k) (fun i => v i ⟨k, h⟩) := by
    intro k
    by_cases h : k ∈ S
    · simp only [hcond, h, dite_true]
      exact sum_ite_apply_apply (p k) (hS k h) _ _
    · simp only [hcond, h, dite_false]
      exact sum_ite_apply (p k) (m k) _
  simp_rw [hc]
  calc _ = ∏ k, ∑ c : M k → Fin n → A k,
        (if cond k c then ∏ j, iidProb (p k) (c j) else 0) := (Fintype.prod_sum _).symm
    _ = _ := by
        rw [prod_congr rfl fun k _ => hk k, Fintype.prod_dite, iidProb_piPMF,
          iidProb_piPMF, iidProb_piPMF, ← prod_mul_distrib]
        congr 1
        exact Finset.prod_congr (congrArg _ (Subsingleton.elim _ _)) fun _ _ => rfl

variable [∀ k, MeasurableSpace (A k)] [Fintype B] [MeasurableSpace B] [DecidableEq B]

theorem sum_codebookWeight_mul_sum_ite (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k))
    (m : ∀ k, M k) (ε : ℝ) :
    ∑ C : ∀ k, M k → Fin n → A k, codebookWeight p C *
        ∑ y, (if (codeInput C m, y) ∈ decodingSet W p n ε then 0
          else (DMC.blockProb W (codeInput C m) y).toReal) =
      1 - ∑ xy ∈ decodingSet W p n ε,
        iidProb (DMC.jointPMF W (piPMF p)) (fun i => (xy.1 i, xy.2 i)) := by
  classical
  have key := sum_mul_comp_eq (codebookWeight p) (fun C => codeInput C m)
    (fun x => ∑ y, if (x, y) ∈ decodingSet W p n ε then 0 else (DMC.blockProb W x y).toReal)
  beta_reduce at key
  rw [key]
  simp_rw [sum_ite_codeInput_eq]
  exact DMC.sum_iidProb_mul_sum_ite_jointPMF W (piPMF p) _

theorem sum_codebookWeight_mul_sum_le (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k))
    (S : Finset (Fin K)) (m m' : ∀ k, M k) (hS : ∀ k, k ∈ S ↔ m' k ≠ m k) (ε : ℝ) :
    ∑ C : ∀ k, M k → Fin n → A k, codebookWeight p C *
        ∑ y, (if (codeInput C m', y) ∈ decodingSet W p n ε then (1 : ℝ) else 0) *
          (DMC.blockProb W (codeInput C m) y).toReal ≤
      Real.exp (-(n * ((sideChannel W p S).inputMutualInfo
        (piPMF fun k : {k // k ∈ S} => p k) - 3 * ε))) := by
  classical
  set D := decodingSet W p n ε
  set qU := piPMF fun k : {k // k ∈ S} => p k
  set qV := piPMF fun k : {k // k ∉ S} => p k
  let mg : (Fin n → Inside A S) → (Fin n → Outside A S) → Fin n → ∀ k, A k :=
    fun u v i => (splitEquiv S).symm (u i, v i)
  let T : (Fin n → ∀ k, A k) → (Fin n → ∀ k, A k) → ℝ := fun x' x =>
    ∑ y, (if (x', y) ∈ D then (1 : ℝ) else 0) * (DMC.blockProb W x y).toReal
  let φ : (∀ k, M k → Fin n → A k) →
      ((Fin n → Inside A S) × (Fin n → Inside A S)) × (Fin n → Outside A S) := fun C =>
    (((fun i (k : {k // k ∈ S}) => C k (m k) i), fun i (k : {k // k ∈ S}) => C k (m' k) i),
      fun i (k : {k // k ∉ S}) => C k (m k) i)
  have hφ : ∀ C, T (codeInput C m') (codeInput C m) =
      T (mg (φ C).1.2 (φ C).2) (mg (φ C).1.1 (φ C).2) := by
    intro C
    have h1 : codeInput C m = mg (φ C).1.1 (φ C).2 := by
      funext i k
      by_cases hk : k ∈ S <;> simp [codeInput, mg, φ, hk]
    have h2 : codeInput C m' = mg (φ C).1.2 (φ C).2 := by
      funext i k
      by_cases hk : k ∈ S
      · simp [codeInput, mg, φ, hk]
      · have : m' k = m k := not_not.1 fun h => hk ((hS k).2 h)
        simp [codeInput, mg, φ, hk, this]
    rw [h1, h2]
  calc _ = ∑ C, codebookWeight p C * T (mg (φ C).1.2 (φ C).2) (mg (φ C).1.1 (φ C).2) :=
        sum_congr rfl fun C _ => by rw [← hφ]
    _ = ∑ t : ((Fin n → Inside A S) × (Fin n → Inside A S)) × (Fin n → Outside A S),
        (iidProb qU t.1.1 * iidProb qU t.1.2 * iidProb qV t.2) *
          T (mg t.1.2 t.2) (mg t.1.1 t.2) := by
        have key := sum_mul_comp_eq (codebookWeight p) φ
          (fun t => T (mg t.1.2 t.2) (mg t.1.1 t.2))
        beta_reduce at key
        rw [key]
        refine sum_congr rfl fun t _ => ?_
        obtain ⟨⟨u, u'⟩, v⟩ := t
        exact congrArg (· * _)
          (sum_ite_pattern_eq p S m m' (fun k hk => Ne.symm ((hS k).1 hk)) u u' v)
    _ ≤ ∑ u : Fin n → Inside A S, ∑ u' : Fin n → Inside A S, iidProb qU u * iidProb qU u' *
        ∑ z : Fin n → Outside A S × B,
          (if (u', z) ∈ jointlyTypicalSet (sidePMF W p S) n ε then (1 : ℝ) else 0) *
            (DMC.blockProb (sideChannel W p S) u z).toReal := by
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
        refine sum_le_sum fun u _ => sum_le_sum fun u' _ => ?_
        rw [sum_arrow_prod, mul_sum]
        refine sum_le_sum fun v _ => ?_
        simp only [T, mul_sum]
        refine sum_le_sum fun y _ => ?_
        rw [blockProb_sideChannel]
        have hD : (mg u' v, y) ∈ D →
            (u', fun i => (v i, y i)) ∈ jointlyTypicalSet (sidePMF W p S) n ε := by
          intro h
          have he : splitSeq S n (mg u' v, y) = (u', fun i => (v i, y i)) := by
            change (fun i => (splitEquiv S (mg u' v i)).1,
              fun i => ((splitEquiv S (mg u' v i)).2, y i)) = _
            simp only [mg, Equiv.apply_symm_apply]
          have := mem_decodingSet.1 h S
          rwa [he] at this
        have hb : 0 ≤ (DMC.blockProb W (mg u v) y).toReal := ENNReal.toReal_nonneg
        have hq : 0 ≤ iidProb qU u * iidProb qU u' * iidProb qV v :=
          mul_nonneg (mul_nonneg (iidProb_nonneg _ _) (iidProb_nonneg _ _)) (iidProb_nonneg _ _)
        by_cases h : (mg u' v, y) ∈ D
        · simp only [h, hD h, ite_true, one_mul]
          exact le_of_eq (by ring)
        · simp only [h, ite_false, zero_mul, mul_zero]
          exact mul_nonneg (mul_nonneg (iidProb_nonneg _ _) (iidProb_nonneg _ _))
            (mul_nonneg (by split_ifs <;> norm_num)
              (mul_nonneg (iidProb_nonneg _ _) ENNReal.toReal_nonneg))
    _ ≤ _ := DMC.sum_iidProb_mul_iidProb_mul_sum_le (sideChannel W p S) qU n ε


end Random

end MACK

namespace MACKCode

variable {K : ℕ} {M A : Fin K → Type*} {B : Type*} {n : ℕ}

def toBlockCode (c : MACKCode M A B n) : BlockCode (∀ k, M k) (∀ k, A k) B n :=
  ⟨c.input, c.dec⟩

theorem errorProb_toBlockCode [Fintype B] [∀ k, DecidableEq (M k)] (c : MACKCode M A B n)
    (W : DMC (∀ k, A k) B) (m : ∀ k, M k) : c.toBlockCode.errorProb W m = c.errorProb W m :=
  rfl

theorem avgError_toBlockCode [Fintype B] [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]
    (c : MACKCode M A B n) (W : DMC (∀ k, A k) B) :
    c.toBlockCode.avgError W = c.avgError W := by
  rw [BlockCode.avgError, avgError, Fintype.card_pi, Nat.cast_prod]
  rfl

noncomputable def typicalCode (C : ∀ k, M k → Fin n → A k)
    (J : Finset ((Fin n → ∀ k, A k) × (Fin n → B))) (m₀ : ∀ k, M k) : MACKCode M A B n :=
  ⟨C, BlockCode.typicalDecoder (MACK.codeInput C) J m₀⟩

theorem toBlockCode_typicalCode (C : ∀ k, M k → Fin n → A k)
    (J : Finset ((Fin n → ∀ k, A k) × (Fin n → B))) (m₀ : ∀ k, M k) :
    (typicalCode C J m₀).toBlockCode = BlockCode.typicalCode (MACK.codeInput C) J m₀ := rfl

end MACKCode

namespace MACK

variable {K : ℕ} {A : Fin K → Type*} {B : Type*}

section Bound

variable {M : Fin K → Type*} {n : ℕ} [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]
  [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)] [∀ k, MeasurableSpace (A k)]
  [Fintype B] [MeasurableSpace B] [DecidableEq B]

def pattern (m m' : ∀ k, M k) : Finset (Fin K) :=
  univ.filter fun k => m' k ≠ m k

omit [∀ k, DecidableEq (A k)] [DecidableEq B] in
theorem sum_errorProb_typicalCode_le (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) (ε : ℝ)
    (m₀ m : ∀ k, M k) :
    ∑ C : ∀ k, M k → Fin n → A k, codebookWeight p C *
        ((MACKCode.typicalCode C (decodingSet W p n ε) m₀).errorProb W m).toReal ≤
      (1 - ∑ xy ∈ decodingSet W p n ε,
          iidProb (DMC.jointPMF W (piPMF p)) (fun i => (xy.1 i, xy.2 i))) +
        ∑ S ∈ univ.erase (∅ : Finset (Fin K)), (∏ k ∈ S, ((Fintype.card (M k) : ℝ) - 1)) *
          Real.exp (-(n * ((sideChannel W p S).inputMutualInfo
            (piPMF fun k : {k // k ∈ S} => p k) - 3 * ε))) := by
  classical
  set D := decodingSet W p n ε
  set e : Finset (Fin K) → ℝ := fun S => Real.exp (-(n * ((sideChannel W p S).inputMutualInfo
    (piPMF fun k : {k // k ∈ S} => p k) - 3 * ε))) with he
  have hw : ∀ C : ∀ k, M k → Fin n → A k, 0 ≤ codebookWeight p C :=
    fun C => prod_nonneg fun k _ => prod_nonneg fun j _ => iidProb_nonneg _ _
  set T0 : (∀ k, M k → Fin n → A k) → ℝ := fun C => ∑ y, (if (codeInput C m, y) ∈ D then 0
    else (DMC.blockProb W (codeInput C m) y).toReal)
  set T : (∀ k, M k → Fin n → A k) → (∀ k, M k) → ℝ := fun C m' =>
    ∑ y, (if (codeInput C m', y) ∈ D then (1 : ℝ) else 0) *
      (DMC.blockProb W (codeInput C m) y).toReal
  have hpt : ∀ C, ((MACKCode.typicalCode C D m₀).errorProb W m).toReal ≤
      T0 C + ∑ m' ∈ univ.erase m, T C m' := by
    intro C
    have h := BlockCode.errorProb_typicalCode_toReal_le W (codeInput C) D m₀ m
    rwa [← MACKCode.toBlockCode_typicalCode, MACKCode.errorProb_toBlockCode] at h
  have hmaps : ∀ m' ∈ univ.erase m, pattern m m' ∈ univ.erase (∅ : Finset (Fin K)) := by
    intro m' hm'
    refine mem_erase.2 ⟨fun h0 => ?_, mem_univ _⟩
    obtain ⟨k, hk⟩ := Function.ne_iff.1 (ne_of_mem_erase hm')
    have : k ∈ pattern m m' := mem_filter.2 ⟨mem_univ _, hk⟩
    rw [h0] at this
    exact absurd this (notMem_empty k)
  have hcard : ∀ S ∈ univ.erase (∅ : Finset (Fin K)),
      ((((univ.erase m).filter fun m' => pattern m m' = S).card : ℕ) : ℝ) ≤
        ∏ k ∈ S, ((Fintype.card (M k) : ℝ) - 1) := by
    intro S _
    have hsub : (univ.erase m).filter (fun m' => pattern m m' = S) ⊆
        Fintype.piFinset fun k => if k ∈ S then univ.erase (m k) else {m k} := by
      intro m' hm'
      rw [Fintype.mem_piFinset]
      intro k
      have hp := (mem_filter.1 hm').2
      by_cases hk : k ∈ S
      · rw [ite_eq_left hk]
        have : k ∈ pattern m m' := hp ▸ hk
        exact mem_erase.2 ⟨(mem_filter.1 this).2, mem_univ _⟩
      · rw [ite_eq_right hk]
        have : k ∉ pattern m m' := hp ▸ hk
        simp only [pattern, mem_filter, mem_univ, true_and, not_not] at this
        exact mem_singleton.2 this
    have hc : ∀ k, (((if k ∈ S then univ.erase (m k) else {m k}).card : ℕ) : ℝ) =
        if k ∈ S then (Fintype.card (M k) : ℝ) - 1 else 1 := by
      intro k
      split_ifs
      · rw [card_erase_of_mem (mem_univ _), card_univ,
          Nat.cast_sub (Fintype.card_pos_iff.2 ⟨m k⟩), Nat.cast_one]
      · simp
    calc _ ≤ (((Fintype.piFinset fun k => if k ∈ S then univ.erase (m k) else {m k}).card : ℕ)
          : ℝ) := Nat.cast_le.2 (card_le_card hsub)
      _ = _ := by
          rw [Fintype.card_piFinset, Nat.cast_prod]
          simp_rw [hc]
          exact Fintype.prod_ite_mem S _
  calc _ ≤ ∑ C, codebookWeight p C * (T0 C + ∑ m' ∈ univ.erase m, T C m') :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hpt C) (hw C)
    _ = ∑ C, codebookWeight p C * T0 C +
        ∑ m' ∈ univ.erase m, ∑ C, codebookWeight p C * T C m' := by
        simp only [mul_add, sum_add_distrib, mul_sum]
        rw [sum_comm (s := univ)]
    _ ≤ (1 - ∑ xy ∈ D, iidProb (DMC.jointPMF W (piPMF p)) (fun i => (xy.1 i, xy.2 i))) +
        ∑ m' ∈ univ.erase m, e (pattern m m') :=
        add_le_add (sum_codebookWeight_mul_sum_ite W p m ε).le
          (sum_le_sum fun m' _ => sum_codebookWeight_mul_sum_le W p (pattern m m') m m'
            (fun k => by simp [pattern]) ε)
    _ ≤ _ := by
        refine add_le_add le_rfl ?_
        rw [← sum_fiberwise_of_maps_to hmaps]
        refine sum_le_sum fun S hS => ?_
        rw [sum_congr rfl fun m' hm' => by rw [(mem_filter.1 hm').2], sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hcard S hS) (Real.exp_pos _).le

omit [∀ k, DecidableEq (A k)] [DecidableEq B] in
theorem exists_typicalCode_avgError_le (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) (ε : ℝ)
    (m₀ : ∀ k, M k) :
    ∃ C : ∀ k, M k → Fin n → A k,
      (MACKCode.typicalCode C (decodingSet W p n ε) m₀).avgError W ≤
        ENNReal.ofReal ((1 - ∑ xy ∈ decodingSet W p n ε,
            iidProb (DMC.jointPMF W (piPMF p)) (fun i => (xy.1 i, xy.2 i))) +
          ∑ S ∈ univ.erase (∅ : Finset (Fin K)), (∏ k ∈ S, ((Fintype.card (M k) : ℝ) - 1)) *
            Real.exp (-(n * ((sideChannel W p S).inputMutualInfo
              (piPMF fun k : {k // k ∈ S} => p k) - 3 * ε)))) := by
  classical
  have : Nonempty (∀ k, M k) := ⟨m₀⟩
  set β := (1 - ∑ xy ∈ decodingSet W p n ε,
      iidProb (DMC.jointPMF W (piPMF p)) (fun i => (xy.1 i, xy.2 i))) +
    ∑ S ∈ univ.erase (∅ : Finset (Fin K)), (∏ k ∈ S, ((Fintype.card (M k) : ℝ) - 1)) *
      Real.exp (-(n * ((sideChannel W p S).inputMutualInfo
        (piPMF fun k : {k // k ∈ S} => p k) - 3 * ε)))
  have h1 : ∑ C : ∀ k, M k → Fin n → A k, codebookWeight p C = 1 := by
    unfold codebookWeight
    calc ∑ C : ∀ k, M k → Fin n → A k, ∏ k, ∏ j, iidProb (p k) (C k j) =
        ∏ k, ∑ c : M k → Fin n → A k, ∏ j, iidProb (p k) (c j) :=
          (Fintype.prod_sum fun k (c : M k → Fin n → A k) => ∏ j, iidProb (p k) (c j)).symm
      _ = 1 := prod_eq_one fun k _ =>
        sum_prod (fun _ x => iidProb (p k) x) (fun _ => sum_iidProb _ n)
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le (w := codebookWeight p)
    (f := fun C => ∑ m,
      ((MACKCode.typicalCode C (decodingSet W p n ε) m₀).errorProb W m).toReal)
    (t := Fintype.card (∀ k, M k) * β)
    (fun C => prod_nonneg fun k _ => prod_nonneg fun j _ => iidProb_nonneg _ _) h1 (by
      simp only [mul_sum]
      rw [sum_comm]
      calc _ ≤ ∑ m : ∀ k, M k, β := sum_le_sum fun m _ => sum_errorProb_typicalCode_le W p ε m₀ m
        _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul])
  refine ⟨C, ?_⟩
  rw [← MACKCode.avgError_toBlockCode]
  exact BlockCode.avgError_le_ofReal _ W hC

private lemma mul_exp_le {n : ℕ} {x R I I' η : ℝ} (hx : x ≤ Real.exp (n * R)) (hI : I ≤ I')
    (hη : 4 * η ≤ I - R) : x * Real.exp (-(n * (I' - 3 * η))) ≤ Real.exp (n * (-η)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc x * Real.exp (-(n * (I' - 3 * η))) ≤ Real.exp (n * R) * Real.exp (-(n * (I - 3 * η))) :=
        mul_le_mul hx (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (n * R - n * (I - 3 * η)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (n * (-η)) := Real.exp_le_exp.2 (by nlinarith)

end Bound

theorem achievable_of_lt [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)]
    [∀ k, MeasurableSingletonClass (A k)] [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) {R : Fin K → ℝ}
    (h : ∀ S : Finset (Fin K), S.Nonempty → ∑ k ∈ S, R k < subsetInfo W p S) :
    Achievable W R := by
  classical
  intro ε hε
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  set g : Finset (Fin K) → ℝ := fun S => if S = ∅ then 1 else subsetInfo W p S - ∑ k ∈ S, R k
  set η := univ.inf' univ_nonempty g / 4 with hη
  have hη0 : 0 < η := by
    refine div_pos ((lt_inf'_iff _).2 fun S _ => ?_) (by norm_num)
    by_cases hS : S = ∅
    · simp [g, hS]
    · simp only [g, hS, ite_false]
      linarith [h S (nonempty_iff_ne_empty.2 hS)]
  have hηS : ∀ S ∈ univ.erase (∅ : Finset (Fin K)), 4 * η ≤ subsetInfo W p S - ∑ k ∈ S, R k := by
    intro S hS
    have := inf'_le g (mem_univ S)
    simp only [g, ne_of_mem_erase hS, ite_false] at this
    rw [hη]
    linarith
  set c : ℝ := ((univ.erase (∅ : Finset (Fin K))).card : ℝ)
  have hJ : Tendsto (fun n : ℕ => 1 - ∑ xy ∈ decodingSet W p n η,
      iidProb (DMC.jointPMF W (piPMF p)) (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_sum_iidProb_decodingSet W p hη0)
  have hE := tendsto_exp_nat_mul (neg_neg_of_pos hη0)
  have hsum := hJ.add (hE.const_mul c)
  rw [mul_zero, add_zero] at hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  set L : Fin K → ℕ := fun k => ⌈Real.exp (n * R k)⌉₊
  have hL : ∀ k, 0 < L k := fun k => Nat.ceil_pos.2 (Real.exp_pos _)
  have hL' : ∀ k, (L k : ℝ) - 1 ≤ Real.exp (n * R k) := fun k => by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R k)).le]
  have hL0 : ∀ k, (0 : ℝ) ≤ L k - 1 := fun k => by
    have : (1 : ℝ) ≤ L k := Nat.one_le_cast.2 (hL k)
    linarith
  refine ⟨L, fun k => Nat.le_ceil _, ?_⟩
  obtain ⟨C, hC⟩ := exists_typicalCode_avgError_le (n := n) W p η
    (fun k => (⟨0, hL k⟩ : Fin (L k)))
  refine ⟨_, hC.trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hδε.le)⟩
  have hb : ∀ S ∈ univ.erase (∅ : Finset (Fin K)),
      (∏ k ∈ S, ((Fintype.card (Fin (L k)) : ℝ) - 1)) *
        Real.exp (-(n * ((sideChannel W p S).inputMutualInfo
          (piPMF fun k : {k // k ∈ S} => p k) - 3 * η))) ≤ Real.exp (n * (-η)) := by
    intro S hS
    refine mul_exp_le ?_ (subsetInfo_le_inputMutualInfo W p S) (hηS S hS)
    rw [mul_sum, Real.exp_sum]
    exact prod_le_prod₀ (fun k _ => by rw [Fintype.card_fin]; exact hL0 k)
      fun k _ => by rw [Fintype.card_fin]; exact hL' k
  have := sum_le_sum hb
  rw [sum_const, nsmul_eq_mul] at this
  linarith [hN n hn]

end MACK

namespace MACKCode

variable {K : ℕ} {M M' A : Fin K → Type*} {B : Type*} {n n' : ℕ}

def append (c : MACKCode M A B n) (c' : MACKCode M' A B n') :
    MACKCode (fun k => M k × M' k) A B (n + n') where
  enc k m := Fin.append (c.enc k m.1) (c'.enc k m.2)
  dec y k := ((c.dec fun i => y (Fin.castAdd n' i)) k, (c'.dec fun i => y (Fin.natAdd n i)) k)

def relabel (c : MACKCode M A B n) (e : ∀ k, M k ≃ M' k) : MACKCode M' A B n where
  enc k m := c.enc k ((e k).symm m)
  dec y k := e k (c.dec y k)

variable [Fintype B]

theorem errorProb_ne_top [∀ k, DecidableEq (M k)] (c : MACKCode M A B n)
    (W : DMC (∀ k, A k) B) (m : ∀ k, M k) : c.errorProb W m ≠ ∞ :=
  c.toBlockCode.errorProb_ne_top W m

theorem errorProb_relabel [∀ k, DecidableEq (M k)] [∀ k, DecidableEq (M' k)]
    (c : MACKCode M A B n) (e : ∀ k, M k ≃ M' k) (W : DMC (∀ k, A k) B) (m : ∀ k, M k) :
    (c.relabel e).errorProb W (fun k => e k (m k)) = c.errorProb W m := by
  have hi : (c.relabel e).input (fun k => e k (m k)) = c.input m := by
    funext i k
    change c.enc k ((e k).symm (e k (m k))) i = c.enc k (m k) i
    rw [Equiv.symm_apply_apply]
  rw [errorProb, errorProb, hi]
  refine sum_congr rfl fun y _ => ?_
  have h : ((c.relabel e).dec y = fun k => e k (m k)) ↔ c.dec y = m := by
    constructor
    · intro h
      funext k
      exact (e k).injective (congrFun h k)
    · intro h
      funext k
      simp [relabel, h]
  by_cases hd : c.dec y = m
  · rw [ite_eq_left hd, ite_eq_left (h.2 hd)]
  · rw [ite_eq_right hd, ite_eq_right fun h' => hd (h.1 h')]

theorem avgError_relabel [∀ k, Fintype (M k)] [∀ k, Fintype (M' k)] [∀ k, DecidableEq (M k)]
    [∀ k, DecidableEq (M' k)] (c : MACKCode M A B n) (e : ∀ k, M k ≃ M' k)
    (W : DMC (∀ k, A k) B) : (c.relabel e).avgError W = c.avgError W := by
  rw [avgError, avgError, ← (Equiv.piCongrRight e).sum_comp]
  congr 1
  · exact sum_congr rfl fun m _ => c.errorProb_relabel e W m
  · exact prod_congr rfl fun k _ => by rw [Fintype.card_congr (e k)]

theorem sum_errorProb_toReal [∀ k, Fintype (M k)] [∀ k, Nonempty (M k)]
    [∀ k, DecidableEq (M k)] (c : MACKCode M A B n) (W : DMC (∀ k, A k) B) :
    ∑ m, (c.errorProb W m).toReal = (∏ k, (Fintype.card (M k) : ℝ)) * (c.avgError W).toReal := by
  have hK : (0 : ℝ) < ∏ k, (Fintype.card (M k) : ℝ) :=
    prod_pos fun k _ => Nat.cast_pos.2 Fintype.card_pos
  rw [avgError, ENNReal.toReal_div, ENNReal.toReal_sum fun m _ => c.errorProb_ne_top W m,
    ENNReal.toReal_prod]
  simp only [ENNReal.toReal_natCast]
  rw [mul_div_cancel₀ _ hK.ne']

theorem avgError_ne_top [∀ k, Fintype (M k)] [∀ k, Nonempty (M k)] [∀ k, DecidableEq (M k)]
    (c : MACKCode M A B n) (W : DMC (∀ k, A k) B) : c.avgError W ≠ ∞ := by
  refine ENNReal.div_ne_top (ENNReal.sum_ne_top.2 fun m _ => c.errorProb_ne_top W m) ?_
  exact prod_ne_zero_iff.2 fun k _ => Nat.cast_ne_zero.2 Fintype.card_ne_zero

private lemma ite_mul_le {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {d m : α} {d' m' : β} {g t : γ} (hg : g = t ↔ d = m ∧ d' = m') (P P' : ℝ≥0∞) :
    (if g = t then 0 else P * P') ≤
      (if d = m then 0 else P) * P' + P * if d' = m' then 0 else P' := by
  by_cases h : d = m <;> by_cases h' : d' = m' <;> simp [hg, h, h']

theorem errorProb_append_le [∀ k, DecidableEq (M k)] [∀ k, DecidableEq (M' k)]
    (c : MACKCode M A B n) (c' : MACKCode M' A B n') (W : DMC (∀ k, A k) B)
    (m : ∀ k, M k × M' k) :
    (c.append c').errorProb W m ≤
      c.errorProb W (fun k => (m k).1) + c'.errorProb W (fun k => (m k).2) := by
  rw [errorProb, ← (Fin.appendEquiv n n').sum_comp, Fintype.sum_prod_type]
  have hb : ∀ (y : Fin n → B) (y' : Fin n' → B),
      DMC.blockProb W ((c.append c').input m) (Fin.appendEquiv n n' (y, y')) =
        DMC.blockProb W (c.input fun k => (m k).1) y *
          DMC.blockProb W (c'.input fun k => (m k).2) y' := by
    intro y y'
    have h1 : ∀ i, (c.append c').input m (Fin.castAdd n' i) = c.input (fun k => (m k).1) i :=
      fun i => funext fun k => by simp [input, append]
    have h2 : ∀ i, (c.append c').input m (Fin.natAdd n i) = c'.input (fun k => (m k).2) i :=
      fun i => funext fun k => by simp [input, append]
    simp only [DMC.blockProb, Fin.appendEquiv_apply, Fin.prod_univ_add, Fin.append_left,
      Fin.append_right, h1, h2]
  have hd : ∀ (y : Fin n → B) (y' : Fin n' → B),
      (c.append c').dec (Fin.appendEquiv n n' (y, y')) = fun k => (c.dec y k, c'.dec y' k) := by
    intro y y'
    funext k
    simp [append]
  calc _ ≤ ∑ y : Fin n → B, ∑ y' : Fin n' → B,
        ((if c.dec y = (fun k => (m k).1) then 0
          else DMC.blockProb W (c.input fun k => (m k).1) y) *
          DMC.blockProb W (c'.input fun k => (m k).2) y' +
        DMC.blockProb W (c.input fun k => (m k).1) y *
          if c'.dec y' = (fun k => (m k).2) then 0
          else DMC.blockProb W (c'.input fun k => (m k).2) y') := by
        refine sum_le_sum fun y _ => sum_le_sum fun y' _ => ?_
        rw [hb, hd]
        refine ite_mul_le ⟨fun h => ⟨funext fun k => congrArg Prod.fst (congrFun h k),
          funext fun k => congrArg Prod.snd (congrFun h k)⟩, fun h => funext fun k =>
            Prod.ext (congrFun h.1 k) (congrFun h.2 k)⟩ _ _
    _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, ← sum_mul, DMC.sum_blockProb_eq_one, mul_one,
          one_mul]
        rfl

private def pairEquiv : (∀ k, M k × M' k) ≃ (∀ k, M k) × (∀ k, M' k) where
  toFun m := (fun k => (m k).1, fun k => (m k).2)
  invFun q k := (q.1 k, q.2 k)
  left_inv _ := rfl
  right_inv _ := rfl

theorem avgError_append_le [∀ k, Fintype (M k)] [∀ k, Fintype (M' k)] [∀ k, Nonempty (M k)]
    [∀ k, Nonempty (M' k)] [∀ k, DecidableEq (M k)] [∀ k, DecidableEq (M' k)]
    (c : MACKCode M A B n) (c' : MACKCode M' A B n') (W : DMC (∀ k, A k) B) :
    (c.append c').avgError W ≤ c.avgError W + c'.avgError W := by
  rw [← avgError_toBlockCode, ← ENNReal.ofReal_toReal (c.avgError_ne_top W),
    ← ENNReal.ofReal_toReal (c'.avgError_ne_top W),
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  refine BlockCode.avgError_le_ofReal _ W ?_
  have h1 := c.sum_errorProb_toReal W
  have h2 := c'.sum_errorProb_toReal W
  have hpt : ∀ m : ∀ k, M k × M' k, ((c.append c').errorProb W m).toReal ≤
      (c.errorProb W fun k => (m k).1).toReal + (c'.errorProb W fun k => (m k).2).toReal := by
    intro m
    rw [← ENNReal.toReal_add (c.errorProb_ne_top W _) (c'.errorProb_ne_top W _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨c.errorProb_ne_top W _,
      c'.errorProb_ne_top W _⟩) (c.errorProb_append_le c' W m)
  calc ∑ m, ((c.append c').toBlockCode.errorProb W m).toReal
      ≤ ∑ m : ∀ k, M k × M' k,
          ((c.errorProb W fun k => (m k).1).toReal + (c'.errorProb W fun k => (m k).2).toReal) :=
        sum_le_sum fun m _ => hpt m
    _ = ∑ q : (∀ k, M k) × (∀ k, M' k),
          ((c.errorProb W q.1).toReal + (c'.errorProb W q.2).toReal) :=
        (pairEquiv.sum_comp (fun q => (c.errorProb W q.1).toReal + (c'.errorProb W q.2).toReal))
    _ = (∏ k, (Fintype.card (M' k) : ℝ)) * ∑ m, (c.errorProb W m).toReal +
        (∏ k, (Fintype.card (M k) : ℝ)) * ∑ m, (c'.errorProb W m).toReal := by
        rw [Fintype.sum_prod_type]
        simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, Fintype.card_pi,
          Nat.cast_prod]
        rw [← mul_sum]
    _ = _ := by
        rw [h1, h2, Fintype.card_pi, Nat.cast_prod]
        simp only [Fintype.card_prod, Nat.cast_mul, prod_mul_distrib]
        ring

end MACKCode

namespace MACK

variable {K : ℕ} {A : Fin K → Type*} {B : Type*}

section TimeSharing

variable [Fintype B]

theorem Achievable.mono {W : DMC (∀ k, A k) B} {R R' : Fin K → ℝ} (h : Achievable W R)
    (h' : ∀ k, R' k ≤ R k) : Achievable W R' := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨L, hL, c, hc⟩ := hN n hn
  exact ⟨L, fun k => (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (h' k)
    (Nat.cast_nonneg n))).trans (hL k), c, hc⟩

theorem Achievable.max_zero {W : DMC (∀ k, A k) B} {R : Fin K → ℝ} (h : Achievable W R) :
    Achievable W fun k => max (R k) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨L, hL, c, hc⟩ := hN n hn
  exact ⟨L, fun k => exp_mul_max_le (hL k), c, hc⟩

theorem mem_closure_achievableRegion (W : DMC (∀ k, A k) B) {R : Fin K → ℝ}
    (h0 : ∀ k, 0 ≤ R k) (h : ∀ δ > 0, Achievable W fun k => R k - δ) :
    R ∈ closure (achievableRegion W) := by
  rw [Metric.mem_closure_iff]
  intro η hη
  have key : ∀ x : ℝ, 0 ≤ x → dist x (max (x - η / 2) 0) < η := by
    intro x hx
    rw [Real.dist_eq]
    rcases le_total (x - η / 2) 0 with h | h
    · rw [max_eq_right h, sub_zero, abs_of_nonneg hx]
      linarith
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]
      linarith
  exact ⟨fun k => max (R k - η / 2) 0, ⟨fun k => le_max_right _ _,
    (h (η / 2) (by positivity)).max_zero⟩, (dist_pi_lt_iff hη).2 fun k => key _ (h0 k)⟩

private lemma exists_code_of_eq {M : Fin K → Type*} [∀ k, Fintype (M k)]
    [∀ k, DecidableEq (M k)] {W : DMC (∀ k, A k) B} {ε : ℝ≥0∞} {n m : ℕ} (h : n = m)
    (hc : ∃ c : MACKCode M A B n, c.avgError W ≤ ε) :
    ∃ c : MACKCode M A B m, c.avgError W ≤ ε := h ▸ hc

theorem Achievable.timeSharing {W : DMC (∀ k, A k) B} {R R' : Fin K → ℝ}
    (h : Achievable W R) (h' : Achievable W R') {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) {δ : ℝ} (hδ : 0 < δ) :
    Achievable W fun k => a * R k + b * R' k - δ := by
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    exact h'.mono fun k => by linarith
  rcases hb.eq_or_lt with rfl | hb'
  · obtain rfl : a = 1 := by linarith
    exact h.mono fun k => by linarith
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨N', hN'⟩ := h' (ε / 2) (ENNReal.half_pos hε.ne')
  set D := ∑ k, |R k - R' k|
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (max (N / a) (N' / b)) (D / δ))
  refine ⟨N₀, fun n hn => ?_⟩
  have hn' : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hNa : (N : ℝ) < a * n := (div_lt_iff₀' ha').1 (((le_max_left _ _).trans
    (le_max_left _ _)).trans_lt (hN₀.trans_le hn'))
  have hNb : (N' : ℝ) < b * n := (div_lt_iff₀' hb').1 (((le_max_right _ _).trans
    (le_max_left _ _)).trans_lt (hN₀.trans_le hn'))
  have hnδ : D < n * δ := (div_lt_iff₀ hδ).1 ((le_max_right _ _).trans_lt (hN₀.trans_le hn'))
  set n₁ := ⌊a * n⌋₊ with hn₁
  have han : 0 ≤ a * n := by positivity
  have hfl : (n₁ : ℝ) ≤ a * n := Nat.floor_le han
  have hfl' : a * n < n₁ + 1 := Nat.lt_floor_add_one _
  have hn₁n : n₁ ≤ n := by
    have : (n₁ : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hn₁N : N ≤ n₁ := Nat.le_floor hNa.le
  have hn₂N : N' ≤ n - n₁ := by
    have : (N' : ℝ) + n₁ ≤ n := by nlinarith
    have : N' + n₁ ≤ n := by exact_mod_cast this
    omega
  obtain ⟨L, hL, c, hc⟩ := hN n₁ hn₁N
  obtain ⟨L', hL', c', hc'⟩ := hN' (n - n₁) hn₂N
  have hcast : ((n - n₁ : ℕ) : ℝ) = n - n₁ := Nat.cast_sub hn₁n
  have hrate : ∀ {R R' : ℝ} {k k' : ℕ}, Real.exp (n₁ * R) ≤ k →
      Real.exp (((n - n₁ : ℕ) : ℝ) * R') ≤ k' → |R - R'| < n * δ →
      Real.exp (n * (a * R + b * R' - δ)) ≤ ((k * k' : ℕ) : ℝ) := by
    intro R R' k k' hk hk' hRR
    rw [Nat.cast_mul]
    refine le_trans ?_ (mul_le_mul hk hk' (Real.exp_pos _).le (Nat.cast_nonneg _))
    rw [← Real.exp_add, hcast]
    refine Real.exp_le_exp.2 ?_
    have hθ0 : 0 ≤ a * n - n₁ := by linarith
    have hθ1 : a * n - n₁ ≤ 1 := by linarith
    have habs := le_abs_self (R - R')
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_le_mul_of_nonneg_left habs hθ0,
      mul_le_mul_of_nonneg_right hθ1 (abs_nonneg (R - R'))]
  refine ⟨fun k => L k * L' k, fun k => hrate (hL k) (hL' k)
    ((single_le_sum (fun j _ => abs_nonneg (R j - R' j)) (mem_univ k)).trans_lt hnδ), ?_⟩
  have hk0 : ∀ {R : ℝ} {m k : ℕ}, Real.exp (m * R) ≤ k → 0 < k := fun hk =>
    Nat.cast_pos.1 ((Real.exp_pos _).trans_le hk)
  have : ∀ k, Nonempty (Fin (L k)) := fun k => ⟨⟨0, hk0 (hL k)⟩⟩
  have : ∀ k, Nonempty (Fin (L' k)) := fun k => ⟨⟨0, hk0 (hL' k)⟩⟩
  refine exists_code_of_eq (Nat.add_sub_cancel' hn₁n)
    ⟨(c.append c').relabel fun k => finProdFinEquiv, ?_⟩
  rw [MACKCode.avgError_relabel]
  calc _ ≤ c.avgError W + c'.avgError W := c.avgError_append_le c' W
    _ ≤ ε / 2 + ε / 2 := add_le_add hc hc'
    _ = ε := ENNReal.add_halves ε

theorem convex_closure_achievableRegion (W : DMC (∀ k, A k) B) :
    Convex ℝ (closure (achievableRegion W)) := by
  have key : ∀ x ∈ achievableRegion W, ∀ y ∈ achievableRegion W, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → a • x + b • y ∈ closure (achievableRegion W) := by
    rintro x ⟨hx0, hx⟩ y ⟨hy0, hy⟩ a b ha hb hab
    refine mem_closure_achievableRegion W (fun k => ?_) fun δ hδ => ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hx0 k)) (mul_nonneg hb (hy0 k))
    · simpa using hx.timeSharing hy ha hb hab hδ
  intro x hx y hy a b ha hb hab
  have hf : Continuous (Function.uncurry fun x y : Fin K → ℝ => a • x + b • y) :=
    (show Continuous fun p : (Fin K → ℝ) × (Fin K → ℝ) => a • p.1 + b • p.2 from
      (continuous_fst.const_smul a).add (continuous_snd.const_smul b))
  have h := map_mem_closure₂ hf hx hy fun x' hx' y' hy' => key x' hx' y' hy' a b ha hb hab
  rwa [closure_closure] at h

end TimeSharing

variable [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)] [∀ k, MeasurableSingletonClass (A k)]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem polymatroid_subset_closure_achievableRegion (W : DMC (∀ k, A k) B)
    (p : ∀ k, PMF (A k)) : polymatroid W p ⊆ closure (achievableRegion W) := by
  rintro R ⟨h0, hS⟩
  refine mem_closure_achievableRegion W h0 fun δ hδ => achievable_of_lt W p fun S hne => ?_
  have hc : (0 : ℝ) < S.card := Nat.cast_pos.2 (card_pos.2 hne)
  calc ∑ k ∈ S, (R k - δ) = ∑ k ∈ S, R k - S.card * δ := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    _ < ∑ k ∈ S, R k := by nlinarith
    _ ≤ subsetInfo W p S := hS S

theorem capacityRegion_subset_closure_achievableRegion (W : DMC (∀ k, A k) B) :
    capacityRegion W ⊆ closure (achievableRegion W) :=
  closure_minimal (convexHull_min (Set.iUnion_subset fun p =>
    polymatroid_subset_closure_achievableRegion W p) (convex_closure_achievableRegion W))
    isClosed_closure

end MACK

end Meat
