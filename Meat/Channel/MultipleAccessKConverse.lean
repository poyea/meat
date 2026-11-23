import Meat.Channel.MultipleAccessKAchievability
import Meat.Shannon.ChainRule

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

section Determined

variable {Ω S T : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem entropy_eq_of_determined {X : Ω → S} {Y : Ω → T} (hX : Measurable X) (hY : Measurable Y)
    (f : S → T) (g : T → S) (hf : ∀ ω, Y ω = f (X ω)) (hg : ∀ ω, X ω = g (Y ω)) :
    H[X ; μ] = H[Y ; μ] := by
  have h1 := entropy_comp_le μ hX f
  have h2 := entropy_comp_le μ hY g
  have e1 : f ∘ X = Y := funext fun ω => (hf ω).symm
  have e2 : g ∘ Y = X := funext fun ω => (hg ω).symm
  rw [e1] at h1
  rw [e2] at h2
  linarith

end Determined

private lemma map_pair_apply_left {X Y Z : Type*} [Finite X]
    (q : PMF X) (y₀ : Y) (ψ : X → Z) (y : Y) (z : Z) :
    (q.map fun a => (y₀, ψ a)) (y, z) = (q.map fun _ => y₀) y * (q.map ψ) z := by
  classical
  have := Fintype.ofFinite X
  simp only [PMF.map_apply, tsum_fintype, Prod.mk.injEq]
  by_cases hy : y = y₀
  · simp only [hy, true_and, ite_true, sum_pmf_eq_one, one_mul]
  · simp [hy]

private lemma map_pair_apply_right {X Y Z : Type*} [Finite X]
    (q : PMF X) (φ : X → Y) (z₀ : Z) (y : Y) (z : Z) :
    (q.map fun a => (φ a, z₀)) (y, z) = (q.map φ) y * (q.map fun _ => z₀) z := by
  classical
  have := Fintype.ofFinite X
  simp only [PMF.map_apply, tsum_fintype, Prod.mk.injEq]
  by_cases hz : z = z₀
  · simp only [hz, and_true, ite_true, sum_pmf_eq_one, mul_one]
  · simp [hz]

namespace MACK

variable {K : ℕ} {A : Fin K → Type*} {B : Type*}

def restrictMask (T : Finset (Fin K)) (m : Masked A) : Masked A :=
  fun k => if k ∈ T then m k else none

def unionMask (T : Finset (Fin K)) (m m' : Masked A) : Masked A :=
  fun k => if k ∈ T then m k else m' k

theorem restrictMask_mask {T T' : Finset (Fin K)} (h : T ⊆ T') (x : ∀ k, A k) :
    restrictMask T (mask T' x) = mask T x := by
  funext k
  by_cases hk : k ∈ T
  · simp [restrictMask, mask, hk, h hk]
  · simp [restrictMask, mask, hk]

theorem unionMask_mask (T T' : Finset (Fin K)) (x : ∀ k, A k) :
    unionMask T (mask T x) (mask T' x) = mask (T ∪ T') x := by
  funext k
  by_cases hk : k ∈ T <;> simp [unionMask, mask, hk]

theorem mask_pair_injective (S : Finset (Fin K)) :
    Function.Injective fun x : ∀ k, A k => (mask S x, mask Sᶜ x) := by
  intro x x' h
  funext k
  have h1 := congrFun (congrArg Prod.fst h) k
  have h2 := congrFun (congrArg Prod.snd h) k
  by_cases hk : k ∈ S
  · simpa [mask, hk] using h1
  · simpa [mask, hk] using h2

theorem mask_univ_injective : Function.Injective (mask (A := A) univ) :=
  fun x x' h => funext fun k => by simpa [mask] using congrFun h k

section PiMask

variable [∀ k, Fintype (A k)]

theorem piPMF_map_mask_apply (p : ∀ k, PMF (A k)) (T : Finset (Fin K)) (s : Masked A) :
    (piPMF p).map (mask T) s =
      ∏ k, (p k).map (fun a => if k ∈ T then some a else none) (s k) := by
  classical
  have h := piPMF_map p fun k (a : A k) => if k ∈ T then some a else none
  change (PMF.map (fun (x : ∀ k, A k) (k : Fin K) => if k ∈ T then some (x k) else none)
    (piPMF p)) s = _
  rw [h]
  exact piPMF_apply _ _

private def maskPairEquiv : (∀ k, Option (A k) × Option (A k)) ≃ Masked A × Masked A where
  toFun m := (fun k => (m k).1, fun k => (m k).2)
  invFun q k := (q.1 k, q.2 k)
  left_inv _ := rfl
  right_inv _ := rfl

theorem piPMF_map_mask_pair_apply (p : ∀ k, PMF (A k)) {T T' : Finset (Fin K)}
    (hT : Disjoint T T') (s t : Masked A) :
    (piPMF p).map (fun x => (mask T x, mask T' x)) (s, t) =
      (piPMF p).map (mask T) s * (piPMF p).map (mask T') t := by
  classical
  have e : (fun x : ∀ k, A k => (mask T x, mask T' x)) = maskPairEquiv ∘
      fun x k => ((if k ∈ T then some (x k) else none), if k ∈ T' then some (x k) else none) :=
    rfl
  have hst : (s, t) = maskPairEquiv (fun k => (s k, t k)) := rfl
  rw [e, ← PMF.map_comp, hst, PMF.map_apply_of_injective _ maskPairEquiv.injective,
    piPMF_map p fun k (a : A k) =>
      ((if k ∈ T then some a else none), if k ∈ T' then some a else none),
    piPMF_apply, piPMF_map_mask_apply, piPMF_map_mask_apply, ← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  by_cases hk : k ∈ T
  · have hk' : k ∉ T' := disjoint_left.1 hT hk
    simp only [hk, hk', ite_true, ite_false]
    exact map_pair_apply_right (p k) _ _ _ _
  · simp only [hk, ite_false]
    exact map_pair_apply_left (p k) _ _ _ _

end PiMask

variable [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)] [∀ k, MeasurableSingletonClass (A k)]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

omit [Fintype B] in
private lemma measureReal_map_fst [Finite B] {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k))
    (g : (∀ k, A k) → X) (v : X) :
    ((W.jointMeasure (piPMF p)).map fun ω => g ω.1).real {v} = ((piPMF p).map g v).toReal := by
  rw [DMC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _),
    measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  congr 2
  rw [show (fun ω : (∀ k, A k) × B => g ω.1) = g ∘ Prod.fst from rfl, ← PMF.map_comp,
    DMC.jointPMF_map_fst]

omit [Fintype B] in
theorem mutualInfo_mask_eq_zero [Finite B] (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k))
    {T T' : Finset (Fin K)} (hT : Disjoint T T') :
    I[fun ω : (∀ k, A k) × B => mask T ω.1 : fun ω => mask T' ω.1 ;
      W.jointMeasure (piPMF p)] = 0 := by
  have := Fintype.ofFinite B
  refine mutualInfo_eq_zero_of_measureReal_eq_mul _ fun s t => ?_
  rw [measureReal_map_fst W p (fun x => (mask T x, mask T' x)), measureReal_map_fst W p,
    measureReal_map_fst W p, piPMF_map_mask_pair_apply p hT, ENNReal.toReal_mul]

noncomputable def residual (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) (T : Finset (Fin K)) :
    ℝ :=
  H[Prod.snd | fun ω : (∀ k, A k) × B => mask T ω.1 ; W.jointMeasure (piPMF p)]

theorem condEntropy_mask_univ (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    residual W p univ = H[Prod.snd | Prod.fst ; W.jointMeasure (piPMF p)] :=
  condEntropy_cond_of_injective _ mask_univ_injective fun _ => rfl

theorem subsetInfo_eq_residual (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k))
    (S : Finset (Fin K)) : subsetInfo W p S = residual W p Sᶜ - residual W p univ := by
  rw [subsetInfo, condMutualInfo_eq_condEntropy_sub_condEntropy, condEntropy_mask_univ,
    condEntropy_cond_of_injective _ (mask_pair_injective S) fun _ => rfl]
  rfl

theorem subsetInfo_empty (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) :
    subsetInfo W p ∅ = 0 := by
  rw [subsetInfo_eq_residual, compl_empty, sub_self]

theorem residual_anti (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) {T T' : Finset (Fin K)}
    (h : T ⊆ T') : residual W p T' ≤ residual W p T := by
  have h1 := condEntropy_le_condEntropy_comp (μ := W.jointMeasure (piPMF p)) (X := Prod.snd)
    (Y := fun ω : (∀ k, A k) × B => mask T' ω.1) measurable_snd (measurable_of_finite _)
    (restrictMask T)
  have e : restrictMask T ∘ (fun ω : (∀ k, A k) × B => mask T' ω.1) =
      fun ω => mask T ω.1 := funext fun ω => restrictMask_mask h ω.1
  rw [e] at h1
  exact h1

theorem residual_sub_le (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) {F F' : Finset (Fin K)}
    {k : Fin K} (hF : F ⊆ F') (hk : k ∉ F') :
    residual W p F - residual W p (insert k F) ≤ residual W p F' - residual W p (insert k F') := by
  classical
  set μ := W.jointMeasure (piPMF p)
  have hins : ∀ G : Finset (Fin K), k ∉ G → residual W p G - residual W p (insert k G) =
      H[fun ω : (∀ k, A k) × B => (ω.2, mask G ω.1) ; μ] -
        H[fun ω : (∀ k, A k) × B => (ω.2, (mask {k} ω.1, mask G ω.1)) ; μ] +
        H[fun ω : (∀ k, A k) × B => mask {k} ω.1 ; μ] := by
    intro G hG
    have hsub1 : ({k} : Finset (Fin K)) ⊆ insert k G := singleton_subset_iff.2 (mem_insert_self k G)
    have hsub2 : G ⊆ insert k G := subset_insert k G
    have hu : ∀ x : ∀ k, A k, unionMask {k} (mask {k} x) (mask G x) = mask (insert k G) x :=
      fun x => by rw [unionMask_mask, insert_eq]
    have e1 : H[fun ω : (∀ k, A k) × B => mask (insert k G) ω.1 ; μ] =
        H[fun ω : (∀ k, A k) × B => (mask {k} ω.1, mask G ω.1) ; μ] :=
      entropy_eq_of_determined μ (measurable_of_finite _) (measurable_of_finite _)
        (fun m => (restrictMask {k} m, restrictMask G m)) (fun q => unionMask {k} q.1 q.2)
        (fun ω => by rw [restrictMask_mask hsub1, restrictMask_mask hsub2])
        (fun ω => (hu ω.1).symm)
    have e2 : H[fun ω : (∀ k, A k) × B => (ω.2, mask (insert k G) ω.1) ; μ] =
        H[fun ω : (∀ k, A k) × B => (ω.2, (mask {k} ω.1, mask G ω.1)) ; μ] :=
      entropy_eq_of_determined μ (measurable_of_finite _) (measurable_of_finite _)
        (fun q => (q.1, (restrictMask {k} q.2, restrictMask G q.2)))
        (fun q => (q.1, unionMask {k} q.2.1 q.2.2))
        (fun ω => by rw [restrictMask_mask hsub1, restrictMask_mask hsub2])
        (fun ω => by rw [hu ω.1])
    have hI := mutualInfo_mask_eq_zero W p (T := {k}) (T' := G) (disjoint_singleton_left.2 hG)
    rw [mutualInfo_def] at hI
    simp only [residual, condEntropy_def]
    rw [e1, e2]
    linarith
  rw [hins F fun h => hk (hF h), hins F' hk]
  have hsm := entropy_submodular μ (X := fun ω : (∀ k, A k) × B => mask {k} ω.1)
    (Y := fun ω => mask F' ω.1) (Z := fun ω => (ω.2, mask F ω.1)) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)
  have e3 : H[fun ω : (∀ k, A k) × B => ((mask {k} ω.1, mask F' ω.1), (ω.2, mask F ω.1)) ; μ] =
      H[fun ω : (∀ k, A k) × B => (ω.2, (mask {k} ω.1, mask F' ω.1)) ; μ] :=
    entropy_eq_of_determined μ (measurable_of_finite _) (measurable_of_finite _)
      (fun q => (q.2.1, q.1))
      (fun q => (q.2, (q.1, restrictMask F q.2.2))) (fun ω => rfl)
      (fun ω => by rw [restrictMask_mask hF])
  have e4 : H[fun ω : (∀ k, A k) × B => (mask {k} ω.1, (ω.2, mask F ω.1)) ; μ] =
      H[fun ω : (∀ k, A k) × B => (ω.2, (mask {k} ω.1, mask F ω.1)) ; μ] :=
    entropy_eq_of_determined μ (measurable_of_finite _) (measurable_of_finite _)
      (fun q => (q.2.1, (q.1, q.2.2)))
      (fun q => (q.2.1, (q.1, q.2.2))) (fun ω => rfl) (fun ω => rfl)
  have e5 : H[fun ω : (∀ k, A k) × B => (mask F' ω.1, (ω.2, mask F ω.1)) ; μ] =
      H[fun ω : (∀ k, A k) × B => (ω.2, mask F' ω.1) ; μ] :=
    entropy_eq_of_determined μ (measurable_of_finite _) (measurable_of_finite _)
      (fun q => (q.2.1, q.1))
      (fun q => (q.2, (q.1, restrictMask F q.2))) (fun ω => rfl)
      (fun ω => by rw [restrictMask_mask hF])
  rw [e3, e4, e5] at hsm
  linarith

theorem subsetInfo_le_insert (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) (T : Finset (Fin K))
    (k : Fin K) : subsetInfo W p T ≤ subsetInfo W p (insert k T) := by
  rw [subsetInfo_eq_residual, subsetInfo_eq_residual]
  have := residual_anti W p (compl_subset_compl.2 (subset_insert k T))
  linarith

theorem subsetInfo_insert_sub_le (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k))
    {T T' : Finset (Fin K)} {k : Fin K} (hT : T ⊆ T') (hk : k ∉ T') :
    subsetInfo W p (insert k T') - subsetInfo W p T' ≤
      subsetInfo W p (insert k T) - subsetInfo W p T := by
  classical
  have hkT : k ∉ T := fun h => hk (hT h)
  have e : ∀ U : Finset (Fin K), k ∉ U → subsetInfo W p (insert k U) - subsetInfo W p U =
      residual W p (Uᶜ.erase k) - residual W p (insert k (Uᶜ.erase k)) := by
    intro U hU
    rw [subsetInfo_eq_residual, subsetInfo_eq_residual, compl_insert,
      insert_erase (mem_compl.2 hU)]
    ring
  rw [e T' hk, e T hkT]
  exact residual_sub_le W p (erase_subset_erase k (compl_subset_compl.2 hT))
    (notMem_erase k _)

section Greedy

def prefixSet (σ : Equiv.Perm (Fin K)) (j : ℕ) : Finset (Fin K) :=
  univ.filter fun k => (σ.symm k : ℕ) < j

theorem prefixSet_succ (σ : Equiv.Perm (Fin K)) (k : Fin K) :
    prefixSet σ ((σ.symm k : ℕ) + 1) = insert k (prefixSet σ (σ.symm k)) := by
  ext l
  simp only [prefixSet, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · exact Or.inr h'
    · exact Or.inl (σ.symm.injective (Fin.ext h'))
  · rintro (rfl | h)
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt h

theorem notMem_prefixSet_self (σ : Equiv.Perm (Fin K)) (k : Fin K) :
    k ∉ prefixSet σ (σ.symm k) := by
  simp [prefixSet]

theorem prefixSet_zero (σ : Equiv.Perm (Fin K)) : prefixSet σ 0 = ∅ := by
  ext k
  simp [prefixSet]

theorem prefixSet_card (σ : Equiv.Perm (Fin K)) : prefixSet σ K = univ := by
  ext k
  simp [prefixSet]

theorem sum_prefixSet (σ : Equiv.Perm (Fin K)) (g : Fin K → ℝ) {j : ℕ} (hj : j ≤ K) :
    ∑ k ∈ prefixSet σ j, g k = ∑ i ∈ range j, if h : i < K then g (σ ⟨i, h⟩) else 0 := by
  set G : ℕ → ℝ := fun i => if h : i < K then g (σ ⟨i, h⟩) else 0
  rw [prefixSet, sum_filter, ← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply]
  calc ∑ i : Fin K, (if (i : ℕ) < j then g (σ i) else 0) =
        ∑ i : Fin K, (fun i : ℕ => if i < j then G i else 0) i :=
        sum_congr rfl fun i _ => by simp [G, i.2]
    _ = ∑ i ∈ range K, (if i < j then G i else 0) :=
        (Finset.sum_range fun i => if i < j then G i else 0).symm
    _ = ∑ i ∈ range j, G i := by
        rw [← sum_filter]
        congr 1
        ext i
        simp only [mem_filter, mem_range]
        omega

theorem sum_prefixSet_telescope (σ : Equiv.Perm (Fin K)) (φ : ℕ → ℝ) {j : ℕ} (hj : j ≤ K) :
    ∑ k ∈ prefixSet σ j, (φ ((σ.symm k : ℕ) + 1) - φ (σ.symm k)) = φ j - φ 0 := by
  rw [sum_prefixSet σ _ hj, ← sum_range_sub]
  refine sum_congr rfl fun i hi => ?_
  have h : i < K := (mem_range.1 hi).trans_le hj
  simp [h]

noncomputable def greedy (σ : Equiv.Perm (Fin K)) (f : Finset (Fin K) → ℝ) (k : Fin K) : ℝ :=
  f (prefixSet σ ((σ.symm k : ℕ) + 1)) - f (prefixSet σ (σ.symm k))

theorem sum_greedy_prefixSet (σ : Equiv.Perm (Fin K)) (f : Finset (Fin K) → ℝ) (hf : f ∅ = 0)
    {j : ℕ} (hj : j ≤ K) : ∑ k ∈ prefixSet σ j, greedy σ f k = f (prefixSet σ j) := by
  unfold greedy
  rw [sum_prefixSet_telescope σ (fun j => f (prefixSet σ j)) hj]
  simp [prefixSet_zero, hf]

theorem greedy_nonneg (σ : Equiv.Perm (Fin K)) {f : Finset (Fin K) → ℝ}
    (hf : ∀ T k, f T ≤ f (insert k T)) (k : Fin K) : 0 ≤ greedy σ f k := by
  rw [greedy, prefixSet_succ]
  linarith [hf (prefixSet σ (σ.symm k)) k]

theorem sum_greedy_le (σ : Equiv.Perm (Fin K)) {f : Finset (Fin K) → ℝ} (hf : f ∅ = 0)
    (hsub : ∀ {T T' : Finset (Fin K)} {k : Fin K}, T ⊆ T' → k ∉ T' →
      f (insert k T') - f T' ≤ f (insert k T) - f T)
    (T : Finset (Fin K)) : ∑ k ∈ T, greedy σ f k ≤ f T := by
  classical
  set φ : ℕ → ℝ := fun j => f (prefixSet σ j ∩ T)
  have hle : ∀ k ∈ T, greedy σ f k ≤ φ ((σ.symm k : ℕ) + 1) - φ (σ.symm k) := by
    intro k hk
    simp only [greedy, φ, prefixSet_succ, insert_inter_of_mem hk]
    exact hsub inter_subset_left (notMem_prefixSet_self σ k)
  have hzero : ∀ k ∈ univ, k ∉ T → φ ((σ.symm k : ℕ) + 1) - φ (σ.symm k) = 0 := by
    intro k _ hk
    simp only [φ, prefixSet_succ, insert_inter_of_notMem hk, sub_self]
  calc ∑ k ∈ T, greedy σ f k ≤ ∑ k ∈ T, (φ ((σ.symm k : ℕ) + 1) - φ (σ.symm k)) :=
        sum_le_sum hle
    _ = ∑ k ∈ prefixSet σ K, (φ ((σ.symm k : ℕ) + 1) - φ (σ.symm k)) := by
        rw [prefixSet_card]
        exact sum_subset (subset_univ T) hzero
    _ = φ K - φ 0 := sum_prefixSet_telescope σ φ le_rfl
    _ = f T := by simp [φ, prefixSet_card, prefixSet_zero, hf]

theorem abel_nonneg {v c : ℕ → ℝ} {N : ℕ} (hv : ∀ i, i + 1 < N → v (i + 1) ≤ v i)
    (hv0 : ∀ i < N, 0 ≤ v i) (hc : ∀ j ≤ N, 0 ≤ ∑ i ∈ range j, c i) :
    0 ≤ ∑ i ∈ range N, v i * c i := by
  have key : ∀ m, m < N → v m * ∑ i ∈ range (m + 1), c i ≤ ∑ i ∈ range (m + 1), v i * c i := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hv m hm
      have h3 := hc (m + 1) (by omega)
      rw [sum_range_succ c (m + 1), sum_range_succ (fun i => v i * c i) (m + 1)]
      nlinarith
  rcases N with _ | m
  · simp
  · exact (mul_nonneg (hv0 m (by omega)) (hc (m + 1) le_rfl)).trans (key m (by omega))

theorem sum_mul_le_of_prefixSet (σ : Equiv.Perm (Fin K)) {w α β : Fin K → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hanti : ∀ a b : Fin K, a ≤ b → w (σ b) ≤ w (σ a))
    (h : ∀ j ≤ K, ∑ k ∈ prefixSet σ j, α k ≤ ∑ k ∈ prefixSet σ j, β k) :
    ∑ k, w k * α k ≤ ∑ k, w k * β k := by
  set v : ℕ → ℝ := fun i => if h : i < K then w (σ ⟨i, h⟩) else 0
  set c : ℕ → ℝ := fun i => if h : i < K then β (σ ⟨i, h⟩) - α (σ ⟨i, h⟩) else 0
  have e : ∑ k, w k * β k - ∑ k, w k * α k = ∑ i ∈ range K, v i * c i := by
    rw [← sum_sub_distrib, ← Equiv.sum_comp σ]
    calc ∑ i : Fin K, (w (σ i) * β (σ i) - w (σ i) * α (σ i)) =
          ∑ i : Fin K, (fun i : ℕ => v i * c i) i :=
          sum_congr rfl fun i _ => by simp [v, c, i.2, mul_sub]
      _ = _ := (Finset.sum_range fun i => v i * c i).symm
  have hc : ∀ j ≤ K, 0 ≤ ∑ i ∈ range j, c i := by
    intro j hj
    have h1 := sum_prefixSet σ (fun k => β k - α k) hj
    rw [sum_sub_distrib] at h1
    have h2 : ∑ i ∈ range j, c i =
        ∑ i ∈ range j, if h : i < K then β (σ ⟨i, h⟩) - α (σ ⟨i, h⟩) else 0 := rfl
    linarith [h j hj]
  have hv : ∀ i, i + 1 < K → v (i + 1) ≤ v i := by
    intro i hi
    simp only [v, hi, (Nat.lt_succ_self i).trans hi, dite_true]
    exact hanti _ _ (Fin.mk_le_mk.2 (Nat.le_succ i))
  have hv0 : ∀ i < K, 0 ≤ v i := fun i hi => by simp only [v, hi, dite_true]; exact hw _
  linarith [abel_nonneg hv hv0 hc]

end Greedy

end MACK

namespace MACKCode

variable {K : ℕ} {M A : Fin K → Type*} {B : Type*} {n : ℕ}

noncomputable def inputLaw [∀ k, Fintype (M k)] [∀ k, Nonempty (M k)] (c : MACKCode M A B n)
    (k : Fin K) (i : Fin n) : PMF (A k) :=
  (PMF.ofFintype _ (sum_inv_card (M k))).map fun m => c.enc k m i

theorem toBlockCode_inputLaw [∀ k, Fintype (M k)] [∀ k, Nonempty (M k)] [∀ k, Fintype (A k)]
    (c : MACKCode M A B n) (i : Fin n) :
    c.toBlockCode.inputLaw i = piPMF fun k => c.inputLaw k i := by
  classical
  have hu : PMF.ofFintype (fun _ : ∀ k, M k => ((Fintype.card (∀ k, M k) : ℝ≥0∞))⁻¹)
      (sum_inv_card _) = piPMF fun k => PMF.ofFintype _ (sum_inv_card (M k)) := by
    ext m
    rw [PMF.ofFintype_apply, piPMF_apply]
    simp only [PMF.ofFintype_apply]
    rw [Fintype.card_pi, Nat.cast_prod, ENNReal.prod_inv_distrib]
    intro a _ b _ _
    exact Or.inr (ENNReal.natCast_ne_top _)
  unfold BlockCode.inputLaw
  rw [hu]
  exact piPMF_map _ fun k m => c.enc k m i

variable [∀ k, Fintype (M k)] [∀ k, Nonempty (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, MeasurableSingletonClass (M k)] [∀ k, DecidableEq (M k)]
  [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)] [∀ k, MeasurableSingletonClass (A k)]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem one_sub_mul_log_le_sum_subsetInfo (c : MACKCode M A B n) (W : DMC (∀ k, A k) B)
    (S : Finset (Fin K)) :
    (1 - (c.avgError W).toReal) * Real.log (∏ k ∈ S, (Fintype.card (M k) : ℝ)) ≤
      ∑ i, MACK.subsetInfo W (fun k => c.inputLaw k i) S + Real.log 2 := by
  classical
  set μ := c.toBlockCode.codeMeasure W
  set MS : (∀ k, M k) × (Fin n → B) → MACK.Inside M S := fun ω => (splitEquiv S ω.1).1
  set MSc : (∀ k, M k) × (Fin n → B) → MACK.Outside M S := fun ω => (splitEquiv S ω.1).2
  have hcardS : (Fintype.card (MACK.Inside M S) : ℝ) = ∏ k ∈ S, (Fintype.card (M k) : ℝ) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    exact prod_coe_sort S fun k => (Fintype.card (M k) : ℝ)
  have hcard : (Fintype.card (∀ k, M k) : ℝ) =
      Fintype.card (MACK.Inside M S) * Fintype.card (MACK.Outside M S) := by
    rw [Fintype.card_congr (splitEquiv (A := M) S), Fintype.card_prod, Nat.cast_mul]
  have hU : H[Prod.fst ; μ] = Real.log (Fintype.card (MACK.Inside M S)) +
      Real.log (Fintype.card (MACK.Outside M S)) := by
    rw [BlockCode.entropy_fst_codeMeasure, hcard,
      Real.log_mul (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
        (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
  have hUc : H[MSc ; μ] ≤ Real.log (Fintype.card (MACK.Outside M S)) := entropy_le_log_card μ
  have hF : H[MS | Prod.snd ; μ] ≤
      Real.log 2 + (c.avgError W).toReal * Real.log (Fintype.card (MACK.Inside M S)) := by
    have h := condEntropy_le_log_two_add_mul_log_card (μ := μ) (X := MS) (Y := Prod.snd)
      (measurable_of_finite _) measurable_snd fun y => (splitEquiv S (c.dec y)).1
    have hm : μ.real {ω | (fun y => (splitEquiv S (c.dec y)).1) ω.2 ≠ MS ω} ≤
        (c.avgError W).toReal := by
      rw [← avgError_toBlockCode, ← BlockCode.measureReal_dec_ne]
      exact measureReal_mono fun ω hω h' => hω (congrArg (fun m => (splitEquiv S m).1) h')
    have := mul_le_mul_of_nonneg_right hm
      (Real.log_natCast_nonneg (Fintype.card (MACK.Inside M S)))
    linarith
  have hC : H[MS | fun ω => (ω.2, MSc ω) ; μ] ≤ H[MS | Prod.snd ; μ] :=
    condEntropy_le_condEntropy_comp (μ := μ) (measurable_of_finite _) (measurable_of_finite _)
      Prod.fst
  have hN := c.toBlockCode.condEntropy_snd_fst_codeMeasure W
  have hS : H[Prod.snd | MSc ; μ] ≤ ∑ i, H[Prod.snd | fun x : (∀ k, A k) × B => MACK.mask Sᶜ x.1 ;
      W.jointMeasure (c.toBlockCode.inputLaw i)] := by
    refine (condEntropy_pi_le_sum μ (Y := Prod.snd) (fun i => measurable_of_finite _)
      (measurable_of_finite _)).trans (sum_le_sum fun i _ => ?_)
    rw [← BlockCode.map_codeMeasure, condEntropy_map _ (measurable_of_finite _) (X := Prod.snd)
      (Y := fun x : (∀ k, A k) × B => MACK.mask Sᶜ x.1) measurable_snd (measurable_of_finite _)]
    set g : MACK.Outside M S → MACK.Masked A :=
      fun v k => if h : k ∉ S then some (c.enc k (v ⟨k, h⟩) i) else none
    have he : (fun x : (∀ k, A k) × B => MACK.mask Sᶜ x.1) ∘
        (fun ω : (∀ k, M k) × (Fin n → B) => (c.toBlockCode.enc ω.1 i, ω.2 i)) = g ∘ MSc := by
      funext ω
      change MACK.mask Sᶜ (c.toBlockCode.enc ω.1 i) = g (MSc ω)
      funext k
      by_cases hk : k ∈ S <;> simp [MACK.mask, g, MSc, hk, toBlockCode, input]
    rw [he]
    exact condEntropy_le_condEntropy_comp (μ := μ) (measurable_of_finite _)
      (measurable_of_finite _) g
  have hI : ∑ i, MACK.subsetInfo W (fun k => c.inputLaw k i) S =
      ∑ i, H[Prod.snd | fun x : (∀ k, A k) × B => MACK.mask Sᶜ x.1 ;
        W.jointMeasure (c.toBlockCode.inputLaw i)] -
      ∑ i, H[Prod.snd | Prod.fst ; W.jointMeasure (c.toBlockCode.inputLaw i)] := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [MACK.subsetInfo_eq_residual, MACK.condEntropy_mask_univ, toBlockCode_inputLaw]
    rfl
  have hR : H[fun ω : (∀ k, M k) × (Fin n → B) => (MS ω, (ω.2, MSc ω)) ; μ] =
      H[fun ω : (∀ k, M k) × (Fin n → B) => (ω.2, ω.1) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω : (∀ k, M k) × (Fin n → B) => (ω.2, ω.1))
      (f := fun q => ((splitEquiv S q.2).1, (q.1, (splitEquiv S q.2).2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 ((splitEquiv S).injective (Prod.ext h.1 h.2.2))
  have key : Real.log (Fintype.card (MACK.Inside M S)) ≤
      H[Prod.snd | MSc ; μ] - H[Prod.snd | Prod.fst ; μ] +
        H[MS | fun ω => (ω.2, MSc ω) ; μ] := by
    simp only [condEntropy_def]
    rw [hR]
    linarith
  rw [← hcardS]
  have h4 : (1 - (c.avgError W).toReal) * Real.log (Fintype.card (MACK.Inside M S)) =
      Real.log (Fintype.card (MACK.Inside M S)) -
        (c.avgError W).toReal * Real.log (Fintype.card (MACK.Inside M S)) := by ring
  linarith

end MACKCode

namespace MACK

variable {K : ℕ} {A : Fin K → Type*} {B : Type*}
  [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)] [∀ k, MeasurableSingletonClass (A k)]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem greedy_mem_polymatroid (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k))
    (σ : Equiv.Perm (Fin K)) (P : Fin K → Prop) [DecidablePred P] :
    (fun k => if P k then greedy σ (subsetInfo W p) k else 0) ∈ polymatroid W p := by
  have hg0 : ∀ k, 0 ≤ greedy σ (subsetInfo W p) k :=
    greedy_nonneg σ (subsetInfo_le_insert W p)
  refine ⟨fun k => by dsimp only; split_ifs <;> simp [hg0 k], fun S => ?_⟩
  refine le_trans (sum_le_sum fun k _ => ?_) (sum_greedy_le σ (subsetInfo_empty W p)
    (subsetInfo_insert_sub_le W p) S)
  split_ifs
  · exact le_rfl
  · exact hg0 k

theorem mem_capacityRegion_of_mem_achievableRegion (W : DMC (∀ k, A k) B) {R : Fin K → ℝ}
    (hR : R ∈ achievableRegion W) : R ∈ capacityRegion W := by
  classical
  obtain ⟨hR0, hA⟩ := hR
  by_contra hRC
  have hconv : Convex ℝ (capacityRegion W) := (convex_convexHull ℝ _).closure
  obtain ⟨φ, u, hφu, huR⟩ := geometric_hahn_banach_closed_point hconv isClosed_closure hRC
  set lam : Fin K → ℝ := fun k => φ fun j => if k = j then (1 : ℝ) else 0
  have hφ : ∀ x : Fin K → ℝ, φ x = ∑ k, lam k * x k := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  set w : Fin K → ℝ := fun k => max (lam k) 0
  have hw0 : ∀ k, 0 ≤ w k := fun k => le_max_right _ _
  set gap := φ R - u
  have hgap : 0 < gap := by simp only [gap]; linarith
  set Ws := ∑ k, w k
  have hWs : 0 ≤ Ws := sum_nonneg fun k _ => hw0 k
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ε * |φ R| ≤ gap / 4 := by
    refine ⟨min (1 / 2) (gap / (4 * (|φ R| + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, ?_⟩
    calc min (1 / 2) (gap / (4 * (|φ R| + 1))) * |φ R|
        ≤ gap / (4 * (|φ R| + 1)) * (|φ R| + 1) :=
          mul_le_mul (min_le_right _ _) (by linarith) (abs_nonneg _) (by positivity)
      _ = gap / 4 := by field_simp
  obtain ⟨N, hN⟩ := hA (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε0)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (4 * (Ws * Real.log 2) / gap)
  obtain ⟨n, hnN, hn0, hn1⟩ : ∃ n : ℕ, N ≤ n ∧ n₀ ≤ n ∧ 1 ≤ n :=
    ⟨max (max N n₀) 1, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogn : Ws * Real.log 2 / n ≤ gap / 4 := by
    have h1 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn0
    rw [div_le_iff₀ hnpos]
    have := (div_lt_iff₀ hgap).1 (hn₀.trans_le h1)
    linarith
  obtain ⟨L, hL, c, hc⟩ := hN n hnN
  have hL0 : ∀ k, (0 : ℝ) < L k := fun k => (Real.exp_pos _).trans_le (hL k)
  have : ∀ k, Nonempty (Fin (L k)) := fun k => ⟨⟨0, Nat.cast_pos.1 (hL0 k)⟩⟩
  have hlam : (c.avgError W).toReal ≤ ε := ENNReal.toReal_le_of_le_ofReal hε0.le hc
  have hlam0 : 0 ≤ (c.avgError W).toReal := ENNReal.toReal_nonneg
  set f : Fin n → Finset (Fin K) → ℝ := fun i => subsetInfo W fun k => c.inputLaw k i
  have hbound : ∀ S : Finset (Fin K),
      (1 - ε) * ∑ k ∈ S, R k ≤ (1 / n) * ∑ i, f i S + Real.log 2 / n := by
    intro S
    have hB := c.one_sub_mul_log_le_sum_subsetInfo W S
    simp only [Fintype.card_fin] at hB
    have hlogS : n * ∑ k ∈ S, R k ≤ Real.log (∏ k ∈ S, (L k : ℝ)) := by
      rw [Real.log_prod fun k _ => (hL0 k).ne', mul_sum]
      exact sum_le_sum fun k _ => (Real.le_log_iff_exp_le (hL0 k)).2 (hL k)
    have hpos : 0 ≤ Real.log (∏ k ∈ S, (L k : ℝ)) :=
      Real.log_nonneg (one_le_prod₀ fun k _ =>
        Nat.one_le_cast.2 (Nat.cast_pos.1 (hL0 k)))
    have hRS : 0 ≤ ∑ k ∈ S, R k := sum_nonneg fun k _ => hR0 k
    have h1 : (1 - ε) * (n * ∑ k ∈ S, R k) ≤ (1 - (c.avgError W).toReal) *
        Real.log (∏ k ∈ S, (L k : ℝ)) :=
      (mul_le_mul_of_nonneg_left hlogS (by linarith)).trans
        (mul_le_mul_of_nonneg_right (by linarith) hpos)
    have e : (1 / (n : ℝ)) * ∑ i, f i S + Real.log 2 / n =
        (∑ i, f i S + Real.log 2) / n := by ring
    rw [e, le_div_iff₀ hnpos]
    nlinarith
  set σ := Tuple.sort fun k => -w k
  have hanti : ∀ a b : Fin K, a ≤ b → w (σ b) ≤ w (σ a) := fun a b hab => by
    have := Tuple.monotone_sort (fun k => -w k) hab
    simp only [Function.comp] at this
    linarith
  set g : Fin n → Fin K → ℝ := fun i => greedy σ (f i)
  set xbar : Fin K → ℝ := fun k => (1 / n) * ∑ i, g i k
  have hprefix : ∀ j ≤ K, ∑ k ∈ prefixSet σ j, xbar k = (1 / n) * ∑ i, f i (prefixSet σ j) := by
    intro j hj
    simp only [xbar, ← mul_sum]
    rw [sum_comm]
    exact congrArg _ (sum_congr rfl fun i _ =>
      sum_greedy_prefixSet σ (f i) (subsetInfo_empty W _) hj)
  have habel : ∑ k, w k * ((1 - ε) * R k) ≤ ∑ k, w k * (xbar k + Real.log 2 / n) := by
    refine sum_mul_le_of_prefixSet σ hw0 hanti fun j hj => ?_
    rw [← mul_sum, sum_add_distrib, hprefix j hj, sum_const, nsmul_eq_mul]
    rcases (prefixSet σ j).eq_empty_or_nonempty with he | hne
    · simp [he, f, subsetInfo_empty]
    · have h1 : (1 : ℝ) ≤ (prefixSet σ j).card := Nat.one_le_cast.2 (card_pos.2 hne)
      have h2 := hbound (prefixSet σ j)
      have h3 : Real.log 2 / n ≤ (prefixSet σ j).card * (Real.log 2 / n) :=
        le_mul_of_one_le_left (div_nonneg hlog2 hnpos.le) h1
      linarith
  set y : Fin n → Fin K → ℝ := fun i k => if 0 ≤ lam k then g i k else 0
  have hy : ∀ i, y i ∈ polymatroid W fun k => c.inputLaw k i := fun i =>
    greedy_mem_polymatroid W _ σ (fun k => 0 ≤ lam k)
  set ybar : Fin K → ℝ := ∑ i, (1 / (n : ℝ)) • y i
  have hybar : ybar ∈ capacityRegion W := by
    refine subset_closure ((convex_convexHull ℝ _).sum_mem (fun i _ => by positivity) ?_
      fun i _ => subset_convexHull ℝ _ (Set.mem_iUnion.2 ⟨_, hy i⟩))
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hφy : φ ybar = ∑ k, w k * xbar k := by
    rw [hφ]
    refine sum_congr rfl fun k _ => ?_
    simp only [ybar, y, xbar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w]
    by_cases hk : 0 ≤ lam k
    · simp [hk, mul_sum]
    · simp [hk, max_eq_right (le_of_lt (not_le.1 hk))]
  have hφR : φ R ≤ ∑ k, w k * R k := by
    rw [hφ]
    exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hR0 k)
  have hlt : φ ybar < u := hφu _ hybar
  have e1 : ∑ k, w k * ((1 - ε) * R k) = (1 - ε) * ∑ k, w k * R k := by
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have e2 : ∑ k, w k * (xbar k + Real.log 2 / n) = ∑ k, w k * xbar k + Ws * Real.log 2 / n := by
    rw [mul_div_assoc, sum_mul]
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  have h5 : (1 - ε) * φ R ≤ (1 - ε) * ∑ k, w k * R k :=
    mul_le_mul_of_nonneg_left hφR (by linarith)
  have h6 : -(ε * |φ R|) ≤ -(ε * φ R) := by
    have := le_abs_self (φ R)
    nlinarith
  have hgapdef : gap = φ R - u := rfl
  nlinarith [abs_nonneg (φ R)]

end MACK

end Meat
