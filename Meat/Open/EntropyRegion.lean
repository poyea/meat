import Mathlib.Computability.RE
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Real
import Meat.Shannon.Markov
import Meat.Shannon.Product

open MeasureTheory Finset

namespace Meat

variable {Ω S : Type*} [MeasurableSpace Ω] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S] {n : ℕ}

def subvector (X : Fin n → Ω → S) (A : Finset (Fin n)) (ω : Ω) : A → S := fun i => X i ω

noncomputable def entropyVector (X : Fin n → Ω → S) (μ : Measure Ω) (A : Finset (Fin n)) : ℝ :=
  H[subvector X A ; μ]

def entropyRegion (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {h | ∃ (k : ℕ) (μ : Measure (Fin n → Fin k)), IsProbabilityMeasure μ ∧
    h = entropyVector (fun i x => x i) μ}

def shannonRegion (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {h | h ∅ = 0 ∧ Monotone h ∧ ∀ A B, h (A ∪ B) + h (A ∩ B) ≤ h A + h B}

def zhangYeungRegion : Set (Finset (Fin 4) → ℝ) :=
  {h | 2 * (h {2} + h {3} - h {2, 3})
    ≤ h {0} + h {1} - h {0, 1} + (h {0} + h {2, 3} - h {0, 2, 3})
      + 3 * (h {0, 2} + h {0, 3} - h {0, 2, 3} - h {0})
      + (h {1, 2} + h {1, 3} - h {1, 2, 3} - h {1})}

def subsetCode (A : Finset (Fin n)) : ℕ := ∑ i ∈ A, 2 ^ (i : ℕ)

noncomputable def entropyFunctional (n : ℕ) (c : List ℤ) (h : Finset (Fin n) → ℝ) : ℝ :=
  ∑ A, (c.getD (subsetCode A) 0 : ℝ) * h A

def InformationInequalitiesDecidable : Prop :=
  ComputablePred fun p : ℕ × List ℤ => ∀ h ∈ entropyRegion p.1, 0 ≤ entropyFunctional p.1 p.2 h

section Vector

variable (μ : Measure Ω) {X : Fin n → Ω → S}

omit [Fintype S] [MeasurableSingletonClass S] in
theorem measurable_subvector (hX : ∀ i, Measurable (X i)) (A : Finset (Fin n)) :
    Measurable (subvector X A) :=
  measurable_pi_iff.2 fun i => hX i

variable [IsProbabilityMeasure μ]

omit [MeasurableSingletonClass S] in
theorem entropyVector_empty : entropyVector X μ ∅ = 0 := by
  refine le_antisymm ?_ (entropy_nonneg μ _)
  have := entropy_le_log_card μ (X := subvector X ∅)
  change H[subvector X ∅ ; μ] ≤ 0
  simpa using this

theorem entropyVector_mono (hX : ∀ i, Measurable (X i)) : Monotone (entropyVector X μ) :=
  fun A B hAB => entropy_comp_le μ (measurable_subvector hX B)
    fun (f : ↥B → S) (i : ↥A) => f ⟨i.1, hAB i.2⟩

theorem entropyVector_submodular (hX : ∀ i, Measurable (X i)) (A B : Finset (Fin n)) :
    entropyVector X μ (A ∪ B) + entropyVector X μ (A ∩ B)
      ≤ entropyVector X μ A + entropyVector X μ B := by
  have h := entropy_submodular μ (measurable_subvector hX A) (measurable_subvector hX B)
    (measurable_subvector hX (A ∩ B))
  have h1 : H[fun ω => (subvector X A ω, subvector X (A ∩ B) ω) ; μ] = H[subvector X A ; μ] :=
    entropy_pair_comp μ fun (f : ↥A → S) (i : ↥(A ∩ B)) => f ⟨i.1, (mem_inter.1 i.2).1⟩
  have h2 : H[fun ω => (subvector X B ω, subvector X (A ∩ B) ω) ; μ] = H[subvector X B ; μ] :=
    entropy_pair_comp μ fun (f : ↥B → S) (i : ↥(A ∩ B)) => f ⟨i.1, (mem_inter.1 i.2).2⟩
  have h3 : H[fun ω => ((subvector X A ω, subvector X B ω), subvector X (A ∩ B) ω) ; μ]
      = H[subvector X (A ∪ B) ; μ] :=
    entropy_comp_of_injective μ (X := subvector X (A ∪ B))
      (f := fun (f : ↥(A ∪ B) → S) => ((fun i : ↥A => f ⟨i.1, mem_union_left _ i.2⟩,
        fun i : ↥B => f ⟨i.1, mem_union_right _ i.2⟩),
        fun i : ↥(A ∩ B) => f ⟨i.1, mem_union_left _ (mem_inter.1 i.2).1⟩))
      (fun f g e => by
        funext ⟨i, hi⟩
        rcases mem_union.1 hi with hi | hi
        · exact congrFun (congrArg (fun p => p.1.1) e) ⟨i, hi⟩
        · exact congrFun (congrArg (fun p => p.1.2) e) ⟨i, hi⟩)
  simp only [entropyVector]
  rw [h1, h2, h3] at h
  linarith

theorem entropyVector_mem_shannonRegion (hX : ∀ i, Measurable (X i)) :
    entropyVector X μ ∈ shannonRegion n :=
  ⟨entropyVector_empty μ, entropyVector_mono μ hX, entropyVector_submodular μ hX⟩

omit [IsProbabilityMeasure μ] [MeasurableSingletonClass S] in
theorem entropyVector_eq_map (hX : ∀ i, Measurable (X i)) :
    entropyVector X μ = entropyVector (fun i x => x i) (μ.map fun ω i => X i ω) := by
  funext A
  have hg : Measurable fun ω i => X i ω := measurable_pi_iff.2 hX
  exact (entropy_map μ hg (measurable_subvector (fun i => measurable_pi_apply i) A)).symm

theorem entropyVector_map_emb {m : ℕ} (hX : ∀ i, Measurable (X i)) (e : Fin m ↪ Fin n)
    (A : Finset (Fin m)) :
    entropyVector X μ (A.map e) = entropyVector (fun i => X (e i)) μ A := by
  classical
  have hY := measurable_subvector hX (A.map e)
  have hZ := measurable_subvector (X := fun i => X (e i)) (fun i => hX (e i)) A
  let g : (↥A → S) → (↥(A.map e) → S) := fun v j =>
    v ⟨(mem_map.1 j.2).choose, (mem_map.1 j.2).choose_spec.1⟩
  have hg : subvector X (A.map e) = g ∘ subvector (fun i => X (e i)) A := by
    funext ω j
    simp only [Function.comp, g, subvector]
    rw [(mem_map.1 j.2).choose_spec.2]
  have hf : subvector (fun i => X (e i)) A
      = (fun u (i : ↥A) => u ⟨e i, mem_map_of_mem e i.2⟩) ∘ subvector X (A.map e) := rfl
  refine le_antisymm ?_ ?_
  · simp only [entropyVector]
    rw [hg]
    exact entropy_comp_le μ hZ g
  · simp only [entropyVector]
    rw [hf]
    exact entropy_comp_le μ hY _

theorem entropyVector_mem_entropyRegion (hX : ∀ i, Measurable (X i)) :
    entropyVector X μ ∈ entropyRegion n := by
  classical
  let e := Fintype.equivFin S
  have hg : Measurable fun ω (i : Fin n) => e (X i ω) :=
    measurable_pi_iff.2 fun i => (measurable_of_finite e).comp (hX i)
  refine ⟨Fintype.card S, μ.map fun ω i => e (X i ω), inferInstance, ?_⟩
  rw [← entropyVector_eq_map μ (X := fun i ω => e (X i ω))
    fun i => (measurable_of_finite e).comp (hX i)]
  funext A
  exact (entropy_comp_of_injective μ (X := subvector X A) (f := fun f => e ∘ f)
    fun f g h => funext fun i => e.injective (congrFun h i)).symm

private lemma entropyVector_eq_entropy {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (hX : ∀ i, Measurable (X i)) (A : Finset (Fin n)) (W : Ω → T)
    (f : (↥A → S) → T) (g : T → ↥A → S) (hf : ∀ ω, W ω = f (subvector X A ω))
    (hg : ∀ ω, subvector X A ω = g (W ω)) : entropyVector X μ A = H[W ; μ] := by
  have hW : W = f ∘ subvector X A := funext hf
  have hV : subvector X A = g ∘ W := funext hg
  have hWm : Measurable W := hW ▸ (measurable_of_finite f).comp (measurable_subvector hX A)
  refine le_antisymm ?_ ?_
  · simp only [entropyVector]
    rw [hV]
    exact entropy_comp_le μ hWm g
  · rw [hW]
    exact entropy_comp_le μ (measurable_subvector hX A) f

end Vector

theorem entropyRegion_subset_shannonRegion : entropyRegion n ⊆ shannonRegion n := by
  rintro _ ⟨k, μ, hμ, rfl⟩
  exact entropyVector_mem_shannonRegion μ fun i => measurable_pi_apply i

theorem isClosed_shannonRegion : IsClosed (shannonRegion n) := by
  have h1 : IsClosed {h : Finset (Fin n) → ℝ | h ∅ = 0} := isClosed_eq (continuous_apply _)
    continuous_const
  have h2 : IsClosed {h : Finset (Fin n) → ℝ | Monotone h} := by
    have : {h : Finset (Fin n) → ℝ | Monotone h}
        = ⋂ A, ⋂ B, ⋂ (_ : A ≤ B), {h | h A ≤ h B} := by
      ext h
      simp [Monotone]
    rw [this]
    exact isClosed_iInter fun A => isClosed_iInter fun B => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply _) (continuous_apply _)
  have h3 : IsClosed {h : Finset (Fin n) → ℝ | ∀ A B, h (A ∪ B) + h (A ∩ B) ≤ h A + h B} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun A => isClosed_iInter fun B =>
      isClosed_le (by fun_prop) (by fun_prop)
  have e : shannonRegion n = {h : Finset (Fin n) → ℝ | h ∅ = 0} ∩ {h | Monotone h}
      ∩ {h | ∀ A B, h (A ∪ B) + h (A ∩ B) ≤ h A + h B} := by
    ext
    simp [shannonRegion, and_assoc]
  rw [e]
  exact (h1.inter h2).inter h3

theorem closure_entropyRegion_subset_shannonRegion :
    closure (entropyRegion n) ⊆ shannonRegion n :=
  closure_minimal entropyRegion_subset_shannonRegion isClosed_shannonRegion

section Copy

variable {α K C : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype K] [DecidableEq K] [MeasurableSpace K] [MeasurableSingletonClass K]
  [Fintype C] [DecidableEq C] [MeasurableSpace C] [MeasurableSingletonClass C]

private noncomputable def massK (p : α → ℝ) (key : α → K) (κ : K) : ℝ :=
  ∑ x, if key x = κ then p x else 0

private noncomputable def massKC (p : α → ℝ) (key : α → K) (c : α → C) (κ : K) (r : C) : ℝ :=
  ∑ x, if key x = κ ∧ c x = r then p x else 0

private noncomputable def copyWeight (p : α → ℝ) (key : α → K) (c : α → C) (z : α × C) : ℝ :=
  p z.1 * massKC p key c (key z.1) z.2 / massK p key (key z.1)

private noncomputable def copyMeasure (p : α → ℝ) (key : α → K) (c : α → C) : Measure (α × C) :=
  ∑ z, ENNReal.ofReal (copyWeight p key c z) • Measure.dirac z

variable {p : α → ℝ} (hp : ∀ x, 0 ≤ p x) (key : α → K) (c : α → C)
include hp

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Fintype K] in
private lemma massK_nonneg (κ : K) : 0 ≤ massK p key κ :=
  sum_nonneg fun x _ => by split_ifs <;> simp [hp x]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Fintype K] [Fintype C] [MeasurableSpace C]
  [MeasurableSingletonClass C] in
private lemma massKC_le (κ : K) (r : C) : massKC p key c κ r ≤ massK p key κ :=
  sum_le_sum fun x _ => by
    by_cases h1 : key x = κ <;> by_cases h2 : c x = r <;> simp [h1, h2, hp x]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Fintype K] [Fintype C] [MeasurableSpace C]
  [MeasurableSingletonClass C] in
private lemma massKC_nonneg (κ : K) (r : C) : 0 ≤ massKC p key c κ r :=
  sum_nonneg fun x _ => by split_ifs <;> simp [hp x]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Fintype K] [Fintype C] [MeasurableSpace C]
  [MeasurableSingletonClass C] in
private lemma copyWeight_nonneg (z : α × C) : 0 ≤ copyWeight p key c z :=
  div_nonneg (mul_nonneg (hp _) (massKC_nonneg hp key c _ _)) (massK_nonneg hp key _)

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Fintype K] in
private lemma le_massK (x : α) : p x ≤ massK p key (key x) := by
  have := single_le_sum (f := fun y => if key y = key x then p y else 0)
    (fun y _ => by split_ifs <;> simp [hp y]) (mem_univ x)
  simpa [massK] using this

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Fintype K] [MeasurableSpace C] [MeasurableSingletonClass C] hp in
private lemma sum_massKC (κ : K) : ∑ r, massKC p key c κ r = massK p key κ := by
  simp only [massKC, massK]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  by_cases h : key x = κ <;> simp [h]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Fintype K] [MeasurableSpace C] [MeasurableSingletonClass C] in
private lemma sum_copyWeight (x : α) : ∑ r, copyWeight p key c (x, r) = p x := by
  have e : ∀ r, copyWeight p key c (x, r)
      = p x / massK p key (key x) * massKC p key c (key x) r := fun r => by
    simp only [copyWeight]
    ring
  simp only [e]
  rw [← mul_sum, sum_massKC key c]
  rcases eq_or_ne (massK p key (key x)) 0 with h | h
  · have : p x = 0 := le_antisymm (h ▸ le_massK hp key x) (hp x)
    simp [this]
  · field_simp

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Fintype K] [Fintype C] [MeasurableSpace C]
  [MeasurableSingletonClass C] in
private lemma sum_key_copyWeight (κ : K) (r : C) :
    ∑ x, (if key x = κ then copyWeight p key c (x, r) else 0) = massKC p key c κ r := by
  have e : ∀ x, (if key x = κ then copyWeight p key c (x, r) else 0)
      = (if key x = κ then p x else 0) * (massKC p key c κ r / massK p key κ) := by
    intro x
    by_cases h : key x = κ
    · simp [copyWeight, h, mul_div_assoc]
    · simp [h]
  simp only [e]
  rw [← sum_mul]
  change massK p key κ * _ = _
  rcases eq_or_ne (massK p key κ) 0 with h | h
  · have h0 : massKC p key c κ r = 0 :=
      le_antisymm (h ▸ massKC_le hp key c κ r) (massKC_nonneg hp key c κ r)
    simp [h, h0]
  · field_simp

omit [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K] in
private lemma copyMeasure_apply (E : Set (α × C)) [DecidablePred (· ∈ E)] :
    copyMeasure p key c E = ENNReal.ofReal (∑ z, if z ∈ E then copyWeight p key c z else 0) := by
  have hnn : ∀ z ∈ (univ : Finset (α × C)),
      0 ≤ (if z ∈ E then copyWeight p key c z else 0) := fun z _ => by
    split_ifs
    exacts [copyWeight_nonneg hp key c z, le_rfl]
  rw [ENNReal.ofReal_sum_of_nonneg hnn]
  simp only [copyMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]
  refine sum_congr rfl fun z _ => ?_
  by_cases hz : z ∈ E <;> simp [hz]

omit [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K] in
private lemma copyMeasure_real (E : Set (α × C)) [DecidablePred (· ∈ E)] :
    (copyMeasure p key c).real E = ∑ z, if z ∈ E then copyWeight p key c z else 0 := by
  rw [measureReal_def, copyMeasure_apply hp key c, ENNReal.toReal_ofReal (sum_nonneg fun z _ => by
    split_ifs
    exacts [copyWeight_nonneg hp key c z, le_rfl])]

omit [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K] in
private lemma isProbabilityMeasure_copyMeasure (h1 : ∑ x, p x = 1) :
    IsProbabilityMeasure (copyMeasure p key c) := by
  classical
  refine ⟨?_⟩
  rw [copyMeasure_apply hp key c Set.univ]
  simp only [Set.mem_univ, ite_true, Fintype.sum_prod_type, sum_copyWeight hp key c, h1,
    ENNReal.ofReal_one]

omit [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K] in
private lemma copyMeasure_map_fst (h1 : ∑ x, p x = 1) (P : Measure α) [IsFiniteMeasure P]
    (hP : ∀ x, P.real {x} = p x) : (copyMeasure p key c).map Prod.fst = P := by
  classical
  have := isProbabilityMeasure_copyMeasure hp key c h1
  refine Measure.ext_of_singleton fun x => ?_
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top P _),
    map_measureReal_apply measurable_fst (measurableSet_singleton x), copyMeasure_real hp key c,
    hP, Fintype.sum_prod_type]
  congr 1
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [sum_eq_single x (fun y _ hy => by simp [hy]) (by simp)]
  simpa using sum_copyWeight hp key c x

omit [Fintype K] in
private lemma copyMeasure_map_pair [Finite K] (h1 : ∑ x, p x = 1) :
    (copyMeasure p key c).map (fun z => (z.2, key z.1))
      = (copyMeasure p key c).map (fun z => (c z.1, key z.1)) := by
  classical
  have := isProbabilityMeasure_copyMeasure hp key c h1
  refine Measure.ext_of_singleton fun ⟨r, κ⟩ => ?_
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top _ _),
    map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _),
    map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _),
    copyMeasure_real hp key c, copyMeasure_real hp key c, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  congr 1
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
  have l : ∀ x, (∑ r', if r' = r ∧ key x = κ then copyWeight p key c (x, r') else 0)
      = if key x = κ then copyWeight p key c (x, r) else 0 := fun x => by
    by_cases h : key x = κ <;> simp [h]
  have m : ∀ x, (∑ r', if c x = r ∧ key x = κ then copyWeight p key c (x, r') else 0)
      = if key x = κ ∧ c x = r then p x else 0 := fun x => by
    by_cases h : key x = κ <;> by_cases h' : c x = r <;> simp [h, h', sum_copyWeight hp key c]
  simp only [l, m, sum_key_copyWeight hp key c]
  rfl

private lemma copyMeasure_markov (h1 : ∑ x, p x = 1) :
    MarkovChain (fun z : α × C => z.2) (fun z => key z.1) (fun z => z.1)
      (copyMeasure p key c) := by
  classical
  have := isProbabilityMeasure_copyMeasure hp key c h1
  rw [markovChain_iff measurable_snd (measurable_of_finite _) measurable_fst]
  intro r κ x
  simp only [copyMeasure_real hp key c, Set.mem_ofPred_eq, Fintype.sum_prod_type]
  have a1 : (∑ y, ∑ r', if r' = r ∧ key y = κ ∧ y = x then copyWeight p key c (y, r') else 0)
      = if key x = κ then copyWeight p key c (x, r) else 0 := by
    rw [sum_eq_single x (fun y _ hy => by simp [hy]) (by simp)]
    by_cases h : key x = κ <;> simp [h]
  have a2 : (∑ y, ∑ r', if key y = κ then copyWeight p key c (y, r') else 0) = massK p key κ := by
    refine sum_congr rfl fun y _ => ?_
    by_cases h : key y = κ <;> simp [h, sum_copyWeight hp key c]
  have a3 : (∑ y, ∑ r', if r' = r ∧ key y = κ then copyWeight p key c (y, r') else 0)
      = massKC p key c κ r := by
    rw [← sum_key_copyWeight hp key c]
    refine sum_congr rfl fun y _ => ?_
    by_cases h : key y = κ <;> simp [h]
  have a4 : (∑ y, ∑ r', if key y = κ ∧ y = x then copyWeight p key c (y, r') else 0)
      = if key x = κ then p x else 0 := by
    rw [sum_eq_single x (fun y _ hy => by simp [hy]) (by simp)]
    by_cases h : key x = κ <;> simp [h, sum_copyWeight hp key c]
  rw [a1, a2, a3, a4]
  by_cases h : key x = κ
  · subst h
    simp only [ite_true, copyWeight]
    rcases eq_or_ne (massK p key (key x)) 0 with h0 | h0
    · have : p x = 0 := le_antisymm (h0 ▸ le_massK hp key x) (hp x)
      simp [this]
    · field_simp
  · simp [h]

end Copy

theorem isClosed_zhangYeungRegion : IsClosed zhangYeungRegion :=
  isClosed_le (by fun_prop) (by fun_prop)

private lemma submod_of {m : ℕ} {g : Finset (Fin m) → ℝ}
    (hsub : ∀ A B, g (A ∪ B) + g (A ∩ B) ≤ g A + g B) (s t u v : Finset (Fin m))
    (hu : s ∪ t = u) (hv : s ∩ t = v) : g u + g v ≤ g s + g t :=
  hu ▸ hv ▸ hsub s t

private lemma zhangYeung_of_copy (g : Finset (Fin 5) → ℝ)
    (hsub : ∀ A B, g (A ∪ B) + g (A ∩ B) ≤ g A + g B)
    (e1 : g {4} = g {0}) (e2 : g {2, 4} = g {0, 2}) (e3 : g {3, 4} = g {0, 3})
    (e4 : g {2, 3, 4} = g {0, 2, 3})
    (e5 : g {2, 3, 4} + g {0, 1, 2, 3} = g {0, 1, 2, 3, 4} + g {2, 3}) :
    2 * (g {2} + g {3} - g {2, 3})
      ≤ g {0} + g {1} - g {0, 1} + (g {0} + g {2, 3} - g {0, 2, 3})
        + 3 * (g {0, 2} + g {0, 3} - g {0, 2, 3} - g {0})
        + (g {1, 2} + g {1, 3} - g {1, 2, 3} - g {1}) := by
  have i1 := submod_of hsub {1, 2, 4} {1, 3, 4} {1, 2, 3, 4} {1, 4} (by decide) (by decide)
  have i2 := submod_of hsub {0, 1, 2, 3} {1, 2, 3, 4} {0, 1, 2, 3, 4} {1, 2, 3} (by decide)
    (by decide)
  have i3 := submod_of hsub {0, 1, 3} {0, 1, 4} {0, 1, 3, 4} {0, 1} (by decide) (by decide)
  have i4 := submod_of hsub {0, 2} {2, 4} {0, 2, 4} {2} (by decide) (by decide)
  have i5 := submod_of hsub {1, 2} {2, 4} {1, 2, 4} {2} (by decide) (by decide)
  have i6 := submod_of hsub {0, 2, 4} {0, 3, 4} {0, 2, 3, 4} {0, 4} (by decide) (by decide)
  have i7 := submod_of hsub {0, 4} {1, 4} {0, 1, 4} {4} (by decide) (by decide)
  have i8 := submod_of hsub {0, 3} {3, 4} {0, 3, 4} {3} (by decide) (by decide)
  have i9 := submod_of hsub {1, 3} {3, 4} {1, 3, 4} {3} (by decide) (by decide)
  have i10 := submod_of hsub {0, 1, 2, 3} {0, 1, 3, 4} {0, 1, 2, 3, 4} {0, 1, 3} (by decide)
    (by decide)
  have i11 := submod_of hsub {0, 1, 2, 3} {0, 2, 3, 4} {0, 1, 2, 3, 4} {0, 2, 3} (by decide)
    (by decide)
  linarith

theorem entropyRegion_subset_zhangYeungRegion : entropyRegion 4 ⊆ zhangYeungRegion := by
  rintro _ ⟨k, μ, hμ, rfl⟩
  let p : (Fin 4 → Fin k) → ℝ := fun x => μ.real {x}
  have hp : ∀ x, 0 ≤ p x := fun _ => measureReal_nonneg
  have h1 : ∑ x, p x = 1 := sum_measureReal_singleton_eq_one μ
  let key : (Fin 4 → Fin k) → Fin k × Fin k := fun x => (x 2, x 3)
  let c : (Fin 4 → Fin k) → Fin k := fun x => x 0
  let ν := copyMeasure p key c
  have : IsProbabilityMeasure ν := isProbabilityMeasure_copyMeasure hp key c h1
  let Y : Fin 5 → (Fin 4 → Fin k) × Fin k → Fin k :=
    fun i z => ![z.1 0, z.1 1, z.1 2, z.1 3, z.2] i
  have hY : ∀ i, Measurable (Y i) := fun i => measurable_of_finite _
  have hT : ∀ A : Finset (Fin 4),
      entropyVector Y ν (A.map Fin.castSuccEmb) = entropyVector (fun i x => x i) μ A := by
    intro A
    rw [entropyVector_map_emb ν hY]
    have e : (fun i => Y (Fin.castSuccEmb i)) = fun i (z : (Fin 4 → Fin k) × Fin k) => z.1 i := by
      funext i z
      fin_cases i <;> rfl
    rw [e, entropyVector_eq_map ν fun i => measurable_of_finite _]
    congr 1
    exact copyMeasure_map_fst hp key c h1 μ fun _ => rfl
  let e4 : Fin 3 ↪ Fin 5 := ⟨![4, 2, 3], by decide⟩
  let e0 : Fin 3 ↪ Fin 5 := ⟨![0, 2, 3], by decide⟩
  have hlaw : ∀ B : Finset (Fin 3),
      entropyVector Y ν (B.map e4) = entropyVector Y ν (B.map e0) := by
    intro B
    rw [entropyVector_map_emb ν hY, entropyVector_map_emb ν hY,
      entropyVector_eq_map ν fun i => hY _, entropyVector_eq_map ν fun i => hY _]
    congr 1
    let ψ : Fin k × (Fin k × Fin k) → Fin 3 → Fin k := fun t => ![t.1, t.2.1, t.2.2]
    have a : (fun z (i : Fin 3) => Y (e4 i) z) = ψ ∘ fun z => (z.2, key z.1) := by
      funext z i
      fin_cases i <;> rfl
    have b : (fun z (i : Fin 3) => Y (e0 i) z) = ψ ∘ fun z => (c z.1, key z.1) := by
      funext z i
      fin_cases i <;> rfl
    rw [a, b, ← Measure.map_map (measurable_of_finite ψ) (measurable_of_finite _),
      ← Measure.map_map (measurable_of_finite ψ) (measurable_of_finite _),
      copyMeasure_map_pair hp key c h1]
  have tl : ∀ (B : Finset (Fin 3)) (B4 B0 : Finset (Fin 5)), B.map e4 = B4 → B.map e0 = B0 →
      entropyVector Y ν B4 = entropyVector Y ν B0 := fun B _ _ h4 h0 => h4 ▸ h0 ▸ hlaw B
  have hM := copyMeasure_markov hp key c h1
  rw [markovChain_def, condMutualInfo_def, condEntropy_def, condEntropy_def,
    condEntropy_def] at hM
  have r1 : entropyVector Y ν {2, 3, 4}
      = H[fun z : (Fin 4 → Fin k) × Fin k => (z.2, key z.1) ; ν] :=
    entropyVector_eq_entropy ν hY _ _
      (fun u => (u ⟨4, by decide⟩, (u ⟨2, by decide⟩, u ⟨3, by decide⟩)))
      (fun t i => ![t.1, t.1, t.2.1, t.2.2, t.1] i.1) (fun _ => rfl) (fun z => by
        funext ⟨i, hi⟩
        revert hi
        fin_cases i <;> intro hi <;> first | rfl | exact absurd hi (by decide))
  have r2 : entropyVector Y ν {0, 1, 2, 3}
      = H[fun z : (Fin 4 → Fin k) × Fin k => (z.1, key z.1) ; ν] :=
    entropyVector_eq_entropy ν hY _ _
      (fun u => (![u ⟨0, by decide⟩, u ⟨1, by decide⟩, u ⟨2, by decide⟩, u ⟨3, by decide⟩],
        (u ⟨2, by decide⟩, u ⟨3, by decide⟩)))
      (fun t i => ![t.1 0, t.1 1, t.1 2, t.1 3, t.1 0] i.1)
      (fun z => by
        refine Prod.ext ?_ rfl
        funext j
        fin_cases j <;> rfl)
      (fun z => by
        funext ⟨i, hi⟩
        revert hi
        fin_cases i <;> intro hi <;> first | rfl | exact absurd hi (by decide))
  have r3 : entropyVector Y ν {0, 1, 2, 3, 4}
      = H[fun z : (Fin 4 → Fin k) × Fin k => ((z.2, z.1), key z.1) ; ν] :=
    entropyVector_eq_entropy ν hY _ _
      (fun u => ((u ⟨4, by decide⟩, ![u ⟨0, by decide⟩, u ⟨1, by decide⟩, u ⟨2, by decide⟩,
        u ⟨3, by decide⟩]), (u ⟨2, by decide⟩, u ⟨3, by decide⟩)))
      (fun t i => ![t.1.2 0, t.1.2 1, t.1.2 2, t.1.2 3, t.1.1] i.1)
      (fun z => by
        refine Prod.ext (Prod.ext rfl ?_) rfl
        funext j
        fin_cases j <;> rfl)
      (fun z => by
        funext ⟨i, hi⟩
        revert hi
        fin_cases i <;> intro hi <;> rfl)
  have r4 : entropyVector Y ν {2, 3} = H[fun z : (Fin 4 → Fin k) × Fin k => key z.1 ; ν] :=
    entropyVector_eq_entropy ν hY _ _ (fun u => (u ⟨2, by decide⟩, u ⟨3, by decide⟩))
      (fun t i => ![t.1, t.1, t.1, t.2, t.1] i.1) (fun _ => rfl) (fun z => by
        funext ⟨i, hi⟩
        revert hi
        fin_cases i <;> intro hi <;> first | rfl | exact absurd hi (by decide))
  have e5 : entropyVector Y ν {2, 3, 4} + entropyVector Y ν {0, 1, 2, 3}
      = entropyVector Y ν {0, 1, 2, 3, 4} + entropyVector Y ν {2, 3} := by
    rw [r1, r2, r3, r4]
    linarith
  have hZY := zhangYeung_of_copy (entropyVector Y ν)
    (entropyVector_submodular ν hY)
    (tl {0} {4} {0} (by simp only [e4]; decide) (by simp only [e0]; decide))
    (tl {0, 1} {2, 4} {0, 2} (by simp only [e4]; decide) (by simp only [e0]; decide))
    (tl {0, 2} {3, 4} {0, 3} (by simp only [e4]; decide) (by simp only [e0]; decide))
    (tl {0, 1, 2} {2, 3, 4} {0, 2, 3} (by simp only [e4]; decide) (by simp only [e0]; decide)) e5
  have t : ∀ A : Finset (Fin 4), ∀ B : Finset (Fin 5), A.map Fin.castSuccEmb = B →
      entropyVector Y ν B = entropyVector (fun i x => x i) μ A := fun A B h => h ▸ hT A
  simp only [zhangYeungRegion, Set.mem_ofPred_eq]
  rwa [t {2} {2} (by decide), t {3} {3} (by decide), t {2, 3} {2, 3} (by decide),
    t {0} {0} (by decide), t {1} {1} (by decide), t {0, 1} {0, 1} (by decide),
    t {0, 2, 3} {0, 2, 3} (by decide), t {0, 2} {0, 2} (by decide), t {0, 3} {0, 3} (by decide),
    t {1, 2} {1, 2} (by decide), t {1, 3} {1, 3} (by decide),
    t {1, 2, 3} {1, 2, 3} (by decide)] at hZY

theorem closure_entropyRegion_subset_zhangYeungRegion :
    closure (entropyRegion 4) ⊆ zhangYeungRegion :=
  closure_minimal entropyRegion_subset_zhangYeungRegion isClosed_zhangYeungRegion

theorem entropyVector_mem_zhangYeungRegion {X : Fin 4 → Ω → S} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : ∀ i, Measurable (X i)) :
    entropyVector X μ ∈ zhangYeungRegion :=
  entropyRegion_subset_zhangYeungRegion (entropyVector_mem_entropyRegion μ hX)

private def zyWitness (A : Finset (Fin 4)) : ℕ :=
  if A = ∅ then 0 else if A = {0, 1} then 4 else min 4 (A.card + 1)

private lemma zyWitness_mono : ∀ A B : Finset (Fin 4), A ⊆ B → zyWitness A ≤ zyWitness B := by
  decide

private lemma zyWitness_submod : ∀ A B : Finset (Fin 4),
    zyWitness (A ∪ B) + zyWitness (A ∩ B) ≤ zyWitness A + zyWitness B := by
  decide

theorem shannonRegion_not_subset_zhangYeungRegion : ¬shannonRegion 4 ⊆ zhangYeungRegion := by
  intro hsub
  have hmem : (fun A => (zyWitness A : ℝ)) ∈ shannonRegion 4 :=
    ⟨by simp [zyWitness], fun A B h => by
      change (zyWitness A : ℝ) ≤ zyWitness B
      exact_mod_cast zyWitness_mono A B h, fun A B => by
      change ((zyWitness (A ∪ B) : ℕ) : ℝ) + zyWitness (A ∩ B) ≤ zyWitness A + zyWitness B
      exact_mod_cast zyWitness_submod A B⟩
  have h := hsub hmem
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ :
      zyWitness {2} = 2 ∧ zyWitness {3} = 2 ∧ zyWitness {2, 3} = 3 ∧ zyWitness {0} = 2 ∧
      zyWitness {1} = 2 ∧ zyWitness {0, 1} = 4 ∧ zyWitness {0, 2, 3} = 4 ∧
      zyWitness {0, 2} = 3 ∧ zyWitness {0, 3} = 3 ∧ zyWitness {1, 2} = 3 ∧
      zyWitness {1, 3} = 3 ∧ zyWitness {1, 2, 3} = 4 := by decide
  simp only [zhangYeungRegion, Set.mem_ofPred_eq, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12] at h
  norm_num at h

theorem closure_entropyRegion_ssubset_shannonRegion :
    closure (entropyRegion 4) ⊂ shannonRegion 4 :=
  ⟨closure_entropyRegion_subset_shannonRegion, fun h =>
    shannonRegion_not_subset_zhangYeungRegion
      (h.trans closure_entropyRegion_subset_zhangYeungRegion)⟩

end Meat
