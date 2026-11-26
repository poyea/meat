import Meat.Open.Interference
import Meat.Channel.WiretapCK
import Meat.Open.Broadcast

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal

namespace Meat

namespace IC

section Book

variable {A B E : Type*} [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

open Classical in
private lemma sum_ite_off {S : Type*} [Fintype S] {n : ℕ} (f : Fin n → S → ℝ≥0∞) (i : Fin n)
    (o : ↥(({i}ᶜ : Finset (Fin n))) → S) (s : S) :
    ∑ y : Fin n → S, (if seqRestrict y {i}ᶜ = o ∧ y i = s then ∏ j, f j (y j) else 0) =
      (∏ j : ↥(({i}ᶜ : Finset (Fin n))), f j (o j)) * f i s := by
  classical
  set y₀ : Fin n → S := fun j => if h : j = i then s else o ⟨j, by simp [h]⟩
  have hy₀ : seqRestrict y₀ {i}ᶜ = o ∧ y₀ i = s := by
    refine ⟨funext fun t => ?_, by simp [y₀]⟩
    have ht : (t : Fin n) ≠ i :=
      fun h => (Finset.mem_compl.1 t.2) (Finset.mem_singleton.2 h)
    simp [seqRestrict, y₀, ht]
  rw [sum_eq_single y₀ (fun y _ hy => ?_) (by simp)]
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hy₀), ← prod_mul_prod_compl {i}, prod_singleton,
      mul_comm, ← prod_coe_sort]
    congr 1
    · refine prod_congr rfl fun t _ => ?_
      have ht : (t : Fin n) ≠ i :=
        fun h => (Finset.mem_compl.1 t.2) (Finset.mem_singleton.2 h)
      simp [y₀, ht]
    · simp [y₀]
  · refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
    rintro ⟨h1, h2⟩
    apply hy
    funext j
    by_cases hj : j = i
    · subst hj
      simp [y₀, h2]
    · have := congrFun h1 ⟨j, by simp [hj]⟩
      simp only [seqRestrict] at this
      simp [y₀, hj, this]

variable {k l n : ℕ} [NeZero k] [NeZero l]

private lemma bookMeasure_off (W : DMC A (B × E)) (C : Fin k × Fin l → Fin n → A) (i : Fin n)
    (u : Fin k × Fin l) (o : ↥(({i}ᶜ : Finset (Fin n))) → B × E) (s : B × E) :
    (Wiretap.bookMeasure W C).real {ω | (ω.1, seqRestrict ω.2 {i}ᶜ) = (u, o) ∧ ω.2 i = s} =
      (Wiretap.bookMeasure W C).real {ω | (ω.1, seqRestrict ω.2 {i}ᶜ) = (u, o)} *
        (W (C u i) s).toReal := by
  classical
  have hseq : ∀ y : Fin n → B × E, Interactive.seqProb W
      (fun (j : Fin n) (_ : Fin j → B × E) => C u j) y = ∏ j, W (C u j) (y j) := fun y => rfl
  have hs : ∑ s', W (C u i) s' = 1 := by
    have h := PMF.tsum_coe (W (C u i))
    rwa [tsum_fintype] at h
  have h1 : (Wiretap.bookMeasure W C) {ω | (ω.1, seqRestrict ω.2 {i}ᶜ) = (u, o) ∧ ω.2 i = s} =
      (Fintype.card (Fin k × Fin l) : ℝ≥0∞)⁻¹ *
        ((∏ j : ↥(({i}ᶜ : Finset (Fin n))), W (C u j) (o j)) * W (C u i) s) := by
    rw [Wiretap.bookMeasure, Interactive.codeMeasure_apply,
      sum_eq_single u (fun u' _ hu => by simp [Prod.ext_iff, hu]) (by simp)]
    rw [← sum_ite_off (fun j => W (C u j)) i o s, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    by_cases h : seqRestrict y {i}ᶜ = o ∧ y i = s
    · have h' : (u, seqRestrict y {i}ᶜ) = (u, o) ∧ y i = s := ⟨by rw [h.1], h.2⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true h),
        hseq]
    · have h' : ¬((u, seqRestrict y {i}ᶜ) = (u, o) ∧ y i = s) := fun h'' =>
        h ⟨(Prod.ext_iff.1 h''.1).2, h''.2⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false h),
        mul_zero]
  have h2 : (Wiretap.bookMeasure W C) {ω | (ω.1, seqRestrict ω.2 {i}ᶜ) = (u, o)} =
      (Fintype.card (Fin k × Fin l) : ℝ≥0∞)⁻¹ *
        ∏ j : ↥(({i}ᶜ : Finset (Fin n))), W (C u j) (o j) := by
    rw [Wiretap.bookMeasure, Interactive.codeMeasure_apply,
      sum_eq_single u (fun u' _ hu => by simp [Prod.ext_iff, hu]) (by simp)]
    have e : ∀ y : Fin n → B × E, (if (u, seqRestrict y {i}ᶜ) = (u, o) then
        (Fintype.card (Fin k × Fin l) : ℝ≥0∞)⁻¹ * Interactive.seqProb W
          (fun (j : Fin n) (_ : Fin j → B × E) => C u j) y else 0) =
        (Fintype.card (Fin k × Fin l) : ℝ≥0∞)⁻¹ * ∑ s', (if seqRestrict y {i}ᶜ = o ∧ y i = s'
          then ∏ j, W (C u j) (y j) else 0) := by
      intro y
      rw [sum_eq_single (y i) (fun s' _ hs' => by simp [Ne.symm hs']) (by simp)]
      by_cases h : seqRestrict y {i}ᶜ = o
      · have h' : (u, seqRestrict y {i}ᶜ) = (u, o) := by rw [h]
        rw [ite_eq_left_of_eq_true _ _ (eq_true h'),
          ite_eq_left_of_eq_true _ _ (eq_true ⟨h, rfl⟩), hseq]
      · have h' : ¬((u, seqRestrict y {i}ᶜ) = (u, o)) := fun h'' => h (Prod.ext_iff.1 h'').2
        rw [ite_eq_right_of_eq_false _ _ (eq_false h'),
          ite_eq_right_of_eq_false _ _ (eq_false fun h'' => h h''.1), mul_zero]
    rw [sum_congr rfl fun y _ => e y, ← mul_sum, sum_comm]
    congr 1
    rw [sum_congr rfl fun s' _ => by convert sum_ite_off (fun j => W (C u j)) i o s', ← mul_sum,
      hs, mul_one]
  rw [measureReal_def, measureReal_def, h1, h2, ← mul_assoc, ENNReal.toReal_mul]

end Book

section Kernel

variable {Ω T : Type*} [MeasurableSpace Ω] [Finite T] [MeasurableSpace T]
  [MeasurableSingletonClass T]

private lemma kernel_comp (μ : Measure Ω) [IsProbabilityMeasure μ] {T' S' : Type*}
    [MeasurableSpace S'] [MeasurableSingletonClass S'] {H : Ω → T} {Sv : Ω → S'}
    (hH : Measurable H) (hS : Measurable Sv) (F : T → T') (K : T' → PMF S')
    (hK : ∀ h s, μ.real {ω | H ω = h ∧ Sv ω = s} = μ.real {ω | H ω = h} * (K (F h) s).toReal)
    (t : T') (s : S') :
    μ.real {ω | F (H ω) = t ∧ Sv ω = s} = μ.real {ω | F (H ω) = t} * (K t s).toReal := by
  classical
  have := Fintype.ofFinite T
  rw [Interactive.measureReal_comp_eq_sum μ hH hS F t s]
  have h2 := Interactive.measureReal_comp_eq_sum μ hH (measurable_const (a := ())) F t ()
  have e1 : {ω | F (H ω) = t ∧ () = ()} = {ω | F (H ω) = t} := by ext; simp
  rw [e1] at h2
  simp only [and_true] at h2
  rw [h2, sum_mul]
  refine sum_congr rfl fun h hh => ?_
  rw [hK, (mem_filter.1 hh).2]

end Kernel

section Letter

variable {Ω T A B₁ B₂ : Type*} [MeasurableSpace Ω] [Fintype T] [MeasurableSpace T]
  [MeasurableSingletonClass T] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

omit [Fintype A] [Fintype B₁] [Fintype B₂] in
private lemma kernel_fst [Finite B₁] [Finite B₂] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {X : Ω → A} {Y : Ω → B₁ × B₂} (hX : Measurable X) (hY : Measurable Y) (U : DMC A (B₁ × B₂))
    (hK : ∀ x y, ν.real {ω | X ω = x ∧ Y ω = y} = ν.real {ω | X ω = x} * (U x y).toReal)
    (x : A) (b : B₁) :
    ν.real {ω | X ω = x ∧ (Y ω).1 = b} =
      ν.real {ω | X ω = x} * ((fun a => (U a).map Prod.fst) x b).toReal := by
  classical
  have := Fintype.ofFinite B₁
  have := Fintype.ofFinite B₂
  have h := Interactive.measureReal_comp_eq_sum ν hY hX Prod.fst b x
  have e : {ω | X ω = x ∧ (Y ω).1 = b} = {ω | (Y ω).1 = b ∧ X ω = x} := by
    ext ω
    simp [and_comm]
  rw [e, h]
  have e2 : ∀ y, ν.real {ω | Y ω = y ∧ X ω = x} = ν.real {ω | X ω = x ∧ Y ω = y} := fun y => by
    congr 1
    ext ω
    simp [and_comm]
  simp only [e2, hK, ← mul_sum]
  congr 1
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun y _ => by
    split_ifs <;> simp [PMF.apply_ne_top]]
  rw [sum_filter]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : y.1 = b
  · simp [hy]
  · simp [hy, Ne.symm hy]

omit [Fintype A] [Fintype B₁] [Fintype B₂] in
private lemma kernel_snd [Finite B₁] [Finite B₂] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {X : Ω → A} {Y : Ω → B₁ × B₂} (hX : Measurable X) (hY : Measurable Y) (U : DMC A (B₁ × B₂))
    (hK : ∀ x y, ν.real {ω | X ω = x ∧ Y ω = y} = ν.real {ω | X ω = x} * (U x y).toReal)
    (x : A) (b : B₂) :
    ν.real {ω | X ω = x ∧ (Y ω).2 = b} =
      ν.real {ω | X ω = x} * ((fun a => (U a).map Prod.snd) x b).toReal := by
  classical
  have := Fintype.ofFinite B₁
  have := Fintype.ofFinite B₂
  have h := Interactive.measureReal_comp_eq_sum ν hY hX Prod.snd b x
  have e : {ω | X ω = x ∧ (Y ω).2 = b} = {ω | (Y ω).2 = b ∧ X ω = x} := by
    ext ω
    simp [and_comm]
  rw [e, h]
  have e2 : ∀ y, ν.real {ω | Y ω = y ∧ X ω = x} = ν.real {ω | X ω = x ∧ Y ω = y} := fun y => by
    congr 1
    ext ω
    simp [and_comm]
  simp only [e2, hK, ← mul_sum]
  congr 1
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun y _ => by
    split_ifs <;> simp [PMF.apply_ne_top]]
  rw [sum_filter]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : y.2 = b
  · simp [hy]
  · simp [hy, Ne.symm hy]

omit [Fintype A] [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂]
  [MeasurableSpace B₂] [MeasurableSingletonClass B₂] in
private lemma map_eq_jointMeasure [Finite A] {B : Type*} [Finite B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (ν : Measure Ω) [IsProbabilityMeasure ν] {X : Ω → A}
    {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y) (K : DMC A B)
    (hK : ∀ x y, ν.real {ω | X ω = x ∧ Y ω = y} = ν.real {ω | X ω = x} * (K x y).toReal) :
    ∃ p : PMF A, ν.map (fun ω => (X ω, Y ω)) = K.jointMeasure p := by
  classical
  have := Fintype.ofFinite A
  have := Fintype.ofFinite B
  have hs : ∑ x, ENNReal.ofReal (ν.real {ω | X ω = x}) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => measureReal_nonneg]
    have h := sum_measureReal_singleton_eq_one (ν.map X)
    simp only [map_measureReal_apply hX (measurableSet_singleton _)] at h
    rw [show ∑ x, ν.real {ω | X ω = x} = ∑ x, ν.real (X ⁻¹' {x}) from rfl, h,
      ENNReal.ofReal_one]
  refine ⟨PMF.ofFintype _ hs, Measure.ext_of_singleton fun t => ?_⟩
  rw [Measure.map_apply (hX.prodMk hY) (measurableSet_singleton _), DMC.jointMeasure_eq_toMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), DMC.jointPMF_apply,
    PMF.ofFintype_apply, ← ENNReal.ofReal_toReal (measure_ne_top ν _), ← measureReal_def,
    ← ENNReal.ofReal_toReal (PMF.apply_ne_top (K t.1) t.2),
    ← ENNReal.ofReal_mul measureReal_nonneg, ← hK]
  congr 2
  ext ω
  simp [Prod.ext_iff]

omit [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [Fintype B₂]
  [MeasurableSpace B₂] [MeasurableSingletonClass B₂] in
private lemma mutualInfo_eq_comp_of_kernel {B : Type*} [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (ν : Measure Ω) [IsProbabilityMeasure ν] {V : Ω → T}
    {Y : Ω → B} (hV : Measurable V) (hY : Measurable Y) (f : T → A) (K : DMC A B)
    (hK : ∀ v y, ν.real {ω | V ω = v ∧ Y ω = y} = ν.real {ω | V ω = v} * (K (f v) y).toReal) :
    I[V : Y ; ν] = I[f ∘ V : Y ; ν] := by
  rw [mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy, mutualInfo_comm,
    mutualInfo_eq_entropy_sub_condEntropy,
    Interactive.condEntropy_eq_comp_of_kernel ν hV hY f K hK]

private lemma mutualInfo_snd_le_of_kernel (ν : Measure Ω) [IsProbabilityMeasure ν] {V : Ω → T}
    {Y : Ω → B₁ × B₂} (hV : Measurable V) (hY : Measurable Y) (f : T → A) (U : DMC A (B₁ × B₂))
    (hK : ∀ v y, ν.real {ω | V ω = v ∧ Y ω = y} = ν.real {ω | V ω = v} * (U (f v) y).toReal)
    (hU : ∀ p : PMF A, I[fun ω : A × (B₁ × B₂) => ω.1 : fun ω => ω.2.2 ; U.jointMeasure p] ≤
      I[fun ω : A × (B₁ × B₂) => ω.1 : fun ω => ω.2.1 ; U.jointMeasure p]) :
    I[V : fun ω => (Y ω).2 ; ν] ≤ I[V : fun ω => (Y ω).1 ; ν] := by
  have hK₁ := kernel_fst ν hV hY (fun v => U (f v)) hK
  have hK₂ := kernel_snd ν hV hY (fun v => U (f v)) hK
  rw [mutualInfo_eq_comp_of_kernel ν hV (Y := fun ω => (Y ω).1) (measurable_fst.comp hY) f
      (fun a => (U a).map Prod.fst) hK₁,
    mutualInfo_eq_comp_of_kernel ν hV (Y := fun ω => (Y ω).2) (measurable_snd.comp hY) f
      (fun a => (U a).map Prod.snd) hK₂]
  have hX : ∀ x y, ν.real {ω | (f ∘ V) ω = x ∧ Y ω = y} =
      ν.real {ω | (f ∘ V) ω = x} * (U x y).toReal :=
    kernel_comp ν hV hY f U hK
  obtain ⟨p, hp⟩ := map_eq_jointMeasure ν ((measurable_of_finite f).comp hV) hY U hX
  have e₁ : I[f ∘ V : fun ω => (Y ω).1 ; ν] =
      I[fun ω : A × (B₁ × B₂) => ω.1 : fun ω => ω.2.1 ; U.jointMeasure p] := by
    rw [← hp, mutualInfo_map _ (((measurable_of_finite f).comp hV).prodMk hY) measurable_fst
      (measurable_of_finite _)]
    rfl
  have e₂ : I[f ∘ V : fun ω => (Y ω).2 ; ν] =
      I[fun ω : A × (B₁ × B₂) => ω.1 : fun ω => ω.2.2 ; U.jointMeasure p] := by
    rw [← hp, mutualInfo_map _ (((measurable_of_finite f).comp hV).prodMk hY) measurable_fst
      (measurable_of_finite _)]
    rfl
  rw [e₁, e₂]
  exact hU p

private lemma condMutualInfo_snd_le_of_kernel {T' : Type*} [Fintype T'] [MeasurableSpace T']
    [MeasurableSingletonClass T'] (μ : Measure Ω) [IsProbabilityMeasure μ] {G : Ω → T'}
    {V : Ω → T} {Y : Ω → B₁ × B₂} (hG : Measurable G) (hV : Measurable V) (hY : Measurable Y)
    (f : T → A) (U : T' → DMC A (B₁ × B₂))
    (hK : ∀ g v y, μ.real {ω | (G ω, V ω) = (g, v) ∧ Y ω = y} =
      μ.real {ω | (G ω, V ω) = (g, v)} * (U g (f v) y).toReal)
    (hU : ∀ g, ∀ p : PMF A,
      I[fun ω : A × (B₁ × B₂) => ω.1 : fun ω => ω.2.2 ; (U g).jointMeasure p] ≤
        I[fun ω : A × (B₁ × B₂) => ω.1 : fun ω => ω.2.1 ; (U g).jointMeasure p]) :
    I[V : fun ω => (Y ω).2 | G ; μ] ≤ I[V : fun ω => (Y ω).1 | G ; μ] := by
  rw [Wiretap.condMutualInfo_eq_sum_cond μ hV (Y := fun ω => (Y ω).2) (measurable_snd.comp hY) hG,
    Wiretap.condMutualInfo_eq_sum_cond μ hV (Y := fun ω => (Y ω).1) (measurable_fst.comp hY) hG]
  refine sum_le_sum fun g _ => ?_
  rcases eq_or_ne (μ.real (G ⁻¹' {g})) 0 with h0 | h0
  · simp [h0]
  refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
  have hne : μ (G ⁻¹' {g}) ≠ 0 := fun h => h0 (by rw [measureReal_def, h]; rfl)
  have := cond_isProbabilityMeasure (μ := μ) hne
  refine mutualInfo_snd_le_of_kernel (μ[|G ⁻¹' {g}]) hV hY f (U g) (fun v y => ?_) (hU g)
  rw [measureReal_def, measureReal_def, cond_apply (hG (measurableSet_singleton g)),
    cond_apply (hG (measurableSet_singleton g)), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ← measureReal_def, ← measureReal_def]
  have e1 : G ⁻¹' {g} ∩ {ω | V ω = v ∧ Y ω = y} = {ω | (G ω, V ω) = (g, v) ∧ Y ω = y} := by
    ext ω
    simp [Prod.ext_iff, and_assoc]
  have e2 : G ⁻¹' {g} ∩ {ω | V ω = v} = {ω | (G ω, V ω) = (g, v)} := by
    ext ω
    simp [Prod.ext_iff]
  rw [e1, e2, hK]
  ring

end Letter

section Pair

variable {Ω P Q R S : Type*} [MeasurableSpace Ω] [Fintype P] [MeasurableSpace P]
  [MeasurableSingletonClass P] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
  [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S] (μ : Measure Ω)

private lemma condMutualInfo_pair {X : Ω → P} {Y : Ω → Q} {Z : Ω → R} {V : Ω → S} :
    I[X : fun ω => (Y ω, V ω) | Z ; μ] =
      I[X : Y | Z ; μ] + I[X : V | fun ω => (Y ω, Z ω) ; μ] := by
  have e1 : H[fun ω => (X ω, (Y ω, Z ω)) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    (entropy_assoc μ).symm
  have e2 : H[fun ω => (V ω, (Y ω, Z ω)) ; μ] = H[fun ω => ((Y ω, V ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((Y ω, V ω), Z ω))
      (f := fun p => (p.1.2, (p.1.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.2.1 h.1) h.2.2
  have e3 : H[fun ω => ((X ω, V ω), (Y ω, Z ω)) ; μ]
      = H[fun ω => ((X ω, (Y ω, V ω)), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, (Y ω, V ω)), Z ω))
      (f := fun p => ((p.1.1, p.1.2.2), (p.1.2.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 (Prod.ext h.2.1 h.1.2)) h.2.2
  simp only [condMutualInfo_def, condEntropy_def]
  rw [e1, e2, e3]
  ring

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] in
private lemma mutualInfo_pair {X : Ω → P} {Y : Ω → Q} {V : Ω → S} :
    I[X : fun ω => (Y ω, V ω) ; μ] = I[X : Y ; μ] + I[X : V | Y ; μ] := by
  have h := mutualInfo_pair_eq_add_condMutualInfo μ (X := X) (Y := V) (Z := Y)
  have hs := mutualInfo_comp_right_of_injective μ (X := X) (Y := fun ω => (V ω, Y ω))
    Prod.swap_injective
  rw [← h, ← hs]
  rfl

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] in
private lemma condMutualInfo_const [IsProbabilityMeasure μ] (X : Ω → P) (Y : Ω → Q) (c : S) :
    I[X : Y | fun _ => c ; μ] = I[X : Y ; μ] := by
  have h0 : H[fun _ : Ω => c ; μ] = 0 := by
    classical
    rw [entropy_def, Measure.map_const, measure_univ, one_smul]
    refine sum_eq_zero fun s _ => ?_
    by_cases hs : s = c
    · subst hs
      simp
    · simp [measureReal_def, hs]
  have hX : H[fun ω => (X ω, c) ; μ] = H[X ; μ] :=
    entropy_comp_of_injective μ (X := X) (f := fun s => (s, c)) fun _ _ h => congrArg Prod.fst h
  have hY : H[fun ω => (Y ω, c) ; μ] = H[Y ; μ] :=
    entropy_comp_of_injective μ (X := Y) (f := fun s => (s, c)) fun _ _ h => congrArg Prod.fst h
  have hXY : H[fun ω => ((X ω, Y ω), c) ; μ] = H[fun ω => (X ω, Y ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Y ω)) (f := fun s => (s, c))
      fun _ _ h => congrArg Prod.fst h
  simp only [condMutualInfo_def, condEntropy_def, mutualInfo_def]
  rw [hX, hY, hXY, h0]
  ring

end Pair

section Strong

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

omit [Fintype A₁] [MeasurableSingletonClass A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂] in
private lemma jointMeasure_out₁_pure [Finite A₂] [Finite B₁] [Finite B₂]
    (W : DMC (A₁ × A₂) (B₁ × B₂)) (x₁ : A₁) (p : PMF A₂) :
    MAC.jointMeasure (out₁ W) (PMF.pure x₁) p =
      (DMC.jointMeasure (fun a => W (x₁, a)) p).map fun ω => (x₁, ω.1, ω.2.1) := by
  rw [DMC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _),
    MAC.jointMeasure_eq_toMeasure]
  congr 1
  simp only [MAC.jointPMF, DMC.jointPMF, PMF.pure_bind, PMF.map_bind, PMF.map_comp, out₁]
  rfl

omit [Fintype A₁] [MeasurableSingletonClass A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂] in
private lemma jointMeasure_out₂_pure [Finite A₂] [Finite B₁] [Finite B₂]
    (W : DMC (A₁ × A₂) (B₁ × B₂)) (x₁ : A₁) (p : PMF A₂) :
    MAC.jointMeasure (out₂ W) (PMF.pure x₁) p =
      (DMC.jointMeasure (fun a => W (x₁, a)) p).map fun ω => (x₁, ω.1, ω.2.2) := by
  rw [DMC.jointMeasure_eq_toMeasure, PMF.toMeasure_map _ _ (measurable_of_finite _),
    MAC.jointMeasure_eq_toMeasure]
  congr 1
  simp only [MAC.jointPMF, DMC.jointPMF, PMF.pure_bind, PMF.map_bind, PMF.map_comp, out₂]
  rfl

private lemma moreCapable_of_strong {W : DMC (A₁ × A₂) (B₁ × B₂)} (hW : StrongInterference W)
    (x₁ : A₁) (p : PMF A₂) :
    I[fun ω : A₂ × (B₁ × B₂) => ω.1 : fun ω => ω.2.2 ; DMC.jointMeasure (fun a => W (x₁, a)) p] ≤
      I[fun ω : A₂ × (B₁ × B₂) => ω.1 : fun ω => ω.2.1 ;
        DMC.jointMeasure (fun a => W (x₁, a)) p] := by
  have h := (hW (PMF.pure x₁) p).2
  rw [jointMeasure_out₁_pure, jointMeasure_out₂_pure,
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)] at h
  rwa [Function.comp_def, Function.comp_def, Function.comp_def, condMutualInfo_const,
    Function.comp_def, Function.comp_def, Function.comp_def, condMutualInfo_const] at h

private lemma condMutualInfo_le_of_strong {W : DMC (A₁ × A₂) (B₁ × B₂)}
    (hW : StrongInterference W) {k₁ k₂ n : ℕ} [NeZero k₁] [NeZero k₂]
    (e₁ : Fin k₁ → Fin n → A₁) (e₂ : Fin k₂ → Fin n → A₂) :
    I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω j => (ω.2 j).2 |
        fun ω => ω.1.1 ; Wiretap.bookMeasure W fun u i => (e₁ u.1 i, e₂ u.2 i)] ≤
      I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω j => (ω.2 j).1 |
        fun ω => ω.1.1 ; Wiretap.bookMeasure W fun u i => (e₁ u.1 i, e₂ u.2 i)] := by
  classical
  set C : Fin k₁ × Fin k₂ → Fin n → A₁ × A₂ := fun u i => (e₁ u.1 i, e₂ u.2 i)
  set μ := Wiretap.bookMeasure W C
  set Y₁ : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) → Fin n → B₁ := fun ω j => (ω.2 j).1
  set Y₂ : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) → Fin n → B₂ := fun ω j => (ω.2 j).2
  set S := fun (i : Fin n) (ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂)) =>
    (seqRestrict (Y₁ ω) (Iio i), seqRestrict (Y₂ ω) (Ioi i))
  have T1 : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1 : Y₁ ; μ] -
      I[fun ω => ω.1 : Y₂ ; μ] = ∑ i, (I[fun ω => ω.1 : fun ω => Y₁ ω i | S i ; μ] -
        I[fun ω => ω.1 : fun ω => Y₂ ω i | S i ; μ]) :=
    Wiretap.mutualInfo_sub_eq_sum μ (fun ω => ω.1) Y₁ Y₂
  have T2 : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1 : Y₁ ; μ] -
      I[fun ω => ω.1.1 : Y₂ ; μ] = ∑ i, (I[fun ω => ω.1.1 : fun ω => Y₁ ω i | S i ; μ] -
        I[fun ω => ω.1.1 : fun ω => Y₂ ω i | S i ; μ]) :=
    Wiretap.mutualInfo_sub_eq_sum μ (fun ω => ω.1.1) Y₁ Y₂
  have P1 : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1 : Y₁ ; μ] =
      I[fun ω => ω.1.1 : Y₁ ; μ] + I[fun ω => ω.1.2 : Y₁ | fun ω => ω.1.1 ; μ] := by
    have h := mutualInfo_pair μ (X := Y₁) (Y := fun ω => ω.1.1) (V := fun ω => ω.1.2)
    have c1 := mutualInfo_comm μ (X := Y₁) (Y := fun ω => (ω.1.1, ω.1.2))
    have c2 := mutualInfo_comm μ (X := Y₁) (Y := fun ω => ω.1.1)
    have c3 := condMutualInfo_comm μ (X := Y₁) (Y := fun ω => ω.1.2) (Z := fun ω => ω.1.1)
    have e : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1 : Y₁ ; μ] =
        I[fun ω => (ω.1.1, ω.1.2) : Y₁ ; μ] := rfl
    linarith
  have P2 : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1 : Y₂ ; μ] =
      I[fun ω => ω.1.1 : Y₂ ; μ] + I[fun ω => ω.1.2 : Y₂ | fun ω => ω.1.1 ; μ] := by
    have h := mutualInfo_pair μ (X := Y₂) (Y := fun ω => ω.1.1) (V := fun ω => ω.1.2)
    have c1 := mutualInfo_comm μ (X := Y₂) (Y := fun ω => (ω.1.1, ω.1.2))
    have c2 := mutualInfo_comm μ (X := Y₂) (Y := fun ω => ω.1.1)
    have c3 := condMutualInfo_comm μ (X := Y₂) (Y := fun ω => ω.1.2) (Z := fun ω => ω.1.1)
    have e : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1 : Y₂ ; μ] =
        I[fun ω => (ω.1.1, ω.1.2) : Y₂ ; μ] := rfl
    linarith
  have key : ∀ i : Fin n,
      (I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1 : fun ω => Y₁ ω i | S i ; μ] -
        I[fun ω => ω.1 : fun ω => Y₂ ω i | S i ; μ]) -
      (I[fun ω => ω.1.1 : fun ω => Y₁ ω i | S i ; μ] -
        I[fun ω => ω.1.1 : fun ω => Y₂ ω i | S i ; μ]) =
      I[fun ω => ω.1.2 : fun ω => Y₁ ω i | fun ω => (ω.1.1, S i ω) ; μ] -
        I[fun ω => ω.1.2 : fun ω => Y₂ ω i | fun ω => (ω.1.1, S i ω) ; μ] := by
    intro i
    have q1 := condMutualInfo_pair μ (X := fun ω => Y₁ ω i) (Y := fun ω => ω.1.1)
      (V := fun ω => ω.1.2) (Z := S i)
    have q2 := condMutualInfo_pair μ (X := fun ω => Y₂ ω i) (Y := fun ω => ω.1.1)
      (V := fun ω => ω.1.2) (Z := S i)
    rw [condMutualInfo_comm, condMutualInfo_comm (X := fun ω => Y₁ ω i) (Y := fun ω => ω.1.1),
      condMutualInfo_comm (X := fun ω => Y₁ ω i) (Y := fun ω => ω.1.2)] at q1
    rw [condMutualInfo_comm, condMutualInfo_comm (X := fun ω => Y₂ ω i) (Y := fun ω => ω.1.1),
      condMutualInfo_comm (X := fun ω => Y₂ ω i) (Y := fun ω => ω.1.2)] at q2
    have r1 : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1 : fun ω => Y₁ ω i | S i ; μ] =
        I[fun ω => (ω.1.1, ω.1.2) : fun ω => Y₁ ω i | S i ; μ] := rfl
    have r2 : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1 : fun ω => Y₂ ω i | S i ; μ] =
        I[fun ω => (ω.1.1, ω.1.2) : fun ω => Y₂ ω i | S i ; μ] := rfl
    linarith
  have hle : ∀ i : Fin n,
      I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω => Y₂ ω i |
          fun ω => (ω.1.1, S i ω) ; μ] ≤
        I[fun ω => ω.1.2 : fun ω => Y₁ ω i | fun ω => (ω.1.1, S i ω) ; μ] := by
    intro i
    set Gf : (↥(({i}ᶜ : Finset (Fin n))) → B₁ × B₂) → (↥(Iio i) → B₁) × (↥(Ioi i) → B₂) :=
      fun o => (fun j => (o ⟨j.1, by simpa using ne_of_lt (mem_Iio.1 j.2)⟩).1,
        fun j => (o ⟨j.1, by simpa using ne_of_gt (mem_Ioi.1 j.2)⟩).2)
    set F : (Fin k₁ × Fin k₂) × (↥(({i}ᶜ : Finset (Fin n))) → B₁ × B₂) →
        (Fin k₁ × ((↥(Iio i) → B₁) × (↥(Ioi i) → B₂))) × Fin k₂ :=
      fun h => ((h.1.1, Gf h.2), h.1.2)
    have hK := kernel_comp μ
      (H := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => (ω.1, seqRestrict ω.2 {i}ᶜ))
      (Sv := fun ω => ω.2 i) (measurable_of_finite _) (measurable_of_finite _) F
      (fun t => W (e₁ t.1.1 i, e₂ t.2 i)) fun h s => bookMeasure_off W C i h.1 h.2 s
    exact condMutualInfo_snd_le_of_kernel μ (G := fun ω => (ω.1.1, S i ω))
      (V := fun ω => ω.1.2) (Y := fun ω => ω.2 i) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _) (fun v => e₂ v i)
      (fun g a => W (e₁ g.1 i, a)) (fun g v y => hK (g, v) y)
      fun g p => moreCapable_of_strong hW (e₁ g.1 i) p
  have hsum : 0 ≤ ∑ i : Fin n,
      (I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω => Y₁ ω i |
          fun ω => (ω.1.1, S i ω) ; μ] -
        I[fun ω => ω.1.2 : fun ω => Y₂ ω i | fun ω => (ω.1.1, S i ω) ; μ]) :=
    sum_nonneg fun i _ => sub_nonneg.2 (hle i)
  rw [← sum_congr rfl fun i _ => key i, sum_sub_distrib, ← T1, ← T2] at hsum
  linarith

end Strong

section Code

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]
  {k₁ k₂ n : ℕ} [NeZero k₁] [NeZero k₂]

private def rx₁ (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) :
    MACCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ n :=
  ⟨c.enc₁, c.enc₂, fun _ => (0, 0)⟩

private noncomputable def icMeasure (W : DMC (A₁ × A₂) (B₁ × B₂))
    (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) :
    Measure ((Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂)) :=
  Wiretap.bookMeasure W fun u i => (c.enc₁ u.1 i, c.enc₂ u.2 i)

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B₁]
  [MeasurableSingletonClass B₂] in
private lemma isProbabilityMeasure_icMeasure (W : DMC (A₁ × A₂) (B₁ × B₂))
    (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) : IsProbabilityMeasure (icMeasure W c) :=
  Wiretap.isProbabilityMeasure_bookMeasure W _

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] in
private lemma map_icMeasure (W : DMC (A₁ × A₂) (B₁ × B₂))
    (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) :
    (icMeasure W c).map (fun ω => (ω.1, fun i => (ω.2 i).1)) =
      (rx₁ c).toBlockCode.codeMeasure (out₁ W) := by
  classical
  refine Measure.ext_of_singleton fun t => ?_
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have e : (fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => (ω.1, fun i => (ω.2 i).1)) ⁻¹' {t} =
      {ω | ω.1 = t.1 ∧ (fun i => (ω.2 i).1) = t.2} := by
    ext ω
    simp [Prod.ext_iff]
  rw [e, icMeasure, Wiretap.bookMeasure, Interactive.codeMeasure_apply,
    sum_eq_single t.1 (fun m _ hm => by simp [hm]) (by simp), BlockCode.codeMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.ofFintype_apply]
  simp only [true_and]
  have h := sum_mul_blockProb_out₁ W (fun i => (c.enc₁ t.1.1 i, c.enc₂ t.1.2 i))
    (fun y₁ => if y₁ = t.2 then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true] at h
  have e2 : ∀ y : Fin n → B₁ × B₂, (if (fun i => (y i).1) = t.2 then
      (Fintype.card (Fin k₁ × Fin k₂) : ℝ≥0∞)⁻¹ * Interactive.seqProb W
        (fun (i : Fin n) (_ : Fin i → B₁ × B₂) => (c.enc₁ t.1.1 i, c.enc₂ t.1.2 i)) y else 0) =
      (Fintype.card (Fin k₁ × Fin k₂) : ℝ≥0∞)⁻¹ * (if (fun i => (y i).1) = t.2 then
        DMC.blockProb W (fun i => (c.enc₁ t.1.1 i, c.enc₂ t.1.2 i)) y else 0) := fun y => by
    split_ifs <;> simp [Interactive.seqProb, DMC.blockProb]
  rw [sum_congr rfl fun y _ => e2 y, ← mul_sum, h]
  rfl

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] in
private lemma measureReal_dec_ne (W : DMC (A₁ × A₂) (B₁ × B₂))
    (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) :
    (icMeasure W c).real {ω | (c.dec₁ fun i => (ω.2 i).1, c.dec₂ fun i => (ω.2 i).2) ≠ ω.1} =
      (c.avgError W).toReal := by
  classical
  rw [measureReal_def, icMeasure, Wiretap.bookMeasure, Interactive.codeMeasure_apply,
    ICCode.avgError, ← Nat.cast_mul, ← Fintype.card_prod, div_eq_mul_inv, sum_mul]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [ICCode.errorProb, sum_mul]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : (c.dec₁ fun i => (y i).1, c.dec₂ fun i => (y i).2) = m
  · simp [h]
  · simp only [h, ne_eq, not_false_eq_true, ite_true, ite_false]
    rw [mul_comm]
    rfl

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] in
private lemma measureReal_dec₁_ne_le (W : DMC (A₁ × A₂) (B₁ × B₂))
    (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) :
    (icMeasure W c).real {ω | c.dec₁ (fun i => (ω.2 i).1) ≠ ω.1.1} ≤ (c.avgError W).toReal := by
  have := isProbabilityMeasure_icMeasure W c
  rw [← measureReal_dec_ne]
  exact measureReal_mono fun ω hω h => hω (congrArg Prod.fst h)

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] in
private lemma measureReal_dec₂_ne_le (W : DMC (A₁ × A₂) (B₁ × B₂))
    (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) :
    (icMeasure W c).real {ω | c.dec₂ (fun i => (ω.2 i).2) ≠ ω.1.2} ≤ (c.avgError W).toReal := by
  have := isProbabilityMeasure_icMeasure W c
  rw [← measureReal_dec_ne]
  exact measureReal_mono fun ω hω h => hω (congrArg Prod.snd h)

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] in
private lemma entropy_messages (W : DMC (A₁ × A₂) (B₁ × B₂))
    (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) :
    H[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1 ; icMeasure W c] = Real.log k₁ ∧
    H[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2 ; icMeasure W c] = Real.log k₂ ∧
    I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1 : fun ω => ω.1.2 ;
      icMeasure W c] = 0 := by
  have := isProbabilityMeasure_icMeasure W c
  have hM : H[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1 ; icMeasure W c] =
      Real.log k₁ + Real.log k₂ := by
    have h := (rx₁ c).toBlockCode.entropy_fst_codeMeasure (out₁ W)
    rw [← map_icMeasure, entropy_map _ (measurable_of_finite _) measurable_fst,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.2 (NeZero.ne k₁)) (Nat.cast_ne_zero.2 (NeZero.ne k₂))] at h
    exact h
  have h1 := entropy_le_log_card (icMeasure W c)
    (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1)
  have h2 := entropy_le_log_card (icMeasure W c)
    (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2)
  have h3 := entropy_pair_le_add (icMeasure W c)
    (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1) (Y := fun ω => ω.1.2)
    (measurable_of_finite _) (measurable_of_finite _)
  rw [Fintype.card_fin] at h1 h2
  have e : H[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => (ω.1.1, ω.1.2) ; icMeasure W c] =
      H[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1 ; icMeasure W c] := rfl
  refine ⟨by linarith, by linarith, ?_⟩
  rw [mutualInfo_def]
  linarith

omit [NeZero k₁] [NeZero k₂] in
private lemma condMutualInfo_le_sum (c : MACCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ n)
    [Nonempty (Fin k₁)] [Nonempty (Fin k₂)] (V : DMC (A₁ × A₂) B₁) :
    I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁) => ω.1.1 : Prod.snd | fun ω => ω.1.2 ;
        c.toBlockCode.codeMeasure V] ≤
      ∑ i, I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure V (c.inputLaw₁ i) (c.inputLaw₂ i)] := by
  set μ := c.toBlockCode.codeMeasure V
  have hN := c.toBlockCode.condEntropy_snd_fst_codeMeasure V
  have hS : H[Prod.snd | fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁) => ω.1.2 ; μ] ≤
      ∑ i, H[Prod.snd | fun x : (A₁ × A₂) × B₁ => x.1.2 ;
        V.jointMeasure (c.toBlockCode.inputLaw i)] := by
    refine (condEntropy_pi_le_sum μ (Y := Prod.snd) (fun i => (measurable_pi_apply i).comp
      measurable_snd) (measurable_snd.comp measurable_fst)).trans (sum_le_sum fun i _ => ?_)
    rw [← BlockCode.map_codeMeasure, condEntropy_map _ (measurable_of_finite _) (X := Prod.snd)
      (Y := fun x : (A₁ × A₂) × B₁ => x.1.2) measurable_snd (measurable_of_finite _)]
    exact condEntropy_le_condEntropy_comp (μ := μ) ((measurable_pi_apply i).comp measurable_snd)
      (measurable_snd.comp measurable_fst) (fun m₂ => c.enc₂ m₂ i)
  have hI : ∑ i, I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure V (c.inputLaw₁ i) (c.inputLaw₂ i)] =
      ∑ i, H[Prod.snd | fun x : (A₁ × A₂) × B₁ => x.1.2 ;
        V.jointMeasure (c.toBlockCode.inputLaw i)] -
      ∑ i, H[Prod.snd | Prod.fst ; V.jointMeasure (c.toBlockCode.inputLaw i)] := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by
      rw [MACCode.toBlockCode_inputLaw, MAC.condMutualInfo_eq_condEntropy_sub]
  have hE : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁) => ω.1.1 : Prod.snd |
      fun ω => ω.1.2 ; μ] = H[Prod.snd | fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁) => ω.1.2 ; μ] -
        H[Prod.snd | Prod.fst ; μ] :=
    condMutualInfo_eq_condEntropy_sub_condEntropy μ
  rw [hE, hI, hN]
  linarith

end Code

section Bounds

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]
  {k₁ k₂ n : ℕ} [NeZero k₁] [NeZero k₂]

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] in
private lemma fano₁ (W : DMC (A₁ × A₂) (B₁ × B₂)) (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) :
    I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1 : fun ω i => (ω.2 i).1 ;
      icMeasure W c] ≥ (1 - (c.avgError W).toReal) * Real.log k₁ - Real.log 2 := by
  have := isProbabilityMeasure_icMeasure W c
  obtain ⟨hH, -, -⟩ := entropy_messages W c
  have hF := condEntropy_le_log_two_add_mul_log_card (μ := icMeasure W c)
    (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1)
    (Y := fun ω i => (ω.2 i).1) (measurable_of_finite _) (measurable_of_finite _) c.dec₁
  have hm := mul_le_mul_of_nonneg_right (measureReal_dec₁_ne_le W c)
    (Real.log_natCast_nonneg k₁)
  rw [Fintype.card_fin] at hF
  have hI := mutualInfo_eq_entropy_sub_condEntropy
    (fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1) (fun ω i => (ω.2 i).1)
    (icMeasure W c)
  have e : (1 - (c.avgError W).toReal) * Real.log k₁ =
      Real.log k₁ - (c.avgError W).toReal * Real.log k₁ := by ring
  linarith

omit [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype A₂]
  [MeasurableSpace A₂] [MeasurableSingletonClass A₂] in
private lemma fano₂ (W : DMC (A₁ × A₂) (B₁ × B₂)) (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) :
    I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω i => (ω.2 i).2 ;
      icMeasure W c] ≥ (1 - (c.avgError W).toReal) * Real.log k₂ - Real.log 2 := by
  have := isProbabilityMeasure_icMeasure W c
  obtain ⟨-, hH, -⟩ := entropy_messages W c
  have hF := condEntropy_le_log_two_add_mul_log_card (μ := icMeasure W c)
    (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2)
    (Y := fun ω i => (ω.2 i).2) (measurable_of_finite _) (measurable_of_finite _) c.dec₂
  have hm := mul_le_mul_of_nonneg_right (measureReal_dec₂_ne_le W c)
    (Real.log_natCast_nonneg k₂)
  rw [Fintype.card_fin] at hF
  have hI := mutualInfo_eq_entropy_sub_condEntropy
    (fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2) (fun ω i => (ω.2 i).2)
    (icMeasure W c)
  have e : (1 - (c.avgError W).toReal) * Real.log k₂ =
      Real.log k₂ - (c.avgError W).toReal * Real.log k₂ := by ring
  linarith

private lemma one_sub_mul_log_le₁ (W : DMC (A₁ × A₂) (B₁ × B₂))
    (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) :
    (1 - (c.avgError W).toReal) * Real.log k₁ ≤
      ∑ i, I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure (out₁ W) ((rx₁ c).inputLaw₁ i) ((rx₁ c).inputLaw₂ i)] +
        Real.log 2 := by
  set μ := icMeasure W c
  have := isProbabilityMeasure_icMeasure W c
  obtain ⟨-, -, h0⟩ := entropy_messages W c
  have hF := fano₁ W c
  have hC := mutualInfo_add_condMutualInfo_comm (μ := μ)
    (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1) (Y := fun ω => ω.1.2)
    (Z := fun ω i => (ω.2 i).1)
  have hN := condMutualInfo_nonneg μ (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1)
    (Y := fun ω => ω.1.2) (Z := fun ω i => (ω.2 i).1) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)
  have hT : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1 : fun ω i => (ω.2 i).1 |
      fun ω => ω.1.2 ; μ] = I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁) => ω.1.1 : Prod.snd |
        fun ω => ω.1.2 ; (rx₁ c).toBlockCode.codeMeasure (out₁ W)] := by
    rw [← map_icMeasure, condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  have hL := condMutualInfo_le_sum (rx₁ c) (out₁ W)
  linarith

private lemma one_sub_mul_log_le_sum {W : DMC (A₁ × A₂) (B₁ × B₂)} (hW : StrongInterference W)
    (c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n) :
    (1 - (c.avgError W).toReal) * (Real.log k₁ + Real.log k₂) ≤
      ∑ i, I[fun ω : A₁ × A₂ × B₁ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
        MAC.jointMeasure (out₁ W) ((rx₁ c).inputLaw₁ i) ((rx₁ c).inputLaw₂ i)] +
        2 * Real.log 2 := by
  set μ := icMeasure W c
  have := isProbabilityMeasure_icMeasure W c
  obtain ⟨-, -, h0⟩ := entropy_messages W c
  have hF₁ := fano₁ W c
  have hF₂ := fano₂ W c
  have hC := mutualInfo_add_condMutualInfo_comm (μ := μ)
    (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2) (Y := fun ω => ω.1.1)
    (Z := fun ω i => (ω.2 i).2)
  have hN := condMutualInfo_nonneg μ (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2)
    (Y := fun ω => ω.1.1) (Z := fun ω i => (ω.2 i).2) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _)
  have h0' := mutualInfo_comm μ (X := fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.1)
    (Y := fun ω => ω.1.2)
  have hS : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2 : fun ω j => (ω.2 j).2 |
      fun ω => ω.1.1 ; μ] ≤ I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => ω.1.2 :
        fun ω j => (ω.2 j).1 | fun ω => ω.1.1 ; μ] :=
    condMutualInfo_le_of_strong hW c.enc₁ c.enc₂
  have hP := mutualInfo_pair μ (X := fun (ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂)) j =>
    (ω.2 j).1) (Y := fun ω => ω.1.1) (V := fun ω => ω.1.2)
  have c1 := mutualInfo_comm μ (X := fun (ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂)) j =>
    (ω.2 j).1) (Y := fun ω => (ω.1.1, ω.1.2))
  have c2 := mutualInfo_comm μ (X := fun (ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂)) j =>
    (ω.2 j).1) (Y := fun ω => ω.1.1)
  have c3 := condMutualInfo_comm μ (X := fun (ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂)) j =>
    (ω.2 j).1) (Y := fun ω => ω.1.2) (Z := fun ω => ω.1.1)
  have hT : I[fun ω : (Fin k₁ × Fin k₂) × (Fin n → B₁ × B₂) => (ω.1.1, ω.1.2) :
      fun ω i => (ω.2 i).1 ; μ] = I[Prod.fst : Prod.snd ;
        (rx₁ c).toBlockCode.codeMeasure (out₁ W)] := by
    rw [← map_icMeasure, mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
    rfl
  have hB := (rx₁ c).toBlockCode.mutualInfo_le_sum_inputMutualInfo (out₁ W)
  simp only [MACCode.toBlockCode_inputLaw, MAC.inputMutualInfo_inputPMF] at hB
  have e : (1 - (c.avgError W).toReal) * (Real.log k₁ + Real.log k₂) =
      (1 - (c.avgError W).toReal) * Real.log k₁ + (1 - (c.avgError W).toReal) * Real.log k₂ := by
    ring
  linarith

end Bounds

section Swap

variable {A₁ A₂ B₁ B₂ : Type*}

private noncomputable def swapChannel (W : DMC (A₁ × A₂) (B₁ × B₂)) : DMC (A₂ × A₁) (B₂ × B₁) :=
  fun a => (W a.swap).map Prod.swap

private def swapCode {M₁ M₂ : Type*} {n : ℕ} (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n) :
    ICCode M₂ M₁ A₂ A₁ B₂ B₁ n :=
  ⟨c.enc₂, c.enc₁, c.dec₂, c.dec₁⟩

private lemma out₁_swapChannel (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    out₁ (swapChannel W) = fun a => out₂ W a.swap := by
  funext a
  simp only [out₁, out₂, swapChannel, PMF.map_comp]
  rfl

private lemma out₂_swapChannel (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    out₂ (swapChannel W) = fun a => out₁ W a.swap := by
  funext a
  simp only [out₁, out₂, swapChannel, PMF.map_comp]
  rfl

private lemma avgError_swapCode [Fintype B₁] [Fintype B₂] {M₁ M₂ : Type*} [Fintype M₁]
    [Fintype M₂] [DecidableEq M₁] [DecidableEq M₂] {n : ℕ} (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n)
    (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    (swapCode c).avgError (swapChannel W) = c.avgError W := by
  rw [ICCode.avgError, ICCode.avgError, mul_comm (Fintype.card M₂ : ℝ≥0∞),
    ← (Equiv.prodComm M₁ M₂).sum_comp]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [ICCode.errorProb, ICCode.errorProb,
    ← (Equiv.arrowCongr (Equiv.refl (Fin n)) (Equiv.prodComm B₁ B₂)).sum_comp]
  refine sum_congr rfl fun y _ => ?_
  have hb : DMC.blockProb (swapChannel W)
      (fun i => ((swapCode c).enc₁ ((Equiv.prodComm M₁ M₂) m).1 i,
        (swapCode c).enc₂ ((Equiv.prodComm M₁ M₂) m).2 i))
      ((Equiv.arrowCongr (Equiv.refl (Fin n)) (Equiv.prodComm B₁ B₂)) y) =
      DMC.blockProb W (fun i => (c.enc₁ m.1 i, c.enc₂ m.2 i)) y := by
    refine prod_congr rfl fun i _ => ?_
    exact map_apply_inj _ Prod.swap_injective (y i)
  rw [hb]
  have hd : ((swapCode c).dec₁ fun i =>
        ((Equiv.arrowCongr (Equiv.refl (Fin n)) (Equiv.prodComm B₁ B₂)) y i).1,
      (swapCode c).dec₂ fun i =>
        ((Equiv.arrowCongr (Equiv.refl (Fin n)) (Equiv.prodComm B₁ B₂)) y i).2) =
        (Equiv.prodComm M₁ M₂) m ↔
      (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) = m := by
    simp only [swapCode, Equiv.arrowCongr_apply, Function.comp_apply,
      Equiv.prodComm_apply, Prod.ext_iff, Prod.swap]
    tauto
  by_cases h : (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) = m
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hd.2 h)), ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (hd.1 h')),
      ite_eq_right_of_eq_false _ _ (eq_false h)]

variable [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

private lemma condMutualInfo_swap₂ {B : Type*} [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (V : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₂ × A₁ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
        MAC.jointMeasure (fun a => V a.swap) p₂ p₁] =
      I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure V p₁ p₂] := by
  have h := MAC.condMutualInfo_swap (fun a : A₂ × A₁ => V a.swap) p₂ p₁
  simp only [Prod.swap_swap] at h
  exact h.symm

private lemma mutualInfo_swap {B : Type*} [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (V : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    I[fun ω : A₂ × A₁ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
        MAC.jointMeasure (fun a => V a.swap) p₂ p₁] =
      I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ; MAC.jointMeasure V p₁ p₂] := by
  have h : I[fun ω : A₁ × A₂ × B => ω.2.2 : fun ω => (ω.2.1, ω.1) ; MAC.jointMeasure V p₁ p₂] =
      I[fun ω : A₁ × A₂ × B => ω.2.2 : fun ω => (ω.1, ω.2.1) ; MAC.jointMeasure V p₁ p₂] :=
    mutualInfo_comp_right_of_injective _ (X := fun ω : A₁ × A₂ × B => ω.2.2)
      (Y := fun ω => (ω.1, ω.2.1)) (f := Prod.swap) Prod.swap_injective
  have e : I[fun ω : A₂ × A₁ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
      MAC.jointMeasure (fun a => V a.swap) p₂ p₁] =
      I[fun ω : A₁ × A₂ × B => (ω.2.1, ω.1) : fun ω => ω.2.2 ; MAC.jointMeasure V p₁ p₂] := by
    rw [MAC.jointMeasure_eq_toMeasure, MAC.jointPMF_swap,
      ← PMF.toMeasure_map _ _ (measurable_of_finite _),
      mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  rw [e, mutualInfo_comm, h, mutualInfo_comm]

private lemma StrongInterference.swap {W : DMC (A₁ × A₂) (B₁ × B₂)} (hW : StrongInterference W) :
    StrongInterference (swapChannel W) := by
  intro p₂ p₁
  rw [out₁_swapChannel, out₂_swapChannel, MAC.condMutualInfo_swap (out₂ W) p₁ p₂,
    MAC.condMutualInfo_swap (out₁ W) p₁ p₂, condMutualInfo_swap₂ (out₁ W) p₁ p₂,
    condMutualInfo_swap₂ (out₂ W) p₁ p₂]
  exact ⟨(hW p₁ p₂).2, (hW p₁ p₂).1⟩

end Swap

section Region

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype A₁] [MeasurableSpace A₁] [Fintype A₂] [MeasurableSpace A₂]
  [Fintype B₁] [MeasurableSpace B₁] [Fintype B₂] [MeasurableSpace B₂]

noncomputable def strongTimeSharingRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) {k : ℕ} (pQ : PMF (Fin k))
    (p₁ : Fin k → PMF A₁) (p₂ : Fin k → PMF A₂) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧
    R.1 ≤ ∑ q, (pQ q).toReal * I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 |
      fun ω => ω.2.1 ; MAC.jointMeasure (out₁ W) (p₁ q) (p₂ q)] ∧
    R.2 ≤ ∑ q, (pQ q).toReal * I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 |
      fun ω => ω.1 ; MAC.jointMeasure (out₂ W) (p₁ q) (p₂ q)] ∧
    R.1 + R.2 ≤ ∑ q, (pQ q).toReal * I[fun ω : A₁ × A₂ × B₁ => (ω.1, ω.2.1) :
      fun ω => ω.2.2 ; MAC.jointMeasure (out₁ W) (p₁ q) (p₂ q)] ∧
    R.1 + R.2 ≤ ∑ q, (pQ q).toReal * I[fun ω : A₁ × A₂ × B₂ => (ω.1, ω.2.1) :
      fun ω => ω.2.2 ; MAC.jointMeasure (out₂ W) (p₁ q) (p₂ q)]}

noncomputable def strongCapacityRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) : Set (ℝ × ℝ) :=
  closure (⋃ (k : ℕ) (pQ : PMF (Fin k)) (p₁ : Fin k → PMF A₁) (p₂ : Fin k → PMF A₂),
    strongTimeSharingRegion W pQ p₁ p₂)

end Region

section Converse

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype B₂] [MeasurableSpace B₂] [MeasurableSingletonClass B₂]

private noncomputable def unifPMF (n : ℕ) [NeZero n] : PMF (Fin n) :=
  PMF.ofFintype (fun _ => (Fintype.card (Fin n) : ℝ≥0∞)⁻¹) (sum_inv_card (Fin n))

private lemma sum_unifPMF_mul {n : ℕ} [NeZero n] (a : Fin n → ℝ) :
    ∑ q, (unifPMF n q).toReal * a q = (∑ q, a q) / n := by
  simp only [unifPMF, PMF.ofFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← mul_sum]
  ring

private lemma rate_le {n R ε l L S t : ℝ} (hn : 0 < n) (hR : 0 ≤ R) (hl : l ≤ ε)
    (hε : ε ≤ 1 / 2) (ht : 0 ≤ t) (hL : n * R ≤ L) (hB : (1 - l) * L ≤ S + t) :
    n * ((1 - ε) * R - 2 * t / n) ≤ S := by
  have e : n * ((1 - ε) * R - 2 * t / n) = (1 - ε) * (n * R) - 2 * t := by
    field_simp
  have h1 : (1 - ε) * (n * R) ≤ (1 - l) * L :=
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hL (by linarith))
  linarith

private lemma clamp {N x y SA SB SC SD : ℝ} (ha : 0 ≤ SA) (hb : 0 ≤ SB) (hac : SA ≤ SC)
    (had : SA ≤ SD) (hbc : SB ≤ SC) (hbd : SB ≤ SD) (hx : N * x ≤ SA) (hy : N * y ≤ SB)
    (hxy : N * (x + y) ≤ SC) (hxy' : N * (x + y) ≤ SD) :
    N * max x 0 ≤ SA ∧ N * max y 0 ≤ SB ∧ N * (max x 0 + max y 0) ≤ SC ∧
      N * (max x 0 + max y 0) ≤ SD := by
  rcases le_total x 0 with h | h <;> rcases le_total y 0 with h' | h' <;>
    simp only [max_eq_right, max_eq_left, h, h', mul_zero, zero_add, add_zero] <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma dist_max_le {r ε l : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε) (hl : 0 ≤ l) :
    dist r (max ((1 - ε) * r - l) 0) ≤ ε * r + l := by
  rw [Real.dist_eq]
  rcases le_total ((1 - ε) * r - l) 0 with h | h
  · rw [max_eq_right h, sub_zero, abs_of_nonneg hr]
    linarith
  · rw [max_eq_left h, abs_of_nonneg (by nlinarith)]
    linarith

theorem achievableRegion_subset_strongCapacityRegion {W : DMC (A₁ × A₂) (B₁ × B₂)}
    (hW : StrongInterference W) : achievableRegion W ⊆ strongCapacityRegion W := by
  classical
  rintro R ⟨hR1, hR2, hA⟩
  rw [strongCapacityRegion, Metric.mem_closure_iff]
  intro η hη
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ε * (R.1 + R.2 + 1) ≤ η / 2 := by
    refine ⟨min (1 / 2) (η / (2 * (R.1 + R.2 + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, ?_⟩
    calc min (1 / 2) (η / (2 * (R.1 + R.2 + 1))) * (R.1 + R.2 + 1)
        ≤ η / (2 * (R.1 + R.2 + 1)) * (R.1 + R.2 + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = η / 2 := by field_simp
  obtain ⟨N, hN⟩ := hA (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε0)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (4 * Real.log 2 / η)
  obtain ⟨n, hnN, hn0, hn1⟩ : ∃ n : ℕ, N ≤ n ∧ n₀ ≤ n ∧ 1 ≤ n :=
    ⟨max (max N n₀) 1, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogn : 2 * Real.log 2 / n < η / 2 := by
    have h1 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn0
    have h2 : 4 * Real.log 2 < η * n := by
      have := (div_lt_iff₀ hη).1 (hn₀.trans_le h1)
      linarith
    rw [div_lt_iff₀ hnpos]
    linarith
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hnN
  have hk₁0 : (0 : ℝ) < k₁ := (Real.exp_pos _).trans_le hk₁
  have hk₂0 : (0 : ℝ) < k₂ := (Real.exp_pos _).trans_le hk₂
  have : NeZero k₁ := ⟨Nat.cast_pos.1 hk₁0 |>.ne'⟩
  have : NeZero k₂ := ⟨Nat.cast_pos.1 hk₂0 |>.ne'⟩
  have : NeZero n := ⟨by omega⟩
  have hlam : (c.avgError W).toReal ≤ ε := ENNReal.toReal_le_of_le_ofReal hε0.le hc
  set L₁ : Fin n → PMF A₁ := fun i => (rx₁ c).inputLaw₁ i
  set L₂ : Fin n → PMF A₂ := fun i => (rx₁ c).inputLaw₂ i
  have B1 := one_sub_mul_log_le₁ W c
  have B2 := one_sub_mul_log_le₁ (swapChannel W) (swapCode c)
  have B3 := one_sub_mul_log_le_sum hW c
  have B4 := one_sub_mul_log_le_sum hW.swap (swapCode c)
  rw [avgError_swapCode, out₁_swapChannel] at B2 B4
  have e2 : ∀ i, I[fun ω : A₂ × A₁ × B₂ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
      MAC.jointMeasure (fun a => out₂ W a.swap) ((rx₁ (swapCode c)).inputLaw₁ i)
        ((rx₁ (swapCode c)).inputLaw₂ i)] =
      I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
        MAC.jointMeasure (out₂ W) (L₁ i) (L₂ i)] := fun i =>
    MAC.condMutualInfo_swap (out₂ W) (L₁ i) (L₂ i)
  have e4 : ∀ i, I[fun ω : A₂ × A₁ × B₂ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
      MAC.jointMeasure (fun a => out₂ W a.swap) ((rx₁ (swapCode c)).inputLaw₁ i)
        ((rx₁ (swapCode c)).inputLaw₂ i)] =
      I[fun ω : A₁ × A₂ × B₂ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
        MAC.jointMeasure (out₂ W) (L₁ i) (L₂ i)] := fun i =>
    mutualInfo_swap (out₂ W) (L₁ i) (L₂ i)
  simp only [e2] at B2
  simp only [e4] at B4
  set a : Fin n → ℝ := fun i => I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 |
    fun ω => ω.2.1 ; MAC.jointMeasure (out₁ W) (L₁ i) (L₂ i)]
  set b : Fin n → ℝ := fun i => I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 |
    fun ω => ω.1 ; MAC.jointMeasure (out₂ W) (L₁ i) (L₂ i)]
  set c₁ : Fin n → ℝ := fun i => I[fun ω : A₁ × A₂ × B₁ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
    MAC.jointMeasure (out₁ W) (L₁ i) (L₂ i)]
  set c₂ : Fin n → ℝ := fun i => I[fun ω : A₁ × A₂ × B₂ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
    MAC.jointMeasure (out₂ W) (L₁ i) (L₂ i)]
  have hl₁ : n * R.1 ≤ Real.log k₁ := (Real.le_log_iff_exp_le hk₁0).2 hk₁
  have hl₂ : n * R.2 ≤ Real.log k₂ := (Real.le_log_iff_exp_le hk₂0).2 hk₂
  have hx := rate_le hnpos hR1 hlam hε1 hlog2 hl₁ B1
  have hy := rate_le hnpos hR2 hlam hε1 hlog2 hl₂ B2
  have hs₁ := rate_le hnpos (add_nonneg hR1 hR2) hlam hε1 (by positivity) (by linarith) B3
  have hs₂ := rate_le hnpos (add_nonneg hR1 hR2) hlam hε1 (by positivity) (by linarith)
    (by linarith [B4] : (1 - (c.avgError W).toReal) * (Real.log k₁ + Real.log k₂) ≤
      ∑ i, c₂ i + 2 * Real.log 2)
  set x := (1 - ε) * R.1 - 2 * Real.log 2 / n
  set y := (1 - ε) * R.2 - 2 * Real.log 2 / n
  have hxy : x + y ≤ (1 - ε) * (R.1 + R.2) - 2 * (2 * Real.log 2) / n := by
    simp only [x, y]
    have : 0 ≤ 2 * Real.log 2 / n := by positivity
    ring_nf
    ring_nf at this
    linarith
  have hs₁' : n * (x + y) ≤ ∑ i, c₁ i :=
    (mul_le_mul_of_nonneg_left hxy hnpos.le).trans hs₁
  have hs₂' : n * (x + y) ≤ ∑ i, c₂ i :=
    (mul_le_mul_of_nonneg_left hxy hnpos.le).trans hs₂
  have ha0 : 0 ≤ ∑ i, a i := sum_nonneg fun i _ => MAC.condMutualInfo_nonneg₁ _ _ _
  have hb0 : 0 ≤ ∑ i, b i := sum_nonneg fun i _ => MAC.condMutualInfo_nonneg₂ _ _ _
  have hac : ∑ i, a i ≤ ∑ i, c₁ i :=
    sum_le_sum fun i _ => MAC.condMutualInfo_le_mutualInfo₁ _ _ _
  have had : ∑ i, a i ≤ ∑ i, c₂ i :=
    sum_le_sum fun i _ => (hW (L₁ i) (L₂ i)).1.trans (MAC.condMutualInfo_le_mutualInfo₁ _ _ _)
  have hbc : ∑ i, b i ≤ ∑ i, c₁ i :=
    sum_le_sum fun i _ => (hW (L₁ i) (L₂ i)).2.trans (MAC.condMutualInfo_le_mutualInfo₂ _ _ _)
  have hbd : ∑ i, b i ≤ ∑ i, c₂ i :=
    sum_le_sum fun i _ => MAC.condMutualInfo_le_mutualInfo₂ _ _ _
  obtain ⟨h₁, h₂, h₃, h₄⟩ := clamp ha0 hb0 hac had hbc hbd hx hy hs₁' hs₂'
  have hdiv : ∀ {u S : ℝ}, n * u ≤ S → u ≤ S / n := fun h => by
    rw [le_div_iff₀ hnpos]
    linarith
  refine ⟨(max x 0, max y 0), Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨unifPMF n,
    Set.mem_iUnion.2 ⟨L₁, Set.mem_iUnion.2 ⟨L₂, ?_⟩⟩⟩⟩, ?_⟩
  · refine ⟨le_max_right _ _, le_max_right _ _, ?_, ?_, ?_, ?_⟩
    · rw [sum_unifPMF_mul a]
      exact hdiv h₁
    · rw [sum_unifPMF_mul b]
      exact hdiv h₂
    · rw [sum_unifPMF_mul c₁]
      exact hdiv h₃
    · rw [sum_unifPMF_mul c₂]
      exact hdiv h₄
  · have hl0 : 0 ≤ 2 * Real.log 2 / n := by positivity
    have d1 := dist_max_le hR1 hε0.le hl0
    have d2 := dist_max_le hR2 hε0.le hl0
    have f1 : ε * R.1 ≤ ε * (R.1 + R.2 + 1) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
    have f2 : ε * R.2 ≤ ε * (R.1 + R.2 + 1) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨d1.trans_lt (by linarith), d2.trans_lt (by linarith)⟩

theorem closure_achievableRegion_subset_strongCapacityRegion {W : DMC (A₁ × A₂) (B₁ × B₂)}
    (hW : StrongInterference W) : closure (achievableRegion W) ⊆ strongCapacityRegion W :=
  closure_minimal (achievableRegion_subset_strongCapacityRegion hW) isClosed_closure

end Converse

end IC

end Meat
