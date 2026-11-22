import Mathlib.InformationTheory.Coding.Kraft
import Meat.Shannon.Inequalities
import Meat.Shannon.Typical

open MeasureTheory InformationTheory

namespace Meat

variable {S α : Type*}

def IsPrefixCode (c : S → List α) : Prop :=
  ∀ s t, c s <+: c t → s = t

def IsUDCode (c : S → List α) : Prop :=
  Function.Injective fun w : List S => (w.map c).flatten

noncomputable def expectedLength [Fintype S] (p : PMF S) (c : S → List α) : ℝ :=
  ∑ s, (p s).toReal * (c s).length

theorem IsPrefixCode.injective {c : S → List α} (hc : IsPrefixCode c) : Function.Injective c :=
  fun s t h => hc s t (h ▸ List.prefix_refl _)

theorem IsUDCode.injective {c : S → List α} (hc : IsUDCode c) : Function.Injective c :=
  fun s t h => by simpa using @hc [s] [t] (by simp [h])

theorem IsUDCode.ne_nil {c : S → List α} (hc : IsUDCode c) (s : S) : c s ≠ [] := fun h => by
  simpa using @hc [s] [s, s] (by simp [h])

private lemma isUDCode_of_range {c : S → List α} (hinj : Function.Injective c)
    (h : IsUniquelyDecodable (Set.range c)) : IsUDCode c := fun w₁ w₂ hw =>
  (List.map_injective_iff.2 hinj) (h _ _ (by simp) (by simp) hw)

private lemma isUniquelyDecodable_range {c : S → List α} (hc : IsUDCode c) :
    IsUniquelyDecodable (Set.range c) := by
  classical
  intro L₁ L₂ h₁ h₂ hL
  rcases isEmpty_or_nonempty S with hS | hS
  · have e : ∀ L : List (List α), (∀ w ∈ L, w ∈ Set.range c) → L = [] := fun L hL =>
      List.eq_nil_iff_forall_not_mem.2 fun w hw => by
        obtain ⟨s, -⟩ := hL w hw
        exact hS.elim s
    rw [e L₁ h₁, e L₂ h₂]
  have key : ∀ L : List (List α), (∀ w ∈ L, w ∈ Set.range c) →
      (L.map (Function.invFun c)).map c = L := fun L hL => by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id L]
    exact List.map_congr_left fun w hw => Function.invFun_eq (hL w hw)
  rw [← key L₁ h₁, ← key L₂ h₂] at hL ⊢
  rw [hc hL]

theorem IsPrefixCode.isUDCode {c : S → List α} (hc : IsPrefixCode c) (hne : ∀ s, c s ≠ []) :
    IsUDCode c := by
  refine isUDCode_of_range hc.injective (IsPrefixFree.isUniquelyDecodable ?_ ?_)
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
    rw [hc s t h]
  · rintro ⟨s, hs⟩
    exact hne s hs

variable [Fintype S] {D : ℕ}

private lemma sum_image_eq [DecidableEq α] {c : S → List α} (hc : Function.Injective c)
    (f : List α → ℝ) : ∑ w ∈ Finset.univ.image c, f w = ∑ s, f (c s) :=
  Finset.sum_image fun _ _ _ _ h => hc h

theorem IsPrefixCode.kraft [NeZero D] {c : S → List (Fin D)} (hc : IsPrefixCode c) :
    ∑ s, (1 / (D : ℝ)) ^ (c s).length ≤ 1 := by
  classical
  have h := IsPrefixFree.finsetSum_one_div_card_pow_length_le_one (S := Finset.univ.image c)
    (by
      intro x hx y hy hxy
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨s, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hy
      rw [hc s t hxy])
  rw [sum_image_eq hc.injective (fun w => (1 / (Fintype.card (Fin D) : ℝ)) ^ w.length)] at h
  simpa using h

theorem IsUDCode.kraft [NeZero D] {c : S → List (Fin D)} (hc : IsUDCode c) :
    ∑ s, (1 / (D : ℝ)) ^ (c s).length ≤ 1 := by
  classical
  have h := IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one
    (S := Finset.univ.image c) (by simpa using isUniquelyDecodable_range hc)
  rw [sum_image_eq hc.injective (fun w => (1 / (Fintype.card (Fin D) : ℝ)) ^ w.length)] at h
  simpa using h

private def words (D n : ℕ) : Finset (List (Fin D)) :=
  (Finset.univ : Finset (List.Vector (Fin D) n)).map
    ⟨List.Vector.toList, List.Vector.toList_injective⟩

private lemma mem_words {n : ℕ} {w : List (Fin D)} : w ∈ words D n ↔ w.length = n := by
  rw [words, Finset.mem_map]
  simp only [Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  exact ⟨fun ⟨v, hv⟩ => hv ▸ v.toList_length, fun h => ⟨⟨w, h⟩, rfl⟩⟩

private lemma card_words (n : ℕ) : (words D n).card = D ^ n := by
  rw [words, Finset.card_map, Finset.card_univ, card_vector, Fintype.card_fin]

omit [Fintype S] in
private lemma exists_prefix_on [NeZero D] (ℓ : S → ℕ) (T : Finset S) :
    ∑ s ∈ T, (1 / (D : ℝ)) ^ ℓ s ≤ 1 → ∃ c : S → List (Fin D),
      (∀ s ∈ T, (c s).length = ℓ s) ∧ ∀ s ∈ T, ∀ t ∈ T, c s <+: c t → s = t := by
  classical
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne D)
  induction T using Finset.induction_on_max_value ℓ with
  | empty => exact fun _ => ⟨fun _ => [], by simp, by simp⟩
  | insert a T haT hmax ih =>
    intro hK
    rw [Finset.sum_insert haT] at hK
    have hpos : 0 < (1 / (D : ℝ)) ^ ℓ a := by positivity
    obtain ⟨c, hlen, hpre⟩ := ih (by linarith)
    set L := ℓ a
    let bad := T.biUnion fun t => (words D (L - ℓ t)).image (c t ++ ·)
    have hcard : bad.card < (words D L).card := by
      have h1 : bad.card ≤ ∑ t ∈ T, D ^ (L - ℓ t) := by
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun t _ => ?_)
        exact Finset.card_image_le.trans (card_words _).le
      refine h1.trans_lt ?_
      rw [card_words]
      have h2 : ∀ t ∈ T, ((D ^ (L - ℓ t) : ℕ) : ℝ) = (D : ℝ) ^ L * (1 / (D : ℝ)) ^ ℓ t :=
        fun t ht => by
          rw [Nat.cast_pow, pow_sub₀ _ hD (hmax t ht), one_div_pow, div_eq_mul_inv, one_mul]
      have h3 : ((∑ t ∈ T, D ^ (L - ℓ t) : ℕ) : ℝ) < ((D ^ L : ℕ) : ℝ) := by
        rw [Nat.cast_sum, Finset.sum_congr rfl h2, ← Finset.mul_sum]
        have hDL : 0 < (D : ℝ) ^ L := by positivity
        have h4 : (D : ℝ) ^ L * (1 / (D : ℝ)) ^ L = 1 := by
          rw [one_div_pow, mul_one_div_cancel hDL.ne']
        push_cast
        nlinarith
      exact_mod_cast h3
    obtain ⟨w, hw, hwb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    rw [mem_words] at hw
    have hext : ∀ t ∈ T, ¬ c t <+: w := by
      rintro t ht ⟨v, rfl⟩
      refine hwb (Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image.2 ⟨v, ?_, rfl⟩⟩)
      rw [mem_words]
      simp only [List.length_append] at hw
      rw [hlen t ht] at hw
      omega
    have hne : ∀ t ∈ T, t ≠ a := fun t ht h => haT (h ▸ ht)
    refine ⟨Function.update c a w, ?_, ?_⟩
    · intro s hs
      rcases Finset.mem_insert.1 hs with rfl | hs
      · simpa using hw
      · rw [Function.update_of_ne (hne s hs)]
        exact hlen s hs
    · have hwa : ∀ t ∈ T, ¬ w <+: c t := fun t ht h => by
        have hl : w.length = (c t).length :=
          le_antisymm h.length_le (by rw [hlen t ht, hw]; exact hmax t ht)
        exact hext t ht (h.eq_of_length hl ▸ List.prefix_refl _)
      intro s hs t ht h
      by_cases hsa : s = a <;> by_cases hta : t = a
      · rw [hsa, hta]
      · have ht' := (Finset.mem_insert.1 ht).resolve_left hta
        rw [hsa, Function.update_self, Function.update_of_ne hta] at h
        exact absurd h (hwa t ht')
      · have hs' := (Finset.mem_insert.1 hs).resolve_left hsa
        rw [hta, Function.update_self, Function.update_of_ne hsa] at h
        exact absurd h (hext s hs')
      · have hs' := (Finset.mem_insert.1 hs).resolve_left hsa
        have ht' := (Finset.mem_insert.1 ht).resolve_left hta
        rw [Function.update_of_ne hsa, Function.update_of_ne hta] at h
        exact hpre s hs' t ht' h

theorem exists_isPrefixCode_of_kraft [NeZero D] (ℓ : S → ℕ)
    (h : ∑ s, (1 / (D : ℝ)) ^ ℓ s ≤ 1) :
    ∃ c : S → List (Fin D), IsPrefixCode c ∧ ∀ s, (c s).length = ℓ s := by
  obtain ⟨c, hlen, hpre⟩ := exists_prefix_on ℓ Finset.univ h
  exact ⟨c, fun s t => hpre s (Finset.mem_univ _) t (Finset.mem_univ _),
    fun s => hlen s (Finset.mem_univ _)⟩

private lemma sum_toReal (p : PMF S) : ∑ s, (p s).toReal = 1 := by
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum fun s _ => p.apply_ne_top s, h, ENNReal.toReal_one]

variable [MeasurableSpace S] [MeasurableSingletonClass S]

theorem measureEntropy_le_of_kraft [NeZero D] (p : PMF S) (ℓ : S → ℕ)
    (h : ∑ s, (1 / (D : ℝ)) ^ ℓ s ≤ 1) :
    measureEntropy p.toMeasure ≤ (∑ s, (p s).toReal * ℓ s) * Real.log D := by
  have hD : (0 : ℝ) < D := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne D))
  have hg := sum_mul_log_le_sum_mul_log Finset.univ (p := fun s => (p s).toReal)
    (q := fun s => (1 / (D : ℝ)) ^ ℓ s) (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ _ => by positivity) (fun _ _ h => absurd h (by positivity)) (by rw [sum_toReal]; exact h)
  rw [measureEntropy_toMeasure]
  simp only [Real.log_pow, one_div, Real.log_inv] at hg
  simp only [Real.negMulLog, Finset.sum_mul]
  have : ∑ s, (p s).toReal * (↑(ℓ s) * -Real.log D) = -∑ s, (p s).toReal * ℓ s * Real.log D := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [this] at hg
  have : ∑ s, -(p s).toReal * Real.log (p s).toReal =
      -∑ s, (p s).toReal * Real.log (p s).toReal := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [this]
  linarith

theorem IsUDCode.measureEntropy_le [NeZero D] (p : PMF S) {c : S → List (Fin D)}
    (hc : IsUDCode c) : measureEntropy p.toMeasure ≤ expectedLength p c * Real.log D :=
  measureEntropy_le_of_kraft p (fun s => (c s).length) hc.kraft

theorem IsPrefixCode.measureEntropy_le [NeZero D] (p : PMF S) {c : S → List (Fin D)}
    (hc : IsPrefixCode c) : measureEntropy p.toMeasure ≤ expectedLength p c * Real.log D :=
  measureEntropy_le_of_kraft p (fun s => (c s).length) hc.kraft

theorem exists_isPrefixCode_expectedLength_lt (hD : 2 ≤ D) (p : PMF S) (hp : ∀ s, p s ≠ 0) :
    ∃ c : S → List (Fin D), IsPrefixCode c ∧
      expectedLength p c < measureEntropy p.toMeasure / Real.log D + 1 := by
  have : NeZero D := ⟨by omega⟩
  have hD1 : (1 : ℝ) < D := by exact_mod_cast hD
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hp0 : ∀ s, 0 < (p s).toReal := fun s =>
    ENNReal.toReal_pos (hp s) (p.apply_ne_top s)
  have hp1 : ∀ s, (p s).toReal ≤ 1 := fun s =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using p.coe_le_one s)
  set x : S → ℝ := fun s => -Real.log (p s).toReal / Real.log D
  have hx0 : ∀ s, 0 ≤ x s := fun s =>
    div_nonneg (neg_nonneg.2 (Real.log_nonpos ENNReal.toReal_nonneg (hp1 s))) hlogD.le
  set ℓ : S → ℕ := fun s => ⌈x s⌉₊
  have hq : ∀ s, (1 / (D : ℝ)) ^ ℓ s ≤ (p s).toReal := fun s => by
    have hDl : 0 < (D : ℝ) ^ ℓ s := by positivity
    rw [one_div_pow, div_le_iff₀ hDl]
    have h1 : -Real.log (p s).toReal ≤ ℓ s * Real.log D := by
      have := Nat.le_ceil (x s)
      rw [div_le_iff₀ hlogD] at this
      exact this
    have h2 : (p s).toReal⁻¹ ≤ (D : ℝ) ^ ℓ s := by
      rw [← Real.exp_log (inv_pos.2 (hp0 s)), Real.log_inv, ← Real.exp_log hDl, Real.log_pow]
      exact Real.exp_le_exp.2 h1
    calc (1 : ℝ) = (p s).toReal * (p s).toReal⁻¹ := (mul_inv_cancel₀ (hp0 s).ne').symm
      _ ≤ (p s).toReal * (D : ℝ) ^ ℓ s := mul_le_mul_of_nonneg_left h2 (hp0 s).le
  obtain ⟨c, hc, hlen⟩ := exists_isPrefixCode_of_kraft (D := D) ℓ
    ((Finset.sum_le_sum fun s _ => hq s).trans (sum_toReal p).le)
  refine ⟨c, hc, ?_⟩
  have hne : (Finset.univ : Finset S).Nonempty := by
    obtain ⟨s, -⟩ := p.support_nonempty
    exact ⟨s, Finset.mem_univ _⟩
  have hlt : expectedLength p c < ∑ s, (p s).toReal * (x s + 1) := by
    simp only [expectedLength, hlen]
    exact Finset.sum_lt_sum_of_nonempty hne fun s _ =>
      mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (hx0 s)) (hp0 s)
  have heq : ∑ s, (p s).toReal * (x s + 1) = measureEntropy p.toMeasure / Real.log D + 1 := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, sum_toReal, measureEntropy_toMeasure,
      Finset.sum_div, x, Real.negMulLog]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

end Meat
