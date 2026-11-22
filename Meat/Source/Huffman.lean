import Meat.Source.Prefix

open MeasureTheory

namespace Meat

section Exchange

variable {ι : Type*}

private lemma sum_split [DecidableEq ι] {M : Type*} [AddCommMonoid M] {F : Finset ι} {i j : ι}
    (hi : i ∈ F) (hj : j ∈ F) (hij : i ≠ j) (f : ι → M) :
    ∑ x ∈ F, f x = f i + f j + ∑ x ∈ (F.erase i).erase j, f x := by
  rw [← Finset.add_sum_erase F f hi,
    ← Finset.add_sum_erase (F.erase i) f (Finset.mem_erase.2 ⟨hij.symm, hj⟩), add_assoc]

private lemma swap_apply_rest [DecidableEq ι] {F : Finset ι} {i j x : ι}
    (hx : x ∈ (F.erase i).erase j) : Equiv.swap i j x = x :=
  Equiv.swap_apply_of_ne_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx))
    (Finset.ne_of_mem_erase hx)

private lemma sum_comp_swap [DecidableEq ι] {M : Type*} [AddCommMonoid M] {F : Finset ι}
    {i j : ι} (hi : i ∈ F) (hj : j ∈ F) (f : ι → M) :
    ∑ x ∈ F, f (Equiv.swap i j x) = ∑ x ∈ F, f x := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  rw [sum_split hi hj hij, sum_split hi hj hij f, Equiv.swap_apply_left, Equiv.swap_apply_right,
    add_comm (f j)]
  congr 1
  exact Finset.sum_congr rfl fun x hx => by rw [swap_apply_rest hx]

private lemma cost_swap_le [DecidableEq ι] {F : Finset ι} {i j : ι} (hi : i ∈ F) (hj : j ∈ F)
    (w : ι → ℝ) (ℓ : ι → ℕ) (hw : w i ≤ w j) (hl : ℓ i ≤ ℓ j) :
    ∑ x ∈ F, w x * ℓ (Equiv.swap i j x) ≤ ∑ x ∈ F, w x * ℓ x := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  rw [sum_split hi hj hij (fun x => w x * (ℓ (Equiv.swap i j x) : ℝ)),
    sum_split hi hj hij (fun x => w x * (ℓ x : ℝ))]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hrest : ∑ x ∈ (F.erase i).erase j, w x * (ℓ (Equiv.swap i j x) : ℝ) =
      ∑ x ∈ (F.erase i).erase j, w x * ℓ x :=
    Finset.sum_congr rfl fun x hx => by rw [swap_apply_rest hx]
  have hl' : (ℓ i : ℝ) ≤ ℓ j := by exact_mod_cast hl
  nlinarith

private lemma kraft_iff_nat (F : Finset ι) (ℓ : ι → ℕ) {M : ℕ} (hM : ∀ i ∈ F, ℓ i ≤ M) :
    ∑ i ∈ F, (1 / 2 : ℝ) ^ ℓ i ≤ 1 ↔ ∑ i ∈ F, 2 ^ (M - ℓ i) ≤ 2 ^ M := by
  have h : ∑ i ∈ F, (1 / 2 : ℝ) ^ ℓ i = ((∑ i ∈ F, 2 ^ (M - ℓ i) : ℕ) : ℝ) / 2 ^ M := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_sub₀ _ two_ne_zero (hM i hi), one_div_pow]
    field_simp
  rw [h, div_le_one (by positivity), show (2 : ℝ) ^ M = ((2 ^ M : ℕ) : ℝ) by push_cast; rfl,
    Nat.cast_le]

theorem exists_sibling_lengths {F : Finset ι} {w : ι → ℝ} (hw : ∀ i ∈ F, 0 ≤ w i) {a b : ι}
    (ha : a ∈ F) (hb : b ∈ F) (hab : a ≠ b) (hwa : ∀ x ∈ F, w a ≤ w x)
    (hwb : ∀ x ∈ F, x ≠ a → w b ≤ w x) (ℓ : ι → ℕ) (hK : ∑ i ∈ F, (1 / 2 : ℝ) ^ ℓ i ≤ 1) :
    ∃ ℓ' : ι → ℕ, ∑ i ∈ F, (1 / 2 : ℝ) ^ ℓ' i ≤ 1 ∧ 1 ≤ ℓ' a ∧ ℓ' b = ℓ' a ∧
      ∑ i ∈ F, w i * ℓ' i ≤ ∑ i ∈ F, w i * ℓ i := by
  classical
  induction hn : ∑ i ∈ F, ℓ i using Nat.strong_induction_on generalizing ℓ with
  | _ n ih =>
  obtain ⟨x, hx, hxmax⟩ := F.exists_max_image ℓ ⟨a, ha⟩
  by_cases hy : ∃ y ∈ F, y ≠ x ∧ ℓ y = ℓ x
  · obtain ⟨y, hy, hyx, hyl⟩ := hy
    have hM : 1 ≤ ℓ x := by
      by_contra h0
      have h0' : ℓ x = 0 := by omega
      rw [sum_split hy hx hyx, hyl, h0'] at hK
      have := Finset.sum_nonneg (s := (F.erase y).erase x)
        (fun i _ => (by positivity : (0 : ℝ) ≤ (1 / 2) ^ ℓ i))
      norm_num at hK
      linarith
    set ℓ₁ : ι → ℕ := fun i => ℓ (Equiv.swap a x i) with hℓ₁
    have hℓ₁le : ∀ i ∈ F, ℓ₁ i ≤ ℓ x := fun i hi => hxmax _ (by
      rw [Equiv.swap_apply_def]
      split_ifs <;> assumption)
    have hℓ₁a : ℓ₁ a = ℓ x := by simp [hℓ₁]
    obtain ⟨y', hy'F, hy'a, hy'l⟩ : ∃ y' ∈ F, y' ≠ a ∧ ℓ₁ y' = ℓ x := by
      by_cases hya : y = a
      · refine ⟨x, hx, fun e => hyx (hya.trans e.symm), ?_⟩
        simp [hℓ₁, ← hya, hyl]
      · refine ⟨y, hy, hya, ?_⟩
        simp only [hℓ₁]
        rw [Equiv.swap_apply_of_ne_of_ne hya hyx, hyl]
    have hswa : Equiv.swap b y' a = a := Equiv.swap_apply_of_ne_of_ne hab hy'a.symm
    refine ⟨fun i => ℓ₁ (Equiv.swap b y' i), ?_, ?_, ?_, ?_⟩
    · exact (sum_comp_swap hb hy'F (fun i => (1 / 2 : ℝ) ^ ℓ₁ i)).trans_le
        ((sum_comp_swap ha hx (fun i => (1 / 2 : ℝ) ^ ℓ i)).trans_le hK)
    · simp only [hswa, hℓ₁a]
      exact hM
    · simp only [hswa, hℓ₁a, Equiv.swap_apply_left, hy'l]
    · exact (cost_swap_le hb hy'F w ℓ₁ (hwb y' hy'F hy'a) (hy'l ▸ hℓ₁le b hb)).trans
        (cost_swap_le ha hx w ℓ (hwa x hx) (hxmax a ha))
  · push Not at hy
    have hlt : ∀ y ∈ F, y ≠ x → ℓ y < ℓ x := fun y hyF hyx =>
      lt_of_le_of_ne (hxmax y hyF) (hy y hyF hyx)
    obtain ⟨z, hz, hzx⟩ : ∃ z ∈ F, z ≠ x := by
      by_cases hax : a = x
      · exact ⟨b, hb, fun e => hab (hax.trans e.symm)⟩
      · exact ⟨a, ha, hax⟩
    have hM : 1 ≤ ℓ x := by
      have := hlt z hz hzx
      omega
    set ℓ₀ := Function.update ℓ x (ℓ x - 1) with hℓ₀
    have hrest : ∀ i ∈ F.erase x, ℓ₀ i = ℓ i := fun i hi =>
      Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
    have hK0 : ∑ i ∈ F, (1 / 2 : ℝ) ^ ℓ₀ i ≤ 1 := by
      have hb0 : ∀ i ∈ F, ℓ₀ i ≤ ℓ x := fun i hi => by
        rcases eq_or_ne i x with rfl | h
        · simp [hℓ₀]
        · rw [hℓ₀, Function.update_of_ne h]
          exact hxmax i hi
      rw [kraft_iff_nat F ℓ hxmax] at hK
      rw [kraft_iff_nat F ℓ₀ hb0]
      rw [← Finset.add_sum_erase F _ hx] at hK ⊢
      rw [Finset.sum_congr rfl fun i hi => by rw [hrest i hi]]
      have heven : 2 ∣ ∑ i ∈ F.erase x, 2 ^ (ℓ x - ℓ i) := Finset.dvd_sum fun i hi =>
        dvd_pow_self 2 (by
          have := hlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
          omega)
      have h2M : 2 ∣ 2 ^ ℓ x := dvd_pow_self 2 (by omega)
      rw [Nat.sub_self, pow_zero] at hK
      rw [hℓ₀, Function.update_self, show ℓ x - (ℓ x - 1) = 1 by omega, pow_one]
      obtain ⟨e, he⟩ := heven
      obtain ⟨m, hm⟩ := h2M
      omega
    have hsum : ∑ i ∈ F, ℓ₀ i < n := by
      have e1 : ∑ i ∈ F.erase x, ℓ₀ i = ∑ i ∈ F.erase x, ℓ i := Finset.sum_congr rfl hrest
      rw [← hn, ← Finset.add_sum_erase F ℓ₀ hx, ← Finset.add_sum_erase F ℓ hx, e1, hℓ₀,
        Function.update_self]
      omega
    obtain ⟨ℓ', h1, h2, h3, h4⟩ := ih _ hsum ℓ₀ hK0 rfl
    refine ⟨ℓ', h1, h2, h3, h4.trans ?_⟩
    rw [← Finset.add_sum_erase F _ hx, ← Finset.add_sum_erase F (fun i => w i * (ℓ i : ℝ)) hx,
      Finset.sum_congr rfl fun i hi => by rw [hrest i hi]]
    simp only [hℓ₀, Function.update_self]
    have := mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ).2 (Nat.sub_le (ℓ x) 1)) (hw x hx)
    linarith

end Exchange

section Huffman

variable {α : Type*} [DecidableEq α] (p : α → ℝ)

private noncomputable def pick (F : Finset (Finset α)) : Finset α :=
  if h : F.Nonempty then (F.exists_min_image (fun t => ∑ s ∈ t, p s) h).choose else ∅

omit [DecidableEq α] in
private lemma pick_mem {F : Finset (Finset α)} (h : F.Nonempty) : pick p F ∈ F := by
  simp only [pick, h, ↓reduceDIte]
  exact (F.exists_min_image (fun t => ∑ s ∈ t, p s) h).choose_spec.1

omit [DecidableEq α] in
private lemma pick_le {F : Finset (Finset α)} (h : F.Nonempty) :
    ∀ t ∈ F, ∑ s ∈ pick p F, p s ≤ ∑ s ∈ t, p s := by
  simp only [pick, h, ↓reduceDIte]
  exact (F.exists_min_image (fun t => ∑ s ∈ t, p s) h).choose_spec.2

private noncomputable def first (F : Finset (Finset α)) : Finset α := pick p F

private noncomputable def second (F : Finset (Finset α)) : Finset α := pick p (F.erase (first p F))

private noncomputable def merge (F : Finset (Finset α)) : Finset (Finset α) :=
  insert (first p F ∪ second p F) ((F.erase (first p F)).erase (second p F))

variable {p}

omit [DecidableEq α] in
private lemma first_mem {F : Finset (Finset α)} (h : 2 ≤ F.card) : first p F ∈ F :=
  pick_mem p (Finset.card_pos.1 (by omega))

private lemma second_mem_erase {F : Finset (Finset α)} (h : 2 ≤ F.card) :
    second p F ∈ F.erase (first p F) :=
  pick_mem p (Finset.card_pos.1 (by rw [Finset.card_erase_of_mem (first_mem h)]; omega))

private lemma second_mem {F : Finset (Finset α)} (h : 2 ≤ F.card) : second p F ∈ F :=
  Finset.mem_of_mem_erase (second_mem_erase h)

private lemma first_ne_second {F : Finset (Finset α)} (h : 2 ≤ F.card) :
    first p F ≠ second p F :=
  (Finset.ne_of_mem_erase (second_mem_erase h)).symm

private lemma card_merge_lt {F : Finset (Finset α)} (h : 2 ≤ F.card) :
    (merge p F).card < F.card := by
  have h1 := Finset.card_erase_of_mem (first_mem (p := p) h)
  have h2 := Finset.card_erase_of_mem (second_mem_erase (p := p) h)
  have h3 := Finset.card_insert_le (first p F ∪ second p F)
    ((F.erase (first p F)).erase (second p F))
  rw [merge]
  omega

noncomputable def huffmanLength (p : α → ℝ) (F : Finset (Finset α)) (t : Finset α) : ℕ :=
  if h : 2 ≤ F.card then
    if t = first p F ∨ t = second p F then
      huffmanLength p (merge p F) (first p F ∪ second p F) + 1
    else huffmanLength p (merge p F) t
  else 0
termination_by F.card
decreasing_by all_goals exact card_merge_lt h

private lemma huffmanLength_step {F : Finset (Finset α)} (h : 2 ≤ F.card) (t : Finset α) :
    huffmanLength p F t = if t = first p F ∨ t = second p F then
      huffmanLength p (merge p F) (first p F ∪ second p F) + 1
    else huffmanLength p (merge p F) t := by
  rw [huffmanLength]
  simp only [h, ↓reduceDIte]

private lemma huffmanLength_of_lt {F : Finset (Finset α)} (h : ¬ 2 ≤ F.card) (t : Finset α) :
    huffmanLength p F t = 0 := by
  rw [huffmanLength]
  simp only [h, ↓reduceDIte]

private lemma huffmanLength_first {F : Finset (Finset α)} (h : 2 ≤ F.card) :
    huffmanLength p F (first p F) = huffmanLength p (merge p F) (first p F ∪ second p F) + 1 := by
  rw [huffmanLength_step h]
  simp

private lemma huffmanLength_second {F : Finset (Finset α)} (h : 2 ≤ F.card) :
    huffmanLength p F (second p F) = huffmanLength p (merge p F) (first p F ∪ second p F) + 1 := by
  rw [huffmanLength_step h]
  simp

private lemma huffmanLength_rest {F : Finset (Finset α)} (h : 2 ≤ F.card) {t : Finset α}
    (ht : t ∈ (F.erase (first p F)).erase (second p F)) :
    huffmanLength p F t = huffmanLength p (merge p F) t := by
  rw [huffmanLength_step h]
  simp [Finset.ne_of_mem_erase ht, Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht)]

private lemma union_notMem {F : Finset (Finset α)} (hne : ∀ t ∈ F, t.Nonempty)
    (hd : (F : Set (Finset α)).PairwiseDisjoint id) (h : 2 ≤ F.card) :
    first p F ∪ second p F ∉ (F.erase (first p F)).erase (second p F) := by
  intro hu
  have huF := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hu)
  have hua := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hu)
  have hdis : Disjoint (first p F ∪ second p F) (first p F) := hd huF (first_mem h) hua
  have := Finset.disjoint_of_subset_left Finset.subset_union_left hdis
  rw [disjoint_self, Finset.bot_eq_empty] at this
  exact (hne _ (first_mem h)).ne_empty this

private lemma sum_merge {M : Type*} [AddCommMonoid M] {F : Finset (Finset α)}
    (hne : ∀ t ∈ F, t.Nonempty) (hd : (F : Set (Finset α)).PairwiseDisjoint id) (h : 2 ≤ F.card)
    (f : Finset α → M) : ∑ t ∈ merge p F, f t =
      f (first p F ∪ second p F) + ∑ t ∈ (F.erase (first p F)).erase (second p F), f t := by
  rw [merge, Finset.sum_insert (union_notMem hne hd h)]

private lemma merge_nonempty {F : Finset (Finset α)} (hne : ∀ t ∈ F, t.Nonempty)
    (h : 2 ≤ F.card) : ∀ t ∈ merge p F, t.Nonempty := by
  intro t ht
  rcases Finset.mem_insert.1 ht with rfl | ht
  · exact (hne _ (second_mem h)).mono Finset.subset_union_right
  · exact hne t (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))

private lemma merge_disjoint {F : Finset (Finset α)} (hd : (F : Set (Finset α)).PairwiseDisjoint id)
    (h : 2 ≤ F.card) : (merge p F : Set (Finset α)).PairwiseDisjoint id := by
  rw [merge, Finset.coe_insert]
  refine (hd.subset fun t ht => ?_).insert fun j hj _ => ?_
  · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
  · have hjF := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)
    have hjb := Finset.ne_of_mem_erase hj
    have hja := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
    exact Finset.disjoint_union_left.2
      ⟨hd (first_mem h) hjF hja.symm, hd (second_mem h) hjF hjb.symm⟩

theorem sum_huffmanLength {F : Finset (Finset α)} (hne : ∀ t ∈ F, t.Nonempty)
    (hd : (F : Set (Finset α)).PairwiseDisjoint id) (hF : F.Nonempty) :
    ∑ t ∈ F, (1 / 2 : ℝ) ^ huffmanLength p F t = 1 := by
  induction hn : F.card using Nat.strong_induction_on generalizing F with
  | _ n ih =>
  by_cases h2 : 2 ≤ F.card
  · have hm := ih _ (hn ▸ card_merge_lt (p := p) h2) (F := merge p F) (merge_nonempty hne h2)
      (merge_disjoint hd h2)
      ⟨_, Finset.mem_insert_self _ _⟩ rfl
    rw [sum_merge hne hd h2] at hm
    rw [sum_split (first_mem h2) (second_mem h2) (first_ne_second h2),
      huffmanLength_first h2, huffmanLength_second h2,
      Finset.sum_congr rfl fun t ht => by rw [huffmanLength_rest h2 ht], pow_succ]
    linarith
  · obtain ⟨t, rfl⟩ := (Finset.card_eq_one (s := F)).1 (by have := hF.card_pos; omega)
    simp [huffmanLength_of_lt h2]

theorem huffmanLength_le (hp : ∀ s, 0 ≤ p s) {F : Finset (Finset α)}
    (hne : ∀ t ∈ F, t.Nonempty) (hd : (F : Set (Finset α)).PairwiseDisjoint id)
    (ℓ : Finset α → ℕ) (hK : ∑ t ∈ F, (1 / 2 : ℝ) ^ ℓ t ≤ 1) :
    ∑ t ∈ F, (∑ s ∈ t, p s) * huffmanLength p F t ≤ ∑ t ∈ F, (∑ s ∈ t, p s) * ℓ t := by
  have hw : ∀ t : Finset α, 0 ≤ ∑ s ∈ t, p s := fun t => Finset.sum_nonneg fun s _ => hp s
  induction hn : F.card using Nat.strong_induction_on generalizing F ℓ with
  | _ n ih =>
  by_cases h2 : 2 ≤ F.card
  · set a := first p F with hadef
    set b := second p F with hbdef
    have ha := first_mem (p := p) h2
    have hb := second_mem (p := p) h2
    have hab := first_ne_second (p := p) h2
    obtain ⟨ℓs, hKs, hs1, hsb, hcost⟩ := exists_sibling_lengths (w := fun t => ∑ s ∈ t, p s)
      (fun t _ => hw t) ha hb hab (pick_le p ⟨_, ha⟩)
      (fun x hx hxa => pick_le p ⟨_, Finset.mem_erase.2 ⟨hab.symm, hb⟩⟩ x
        (Finset.mem_erase.2 ⟨hxa, hx⟩)) ℓ hK
    obtain ⟨m, hm⟩ : ∃ m, ℓs a = m + 1 := ⟨ℓs a - 1, (Nat.sub_add_cancel hs1).symm⟩
    set R := (F.erase a).erase b with hRdef
    have hu := union_notMem (p := p) hne hd h2
    have hR : ∀ t ∈ R, t ≠ a ∪ b := fun t ht e => hu (e ▸ ht)
    set ℓ' : Finset α → ℕ := fun t => if t = a ∪ b then m else ℓs t with hℓ'
    have hℓ'u : ℓ' (a ∪ b) = m := by simp [hℓ']
    have hℓ'R : ∀ t ∈ R, ℓ' t = ℓs t := fun t ht => by simp [hℓ', hR t ht]
    have hK' : ∑ t ∈ merge p F, (1 / 2 : ℝ) ^ ℓ' t ≤ 1 := by
      rw [sum_merge hne hd h2, hℓ'u, Finset.sum_congr rfl fun t ht => by rw [hℓ'R t ht]]
      rw [sum_split ha hb hab, hsb, hm, pow_succ] at hKs
      linarith
    have hIH := ih _ (hn ▸ card_merge_lt (p := p) h2) (F := merge p F) (merge_nonempty hne h2)
      (merge_disjoint hd h2) ℓ' hK' rfl
    have e1 : ∑ t ∈ R, (∑ s ∈ t, p s) * (ℓ' t : ℝ) = ∑ t ∈ R, (∑ s ∈ t, p s) * (ℓs t : ℝ) :=
      Finset.sum_congr rfl fun t ht => by rw [hℓ'R t ht]
    have e2 : ∑ t ∈ R, (∑ s ∈ t, p s) * (huffmanLength p F t : ℝ) =
        ∑ t ∈ R, (∑ s ∈ t, p s) * (huffmanLength p (merge p F) t : ℝ) :=
      Finset.sum_congr rfl fun t ht => by rw [huffmanLength_rest h2 ht]
    have e3 : ∑ s ∈ a ∪ b, p s = ∑ s ∈ a, p s + ∑ s ∈ b, p s := Finset.sum_union (hd ha hb hab)
    rw [sum_merge hne hd h2, sum_merge hne hd h2, hℓ'u, e1, e3] at hIH
    rw [sum_split ha hb hab (fun i => (∑ s ∈ i, p s) * (ℓs i : ℝ)), hsb, hm] at hcost
    rw [sum_split ha hb hab (fun t => (∑ s ∈ t, p s) * (huffmanLength p F t : ℝ)),
      huffmanLength_first h2, huffmanLength_second h2]
    simp only [← hadef, ← hbdef, ← hRdef] at hIH hcost ⊢
    rw [e2]
    push_cast at hIH hcost ⊢
    linarith
  · rw [Finset.sum_congr rfl fun t _ => by rw [huffmanLength_of_lt h2], Nat.cast_zero]
    simp only [mul_zero, Finset.sum_const_zero]
    exact Finset.sum_nonneg fun t _ => mul_nonneg (hw t) (Nat.cast_nonneg _)

end Huffman

section Code

variable {S : Type*} [Fintype S] [DecidableEq S]

private def singletons (S : Type*) [Fintype S] [DecidableEq S] : Finset (Finset S) :=
  Finset.univ.image fun s : S => ({s} : Finset S)

noncomputable def huffmanCodeLength (p : PMF S) (s : S) : ℕ :=
  huffmanLength (fun s => (p s).toReal) (singletons S) {s}

private lemma singletons_nonempty : ∀ t ∈ singletons S, t.Nonempty := by
  simp [singletons]

private lemma singletons_disjoint :
    ((singletons S : Finset (Finset S)) : Set (Finset S)).PairwiseDisjoint id := by
  rintro _ hs _ ht hst
  simp only [singletons, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_range] at hs ht
  obtain ⟨s, rfl⟩ := hs
  obtain ⟨t, rfl⟩ := ht
  simpa [Function.onFun] using fun h : s = t => hst (h ▸ rfl)

private lemma sum_singletons {M : Type*} [AddCommMonoid M] (g : Finset S → M) :
    ∑ t ∈ singletons S, g t = ∑ s, g {s} :=
  Finset.sum_image fun _ _ _ _ h => Finset.singleton_injective h

theorem sum_huffmanCodeLength (p : PMF S) :
    ∑ s, (1 / 2 : ℝ) ^ huffmanCodeLength p s = 1 := by
  have hne : (singletons S).Nonempty := by
    obtain ⟨s, -⟩ := p.support_nonempty
    exact ⟨{s}, Finset.mem_image_of_mem _ (Finset.mem_univ s)⟩
  have := sum_huffmanLength (p := fun s => (p s).toReal) singletons_nonempty singletons_disjoint hne
  rwa [sum_singletons (fun t => (1 / 2 : ℝ) ^ huffmanLength (fun s => (p s).toReal)
    (singletons S) t)] at this

theorem huffmanCodeLength_le (p : PMF S) (ℓ : S → ℕ) (hK : ∑ s, (1 / 2 : ℝ) ^ ℓ s ≤ 1) :
    ∑ s, (p s).toReal * huffmanCodeLength p s ≤ ∑ s, (p s).toReal * ℓ s := by
  have := huffmanLength_le (p := fun s => (p s).toReal) (fun _ => ENNReal.toReal_nonneg)
    singletons_nonempty singletons_disjoint (fun t => ∑ s ∈ t, ℓ s)
    (by rw [sum_singletons (fun t => (1 / 2 : ℝ) ^ ∑ s ∈ t, ℓ s)]; simpa using hK)
  rw [sum_singletons (fun t => (∑ s ∈ t, (p s).toReal) * (huffmanLength _ _ t : ℝ)),
    sum_singletons (fun t => (∑ s ∈ t, (p s).toReal) * ((∑ s ∈ t, ℓ s : ℕ) : ℝ))] at this
  simpa [huffmanCodeLength] using this

private lemma kraft_huffmanCodeLength (p : PMF S) :
    ∑ s, (1 / ((2 : ℕ) : ℝ)) ^ huffmanCodeLength p s ≤ 1 := by
  rw [Nat.cast_ofNat, sum_huffmanCodeLength]

noncomputable def huffmanCode (p : PMF S) : S → List (Fin 2) :=
  (exists_isPrefixCode_of_kraft (huffmanCodeLength p) (kraft_huffmanCodeLength p)).choose

theorem isPrefixCode_huffmanCode (p : PMF S) : IsPrefixCode (huffmanCode p) :=
  (exists_isPrefixCode_of_kraft (huffmanCodeLength p) (kraft_huffmanCodeLength p)).choose_spec.1

theorem length_huffmanCode (p : PMF S) (s : S) :
    (huffmanCode p s).length = huffmanCodeLength p s :=
  (exists_isPrefixCode_of_kraft (huffmanCodeLength p) (kraft_huffmanCodeLength p)).choose_spec.2 s

private lemma expectedLength_huffmanCode_le_of_kraft (p : PMF S) (c : S → List (Fin 2))
    (hK : ∑ s, (1 / ((2 : ℕ) : ℝ)) ^ (c s).length ≤ 1) :
    expectedLength p (huffmanCode p) ≤ expectedLength p c := by
  simp only [expectedLength, length_huffmanCode]
  exact huffmanCodeLength_le p _ (by simpa using hK)

theorem IsPrefixCode.expectedLength_huffmanCode_le (p : PMF S) {c : S → List (Fin 2)}
    (hc : IsPrefixCode c) : expectedLength p (huffmanCode p) ≤ expectedLength p c :=
  expectedLength_huffmanCode_le_of_kraft p c hc.kraft

theorem IsUDCode.expectedLength_huffmanCode_le (p : PMF S) {c : S → List (Fin 2)}
    (hc : IsUDCode c) : expectedLength p (huffmanCode p) ≤ expectedLength p c :=
  expectedLength_huffmanCode_le_of_kraft p c hc.kraft

variable [MeasurableSpace S] [MeasurableSingletonClass S]

theorem expectedLength_huffmanCode_lt (p : PMF S) (hp : ∀ s, p s ≠ 0) :
    expectedLength p (huffmanCode p) < measureEntropy p.toMeasure / Real.log 2 + 1 := by
  obtain ⟨c, hc, hlt⟩ := exists_isPrefixCode_expectedLength_lt (D := 2) le_rfl p hp
  exact (hc.expectedLength_huffmanCode_le p).trans_lt (by simpa using hlt)

end Code

end Meat
