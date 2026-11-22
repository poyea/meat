import Meat.Shannon.Divergence
import Meat.Shannon.Typical

open MeasureTheory Filter Topology Finset

namespace Meat

variable {S : Type*} [Fintype S] [DecidableEq S]

def typeCount {n : ℕ} (x : Fin n → S) (s : S) : ℕ := #{i | x i = s}

theorem sum_typeCount {n : ℕ} (x : Fin n → S) : ∑ s, typeCount x s = n := by
  simp only [typeCount]
  rw [← card_eq_sum_card_fiberwise (f := x) (t := univ) (fun _ _ => mem_univ _), card_univ,
    Fintype.card_fin]

omit [Fintype S] in
theorem typeCount_le {n : ℕ} (x : Fin n → S) (s : S) : typeCount x s ≤ n :=
  (card_filter_le _ _).trans (by simp)

theorem prod_comp_eq_prod_pow {M : Type*} [CommMonoid M] {n : ℕ} (x : Fin n → S) (f : S → M) :
    ∏ i, f (x i) = ∏ s, f s ^ typeCount x s := by
  rw [← prod_fiberwise univ x fun i => f (x i)]
  refine prod_congr rfl fun s _ => ?_
  rw [prod_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], prod_const]
  rfl

theorem sum_comp_eq_sum_typeCount_mul {n : ℕ} (x : Fin n → S) (f : S → ℝ) :
    ∑ i, f (x i) = ∑ s, (typeCount x s : ℝ) * f s := by
  rw [← sum_fiberwise univ x fun i => f (x i)]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], sum_const, nsmul_eq_mul]
  rfl

theorem prod_comp_eq_exp {n : ℕ} (x : Fin n → S) (w : S → ℝ) (hw : ∀ i, 0 < w (x i)) :
    ∏ i, w (x i) = Real.exp (∑ s, (typeCount x s : ℝ) * Real.log (w s)) := by
  rw [← sum_comp_eq_sum_typeCount_mul, Real.exp_sum]
  exact prod_congr rfl fun i _ => (Real.exp_log (hw i)).symm

omit [Fintype S] in
theorem typeCount_cons {n : ℕ} (a : S) (y : Fin n → S) (s : S) :
    typeCount (Fin.cons a y : Fin (n + 1) → S) s = typeCount y s + if a = s then 1 else 0 := by
  simp only [typeCount, card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem card_typeCount_eq_mul_prod_factorial (n : ℕ) (k : S → ℕ) (hk : ∑ s, k s = n) :
    #{x : Fin n → S | typeCount x = k} * ∏ s, (k s).factorial = n.factorial := by
  induction n generalizing k with
  | zero =>
    have h0 : ∀ s, k s = 0 := fun s => (sum_eq_zero_iff.1 hk) s (mem_univ s)
    have hx : ∀ x : Fin 0 → S, typeCount x = k := fun x =>
      funext fun s => by rw [h0 s]; exact Nat.le_zero.1 (typeCount_le x s)
    simp [hx, h0]
  | succ n ih =>
    have hsplit : ∀ a, #{y : Fin n → S | typeCount (Fin.cons a y : Fin (n + 1) → S) = k}
        * ∏ s, (k s).factorial = k a * n.factorial := by
      intro a
      rcases Nat.eq_zero_or_pos (k a) with ha | ha
      · rw [ha, zero_mul, mul_eq_zero, card_eq_zero]
        left
        refine filter_eq_empty_iff.2 fun y _ h => ?_
        have := congrFun h a
        rw [typeCount_cons] at this
        simp at this
        omega
      set k' : S → ℕ := fun s => k s - if a = s then 1 else 0
      have hiff : ∀ y : Fin n → S,
          typeCount (Fin.cons a y : Fin (n + 1) → S) = k ↔ typeCount y = k' := fun y => by
        simp only [funext_iff, typeCount_cons, k']
        refine forall_congr' fun s => ?_
        split_ifs with h
        · subst h
          omega
        · omega
      have hk' : ∑ s, k' s = n := by
        have e : ∑ s, k s = ∑ s, (k' s + if a = s then 1 else 0) := sum_congr rfl fun s _ => by
          simp only [k']
          split_ifs with h
          · subst h
            omega
          · omega
        rw [sum_add_distrib, sum_ite_eq] at e
        simp only [mem_univ, ite_true, hk] at e
        omega
      have hprod : ∏ s, (k s).factorial = k a * ∏ s, (k' s).factorial := by
        have e1 : k' a = k a - 1 := by simp [k']
        have e2 : ∏ s ∈ {a}ᶜ, (k' s).factorial = ∏ s ∈ {a}ᶜ, (k s).factorial :=
          prod_congr rfl fun s hs => by
            have : a ≠ s := fun h => by simp [h] at hs
            simp [k', this]
        rw [Fintype.prod_eq_mul_prod_compl a (fun s => (k s).factorial),
          Fintype.prod_eq_mul_prod_compl a (fun s => (k' s).factorial), e1, e2,
          ← mul_assoc, Nat.mul_factorial_pred ha.ne']
      rw [filter_congr fun y _ => hiff y, hprod, mul_left_comm, ih k' hk']
    have hcard : #{x : Fin (n + 1) → S | typeCount x = k}
        = ∑ a, #{y : Fin n → S | typeCount (Fin.cons a y : Fin (n + 1) → S) = k} := by
      simp only [card_filter]
      rw [← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ => S).sum_comp]
      rfl
    rw [hcard, sum_mul, sum_congr rfl fun a _ => hsplit a, ← sum_mul, hk,
      Nat.factorial_succ]

theorem exists_typeCount_eq (n : ℕ) (k : S → ℕ) (hk : ∑ s, k s = n) :
    ∃ x : Fin n → S, typeCount x = k := by
  have h := card_typeCount_eq_mul_prod_factorial n k hk
  obtain ⟨x, hx⟩ := card_pos.1 (Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at h
    exact (Nat.factorial_pos n).ne' h.symm)
  exact ⟨x, (mem_filter.1 hx).2⟩

theorem factorial_mul_pow_le (j k : ℕ) : k.factorial * k ^ j ≤ j.factorial * k ^ k := by
  rcases le_total j k with h | h
  · have e := Nat.factorial_mul_descFactorial (Nat.sub_le k j)
    rw [Nat.sub_sub_self h] at e
    calc k.factorial * k ^ j = j.factorial * k.descFactorial (k - j) * k ^ j := by rw [e]
      _ ≤ j.factorial * k ^ (k - j) * k ^ j := by
        gcongr
        exact Nat.descFactorial_le_pow k _
      _ = j.factorial * k ^ k := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    calc k.factorial * k ^ (k + m) = k.factorial * k ^ m * k ^ k := by ring
      _ ≤ k.factorial * (k + 1) ^ m * k ^ k := by
        gcongr
        exact Nat.le_succ k
      _ ≤ (k + m).factorial * k ^ k := by
        gcongr
        exact Nat.factorial_mul_pow_le_factorial

variable [MeasurableSpace S] [MeasurableSingletonClass S]

noncomputable def seqType {n : ℕ} (x : Fin n → S) : Measure S :=
  ∑ s, ENNReal.ofReal (typeCount x s / n) • Measure.dirac s

noncomputable def typeSet (n : ℕ) : Finset (Measure S) := by
  classical
  exact univ.image fun x : Fin n → S => seqType x

noncomputable def typeClass (P : Measure S) (n : ℕ) : Finset (Fin n → S) := by
  classical
  exact {x | seqType x = P}

theorem seqType_apply_singleton {n : ℕ} (x : Fin n → S) (s : S) :
    seqType x {s} = ENNReal.ofReal (typeCount x s / n) := by
  simp [seqType, Measure.dirac_apply' _ (measurableSet_singleton s),
    Set.indicator_apply]

theorem seqType_real {n : ℕ} (x : Fin n → S) (s : S) :
    (seqType x).real {s} = typeCount x s / n := by
  rw [measureReal_def, seqType_apply_singleton, ENNReal.toReal_ofReal (by positivity)]

theorem isProbabilityMeasure_seqType {n : ℕ} (hn : 0 < n) (x : Fin n → S) :
    IsProbabilityMeasure (seqType x) := by
  constructor
  rw [← Finset.coe_univ, ← sum_measure_singleton]
  simp_rw [seqType_apply_singleton]
  rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, ← sum_div]
  have : (n : ℝ) ≠ 0 := by positivity
  simp [← Nat.cast_sum, sum_typeCount, this]

theorem seqType_eq_seqType_iff {n : ℕ} (x y : Fin n → S) :
    seqType x = seqType y ↔ typeCount x = typeCount y := by
  refine ⟨fun h => funext fun s => ?_, fun h => by simp only [seqType, h]⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Nat.le_zero.1 (typeCount_le x s), Nat.le_zero.1 (typeCount_le y s)]
  have e := congrArg (fun μ : Measure S => μ.real {s}) h
  simp only [seqType_real] at e
  exact_mod_cast (div_left_inj' (by positivity : (n : ℝ) ≠ 0)).1 e

omit [MeasurableSingletonClass S] in
theorem mem_typeClass {P : Measure S} {n : ℕ} {x : Fin n → S} :
    x ∈ typeClass P n ↔ seqType x = P := by
  simp [typeClass]

omit [MeasurableSingletonClass S] in
theorem mem_typeSet {P : Measure S} {n : ℕ} : P ∈ typeSet n ↔ ∃ x : Fin n → S, seqType x = P := by
  simp [typeSet]

omit [MeasurableSingletonClass S] in
theorem card_typeSet_le (n : ℕ) : #(typeSet (S := S) n) ≤ (n + 1) ^ Fintype.card S := by
  classical
  let F : (S → ℕ) → Measure S := fun k => ∑ s, ENNReal.ofReal (k s / n) • Measure.dirac s
  have hsub : typeSet (S := S) n ⊆ (Fintype.piFinset fun _ : S => range (n + 1)).image F := by
    intro P hP
    obtain ⟨x, rfl⟩ := mem_typeSet.1 hP
    exact mem_image.2 ⟨typeCount x, Fintype.mem_piFinset.2 fun s =>
      mem_range.2 (Nat.lt_succ_of_le (typeCount_le x s)), rfl⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  simp

omit [Fintype S] [DecidableEq S] [MeasurableSingletonClass S] in
theorem absolutelyContinuous_iff_singleton [Countable S] {ν ρ : Measure S} :
    ν ≪ ρ ↔ ∀ s, ρ {s} = 0 → ν {s} = 0 := by
  refine ⟨fun h s hs => h hs, fun h A hA => ?_⟩
  rw [← Set.biUnion_of_singleton A, measure_biUnion_null_iff A.to_countable] at hA ⊢
  exact fun s hs => h s (hA s hs)

omit [Fintype S] [DecidableEq S] in
theorem PMF.toMeasure_real_singleton (q : PMF S) (s : S) : q.toMeasure.real {s} = (q s).toReal := by
  rw [measureReal_def, q.toMeasure_apply_singleton s (measurableSet_singleton s)]

theorem seqType_absolutelyContinuous_iff {n : ℕ} (x : Fin n → S) (q : PMF S) :
    seqType x ≪ q.toMeasure ↔ ∀ i, q (x i) ≠ 0 := by
  rw [absolutelyContinuous_iff_singleton]
  simp only [q.toMeasure_apply_singleton _ (measurableSet_singleton _), seqType_apply_singleton,
    ENNReal.ofReal_eq_zero]
  refine ⟨fun h i hi => ?_, fun h s hs => ?_⟩
  · have h1 := h _ hi
    have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Fin.pos i)
    have hc : 0 < typeCount x (x i) := card_pos.2 ⟨i, by simp⟩
    rw [div_nonpos_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd h1.2 (not_le.2 hn)
    · exact absurd h1.1 (not_le.2 (Nat.cast_pos.2 hc))
  · have : typeCount x s = 0 := card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ e => h i (e ▸ hs))
    simp [this]

omit [Fintype S] [DecidableEq S] [MeasurableSingletonClass S] in
private lemma negMulLog_add_mul_log_div {p q : ℝ} (hpq : q = 0 → p = 0) :
    Real.negMulLog p + p * Real.log (p / q) = -(p * Real.log q) := by
  by_cases hp : p = 0
  · simp [hp]
  have hq : q ≠ 0 := fun h => hp (hpq h)
  rw [Real.negMulLog, Real.log_div hp hq]
  ring

omit [DecidableEq S] [MeasurableSingletonClass S] in
theorem measureEntropy_add_klDiv {ν ρ : Measure S} [IsFiniteMeasure ρ] (h : ν ≪ ρ) :
    measureEntropy ν + klDiv ν ρ = -∑ s, ν.real {s} * Real.log (ρ.real {s}) := by
  rw [measureEntropy, klDiv, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun s _ => negMulLog_add_mul_log_div fun hs => ?_
  rw [measureReal_eq_zero_iff] at hs
  simp [Measure.real, h hs]

omit [DecidableEq S] [MeasurableSingletonClass S] in
theorem klDiv_eq_sum_sub {ν ρ : Measure S} [IsFiniteMeasure ρ] (h : ν ≪ ρ) :
    klDiv ν ρ = ∑ s, (ν.real {s} * Real.log (ν.real {s}) - ν.real {s} * Real.log (ρ.real {s})) := by
  have e := measureEntropy_add_klDiv h
  rw [measureEntropy] at e
  rw [sum_sub_distrib]
  simp only [Real.negMulLog, neg_mul, sum_neg_distrib] at e
  linarith

theorem iidProb_eq_exp {n : ℕ} (q : PMF S) (x : Fin n → S) (h : seqType x ≪ q.toMeasure) :
    iidProb q x
      = Real.exp (-(n * (measureEntropy (seqType x) + klDiv (seqType x) q.toMeasure))) := by
  have hq := (seqType_absolutelyContinuous_iff x q).1 h
  rw [iidProb, prod_comp_eq_exp x (fun s => (q s).toReal)
    (fun i => ENNReal.toReal_pos (hq i) (q.apply_ne_top _)), measureEntropy_add_klDiv h]
  congr 1
  simp only [seqType_real, PMF.toMeasure_real_singleton, mul_neg, neg_neg, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Nat.le_zero.1 (typeCount_le x s)]
  field_simp

theorem iidProb_eq_zero {n : ℕ} (q : PMF S) (x : Fin n → S) (h : ¬ seqType x ≪ q.toMeasure) :
    iidProb q x = 0 := by
  rw [seqType_absolutelyContinuous_iff] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact prod_eq_zero (mem_univ i) (by simp [hi])

theorem prod_seqType_real {n : ℕ} (x : Fin n → S) :
    ∏ i, (seqType x).real {x i} = Real.exp (-(n * measureEntropy (seqType x))) := by
  have hpos : ∀ i, 0 < (seqType x).real {x i} := fun i => by
    rw [seqType_real]
    have : 0 < typeCount x (x i) := card_pos.2 ⟨i, by simp⟩
    have : (0 : ℝ) < n := Nat.cast_pos.2 (Fin.pos i)
    positivity
  rw [prod_comp_eq_exp x (fun s => (seqType x).real {s}) hpos]
  congr 1
  rw [measureEntropy, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun s _ => ?_
  simp only [seqType_real, Real.negMulLog]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Nat.le_zero.1 (typeCount_le x s)]
  field_simp

theorem sum_seqType_real {n : ℕ} (hn : 0 < n) (x : Fin n → S) : ∑ s, (seqType x).real {s} = 1 := by
  have := isProbabilityMeasure_seqType hn x
  exact sum_measureReal_singleton_eq_one _

omit [MeasurableSingletonClass S] in
theorem sum_typeSet_sum_typeClass {n : ℕ} (f : (Fin n → S) → ℝ) :
    ∑ P ∈ typeSet n, ∑ x ∈ typeClass P n, f x = ∑ x, f x := by
  classical
  exact sum_fiberwise_of_maps_to (s := univ) (g := seqType) (fun x _ => mem_typeSet.2 ⟨x, rfl⟩) f

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem card_mul_prod_pow_le {n : ℕ} (x y : Fin n → S) :
    #{z : Fin n → S | typeCount z = typeCount y} * ∏ s, typeCount x s ^ typeCount y s
      ≤ #{z : Fin n → S | typeCount z = typeCount x} * ∏ s, typeCount x s ^ typeCount x s := by
  have hA := card_typeCount_eq_mul_prod_factorial n (typeCount y) (sum_typeCount y)
  have hB := card_typeCount_eq_mul_prod_factorial n (typeCount x) (sum_typeCount x)
  set A := #{z : Fin n → S | typeCount z = typeCount y}
  set B := #{z : Fin n → S | typeCount z = typeCount x}
  set k := typeCount x
  set j := typeCount y
  have hc : 0 < (∏ s, (j s).factorial) * ∏ s, (k s).factorial :=
    Nat.mul_pos (prod_pos fun s _ => Nat.factorial_pos (j s))
      (prod_pos fun s _ => Nat.factorial_pos (k s))
  refine le_of_mul_le_mul_right ?_ hc
  calc A * (∏ s, k s ^ j s) * ((∏ s, (j s).factorial) * ∏ s, (k s).factorial)
      = (A * ∏ s, (j s).factorial) * ∏ s, ((k s).factorial * k s ^ j s) := by
        rw [prod_mul_distrib]
        ring
    _ ≤ (A * ∏ s, (j s).factorial) * ∏ s, ((j s).factorial * k s ^ k s) := by
        exact Nat.mul_le_mul_left _ (prod_le_prod fun s _ => factorial_mul_pow_le (j s) (k s))
    _ = (B * ∏ s, (k s).factorial) * ∏ s, ((j s).factorial * k s ^ k s) := by rw [hA, hB]
    _ = B * (∏ s, k s ^ k s) * ((∏ s, (j s).factorial) * ∏ s, (k s).factorial) := by
        rw [prod_mul_distrib]
        ring

private lemma typeClass_seqType {n : ℕ} (x : Fin n → S) :
    typeClass (seqType x) n = ({z : Fin n → S | typeCount z = typeCount x} : Finset _) := by
  ext z
  simp only [mem_typeClass, mem_filter, mem_univ, true_and]
  exact seqType_eq_seqType_iff z x

private lemma sum_typeClass_prod_le {n : ℕ} (x y : Fin n → S) :
    ∑ z ∈ typeClass (seqType y) n, ∏ i, (seqType x).real {z i}
      ≤ #(typeClass (seqType x) n) * Real.exp (-(n * measureEntropy (seqType x))) := by
  have hz : ∀ z ∈ typeClass (seqType y) n, ∏ i, (seqType x).real {z i}
      = ∏ s, ((typeCount x s : ℝ) / n) ^ typeCount y s := fun z hz => by
    rw [prod_comp_eq_prod_pow z (fun s => (seqType x).real {s}),
      (seqType_eq_seqType_iff z y).1 (mem_typeClass.1 hz)]
    simp only [seqType_real]
  have hn : ∀ m : S → ℕ, ∑ s, m s = n → ∏ s, ((typeCount x s : ℝ) / n) ^ m s
      = (∏ s, typeCount x s ^ m s : ℕ) / (n : ℝ) ^ n := fun m hm => by
    rw [prod_congr rfl fun s _ => div_pow _ _ _, prod_div_distrib, prod_pow_eq_pow_sum, hm]
    push_cast
    rfl
  rw [sum_congr rfl hz, sum_const, nsmul_eq_mul, ← prod_seqType_real x,
    prod_comp_eq_prod_pow x (fun s => (seqType x).real {s})]
  simp only [seqType_real]
  rw [hn _ (sum_typeCount y), hn _ (sum_typeCount x), typeClass_seqType, typeClass_seqType,
    ← mul_div_assoc, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_mul_prod_pow_le x y) (by positivity)

theorem card_typeClass_le (P : Measure S) (n : ℕ) :
    (#(typeClass P n) : ℝ) ≤ Real.exp (n * measureEntropy P) := by
  rcases (typeClass P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h, card_empty, Nat.cast_zero]
    exact (Real.exp_pos _).le
  obtain rfl := mem_typeClass.1 hx
  have h1 : ∑ y : Fin n → S, ∏ i, (seqType x).real {y i} = 1 :=
    sum_prod (fun _ s => (seqType x).real {s}) fun i => sum_seqType_real (Fin.pos i) x
  have hT : ∀ y ∈ typeClass (seqType x) n,
      ∏ i, (seqType x).real {y i} = Real.exp (-(n * measureEntropy (seqType x))) := fun y hy => by
    rw [← mem_typeClass.1 hy]
    exact prod_seqType_real y
  have hle : ∑ y ∈ typeClass (seqType x) n, ∏ i, (seqType x).real {y i}
      ≤ ∑ y : Fin n → S, ∏ i, (seqType x).real {y i} :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ =>
      prod_nonneg fun i _ => measureReal_nonneg
  rw [sum_congr rfl hT, sum_const, nsmul_eq_mul, h1, Real.exp_neg, ← div_eq_mul_inv,
    div_le_one (Real.exp_pos _)] at hle
  exact hle

theorem card_typeClass_ge {P : Measure S} {n : ℕ} (hP : P ∈ typeSet n) :
    Real.exp (n * measureEntropy P) / (n + 1) ^ Fintype.card S ≤ #(typeClass P n) := by
  obtain ⟨x, rfl⟩ := mem_typeSet.1 hP
  have h1 : ∑ y : Fin n → S, ∏ i, (seqType x).real {y i} = 1 :=
    sum_prod (fun _ s => (seqType x).real {s}) fun i => sum_seqType_real (Fin.pos i) x
  rw [← sum_typeSet_sum_typeClass] at h1
  have hle : (1 : ℝ) ≤ #(typeSet (S := S) n) *
      (#(typeClass (seqType x) n) * Real.exp (-(n * measureEntropy (seqType x)))) := by
    rw [← h1, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun P hP => ?_
    obtain ⟨y, rfl⟩ := mem_typeSet.1 hP
    exact sum_typeClass_prod_le x y
  have hc : (#(typeSet (S := S) n) : ℝ) ≤ (n + 1) ^ Fintype.card S := by
    exact_mod_cast card_typeSet_le n
  have hpos : (0 : ℝ) < (n + 1) ^ Fintype.card S := by positivity
  rw [div_le_iff₀ hpos]
  have := hle.trans (mul_le_mul_of_nonneg_right hc (by positivity))
  rw [Real.exp_neg] at this
  have he := Real.exp_pos (n * measureEntropy (seqType x))
  calc Real.exp (n * measureEntropy (seqType x))
      ≤ Real.exp (n * measureEntropy (seqType x)) * ((n + 1) ^ Fintype.card S *
        (#(typeClass (seqType x) n) * (Real.exp (n * measureEntropy (seqType x)))⁻¹)) :=
        le_mul_of_one_le_right he.le this
    _ = #(typeClass (seqType x) n) * (n + 1) ^ Fintype.card S := by
        field_simp

private lemma sum_iidProb_typeClass_eq {P : Measure S} {n : ℕ} (q : PMF S) (h : P ≪ q.toMeasure) :
    ∑ x ∈ typeClass P n, iidProb q x
      = #(typeClass P n) * Real.exp (-(n * measureEntropy P))
        * Real.exp (-(n * klDiv P q.toMeasure)) := by
  rw [mul_assoc, ← Real.exp_add, ← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun x hx => ?_
  obtain rfl := mem_typeClass.1 hx
  rw [iidProb_eq_exp q x h]
  ring_nf

theorem sum_iidProb_typeClass_le (q : PMF S) (P : Measure S) (n : ℕ) :
    ∑ x ∈ typeClass P n, iidProb q x ≤ Real.exp (-(n * klDiv P q.toMeasure)) := by
  by_cases h : P ≪ q.toMeasure
  · rw [sum_iidProb_typeClass_eq q h]
    refine mul_le_of_le_one_left (Real.exp_pos _).le ?_
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact card_typeClass_le P n
  · rw [sum_eq_zero fun x hx => iidProb_eq_zero q x ((mem_typeClass.1 hx).symm ▸ h)]
    exact (Real.exp_pos _).le

theorem le_sum_iidProb_typeClass (q : PMF S) {P : Measure S} {n : ℕ} (hP : P ∈ typeSet n)
    (h : P ≪ q.toMeasure) :
    Real.exp (-(n * klDiv P q.toMeasure)) / (n + 1) ^ Fintype.card S
      ≤ ∑ x ∈ typeClass P n, iidProb q x := by
  rw [sum_iidProb_typeClass_eq q h]
  have hc := card_typeClass_ge hP
  have he := Real.exp_pos (-(n * measureEntropy P))
  calc Real.exp (-(n * klDiv P q.toMeasure)) / (n + 1) ^ Fintype.card S
      = Real.exp (n * measureEntropy P) / (n + 1) ^ Fintype.card S
        * Real.exp (-(n * measureEntropy P)) * Real.exp (-(n * klDiv P q.toMeasure)) := by
        have e : Real.exp (-(n * measureEntropy P)) * Real.exp (n * measureEntropy P) = 1 := by
          rw [← Real.exp_add]
          simp
        rw [div_eq_mul_inv, div_eq_mul_inv]
        linear_combination (-(Real.exp (-(n * klDiv P q.toMeasure)) *
          ((n + 1 : ℝ) ^ Fintype.card S)⁻¹)) * e
    _ ≤ _ := by gcongr

omit [DecidableEq S] [MeasurableSingletonClass S] in
theorem tendsto_klDiv {ν : ℕ → Measure S} {ρ : Measure S} [IsFiniteMeasure ρ] {w : S → ℝ}
    (hν : ∀ n, ν n ≪ ρ) (h : ∀ s, Tendsto (fun n => (ν n).real {s}) atTop (𝓝 (w s))) :
    Tendsto (fun n => klDiv (ν n) ρ) atTop
      (𝓝 (∑ s, (w s * Real.log (w s) - w s * Real.log (ρ.real {s})))) := by
  simp_rw [klDiv_eq_sum_sub (hν _)]
  exact tendsto_finsetSum _ fun s _ =>
    ((Real.continuous_mul_log.tendsto _).comp (h s)).sub ((h s).mul_const _)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem exists_seq_typeCount_tendsto (w : S → ℝ) (hw0 : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1) :
    ∃ x : (n : ℕ) → Fin n → S, (∀ n s, w s = 0 → typeCount (x n) s = 0) ∧
      ∀ s, Tendsto (fun n => (typeCount (x n) s : ℝ) / n) atTop (𝓝 (w s)) := by
  obtain ⟨s₀, hs₀⟩ : ∃ s, 0 < w s := by
    by_contra h
    push Not at h
    have : ∑ s, w s ≤ 0 := sum_nonpos fun s _ => h s
    linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ → ℕ, ∀ n, R n = ∑ t ∈ univ.erase s₀, ⌊w t * n⌋₊ := ⟨_, fun _ => rfl⟩
  have hR : ∀ n, R n ≤ n := fun n => by
    have : (R n : ℝ) ≤ n :=
      calc (R n : ℝ) = ∑ t ∈ univ.erase s₀, (⌊w t * n⌋₊ : ℝ) := by rw [hRdef, Nat.cast_sum]
        _ ≤ ∑ t ∈ univ.erase s₀, w t * n :=
          sum_le_sum fun t _ => Nat.floor_le (mul_nonneg (hw0 t) (Nat.cast_nonneg n))
        _ ≤ ∑ t, w t * n := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun t _ _ =>
          mul_nonneg (hw0 t) (Nat.cast_nonneg n)
        _ = n := by rw [← sum_mul, hw1, one_mul]
    exact_mod_cast this
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ → S → ℕ, ∀ n s, k n s = if s = s₀ then n - R n else ⌊w s * n⌋₊ :=
    ⟨_, fun _ _ => rfl⟩
  have hk0 : ∀ n, k n s₀ = n - R n := fun n => by simp [hkdef]
  have hk1 : ∀ n s, s ≠ s₀ → k n s = ⌊w s * n⌋₊ := fun n s hs => by simp [hkdef, hs]
  have hk : ∀ n, ∑ s, k n s = n := fun n => by
    rw [← add_sum_erase _ _ (mem_univ s₀), sum_congr rfl fun t ht => hk1 n t (ne_of_mem_erase ht),
      hk0, ← hRdef]
    have := hR n
    omega
  choose x hx using fun n => exists_typeCount_eq n (k n) (hk n)
  refine ⟨x, fun n s hs => ?_, fun s => ?_⟩
  · have : s ≠ s₀ := fun h => by rw [h] at hs; linarith
    rw [hx n, hk1 n s this, hs, zero_mul, Nat.floor_zero]
  have hfl : ∀ t, Tendsto (fun n : ℕ => (⌊w t * n⌋₊ : ℝ) / n) atTop (𝓝 (w t)) := fun t =>
    (tendsto_nat_floor_mul_div_atTop (hw0 t)).comp tendsto_natCast_atTop_atTop
  simp_rw [hx]
  by_cases hs : s = s₀
  · subst hs
    have hsum : Tendsto (fun n : ℕ => 1 - ∑ t ∈ univ.erase s, (⌊w t * n⌋₊ : ℝ) / n) atTop
        (𝓝 (1 - ∑ t ∈ univ.erase s, w t)) :=
      tendsto_const_nhds.sub (tendsto_finsetSum _ fun t _ => hfl t)
    have hlim : 1 - ∑ t ∈ univ.erase s, w t = w s := by
      rw [← hw1, ← add_sum_erase _ _ (mem_univ s)]
      ring
    rw [hlim] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [hk0, Nat.cast_sub (hR n), hRdef, Nat.cast_sum, ← sum_div, sub_div, div_self hn']
  · refine (hfl s).congr fun n => ?_
    rw [hk1 n s hs]

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem eventually_pow_le_exp (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ k ≤ Real.exp (n * η) := by
  have hr : 1 < Real.exp (η / 2) := Real.one_lt_exp_iff.2 (by linarith)
  have h := ((tendsto_pow_const_div_const_pow_of_one_lt k hr).comp
    (tendsto_add_atTop_nat 1)).eventually
    (gt_mem_nhds zero_lt_one)
  filter_upwards [h, eventually_ge_atTop 1] with n hn h1
  simp only [Function.comp, Nat.cast_add, Nat.cast_one] at hn
  rw [div_lt_one (by positivity), ← Real.exp_nat_mul] at hn
  refine hn.le.trans (Real.exp_le_exp.2 ?_)
  have : (1 : ℝ) ≤ n := by exact_mod_cast h1
  push_cast
  nlinarith

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem le_neg_log_div_of_le_exp {n : ℕ} (hn : 0 < n) {y c : ℝ} (hy : 0 < y)
    (h : y ≤ Real.exp (-(n * c))) : c ≤ -Real.log y / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [le_div_iff₀ hn']
  have := (Real.log_le_iff_le_exp hy).2 h
  linarith

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem neg_log_div_le_of_exp_le {n : ℕ} (hn : 0 < n) {y c : ℝ}
    (h : Real.exp (-(n * c)) ≤ y) : -Real.log y / n ≤ c := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [div_le_iff₀ hn']
  have := (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le h)).2 h
  linarith

end Meat
