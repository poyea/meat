import Meat.Shannon.Average
import Meat.Shannon.Types

open Finset

namespace Meat

section Variance

variable {B : Type*} [Fintype B] {n : ℕ}

theorem sum_prod_mul_sq_sum (w g : Fin n → B → ℝ) (h1 : ∀ i, ∑ b, w i b = 1)
    (h0 : ∀ i, ∑ b, w i b * g i b = 0) :
    ∑ y : Fin n → B, (∏ i, w i (y i)) * (∑ i, g i (y i)) ^ 2 =
      ∑ i, ∑ b, w i b * g i b ^ 2 := by
  have hij : ∀ i j : Fin n, ∑ y : Fin n → B, (∏ k, w k (y k)) * (g i (y i) * g j (y j)) =
      if i = j then ∑ b, w i b * g i b ^ 2 else 0 := by
    intro i j
    have h := sum_prod_mul_prod w fun k b =>
      (if k = i then g i b else 1) * (if k = j then g j b else 1)
    simp only [prod_mul_distrib, prod_ite_eq', mem_univ, ite_true] at h
    rw [h]
    split_ifs with hij
    · subst hij
      rw [prod_eq_single i (fun k _ hk => by simp [hk, h1]) (by simp)]
      simp [sq]
    · exact prod_eq_zero (mem_univ i) (by simp [hij, h0])
  simp_rw [sq, sum_mul_sum, mul_sum]
  rw [sum_comm]
  rw [sum_congr rfl fun i _ => by rw [sum_comm]]
  simp [hij, ← sq]

end Variance

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

noncomputable def strongTypicalSet (r : A → ℝ) (n : ℕ) (ε : ℝ) : Finset (Fin n → A) := by
  classical
  exact univ.filter fun x => ∀ a, |(typeCount x a : ℝ) / n - r a| ≤ ε

theorem mem_strongTypicalSet {r : A → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → A} :
    x ∈ strongTypicalSet r n ε ↔ ∀ a, |(typeCount x a : ℝ) / n - r a| ≤ ε := by
  classical
  simp [strongTypicalSet]

theorem abs_avg_sub_le_of_mem_strongTypicalSet {r : A → ℝ} {n : ℕ} {ε : ℝ} (hn : 0 < n)
    {x : Fin n → A} (hx : x ∈ strongTypicalSet r n ε) (f : A → ℝ) :
    |(∑ i, f (x i)) / n - ∑ a, r a * f a| ≤ ε * ∑ a, |f a| := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [sum_comp_eq_sum_typeCount_mul, sum_div, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
  rw [show (typeCount x a : ℝ) * f a / n - r a * f a = ((typeCount x a : ℝ) / n - r a) * f a by
    field_simp, abs_mul]
  exact mul_le_mul_of_nonneg_right ((mem_strongTypicalSet.1 hx) a) (abs_nonneg _)

omit [Fintype A] [Fintype B] in
private lemma count_pair {n : ℕ} (x : Fin n → A) (y : Fin n → B) (a : A) (b : B) :
    (typeCount (fun i => (x i, y i)) (a, b) : ℝ) =
      ∑ i, (if x i = a then 1 else 0) * (if y i = b then 1 else 0) := by
  rw [typeCount, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  by_cases ha : x i = a <;> by_cases hb : y i = b <;> simp [ha, hb]

omit [Fintype A] in
private lemma count_one {n : ℕ} (x : Fin n → A) (a : A) :
    (typeCount x a : ℝ) = ∑ i, if x i = a then 1 else 0 := by
  rw [typeCount, card_filter, Nat.cast_sum]
  exact sum_congr rfl fun i _ => by split_ifs <;> simp

theorem sum_not_mem_strongTypicalSet_le (W : A → PMF B) (r : A → ℝ) {δ η : ℝ} (hη : 0 < η)
    {n : ℕ} (hn : 0 < n) {x : Fin n → A} (hx : x ∈ strongTypicalSet r n δ) :
    ∑ y ∈ univ.filter (fun y : Fin n → B => (fun i => (x i, y i)) ∉
        strongTypicalSet (fun ab : A × B => r ab.1 * (W ab.1 ab.2).toReal) n (δ + η)),
      ∏ i, (W (x i) (y i)).toReal ≤
      Fintype.card A * Fintype.card B / (4 * n * η ^ 2) := by
  classical
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set w : Fin n → B → ℝ := fun i b => (W (x i) b).toReal
  have hw1 : ∀ i, ∑ b, w i b = 1 := fun i => sum_toReal_pmf_eq_one (W (x i))
  have hw0 : ∀ i b, 0 ≤ w i b := fun _ _ => ENNReal.toReal_nonneg
  set P : (Fin n → B) → ℝ := fun y => ∏ i, w i (y i)
  have hP0 : ∀ y, 0 ≤ P y := fun y => prod_nonneg fun i _ => hw0 i _
  set g : A → B → Fin n → B → ℝ := fun a b i b' =>
    (if x i = a then 1 else 0) * ((if b' = b then 1 else 0) - (W a b).toReal)
  set Sab : A → B → (Fin n → B) → ℝ := fun a b y => ∑ i, g a b i (y i)
  have hg0 : ∀ a b i, ∑ b', w i b' * g a b i b' = 0 := fun a b i => by
    by_cases hxa : x i = a
    · simp only [g, w, hxa, ite_true, one_mul, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib,
        sum_ite_eq', mem_univ, ← sum_mul, sum_toReal_pmf_eq_one]
      ring
    · simp [g, hxa]
  have hvar : ∀ a b, ∑ y, P y * Sab a b y ^ 2 ≤ n / 4 := fun a b => by
    rw [sum_prod_mul_sq_sum w (g a b) hw1 (hg0 a b)]
    calc ∑ i, ∑ b', w i b' * g a b i b' ^ 2 ≤ ∑ _i : Fin n, (1 / 4 : ℝ) :=
          sum_le_sum fun i _ => by
            by_cases hxa : x i = a
            · have e : ∑ b', w i b' * g a b i b' ^ 2 =
                  (W a b).toReal * (1 - (W a b).toReal) := by
                simp only [g, w, hxa, ite_true, one_mul]
                have h1 := hw1 i
                simp only [w, hxa] at h1
                have : ∀ b', (W a b').toReal * ((if b' = b then 1 else 0) - (W a b).toReal) ^ 2 =
                    (W a b').toReal * (W a b).toReal ^ 2 + (if b' = b then
                      (W a b).toReal * (1 - 2 * (W a b).toReal) else 0) := fun b' => by
                  split_ifs with hb
                  · subst hb
                    ring
                  · ring
                rw [sum_congr rfl fun b' _ => this b', sum_add_distrib, ← sum_mul, h1,
                  sum_ite_eq']
                simp only [mem_univ, ite_true]
                ring
              rw [e]
              nlinarith [sq_nonneg ((W a b).toReal - 1 / 2)]
            · simp [g, hxa]
      _ = n / 4 := by simp [sum_const, card_univ, Fintype.card_fin]; ring
  have hbad : ∀ y, (fun i => (x i, y i)) ∉
      strongTypicalSet (fun ab : A × B => r ab.1 * (W ab.1 ab.2).toReal) n (δ + η) →
      1 ≤ ∑ ab : A × B, Sab ab.1 ab.2 y ^ 2 / (n * η) ^ 2 := by
    intro y hy
    rw [mem_strongTypicalSet] at hy
    push Not at hy
    obtain ⟨⟨a, b⟩, hab⟩ := hy
    have hS : Sab a b y = (typeCount (fun i => (x i, y i)) (a, b) : ℝ) -
        (typeCount x a : ℝ) * (W a b).toReal := by
      change ∑ i, g a b i (y i) = _
      rw [count_pair, count_one, sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      by_cases hxa : x i = a <;> by_cases hyb : y i = b <;> simp [g, hxa, hyb]
    have hxa := (mem_strongTypicalSet.1 hx) a
    have hW0 : 0 ≤ (W a b).toReal := ENNReal.toReal_nonneg
    have hW1 : (W a b).toReal ≤ 1 := by
      have := hw1 ⟨0, hn⟩
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by rw [ENNReal.ofReal_one]; exact PMF.coe_le_one _ _)
    have hdev : n * η < |Sab a b y| := by
      have e1 : (typeCount (fun i => (x i, y i)) (a, b) : ℝ) / n - r a * (W a b).toReal =
          Sab a b y / n + ((typeCount x a : ℝ) / n - r a) * (W a b).toReal := by
        rw [hS]
        field_simp
        ring
      have e2 : |((typeCount x a : ℝ) / n - r a) * (W a b).toReal| ≤ δ := by
        rw [abs_mul, abs_of_nonneg hW0]
        nlinarith [abs_nonneg ((typeCount x a : ℝ) / n - r a)]
      have e3 : δ + η < |Sab a b y / n| + δ := by
        calc δ + η < |(typeCount (fun i => (x i, y i)) (a, b) : ℝ) / n -
              r a * (W a b).toReal| := hab
          _ ≤ |Sab a b y / n| + |((typeCount x a : ℝ) / n - r a) * (W a b).toReal| := by
              rw [e1]
              exact abs_add_le _ _
          _ ≤ _ := by linarith
      rw [abs_div, abs_of_pos hn'] at e3
      have e4 : η < |Sab a b y| / n := by linarith
      rw [lt_div_iff₀ hn'] at e4
      linarith
    have hsq : (n * η) ^ 2 < Sab a b y ^ 2 := by
      rw [← sq_abs (Sab a b y)]
      exact pow_lt_pow_left₀ hdev (by positivity) two_ne_zero
    calc (1 : ℝ) ≤ Sab a b y ^ 2 / (n * η) ^ 2 := by
          rw [le_div_iff₀ (by positivity), one_mul]
          exact hsq.le
      _ ≤ _ := single_le_sum (f := fun ab : A × B => Sab ab.1 ab.2 y ^ 2 / (n * η) ^ 2)
          (fun _ _ => by positivity) (mem_univ (a, b))
  calc ∑ y ∈ univ.filter (fun y : Fin n → B => (fun i => (x i, y i)) ∉
        strongTypicalSet (fun ab : A × B => r ab.1 * (W ab.1 ab.2).toReal) n (δ + η)), P y
      ≤ ∑ y ∈ univ.filter (fun y : Fin n → B => (fun i => (x i, y i)) ∉
        strongTypicalSet (fun ab : A × B => r ab.1 * (W ab.1 ab.2).toReal) n (δ + η)),
          P y * ∑ ab : A × B, Sab ab.1 ab.2 y ^ 2 / (n * η) ^ 2 :=
        sum_le_sum fun y hy => le_mul_of_one_le_right (hP0 y) (hbad y (mem_filter.1 hy).2)
    _ ≤ ∑ y, P y * ∑ ab : A × B, Sab ab.1 ab.2 y ^ 2 / (n * η) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun y _ _ =>
          mul_nonneg (hP0 y) (sum_nonneg fun _ _ => by positivity)
    _ = ∑ ab : A × B, (∑ y, P y * Sab ab.1 ab.2 y ^ 2) / (n * η) ^ 2 := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun ab _ => ?_
        rw [sum_div]
        exact sum_congr rfl fun y _ => by ring
    _ ≤ ∑ _ab : A × B, (n / 4) / (n * η) ^ 2 :=
        sum_le_sum fun ab _ => div_le_div_of_nonneg_right (hvar ab.1 ab.2) (by positivity)
    _ = Fintype.card A * Fintype.card B / (4 * n * η ^ 2) := by
        rw [sum_const, card_univ, Fintype.card_prod, nsmul_eq_mul]
        push_cast
        field_simp

theorem markov_lemma {U : Type*} [Fintype U] [DecidableEq U] (W : A → PMF B)
    (r : U × A → ℝ) {δ η : ℝ} (hη : 0 < η) {n : ℕ} (hn : 0 < n) {ux : Fin n → U × A}
    (hux : ux ∈ strongTypicalSet r n δ) :
    ∑ y ∈ univ.filter (fun y : Fin n → B => (fun i => (ux i, y i)) ∉
        strongTypicalSet (fun t : (U × A) × B => r t.1 * (W t.1.2 t.2).toReal) n (δ + η)),
      ∏ i, (W (ux i).2 (y i)).toReal ≤
      Fintype.card (U × A) * Fintype.card B / (4 * n * η ^ 2) :=
  sum_not_mem_strongTypicalSet_le (fun t : U × A => W t.2) r hη hn hux

end Meat
