import Meat.Channel.Broadcast
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Sort

open Finset
open scoped ENNReal

namespace Meat

namespace BC

variable {A B₁ B₂ : Type*}

def MaxAchievable [Fintype B₁] [Fintype B₂] (W : DMC A (B₁ × B₂)) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k₁ k₂ : ℕ, Real.exp (n * R₁) ≤ k₁ ∧ Real.exp (n * R₂) ≤ k₂ ∧
      ∃ c : BCCode (Fin k₁) (Fin k₂) A B₁ B₂ n, ∀ m, c.errorProb W m ≤ ε

def maxAchievableRegion [Fintype B₁] [Fintype B₂] (W : DMC A (B₁ × B₂)) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ MaxAchievable W R.1 R.2}

section Codes

variable [Fintype B₁] [Fintype B₂]

theorem avgError_le_of_forall_errorProb_le {M₁ M₂ : Type*} [Fintype M₁] [Fintype M₂]
    [DecidableEq M₁] [DecidableEq M₂] {n : ℕ} (c : BCCode M₁ M₂ A B₁ B₂ n)
    (W : DMC A (B₁ × B₂)) {ε : ℝ≥0∞} (h : ∀ m, c.errorProb W m ≤ ε) : c.avgError W ≤ ε := by
  rw [BCCode.avgError]
  refine ENNReal.div_le_of_le_mul ?_
  calc ∑ m, c.errorProb W m ≤ ∑ _m : M₁ × M₂, ε := sum_le_sum fun m _ => h m
    _ = ε * ((Fintype.card M₁ : ℝ≥0∞) * (Fintype.card M₂ : ℝ≥0∞)) := by
        rw [sum_const, card_univ, Fintype.card_prod, nsmul_eq_mul, mul_comm]
        push_cast
        rfl

theorem maxAchievableRegion_subset (W : DMC A (B₁ × B₂)) :
    maxAchievableRegion W ⊆ achievableRegion W := by
  rintro R ⟨h0₁, h0₂, h⟩
  refine ⟨h0₁, h0₂, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hn
  exact ⟨k₁, k₂, hk₁, hk₂, c, avgError_le_of_forall_errorProb_le c W hc⟩

end Codes

private lemma exists_bin {α ι : Type*} [Finite α] [Fintype ι]
    (G : ι → Finset α) {K s : ℕ} (hK : 0 < K) (hs : ∀ j, s ≤ (G j).card)
    (h : (K : ℝ) * Fintype.card ι * (1 - 1 / (K : ℝ)) ^ s < 1) :
    ∃ β : α → Fin K, ∀ i j, ∃ a ∈ G j, β a = i := by
  classical
  have := Fintype.ofFinite α
  by_contra hne
  push Not at hne
  let S : Fin K × ι → Finset (α → Fin K) := fun ij =>
    Fintype.piFinset fun a => if a ∈ G ij.2 then univ.erase ij.1 else univ
  have hcov : (univ : Finset (α → Fin K)) ⊆ univ.biUnion S := by
    intro β _
    obtain ⟨i, j, hij⟩ := hne β
    refine mem_biUnion.2 ⟨(i, j), mem_univ _, Fintype.mem_piFinset.2 fun a => ?_⟩
    by_cases ha : a ∈ G j
    · simp only [ha, ite_true]
      exact mem_erase.2 ⟨hij a ha, mem_univ _⟩
    · simp only [ha, ite_false]
      exact mem_univ _
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hq0 : 0 ≤ 1 - 1 / (K : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact hK1
  have hq1 : 1 - 1 / (K : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (K : ℝ) := by positivity
    linarith
  have hcard : ∀ ij, ((S ij).card : ℝ) ≤ (K : ℝ) ^ Fintype.card α * (1 - 1 / (K : ℝ)) ^ s := by
    intro ij
    have e1 : (S ij).card = ∏ a, (if a ∈ G ij.2 then K - 1 else K) := by
      rw [Fintype.card_piFinset]
      refine prod_congr rfl fun a _ => ?_
      split_ifs
      · rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
      · rw [card_univ, Fintype.card_fin]
    have e2 : (((S ij).card : ℕ) : ℝ) =
        ∏ a, ((K : ℝ) * (if a ∈ G ij.2 then (1 - 1 / (K : ℝ)) else 1)) := by
      rw [e1, Nat.cast_prod]
      refine prod_congr rfl fun a _ => ?_
      split_ifs
      · rw [Nat.cast_sub hK, Nat.cast_one, mul_sub, mul_one, mul_one_div_cancel (by linarith)]
      · rw [mul_one]
    rw [e2, prod_mul_distrib, prod_const, card_univ, prod_ite_mem, univ_inter, prod_const]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 (hs ij.2)) (by positivity)
  have h1 : ((K : ℝ) ^ Fintype.card α) ≤ ∑ ij, ((S ij).card : ℝ) := by
    have := card_le_card hcov
    have h2 := card_biUnion_le (s := univ) (t := S)
    rw [card_univ, Fintype.card_fun, Fintype.card_fin] at this
    have h3 : ((K ^ Fintype.card α : ℕ) : ℝ) ≤ ((∑ ij, (S ij).card : ℕ) : ℝ) := by
      exact_mod_cast this.trans h2
    push_cast at h3
    exact h3
  have h2 : ∑ ij, ((S ij).card : ℝ) ≤
      ∑ _ij : Fin K × ι, (K : ℝ) ^ Fintype.card α * (1 - 1 / (K : ℝ)) ^ s :=
    sum_le_sum fun ij _ => hcard ij
  rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul] at h2
  have hpos : (0 : ℝ) < (K : ℝ) ^ Fintype.card α := by positivity
  have h3 : ((K * Fintype.card ι : ℕ) : ℝ) * ((K : ℝ) ^ Fintype.card α * (1 - 1 / (K : ℝ)) ^ s) =
      (K : ℝ) ^ Fintype.card α * ((K : ℝ) * Fintype.card ι * (1 - 1 / (K : ℝ)) ^ s) := by
    push_cast
    ring
  rw [h3] at h2
  have := h1.trans h2
  nlinarith

private lemma exists_maxCode [Fintype B₁] [Fintype B₂] {k₁ k₂ K g n : ℕ} (W : DMC A (B₁ × B₂))
    (c : BCCode (Fin k₁) (Fin k₂) A B₁ B₂ n) {ε : ℝ≥0∞} (hε0 : 0 < ε) (hεt : ε ≠ ⊤)
    (hc : c.avgError W ≤ ε) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hK : 0 < K) (hg : 0 < g)
    (hgk : 2 * g ≤ k₂ + 1)
    (hbin : (K : ℝ) * g * (1 - 1 / (K : ℝ)) ^ ((k₁ + 1) / 2) < 1) :
    ∃ c' : BCCode (Fin K) (Fin g) A B₁ B₂ n, ∀ m, c'.errorProb W m ≤ 4 * ε := by
  classical
  set e := fun m => c.errorProb W m with he
  set t := 4 * ε
  set Bd := univ.filter fun m : Fin k₁ × Fin k₂ => t < e m
  have hsum : ∑ m, e m ≤ ε * ((k₁ : ℝ≥0∞) * k₂) := by
    have hc' := hc
    rw [BCCode.avgError, Fintype.card_fin, Fintype.card_fin,
      ENNReal.div_le_iff (by positivity) (by finiteness)] at hc'
    exact hc'
  have hBd : Bd.card * 4 ≤ k₁ * k₂ := by
    have h1 : ∑ _m ∈ Bd, t ≤ ∑ m ∈ Bd, e m := sum_le_sum fun m hm => (mem_filter.1 hm).2.le
    have h2 : ∑ m ∈ Bd, e m ≤ ∑ m, e m := sum_le_univ_sum_of_nonneg fun _ => zero_le
    rw [sum_const, nsmul_eq_mul] at h1
    have h3 : ((Bd.card * 4 : ℕ) : ℝ≥0∞) * ε ≤ ((k₁ * k₂ : ℕ) : ℝ≥0∞) * ε := by
      push_cast
      calc (Bd.card : ℝ≥0∞) * 4 * ε = Bd.card * t := by rw [mul_assoc]
        _ ≤ _ := h1.trans (h2.trans hsum)
        _ = _ := mul_comm _ _
    exact_mod_cast (ENNReal.mul_le_mul_iff_left hε0.ne' hεt).1 h3
  set r : Fin k₂ → ℕ := fun b => (univ.filter fun a : Fin k₁ => t < e (a, b)).card
  have hr : ∑ b, r b = Bd.card := by
    simp only [r, Bd, card_filter]
    rw [Fintype.sum_prod_type_right]
  set Gc := univ.filter fun b : Fin k₂ => 2 * r b ≤ k₁
  have hGc : k₂ + 1 ≤ 2 * Gc.card := by
    set Bc := univ.filter fun b : Fin k₂ => ¬ 2 * r b ≤ k₁
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin k₂)))
      (fun b => 2 * r b ≤ k₁)
    rw [card_univ, Fintype.card_fin] at hsplit
    change Gc.card + Bc.card = k₂ at hsplit
    have h1 : ∑ _b ∈ Bc, (k₁ + 1) ≤ ∑ b ∈ Bc, 2 * r b :=
      sum_le_sum fun b hb => by
        have := (mem_filter.1 hb).2
        omega
    have h2 : ∑ b ∈ Bc, 2 * r b ≤ ∑ b, 2 * r b :=
      sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    rw [sum_const, smul_eq_mul, ← mul_sum] at h1
    rw [← mul_sum, ← mul_sum, hr] at h2
    have h3 : Bc.card * (k₁ + 1) * 2 ≤ k₁ * k₂ := by nlinarith
    have h4 : 2 * Bc.card < k₂ := by
      by_contra h5
      push Not at h5
      nlinarith
    omega
  have hle : g ≤ Gc.card := by omega
  let ι : Fin g → Fin k₂ := fun j => Gc.orderEmbOfFin rfl (Fin.castLE hle j)
  have hι : Function.Injective ι :=
    (Gc.orderEmbOfFin rfl).injective.comp (Fin.castLE_injective hle)
  have hιG : ∀ j, ι j ∈ Gc := fun j => Gc.orderEmbOfFin_mem rfl _
  let G : Fin g → Finset (Fin k₁) := fun j => univ.filter fun a => e (a, ι j) ≤ t
  have hG : ∀ j, (k₁ + 1) / 2 ≤ (G j).card := by
    intro j
    have h1 := (mem_filter.1 (hιG j)).2
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin k₁)))
      (fun a => e (a, ι j) ≤ t)
    rw [card_univ, Fintype.card_fin] at hsplit
    have h2 : (univ.filter fun a : Fin k₁ => ¬ e (a, ι j) ≤ t).card = r (ι j) := by
      simp only [r, not_le]
    change (univ.filter fun a : Fin k₁ => e (a, ι j) ≤ t).card + _ = _ at hsplit
    change (k₁ + 1) / 2 ≤ (univ.filter fun a : Fin k₁ => e (a, ι j) ≤ t).card
    omega
  have hbin' : (K : ℝ) * Fintype.card (Fin g) * (1 - 1 / (K : ℝ)) ^ ((k₁ + 1) / 2) < 1 := by
    rwa [Fintype.card_fin]
  obtain ⟨β, hβ⟩ := exists_bin G hK hG hbin'
  choose a ha hb using hβ
  have : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
  refine ⟨⟨fun m => c.enc (a m.1 m.2, ι m.2), fun y => β (c.dec₁ y),
    fun y => Function.invFun ι (c.dec₂ y)⟩, fun m => ?_⟩
  obtain ⟨i, j⟩ := m
  calc _ ≤ ∑ y : Fin n → B₁ × B₂,
        (if (c.dec₁ (fun l => (y l).1), c.dec₂ (fun l => (y l).2)) = (a i j, ι j) then 0
          else DMC.blockProb W (c.enc (a i j, ι j)) y) := by
        refine sum_le_sum fun y _ => ?_
        by_cases hy : (c.dec₁ (fun l => (y l).1), c.dec₂ (fun l => (y l).2)) = (a i j, ι j)
        · rw [Prod.mk.injEq] at hy
          have h' : (β (c.dec₁ (fun l => (y l).1)), Function.invFun ι (c.dec₂ (fun l => (y l).2)))
              = (i, j) := by
            rw [hy.1, hy.2, hb, Function.leftInverse_invFun hι]
          simp only [h', ite_true]
          exact zero_le
        · simp only [hy, ite_false]
          split_ifs
          · exact zero_le
          · exact le_rfl
    _ = e (a i j, ι j) := rfl
    _ ≤ t := (mem_filter.1 (ha i j)).2

private lemma eventually_log_lt {Δ C : ℝ} (hΔ : 0 < Δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Real.log 4 + n * C < Real.exp (n * Δ) / 4 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (8 * (C + Real.log 4) / Δ ^ 2)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ (n : ℝ) * Δ)
  have h1 : 8 * (C + Real.log 4) < n * Δ ^ 2 := by
    have := (div_lt_iff₀ (by positivity)).1 (hN.trans_le hnN)
    linarith
  nlinarith

private lemma eventually_three_mul_le {R R' : ℝ} (h : R' < R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 3 * Real.exp (n * R') ≤ Real.exp (n * R) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.log 3 / (R - R'))
  refine ⟨N, fun n hn => ?_⟩
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : Real.log 3 ≤ n * (R - R') := by
    have := (div_lt_iff₀ (by linarith)).1 (hN.trans_le hnN)
    linarith
  have h2 : 3 ≤ Real.exp (n * (R - R')) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.2 h1
  have h3 : Real.exp (n * R) = Real.exp (n * R') * Real.exp (n * (R - R')) := by
    rw [← Real.exp_add]
    ring_nf
  rw [h3, mul_comm 3]
  exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

private lemma one_sub_inv_pow_le {K : ℕ} (hK : 0 < K) (s : ℕ) :
    (1 - 1 / (K : ℝ)) ^ s ≤ Real.exp (-(s / K)) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hq0 : 0 ≤ 1 - 1 / (K : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact hK1
  have h1 : 1 - 1 / (K : ℝ) ≤ Real.exp (-(1 / K)) := by
    have := Real.add_one_le_exp (-(1 / (K : ℝ)))
    linarith
  calc (1 - 1 / (K : ℝ)) ^ s ≤ Real.exp (-(1 / K)) ^ s := pow_le_pow_left₀ hq0 h1 s
    _ = Real.exp (-(s / K)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

theorem maxAchievable_of_achievable [Fintype B₁] [Fintype B₂] {W : DMC A (B₁ × B₂)}
    {R₁ R₂ R₁' R₂' : ℝ} (h : Achievable W R₁ R₂) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (h0₁ : 0 ≤ R₁') (h0₂ : 0 ≤ R₂') (h₁ : R₁' < R₁ ∨ R₁' = 0) (h₂ : R₂' < R₂ ∨ R₂' = 0) :
    MaxAchievable W R₁' R₂' := by
  intro ε hε
  set ε₀ := min ε 1 / 4 with hε₀
  have hε₀0 : 0 < ε₀ := ENNReal.div_pos (lt_min hε one_pos).ne' (by norm_num)
  have hε₀t : ε₀ ≠ ⊤ := ENNReal.div_ne_top (lt_of_le_of_lt (min_le_right _ _)
    ENNReal.one_lt_top).ne (by norm_num)
  have h4 : 4 * ε₀ ≤ ε := by
    rw [hε₀, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    exact min_le_left _ _
  obtain ⟨N₀, hN₀⟩ := h ε₀ hε₀0
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → R₁' < R₁ →
      Real.log 4 + n * (R₁' + R₂') < Real.exp (n * (R₁ - R₁')) / 4 := by
    by_cases h' : R₁' < R₁
    · obtain ⟨N, hN⟩ := eventually_log_lt (sub_pos.2 h')
      exact ⟨N, fun n hn _ => hN n hn⟩
    · exact ⟨0, fun _ _ h => absurd h h'⟩
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → R₂' < R₂ →
      3 * Real.exp (n * R₂') ≤ Real.exp (n * R₂) := by
    by_cases h' : R₂' < R₂
    · obtain ⟨N, hN⟩ := eventually_three_mul_le h'
      exact ⟨N, fun n hn _ => hN n hn⟩
    · exact ⟨0, fun _ _ h => absurd h h'⟩
  refine ⟨max N₀ (max N₁ N₂), fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN₀ n hn₀
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hX : ∀ R : ℝ, 0 ≤ R → 1 ≤ Real.exp (n * R) := fun R hR =>
    Real.one_le_exp (mul_nonneg hn0 hR)
  have hk₁0 : 0 < k₁ := by
    have := (hX R₁ hR₁).trans hk₁
    exact_mod_cast (zero_lt_one.trans_le this)
  have hk₂0 : 0 < k₂ := by
    have := (hX R₂ hR₂).trans hk₂
    exact_mod_cast (zero_lt_one.trans_le this)
  set K := ⌈Real.exp (n * R₁')⌉₊ with hKdef
  set g := ⌈Real.exp (n * R₂')⌉₊ with hgdef
  have hK : 0 < K := Nat.ceil_pos.2 (Real.exp_pos _)
  have hg : 0 < g := Nat.ceil_pos.2 (Real.exp_pos _)
  have hgk : 2 * g ≤ k₂ + 1 := by
    rcases h₂ with h₂ | h₂
    · have hc1 := Nat.ceil_lt_add_one (Real.exp_pos (n * R₂')).le
      have h3 := hN₂ n hn₂ h₂
      have h5 : ((2 * g : ℕ) : ℝ) < ((k₂ + 2 : ℕ) : ℝ) := by
        push_cast
        have := hX R₂' h0₂
        linarith
      have := Nat.cast_lt.1 h5
      omega
    · have : g = 1 := by
        rw [hgdef, h₂, mul_zero, Real.exp_zero, Nat.ceil_one]
      omega
  have hbin : (K : ℝ) * g * (1 - 1 / (K : ℝ)) ^ ((k₁ + 1) / 2) < 1 := by
    by_cases h₁' : R₁' < R₁
    · set s := (k₁ + 1) / 2
      have hs : (k₁ : ℝ) ≤ 2 * s := by
        have : k₁ ≤ 2 * s := by omega
        exact_mod_cast this
      set X₁ := Real.exp (n * R₁')
      set X₂ := Real.exp (n * R₂')
      have hX₁ := hX R₁' h0₁
      have hX₂ := hX R₂' h0₂
      have hKle : (K : ℝ) ≤ 2 * X₁ := by
        have := Nat.ceil_lt_add_one (Real.exp_pos (n * R₁')).le
        linarith
      have hgle : (g : ℝ) ≤ 2 * X₂ := by
        have := Nat.ceil_lt_add_one (Real.exp_pos (n * R₂')).le
        linarith
      have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
      have hsplit : Real.exp (n * R₁) = X₁ * Real.exp (n * (R₁ - R₁')) := by
        rw [← Real.exp_add]
        ring_nf
      have hsK : Real.exp (n * (R₁ - R₁')) / 4 ≤ s / K := by
        rw [le_div_iff₀ hKpos]
        have hE := (Real.exp_pos (n * (R₁ - R₁'))).le
        nlinarith
      have hpow := one_sub_inv_pow_le hK s
      have hL := hN₁ n hn₁ h₁'
      have h4X : (4 : ℝ) * X₁ * X₂ = Real.exp (Real.log 4 + n * (R₁' + R₂')) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
        simp only [X₁, X₂]
        rw [mul_add, Real.exp_add]
        ring
      calc (K : ℝ) * g * (1 - 1 / (K : ℝ)) ^ s
          ≤ (2 * X₁) * (2 * X₂) * Real.exp (-(s / K)) := by
            gcongr
            exact pow_nonneg (by
              rw [sub_nonneg, div_le_one hKpos]
              exact_mod_cast hK) _
        _ ≤ (2 * X₁) * (2 * X₂) * Real.exp (-(Real.exp (n * (R₁ - R₁')) / 4)) := by
            gcongr
        _ = Real.exp (Real.log 4 + n * (R₁' + R₂') - Real.exp (n * (R₁ - R₁')) / 4) := by
            rw [Real.exp_sub, ← h4X, Real.exp_neg]
            ring
        _ < 1 := by
            rw [Real.exp_lt_one_iff]
            linarith
    · have h0 : R₁' = 0 := h₁.resolve_left h₁'
      have : K = 1 := by
        rw [hKdef, h0, mul_zero, Real.exp_zero, Nat.ceil_one]
      have hs : (k₁ + 1) / 2 ≠ 0 := by omega
      rw [this]
      simp [zero_pow hs]
  obtain ⟨c', hc'⟩ := exists_maxCode W c hε₀0 hε₀t hc hk₁0 hk₂0 hK hg hgk hbin
  exact ⟨K, g, Nat.le_ceil _, Nat.le_ceil _, c', fun m => (hc' m).trans h4⟩

theorem closure_maxAchievableRegion_eq [Fintype B₁] [Fintype B₂] (W : DMC A (B₁ × B₂)) :
    closure (maxAchievableRegion W) = closure (achievableRegion W) := by
  refine le_antisymm (closure_mono (maxAchievableRegion_subset W))
    (closure_minimal (fun R hR => ?_) isClosed_closure)
  obtain ⟨h0₁, h0₂, hR⟩ := hR
  rw [Metric.mem_closure_iff]
  intro δ hδ
  have pick : ∀ x : ℝ, 0 ≤ x → 0 ≤ max 0 (x - δ / 2) ∧
      (max 0 (x - δ / 2) < x ∨ max 0 (x - δ / 2) = 0) ∧ |x - max 0 (x - δ / 2)| < δ := by
    intro x hx
    refine ⟨le_max_left _ _, ?_, ?_⟩
    · rcases le_total (x - δ / 2) 0 with h | h
      · exact Or.inr (max_eq_left h)
      · left
        rw [max_eq_right h]
        linarith
    · rw [abs_lt]
      constructor
      · have : max 0 (x - δ / 2) ≤ x := max_le hx (by linarith)
        linarith
      · have : x - δ / 2 ≤ max 0 (x - δ / 2) := le_max_right _ _
        linarith
  obtain ⟨a₁, b₁, d₁⟩ := pick R.1 h0₁
  obtain ⟨a₂, b₂, d₂⟩ := pick R.2 h0₂
  refine ⟨(max 0 (R.1 - δ / 2), max 0 (R.2 - δ / 2)),
    ⟨a₁, a₂, maxAchievable_of_achievable hR h0₁ h0₂ a₁ a₂ b₁ b₂⟩, ?_⟩
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt d₁ d₂

end BC

end Meat
