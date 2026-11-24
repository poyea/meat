import Meat.Shannon.JointTypes
import Meat.Shannon.MarkovLemma

open MeasureTheory Finset Filter Topology

namespace Meat

section Round

variable {U : Type*} [Fintype U]

theorem exists_round (N : ℕ) (w : U → ℝ) (hw0 : ∀ u, 0 ≤ w u) (hw1 : ∑ u, w u = 1) :
    ∃ k : U → ℕ, ∑ u, k u = N ∧ (∀ u, |(k u : ℝ) - N * w u| ≤ Fintype.card U) ∧
      ∀ u, w u = 0 → k u = 0 := by
  classical
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, 0 < w u₀ := by
    by_contra h
    push Not at h
    have : ∑ u, w u ≤ 0 := sum_nonpos fun u _ => h u
    linarith
  set f : U → ℕ := fun u => ⌊N * w u⌋₊
  have hf : ∀ u, (f u : ℝ) ≤ N * w u := fun u =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hw0 u))
  have hf' : ∀ u, N * w u - 1 < f u := fun u => by
    have := Nat.lt_floor_add_one (N * w u)
    simp only [f]
    linarith
  have hsum : ((∑ u ∈ univ.erase u₀, f u : ℕ) : ℝ) ≤ N := by
    push_cast
    calc ∑ u ∈ univ.erase u₀, (f u : ℝ) ≤ ∑ u ∈ univ.erase u₀, N * w u := sum_le_sum fun u _ => hf u
      _ ≤ ∑ u, N * w u := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun u _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (hw0 u)
      _ = N := by rw [← mul_sum, hw1, mul_one]
  have hsumN : ∑ u ∈ univ.erase u₀, f u ≤ N := by exact_mod_cast hsum
  refine ⟨fun u => if u = u₀ then N - ∑ v ∈ univ.erase u₀, f v else f u, ?_, fun u => ?_,
    fun u hu => ?_⟩
  · have e : ∑ u ∈ univ.erase u₀, (if u = u₀ then N - ∑ v ∈ univ.erase u₀, f v else f u) =
        ∑ u ∈ univ.erase u₀, f u :=
      sum_congr rfl fun u hu => by simp [ne_of_mem_erase hu]
    rw [← add_sum_erase _ _ (mem_univ u₀), e]
    simp only [ite_true]
    omega
  · dsimp only
    by_cases h : u = u₀
    · subst h
      simp only [ite_true]
      rw [Nat.cast_sub hsumN, Nat.cast_sum]
      have hs : ∑ v ∈ univ.erase u, w v = 1 - w u := by
        have := sum_erase_add univ w (mem_univ u)
        linarith
      have e : (N : ℝ) * w u = N - ∑ v ∈ univ.erase u, N * w v := by
        rw [← mul_sum, hs]
        ring
      rw [e]
      have h1 : ∑ v ∈ univ.erase u, ((N : ℝ) * w v - f v) ≤ Fintype.card U := by
        calc ∑ v ∈ univ.erase u, ((N : ℝ) * w v - f v) ≤ ∑ _v ∈ univ.erase u, (1 : ℝ) :=
              sum_le_sum fun v _ => by linarith [hf' v]
          _ ≤ Fintype.card U := by
              rw [sum_const, nsmul_eq_mul, mul_one, card_erase_of_mem (mem_univ u), card_univ]
              exact_mod_cast Nat.sub_le _ _
      have h2 : 0 ≤ ∑ v ∈ univ.erase u, ((N : ℝ) * w v - f v) :=
        sum_nonneg fun v _ => by linarith [hf v]
      rw [sum_sub_distrib] at h1 h2
      rw [abs_le]
      constructor <;> linarith
    · simp only [h, ite_false]
      rw [abs_le]
      have hc : (1 : ℝ) ≤ Fintype.card U := by exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
      constructor <;> linarith [hf u, hf' u]
  · have h : u ≠ u₀ := fun h => by subst h; linarith
    simp [h, f, hu]

end Round

section Exponent

variable {B U : Type*} [Fintype B] [Fintype U]

noncomputable def typeExponent (P : B × U → ℝ) (q : U → ℝ) : ℝ :=
  ∑ z, Real.negMulLog (P z) - ∑ b, Real.negMulLog (∑ u, P (b, u)) +
    ∑ u, (∑ b, P (b, u)) * Real.log (q u)

noncomputable def jointInfo (p : B × U → ℝ) : ℝ :=
  ∑ b, Real.negMulLog (∑ u, p (b, u)) + ∑ u, Real.negMulLog (∑ b, p (b, u)) -
    ∑ z, Real.negMulLog (p z)

theorem continuous_typeExponent (q : U → ℝ) : Continuous fun P : B × U → ℝ => typeExponent P q := by
  unfold typeExponent
  fun_prop

theorem typeExponent_marginal (p : B × U → ℝ) :
    typeExponent p (fun u => ∑ b, p (b, u)) = -jointInfo p := by
  simp only [typeExponent, jointInfo, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

private lemma mul_negMulLog_div {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (n : ℝ) * Real.negMulLog ((k : ℝ) / n) = k * Real.log n - k * Real.log k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [Real.negMulLog, Real.log_div hk' hn']
  field_simp
  ring

private lemma countEntropy_eq (k : U → ℕ) :
    countEntropy k = (∑ u, k u : ℕ) * Real.log (∑ u, k u : ℕ) -
      ∑ u, (k u : ℝ) * Real.log (k u) := by
  rw [countEntropy, Nat.cast_sum, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun u _ => ?_
  rcases Nat.eq_zero_or_pos (k u) with h | h
  · simp [h]
  have hN : (0 : ℝ) < ∑ v, (k v : ℝ) := by
    have := single_le_sum (f := fun v => (k v : ℝ)) (fun _ _ => Nat.cast_nonneg _) (mem_univ u)
    have : (0 : ℝ) < k u := by exact_mod_cast h
    linarith
  rw [← Nat.cast_sum, Real.log_div (by exact_mod_cast hN.ne') (by exact_mod_cast h.ne')]
  push_cast
  ring

theorem exp_countEntropy_mul_prod {n : ℕ} (hn : 0 < n) (k : B → U → ℕ)
    (hk : ∑ b, ∑ u, k b u = n) (q : U → ℝ)
    (hpos : ∀ u, 0 < ∑ b, k b u → 0 < q u) :
    Real.exp (∑ b, countEntropy (k b)) * ∏ u, q u ^ (∑ b, k b u) =
      Real.exp (n * typeExponent (fun z => (k z.1 z.2 : ℝ) / n) q) := by
  have hprod : ∏ u, q u ^ (∑ b, k b u) =
      Real.exp (∑ u, ((∑ b, k b u : ℕ) : ℝ) * Real.log (q u)) := by
    rw [Real.exp_sum]
    refine prod_congr rfl fun u _ => ?_
    rcases Nat.eq_zero_or_pos (∑ b, k b u) with h | h
    · rw [h]
      simp
    · rw [← Real.exp_log (hpos u h), ← Real.exp_nat_mul, Real.exp_log (hpos u h)]
  rw [hprod, ← Real.exp_add]
  congr 1
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [typeExponent, mul_add, mul_sub, mul_sum, Fintype.sum_prod_type]
  simp only [← sum_div, mul_negMulLog_div hn, countEntropy_eq]
  have e1 : ∀ b, (n : ℝ) * Real.negMulLog ((∑ u, (k b u : ℝ)) / n) =
      (∑ u, k b u : ℕ) * Real.log n - (∑ u, k b u : ℕ) * Real.log (∑ u, k b u : ℕ) := fun b => by
    rw [← mul_negMulLog_div hn]
    push_cast
    rfl
  have e2 : ∀ u, (n : ℝ) * ((∑ b, (k b u : ℝ) / n) * Real.log (q u)) =
      ((∑ b, k b u : ℕ) : ℝ) * Real.log (q u) := fun u => by
    rw [← sum_div]
    push_cast
    field_simp
  simp only [e1]
  have hk' : ∑ b, ((∑ u, k b u : ℕ) : ℝ) = n := by exact_mod_cast hk
  simp only [sum_sub_distrib, ← sum_mul, hk']
  push_cast
  have hk2 : ∑ i, ∑ j, (k i j : ℝ) = n := by exact_mod_cast hk
  have hD : ∑ x, (n : ℝ) * ((∑ i, (k i x : ℝ)) / n * Real.log (q x)) =
      ∑ x, (∑ i, (k i x : ℝ)) * Real.log (q x) :=
    sum_congr rfl fun x _ => by field_simp
  rw [hD, hk2]
  ring

end Exponent

section Continuity

variable {B U : Type*} [Fintype B] [Fintype U]

private lemma exists_typeExponent_close (p : B × U → ℝ) (q : U → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ > 0, ∀ P : B × U → ℝ, (∀ z, |P z - p z| ≤ ρ) →
      |typeExponent P q - typeExponent p q| < δ := by
  obtain ⟨ρ, hρ, h⟩ := Metric.continuous_iff.1 (continuous_typeExponent (B := B) q) p δ hδ
  refine ⟨ρ / 2, by positivity, fun P hP => ?_⟩
  have hd : dist P p < ρ := by
    rw [dist_pi_lt_iff hρ]
    intro z
    rw [Real.dist_eq]
    linarith [hP z]
  have := h P hd
  rwa [Real.dist_eq] at this

private lemma exp_bound {n : ℕ} {G I δ m : ℝ} (hG : -I - δ / 2 ≤ G) (hm0 : 0 < m)
    (hm : m ≤ Real.exp (n * (δ / 2))) (hn : (0 : ℝ) ≤ n) :
    Real.exp (-(n * (I + δ))) ≤ Real.exp (n * G) / m := by
  rw [le_div_iff₀ hm0]
  calc Real.exp (-(n * (I + δ))) * m ≤ Real.exp (-(n * (I + δ))) * Real.exp (n * (δ / 2)) :=
        mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = Real.exp (n * (-I - δ / 2)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (n * G) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hG hn)

end Continuity

section Covering

variable {A U : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U] [MeasurableSpace U]
  [MeasurableSingletonClass U]

theorem strong_covering (p : A × U → ℝ) (hp0 : ∀ z, 0 ≤ p z) (q : PMF U)
    (hq : ∀ u, (q u).toReal = ∑ a, p (a, u)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → A,
      (∀ a, |(typeCount x a : ℝ) / n - ∑ u, p (a, u)| ≤ ε) →
      (∀ a, ∑ u, p (a, u) = 0 → typeCount x a = 0) →
      Real.exp (-(n * (jointInfo p + δ))) ≤
        ∑ u ∈ univ.filter (fun u : Fin n → U => (fun i => (x i, u i)) ∈ strongTypicalSet p n δ),
          iidProb q u := by
  classical
  set qr : U → ℝ := fun u => (q u).toReal
  have hqr : qr = fun u => ∑ a, p (a, u) := funext hq
  have hGp : typeExponent p qr = -jointInfo p := by rw [hqr, typeExponent_marginal]
  obtain ⟨ρ, hρ, hcont⟩ := exists_typeExponent_close p qr (half_pos hδ)
  set ε := min ρ δ / 4 with hεdef
  have hε : 0 < ε := by positivity
  have hερ : ε ≤ ρ / 4 := by rw [hεdef]; linarith [min_le_left ρ δ]
  have hεδ : ε ≤ δ / 4 := by rw [hεdef]; linarith [min_le_right ρ δ]
  refine ⟨ε, hε, ?_⟩
  have hU : Nonempty U := ⟨q.support_nonempty.some⟩
  have hcU : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  filter_upwards [eventually_pow_le_exp (Fintype.card U * Fintype.card A) (half_pos hδ),
    eventually_ge_atTop 1, eventually_ge_atTop ⌈(Fintype.card U : ℝ) / ε⌉₊]
    with n hpow hn1 hnε x hx hsupp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  have hUn : (Fintype.card U : ℝ) / n ≤ ε := by
    have h1 : (Fintype.card U : ℝ) / ε ≤ n := (Nat.ceil_le.1 hnε)
    rw [div_le_iff₀ hε] at h1
    rw [div_le_iff₀ hn']
    linarith
  set pA : A → ℝ := fun a => ∑ u, p (a, u)
  have hpA0 : ∀ a, 0 ≤ pA a := fun a => sum_nonneg fun u _ => hp0 _
  set w : A → U → ℝ := fun a u => if pA a = 0 then (Fintype.card U : ℝ)⁻¹ else p (a, u) / pA a
  have hw0 : ∀ a u, 0 ≤ w a u := fun a u => by
    simp only [w]
    split_ifs
    · positivity
    · exact div_nonneg (hp0 _) (hpA0 a)
  have hw1 : ∀ a, ∑ u, w a u = 1 := fun a => by
    simp only [w]
    split_ifs with h
    · rw [sum_const, card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcU.ne']
    · rw [← sum_div]
      exact div_self h
  choose k hk1 hk2 hk3 using fun a => exists_round (typeCount x a) (w a) (hw0 a) (hw1 a)
  have hzero : ∀ a, pA a = 0 → ∀ u, k a u = 0 ∧ p (a, u) = 0 := fun a h u => by
    refine ⟨?_, (sum_eq_zero_iff_of_nonneg fun v _ => hp0 (a, v)).1 h u (mem_univ u)⟩
    have := hk1 a
    rw [hsupp a h] at this
    exact (sum_eq_zero_iff.1 this) u (mem_univ u)
  have hclose : ∀ z : A × U, |(k z.1 z.2 : ℝ) / n - p z| ≤ 2 * ε := by
    rintro ⟨a, u⟩
    by_cases h : pA a = 0
    · obtain ⟨h1, h2⟩ := hzero a h u
      simp only [h1, h2, Nat.cast_zero, zero_div, sub_zero, abs_zero]
      positivity
    · have hpos : 0 < pA a := lt_of_le_of_ne (hpA0 a) (Ne.symm h)
      have hwa : w a u = p (a, u) / pA a := by simp only [w, h, ite_false]
      have hw1' : w a u ≤ 1 := by
        rw [hwa, div_le_one hpos]
        exact single_le_sum (f := fun v => p (a, v)) (fun v _ => hp0 (a, v)) (mem_univ u)
      have e : (k a u : ℝ) / n - p (a, u) =
          ((k a u : ℝ) - typeCount x a * w a u) / n +
            w a u * ((typeCount x a : ℝ) / n - pA a) := by
        rw [hwa]
        field_simp
        ring
      rw [e]
      have t1 : |((k a u : ℝ) - typeCount x a * w a u) / n| ≤ ε := by
        rw [abs_div, abs_of_pos hn']
        exact (div_le_div_of_nonneg_right (hk2 a u) hn'.le).trans hUn
      have t2 : |w a u * ((typeCount x a : ℝ) / n - pA a)| ≤ ε := by
        rw [abs_mul, abs_of_nonneg (hw0 a u)]
        calc w a u * |(typeCount x a : ℝ) / n - pA a| ≤ 1 * ε :=
              mul_le_mul hw1' (hx a) (abs_nonneg _) zero_le_one
          _ = ε := one_mul ε
      linarith [abs_add_le (((k a u : ℝ) - typeCount x a * w a u) / n)
        (w a u * ((typeCount x a : ℝ) / n - pA a))]
  have hsub : condTypeClass x k ⊆
      univ.filter (fun u : Fin n → U => (fun i => (x i, u i)) ∈ strongTypicalSet p n δ) := by
    intro u hu
    rw [mem_filter, mem_strongTypicalSet]
    refine ⟨mem_univ _, fun z => ?_⟩
    rw [(mem_condTypeClass.1 hu) z.1 z.2]
    linarith [hclose z]
  have hlow := le_sum_iidProb_condTypeClass x q k hk1
  have htot : ∑ a, ∑ u, k a u = n := by
    simp only [hk1]
    exact sum_typeCount x
  have hpos : ∀ u, 0 < ∑ a, k a u → 0 < qr u := fun u hu => by
    obtain ⟨a, -, ha⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℕ))
      (g := fun a => k a u) (by simpa using hu)
    have hpA : pA a ≠ 0 := fun h => by
      have := (hzero a h u).1
      omega
    have hw : w a u ≠ 0 := fun h => by
      have := hk3 a u h
      omega
    have hp : 0 < p (a, u) := by
      simp only [w, hpA, ite_false] at hw
      exact lt_of_le_of_ne (hp0 _) (Ne.symm (left_ne_zero_of_mul hw))
    change 0 < (q u).toReal
    rw [hq]
    exact hp.trans_le (single_le_sum (f := fun b => p (b, u)) (fun b _ => hp0 (b, u))
      (mem_univ a))
  have hexp := exp_countEntropy_mul_prod hn1 k htot qr hpos
  have hG : -jointInfo p - δ / 2 ≤ typeExponent (fun z => (k z.1 z.2 : ℝ) / n) qr := by
    have := hcont (fun z => (k z.1 z.2 : ℝ) / n) fun z => by linarith [hclose z]
    rw [hGp] at this
    linarith [(abs_lt.1 this).1]
  have hm0 : (0 : ℝ) < ((n : ℝ) + 1) ^ (Fintype.card U * Fintype.card A) := by positivity
  calc Real.exp (-(n * (jointInfo p + δ)))
      ≤ Real.exp (n * typeExponent (fun z => (k z.1 z.2 : ℝ) / n) qr) /
          ((n : ℝ) + 1) ^ (Fintype.card U * Fintype.card A) :=
        exp_bound hG hm0 hpow hn'.le
    _ = Real.exp (∑ a, countEntropy (k a)) / ((n : ℝ) + 1) ^ (Fintype.card U * Fintype.card A) *
          ∏ u, (q u).toReal ^ (∑ a, k a u) := by
        rw [← hexp]
        ring
    _ ≤ ∑ u ∈ condTypeClass x k, iidProb q u := hlow
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun u _ _ => iidProb_nonneg q u

end Covering

section Packing

variable {B U : Type*} [Fintype B] [DecidableEq B] [Fintype U] [DecidableEq U] [MeasurableSpace U]
  [MeasurableSingletonClass U]

omit [Fintype B] [MeasurableSpace U] [MeasurableSingletonClass U] in
private lemma typeCount_eq_sum_pair_left {n : ℕ} (y : Fin n → B) (u : Fin n → U) (b : B) :
    typeCount y b = ∑ v, typeCount (fun i => (y i, u i)) (b, v) := by
  classical
  unfold typeCount
  rw [card_eq_sum_card_fiberwise (f := u) (t := univ) fun _ _ => mem_univ _]
  refine sum_congr rfl fun v _ => ?_
  congr 1
  ext i
  simp

theorem strong_packing (p : B × U → ℝ) (q : PMF U) (hq : ∀ u, (q u).toReal = ∑ b, p (b, u))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ y : Fin n → B,
      ∑ u ∈ univ.filter (fun u : Fin n → U => (fun i => (y i, u i)) ∈ strongTypicalSet p n ε),
          iidProb q u ≤ Real.exp (-(n * (jointInfo p - δ))) := by
  classical
  set qr : U → ℝ := fun u => (q u).toReal
  have hqr : qr = fun u => ∑ b, p (b, u) := funext hq
  have hGp : typeExponent p qr = -jointInfo p := by rw [hqr, typeExponent_marginal]
  obtain ⟨ρ, hρ, hcont⟩ := exists_typeExponent_close p qr (half_pos hδ)
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [eventually_pow_le_exp (Fintype.card B * Fintype.card U) (half_pos hδ),
    eventually_ge_atTop 1] with n hpow hn1 y
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  set S := univ.filter (fun u : Fin n → U => (fun i => (y i, u i)) ∈ strongTypicalSet p n ρ)
  set f : (Fin n → U) → B → U → ℕ := fun u b v => typeCount (fun i => (y i, u i)) (b, v)
  set T := Fintype.piFinset fun _ : B => Fintype.piFinset fun _ : U => range (n + 1)
  have hmaps : ∀ u ∈ S, f u ∈ S.image f := fun u hu => mem_image_of_mem f hu
  have hT : S.image f ⊆ T := by
    intro K hK
    obtain ⟨u, -, rfl⟩ := mem_image.1 hK
    simp only [T, Fintype.mem_piFinset, mem_range]
    exact fun b v => Nat.lt_succ_of_le (typeCount_le _ _)
  have hcardT : ((S.image f).card : ℝ) ≤ ((n : ℝ) + 1) ^ (Fintype.card B * Fintype.card U) := by
    have h1 := card_le_card hT
    simp only [T, Fintype.card_piFinset, card_range, prod_const, card_univ] at h1
    rw [← pow_mul, mul_comm] at h1
    exact_mod_cast h1
  have hclass : ∀ K ∈ S.image f, ∑ u ∈ condTypeClass y K, iidProb q u ≤
      Real.exp (n * (-jointInfo p + δ / 2)) := by
    intro K hK
    obtain ⟨u₀, hu₀, rfl⟩ := mem_image.1 hK
    have hrow : ∀ b, ∑ v, f u₀ b v = typeCount y b := fun b =>
      (typeCount_eq_sum_pair_left y u₀ b).symm
    by_cases hz : ∃ v, 0 < ∑ b, f u₀ b v ∧ qr v = 0
    · obtain ⟨v, hv, hqv⟩ := hz
      rw [sum_iidProb_condTypeClass, prod_eq_zero (mem_univ v)]
      · rw [mul_zero]
        exact (Real.exp_pos _).le
      · simp only [qr] at hqv
        rw [hqv]
        exact zero_pow (Nat.pos_iff_ne_zero.1 hv)
    push Not at hz
    have hpos : ∀ v, 0 < ∑ b, f u₀ b v → 0 < qr v := fun v hv =>
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm (hz v hv))
    have htot : ∑ b, ∑ v, f u₀ b v = n := by
      simp only [hrow]
      exact sum_typeCount y
    have hexp := exp_countEntropy_mul_prod hn1 (f u₀) htot qr hpos
    have hG : typeExponent (fun z => (f u₀ z.1 z.2 : ℝ) / n) qr ≤ -jointInfo p + δ / 2 := by
      have := hcont (fun z => (f u₀ z.1 z.2 : ℝ) / n) fun z =>
        (mem_strongTypicalSet.1 (mem_filter.1 hu₀).2) z
      rw [hGp] at this
      linarith [(abs_lt.1 this).2]
    calc ∑ u ∈ condTypeClass y (f u₀), iidProb q u
        ≤ Real.exp (∑ b, countEntropy (f u₀ b)) * ∏ v, (q v).toReal ^ (∑ b, f u₀ b v) :=
          sum_iidProb_condTypeClass_le y q (f u₀) hrow
      _ = Real.exp (n * typeExponent (fun z => (f u₀ z.1 z.2 : ℝ) / n) qr) := hexp
      _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hG hn'.le)
  calc ∑ u ∈ S, iidProb q u
      = ∑ K ∈ S.image f, ∑ u ∈ S with f u = K, iidProb q u :=
        (sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ K ∈ S.image f, ∑ u ∈ condTypeClass y K, iidProb q u := by
        refine sum_le_sum fun K _ => sum_le_sum_of_subset_of_nonneg (fun u hu => ?_)
          fun u _ _ => iidProb_nonneg q u
        rw [mem_condTypeClass]
        intro b v
        rw [← (mem_filter.1 hu).2]
    _ ≤ ∑ _K ∈ S.image f, Real.exp (n * (-jointInfo p + δ / 2)) := sum_le_sum hclass
    _ = (S.image f).card * Real.exp (n * (-jointInfo p + δ / 2)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (n * (δ / 2)) * Real.exp (n * (-jointInfo p + δ / 2)) :=
        mul_le_mul_of_nonneg_right (hcardT.trans hpow) (Real.exp_pos _).le
    _ = Real.exp (-(n * (jointInfo p - δ))) := by rw [← Real.exp_add]; ring_nf

end Packing

end Meat
