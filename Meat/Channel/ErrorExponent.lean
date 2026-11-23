import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Meat.Channel.Achievability
import Meat.Channel.StrongConverse

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace DMC

variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def gallagerTerm (W : DMC A B) (p : PMF A) (ρ : ℝ) (b : B) : ℝ :=
  ∑ a, (p a).toReal * (W a b).toReal ^ (1 / (1 + ρ))

noncomputable def gallagerSum (W : DMC A B) (p : PMF A) (ρ : ℝ) : ℝ :=
  ∑ b, gallagerTerm W p ρ b ^ (1 + ρ)

noncomputable def gallagerE0 (W : DMC A B) (p : PMF A) (ρ : ℝ) : ℝ :=
  -Real.log (gallagerSum W p ρ)

omit [Fintype B] in
theorem gallagerTerm_nonneg (W : DMC A B) (p : PMF A) (ρ : ℝ) (b : B) :
    0 ≤ gallagerTerm W p ρ b :=
  sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)

theorem gallagerSum_nonneg (W : DMC A B) (p : PMF A) (ρ : ℝ) : 0 ≤ gallagerSum W p ρ :=
  sum_nonneg fun b _ => Real.rpow_nonneg (gallagerTerm_nonneg W p ρ b) _

omit [Fintype B] in
theorem iidProb_mul_blockProb_rpow {n : ℕ} (W : DMC A B) (p : PMF A) (s : ℝ) (y : Fin n → B) :
    ∑ x : Fin n → A, iidProb p x * (blockProb W x y).toReal ^ s =
      ∏ t, ∑ a, (p a).toReal * (W a (y t)).toReal ^ s := by
  have h : ∀ x : Fin n → A, (blockProb W x y).toReal ^ s = ∏ t, (W (x t) (y t)).toReal ^ s := by
    intro x
    rw [blockProb, ENNReal.toReal_prod, Real.finsetProd_rpow _ _ fun t _ => ENNReal.toReal_nonneg]
  simp only [h, iidProb]
  exact sum_prod_mul_prod (fun t a => (p a).toReal) fun t a => (W a (y t)).toReal ^ s


variable {M : Type*} [Fintype M] [Nonempty M] [DecidableEq M]

noncomputable def mlDecode {n : ℕ} (W : DMC A B) (C : M → Fin n → A) (y : Fin n → B) : M :=
  (exists_max_image univ (fun m => (blockProb W (C m) y).toReal) univ_nonempty).choose

omit [Fintype A] [Fintype B] [DecidableEq M] in
theorem le_mlDecode {n : ℕ} (W : DMC A B) (C : M → Fin n → A) (y : Fin n → B) (m : M) :
    (blockProb W (C m) y).toReal ≤ (blockProb W (C (mlDecode W C y)) y).toReal :=
  (exists_max_image univ (fun m => (blockProb W (C m) y).toReal) univ_nonempty).choose_spec.2 m
    (mem_univ m)

noncomputable def mlCode {n : ℕ} (W : DMC A B) (C : M → Fin n → A) : BlockCode M A B n :=
  ⟨C, mlDecode W C⟩

omit [Fintype A] in
theorem errorProb_mlCode_le {n : ℕ} (W : DMC A B) (C : M → Fin n → A) (m : M) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) :
    ((mlCode W C).errorProb W m).toReal ≤
      ∑ y, (blockProb W (C m) y).toReal ^ (1 / (1 + ρ)) *
        (∑ m' ∈ univ.erase m, (blockProb W (C m') y).toReal ^ (1 / (1 + ρ))) ^ ρ := by
  rw [BlockCode.errorProb_toReal]
  refine sum_le_sum fun y _ => ?_
  set P : M → ℝ := fun m => (blockProb W (C m) y).toReal
  set s := 1 / (1 + ρ)
  have hP : ∀ m, 0 ≤ P m := fun m => ENNReal.toReal_nonneg
  have hS : 0 ≤ ∑ m' ∈ univ.erase m, P m' ^ s := sum_nonneg fun m' _ => Real.rpow_nonneg (hP m') _
  have hrhs : 0 ≤ P m ^ s * (∑ m' ∈ univ.erase m, P m' ^ s) ^ ρ :=
    mul_nonneg (Real.rpow_nonneg (hP m) _) (Real.rpow_nonneg hS _)
  split_ifs with hd
  · exact hrhs
  change P m ≤ _
  rcases (hP m).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact hrhs
  set m₁ := mlDecode W C y
  have hm₁ : m₁ ∈ univ.erase m := mem_erase.2 ⟨hd, mem_univ _⟩
  have hle : P m ≤ P m₁ := le_mlDecode W C y m
  have hs : 0 < s := by positivity
  have h1 : P m ^ s ≤ ∑ m' ∈ univ.erase m, P m' ^ s :=
    (Real.rpow_le_rpow (hP m) hle hs.le).trans
      (single_le_sum (f := fun m' => P m' ^ s) (fun m' _ => Real.rpow_nonneg (hP m') _) hm₁)
  have h2 : (P m ^ s) ^ ρ ≤ (∑ m' ∈ univ.erase m, P m' ^ s) ^ ρ :=
    Real.rpow_le_rpow (Real.rpow_nonneg (hP m) _) h1 hρ0
  have h3 : P m = P m ^ s * (P m ^ s) ^ ρ := by
    rw [← Real.rpow_mul (hP m), ← Real.rpow_add hpos]
    have e : s + s * ρ = 1 := by
      simp only [s]
      field_simp
    rw [e, Real.rpow_one]
  rw [h3]
  exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (hP m) _)

noncomputable def codebookWeight {n : ℕ} (p : PMF A) (C : M → Fin n → A) : ℝ :=
  ∏ m, iidProb p (C m)

theorem sum_codebookWeight_errorProb_mlCode_le {n : ℕ} (W : DMC A B) (p : PMF A) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (m : M) :
    ∑ C : M → Fin n → A, codebookWeight p C * ((mlCode W C).errorProb W m).toReal ≤
      ((Fintype.card M : ℝ) - 1) ^ ρ * gallagerSum W p ρ ^ n := by
  classical
  set s := 1 / (1 + ρ)
  have hs : 0 < s := by positivity
  have hw : ∀ C : M → Fin n → A, 0 ≤ codebookWeight p C :=
    fun C => prod_nonneg fun m _ => iidProb_nonneg p _
  have h1 : ∀ i : M, ∑ x : Fin n → A, iidProb p x = 1 := fun _ => sum_iidProb p n
  set E : (Fin n → B) → ℝ := fun y => ∑ x : Fin n → A, iidProb p x * (blockProb W x y).toReal ^ s
  have hE0 : ∀ y, 0 ≤ E y := fun y => sum_nonneg fun x _ =>
    mul_nonneg (iidProb_nonneg p x) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hy : ∀ y : Fin n → B, ∑ C : M → Fin n → A, codebookWeight p C *
      ((blockProb W (C m) y).toReal ^ s *
        (∑ m' ∈ univ.erase m, (blockProb W (C m') y).toReal ^ s) ^ ρ) ≤
      ((Fintype.card M : ℝ) - 1) ^ ρ * E y ^ (1 + ρ) := by
    intro y
    set F : (M → Fin n → A) → ℝ := fun C => (blockProb W (C m) y).toReal ^ s
    set S : (M → Fin n → A) → ℝ := fun C =>
      ∑ m' ∈ univ.erase m, (blockProb W (C m') y).toReal ^ s
    have hF0 : ∀ C, 0 ≤ F C := fun C => Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hS0 : ∀ C, 0 ≤ S C := fun C => sum_nonneg fun m' _ =>
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hEF : ∑ C, codebookWeight p C * F C = E y :=
      sum_prod_mul_apply (fun _ x => iidProb p x) h1
        (fun x => (blockProb W x y).toReal ^ s) m
    have hEFS : ∑ C, codebookWeight p C * (F C * S C) =
        ((Fintype.card M : ℝ) - 1) * (E y * E y) := by
      simp only [S, mul_sum]
      rw [sum_comm]
      have hm : ∀ m' ∈ univ.erase m, ∑ C : M → Fin n → A, codebookWeight p C *
          (F C * (blockProb W (C m') y).toReal ^ s) = E y * E y := by
        intro m' hm'
        exact sum_prod_mul_apply_mul_apply (fun _ x => iidProb p x) h1
          (fun x => (blockProb W x y).toReal ^ s) (fun x => (blockProb W x y).toReal ^ s)
          (Ne.symm (ne_of_mem_erase hm'))
      rw [sum_congr rfl hm, sum_const, card_erase_of_mem (mem_univ m), card_univ,
        nsmul_eq_mul, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
    rcases (hE0 y).eq_or_lt with hz | hpos
    · have hzero : ∀ C, codebookWeight p C * F C = 0 := by
        intro C
        have hsum := hEF
        rw [← hz] at hsum
        exact (sum_eq_zero_iff_of_nonneg fun C _ => mul_nonneg (hw C) (hF0 C)).1 hsum C
          (mem_univ C)
      calc _ = ∑ C : M → Fin n → A, (codebookWeight p C * F C) * S C ^ ρ :=
            sum_congr rfl fun C _ => by ring
        _ = 0 := sum_eq_zero fun C _ => by rw [hzero C, zero_mul]
        _ ≤ _ := by
            rw [← hz, Real.zero_rpow (by positivity), mul_zero]
    · set v : (M → Fin n → A) → ℝ := fun C => codebookWeight p C * F C / E y
      have hv0 : ∀ C ∈ univ, 0 ≤ v C := fun C _ => div_nonneg (mul_nonneg (hw C) (hF0 C)) hpos.le
      have hv1 : ∑ C, v C = 1 := by rw [← sum_div, hEF, div_self hpos.ne']
      have hJ := (Real.concaveOn_rpow hρ0 hρ1).le_map_sum hv0 hv1 fun C _ => Set.mem_Ici.2 (hS0 C)
      simp only [smul_eq_mul] at hJ
      have hvS : ∑ C, v C * S C = ((Fintype.card M : ℝ) - 1) * E y := by
        simp only [v, div_mul_eq_mul_div, ← sum_div, mul_assoc, hEFS]
        field_simp
      rw [hvS] at hJ
      have hM1 : (0 : ℝ) ≤ (Fintype.card M : ℝ) - 1 := by
        have : (1 : ℝ) ≤ Fintype.card M := Nat.one_le_cast.2 Fintype.card_pos
        linarith
      calc _ = E y * ∑ C, v C * S C ^ ρ := by
            rw [mul_sum]
            refine sum_congr rfl fun C _ => ?_
            simp only [v]
            field_simp
            rfl
        _ ≤ E y * (((Fintype.card M : ℝ) - 1) * E y) ^ ρ :=
            mul_le_mul_of_nonneg_left hJ hpos.le
        _ = _ := by
            rw [Real.mul_rpow hM1 hpos.le, Real.rpow_one_add' hpos.le (by positivity)]
            ring
  have hsum : ∑ y : Fin n → B, E y ^ (1 + ρ) = gallagerSum W p ρ ^ n := by
    simp only [E, iidProb_mul_blockProb_rpow]
    simp_rw [← Real.finsetProd_rpow _ _ fun t _ => sum_nonneg fun a _ =>
      mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    change ∑ y : Fin n → B, ∏ t, gallagerTerm W p ρ (y t) ^ (1 + ρ) = _
    rw [← (Fintype.prod_sum fun (_ : Fin n) b => gallagerTerm W p ρ b ^ (1 + ρ)), prod_const,
      card_univ, Fintype.card_fin]
    rfl
  calc _ ≤ ∑ C : M → Fin n → A, codebookWeight p C *
        ∑ y, (blockProb W (C m) y).toReal ^ s *
          (∑ m' ∈ univ.erase m, (blockProb W (C m') y).toReal ^ s) ^ ρ :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (errorProb_mlCode_le W C m hρ0) (hw C)
    _ = ∑ y, ∑ C : M → Fin n → A, codebookWeight p C *
        ((blockProb W (C m) y).toReal ^ s *
          (∑ m' ∈ univ.erase m, (blockProb W (C m') y).toReal ^ s) ^ ρ) := by
        simp only [mul_sum]
        exact sum_comm
    _ ≤ ∑ y : Fin n → B, ((Fintype.card M : ℝ) - 1) ^ ρ * E y ^ (1 + ρ) :=
        sum_le_sum fun y _ => hy y
    _ = _ := by rw [← mul_sum, hsum]

theorem exists_mlCode_avgError_le {n : ℕ} (W : DMC A B) (p : PMF A) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) :
    ∃ C : M → Fin n → A, (mlCode W C).avgError W ≤
      ENNReal.ofReal (((Fintype.card M : ℝ) - 1) ^ ρ * gallagerSum W p ρ ^ n) := by
  set β := ((Fintype.card M : ℝ) - 1) ^ ρ * gallagerSum W p ρ ^ n
  have h1 : ∑ C : M → Fin n → A, codebookWeight p C = 1 :=
    sum_prod (fun _ x => iidProb p x) fun _ => sum_iidProb p n
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le (w := codebookWeight p)
    (f := fun C => ∑ m, ((mlCode W C).errorProb W m).toReal) (t := Fintype.card M * β)
    (fun C => prod_nonneg fun m _ => iidProb_nonneg p _) h1 (by
      simp only [mul_sum]
      rw [sum_comm]
      calc _ ≤ ∑ m : M, β := sum_le_sum fun m _ =>
            sum_codebookWeight_errorProb_mlCode_le W p hρ0 hρ1 m
        _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul])
  exact ⟨C, BlockCode.avgError_le_ofReal _ W hC⟩

section Exponent

omit [Fintype B] in
theorem gallagerTerm_zero (W : DMC A B) (p : PMF A) (b : B) :
    gallagerTerm W p 0 b = outputLaw W (fun a => (p a).toReal) b := by
  simp [gallagerTerm, outputLaw]

theorem gallagerSum_zero (W : DMC A B) (p : PMF A) : gallagerSum W p 0 = 1 := by
  simp only [gallagerSum, gallagerTerm_zero, add_zero, Real.rpow_one]
  rw [sum_outputLaw, sum_toReal_pmf_eq_one]

omit [Fintype B] in
theorem outputLaw_le_gallagerTerm (W : DMC A B) (p : PMF A) {ρ : ℝ} (hρ : 0 ≤ ρ) (b : B) :
    outputLaw W (fun a => (p a).toReal) b ≤ gallagerTerm W p ρ b := by
  refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  set w := (W a b).toReal
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  have hw1 : w ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  rcases hw0.eq_or_lt with h | h
  · rw [← h]
    exact Real.rpow_nonneg le_rfl _
  have hs : 1 / (1 + ρ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  calc w = w ^ (1 : ℝ) := (Real.rpow_one w).symm
    _ ≤ w ^ (1 / (1 + ρ)) := Real.rpow_le_rpow_of_exponent_ge h hw1 hs

theorem inv_card_le_gallagerSum (W : DMC A B) (p : PMF A) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    1 / (Fintype.card B : ℝ) ≤ gallagerSum W p ρ := by
  set q := outputLaw W fun a => (p a).toReal
  have hq0 : ∀ b, 0 ≤ q b := outputLaw_nonneg W (fun a => ENNReal.toReal_nonneg)
  have hq1 : ∀ b, q b ≤ 1 :=
    outputLaw_le_one W (fun a => ENNReal.toReal_nonneg) (sum_toReal_pmf_eq_one p)
  have hsq : ∀ b, q b ^ 2 ≤ gallagerTerm W p ρ b ^ (1 + ρ) := by
    intro b
    have h1 : q b ^ 2 ≤ q b ^ (1 + ρ) := by
      rcases (hq0 b).eq_or_lt with h | h
      · rw [← h, sq, zero_mul]
        exact Real.rpow_nonneg le_rfl _
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge h (hq1 b) (by push_cast; linarith)
    exact h1.trans (Real.rpow_le_rpow (hq0 b) (outputLaw_le_gallagerTerm W p hρ0 b) (by linarith))
  have hcs := sum_mul_sq_le_sq_mul_sq univ q fun _ => (1 : ℝ)
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul] at hcs
  rw [sum_outputLaw, sum_toReal_pmf_eq_one, one_pow] at hcs
  rcases (Nat.zero_le (Fintype.card B)).eq_or_lt with h | h
  · rw [← h, Nat.cast_zero, div_zero]
    exact gallagerSum_nonneg W p ρ
  have hc : (0 : ℝ) < Fintype.card B := Nat.cast_pos.2 h
  rw [div_le_iff₀ hc]
  calc (1 : ℝ) ≤ (∑ b, q b ^ 2) * Fintype.card B := hcs
    _ ≤ gallagerSum W p ρ * Fintype.card B :=
        mul_le_mul_of_nonneg_right (sum_le_sum fun b _ => hsq b) hc.le

theorem gallagerSum_pos [Nonempty B] (W : DMC A B) (p : PMF A) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) : 0 < gallagerSum W p ρ :=
  lt_of_lt_of_le (by have := Fintype.card_pos (α := B); positivity)
    (inv_card_le_gallagerSum W p hρ0 hρ1)

theorem gallagerE0_le [Nonempty B] (W : DMC A B) (p : PMF A) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) : gallagerE0 W p ρ ≤ Real.log (Fintype.card B) := by
  have hc : (0 : ℝ) < Fintype.card B := Nat.cast_pos.2 Fintype.card_pos
  have h := Real.log_le_log (by positivity) (inv_card_le_gallagerSum W p hρ0 hρ1)
  rw [one_div, Real.log_inv] at h
  rw [gallagerE0]
  linarith

theorem exists_code_avgError_le_exp [Nonempty B] (W : DMC A B) (p : PMF A) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (R : ℝ) (n : ℕ) :
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : BlockCode (Fin k) A B n,
      c.avgError W ≤ ENNReal.ofReal (Real.exp (-(n * (gallagerE0 W p ρ - ρ * R)))) := by
  set k := ⌈Real.exp (n * R)⌉₊
  have hk : 0 < k := Nat.ceil_pos.2 (Real.exp_pos _)
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨C, hC⟩ := exists_mlCode_avgError_le (M := Fin k) (n := n) W p hρ0 hρ1
  refine ⟨k, Nat.le_ceil _, mlCode W C, hC.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [Fintype.card_fin]
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := Nat.one_le_cast.2 hk
    linarith
  have hk2 : (k : ℝ) - 1 ≤ Real.exp (n * R) := by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R)).le]
  have hS := gallagerSum_pos W p hρ0 hρ1
  have e1 : gallagerSum W p ρ ^ n = Real.exp (n * Real.log (gallagerSum W p ρ)) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hS n)]
  have e2 : Real.exp (n * R) ^ ρ = Real.exp (n * R * ρ) := by
    rw [← Real.exp_mul]
  calc ((k : ℝ) - 1) ^ ρ * gallagerSum W p ρ ^ n ≤ Real.exp (n * R) ^ ρ * gallagerSum W p ρ ^ n :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hk1 hk2 hρ0) (pow_nonneg hS.le n)
    _ = _ := by
        rw [e1, e2, ← Real.exp_add, gallagerE0]
        congr 1
        ring

noncomputable def randomCodingExponent (W : DMC A B) (R : ℝ) : ℝ :=
  sSup {E | ∃ ρ ∈ Set.Icc (0 : ℝ) 1, ∃ p : PMF A, E = gallagerE0 W p ρ - ρ * R}

theorem exists_code_of_lt_randomCodingExponent [Nonempty A] [Nonempty B] (W : DMC A B)
    {R E : ℝ} (hE : E < randomCodingExponent W R) (n : ℕ) :
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : BlockCode (Fin k) A B n,
      c.avgError W ≤ ENNReal.ofReal (Real.exp (-(n * E))) := by
  have hne : {E | ∃ ρ ∈ Set.Icc (0 : ℝ) 1, ∃ p : PMF A, E = gallagerE0 W p ρ - ρ * R}.Nonempty :=
    ⟨_, 0, ⟨le_rfl, zero_le_one⟩, PMF.pure (Classical.arbitrary A), rfl⟩
  obtain ⟨_, ⟨ρ, ⟨hρ0, hρ1⟩, p, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hE
  obtain ⟨k, hk, c, hc⟩ := exists_code_avgError_le_exp W p hρ0 hρ1 R n
  refine ⟨k, hk, c, hc.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))⟩
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

variable [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B]

theorem inputMutualInfo_eq_sub (W : DMC A B) (p : PMF A) :
    W.inputMutualInfo p = ∑ a, ∑ b, (p a).toReal * ((W a b).toReal * Real.log (W a b).toReal) -
      ∑ b, outputLaw W (fun a => (p a).toReal) b *
        Real.log (outputLaw W (fun a => (p a).toReal) b) := by
  rw [inputMutualInfo_eq_sum_log_div]
  have key : ∀ a b, (p a).toReal * (W a b).toReal *
      Real.log ((W a b).toReal / outputLaw W (fun a => (p a).toReal) b) =
      (p a).toReal * ((W a b).toReal * Real.log (W a b).toReal) -
        (p a).toReal * (W a b).toReal * Real.log (outputLaw W (fun a => (p a).toReal) b) := by
    intro a b
    rcases eq_or_ne ((p a).toReal * (W a b).toReal) 0 with h | h
    · rcases mul_eq_zero.1 h with h' | h' <;> simp [h']
    have hw : (W a b).toReal ≠ 0 := (mul_ne_zero_iff.1 h).2
    have hqb : 0 < outputLaw W (fun a => (p a).toReal) b := lt_of_lt_of_le
      (lt_of_le_of_ne (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (Ne.symm h))
      (le_outputLaw W (fun a => ENNReal.toReal_nonneg) a b)
    rw [Real.log_div hw hqb.ne']
    ring
  simp_rw [key, sum_sub_distrib]
  congr 1
  rw [sum_comm]
  exact sum_congr rfl fun b _ => by rw [← sum_mul]; rfl

theorem hasDerivAt_gallagerSum (W : DMC A B) (p : PMF A) :
    HasDerivAt (gallagerSum W p) (-W.inputMutualInfo p) 0 := by
  set q := outputLaw W fun a => (p a).toReal
  have hnear : ∀ᶠ ρ : ℝ in 𝓝 0, -1 < ρ := Ioi_mem_nhds (by norm_num)
  have hs : HasDerivAt (fun ρ : ℝ => 1 / (1 + ρ)) (-1) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).const_add 1).inv (by norm_num)
    have e : (fun ρ : ℝ => 1 / (1 + ρ)) = (fun x => 1 + id x)⁻¹ := by
      funext ρ
      simp
    rw [e]
    convert h using 1
    norm_num
  have hterm : ∀ a b, HasDerivAt (fun ρ : ℝ => (p a).toReal * (W a b).toReal ^ (1 / (1 + ρ)))
      ((p a).toReal * (-((W a b).toReal * Real.log (W a b).toReal))) 0 := by
    intro a b
    set w := (W a b).toReal
    rcases (show (0 : ℝ) ≤ w from ENNReal.toReal_nonneg).eq_or_lt with h | h
    · rw [← h]
      simp only [zero_mul, neg_zero, mul_zero]
      refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [hnear] with ρ hρ
      rw [Real.zero_rpow (one_div_pos.2 (by linarith : (0 : ℝ) < 1 + ρ)).ne', mul_zero]
    · have h2 := (hs.const_rpow h).const_mul (p a).toReal
      rw [show (p a).toReal * (-(w * Real.log w)) =
          (p a).toReal * (Real.log w * -1 * w ^ (1 / (1 + (0 : ℝ)))) by
        rw [add_zero, div_one, Real.rpow_one]
        ring]
      exact h2
  have hg : ∀ b, HasDerivAt (fun ρ => gallagerTerm W p ρ b)
      (∑ a, (p a).toReal * (-((W a b).toReal * Real.log (W a b).toReal))) 0 := by
    intro b
    exact HasDerivAt.fun_sum fun a _ => hterm a b
  have hg0 : ∀ b, gallagerTerm W p 0 b = q b := gallagerTerm_zero W p
  have hφ : ∀ b, HasDerivAt (fun ρ => gallagerTerm W p ρ b ^ (1 + ρ))
      (q b * Real.log (q b) -
        ∑ a, (p a).toReal * ((W a b).toReal * Real.log (W a b).toReal)) 0 := by
    intro b
    rcases (outputLaw_nonneg W (fun a => ENNReal.toReal_nonneg) b).eq_or_lt with h | h
    · have hz : ∀ a, (p a).toReal * (W a b).toReal = 0 := fun a =>
        le_antisymm ((le_outputLaw W (fun a => ENNReal.toReal_nonneg) a b).trans h.symm.le)
          (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      have hD : q b * Real.log (q b) -
          ∑ a, (p a).toReal * ((W a b).toReal * Real.log (W a b).toReal) = 0 := by
        rw [show q b = 0 from h.symm]
        simp only [zero_mul, zero_sub, neg_eq_zero]
        exact sum_eq_zero fun a _ => by rw [← mul_assoc, hz a, zero_mul]
      rw [hD]
      refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [hnear] with ρ hρ
      have hpos : 0 < 1 + ρ := by linarith
      have hzero : gallagerTerm W p ρ b = 0 := sum_eq_zero fun a _ => by
        rcases mul_eq_zero.1 (hz a) with h' | h'
        · rw [h', zero_mul]
        · rw [h', Real.zero_rpow (by positivity), mul_zero]
      simp only [hzero, Real.zero_rpow hpos.ne']
    · have hpos : 0 < gallagerTerm W p 0 b := by rw [hg0]; exact h
      have h2 := (hg b).rpow ((hasDerivAt_id (0 : ℝ)).const_add 1) hpos
      convert h2 using 1
      · rfl
      · rw [hg0]
        simp only [id_eq, add_zero, sub_self, Real.rpow_zero, Real.rpow_one, mul_one, one_mul,
          mul_neg, sum_neg_distrib]
        ring
  have hsum := HasDerivAt.fun_sum fun b (_ : b ∈ univ) => hφ b
  have e : -W.inputMutualInfo p = ∑ b, (q b * Real.log (q b) -
      ∑ a, (p a).toReal * ((W a b).toReal * Real.log (W a b).toReal)) := by
    rw [inputMutualInfo_eq_sub, sum_sub_distrib,
      show q = outputLaw W (fun a => (p a).toReal) from rfl, sum_comm (s := (univ : Finset B))]
    ring
  rw [e]
  exact hsum

theorem exists_lt_gallagerE0 [Nonempty B] (W : DMC A B) (p : PMF A) {R : ℝ}
    (hR : R < W.inputMutualInfo p) :
    ∃ ρ ∈ Set.Icc (0 : ℝ) 1, ρ * R < gallagerE0 W p ρ := by
  set I := W.inputMutualInfo p
  have h := hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_gallagerSum W p)
  have h' := h.mono_left (nhdsWithin_mono _ fun x (hx : 0 < x) => ne_of_gt hx)
  have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), slope (gallagerSum W p) 0 ρ < -((I + R) / 2) :=
    h'.eventually (gt_mem_nhds (by linarith))
  have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have h3 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ := self_mem_nhdsWithin
  obtain ⟨ρ, hρs, hρ1, hρ0⟩ := (h1.and (h2.and h3)).exists
  refine ⟨ρ, ⟨hρ0.le, hρ1.le⟩, ?_⟩
  rw [slope_def_field, gallagerSum_zero, sub_zero, div_lt_iff₀ hρ0] at hρs
  have hS := gallagerSum_pos W p hρ0.le hρ1.le
  have hlog := Real.log_le_sub_one_of_pos hS
  rw [gallagerE0]
  nlinarith

theorem randomCodingExponent_pos [Nonempty A] [Nonempty B] (W : DMC A B) {R : ℝ}
    (hR : R < W.capacity) : 0 < randomCodingExponent W R := by
  obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup hR
  obtain ⟨ρ, hρ, hlt⟩ := exists_lt_gallagerE0 W p hp
  have hbdd : BddAbove {E | ∃ ρ ∈ Set.Icc (0 : ℝ) 1, ∃ p : PMF A,
      E = gallagerE0 W p ρ - ρ * R} := by
    refine ⟨Real.log (Fintype.card B) + |R|, ?_⟩
    rintro _ ⟨ρ, ⟨hρ0, hρ1⟩, p, rfl⟩
    have h1 := gallagerE0_le W p hρ0 hρ1
    have h2 : -(ρ * R) ≤ |R| := by
      have := neg_abs_le R
      have := le_abs_self R
      rcases le_total 0 R with h | h <;> nlinarith
    linarith
  exact lt_of_lt_of_le (by linarith) (le_csSup hbdd ⟨ρ, hρ, p, rfl⟩)

end Exponent

end DMC

end Meat
