import Meat.Channel.Basic
import Meat.Shannon.Average
import Meat.Shannon.Typical

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace DMC

variable {A B : Type*}

noncomputable def jointPMF (W : DMC A B) (q : PMF A) : PMF (A × B) :=
  q.bind fun a => (W a).map fun b => (a, b)

theorem jointMeasure_eq_toMeasure [MeasurableSpace A] [MeasurableSpace B] (W : DMC A B)
    (q : PMF A) : jointMeasure W q = (jointPMF W q).toMeasure := rfl

theorem jointPMF_apply (W : DMC A B) (q : PMF A) (a : A) (b : B) :
    jointPMF W q (a, b) = q a * W a b := by
  classical
  rw [jointPMF, PMF.bind_apply, tsum_eq_single a fun a' ha' => by
    simp [PMF.map_apply, Ne.symm ha']]
  congr 1
  rw [PMF.map_apply, tsum_eq_single b fun b' hb' => by simp [Ne.symm hb']]
  simp

theorem jointPMF_map_fst (W : DMC A B) (q : PMF A) : (jointPMF W q).map Prod.fst = q := by
  have h : ∀ a, (W a).map (fun _ => a) = PMF.pure a := fun a => PMF.map_const (W a) a
  simp [jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def, h]

theorem iidProb_jointPMF {n : ℕ} (W : DMC A B) (q : PMF A) (x : Fin n → A) (y : Fin n → B) :
    iidProb (jointPMF W q) (fun i => (x i, y i)) = iidProb q x * (blockProb W x y).toReal := by
  simp [iidProb, blockProb, jointPMF_apply, ENNReal.toReal_prod, prod_mul_distrib]

theorem blockProb_ne_top {n : ℕ} (W : DMC A B) (x : Fin n → A) (y : Fin n → B) :
    blockProb W x y ≠ ∞ :=
  ENNReal.prod_ne_top fun i _ => (W (x i)).apply_ne_top (y i)

theorem sum_blockProb_eq_one [Fintype B] {n : ℕ} (W : DMC A B) (x : Fin n → A) :
    ∑ y, blockProb W x y = 1 := by
  simp only [blockProb]
  rw [← Fintype.prod_sum]
  exact prod_eq_one fun i _ => sum_pmf_eq_one _

end DMC

namespace BlockCode

variable {M A B : Type*} {n : ℕ}

theorem errorProb_ne_top [Fintype B] [DecidableEq M] (c : BlockCode M A B n) (W : DMC A B)
    (m : M) : c.errorProb W m ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun y _ => by split_ifs <;> simp [DMC.blockProb_ne_top]

theorem errorProb_toReal [Fintype B] [DecidableEq M] (c : BlockCode M A B n) (W : DMC A B)
    (m : M) : (c.errorProb W m).toReal =
      ∑ y, if c.dec y = m then 0 else (DMC.blockProb W (c.enc m) y).toReal := by
  rw [errorProb, ENNReal.toReal_sum fun y _ => by split_ifs <;> simp [DMC.blockProb_ne_top]]
  exact sum_congr rfl fun y _ => by split_ifs <;> simp

theorem avgError_le_ofReal [Fintype B] [Fintype M] [DecidableEq M] [Nonempty M]
    (c : BlockCode M A B n) (W : DMC A B) {δ : ℝ}
    (h : ∑ m, (c.errorProb W m).toReal ≤ Fintype.card M * δ) :
    c.avgError W ≤ ENNReal.ofReal δ := by
  have hpos : (0 : ℝ) < Fintype.card M := Nat.cast_pos.2 Fintype.card_pos
  have hδ : 0 ≤ δ :=
    (mul_nonneg_iff_of_pos_left hpos).1 ((sum_nonneg fun m _ => ENNReal.toReal_nonneg).trans h)
  have hcard : (Fintype.card M : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  rw [avgError, ENNReal.div_le_iff hcard (ENNReal.natCast_ne_top _),
    ← ENNReal.ofReal_toReal (ENNReal.sum_ne_top.2 fun m _ => c.errorProb_ne_top W m),
    ENNReal.toReal_sum fun m _ => c.errorProb_ne_top W m, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul hδ]
  exact ENNReal.ofReal_le_ofReal (by linarith)

noncomputable def typicalDecoder (C : M → Fin n → A) (J : Finset ((Fin n → A) × (Fin n → B)))
    (m₀ : M) (y : Fin n → B) : M := by
  classical
  exact if h : ∃ m, (C m, y) ∈ J then h.choose else m₀

noncomputable def typicalCode (C : M → Fin n → A) (J : Finset ((Fin n → A) × (Fin n → B)))
    (m₀ : M) : BlockCode M A B n :=
  ⟨C, typicalDecoder C J m₀⟩

theorem typicalDecoder_eq {C : M → Fin n → A} {J : Finset ((Fin n → A) × (Fin n → B))}
    (m₀ : M) {m : M} {y : Fin n → B} (hm : (C m, y) ∈ J) (h : ∀ m', m' ≠ m → (C m', y) ∉ J) :
    typicalDecoder C J m₀ y = m := by
  have he : ∃ m, (C m, y) ∈ J := ⟨m, hm⟩
  simp only [typicalDecoder, he, dite_true]
  by_contra hne
  exact h _ hne he.choose_spec

theorem typicalDecoder_mem {C : M → Fin n → A} {J : Finset ((Fin n → A) × (Fin n → B))}
    (m₀ : M) {m : M} {y : Fin n → B} (hm : (C m, y) ∈ J) :
    (C (typicalDecoder C J m₀ y), y) ∈ J := by
  have he : ∃ m, (C m, y) ∈ J := ⟨m, hm⟩
  simp only [typicalDecoder, he, dite_true]
  exact he.choose_spec

theorem ite_comp_typicalDecoder_le {M' : Type*} [Fintype M] [DecidableEq M'] [DecidableEq A]
    [DecidableEq B] (π : M → M') (C : M → Fin n → A) (J : Finset ((Fin n → A) × (Fin n → B)))
    (m₀ m : M) (y : Fin n → B) {b : ℝ} (hb : 0 ≤ b) :
    (if π (typicalDecoder C J m₀ y) = π m then 0 else b) ≤
      (if (C m, y) ∈ J then 0 else b) +
        ∑ m' with π m' ≠ π m, (if (C m', y) ∈ J then (1 : ℝ) else 0) * b := by
  have hs : 0 ≤ ∑ m' with π m' ≠ π m, (if (C m', y) ∈ J then (1 : ℝ) else 0) * b :=
    sum_nonneg fun m' _ => mul_nonneg (by split_ifs <;> norm_num) hb
  by_cases hd : π (typicalDecoder C J m₀ y) = π m
  · rw [ite_eq_left hd]
    exact add_nonneg (by split_ifs <;> simp [hb]) hs
  rw [ite_eq_right hd]
  by_cases hm : (C m, y) ∈ J
  · rw [ite_eq_left hm, zero_add]
    have hmem := typicalDecoder_mem m₀ hm
    calc b = (if (C (typicalDecoder C J m₀ y), y) ∈ J then (1 : ℝ) else 0) * b := by simp [hmem]
      _ ≤ _ := single_le_sum (f := fun m' => (if (C m', y) ∈ J then (1 : ℝ) else 0) * b)
          (fun m' _ => mul_nonneg (by split_ifs <;> norm_num) hb) (mem_filter.2 ⟨mem_univ _, hd⟩)
  · rw [ite_eq_right hm]
    exact le_add_of_nonneg_right hs

theorem errorProb_typicalCode_toReal_le [Fintype B] [Fintype M] [DecidableEq M] [DecidableEq A]
    [DecidableEq B] (W : DMC A B) (C : M → Fin n → A) (J : Finset ((Fin n → A) × (Fin n → B)))
    (m₀ m : M) :
    ((typicalCode C J m₀).errorProb W m).toReal ≤
      ∑ y, (if (C m, y) ∈ J then 0 else (DMC.blockProb W (C m) y).toReal) +
        ∑ m' ∈ univ.erase m, ∑ y,
          (if (C m', y) ∈ J then (1 : ℝ) else 0) * (DMC.blockProb W (C m) y).toReal := by
  rw [errorProb_toReal, ← filter_ne', sum_comm (s := univ.filter fun m' => m' ≠ m),
    ← sum_add_distrib]
  exact sum_le_sum fun y _ => ite_comp_typicalDecoder_le id C J m₀ m y ENNReal.toReal_nonneg

end BlockCode

namespace DMC

variable {A B M : Type*}

theorem sum_iidProb_mul_sum_ite_jointPMF [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (W : DMC A B) (q : PMF A) (J : Finset ((Fin n → A) × (Fin n → B))) :
    ∑ x, iidProb q x * ∑ y, (if (x, y) ∈ J then 0 else (blockProb W x y).toReal) =
      1 - ∑ xy ∈ J, iidProb (jointPMF W q) (fun i => (xy.1 i, xy.2 i)) := by
  rw [← sum_iidProb_pair (jointPMF W q) n, ← sum_ite_mem_zero, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  split_ifs <;> simp [iidProb_jointPMF]

theorem sum_iidProb_mul_iidProb_mul_sum_le [Fintype A] [MeasurableSpace A] [Fintype B]
    [MeasurableSpace B] [DecidableEq A] [DecidableEq B] (W : DMC A B) (q : PMF A) (n : ℕ)
    (ε : ℝ) :
    ∑ x : Fin n → A, ∑ x' : Fin n → A, iidProb q x * iidProb q x' *
        ∑ y, (if (x', y) ∈ jointlyTypicalSet (jointPMF W q) n ε then (1 : ℝ) else 0) *
          (blockProb W x y).toReal ≤
      Real.exp (-(n * (W.inputMutualInfo q - 3 * ε))) := by
  have hB := sum_iidProb_mul_iidProb_jointlyTypicalSet_le (jointPMF W q) n ε
  rw [jointPMF_map_fst] at hB
  refine Eq.trans_le ?_ hB
  conv_rhs => rw [← Fintype.sum_ite_mem, Fintype.sum_prod_type]
  set J := jointlyTypicalSet (jointPMF W q) n ε
  have hr : ∀ y : Fin n → B, ∑ x, iidProb q x * (blockProb W x y).toReal =
      iidProb ((jointPMF W q).map Prod.snd) y := by
    intro y
    rw [← sum_iidProb_pair_left]
    exact sum_congr rfl fun x _ => (iidProb_jointPMF W q x y).symm
  calc _ = ∑ x' : Fin n → A, ∑ y : Fin n → B, ∑ x : Fin n → A,
        (if (x', y) ∈ J then iidProb q x' else 0) * (iidProb q x * (blockProb W x y).toReal) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun x' _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
        split_ifs <;> ring
    _ = _ := by
        refine sum_congr rfl fun x' _ => sum_congr rfl fun y _ => ?_
        rw [← mul_sum, hr]
        split_ifs <;> simp

theorem sum_errorProb_typicalCode_le [Fintype A] [MeasurableSpace A] [Fintype B]
    [MeasurableSpace B] [Fintype M] [DecidableEq M] {n : ℕ} (W : DMC A B) (q : PMF A) (ε : ℝ)
    (m₀ m : M) :
    ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) *
        ((BlockCode.typicalCode C (jointlyTypicalSet (jointPMF W q) n ε) m₀).errorProb W m).toReal ≤
      (1 - ∑ xy ∈ jointlyTypicalSet (jointPMF W q) n ε,
          iidProb (jointPMF W q) (fun i => (xy.1 i, xy.2 i))) +
        (Fintype.card M - 1) * Real.exp (-(n * (W.inputMutualInfo q - 3 * ε))) := by
  classical
  have : Nonempty M := ⟨m⟩
  set J := jointlyTypicalSet (jointPMF W q) n ε
  set e := Real.exp (-(n * (W.inputMutualInfo q - 3 * ε)))
  have hw : ∀ C : M → Fin n → A, 0 ≤ ∏ j, iidProb q (C j) :=
    fun C => prod_nonneg fun j _ => iidProb_nonneg q _
  have h1 : ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) *
      ∑ y, (if (C m, y) ∈ J then 0 else (blockProb W (C m) y).toReal) =
        ∑ x, iidProb q x * ∑ y, (if (x, y) ∈ J then 0 else (blockProb W x y).toReal) :=
    sum_prod_mul_apply (fun _ x => iidProb q x) (fun _ => sum_iidProb q n)
      (fun x => ∑ y, if (x, y) ∈ J then 0 else (blockProb W x y).toReal) m
  have h2 : ∀ m' ∈ univ.erase m, ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) *
      ∑ y, (if (C m', y) ∈ J then (1 : ℝ) else 0) * (blockProb W (C m) y).toReal =
        ∑ x, ∑ x', iidProb q x * iidProb q x' *
          ∑ y, (if (x', y) ∈ J then (1 : ℝ) else 0) * (blockProb W x y).toReal :=
    fun m' hm' => sum_prod_mul_apply_apply (fun _ x => iidProb q x) (fun _ => sum_iidProb q n)
      (fun x x' => ∑ y, (if (x', y) ∈ J then (1 : ℝ) else 0) * (blockProb W x y).toReal)
      (Ne.symm (ne_of_mem_erase hm'))
  calc _ ≤ ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) *
        (∑ y, (if (C m, y) ∈ J then 0 else (blockProb W (C m) y).toReal) +
          ∑ m' ∈ univ.erase m, ∑ y,
            (if (C m', y) ∈ J then (1 : ℝ) else 0) * (blockProb W (C m) y).toReal) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left
          (BlockCode.errorProb_typicalCode_toReal_le W C J m₀ m) (hw C)
    _ = ∑ x, iidProb q x * ∑ y, (if (x, y) ∈ J then 0 else (blockProb W x y).toReal) +
        ∑ m' ∈ univ.erase m, ∑ x, ∑ x', iidProb q x * iidProb q x' *
          ∑ y, (if (x', y) ∈ J then (1 : ℝ) else 0) * (blockProb W x y).toReal := by
      have h3 : ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) * ∑ m' ∈ univ.erase m, ∑ y,
          (if (C m', y) ∈ J then (1 : ℝ) else 0) * (blockProb W (C m) y).toReal =
            ∑ m' ∈ univ.erase m, ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) *
              ∑ y, (if (C m', y) ∈ J then (1 : ℝ) else 0) * (blockProb W (C m) y).toReal := by
        simp only [mul_sum]
        exact sum_comm
      rw [← h1, ← sum_congr rfl h2, ← h3, ← sum_add_distrib]
      exact sum_congr rfl fun C _ => mul_add _ _ _
    _ ≤ (1 - ∑ xy ∈ J, iidProb (jointPMF W q) (fun i => (xy.1 i, xy.2 i))) +
        ∑ m' ∈ univ.erase m, e := by
      rw [sum_iidProb_mul_sum_ite_jointPMF]
      exact add_le_add le_rfl
        (sum_le_sum fun m' _ => sum_iidProb_mul_iidProb_mul_sum_le W q n ε)
    _ = _ := by
      rw [sum_const, card_erase_of_mem (mem_univ m), card_univ, nsmul_eq_mul,
        Nat.cast_sub Fintype.card_pos, Nat.cast_one]

theorem exists_typicalCode_avgError_le [Fintype A] [MeasurableSpace A] [Fintype B]
    [MeasurableSpace B] [Fintype M] [DecidableEq M] {n : ℕ} (W : DMC A B) (q : PMF A) (ε : ℝ)
    (m₀ : M) :
    ∃ C : M → Fin n → A,
      (BlockCode.typicalCode C (jointlyTypicalSet (jointPMF W q) n ε) m₀).avgError W ≤
        ENNReal.ofReal ((1 - ∑ xy ∈ jointlyTypicalSet (jointPMF W q) n ε,
            iidProb (jointPMF W q) (fun i => (xy.1 i, xy.2 i))) +
          (Fintype.card M - 1) * Real.exp (-(n * (W.inputMutualInfo q - 3 * ε)))) := by
  have : Nonempty M := ⟨m₀⟩
  set J := jointlyTypicalSet (jointPMF W q) n ε
  set β := (1 - ∑ xy ∈ J, iidProb (jointPMF W q) (fun i => (xy.1 i, xy.2 i))) +
    (Fintype.card M - 1) * Real.exp (-(n * (W.inputMutualInfo q - 3 * ε)))
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le
    (w := fun C : M → Fin n → A => ∏ j, iidProb q (C j))
    (f := fun C => ∑ m, ((BlockCode.typicalCode C J m₀).errorProb W m).toReal)
    (t := Fintype.card M * β) (fun C => prod_nonneg fun j _ => iidProb_nonneg q _)
    (sum_prod _ fun _ => sum_iidProb q n) (by
      simp only [mul_sum]
      rw [sum_comm]
      calc _ ≤ ∑ m : M, β := sum_le_sum fun m _ => sum_errorProb_typicalCode_le W q ε m₀ m
        _ = _ := by simp)
  exact ⟨C, BlockCode.avgError_le_ofReal _ W hC⟩

theorem achievable_of_lt_inputMutualInfo [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (W : DMC A B) {R : ℝ} (q : PMF A) (h : R < W.inputMutualInfo q) : W.Achievable R := by
  intro ε hε
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  set I := W.inputMutualInfo q
  set η := (I - R) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set p := jointPMF W q
  have hJ : Tendsto (fun n : ℕ => 1 - ∑ xy ∈ jointlyTypicalSet p n η,
      iidProb p (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_jointlyTypicalSet p hη0)
  have hE := tendsto_exp_nat_mul (show R - (I - 3 * η) < 0 by rw [hη]; linarith)
  have hsum := hJ.add hE
  rw [add_zero] at hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  set k := ⌈Real.exp (n * R)⌉₊
  have hk : 0 < k := Nat.ceil_pos.2 (Real.exp_pos _)
  have hk1 : (k : ℝ) - 1 ≤ Real.exp (n * R) := by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R)).le]
  refine ⟨k, Nat.le_ceil _, ?_⟩
  obtain ⟨C, hC⟩ := exists_typicalCode_avgError_le (n := n) W q η (⟨0, hk⟩ : Fin k)
  refine ⟨_, hC.trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hδε.le)⟩
  have h2 : ((k : ℝ) - 1) * Real.exp (-(n * (I - 3 * η))) ≤ Real.exp (n * (R - (I - 3 * η))) :=
    calc _ ≤ Real.exp (n * R) * Real.exp (-(n * (I - 3 * η))) :=
          mul_le_mul_of_nonneg_right hk1 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; ring_nf
  rw [Fintype.card_fin]
  linarith [hN n hn]

theorem achievable_of_lt_capacity [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] (W : DMC A B) {R : ℝ}
    (h0 : 0 ≤ R) (h : R < W.capacity) : W.Achievable R := by
  rcases isEmpty_or_nonempty (PMF A) with hA | hA
  · rw [capacity, Real.iSup_of_isEmpty] at h
    linarith
  · obtain ⟨q, hq⟩ := exists_lt_of_lt_ciSup h
    exact achievable_of_lt_inputMutualInfo W q hq

theorem achievable_zero [Nonempty A] [Fintype B] (W : DMC A B) : W.Achievable 0 := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨1, by simp, ⟨fun _ _ => Classical.arbitrary A, fun _ => 0⟩, ?_⟩⟩
  simp [BlockCode.avgError, BlockCode.errorProb]

end DMC

theorem exp_mul_max_le {n k : ℕ} {R : ℝ} (h : Real.exp (n * R) ≤ k) :
    Real.exp (n * max R 0) ≤ k := by
  rcases le_total R 0 with hR | hR
  · rw [max_eq_right hR, mul_zero, Real.exp_zero]
    have hk : (0 : ℝ) < k := (Real.exp_pos _).trans_le h
    exact Nat.one_le_cast.2 (Nat.cast_pos.1 hk)
  · rwa [max_eq_left hR]

end Meat
