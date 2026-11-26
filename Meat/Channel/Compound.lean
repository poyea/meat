import Meat.Channel.CodingTheorem
import Meat.Open.Interactive

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

section Typical

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
private lemma mutualInfo_fst_snd (p : PMF (S × T)) :
    mutualInfo (fun ω : S × T => ω.1) (fun ω => ω.2) p.toMeasure
      = measureEntropy (p.map Prod.fst).toMeasure + measureEntropy (p.map Prod.snd).toMeasure
        - measureEntropy p.toMeasure := by
  simp only [mutualInfo, entropy]
  have h : p.toMeasure.map (fun ω : S × T => (ω.1, ω.2)) = p.toMeasure := Measure.map_id'
  rw [h, PMF.toMeasure_map (f := Prod.fst) (p := p) (hf := measurable_fst),
    PMF.toMeasure_map (f := Prod.snd) (p := p) (hf := measurable_snd)]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem sum_filter_jointlyTypicalSet_le [DecidableEq S] [DecidableEq T] (p : PMF (S × T))
    (n : ℕ) (ε : ℝ) (y : Fin n → T) :
    ∑ x ∈ univ.filter (fun x => (x, y) ∈ jointlyTypicalSet p n ε), iidProb (p.map Prod.fst) x ≤
      Real.exp (-(n * (mutualInfo (fun ω : S × T => ω.1) (fun ω => ω.2) p.toMeasure
        - 3 * ε))) := by
  have hI := mutualInfo_fst_snd p
  set HX := measureEntropy (p.map Prod.fst).toMeasure
  set HY := measureEntropy (p.map Prod.snd).toMeasure
  set HXY := measureEntropy p.toMeasure
  by_cases hy : ∃ x, (x, y) ∈ jointlyTypicalSet p n ε
  · obtain ⟨x0, hx0⟩ := hy
    have hY : iidProb (p.map Prod.snd) y ≤ Real.exp (-(n * (HY - ε))) := by
      simp only [jointlyTypicalSet, typicalSet, mem_filter, mem_univ, true_and] at hx0
      exact hx0.2.1.2
    set c := Real.exp (-(n * (HX - ε))) * Real.exp (n * (HXY + ε)) with hcdef
    have hc : 0 ≤ c := by positivity
    have hterm : ∀ x ∈ univ.filter (fun x => (x, y) ∈ jointlyTypicalSet p n ε),
        iidProb (p.map Prod.fst) x ≤ c * iidProb p (fun i => (x i, y i)) := by
      intro x hx
      simp only [jointlyTypicalSet, typicalSet, mem_filter, mem_univ, true_and] at hx
      have h1 := hx.1.2
      have h2 := hx.2.2.1
      have he : Real.exp (n * (HXY + ε)) * Real.exp (-(n * (HXY + ε))) = 1 := by
        rw [← Real.exp_add]
        simp
      calc iidProb (p.map Prod.fst) x ≤ Real.exp (-(n * (HX - ε))) := h1
        _ = c * Real.exp (-(n * (HXY + ε))) := by rw [mul_assoc, he, mul_one]
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 hc
    calc _ ≤ ∑ x ∈ univ.filter (fun x => (x, y) ∈ jointlyTypicalSet p n ε),
          c * iidProb p (fun i => (x i, y i)) := sum_le_sum hterm
      _ ≤ ∑ x : Fin n → S, c * iidProb p (fun i => (x i, y i)) :=
          sum_le_univ_sum_of_nonneg fun x => mul_nonneg hc (iidProb_nonneg p fun i => (x i, y i))
      _ = c * iidProb (p.map Prod.snd) y := by rw [← mul_sum, sum_iidProb_pair_left]
      _ ≤ c * Real.exp (-(n * (HY - ε))) := mul_le_mul_of_nonneg_left hY hc
      _ = _ := by
          rw [hI, hcdef, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  · push Not at hy
    rw [filter_false_of_mem fun x _ => hy x, sum_empty]
    exact (Real.exp_pos _).le

end Typical

namespace DMC

variable {A B : Type*}

theorem sum_iidProb_mul_iidProb_mul_sum_cross_le [Fintype A] [MeasurableSpace A] [Fintype B]
    [MeasurableSpace B] [DecidableEq A] [DecidableEq B] (W V : DMC A B) (q : PMF A) (n : ℕ)
    (ε : ℝ) :
    ∑ x : Fin n → A, ∑ x' : Fin n → A, iidProb q x * iidProb q x' *
        ∑ y, (if (x', y) ∈ jointlyTypicalSet (jointPMF V q) n ε then (1 : ℝ) else 0) *
          (blockProb W x y).toReal ≤
      Real.exp (-(n * (V.inputMutualInfo q - 3 * ε))) := by
  set J := jointlyTypicalSet (jointPMF V q) n ε
  set e := Real.exp (-(n * (V.inputMutualInfo q - 3 * ε)))
  have hA : ∀ y : Fin n → B,
      ∑ x', iidProb q x' * (if (x', y) ∈ J then (1 : ℝ) else 0) ≤ e := by
    intro y
    have h := sum_filter_jointlyTypicalSet_le (jointPMF V q) n ε y
    rw [jointPMF_map_fst] at h
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    exact h
  have hw : ∀ x : Fin n → A, ∑ y, (blockProb W x y).toReal = 1 := fun x => by
    rw [← ENNReal.toReal_sum fun y _ => blockProb_ne_top W x y, sum_blockProb_eq_one,
      ENNReal.toReal_one]
  calc _ = ∑ x, iidProb q x * ∑ y, (blockProb W x y).toReal *
        ∑ x', iidProb q x' * (if (x', y) ∈ J then (1 : ℝ) else 0) := by
        refine sum_congr rfl fun x _ => ?_
        simp_rw [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun y _ => sum_congr rfl fun x' _ => by ring
    _ ≤ ∑ x, iidProb q x * ∑ y, (blockProb W x y).toReal * e := by
        gcongr with x _ y _
        · exact iidProb_nonneg q x
        · exact hA y
    _ = e := by
        simp_rw [← sum_mul, hw, one_mul]
        rw [← sum_mul, sum_iidProb, one_mul]

end DMC

namespace Compound

variable {S A B : Type*}

def Achievable [Fintype B] (W : S → DMC A B) (R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : BlockCode (Fin k) A B n, ∀ s, c.avgError (W s) ≤ ε

noncomputable def capacity [Fintype A] [MeasurableSpace A] [Fintype B] [MeasurableSpace B]
    (W : S → DMC A B) : ℝ :=
  ⨆ p : PMF A, ⨅ s, (W s).inputMutualInfo p

section Info

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

private lemma bddBelow_range (W : S → DMC A B) (p : PMF A) :
    BddBelow (Set.range fun s => (W s).inputMutualInfo p) :=
  ⟨0, Set.forall_mem_range.2 fun s => (W s).inputMutualInfo_nonneg p⟩

private lemma bddAbove_range [Nonempty S] (W : S → DMC A B) :
    BddAbove (Set.range fun p : PMF A => ⨅ s, (W s).inputMutualInfo p) :=
  ⟨Real.log (Fintype.card A), Set.forall_mem_range.2 fun p =>
    (ciInf_le (bddBelow_range W p) (Classical.arbitrary S)).trans
      ((W _).inputMutualInfo_le_log_card p)⟩

theorem capacity_nonneg (W : S → DMC A B) : 0 ≤ capacity W :=
  Real.iSup_nonneg fun p => Real.iInf_nonneg fun s => (W s).inputMutualInfo_nonneg p

theorem iInf_inputMutualInfo_le_capacity [Nonempty S] (W : S → DMC A B) (p : PMF A) :
    ⨅ s, (W s).inputMutualInfo p ≤ capacity W :=
  le_ciSup (bddAbove_range W) p

end Info

section Converse

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem _root_.Meat.DMC.sum_inputMutualInfo_le {k : ℕ} [NeZero k] (W : DMC A B)
    (p : Fin k → PMF A) :
    (k : ℝ)⁻¹ * ∑ q, W.inputMutualInfo (p q) ≤
      W.inputMutualInfo ((Interactive.uniformPMF k).bind p) := by
  have hI : ∀ r, W.inputMutualInfo r =
      H[Prod.snd ; W.jointMeasure r] - H[Prod.snd | Prod.fst ; W.jointMeasure r] := fun r => by
    rw [DMC.inputMutualInfo, mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy]
  have h1 := Interactive.condEntropy_jointMeasure_avg W p
  have h2 := Interactive.sum_entropy_le (fun q => DMC.jointPMF W (p q)) Prod.snd
  rw [← Interactive.jointPMF_bind] at h2
  simp only [← DMC.jointMeasure_eq_toMeasure] at h2
  simp only [hI, sum_sub_distrib, mul_sub]
  linarith

private lemma one_sub_mul_log_card_le_sum {M : Type*} {n : ℕ} [Fintype M] [Nonempty M]
    [MeasurableSpace M] [MeasurableSingletonClass M] [DecidableEq M] (c : BlockCode M A B n)
    (W : DMC A B) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card M) ≤
      ∑ i, W.inputMutualInfo (c.inputLaw i) + Real.log 2 := by
  have h1 := c.mutualInfo_le_sum_inputMutualInfo W
  have h2 := c.condEntropy_fst_snd_codeMeasure_le W
  have h3 := mutualInfo_eq_entropy_sub_condEntropy Prod.fst Prod.snd (c.codeMeasure W)
  rw [BlockCode.entropy_fst_codeMeasure] at h3
  have h4 : (1 - (c.avgError W).toReal) * Real.log (Fintype.card M)
      = Real.log (Fintype.card M) - (c.avgError W).toReal * Real.log (Fintype.card M) := by ring
  linarith

private lemma exists_one_sub_mul_log_card_le [Finite S] [Nonempty S] {M : Type*} {n : ℕ}
    [NeZero n] [Fintype M] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M]
    [DecidableEq M] (c : BlockCode M A B n) (W : S → DMC A B) :
    ∃ s, (1 - (c.avgError (W s)).toReal) * Real.log (Fintype.card M) ≤
      n * capacity W + Real.log 2 := by
  set p := (Interactive.uniformPMF n).bind c.inputLaw
  obtain ⟨s, hs⟩ := exists_eq_ciInf_of_finite (f := fun s => (W s).inputMutualInfo p)
  refine ⟨s, (one_sub_mul_log_card_le_sum c (W s)).trans (add_le_add_left ?_ _)⟩
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hc := (W s).sum_inputMutualInfo_le c.inputLaw
  have hC := iInf_inputMutualInfo_le_capacity W p
  rw [← hs] at hC
  rw [inv_mul_le_iff₀ hn] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left hC hn.le)

theorem le_capacity_of_achievable [Finite S] [Nonempty S] (W : S → DMC A B) {R : ℝ}
    (h : Achievable W R) : R ≤ capacity W := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hC := capacity_nonneg W
  set C := capacity W
  set δ := R - C with hδ
  have hδ0 : 0 < δ := by linarith
  have hR : 0 < R := by linarith
  set e := δ / (2 * R) with he
  have he0 : 0 < e := by positivity
  have he1 : e * R = δ / 2 := by
    rw [he]
    field_simp
  have he2 : 0 < 1 - e := by nlinarith
  obtain ⟨N, hN⟩ := h (ENNReal.ofReal e) (ENNReal.ofReal_pos.2 he0)
  obtain ⟨n0, hn0⟩ := exists_nat_gt (2 * Real.log 2 / δ)
  obtain ⟨n, hNn, hn0n⟩ : ∃ n : ℕ, N ≤ n ∧ n0 ≤ n := ⟨max N n0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hNn
  have hn : 2 * Real.log 2 < n * δ := by
    rw [← div_lt_iff₀ hδ0]
    exact hn0.trans_le (by exact_mod_cast hn0n)
  have hn1 : n ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, zero_mul] at hn
    linarith [Real.log_pos one_lt_two]
  have : NeZero n := ⟨hn1⟩
  have hk0 : (0 : ℝ) < k := (Real.exp_pos _).trans_le hk
  have : Nonempty (Fin k) := ⟨⟨0, by exact_mod_cast hk0⟩⟩
  obtain ⟨s, key⟩ := exists_one_sub_mul_log_card_le c W
  rw [Fintype.card_fin] at key
  have hPe : (c.avgError (W s)).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le (hc s)
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1 : (1 - e) * Real.log k ≤ n * C + Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)).trans key
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

end Converse

section Achievability

variable [Fintype A] [MeasurableSpace A] [Fintype B] [MeasurableSpace B]

private noncomputable def unionSet [Fintype S] [DecidableEq A] [DecidableEq B] (W : S → DMC A B)
    (q : PMF A) (n : ℕ) (ε : ℝ) : Finset ((Fin n → A) × (Fin n → B)) :=
  univ.biUnion fun s => jointlyTypicalSet (DMC.jointPMF (W s) q) n ε

private lemma ite_unionSet_le [Fintype S] [DecidableEq A] [DecidableEq B] (W : S → DMC A B)
    (q : PMF A) {n : ℕ} (ε : ℝ)
    (xy : (Fin n → A) × (Fin n → B)) :
    (if xy ∈ unionSet W q n ε then (1 : ℝ) else 0) ≤
      ∑ s, if xy ∈ jointlyTypicalSet (DMC.jointPMF (W s) q) n ε then (1 : ℝ) else 0 := by
  split_ifs with h
  · simp only [unionSet] at h
    obtain ⟨s, -, hs⟩ := mem_biUnion.1 h
    calc (1 : ℝ) = if xy ∈ jointlyTypicalSet (DMC.jointPMF (W s) q) n ε then 1 else 0 := by
          simp [hs]
      _ ≤ _ := single_le_sum (f := fun s =>
          if xy ∈ jointlyTypicalSet (DMC.jointPMF (W s) q) n ε then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) (mem_univ s)
  · exact sum_nonneg fun _ _ => by split_ifs <;> norm_num

private lemma sum_errorProb_le [Fintype S] [DecidableEq A] [DecidableEq B] {M : Type*}
    [Fintype M] [DecidableEq M] {n : ℕ}
    (W : S → DMC A B) (q : PMF A) (ε : ℝ) (m₀ m : M) (s : S) :
    ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) *
        ((BlockCode.typicalCode C (unionSet W q n ε) m₀).errorProb (W s) m).toReal ≤
      (1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (W s) q) n ε,
          iidProb (DMC.jointPMF (W s) q) (fun i => (xy.1 i, xy.2 i))) +
        (Fintype.card M - 1) * ∑ s', Real.exp (-(n * ((W s').inputMutualInfo q - 3 * ε))) := by
  have : Nonempty M := ⟨m⟩
  set J := unionSet W q n ε
  set Js := jointlyTypicalSet (DMC.jointPMF (W s) q) n ε
  set e := ∑ s', Real.exp (-(n * ((W s').inputMutualInfo q - 3 * ε)))
  set V := W s
  have hw : ∀ C : M → Fin n → A, 0 ≤ ∏ j, iidProb q (C j) :=
    fun C => prod_nonneg fun j _ => iidProb_nonneg q _
  have h1 : ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) *
      ∑ y, (if (C m, y) ∈ J then 0 else (DMC.blockProb V (C m) y).toReal) =
        ∑ x, iidProb q x * ∑ y, (if (x, y) ∈ J then 0 else (DMC.blockProb V x y).toReal) :=
    sum_prod_mul_apply (fun _ x => iidProb q x) (fun _ => sum_iidProb q n)
      (fun x => ∑ y, if (x, y) ∈ J then 0 else (DMC.blockProb V x y).toReal) m
  have h2 : ∀ m' ∈ univ.erase m, ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) *
      ∑ y, (if (C m', y) ∈ J then (1 : ℝ) else 0) * (DMC.blockProb V (C m) y).toReal =
        ∑ x, ∑ x', iidProb q x * iidProb q x' *
          ∑ y, (if (x', y) ∈ J then (1 : ℝ) else 0) * (DMC.blockProb V x y).toReal :=
    fun m' hm' => sum_prod_mul_apply_apply (fun _ x => iidProb q x) (fun _ => sum_iidProb q n)
      (fun x x' => ∑ y, (if (x', y) ∈ J then (1 : ℝ) else 0) * (DMC.blockProb V x y).toReal)
      (Ne.symm (ne_of_mem_erase hm'))
  have hsub : Js ⊆ J := fun xy hxy => by
    simp only [J, unionSet]
    exact mem_biUnion.2 ⟨s, mem_univ s, hxy⟩
  have hfirst : ∑ x, iidProb q x * ∑ y, (if (x, y) ∈ J then 0 else (DMC.blockProb V x y).toReal)
      ≤ 1 - ∑ xy ∈ Js, iidProb (DMC.jointPMF V q) (fun i => (xy.1 i, xy.2 i)) := by
    rw [← DMC.sum_iidProb_mul_sum_ite_jointPMF]
    gcongr with x _ y _
    · exact iidProb_nonneg q x
    · by_cases h : (x, y) ∈ Js
      · simp [h, hsub h]
      · simp only [h, ↓reduceIte]
        split_ifs <;> simp
  have hcross : ∑ x : Fin n → A, ∑ x' : Fin n → A, iidProb q x * iidProb q x' *
      ∑ y, (if (x', y) ∈ J then (1 : ℝ) else 0) * (DMC.blockProb V x y).toReal ≤ e := by
    calc _ ≤ ∑ x : Fin n → A, ∑ x' : Fin n → A, iidProb q x * iidProb q x' *
          ∑ y, (∑ s', if (x', y) ∈ jointlyTypicalSet (DMC.jointPMF (W s') q) n ε
            then (1 : ℝ) else 0) * (DMC.blockProb V x y).toReal := by
          gcongr with x _ x' _ y _
          · exact mul_nonneg (iidProb_nonneg q x) (iidProb_nonneg q x')
          · exact ite_unionSet_le W q ε (x', y)
      _ = ∑ s', ∑ x : Fin n → A, ∑ x' : Fin n → A, iidProb q x * iidProb q x' *
          ∑ y, (if (x', y) ∈ jointlyTypicalSet (DMC.jointPMF (W s') q) n ε
            then (1 : ℝ) else 0) * (DMC.blockProb V x y).toReal := by
          simp only [sum_mul, mul_sum]
          refine ((sum_congr rfl fun x _ =>
            (sum_congr rfl fun x' _ => sum_comm).trans sum_comm)).trans sum_comm
      _ ≤ e := sum_le_sum fun s' _ =>
          DMC.sum_iidProb_mul_iidProb_mul_sum_cross_le V (W s') q n ε
  calc _ ≤ ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) *
        (∑ y, (if (C m, y) ∈ J then 0 else (DMC.blockProb V (C m) y).toReal) +
          ∑ m' ∈ univ.erase m, ∑ y,
            (if (C m', y) ∈ J then (1 : ℝ) else 0) * (DMC.blockProb V (C m) y).toReal) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left
          (BlockCode.errorProb_typicalCode_toReal_le V C J m₀ m) (hw C)
    _ = ∑ x, iidProb q x * ∑ y, (if (x, y) ∈ J then 0 else (DMC.blockProb V x y).toReal) +
        ∑ m' ∈ univ.erase m, ∑ x, ∑ x', iidProb q x * iidProb q x' *
          ∑ y, (if (x', y) ∈ J then (1 : ℝ) else 0) * (DMC.blockProb V x y).toReal := by
      have h3 : ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) * ∑ m' ∈ univ.erase m, ∑ y,
          (if (C m', y) ∈ J then (1 : ℝ) else 0) * (DMC.blockProb V (C m) y).toReal =
            ∑ m' ∈ univ.erase m, ∑ C : M → Fin n → A, (∏ j, iidProb q (C j)) *
              ∑ y, (if (C m', y) ∈ J then (1 : ℝ) else 0) *
                (DMC.blockProb V (C m) y).toReal := by
        simp only [mul_sum]
        exact sum_comm
      rw [← h1, ← sum_congr rfl h2, ← h3, ← sum_add_distrib]
      exact sum_congr rfl fun C _ => mul_add _ _ _
    _ ≤ (1 - ∑ xy ∈ Js, iidProb (DMC.jointPMF V q) (fun i => (xy.1 i, xy.2 i))) +
        ∑ m' ∈ univ.erase m, e := add_le_add hfirst (sum_le_sum fun m' _ => hcross)
    _ = _ := by
      rw [sum_const, card_erase_of_mem (mem_univ m), card_univ, nsmul_eq_mul,
        Nat.cast_sub Fintype.card_pos, Nat.cast_one]

variable [MeasurableSingletonClass A] [MeasurableSingletonClass B]

theorem achievable_of_lt_capacity [Finite S] [Nonempty A] (W : S → DMC A B)
    {R : ℝ} (h : R < capacity W) : Achievable W R := by
  classical
  have := Fintype.ofFinite S
  intro ε hε
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  obtain ⟨q, hq⟩ := exists_lt_of_lt_ciSup h
  set I0 := ⨅ s, (W s).inputMutualInfo q
  have hI : ∀ s, I0 ≤ (W s).inputMutualInfo q := fun s => ciInf_le (bddBelow_range W q) s
  set η := (I0 - R) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hJ : ∀ s, Tendsto (fun n : ℕ => 1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (W s) q) n η,
      iidProb (DMC.jointPMF (W s) q) (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 0) := fun s => by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_jointlyTypicalSet (DMC.jointPMF (W s) q) hη0)
  have hE : ∀ s, Tendsto (fun n : ℕ =>
      Real.exp (n * (R - ((W s).inputMutualInfo q - 3 * η)))) atTop (𝓝 0) := fun s =>
    tendsto_exp_nat_mul (by have := hI s; rw [hη] at *; linarith)
  have hsum : Tendsto (fun n : ℕ => ∑ s, ((1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (W s) q) n η,
      iidProb (DMC.jointPMF (W s) q) (fun i => (xy.1 i, xy.2 i))) +
        ∑ s', Real.exp (n * (R - ((W s').inputMutualInfo q - 3 * η))))) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum univ fun s _ =>
      (hJ s).add (tendsto_finsetSum univ fun s' _ => hE s')
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  set k := ⌈Real.exp (n * R)⌉₊
  have hk : 0 < k := Nat.ceil_pos.2 (Real.exp_pos _)
  have hk1 : (k : ℝ) - 1 ≤ Real.exp (n * R) := by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R)).le]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine ⟨k, Nat.le_ceil _, ?_⟩
  set m₀ : Fin k := ⟨0, hk⟩
  set β := ∑ s, ((1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (W s) q) n η,
      iidProb (DMC.jointPMF (W s) q) (fun i => (xy.1 i, xy.2 i))) +
        ((k : ℝ) - 1) * ∑ s', Real.exp (-(n * ((W s').inputMutualInfo q - 3 * η))))
  have herr : ∀ (C : Fin k → Fin n → A) s m,
      0 ≤ ((BlockCode.typicalCode C (unionSet W q n η) m₀).errorProb (W s) m).toReal :=
    fun _ _ _ => ENNReal.toReal_nonneg
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le
    (w := fun C : Fin k → Fin n → A => ∏ j, iidProb q (C j))
    (f := fun C => ∑ s, ∑ m, ((BlockCode.typicalCode C (unionSet W q n η) m₀).errorProb
      (W s) m).toReal)
    (t := k * β) (fun C => prod_nonneg fun j _ => iidProb_nonneg q _)
    (sum_prod _ fun _ => sum_iidProb q n) (by
      simp only [mul_sum]
      rw [sum_comm]
      refine (sum_le_sum fun s _ => ?_).trans_eq (mul_sum _ _ _).symm
      rw [sum_comm]
      calc _ ≤ ∑ m : Fin k, ((1 - ∑ xy ∈ jointlyTypicalSet (DMC.jointPMF (W s) q) n η,
            iidProb (DMC.jointPMF (W s) q) (fun i => (xy.1 i, xy.2 i))) +
              ((Fintype.card (Fin k) : ℝ) - 1) *
                ∑ s', Real.exp (-(n * ((W s').inputMutualInfo q - 3 * η)))) :=
            sum_le_sum fun m _ => sum_errorProb_le W q η m₀ m s
        _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul])
  have hβ : β < δ := by
    refine lt_of_le_of_lt (sum_le_sum fun s _ => add_le_add le_rfl ?_) (hN n hn)
    rw [mul_sum]
    refine sum_le_sum fun s' _ => ?_
    calc ((k : ℝ) - 1) * Real.exp (-(n * ((W s').inputMutualInfo q - 3 * η)))
        ≤ Real.exp (n * R) * Real.exp (-(n * ((W s').inputMutualInfo q - 3 * η))) :=
          mul_le_mul_of_nonneg_right hk1 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have : Nonempty (Fin k) := ⟨m₀⟩
  refine ⟨BlockCode.typicalCode C (unionSet W q n η) m₀, fun s => ?_⟩
  have hs : ∑ m, ((BlockCode.typicalCode C (unionSet W q n η) m₀).errorProb (W s) m).toReal ≤
      Fintype.card (Fin k) * β := by
    rw [Fintype.card_fin]
    refine le_trans ?_ hC
    exact single_le_sum (f := fun s => ∑ m, ((BlockCode.typicalCode C (unionSet W q n η)
      m₀).errorProb (W s) m).toReal) (fun s _ => sum_nonneg fun m _ => herr C s m) (mem_univ s)
  exact (BlockCode.avgError_le_ofReal _ (W s) hs).trans
    ((ENNReal.ofReal_le_ofReal hβ.le).trans hδε.le)

omit [Fintype A] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A]
  [MeasurableSingletonClass B] in
theorem achievable_zero [Nonempty A] (W : S → DMC A B) : Achievable W 0 := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨1, by simp, ⟨fun _ _ => Classical.arbitrary A, fun _ => 0⟩,
    fun s => ?_⟩⟩
  simp [BlockCode.avgError, BlockCode.errorProb]

theorem closure_achievable_eq [Finite S] [Nonempty S] [Nonempty A] (W : S → DMC A B) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable W R} = Set.Icc 0 (capacity W) := by
  refine subset_antisymm (closure_minimal (fun R hR => ⟨hR.1, le_capacity_of_achievable W hR.2⟩)
    isClosed_Icc) fun R hR => ?_
  rcases (capacity_nonneg W).eq_or_lt with h | h
  · rw [← h, Set.Icc_self, Set.mem_singleton_iff] at hR
    exact subset_closure ⟨hR.symm ▸ le_rfl, hR ▸ achievable_zero W⟩
  · rw [← closure_Ico h.ne] at hR
    refine closure_mono (fun R (hR : R ∈ Set.Ico 0 (capacity W)) => ?_) hR
    exact ⟨hR.1, achievable_of_lt_capacity W hR.2⟩

end Achievability

end Compound

end Meat
