import Meat.Channel.Converse
import Meat.Shannon.Types

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace DMC

variable {A B : Type*}

noncomputable def outputLaw [Fintype A] (W : DMC A B) (P : A → ℝ) (b : B) : ℝ :=
  ∑ a, P a * (W a b).toReal

noncomputable def typeWeight [DecidableEq A] {n : ℕ} (x : Fin n → A) (a : A) : ℝ :=
  (typeCount x a : ℝ) / n

noncomputable def typePMF [Fintype A] [DecidableEq A] {n : ℕ} (hn : 0 < n) (x : Fin n → A) :
    PMF A :=
  PMF.ofFintype (fun a => (typeCount x a : ℝ≥0∞) / n) (by
    simp_rw [div_eq_mul_inv, ← sum_mul]
    rw [← Nat.cast_sum, sum_typeCount]
    exact ENNReal.mul_inv_cancel (by simp [hn.ne']) (ENNReal.natCast_ne_top n))

theorem typePMF_toReal [Fintype A] [DecidableEq A] {n : ℕ} (hn : 0 < n) (x : Fin n → A) (a : A) :
    (typePMF hn x a).toReal = typeWeight x a := by
  rw [typePMF, PMF.ofFintype_apply, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, typeWeight]

theorem sum_outputLaw [Fintype A] [Fintype B] (W : DMC A B) (P : A → ℝ) :
    ∑ b, outputLaw W P b = ∑ a, P a := by
  simp only [outputLaw]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [← mul_sum, ← ENNReal.toReal_sum fun b _ => (W a).apply_ne_top b, sum_pmf_eq_one,
    ENNReal.toReal_one, mul_one]

theorem outputLaw_nonneg [Fintype A] (W : DMC A B) {P : A → ℝ} (hP : ∀ a, 0 ≤ P a) (b : B) :
    0 ≤ outputLaw W P b :=
  sum_nonneg fun a _ => mul_nonneg (hP a) ENNReal.toReal_nonneg

theorem le_outputLaw [Fintype A] (W : DMC A B) {P : A → ℝ} (hP : ∀ a, 0 ≤ P a) (a : A) (b : B) :
    P a * (W a b).toReal ≤ outputLaw W P b :=
  single_le_sum (f := fun a => P a * (W a b).toReal)
    (fun a _ => mul_nonneg (hP a) ENNReal.toReal_nonneg) (mem_univ a)

theorem outputLaw_le_one [Fintype A] (W : DMC A B) {P : A → ℝ} (hP : ∀ a, 0 ≤ P a)
    (hP1 : ∑ a, P a = 1)
    (b : B) : outputLaw W P b ≤ 1 := by
  rw [← hP1]
  refine sum_le_sum fun a _ => ?_
  have : (W a b).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  nlinarith [hP a, (ENNReal.toReal_nonneg : 0 ≤ (W a b).toReal)]

theorem mul_log_sq_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) : p * Real.log p ^ 2 ≤ 2 := by
  set s := -Real.log p with hs
  have hs0 : 0 ≤ s := by
    rw [hs, neg_nonneg]
    exact Real.log_nonpos hp.le hp1
  have hp' : p = Real.exp (-s) := by rw [hs, neg_neg, Real.exp_log hp]
  have h := Real.pow_div_factorial_le_exp s hs0 2
  norm_num [Nat.factorial] at h
  have he : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hl : Real.log p ^ 2 = s ^ 2 := by rw [hs, neg_sq]
  rw [hl, hp']
  have := Real.exp_pos (-s)
  nlinarith

theorem sum_prod_mul_sq [Fintype B] {n : ℕ} (w : Fin n → B → ℝ) (h1 : ∀ t, ∑ b, w t b = 1)
    (f : Fin n → B → ℝ) (h0 : ∀ t, ∑ b, w t b * f t b = 0) :
    ∑ y : Fin n → B, (∏ t, w t (y t)) * (∑ t, f t (y t)) ^ 2 =
      ∑ t, ∑ b, w t b * f t b ^ 2 := by
  have key : ∀ s t : Fin n, ∑ y : Fin n → B, (∏ i, w i (y i)) * (f s (y s) * f t (y t)) =
      if s = t then ∑ b, w s b * f s b ^ 2 else 0 := by
    intro s t
    split_ifs with hst
    · subst hst
      have := sum_prod_mul_apply w h1 (fun b => f s b * f s b) s
      simpa [sq] using this
    · have := sum_prod_mul_apply_mul_apply w h1 (f s) (f t) hst
      rw [this, h0 s, zero_mul]
  simp_rw [sq, sum_mul_sum, mul_sum]
  rw [sum_comm]
  simp_rw [fun s => sum_comm (s := (univ : Finset (Fin n → B))) (t := univ)
    (f := fun y (t : Fin n) => (∏ i, w i (y i)) * (f s (y s) * f t (y t)))]
  simp [key, sq]

section TypeMix

variable [Fintype A] [DecidableEq A] [Fintype B]

def typeCounts (n : ℕ) : Finset (A → ℕ) :=
  univ.image fun x : Fin n → A => typeCount x

theorem card_typeCounts_le (n : ℕ) :
    ((typeCounts (A := A) n).card : ℝ) ≤ ((n : ℝ) + 1) ^ Fintype.card A := by
  have h : typeCounts (A := A) n ⊆ Fintype.piFinset fun _ => range (n + 1) := by
    intro k hk
    obtain ⟨x, -, rfl⟩ := mem_image.1 hk
    exact Fintype.mem_piFinset.2 fun a => mem_range.2 (Nat.lt_succ_of_le (typeCount_le x a))
  have := card_le_card h
  rw [Fintype.card_piFinset, prod_const, card_range, card_univ] at this
  exact_mod_cast this

noncomputable def typeMix (W : DMC A B) (n : ℕ) (y : Fin n → B) : ℝ :=
  (∑ k ∈ typeCounts n, ∏ t, outputLaw W (fun a => (k a : ℝ) / n) (y t)) /
    (typeCounts (A := A) n).card

noncomputable def outSeq {n : ℕ} (W : DMC A B) (x : Fin n → A) (y : Fin n → B) : ℝ :=
  ∏ t, outputLaw W (typeWeight x) (y t)

theorem sum_typeMix_le (W : DMC A B) (n : ℕ) : ∑ y, typeMix W n y ≤ 1 := by
  have h : ∀ k ∈ typeCounts (A := A) n,
      ∑ y : Fin n → B, ∏ t, outputLaw W (fun a => (k a : ℝ) / n) (y t) = 1 := by
    intro k hk
    obtain ⟨x, -, rfl⟩ := mem_image.1 hk
    rw [← Fintype.prod_sum]
    refine prod_eq_one fun t _ => ?_
    have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Fin.pos t)
    rw [sum_outputLaw, ← sum_div, ← Nat.cast_sum, sum_typeCount, div_self hn.ne']
  simp only [typeMix, ← sum_div]
  rw [sum_comm, sum_congr rfl h, sum_const, nsmul_eq_mul, mul_one]
  exact div_self_le_one _

omit [Fintype B] in
theorem outSeq_le_typeMix {n : ℕ} (W : DMC A B) (x : Fin n → A) (y : Fin n → B) :
    outSeq W x y ≤ (typeCounts (A := A) n).card * typeMix W n y := by
  have hx : typeCount x ∈ typeCounts n := mem_image.2 ⟨x, mem_univ _, rfl⟩
  have hc : ((typeCounts (A := A) n).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero.2 ⟨_, hx⟩)
  rw [typeMix, mul_div_cancel₀ _ hc]
  exact single_le_sum (f := fun k : A → ℕ => ∏ t, outputLaw W (fun a => (k a : ℝ) / n) (y t))
    (fun k _ => prod_nonneg fun t _ => outputLaw_nonneg W (fun a => by positivity) _) hx

theorem one_sub_avgError_le {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
    (c : BlockCode M A B n) (W : DMC A B) {lam : ℝ} (hlam : 0 ≤ lam) :
    1 - (c.avgError W).toReal ≤
      (∑ m, ∑ y, if lam * outSeq W (c.enc m) y < (blockProb W (c.enc m) y).toReal
        then (blockProb W (c.enc m) y).toReal else 0) / Fintype.card M +
      lam * (typeCounts (A := A) n).card / Fintype.card M := by
  have hM : (0 : ℝ) < Fintype.card M := Nat.cast_pos.2 Fintype.card_pos
  have hP : ∀ m, ∑ y, (blockProb W (c.enc m) y).toReal = 1 := fun m => by
    rw [← ENNReal.toReal_sum fun y _ => blockProb_ne_top W _ y, sum_blockProb_eq_one,
      ENNReal.toReal_one]
  have hav : (c.avgError W).toReal =
      (∑ m, (1 - ∑ y, if c.dec y = m then (blockProb W (c.enc m) y).toReal else 0)) /
        Fintype.card M := by
    rw [BlockCode.avgError, ENNReal.toReal_div, ENNReal.toReal_sum fun m _ =>
      c.errorProb_ne_top W m, ENNReal.toReal_natCast]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [BlockCode.errorProb_toReal, ← hP m, ← sum_sub_distrib]
    exact sum_congr rfl fun y _ => by split_ifs <;> ring
  have hpt : ∀ m y, (if c.dec y = m then (blockProb W (c.enc m) y).toReal else 0) ≤
      (if lam * outSeq W (c.enc m) y < (blockProb W (c.enc m) y).toReal
        then (blockProb W (c.enc m) y).toReal else 0) +
      lam * (typeCounts (A := A) n).card * (if c.dec y = m then typeMix W n y else 0) := by
    intro m y
    have hb : 0 ≤ (blockProb W (c.enc m) y).toReal := ENNReal.toReal_nonneg
    have hq := outSeq_le_typeMix W (c.enc m) y
    have hq0 : 0 ≤ (typeCounts (A := A) n).card * typeMix W n y :=
      (prod_nonneg fun t _ => outputLaw_nonneg W (fun a => by
        unfold typeWeight; positivity) _).trans hq
    by_cases hd : c.dec y = m <;> by_cases hl : lam * outSeq W (c.enc m) y <
      (blockProb W (c.enc m) y).toReal <;> simp only [hd, hl, ite_true, ite_false]
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left hq hlam]
    · nlinarith
    · nlinarith
  have hQ : ∑ m, ∑ y, (if c.dec y = m then typeMix W n y else 0) ≤ 1 := by
    rw [sum_comm]
    simp only [sum_ite_eq, mem_univ, ite_true]
    exact sum_typeMix_le W n
  have h1a : 1 - (c.avgError W).toReal =
      (∑ m, ∑ y, if c.dec y = m then (blockProb W (c.enc m) y).toReal else 0) /
        Fintype.card M := by
    rw [hav, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
    field_simp
    ring
  rw [h1a, ← add_div, div_le_div_iff_of_pos_right hM]
  calc ∑ m, ∑ y, (if c.dec y = m then (blockProb W (c.enc m) y).toReal else 0)
      ≤ ∑ m, ∑ y, ((if lam * outSeq W (c.enc m) y < (blockProb W (c.enc m) y).toReal
        then (blockProb W (c.enc m) y).toReal else 0) +
        lam * (typeCounts (A := A) n).card * (if c.dec y = m then typeMix W n y else 0)) :=
        sum_le_sum fun m _ => sum_le_sum fun y _ => hpt m y
    _ = (∑ m, ∑ y, if lam * outSeq W (c.enc m) y < (blockProb W (c.enc m) y).toReal
          then (blockProb W (c.enc m) y).toReal else 0) + lam * (typeCounts (A := A) n).card *
          ∑ m, ∑ y, (if c.dec y = m then typeMix W n y else 0) := by
        simp only [sum_add_distrib, mul_sum]
    _ ≤ _ := by
        have hl0 : 0 ≤ lam * (typeCounts (A := A) n).card := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hQ hl0]

end TypeMix

variable [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B]

private lemma jointMeasure_real (W : DMC A B) (p : PMF A) (x : A × B) :
    (W.jointMeasure p).real {x} = (p x.1).toReal * (W x.1 x.2).toReal := by
  rw [measureReal_def, jointMeasure_eq_toMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), ← ENNReal.toReal_mul,
    ← jointPMF_apply]

theorem inputMutualInfo_eq_sum_log_div [Fintype A] [Fintype B] (W : DMC A B) (p : PMF A) :
    W.inputMutualInfo p = ∑ a, ∑ b, (p a).toReal * (W a b).toReal *
      Real.log ((W a b).toReal / outputLaw W (fun a => (p a).toReal) b) := by
  classical
  set ν := W.jointMeasure p
  set q := outputLaw W fun a => (p a).toReal
  have hq : ∀ b, (ν.map Prod.snd).real {b} = q b := by
    intro b
    rw [measureReal_map_singleton, sum_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_eq_single b (fun b' _ hb' => by simp [hb']) (by simp)]
    simp [ν, jointMeasure_real]
  have hY : H[Prod.snd ; ν] = ∑ b, Real.negMulLog (q b) := by
    rw [entropy_def]
    exact sum_congr rfl fun b _ => by rw [hq]
  have hYX := condEntropy_snd_fst_jointMeasure W p
  rw [DMC.inputMutualInfo, mutualInfo_comm, mutualInfo_eq_entropy_sub_condEntropy, hY, hYX,
    Fintype.sum_prod_type]
  simp only [jointMeasure_real]
  have key : ∀ a b, (p a).toReal * (W a b).toReal * Real.log ((W a b).toReal / q b) =
      (p a).toReal * (W a b).toReal * Real.log (W a b).toReal -
        (p a).toReal * (W a b).toReal * Real.log (q b) := by
    intro a b
    rcases eq_or_ne ((p a).toReal * (W a b).toReal) 0 with h | h
    · simp [h]
    have hw : (W a b).toReal ≠ 0 := (mul_ne_zero_iff.1 h).2
    have hqb : 0 < q b := lt_of_lt_of_le
      (lt_of_le_of_ne (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (Ne.symm h))
      (le_outputLaw W (fun a => ENNReal.toReal_nonneg) a b)
    rw [Real.log_div hw hqb.ne']
    ring
  simp_rw [key, sum_sub_distrib]
  have hlog : ∑ a, ∑ b, (p a).toReal * (W a b).toReal * Real.log (q b) =
      -∑ b, Real.negMulLog (q b) := by
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [← sum_mul, Real.negMulLog, neg_mul, neg_neg]
    rfl
  rw [hlog]
  ring

section Converse

variable [Fintype A] [DecidableEq A] [Fintype B]

omit [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
omit [Fintype A] in
theorem one_le_typeCount {n : ℕ} (x : Fin n → A) (t : Fin n) : 1 ≤ typeCount x (x t) :=
  card_pos.2 ⟨t, mem_filter.2 ⟨mem_univ _, rfl⟩⟩

omit [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
omit [Fintype A] in
theorem typeWeight_nonneg {n : ℕ} (x : Fin n → A) (a : A) : 0 ≤ typeWeight x a := by
  unfold typeWeight
  positivity

theorem sum_mean_le_capacity (W : DMC A B) {n : ℕ} (hn : 0 < n) (x : Fin n → A) :
    ∑ t, ∑ b, (W (x t) b).toReal *
      Real.log ((W (x t) b).toReal / outputLaw W (typeWeight x) b) ≤ n * W.capacity := by
  set g : A → ℝ := fun a => ∑ b, (W a b).toReal *
    Real.log ((W a b).toReal / outputLaw W (typeWeight x) b)
  have h1 : ∑ t, g (x t) = ∑ a, (typeCount x a : ℝ) * g a := sum_comp_eq_sum_typeCount_mul x g
  have hI := inputMutualInfo_eq_sum_log_div W (typePMF hn x)
  simp_rw [typePMF_toReal] at hI
  have hcap := W.inputMutualInfo_le_capacity (typePMF hn x)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h2 : ∑ a, (typeCount x a : ℝ) * g a = n * W.inputMutualInfo (typePMF hn x) := by
    rw [hI, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    simp only [g, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    have ht : typeWeight x a = typeCount x a / n := rfl
    rw [ht]
    field_simp
  change ∑ t, g (x t) ≤ _
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left hcap hn'.le

noncomputable def logBound (W : DMC A B) : ℝ :=
  ∑ a, ∑ b, |Real.log (W a b).toReal|

omit [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
theorem abs_log_le_logBound (W : DMC A B) (a : A) (b : B) :
    |Real.log (W a b).toReal| ≤ logBound W :=
  (single_le_sum (f := fun b => |Real.log (W a b).toReal|) (fun _ _ => abs_nonneg _)
    (mem_univ b)).trans (single_le_sum (f := fun a => ∑ b, |Real.log (W a b).toReal|)
      (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ a))

omit [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
theorem sum_mul_log_sq_le (W : DMC A B) {n : ℕ} (x : Fin n → A) (t : Fin n) :
    ∑ b, (W (x t) b).toReal * Real.log ((W (x t) b).toReal / outputLaw W (typeWeight x) b) ^ 2 ≤
      Real.log (n / typeCount x (x t)) ^ 2 + logBound W ^ 2 := by
  set K := Real.log (n / typeCount x (x t)) ^ 2 + logBound W ^ 2
  have hk : (1 : ℝ) ≤ typeCount x (x t) := Nat.one_le_cast.2 (one_le_typeCount x t)
  have hnk : (typeCount x (x t) : ℝ) ≤ n := Nat.cast_le.2 (typeCount_le x _)
  have hn : (0 : ℝ) < n := lt_of_lt_of_le one_pos (hk.trans hnk)
  have hpt : ∀ b, (W (x t) b).toReal *
      Real.log ((W (x t) b).toReal / outputLaw W (typeWeight x) b) ^ 2 ≤
        (W (x t) b).toReal * K := by
    intro b
    set w := (W (x t) b).toReal
    set o := outputLaw W (typeWeight x) b
    have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
    rcases hw0.eq_or_lt with hw | hw
    · rw [← hw]
      simp
    refine mul_le_mul_of_nonneg_left ?_ hw0
    have ho : typeWeight x (x t) * w ≤ o := le_outputLaw W (typeWeight_nonneg x) _ b
    have htw : 0 < typeWeight x (x t) := div_pos (by linarith) hn
    have ho0 : 0 < o := lt_of_lt_of_le (mul_pos htw hw) ho
    have ho1 : o ≤ 1 := outputLaw_le_one W (typeWeight_nonneg x) (by
      simp only [typeWeight, ← sum_div, ← Nat.cast_sum, sum_typeCount, div_self hn.ne']) b
    have hL := abs_log_le_logBound W (x t) b
    have hK1 : 0 ≤ Real.log (n / typeCount x (x t)) ^ 2 := sq_nonneg _
    have hK2 : 0 ≤ logBound W ^ 2 := sq_nonneg _
    rcases le_or_gt 1 (w / o) with hr | hr
    · have hr' : w / o ≤ n / typeCount x (x t) := by
        rw [div_le_div_iff₀ ho0 (by linarith)]
        have : typeWeight x (x t) * w * n = typeCount x (x t) * w := by
          unfold typeWeight
          field_simp
        nlinarith
      have h0 : 0 ≤ Real.log (w / o) := Real.log_nonneg hr
      have h1 : Real.log (w / o) ≤ Real.log (n / typeCount x (x t)) :=
        Real.log_le_log (by linarith) hr'
      nlinarith
    · have h0 : Real.log (w / o) ≤ 0 := Real.log_nonpos (div_nonneg hw0 ho0.le) hr.le
      have h1 : Real.log w ≤ Real.log (w / o) := by
        rw [Real.log_div hw.ne' ho0.ne']
        linarith [Real.log_nonpos ho0.le ho1]
      have h2 : -logBound W ≤ Real.log w := by
        have := neg_abs_le (Real.log w)
        linarith
      nlinarith
  calc _ ≤ ∑ b, (W (x t) b).toReal * K := sum_le_sum fun b _ => hpt b
    _ = K := by
        rw [← sum_mul, ← ENNReal.toReal_sum fun b _ => (W (x t)).apply_ne_top b, sum_pmf_eq_one,
          ENNReal.toReal_one, one_mul]

omit [Fintype B] [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
theorem sum_log_typeCount_sq_le {n : ℕ} (x : Fin n → A) :
    ∑ t, Real.log (n / typeCount x (x t)) ^ 2 ≤ 2 * n * Fintype.card A := by
  rw [sum_comp_eq_sum_typeCount_mul x fun a => Real.log (n / typeCount x a) ^ 2]
  have hpt : ∀ a, (typeCount x a : ℝ) * Real.log (n / typeCount x a) ^ 2 ≤ 2 * n := by
    intro a
    rcases (Nat.zero_le (typeCount x a)).eq_or_lt with h | h
    · rw [← h]
      simp only [Nat.cast_zero, zero_mul]
      positivity
    have hk : (0 : ℝ) < typeCount x a := Nat.cast_pos.2 h
    have hn : (0 : ℝ) < n := hk.trans_le (Nat.cast_le.2 (typeCount_le x a))
    have hp1 : (typeCount x a : ℝ) / n ≤ 1 := (div_le_one hn).2 (Nat.cast_le.2 (typeCount_le x a))
    have := mul_log_sq_le (div_pos hk hn) hp1
    have e : (typeCount x a : ℝ) * Real.log (n / typeCount x a) ^ 2 =
        n * ((typeCount x a : ℝ) / n * Real.log ((typeCount x a : ℝ) / n) ^ 2) := by
      have hl : Real.log (n / typeCount x a) = -Real.log ((typeCount x a : ℝ) / n) := by
        rw [← Real.log_inv, inv_div]
      rw [hl, neg_sq]
      field_simp
    rw [e]
    nlinarith
  calc _ ≤ ∑ _a : A, 2 * (n : ℝ) := sum_le_sum fun a _ => hpt a
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring

theorem sum_error_event_le (W : DMC A B) {n : ℕ} (hn : 0 < n) (x : Fin n → A) {δ : ℝ}
    (hδ : 0 < δ) :
    ∑ y, (if Real.exp (n * (W.capacity + δ)) * outSeq W x y < (blockProb W x y).toReal
      then (blockProb W x y).toReal else 0) ≤
        (logBound W ^ 2 + 2 * Fintype.card A) / (n * δ ^ 2) := by
  set w : Fin n → B → ℝ := fun t b => (W (x t) b).toReal
  set o := outputLaw W (typeWeight x)
  set Z : Fin n → B → ℝ := fun t b => Real.log (w t b / o b)
  set m : Fin n → ℝ := fun t => ∑ b, w t b * Z t b
  set Y : Fin n → B → ℝ := fun t b => Z t b - m t
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1 : ∀ t, ∑ b, w t b = 1 := fun t => by
    simp only [w]
    rw [← ENNReal.toReal_sum fun b _ => (W (x t)).apply_ne_top b, sum_pmf_eq_one,
      ENNReal.toReal_one]
  have h0 : ∀ t, ∑ b, w t b * Y t b = 0 := fun t => by
    simp only [Y, mul_sub, sum_sub_distrib, ← sum_mul, h1, one_mul, m, sub_self]
  have hvar : ∀ t, ∑ b, w t b * Y t b ^ 2 ≤ ∑ b, w t b * Z t b ^ 2 := fun t => by
    have e : ∑ b, w t b * Y t b ^ 2 = ∑ b, w t b * Z t b ^ 2 - m t ^ 2 := by
      simp only [Y, sub_sq, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
      have e1 : ∑ b, w t b * (2 * Z t b * m t) = 2 * m t * m t := by
        rw [show (2 : ℝ) * m t * m t = 2 * m t * ∑ b, w t b * Z t b from rfl, mul_sum]
        exact sum_congr rfl fun b _ => by ring
      have e2 : ∑ b, w t b * m t ^ 2 = m t ^ 2 := by rw [← sum_mul, h1, one_mul]
      rw [e1, e2]
      ring
    rw [e]
    nlinarith [sq_nonneg (m t)]
  have hsec := sum_prod_mul_sq w h1 Y h0
  have hmean := sum_mean_le_capacity W hn x
  have hP : ∀ y : Fin n → B, (blockProb W x y).toReal = ∏ t, w t (y t) := fun y => by
    simp only [blockProb, ENNReal.toReal_prod, w]
  have hpt : ∀ y : Fin n → B,
      (if Real.exp (n * (W.capacity + δ)) * outSeq W x y < (blockProb W x y).toReal
        then (blockProb W x y).toReal else 0) ≤
      (∏ t, w t (y t)) * (∑ t, Y t (y t)) ^ 2 / (n * δ) ^ 2 := by
    intro y
    have hw0 : ∀ t, 0 ≤ w t (y t) := fun t => ENNReal.toReal_nonneg
    have hq0 : 0 ≤ (∏ t, w t (y t)) * (∑ t, Y t (y t)) ^ 2 / (n * δ) ^ 2 :=
      div_nonneg (mul_nonneg (prod_nonneg fun t _ => hw0 t) (sq_nonneg _)) (sq_nonneg _)
    split_ifs with hc
    swap
    · exact hq0
    rw [hP] at hc ⊢
    have hos : 0 ≤ outSeq W x y :=
      prod_nonneg fun t _ => outputLaw_nonneg W (typeWeight_nonneg x) _
    have hPpos : 0 < ∏ t, w t (y t) :=
      lt_of_le_of_lt (mul_nonneg (Real.exp_pos _).le hos) hc
    have hwpos : ∀ t, 0 < w t (y t) := fun t => lt_of_le_of_ne (hw0 t) fun h =>
      hPpos.ne' (prod_eq_zero (mem_univ t) h.symm)
    have hopos : ∀ t, 0 < o (y t) := fun t => lt_of_lt_of_le
      (mul_pos (div_pos (Nat.cast_pos.2 (one_le_typeCount x t)) hn') (hwpos t))
      (le_outputLaw W (typeWeight_nonneg x) (x t) (y t))
    have hosp : 0 < outSeq W x y := prod_pos fun t _ => hopos t
    have hratio : Real.exp (n * (W.capacity + δ)) < ∏ t, (w t (y t) / o (y t)) := by
      rw [prod_div_distrib]
      exact (lt_div_iff₀ hosp).2 hc
    have hlog : n * (W.capacity + δ) < ∑ t, Z t (y t) := by
      have := Real.log_lt_log (Real.exp_pos _) hratio
      rw [Real.log_exp, Real.log_prod fun t _ => (div_pos (hwpos t) (hopos t)).ne'] at this
      exact this
    have hY : n * δ < ∑ t, Y t (y t) := by
      simp only [Y, sum_sub_distrib]
      have : ∑ t, m t ≤ n * W.capacity := hmean
      nlinarith
    have hsq : (n * δ) ^ 2 ≤ (∑ t, Y t (y t)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hY.le 2
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc _ ≤ ∑ y : Fin n → B, (∏ t, w t (y t)) * (∑ t, Y t (y t)) ^ 2 / (n * δ) ^ 2 :=
        sum_le_sum fun y _ => hpt y
    _ = (∑ t, ∑ b, w t b * Y t b ^ 2) / (n * δ) ^ 2 := by rw [← sum_div, hsec]
    _ ≤ (n * logBound W ^ 2 + 2 * n * Fintype.card A) / (n * δ) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
        calc _ ≤ ∑ t, (Real.log (n / typeCount x (x t)) ^ 2 + logBound W ^ 2) :=
              sum_le_sum fun t _ => (hvar t).trans (sum_mul_log_sq_le W x t)
          _ = ∑ t, Real.log (n / typeCount x (x t)) ^ 2 + n * logBound W ^ 2 := by
              rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ _ := by linarith [sum_log_typeCount_sq_le x]
    _ = _ := by
        field_simp

omit [DecidableEq A] in
theorem strongConverse (W : DMC A B) {R : ℝ} (hR : W.capacity < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, Real.exp (n * R) ≤ k →
      ∀ c : BlockCode (Fin k) A B n, 1 - ε ≤ (c.avgError W).toReal := by
  classical
  set δ := (R - W.capacity) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set K0 := (logBound W ^ 2 + 2 * Fintype.card A) / δ ^ 2
  have h1 : ∀ᶠ n : ℕ in atTop, K0 / n < ε / 2 :=
    (tendsto_const_div_atTop_nhds_zero_nat K0).eventually (gt_mem_nhds (by linarith))
  have h2 := eventually_pow_le_exp (Fintype.card A) (show 0 < δ / 2 by linarith)
  have h3 : ∀ᶠ n : ℕ in atTop, Real.exp (n * (-(δ / 2))) < ε / 2 :=
    (tendsto_exp_nat_mul (by linarith : -(δ / 2) < 0)).eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((h1.and (h2.and h3)).and (eventually_gt_atTop 0))
  refine ⟨N, fun n hn k hk c => ?_⟩
  obtain ⟨⟨hb1, hb2, hb3⟩, hn0⟩ := hN n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hk0 : (0 : ℝ) < k := (Real.exp_pos _).trans_le hk
  have : Nonempty (Fin k) := ⟨⟨0, Nat.cast_pos.1 hk0⟩⟩
  set lam := Real.exp (n * (W.capacity + δ))
  have hmain := one_sub_avgError_le c W (lam := lam) (Real.exp_pos _).le
  rw [Fintype.card_fin] at hmain
  have hbad : (∑ m, ∑ y, if lam * outSeq W (c.enc m) y < (blockProb W (c.enc m) y).toReal
      then (blockProb W (c.enc m) y).toReal else 0) / k ≤ K0 / n := by
    rw [div_le_iff₀ hk0]
    calc _ ≤ ∑ _m : Fin k, K0 / n := sum_le_sum fun m _ => by
          have := sum_error_event_le W hn0 (c.enc m) hδ
          calc _ ≤ _ := this
            _ = K0 / n := by simp only [K0]; field_simp
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hcard := card_typeCounts_le (A := A) n
  have hsec : lam * (typeCounts (A := A) n).card / k ≤ Real.exp (n * (-(δ / 2))) := by
    rw [div_le_iff₀ hk0]
    calc lam * (typeCounts (A := A) n).card ≤ lam * Real.exp (n * (δ / 2)) :=
          mul_le_mul_of_nonneg_left (hcard.trans hb2) (Real.exp_pos _).le
      _ = Real.exp (n * (-(δ / 2))) * Real.exp (n * R) := by
          simp only [lam, ← Real.exp_add]
          congr 1
          rw [hδdef]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
  linarith

end Converse

end DMC

end Meat
