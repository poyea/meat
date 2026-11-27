import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Meat.Shannon.Entropy

open Filter Topology

namespace Meat

def IsProbList (l : List ℝ) : Prop := (∀ x ∈ l, 0 ≤ x) ∧ l.sum = 1

noncomputable def listEntropy (l : List ℝ) : ℝ := (l.map Real.negMulLog).sum

structure FaddeevAxioms (H : List ℝ → ℝ) : Prop where
  perm : ∀ {l l' : List ℝ}, l.Perm l' → IsProbList l → H l = H l'
  cont : ContinuousOn (fun x => H [x, 1 - x]) (Set.Icc 0 1)
  group : ∀ {a b : ℝ} {l : List ℝ}, 0 < a + b → IsProbList (a :: b :: l) →
    H (a :: b :: l) = H ((a + b) :: l) + (a + b) * H [a / (a + b), b / (a + b)]

theorem IsProbList.perm {l l' : List ℝ} (h : l.Perm l') (hl : IsProbList l) : IsProbList l' :=
  ⟨fun x hx => hl.1 x (h.mem_iff.2 hx), h.sum_eq ▸ hl.2⟩

private lemma isProbList_map_div {q : List ℝ} (hq : ∀ x ∈ q, 0 ≤ x) (hs : 0 < q.sum) :
    IsProbList (q.map (· / q.sum)) := by
  refine ⟨fun y hy => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact div_nonneg (hq x hx) hs.le
  · simp only [div_eq_mul_inv]
    rw [List.sum_map_mul_right, List.map_id', mul_inv_cancel₀ hs.ne']

private lemma tendsto_diff {F : ℕ → ℝ}
    (hδ : Tendsto (fun n : ℕ => F (n + 1) - n / (n + 1) * F n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => F (n + 1) - F n) atTop (𝓝 0) := by
  set δ := fun n : ℕ => F (n + 1) - n / (n + 1) * F n with hδdef
  have htel : ∀ n : ℕ, n * F n = ∑ i ∈ Finset.range n, (i + 1) * δ i := by
    intro n
    have : ∀ i : ℕ, ((i : ℝ) + 1) * δ i = ((i + 1 : ℕ) : ℝ) * F (i + 1) - (i : ℝ) * F i := by
      intro i
      simp only [hδdef]
      push_cast
      field_simp
    simp only [this]
    rw [Finset.sum_range_sub (fun i => (i : ℝ) * F i)]
    simp
  have hbound : ∀ n : ℕ, 0 < n → |F n| ≤ ∑ i ∈ Finset.range n, |δ i| := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : n * |F n| ≤ n * ∑ i ∈ Finset.range n, |δ i| := by
      have e : (n : ℝ) * |F n| = |(n : ℝ) * F n| := by rw [abs_mul, abs_of_pos hn']
      rw [e, htel, Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < i + 1)]
      have : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hi
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    exact le_of_mul_le_mul_left h1 hn'
  have hc := ((hδ.abs.cesaro).comp (tendsto_add_atTop_nat 1))
  simp only [abs_zero] at hc
  have hq : Tendsto (fun n : ℕ => F n / (n + 1)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩) hc
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_div, Nat.cast_add, Nat.cast_one]
    rw [abs_of_pos (by positivity : (0 : ℝ) < n + 1), div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ((hbound n hn).trans ?_) (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ n))
      fun _ _ _ => abs_nonneg _
  have := hδ.sub hq
  rw [sub_zero] at this
  refine this.congr fun n => ?_
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [hδdef]
  field_simp
  ring

private lemma eq_log_of_mul {F : ℕ → ℝ} (hmul : ∀ m n : ℕ, 0 < m → 0 < n → F (m * n) = F m + F n)
    (hd : Tendsto (fun n : ℕ => F (n + 1) - F n) atTop (𝓝 0)) {n : ℕ} (hn : 0 < n) :
    F n = F 2 / Real.log 2 * Real.log n := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  set c := F 2 / Real.log 2
  set g : ℕ → ℝ := fun n => F n - c * Real.log n with hg
  have hgmul : ∀ m n : ℕ, 0 < m → 0 < n → g (m * n) = g m + g n := by
    intro m n hm hn
    simp only [hg, hmul m n hm hn, Nat.cast_mul]
    rw [Real.log_mul (by positivity) (by positivity)]
    ring
  have hg2 : g 2 = 0 := by
    simp only [hg, c, Nat.cast_ofNat]
    field_simp
    ring
  have hgd : Tendsto (fun n : ℕ => g (n + 1) - g n) atTop (𝓝 0) := by
    have := hd.sub (Real.tendsto_log_nat_add_one_sub_log.const_mul c)
    rw [mul_zero, sub_zero] at this
    refine this.congr fun n => ?_
    simp only [hg, Nat.cast_add, Nat.cast_one]
    ring
  have hgrow : ∀ ε > 0, ∃ A : ℝ, ∀ n : ℕ, 0 < n → |g n| ≤ A + ε * Real.log n := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hgd (ε * Real.log 2)
      (mul_pos hε (Real.log_pos one_lt_two))
    refine ⟨∑ i ∈ Finset.range (2 * N + 2), |g i|, fun n => ?_⟩
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hn
    by_cases hsmall : n < 2 * N + 2
    · have h1 := Finset.single_le_sum (f := fun i => |g i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.2 hsmall)
      have h2 : 0 ≤ ε * Real.log n := mul_nonneg hε.le (Real.log_natCast_nonneg n)
      linarith
    push Not at hsmall
    set a := n / 2 with ha
    have ha1 : N + 1 ≤ a := by omega
    have hapos : 0 < a := by omega
    have han : a < n := by omega
    have h2a : g (2 * a) = g a := by rw [hgmul 2 a two_pos hapos, hg2, zero_add]
    have hstep : |g n| ≤ |g a| + ε * Real.log 2 := by
      rcases Nat.even_or_odd' n with ⟨b, hb | hb⟩
      · have hb2 : n = 2 * a := by omega
        rw [hb2, h2a]
        have : 0 ≤ ε * Real.log 2 := by positivity
        linarith
      · have hb2 : n = 2 * a + 1 := by omega
        have h := hN (2 * a) (by omega)
        rw [Real.dist_eq, sub_zero] at h
        rw [hb2, ← h2a]
        have := abs_sub_abs_le_abs_sub (g (2 * a + 1)) (g (2 * a))
        linarith
    have hlog : Real.log a + Real.log 2 ≤ Real.log n := by
      rw [← Real.log_mul (by positivity) (by norm_num)]
      exact Real.log_le_log (by positivity) (by exact_mod_cast (by omega : a * 2 ≤ n))
    have := ih a han hapos
    nlinarith
  have hpow : ∀ m k : ℕ, 0 < m → g (m ^ k) = k * g m := by
    intro m k hm
    induction k with
    | zero =>
      have := hgmul 1 1 one_pos one_pos
      simp only [mul_one] at this
      simp
      linarith
    | succ k ih =>
      rw [pow_succ, hgmul _ _ (by positivity) hm, ih]
      push_cast
      ring
  have hzero : g n = 0 := by
    have hle : ∀ ε > 0, |g n| ≤ ε * (1 + Real.log n) := by
      intro ε hε
      obtain ⟨A, hA⟩ := hgrow ε hε
      obtain ⟨k, hk⟩ := exists_nat_gt (max A 0 / ε)
      have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
      have h := hA (n ^ k) (by positivity)
      rw [hpow n k hn, abs_mul, Nat.abs_cast, Nat.cast_pow, Real.log_pow] at h
      have hAk : A < k * ε := by
        rw [div_lt_iff₀ hε] at hk
        linarith [le_max_left A 0]
      nlinarith
    by_contra hne
    have hpos : 0 < |g n| := abs_pos.2 hne
    have hL : 0 < 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
    have := hle (|g n| / (2 * (1 + Real.log n))) (by positivity)
    have e : |g n| / (2 * (1 + Real.log n)) * (1 + Real.log n) = |g n| / 2 := by field_simp
    rw [e] at this
    linarith
  simp only [hg] at hzero
  linarith

private lemma negMulLog_split {a b : ℝ} (h : 0 < a + b) :
    Real.negMulLog a + Real.negMulLog b = Real.negMulLog (a + b) +
      (a + b) * (Real.negMulLog (a / (a + b)) + Real.negMulLog (b / (a + b))) := by
  have ha : Real.negMulLog a = a / (a + b) * Real.negMulLog (a + b) +
      (a + b) * Real.negMulLog (a / (a + b)) := by
    rw [← Real.negMulLog_mul, mul_div_cancel₀ _ h.ne']
  have hb : Real.negMulLog b = b / (a + b) * Real.negMulLog (a + b) +
      (a + b) * Real.negMulLog (b / (a + b)) := by
    rw [← Real.negMulLog_mul, mul_div_cancel₀ _ h.ne']
  have hab : a / (a + b) + b / (a + b) = 1 := by rw [← add_div, div_self h.ne']
  linear_combination ha + hb + Real.negMulLog (a + b) * hab

theorem listEntropy_perm {l l' : List ℝ} (h : l.Perm l') : listEntropy l = listEntropy l' :=
  (h.map _).sum_eq

theorem faddeevAxioms_mul_listEntropy (c : ℝ) : FaddeevAxioms fun l => c * listEntropy l where
  perm h _ := by rw [listEntropy_perm h]
  cont := by
    simp only [listEntropy, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact (Continuous.continuousOn (by fun_prop))
  group {a b l} h _ := by
    simp only [listEntropy, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have := negMulLog_split h
    linear_combination c * this

namespace FaddeevAxioms

variable {H : List ℝ → ℝ}

private lemma one (hH : FaddeevAxioms H) : H [1] = 0 := by
  have h := hH.group (a := 1) (b := 0) (l := []) (by norm_num) ⟨by simp, by simp⟩
  norm_num at h
  linarith

private lemma one_zero (hH : FaddeevAxioms H) : H [1, 0] = 0 := by
  have h1 := hH.group (a := 1 / 2) (b := 1 / 2) (l := [0]) (by norm_num)
    ⟨by simp, by norm_num⟩
  have h2 := hH.group (a := 1 / 2) (b := 0) (l := [1 / 2]) (by norm_num)
    ⟨by simp, by norm_num⟩
  have hp : H [1 / 2, 1 / 2, 0] = H [1 / 2, 0, 1 / 2] :=
    hH.perm (List.Perm.cons _ (List.Perm.swap _ _ _)) ⟨by simp, by norm_num⟩
  norm_num at h1 h2 hp
  linarith

private lemma zero_one (hH : FaddeevAxioms H) : H [0, 1] = 0 := by
  exact (hH.perm (List.Perm.swap _ _ _) ⟨by simp, by simp⟩).trans hH.one_zero

private lemma group_list (hH : FaddeevAxioms H) :
    ∀ (n : ℕ) (q l : List ℝ), q.length = n → 0 < q.sum → IsProbList (q ++ l) →
      H (q ++ l) = H (q.sum :: l) + q.sum * H (q.map (· / q.sum)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro q l hn hs hp
  have hq : ∀ x ∈ q, 0 ≤ x := fun x hx => hp.1 x (List.mem_append_left _ hx)
  obtain ⟨x, hx, hxpos⟩ : ∃ x ∈ q, 0 < x := by
    by_contra h
    push Not at h
    exact absurd hs (not_lt.2 ((List.sum_le_length_nsmul q 0 h).trans (by simp)))
  have hperm : q.Perm (x :: q.erase x) := List.perm_cons_erase hx
  have hsum : q.sum = x + (q.erase x).sum := hperm.sum_eq.trans (List.sum_cons ..)
  rw [hH.perm (hperm.append_right l) hp,
    hH.perm (hperm.map _) (isProbList_map_div hq hs), hsum]
  have hp' := hp.perm (hperm.append_right l)
  have hlen : (q.erase x).length + 1 = n := by
    rw [← hn, hperm.length_eq, List.length_cons]
  rcases hr : q.erase x with _ | ⟨y, r⟩
  · simp [div_self hxpos.ne', hH.one]
  rw [hr] at hp' hlen
  have hy : 0 ≤ y := hp'.1 y (by simp)
  have hxy : 0 < x + y := by linarith
  have hr0 : ∀ z ∈ r, 0 ≤ z := fun z hz => hp'.1 z (by simp [hz])
  have hs' : 0 < x + (y :: r).sum := by rw [← hr, ← hsum]; exact hs
  set s := x + (y :: r).sum with hsdef
  have hss : ((x + y) :: r).sum = s := by simp [hsdef, add_assoc]
  have hg := hH.group (a := x) (b := y) (l := r ++ l) hxy (by simpa using hp')
  have hih := ih ((x + y) :: r).length (by simp [← hlen]) ((x + y) :: r) l rfl (hss ▸ hs')
    (by
      refine ⟨fun z hz => ?_, ?_⟩
      · simp only [List.cons_append, List.mem_cons, List.mem_append] at hz
        rcases hz with rfl | hz | hz
        · exact hxy.le
        · exact hr0 z hz
        · exact hp.1 z (List.mem_append_right _ hz)
      · have := hp'.2
        simp only [List.cons_append, List.sum_cons, List.sum_append] at this ⊢
        linarith)
  have hxys : 0 < x / s + y / s := by rw [← add_div]; exact div_pos hxy hs'
  have hg' := hH.group (a := x / s) (b := y / s) (l := r.map (· / s)) hxys
    (by
      have := isProbList_map_div (q := x :: y :: r)
        (fun z hz => by
          simp only [List.mem_cons] at hz
          rcases hz with rfl | rfl | hz
          · exact hxpos.le
          · exact hy
          · exact hr0 z hz)
        (by simpa [hsdef, add_assoc] using hs')
      simpa [hsdef, add_assoc] using this)
  have e1 : x / s + y / s = (x + y) / s := by rw [add_div]
  have e2 : x / s / ((x + y) / s) = x / (x + y) := by field_simp
  have e3 : y / s / ((x + y) / s) = y / (x + y) := by field_simp
  rw [e1, e2, e3] at hg'
  simp only [List.cons_append, List.map_cons] at hg hih ⊢
  rw [hss] at hih
  rw [hg, hih, hg']
  field_simp
  ring

private noncomputable def unif (n : ℕ) : List ℝ := List.replicate n (1 / n)

private lemma isProbList_merge {k : ℕ} {x : ℝ} {l : List ℝ}
    (hp : IsProbList (List.replicate k x ++ l)) (hx : 0 ≤ x) : IsProbList ((k * x) :: l) := by
  refine ⟨fun z hz => ?_, ?_⟩
  · rcases List.mem_cons.1 hz with rfl | hz
    · positivity
    · exact hp.1 z (List.mem_append_right _ hz)
  · have := hp.2
    simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul] at this
    simpa using this

private lemma group_rep (hH : FaddeevAxioms H) {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 < x)
    (l : List ℝ) (hp : IsProbList (List.replicate k x ++ l)) :
    H (List.replicate k x ++ l) = H ((k * x) :: l) + k * x * H (unif k) := by
  have hs : (List.replicate k x).sum = k * x := by simp [List.sum_replicate]
  have hkx : 0 < (k : ℝ) * x := by positivity
  rw [hH.group_list _ _ l rfl (hs ▸ hkx) hp, hs, List.map_replicate, unif]
  congr 4
  field_simp

private lemma flat (hH : FaddeevAxioms H) {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    ∀ (j : ℕ) (l : List ℝ), IsProbList ((List.replicate j (List.replicate n x)).flatten ++ l) →
      H ((List.replicate j (List.replicate n x)).flatten ++ l) =
        H (List.replicate j (n * x) ++ l) + j * (n * x) * H (unif n) := by
  intro j
  induction j with
  | zero => intro l _; simp
  | succ j ih =>
  intro l hp
  rw [List.replicate_succ, List.flatten_cons, List.append_assoc] at hp ⊢
  have hm := isProbList_merge hp hx.le
  have hm' := hm.perm List.perm_middle.symm
  rw [hH.group_rep hn hx _ hp, hH.perm List.perm_middle.symm hm, ih _ hm',
    List.replicate_succ' (n := j), List.append_assoc, List.singleton_append]
  push_cast
  ring

private lemma unif_mul (hH : FaddeevAxioms H) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    H (unif (m * n)) = H (unif m) + H (unif n) := by
  have hx : (0 : ℝ) < 1 / (m * n) := by positivity
  have h := hH.flat hn hx m []
  rw [List.flatten_replicate_replicate, List.append_nil, List.append_nil] at h
  have e1 : (n : ℝ) * (1 / (m * n)) = 1 / m := by field_simp
  have e2 : (m : ℝ) * (1 / m) = 1 := by field_simp
  have hp : IsProbList (List.replicate (m * n) (1 / ((m : ℝ) * n))) := by
    refine ⟨fun z hz => ?_, ?_⟩
    · rw [List.eq_of_mem_replicate hz]; exact hx.le
    · simp only [List.sum_replicate, nsmul_eq_mul]; push_cast; field_simp
  rw [unif, Nat.cast_mul, h hp, e1, e2, one_mul]
  rfl

private lemma two_block (hH : FaddeevAxioms H) {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    H (unif (j + k)) = H [k / (j + k), j / (j + k)] + k / (j + k) * H (unif k) +
      j / (j + k) * H (unif j) := by
  have hN : (0 : ℝ) < j + k := by positivity
  have hx : (0 : ℝ) < 1 / (j + k) := by positivity
  have hp : IsProbList
      (List.replicate j (1 / ((j : ℝ) + k)) ++ List.replicate k (1 / ((j : ℝ) + k))) := by
    refine ⟨fun z hz => ?_, ?_⟩
    · rcases List.mem_append.1 hz with hz | hz <;> rw [List.eq_of_mem_replicate hz] <;> exact hx.le
    · simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul]; field_simp
  have hm := isProbList_merge hp hx.le
  have hm' := hm.perm (List.perm_append_singleton _ _).symm
  rw [unif, Nat.cast_add, List.replicate_add, hH.group_rep hj hx _ hp,
    hH.perm (List.perm_append_singleton _ _).symm hm, hH.group_rep hk hx _ hm']
  have e1 : (j : ℝ) * (1 / (j + k)) = j / (j + k) := by field_simp
  have e2 : (k : ℝ) * (1 / (j + k)) = k / (j + k) := by field_simp
  rw [e1, e2]

private lemma binary (hH : FaddeevAxioms H) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    H [x, 1 - x] = H [1 / 2, 1 / 2] / Real.log 2 *
      (Real.negMulLog x + Real.negMulLog (1 - x)) := by
  set c := H [1 / 2, 1 / 2] / Real.log 2 with hcdef
  set F : ℕ → ℝ := fun n => H (unif n) with hF
  have hF1 : F 1 = 0 := by simp [hF, unif, hH.one]
  have hδ : ∀ n : ℕ, F (n + 1) - n / (n + 1) * F n = H [n / (n + 1), 1 - n / (n + 1)] := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF1, hH.zero_one]
    have h := hH.two_block one_pos hn
    have e : 1 - (n : ℝ) / (n + 1) = 1 / (n + 1) := by field_simp; ring
    simp only [Nat.cast_one] at h
    rw [add_comm 1 n, add_comm (1 : ℝ) n] at h
    simp only [hF, e, h] at hF1 ⊢
    rw [hF1]
    ring
  have hlim : Tendsto (fun n : ℕ => F (n + 1) - n / (n + 1) * F n) atTop (𝓝 0) := by
    simp only [hδ]
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝[Set.Icc 0 1] 1) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_natCast_div_add_atTop 1, Eventually.of_forall
        fun n => ⟨by positivity, (div_le_one (by positivity)).2 (by linarith)⟩⟩
    have h2 := (hH.cont 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp h1
    simp only [sub_self, hH.one_zero] at h2
    exact h2
  have hlog : ∀ n : ℕ, 0 < n → F n = c * Real.log n := by
    intro n hn
    rw [eq_log_of_mul (fun m k hm hk => hH.unif_mul hm hk) (tendsto_diff hlim) hn]
    simp [hF, unif, hcdef]
  have hrat : ∀ k N : ℕ, 0 < N → k ≤ N →
      H [(k : ℝ) / N, 1 - k / N] = c * (Real.negMulLog (k / N) + Real.negMulLog (1 - k / N)) := by
    intro k N hN hkN
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hH.zero_one]
    rcases eq_or_lt_of_le hkN with rfl | hlt
    · have : (k : ℝ) / k = 1 := div_self (by positivity)
      simp [this, hH.one_zero]
    obtain ⟨j, rfl⟩ : ∃ j, N = j + k := ⟨N - k, by omega⟩
    have hj : 0 < j := by omega
    have h := hH.two_block hj hk
    have e : 1 - (k : ℝ) / (j + k : ℕ) = j / (j + k) := by push_cast; field_simp; ring
    rw [e]
    push_cast
    have h' : H [(k : ℝ) / (j + k), j / (j + k)] =
        F (j + k) - k / (j + k) * F k - j / (j + k) * F j := by
      simp only [hF] at h ⊢
      linarith
    rw [h', hlog _ (by omega), hlog _ hk, hlog _ hj]
    have hN : (0 : ℝ) < j + k := by positivity
    simp only [Real.negMulLog, Nat.cast_add]
    rw [Real.log_div (by positivity) hN.ne', Real.log_div (by positivity) hN.ne']
    field_simp
    ring
  have hseq : Tendsto (fun n : ℕ => (⌊x * n⌋₊ : ℝ) / n) atTop (𝓝[Set.Icc 0 1] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_nat_floor_mul_div_atTop hx.1).comp
      tendsto_natCast_atTop_atTop, Eventually.of_forall fun n => ⟨by positivity, ?_⟩⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [div_le_one (by positivity)]
    exact (Nat.floor_le (by have := hx.1; positivity)).trans
      (mul_le_of_le_one_left (by positivity) hx.2)
  have hA := (hH.cont x hx).tendsto.comp hseq
  have hB : Tendsto (fun n : ℕ => c * (Real.negMulLog ((⌊x * n⌋₊ : ℝ) / n) +
      Real.negMulLog (1 - (⌊x * n⌋₊ : ℝ) / n))) atTop
      (𝓝 (c * (Real.negMulLog x + Real.negMulLog (1 - x)))) :=
    (((show Continuous fun y : ℝ => c * (Real.negMulLog y + Real.negMulLog (1 - y)) by
      fun_prop).tendsto x).comp
      (tendsto_nhdsWithin_iff.1 hseq).1)
  refine tendsto_nhds_unique hA (hB.congr' (Eventually.of_forall fun n => ?_))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hH.zero_one]
  refine (hrat _ n hn ?_).symm
  have h1 : x * n ≤ n := mul_le_of_le_one_left (by positivity) hx.2
  exact_mod_cast (Nat.floor_le_floor h1).trans (Nat.floor_natCast n).le

theorem eq_mul_listEntropy (hH : FaddeevAxioms H) {l : List ℝ} (hl : IsProbList l) :
    H l = H [1 / 2, 1 / 2] / Real.log 2 * listEntropy l := by
  set c := H [1 / 2, 1 / 2] / Real.log 2
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  obtain ⟨x, hx, hxpos⟩ : ∃ x ∈ l, 0 < x := by
    by_contra h
    push Not at h
    have : l.sum ≤ 0 := (List.sum_le_length_nsmul l 0 h).trans (by simp)
    linarith [hl.2]
  have hperm : l.Perm (x :: l.erase x) := List.perm_cons_erase hx
  have hp := hl.perm hperm
  rw [hH.perm hperm hl, listEntropy_perm hperm]
  have hlen : (l.erase x).length + 1 = n := by rw [← hn, hperm.length_eq, List.length_cons]
  rcases hr : l.erase x with _ | ⟨y, r⟩
  · rw [hr] at hp
    have : x = 1 := by simpa using hp.2
    subst this
    simp [listEntropy, hH.one]
  rw [hr] at hp hlen
  have hy : 0 ≤ y := hp.1 y (by simp)
  have hxy : 0 < x + y := by linarith
  have hp' : IsProbList ((x + y) :: r) := by
    refine ⟨fun z hz => ?_, ?_⟩
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy.le
      · exact hp.1 z (by simp [hz])
    · have := hp.2
      simp only [List.sum_cons] at this ⊢
      linarith
  have hih := ih _ (by simp [← hlen]) hp' rfl
  have hb := hH.binary (x := x / (x + y)) ⟨by positivity, (div_le_one hxy).2 (by linarith)⟩
  have e : 1 - x / (x + y) = y / (x + y) := by field_simp; ring
  rw [e] at hb
  rw [hH.group hxy hp, hih, hb]
  simp only [listEntropy, List.map_cons, List.sum_cons]
  have := negMulLog_split hxy
  linear_combination (-c) * this

theorem eq_listEntropy_div_log_two (hH : FaddeevAxioms H) (h1 : H [1 / 2, 1 / 2] = 1)
    {l : List ℝ} (hl : IsProbList l) : H l = listEntropy l / Real.log 2 := by
  rw [hH.eq_mul_listEntropy hl, h1]
  ring

end FaddeevAxioms

theorem faddeevAxioms_iff {H : List ℝ → ℝ} :
    FaddeevAxioms H ↔ ∃ c : ℝ, ∀ l, IsProbList l → H l = c * listEntropy l := by
  refine ⟨fun hH => ⟨_, fun l hl => hH.eq_mul_listEntropy hl⟩, fun ⟨c, hc⟩ => ?_⟩
  have G := faddeevAxioms_mul_listEntropy c
  have hpair : ∀ x ∈ Set.Icc (0 : ℝ) 1, IsProbList [x, 1 - x] := fun x hx =>
    ⟨by simpa using ⟨hx.1, hx.2⟩, by simp⟩
  refine ⟨fun h hl => ?_, ?_, fun {a b l} h hl => ?_⟩
  · rw [hc _ hl, hc _ (hl.perm h)]
    exact G.perm h hl
  · exact G.cont.congr fun x hx => hc _ (hpair x hx)
  · have hab : IsProbList ((a + b) :: l) := by
      refine ⟨fun z hz => ?_, ?_⟩
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact h.le
        · exact hl.1 z (by simp [hz])
      · have := hl.2
        simp only [List.sum_cons] at this ⊢
        linarith
    have hq : IsProbList [a / (a + b), b / (a + b)] := by
      have := isProbList_map_div (q := [a, b])
        (fun z hz => hl.1 z (by simp at hz ⊢; tauto)) (by simpa using h)
      simpa using this
    rw [hc _ hl, hc _ hab, hc _ hq]
    exact G.group h hl

theorem measureEntropy_eq_listEntropy {S : Type*} [Fintype S] [MeasurableSpace S]
    (ν : MeasureTheory.Measure S) :
    measureEntropy ν = listEntropy (Finset.univ.toList.map fun s => ν.real {s}) := by
  rw [measureEntropy, listEntropy, List.map_map, Finset.sum_map_toList]
  rfl

theorem isProbList_measureReal {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : MeasureTheory.Measure S)
    [MeasureTheory.IsProbabilityMeasure ν] :
    IsProbList (Finset.univ.toList.map fun s => ν.real {s}) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
    exact MeasureTheory.measureReal_nonneg
  · rw [Finset.sum_map_toList, MeasureTheory.sum_measureReal_singleton, Finset.coe_univ,
      MeasureTheory.probReal_univ]

theorem FaddeevAxioms.eq_mul_entropy {H : List ℝ → ℝ} (hH : FaddeevAxioms H)
    {Ω S : Type*} [MeasurableSpace Ω] [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {X : Ω → S} (hX : Measurable X) (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] :
    H (Finset.univ.toList.map fun s => (μ.map X).real {s}) =
      H [1 / 2, 1 / 2] / Real.log 2 * H[X ; μ] := by
  have : MeasureTheory.IsProbabilityMeasure (μ.map X) :=
    (MeasureTheory.Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  rw [hH.eq_mul_listEntropy (isProbList_measureReal _), entropy, measureEntropy_eq_listEntropy]

end Meat
