import Meat.Channel.GelfandPinskerConverse
import Meat.Shannon.StrongCovering

open MeasureTheory Finset Filter Topology
open scoped ENNReal

namespace Meat

namespace GelfandPinsker

section Typical

variable {S U B : Type*} [Fintype S] [DecidableEq S] [Fintype U] [DecidableEq U]
  [Fintype B] [DecidableEq B]

private lemma sum_iidProb_not_typical_le (q : PMF S) {η : ℝ} (hη : 0 < η) {n : ℕ}
    (hn : 0 < n) :
    ∑ x ∈ univ.filter (fun x : Fin n → S => x ∉ strongTypicalSet (fun a => (q a).toReal) n η),
      iidProb q x ≤ Fintype.card S / (4 * n * η ^ 2) := by
  have hx : (fun _ : Fin n => ()) ∈ strongTypicalSet (fun _ : Unit => (1 : ℝ)) n 0 := by
    rw [mem_strongTypicalSet]
    intro a
    have hc : typeCount (fun _ : Fin n => ()) a = n := by
      simp [typeCount]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [hc, div_self hn', sub_self, abs_zero]
  have h := sum_not_mem_strongTypicalSet_le (fun _ : Unit => q) (fun _ => (1 : ℝ)) hη hn hx
  have hc : ∀ x : Fin n → S, ∀ a, typeCount (fun i => ((), x i)) ((), a) = typeCount x a :=
    fun x a => by simp [typeCount]
  have he : (univ.filter fun x : Fin n → S => (fun i => ((), x i)) ∉
      strongTypicalSet (fun ab : Unit × S => (1 : ℝ) * (q ab.2).toReal) n (0 + η)) =
      univ.filter fun x : Fin n → S => x ∉ strongTypicalSet (fun a => (q a).toReal) n η := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_strongTypicalSet, one_mul, zero_add]
    constructor
    · intro h1 h2
      exact h1 fun z => by rw [hc x z.2]; exact h2 z.2
    · intro h1 h2
      exact h1 fun a => by rw [← hc x a]; exact h2 ((), a)
  rw [he, Fintype.card_unit, Nat.cast_one, one_mul] at h
  exact h

private lemma sum_codebook_not_mem (q : PMF S) {n K : ℕ} (s : Finset (Fin n → S)) :
    ∑ C : Fin K → Fin n → S, (∏ l, iidProb q (C l)) * (if ∀ l, C l ∉ s then 1 else 0) =
      (1 - ∑ u ∈ s, iidProb q u) ^ K := by
  have h := sum_prod_mul_prod (fun (_ : Fin K) u => iidProb q u)
    fun (_ : Fin K) u => if u ∉ s then (1 : ℝ) else 0
  simp only [prod_boole, mem_univ, true_implies] at h
  rw [h, prod_const, card_univ, Fintype.card_fin]
  congr 1
  have h1 := sum_iidProb q n
  rw [← sum_filter_add_sum_filter_not univ (fun u => u ∈ s)] at h1
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite, sum_const_zero, add_zero]
  have e2 : (univ.filter fun u : Fin n → S => u ∈ s) = s := by ext; simp
  rw [e2] at h1
  linarith

private lemma sum_codebook_apply_mem (q : PMF S) {n K : ℕ} (s : Finset (Fin n → S)) (l : Fin K) :
    ∑ C : Fin K → Fin n → S, (∏ l', iidProb q (C l')) * (if C l ∈ s then 1 else 0) =
      ∑ u ∈ s, iidProb q u := by
  rw [sum_prod_mul_apply (fun (_ : Fin K) u => iidProb q u) (fun _ => sum_iidProb q n)
    (fun u => if u ∈ s then (1 : ℝ) else 0) l]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext
  simp

private lemma strongTypicalSet_mono {A : Type*} [Fintype A] [DecidableEq A] {r : A → ℝ} {n : ℕ}
    {ε ε' : ℝ} (h : ε ≤ ε') : strongTypicalSet r n ε ⊆ strongTypicalSet r n ε' := fun _ hx =>
  mem_strongTypicalSet.2 fun a => (mem_strongTypicalSet.1 hx a).trans h

private lemma mem_typical_marginal {n : ℕ} {s : Fin n → S} {u : Fin n → U} {y : Fin n → B}
    {r : (S × U) × B → ℝ} {ε : ℝ}
    (h : (fun i => ((s i, u i), y i)) ∈ strongTypicalSet r n ε) :
    (fun i => (y i, u i)) ∈ strongTypicalSet (fun z => ∑ a, r ((a, z.2), z.1)) n
      (Fintype.card S * ε) := by
  rw [mem_strongTypicalSet] at h ⊢
  rintro ⟨b, c⟩
  have hc : (typeCount (fun i => (y i, u i)) (b, c) : ℝ) =
      ∑ a, (typeCount (fun i => ((s i, u i), y i)) ((a, c), b) : ℝ) := by
    rw [← Nat.cast_sum]
    congr 1
    unfold typeCount
    rw [card_eq_sum_card_fiberwise (f := s) (t := univ) fun _ _ => mem_univ _]
    refine sum_congr rfl fun a _ => ?_
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq]
    tauto
  rw [hc, sum_div, ← sum_sub_distrib]
  calc |∑ a, ((typeCount (fun i => ((s i, u i), y i)) ((a, c), b) : ℝ) / n - r ((a, c), b))|
      ≤ ∑ a, |(typeCount (fun i => ((s i, u i), y i)) ((a, c), b) : ℝ) / n - r ((a, c), b)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : S, ε := sum_le_sum fun a _ => h ((a, c), b)
    _ = Fintype.card S * ε := by rw [sum_const, card_univ, nsmul_eq_mul]

end Typical

section Joint

variable {Ω X Y : Type*} [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
  [MeasurableSingletonClass X] [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

private lemma mutualInfo_eq_jointInfo (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → X}
    {G : Ω → Y} (hF : Measurable F) (hG : Measurable G) :
    I[F : G ; μ] = jointInfo (fun z : X × Y => (μ.map fun ω => (F ω, G ω)).real {z}) := by
  classical
  set ν := μ.map fun ω => (F ω, G ω)
  have hFG : Measurable fun ω => (F ω, G ω) := hF.prodMk hG
  have h1 : ∀ x, (μ.map F).real {x} = ∑ y, ν.real {(x, y)} := by
    intro x
    rw [show μ.map F = ν.map Prod.fst by rw [Measure.map_map measurable_fst hFG]; rfl,
      measureReal_map_singleton, sum_filter, Fintype.sum_prod_type]
    rw [sum_eq_single x (fun x' _ hx => by simp [hx]) (by simp)]
    simp
  have h2 : ∀ y, (μ.map G).real {y} = ∑ x, ν.real {(x, y)} := by
    intro y
    rw [show μ.map G = ν.map Prod.snd by rw [Measure.map_map measurable_snd hFG]; rfl,
      measureReal_map_singleton, sum_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_eq_single y (fun y' _ hy => by simp [hy]) (by simp)]
    simp
  rw [mutualInfo_def, entropy_def, entropy_def, entropy_def, jointInfo]
  simp only [h1, h2]
  rfl

end Joint

section Letter

variable {St A B : Type*} [Fintype St] [DecidableEq St] [Fintype A] [Fintype B] [DecidableEq B]
  {m : ℕ}

omit [DecidableEq St] in
private lemma sum_filter_yu (F : (St × Fin m × A) × B → ℝ) (y : B) (u : Fin m) :
    ∑ w with (w.2, w.1.2.1) = (y, u), F w = ∑ s, ∑ x, F ((s, u, x), y) := by
  classical
  rw [sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type, sum_eq_single u (fun u' _ hu => sum_eq_zero fun x _ =>
    sum_eq_zero fun y' _ => by simp [hu]) (by simp)]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_eq_single y (fun y' _ hy => by simp [hy]) (by simp)]
  simp

omit [DecidableEq B] in
private lemma sum_filter_su (F : St × Fin m × A → ℝ) (s : St) (u : Fin m) :
    ∑ w with (w.1, w.2.1) = (s, u), F w = ∑ x, F (s, u, x) := by
  rw [sum_filter, Fintype.sum_prod_type, sum_eq_single s (fun s' _ hs => sum_eq_zero fun w _ =>
    by simp [hs]) (by simp), Fintype.sum_prod_type, sum_eq_single u (fun u' _ hu =>
    sum_eq_zero fun x _ => by simp [hu]) (by simp)]
  simp

omit [DecidableEq St] [DecidableEq B] in
private lemma sum_filter_u (F : St × Fin m × A → ℝ) (u : Fin m) :
    ∑ w with w.2.1 = u, F w = ∑ s, ∑ x, F (s, u, x) := by
  rw [sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type, sum_eq_single u (fun u' _ hu =>
    sum_eq_zero fun x _ => by simp [hu]) (by simp)]
  simp

omit [DecidableEq B] in
private lemma sum_filter_s (F : St × Fin m × A → ℝ) (s : St) :
    ∑ w with w.1 = s, F w = ∑ u, ∑ x, F (s, u, x) := by
  rw [sum_filter, Fintype.sum_prod_type, sum_eq_single s (fun s' _ hs => sum_eq_zero fun w _ =>
    by simp [hs]) (by simp), Fintype.sum_prod_type]
  simp

omit [Fintype St] [DecidableEq St] [Fintype B] [DecidableEq B] in
private noncomputable def pSU (q : PMF (St × Fin m × A)) (z : St × Fin m) : ℝ :=
  ∑ x, (q (z.1, z.2, x)).toReal

omit [Fintype St] [DecidableEq St] [Fintype B] [DecidableEq B] in
private lemma pSU_nonneg (q : PMF (St × Fin m × A)) (z : St × Fin m) : 0 ≤ pSU q z :=
  sum_nonneg fun _ _ => ENNReal.toReal_nonneg

omit [DecidableEq St] [Fintype B] [DecidableEq B] in
private lemma toReal_qU (q : PMF (St × Fin m × A)) (u : Fin m) :
    ((q.map fun t => t.2.1) u).toReal = ∑ s, pSU q (s, u) := by
  rw [toReal_map_apply, sum_filter_u]
  rfl

omit [Fintype St] [DecidableEq St] [Fintype B] [DecidableEq B] in
private lemma toReal_pS [Finite St] {pS : PMF St} (q : PMF (St × Fin m × A))
    (hq : q.map Prod.fst = pS) (s : St) : (pS s).toReal = ∑ u, pSU q (s, u) := by
  classical
  have := Fintype.ofFinite St
  rw [← hq, toReal_map_apply]
  convert sum_filter_s (fun w => (q w).toReal) s using 1
  rfl

omit [Fintype St] [DecidableEq St] [Fintype B] [DecidableEq B] in
private noncomputable def kern (q : PMF (St × Fin m × A)) (z : St × Fin m) : PMF A := by
  classical
  exact if h : ∑ x, q (z.1, z.2, x) = 0 then q.map fun t => t.2.2
    else PMF.ofFintype (fun x => q (z.1, z.2, x) / ∑ x', q (z.1, z.2, x')) (by
      rw [← ENNReal.sum_div]
      exact ENNReal.div_self h (ENNReal.sum_ne_top.2 fun x _ => PMF.apply_ne_top _ _))

omit [Fintype St] [DecidableEq St] [DecidableEq B] in
private noncomputable def chan (W : DMC (A × St) B) (q : PMF (St × Fin m × A)) :
    DMC (St × Fin m) B :=
  fun z => (kern q z).bind fun x => W (x, z.1)

omit [Fintype St] [DecidableEq St] [Fintype B] [DecidableEq B] in
private lemma pSU_mul_chan (W : DMC (A × St) B) (q : PMF (St × Fin m × A)) (z : St × Fin m)
    (y : B) : pSU q z * (chan W q z y).toReal =
      ∑ x, (q (z.1, z.2, x)).toReal * (W (x, z.1) y).toReal := by
  classical
  have hb : (chan W q z y).toReal = ∑ x, (kern q z x).toReal * (W (x, z.1) y).toReal := by
    rw [chan, PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum fun a _ =>
      ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    simp [ENNReal.toReal_mul]
  rw [hb]
  by_cases h : ∑ x, q (z.1, z.2, x) = 0
  · have h0 : ∀ x, q (z.1, z.2, x) = 0 := fun x => (sum_eq_zero_iff.1 h) x (mem_univ x)
    simp [pSU, h0]
  · have hne : ∑ x, q (z.1, z.2, x) ≠ ⊤ := ENNReal.sum_ne_top.2 fun x _ => PMF.apply_ne_top _ _
    have hp : pSU q z = (∑ x, q (z.1, z.2, x)).toReal := by
      rw [pSU, ENNReal.toReal_sum fun x _ => PMF.apply_ne_top _ _]
    have hp0 : pSU q z ≠ 0 := by
      rw [hp]
      exact ENNReal.toReal_ne_zero.2 ⟨h, hne⟩
    have hk : ∀ x, (kern q z x).toReal = (q (z.1, z.2, x)).toReal / pSU q z := by
      intro x
      simp only [kern, h, dite_false, PMF.ofFintype_apply]
      rw [ENNReal.toReal_div, hp]
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [hk]
    field_simp

omit [DecidableEq St] [DecidableEq B] in
private noncomputable def pYU (W : DMC (A × St) B) (q : PMF (St × Fin m × A)) (z : B × Fin m) :
    ℝ :=
  ∑ s, pSU q (s, z.2) * (chan W q (s, z.2) z.1).toReal

variable [MeasurableSpace St] [MeasurableSingletonClass St] [MeasurableSpace A]
  [MeasurableSingletonClass A] [MeasurableSpace B] [MeasurableSingletonClass B]

omit [DecidableEq St] [Fintype B] [DecidableEq B] in
private lemma mutualInfo_US [Finite B] (W : DMC (A × St) B) (q : PMF (St × Fin m × A)) :
    I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.1.1 ; (jointLaw W q).toMeasure] =
      jointInfo (pSU q) := by
  classical
  have hc : (jointLaw W q).map (fun b => (b.1.1, b.1.2.1)) = q.map (fun t => (t.1, t.2.1)) := by
    have h : ∀ a : St × Fin m × A, (W (a.2.2, a.1)).map (fun _ => (a.1, a.2.1)) =
        PMF.pure (a.1, a.2.1) := fun a => PMF.map_const _ _
    simp only [jointLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, h]
    exact PMF.bind_pure_comp _ q
  rw [mutualInfo_comm, mutualInfo_eq_jointInfo _ (measurable_of_finite _)
    (measurable_of_finite _)]
  congr 1
  funext z
  rw [PMF.toMeasure_map _ _ (measurable_of_finite _), PMF.toMeasure_real_singleton, hc,
    toReal_map_apply, sum_filter_su]
  rfl

omit [DecidableEq St] [DecidableEq B] in
private lemma mutualInfo_UY (W : DMC (A × St) B) (q : PMF (St × Fin m × A)) :
    I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.2 ; (jointLaw W q).toMeasure] =
      jointInfo (pYU W q) := by
  classical
  rw [mutualInfo_comm, mutualInfo_eq_jointInfo _ (measurable_of_finite _)
    (measurable_of_finite _)]
  congr 1
  funext z
  rw [PMF.toMeasure_map _ _ (measurable_of_finite _), PMF.toMeasure_real_singleton,
    toReal_map_apply, sum_filter_yu, pYU]
  refine sum_congr rfl fun s _ => ?_
  rw [pSU_mul_chan]
  refine sum_congr rfl fun x _ => ?_
  rw [show jointLaw W q = DMC.jointPMF (fun a : St × Fin m × A => W (a.2.2, a.1)) q from rfl,
    DMC.jointPMF_apply, ENNReal.toReal_mul]

end Letter

section Random

variable {St U B : Type*} [Fintype St] [DecidableEq St] [Fintype U] [DecidableEq U]
  [Fintype B] [DecidableEq B] {n L k : ℕ}

omit [Fintype St] [Fintype U] [Fintype B] [DecidableEq B] in
private noncomputable def encRow (Tc : Finset (Fin n → St × U)) (u₀ : Fin n → U)
    (D : Fin L → Fin n → U) (s : Fin n → St) : Fin n → U := by
  classical
  exact if h : ∃ l, (fun i => (s i, D l i)) ∈ Tc then D h.choose else u₀

omit [Fintype St] [DecidableEq St] [Fintype U] [Fintype B] in
private noncomputable def decAll (Td : Finset (Fin n → B × U)) (m₀ : Fin k)
    (C : Fin k → Fin L → Fin n → U) (y : Fin n → B) : Fin k := by
  classical
  exact if h : ∃ m l, (fun i => (y i, C m l i)) ∈ Td then h.choose else m₀

omit [Fintype St] [Fintype U] [Fintype B] [DecidableEq B] in
private lemma encRow_spec {Tc : Finset (Fin n → St × U)} {u₀ : Fin n → U}
    {D : Fin L → Fin n → U} {s : Fin n → St} (h : ∃ l, (fun i => (s i, D l i)) ∈ Tc) :
    ∃ l, encRow Tc u₀ D s = D l ∧ (fun i => (s i, D l i)) ∈ Tc := by
  classical
  refine ⟨h.choose, ?_, h.choose_spec⟩
  simp only [encRow, h, dite_true]

omit [Fintype St] [DecidableEq St] [Fintype U] [Fintype B] in
private lemma decAll_spec {Td : Finset (Fin n → B × U)} {m₀ : Fin k}
    {C : Fin k → Fin L → Fin n → U} {y : Fin n → B}
    (h : ∃ m l, (fun i => (y i, C m l i)) ∈ Td) :
    ∃ l, (fun i => (y i, C (decAll Td m₀ C y) l i)) ∈ Td := by
  classical
  simp only [decAll, h, dite_true]
  exact h.choose_spec

omit [DecidableEq St] [DecidableEq U] [DecidableEq B] in
private noncomputable def blk (V : DMC (St × U) B) (s : Fin n → St) (u : Fin n → U)
    (y : Fin n → B) : ℝ :=
  ∏ i, (V (s i, u i) (y i)).toReal

omit [Fintype St] [DecidableEq St] [Fintype U] [DecidableEq U] [Fintype B] [DecidableEq B] in
private lemma blk_nonneg (V : DMC (St × U) B) (s : Fin n → St) (u : Fin n → U)
    (y : Fin n → B) : 0 ≤ blk V s u y :=
  prod_nonneg fun _ _ => ENNReal.toReal_nonneg

omit [Fintype St] [DecidableEq St] [Fintype U] [DecidableEq U] [DecidableEq B] in
private lemma sum_blk (V : DMC (St × U) B) (s : Fin n → St) (u : Fin n → U) :
    ∑ y, blk V s u y = 1 :=
  sum_prod (fun i b => (V (s i, u i) b).toReal) fun _ => sum_toReal_pmf_eq_one _

private noncomputable def errV (V : DMC (St × U) B) (Tc : Finset (Fin n → St × U))
    (Td : Finset (Fin n → B × U)) (u₀ : Fin n → U) (m₀ : Fin k)
    (C : Fin k → Fin L → Fin n → U) (m : Fin k) (s : Fin n → St) : ℝ :=
  ∑ y, if decAll Td m₀ C y = m then 0 else blk V s (encRow Tc u₀ (C m) s) y

omit [Fintype St] [Fintype U] in
private lemma errV_le (V : DMC (St × U) B) (Tc : Finset (Fin n → St × U))
    (Td : Finset (Fin n → B × U)) (u₀ : Fin n → U) (m₀ : Fin k)
    (C : Fin k → Fin L → Fin n → U) (m : Fin k) (s : Fin n → St) :
    errV V Tc Td u₀ m₀ C m s ≤
      (if ∃ l, (fun i => (s i, C m l i)) ∈ Tc then 0 else 1) +
      (if (fun i => (s i, encRow Tc u₀ (C m) s i)) ∈ Tc then
        ∑ y, (if (fun i => (y i, encRow Tc u₀ (C m) s i)) ∈ Td then 0 else
          blk V s (encRow Tc u₀ (C m) s) y) else 0) +
      ∑ y, blk V s (encRow Tc u₀ (C m) s) y *
        ∑ m', ∑ l, (if m' ≠ m ∧ (fun i => (y i, C m' l i)) ∈ Td then 1 else 0) := by
  classical
  set u := encRow Tc u₀ (C m) s
  have hpt : ∀ y, (if decAll Td m₀ C y = m then 0 else blk V s u y) ≤
      (if ∃ l, (fun i => (s i, C m l i)) ∈ Tc then 0 else blk V s u y) +
      (if (fun i => (s i, u i)) ∈ Tc then
        (if (fun i => (y i, u i)) ∈ Td then 0 else blk V s u y) else 0) +
      blk V s u y * ∑ m', ∑ l, (if m' ≠ m ∧ (fun i => (y i, C m' l i)) ∈ Td then 1 else 0) := by
    intro y
    have hb := blk_nonneg V s u y
    have hS : 0 ≤ ∑ m', ∑ l, (if m' ≠ m ∧ (fun i => (y i, C m' l i)) ∈ Td then (1 : ℝ)
        else 0) := sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have h3 : 0 ≤ blk V s u y * ∑ m', ∑ l,
        (if m' ≠ m ∧ (fun i => (y i, C m' l i)) ∈ Td then (1 : ℝ) else 0) := mul_nonneg hb hS
    by_cases hd : decAll Td m₀ C y = m
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
      have h1 : 0 ≤ (if ∃ l, (fun i => (s i, C m l i)) ∈ Tc then 0 else blk V s u y) := by
        split_ifs <;> linarith
      have h2 : 0 ≤ (if (fun i => (s i, u i)) ∈ Tc then
          (if (fun i => (y i, u i)) ∈ Td then 0 else blk V s u y) else 0) := by
        split_ifs <;> linarith
      linarith
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    by_cases hc : ∃ l, (fun i => (s i, C m l i)) ∈ Tc
    · obtain ⟨l, hl, hlT⟩ := encRow_spec (u₀ := u₀) hc
      have huT : (fun i => (s i, u i)) ∈ Tc := by
        simp only [u, hl]
        exact hlT
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true huT)]
      by_cases hy : (fun i => (y i, u i)) ∈ Td
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hy)]
        have hex : ∃ m l, (fun i => (y i, C m l i)) ∈ Td := ⟨m, l, by
          simp only [u, hl] at hy
          exact hy⟩
        obtain ⟨l', hl'⟩ := decAll_spec (m₀ := m₀) hex
        have h1 : (1 : ℝ) ≤ ∑ m', ∑ l, (if m' ≠ m ∧ (fun i => (y i, C m' l i)) ∈ Td then 1
            else 0) := by
          calc (1 : ℝ) = if decAll Td m₀ C y ≠ m ∧
                (fun i => (y i, C (decAll Td m₀ C y) l' i)) ∈ Td then 1 else 0 := by
                rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hd, hl'⟩)]
            _ ≤ ∑ l, (if decAll Td m₀ C y ≠ m ∧
                (fun i => (y i, C (decAll Td m₀ C y) l i)) ∈ Td then (1 : ℝ) else 0) :=
                single_le_sum (f := fun l => if decAll Td m₀ C y ≠ m ∧
                  (fun i => (y i, C (decAll Td m₀ C y) l i)) ∈ Td then (1 : ℝ) else 0)
                  (fun _ _ => by split_ifs <;> norm_num) (mem_univ l')
            _ ≤ _ := single_le_sum (f := fun m' => ∑ l, (if m' ≠ m ∧
                  (fun i => (y i, C m' l i)) ∈ Td then (1 : ℝ) else 0))
                  (fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num)
                  (mem_univ (decAll Td m₀ C y))
        nlinarith
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hy)]
        linarith
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      have h2 : 0 ≤ (if (fun i => (s i, u i)) ∈ Tc then
          (if (fun i => (y i, u i)) ∈ Td then 0 else blk V s u y) else 0) := by
        split_ifs <;> linarith
      linarith
  refine (sum_le_sum fun y _ => hpt y).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_add_distrib]
  congr 1
  congr 1
  · split_ifs
    · simp
    · exact sum_blk V s u
  · split_ifs
    · rfl
    · simp

end Random

section Average

private lemma mul_sum_comm {α β : Type*} [Fintype α] [Fintype β] (w : α → ℝ) (X : α → β → ℝ) :
    ∑ a, w a * ∑ b, X a b = ∑ b, ∑ a, w a * X a b := by
  simp_rw [mul_sum]
  exact sum_comm

variable {St U B : Type*} [Fintype St] [DecidableEq St] [Fintype U] [DecidableEq U]
  [Fintype B] [DecidableEq B] {n L k : ℕ}

omit [DecidableEq St] [DecidableEq U] [Fintype B] [DecidableEq B] in
private lemma sum_row (qU : PMF U) (F : (Fin L → Fin n → U) → ℝ) (m : Fin k) :
    ∑ C : Fin k → Fin L → Fin n → U, (∏ m', ∏ l, iidProb qU (C m' l)) * F (C m) =
      ∑ D : Fin L → Fin n → U, (∏ l, iidProb qU (D l)) * F D := by
  have h := sum_prod_mul_apply (fun (_ : Fin k) (D : Fin L → Fin n → U) => ∏ l, iidProb qU (D l))
    (fun _ => sum_prod (fun _ u => iidProb qU u) fun _ => sum_iidProb qU n) F m
  exact h

omit [DecidableEq St] [DecidableEq U] [Fintype B] [DecidableEq B] in
private lemma sum_row_pair (qU : PMF U) (F G : (Fin L → Fin n → U) → ℝ) {m m' : Fin k}
    (h : m ≠ m') :
    ∑ C : Fin k → Fin L → Fin n → U,
        (∏ m'', ∏ l, iidProb qU (C m'' l)) * (F (C m) * G (C m')) =
      (∑ D : Fin L → Fin n → U, (∏ l, iidProb qU (D l)) * F D) *
        ∑ D : Fin L → Fin n → U, (∏ l, iidProb qU (D l)) * G D := by
  have h' := sum_prod_mul_apply_mul_apply
    (fun (_ : Fin k) (D : Fin L → Fin n → U) => ∏ l, iidProb qU (D l))
    (fun _ => sum_prod (fun _ u => iidProb qU u) fun _ => sum_iidProb qU n) F G h
  exact h'

omit [DecidableEq St] [DecidableEq U] [Fintype B] [DecidableEq B] in
private lemma sum_wC (qU : PMF U) :
    ∑ C : Fin k → Fin L → Fin n → U, (∏ m', ∏ l, iidProb qU (C m' l)) = 1 := by
  have h := sum_prod (fun (_ : Fin k) (D : Fin L → Fin n → U) => ∏ l, iidProb qU (D l))
    fun _ => sum_prod (fun _ u => iidProb qU u) fun _ => sum_iidProb qU n
  exact h

omit [Fintype St] [DecidableEq St] [Fintype U] [DecidableEq U] [Fintype B] [DecidableEq B] in
private lemma wC_nonneg (qU : PMF U) (C : Fin k → Fin L → Fin n → U) :
    0 ≤ ∏ m', ∏ l, iidProb qU (C m' l) :=
  prod_nonneg fun _ _ => prod_nonneg fun _ _ => iidProb_nonneg qU _

omit [Fintype B] [DecidableEq B] in
private lemma avg_t1 (qU : PMF U) (pS : PMF St) (Tc : Finset (Fin n → St × U)) (m : Fin k) :
    ∑ C : Fin k → Fin L → Fin n → U, (∏ m', ∏ l, iidProb qU (C m' l)) *
        ∑ s, iidProb pS s * (if ∃ l, (fun i => (s i, C m l i)) ∈ Tc then 0 else 1) =
      ∑ s, iidProb pS s * (1 - ∑ u ∈ univ.filter (fun u : Fin n → U =>
        (fun i => (s i, u i)) ∈ Tc), iidProb qU u) ^ L := by
  rw [mul_sum_comm]
  refine sum_congr rfl fun s _ => ?_
  simp_rw [mul_left_comm _ (iidProb pS s), ← mul_sum]
  congr 1
  rw [sum_row qU (fun D => if ∃ l, (fun i => (s i, D l i)) ∈ Tc then (0 : ℝ) else 1) m,
    ← sum_codebook_not_mem qU]
  refine sum_congr rfl fun D _ => ?_
  congr 1
  by_cases h : ∃ l, (fun i => (s i, D l i)) ∈ Tc
  · obtain ⟨l, hl⟩ := h
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨l, hl⟩), ite_eq_right_of_eq_false _ _
      (eq_false fun h' => h' l (by simpa using hl))]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_left_of_eq_true _ _
      (eq_true fun l hl => h ⟨l, by simpa using hl⟩)]

omit [DecidableEq St] [DecidableEq U] [Fintype B] [DecidableEq B] in
private lemma avg_le_const (qU : PMF U) (pS : PMF St) (X : (Fin k → Fin L → Fin n → U) →
    (Fin n → St) → ℝ) {β : ℝ} (h : ∀ C s, X C s ≤ β) :
    ∑ C : Fin k → Fin L → Fin n → U, (∏ m', ∏ l, iidProb qU (C m' l)) *
        ∑ s, iidProb pS s * X C s ≤ β := by
  have h1 : ∀ C, ∑ s, iidProb pS s * X C s ≤ β := fun C =>
    (sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h C s) (iidProb_nonneg pS s)).trans
      (by rw [← sum_mul, sum_iidProb, one_mul])
  calc _ ≤ ∑ C : Fin k → Fin L → Fin n → U, (∏ m', ∏ l, iidProb qU (C m' l)) * β :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (h1 C) (wC_nonneg qU C)
    _ = β := by rw [← sum_mul, sum_wC, one_mul]

omit [DecidableEq St] in
private lemma avg_t3 (qU : PMF U) (pS : PMF St) (Td : Finset (Fin n → B × U))
    (E : (Fin L → Fin n → U) → (Fin n → St) → (Fin n → B) → ℝ) (hE0 : ∀ D s y, 0 ≤ E D s y)
    (hE1 : ∀ D s, ∑ y, E D s y = 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ y : Fin n → B, ∑ u ∈ univ.filter (fun u : Fin n → U => (fun i => (y i, u i)) ∈ Td),
      iidProb qU u ≤ ρ) (m : Fin k) :
    ∑ C : Fin k → Fin L → Fin n → U, (∏ m', ∏ l, iidProb qU (C m' l)) *
        ∑ s, iidProb pS s * ∑ y, E (C m) s y *
          ∑ m', ∑ l, (if m' ≠ m ∧ (fun i => (y i, C m' l i)) ∈ Td then 1 else 0) ≤
      k * L * ρ := by
  set wr : (Fin L → Fin n → U) → ℝ := fun D => ∏ l, iidProb qU (D l)
  have hwr0 : ∀ D, 0 ≤ wr D := fun D => prod_nonneg fun _ _ => iidProb_nonneg qU _
  have key : ∀ s y m' l, ∑ C : Fin k → Fin L → Fin n → U, (∏ m'', ∏ l, iidProb qU (C m'' l)) *
      (E (C m) s y * (if m' ≠ m ∧ (fun i => (y i, C m' l i)) ∈ Td then 1 else 0)) ≤
      (∑ D, wr D * E D s y) * ρ := by
    intro s y m' l
    have hF0 : 0 ≤ ∑ D, wr D * E D s y := sum_nonneg fun D _ => mul_nonneg (hwr0 D) (hE0 D s y)
    by_cases hm : m' = m
    · subst hm
      simp only [ne_eq, not_true_eq_false, false_and, ite_false, mul_zero, sum_const_zero]
      exact mul_nonneg hF0 hρ0
    · have e : ∀ C : Fin k → Fin L → Fin n → U,
          (if m' ≠ m ∧ (fun i => (y i, C m' l i)) ∈ Td then (1 : ℝ) else 0) =
            (fun D : Fin L → Fin n → U =>
              if D l ∈ univ.filter (fun u : Fin n → U => (fun i => (y i, u i)) ∈ Td)
              then (1 : ℝ) else 0) (C m') := fun C => by
        by_cases h : (fun i => (y i, C m' l i)) ∈ Td <;> simp [h, hm]
      rw [sum_congr rfl fun C _ => by rw [e C]]
      refine (sum_row_pair qU (fun D => E D s y) (fun D : Fin L → Fin n → U =>
        if D l ∈ univ.filter (fun u : Fin n → U => (fun i => (y i, u i)) ∈ Td)
        then (1 : ℝ) else 0) (Ne.symm hm)).trans_le ?_
      rw [sum_codebook_apply_mem]
      exact mul_le_mul_of_nonneg_left (hρ y) hF0
  calc _ = ∑ s, iidProb pS s * ∑ y, ∑ m', ∑ l, ∑ C : Fin k → Fin L → Fin n → U,
        (∏ m'', ∏ l, iidProb qU (C m'' l)) *
          (E (C m) s y * (if m' ≠ m ∧ (fun i => (y i, C m' l i)) ∈ Td then 1 else 0)) := by
        rw [mul_sum_comm]
        refine sum_congr rfl fun s _ => ?_
        simp_rw [mul_left_comm _ (iidProb pS s), ← mul_sum]
        congr 1
        rw [mul_sum_comm]
        refine sum_congr rfl fun y _ => ?_
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun m' _ => ?_
        rw [sum_comm]
    _ ≤ ∑ s, iidProb pS s * ∑ y, ∑ _m' : Fin k, ∑ _l : Fin L, (∑ D, wr D * E D s y) * ρ :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (sum_le_sum fun y _ =>
          sum_le_sum fun m' _ => sum_le_sum fun l _ => key s y m' l) (iidProb_nonneg pS s)
    _ = k * L * ρ := by
        have h1 : ∀ s, ∑ y, (∑ D, wr D * E D s y) = 1 := fun s => by
          rw [sum_comm]
          simp_rw [← mul_sum, hE1, mul_one]
          exact sum_prod (fun _ u => iidProb qU u) fun _ => sum_iidProb qU n
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h2 : ∀ s, ∑ y, (k : ℝ) * (L * ((∑ D, wr D * E D s y) * ρ)) = k * L * ρ :=
          fun s => by
            rw [← mul_sum, ← mul_sum, ← sum_mul, h1]
            ring
        simp_rw [h2, ← sum_mul, sum_iidProb, one_mul]

omit [Fintype St] [Fintype U] [DecidableEq U] [Fintype B] [DecidableEq B] in
private lemma typeCount_eq_zero_of_iidProb_ne_zero {pS : PMF St} {s : Fin n → St}
    (hs : iidProb pS s ≠ 0) (x : St) (hx : (pS x).toReal = 0) : typeCount s x = 0 := by
  by_contra h
  obtain ⟨i, hi⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h)
  apply hs
  refine prod_eq_zero (mem_univ i) ?_
  rw [(mem_filter.1 hi).2, hx]

omit [Fintype B] [DecidableEq B] in
private lemma sum_cov_le (qU : PMF U) (pS : PMF St) (Tc : Finset (Fin n → St × U)) {ε a : ℝ}
    (hε : 0 < ε) (hn : 0 < n)
    (hcov : ∀ s : Fin n → St, s ∈ strongTypicalSet (fun x => (pS x).toReal) n ε →
      (∀ x, (pS x).toReal = 0 → typeCount s x = 0) →
      a ≤ ∑ u ∈ univ.filter (fun u : Fin n → U => (fun i => (s i, u i)) ∈ Tc), iidProb qU u) :
    ∑ s, iidProb pS s * (1 - ∑ u ∈ univ.filter (fun u : Fin n → U =>
        (fun i => (s i, u i)) ∈ Tc), iidProb qU u) ^ L ≤
      Fintype.card St / (4 * n * ε ^ 2) + Real.exp (-(L * a)) := by
  set T := strongTypicalSet (fun x => (pS x).toReal) n ε
  have hpt : ∀ s : Fin n → St, iidProb pS s * (1 - ∑ u ∈ univ.filter (fun u : Fin n → U =>
      (fun i => (s i, u i)) ∈ Tc), iidProb qU u) ^ L ≤
      (if s ∈ T then 0 else iidProb pS s) + iidProb pS s * Real.exp (-(L * a)) := by
    intro s
    set P := ∑ u ∈ univ.filter (fun u : Fin n → U => (fun i => (s i, u i)) ∈ Tc), iidProb qU u
    have hP0 : 0 ≤ P := sum_nonneg fun u _ => iidProb_nonneg qU u
    have hP1 : P ≤ 1 := (sum_le_univ_sum_of_nonneg fun u => iidProb_nonneg qU u).trans_eq
      (sum_iidProb qU n)
    have hi := iidProb_nonneg pS s
    have hpow : (1 - P) ^ L ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have he := (Real.exp_pos (-(L * a))).le
    by_cases hT : s ∈ T
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hT), zero_add]
      by_cases hs : iidProb pS s = 0
      · rw [hs]
        simp
      · have ha := hcov s hT fun x hx => typeCount_eq_zero_of_iidProb_ne_zero hs x hx
        refine mul_le_mul_of_nonneg_left ?_ hi
        calc (1 - P) ^ L ≤ Real.exp (-P) ^ L :=
              pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-P)]) L
          _ = Real.exp (-(L * P)) := by rw [← Real.exp_nat_mul]; ring_nf
          _ ≤ Real.exp (-(L * a)) := Real.exp_le_exp.2 (by
              have : (L : ℝ) * a ≤ L * P := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg L)
              linarith)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hT)]
      nlinarith [mul_nonneg hi he]
  refine (sum_le_sum fun s _ => hpt s).trans ?_
  rw [sum_add_distrib, ← sum_mul, sum_iidProb, one_mul]
  have h1 : ∑ s : Fin n → St, (if s ∈ T then 0 else iidProb pS s) =
      ∑ s ∈ univ.filter (fun s : Fin n → St => s ∉ T), iidProb pS s := by
    rw [sum_filter]
    exact sum_congr rfl fun s _ => by split_ifs <;> simp_all
  rw [h1]
  linarith [sum_iidProb_not_typical_le pS hε hn]

private lemma exists_book (V : DMC (St × U) B) (qU : PMF U) (pS : PMF St)
    (Tc : Finset (Fin n → St × U)) (Td : Finset (Fin n → B × U)) (u₀ : Fin n → U) (m₀ : Fin k)
    {ε a β ρ : ℝ} (hε : 0 < ε) (hn : 0 < n)
    (hcov : ∀ s : Fin n → St, s ∈ strongTypicalSet (fun x => (pS x).toReal) n ε →
      (∀ x, (pS x).toReal = 0 → typeCount s x = 0) →
      a ≤ ∑ u ∈ univ.filter (fun u : Fin n → U => (fun i => (s i, u i)) ∈ Tc), iidProb qU u)
    (hβ0 : 0 ≤ β) (hβ : ∀ (s : Fin n → St) (u : Fin n → U), (fun i => (s i, u i)) ∈ Tc →
      ∑ y, (if (fun i => (y i, u i)) ∈ Td then 0 else blk V s u y) ≤ β)
    (hρ0 : 0 ≤ ρ) (hρ : ∀ y : Fin n → B, ∑ u ∈ univ.filter
      (fun u : Fin n → U => (fun i => (y i, u i)) ∈ Td), iidProb qU u ≤ ρ) :
    ∃ C : Fin k → Fin L → Fin n → U,
      (∑ m, ∑ s, iidProb pS s * errV V Tc Td u₀ m₀ C m s) / k ≤
        Fintype.card St / (4 * n * ε ^ 2) + Real.exp (-(L * a)) + β + k * L * ρ := by
  set bd := Fintype.card St / (4 * n * ε ^ 2) + Real.exp (-(L * a)) + β + k * L * ρ
  have hk : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => (h ▸ m₀).elim0)
  have hm : ∀ m : Fin k, ∑ C : Fin k → Fin L → Fin n → U, (∏ m', ∏ l, iidProb qU (C m' l)) *
      ∑ s, iidProb pS s * errV V Tc Td u₀ m₀ C m s ≤ bd := by
    intro m
    have e1 := avg_t1 (L := L) qU pS Tc m
    have e2 := avg_le_const (k := k) (L := L) qU pS (fun C s =>
      if (fun i => (s i, encRow Tc u₀ (C m) s i)) ∈ Tc then
        ∑ y, (if (fun i => (y i, encRow Tc u₀ (C m) s i)) ∈ Td then 0 else
          blk V s (encRow Tc u₀ (C m) s) y) else 0) (β := β) fun C s => by
        split_ifs with h
        · exact hβ s _ h
        · exact hβ0
    have e3 := avg_t3 (L := L) qU pS Td (fun D s y => blk V s (encRow Tc u₀ D s) y)
      (fun D s y => blk_nonneg V s (encRow Tc u₀ D s) y)
      (fun D s => sum_blk V s (encRow Tc u₀ D s)) hρ0 hρ m
    have hc := sum_cov_le (L := L) qU pS Tc hε hn hcov
    calc _ ≤ ∑ C : Fin k → Fin L → Fin n → U, (∏ m', ∏ l, iidProb qU (C m' l)) *
          ∑ s, iidProb pS s * ((if ∃ l, (fun i => (s i, C m l i)) ∈ Tc then 0 else 1) +
            (if (fun i => (s i, encRow Tc u₀ (C m) s i)) ∈ Tc then
              ∑ y, (if (fun i => (y i, encRow Tc u₀ (C m) s i)) ∈ Td then 0 else
                blk V s (encRow Tc u₀ (C m) s) y) else 0) +
            ∑ y, blk V s (encRow Tc u₀ (C m) s) y *
              ∑ m', ∑ l, (if m' ≠ m ∧ (fun i => (y i, C m' l i)) ∈ Td then 1 else 0)) :=
          sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (sum_le_sum fun s _ =>
            mul_le_mul_of_nonneg_left (errV_le V Tc Td u₀ m₀ C m s) (iidProb_nonneg pS s))
            (wC_nonneg qU C)
      _ ≤ bd := by
          simp only [mul_add, sum_add_distrib]
          linarith
  have havg : ∑ C : Fin k → Fin L → Fin n → U, (∏ m', ∏ l, iidProb qU (C m' l)) *
      ((∑ m, ∑ s, iidProb pS s * errV V Tc Td u₀ m₀ C m s) / k) ≤ bd := by
    have e : ∀ C : Fin k → Fin L → Fin n → U, (∏ m', ∏ l, iidProb qU (C m' l)) *
        ((∑ m, ∑ s, iidProb pS s * errV V Tc Td u₀ m₀ C m s) / k) =
        (∑ m, (∏ m', ∏ l, iidProb qU (C m' l)) *
          ∑ s, iidProb pS s * errV V Tc Td u₀ m₀ C m s) / k := fun C => by
      rw [mul_div_assoc', mul_sum]
    rw [sum_congr rfl fun C _ => e C, ← sum_div, sum_comm, div_le_iff₀ hk]
    calc _ ≤ ∑ _m : Fin k, bd := sum_le_sum fun m _ => hm m
      _ = bd * k := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  exact exists_le_of_sum_mul_le (wC_nonneg qU) (sum_wC qU) havg

end Average

private lemma ceil_exp_bounds {a : ℝ} (ha : 0 ≤ a) :
    0 < ⌈Real.exp a⌉₊ ∧ Real.exp a ≤ ⌈Real.exp a⌉₊ ∧ (⌈Real.exp a⌉₊ : ℝ) ≤ 2 * Real.exp a := by
  have h1 : 1 ≤ Real.exp a := Real.one_le_exp ha
  have hlt : (⌈Real.exp a⌉₊ : ℝ) < Real.exp a + 1 := Nat.ceil_lt_add_one (Real.exp_pos a).le
  exact ⟨Nat.ceil_pos.2 (Real.exp_pos a), Nat.le_ceil _, by linarith⟩

section Ucode

variable {St U B : Type*} [Fintype St] [Fintype U] [MeasurableSpace U]
  [MeasurableSingletonClass U] [Fintype B]

private lemma exists_Ucode (V : DMC (St × U) B) (pS : PMF St) (qU : PMF U) (p : St × U → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hS : ∀ s, (pS s).toReal = ∑ u, p (s, u))
    (hU : ∀ u, (qU u).toReal = ∑ s, p (s, u)) (hI0 : 0 ≤ jointInfo p) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R < jointInfo (fun z : B × U => ∑ s, p (s, z.2) * (V (s, z.2) z.1).toReal) -
      jointInfo p) {e : ℝ} (he : 0 < e) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ k : ℕ, Real.exp (n * R) ≤ k ∧
      ∃ (enc : Fin k → (Fin n → St) → Fin n → U) (dec : (Fin n → B) → Fin k),
        (∑ m, ∑ s, iidProb pS s *
          ∑ y, (if dec y = m then 0 else blk V s (enc m s) y)) / k ≤ e := by
  classical
  set pYU : B × U → ℝ := fun z => ∑ s, p (s, z.2) * (V (s, z.2) z.1).toReal
  set IUY := jointInfo pYU
  set IUS := jointInfo p
  set γ := (IUY - IUS - R) / 4
  have hγ : 0 < γ := by simp only [γ]; linarith
  have hqY : ∀ u, (qU u).toReal = ∑ b, pYU (b, u) := fun u => by
    simp only [pYU]
    rw [sum_comm, hU]
    refine sum_congr rfl fun s _ => ?_
    rw [← mul_sum, sum_toReal_pmf_eq_one, mul_one]
  obtain ⟨εd, hεd, hpack⟩ := strong_packing pYU qU hqY hγ
  have hSt : (0 : ℝ) < Fintype.card St := by
    have : Nonempty St := ⟨pS.support_nonempty.some⟩
    exact_mod_cast Fintype.card_pos
  set δ := min γ (εd / (2 * Fintype.card St))
  have hδ : 0 < δ := lt_min hγ (by positivity)
  have hδγ : δ ≤ γ := min_le_left _ _
  have hδd : (Fintype.card St : ℝ) * (δ + δ) ≤ εd := by
    have h := min_le_right γ (εd / (2 * Fintype.card St))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨εS, hεS, hcov⟩ := strong_covering p hp0 qU hU hδ
  have t1 : Tendsto (fun n : ℕ => (Fintype.card St : ℝ) / (4 * εS ^ 2) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have t3 : Tendsto (fun n : ℕ => (Fintype.card (St × U) * Fintype.card B : ℝ) / (4 * δ ^ 2) / n)
      atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have t2 := tendsto_exp_nat_mul (neg_neg_of_pos hδ)
  have t4 := (tendsto_exp_nat_mul (neg_neg_of_pos hγ)).const_mul 4
  rw [mul_zero] at t4
  have he4 : (0 : ℝ) < e / 4 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hpack.and (hcov.and ((eventually_ge_atTop 1).and
    ((t1.eventually (gt_mem_nhds he4)).and ((t2.eventually (gt_mem_nhds he4)).and
    ((t3.eventually (gt_mem_nhds he4)).and (t4.eventually (gt_mem_nhds he4))))))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hpk, hcv, hn1, h1, h2, h3, h4⟩ := hN n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨hk0, hk1, hk2⟩ := ceil_exp_bounds (mul_nonneg hnpos.le hR0)
  obtain ⟨hL0, hL1, hL2⟩ := ceil_exp_bounds (mul_nonneg hnpos.le
    (show 0 ≤ IUS + 2 * δ by linarith))
  set k := ⌈Real.exp (n * R)⌉₊
  set L := ⌈Real.exp (n * (IUS + 2 * δ))⌉₊
  have u0 : U := qU.support_nonempty.some
  set Tc := strongTypicalSet p n δ
  set Td := strongTypicalSet pYU n εd
  set a := Real.exp (-(n * (IUS + δ)))
  set β := (Fintype.card (St × U) * Fintype.card B : ℝ) / (4 * n * δ ^ 2)
  set ρ := Real.exp (-(n * (IUY - γ)))
  have hcov' : ∀ s : Fin n → St, s ∈ strongTypicalSet (fun x => (pS x).toReal) n εS →
      (∀ x, (pS x).toReal = 0 → typeCount s x = 0) →
      a ≤ ∑ u ∈ univ.filter (fun u : Fin n → U => (fun i => (s i, u i)) ∈ Tc), iidProb qU u := by
    intro s hs hsupp
    refine hcv s (fun x => ?_) (fun x hx => hsupp x (by rw [hS]; exact hx))
    rw [← hS]
    exact mem_strongTypicalSet.1 hs x
  have hβ : ∀ (s : Fin n → St) (u : Fin n → U), (fun i => (s i, u i)) ∈ Tc →
      ∑ y, (if (fun i => (y i, u i)) ∈ Td then 0 else blk V s u y) ≤ β := by
    intro s u hsu
    have hm := sum_not_mem_strongTypicalSet_le V p hδ hn1 hsu
    rw [sum_ite, sum_const_zero, zero_add]
    refine le_trans (sum_le_sum_of_subset_of_nonneg (fun y hy => ?_)
      fun y _ _ => blk_nonneg V s u y) (le_of_eq_of_le (sum_congr rfl fun y _ => rfl) hm)
    rw [mem_filter] at hy ⊢
    refine ⟨mem_univ _, fun hT => hy.2 ?_⟩
    have hM : (fun i => (y i, u i)) ∈ strongTypicalSet pYU n (Fintype.card St * (δ + δ)) :=
      mem_typical_marginal (r := fun ab : (St × U) × B => p ab.1 * (V ab.1 ab.2).toReal) hT
    exact strongTypicalSet_mono hδd hM
  obtain ⟨C, hC⟩ := exists_book (L := L) V qU pS Tc Td (fun _ => u0) (⟨0, hk0⟩ : Fin k) hεS hn1
    hcov' (by positivity) hβ (Real.exp_pos _).le hpk
  refine ⟨k, hk1, fun m s => encRow Tc (fun _ => u0) (C m) s, decAll Td ⟨0, hk0⟩ C,
    hC.trans ?_⟩
  have e1 : (Fintype.card St : ℝ) / (4 * n * εS ^ 2) < e / 4 := by
    have : (Fintype.card St : ℝ) / (4 * n * εS ^ 2) =
        (Fintype.card St : ℝ) / (4 * εS ^ 2) / n := by field_simp
    rw [this]
    exact h1
  have e3 : β < e / 4 := by
    have : β = (Fintype.card (St × U) * Fintype.card B : ℝ) / (4 * δ ^ 2) / n := by
      simp only [β]
      field_simp
    rw [this]
    exact h3
  have e2 : Real.exp (-(L * a)) ≤ Real.exp (n * -δ) := by
    refine Real.exp_le_exp.2 ?_
    have hLa : Real.exp (n * δ) ≤ L * a := by
      calc Real.exp (n * δ) = Real.exp (n * (IUS + 2 * δ)) * a := by
            rw [← Real.exp_add]; ring_nf
        _ ≤ L * a := mul_le_mul_of_nonneg_right hL1 (Real.exp_pos _).le
    have := Real.add_one_le_exp (n * δ)
    nlinarith
  have e4 : (k : ℝ) * L * ρ ≤ 4 * Real.exp (n * -γ) := by
    calc (k : ℝ) * L * ρ ≤ 2 * Real.exp (n * R) * (2 * Real.exp (n * (IUS + 2 * δ))) * ρ := by
          gcongr
      _ = 4 * Real.exp (n * (R + (IUS + 2 * δ) - (IUY - γ))) := by
          simp only [ρ]
          rw [show n * (R + (IUS + 2 * δ) - (IUY - γ)) =
            n * R + n * (IUS + 2 * δ) + -(n * (IUY - γ)) by ring, Real.exp_add, Real.exp_add]
          ring
      _ ≤ 4 * Real.exp (n * -γ) := by
          gcongr
          simp only [γ] at hδγ ⊢
          linarith
  linarith

end Ucode

section Final

variable {St A B : Type*} [Fintype St] [DecidableEq St] [Fintype A] [Fintype B] [DecidableEq B]
  {m n k : ℕ}

omit [Fintype St] [DecidableEq St] [DecidableEq B] in
private lemma exists_input (W : DMC (A × St) B) (q : PMF (St × Fin m × A)) (u : Fin n → Fin m)
    (s : Fin n → St) (D : (Fin n → B) → Prop) [DecidablePred D] :
    ∃ x : Fin n → A, ∑ y, (if D y then 0 else ∏ i, (W (x i, s i) (y i)).toReal) ≤
      ∑ y, (if D y then 0 else blk (chan W q) s u y) := by
  set w : (Fin n → A) → ℝ := fun x => ∏ i, (kern q (s i, u i) (x i)).toReal
  have hw0 : ∀ x, 0 ≤ w x := fun x => prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hw1 : ∑ x, w x = 1 :=
    sum_prod (fun i a => (kern q (s i, u i) a).toReal) fun _ => sum_toReal_pmf_eq_one _
  refine exists_le_of_sum_mul_le hw0 hw1 (le_of_eq ?_)
  rw [mul_sum_comm]
  refine sum_congr rfl fun y _ => ?_
  by_cases hD : D y
  · simp [hD]
  · simp only [hD, ite_false, blk]
    have hc : ∀ i, (chan W q (s i, u i) (y i)).toReal =
        ∑ a, (kern q (s i, u i) a).toReal * (W (a, s i) (y i)).toReal := fun i => by
      rw [chan, PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum fun a _ =>
        ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
      simp [ENNReal.toReal_mul]
    simp_rw [hc, Fintype.prod_sum, w, ← prod_mul_distrib]

omit [Fintype A] [DecidableEq St] [DecidableEq B] in
private lemma avgError_toReal (W : DMC (A × St) B) (pS : PMF St)
    (c : StateCode (Fin k) St A B n) :
    (c.avgError W pS).toReal = (∑ m, ∑ s, iidProb pS s *
      ∑ y, (if c.dec y = m then 0 else ∏ i, (W (c.enc m s i, s i) (y i)).toReal)) / k := by
  have hy : ∀ (m : Fin k) (s : Fin n → St) (y : Fin n → B),
      (if c.dec y = m then 0 else ∏ i, W (c.enc m s i, s i) (y i)) ≠ ⊤ := fun m s y => by
    split_ifs
    · exact ENNReal.zero_ne_top
    · exact ENNReal.prod_ne_top fun i _ => PMF.apply_ne_top _ _
  have hs : ∀ (m : Fin k) (s : Fin n → St), (∏ i, pS (s i)) * ∑ y : Fin n → B,
      (if c.dec y = m then 0 else ∏ i, W (c.enc m s i, s i) (y i)) ≠ ⊤ := fun m s =>
    ENNReal.mul_ne_top (ENNReal.prod_ne_top fun i _ => PMF.apply_ne_top _ _)
      (ENNReal.sum_ne_top.2 fun y _ => hy m s y)
  rw [StateCode.avgError, ENNReal.toReal_div, Fintype.card_fin, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun m _ => ENNReal.sum_ne_top.2 fun s _ => hs m s]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [ENNReal.toReal_sum fun s _ => hs m s]
  refine sum_congr rfl fun s _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_sum fun y _ => hy m s y]
  congr 1
  refine sum_congr rfl fun y _ => ?_
  split_ifs
  · rfl
  · rw [ENNReal.toReal_prod]

variable [MeasurableSpace St] [MeasurableSingletonClass St] [MeasurableSpace A]
  [MeasurableSingletonClass A] [MeasurableSpace B] [MeasurableSingletonClass B]

omit [Fintype A] [DecidableEq St] [DecidableEq B] [MeasurableSpace St]
  [MeasurableSingletonClass St] [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private lemma achievable_mono {W : DMC (A × St) B} {pS : PMF St} {R R' : ℝ}
    (h : Achievable W pS R') (hR : R ≤ R') : Achievable W pS R := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hn
  exact ⟨k, (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg n))).trans hk,
    c, hc⟩

omit [Fintype A] [DecidableEq St] [DecidableEq B] [MeasurableSpace St]
  [MeasurableSingletonClass St] [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [MeasurableSingletonClass B] in
theorem achievable_zero [Nonempty A] (W : DMC (A × St) B) (pS : PMF St) :
    Achievable W pS 0 := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨1, by simp, ⟨fun _ _ _ => Classical.arbitrary A, fun _ => 0⟩, ?_⟩⟩
  simp [StateCode.avgError]

omit [Fintype A] [DecidableEq St] [DecidableEq B] in
theorem achievable_of_lt_infoCapacity [Finite A] [Nonempty A] (W : DMC (A × St) B) (pS : PMF St)
    {R : ℝ} (h : R < infoCapacity W pS) : Achievable W pS R := by
  classical
  have := Fintype.ofFinite A
  rcases lt_or_ge R 0 with hR0 | hR0
  · exact achievable_mono (achievable_zero W pS) hR0.le
  set a : A := Classical.arbitrary A
  have hne : {v | ∃ (m : ℕ) (q : PMF (St × Fin m × A)), q.map Prod.fst = pS ∧
      v = I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.2 ; (jointLaw W q).toMeasure] -
        I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.1.1 ;
          (jointLaw W q).toMeasure]}.Nonempty := by
    refine ⟨_, 1, pS.map fun s => (s, 0, a), ?_, rfl⟩
    rw [PMF.map_comp]
    exact PMF.map_id pS
  obtain ⟨v, ⟨m, q, hq, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hne h
  rw [mutualInfo_US, mutualInfo_UY] at hv
  have hI0 : 0 ≤ jointInfo (pSU q) := by
    rw [← mutualInfo_US W q]
    exact mutualInfo_nonneg _ (measurable_of_finite _) (measurable_of_finite _)
  intro ε hε
  set e := (min ε 1).toReal
  have he : 0 < e := ENNReal.toReal_pos (lt_min hε one_pos).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
  have heε : ENNReal.ofReal e ≤ ε := by
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
    exact min_le_left _ _
  obtain ⟨N, hN⟩ := exists_Ucode (chan W q) pS (q.map fun t => t.2.1) (pSU q) (pSU_nonneg q)
    (toReal_pS q hq) (toReal_qU q) hI0 hR0 hv he
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, enc, dec, hb⟩ := hN n hn
  choose x hx using fun (m' : Fin k) (s : Fin n → St) =>
    exists_input W q (enc m' s) s (fun y => dec y = m')
  refine ⟨k, hk, ⟨x, dec⟩, ?_⟩
  refine le_trans ?_ heε
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.cast_pos.1 ((Real.exp_pos _).trans_le hk))
  have hfin : StateCode.avgError (⟨x, dec⟩ : StateCode (Fin k) St A B n) W pS ≠ ⊤ := by
    unfold StateCode.avgError
    refine ENNReal.div_ne_top (ENNReal.sum_ne_top.2 fun m' _ =>
      ENNReal.sum_ne_top.2 fun s _ => ENNReal.mul_ne_top
        (ENNReal.prod_ne_top fun i _ => PMF.apply_ne_top _ _)
        (ENNReal.sum_ne_top.2 fun y _ => ?_)) (by simp [hk0])
    split_ifs
    · exact ENNReal.zero_ne_top
    · exact ENNReal.prod_ne_top fun i _ => PMF.apply_ne_top _ _
  rw [ENNReal.le_ofReal_iff_toReal_le hfin he.le, avgError_toReal]
  refine le_trans (div_le_div_of_nonneg_right (sum_le_sum fun m' _ => sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_left (hx m' s) (iidProb_nonneg pS s)) (Nat.cast_nonneg k)) hb

end Final

end GelfandPinsker

end Meat
