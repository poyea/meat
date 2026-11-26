import Meat.Channel.State
import Meat.Channel.Converse
import Meat.Open.Interactive

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

namespace GelfandPinsker

section Chain

variable {Ω T St B : Type*} [MeasurableSpace Ω] [Finite Ω] [MeasurableSingletonClass Ω]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure Ω) {n : ℕ}

omit [Finite Ω] [MeasurableSingletonClass Ω] in
private lemma cmi_pair {P Q R S : Type*} [Fintype P] [MeasurableSpace P]
    [MeasurableSingletonClass P] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {X : Ω → P} {Y : Ω → Q} {Z : Ω → R} {V : Ω → S} :
    I[X : fun ω => (Y ω, V ω) | Z ; μ] =
      I[X : Y | Z ; μ] + I[X : V | fun ω => (Y ω, Z ω) ; μ] := by
  have e1 : H[fun ω => (X ω, (Y ω, Z ω)) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    (entropy_assoc μ).symm
  have e2 : H[fun ω => (V ω, (Y ω, Z ω)) ; μ] = H[fun ω => ((Y ω, V ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((Y ω, V ω), Z ω))
      (f := fun p => (p.1.2, (p.1.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.2.1 h.1) h.2.2
  have e3 : H[fun ω => ((X ω, V ω), (Y ω, Z ω)) ; μ]
      = H[fun ω => ((X ω, (Y ω, V ω)), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, (Y ω, V ω)), Z ω))
      (f := fun p => ((p.1.1, p.1.2.2), (p.1.2.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 (Prod.ext h.2.1 h.1.2)) h.2.2
  simp only [condMutualInfo_def, condEntropy_def]
  rw [e1, e2, e3]
  ring

omit [Finite Ω] [MeasurableSingletonClass Ω] in
private lemma cmi_cond_inj {P Q R S : Type*} [Fintype P] [MeasurableSpace P]
    [MeasurableSingletonClass P] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {X : Ω → P} {Y : Ω → Q} {Z : Ω → R} {Z' : Ω → S} {e : R → S}
    (he : Function.Injective e) (hZ : ∀ ω, Z' ω = e (Z ω)) :
    I[X : Y | Z' ; μ] = I[X : Y | Z ; μ] := by
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy, condMutualInfo_eq_condEntropy_sub_condEntropy,
    condEntropy_cond_of_injective μ he hZ]
  congr 1
  exact condEntropy_cond_of_injective μ (Z := fun ω => (X ω, Z ω))
    (e := fun p => (p.1, e p.2)) (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (he h.2)) fun ω => by rw [hZ]

omit [Finite Ω] [MeasurableSingletonClass Ω] [Fintype St] [MeasurableSpace St]
  [MeasurableSingletonClass St] in
private lemma mutualInfo_eq_sum_Iio [IsProbabilityMeasure μ] (Mv : Ω → T) (Y : Ω → Fin n → B) :
    I[Mv : Y ; μ] = ∑ i, I[Mv : fun ω => Y ω i | fun ω => seqRestrict (Y ω) (Iio i) ; μ] := by
  rw [mutualInfo_comm, mutualInfo_eq_sum μ Y Mv]
  refine sum_congr rfl fun i _ => ?_
  rw [condMutualInfo_comm]
  refine cmi_cond_inj μ (Z := fun ω => seqRestrict (Y ω) (Iio i))
    (e := fun r j => r ⟨⟨j, j.2.trans i.2⟩, by simp [Fin.lt_def]⟩) (fun a b h => ?_)
    fun ω => rfl
  funext t
  have ht : (t : Fin n) < i := mem_Iio.1 t.2
  have := congrFun h ⟨t.1.1, ht⟩
  simpa using this

omit [Finite Ω] [MeasurableSingletonClass Ω] in
private lemma letter_y {P Q R : Type*} [Fintype P] [MeasurableSpace P]
    [MeasurableSingletonClass P] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [IsProbabilityMeasure μ]
    (Mv : Ω → T) (Yi : Ω → P) (Rr : Ω → Q) (Tl : Ω → R) (hY : Measurable Yi)
    (hR : Measurable Rr) :
    I[Mv : Yi | Rr ; μ] ≤ I[fun ω => ((Mv ω, Tl ω), Rr ω) : Yi ; μ] -
      I[Tl : Yi | fun ω => (Mv ω, Rr ω) ; μ] := by
  have c1 := condMutualInfo_comm μ (X := Mv) (Y := Yi) (Z := Rr)
  have f1 := cmi_pair μ (X := Yi) (Y := Mv) (Z := Rr) (V := Tl)
  have f2 := mutualInfo_pair_eq_add_condMutualInfo μ (X := Yi)
    (Y := fun ω => (Mv ω, Tl ω)) (Z := Rr)
  have f3 := mutualInfo_nonneg μ hY hR
  have f4 := mutualInfo_comm μ (X := fun ω => ((Mv ω, Tl ω), Rr ω)) (Y := Yi)
  have f5 := condMutualInfo_comm μ (X := Tl) (Y := Yi) (Z := fun ω => (Mv ω, Rr ω))
  linarith

omit [Finite Ω] [MeasurableSingletonClass Ω] in
private lemma letter_s {P Q R : Type*} [Fintype P] [MeasurableSpace P]
    [MeasurableSingletonClass P] [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (Mv : Ω → T) (Si : Ω → P) (Rr : Ω → Q) (Tl : Ω → R)
    (h0 : I[Si : fun ω => (Mv ω, Tl ω) ; μ] = 0) :
    I[Rr : Si | fun ω => (Mv ω, Tl ω) ; μ] = I[fun ω => ((Mv ω, Tl ω), Rr ω) : Si ; μ] := by
  have g1 := mutualInfo_pair_eq_add_condMutualInfo μ (X := Si) (Y := Rr)
    (Z := fun ω => (Mv ω, Tl ω))
  have g2 := mutualInfo_comp_right_of_injective μ (X := Si)
    (Y := fun ω => ((Mv ω, Tl ω), Rr ω)) (f := Prod.swap) Prod.swap_injective
  rw [show (Prod.swap ∘ fun ω => ((Mv ω, Tl ω), Rr ω)) = fun ω => (Rr ω, (Mv ω, Tl ω)) from rfl]
    at g2
  have g4 := condMutualInfo_comm μ (X := Rr) (Y := Si) (Z := fun ω => (Mv ω, Tl ω))
  have g5 := mutualInfo_comm μ (X := fun ω => ((Mv ω, Tl ω), Rr ω)) (Y := Si)
  linarith

theorem mutualInfo_le_sum_sub [IsProbabilityMeasure μ] (Mv : Ω → T) (S : Ω → Fin n → St)
    (Y : Ω → Fin n → B)
    (hind : ∀ i, I[fun ω => S ω i : fun ω => (Mv ω, seqRestrict (S ω) (Ioi i)) ; μ] = 0) :
    I[Mv : Y ; μ] ≤ ∑ i,
      (I[fun ω => ((Mv ω, seqRestrict (S ω) (Ioi i)), seqRestrict (Y ω) (Iio i)) :
          fun ω => Y ω i ; μ] -
        I[fun ω => ((Mv ω, seqRestrict (S ω) (Ioi i)), seqRestrict (Y ω) (Iio i)) :
          fun ω => S ω i ; μ]) := by
  rw [mutualInfo_eq_sum_Iio μ Mv Y]
  refine (sum_le_sum fun i _ => letter_y μ Mv (fun ω => Y ω i)
    (fun ω => seqRestrict (Y ω) (Iio i)) (fun ω => seqRestrict (S ω) (Ioi i))
    (measurable_of_finite _) (measurable_of_finite _)).trans (le_of_eq ?_)
  rw [sum_sub_distrib, sum_sub_distrib, csiszar_sum μ Y S Mv]
  congr 1
  exact sum_congr rfl fun i _ => letter_s μ Mv (fun ω => S ω i)
    (fun ω => seqRestrict (Y ω) (Iio i)) (fun ω => seqRestrict (S ω) (Ioi i)) (hind i)

end Chain

section Bound

variable {St A B : Type*} [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St]
  [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

private lemma rate_le_log_card (W : DMC (A × St) B) {m : ℕ} (q : PMF (St × Fin m × A)) :
    I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.2 ; (jointLaw W q).toMeasure] -
      I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.1.1 ;
        (jointLaw W q).toMeasure] ≤ Real.log (Fintype.card B) := by
  have h1 := mutualInfo_nonneg (jointLaw W q).toMeasure
    (X := fun b : (St × Fin m × A) × B => b.1.2.1) (Y := fun b => b.1.1)
    (measurable_of_finite _) (measurable_of_finite _)
  have h2 := mutualInfo_eq_entropy_sub_condEntropy (μ := (jointLaw W q).toMeasure)
    (fun b : (St × Fin m × A) × B => b.2) (fun b => b.1.2.1)
  have h3 := condEntropy_nonneg (jointLaw W q).toMeasure
    (X := fun b : (St × Fin m × A) × B => b.2) (Y := fun b => b.1.2.1)
    (measurable_of_finite _) (measurable_of_finite _)
  have h4 := entropy_le_log_card (jointLaw W q).toMeasure
    (X := fun b : (St × Fin m × A) × B => b.2)
  have h5 := mutualInfo_comm (jointLaw W q).toMeasure
    (X := fun b : (St × Fin m × A) × B => b.1.2.1) (Y := fun b => b.2)
  linarith

private lemma bddAbove_rates (W : DMC (A × St) B) (pS : PMF St) :
    BddAbove {v | ∃ (m : ℕ) (q : PMF (St × Fin m × A)), q.map Prod.fst = pS ∧
      v = I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.2 ; (jointLaw W q).toMeasure] -
        I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.1.1 ;
          (jointLaw W q).toMeasure]} := by
  refine ⟨Real.log (Fintype.card B), ?_⟩
  rintro v ⟨m, q, -, rfl⟩
  exact rate_le_log_card W q

theorem le_infoCapacity (W : DMC (A × St) B) (pS : PMF St) {m : ℕ} (q : PMF (St × Fin m × A))
    (hq : q.map Prod.fst = pS) :
    I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.2 ; (jointLaw W q).toMeasure] -
      I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.1.1 ;
        (jointLaw W q).toMeasure] ≤ infoCapacity W pS :=
  le_csSup (bddAbove_rates W pS) ⟨m, q, hq, rfl⟩

theorem infoCapacity_nonneg [Nonempty A] (W : DMC (A × St) B) (pS : PMF St) :
    0 ≤ infoCapacity W pS := by
  set a : A := Classical.arbitrary A
  set q : PMF (St × Fin 1 × A) := pS.map fun s => (s, 0, a)
  have hq : q.map Prod.fst = pS := by
    rw [PMF.map_comp]
    exact PMF.map_id pS
  refine le_trans (le_of_eq ?_) (le_infoCapacity W pS q hq)
  have hU : H[fun b : (St × Fin 1 × A) × B => b.1.2.1 ; (jointLaw W q).toMeasure] = 0 := by
    have h := entropy_le_log_card (jointLaw W q).toMeasure
      (X := fun b : (St × Fin 1 × A) × B => b.1.2.1)
    rw [Fintype.card_fin, Nat.cast_one, Real.log_one] at h
    exact le_antisymm h (entropy_nonneg _ _)
  have bY := mutualInfo_nonneg (jointLaw W q).toMeasure
    (X := fun b : (St × Fin 1 × A) × B => b.1.2.1) (Y := fun b => b.2)
    (measurable_of_finite _) (measurable_of_finite _)
  have bY2 := mutualInfo_eq_entropy_sub_condEntropy (μ := (jointLaw W q).toMeasure)
    (fun b : (St × Fin 1 × A) × B => b.1.2.1) (fun b => b.2)
  have bY3 := condEntropy_nonneg (jointLaw W q).toMeasure
    (X := fun b : (St × Fin 1 × A) × B => b.1.2.1) (Y := fun b => b.2)
    (measurable_of_finite _) (measurable_of_finite _)
  have bS := mutualInfo_nonneg (jointLaw W q).toMeasure
    (X := fun b : (St × Fin 1 × A) × B => b.1.2.1) (Y := fun b => b.1.1)
    (measurable_of_finite _) (measurable_of_finite _)
  have bS2 := mutualInfo_eq_entropy_sub_condEntropy (μ := (jointLaw W q).toMeasure)
    (fun b : (St × Fin 1 × A) × B => b.1.2.1) (fun b => b.1.1)
  have bS3 := condEntropy_nonneg (jointLaw W q).toMeasure
    (X := fun b : (St × Fin 1 × A) × B => b.1.2.1) (Y := fun b => b.1.1)
    (measurable_of_finite _) (measurable_of_finite _)
  linarith

theorem le_infoCapacity_of_kernel {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (W : DMC (A × St) B) (pS : PMF St) {m : ℕ} {Sv : Ω → St}
    {U : Ω → Fin m} {X : Ω → A} {Y : Ω → B} (hS : Measurable Sv) (hU : Measurable U)
    (hX : Measurable X) (hY : Measurable Y)
    (hSl : ∀ s, ν.real {ω | Sv ω = s} = (pS s).toReal)
    (hK : ∀ t y, ν.real {ω | (Sv ω, U ω, X ω) = t ∧ Y ω = y} =
      ν.real {ω | (Sv ω, U ω, X ω) = t} * (W (t.2.2, t.1) y).toReal) :
    I[U : Y ; ν] - I[U : Sv ; ν] ≤ infoCapacity W pS := by
  classical
  have := Fintype.ofFinite A
  have hG : Measurable fun ω => (Sv ω, U ω, X ω) := hS.prodMk (hU.prodMk hX)
  have hs : ∑ t : St × Fin m × A, ENNReal.ofReal (ν.real {ω | (Sv ω, U ω, X ω) = t}) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => measureReal_nonneg]
    have h := Interactive.measureReal_comp_eq_sum ν hG (measurable_const (a := ()))
      (fun _ => ()) () ()
    rw [filter_true_of_mem fun _ _ => rfl] at h
    have h' : ν.real {ω | () = () ∧ () = ()} = 1 := by simp
    rw [h'] at h
    rw [show ∑ t : St × Fin m × A, ν.real {ω | (Sv ω, U ω, X ω) = t} = 1 by
      rw [h]; refine sum_congr rfl fun t _ => ?_; congr 1; ext ω; simp]
    simp
  set q : PMF (St × Fin m × A) := PMF.ofFintype _ hs
  have hq : q.map Prod.fst = pS := by
    ext s
    rw [PMF.map_apply, tsum_fintype]
    have h := Interactive.measureReal_comp_eq_sum ν hG (measurable_const (a := ()))
      Prod.fst s ()
    have e1 : {ω | ((Sv ω, U ω, X ω)).1 = s ∧ () = ()} = {ω | Sv ω = s} := by ext; simp
    rw [e1, hSl] at h
    rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top pS s), h, ENNReal.ofReal_sum_of_nonneg
      fun _ _ => measureReal_nonneg, sum_filter]
    refine sum_congr rfl fun t _ => ?_
    by_cases ht : t.1 = s
    · simp only [ht, ite_true, q, PMF.ofFintype_apply]
      congr 2
      ext ω
      simp
    · simp [ht, Ne.symm ht]
  have hmap : ν.map (fun ω => ((Sv ω, U ω, X ω), Y ω)) = (jointLaw W q).toMeasure := by
    refine Measure.ext_of_singleton fun t => ?_
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      show jointLaw W q = DMC.jointPMF (fun a : St × Fin m × A => W (a.2.2, a.1)) q from rfl,
      DMC.jointPMF_apply, Measure.map_apply (hG.prodMk hY) (measurableSet_singleton _)]
    simp only [q, PMF.ofFintype_apply]
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν _), ← measureReal_def,
      ← ENNReal.ofReal_toReal (PMF.apply_ne_top (W (t.1.2.2, t.1.1)) t.2),
      ← ENNReal.ofReal_mul measureReal_nonneg, ← hK]
    congr 2
    ext ω
    simp [Prod.ext_iff]
  have hY' : I[U : Y ; ν] = I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.2 ;
      (jointLaw W q).toMeasure] := by
    rw [← hmap, mutualInfo_map _ (hG.prodMk hY) (measurable_of_finite _)
      (measurable_of_finite _)]
    rfl
  have hS' : I[U : Sv ; ν] = I[fun b : (St × Fin m × A) × B => b.1.2.1 : fun b => b.1.1 ;
      (jointLaw W q).toMeasure] := by
    rw [← hmap, mutualInfo_map _ (hG.prodMk hY) (measurable_of_finite _)
      (measurable_of_finite _)]
    rfl
  rw [hY', hS']
  exact le_infoCapacity W pS q hq

end Bound

section Code

open Classical in
private lemma sum_ite_off {X : Type*} [Fintype X] {n : ℕ} (f : Fin n → X → ℝ≥0∞) (i : Fin n)
    (o : ↥(({i}ᶜ : Finset (Fin n))) → X) (s : X) :
    ∑ y : Fin n → X, (if seqRestrict y {i}ᶜ = o ∧ y i = s then ∏ j, f j (y j) else 0) =
      (∏ j : ↥(({i}ᶜ : Finset (Fin n))), f j (o j)) * f i s := by
  set y₀ : Fin n → X := fun j => if h : j = i then s else o ⟨j, by simp [h]⟩
  have hy₀ : seqRestrict y₀ {i}ᶜ = o ∧ y₀ i = s := by
    refine ⟨funext fun t => ?_, by simp [y₀]⟩
    have ht : (t : Fin n) ≠ i :=
      fun h => (Finset.mem_compl.1 t.2) (Finset.mem_singleton.2 h)
    simp [seqRestrict, y₀, ht]
  rw [sum_eq_single y₀ (fun y _ hy => ?_) (by simp)]
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hy₀), ← prod_mul_prod_compl {i}, prod_singleton,
      mul_comm, ← prod_coe_sort]
    congr 1
    · refine prod_congr rfl fun t _ => ?_
      have ht : (t : Fin n) ≠ i :=
        fun h => (Finset.mem_compl.1 t.2) (Finset.mem_singleton.2 h)
      simp [y₀, ht]
    · simp [y₀]
  · refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
    rintro ⟨h1, h2⟩
    apply hy
    funext j
    by_cases hj : j = i
    · subst hj
      simp [y₀, h2]
    · have := congrFun h1 ⟨j, by simp [hj]⟩
      simp only [seqRestrict] at this
      simp [y₀, hj, this]

open Classical in
private lemma sum_ite_off' {X : Type*} [Fintype X] {n : ℕ} (f : Fin n → PMF X) (i : Fin n)
    (o : ↥(({i}ᶜ : Finset (Fin n))) → X) :
    ∑ y : Fin n → X, (if seqRestrict y {i}ᶜ = o then ∏ j, f j (y j) else 0) =
      ∏ j : ↥(({i}ᶜ : Finset (Fin n))), f j (o j) := by
  have e : ∀ y : Fin n → X, (if seqRestrict y {i}ᶜ = o then ∏ j, f j (y j) else 0) =
      ∑ s, (if seqRestrict y {i}ᶜ = o ∧ y i = s then ∏ j, f j (y j) else 0) := by
    intro y
    rw [sum_eq_single (y i) (fun s _ hs => by simp [Ne.symm hs]) (by simp)]
    simp
  rw [sum_congr rfl fun y _ => e y, sum_comm,
    sum_congr rfl fun s _ => sum_ite_off (fun j => f j) i o s, ← mul_sum, sum_pmf_eq_one,
    mul_one]

private lemma sum_prod_pmf {X : Type*} [Fintype X] {n : ℕ} (f : Fin n → PMF X) :
    ∑ y : Fin n → X, ∏ i, f i (y i) = 1 := by
  rw [← Fintype.prod_sum]
  exact prod_eq_one fun i _ => sum_pmf_eq_one _

variable {M St A B : Type*} {n : ℕ} [Fintype M] [Nonempty M] [MeasurableSpace M]
  [MeasurableSingletonClass M] [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

private noncomputable def mass (c : StateCode M St A B n) (W : DMC (A × St) B) (pS : PMF St)
    (ω : M × (Fin n → St) × (Fin n → B)) : ℝ≥0∞ :=
  (Fintype.card M : ℝ≥0∞)⁻¹ *
    ((∏ i, pS (ω.2.1 i)) * ∏ i, W (c.enc ω.1 ω.2.1 i, ω.2.1 i) (ω.2.2 i))

omit [MeasurableSpace M] [MeasurableSingletonClass M] [MeasurableSpace St]
  [MeasurableSingletonClass St] [MeasurableSpace B] [MeasurableSingletonClass B] in
private lemma sum_mass (c : StateCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) :
    ∑ ω, mass c W pS ω = 1 := by
  simp only [mass, Fintype.sum_prod_type, ← mul_sum]
  have h : ∀ (m : M) (s : Fin n → St),
      ∑ y : Fin n → B, ∏ i, W (c.enc m s i, s i) (y i) = 1 :=
    fun m s => sum_prod_pmf fun i => W (c.enc m s i, s i)
  simp only [h, mul_one, sum_prod_pmf fun _ => pS]
  rw [mul_sum]
  simpa using sum_inv_card M

omit [MeasurableSingletonClass M] [MeasurableSingletonClass St] [MeasurableSingletonClass B] in
private noncomputable def codeMeasure (c : StateCode M St A B n) (W : DMC (A × St) B)
    (pS : PMF St) : Measure (M × (Fin n → St) × (Fin n → B)) :=
  (PMF.ofFintype _ (sum_mass c W pS)).toMeasure

omit [MeasurableSingletonClass M] [MeasurableSingletonClass St] [MeasurableSingletonClass B] in
private instance (c : StateCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) :
    IsProbabilityMeasure (codeMeasure c W pS) := by
  unfold codeMeasure
  infer_instance

private lemma codeMeasure_apply (c : StateCode M St A B n) (W : DMC (A × St) B) (pS : PMF St)
    (s : Set (M × (Fin n → St) × (Fin n → B))) :
    codeMeasure c W pS s = ∑ ω, s.indicator (mass c W pS) ω := by
  rw [codeMeasure, PMF.toMeasure_apply_fintype]
  rfl

private lemma codeMeasure_fix (c : StateCode M St A B n) (W : DMC (A × St) B)
    (pS : PMF St) (m : M) (s : Fin n → St) (P : (Fin n → B) → Prop) [DecidablePred P] :
    codeMeasure c W pS {ω | ω.1 = m ∧ ω.2.1 = s ∧ P ω.2.2} =
      (Fintype.card M : ℝ≥0∞)⁻¹ * ((∏ i, pS (s i)) *
        ∑ y, if P y then ∏ i, W (c.enc m s i, s i) (y i) else 0) := by
  classical
  rw [codeMeasure_apply, Fintype.sum_prod_type, sum_eq_single m (fun m' _ hm => ?_) (by simp)]
  · rw [Fintype.sum_prod_type, sum_eq_single s (fun s' _ hs => ?_) (by simp), mul_sum, mul_sum]
    · refine sum_congr rfl fun y _ => ?_
      by_cases h : P y <;> simp [Set.indicator, h, mass]
    · refine sum_eq_zero fun y _ => ?_
      simp [Set.indicator, hs]
  · refine sum_eq_zero fun x _ => ?_
    simp [Set.indicator, hm]

private lemma codeMeasure_fix_m (c : StateCode M St A B n) (W : DMC (A × St) B)
    (pS : PMF St) (m : M) (P : (Fin n → St) → Prop) [DecidablePred P] :
    codeMeasure c W pS {ω | ω.1 = m ∧ P ω.2.1} =
      (Fintype.card M : ℝ≥0∞)⁻¹ * ∑ s, if P s then ∏ i, pS (s i) else 0 := by
  classical
  rw [codeMeasure_apply, Fintype.sum_prod_type, sum_eq_single m (fun m' _ hm => ?_) (by simp)]
  · rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun s _ => ?_
    by_cases h : P s
    · simp only [Set.indicator, Set.mem_ofPred_eq, h, and_self, ite_true, mass, ← mul_sum,
        sum_prod_pmf fun i => W (c.enc m s i, s i), mul_one]
    · simp [Set.indicator, h]
  · refine sum_eq_zero fun x _ => ?_
    simp [Set.indicator, hm]

private lemma kernel_y (c : StateCode M St A B n) (W : DMC (A × St) B)
    (pS : PMF St) (i : Fin n) (h : M × (Fin n → St) × (↥(({i}ᶜ : Finset (Fin n))) → B))
    (b : B) :
    (codeMeasure c W pS).real {ω | (ω.1, ω.2.1, seqRestrict ω.2.2 {i}ᶜ) = h ∧ ω.2.2 i = b} =
      (codeMeasure c W pS).real {ω | (ω.1, ω.2.1, seqRestrict ω.2.2 {i}ᶜ) = h} *
        (W (c.enc h.1 h.2.1 i, h.2.1 i) b).toReal := by
  classical
  obtain ⟨m, s, o⟩ := h
  have e1 : {ω : M × (Fin n → St) × (Fin n → B) |
      (ω.1, ω.2.1, seqRestrict ω.2.2 {i}ᶜ) = (m, s, o) ∧ ω.2.2 i = b} =
      {ω | ω.1 = m ∧ ω.2.1 = s ∧ (seqRestrict ω.2.2 {i}ᶜ = o ∧ ω.2.2 i = b)} := by
    ext ω
    simp [Prod.ext_iff, and_assoc]
  have e2 : {ω : M × (Fin n → St) × (Fin n → B) |
      (ω.1, ω.2.1, seqRestrict ω.2.2 {i}ᶜ) = (m, s, o)} =
      {ω | ω.1 = m ∧ ω.2.1 = s ∧ seqRestrict ω.2.2 {i}ᶜ = o} := by
    ext ω
    simp [Prod.ext_iff]
  have h1 := codeMeasure_fix c W pS m s fun y => seqRestrict y {i}ᶜ = o ∧ y i = b
  have h2 := codeMeasure_fix c W pS m s fun y => seqRestrict y {i}ᶜ = o
  rw [e1, e2, measureReal_def, measureReal_def, h1, h2,
    sum_ite_off (fun j => W (c.enc m s j, s j)) i o b,
    sum_ite_off' (fun j => W (c.enc m s j, s j)) i o, ← ENNReal.toReal_mul]
  congr 1
  ring

private lemma kernel_s (c : StateCode M St A B n) (W : DMC (A × St) B)
    (pS : PMF St) (i : Fin n) (g : M × (↥(({i}ᶜ : Finset (Fin n))) → St)) (a : St) :
    (codeMeasure c W pS).real {ω | (ω.1, seqRestrict ω.2.1 {i}ᶜ) = g ∧ ω.2.1 i = a} =
      (codeMeasure c W pS).real {ω | (ω.1, seqRestrict ω.2.1 {i}ᶜ) = g} * (pS a).toReal := by
  classical
  obtain ⟨m, o⟩ := g
  have e1 : {ω : M × (Fin n → St) × (Fin n → B) |
      (ω.1, seqRestrict ω.2.1 {i}ᶜ) = (m, o) ∧ ω.2.1 i = a} =
      {ω | ω.1 = m ∧ (seqRestrict ω.2.1 {i}ᶜ = o ∧ ω.2.1 i = a)} := by
    ext ω
    simp [Prod.ext_iff, and_assoc]
  have e2 : {ω : M × (Fin n → St) × (Fin n → B) | (ω.1, seqRestrict ω.2.1 {i}ᶜ) = (m, o)} =
      {ω | ω.1 = m ∧ seqRestrict ω.2.1 {i}ᶜ = o} := by
    ext ω
    simp [Prod.ext_iff]
  have h1 := codeMeasure_fix_m c W pS m fun s => seqRestrict s {i}ᶜ = o ∧ s i = a
  have h2 := codeMeasure_fix_m c W pS m fun s => seqRestrict s {i}ᶜ = o
  rw [e1, e2, measureReal_def, measureReal_def, h1, h2,
    sum_ite_off (fun _ => pS) i o a, sum_ite_off' (fun _ => pS) i o, ← ENNReal.toReal_mul]
  congr 1
  ring

omit [Fintype M] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M] [Fintype St]
  [MeasurableSpace St] [MeasurableSingletonClass St] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private lemma sum_real_eq_one {Ω T : Type*} [MeasurableSpace Ω] [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (μ : Measure Ω) [IsProbabilityMeasure μ] {G : Ω → T}
    (hG : Measurable G) : ∑ g, μ.real {ω | G ω = g} = 1 := by
  classical
  have h := Interactive.measureReal_comp_eq_sum μ hG (measurable_const (a := ()))
    (fun _ => ()) () ()
  rw [filter_true_of_mem fun _ _ => rfl] at h
  have h' : μ.real {ω | () = () ∧ () = ()} = 1 := by simp
  rw [h'] at h
  rw [h]
  refine sum_congr rfl fun g _ => ?_
  congr 1
  ext ω
  simp

omit [Fintype M] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M] [Fintype St]
  [MeasurableSpace St] [MeasurableSingletonClass St] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private lemma real_eq_of_kernel {Ω T X : Type*} [MeasurableSpace Ω] [Finite T]
    [MeasurableSpace T] [MeasurableSingletonClass T] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure Ω) [IsProbabilityMeasure μ] {G : Ω → T}
    {Z : Ω → X} (hG : Measurable G) (hZ : Measurable Z) (K : PMF X)
    (hK : ∀ g s, μ.real {ω | G ω = g ∧ Z ω = s} = μ.real {ω | G ω = g} * (K s).toReal)
    (s : X) : μ.real {ω | Z ω = s} = (K s).toReal := by
  classical
  have := Fintype.ofFinite T
  have h := Interactive.measureReal_comp_eq_sum μ hG hZ (fun _ => ()) () s
  rw [filter_true_of_mem fun _ _ => rfl] at h
  have e : {ω | () = () ∧ Z ω = s} = {ω | Z ω = s} := by ext; simp
  rw [e] at h
  rw [h, sum_congr rfl fun g _ => hK g s, ← sum_mul, sum_real_eq_one μ hG, one_mul]

omit [Fintype M] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M] [Fintype St]
  [MeasurableSpace St] [MeasurableSingletonClass St] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private lemma mutualInfo_eq_zero_of_kernel {Ω T X : Type*} [MeasurableSpace Ω] [Fintype T]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure Ω) [IsProbabilityMeasure μ] {G : Ω → T}
    {Z : Ω → X} (hG : Measurable G) (hZ : Measurable Z) (K : PMF X)
    (hK : ∀ g s, μ.real {ω | G ω = g ∧ Z ω = s} = μ.real {ω | G ω = g} * (K s).toReal) :
    I[Z : G ; μ] = 0 := by
  refine mutualInfo_eq_zero_of_measureReal_eq_mul μ fun s g => ?_
  rw [map_measureReal_apply (hZ.prodMk hG) (measurableSet_singleton _),
    map_measureReal_apply hZ (measurableSet_singleton _),
    map_measureReal_apply hG (measurableSet_singleton _)]
  have e1 : (fun ω => (Z ω, G ω)) ⁻¹' {(s, g)} = {ω | G ω = g ∧ Z ω = s} := by
    ext ω
    simp [and_comm]
  have e2 : Z ⁻¹' {s} = {ω | Z ω = s} := rfl
  have e3 : G ⁻¹' {g} = {ω | G ω = g} := rfl
  rw [e1, e2, e3, hK, real_eq_of_kernel μ hG hZ K hK]
  ring

omit [Fintype M] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M] [Fintype St]
  [MeasurableSpace St] [MeasurableSingletonClass St] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] in
private lemma kernel_comp {Ω T T' X : Type*} [MeasurableSpace Ω] [Finite T] [MeasurableSpace T]
    [MeasurableSingletonClass T] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {H : Ω → T} {Sv : Ω → X}
    (hH : Measurable H) (hS : Measurable Sv) (F : T → T') (K : T' → PMF X)
    (hK : ∀ h s, μ.real {ω | H ω = h ∧ Sv ω = s} = μ.real {ω | H ω = h} * (K (F h) s).toReal)
    (t : T') (s : X) :
    μ.real {ω | F (H ω) = t ∧ Sv ω = s} = μ.real {ω | F (H ω) = t} * (K t s).toReal := by
  classical
  have := Fintype.ofFinite T
  rw [Interactive.measureReal_comp_eq_sum μ hH hS F t s]
  have h2 := Interactive.measureReal_comp_eq_sum μ hH (measurable_const (a := ())) F t ()
  simp only [and_true] at h2
  rw [h2, sum_mul]
  refine sum_congr rfl fun h hh => ?_
  rw [hK, (mem_filter.1 hh).2]

private lemma entropy_fst (c : StateCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) :
    H[fun ω : M × (Fin n → St) × (Fin n → B) => ω.1 ; codeMeasure c W pS] =
      Real.log (Fintype.card M) := by
  classical
  refine entropy_eq_log_card _ fun m => ?_
  rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have e : (fun ω : M × (Fin n → St) × (Fin n → B) => ω.1) ⁻¹' {m} =
      {ω | ω.1 = m ∧ (fun _ : Fin n → St => True) ω.2.1} := by
    ext ω
    simp
  have h := codeMeasure_fix_m c W pS m fun _ => True
  rw [e, measureReal_def, h]
  simp only [ite_true, sum_prod_pmf fun _ => pS, mul_one, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

private lemma measureReal_dec_ne [DecidableEq M] (c : StateCode M St A B n) (W : DMC (A × St) B)
    (pS : PMF St) :
    (codeMeasure c W pS).real {ω | c.dec ω.2.2 ≠ ω.1} = (c.avgError W pS).toReal := by
  rw [measureReal_def, codeMeasure_apply, StateCode.avgError, div_eq_mul_inv, mul_comm, mul_sum,
    Fintype.sum_prod_type]
  refine congrArg ENNReal.toReal (sum_congr rfl fun m _ => ?_)
  rw [mul_sum, Fintype.sum_prod_type]
  refine sum_congr rfl fun s _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : c.dec y = m <;> simp [Set.indicator, h, mass]

private lemma indep (c : StateCode M St A B n) (W : DMC (A × St) B) (pS : PMF St)
    (i : Fin n) :
    I[fun ω : M × (Fin n → St) × (Fin n → B) => ω.2.1 i :
      fun ω => (ω.1, seqRestrict ω.2.1 (Ioi i)) ; codeMeasure c W pS] = 0 := by
  have h0 := mutualInfo_eq_zero_of_kernel (codeMeasure c W pS)
    (G := fun ω : M × (Fin n → St) × (Fin n → B) => (ω.1, seqRestrict ω.2.1 {i}ᶜ))
    (Z := fun ω => ω.2.1 i) (measurable_of_finite _) (measurable_of_finite _) pS
    (kernel_s c W pS i)
  have h1 := mutualInfo_comp_le (codeMeasure c W pS)
    (X := fun ω : M × (Fin n → St) × (Fin n → B) => ω.2.1 i)
    (Y := fun ω => (ω.1, seqRestrict ω.2.1 {i}ᶜ)) (measurable_of_finite _)
    (measurable_of_finite _) (fun g => (g.1, fun j : ↥(Ioi i) =>
      g.2 ⟨j.1, by simpa using ne_of_gt (mem_Ioi.1 j.2)⟩))
  have h2 := mutualInfo_nonneg (codeMeasure c W pS)
    (X := fun ω : M × (Fin n → St) × (Fin n → B) => ω.2.1 i)
    (Y := fun ω => (ω.1, seqRestrict ω.2.1 (Ioi i))) (measurable_of_finite _)
    (measurable_of_finite _)
  exact le_antisymm (h1.trans_eq h0) h2

private lemma letter_le [Finite A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (c : StateCode M St A B n) (W : DMC (A × St) B) (pS : PMF St)
    (i : Fin n) :
    I[fun ω : M × (Fin n → St) × (Fin n → B) =>
        ((ω.1, seqRestrict ω.2.1 (Ioi i)), seqRestrict ω.2.2 (Iio i)) :
        fun ω => ω.2.2 i ; codeMeasure c W pS] -
      I[fun ω : M × (Fin n → St) × (Fin n → B) =>
        ((ω.1, seqRestrict ω.2.1 (Ioi i)), seqRestrict ω.2.2 (Iio i)) :
        fun ω => ω.2.1 i ; codeMeasure c W pS] ≤ infoCapacity W pS := by
  classical
  set ν := codeMeasure c W pS
  set e := Fintype.equivFin ((M × (↥(Ioi i) → St)) × (↥(Iio i) → B))
  set Gf : (↥(({i}ᶜ : Finset (Fin n))) → B) → (↥(Iio i) → B) :=
    fun o j => o ⟨j.1, by simpa using ne_of_lt (mem_Iio.1 j.2)⟩
  set F : M × (Fin n → St) × (↥(({i}ᶜ : Finset (Fin n))) → B) →
      St × Fin (Fintype.card ((M × (↥(Ioi i) → St)) × (↥(Iio i) → B))) × A :=
    fun h => (h.2.1 i, e ((h.1, seqRestrict h.2.1 (Ioi i)), Gf h.2.2), c.enc h.1 h.2.1 i)
  have hK := kernel_comp ν
    (H := fun ω : M × (Fin n → St) × (Fin n → B) => (ω.1, ω.2.1, seqRestrict ω.2.2 {i}ᶜ))
    (Sv := fun ω => ω.2.2 i) (measurable_of_finite _) (measurable_of_finite _) F
    (fun t => W (t.2.2, t.1)) fun h b => kernel_y c W pS i h b
  have hS := real_eq_of_kernel ν
    (G := fun ω : M × (Fin n → St) × (Fin n → B) => (ω.1, seqRestrict ω.2.1 {i}ᶜ))
    (Z := fun ω => ω.2.1 i) (measurable_of_finite _) (measurable_of_finite _) pS
    (kernel_s c W pS i)
  have key := le_infoCapacity_of_kernel ν W pS
    (Sv := fun ω : M × (Fin n → St) × (Fin n → B) => ω.2.1 i)
    (U := fun ω => e ((ω.1, seqRestrict ω.2.1 (Ioi i)), seqRestrict ω.2.2 (Iio i)))
    (X := fun ω => c.enc ω.1 ω.2.1 i) (Y := fun ω => ω.2.2 i) (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _) hS
    fun t y => hK t y
  have iY : I[fun ω => e ((ω.1, seqRestrict ω.2.1 (Ioi i)), seqRestrict ω.2.2 (Iio i)) :
      fun ω => ω.2.2 i ; ν] = I[fun ω : M × (Fin n → St) × (Fin n → B) =>
        ((ω.1, seqRestrict ω.2.1 (Ioi i)), seqRestrict ω.2.2 (Iio i)) : fun ω => ω.2.2 i ; ν] := by
    rw [mutualInfo_comm]
    conv_rhs => rw [mutualInfo_comm]
    exact mutualInfo_comp_right_of_injective ν e.injective
  have iS : I[fun ω => e ((ω.1, seqRestrict ω.2.1 (Ioi i)), seqRestrict ω.2.2 (Iio i)) :
      fun ω => ω.2.1 i ; ν] = I[fun ω : M × (Fin n → St) × (Fin n → B) =>
        ((ω.1, seqRestrict ω.2.1 (Ioi i)), seqRestrict ω.2.2 (Iio i)) : fun ω => ω.2.1 i ; ν] := by
    rw [mutualInfo_comm]
    conv_rhs => rw [mutualInfo_comm]
    exact mutualInfo_comp_right_of_injective ν e.injective
  rw [iY, iS] at key
  exact key

private lemma one_sub_mul_log_card_le [DecidableEq M] [Finite A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (c : StateCode M St A B n) (W : DMC (A × St) B) (pS : PMF St) :
    (1 - (c.avgError W pS).toReal) * Real.log (Fintype.card M) ≤
      n * infoCapacity W pS + Real.log 2 := by
  set ν := codeMeasure c W pS
  have hH := entropy_fst c W pS
  have hI := mutualInfo_eq_entropy_sub_condEntropy (μ := ν)
    (fun ω : M × (Fin n → St) × (Fin n → B) => ω.1) (fun ω => ω.2.2)
  have hF := condEntropy_le_log_two_add_mul_log_card (μ := ν)
    (X := fun ω : M × (Fin n → St) × (Fin n → B) => ω.1) (Y := fun ω => ω.2.2)
    (measurable_of_finite _) (measurable_of_finite _) c.dec
  rw [measureReal_dec_ne] at hF
  have hC := mutualInfo_le_sum_sub ν (fun ω : M × (Fin n → St) × (Fin n → B) => ω.1)
    (fun ω => ω.2.1) (fun ω => ω.2.2) (indep c W pS)
  have hS := sum_le_sum fun i (_ : i ∈ univ) => letter_le c W pS i
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hS
  have hexp : (1 - (c.avgError W pS).toReal) * Real.log (Fintype.card M) =
      Real.log (Fintype.card M) - (c.avgError W pS).toReal * Real.log (Fintype.card M) := by
    ring
  linarith

end Code

section Main

variable {St A B : Type*} [Fintype St] [MeasurableSpace St] [MeasurableSingletonClass St]
  [Finite A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem le_infoCapacity_of_achievable (W : DMC (A × St) B) (pS : PMF St) {R : ℝ}
    (h : Achievable W pS R) : R ≤ infoCapacity W pS := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hC := infoCapacity_nonneg W pS
  set C := infoCapacity W pS
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
  have hk0 : (0 : ℝ) < k := (Real.exp_pos _).trans_le hk
  have : Nonempty (Fin k) := ⟨⟨0, by exact_mod_cast hk0⟩⟩
  have key := one_sub_mul_log_card_le c W pS
  rw [Fintype.card_fin] at key
  have hPe : (c.avgError W pS).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1 : (1 - e) * Real.log k ≤ n * C + Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)).trans key
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

end Main

end GelfandPinsker

end Meat
