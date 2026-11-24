import Meat.Network.Linear
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Meat

namespace Network

namespace RLNC

open Finset Module Submodule

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}

abbrev Idx (N : Network V) (h : ℕ) := Σ e : Edge N, Fin h ⊕ Σ w : V, Fin (N.cap w e.1.1)

section Global

variable {R : Type*} [CommRing R] (s : V) {h : ℕ}

def src (β : Idx N h → R) (e : Edge N) : Fin h → R :=
  if e.1.1 = s then fun k => β ⟨e, Sum.inl k⟩ else 0

def gIter (β : Idx N h → R) : ℕ → Edge N → Fin h → R
  | 0 => fun _ => 0
  | k + 1 => fun e => src s β e +
      ∑ w, ∑ j : Fin (N.cap w e.1.1), β ⟨e, Sum.inr ⟨w, j⟩⟩ • gIter β k ⟨(w, e.1.1), j⟩

theorem gIter_succ (β : Idx N h → R) (k : ℕ) (e : Edge N) :
    gIter s β (k + 1) e = src s β e +
      ∑ w, ∑ j : Fin (N.cap w e.1.1), β ⟨e, Sum.inr ⟨w, j⟩⟩ • gIter s β k ⟨(w, e.1.1), j⟩ :=
  rfl

noncomputable def pot (hN : N.IsAcyclic) (u : V) : ℕ :=
  (univ.filter fun w => hN.choose w < hN.choose u).card

omit [DecidableEq V] in
theorem pot_lt_card (hN : N.IsAcyclic) (u : V) : pot hN u < Fintype.card V := by
  rw [pot, ← card_univ]
  exact card_lt_card (filter_ssubset.2 ⟨u, mem_univ _, lt_irrefl _⟩)

omit [DecidableEq V] in
theorem pot_lt (hN : N.IsAcyclic) {w u : V} (h : 0 < N.cap w u) : pot hN w < pot hN u := by
  have hr := hN.choose_spec w u h
  refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact hx.trans hr
  · have := hsub (show w ∈ univ.filter fun x => hN.choose x < hN.choose u by simpa using hr)
    simp at this

theorem gIter_succ_eq (hN : N.IsAcyclic) (β : Idx N h → R) :
    ∀ k (e : Edge N), pot hN e.1.1 < k → gIter s β (k + 1) e = gIter s β k e := by
  intro k
  induction k with
  | zero => intro e he; omega
  | succ k ih =>
    intro e he
    rw [gIter_succ s β (k + 1) e, gIter_succ s β k e]
    congr 1
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ih ⟨(w, e.1.1), j⟩ (by
      have := pot_lt hN (Fin.pos j)
      simp only at this ⊢
      omega)]

theorem gIter_eq_of_le (hN : N.IsAcyclic) (β : Idx N h → R) (e : Edge N) :
    ∀ k, pot hN e.1.1 < k → ∀ m, k ≤ m → gIter s β m e = gIter s β k e := by
  intro k hk m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [gIter_succ_eq s hN β m e (by omega), ih]

noncomputable def glob (β : Idx N h → R) (e : Edge N) : Fin h → R :=
  gIter s β (Fintype.card V) e

theorem glob_eq (hN : N.IsAcyclic) (β : Idx N h → R) (e : Edge N) :
    glob s β e = src s β e +
      ∑ w, ∑ j : Fin (N.cap w e.1.1), β ⟨e, Sum.inr ⟨w, j⟩⟩ • glob s β ⟨(w, e.1.1), j⟩ := by
  rw [glob, ← gIter_succ_eq s hN β _ e (pot_lt_card hN _)]
  rfl

theorem glob_unique (hN : N.IsAcyclic) (β : Idx N h → R) (g : Edge N → Fin h → R)
    (hg : ∀ e, g e = src s β e +
      ∑ w, ∑ j : Fin (N.cap w e.1.1), β ⟨e, Sum.inr ⟨w, j⟩⟩ • g ⟨(w, e.1.1), j⟩) :
    glob s β = g := by
  have key : ∀ k (e : Edge N), pot hN e.1.1 < k → gIter s β k e = g e := by
    intro k
    induction k with
    | zero => intro e he; omega
    | succ k ih =>
      intro e he
      rw [hg e, gIter_succ s β k e]
      congr 1
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => ?_
      rw [ih ⟨(w, e.1.1), j⟩ (by
        have := pot_lt hN (Fin.pos j)
        simp only at this ⊢
        omega)]
  funext e
  exact key _ e (pot_lt_card hN _)

theorem gIter_map {R' : Type*} [CommRing R'] (f : R →+* R') (β : Idx N h → R) :
    ∀ k e, gIter s (fun x => f (β x)) k e = fun j => f (gIter s β k e j) := by
  intro k
  induction k with
  | zero => intro e; funext j; simp [gIter]
  | succ k ih =>
    intro e
    funext j
    rw [gIter_succ, gIter_succ]
    simp only [src, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ih,
      map_add, map_sum, map_mul]
    split_ifs <;> simp

theorem glob_map {R' : Type*} [CommRing R'] (f : R →+* R') (β : Idx N h → R) (e : Edge N) :
    glob s (fun x => f (β x)) e = fun j => f (glob s β e j) :=
  gIter_map s f β _ e

end Global

section Exists

variable {K : Type*} [Field K] {h : ℕ}

def coordMap : Dual K (Fin h → K) →ₗ[K] Fin h → K where
  toFun φ k := φ (Pi.single k 1)
  map_add' φ ψ := by funext k; simp
  map_smul' c φ := by funext k; simp

theorem coordMap_injective : Function.Injective (coordMap (K := K) (h := h)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  ext x
  have := congrFun hφ x
  simpa [coordMap] using this

theorem coordMap_surjective : Function.Surjective (coordMap (K := K) (h := h)) := by
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact coordMap_injective
  · rw [Subspace.dual_finrank_eq]

theorem exists_spanning_coeffs (hN : N.IsAcyclic) {s : V} {T : Finset V} (hs : s ∉ T)
    (hT : ∀ t ∈ T, h ≤ N.minCut s t) [Fintype K]
    (hK : 2 ^ (Fintype.card V + ∑ u, ∑ v, N.cap u v) ≤ Fintype.card K) :
    ∃ β₀ : Idx N h → K, ∀ t ∈ T,
      span K (Set.range fun x : Σ w, Fin (N.cap w t) => glob s β₀ ⟨(x.1, t), x.2⟩) = ⊤ := by
  classical
  obtain ⟨g, hL, hD⟩ := exists_linear_family hN hs hT hK
  have ha : ∀ e : Edge N, e.1.1 ≠ s → ∃ a : (Σ w, Fin (N.cap w e.1.1)) → K,
      ∑ x, a x • inFam g e.1.1 x = g e := fun e he => by
    have := hL e.1.1 he e.1.2 e.2
    rwa [mem_span_range_iff_exists_fun] at this
  choose! a ha using ha
  set c : Edge N → Fin h → K := fun e => coordMap (g e)
  let β₀ : Idx N h → K := fun x => match x with
    | ⟨e, Sum.inl k⟩ => if e.1.1 = s then c e k else 0
    | ⟨e, Sum.inr y⟩ => if e.1.1 = s then 0 else a e y
  have hfix : ∀ e, c e = src s β₀ e +
      ∑ w, ∑ j : Fin (N.cap w e.1.1), β₀ ⟨e, Sum.inr ⟨w, j⟩⟩ • c ⟨(w, e.1.1), j⟩ := by
    intro e
    by_cases he : e.1.1 = s
    · simp [src, he, β₀]
    · have h1 : src s β₀ e = 0 := by simp [src, he]
      rw [h1, zero_add]
      simp only [β₀, he, ite_false]
      rw [← Fintype.sum_sigma (fun x : Σ w, Fin (N.cap w e.1.1) =>
        a e x • c ⟨(x.1, e.1.1), x.2⟩)]
      simp only [c]
      rw [← ha e he, map_sum]
      simp only [map_smul]
      rfl
  have hglob := glob_unique s hN β₀ c hfix
  refine ⟨β₀, fun t ht => ?_⟩
  rw [hglob]
  have : (Set.range fun x : Σ w, Fin (N.cap w t) => c ⟨(x.1, t), x.2⟩) =
      coordMap '' Set.range (inFam g t) := by
    rw [← Set.range_comp]
    rfl
  rw [this, Submodule.span_image, hD t ht, Submodule.map_top, LinearMap.range_eq_top]
  exact coordMap_surjective

end Exists

section Det

variable {L : Type*} [Field L] {h : ℕ}

theorem exists_det_ne_zero {ι : Type*} [Finite ι] (v : ι → Fin h → L)
    (hv : span L (Set.range v) = ⊤) :
    ∃ σ : Fin h → ι, (Matrix.of fun i j => v (σ i) j).det ≠ 0 := by
  classical
  obtain ⟨S, hS, hspan, hli⟩ := exists_linearIndependent L (Set.range v)
  have : Fintype S := ((Set.finite_range v).subset hS).fintype
  have hcard : Fintype.card S = h := by
    have h1 := finrank_span_eq_card hli
    rw [Subtype.range_coe, hspan, hv, finrank_top, Module.finrank_fin_fun] at h1
    exact h1.symm
  let e : Fin h ≃ S := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ i, ∃ x, v x = (e i : Fin h → L) := fun i => hS (e i).2
  choose σ hσ using hpre
  refine ⟨σ, fun h0 => ?_⟩
  have hrow : LinearIndependent L (Matrix.of fun i j => v (σ i) j).row := by
    have : (Matrix.of fun i j => v (σ i) j).row = fun i => (e i : Fin h → L) := by
      funext i j
      simp [Matrix.row, hσ]
    rw [this]
    exact hli.comp e e.injective
  have hu := (Matrix.linearIndependent_row_iff_isUnit.1 hrow)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero h0

theorem span_eq_top_of_det_ne_zero {ι : Type*} (v : ι → Fin h → L) (σ : Fin h → ι)
    (hd : (Matrix.of fun i j => v (σ i) j).det ≠ 0) : span L (Set.range v) = ⊤ := by
  have hu : IsUnit (Matrix.of fun i j => v (σ i) j) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)
  have hli := Matrix.linearIndependent_row_iff_isUnit.2 hu
  have htop := hli.span_eq_top_of_card_eq_finrank' (by simp)
  refine eq_top_iff.2 (htop.symm.le.trans (span_mono ?_))
  rintro _ ⟨i, rfl⟩
  exact ⟨σ i, by funext j; simp [Matrix.row]⟩

end Det

section Poly

variable {F : Type*} [Field F] (s : V) {h : ℕ}

open MvPolynomial

theorem totalDegree_gIter :
    ∀ k (e : Edge N) (j : Fin h),
      (gIter s (X : Idx N h → MvPolynomial (Idx N h) F) k e j).totalDegree ≤ k := by
  intro k
  induction k with
  | zero => intro e j; simp [gIter]
  | succ k ih =>
    intro e j
    rw [gIter_succ]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp only [src]
      split_ifs
      · exact (totalDegree_X _).le.trans (by omega)
      · simp
    · refine totalDegree_finsetSum_le fun w _ => totalDegree_finsetSum_le fun j' _ => ?_
      refine (totalDegree_mul _ _).trans ?_
      have := (totalDegree_X (R := F) (⟨e, Sum.inr ⟨w, j'⟩⟩ : Idx N h)).le
      have := ih ⟨(w, e.1.1), j'⟩ j
      omega

noncomputable def detPoly (t : V) (σ : Fin h → Σ w, Fin (N.cap w t)) :
    MvPolynomial (Idx N h) F :=
  (Matrix.of fun i j => glob s (X : Idx N h → MvPolynomial (Idx N h) F)
    ⟨((σ i).1, t), (σ i).2⟩ j).det

theorem totalDegree_detPoly (t : V) (σ : Fin h → Σ w, Fin (N.cap w t)) :
    (detPoly (F := F) s t σ).totalDegree ≤ h * Fintype.card V := by
  rw [detPoly, Matrix.det_apply]
  refine totalDegree_finsetSum_le fun π _ => ?_
  rw [Units.smul_def]
  refine (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (Matrix.of (fun i j => glob s (X : Idx N h → MvPolynomial (Idx N h) F)
        ⟨((σ i).1, t), (σ i).2⟩ j) (π i) i).totalDegree ≤ ∑ _i : Fin h, Fintype.card V :=
        Finset.sum_le_sum fun i _ => totalDegree_gIter s _ _ _
    _ = h * Fintype.card V := by simp

theorem eval_detPoly {L : Type*} [Field L] [Algebra F L] (β : Idx N h → L) (t : V)
    (σ : Fin h → Σ w, Fin (N.cap w t)) :
    aeval β (detPoly (F := F) s t σ) =
      (Matrix.of fun i j => glob s β ⟨((σ i).1, t), (σ i).2⟩ j).det := by
  rw [detPoly, ← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  have := congrFun (glob_map s (aeval β).toRingHom (X : Idx N h → MvPolynomial (Idx N h) F)
    ⟨((σ i).1, t), (σ i).2⟩) j
  have hb : (fun x => (aeval β).toRingHom (X x : MvPolynomial (Idx N h) F)) = β :=
    funext fun x => by simp
  rw [hb] at this
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply]
  exact this.symm

end Poly

section Random

open MvPolynomial

variable {F : Type*} [Field F] [Fintype F] {h : ℕ}

theorem card_fail_le (hN : N.IsAcyclic) {s : V} {T : Finset V} (hs : s ∉ T)
    (hT : ∀ t ∈ T, h ≤ N.minCut s t) :
    ((univ.filter fun β : Idx N h → F => ¬∀ t ∈ T,
        span F (Set.range fun x : Σ w, Fin (N.cap w t) => glob s β ⟨(x.1, t), x.2⟩) = ⊤).card :
        ℚ≥0) / (Fintype.card F ^ Fintype.card (Idx N h) : ℚ≥0) ≤
      ((T.card * (h * Fintype.card V) : ℕ) : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  set B := Fintype.card V + ∑ u, ∑ v, N.cap u v
  let K := FiniteField.Extension F p (B + 1)
  have : Fintype K := Fintype.ofFinite K
  have hK : 2 ^ B ≤ Fintype.card K := by
    have h1 : Fintype.card K = Fintype.card F ^ (B + 1) := by
      rw [← Nat.card_eq_fintype_card, FiniteField.natCard_extension, Nat.card_eq_fintype_card]
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    rw [h1]
    calc 2 ^ B ≤ 2 ^ (B + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ _ := Nat.pow_le_pow_left h2 _
  obtain ⟨β₀, hβ₀⟩ := exists_spanning_coeffs (K := K) hN hs hT hK
  have hσ : ∀ t ∈ T, ∃ σ : Fin h → Σ w, Fin (N.cap w t),
      (Matrix.of fun i j => glob s β₀ ⟨((σ i).1, t), (σ i).2⟩ j).det ≠ 0 := fun t ht =>
    exists_det_ne_zero (fun x : Σ w, Fin (N.cap w t) => glob s β₀ ⟨(x.1, t), x.2⟩) (hβ₀ t ht)
  choose σ hσ using hσ
  set P : MvPolynomial (Idx N h) F := ∏ t ∈ T.attach, detPoly s t.1 (σ t.1 t.2)
  have hP0 : P ≠ 0 := by
    intro h0
    have := congrArg (aeval β₀) h0
    rw [map_zero, map_prod] at this
    refine (Finset.prod_ne_zero_iff.2 fun t _ => ?_) this
    rw [eval_detPoly]
    exact hσ t.1 t.2
  have hdeg : P.totalDegree ≤ T.card * (h * Fintype.card V) := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc _ ≤ ∑ _t ∈ T.attach, h * Fintype.card V :=
          Finset.sum_le_sum fun t _ => totalDegree_detPoly s _ _
      _ = _ := by rw [Finset.sum_const, Finset.card_attach, smul_eq_mul]
  have hzero : ∀ β : Idx N h → F, (¬∀ t ∈ T,
      span F (Set.range fun x : Σ w, Fin (N.cap w t) => glob s β ⟨(x.1, t), x.2⟩) = ⊤) →
      eval β P = 0 := by
    intro β hβ
    by_contra hne
    refine hβ fun t ht => ?_
    rw [← aeval_eq_eval, map_prod] at hne
    have := (Finset.prod_ne_zero_iff.1 hne) ⟨t, ht⟩ (Finset.mem_attach _ _)
    rw [eval_detPoly] at this
    exact span_eq_top_of_det_ne_zero _ _ this
  set e := Fintype.equivFin (Idx N h)
  set P' := rename e P
  have hP'0 : P' ≠ 0 := fun h0 => hP0 (rename_injective _ e.injective (by rw [map_zero]; exact h0))
  have hsz := schwartz_zippel_totalDegree hP'0 (Finset.univ : Finset F)
  rw [Fintype.piFinset_univ, Finset.card_univ] at hsz
  have hcard : (univ.filter fun β : Idx N h → F => ¬∀ t ∈ T,
      span F (Set.range fun x : Σ w, Fin (N.cap w t) => glob s β ⟨(x.1, t), x.2⟩) = ⊤).card ≤
      (univ.filter fun f : Fin (Fintype.card (Idx N h)) → F => eval f P' = 0).card := by
    refine Finset.card_le_card_of_injOn (fun β => β ∘ e.symm) (fun β hβ => ?_) ?_
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hβ ⊢
      rw [eval_rename]
      have : (β ∘ e.symm) ∘ e = β := by funext x; simp
      rw [this]
      exact hzero β hβ
    · intro a _ b _ hab
      funext x
      have := congrFun hab (e x)
      simpa using this
  have htd : (P'.totalDegree : ℚ≥0) ≤ ((T.card * (h * Fintype.card V) : ℕ) : ℚ≥0) := by
    exact_mod_cast (totalDegree_rename_le _ _).trans hdeg
  calc _ ≤ ((univ.filter fun f : Fin (Fintype.card (Idx N h)) → F => eval f P' = 0).card :
        ℚ≥0) / (Fintype.card F ^ Fintype.card (Idx N h) : ℚ≥0) := by
        gcongr
    _ ≤ (P'.totalDegree : ℚ≥0) / Fintype.card F := hsz
    _ ≤ _ := by gcongr

end Random

section Code

variable {F : Type*} [Field F] {h : ℕ}

noncomputable def linCode (hN : N.IsAcyclic) (s : V) (β : Idx N h → F) :
    Code N s (Fin h → F) F where
  edge u v m i := ∑ k, glob s β ⟨(u, v), i⟩ k * m k
  causal u v hu := ⟨fun y i =>
      ∑ w, ∑ j : Fin (N.cap w u), β ⟨⟨(u, v), i⟩, Sum.inr ⟨w, j⟩⟩ * y w j,
    fun m => by
      funext i
      rw [glob_eq s hN β ⟨(u, v), i⟩]
      have h0 : src s β ⟨(u, v), i⟩ = 0 := by simp [src, hu]
      simp only [h0, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
        mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]⟩

theorem decodes_of_span (hN : N.IsAcyclic) (s : V) (β : Idx N h → F) (t : V)
    (ht : span F (Set.range fun x : Σ w, Fin (N.cap w t) => glob s β ⟨(x.1, t), x.2⟩) = ⊤) :
    (linCode hN s β).Decodes t := by
  classical
  refine ⟨Function.invFun fun m w i => (linCode hN s β).edge w t m i,
    fun m => Function.leftInverse_invFun ?_ m⟩
  intro m m' hm
  let ℓ : (Fin h → F) →ₗ[F] F :=
    { toFun := fun x => ∑ k, x k * (m - m') k
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum, mul_assoc] }
  have hker : span F (Set.range fun x : Σ w, Fin (N.cap w t) => glob s β ⟨(x.1, t), x.2⟩) ≤
      LinearMap.ker ℓ := by
    refine span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    have := congrFun (congrFun hm x.1) x.2
    simp only [linCode] at this
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk, ℓ,
      Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, this, sub_self]
  rw [ht] at hker
  funext k
  have := hker (mem_top (x := Pi.single k 1))
  simp only [LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk, ℓ, Pi.single_apply] at this
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Pi.sub_apply, sub_eq_zero] at this
  exact this

open scoped Classical in
theorem card_not_decodes_le [Fintype F] (hN : N.IsAcyclic) {s : V} {T : Finset V} (hs : s ∉ T)
    (hT : ∀ t ∈ T, h ≤ N.minCut s t) :
    ((univ.filter fun β : Idx N h → F => ¬∀ t ∈ T, (linCode hN s β).Decodes t).card : ℚ≥0) /
        (Fintype.card F ^ Fintype.card (Idx N h) : ℚ≥0) ≤
      ((T.card * (h * Fintype.card V) : ℕ) : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
  refine le_trans ?_ (card_fail_le hN hs hT)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine Nat.cast_le.2 (Finset.card_le_card fun β hβ => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ ⊢
  exact fun h' => hβ fun t ht => decodes_of_span hN s β t (h' t ht)

end Code

end RLNC

end Network

end Meat
