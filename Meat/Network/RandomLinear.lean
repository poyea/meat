import Meat.Network.Linear
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Meat

namespace Network

namespace RLNC

open Finset Module Submodule

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}

abbrev Edge (N : Network V) := Σ p : V × V, Fin (N.cap p.1 p.2)

def edg (N : Network V) (X Y : Finset V) : Finset (Edge N) :=
  (X ×ˢ Y).sigma fun p => (univ : Finset (Fin (N.cap p.1 p.2)))

omit [Fintype V] [DecidableEq V] in
theorem mem_edg {X Y : Finset V} {e : Edge N} :
    e ∈ edg N X Y ↔ e.1.1 ∈ X ∧ e.1.2 ∈ Y := by
  simp [edg]

omit [Fintype V] [DecidableEq V] in
theorem card_edg (X Y : Finset V) :
    (edg N X Y).card = ∑ u ∈ X, ∑ v ∈ Y, N.cap u v := by
  simp [edg, card_sigma, sum_product]

def inFam {F : Type*} [Field F] {h : ℕ} (g : Edge N → Dual F (Fin h → F)) (u : V) :
    (Σ w, Fin (N.cap w u)) → Dual F (Fin h → F) :=
  fun x => g ⟨(x.1, u), x.2⟩

private def Good {F : Type*} [Field F] (N : Network V) (s : V) (T : Finset V) (h : ℕ)
    (P : Finset V) (g : Edge N → Dual F (Fin h → F)) : Prop :=
  (∀ u ∈ P, u ≠ s → ∀ w, 0 < N.cap w u → w ∈ P) ∧
  (∀ u ∈ P, u ≠ s → ∀ v (i : Fin (N.cap u v)), g ⟨(u, v), i⟩ ∈ span F (Set.range (inFam g u))) ∧
  (∀ t ∈ T, t ∈ P → span F (Set.range (inFam g t)) = ⊤) ∧
  ∀ S : Finset V, s ∈ S → P ⊆ S → (∃ t ∈ T, t ∉ S) →
    h ≤ finrank F ↥(span F (g '' ↑(edg N P Sᶜ))) + ∑ u ∈ S \ P, ∑ v ∈ Sᶜ, N.cap u v

private theorem good_empty {F : Type*} [Field F] {s : V} {T : Finset V} {h : ℕ}
    (hT : ∀ t ∈ T, h ≤ N.minCut s t) : Good N s T h ∅ (0 : Edge N → Dual F (Fin h → F)) := by
  refine ⟨by simp, by simp, by simp, fun S hs _ ⟨t, ht, htS⟩ => ?_⟩
  rw [sdiff_empty]
  calc h ≤ N.minCut s t := hT t ht
    _ ≤ N.cutValue S :=
      ciInf_le' (fun S : {S : Finset V // s ∈ S ∧ t ∉ S} => N.cutValue S.1) ⟨S, hs, htS⟩
    _ ≤ _ := Nat.le_add_left _ _

private theorem good_insert {F : Type*} [Field F] [Fintype F] {s : V} {T : Finset V}
    (hs : s ∉ T) {h : ℕ} (hF : 2 ^ Fintype.card V * 2 ^ Fintype.card (Edge N) ≤ Fintype.card F)
    {P : Finset V} {g : Edge N → Dual F (Fin h → F)} (hg : Good N s T h P g) {u : V}
    (hu : u ∉ P) (hpred : u ≠ s → ∀ w, 0 < N.cap w u → w ∈ P) :
    ∃ g' : Edge N → Dual F (Fin h → F), Good N s T h (insert u P) g' := by
  classical
  obtain ⟨hcl, hL, hD, hC⟩ := hg
  let I : Submodule F (Dual F (Fin h → F)) :=
    if u = s then ⊤ else span F (g '' ↑(edg N P {u}))
  let W : Finset V → Submodule F (Dual F (Fin h → F)) := fun S => span F (g '' ↑(edg N P Sᶜ))
  have hbound : Fintype.card (Finset V) * 2 ^ (edg N {u} univ).card ≤ Fintype.card F := by
    rw [Fintype.card_finset]
    exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (card_le_univ _))) hF
  obtain ⟨x, hxI, hx⟩ := exists_generic I W (edg N {u} univ) hbound
  let g' : Edge N → Dual F (Fin h → F) := fun e => if e.1.1 = u then x e else g e
  have hgg : ∀ e : Edge N, e.1.1 ≠ u → g' e = g e := fun e he => ite_eq_right he
  have himg : ∀ X Y : Finset V, u ∉ X → g' '' ↑(edg N X Y) = g '' ↑(edg N X Y) := by
    intro X Y hX
    refine Set.image_congr fun e he => hgg e ?_
    intro hEq
    exact hX (hEq ▸ (mem_edg.mp he).1)
  have hfam : ∀ v, (∀ w, 0 < N.cap w v → w ≠ u) → inFam g' v = inFam g v := by
    intro v hv
    funext y
    exact hgg _ (hv y.1 (Fin.pos y.2))
  have hIle : ∀ Y : Finset V, (∀ v ∈ Y, v = u) →
      span F (g '' ↑(edg N P Y)) ≤ span F (Set.range (inFam g' u)) := by
    intro Y hY
    refine span_le.mpr ?_
    rintro _ ⟨⟨⟨a, b⟩, j⟩, he, rfl⟩
    obtain ⟨ha, hb⟩ := mem_edg.mp he
    have hbu : b = u := hY b hb
    subst hbu
    exact subset_span ⟨⟨a, j⟩, hgg _ fun h => hu (h ▸ ha)⟩
  refine ⟨g', ?_, ?_, ?_, ?_⟩
  · intro v hv hvs w hw
    rcases mem_insert.mp hv with hvu | hv
    · subst hvu
      exact mem_insert_of_mem (hpred hvs w hw)
    · exact mem_insert_of_mem (hcl v hv hvs w hw)
  · intro v hv hvs w i
    by_cases hvu : v = u
    · subst hvu
      have hxe : g' ⟨(v, w), i⟩ = x ⟨(v, w), i⟩ := ite_eq_left rfl
      rw [hxe]
      have hxv := hxI ⟨(v, w), i⟩
      simp only [I, ite_eq_right hvs] at hxv
      exact hIle {v} (fun _ h => mem_singleton.mp h) hxv
    · have hvP : v ∈ P := (mem_insert.mp hv).resolve_left hvu
      rw [hgg _ hvu, hfam v fun a ha h => hu (h ▸ hcl v hvP hvs a ha)]
      exact hL v hvP hvs w i
  · intro t ht htP
    have hts : t ≠ s := fun h => hs (h ▸ ht)
    by_cases htu : t = u
    · subst htu
      refine eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
      have hc := hC (univ.erase t) (mem_erase.mpr ⟨fun h => hts h.symm, mem_univ _⟩)
        (fun a ha => mem_erase.mpr ⟨fun h => hu (h ▸ ha), mem_univ _⟩)
        ⟨t, ht, notMem_erase t univ⟩
      have hz : ∑ a ∈ univ.erase t \ P, ∑ v ∈ (univ.erase t)ᶜ, N.cap a v = 0 := by
        refine sum_eq_zero fun a ha => sum_eq_zero fun v hv => ?_
        have hvt : v = t := by simpa using hv
        rw [hvt]
        by_contra hne
        exact (mem_sdiff.mp ha).2 (hpred hts a (Nat.pos_of_ne_zero hne))
      rw [hz, add_zero] at hc
      rw [Subspace.dual_finrank_eq, Module.finrank_fin_fun]
      exact hc.trans (Submodule.finrank_mono (hIle _ fun v hv => by simpa using hv))
    · have htP' : t ∈ P := (mem_insert.mp htP).resolve_left htu
      rw [hfam t fun a ha h => hu (h ▸ hcl t htP' hts a ha)]
      exact hD t ht htP'
  · intro S hsS hPS ⟨t0, ht0, ht0S⟩
    have huS : u ∈ S := hPS (mem_insert_self u P)
    have hP : P ⊆ S := fun a ha => hPS (mem_insert_of_mem ha)
    have ha : h ≤ finrank F ↥(W S) + ∑ a ∈ S \ P, ∑ v ∈ Sᶜ, N.cap a v :=
      hC S hsS hP ⟨t0, ht0, ht0S⟩
    have hsplit : ∑ a ∈ S \ P, ∑ v ∈ Sᶜ, N.cap a v =
        (edg N {u} Sᶜ).card + ∑ a ∈ S \ insert u P, ∑ v ∈ Sᶜ, N.cap a v := by
      have h1 : S \ P = insert u (S \ insert u P) := by
        ext a
        simp only [mem_sdiff, mem_insert]
        by_cases hau : a = u
        · subst hau
          simp [huS, hu]
        · simp [hau]
      rw [h1, sum_insert (by simp), card_edg, sum_singleton]
    rw [hsplit] at ha
    have hb : h ≤ finrank F ↥(W S ⊔ I) + ∑ a ∈ S \ insert u P, ∑ v ∈ Sᶜ, N.cap a v := by
      by_cases hus : u = s
      · have hI : I = ⊤ := ite_eq_left hus
        rw [hI, sup_top_eq, finrank_top, Subspace.dual_finrank_eq, Module.finrank_fin_fun]
        omega
      · have hc := hC (S.erase u) (mem_erase.mpr ⟨fun h => hus h.symm, hsS⟩)
          (fun a ha => mem_erase.mpr ⟨fun h => hu (h ▸ ha), hP ha⟩)
          ⟨t0, ht0, fun h => ht0S (mem_of_mem_erase h)⟩
        have hE : edg N P (S.erase u)ᶜ = edg N P Sᶜ ∪ edg N P {u} := by
          ext e
          simp only [mem_union, mem_edg, mem_compl, mem_erase, mem_singleton]
          tauto
        have h1 : S.erase u \ P = S \ insert u P := by
          ext a
          simp only [mem_sdiff, mem_erase, mem_insert]
          tauto
        have h2 : (S.erase u)ᶜ = insert u Sᶜ := by
          ext v
          simp only [mem_compl, mem_erase, mem_insert]
          tauto
        have hsum : ∑ a ∈ S.erase u \ P, ∑ v ∈ (S.erase u)ᶜ, N.cap a v =
            ∑ a ∈ S \ insert u P, ∑ v ∈ Sᶜ, N.cap a v := by
          rw [h1]
          refine sum_congr rfl fun a ha => ?_
          rw [h2, sum_insert (by simp [huS])]
          have hz : N.cap a u = 0 := by
            by_contra hne
            have := hpred hus a (Nat.pos_of_ne_zero hne)
            simp only [mem_sdiff, mem_insert] at ha
            tauto
          rw [hz, zero_add]
        have hWI : W S ⊔ I = span F (g '' ↑(edg N P Sᶜ)) ⊔ span F (g '' ↑(edg N P {u})) := by
          simp only [W, I, ite_eq_right hus]
        rw [hE, coe_union, Set.image_union, span_union, hsum] at hc
        rw [hWI]
        exact hc
    have hE' : edg N (insert u P) Sᶜ = edg N {u} Sᶜ ∪ edg N P Sᶜ := by
      ext e
      simp only [mem_union, mem_edg, mem_insert, mem_singleton]
      tauto
    have hx' : g' '' ↑(edg N {u} Sᶜ) = x '' ↑(edg N {u} Sᶜ) :=
      Set.image_congr fun e he => ite_eq_left (mem_singleton.mp (mem_edg.mp he).1)
    have hgen := hx S (edg N {u} Sᶜ) fun e he => mem_edg.mpr ⟨(mem_edg.mp he).1, mem_univ _⟩
    rw [hE', coe_union, Set.image_union, span_union, hx', himg P _ hu, sup_comm]
    change h ≤ finrank F ↥(W S ⊔ span F (x '' ↑(edg N {u} Sᶜ))) + _
    rw [min_le_iff] at hgen
    omega

private theorem exists_good (hN : N.IsAcyclic) {s : V} {T : Finset V} (hs : s ∉ T) {h : ℕ}
    (hT : ∀ t ∈ T, h ≤ N.minCut s t) {F : Type*} [Field F] [Fintype F]
    (hF : 2 ^ Fintype.card V * 2 ^ Fintype.card (Edge N) ≤ Fintype.card F) :
    ∀ n ≤ Fintype.card V, ∃ (P : Finset V) (g : Edge N → Dual F (Fin h → F)),
      P.card = n ∧ Good N s T h P g := by
  obtain ⟨r, hr⟩ := hN
  intro n
  induction n with
  | zero => exact fun _ => ⟨∅, 0, rfl, good_empty hT⟩
  | succ n ih =>
    intro hn
    obtain ⟨P, g, hPn, hg⟩ := ih (by omega)
    have hne : (univ \ P).Nonempty := by
      by_contra hem
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at hem
      have := card_le_card hem
      rw [card_univ] at this
      omega
    by_cases hsP : s ∈ P
    · obtain ⟨u, hu, hmin⟩ := exists_min_image (univ \ P) r hne
      have huP : u ∉ P := (mem_sdiff.mp hu).2
      obtain ⟨g', hg'⟩ := good_insert hs hF hg huP fun _ w hw => by
        by_contra hwP
        exact absurd (hmin w (mem_sdiff.mpr ⟨mem_univ _, hwP⟩)) (not_le.mpr (hr w u hw))
      exact ⟨insert u P, g', by rw [card_insert_of_notMem huP, hPn], hg'⟩
    · obtain ⟨g', hg'⟩ := good_insert hs hF hg hsP fun h => absurd rfl h
      exact ⟨insert s P, g', by rw [card_insert_of_notMem hsP, hPn], hg'⟩


theorem exists_linear_family (hN : N.IsAcyclic) {s : V} {T : Finset V} (hs : s ∉ T) {h : ℕ}
    (hT : ∀ t ∈ T, h ≤ N.minCut s t) {F : Type*} [Field F] [Fintype F]
    (hF : 2 ^ (Fintype.card V + ∑ u, ∑ v, N.cap u v) ≤ Fintype.card F) :
    ∃ g : Edge N → Dual F (Fin h → F),
      (∀ u, u ≠ s → ∀ v (i : Fin (N.cap u v)), g ⟨(u, v), i⟩ ∈ span F (Set.range (inFam g u))) ∧
      ∀ t ∈ T, span F (Set.range (inFam g t)) = ⊤ := by
  classical
  have hcard : Fintype.card (Edge N) = ∑ u, ∑ v, N.cap u v := by
    simp [Edge, Fintype.card_sigma, Fintype.sum_prod_type]
  obtain ⟨P, g, hP, -, hL, hD, -⟩ :=
    exists_good hN hs hT (F := F) (by rwa [hcard, ← pow_add]) _ le_rfl
  have hPu : P = univ := eq_univ_of_card P hP
  subst hPu
  exact ⟨g, fun u hu v i => hL u (mem_univ u) hu v i, fun t ht => hD t ht (mem_univ t)⟩

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
