import Meat.Network.Coding
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

namespace Meat

namespace Network

open Finset Module Submodule

section Generic

variable {F M : Type*} [Field F] [Fintype F] [AddCommGroup M] [Module F M]

theorem exists_mem_forall_notMem {K : Type*} (I : Submodule F M) (U : K → Submodule F M)
    (A : Finset K) (hA : A.card ≤ Fintype.card F) (hU : ∀ k ∈ A, ¬I ≤ U k) :
    ∃ y ∈ I, ∀ k ∈ A, y ∉ U k := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨0, I.zero_mem, by simp⟩
  | insert a A ha ih =>
    rw [card_insert_of_notMem ha] at hA
    obtain ⟨v, hvI, hv⟩ := ih (by omega) fun k hk => hU k (mem_insert_of_mem hk)
    by_cases hva : v ∈ U a
    · obtain ⟨w, hwI, hwa⟩ := IsConcreteLE.not_le_iff_exists.mp (hU a (mem_insert_self a A))
      by_contra hne
      push Not at hne
      have hbad : ∀ c : F, ∃ k ∈ A, w + c • v ∈ U k := by
        intro c
        obtain ⟨k, hk, hy⟩ := hne (w + c • v) (I.add_mem hwI (I.smul_mem c hvI))
        rcases mem_insert.mp hk with rfl | hk
        · exact absurd (((U k).add_mem_iff_left ((U k).smul_mem c hva)).mp hy) hwa
        · exact ⟨k, hk, hy⟩
      choose φ hφA hφ using hbad
      have hinj : Function.Injective fun c => (⟨φ c, hφA c⟩ : A) := by
        intro c c' hcc'
        simp only [Subtype.mk.injEq] at hcc'
        by_contra hne'
        have h1 : w + c' • v ∈ U (φ c) := by rw [hcc']; exact hφ c'
        have h2 := (U (φ c)).sub_mem (hφ c) h1
        rw [add_sub_add_left_eq_sub, ← sub_smul] at h2
        exact hv _ (hφA c) (((U (φ c)).smul_mem_iff (sub_ne_zero.mpr hne')).mp h2)
      have := Fintype.card_le_of_injective _ hinj
      simp only [Fintype.card_coe] at this
      omega
    · exact ⟨v, hvI, fun k hk => (mem_insert.mp hk).elim (fun h => h ▸ hva) (hv k)⟩

omit [Fintype F] in
theorem finrank_sup_span_singleton [FiniteDimensional F M] {U : Submodule F M} {y : M}
    (hy : y ∉ U) : finrank F ↥(U ⊔ span F {y}) = finrank F U + 1 := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ U.zero_mem)
  have hd : Disjoint U (span F {y}) := (Submodule.disjoint_span_singleton' hy0).mpr hy
  have := Submodule.finrank_sup_add_finrank_inf_eq U (span F {y})
  rw [hd.eq_bot, finrank_bot, finrank_span_singleton hy0] at this
  omega

theorem exists_generic [FiniteDimensional F M] {ι J : Type*} [Fintype J] (I : Submodule F M)
    (W : J → Submodule F M) (s : Finset ι) (hF : Fintype.card J * 2 ^ s.card ≤ Fintype.card F) :
    ∃ x : ι → M, (∀ i, x i ∈ I) ∧ ∀ j, ∀ B ⊆ s,
      min (finrank F (W j) + B.card) (finrank F ↥(W j ⊔ I)) ≤
        finrank F ↥(W j ⊔ span F (x '' B)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, fun _ => I.zero_mem, fun j B hB => ?_⟩
    rw [subset_empty.mp hB, coe_empty, Set.image_empty, span_empty, sup_bot_eq]
    exact min_le_left _ _
  | insert a s ha ih =>
    rw [card_insert_of_notMem ha, pow_succ] at hF
    obtain ⟨x, hxI, hx⟩ := ih (le_trans (Nat.mul_le_mul_left _ (by omega)) hF)
    obtain ⟨U, hU⟩ : ∃ U : J × Finset ι → Submodule F M,
        ∀ p, U p = W p.1 ⊔ span F (x '' ↑p.2) := ⟨_, fun _ => rfl⟩
    let A := (univ ×ˢ s.powerset).filter fun p => ¬I ≤ U p
    have hA : A.card ≤ Fintype.card F := by
      refine (card_filter_le _ _).trans (le_trans ?_ hF)
      rw [card_product, card_univ, card_powerset]
      exact Nat.mul_le_mul_left _ (by omega)
    obtain ⟨y, hyI, hy⟩ := exists_mem_forall_notMem I U A hA fun p hp => (mem_filter.mp hp).2
    refine ⟨Function.update x a y, fun i => ?_, fun j B hB => ?_⟩
    · by_cases hi : i = a
      · subst hi; simpa using hyI
      · simpa [hi] using hxI i
    · by_cases haB : a ∈ B
      · have hB0 : B.erase a ⊆ s := by
          intro i hi
          have := hB (mem_of_mem_erase hi)
          rcases mem_insert.mp this with rfl | h
          · exact absurd hi (notMem_erase _ _)
          · exact h
        have himg : Function.update x a y '' ↑B = insert y (x '' ↑(B.erase a)) := by
          conv_lhs => rw [← insert_erase haB]
          rw [coe_insert, Set.image_insert_eq, Function.update_self]
          congr 1
          refine Set.image_congr fun i hi => ?_
          have : i ≠ a := fun h => notMem_erase a B (h ▸ hi)
          simp [this]
        have hcard : B.card = (B.erase a).card + 1 := (card_erase_add_one haB).symm
        rw [himg, span_insert, sup_comm (span F {y}), ← sup_assoc]
        have ih0 := hx j (B.erase a) hB0
        by_cases hIU : I ≤ U (j, B.erase a)
        · rw [hU] at hIU
          have h1 : W j ⊔ I ≤ W j ⊔ span F (x '' ↑(B.erase a)) ⊔ span F {y} :=
            sup_le (le_sup_left.trans le_sup_left) (hIU.trans le_sup_left)
          exact (min_le_right _ _).trans (Submodule.finrank_mono h1)
        · have hmem : (j, B.erase a) ∈ A :=
            mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_powerset.mpr hB0⟩, hIU⟩
          have hyU : y ∉ W j ⊔ span F (x '' ↑(B.erase a)) := by
            have := hy _ hmem
            rwa [hU] at this
          rw [finrank_sup_span_singleton hyU]
          rw [min_le_iff] at ih0 ⊢
          omega
      · have hBs : B ⊆ s := fun i hi => by
          rcases mem_insert.mp (hB hi) with rfl | h
          · exact absurd hi haB
          · exact h
        have : Function.update x a y '' ↑B = x '' ↑B :=
          Set.image_congr fun i hi => by
            have : i ≠ a := fun h => haB (h ▸ hi)
            simp [this]
        rw [this]
        exact hx j B hBs

end Generic

section Construction

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}

private abbrev Edge (N : Network V) := Σ p : V × V, Fin (N.cap p.1 p.2)

private def edg (N : Network V) (X Y : Finset V) : Finset (Edge N) :=
  (X ×ˢ Y).sigma fun p => (univ : Finset (Fin (N.cap p.1 p.2)))

omit [Fintype V] [DecidableEq V] in
private theorem mem_edg {X Y : Finset V} {e : Edge N} :
    e ∈ edg N X Y ↔ e.1.1 ∈ X ∧ e.1.2 ∈ Y := by
  simp [edg]

omit [Fintype V] [DecidableEq V] in
private theorem card_edg (X Y : Finset V) :
    (edg N X Y).card = ∑ u ∈ X, ∑ v ∈ Y, N.cap u v := by
  simp [edg, card_sigma, sum_product]

private def inFam {F : Type*} [Field F] {h : ℕ} (g : Edge N → Dual F (Fin h → F)) (u : V) :
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

theorem exists_code_of_le_minCut (hN : N.IsAcyclic) {s : V} {T : Finset V} (hs : s ∉ T) {h : ℕ}
    (hT : ∀ t ∈ T, h ≤ N.minCut s t) {F : Type*} [Field F] [Fintype F]
    (hF : 2 ^ (Fintype.card V + ∑ u, ∑ v, N.cap u v) ≤ Fintype.card F) :
    ∃ c : Code N s (Fin h → F) F, ∀ t ∈ T, c.Decodes t := by
  classical
  have hcard : Fintype.card (Edge N) = ∑ u, ∑ v, N.cap u v := by
    simp [Edge, Fintype.card_sigma, Fintype.sum_prod_type]
  obtain ⟨P, g, hP, -, hL, hD, -⟩ :=
    exists_good hN hs hT (F := F) (by rwa [hcard, ← pow_add]) _ le_rfl
  have hPu : P = univ := eq_univ_of_card P hP
  subst hPu
  refine ⟨⟨fun u v m i => g ⟨(u, v), i⟩ m, fun u v hu => ?_⟩, fun t ht => ?_⟩
  · have hmem := fun i => hL u (mem_univ u) hu v i
    simp only [mem_span_range_iff_exists_fun] at hmem
    choose c hc using hmem
    refine ⟨fun y i => ∑ x : Σ w, Fin (N.cap w u), c i x * y x.1 x.2, fun m => ?_⟩
    funext i
    rw [← hc i]
    simp [inFam]
  · refine ⟨Function.invFun fun m w i => g ⟨(w, t), i⟩ m,
      fun m => Function.leftInverse_invFun ?_ m⟩
    intro m m' hm
    have hker : span F (Set.range (inFam g t)) ≤
        LinearMap.ker (Dual.eval F (Fin h → F) (m - m')) := by
      refine span_le.mpr ?_
      rintro _ ⟨y, rfl⟩
      have := congrFun (congrFun hm y.1) y.2
      simp only at this
      simp [inFam, this]
    rw [hD t ht (mem_univ t)] at hker
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff F]
    intro φ
    simpa using hker (mem_top (x := φ))

end Construction

end Network

end Meat
