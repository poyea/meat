import Meat.Network.Coding
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

namespace Meat

namespace Network

open Finset

variable {V : Type*}

theorem incoming_eq_of_cut {N : Network V} (hN : N.IsAcyclic) {s : V} {Msg F : Type*}
    (c : Code N s Msg F) {S : Finset V} (hs : s ∈ S) {m m' : Msg}
    (hX : ∀ u ∈ S, ∀ v ∉ S, c.edge u v m = c.edge u v m') :
    ∀ v ∉ S, (fun w => c.edge w v m) = fun w => c.edge w v m' := by
  obtain ⟨r, hr⟩ := hN
  intro v
  induction hn : r v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    intro hv
    funext w j
    by_cases hw : w ∈ S
    · exact congrFun (hX w hw v hv) j
    · have hws : w ≠ s := fun h => hw (h ▸ hs)
      obtain ⟨f, hf⟩ := c.causal w v hws
      rw [hf m, hf m', ih (r w) (hn ▸ hr w v (Fin.pos j)) w rfl hw]

theorem le_cutValue_of_decodes [Fintype V] [DecidableEq V] {N : Network V} (hN : N.IsAcyclic)
    {s t : V} {h : ℕ} {F : Type*} [Finite F] [Nontrivial F] (c : Code N s (Fin h → F) F)
    (ht : c.Decodes t) {S : Finset V} (hs : s ∈ S) (htS : t ∉ S) : h ≤ N.cutValue S := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨d, hd⟩ := ht
  let D : Finset (Σ p : V × V, Fin (N.cap p.1 p.2)) :=
    (S ×ˢ Sᶜ).sigma fun p => (univ : Finset (Fin (N.cap p.1 p.2)))
  let X : (Fin h → F) → D → F := fun m e => c.edge e.1.1.1 e.1.1.2 m e.1.2
  have hX : Function.Injective X := by
    intro m m' hm
    have hcut : ∀ u ∈ S, ∀ v ∉ S, c.edge u v m = c.edge u v m' := by
      intro u hu v hv
      funext j
      exact congrFun hm ⟨⟨(u, v), j⟩, by simp [D, hu, hv]⟩
    rw [← hd m, ← hd m', incoming_eq_of_cut hN c hs hcut t htS]
  have hcard := Fintype.card_le_of_injective X hX
  have hD : D.card = N.cutValue S := by
    simp [D, card_sigma, cutValue, sum_product]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hD] at hcard
  exact (Nat.pow_le_pow_iff_right Fintype.one_lt_card).mp hcard

theorem le_minCut_of_decodes [Fintype V] [DecidableEq V] {N : Network V} (hN : N.IsAcyclic)
    {s t : V} (hst : s ≠ t) {h : ℕ} {F : Type*} [Finite F] [Nontrivial F]
    (c : Code N s (Fin h → F) F) (ht : c.Decodes t) : h ≤ N.minCut s t := by
  have : Nonempty {S : Finset V // s ∈ S ∧ t ∉ S} :=
    ⟨⟨{s}, mem_singleton_self s, by simpa [eq_comm] using hst⟩⟩
  exact le_ciInf fun S => le_cutValue_of_decodes hN c ht S.2.1 S.2.2

end Network

end Meat
