import Meat.Network.CutSetBound
import Meat.Network.Linear

namespace Meat

namespace Network

variable {V : Type*}

theorem multicast_iff [Fintype V] [DecidableEq V] (N : Network V) (hN : N.IsAcyclic)
    (s : V) (T : Finset V) (hs : s ∉ T) (h : ℕ) :
    (∀ t ∈ T, h ≤ N.minCut s t) ↔
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (c : Code N s (Fin h → F) F),
        ∀ t ∈ T, c.Decodes t := by
  constructor
  · intro hT
    obtain ⟨p, hp, hp'⟩ := Nat.exists_infinite_primes (2 ^ (Fintype.card V + ∑ u, ∑ v, N.cap u v))
    have : Fact p.Prime := ⟨hp'⟩
    obtain ⟨c, hc⟩ := exists_code_of_le_minCut hN hs hT (F := ZMod p) (by rwa [ZMod.card])
    exact ⟨ZMod p, inferInstance, inferInstance, c, hc⟩
  · rintro ⟨F, _, _, c, hc⟩ t ht
    exact le_minCut_of_decodes hN (fun e : s = t => hs (e ▸ ht)) c (hc t ht)

end Network

end Meat
