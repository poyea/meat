import Meat.Shannon.MarkovLemma

open Finset

namespace Meat

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem sum_iidProb_not_mem_strongTypicalSet_le (q : PMF S) {η : ℝ} (hη : 0 < η) {n : ℕ}
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

end Meat
