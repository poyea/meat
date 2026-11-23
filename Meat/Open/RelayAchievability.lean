import Meat.Open.Relay

namespace Meat

namespace Relay

variable {A A₁ B₁ K S : Type*}

def blockOf {nb m : ℕ} (y : Fin (nb * m) → S) (b : Fin nb) : Fin m → S :=
  fun j => y (finProdFinEquiv (b, j))

theorem finProdFinEquiv_lt {nb m : ℕ} {b b' : Fin nb} (j j' : Fin m) (h : b < b') :
    finProdFinEquiv (b, j) < finProdFinEquiv (b', j') := by
  rw [Fin.lt_def]
  simp only [finProdFinEquiv_apply_val]
  have h' : (b : ℕ) + 1 ≤ b' := h
  have := j.2
  nlinarith

def relayEstimate {nb m : ℕ} (k₀ : K) (φ : K → (Fin m → B₁) → K) (y : Fin (nb * m) → B₁) :
    ℕ → K
  | 0 => k₀
  | k + 1 => if h : k < nb then φ (relayEstimate k₀ φ y k) (blockOf y ⟨k, h⟩)
    else relayEstimate k₀ φ y k

theorem relayEstimate_congr {nb m : ℕ} (k₀ : K) (φ : K → (Fin m → B₁) → K)
    {y y' : Fin (nb * m) → B₁} (b : Fin nb)
    (h : ∀ j : Fin m, ∀ b' : Fin nb, b' < b → y (finProdFinEquiv (b', j)) =
      y' (finProdFinEquiv (b', j))) :
    ∀ k : ℕ, k ≤ (b : ℕ) → relayEstimate k₀ φ y k = relayEstimate k₀ φ y' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hk' : k < nb := by omega
    simp only [relayEstimate, hk', dite_true]
    rw [ih (by omega)]
    congr 1
    funext j
    exact h j ⟨k, hk'⟩ (by rw [Fin.lt_def]; simp; omega)

def destEstimate {nb m : ℕ} (k₀ : K) (ψ : K → (Fin m → S) → K) (y : Fin ((nb + 1) * m) → S) :
    ℕ → K
  | 0 => k₀
  | r + 1 => if h : nb - r < nb + 1 then ψ (destEstimate k₀ ψ y r) (blockOf y ⟨nb - r, h⟩)
    else destEstimate k₀ ψ y r

def currentMessage {nb : ℕ} (k₀ : K) (w : Fin nb → K) (b : Fin (nb + 1)) : K :=
  if h : (b : ℕ) < nb then w ⟨b, h⟩ else k₀

def previousMessage {nb : ℕ} (k₀ : K) (w : Fin nb → K) (b : Fin (nb + 1)) : K :=
  if h : (b : ℕ) = 0 then k₀ else w ⟨b - 1, by omega⟩

def blockMarkovCode {B : Type*} {nb m : ℕ} (k₀ : K) (C : K → K → Fin m → A)
    (C₁ : K → Fin m → A₁) (φ : K → (Fin m → B₁) → K) (ψ : K → (Fin m → B) → K) :
    RelayCode (Fin nb → K) A A₁ B B₁ ((nb + 1) * m) where
  enc w t := C (currentMessage k₀ w (finProdFinEquiv.symm t).1)
    (previousMessage k₀ w (finProdFinEquiv.symm t).1) (finProdFinEquiv.symm t).2
  relay t y := C₁ (relayEstimate k₀ φ y (finProdFinEquiv.symm t).1) (finProdFinEquiv.symm t).2
  causal t y y' h := by
    have e := relayEstimate_congr k₀ φ (y := y) (y' := y') (finProdFinEquiv.symm t).1
      (fun j b' hb => h _ (by
        have := finProdFinEquiv_lt j (finProdFinEquiv.symm t).2 hb
        rwa [show (finProdFinEquiv ((finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2)) = t
          from finProdFinEquiv.apply_symm_apply t] at this))
      _ le_rfl
    simp only [e]
  dec y b := destEstimate k₀ ψ y (nb - b)

end Relay

end Meat
