import Meat.Open.RelayAchievability
import Meat.Open.RelayConverse

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

namespace Relay

variable {A A₁ B B₁ K S In : Type*}

theorem sum_ite_le_of_agree {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) (hf : ∑ ω, f ω = 1)
    (hg : ∑ ω, g ω = 1) (G E : Ω → Prop) [DecidablePred G] [DecidablePred E]
    (hfg : ∀ ω, G ω → f ω = g ω) (hf0 : ∀ ω, 0 ≤ f ω) :
    ∑ ω, (if E ω then f ω else 0) ≤ ∑ ω, (if E ω ∨ ¬G ω then g ω else 0) := by
  have h1 : ∀ ω, (if E ω then f ω else 0) - (if E ω ∨ ¬G ω then g ω else 0) ≤
      (if G ω then 0 else f ω - g ω) := by
    intro ω
    by_cases hG : G ω <;> by_cases hE : E ω <;> simp [hG, hE, hfg ω, hf0 ω]
  have h2 : ∑ ω, (if G ω then 0 else f ω - g ω) = 0 := by
    have : ∑ ω, (if G ω then 0 else f ω - g ω) = ∑ ω, (f ω - g ω) := by
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases hG : G ω
      · simp [hG, hfg ω hG]
      · simp [hG]
    rw [this, Finset.sum_sub_distrib, hf, hg, sub_self]
  have h3 := Finset.sum_le_sum fun ω (_ : ω ∈ Finset.univ) => h1 ω
  rw [Finset.sum_sub_distrib, h2] at h3
  linarith

def blockSplit {nb m : ℕ} : (Fin (nb * m) → S) ≃ (Fin nb → Fin m → S) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl S)).trans (Equiv.curry _ _ _)

theorem blockSplit_apply {nb m : ℕ} (y : Fin (nb * m) → S) (b : Fin nb) :
    blockSplit y b = blockOf y b := by
  funext j
  simp [blockSplit, blockOf, Equiv.arrowCongr]

theorem toReal_blockProb_split {nb m : ℕ} (W : DMC In S) (x : Fin (nb * m) → In)
    (y : Fin (nb * m) → S) :
    (DMC.blockProb W x y).toReal = ∏ b, (DMC.blockProb W (blockOf x b) (blockOf y b)).toReal := by
  simp only [DMC.toReal_blockProb, blockOf]
  rw [← Finset.prod_product', ← Fintype.prod_equiv finProdFinEquiv
    (fun p : Fin nb × Fin m => (W (x (finProdFinEquiv p)) (y (finProdFinEquiv p))).toReal)
    (fun t => (W (x t) (y t)).toReal) fun p => rfl]
  rfl

theorem sum_blockProb_block [Fintype S] {nb m : ℕ} (W : DMC In S) (x : Fin (nb * m) → In)
    (β : Fin nb) (F : (Fin m → S) → ℝ) :
    ∑ y, (DMC.blockProb W x y).toReal * F (blockOf y β) =
      ∑ z, (DMC.blockProb W (blockOf x β) z).toReal * F z := by
  classical
  rw [← Fintype.sum_equiv blockSplit.symm
    (fun Y : Fin nb → Fin m → S => (DMC.blockProb W x (blockSplit.symm Y)).toReal *
      F (blockOf (blockSplit.symm Y) β)) _ fun Y => rfl]
  have e : ∀ Y : Fin nb → Fin m → S, blockOf (blockSplit.symm Y) = Y := fun Y => by
    funext b
    rw [← blockSplit_apply, Equiv.apply_symm_apply]
  simp_rw [toReal_blockProb_split, e]
  exact sum_prod_mul_apply (fun b z => (DMC.blockProb W (blockOf x b) z).toReal)
    (fun b => by rw [← ENNReal.toReal_sum fun _ _ => DMC.blockProb_ne_top _ _ _,
      DMC.sum_blockProb_eq_one, ENNReal.toReal_one]) F β

section Genie

variable {nb m : ℕ} (k₀ : K) (C : K → K → Fin m → A) (C₁ : K → Fin m → A₁)

def genieInput (w : Fin nb → K) : Fin ((nb + 1) * m) → A × A₁ := fun t =>
  (C (currentMessage k₀ w (finProdFinEquiv.symm t).1) (previousMessage k₀ w
    (finProdFinEquiv.symm t).1) (finProdFinEquiv.symm t).2,
    C₁ (previousMessage k₀ w (finProdFinEquiv.symm t).1) (finProdFinEquiv.symm t).2)

theorem blockOf_genieInput (w : Fin nb → K) (β : Fin (nb + 1)) :
    blockOf (genieInput k₀ C C₁ w) β = fun j =>
      (C (currentMessage k₀ w β) (previousMessage k₀ w β) j, C₁ (previousMessage k₀ w β) j) := by
  funext j
  simp [blockOf, genieInput]

variable (φ : K → (Fin m → B₁) → K) (ψ : K → (Fin m → B) → K)

theorem seqProb_eq_of_good (W : DMC (A × A₁) (B × B₁)) (w : Fin nb → K)
    (y : Fin ((nb + 1) * m) → B × B₁)
    (h : ∀ b : Fin (nb + 1), relayEstimate k₀ φ (fun t => (y t).2) b = previousMessage k₀ w b) :
    (blockMarkovCode (B := B) k₀ C C₁ φ ψ).seqProb W w y =
      DMC.blockProb W (genieInput k₀ C C₁ w) y := by
  simp only [RelayCode.seqProb, DMC.blockProb, blockMarkovCode, genieInput, h]

theorem good_of_relay (w : Fin nb → K) (y₁ : Fin ((nb + 1) * m) → B₁)
    (h : ∀ k : Fin nb, φ (previousMessage k₀ w k.castSucc) (blockOf y₁ k.castSucc) = w k) :
    ∀ b : Fin (nb + 1), relayEstimate k₀ φ y₁ b = previousMessage k₀ w b := by
  have key : ∀ b : ℕ, (hb : b < nb + 1) →
      relayEstimate k₀ φ y₁ b = previousMessage k₀ w ⟨b, hb⟩ := by
    intro b
    induction b with
    | zero => intro _; simp [relayEstimate, previousMessage]
    | succ b ih =>
      intro hb
      have hb' : b < nb + 1 := by omega
      simp only [relayEstimate, hb', dite_true]
      rw [ih hb']
      have := h ⟨b, by omega⟩
      simp only [Fin.castSucc_mk] at this
      rw [this]
      simp [previousMessage]
  exact fun b => key b b.2

theorem dec_of_dest (w : Fin nb → K) (y : Fin ((nb + 1) * m) → B)
    (h : ∀ k : Fin nb, ψ (currentMessage k₀ w k.succ) (blockOf y k.succ) = w k) :
    (blockMarkovCode (B₁ := B₁) k₀ C C₁ φ ψ).dec y = w := by
  have key : ∀ r : ℕ, (hr : r ≤ nb) →
      destEstimate k₀ ψ y r = currentMessage k₀ w ⟨nb - r, by omega⟩ := by
    intro r
    induction r with
    | zero => intro _; simp [destEstimate, currentMessage]
    | succ r ih =>
      intro hr
      have h1 : nb - r < nb + 1 := by omega
      simp only [destEstimate, h1, dite_true]
      rw [ih (by omega)]
      have := h ⟨nb - (r + 1), by omega⟩
      have e : (⟨nb - (r + 1), by omega⟩ : Fin nb).succ = ⟨nb - r, h1⟩ := by
        ext
        simp only [Fin.val_succ]
        omega
      rw [e] at this
      rw [this]
      simp only [currentMessage, show nb - (r + 1) < nb by omega, dite_true]
  funext b
  simp only [blockMarkovCode]
  rw [key _ (by omega)]
  simp only [currentMessage, show nb - (nb - (b : ℕ)) < nb by omega, dite_true]
  congr 1
  ext
  simp
  omega

end Genie

section Bound

variable {nb m : ℕ} [Fintype B] [Nonempty B] [Fintype B₁] [Nonempty B₁] [DecidableEq K]
  (k₀ : K) (C : K → K → Fin m → A) (C₁ : K → Fin m → A₁) (φ : K → (Fin m → B₁) → K)
  (ψ : K → (Fin m → B) → K)

omit [Nonempty B] [Nonempty B₁] in
private lemma sum_block_marginal {T : Type*} [Fintype T] (W : DMC (A × A₁) (B × B₁))
    (x : Fin ((nb + 1) * m) → A × A₁) (β : Fin (nb + 1)) (g : B × B₁ → T)
    (P : (Fin m → T) → Prop) [DecidablePred P] :
    ∑ y, (if P (fun j => g (blockOf y β j)) then (DMC.blockProb W x y).toReal else 0) =
      ∑ z, (if P z then (DMC.blockProb (fun a => (W a).map g) (blockOf x β) z).toReal else 0) := by
  classical
  have h1 := sum_blockProb_block W x β fun z => if P (fun j => g (z j)) then (1 : ℝ) else 0
  have h2 := DMC.sum_blockProb_mul_comp W g (blockOf x β) fun z => if P z then (1 : ℝ) else 0
  simp only [mul_ite, mul_one, mul_zero] at h1 h2
  rw [h1, h2]

theorem errorProb_blockMarkov_le (W : DMC (A × A₁) (B × B₁)) (w : Fin nb → K) :
    ((blockMarkovCode k₀ C C₁ φ ψ).errorProb W w).toReal ≤
      ∑ k : Fin nb, ∑ z : Fin m → B₁, (if φ (previousMessage k₀ w k.castSucc) z = w k then 0
        else (DMC.blockProb (fun a => (W a).map Prod.snd)
          (blockOf (genieInput k₀ C C₁ w) k.castSucc) z).toReal) +
      ∑ k : Fin nb, ∑ z : Fin m → B, (if ψ (currentMessage k₀ w k.succ) z = w k then 0
        else (DMC.blockProb (fun a => (W a).map Prod.fst)
          (blockOf (genieInput k₀ C C₁ w) k.succ) z).toReal) := by
  classical
  set c := blockMarkovCode k₀ C C₁ φ ψ
  set x := genieInput k₀ C C₁ w
  have hne : ∀ y, c.seqProb W w y ≠ ∞ := fun y =>
    ENNReal.prod_ne_top fun _ _ => PMF.apply_ne_top _ _
  have h0 : (c.errorProb W w).toReal = ∑ y, (if c.dec (fun i => (y i).1) ≠ w then
      (c.seqProb W w y).toReal else 0) := by
    rw [RelayCode.errorProb, ENNReal.toReal_sum fun y _ => by split_ifs <;> simp [hne]]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : c.dec (fun i => (y i).1) = w <;> simp [h]
  have hf : ∑ y, (c.seqProb W w y).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun y _ => hne y, RelayCode.sum_seqProb, ENNReal.toReal_one]
  have hg : ∑ y, (DMC.blockProb W x y).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun y _ => DMC.blockProb_ne_top _ _ _, DMC.sum_blockProb_eq_one,
      ENNReal.toReal_one]
  have h1 := sum_ite_le_of_agree (fun y => (c.seqProb W w y).toReal)
    (fun y => (DMC.blockProb W x y).toReal) hf hg
    (fun y => ∀ b : Fin (nb + 1), relayEstimate k₀ φ (fun t => (y t).2) b = previousMessage k₀ w b)
    (fun y => c.dec (fun i => (y i).1) ≠ w)
    (fun y hy => by rw [seqProb_eq_of_good k₀ C C₁ φ ψ W w y hy]) fun y => ENNReal.toReal_nonneg
  rw [h0]
  refine h1.trans ?_
  have h2 : ∀ y, (if c.dec (fun i => (y i).1) ≠ w ∨ ¬∀ b : Fin (nb + 1),
      relayEstimate k₀ φ (fun t => (y t).2) b = previousMessage k₀ w b then
        (DMC.blockProb W x y).toReal else 0) ≤
      ∑ k : Fin nb, (if φ (previousMessage k₀ w k.castSucc)
        (fun j => (blockOf y k.castSucc j).2) ≠ w k then (DMC.blockProb W x y).toReal else 0) +
      ∑ k : Fin nb, (if ψ (currentMessage k₀ w k.succ)
        (fun j => (blockOf y k.succ j).1) ≠ w k then (DMC.blockProb W x y).toReal else 0) := by
    intro y
    have hb : 0 ≤ (DMC.blockProb W x y).toReal := ENNReal.toReal_nonneg
    have hs1 : 0 ≤ ∑ k : Fin nb, (if φ (previousMessage k₀ w k.castSucc)
        (fun j => (blockOf y k.castSucc j).2) ≠ w k then (DMC.blockProb W x y).toReal else 0) :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> simp [hb]
    have hs2 : 0 ≤ ∑ k : Fin nb, (if ψ (currentMessage k₀ w k.succ)
        (fun j => (blockOf y k.succ j).1) ≠ w k then (DMC.blockProb W x y).toReal else 0) :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> simp [hb]
    by_cases hR : ∃ k : Fin nb, φ (previousMessage k₀ w k.castSucc)
        (fun j => (blockOf y k.castSucc j).2) ≠ w k
    · obtain ⟨k, hk⟩ := hR
      have := Finset.single_le_sum (f := fun k : Fin nb => if φ (previousMessage k₀ w k.castSucc)
        (fun j => (blockOf y k.castSucc j).2) ≠ w k then (DMC.blockProb W x y).toReal else 0)
        (fun _ _ => by split_ifs <;> simp [hb]) (Finset.mem_univ k)
      simp only [hk, ne_eq, not_false_eq_true, ite_true] at this
      split_ifs <;> linarith
    by_cases hD : ∃ k : Fin nb, ψ (currentMessage k₀ w k.succ)
        (fun j => (blockOf y k.succ j).1) ≠ w k
    · obtain ⟨k, hk⟩ := hD
      have := Finset.single_le_sum (f := fun k : Fin nb => if ψ (currentMessage k₀ w k.succ)
        (fun j => (blockOf y k.succ j).1) ≠ w k then (DMC.blockProb W x y).toReal else 0)
        (fun _ _ => by split_ifs <;> simp [hb]) (Finset.mem_univ k)
      simp only [hk, ne_eq, not_false_eq_true, ite_true] at this
      split_ifs <;> linarith
    push Not at hR hD
    have hG := good_of_relay k₀ φ w (fun t => (y t).2) hR
    have hE := dec_of_dest (B₁ := B₁) k₀ C C₁ φ ψ w (fun t => (y t).1) hD
    rw [ite_eq_right (by simp only [ne_eq, not_or, not_not]; exact ⟨hE, hG⟩)]
    linarith
  refine (Finset.sum_le_sum fun y _ => h2 y).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.sum_comm]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_block_marginal W x k.castSucc Prod.snd
      (fun z => φ (previousMessage k₀ w k.castSucc) z ≠ w k)]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h : φ (previousMessage k₀ w k.castSucc) z = w k <;> simp [h]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_block_marginal W x k.succ Prod.fst
      (fun z => ψ (currentMessage k₀ w k.succ) z ≠ w k)]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h : ψ (currentMessage k₀ w k.succ) z = w k <;> simp [h]

end Bound

noncomputable def satLaw (pX : A₁ → PMF A) : A₁ → PMF (A₁ × A) :=
  fun u => (pX u).map fun x => (u, x)

noncomputable def relayBC (W : DMC (A × A₁) (B × B₁)) : DMC (A₁ × A) (B₁ × B) :=
  fun x => (W (x.2, x.1)).map Prod.swap

def destBC (W : DMC (A × A₁) (B × B₁)) : DMC (A₁ × A) (B × B₁) :=
  fun x => W (x.2, x.1)

theorem channel₁_relayBC (W : DMC (A × A₁) (B × B₁)) (x : A₁ × A) :
    BC.channel₁ (relayBC W) x = (W (x.2, x.1)).map Prod.snd := by
  simp only [BC.channel₁, relayBC, PMF.map_comp]
  rfl

theorem fst_eq_of_codebookWeight_ne_zero {n : ℕ} [Fintype K] (pU : PMF A₁) (pX : A₁ → PMF A)
    (Cu : K → Fin n → A₁) (Cx : K × K → Fin n → A₁ × A)
    (h : BC.codebookWeight pU (satLaw pX) Cu Cx ≠ 0) (m : K × K) (j : Fin n) :
    (Cx m j).1 = Cu m.2 j := by
  classical
  have h2 : ∏ m, (DMC.blockProb (satLaw pX) (Cu m.2) (Cx m)).toReal ≠ 0 := fun h0 =>
    h (by rw [BC.codebookWeight, h0, mul_zero])
  have h3 := (Finset.prod_ne_zero_iff.1 h2) m (Finset.mem_univ _)
  rw [DMC.toReal_blockProb] at h3
  have h4 := (Finset.prod_ne_zero_iff.1 h3) j (Finset.mem_univ _)
  have h5 : Cx m j ∈ (satLaw pX (Cu m.2 j)).support := by
    rw [PMF.mem_support_iff]
    intro h0
    exact h4 (by rw [h0, ENNReal.toReal_zero])
  rw [satLaw, PMF.support_map] at h5
  obtain ⟨x, -, hx⟩ := h5
  rw [← hx]

section Random

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype K] [DecidableEq K] {m : ℕ}

omit [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] in
theorem sum_codebookWeight_relayError (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁)
    (pX : A₁ → PMF A) (ε : ℝ) (k₀ a b : K) :
    ∑ Cu : K → Fin m → A₁, ∑ Cx : K × K → Fin m → A₁ × A,
      BC.codebookWeight pU (satLaw pX) Cu Cx *
      ∑ z, (if BlockCode.typicalDecoder (fun a i => (Cu b i, Cx (a, b) i))
          (superpositionTypicalSet (BC.law₁ (relayBC W) pU (satLaw pX)) m ε) k₀ z = a then 0
        else (DMC.blockProb (fun x => (W x).map Prod.snd)
          (fun j => ((Cx (a, b) j).2, Cu b j)) z).toReal) ≤
      (1 - ∑ z ∈ superpositionTypicalSet (BC.law₁ (relayBC W) pU (satLaw pX)) m ε,
          iidProb (BC.law₁ (relayBC W) pU (satLaw pX)) (fun i => (z.1 i, z.2 i))) +
        (Fintype.card K - 1) * Real.exp (-(m * (I[fun ω : (A₁ × A₁ × A) × B₁ => ω.1.2 :
          fun ω => ω.2 | fun ω => ω.1.1 ;
          (BC.law₁ (relayBC W) pU (satLaw pX)).toMeasure] - 4 * ε))) := by
  classical
  set J := superpositionTypicalSet (BC.law₁ (relayBC W) pU (satLaw pX)) m ε
  have hsupp : ∀ (Cu : K → Fin m → A₁) (Cx : K × K → Fin m → A₁ × A),
      BC.codebookWeight pU (satLaw pX) Cu Cx *
      ∑ z, (if BlockCode.typicalDecoder (fun a i => (Cu b i, Cx (a, b) i)) J k₀ z = a then 0
        else (DMC.blockProb (fun x => (W x).map Prod.snd)
          (fun j => ((Cx (a, b) j).2, Cu b j)) z).toReal) ≤
      BC.codebookWeight pU (satLaw pX) Cu Cx *
        (∑ z, (if ((fun i => (Cu (a, b).2 i, Cx (a, b) i)), z) ∈ J then 0
          else (DMC.blockProb (BC.channel₁ (relayBC W)) (Cx (a, b)) z).toReal) +
        ∑ a' with a' ≠ a, ∑ z, (if ((fun i => (Cu (a', b).2 i, Cx (a', b) i)), z) ∈ J
          then (1 : ℝ) else 0) *
            (DMC.blockProb (BC.channel₁ (relayBC W)) (Cx (a, b)) z).toReal) := by
    intro Cu Cx
    by_cases hw : BC.codebookWeight pU (satLaw pX) Cu Cx = 0
    · simp [hw]
    refine mul_le_mul_of_nonneg_left ?_ (BC.codebookWeight_nonneg _ _ _ _)
    have he : ∀ z, DMC.blockProb (fun x => (W x).map Prod.snd)
        (fun j => ((Cx (a, b) j).2, Cu b j)) z =
        DMC.blockProb (BC.channel₁ (relayBC W)) (Cx (a, b)) z := fun z => by
      simp only [DMC.blockProb, channel₁_relayBC,
        fst_eq_of_codebookWeight_ne_zero pU pX Cu Cx hw (a, b)]
    simp_rw [he]
    rw [Finset.sum_comm (s := Finset.univ.filter fun a' => a' ≠ a), ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    exact BlockCode.ite_comp_typicalDecoder_le id (fun a i => (Cu b i, Cx (a, b) i)) J k₀ a z
      ENNReal.toReal_nonneg
  refine (Finset.sum_le_sum fun Cu _ => Finset.sum_le_sum fun Cx _ => hsupp Cu Cx).trans ?_
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hmiss := BC.sum_codebookWeight_mul_miss (relayBC W) pU (satLaw pX) J (a, b)
  simp only [Finset.mul_sum] at hmiss
  rw [hmiss]
  have hcl : ∀ a' ∈ Finset.univ.filter fun a' => a' ≠ a,
      ∑ Cu : K → Fin m → A₁, ∑ Cx : K × K → Fin m → A₁ × A, ∑ z,
        BC.codebookWeight pU (satLaw pX) Cu Cx *
        ((if ((fun i => (Cu (a', b).2 i, Cx (a', b) i)), z) ∈ J then (1 : ℝ) else 0) *
          (DMC.blockProb (BC.channel₁ (relayBC W)) (Cx (a, b)) z).toReal) ≤
      Real.exp (-(m * (I[fun ω : (A₁ × A₁ × A) × B₁ => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
          (BC.law₁ (relayBC W) pU (satLaw pX)).toMeasure] - 4 * ε))) := fun a' ha' => by
    have := BC.sum_codebookWeight_mul_same_cloud (relayBC W) pU (satLaw pX) ε
      (m := (a, b)) (m' := (a', b)) (n := m) (Finset.mem_filter.1 ha').2 rfl
    simpa only [Finset.mul_sum] using this
  have : Nonempty K := ⟨a⟩
  have hcard : ((Finset.univ.filter fun a' : K => a' ≠ a).card : ℝ) = Fintype.card K - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have hsw : ∑ Cu : K → Fin m → A₁, ∑ Cx : K × K → Fin m → A₁ × A,
      ∑ a' ∈ Finset.univ.filter (fun a' : K => a' ≠ a), ∑ z,
        BC.codebookWeight pU (satLaw pX) Cu Cx *
        ((if ((fun i => (Cu (a', b).2 i, Cx (a', b) i)), z) ∈ J then (1 : ℝ) else 0) *
          (DMC.blockProb (BC.channel₁ (relayBC W)) (Cx (a, b)) z).toReal) =
      ∑ a' ∈ Finset.univ.filter (fun a' : K => a' ≠ a), ∑ Cu : K → Fin m → A₁,
        ∑ Cx : K × K → Fin m → A₁ × A, ∑ z, BC.codebookWeight pU (satLaw pX) Cu Cx *
        ((if ((fun i => (Cu (a', b).2 i, Cx (a', b) i)), z) ∈ J then (1 : ℝ) else 0) *
          (DMC.blockProb (BC.channel₁ (relayBC W)) (Cx (a, b)) z).toReal) := by
    exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
  rw [hsw]
  have := Finset.sum_le_sum hcl
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at this
  linarith

omit [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁] in
theorem sum_codebookWeight_destError (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁)
    (pX : A₁ → PMF A) (ε : ℝ) (k₀ a' a : K) :
    ∑ Cu : K → Fin m → A₁, ∑ Cx : K × K → Fin m → A₁ × A,
      BC.codebookWeight pU (satLaw pX) Cu Cx *
      ∑ z, (if BlockCode.typicalDecoder (fun b i => (Cu b i, Cx (a', b) i))
          (superpositionTypicalSet (BC.law₁ (destBC W) pU (satLaw pX)) m ε) k₀ z = a then 0
        else (DMC.blockProb (fun x => (W x).map Prod.fst)
          (fun j => ((Cx (a', a) j).2, Cu a j)) z).toReal) ≤
      (1 - ∑ z ∈ superpositionTypicalSet (BC.law₁ (destBC W) pU (satLaw pX)) m ε,
          iidProb (BC.law₁ (destBC W) pU (satLaw pX)) (fun i => (z.1 i, z.2 i))) +
        (Fintype.card K - 1) * Real.exp (-(m * (I[fun ω : (A₁ × A₁ × A) × B => ω.1.2 :
          fun ω => ω.2 ; (BC.law₁ (destBC W) pU (satLaw pX)).toMeasure] - 3 * ε))) := by
  classical
  set J := superpositionTypicalSet (BC.law₁ (destBC W) pU (satLaw pX)) m ε
  have hsupp : ∀ (Cu : K → Fin m → A₁) (Cx : K × K → Fin m → A₁ × A),
      BC.codebookWeight pU (satLaw pX) Cu Cx *
      ∑ z, (if BlockCode.typicalDecoder (fun b i => (Cu b i, Cx (a', b) i)) J k₀ z = a then 0
        else (DMC.blockProb (fun x => (W x).map Prod.fst)
          (fun j => ((Cx (a', a) j).2, Cu a j)) z).toReal) ≤
      BC.codebookWeight pU (satLaw pX) Cu Cx *
        (∑ z, (if ((fun i => (Cu (a', a).2 i, Cx (a', a) i)), z) ∈ J then 0
          else (DMC.blockProb (BC.channel₁ (destBC W)) (Cx (a', a)) z).toReal) +
        ∑ b with b ≠ a, ∑ z, (if ((fun i => (Cu (a', b).2 i, Cx (a', b) i)), z) ∈ J
          then (1 : ℝ) else 0) *
            (DMC.blockProb (BC.channel₁ (destBC W)) (Cx (a', a)) z).toReal) := by
    intro Cu Cx
    by_cases hw : BC.codebookWeight pU (satLaw pX) Cu Cx = 0
    · simp [hw]
    refine mul_le_mul_of_nonneg_left ?_ (BC.codebookWeight_nonneg _ _ _ _)
    have he : ∀ z, DMC.blockProb (fun x => (W x).map Prod.fst)
        (fun j => ((Cx (a', a) j).2, Cu a j)) z =
        DMC.blockProb (BC.channel₁ (destBC W)) (Cx (a', a)) z := fun z => by
      simp only [DMC.blockProb, BC.channel₁, destBC,
        fst_eq_of_codebookWeight_ne_zero pU pX Cu Cx hw (a', a)]
    simp_rw [he]
    rw [Finset.sum_comm (s := Finset.univ.filter fun b => b ≠ a), ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    exact BlockCode.ite_comp_typicalDecoder_le id (fun b i => (Cu b i, Cx (a', b) i)) J k₀ a z
      ENNReal.toReal_nonneg
  refine (Finset.sum_le_sum fun Cu _ => Finset.sum_le_sum fun Cx _ => hsupp Cu Cx).trans ?_
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hmiss := BC.sum_codebookWeight_mul_miss (destBC W) pU (satLaw pX) J (a', a)
  simp only [Finset.mul_sum] at hmiss
  rw [hmiss]
  have hcl : ∀ b ∈ Finset.univ.filter fun b => b ≠ a,
      ∑ Cu : K → Fin m → A₁, ∑ Cx : K × K → Fin m → A₁ × A, ∑ z,
        BC.codebookWeight pU (satLaw pX) Cu Cx *
        ((if ((fun i => (Cu (a', b).2 i, Cx (a', b) i)), z) ∈ J then (1 : ℝ) else 0) *
          (DMC.blockProb (BC.channel₁ (destBC W)) (Cx (a', a)) z).toReal) ≤
      Real.exp (-(m * (I[fun ω : (A₁ × A₁ × A) × B => ω.1.2 : fun ω => ω.2 ;
          (BC.law₁ (destBC W) pU (satLaw pX)).toMeasure] - 3 * ε))) := fun b hb => by
    have := BC.sum_codebookWeight_mul_other_cloud (destBC W) pU (satLaw pX) ε
      (m := (a', a)) (m' := (a', b)) (n := m) (Finset.mem_filter.1 hb).2
    simpa only [Finset.mul_sum] using this
  have : Nonempty K := ⟨a⟩
  have hcard : ((Finset.univ.filter fun b : K => b ≠ a).card : ℝ) = Fintype.card K - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have hsw : ∑ Cu : K → Fin m → A₁, ∑ Cx : K × K → Fin m → A₁ × A,
      ∑ b ∈ Finset.univ.filter (fun b : K => b ≠ a), ∑ z,
        BC.codebookWeight pU (satLaw pX) Cu Cx *
        ((if ((fun i => (Cu (a', b).2 i, Cx (a', b) i)), z) ∈ J then (1 : ℝ) else 0) *
          (DMC.blockProb (BC.channel₁ (destBC W)) (Cx (a', a)) z).toReal) =
      ∑ b ∈ Finset.univ.filter (fun b : K => b ≠ a), ∑ Cu : K → Fin m → A₁,
        ∑ Cx : K × K → Fin m → A₁ × A, ∑ z, BC.codebookWeight pU (satLaw pX) Cu Cx *
        ((if ((fun i => (Cu (a', b).2 i, Cx (a', b) i)), z) ∈ J then (1 : ℝ) else 0) *
          (DMC.blockProb (BC.channel₁ (destBC W)) (Cx (a', a)) z).toReal) :=
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
  rw [hsw]
  have := Finset.sum_le_sum hcl
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at this
  linarith

end Random

theorem currentMessage_castSucc {nb : ℕ} (k₀ : K) (w : Fin nb → K) (k : Fin nb) :
    currentMessage k₀ w k.castSucc = w k := by
  simp [currentMessage]

theorem previousMessage_succ {nb : ℕ} (k₀ : K) (w : Fin nb → K) (k : Fin nb) :
    previousMessage k₀ w k.succ = w k := by
  simp [previousMessage]

section Exists

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype B₁] [Nonempty B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [Fintype K] [DecidableEq K] {nb m : ℕ}

noncomputable def relayDecoder (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁) (pX : A₁ → PMF A)
    (ε : ℝ) (k₀ : K) (Cu : K → Fin m → A₁) (Cx : K × K → Fin m → A₁ × A) (b : K)
    (z : Fin m → B₁) : K :=
  BlockCode.typicalDecoder (fun a i => (Cu b i, Cx (a, b) i))
    (superpositionTypicalSet (BC.law₁ (relayBC W) pU (satLaw pX)) m ε) k₀ z

noncomputable def destDecoder (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁) (pX : A₁ → PMF A)
    (ε : ℝ) (k₀ : K) (Cu : K → Fin m → A₁) (Cx : K × K → Fin m → A₁ × A) (a : K)
    (z : Fin m → B) : K :=
  BlockCode.typicalDecoder (fun b i => (Cu b i, Cx (a, b) i))
    (superpositionTypicalSet (BC.law₁ (destBC W) pU (satLaw pX)) m ε) k₀ z

noncomputable def dfCode (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁) (pX : A₁ → PMF A) (ε : ℝ)
    (k₀ : K) (Cu : K → Fin m → A₁) (Cx : K × K → Fin m → A₁ × A) :
    RelayCode (Fin nb → K) A A₁ B B₁ ((nb + 1) * m) :=
  blockMarkovCode k₀ (fun a b j => (Cx (a, b) j).2) Cu (relayDecoder W pU pX ε k₀ Cu Cx)
    (destDecoder W pU pX ε k₀ Cu Cx)

noncomputable def dfBound (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁) (pX : A₁ → PMF A) (ε : ℝ)
    (nb m k : ℕ) : ℝ :=
  nb * ((1 - ∑ z ∈ superpositionTypicalSet (BC.law₁ (relayBC W) pU (satLaw pX)) m ε,
      iidProb (BC.law₁ (relayBC W) pU (satLaw pX)) (fun i => (z.1 i, z.2 i))) +
    (k - 1) * Real.exp (-(m * (I[fun ω : (A₁ × A₁ × A) × B₁ => ω.1.2 : fun ω => ω.2 |
      fun ω => ω.1.1 ; (BC.law₁ (relayBC W) pU (satLaw pX)).toMeasure] - 4 * ε)))) +
  nb * ((1 - ∑ z ∈ superpositionTypicalSet (BC.law₁ (destBC W) pU (satLaw pX)) m ε,
      iidProb (BC.law₁ (destBC W) pU (satLaw pX)) (fun i => (z.1 i, z.2 i))) +
    (k - 1) * Real.exp (-(m * (I[fun ω : (A₁ × A₁ × A) × B => ω.1.2 : fun ω => ω.2 ;
      (BC.law₁ (destBC W) pU (satLaw pX)).toMeasure] - 3 * ε))))

theorem sum_codebookWeight_errorProb_dfCode_le (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁)
    (pX : A₁ → PMF A) (ε : ℝ) (k₀ : K) (w : Fin nb → K) :
    ∑ Cu : K → Fin m → A₁, ∑ Cx : K × K → Fin m → A₁ × A,
      BC.codebookWeight pU (satLaw pX) Cu Cx *
        ((dfCode (nb := nb) W pU pX ε k₀ Cu Cx).errorProb W w).toReal ≤
      dfBound W pU pX ε nb m (Fintype.card K) := by
  classical
  set R : (K → Fin m → A₁) → (K × K → Fin m → A₁ × A) → Fin nb → ℝ := fun Cu Cx k =>
    ∑ z, (if relayDecoder W pU pX ε k₀ Cu Cx (previousMessage k₀ w k.castSucc) z = w k
      then 0 else (DMC.blockProb (fun x => (W x).map Prod.snd)
        (fun j => ((Cx (w k, previousMessage k₀ w k.castSucc) j).2,
          Cu (previousMessage k₀ w k.castSucc) j)) z).toReal) with hR
  set D : (K → Fin m → A₁) → (K × K → Fin m → A₁ × A) → Fin nb → ℝ := fun Cu Cx k =>
    ∑ z, (if destDecoder W pU pX ε k₀ Cu Cx (currentMessage k₀ w k.succ) z = w k
      then 0 else (DMC.blockProb (fun x => (W x).map Prod.fst)
        (fun j => ((Cx (currentMessage k₀ w k.succ, w k) j).2, Cu (w k) j)) z).toReal) with hD
  have h1 : ∀ Cu Cx, ((dfCode (nb := nb) W pU pX ε k₀ Cu Cx).errorProb W w).toReal ≤
      ∑ k, R Cu Cx k + ∑ k, D Cu Cx k := fun Cu Cx => by
    have h := errorProb_blockMarkov_le k₀ (fun a b j => (Cx (a, b) j).2) Cu
      (relayDecoder W pU pX ε k₀ Cu Cx) (destDecoder W pU pX ε k₀ Cu Cx) W w
    simp only [blockOf_genieInput, currentMessage_castSucc, previousMessage_succ] at h
    exact h
  calc _ ≤ ∑ Cu : K → Fin m → A₁, ∑ Cx : K × K → Fin m → A₁ × A,
        BC.codebookWeight pU (satLaw pX) Cu Cx * (∑ k, R Cu Cx k + ∑ k, D Cu Cx k) :=
        Finset.sum_le_sum fun Cu _ => Finset.sum_le_sum fun Cx _ =>
          mul_le_mul_of_nonneg_left (h1 Cu Cx) (BC.codebookWeight_nonneg _ _ _ _)
    _ = ∑ k, (∑ Cu : K → Fin m → A₁, ∑ Cx : K × K → Fin m → A₁ × A,
          BC.codebookWeight pU (satLaw pX) Cu Cx * R Cu Cx k) +
        ∑ k, (∑ Cu : K → Fin m → A₁, ∑ Cx : K × K → Fin m → A₁ × A,
          BC.codebookWeight pU (satLaw pX) Cu Cx * D Cu Cx k) := by
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        congr 1
        · exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
        · exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
    _ ≤ _ := by
        rw [dfBound]
        refine add_le_add ?_ ?_
        · refine (Finset.sum_le_sum fun k _ => sum_codebookWeight_relayError W pU pX ε k₀ (w k)
            (previousMessage k₀ w k.castSucc)).trans (le_of_eq ?_)
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        · refine (Finset.sum_le_sum fun k _ => sum_codebookWeight_destError W pU pX ε k₀
            (currentMessage k₀ w k.succ) (w k)).trans (le_of_eq ?_)
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem exists_dfCode_avgError_le (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁)
    (pX : A₁ → PMF A) (ε : ℝ) (k₀ : K) :
    ∃ (Cu : K → Fin m → A₁) (Cx : K × K → Fin m → A₁ × A),
      (dfCode (nb := nb) W pU pX ε k₀ Cu Cx).avgError W ≤
        ENNReal.ofReal (dfBound W pU pX ε nb m (Fintype.card K)) := by
  classical
  have : Nonempty K := ⟨k₀⟩
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le
    (w := fun C : (K → Fin m → A₁) × (K × K → Fin m → A₁ × A) =>
      BC.codebookWeight pU (satLaw pX) C.1 C.2)
    (f := fun C => ∑ w, ((dfCode (nb := nb) W pU pX ε k₀ C.1 C.2).errorProb W w).toReal)
    (t := Fintype.card (Fin nb → K) * dfBound W pU pX ε nb m (Fintype.card K))
    (fun C => BC.codebookWeight_nonneg _ _ C.1 C.2)
    (by rw [Fintype.sum_prod_type]; exact BC.sum_codebookWeight pU (satLaw pX)) (by
      rw [Fintype.sum_prod_type]
      simp_rw [Finset.mul_sum]
      calc _ = ∑ w : Fin nb → K, ∑ Cu : K → Fin m → A₁, ∑ Cx : K × K → Fin m → A₁ × A,
            BC.codebookWeight pU (satLaw pX) Cu Cx *
              ((dfCode (nb := nb) W pU pX ε k₀ Cu Cx).errorProb W w).toReal := by
            exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
        _ ≤ ∑ w : Fin nb → K, dfBound W pU pX ε nb m (Fintype.card K) :=
            Finset.sum_le_sum fun w _ => sum_codebookWeight_errorProb_dfCode_le W pU pX ε k₀ w
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
  exact ⟨C.1, C.2, RelayCode.avgError_le_ofReal _ W hC⟩

end Exists

end Relay

end Meat
