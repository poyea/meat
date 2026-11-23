import Meat.Channel.MultipleAccessK

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

structure BCKCode {K : ℕ} (M : Fin K → Type*) (A : Type*) (B : Fin K → Type*) (n : ℕ) where
  enc : (∀ k, M k) → Fin n → A
  dec : ∀ k, (Fin n → B k) → M k

namespace BCKCode

variable {K : ℕ} {M : Fin K → Type*} {A : Type*} {B : Fin K → Type*} {n : ℕ}

def decode (c : BCKCode M A B n) (y : Fin n → ∀ k, B k) : ∀ k, M k :=
  fun k => c.dec k fun i => y i k

noncomputable def errorProb [∀ k, Fintype (B k)] [∀ k, DecidableEq (M k)]
    (c : BCKCode M A B n) (W : DMC A (∀ k, B k)) (m : ∀ k, M k) : ℝ≥0∞ :=
  ∑ y : Fin n → ∀ k, B k, if c.decode y = m then 0 else DMC.blockProb W (c.enc m) y

noncomputable def avgError [∀ k, Fintype (B k)] [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]
    (c : BCKCode M A B n) (W : DMC A (∀ k, B k)) : ℝ≥0∞ :=
  (∑ m : ∀ k, M k, c.errorProb W m) / ∏ k, (Fintype.card (M k) : ℝ≥0∞)

end BCKCode

namespace BCK

variable {K : ℕ} {A : Type*} {B : Fin K → Type*}

def Achievable [∀ k, Fintype (B k)] (W : DMC A (∀ k, B k)) (R : Fin K → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ L : Fin K → ℕ, (∀ k, Real.exp (n * R k) ≤ L k) ∧
      ∃ c : BCKCode (fun k => Fin (L k)) A B n, c.avgError W ≤ ε

def achievableRegion [∀ k, Fintype (B k)] (W : DMC A (∀ k, B k)) : Set (Fin K → ℝ) :=
  {R | (∀ k, 0 ≤ R k) ∧ Achievable W R}

noncomputable def out (W : DMC A (∀ k, B k)) (k : Fin K) : DMC A (B k) :=
  fun a => (W a).map fun b => b k

def IsDegraded (W : DMC A (∀ k, B k)) : Prop :=
  ∀ k j : Fin K, k ≤ j → ∃ D : DMC (B k) (B j), ∀ a, out W j a = (out W k a).bind D

def layer (k : Fin K) : Finset (Fin K) :=
  univ.filter fun j => k ≤ j

def above (k : Fin K) : Finset (Fin K) :=
  univ.filter fun j => k < j

variable [NeZero K] {V : Fin K → Type*}

noncomputable def layerPMF (W : DMC A (∀ k, B k)) (law : PMF (∀ j, V j)) (f : V 0 → A) :
    PMF ((∀ j, V j) × ∀ k, B k) :=
  law.bind fun v => (W (f (v 0))).map fun y => (v, y)

variable [∀ j, Fintype (V j)] [∀ j, MeasurableSpace (V j)] [∀ k, Fintype (B k)]
  [∀ k, MeasurableSpace (B k)]

noncomputable def superpositionRegion (W : DMC A (∀ k, B k)) (law : PMF (∀ j, V j))
    (f : V 0 → A) : Set (Fin K → ℝ) :=
  {R | (∀ k, 0 ≤ R k) ∧ ∀ k, R k ≤
    I[fun ω : (∀ j, V j) × (∀ k, B k) => MACK.mask (layer k) ω.1 : fun ω => ω.2 k |
      fun ω => MACK.mask (above k) ω.1 ; (layerPMF W law f).toMeasure]}

noncomputable def superpositionUnion (W : DMC A (∀ k, B k)) : Set (Fin K → ℝ) :=
  ⋃ (s : Fin K → ℕ) (law : PMF (∀ j, Fin (s j))) (f : Fin (s 0) → A),
    superpositionRegion W law f

end BCK

end Meat
