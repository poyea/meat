import Meat.Channel.Basic
import Meat.Shannon.Typical

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

noncomputable def piPMF {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (p : ∀ i, PMF (A i)) : PMF (∀ i, A i) :=
  PMF.ofFintype (fun x => ∏ i, p i (x i)) (by
    rw [← Fintype.prod_sum]
    exact prod_eq_one fun i _ => sum_pmf_eq_one (p i))

structure MACKCode {K : ℕ} (M A : Fin K → Type*) (B : Type*) (n : ℕ) where
  enc : ∀ k, M k → Fin n → A k
  dec : (Fin n → B) → ∀ k, M k

namespace MACKCode

variable {K : ℕ} {M A : Fin K → Type*} {B : Type*} {n : ℕ}

def input (c : MACKCode M A B n) (m : ∀ k, M k) : Fin n → ∀ k, A k :=
  fun i k => c.enc k (m k) i

noncomputable def errorProb [Fintype B] [∀ k, DecidableEq (M k)] (c : MACKCode M A B n)
    (W : DMC (∀ k, A k) B) (m : ∀ k, M k) : ℝ≥0∞ :=
  ∑ y : Fin n → B, if c.dec y = m then 0 else DMC.blockProb W (c.input m) y

noncomputable def avgError [Fintype B] [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]
    (c : MACKCode M A B n) (W : DMC (∀ k, A k) B) : ℝ≥0∞ :=
  (∑ m : ∀ k, M k, c.errorProb W m) / ∏ k, (Fintype.card (M k) : ℝ≥0∞)

end MACKCode

namespace MACK

variable {K : ℕ} {A : Fin K → Type*} {B : Type*}

def Achievable [Fintype B] (W : DMC (∀ k, A k) B) (R : Fin K → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ L : Fin K → ℕ, (∀ k, Real.exp (n * R k) ≤ L k) ∧
      ∃ c : MACKCode (fun k => Fin (L k)) A B n, c.avgError W ≤ ε

def achievableRegion [Fintype B] (W : DMC (∀ k, A k) B) : Set (Fin K → ℝ) :=
  {R | (∀ k, 0 ≤ R k) ∧ Achievable W R}

def Masked (A : Fin K → Type*) : Type _ := ∀ k, Option (A k)

instance : MeasurableSpace (Masked A) := ⊤

instance : MeasurableSingletonClass (Masked A) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance [∀ k, Fintype (A k)] : Fintype (Masked A) :=
  inferInstanceAs (Fintype (∀ k, Option (A k)))

def mask (S : Finset (Fin K)) (x : ∀ k, A k) : Masked A :=
  fun k => if k ∈ S then some (x k) else none

variable [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)] [Fintype B] [MeasurableSpace B]

noncomputable def subsetInfo (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) (S : Finset (Fin K)) :
    ℝ :=
  I[fun ω : (∀ k, A k) × B => mask S ω.1 : Prod.snd | fun ω => mask Sᶜ ω.1 ;
    W.jointMeasure (piPMF p)]

def polymatroid (W : DMC (∀ k, A k) B) (p : ∀ k, PMF (A k)) : Set (Fin K → ℝ) :=
  {R | (∀ k, 0 ≤ R k) ∧ ∀ S : Finset (Fin K), ∑ k ∈ S, R k ≤ subsetInfo W p S}

noncomputable def capacityRegion (W : DMC (∀ k, A k) B) : Set (Fin K → ℝ) :=
  closure (convexHull ℝ (⋃ p : ∀ k, PMF (A k), polymatroid W p))

end MACK

end Meat
