import Meat.Channel.MultipleAccessTheorem
import Meat.Open.EntropicFormula

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

structure ICCode (M₁ M₂ A₁ A₂ B₁ B₂ : Type*) (n : ℕ) where
  enc₁ : M₁ → Fin n → A₁
  enc₂ : M₂ → Fin n → A₂
  dec₁ : (Fin n → B₁) → M₁
  dec₂ : (Fin n → B₂) → M₂

namespace ICCode

variable {M₁ M₂ A₁ A₂ B₁ B₂ : Type*} {n : ℕ}

noncomputable def errorProb [Fintype B₁] [Fintype B₂] [DecidableEq M₁] [DecidableEq M₂]
    (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n) (W : DMC (A₁ × A₂) (B₁ × B₂)) (m : M₁ × M₂) : ℝ≥0∞ :=
  ∑ y : Fin n → B₁ × B₂,
    if (c.dec₁ (fun i => (y i).1), c.dec₂ (fun i => (y i).2)) = m then 0
    else DMC.blockProb W (fun i => (c.enc₁ m.1 i, c.enc₂ m.2 i)) y

noncomputable def avgError [Fintype B₁] [Fintype B₂] [Fintype M₁] [Fintype M₂]
    [DecidableEq M₁] [DecidableEq M₂]
    (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n) (W : DMC (A₁ × A₂) (B₁ × B₂)) : ℝ≥0∞ :=
  (∑ m : M₁ × M₂, c.errorProb W m) / ((Fintype.card M₁ : ℝ≥0∞) * (Fintype.card M₂ : ℝ≥0∞))

def toMACCode (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n) : MACCode M₁ M₂ A₁ A₂ (B₁ × B₂) n :=
  ⟨c.enc₁, c.enc₂, fun y => (c.dec₁ fun i => (y i).1, c.dec₂ fun i => (y i).2)⟩

theorem errorProb_toMACCode [Fintype B₁] [Fintype B₂] [DecidableEq M₁] [DecidableEq M₂]
    (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n) (W : DMC (A₁ × A₂) (B₁ × B₂)) (m : M₁ × M₂) :
    c.toMACCode.errorProb W m = c.errorProb W m := rfl

theorem avgError_toMACCode [Fintype B₁] [Fintype B₂] [Fintype M₁] [Fintype M₂]
    [DecidableEq M₁] [DecidableEq M₂]
    (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n) (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    c.toMACCode.avgError W = c.avgError W := rfl

end ICCode

namespace IC

variable {A₁ A₂ B₁ B₂ : Type*}

def Achievable [Fintype B₁] [Fintype B₂] (W : DMC (A₁ × A₂) (B₁ × B₂)) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k₁ k₂ : ℕ, Real.exp (n * R₁) ≤ k₁ ∧ Real.exp (n * R₂) ≤ k₂ ∧
      ∃ c : ICCode (Fin k₁) (Fin k₂) A₁ A₂ B₁ B₂ n, c.avgError W ≤ ε

def achievableRegion [Fintype B₁] [Fintype B₂] (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ Achievable W R.1 R.2}

noncomputable def out₁ (W : DMC (A₁ × A₂) (B₁ × B₂)) : DMC (A₁ × A₂) B₁ :=
  fun a => (W a).map Prod.fst

noncomputable def out₂ (W : DMC (A₁ × A₂) (B₁ × B₂)) : DMC (A₁ × A₂) B₂ :=
  fun a => (W a).map Prod.snd

def SingleLetterCapacity : Prop :=
  ∃ (m : ℕ) (κ : ℕ → ℕ → ℕ → ℕ → ℕ) (F : EntropicFormula m 4),
    ∀ (A₁ A₂ B₁ B₂ : Type) [Fintype A₁] [Fintype A₂] [Fintype B₁] [Fintype B₂]
      [Nonempty A₁] [Nonempty A₂] (W : DMC (A₁ × A₂) (B₁ × B₂)),
      closure (achievableRegion W) =
        F.value (EntropicFormula.letterLaw₄ (m := m)
          (k := κ (Fintype.card A₁) (Fintype.card A₂) (Fintype.card B₁) (Fintype.card B₂)) W)

variable [Fintype A₁] [MeasurableSpace A₁] [Fintype A₂] [MeasurableSpace A₂]
  [Fintype B₁] [MeasurableSpace B₁] [Fintype B₂] [MeasurableSpace B₂]

noncomputable def compoundRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ (⋃ p₁ : PMF A₁, ⋃ p₂ : PMF A₂,
    MAC.pentagon (out₁ W) p₁ p₂ ∩ MAC.pentagon (out₂ W) p₁ p₂))

def StrongInterference (W : DMC (A₁ × A₂) (B₁ × B₂)) : Prop :=
  ∀ (p₁ : PMF A₁) (p₂ : PMF A₂),
    I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure (out₁ W) p₁ p₂] ≤
      I[fun ω : A₁ × A₂ × B₂ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure (out₂ W) p₁ p₂] ∧
    I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
        MAC.jointMeasure (out₂ W) p₁ p₂] ≤
      I[fun ω : A₁ × A₂ × B₁ => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
        MAC.jointMeasure (out₁ W) p₁ p₂]

noncomputable def strongRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧
    R.1 ≤ I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
      MAC.jointMeasure (out₁ W) p₁ p₂] ∧
    R.2 ≤ I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
      MAC.jointMeasure (out₂ W) p₁ p₂] ∧
    R.1 + R.2 ≤ I[fun ω : A₁ × A₂ × B₁ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
      MAC.jointMeasure (out₁ W) p₁ p₂] ∧
    R.1 + R.2 ≤ I[fun ω : A₁ × A₂ × B₂ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
      MAC.jointMeasure (out₂ W) p₁ p₂]}

noncomputable def strongInterferenceRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ (⋃ p₁ : PMF A₁, ⋃ p₂ : PMF A₂, strongRegion W p₁ p₂))

section HanKobayashi

variable {Q V₁ V₂ : Type*} [Fintype Q] [MeasurableSpace Q] [Fintype V₁] [MeasurableSpace V₁]
  [Fintype V₂] [MeasurableSpace V₂]

noncomputable def hkJointMeasure (W : DMC (A₁ × A₂) (B₁ × B₂)) (pQ : PMF Q)
    (p₁ : Q → PMF (V₁ × A₁)) (p₂ : Q → PMF (V₂ × A₂)) :
    Measure (Q × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂)) :=
  (pQ.bind fun q => (p₁ q).bind fun x₁ => (p₂ q).bind fun x₂ =>
    (W (x₁.2, x₂.2)).map fun y => (q, x₁, x₂, y)).toMeasure

noncomputable def hkRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) (pQ : PMF Q)
    (p₁ : Q → PMF (V₁ × A₁)) (p₂ : Q → PMF (V₂ × A₂)) : Set (ℝ × ℝ) :=
  let μ := hkJointMeasure W pQ p₁ p₂
  let q := fun ω : Q × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂) => ω.1
  let u₁ := fun ω : Q × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂) => ω.2.1.1
  let x₁ := fun ω : Q × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂) => ω.2.1.2
  let u₂ := fun ω : Q × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂) => ω.2.2.1.1
  let x₂ := fun ω : Q × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂) => ω.2.2.1.2
  let y₁ := fun ω : Q × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂) => ω.2.2.2.1
  let y₂ := fun ω : Q × (V₁ × A₁) × (V₂ × A₂) × (B₁ × B₂) => ω.2.2.2.2
  let a := I[x₁ : y₁ | fun ω => (u₂ ω, q ω) ; μ]
  let b := I[x₂ : y₂ | fun ω => (u₁ ω, q ω) ; μ]
  let c₁ := I[fun ω => (x₁ ω, u₂ ω) : y₁ | q ; μ]
  let c₂ := I[fun ω => (x₂ ω, u₁ ω) : y₂ | q ; μ]
  let d₁ := I[x₁ : y₁ | fun ω => (u₁ ω, u₂ ω, q ω) ; μ]
  let d₂ := I[x₂ : y₂ | fun ω => (u₁ ω, u₂ ω, q ω) ; μ]
  let e₁ := I[fun ω => (x₁ ω, u₂ ω) : y₁ | fun ω => (u₁ ω, q ω) ; μ]
  let e₂ := I[fun ω => (x₂ ω, u₁ ω) : y₂ | fun ω => (u₂ ω, q ω) ; μ]
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ R.1 ≤ a ∧ R.2 ≤ b ∧
    R.1 + R.2 ≤ c₁ + d₂ ∧ R.1 + R.2 ≤ c₂ + d₁ ∧ R.1 + R.2 ≤ e₁ + e₂ ∧
    2 * R.1 + R.2 ≤ c₁ + d₁ + e₂ ∧ R.1 + 2 * R.2 ≤ c₂ + d₂ + e₁}

end HanKobayashi

noncomputable def hanKobayashiRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) : Set (ℝ × ℝ) :=
  ⋃ (k : ℕ) (pQ : PMF (Fin k)) (p₁ : Fin k → PMF (Fin k × A₁)) (p₂ : Fin k → PMF (Fin k × A₂)),
    hkRegion W pQ p₁ p₂

section Marginal

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype B₁] [Fintype B₂]

omit [Fintype B₁] in
theorem out₁_apply [Finite B₁] (W : DMC (A₁ × A₂) (B₁ × B₂)) (a : A₁ × A₂) (b₁ : B₁) :
    out₁ W a b₁ = ∑ b₂, W a (b₁, b₂) := by
  classical
  have := Fintype.ofFinite B₁
  rw [out₁, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Finset.sum_eq_single b₁ (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

omit [Fintype B₂] in
theorem out₂_apply [Finite B₂] (W : DMC (A₁ × A₂) (B₁ × B₂)) (a : A₁ × A₂) (b₂ : B₂) :
    out₂ W a b₂ = ∑ b₁, W a (b₁, b₂) := by
  classical
  have := Fintype.ofFinite B₂
  rw [out₂, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp

omit [Fintype B₁] in
theorem blockProb_out₁ [Finite B₁] {n : ℕ} (W : DMC (A₁ × A₂) (B₁ × B₂)) (x : Fin n → A₁ × A₂)
    (y₁ : Fin n → B₁) :
    DMC.blockProb (out₁ W) x y₁ =
      ∑ y₂ : Fin n → B₂, DMC.blockProb W x (fun i => (y₁ i, y₂ i)) := by
  have := Fintype.ofFinite B₁
  simp only [DMC.blockProb, out₁_apply]
  exact Fintype.prod_sum _

omit [Fintype B₂] in
theorem blockProb_out₂ [Finite B₂] {n : ℕ} (W : DMC (A₁ × A₂) (B₁ × B₂)) (x : Fin n → A₁ × A₂)
    (y₂ : Fin n → B₂) :
    DMC.blockProb (out₂ W) x y₂ =
      ∑ y₁ : Fin n → B₁, DMC.blockProb W x (fun i => (y₁ i, y₂ i)) := by
  have := Fintype.ofFinite B₂
  simp only [DMC.blockProb, out₂_apply]
  exact Fintype.prod_sum _

theorem sum_mul_blockProb_out₁ {n : ℕ} (W : DMC (A₁ × A₂) (B₁ × B₂)) (x : Fin n → A₁ × A₂)
    (f : (Fin n → B₁) → ℝ≥0∞) :
    ∑ y : Fin n → B₁ × B₂, f (fun i => (y i).1) * DMC.blockProb W x y =
      ∑ y₁, f y₁ * DMC.blockProb (out₁ W) x y₁ := by
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => B₁) (fun _ => B₂)).symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [blockProb_out₁, mul_sum]
  rfl

theorem sum_mul_blockProb_out₂ {n : ℕ} (W : DMC (A₁ × A₂) (B₁ × B₂)) (x : Fin n → A₁ × A₂)
    (f : (Fin n → B₂) → ℝ≥0∞) :
    ∑ y : Fin n → B₁ × B₂, f (fun i => (y i).2) * DMC.blockProb W x y =
      ∑ y₂, f y₂ * DMC.blockProb (out₂ W) x y₂ := by
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => B₁) (fun _ => B₂)).symm.sum_comp,
    Fintype.sum_prod_type,
    sum_comm]
  simp only [blockProb_out₂, mul_sum]
  rfl

end Marginal

end IC

namespace ICCode

variable {M₁ M₂ A₁ A₂ B₁ B₂ : Type*} {n : ℕ}

def ofMACCodes (c₁ : MACCode M₁ M₂ A₁ A₂ B₁ n) (c₂ : MACCode M₁ M₂ A₁ A₂ B₂ n) :
    ICCode M₁ M₂ A₁ A₂ B₁ B₂ n :=
  ⟨c₁.enc₁, c₁.enc₂, fun y => (c₁.dec y).1, fun y => (c₂.dec y).2⟩

private lemma ite_le_add {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {g g' : α} {d t : β} {e u : γ} (hg : d = t → e = u → g = g') (P : ℝ≥0∞) :
    (if g = g' then 0 else P) ≤ (if d = t then 0 else 1) * P + (if e = u then 0 else 1) * P := by
  have hP : (if g = g' then 0 else P) ≤ P := by split_ifs <;> simp
  by_cases a : d = t <;> by_cases b : e = u
  · simp [a, b, hg a b]
  · simpa [a, b] using hP
  · simpa [a, b] using hP
  · simpa [a, b] using hP.trans le_self_add

theorem errorProb_ofMACCodes_le [Fintype B₁] [Fintype B₂] [DecidableEq M₁] [DecidableEq M₂]
    (c₁ : MACCode M₁ M₂ A₁ A₂ B₁ n) (c₂ : MACCode M₁ M₂ A₁ A₂ B₂ n)
    (h₁ : c₂.enc₁ = c₁.enc₁) (h₂ : c₂.enc₂ = c₁.enc₂) (W : DMC (A₁ × A₂) (B₁ × B₂))
    (m : M₁ × M₂) :
    (ofMACCodes c₁ c₂).errorProb W m ≤ c₁.errorProb (IC.out₁ W) m + c₂.errorProb (IC.out₂ W) m := by
  set x : Fin n → A₁ × A₂ := fun i => (c₁.enc₁ m.1 i, c₁.enc₂ m.2 i)
  have e₁ : c₁.errorProb (IC.out₁ W) m = ∑ y₁ : Fin n → B₁,
      (if c₁.dec y₁ = m then 0 else 1) * DMC.blockProb (IC.out₁ W) x y₁ := by
    refine sum_congr rfl fun y _ => ?_
    split_ifs <;> simp [x]
  have e₂ : c₂.errorProb (IC.out₂ W) m = ∑ y₂ : Fin n → B₂,
      (if c₂.dec y₂ = m then 0 else 1) * DMC.blockProb (IC.out₂ W) x y₂ := by
    refine sum_congr rfl fun y _ => ?_
    rw [h₁, h₂]
    split_ifs <;> simp [x]
  rw [e₁, e₂, ← IC.sum_mul_blockProb_out₁ W x (fun y₁ => if c₁.dec y₁ = m then 0 else 1),
    ← IC.sum_mul_blockProb_out₂ W x (fun y₂ => if c₂.dec y₂ = m then 0 else 1),
    ← sum_add_distrib]
  refine sum_le_sum fun y _ => ite_le_add (fun hd he => ?_) _
  simp only [ofMACCodes, hd, he]

def append {M₁' M₂' : Type*} {n' : ℕ} (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n)
    (c' : ICCode M₁' M₂' A₁ A₂ B₁ B₂ n') :
    ICCode (M₁ × M₁') (M₂ × M₂') A₁ A₂ B₁ B₂ (n + n') where
  enc₁ m := Fin.append (c.enc₁ m.1) (c'.enc₁ m.2)
  enc₂ m := Fin.append (c.enc₂ m.1) (c'.enc₂ m.2)
  dec₁ y := (c.dec₁ fun i => y (Fin.castAdd n' i), c'.dec₁ fun i => y (Fin.natAdd n i))
  dec₂ y := (c.dec₂ fun i => y (Fin.castAdd n' i), c'.dec₂ fun i => y (Fin.natAdd n i))

def relabel {M₁' M₂' : Type*} (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n) (e₁ : M₁ ≃ M₁')
    (e₂ : M₂ ≃ M₂') : ICCode M₁' M₂' A₁ A₂ B₁ B₂ n where
  enc₁ m := c.enc₁ (e₁.symm m)
  enc₂ m := c.enc₂ (e₂.symm m)
  dec₁ y := e₁ (c.dec₁ y)
  dec₂ y := e₂ (c.dec₂ y)

theorem toMACCode_append {M₁' M₂' : Type*} {n' : ℕ} (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n)
    (c' : ICCode M₁' M₂' A₁ A₂ B₁ B₂ n') :
    (c.append c').toMACCode = c.toMACCode.append c'.toMACCode := rfl

theorem toMACCode_relabel {M₁' M₂' : Type*} (c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n) (e₁ : M₁ ≃ M₁')
    (e₂ : M₂ ≃ M₂') : (c.relabel e₁ e₂).toMACCode = c.toMACCode.relabel e₁ e₂ := rfl

end ICCode

namespace IC

variable {A₁ A₂ B₁ B₂ : Type*} [Fintype B₁] [Fintype B₂]

theorem Achievable.toMAC {W : DMC (A₁ × A₂) (B₁ × B₂)} {R₁ R₂ : ℝ} (h : Achievable W R₁ R₂) :
    MAC.Achievable W R₁ R₂ := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hn
  exact ⟨k₁, k₂, hk₁, hk₂, c.toMACCode, hc⟩

theorem achievableRegion_subset (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    achievableRegion W ⊆ MAC.achievableRegion W :=
  fun _ ⟨h1, h2, h⟩ => ⟨h1, h2, h.toMAC⟩

theorem closure_achievableRegion_subset [Fintype A₁] [MeasurableSpace A₁]
    [MeasurableSingletonClass A₁] [Nonempty A₁] [Fintype A₂] [MeasurableSpace A₂]
    [MeasurableSingletonClass A₂] [Nonempty A₂] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
    [MeasurableSpace B₂] [MeasurableSingletonClass B₂] (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    closure (achievableRegion W) ⊆ MAC.capacityRegion W :=
  (closure_mono (achievableRegion_subset W)).trans (MAC.closure_achievableRegion_eq W).le

theorem Achievable.mono {W : DMC (A₁ × A₂) (B₁ × B₂)} {R₁ R₂ R₁' R₂' : ℝ}
    (h : Achievable W R₁ R₂) (h₁ : R₁' ≤ R₁) (h₂ : R₂' ≤ R₂) : Achievable W R₁' R₂' := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hn
  exact ⟨k₁, k₂, (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg n))).trans hk₁,
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg n))).trans hk₂, c, hc⟩

theorem Achievable.max_zero {W : DMC (A₁ × A₂) (B₁ × B₂)} {R₁ R₂ : ℝ}
    (h : Achievable W R₁ R₂) : Achievable W (max R₁ 0) (max R₂ 0) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hn
  exact ⟨k₁, k₂, exp_mul_max_le hk₁, exp_mul_max_le hk₂, c, hc⟩

theorem mem_closure_achievableRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) {R : ℝ × ℝ} (h1 : 0 ≤ R.1)
    (h2 : 0 ≤ R.2) (h : ∀ δ > 0, Achievable W (R.1 - δ) (R.2 - δ)) :
    R ∈ closure (achievableRegion W) := by
  rw [Metric.mem_closure_iff]
  intro η hη
  have key : ∀ x : ℝ, 0 ≤ x → dist x (max (x - η / 2) 0) < η := by
    intro x hx
    rw [Real.dist_eq]
    rcases le_total (x - η / 2) 0 with h | h
    · rw [max_eq_right h, sub_zero, abs_of_nonneg hx]
      linarith
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]
      linarith
  refine ⟨(max (R.1 - η / 2) 0, max (R.2 - η / 2) 0),
    ⟨le_max_right _ _, le_max_right _ _, (h (η / 2) (by positivity)).max_zero⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨key _ h1, key _ h2⟩

private lemma exists_code_of_eq {M₁ M₂ : Type*} [Fintype M₁] [Fintype M₂] [DecidableEq M₁]
    [DecidableEq M₂] {W : DMC (A₁ × A₂) (B₁ × B₂)} {ε : ℝ≥0∞} {n m : ℕ} (h : n = m)
    (hc : ∃ c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n, c.avgError W ≤ ε) :
    ∃ c : ICCode M₁ M₂ A₁ A₂ B₁ B₂ m, c.avgError W ≤ ε := h ▸ hc

theorem Achievable.timeSharing {W : DMC (A₁ × A₂) (B₁ × B₂)} {R₁ R₂ R₁' R₂' : ℝ}
    (h : Achievable W R₁ R₂) (h' : Achievable W R₁' R₂') {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) {δ : ℝ} (hδ : 0 < δ) :
    Achievable W (a * R₁ + b * R₁' - δ) (a * R₂ + b * R₂' - δ) := by
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    exact h'.mono (by linarith) (by linarith)
  rcases hb.eq_or_lt with rfl | hb'
  · obtain rfl : a = 1 := by linarith
    exact h.mono (by linarith) (by linarith)
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨N', hN'⟩ := h' (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (max (N / a) (N' / b)) ((|R₁ - R₁'| + |R₂ - R₂'|) / δ))
  refine ⟨N₀, fun n hn => ?_⟩
  have hn' : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hNa : (N : ℝ) < a * n := (div_lt_iff₀' ha').1 (((le_max_left _ _).trans
    (le_max_left _ _)).trans_lt (hN₀.trans_le hn'))
  have hNb : (N' : ℝ) < b * n := (div_lt_iff₀' hb').1 (((le_max_right _ _).trans
    (le_max_left _ _)).trans_lt (hN₀.trans_le hn'))
  have hnδ : |R₁ - R₁'| + |R₂ - R₂'| < n * δ := (div_lt_iff₀ hδ).1 ((le_max_right _ _).trans_lt
    (hN₀.trans_le hn'))
  set n₁ := ⌊a * n⌋₊ with hn₁
  have han : 0 ≤ a * n := by positivity
  have hfl : (n₁ : ℝ) ≤ a * n := Nat.floor_le han
  have hfl' : a * n < n₁ + 1 := Nat.lt_floor_add_one _
  have hn₁n : n₁ ≤ n := by
    have : (n₁ : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hn₁N : N ≤ n₁ := Nat.le_floor hNa.le
  have hn₂N : N' ≤ n - n₁ := by
    have : (N' : ℝ) + n₁ ≤ n := by nlinarith
    have : N' + n₁ ≤ n := by exact_mod_cast this
    omega
  obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n₁ hn₁N
  obtain ⟨k₁', k₂', hk₁', hk₂', c', hc'⟩ := hN' (n - n₁) hn₂N
  have hcast : ((n - n₁ : ℕ) : ℝ) = n - n₁ := Nat.cast_sub hn₁n
  have hrate : ∀ {R R' : ℝ} {k k' : ℕ}, Real.exp (n₁ * R) ≤ k →
      Real.exp (((n - n₁ : ℕ) : ℝ) * R') ≤ k' → |R - R'| < n * δ →
      Real.exp (n * (a * R + b * R' - δ)) ≤ ((k * k' : ℕ) : ℝ) := by
    intro R R' k k' hk hk' hRR
    rw [Nat.cast_mul]
    refine le_trans ?_ (mul_le_mul hk hk' (Real.exp_pos _).le (Nat.cast_nonneg _))
    rw [← Real.exp_add, hcast]
    refine Real.exp_le_exp.2 ?_
    have hθ0 : 0 ≤ a * n - n₁ := by linarith
    have hθ1 : a * n - n₁ ≤ 1 := by linarith
    have habs := le_abs_self (R - R')
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_le_mul_of_nonneg_left habs hθ0,
      mul_le_mul_of_nonneg_right hθ1 (abs_nonneg (R - R'))]
  refine ⟨k₁ * k₁', k₂ * k₂', hrate hk₁ hk₁' (by linarith [abs_nonneg (R₂ - R₂')]),
    hrate hk₂ hk₂' (by linarith [abs_nonneg (R₁ - R₁')]), ?_⟩
  have hk0 : ∀ {R : ℝ} {m k : ℕ}, Real.exp (m * R) ≤ k → 0 < k := fun hk =>
    Nat.cast_pos.1 ((Real.exp_pos _).trans_le hk)
  have : NeZero k₁ := ⟨(hk0 hk₁).ne'⟩
  have : NeZero k₂ := ⟨(hk0 hk₂).ne'⟩
  have : NeZero k₁' := ⟨(hk0 hk₁').ne'⟩
  have : NeZero k₂' := ⟨(hk0 hk₂').ne'⟩
  refine exists_code_of_eq (Nat.add_sub_cancel' hn₁n)
    ⟨(c.append c').relabel finProdFinEquiv finProdFinEquiv, ?_⟩
  rw [← ICCode.avgError_toMACCode, ICCode.toMACCode_relabel, MACCode.avgError_relabel,
    ICCode.toMACCode_append]
  calc _ ≤ c.toMACCode.avgError W + c'.toMACCode.avgError W :=
        c.toMACCode.avgError_append_le c'.toMACCode W
    _ ≤ ε / 2 + ε / 2 := add_le_add hc hc'
    _ = ε := ENNReal.add_halves ε

theorem convex_closure_achievableRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    Convex ℝ (closure (achievableRegion W)) := by
  have key : ∀ x ∈ achievableRegion W, ∀ y ∈ achievableRegion W, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → a • x + b • y ∈ closure (achievableRegion W) := by
    rintro x ⟨hx1, hx2, hx⟩ y ⟨hy1, hy2, hy⟩ a b ha hb hab
    refine mem_closure_achievableRegion W ?_ ?_ fun δ hδ => ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      positivity
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      positivity
    · simpa using hx.timeSharing hy ha hb hab hδ
  intro x hx y hy a b ha hb hab
  have hf : Continuous (Function.uncurry fun x y : ℝ × ℝ => a • x + b • y) :=
    (show Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) => a • p.1 + b • p.2 from
      (continuous_fst.const_smul a).add (continuous_snd.const_smul b))
  have h := map_mem_closure₂ hf hx hy fun x' hx' y' hy' => key x' hx' y' hy' a b ha hb hab
  rwa [closure_closure] at h

section Random

variable [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁]
  [Fintype A₂] [MeasurableSpace A₂] [MeasurableSingletonClass A₂]
  [MeasurableSpace B₁] [MeasurableSingletonClass B₁] [MeasurableSpace B₂]
  [MeasurableSingletonClass B₂]

omit [Fintype B₁] [Fintype B₂] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [MeasurableSpace B₂] [MeasurableSingletonClass B₂] in
noncomputable def typicalBound {B : Type*} [Fintype B] [MeasurableSpace B]
    (V : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) (n : ℕ) (ε : ℝ) (k₁ k₂ : ℕ) : ℝ :=
  (1 - ∑ xy ∈ MAC.decodingSet V p₁ p₂ n ε,
      iidProb (DMC.jointPMF V (MAC.inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i))) +
    ((k₁ : ℝ) - 1) * Real.exp (-(n * ((MAC.sideChannel₁ V p₂).inputMutualInfo p₁ - 3 * ε))) +
    ((k₂ : ℝ) - 1) * Real.exp (-(n * ((MAC.sideChannel₂ V p₁).inputMutualInfo p₂ - 3 * ε))) +
    ((k₁ : ℝ) - 1) * ((k₂ : ℝ) - 1) *
      Real.exp (-(n * (V.inputMutualInfo (MAC.inputPMF p₁ p₂) - 3 * ε)))

noncomputable def typicalCode {M₁ M₂ : Type*} {n : ℕ} (W : DMC (A₁ × A₂) (B₁ × B₂))
    (p₁ : PMF A₁) (p₂ : PMF A₂) (ε : ℝ) (C₁ : M₁ → Fin n → A₁) (C₂ : M₂ → Fin n → A₂)
    (m₀ : M₁ × M₂) : ICCode M₁ M₂ A₁ A₂ B₁ B₂ n :=
  ICCode.ofMACCodes (MACCode.typicalCode C₁ C₂ (MAC.decodingSet (out₁ W) p₁ p₂ n ε) m₀)
    (MACCode.typicalCode C₁ C₂ (MAC.decodingSet (out₂ W) p₁ p₂ n ε) m₀)

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B₁]
  [MeasurableSingletonClass B₂] in
theorem exists_typicalCode_avgError_le {M₁ M₂ : Type*} [Fintype M₁] [Fintype M₂]
    [DecidableEq M₁] [DecidableEq M₂] {n : ℕ} (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁)
    (p₂ : PMF A₂) (ε : ℝ) (m₀ : M₁ × M₂) :
    ∃ (C₁ : M₁ → Fin n → A₁) (C₂ : M₂ → Fin n → A₂),
      (typicalCode W p₁ p₂ ε C₁ C₂ m₀).avgError W ≤
        ENNReal.ofReal
          (typicalBound (out₁ W) p₁ p₂ n ε (Fintype.card M₁) (Fintype.card M₂) +
            typicalBound (out₂ W) p₁ p₂ n ε (Fintype.card M₁) (Fintype.card M₂)) := by
  have : Nonempty (M₁ × M₂) := ⟨m₀⟩
  set β₁ := typicalBound (out₁ W) p₁ p₂ n ε (Fintype.card M₁) (Fintype.card M₂)
  set β₂ := typicalBound (out₂ W) p₁ p₂ n ε (Fintype.card M₁) (Fintype.card M₂)
  set w := fun C : (M₁ → Fin n → A₁) × (M₂ → Fin n → A₂) =>
    (∏ j, iidProb p₁ (C.1 j)) * ∏ j, iidProb p₂ (C.2 j)
  have hw : ∀ C, 0 ≤ w C := fun C => mul_nonneg (prod_nonneg fun j _ => iidProb_nonneg _ _)
    (prod_nonneg fun j _ => iidProb_nonneg _ _)
  have h1 : ∑ C, w C = 1 := by
    simp only [w]
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, sum_prod (fun _ x => iidProb p₂ x) (fun _ => sum_iidProb p₂ n), mul_one]
    exact sum_prod (fun _ x => iidProb p₁ x) (fun _ => sum_iidProb p₁ n)
  have hm : ∀ m : M₁ × M₂, ∑ C, w C * ((typicalCode W p₁ p₂ ε C.1 C.2 m₀).errorProb W m).toReal ≤
      β₁ + β₂ := by
    intro m
    have e₁ := MAC.sum_errorProb_typicalCode_le (out₁ W) p₁ p₂ ε m₀ m (n := n)
    have e₂ := MAC.sum_errorProb_typicalCode_le (out₂ W) p₁ p₂ ε m₀ m (n := n)
    calc _ ≤ ∑ C, (w C *
          ((MACCode.typicalCode C.1 C.2 (MAC.decodingSet (out₁ W) p₁ p₂ n ε) m₀).errorProb
            (out₁ W) m).toReal + w C *
          ((MACCode.typicalCode C.1 C.2 (MAC.decodingSet (out₂ W) p₁ p₂ n ε) m₀).errorProb
            (out₂ W) m).toReal) := by
          refine sum_le_sum fun C _ => ?_
          rw [← mul_add, ← ENNReal.toReal_add (MACCode.errorProb_ne_top _ _ _)
            (MACCode.errorProb_ne_top _ _ _)]
          exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (ENNReal.add_ne_top.2
            ⟨MACCode.errorProb_ne_top _ _ _, MACCode.errorProb_ne_top _ _ _⟩)
            (ICCode.errorProb_ofMACCodes_le
              (MACCode.typicalCode C.1 C.2 (MAC.decodingSet (out₁ W) p₁ p₂ n ε) m₀)
              (MACCode.typicalCode C.1 C.2 (MAC.decodingSet (out₂ W) p₁ p₂ n ε) m₀)
              rfl rfl W m)) (hw C)
      _ ≤ β₁ + β₂ := by
          rw [sum_add_distrib]
          exact add_le_add e₁ e₂
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le
    (f := fun C => ∑ m, ((typicalCode W p₁ p₂ ε C.1 C.2 m₀).errorProb W m).toReal)
    (t := Fintype.card (M₁ × M₂) * (β₁ + β₂)) hw h1 (by
      simp only [mul_sum]
      rw [sum_comm]
      calc _ ≤ ∑ m : M₁ × M₂, (β₁ + β₂) := sum_le_sum fun m _ => hm m
        _ = _ := by simp; ring)
  refine ⟨C.1, C.2, ?_⟩
  rw [← ICCode.avgError_toMACCode, ← MACCode.avgError_toBlockCode]
  exact BlockCode.avgError_le_ofReal _ W hC

private lemma mul_exp_le {n : ℕ} {x R I I' η : ℝ} (hx : x ≤ Real.exp (n * R)) (hI : I ≤ I')
    (hη : 4 * η ≤ I - R) : x * Real.exp (-(n * (I' - 3 * η))) ≤ Real.exp (n * (-η)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc x * Real.exp (-(n * (I' - 3 * η))) ≤ Real.exp (n * R) * Real.exp (-(n * (I - 3 * η))) :=
        mul_le_mul hx (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (n * R - n * (I - 3 * η)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (n * (-η)) := Real.exp_le_exp.2 (by nlinarith)

omit [Fintype B₁] [Fintype B₂] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]
  [MeasurableSpace B₂] [MeasurableSingletonClass B₂] in
private lemma typicalBound_le {B : Type*} [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (V : DMC (A₁ × A₂) B) (p₁ : PMF A₁) (p₂ : PMF A₂) {n : ℕ}
    {R₁ R₂ η : ℝ} {k₁ k₂ : ℕ} (hk₁ : (k₁ : ℝ) - 1 ≤ Real.exp (n * R₁))
    (hk₂ : (k₂ : ℝ) - 1 ≤ Real.exp (n * R₂)) (hk₂0 : 0 ≤ (k₂ : ℝ) - 1)
    (hη1 : 4 * η ≤ I[fun ω : A₁ × A₂ × B => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
      MAC.jointMeasure V p₁ p₂] - R₁)
    (hη2 : 4 * η ≤ I[fun ω : A₁ × A₂ × B => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
      MAC.jointMeasure V p₁ p₂] - R₂)
    (hη3 : 4 * η ≤ I[fun ω : A₁ × A₂ × B => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
      MAC.jointMeasure V p₁ p₂] - (R₁ + R₂)) :
    typicalBound V p₁ p₂ n η k₁ k₂ ≤
      (1 - ∑ xy ∈ MAC.decodingSet V p₁ p₂ n η,
        iidProb (DMC.jointPMF V (MAC.inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i))) +
      3 * Real.exp (n * (-η)) := by
  have b1 := mul_exp_le hk₁ (MAC.condMutualInfo_le_inputMutualInfo_sideChannel₁ V p₁ p₂) hη1
  have b2 := mul_exp_le hk₂ (MAC.condMutualInfo_le_inputMutualInfo_sideChannel₂ V p₁ p₂) hη2
  have hk : ((k₁ : ℝ) - 1) * ((k₂ : ℝ) - 1) ≤ Real.exp (n * (R₁ + R₂)) := by
    rw [mul_add, Real.exp_add]
    exact mul_le_mul hk₁ hk₂ hk₂0 (Real.exp_pos _).le
  have b3 := mul_exp_le hk (MAC.inputMutualInfo_inputPMF V p₁ p₂).ge hη3
  unfold typicalBound
  linarith

theorem achievable_of_lt (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁) (p₂ : PMF A₂)
    {R₁ R₂ : ℝ}
    (h₁ : R₁ < I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
      MAC.jointMeasure (out₁ W) p₁ p₂])
    (h₂ : R₂ < I[fun ω : A₁ × A₂ × B₁ => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
      MAC.jointMeasure (out₁ W) p₁ p₂])
    (h₃ : R₁ + R₂ < I[fun ω : A₁ × A₂ × B₁ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
      MAC.jointMeasure (out₁ W) p₁ p₂])
    (h₄ : R₁ < I[fun ω : A₁ × A₂ × B₂ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
      MAC.jointMeasure (out₂ W) p₁ p₂])
    (h₅ : R₂ < I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
      MAC.jointMeasure (out₂ W) p₁ p₂])
    (h₆ : R₁ + R₂ < I[fun ω : A₁ × A₂ × B₂ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
      MAC.jointMeasure (out₂ W) p₁ p₂]) :
    Achievable W R₁ R₂ := by
  classical
  intro ε hε
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  obtain ⟨η, hη0, hη1, hη2, hη3, hη4, hη5, hη6⟩ : ∃ η : ℝ, 0 < η ∧
      4 * η ≤ I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure (out₁ W) p₁ p₂] - R₁ ∧
      4 * η ≤ I[fun ω : A₁ × A₂ × B₁ => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
        MAC.jointMeasure (out₁ W) p₁ p₂] - R₂ ∧
      4 * η ≤ I[fun ω : A₁ × A₂ × B₁ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
        MAC.jointMeasure (out₁ W) p₁ p₂] - (R₁ + R₂) ∧
      4 * η ≤ I[fun ω : A₁ × A₂ × B₂ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure (out₂ W) p₁ p₂] - R₁ ∧
      4 * η ≤ I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
        MAC.jointMeasure (out₂ W) p₁ p₂] - R₂ ∧
      4 * η ≤ I[fun ω : A₁ × A₂ × B₂ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
        MAC.jointMeasure (out₂ W) p₁ p₂] - (R₁ + R₂) := by
    refine ⟨min (min (min (I[fun ω : A₁ × A₂ × B₁ => ω.1 : fun ω => ω.2.2 | fun ω => ω.2.1 ;
        MAC.jointMeasure (out₁ W) p₁ p₂] - R₁) (I[fun ω : A₁ × A₂ × B₁ => ω.2.1 :
        fun ω => ω.2.2 | fun ω => ω.1 ; MAC.jointMeasure (out₁ W) p₁ p₂] - R₂))
      (min (I[fun ω : A₁ × A₂ × B₁ => (ω.1, ω.2.1) : fun ω => ω.2.2 ;
        MAC.jointMeasure (out₁ W) p₁ p₂] - (R₁ + R₂)) (I[fun ω : A₁ × A₂ × B₂ => ω.1 :
        fun ω => ω.2.2 | fun ω => ω.2.1 ; MAC.jointMeasure (out₂ W) p₁ p₂] - R₁)))
      (min (I[fun ω : A₁ × A₂ × B₂ => ω.2.1 : fun ω => ω.2.2 | fun ω => ω.1 ;
        MAC.jointMeasure (out₂ W) p₁ p₂] - R₂) (I[fun ω : A₁ × A₂ × B₂ => (ω.1, ω.2.1) :
        fun ω => ω.2.2 ; MAC.jointMeasure (out₂ W) p₁ p₂] - (R₁ + R₂))) / 4, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · refine div_pos (lt_min (lt_min (lt_min ?_ ?_) (lt_min ?_ ?_)) (lt_min ?_ ?_)) (by norm_num)
        <;> linarith
    all_goals rw [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)]
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hJ₁ : Tendsto (fun n : ℕ => 1 - ∑ xy ∈ MAC.decodingSet (out₁ W) p₁ p₂ n η,
      iidProb (DMC.jointPMF (out₁ W) (MAC.inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (MAC.tendsto_sum_iidProb_decodingSet (out₁ W) p₁ p₂ hη0)
  have hJ₂ : Tendsto (fun n : ℕ => 1 - ∑ xy ∈ MAC.decodingSet (out₂ W) p₁ p₂ n η,
      iidProb (DMC.jointPMF (out₂ W) (MAC.inputPMF p₁ p₂)) (fun i => (xy.1 i, xy.2 i)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (MAC.tendsto_sum_iidProb_decodingSet (out₂ W) p₁ p₂ hη0)
  have hE := tendsto_exp_nat_mul (neg_neg_of_pos hη0)
  have hsum := (hJ₁.add hJ₂).add (hE.const_mul 6)
  rw [mul_zero, add_zero, add_zero] at hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  set k₁ := ⌈Real.exp (n * R₁)⌉₊
  set k₂ := ⌈Real.exp (n * R₂)⌉₊
  have hk₁ : 0 < k₁ := Nat.ceil_pos.2 (Real.exp_pos _)
  have hk₂ : 0 < k₂ := Nat.ceil_pos.2 (Real.exp_pos _)
  have hk₁' : (k₁ : ℝ) - 1 ≤ Real.exp (n * R₁) := by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R₁)).le]
  have hk₂' : (k₂ : ℝ) - 1 ≤ Real.exp (n * R₂) := by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R₂)).le]
  have hk₂0 : (0 : ℝ) ≤ k₂ - 1 := by
    have : (1 : ℝ) ≤ k₂ := Nat.one_le_cast.2 hk₂
    linarith
  refine ⟨k₁, k₂, Nat.le_ceil _, Nat.le_ceil _, ?_⟩
  obtain ⟨C₁, C₂, hC⟩ := exists_typicalCode_avgError_le (n := n) W p₁ p₂ η
    ((⟨0, hk₁⟩, ⟨0, hk₂⟩) : Fin k₁ × Fin k₂)
  refine ⟨_, hC.trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hδε.le)⟩
  rw [Fintype.card_fin, Fintype.card_fin]
  have b₁ := typicalBound_le (out₁ W) p₁ p₂ hk₁' hk₂' hk₂0 hη1 hη2 hη3
  have b₂ := typicalBound_le (out₂ W) p₁ p₂ hk₁' hk₂' hk₂0 hη4 hη5 hη6
  linarith [hN n hn]

theorem inter_pentagon_subset_closure_achievableRegion (W : DMC (A₁ × A₂) (B₁ × B₂))
    (p₁ : PMF A₁) (p₂ : PMF A₂) :
    MAC.pentagon (out₁ W) p₁ p₂ ∩ MAC.pentagon (out₂ W) p₁ p₂ ⊆
      closure (achievableRegion W) := by
  rintro R ⟨⟨h1, h2, h3, h4, h5⟩, ⟨-, -, h6, h7, h8⟩⟩
  exact mem_closure_achievableRegion W h1 h2 fun δ hδ =>
    achievable_of_lt W p₁ p₂ (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)

theorem compoundRegion_subset_closure_achievableRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) :
    compoundRegion W ⊆ closure (achievableRegion W) :=
  closure_minimal (convexHull_min (Set.iUnion₂_subset fun p₁ p₂ =>
    inter_pentagon_subset_closure_achievableRegion W p₁ p₂) (convex_closure_achievableRegion W))
    isClosed_closure

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B₁]
  [MeasurableSingletonClass B₂] in
theorem inter_pentagon_subset_strongRegion (W : DMC (A₁ × A₂) (B₁ × B₂)) (p₁ : PMF A₁)
    (p₂ : PMF A₂) :
    MAC.pentagon (out₁ W) p₁ p₂ ∩ MAC.pentagon (out₂ W) p₁ p₂ ⊆ strongRegion W p₁ p₂ := by
  rintro R ⟨⟨h1, h2, h3, -, h5⟩, ⟨-, -, -, h7, h8⟩⟩
  exact ⟨h1, h2, h3, h7, h5, h8⟩

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B₁]
  [MeasurableSingletonClass B₂] in
theorem strongRegion_subset_inter_pentagon {W : DMC (A₁ × A₂) (B₁ × B₂)}
    (hW : StrongInterference W) (p₁ : PMF A₁) (p₂ : PMF A₂) :
    strongRegion W p₁ p₂ ⊆ MAC.pentagon (out₁ W) p₁ p₂ ∩ MAC.pentagon (out₂ W) p₁ p₂ := by
  rintro R ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨⟨h1, h2, h3, h4.trans (hW p₁ p₂).2, h5⟩, ⟨h1, h2, h3.trans (hW p₁ p₂).1, h4, h6⟩⟩

omit [MeasurableSingletonClass A₁] [MeasurableSingletonClass A₂] [MeasurableSingletonClass B₁]
  [MeasurableSingletonClass B₂] in
theorem strongInterferenceRegion_eq_compoundRegion {W : DMC (A₁ × A₂) (B₁ × B₂)}
    (hW : StrongInterference W) : strongInterferenceRegion W = compoundRegion W := by
  unfold strongInterferenceRegion compoundRegion
  congr 2
  exact Set.iUnion₂_congr fun p₁ p₂ => (Set.Subset.antisymm
    (strongRegion_subset_inter_pentagon hW p₁ p₂) (inter_pentagon_subset_strongRegion W p₁ p₂))

theorem strongInterferenceRegion_subset_closure_achievableRegion
    {W : DMC (A₁ × A₂) (B₁ × B₂)} (hW : StrongInterference W) :
    strongInterferenceRegion W ⊆ closure (achievableRegion W) :=
  (strongInterferenceRegion_eq_compoundRegion hW).le.trans
    (compoundRegion_subset_closure_achievableRegion W)

end Random

end IC

end Meat
