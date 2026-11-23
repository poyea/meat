import Meat.Channel.MultipleAccessKTheorem
import Meat.Open.EntropicFormula

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

structure ICKCode {K : ℕ} (M A B : Fin K → Type*) (n : ℕ) where
  enc : ∀ k, M k → Fin n → A k
  dec : ∀ k, (Fin n → B k) → M k

namespace ICKCode

variable {K : ℕ} {M A B : Fin K → Type*} {n : ℕ}

def toMACKCode (c : ICKCode M A B n) : MACKCode M A (∀ k, B k) n :=
  ⟨c.enc, fun y k => c.dec k fun i => y i k⟩

noncomputable def errorProb [∀ k, Fintype (B k)] [∀ k, DecidableEq (M k)]
    (c : ICKCode M A B n) (W : DMC (∀ k, A k) (∀ k, B k)) (m : ∀ k, M k) : ℝ≥0∞ :=
  ∑ y : Fin n → ∀ k, B k, if (fun k => c.dec k fun i => y i k) = m then 0
    else DMC.blockProb W (fun i k => c.enc k (m k) i) y

noncomputable def avgError [∀ k, Fintype (B k)] [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]
    (c : ICKCode M A B n) (W : DMC (∀ k, A k) (∀ k, B k)) : ℝ≥0∞ :=
  (∑ m : ∀ k, M k, c.errorProb W m) / ∏ k, (Fintype.card (M k) : ℝ≥0∞)

theorem errorProb_toMACKCode [∀ k, Fintype (B k)] [∀ k, DecidableEq (M k)]
    (c : ICKCode M A B n) (W : DMC (∀ k, A k) (∀ k, B k)) (m : ∀ k, M k) :
    c.toMACKCode.errorProb W m = c.errorProb W m := rfl

theorem avgError_toMACKCode [∀ k, Fintype (B k)] [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]
    (c : ICKCode M A B n) (W : DMC (∀ k, A k) (∀ k, B k)) :
    c.toMACKCode.avgError W = c.avgError W := rfl

def append {M' : Fin K → Type*} {n' : ℕ} (c : ICKCode M A B n) (c' : ICKCode M' A B n') :
    ICKCode (fun k => M k × M' k) A B (n + n') where
  enc k m := Fin.append (c.enc k m.1) (c'.enc k m.2)
  dec k y := (c.dec k fun i => y (Fin.castAdd n' i), c'.dec k fun i => y (Fin.natAdd n i))

def relabel {M' : Fin K → Type*} (c : ICKCode M A B n) (e : ∀ k, M k ≃ M' k) :
    ICKCode M' A B n where
  enc k m := c.enc k ((e k).symm m)
  dec k y := e k (c.dec k y)

theorem toMACKCode_append {M' : Fin K → Type*} {n' : ℕ} (c : ICKCode M A B n)
    (c' : ICKCode M' A B n') :
    (c.append c').toMACKCode = c.toMACKCode.append c'.toMACKCode := rfl

theorem toMACKCode_relabel {M' : Fin K → Type*} (c : ICKCode M A B n) (e : ∀ k, M k ≃ M' k) :
    (c.relabel e).toMACKCode = c.toMACKCode.relabel e := rfl

end ICKCode

namespace ICK

variable {K : ℕ} {A B : Fin K → Type*}

def Achievable [∀ k, Fintype (B k)] (W : DMC (∀ k, A k) (∀ k, B k)) (R : Fin K → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ L : Fin K → ℕ, (∀ k, Real.exp (n * R k) ≤ L k) ∧
      ∃ c : ICKCode (fun k => Fin (L k)) A B n, c.avgError W ≤ ε

def achievableRegion [∀ k, Fintype (B k)] (W : DMC (∀ k, A k) (∀ k, B k)) :
    Set (Fin K → ℝ) :=
  {R | (∀ k, 0 ≤ R k) ∧ Achievable W R}

noncomputable def out (W : DMC (∀ k, A k) (∀ k, B k)) (k : Fin K) : DMC (∀ k, A k) (B k) :=
  fun a => (W a).map fun b => b k

structure RateFormula (m r K : ℕ) where
  L : ℕ
  J : ℕ
  a : Fin L → Fin K → ℝ
  c : Fin L → Finset (Fin m) × Finset (Fin r) → ℝ
  d : Fin J → Finset (Fin m) × Finset (Fin r) → ℝ

namespace RateFormula

variable {m r k : ℕ} {C : Type*} [Fintype C]

def Admissible (F : RateFormula m r K) (h : Finset (Fin m) × Finset (Fin r) → ℝ) : Prop :=
  ∀ j, ∑ S, F.d j S * h S = 0

def region (F : RateFormula m r K) (h : Finset (Fin m) × Finset (Fin r) → ℝ) :
    Set (Fin K → ℝ) :=
  {R | (∀ i, 0 ≤ R i) ∧ ∀ l, ∑ i, F.a l i * R i ≤ ∑ S, F.c l S * h S}

def value {ι : Type*} (F : RateFormula m r K)
    (law : ι → PMF ((Fin m → Fin k) × (Fin r → C))) : Set (Fin K → ℝ) :=
  closure (⋃ q, ⋃ (_ : F.Admissible (EntropicFormula.entropyVector (law q))),
    F.region (EntropicFormula.entropyVector (law q)))

end RateFormula

def letter (a : ∀ k, A k) (b : ∀ k, B k) : Fin (K + K) → (Σ k, A k) ⊕ (Σ k, B k) :=
  Fin.addCases (fun k => Sum.inl ⟨k, a k⟩) fun k => Sum.inr ⟨k, b k⟩

noncomputable def letterLaw {m k : ℕ} (W : DMC (∀ k, A k) (∀ k, B k))
    (q : PMF ((Fin m → Fin k) × ∀ j, A j)) :
    PMF ((Fin m → Fin k) × (Fin (K + K) → (Σ k, A k) ⊕ (Σ k, B k))) :=
  q.bind fun ω => (W ω.2).map fun b => (ω.1, letter ω.2 b)

def SingleLetterCapacity (K : ℕ) : Prop :=
  ∃ (m : ℕ) (κ : (Fin K → ℕ) → (Fin K → ℕ) → ℕ) (F : RateFormula m (K + K) K),
    ∀ (A B : Fin K → Type) [∀ k, Fintype (A k)] [∀ k, Fintype (B k)] [∀ k, Nonempty (A k)]
      (W : DMC (∀ k, A k) (∀ k, B k)),
      closure (achievableRegion W) =
        F.value (letterLaw (m := m)
          (k := κ (fun k => Fintype.card (A k)) (fun k => Fintype.card (B k))) W)

section Outer

variable [∀ k, Fintype (B k)]

theorem Achievable.toMACK {W : DMC (∀ k, A k) (∀ k, B k)} {R : Fin K → ℝ}
    (h : Achievable W R) : MACK.Achievable W R := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨L, hL, c, hc⟩ := hN n hn
  exact ⟨L, hL, c.toMACKCode, hc⟩

theorem achievableRegion_subset (W : DMC (∀ k, A k) (∀ k, B k)) :
    achievableRegion W ⊆ MACK.achievableRegion W :=
  fun _ hR => ⟨hR.1, hR.2.toMACK⟩

theorem closure_achievableRegion_subset [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)]
    [∀ k, MeasurableSingletonClass (A k)] [∀ k, MeasurableSpace (B k)]
    [∀ k, MeasurableSingletonClass (B k)] (W : DMC (∀ k, A k) (∀ k, B k)) :
    closure (achievableRegion W) ⊆ MACK.capacityRegion W := by
  rw [← MACK.closure_achievableRegion_eq]
  exact closure_mono (achievableRegion_subset W)

end Outer

section TimeSharing

variable [∀ k, Fintype (B k)]

theorem Achievable.mono {W : DMC (∀ k, A k) (∀ k, B k)} {R R' : Fin K → ℝ}
    (h : Achievable W R) (h' : ∀ k, R' k ≤ R k) : Achievable W R' := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨L, hL, c, hc⟩ := hN n hn
  exact ⟨L, fun k => (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (h' k)
    (Nat.cast_nonneg n))).trans (hL k), c, hc⟩

theorem Achievable.max_zero {W : DMC (∀ k, A k) (∀ k, B k)} {R : Fin K → ℝ}
    (h : Achievable W R) : Achievable W fun k => max (R k) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨L, hL, c, hc⟩ := hN n hn
  exact ⟨L, fun k => exp_mul_max_le (hL k), c, hc⟩

theorem mem_closure_achievableRegion (W : DMC (∀ k, A k) (∀ k, B k)) {R : Fin K → ℝ}
    (h0 : ∀ k, 0 ≤ R k) (h : ∀ δ > 0, Achievable W fun k => R k - δ) :
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
  exact ⟨fun k => max (R k - η / 2) 0, ⟨fun k => le_max_right _ _,
    (h (η / 2) (by positivity)).max_zero⟩, (dist_pi_lt_iff hη).2 fun k => key _ (h0 k)⟩

private lemma exists_code_of_eq {M : Fin K → Type*} [∀ k, Fintype (M k)]
    [∀ k, DecidableEq (M k)] {W : DMC (∀ k, A k) (∀ k, B k)} {ε : ℝ≥0∞} {n m : ℕ} (h : n = m)
    (hc : ∃ c : ICKCode M A B n, c.avgError W ≤ ε) :
    ∃ c : ICKCode M A B m, c.avgError W ≤ ε := h ▸ hc

theorem Achievable.timeSharing {W : DMC (∀ k, A k) (∀ k, B k)} {R R' : Fin K → ℝ}
    (h : Achievable W R) (h' : Achievable W R') {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) {δ : ℝ} (hδ : 0 < δ) :
    Achievable W fun k => a * R k + b * R' k - δ := by
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    exact h'.mono fun k => by linarith
  rcases hb.eq_or_lt with rfl | hb'
  · obtain rfl : a = 1 := by linarith
    exact h.mono fun k => by linarith
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨N', hN'⟩ := h' (ε / 2) (ENNReal.half_pos hε.ne')
  set D := ∑ k, |R k - R' k|
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (max (N / a) (N' / b)) (D / δ))
  refine ⟨N₀, fun n hn => ?_⟩
  have hn' : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hNa : (N : ℝ) < a * n := (div_lt_iff₀' ha').1 (((le_max_left _ _).trans
    (le_max_left _ _)).trans_lt (hN₀.trans_le hn'))
  have hNb : (N' : ℝ) < b * n := (div_lt_iff₀' hb').1 (((le_max_right _ _).trans
    (le_max_left _ _)).trans_lt (hN₀.trans_le hn'))
  have hnδ : D < n * δ := (div_lt_iff₀ hδ).1 ((le_max_right _ _).trans_lt (hN₀.trans_le hn'))
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
  obtain ⟨L, hL, c, hc⟩ := hN n₁ hn₁N
  obtain ⟨L', hL', c', hc'⟩ := hN' (n - n₁) hn₂N
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
  refine ⟨fun k => L k * L' k, fun k => hrate (hL k) (hL' k)
    ((single_le_sum (fun j _ => abs_nonneg (R j - R' j)) (mem_univ k)).trans_lt hnδ), ?_⟩
  have hk0 : ∀ {R : ℝ} {m k : ℕ}, Real.exp (m * R) ≤ k → 0 < k := fun hk =>
    Nat.cast_pos.1 ((Real.exp_pos _).trans_le hk)
  have : ∀ k, Nonempty (Fin (L k)) := fun k => ⟨⟨0, hk0 (hL k)⟩⟩
  have : ∀ k, Nonempty (Fin (L' k)) := fun k => ⟨⟨0, hk0 (hL' k)⟩⟩
  refine exists_code_of_eq (Nat.add_sub_cancel' hn₁n)
    ⟨(c.append c').relabel fun k => finProdFinEquiv, ?_⟩
  rw [← ICKCode.avgError_toMACKCode, ICKCode.toMACKCode_relabel, MACKCode.avgError_relabel,
    ICKCode.toMACKCode_append]
  calc _ ≤ c.toMACKCode.avgError W + c'.toMACKCode.avgError W :=
        c.toMACKCode.avgError_append_le c'.toMACKCode W
    _ ≤ ε / 2 + ε / 2 := add_le_add hc hc'
    _ = ε := ENNReal.add_halves ε

theorem convex_closure_achievableRegion (W : DMC (∀ k, A k) (∀ k, B k)) :
    Convex ℝ (closure (achievableRegion W)) := by
  have key : ∀ x ∈ achievableRegion W, ∀ y ∈ achievableRegion W, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → a • x + b • y ∈ closure (achievableRegion W) := by
    rintro x ⟨hx0, hx⟩ y ⟨hy0, hy⟩ a b ha hb hab
    refine mem_closure_achievableRegion W (fun k => ?_) fun δ hδ => ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hx0 k)) (mul_nonneg hb (hy0 k))
    · simpa using hx.timeSharing hy ha hb hab hδ
  intro x hx y hy a b ha hb hab
  have hf : Continuous (Function.uncurry fun x y : Fin K → ℝ => a • x + b • y) :=
    (show Continuous fun p : (Fin K → ℝ) × (Fin K → ℝ) => a • p.1 + b • p.2 from
      (continuous_fst.const_smul a).add (continuous_snd.const_smul b))
  have h := map_mem_closure₂ hf hx hy fun x' hx' y' hy' => key x' hx' y' hy' a b ha hb hab
  rwa [closure_closure] at h

end TimeSharing

section Marginal

variable [∀ k, Fintype (B k)] [∀ k, DecidableEq (B k)]

theorem blockProb_out {n : ℕ} (W : DMC (∀ k, A k) (∀ k, B k)) (k : Fin K)
    (x : Fin n → ∀ k, A k) (z : Fin n → B k) :
    DMC.blockProb (out W k) x z =
      ∑ y : Fin n → ∀ k, B k, if (fun i => y i k) = z then DMC.blockProb W x y else 0 := by
  have h : ∀ i, out W k (x i) (z i) = ∑ b : ∀ k, B k, if b k = z i then W (x i) b else 0 := by
    intro i
    rw [out, PMF.map_apply, tsum_fintype]
    refine sum_congr rfl fun b _ => ?_
    by_cases hb : b k = z i
    · simp [hb]
    · simp [hb, Ne.symm hb]
  simp only [DMC.blockProb, h]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : ∀ i, y i k = z i
  · rw [ite_eq_left (funext hy)]
    exact prod_congr rfl fun i _ => ite_eq_left (hy i)
  · obtain ⟨i, hi⟩ := not_forall.1 hy
    rw [ite_eq_right fun h => hi (congrFun h i)]
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

omit [∀ k, DecidableEq (B k)] in
theorem sum_mul_blockProb_out {n : ℕ} (W : DMC (∀ k, A k) (∀ k, B k)) (k : Fin K)
    (x : Fin n → ∀ k, A k) (F : (Fin n → B k) → ℝ≥0∞) :
    ∑ y : Fin n → ∀ k, B k, F (fun i => y i k) * DMC.blockProb W x y =
      ∑ z, F z * DMC.blockProb (out W k) x z := by
  classical
  simp only [blockProb_out, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_eq_single (fun i => y i k) (fun z _ hz => by simp [Ne.symm hz]) (by simp)]
  simp

end Marginal

end ICK

namespace ICKCode

variable {K : ℕ} {M A B : Fin K → Type*} {n : ℕ}

def ofMACKCodes (enc : ∀ k, M k → Fin n → A k) (dec : ∀ k, (Fin n → B k) → ∀ j, M j) :
    ICKCode M A B n :=
  ⟨enc, fun k y => dec k y k⟩

theorem errorProb_ofMACKCodes_le [∀ k, Fintype (B k)] [∀ k, DecidableEq (M k)]
    (enc : ∀ k, M k → Fin n → A k)
    (dec : ∀ k, (Fin n → B k) → ∀ j, M j) (W : DMC (∀ k, A k) (∀ k, B k)) (m : ∀ k, M k) :
    (ofMACKCodes enc dec).errorProb W m ≤
      ∑ k, (MACKCode.mk enc (dec k)).errorProb (ICK.out W k) m := by
  classical
  set x : Fin n → ∀ k, A k := fun i k => enc k (m k) i
  have e : ∀ k, (MACKCode.mk enc (dec k)).errorProb (ICK.out W k) m =
      ∑ z : Fin n → B k, (if dec k z = m then 0 else 1) * DMC.blockProb (ICK.out W k) x z := by
    intro k
    refine sum_congr rfl fun z _ => ?_
    split_ifs
    · simp
    · rw [one_mul]
      rfl
  simp only [e]
  simp only [← ICK.sum_mul_blockProb_out W _ x (fun z => if dec _ z = m then 0 else 1)]
  rw [sum_comm, errorProb]
  refine sum_le_sum fun y _ => ?_
  by_cases hd : (fun k => (ofMACKCodes enc dec).dec k fun i => y i k) = m
  · rw [ite_eq_left hd]
    exact bot_le
  · rw [ite_eq_right hd]
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hd
    have hk' : dec k (fun i => y i k) ≠ m := fun h => hk (by simp [ofMACKCodes, h])
    calc DMC.blockProb W (fun i k => enc k (m k) i) y =
          (if dec k (fun i => y i k) = m then 0 else 1) * DMC.blockProb W x y := by
          rw [ite_eq_right hk', one_mul]
      _ ≤ _ := single_le_sum (f := fun k => (if dec k (fun i => y i k) = m then 0 else 1) *
          DMC.blockProb W x y) (fun _ _ => bot_le) (mem_univ k)

end ICKCode

namespace ICK

variable {K : ℕ} {A B : Fin K → Type*}
  [∀ k, Fintype (A k)] [∀ k, MeasurableSpace (A k)] [∀ k, MeasurableSingletonClass (A k)]
  [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)] [∀ k, MeasurableSingletonClass (B k)]

noncomputable def compoundRegion (W : DMC (∀ k, A k) (∀ k, B k)) : Set (Fin K → ℝ) :=
  closure (convexHull ℝ (⋃ p : ∀ k, PMF (A k), ⋂ k, MACK.polymatroid (out W k) p))

noncomputable def typicalCode {M : Fin K → Type*} {n : ℕ} (W : DMC (∀ k, A k) (∀ k, B k))
    (p : ∀ k, PMF (A k)) (ε : ℝ) (C : ∀ k, M k → Fin n → A k) (m₀ : ∀ k, M k) :
    ICKCode M A B n :=
  ICKCode.ofMACKCodes C fun k =>
    BlockCode.typicalDecoder (MACK.codeInput C) (MACK.decodingSet (out W k) p n ε) m₀

noncomputable def typicalBound {M : Fin K → Type*} [∀ k, Fintype (M k)] {n : ℕ}
    (W : DMC (∀ k, A k) (∀ k, B k)) (p : ∀ k, PMF (A k)) (ε : ℝ) (k : Fin K) : ℝ :=
  (1 - ∑ xy ∈ MACK.decodingSet (out W k) p n ε,
      iidProb (DMC.jointPMF (out W k) (piPMF p)) (fun i => (xy.1 i, xy.2 i))) +
    ∑ S ∈ univ.erase (∅ : Finset (Fin K)), (∏ j ∈ S, ((Fintype.card (M j) : ℝ) - 1)) *
      Real.exp (-(n * ((MACK.sideChannel (out W k) p S).inputMutualInfo
        (piPMF fun j : {j // j ∈ S} => p j) - 3 * ε)))

omit [∀ k, MeasurableSingletonClass (A k)] [∀ k, MeasurableSingletonClass (B k)] in
theorem exists_typicalCode_avgError_le {M : Fin K → Type*} [∀ k, Fintype (M k)]
    [∀ k, DecidableEq (M k)] {n : ℕ} (W : DMC (∀ k, A k) (∀ k, B k)) (p : ∀ k, PMF (A k))
    (ε : ℝ) (m₀ : ∀ k, M k) :
    ∃ C : ∀ k, M k → Fin n → A k, (typicalCode W p ε C m₀).avgError W ≤
      ENNReal.ofReal (∑ k, typicalBound (M := M) (n := n) W p ε k) := by
  classical
  have : Nonempty (∀ k, M k) := ⟨m₀⟩
  set β := ∑ k, typicalBound (M := M) (n := n) W p ε k
  have hw : ∀ C : ∀ k, M k → Fin n → A k, 0 ≤ MACK.codebookWeight p C :=
    fun C => prod_nonneg fun k _ => prod_nonneg fun j _ => iidProb_nonneg _ _
  have h1 : ∑ C : ∀ k, M k → Fin n → A k, MACK.codebookWeight p C = 1 := by
    unfold MACK.codebookWeight
    calc ∑ C : ∀ k, M k → Fin n → A k, ∏ k, ∏ j, iidProb (p k) (C k j) =
        ∏ k, ∑ c : M k → Fin n → A k, ∏ j, iidProb (p k) (c j) :=
          (Fintype.prod_sum fun k (c : M k → Fin n → A k) => ∏ j, iidProb (p k) (c j)).symm
      _ = 1 := prod_eq_one fun k _ =>
        sum_prod (fun _ x => iidProb (p k) x) (fun _ => sum_iidProb _ n)
  have hm : ∀ m : ∀ k, M k, ∑ C : ∀ k, M k → Fin n → A k, MACK.codebookWeight p C *
      ((typicalCode W p ε C m₀).errorProb W m).toReal ≤ β := by
    intro m
    calc _ ≤ ∑ C, ∑ k, MACK.codebookWeight p C *
          ((MACKCode.typicalCode C (MACK.decodingSet (out W k) p n ε) m₀).errorProb
            (out W k) m).toReal := by
          refine sum_le_sum fun C _ => ?_
          rw [← mul_sum, ← ENNReal.toReal_sum fun k _ => MACKCode.errorProb_ne_top _ _ _]
          exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (ENNReal.sum_ne_top.2
            fun k _ => MACKCode.errorProb_ne_top _ _ _)
            (ICKCode.errorProb_ofMACKCodes_le C _ W m)) (hw C)
      _ ≤ β := by
          rw [sum_comm]
          exact sum_le_sum fun k _ => MACK.sum_errorProb_typicalCode_le (out W k) p ε m₀ m
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le (w := MACK.codebookWeight p)
    (f := fun C => ∑ m, ((typicalCode W p ε C m₀).errorProb W m).toReal)
    (t := Fintype.card (∀ k, M k) * β) hw h1 (by
      simp only [mul_sum]
      rw [sum_comm]
      calc _ ≤ ∑ m : ∀ k, M k, β := sum_le_sum fun m _ => hm m
        _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul])
  refine ⟨C, ?_⟩
  rw [← ICKCode.avgError_toMACKCode, ← MACKCode.avgError_toBlockCode]
  exact BlockCode.avgError_le_ofReal _ W hC

private lemma mul_exp_le {n : ℕ} {x R I I' η : ℝ} (hx : x ≤ Real.exp (n * R)) (hI : I ≤ I')
    (hη : 4 * η ≤ I - R) : x * Real.exp (-(n * (I' - 3 * η))) ≤ Real.exp (n * (-η)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc x * Real.exp (-(n * (I' - 3 * η))) ≤ Real.exp (n * R) * Real.exp (-(n * (I - 3 * η))) :=
        mul_le_mul hx (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (n * R - n * (I - 3 * η)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (n * (-η)) := Real.exp_le_exp.2 (by nlinarith)

theorem achievable_of_lt (W : DMC (∀ k, A k) (∀ k, B k)) (p : ∀ k, PMF (A k))
    {R : Fin K → ℝ}
    (h : ∀ k, ∀ S : Finset (Fin K), S.Nonempty → ∑ j ∈ S, R j < MACK.subsetInfo (out W k) p S) :
    Achievable W R := by
  classical
  intro ε hε
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  set g : Fin K × Finset (Fin K) → ℝ := fun q =>
    if q.2 = ∅ then 1 else MACK.subsetInfo (out W q.1) p q.2 - ∑ j ∈ q.2, R j
  have hne : (univ : Finset (Fin K × Finset (Fin K))).Nonempty ∨ IsEmpty (Fin K) := by
    rcases isEmpty_or_nonempty (Fin K) with h0 | ⟨⟨k⟩⟩
    · exact Or.inr h0
    · exact Or.inl ⟨(k, ∅), mem_univ _⟩
  obtain ⟨η, hη0, hηS⟩ : ∃ η : ℝ, 0 < η ∧ ∀ k, ∀ S ∈ univ.erase (∅ : Finset (Fin K)),
      4 * η ≤ MACK.subsetInfo (out W k) p S - ∑ j ∈ S, R j := by
    rcases hne with hu | h0
    · refine ⟨univ.inf' hu g / 4, div_pos ((lt_inf'_iff _).2 fun q _ => ?_) (by norm_num),
        fun k S hS => ?_⟩
      · by_cases hq : q.2 = ∅
        · simp [g, hq]
        · simp only [g, hq, ite_false]
          linarith [h q.1 q.2 (nonempty_iff_ne_empty.2 hq)]
      · have := inf'_le g (mem_univ (k, S))
        simp only [g, ne_of_mem_erase hS, ite_false] at this
        linarith
    · exact ⟨1, one_pos, fun k => isEmptyElim k⟩
  set c : ℝ := ((univ.erase (∅ : Finset (Fin K))).card : ℝ)
  have hJ : ∀ k, Tendsto (fun n : ℕ => (1 - ∑ xy ∈ MACK.decodingSet (out W k) p n η,
      iidProb (DMC.jointPMF (out W k) (piPMF p)) (fun i => (xy.1 i, xy.2 i))) +
        c * Real.exp (n * (-η))) atTop (𝓝 0) := by
    intro k
    have h1 : Tendsto (fun n : ℕ => 1 - ∑ xy ∈ MACK.decodingSet (out W k) p n η,
        iidProb (DMC.jointPMF (out W k) (piPMF p)) (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
        (MACK.tendsto_sum_iidProb_decodingSet (out W k) p hη0)
    simpa using h1.add ((tendsto_exp_nat_mul (neg_neg_of_pos hη0)).const_mul c)
  have hsum := tendsto_finsetSum univ fun k _ => hJ k
  rw [sum_const_zero] at hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  set L : Fin K → ℕ := fun k => ⌈Real.exp (n * R k)⌉₊
  have hL : ∀ k, 0 < L k := fun k => Nat.ceil_pos.2 (Real.exp_pos _)
  have hL' : ∀ k, (L k : ℝ) - 1 ≤ Real.exp (n * R k) := fun k => by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R k)).le]
  have hL0 : ∀ k, (0 : ℝ) ≤ L k - 1 := fun k => by
    have : (1 : ℝ) ≤ L k := Nat.one_le_cast.2 (hL k)
    linarith
  refine ⟨L, fun k => Nat.le_ceil _, ?_⟩
  obtain ⟨C, hC⟩ := exists_typicalCode_avgError_le (n := n) W p η
    (fun k => (⟨0, hL k⟩ : Fin (L k)))
  refine ⟨_, hC.trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hδε.le)⟩
  have hb : ∀ k, typicalBound (M := fun k => Fin (L k)) (n := n) W p η k ≤
      (1 - ∑ xy ∈ MACK.decodingSet (out W k) p n η,
        iidProb (DMC.jointPMF (out W k) (piPMF p)) (fun i => (xy.1 i, xy.2 i))) +
          c * Real.exp (n * (-η)) := by
    intro k
    have hS : ∀ S ∈ univ.erase (∅ : Finset (Fin K)),
        (∏ j ∈ S, ((Fintype.card (Fin (L j)) : ℝ) - 1)) *
          Real.exp (-(n * ((MACK.sideChannel (out W k) p S).inputMutualInfo
            (piPMF fun j : {j // j ∈ S} => p j) - 3 * η))) ≤ Real.exp (n * (-η)) := by
      intro S hS
      refine mul_exp_le ?_ (MACK.subsetInfo_le_inputMutualInfo (out W k) p S) (hηS k S hS)
      rw [mul_sum, Real.exp_sum]
      exact prod_le_prod₀ (fun j _ => by rw [Fintype.card_fin]; exact hL0 j)
        fun j _ => by rw [Fintype.card_fin]; exact hL' j
    have := sum_le_sum hS
    rw [sum_const, nsmul_eq_mul] at this
    unfold typicalBound
    linarith
  linarith [sum_le_sum fun k (_ : k ∈ univ) => hb k, hN n hn]

theorem inter_polymatroid_subset_closure_achievableRegion (W : DMC (∀ k, A k) (∀ k, B k))
    (p : ∀ k, PMF (A k)) :
    (⋂ k, MACK.polymatroid (out W k) p) ⊆ closure (achievableRegion W) := by
  intro R hR
  have hR' : ∀ k, R ∈ MACK.polymatroid (out W k) p := Set.mem_iInter.1 hR
  rcases isEmpty_or_nonempty (Fin K) with h0 | ⟨⟨k₀⟩⟩
  · exact mem_closure_achievableRegion W (fun k => isEmptyElim k) fun δ hδ =>
      achievable_of_lt W p fun k => isEmptyElim k
  refine mem_closure_achievableRegion W (hR' k₀).1 fun δ hδ =>
    achievable_of_lt W p fun k S hne => ?_
  have hc : (0 : ℝ) < S.card := Nat.cast_pos.2 (card_pos.2 hne)
  calc ∑ j ∈ S, (R j - δ) = ∑ j ∈ S, R j - S.card * δ := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    _ < ∑ j ∈ S, R j := by nlinarith
    _ ≤ MACK.subsetInfo (out W k) p S := (hR' k).2 S

theorem compoundRegion_subset_closure_achievableRegion (W : DMC (∀ k, A k) (∀ k, B k)) :
    compoundRegion W ⊆ closure (achievableRegion W) :=
  closure_minimal (convexHull_min (Set.iUnion_subset fun p =>
    inter_polymatroid_subset_closure_achievableRegion W p)
    (convex_closure_achievableRegion W)) isClosed_closure

end ICK

end Meat
