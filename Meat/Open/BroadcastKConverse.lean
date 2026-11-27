import Meat.Open.BroadcastConverse
import Meat.Channel.BroadcastK

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace BCK

section Help

variable {Ω S T U : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

private lemma entropy_eq_of_comp {X : Ω → S} {X' : Ω → T} (hX : Measurable X)
    (hX' : Measurable X') (f : S → T) (g : T → S) (hf : ∀ ω, X' ω = f (X ω))
    (hg : ∀ ω, X ω = g (X' ω)) : H[X' ; μ] = H[X ; μ] := by
  have h1 := entropy_comp_le μ hX f
  have h2 := entropy_comp_le μ hX' g
  have e1 : f ∘ X = X' := funext fun ω => (hf ω).symm
  have e2 : g ∘ X' = X := funext fun ω => (hg ω).symm
  rw [e1] at h1
  rw [e2] at h2
  linarith

private lemma condEntropy_eq_of_comp_left {X : Ω → S} {X' : Ω → T} {Z : Ω → U} (hX : Measurable X)
    (hX' : Measurable X') (hZ : Measurable Z) (f : S → T) (g : T → S) (hf : ∀ ω, X' ω = f (X ω))
    (hg : ∀ ω, X ω = g (X' ω)) : H[X' | Z ; μ] = H[X | Z ; μ] := by
  rw [condEntropy_def, condEntropy_def, entropy_eq_of_comp μ (hX.prodMk hZ) (hX'.prodMk hZ)
    (Prod.map f id) (Prod.map g id) (fun ω => by simp [hf ω]) (fun ω => by simp [hg ω])]

private lemma condEntropy_eq_of_comp_right {X : Ω → S} {Z : Ω → T} {Z' : Ω → U} (hX : Measurable X)
    (hZ : Measurable Z) (hZ' : Measurable Z') (f : T → U) (g : U → T) (hf : ∀ ω, Z' ω = f (Z ω))
    (hg : ∀ ω, Z ω = g (Z' ω)) : H[X | Z' ; μ] = H[X | Z ; μ] := by
  rw [condEntropy_def, condEntropy_def, entropy_eq_of_comp μ (hX.prodMk hZ) (hX.prodMk hZ')
    (Prod.map id f) (Prod.map id g) (fun ω => by simp [hf ω]) (fun ω => by simp [hg ω]),
    entropy_eq_of_comp μ hZ hZ' f g hf hg]

private lemma condEntropy_le_of_comp {X : Ω → S} {Z : Ω → T} {Z' : Ω → U} (hX : Measurable X)
    (hZ : Measurable Z) (f : T → U) (hf : ∀ ω, Z' ω = f (Z ω)) : H[X | Z ; μ] ≤ H[X | Z' ; μ] := by
  have e : Z' = f ∘ Z := funext hf
  rw [e]
  exact condEntropy_le_condEntropy_comp (μ := μ) hX hZ f

end Help

private lemma map_pair_apply {U A Y S : Type*} [Finite U] [Fintype A] [Finite Y]
    (σ : PMF (U × A × Y)) (σ₂ : U × A → ℝ≥0∞) (V : A → PMF Y)
    (h : ∀ u x y, σ (u, x, y) = σ₂ (u, x) * V x y) (F : Y → S) (u : U) (s : S) :
    σ.map (fun r => (r.1, F r.2.2)) (u, s) = ∑ x, σ₂ (u, x) * (V x).map F s := by
  classical
  have := Fintype.ofFinite U
  have := Fintype.ofFinite Y
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Finset.sum_eq_single u (fun b _ hb => Finset.sum_eq_zero fun _ _ => by simp [Ne.symm hb])
      (by simp)]
  simp only [Fintype.sum_prod_type, h]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [PMF.map_apply, tsum_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : s = F y <;> simp [hy]

variable {K : ℕ} {A : Type*} {B : Fin K → Type*}

section Twin

variable (D : ∀ (k : Fin K) (_ : k.val + 1 < K), DMC (B k) (B ⟨k.val + 1, ‹_›⟩)) (d : ∀ k, B k)

private noncomputable def chainTail (k : Fin K) (b : B k) : PMF (∀ j, B j) :=
  if h : k.val + 1 < K then
    (D k h b).bind fun b' => (chainTail ⟨k.val + 1, h⟩ b').map fun y => Function.update y k b
  else PMF.pure (Function.update d k b)
termination_by K - k.val

private def tailOf (k : Fin K) (y : ∀ j, B j) : ∀ j, B j :=
  fun j => if k < j then y j else d j

private theorem chainTail_eq_map (k : Fin K) (b : B k) :
    chainTail D d k b = (chainTail D d k b).map fun y => Function.update y k b := by
  rw [chainTail]
  split_ifs with h
  · rw [PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, Function.update_idem]
  · simp [PMF.pure_map]

private theorem map_chainTail_apply_self {S : Type*} (k : Fin K) (b : B k) (F : (∀ j, B j) → S)
    (hF : ∀ y c, F (Function.update y k c) = F y) :
    (chainTail D d k b).map (fun y => (y k, F y)) = (chainTail D d k b).map fun y => (b, F y) := by
  rw [chainTail_eq_map, PMF.map_comp, PMF.map_comp]
  congr 1
  funext y
  simp [hF]

private theorem tailOf_update (k : Fin K) (y : ∀ j, B j) (c : B k) :
    tailOf d k (Function.update y k c) = tailOf d k y := by
  funext j
  by_cases h : k < j
  · simp [tailOf, h, Function.update_of_ne (ne_of_gt h)]
  · simp [tailOf, h]

variable [NeZero K]

private noncomputable def chainTwin (W : DMC A (∀ k, B k)) : DMC A (∀ k, B k) :=
  fun a => (out W 0 a).bind (chainTail D d 0)

private theorem map_chainTwin (W : DMC A (∀ k, B k))
    (hD : ∀ (k : Fin K) (h : k.val + 1 < K) a, out W ⟨k.val + 1, h⟩ a = (out W k a).bind (D k h))
    (a : A) (k : Fin K) :
    (chainTwin D d W a).map (fun y => (y k, tailOf d k y)) =
      (out W k a).bind fun b => (chainTail D d k b).map fun y => (b, tailOf d k y) := by
  obtain ⟨t, ht⟩ := k
  induction t with
  | zero =>
    rw [chainTwin, PMF.map_bind]
    congr 1
    funext b
    exact map_chainTail_apply_self D d _ b _ (tailOf_update d _)
  | succ t ih =>
    have ht' : t < K := by omega
    have e : (fun y : ∀ j, B j => (y ⟨t + 1, ht⟩, tailOf d ⟨t + 1, ht⟩ y)) =
        (fun p : B ⟨t, ht'⟩ × (∀ j, B j) => (p.2 ⟨t + 1, ht⟩, tailOf d ⟨t + 1, ht⟩ p.2)) ∘
          fun y => (y ⟨t, ht'⟩, tailOf d ⟨t, ht'⟩ y) := by
      funext y
      have h1 : (⟨t, ht'⟩ : Fin K) < ⟨t + 1, ht⟩ := by simp [Fin.lt_def]
      refine Prod.ext (by simp [tailOf, h1]) (funext fun j => ?_)
      by_cases h : (⟨t + 1, ht⟩ : Fin K) < j
      · have h2 : (⟨t, ht'⟩ : Fin K) < j := lt_trans h1 h
        simp [tailOf, h, h2]
      · simp [tailOf, h]
    rw [e, ← PMF.map_comp, ih ht', PMF.map_bind, hD ⟨t, ht'⟩ ht, PMF.bind_bind]
    congr 1
    funext b
    rw [PMF.map_comp]
    conv_lhs => rw [chainTail]
    rw [dite_eq_left_of_eq_true (eq_true ht), PMF.map_bind]
    congr 1
    funext b'
    rw [PMF.map_comp]
    have e2 : ((fun p : B ⟨t, ht'⟩ × (∀ j, B j) => (p.2 ⟨t + 1, ht⟩, tailOf d ⟨t + 1, ht⟩ p.2)) ∘
        (fun y => (b, tailOf d ⟨t, ht'⟩ y)) ∘ fun y => Function.update y ⟨t, ht'⟩ b) =
        fun y => (y ⟨t + 1, ht⟩, tailOf d ⟨t + 1, ht⟩ y) := by
      funext y
      have h1 : (⟨t, ht'⟩ : Fin K) < ⟨t + 1, ht⟩ := by simp [Fin.lt_def]
      refine Prod.ext ?_ (funext fun j => ?_)
      · simp [tailOf, h1]
      · by_cases h : (⟨t + 1, ht⟩ : Fin K) < j
        · have h2 : (⟨t, ht'⟩ : Fin K) < j := lt_trans h1 h
          simp [tailOf, h, h2, Function.update_of_ne (ne_of_gt h2)]
        · simp [tailOf, h]
    rw [Function.comp_assoc, e2]
    exact map_chainTail_apply_self D d _ b' _ (tailOf_update d _)

private theorem out_chainTwin (W : DMC A (∀ k, B k))
    (hD : ∀ (k : Fin K) (h : k.val + 1 < K) a, out W ⟨k.val + 1, h⟩ a = (out W k a).bind (D k h))
    (k : Fin K) : out (chainTwin D d W) k = out W k := by
  funext a
  have h := congrArg (PMF.map Prod.fst) (map_chainTwin D d W hD a k)
  rw [PMF.map_comp, PMF.map_bind] at h
  simp only [PMF.map_comp, Function.comp_def] at h
  rw [out, h]
  have e : ∀ b : B k, (chainTail D d k b).map (fun _ => b) = PMF.pure b := fun b =>
    PMF.map_const _ b
  simp only [e, PMF.bind_pure]

private lemma map_chainTwin_apply (W : DMC A (∀ k, B k))
    (hD : ∀ (k : Fin K) (h : k.val + 1 < K) a, out W ⟨k.val + 1, h⟩ a = (out W k a).bind (D k h))
    (a : A) (k : Fin K) (b : B k) (z : ∀ j, B j) :
    (chainTwin D d W a).map (fun y => (y k, tailOf d k y)) (b, z) =
      out W k a b * (chainTail D d k b).map (tailOf d k) z := by
  classical
  rw [map_chainTwin D d W hD, PMF.bind_apply, tsum_eq_single b fun b' hb' => by
    rw [PMF.map_apply, ENNReal.tsum_eq_zero.2 fun y => by simp [Ne.symm hb'], mul_zero]]
  congr 1
  have e : (fun y : ∀ j, B j => (b, tailOf d k y)) = (fun t => (b, t)) ∘ tailOf d k := rfl
  rw [e, ← PMF.map_comp]
  exact map_apply_inj _ (fun _ _ h => congrArg Prod.snd h) z

end Twin

section Letter

private def fill {X : Fin K → Type*} (z : ∀ k, X k) (S : Finset (Fin K)) (x : ∀ k, X k) :
    ∀ k, X k :=
  fun j => if j ∈ S then x j else z j

private lemma fill_fill {X : Fin K → Type*} (z : ∀ k, X k) {S S' : Finset (Fin K)} (h : S ⊆ S')
    (x : ∀ k, X k) : fill z S (fill z S' x) = fill z S x := by
  funext j
  by_cases hj : j ∈ S
  · simp [fill, hj, h hj]
  · simp [fill, hj]

private lemma fill_self {X : Fin K → Type*} (z : ∀ k, X k) (S : Finset (Fin K)) :
    fill z S z = z := by
  funext j
  simp [fill]

private def layerY (j : Fin K) : Finset (Fin K) :=
  univ.filter fun l => j.val ≤ l.val + 1

private lemma layer_subset_layerY (j : Fin K) : layer j ⊆ layerY j := by
  intro l hl
  simp only [layer, layerY, mem_filter, mem_univ, true_and, Fin.le_def] at hl ⊢
  omega

private lemma layer_subset_above {k j : Fin K} (h : k < j) : layer j ⊆ above k := by
  intro l hl
  simp only [layer, above, mem_filter, mem_univ, true_and] at hl ⊢
  exact lt_of_lt_of_le h hl

private lemma layerY_subset_layer {k j : Fin K} (h : k < j) : layerY j ⊆ layer k := by
  intro l hl
  simp only [layer, layerY, mem_filter, mem_univ, true_and, Fin.le_def, Fin.lt_def] at hl h ⊢
  omega

private lemma above_subset_layer (k : Fin K) : above k ⊆ layer k := by
  intro l hl
  simp only [layer, above, mem_filter, mem_univ, true_and] at hl ⊢
  exact hl.le

private lemma mem_layer_self (k : Fin K) : k ∈ layer k := by simp [layer]

variable {M : Fin K → Type*} {n : ℕ}

private def auxV (m₀ : ∀ k, M k) (d : ∀ k, B k) (j : Fin K)
    (u : (∀ k, M k) × (Fin n → ∀ k, B k)) : (∀ k, M k) × (Fin n → ∀ k, B k) :=
  (fill m₀ (layer j) u.1, fun i => fill d (layerY j) (u.2 i))

variable [∀ k, Fintype (M k)] [∀ k, MeasurableSpace (M k)] [∀ k, MeasurableSingletonClass (M k)]
  [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)] [∀ k, MeasurableSingletonClass (B k)]
  [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
  (D : ∀ (k : Fin K) (_ : k.val + 1 < K), DMC (B k) (B ⟨k.val + 1, ‹_›⟩)) (d : ∀ k, B k)

private lemma letter_le [NeZero K] (W : DMC A (∀ k, B k))
    (hD : ∀ (k : Fin K) (h : k.val + 1 < K) a, out W ⟨k.val + 1, h⟩ a = (out W k a).bind (D k h))
    (σ : PMF (((∀ k, M k) × (Fin n → ∀ k, B k)) × A × ∀ k, B k))
    (hσ : ∀ u x y, σ (u, x, y) = (σ.map fun r => (r.1, r.2.1)) (u, x) * chainTwin D d W x y)
    (m₀ : ∀ k, M k) (k : Fin K) :
    H[fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) => fill d (layer k) r.2.2 |
        fun r => (fill m₀ (above k) r.1.1, fun i => fill d (layer k) (r.1.2 i)) ; σ.toMeasure] -
      H[fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) => fill d (layer k) r.2.2 |
        fun r => (fill m₀ (layer k) r.1.1, fun i => fill d (layer k) (r.1.2 i)) ; σ.toMeasure] ≤
      H[fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) => r.2.2 k |
        fun r => MACK.mask (above k) fun j => auxV m₀ d j r.1 ; σ.toMeasure] -
      H[fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) => r.2.2 k |
        fun r => MACK.mask (layer k) fun j => auxV m₀ d j r.1 ; σ.toMeasure] := by
  classical
  have := Fintype.ofFinite A
  set μ := σ.toMeasure
  set Z := fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) => fill d (layer k) r.2.2
  set Yk := fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) => r.2.2 k
  set Tk := fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) => tailOf d k r.2.2
  set Ab := fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) =>
    MACK.mask (above k) fun j => auxV m₀ d j r.1
  set Ly := fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) =>
    MACK.mask (layer k) fun j => auxV m₀ d j r.1
  have ha : H[Z | Ly ; μ] ≤ H[Z | fun r => (fill m₀ (layer k) r.1.1,
      fun i => fill d (layer k) (r.1.2 i)) ; μ] :=
    condEntropy_le_of_comp μ (measurable_of_finite _) (measurable_of_finite _)
      (fun w => (w k).elim (m₀, fun _ => d) fun v => (v.1, fun i => fill d (layer k) (v.2 i)))
      fun r => by
        simp only [Ly, MACK.mask, mem_layer_self, ite_true, Option.elim, auxV]
        simp only [fill_fill d (layer_subset_layerY k)]
  have hb : H[Z | fun r => (fill m₀ (above k) r.1.1, fun i => fill d (layer k) (r.1.2 i)) ; μ] ≤
      H[Z | Ab ; μ] :=
    condEntropy_le_of_comp μ (measurable_of_finite _) (measurable_of_finite _)
      (fun a j => if k < j then some (fill m₀ (layer j) a.1, fun i => fill d (layerY j) (a.2 i))
        else none)
      fun r => by
        funext j
        by_cases hj : k < j
        · simp only [Ab, MACK.mask, auxV]
          rw [ite_eq_left (by simp [above, hj] : j ∈ above k), ite_eq_left hj]
          simp only [fill_fill m₀ (layer_subset_above hj), fill_fill d (layerY_subset_layer hj)]
        · simp [Ab, MACK.mask, above, hj]
  have hsplit : ∀ C : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) →
      MACK.Masked fun _ : Fin K => (∀ k, M k) × (Fin n → ∀ k, B k),
      H[Z | C ; μ] = H[Yk | C ; μ] + H[Tk | fun r => (Yk r, C r) ; μ] := by
    intro C
    rw [← condEntropy_pair_eq_add]
    refine (condEntropy_eq_of_comp_left μ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (fun z => (z k, tailOf d k z))
      (fun p => Function.update p.2 k p.1) (fun r => ?_) fun r => ?_).symm
    · refine Prod.ext (by simp [Z, Yk, fill, mem_layer_self]) (funext fun j => ?_)
      by_cases hj : k < j
      · simp [Z, Tk, tailOf, fill, hj, layer, hj.le]
      · simp [Z, Tk, tailOf, hj]
    · funext j
      by_cases hj : j = k
      · subst hj
        simp [Z, Yk, fill, mem_layer_self]
      · by_cases hkj : k < j
        · simp [Z, Tk, tailOf, fill, hj, hkj, layer, hkj.le]
        · have : j ∉ layer k := by
            simp only [layer, mem_filter, mem_univ, true_and, not_le]
            exact lt_of_le_of_ne (not_lt.1 hkj) hj
          simp [Z, Tk, tailOf, fill, hj, hkj, this]
  have hmk : MarkovChain (fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) => r.1)
      Yk Tk μ := by
    refine BC.markovChain_of_pmf σ _ _ _ (fun b z => (chainTail D d k b).map (tailOf d k) z)
      fun u b z => ?_
    have h1 := map_pair_apply σ _ (chainTwin D d W) hσ (fun y => (y k, tailOf d k y)) u (b, z)
    have h2 := map_pair_apply σ _ (chainTwin D d W) hσ (fun y => y k) u b
    change σ.map (fun r => (r.1, (fun y => (y k, tailOf d k y)) r.2.2)) (u, b, z) =
      σ.map (fun r => (r.1, (fun y => y k) r.2.2)) (u, b) * _
    rw [h1, h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_chainTwin_apply D d W hD, mul_assoc]
    congr 2
    exact (congrFun (congrArg DFunLike.coe (congrFun (out_chainTwin D d W hD k) x)) b).symm
  have hI : I[Ly : Tk | Yk ; μ] = 0 := by
    refine le_antisymm ?_ (condMutualInfo_nonneg _ (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _))
    have := condMutualInfo_comp_left_le (μ := μ)
      (X := fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) => r.1) (Y := Tk) (Z := Yk)
      (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
      (fun u => MACK.mask (layer k) fun j => auxV m₀ d j u)
    rw [markovChain_def] at hmk
    exact this.trans_eq hmk
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy] at hI
  have hsw : H[Tk | fun r => (Yk r, Ly r) ; μ] = H[Tk | fun r => (Ly r, Yk r) ; μ] :=
    condEntropy_eq_of_comp_right μ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) Prod.swap Prod.swap (fun _ => rfl) fun _ => rfl
  have hd : H[Tk | fun r => (Yk r, Ab r) ; μ] ≤ H[Tk | Yk ; μ] :=
    condEntropy_le_of_comp μ (measurable_of_finite _) (measurable_of_finite _) Prod.fst
      fun _ => rfl
  have e1 := hsplit Ab
  have e2 := hsplit Ly
  linarith

end Letter

section Code

variable {M : Fin K → Type*} {n : ℕ}

private def toBlock (c : BCKCode M A B n) : BlockCode (∀ k, M k) A (∀ k, B k) n :=
  ⟨c.enc, c.decode⟩

variable [∀ k, Fintype (M k)] [∀ k, Nonempty (M k)] [∀ k, DecidableEq (M k)]
  [∀ k, MeasurableSpace (M k)] [∀ k, MeasurableSingletonClass (M k)]
  [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)] [∀ k, MeasurableSingletonClass (B k)]

omit [∀ k, Nonempty (M k)] [∀ k, MeasurableSpace (M k)] [∀ k, MeasurableSingletonClass (M k)]
  [∀ k, MeasurableSpace (B k)] [∀ k, MeasurableSingletonClass (B k)] in
private lemma avgError_toBlock (c : BCKCode M A B n) (W : DMC A (∀ k, B k)) :
    (toBlock c).avgError W = c.avgError W := by
  rw [BlockCode.avgError, BCKCode.avgError, Fintype.card_pi, Nat.cast_prod]
  rfl

omit [∀ k, MeasurableSpace (B k)] [∀ k, MeasurableSingletonClass (B k)] in
private lemma blockProb_out [∀ k, DecidableEq (B k)] (V : DMC A (∀ k, B k)) (k : Fin K)
    (x : Fin n → A)
    (z : Fin n → B k) :
    DMC.blockProb (out V k) x z =
      ∑ y : Fin n → ∀ j, B j, if (fun i => y i k) = z then DMC.blockProb V x y else 0 := by
  refine (ENNReal.toReal_eq_toReal_iff' (DMC.blockProb_ne_top _ _ _)
    (ENNReal.sum_ne_top.2 fun y _ => by split_ifs <;> simp [DMC.blockProb_ne_top])).1 ?_
  rw [show out V k = fun a => (V a).map fun b => b k from rfl, DMC.toReal_blockProb_map,
    ENNReal.toReal_sum fun y _ => by split_ifs <;> simp [DMC.blockProb_ne_top], Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

omit [∀ k, DecidableEq (M k)] [∀ k, MeasurableSpace (M k)] [∀ k, MeasurableSingletonClass (M k)]
  [∀ k, MeasurableSpace (B k)] [∀ k, MeasurableSingletonClass (B k)] in
private lemma codePMF_map_out (c : BlockCode (∀ k, M k) A (∀ k, B k) n)
    (V : DMC A (∀ k, B k))
    (k : Fin K) :
    (BC.codePMF c V).map (fun ω => (ω.1, fun i => ω.2 i k)) =
      BC.codePMF (⟨c.enc, fun _ => Classical.arbitrary _⟩ :
        BlockCode (∀ k, M k) A (B k) n) (out V k) := by
  classical
  ext ⟨m, z⟩
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Finset.sum_eq_single m (fun b _ hb => Finset.sum_eq_zero fun _ _ => by simp [Ne.symm hb])
      (by simp)]
  simp only [BC.codePMF, PMF.ofFintype_apply, blockProb_out, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : (fun i => y i k) = z
  · simp [h]
  · simp [Ne.symm h, h]

private lemma error_le (c : BCKCode M A B n) {V W : DMC A (∀ k, B k)}
    (k : Fin K) (hk : out V k = out W k) :
    ((toBlock c).codeMeasure V).real {ω | c.dec k (fun i => ω.2 i k) ≠ ω.1 k} ≤
      (c.avgError W).toReal := by
  classical
  set g := fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => (ω.1, fun i => ω.2 i k)
  have hmap : ((toBlock c).codeMeasure V).map g = ((toBlock c).codeMeasure W).map g := by
    rw [BC.codeMeasure_eq, BC.codeMeasure_eq, PMF.toMeasure_map _ _ (measurable_of_finite _),
      PMF.toMeasure_map _ _ (measurable_of_finite _), codePMF_map_out, codePMF_map_out, hk]
  have hS : MeasurableSet {p : (∀ k, M k) × (Fin n → B k) | c.dec k p.2 ≠ p.1 k} :=
    (Set.toFinite _).measurableSet
  have e : ∀ μ : Measure ((∀ k, M k) × (Fin n → ∀ k, B k)),
      μ.real {ω | c.dec k (fun i => ω.2 i k) ≠ ω.1 k} =
        (μ.map g).real {p | c.dec k p.2 ≠ p.1 k} := fun μ => by
    rw [map_measureReal_apply (measurable_of_finite _) hS]
    rfl
  rw [e, hmap, ← e, ← avgError_toBlock, ← BlockCode.measureReal_dec_ne]
  refine measureReal_mono (fun ω h h' => h ?_)
  rw [← h']
  rfl

omit [∀ k, DecidableEq (M k)] in
private lemma log_card_le_condEntropy (c : BlockCode (∀ k, M k) A (∀ k, B k) n)
    (V : DMC A (∀ k, B k)) (m₀ : ∀ k, M k) (k : Fin K) :
    Real.log (Fintype.card (M k)) ≤
      H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => ω.1 k | fun ω => fill m₀ (above k) ω.1 ;
        c.codeMeasure V] := by
  classical
  set μ := c.codeMeasure V
  set Rest := fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => fun j : {j // j ≠ k} => ω.1 j
  have h1 : H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => ω.1 k | Rest ; μ] ≤
      H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => ω.1 k | fun ω => fill m₀ (above k) ω.1 ; μ] :=
    condEntropy_le_of_comp μ (measurable_of_finite _) (measurable_of_finite _)
      (fun r j => if h : j ∈ above k then r ⟨j, ne_of_gt (mem_filter.1 h).2⟩ else m₀ j)
      fun ω => by
        funext j
        by_cases h : j ∈ above k <;> simp [fill, h, Rest]
  have h3 : H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => (ω.1 k, Rest ω) ; μ] =
      H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => ω.1 ; μ] :=
    entropy_eq_of_comp μ (measurable_of_finite _) (measurable_of_finite _)
      (fun m => (m k, fun j => m j))
      (fun p j => if h : j = k then h ▸ p.1 else p.2 ⟨j, h⟩) (fun _ => rfl) fun ω => by
        funext j
        by_cases h : j = k
        · subst h
          simp
        · simp [h, Rest]
  have h4 := BlockCode.entropy_fst_codeMeasure c V
  have h5 := entropy_le_log_card μ (X := Rest)
  have hc : (Fintype.card (∀ k, M k) : ℝ) =
      Fintype.card (M k) * Fintype.card (∀ j : {j // j ≠ k}, M j) := by
    rw [Fintype.card_pi, Fintype.card_pi, Fintype.prod_eq_mul_prod_subtype_ne _ k]
    push_cast
    rfl
  have hp1 : (0 : ℝ) < Fintype.card (M k) := Nat.cast_pos.2 Fintype.card_pos
  have hp2 : (0 : ℝ) < Fintype.card (∀ j : {j // j ≠ k}, M j) := Nat.cast_pos.2 Fintype.card_pos
  rw [hc, Real.log_mul hp1.ne' hp2.ne'] at h4
  rw [condEntropy_def, h3] at h1
  linarith

omit [∀ k, DecidableEq (M k)] in
private lemma condEntropy_seq_eq [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (c : BlockCode (∀ k, M k) A (∀ k, B k) n) (V : DMC A (∀ k, B k))
    (d : ∀ k, B k) (κ : (∀ k, M k) → X) (S : Finset (Fin K)) :
    H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => fun i => fill d S (ω.2 i) | fun ω => κ ω.1 ;
        c.codeMeasure V] =
      ∑ q, H[fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) => fill d S r.2.2 |
        fun r => (κ r.1.1, fun i => fill d S (r.1.2 i)) ;
        (BC.letterPMF c V id q d).toMeasure] := by
  classical
  rw [condEntropy_eq_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [BC.letterPMF, ← PMF.toMeasure_map _ _ (measurable_of_finite _), ← BC.codeMeasure_eq,
    condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
  refine (condEntropy_eq_of_comp_right _ (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _)
    (fun p : X × (Fin q → ∀ j, B j) =>
      (p.1, fun j : Fin n => if h : (j : ℕ) < q then p.2 ⟨j, h⟩ else d))
    (fun p : X × (Fin n → ∀ j, B j) => (p.1, fun j : Fin q => p.2 ⟨j, j.2.trans q.2⟩))
    (fun ω => ?_) fun ω => ?_).symm
  · refine Prod.ext rfl (funext fun j => ?_)
    by_cases h : (j : ℕ) < q
    · have h' : j < q := Fin.lt_def.2 h
      simp [BC.padPrefix, seqPrefix, h']
    · have h' : ¬ j < q := fun h' => h (Fin.lt_def.1 h')
      simp [BC.padPrefix, h', fill_self]
  · refine Prod.ext rfl (funext fun j => ?_)
    have h' : (⟨j, j.2.trans q.2⟩ : Fin n) < q := Fin.lt_def.2 j.2
    simp [BC.padPrefix, seqPrefix, h']

private lemma code_bound_seq (c : BCKCode M A B n)
    {V W : DMC A (∀ k, B k)} (k : Fin K) (hk : out V k = out W k) (m₀ : ∀ k, M k)
    (d : ∀ k, B k) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card (M k)) - Real.log 2 ≤
      H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => fun i => fill d (layer k) (ω.2 i) |
          fun ω => fill m₀ (above k) ω.1 ; (toBlock c).codeMeasure V] -
        H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => fun i => fill d (layer k) (ω.2 i) |
          fun ω => fill m₀ (layer k) ω.1 ; (toBlock c).codeMeasure V] := by
  classical
  have e1 := condMutualInfo_eq_condEntropy_sub_condEntropy ((toBlock c).codeMeasure V)
    (X := fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => ω.1 k)
    (Y := fun ω => fun i => fill d (layer k) (ω.2 i)) (Z := fun ω => fill m₀ (above k) ω.1)
  have e2 : H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => fun i => fill d (layer k) (ω.2 i) |
      fun ω => (ω.1 k, fill m₀ (above k) ω.1) ; (toBlock c).codeMeasure V] =
      H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => fun i => fill d (layer k) (ω.2 i) |
        fun ω => fill m₀ (layer k) ω.1 ; (toBlock c).codeMeasure V] := by
    refine condEntropy_eq_of_comp_right ((toBlock c).codeMeasure V)
      (X := fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => fun i => fill d (layer k) (ω.2 i))
      (Z := fun ω => fill m₀ (layer k) ω.1) (Z' := fun ω => (ω.1 k, fill m₀ (above k) ω.1))
      (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (fun ml : ∀ k, M k => (ml k, fill m₀ (above k) ml))
      (fun p : M k × (∀ k, M k) => Function.update p.2 k p.1) (fun ω => ?_) fun ω => ?_
    · refine Prod.ext (by simp [fill, mem_layer_self]) ?_
      exact (fill_fill m₀ (above_subset_layer k) _).symm
    · funext j
      by_cases hj : j = k
      · subst hj
        simp [fill, mem_layer_self]
      · have : j ∈ layer k ↔ j ∈ above k := by
          simp only [layer, above, mem_filter, mem_univ, true_and]
          exact ⟨fun h => lt_of_le_of_ne h (Ne.symm hj), le_of_lt⟩
        simp [fill, hj, this]
  have e3 := condMutualInfo_eq_condEntropy_sub_condEntropy ((toBlock c).codeMeasure V)
    (X := fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => fun i => fill d (layer k) (ω.2 i))
    (Y := fun ω => ω.1 k) (Z := fun ω => fill m₀ (above k) ω.1)
  have e4 := condMutualInfo_comm ((toBlock c).codeMeasure V)
    (X := fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => ω.1 k)
    (Y := fun ω => fun i => fill d (layer k) (ω.2 i)) (Z := fun ω => fill m₀ (above k) ω.1)
  have e5 : H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => ω.1 k |
      fun ω => (fun i => fill d (layer k) (ω.2 i), fill m₀ (above k) ω.1) ;
        (toBlock c).codeMeasure V] ≤
      H[fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => ω.1 k | fun ω i => ω.2 i k ;
        (toBlock c).codeMeasure V] :=
    condEntropy_le_of_comp ((toBlock c).codeMeasure V) (measurable_of_finite _)
      (measurable_of_finite _)
      (fun p : (Fin n → ∀ j, B j) × (∀ k, M k) => fun i => p.1 i k) fun ω => by
        funext i
        simp [fill, mem_layer_self]
  have e6 := condEntropy_le_log_two_add_mul_log_card (μ := (toBlock c).codeMeasure V)
    (X := fun ω : (∀ k, M k) × (Fin n → ∀ k, B k) => ω.1 k)
    (Y := fun ω i => ω.2 i k) (measurable_of_finite _) (measurable_of_finite _) (c.dec k)
  have e7 := error_le c k hk
  have e8 := log_card_le_condEntropy (toBlock c) V m₀ k
  have hl : 0 ≤ Real.log (Fintype.card (M k)) := Real.log_natCast_nonneg _
  have e9 := mul_le_mul_of_nonneg_right e7 hl
  linarith

private lemma code_bound [NeZero K] [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (D : ∀ (k : Fin K) (_ : k.val + 1 < K), DMC (B k) (B ⟨k.val + 1, ‹_›⟩)) (d : ∀ k, B k)
    (W : DMC A (∀ k, B k))
    (hD : ∀ (k : Fin K) (h : k.val + 1 < K) a, out W ⟨k.val + 1, h⟩ a = (out W k a).bind (D k h))
    (c : BCKCode M A B n) (m₀ : ∀ k, M k) (k : Fin K) :
    (1 - (c.avgError W).toReal) * Real.log (Fintype.card (M k)) - Real.log 2 ≤
      ∑ q, (H[fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) =>
          fill d (layer k) r.2.2 | fun r => (fill m₀ (above k) r.1.1,
            fun i => fill d (layer k) (r.1.2 i)) ;
          (BC.letterPMF (toBlock c) (chainTwin D d W) id q d).toMeasure] -
        H[fun r : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) =>
          fill d (layer k) r.2.2 | fun r => (fill m₀ (layer k) r.1.1,
            fun i => fill d (layer k) (r.1.2 i)) ;
          (BC.letterPMF (toBlock c) (chainTwin D d W) id q d).toMeasure]) := by
  rw [Finset.sum_sub_distrib, ← condEntropy_seq_eq, ← condEntropy_seq_eq]
  exact code_bound_seq c k (out_chainTwin D d W hD k) m₀ d

end Code

section Region

variable {Ω S S' T U U' : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype S'] [MeasurableSpace S'] [MeasurableSingletonClass S']
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype U'] [MeasurableSpace U'] [MeasurableSingletonClass U']

private lemma condMutualInfo_comp_inj' (μ : Measure Ω) {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
    {f : S → S'} {h : U → U'} (hf : Function.Injective f) (hh : Function.Injective h) :
    I[fun ω => f (X ω) : Y | fun ω => h (Z ω) ; μ] = I[X : Y | Z ; μ] := by
  have e1 : H[fun ω => (f (X ω), h (Z ω)) ; μ] = H[fun ω => (X ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Z ω)) (f := Prod.map f h) (hf.prodMap hh)
  have e2 : H[fun ω => (Y ω, h (Z ω)) ; μ] = H[fun ω => (Y ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (Y ω, Z ω)) (f := Prod.map id h)
      (Function.injective_id.prodMap hh)
  have e3 : H[fun ω => ((f (X ω), Y ω), h (Z ω)) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω))
      (f := Prod.map (Prod.map f id) h) ((hf.prodMap Function.injective_id).prodMap hh)
  have e4 : H[fun ω => h (Z ω) ; μ] = H[Z ; μ] := entropy_comp_of_injective μ hh
  simp only [condMutualInfo_def, condEntropy_def]
  rw [e1, e2, e3, e4]

variable [NeZero K] [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)]
  [∀ k, MeasurableSingletonClass (B k)]
  {V V' : Fin K → Type*} [∀ j, Fintype (V j)] [∀ j, MeasurableSpace (V j)]
  [∀ j, MeasurableSingletonClass (V j)] [∀ j, Fintype (V' j)] [∀ j, MeasurableSpace (V' j)]
  [∀ j, MeasurableSingletonClass (V' j)]

private def relabelMask (e : ∀ j, V j ≃ V' j) (w : MACK.Masked V) : MACK.Masked V' :=
  fun j => (w j).map (e j)

omit [∀ k, Fintype (B k)]
  [∀ k, MeasurableSpace (B k)] [∀ k, MeasurableSingletonClass (B k)] [∀ j, Fintype (V j)]
  [∀ j, MeasurableSpace (V j)] [∀ j, MeasurableSingletonClass (V j)] in
private lemma layerPMF_map_out (W : DMC A (∀ k, B k)) (law : PMF (∀ j, V j)) (f : V 0 → A)
    (k : Fin K) :
    (layerPMF W law f).map (fun ω => (ω.1, ω.2 k)) =
      law.bind fun v => (out W k (f (v 0))).map fun y => (v, y) := by
  simp only [layerPMF, out, PMF.map_bind, PMF.map_comp, Function.comp_def]

private lemma regionTerm_eq (W : DMC A (∀ k, B k)) (law : PMF (∀ j, V j)) (f : V 0 → A)
    (k : Fin K) :
    I[fun ω : (∀ j, V j) × (∀ k, B k) => MACK.mask (layer k) ω.1 : fun ω => ω.2 k |
        fun ω => MACK.mask (above k) ω.1 ; (layerPMF W law f).toMeasure] =
      I[fun ω : (∀ j, V j) × B k => MACK.mask (layer k) ω.1 : fun ω => ω.2 |
        fun ω => MACK.mask (above k) ω.1 ;
        (law.bind fun v => (out W k (f (v 0))).map fun y => (v, y)).toMeasure] := by
  rw [← layerPMF_map_out, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
  rfl

private theorem superpositionRegion_congr {W W' : DMC A (∀ k, B k)} (h : ∀ k, out W k = out W' k)
    (law : PMF (∀ j, V j)) (f : V 0 → A) :
    superpositionRegion W law f = superpositionRegion W' law f := by
  ext R
  simp only [superpositionRegion, Set.mem_ofPred_eq, regionTerm_eq, h]

private theorem superpositionRegion_map_equiv (W : DMC A (∀ k, B k)) (law : PMF (∀ j, V j))
    (f : V 0 → A) (e : ∀ j, V j ≃ V' j) :
    superpositionRegion W (law.map fun v j => e j (v j)) (fun a => f ((e 0).symm a)) =
      superpositionRegion W law f := by
  have hl : layerPMF W (law.map fun v j => e j (v j)) (fun a => f ((e 0).symm a)) =
      (layerPMF W law f).map fun ω => (fun j => e j (ω.1 j), ω.2) := by
    simp only [layerPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def,
      Equiv.symm_apply_apply]
  have hinj : Function.Injective (relabelMask e) := by
    intro w w' hw
    funext j
    exact Option.map_injective (e j).injective (congrFun hw j)
  ext R
  simp only [superpositionRegion, Set.mem_ofPred_eq, hl]
  refine and_congr Iff.rfl (forall_congr' fun k => ?_)
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
  have e1 : (fun ω : (∀ j, V' j) × (∀ k, B k) => MACK.mask (layer k) ω.1) ∘
      (fun ω : (∀ j, V j) × (∀ k, B k) => (fun j => e j (ω.1 j), ω.2)) =
      fun ω => relabelMask e (MACK.mask (layer k) ω.1) := by
    funext ω j
    by_cases hj : j ∈ layer k <;> simp [MACK.mask, relabelMask, hj]
  have e2 : (fun ω : (∀ j, V' j) × (∀ k, B k) => MACK.mask (above k) ω.1) ∘
      (fun ω : (∀ j, V j) × (∀ k, B k) => (fun j => e j (ω.1 j), ω.2)) =
      fun ω => relabelMask e (MACK.mask (above k) ω.1) := by
    funext ω j
    by_cases hj : j ∈ above k <;> simp [MACK.mask, relabelMask, hj]
  rw [e1, e2, condMutualInfo_comp_inj' _ hinj hinj]
  rfl

end Region

section Single

variable {M : Fin K → Type*} {n : ℕ}

private lemma letterPMF_eq [∀ k, Fintype (M k)] [∀ k, Nonempty (M k)] [∀ k, Fintype (B k)]
    (c : BCKCode M A B n) (V : DMC A (∀ k, B k)) (q : Fin n) (d : ∀ k, B k) :
    BC.letterPMF (toBlock c) V id q d =
      ((BC.letterPMF (toBlock c) V id q d).map Prod.fst).bind fun u =>
        (V (c.enc u.1 q)).map fun y => (u, c.enc u.1 q, y) := by
  classical
  have h12 : (BC.letterPMF (toBlock c) V id q d).map (fun r => (r.1, r.2.1)) =
      ((BC.letterPMF (toBlock c) V id q d).map Prod.fst).map fun u => (u, c.enc u.1 q) := by
    simp only [BC.letterPMF, PMF.map_comp]
    rfl
  have e : ((BC.letterPMF (toBlock c) V id q d).map Prod.fst).bind (fun u =>
        (V (c.enc u.1 q)).map fun y => (u, c.enc u.1 q, y)) =
      ((BC.letterPMF (toBlock c) V id q d).map (fun r => (r.1, r.2.1))).bind fun p =>
        (V p.2).map fun y => (p.1, p.2, y) := by
    rw [h12]
    exact (PMF.bind_map _ (fun u => (u, c.enc u.1 q))
      fun p : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A => (V p.2).map fun y => (p.1, p.2, y)).symm
  rw [e]
  ext ⟨u, x, y⟩
  have hinj : Function.Injective fun y' : (∀ k, B k) => (u, x, y') := fun a b h => by
    simp only [Prod.mk.injEq] at h
    exact h.2.2
  have hz : ∀ p : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A, p ≠ (u, x) →
      (V p.2).map (fun y => (p.1, p.2, y)) (u, x, y) = 0 := fun p hp => by
    rw [PMF.map_apply]
    refine ENNReal.tsum_eq_zero.2 fun y' => ?_
    split_ifs with h
    · simp only [Prod.mk.injEq] at h
      exact absurd (Prod.ext h.1.symm h.2.1.symm) hp
    · rfl
  rw [BC.letterPMF_apply, PMF.bind_apply,
    tsum_eq_single (u, x) fun p hp => by rw [hz p hp, mul_zero]]
  exact congrArg _ (map_apply_inj _ hinj y).symm

private lemma auxV_zero [NeZero K] (m₀ : ∀ k, M k) (d : ∀ k, B k)
    (u : (∀ k, M k) × (Fin n → ∀ k, B k)) : (auxV m₀ d 0 u).1 = u.1 := by
  funext j
  simp [auxV, fill, layer]

variable [NeZero K]
  [∀ k, Fintype (M k)] [∀ k, Nonempty (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, MeasurableSingletonClass (M k)] [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)]
  [∀ k, MeasurableSingletonClass (B k)] [Finite A] [MeasurableSpace A]
  [MeasurableSingletonClass A]

private lemma mixture_mem [NeZero n] (W : DMC A (∀ k, B k))
    (D : ∀ (k : Fin K) (_ : k.val + 1 < K), DMC (B k) (B ⟨k.val + 1, ‹_›⟩)) (d : ∀ k, B k)
    (hD : ∀ (k : Fin K) (h : k.val + 1 < K) a, out W ⟨k.val + 1, h⟩ a = (out W k a).bind (D k h))
    (c : BCKCode M A B n) (m₀ : ∀ k, M k) {r : Fin K → ℝ} (h0 : ∀ k, 0 ≤ r k)
    (h : ∀ k, n * r k ≤ ∑ q, (H[fun ω : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) =>
        ω.2.2 k | fun ω => MACK.mask (above k) fun j => auxV m₀ d j ω.1 ;
        (BC.letterPMF (toBlock c) (chainTwin D d W) id q d).toMeasure] -
      H[fun ω : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) =>
        ω.2.2 k | fun ω => MACK.mask (layer k) fun j => auxV m₀ d j ω.1 ;
        (BC.letterPMF (toBlock c) (chainTwin D d W) id q d).toMeasure])) :
    r ∈ superpositionUnion W := by
  classical
  set W' := chainTwin D d W
  set σ := fun q => BC.letterPMF (toBlock c) W' id q d
  set τ := fun q => (σ q).map Prod.fst
  set ρ := DMC.jointPMF σ (BC.unifPMF n)
  let v : Fin n × ((∀ k, M k) × (Fin n → ∀ k, B k)) →
      ∀ _ : Fin K, Fin n × ((∀ k, M k) × (Fin n → ∀ k, B k)) :=
    fun p j => (p.1, auxV m₀ d j p.2)
  let law := ρ.map fun p => v (p.1, p.2.1)
  let f : Fin n × ((∀ k, M k) × (Fin n → ∀ k, B k)) → A := fun p => c.enc p.2.1 p.1
  have hρ : ρ = (BC.unifPMF n).bind fun q => (τ q).bind fun u =>
      (W' (c.enc u.1 q)).map fun y => (q, u, c.enc u.1 q, y) := by
    simp only [ρ, DMC.jointPMF]
    congr 1
    funext q
    rw [show σ q = BC.letterPMF (toBlock c) W' id q d from rfl, letterPMF_eq c W' q d,
      PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, τ, σ]
  have hl : layerPMF W' law f = ρ.map fun p => (v (p.1, p.2.1), p.2.2.2) := by
    simp only [layerPMF, law, hρ, PMF.map_bind, PMF.bind_bind, PMF.map_comp, Function.comp_def,
      PMF.bind_map, PMF.bind_const, v, f, auxV_zero]
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hreg : r ∈ superpositionRegion W' law f := by
    refine ⟨h0, fun k => ?_⟩
    rw [hl, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
      condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
        (measurable_of_finite _) (measurable_of_finite _),
      condMutualInfo_eq_condEntropy_sub_condEntropy]
    set Yk := fun ω : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) => ω.2.2 k
    set Ab := fun ω : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) =>
      MACK.mask (above k) fun j => auxV m₀ d j ω.1
    set Ly := fun ω : ((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) =>
      MACK.mask (layer k) fun j => auxV m₀ d j ω.1
    have a1 := BC.condEntropy_mixture σ Yk Ly
    have a2 := BC.condEntropy_mixture σ Yk Ab
    have c1 : H[fun p : Fin n × (((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k)) =>
        Yk p.2 | fun p => (MACK.mask (layer k) (v (p.1, p.2.1)),
          MACK.mask (above k) (v (p.1, p.2.1))) ; ρ.toMeasure] =
        H[fun p : Fin n × (((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k)) =>
          Yk p.2 | fun p => (p.1, Ly p.2) ; ρ.toMeasure] := by
      refine condEntropy_eq_of_comp_right _ (measurable_of_finite _) (measurable_of_finite _)
        (measurable_of_finite _)
        (fun t => (fun j => (t.2 j).map fun x => (t.1, x),
          fun j => if j ∈ above k then (t.2 j).map fun x => (t.1, x) else none))
        (fun t => ((t.1 k).elim 0 Prod.fst, fun j => (t.1 j).map Prod.snd)) (fun p => ?_)
        fun p => ?_
      · refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
        · by_cases hj : j ∈ layer k <;> simp [MACK.mask, v, Ly, hj]
        · by_cases ha : j ∈ above k
          · have hl' := above_subset_layer k ha
            simp [MACK.mask, v, Ly, ha, hl']
          · simp [MACK.mask, ha]
      · refine Prod.ext (by simp [MACK.mask, mem_layer_self, v]) (funext fun j => ?_)
        by_cases hj : j ∈ layer k <;> simp [MACK.mask, v, Ly, hj]
    have c2 : H[fun p : Fin n × (((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k)) =>
        Yk p.2 | fun p => (p.1, Ab p.2) ; ρ.toMeasure] ≤
        H[fun p : Fin n × (((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k)) =>
          Yk p.2 | fun p => MACK.mask (above k) (v (p.1, p.2.1)) ; ρ.toMeasure] := by
      refine condEntropy_le_of_comp _ (measurable_of_finite _) (measurable_of_finite _)
        (fun t j => (t.2 j).map fun x => (t.1, x)) fun p => ?_
      funext j
      by_cases ha : j ∈ above k <;> simp [MACK.mask, v, Ab, ha]
    have hk := h k
    rw [Finset.sum_sub_distrib] at hk
    have hr : r k ≤ (n : ℝ)⁻¹ * (∑ q, H[Yk | Ab ; (σ q).toMeasure] -
        ∑ q, H[Yk | Ly ; (σ q).toMeasure]) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hn]
      linarith
    change r k ≤ H[fun p : Fin n × (((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k)) =>
        Yk p.2 | fun p => MACK.mask (above k) (v (p.1, p.2.1)) ; ρ.toMeasure] -
      H[fun p : Fin n × (((∀ k, M k) × (Fin n → ∀ k, B k)) × A × (∀ k, B k)) =>
        Yk p.2 | fun p => (MACK.mask (layer k) (v (p.1, p.2.1)),
          MACK.mask (above k) (v (p.1, p.2.1))) ; ρ.toMeasure]
    rw [c1, a1]
    rw [a2] at c2
    rw [mul_sub] at hr
    linarith
  rw [superpositionRegion_congr (fun k => out_chainTwin D d W hD k),
    ← superpositionRegion_map_equiv W law f fun _ => Fintype.equivFin _] at hreg
  simp only [superpositionUnion, Set.mem_iUnion]
  exact ⟨_, _, _, hreg⟩

end Single

section Theorem

variable [NeZero K] [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)] [∀ k, MeasurableSingletonClass (B k)]

theorem achievableRegion_subset_of_isDegraded {W : DMC A (∀ k, B k)} (hW : IsDegraded W) :
    achievableRegion W ⊆ closure (superpositionUnion W) := by
  classical
  choose D hD using fun (k : Fin K) (h : k.val + 1 < K) =>
    hW k ⟨k.val + 1, h⟩ (Fin.le_def.2 (Nat.le_succ _))
  rintro R ⟨h0, hR⟩
  rw [Metric.mem_closure_iff]
  intro δ hδ
  set S := ∑ k, R k
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => h0 k
  have hRS : ∀ k, R k ≤ S := fun k =>
    Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ k)
  set ε₀ := min (1 / 2) (δ / (4 * (S + 1))) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (by norm_num) (by positivity)
  obtain ⟨N, hN⟩ := hR (ENNReal.ofReal ε₀) (ENNReal.ofReal_pos.2 hε₀0)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * Real.log 2 / δ)
  set n := max N (max n₀ 1)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
  have : NeZero n := ⟨by omega⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨L, hL, c, hc⟩ := hN n (le_max_left _ _)
  have hL0 : ∀ k, (0 : ℝ) < L k := fun k => (Real.exp_pos _).trans_le (hL k)
  have : ∀ k, Nonempty (Fin (L k)) := fun k => ⟨⟨0, by exact_mod_cast hL0 k⟩⟩
  set m₀ : ∀ k, Fin (L k) := fun _ => Classical.arbitrary _
  obtain ⟨d, -⟩ := (W (c.enc m₀ ⟨0, by omega⟩)).support_nonempty
  set ε' := (c.avgError W).toReal
  have hε' : ε' ≤ ε₀ := ENNReal.toReal_le_of_le_ofReal hε₀0.le hc
  have hε'0 : 0 ≤ ε' := ENNReal.toReal_nonneg
  have hε'1 : ε' ≤ 1 / 2 := hε'.trans (min_le_left _ _)
  have hlog2 : Real.log 2 / n < δ / 2 := by
    rw [div_lt_iff₀ hnpos]
    have : (n₀ : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 := (div_lt_iff₀ hδ).1 (hn₀.trans_le this)
    linarith
  have hlog2' : 0 ≤ Real.log 2 / n := div_nonneg (Real.log_nonneg (by norm_num)) hnpos.le
  set r : Fin K → ℝ := fun k => max 0 ((1 - ε') * R k - Real.log 2 / n)
  have hmem : r ∈ superpositionUnion W := by
    refine mixture_mem W D d hD c m₀ (fun k => le_max_left _ _) fun k => ?_
    have b := code_bound D d W hD c m₀ k
    simp only [Fintype.card_fin] at b
    have hl := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => letter_le D d W hD
      (BC.letterPMF (toBlock c) (chainTwin D d W) id q d)
      (BC.letterPMF_apply (toBlock c) (chainTwin D d W) id q d) m₀ k
    have hlk : n * R k ≤ Real.log (L k) := (Real.le_log_iff_exp_le (hL0 k)).2 (hL k)
    have hnn : ∀ q, 0 ≤ H[fun ω : ((∀ k, Fin (L k)) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) =>
        ω.2.2 k | fun ω => MACK.mask (above k) fun j => auxV m₀ d j ω.1 ;
        (BC.letterPMF (toBlock c) (chainTwin D d W) id q d).toMeasure] -
      H[fun ω : ((∀ k, Fin (L k)) × (Fin n → ∀ k, B k)) × A × (∀ k, B k) =>
        ω.2.2 k | fun ω => MACK.mask (layer k) fun j => auxV m₀ d j ω.1 ;
        (BC.letterPMF (toBlock c) (chainTwin D d W) id q d).toMeasure] := fun q => by
      refine sub_nonneg.2 (condEntropy_le_of_comp _ (measurable_of_finite _)
        (measurable_of_finite _) (fun w j => if j ∈ above k then w j else none) fun ω => ?_)
      funext j
      by_cases ha : j ∈ above k
      · simp [MACK.mask, ha, above_subset_layer k ha]
      · simp [MACK.mask, ha]
    rw [mul_max_of_nonneg _ _ hnpos.le, mul_zero]
    refine max_le (Finset.sum_nonneg fun q _ => hnn q) ?_
    have hc' : (n : ℝ) * ((1 - ε') * R k - Real.log 2 / n) ≤
        (1 - ε') * Real.log (L k) - Real.log 2 := by
      rw [mul_sub, mul_div_cancel₀ _ hnpos.ne']
      nlinarith
    linarith
  refine ⟨r, hmem, ?_⟩
  rw [dist_pi_lt_iff hδ]
  intro k
  have hS4 : ε₀ * S ≤ δ / 4 := by
    have h1 := min_le_right (1 / 2 : ℝ) (δ / (4 * (S + 1)))
    rw [← hε₀] at h1
    have h2 : δ / (4 * (S + 1)) * S ≤ δ / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have hrR : r k ≤ R k := max_le (h0 k) (by nlinarith [mul_nonneg hε'0 (h0 k)])
  have hrl : (1 - ε') * R k - Real.log 2 / n ≤ r k := le_max_right _ _
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith
  · nlinarith [hRS k]

end Theorem

end BCK

end Meat
