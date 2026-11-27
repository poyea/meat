import Meat.Channel.BroadcastK
import Meat.Channel.BroadcastAchievability
import Meat.Channel.MultipleAccessKAchievability
import Meat.Open.BroadcastConverse

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace BCK

section Cond

variable {X Y : Type*} [Finite X] [Fintype Y]

private lemma map_fst_apply (ρ : PMF (X × Y)) (x : X) : ρ.map Prod.fst x = ∑ y, ρ (x, y) := by
  classical
  have := Fintype.ofFinite X
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Finset.sum_eq_single x (fun b _ hb => Finset.sum_eq_zero fun _ _ => by simp [Ne.symm hb])
      (by simp)]
  simp

private noncomputable def condPMF (ρ : PMF (X × Y)) (x : X) : PMF Y :=
  if h : ρ.map Prod.fst x = 0 then ρ.map Prod.snd
  else PMF.ofFintype (fun y => ρ (x, y) / ρ.map Prod.fst x) (by
    rw [← ENNReal.sum_div, ← map_fst_apply]
    exact ENNReal.div_self h (PMF.apply_ne_top _ _))

private lemma bind_condPMF (ρ : PMF (X × Y)) :
    (ρ.map Prod.fst).bind (fun x => (condPMF ρ x).map fun y => (x, y)) = ρ := by
  classical
  ext ⟨x, y⟩
  rw [PMF.bind_apply, tsum_eq_single x fun x' hx' => mul_eq_zero_of_right _ (by
    rw [PMF.map_apply (fun y => (x', y))]
    exact ENNReal.tsum_eq_zero.2 fun y' => by simp [Prod.ext_iff, Ne.symm hx'])]
  rw [map_apply_inj _ (fun a b h => congrArg Prod.snd h)]
  by_cases h : ρ.map Prod.fst x = 0
  · have hle : ρ (x, y) ≤ ρ.map Prod.fst x := by
      rw [map_fst_apply]
      exact Finset.single_le_sum (f := fun y => ρ (x, y)) (fun _ _ => zero_le) (mem_univ y)
    rw [h, zero_mul]
    exact (le_antisymm (h ▸ hle) zero_le).symm
  · simp only [condPMF, h, ↓reduceDIte]
    rw [PMF.ofFintype_apply,
      ENNReal.mul_div_cancel h (PMF.apply_ne_top _ _)]

end Cond

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

open scoped Classical in
private lemma sum_update_eq (p : ∀ i, PMF (X i)) (l : ι) (a : X l) (x : ∀ i, X i)
    [∀ t : ∀ i, X i, Decidable (x = Function.update t l a)] :
    ∑ t : ∀ i, X i, (if x = Function.update t l a then piPMF p t else 0) =
      if a = x l then ∏ i ∈ univ.erase l, p i (x i) else 0 := by
  have hpt : ∀ t : ∀ i, X i, (if x = Function.update t l a then piPMF p t else 0) =
      ∏ i, (if i = l then (if a = x l then p i (t i) else 0)
        else if x i = t i then p i (t i) else 0) := by
    intro t
    rw [piPMF_apply]
    by_cases h : x = Function.update t l a
    · simp only [h, ↓reduceIte]
      refine prod_congr rfl fun i _ => ?_
      by_cases hi : i = l
      · subst hi
        simp
      · simp [hi]
    · simp only [h, ↓reduceIte]
      symm
      by_cases ha : a = x l
      · have : ∃ i, i ≠ l ∧ x i ≠ t i := by
          by_contra hc
          push Not at hc
          apply h
          funext i
          by_cases hi : i = l
          · subst hi
            simp [ha]
          · simp [hi, hc i hi]
        obtain ⟨i, hi, hne⟩ := this
        exact prod_eq_zero (mem_univ i) (by simp [hi, hne])
      · exact prod_eq_zero (mem_univ l) (by simp [ha])
  simp_rw [hpt]
  rw [← Fintype.prod_sum (fun i (b : X i) => if i = l then (if a = x l then p i b else 0)
    else if x i = b then p i b else 0), ← mul_prod_erase univ _ (mem_univ l)]
  have hl : ∑ b : X l, (if l = l then (if a = x l then p l b else 0)
      else if x l = b then p l b else 0) = if a = x l then 1 else 0 := by
    split_ifs <;> simp_all [sum_pmf_eq_one]
  have hr : ∏ i ∈ univ.erase l, ∑ b : X i, (if i = l then (if a = x l then p i b else 0)
      else if x i = b then p i b else 0) = ∏ i ∈ univ.erase l, p i (x i) := by
    refine prod_congr rfl fun i hi => ?_
    simp [ne_of_mem_erase hi]
  rw [hl, hr]
  split_ifs <;> simp

private lemma piPMF_eq_bind (p : ∀ i, PMF (X i)) (l : ι) :
    piPMF p = (p l).bind fun a => (piPMF p).map fun t => Function.update t l a := by
  ext x
  rw [PMF.bind_apply, tsum_fintype]
  simp_rw [PMF.map_apply, tsum_fintype]
  simp_rw [sum_update_eq]
  rw [Finset.sum_eq_single (x l) (fun b _ hb => by simp [hb]) (by simp)]
  simp only [↓reduceIte]
  rw [piPMF_apply, ← mul_prod_erase univ _ (mem_univ l)]

private lemma piPMF_map_eval (p : ∀ i, PMF (X i)) (l : ι) :
    (piPMF p).map (fun t => t l) = p l := by
  conv_lhs => rw [piPMF_eq_bind p l]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Function.update_self]
  have h : ∀ a : X l, (piPMF p).map (fun _ => a) = PMF.pure a := fun a => PMF.map_const _ a
  simp only [h, PMF.bind_pure]

private lemma piPMF_map_pair {Z : Type*} (p : ∀ i, PMF (X i)) (l : ι) (G : (∀ i, X i) → Z)
    (hG : ∀ t a, G (Function.update t l a) = G t) :
    (piPMF p).map (fun t => (G t, t l)) = ((piPMF p).map G).bind fun w => (p l).map (w, ·) := by
  conv_lhs => rw [piPMF_eq_bind p l]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Function.update_self, hG]
  rw [PMF.bind_map]
  simp only [← PMF.bind_pure_comp, Function.comp_def]
  exact PMF.bind_comm _ _ _

end Pi

section Build

variable {K : ℕ} {V : Fin K → Type*}

private def fill (d : ∀ j, V j) (S : Finset (Fin K)) (x : ∀ j, V j) : ∀ j, V j :=
  fun j => if j ∈ S then x j else d j

private def build (d : ∀ j, V j) (t : ∀ l, (∀ j, V j) → V l) (l : Fin K) : V l :=
  t l fun j => if _h : l < j then build d t j else d j
termination_by K - l.val
decreasing_by
  have := Fin.lt_def.1 _h
  have := j.isLt
  omega

private lemma build_eq (d : ∀ j, V j) (t : ∀ l, (∀ j, V j) → V l) (l : Fin K) :
    build d t l = t l (fill d (above l) (build d t)) := by
  rw [build]
  congr 1
  funext j
  by_cases h : l < j <;> simp [fill, above, h]

private theorem build_congr (d : ∀ j, V j) {t t' : ∀ l, (∀ j, V j) → V l} (j : Fin K)
    (h : ∀ i, j ≤ i → t i = t' i) : build d t j = build d t' j := by
  rw [build, build, h j le_rfl]
  congr 1
  funext i
  split_ifs with hi
  · exact build_congr d i fun i' hi' => h i' (hi.le.trans hi')
  · rfl
termination_by K - j.val
decreasing_by
  have := Fin.lt_def.1 hi
  have := i.isLt
  omega

private lemma fill_above_build_update (d : ∀ j, V j) (t : ∀ l, (∀ j, V j) → V l) (l : Fin K)
    (a : (∀ j, V j) → V l) :
    fill d (above l) (build d (Function.update t l a)) = fill d (above l) (build d t) := by
  funext j
  by_cases h : j ∈ above l
  · simp only [fill, h, ite_true]
    refine build_congr d j fun i hi => ?_
    have : l < i := lt_of_lt_of_le (by simpa [above] using h) hi
    exact Function.update_of_ne (ne_of_gt this) _ _
  · simp [fill, h]

variable [∀ j, Fintype (V j)] [∀ j, DecidableEq (V j)]

private noncomputable def kernel (law : PMF (∀ j, V j)) (d : ∀ j, V j) (l : Fin K)
    (w : ∀ j, V j) : PMF (V l) :=
  condPMF (law.map fun v => (fill d (above l) v, v l)) w

private noncomputable def inputPMF (law : PMF (∀ j, V j)) (d : ∀ j, V j) (l : Fin K) :
    PMF ((∀ j, V j) → V l) :=
  piPMF fun w => kernel law d l w

private noncomputable def repPMF (law : PMF (∀ j, V j)) (d : ∀ j, V j) :
    PMF (∀ l, (∀ j, V j) → V l) :=
  piPMF fun l => inputPMF law d l

omit [∀ j, Fintype (V j)] [∀ j, DecidableEq (V j)] in
private lemma fill_layer_eq (d : ∀ j, V j) (l : Fin K) (x : ∀ j, V j) :
    fill d (layer l) x = Function.update (fill d (above l) x) l (x l) := by
  funext j
  by_cases hj : j = l
  · subst hj
    simp [fill, layer]
  · by_cases h : l < j
    · simp [fill, layer, above, hj, h, h.le]
    · have : ¬ l ≤ j := fun h' => h (lt_of_le_of_ne h' (Ne.symm hj))
      simp [fill, layer, above, hj, h, this]

private lemma map_fill_layer (law : PMF (∀ j, V j)) (d : ∀ j, V j) (l : Fin K)
    (hA : (repPMF law d).map (fun t => fill d (above l) (build d t)) =
      law.map (fill d (above l))) :
    (repPMF law d).map (fun t => fill d (layer l) (build d t)) = law.map (fill d (layer l)) := by
  have e1 : (fun t => fill d (layer l) (build d t)) =
      (fun q : (∀ j, V j) × ((∀ j, V j) → V l) => Function.update q.1 l (q.2 q.1)) ∘
        fun t => (fill d (above l) (build d t), t l) := by
    funext t
    simp only [Function.comp_apply]
    rw [fill_layer_eq, build_eq]
  have e2 : fill d (layer l) = (fun q : (∀ j, V j) × V l => Function.update q.1 l q.2) ∘
      fun v => (fill d (above l) v, v l) := by
    funext v
    exact fill_layer_eq d l v
  rw [e1, ← PMF.map_comp, repPMF, piPMF_map_pair _ l _ fun t a => fill_above_build_update d t l a,
    ← repPMF, hA, e2, ← PMF.map_comp, ← bind_condPMF (law.map fun v => (fill d (above l) v, v l))]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_map]
  congr 1
  funext w
  have h := piPMF_map_eval (fun w => kernel law d l w) (fill d (above l) w)
  rw [show (fun x : (∀ j, V j) → V l => Function.update (fill d (above l) w) l
      (x (fill d (above l) w))) = (fun a => Function.update (fill d (above l) w) l a) ∘
        fun x => x (fill d (above l) w) from rfl, ← PMF.map_comp, inputPMF, h]
  rfl

private theorem map_fill_layer_build (law : PMF (∀ j, V j)) (d : ∀ j, V j) (l : Fin K) :
    (repPMF law d).map (fun t => fill d (layer l) (build d t)) = law.map (fill d (layer l)) := by
  refine map_fill_layer law d l ?_
  by_cases hl : l.val + 1 < K
  · have e : above l = layer ⟨l.val + 1, hl⟩ := by
      ext j
      simp only [above, layer, mem_filter, mem_univ, true_and, Fin.lt_def, Fin.le_def]
      omega
    rw [e]
    exact map_fill_layer_build law d ⟨l.val + 1, hl⟩
  · have e : ∀ x : ∀ j, V j, fill d (above l) x = d := fun x => by
      funext j
      have : j ∉ above l := by
        simp only [above, mem_filter, mem_univ, true_and, Fin.lt_def, not_lt]
        omega
      simp [fill, this]
    have e' : fill d (above l) = fun _ => d := funext e
    simp only [e']
    exact (PMF.map_const _ d).trans (PMF.map_const _ d).symm
termination_by K - l.val

private lemma map_build [NeZero K] (law : PMF (∀ j, V j)) (d : ∀ j, V j) :
    (repPMF law d).map (build d) = law := by
  have h := map_fill_layer_build law d 0
  have e : ∀ x : ∀ j, V j, fill d (layer 0) x = x := fun x => by
    funext j
    simp [fill, layer]
  have e' : fill d (layer 0) = id := funext e
  rw [e', PMF.map_id] at h
  exact h

end Build

section Step

variable {K : ℕ} [NeZero K] {A : Type*} {B : Fin K → Type*} {V : Fin K → Type*}
  [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

private abbrev Inp (V : Fin K → Type*) (l : Fin K) : Type _ := (∀ i, V i) → V l

private noncomputable def repJoint (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (d : ∀ i, V i)
    (f : V 0 → A) (k : Fin K) : PMF ((∀ l, Inp V l) × B k) :=
  DMC.jointPMF (fun t => out W k (f (build d t 0))) (repPMF law d)

private noncomputable def stepChannel (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i))
    (d : ∀ i, V i) (f : V 0 → A) (k j : Fin K) : DMC (Inp V j) (B k × MACK.Masked (Inp V)) :=
  fun a => (repPMF law d).bind fun t =>
    (out W k (f (build d (Function.update t j a) 0))).map fun y => (y, MACK.mask (above j) t)

omit [NeZero K] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
private lemma mask_above_update (j : Fin K) (t : ∀ l, Inp V l) (a : Inp V j) :
    MACK.mask (above j) (Function.update t j a) = MACK.mask (above j) t := by
  funext l
  by_cases h : l ∈ above j
  · have : l ≠ j := ne_of_gt (by simpa [above] using h)
    simp [MACK.mask, h, this]
  · simp [MACK.mask, h]

private lemma jointPMF_stepChannel (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i))
    (d : ∀ i, V i) (f : V 0 → A) (k j : Fin K) :
    DMC.jointPMF (stepChannel W law d f k j) (inputPMF law d j) =
      (repJoint W law d f k).map fun ω => (ω.1 j, (ω.2, MACK.mask (above j) ω.1)) := by
  rw [repJoint]
  conv_rhs => rw [repPMF, piPMF_eq_bind _ j, ← repPMF]
  simp only [DMC.jointPMF, stepChannel, PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def, Function.update_self, mask_above_update]

end Step

section Indep

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

private def swapOut (S : Finset ι) (q : (∀ i, X i) × (∀ i, X i)) : (∀ i, X i) × (∀ i, X i) :=
  (fun i => if i ∈ S then q.1 i else q.2 i, fun i => if i ∈ S then q.2 i else q.1 i)

omit [Fintype ι] [∀ i, Fintype (X i)] in
private lemma swapOut_involutive (S : Finset ι) : Function.Involutive (swapOut (X := X) S) := by
  intro q
  ext i <;> by_cases h : i ∈ S <;> simp [swapOut, h]

private lemma sum_piPMF_mul_mul (p : ∀ i, PMF (X i)) (S : Finset ι) (F G : (∀ i, X i) → ℝ≥0∞)
    (hF : ∀ t t', (∀ i ∈ S, t i = t' i) → F t = F t')
    (hG : ∀ t t', (∀ i ∉ S, t i = t' i) → G t = G t') :
    ∑ t, piPMF p t * F t * G t = (∑ t, piPMF p t * F t) * ∑ t, piPMF p t * G t := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  rw [← Equiv.sum_comp (swapOut_involutive (X := X) S).toPerm]
  have hP : ∀ q : (∀ i, X i) × (∀ i, X i), piPMF p (swapOut S q).1 * piPMF p (swapOut S q).2 =
      piPMF p q.1 * piPMF p q.2 := fun q => by
    simp only [piPMF_apply, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    by_cases h : i ∈ S <;> simp [swapOut, h, mul_comm]
  have hF' : ∀ q : (∀ i, X i) × (∀ i, X i), F (swapOut S q).1 = F q.1 := fun q =>
    hF _ _ fun i hi => by simp [swapOut, hi]
  have hG' : ∀ q : (∀ i, X i) × (∀ i, X i), G (swapOut S q).2 = G q.1 := fun q =>
    hG _ _ fun i hi => by simp [swapOut, hi]
  have e : ∀ q : (∀ i, X i) × (∀ i, X i),
      piPMF p (swapOut S q).1 * F (swapOut S q).1 * (piPMF p (swapOut S q).2 * G (swapOut S q).2) =
        piPMF p q.1 * F q.1 * G q.1 * piPMF p q.2 := fun q => by
    rw [hF', hG', show piPMF p (swapOut S q).1 * F q.1 * (piPMF p (swapOut S q).2 * G q.1) =
      (piPMF p (swapOut S q).1 * piPMF p (swapOut S q).2) * (F q.1 * G q.1) by ring, hP q]
    ring
  simp only [Function.Involutive.coe_toPerm, e]
  rw [Fintype.sum_prod_type' (f := fun a b => piPMF p a * F a * G a * piPMF p b)]
  simp only [← Finset.mul_sum, sum_pmf_eq_one, mul_one]

end Indep

section Markov

variable {K : ℕ} {V : Fin K → Type*}

private def hybrid (t : ∀ l, Inp V l) (L : Finset (Fin K)) (c : ∀ i, V i) : ∀ l, Inp V l :=
  fun l => if l ∈ L then fun _ => c l else t l

private theorem build_hybrid (d : ∀ i, V i) (t : ∀ l, Inp V l) (L : Finset (Fin K))
    (j : Fin K) : build d (hybrid t L (build d t)) j = build d t j := by
  by_cases hj : j ∈ L
  · rw [build]
    simp [hybrid, hj]
  · rw [build, build]
    simp only [hybrid, hj, ite_false]
    congr 1
    funext i
    split_ifs with hi
    · exact build_hybrid d t L i
    · rfl
termination_by K - j.val
decreasing_by
  have := Fin.lt_def.1 hi
  have := i.isLt
  omega

private def unmask (d : ∀ i, V i) (w : MACK.Masked (Inp V)) : ∀ l, Inp V l :=
  fun l => (w l).getD fun _ => d l

private def IsUpper (L : Finset (Fin K)) : Prop :=
  ∀ i ∈ L, ∀ j, i ≤ j → j ∈ L

private lemma fill_build_congr (d : ∀ i, V i) {L : Finset (Fin K)} (hL : IsUpper L)
    {t t' : ∀ l, Inp V l} (h : ∀ i ∈ L, t i = t' i) :
    fill d L (build d t) = fill d L (build d t') := by
  funext j
  by_cases hj : j ∈ L
  · simp only [fill, hj, ite_true]
    exact build_congr d j fun i hi => h i (hL j hj i hi)
  · simp [fill, hj]

private lemma fill_build_unmask (d : ∀ i, V i) {L : Finset (Fin K)} (hL : IsUpper L)
    (t : ∀ l, Inp V l) :
    fill d L (build d (unmask d (MACK.mask L t))) = fill d L (build d t) :=
  fill_build_congr d hL fun i hi => by simp [unmask, MACK.mask, hi]

end Markov

section Reduce

private lemma jointPMF_map_pair_apply {T γ Z : Type*} [Fintype T] [Finite Z] [DecidableEq γ]
    (Q : DMC T Z)
    (P : PMF T) (g : T → γ) (c : γ) (z : Z) :
    (DMC.jointPMF Q P).map (fun ω => (g ω.1, ω.2)) (c, z) =
      ∑ t, if g t = c then P t * Q t z else 0 := by
  classical
  have := Fintype.ofFinite Z
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  refine sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single z (fun z' _ hz => by simp [Prod.ext_iff, Ne.symm hz]) (by simp)]
  by_cases h : g t = c
  · simp [h, DMC.jointPMF_apply]
  · simp [h, Ne.symm h, Prod.ext_iff]

private lemma jointPMF_map_fst_apply {T γ Z : Type*} [Fintype T] [Finite Z] [DecidableEq γ]
    (Q : DMC T Z)
    (P : PMF T) (g : T → γ) (c : γ) :
    (DMC.jointPMF Q P).map (fun ω => g ω.1) c = ∑ t, if g t = c then P t else 0 := by
  classical
  have := Fintype.ofFinite Z
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  refine sum_congr rfl fun t _ => ?_
  by_cases h : g t = c
  · simp only [h, ite_true, DMC.jointPMF_apply, ← Finset.mul_sum, sum_pmf_eq_one, mul_one]
  · simp [h, Ne.symm h]

variable {K : ℕ} [NeZero K] {A : Type*} {B : Fin K → Type*} {V : Fin K → Type*}
  [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, MeasurableSpace (V i)]
  [∀ i, MeasurableSingletonClass (V i)] [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)]
  [∀ k, MeasurableSingletonClass (B k)]

private lemma condEntropy_mask_eq (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (d : ∀ i, V i)
    (f : V 0 → A) (k : Fin K) {L : Finset (Fin K)} (hL : IsUpper L) :
    H[fun ω : (∀ l, Inp V l) × B k => ω.2 | fun ω => MACK.mask L ω.1 ;
        (repJoint W law d f k).toMeasure] =
      H[fun ω : (∀ l, Inp V l) × B k => ω.2 | fun ω => fill d L (build d ω.1) ;
        (repJoint W law d f k).toMeasure] := by
  classical
  set σ := repJoint W law d f k
  set g : (∀ l, Inp V l) → MACK.Masked (Inp V) × (∀ i, V i) :=
    fun t => (MACK.mask L t, fill d L (build d t))
  set κ : (∀ i, V i) → B k → ℝ≥0∞ := fun c z =>
    ∑ t, repPMF law d t * out W k (f (build d (hybrid t L c) 0)) z
  have hm : MarkovChain (fun ω : (∀ l, Inp V l) × B k => MACK.mask L ω.1)
      (fun ω => fill d L (build d ω.1)) (fun ω => ω.2) σ.toMeasure := by
    refine BC.markovChain_of_pmf σ _ _ _ κ fun w c z => ?_
    have hinj : Function.Injective fun q : (MACK.Masked (Inp V) × (∀ i, V i)) × B k =>
        (q.1.1, q.1.2, q.2) := fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2
    have e1 : σ.map (fun ω : (∀ l, Inp V l) × B k =>
        (MACK.mask L ω.1, fill d L (build d ω.1), ω.2)) (w, c, z) =
        σ.map (fun ω => (g ω.1, ω.2)) ((w, c), z) := by
      rw [show (fun ω : (∀ l, Inp V l) × B k => (MACK.mask L ω.1, fill d L (build d ω.1), ω.2)) =
        (fun q : (MACK.Masked (Inp V) × (∀ i, V i)) × B k => (q.1.1, q.1.2, q.2)) ∘
          fun ω => (g ω.1, ω.2) from rfl, ← PMF.map_comp]
      exact map_apply_inj _ hinj ((w, c), z)
    rw [e1, show (fun ω : (∀ l, Inp V l) × B k => (MACK.mask L ω.1, fill d L (build d ω.1))) =
      fun ω => g ω.1 from rfl,
      show σ = DMC.jointPMF (fun t => out W k (f (build d t 0))) (repPMF law d) from rfl,
      jointPMF_map_pair_apply, jointPMF_map_fst_apply]
    have hs : ∀ t, (if g t = (w, c) then repPMF law d t * out W k (f (build d t 0)) z else 0) =
        repPMF law d t * (if g t = (w, c) then 1 else 0) *
          out W k (f (build d (hybrid t L c) 0)) z := fun t => by
      by_cases h : g t = (w, c)
      · have hc : fill d L (build d t) = c := congrArg Prod.snd h
        have hh : hybrid t L c = hybrid t L (build d t) := by
          funext l
          by_cases hl : l ∈ L
          · simp only [hybrid, hl, ite_true]
            rw [← hc]
            simp [fill, hl]
          · simp [hybrid, hl]
        rw [hh, show build d (hybrid t L (build d t)) = build d t from
          funext (build_hybrid d t L)]
        simp [h]
      · simp [h]
    rw [Finset.sum_congr rfl fun t _ => hs t, repPMF, sum_piPMF_mul_mul _ L, ← repPMF]
    · congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs <;> simp
    · intro t t' h
      have : g t = g t' := by
        refine Prod.ext (funext fun l => ?_) (by simp only [g]; exact fill_build_congr d hL h)
        by_cases hl : l ∈ L
        · simp [g, MACK.mask, hl, h l hl]
        · simp [g, MACK.mask, hl]
      rw [this]
    · intro t t' h
      have : hybrid t L c = hybrid t' L c := by
        funext l
        by_cases hl : l ∈ L
        · simp [hybrid, hl]
        · simp [hybrid, hl, h l hl]
      rw [this]
  have hI := hm
  rw [markovChain_def, condMutualInfo_eq_condEntropy_sub_condEntropy] at hI
  have he : H[fun ω : (∀ l, Inp V l) × B k => ω.2 |
      fun ω => (MACK.mask L ω.1, fill d L (build d ω.1)) ; σ.toMeasure] =
      H[fun ω : (∀ l, Inp V l) × B k => ω.2 | fun ω => MACK.mask L ω.1 ; σ.toMeasure] :=
    condEntropy_cond_of_injective _ (e := fun w => (w, fill d L (build d (unmask d w))))
      (fun a b h => congrArg Prod.fst h) fun ω => by
        simp only [fill_build_unmask d hL]
  linarith

end Reduce

section Gen

variable {Ω S T U U' : Type*} [Finite Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype U'] [MeasurableSpace U'] [MeasurableSingletonClass U']
  (μ : Measure Ω) [IsProbabilityMeasure μ]

private lemma condEntropy_congr_cond {X : Ω → S} {Z : Ω → U} {Z' : Ω → U'} (f : U → U')
    (g : U' → U) (hf : ∀ ω, Z' ω = f (Z ω)) (hg : ∀ ω, Z ω = g (Z' ω)) :
    H[X | Z' ; μ] = H[X | Z ; μ] := by
  have h1 := condEntropy_le_condEntropy_comp (μ := μ) (measurable_of_finite X)
    (measurable_of_finite Z) f
  have h2 := condEntropy_le_condEntropy_comp (μ := μ) (measurable_of_finite X)
    (measurable_of_finite Z') g
  rw [show f ∘ Z = Z' from funext fun ω => (hf ω).symm] at h1
  rw [show g ∘ Z' = Z from funext fun ω => (hg ω).symm] at h2
  exact le_antisymm h2 h1

private lemma condMutualInfo_le_mutualInfo_pair (X : Ω → S) (Y : Ω → T) (Z : Ω → U) :
    I[X : Y | Z ; μ] ≤ I[X : fun ω => (Y ω, Z ω) ; μ] := by
  have he : H[fun ω => (X ω, (Y ω, Z ω)) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω))
      (f := fun p => (p.1.1, (p.1.2, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2
  have h0 := mutualInfo_nonneg μ (measurable_of_finite X) (measurable_of_finite Z)
  simp only [condMutualInfo_def, mutualInfo_def, condEntropy_def] at h0 ⊢
  rw [he]
  linarith

end Gen

section Degraded

variable {Ω S T T' U : Type*} [Finite Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype T'] [MeasurableSpace T'] [MeasurableSingletonClass T']
  [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

private lemma condMutualInfo_le_of_markov (X : Ω → S) (G : Ω → U) (Y : Ω → T) (Z : Ω → T')
    (h : MarkovChain (fun ω => (X ω, G ω)) Y Z μ) : I[X : Z | G ; μ] ≤ I[X : Y | G ; μ] := by
  have a := condMutualInfo_eq_condEntropy_sub_condEntropy μ (X := X) (Y := Z) (Z := G)
  have b := condMutualInfo_eq_condEntropy_sub_condEntropy μ (X := X) (Y := Y) (Z := G)
  have c1 := condEntropy_pair_eq_add μ (X := Y) (Y := Z) (Z := G)
  have c2 := condEntropy_pair_eq_add μ (X := Y) (Y := Z) (Z := fun ω => (X ω, G ω))
  have c3 := condEntropy_pair_eq_add μ (X := Z) (Y := Y) (Z := G)
  have c4 := condEntropy_pair_eq_add μ (X := Z) (Y := Y) (Z := fun ω => (X ω, G ω))
  have hsw : Function.Injective fun p : T × T' => (p.2, p.1) := fun a b h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  have c5 := condEntropy_comp_of_injective μ (X := fun ω => (Y ω, Z ω)) (Z := G) hsw
  have c6 := condEntropy_comp_of_injective μ (X := fun ω => (Y ω, Z ω))
    (Z := fun ω => (X ω, G ω)) hsw
  have m1 : H[Y | fun ω => (Z ω, (X ω, G ω)) ; μ] ≤ H[Y | fun ω => (Z ω, G ω) ; μ] :=
    condEntropy_le_condEntropy_comp (μ := μ) (measurable_of_finite _) (measurable_of_finite _)
      (fun p : T' × S × U => (p.1, p.2.2))
  have m2 : H[Z | fun ω => (Y ω, G ω) ; μ] ≤ H[Z | Y ; μ] :=
    condEntropy_le_condEntropy_comp (μ := μ) (measurable_of_finite _) (measurable_of_finite _)
      (fun p : T × U => p.1)
  have mk := h
  rw [markovChain_def, condMutualInfo_eq_condEntropy_sub_condEntropy] at mk
  have hs : H[Z | fun ω => (Y ω, (X ω, G ω)) ; μ] = H[Z | fun ω => ((X ω, G ω), Y ω) ; μ] :=
    condEntropy_congr_cond μ (fun p : (S × U) × T => (p.2, p.1))
      (fun p : T × S × U => (p.2, p.1)) (fun _ => rfl) fun _ => rfl
  simp only [Function.comp_def] at c5 c6
  linarith

end Degraded

section Info

variable {K : ℕ} [NeZero K] {A : Type*} {B : Fin K → Type*} {V : Fin K → Type*}
  [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, MeasurableSpace (V i)]
  [∀ i, MeasurableSingletonClass (V i)] [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)]
  [∀ k, MeasurableSingletonClass (B k)]

private noncomputable def outPMF (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (f : V 0 → A)
    (k : Fin K) : PMF ((∀ i, V i) × B k) :=
  law.bind fun v => (out W k (f (v 0))).map fun y => (v, y)

omit [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)]
  [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)] [∀ k, MeasurableSingletonClass (B k)] in
private lemma map_repJoint (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (d : ∀ i, V i)
    (f : V 0 → A) (k : Fin K) :
    (repJoint W law d f k).map (fun ω => (build d ω.1, ω.2)) = outPMF W law f k := by
  rw [outPMF]
  conv_rhs => rw [← map_build law d]
  rw [PMF.bind_map, repJoint, DMC.jointPMF, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]

private def unmaskV (d : ∀ i, V i) (w : MACK.Masked V) : ∀ i, V i :=
  fun i => (w i).getD (d i)

omit [NeZero K] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, MeasurableSpace (V i)]
  [∀ i, MeasurableSingletonClass (V i)] in
private lemma fill_unmaskV_mask (d : ∀ i, V i) (S : Finset (Fin K)) (v : ∀ i, V i) :
    fill d S (unmaskV d (MACK.mask S v)) = fill d S v := by
  funext i
  by_cases h : i ∈ S <;> simp [fill, unmaskV, MACK.mask, h]

omit [NeZero K] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, MeasurableSpace (V i)]
  [∀ i, MeasurableSingletonClass (V i)] in
private lemma mask_fill {S T : Finset (Fin K)} (h : S ⊆ T) (d v : ∀ i, V i) :
    MACK.mask S (fill d T v) = MACK.mask S v := by
  funext i
  by_cases hi : i ∈ S
  · simp [MACK.mask, fill, hi, h hi]
  · simp [MACK.mask, hi]

omit [NeZero K] in
private lemma mem_layer_self (j : Fin K) : j ∈ layer j := by simp [layer]

omit [NeZero K] in
private lemma isUpper_layer (j : Fin K) : IsUpper (layer j) := fun i hi l hl => by
  simp only [layer, mem_filter, mem_univ, true_and] at hi ⊢
  exact hi.trans hl

omit [NeZero K] in
private lemma isUpper_above (j : Fin K) : IsUpper (above j) := fun i hi l hl => by
  simp only [above, mem_filter, mem_univ, true_and] at hi ⊢
  exact lt_of_lt_of_le hi hl

omit [NeZero K] in
private lemma above_subset_layer (j : Fin K) : above j ⊆ layer j := fun i hi => by
  simp only [above, layer, mem_filter, mem_univ, true_and] at hi ⊢
  exact hi.le

private lemma regionTerm_le_step (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (d : ∀ i, V i)
    (f : V 0 → A) (k j : Fin K) :
    I[fun ω : (∀ i, V i) × B k => MACK.mask (layer j) ω.1 : fun ω => ω.2 |
        fun ω => MACK.mask (above j) ω.1 ; (outPMF W law f k).toMeasure] ≤
      (stepChannel W law d f k j).inputMutualInfo (inputPMF law d j) := by
  set σ := repJoint W law d f k
  have h1 : (stepChannel W law d f k j).inputMutualInfo (inputPMF law d j) =
      I[fun ω : (∀ l, Inp V l) × B k => ω.1 j : fun ω => (ω.2, MACK.mask (above j) ω.1) ;
        σ.toMeasure] := by
    rw [DMC.inputMutualInfo, DMC.jointMeasure_eq_toMeasure, jointPMF_stepChannel,
      ← PMF.toMeasure_map _ _ (measurable_of_finite _),
      mutualInfo_map _ (measurable_of_finite _) measurable_fst measurable_snd]
    rfl
  have h2 := condMutualInfo_le_mutualInfo_pair σ.toMeasure (fun ω : (∀ l, Inp V l) × B k => ω.1 j)
    (fun ω => ω.2) (fun ω => MACK.mask (above j) ω.1)
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy] at h2
  have h3 : H[fun ω : (∀ l, Inp V l) × B k => ω.2 |
      fun ω => (ω.1 j, MACK.mask (above j) ω.1) ; σ.toMeasure] =
      H[fun ω : (∀ l, Inp V l) × B k => ω.2 | fun ω => MACK.mask (layer j) ω.1 ; σ.toMeasure] :=
    condEntropy_congr_cond _
      (fun w : MACK.Masked (Inp V) => ((w j).getD fun _ => d j,
        fun l => if l ∈ above j then w l else none))
      (fun p : Inp V j × MACK.Masked (Inp V) => Function.update p.2 j (some p.1))
      (fun ω => by
        refine Prod.ext (by simp [MACK.mask, layer]) (funext fun l => ?_)
        by_cases h : l ∈ above j
        · simp [MACK.mask, h, above_subset_layer j h]
        · simp [MACK.mask, h])
      fun ω => by
        funext l
        by_cases hl : l = j
        · subst hl
          simp only [MACK.mask, mem_layer_self, ite_true]
          exact (Function.update_self (β := fun i => Option (Inp V i)) l _ _).symm
        · have : l ∈ layer j ↔ l ∈ above j := by
            simp only [layer, above, mem_filter, mem_univ, true_and]
            exact ⟨fun h => lt_of_le_of_ne h (Ne.symm hl), le_of_lt⟩
          simp [Function.update, hl, MACK.mask, this]
  have h4 := condEntropy_mask_eq W law d f k (isUpper_layer j)
  have h5 := condEntropy_mask_eq W law d f k (isUpper_above j)
  have h6 : ∀ L : Finset (Fin K), H[fun ω : (∀ l, Inp V l) × B k => ω.2 |
      fun ω => fill d L (build d ω.1) ; σ.toMeasure] =
      H[fun ω : (∀ i, V i) × B k => ω.2 | fun ω => fill d L ω.1 ;
        (outPMF W law f k).toMeasure] := fun L => by
    rw [← map_repJoint W law d f k, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
      condEntropy_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  have h8 : H[fun ω : (∀ i, V i) × B k => ω.2 | fun ω => MACK.mask (above j) ω.1 ;
      (outPMF W law f k).toMeasure] =
      H[fun ω : (∀ i, V i) × B k => ω.2 | fun ω => fill d (above j) ω.1 ;
        (outPMF W law f k).toMeasure] :=
    condEntropy_congr_cond _ (MACK.mask (above j)) (fun w => fill d (above j) (unmaskV d w))
      (fun ω => (mask_fill subset_rfl d ω.1).symm) fun ω => (fill_unmaskV_mask d _ ω.1).symm
  have h9 : H[fun ω : (∀ i, V i) × B k => ω.2 |
      fun ω => (MACK.mask (layer j) ω.1, MACK.mask (above j) ω.1) ;
      (outPMF W law f k).toMeasure] =
      H[fun ω : (∀ i, V i) × B k => ω.2 | fun ω => fill d (layer j) ω.1 ;
        (outPMF W law f k).toMeasure] :=
    condEntropy_congr_cond _ (fun x => (MACK.mask (layer j) x, MACK.mask (above j) x))
      (fun p => fill d (layer j) (unmaskV d p.1))
      (fun ω => by rw [mask_fill subset_rfl, mask_fill (above_subset_layer j)])
      fun ω => (fill_unmaskV_mask d _ ω.1).symm
  rw [condMutualInfo_eq_condEntropy_sub_condEntropy, h8, h9, ← h6, ← h6, ← h4, ← h5, h1]
  rw [h3] at h2
  exact h2

end Info

section DegradedTerm

variable {K : ℕ} [NeZero K] {A : Type*} {B : Fin K → Type*} {V : Fin K → Type*}
  [∀ i, Fintype (V i)] [∀ i, MeasurableSpace (V i)]
  [∀ i, MeasurableSingletonClass (V i)] [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)]
  [∀ k, MeasurableSingletonClass (B k)]

private lemma bind_map_apply_eq {α β γ : Type*} (P : PMF (α × β)) (D : β → PMF γ) (a : α)
    (b : β) (c : γ) :
    (P.bind fun p => (D p.2).map fun z => (p.1, p.2, z)) (a, b, c) = P (a, b) * D b c := by
  classical
  rw [PMF.bind_apply, tsum_eq_single (a, b) fun p hp => mul_eq_zero_of_right _ (by
    rw [PMF.map_apply (fun z => (p.1, p.2, z))]
    exact ENNReal.tsum_eq_zero.2 fun z => by
      simp only [Prod.mk.injEq]
      split_ifs with h
      · exact absurd (Prod.ext h.1.symm h.2.1.symm) hp
      · rfl)]
  rw [map_apply_inj _ (fun x y h => by simp only [Prod.mk.injEq] at h; exact h.2.2)]

private lemma regionTerm_le_of_degraded (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i))
    (f : V 0 → A) {k j : Fin K} (D : DMC (B k) (B j))
    (hD : ∀ a, out W j a = (out W k a).bind D) :
    I[fun ω : (∀ i, V i) × B j => MACK.mask (layer j) ω.1 : fun ω => ω.2 |
        fun ω => MACK.mask (above j) ω.1 ; (outPMF W law f j).toMeasure] ≤
      I[fun ω : (∀ i, V i) × B k => MACK.mask (layer j) ω.1 : fun ω => ω.2 |
        fun ω => MACK.mask (above j) ω.1 ; (outPMF W law f k).toMeasure] := by
  set σ : PMF ((∀ i, V i) × B k × B j) :=
    law.bind fun v => (out W k (f (v 0))).bind fun y => (D y).map fun z => (v, y, z)
  have e1 : σ.map (fun ω => (ω.1, ω.2.1)) = outPMF W law f k := by
    have h : ∀ (v : ∀ i, V i) (y : B k), (D y).map (fun _ => (v, y)) = PMF.pure (v, y) :=
      fun v y => PMF.map_const _ _
    simp only [σ, outPMF, PMF.map_bind, PMF.map_comp, Function.comp_def, h]
    rfl
  have e2 : σ.map (fun ω => (ω.1, ω.2.2)) = outPMF W law f j := by
    simp only [σ, outPMF, hD, PMF.map_bind, PMF.map_comp, Function.comp_def]
  set H : (∀ i, V i) → MACK.Masked V × MACK.Masked V :=
    fun v => (MACK.mask (layer j) v, MACK.mask (above j) v)
  have hm : MarkovChain (fun ω : (∀ i, V i) × B k × B j => ((H ω.1).1, (H ω.1).2))
      (fun ω => ω.2.1) (fun ω => ω.2.2) σ.toMeasure := by
    refine BC.markovChain_of_pmf σ _ _ _ (fun y z => D y z) fun x y z => ?_
    have hb : σ.map (fun ω => (((H ω.1).1, (H ω.1).2), ω.2.1, ω.2.2)) =
        (σ.map fun ω => (((H ω.1).1, (H ω.1).2), ω.2.1)).bind
          fun p => (D p.2).map fun z => (p.1, p.2, z) := by
      simp only [σ, PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp, Function.comp_def,
        PMF.bind_const]
    rw [hb, bind_map_apply_eq]
  have h := condMutualInfo_le_of_markov σ.toMeasure (fun ω => (H ω.1).1) (fun ω => (H ω.1).2)
    (fun ω => ω.2.1) (fun ω => ω.2.2) hm
  rw [← e1, ← e2, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _)]
  exact h

end DegradedTerm

section Average

private lemma ite_forall_eq_prod' {ι : Type*} [Fintype ι] {P : ι → Prop} [∀ i, Decidable (P i)]
    [Decidable (∀ i, P i)] (f : ι → ℝ) :
    (if ∀ i, P i then ∏ i, f i else 0) = ∏ i, if P i then f i else 0 := by
  by_cases h : ∀ i, P i
  · rw [ite_eq_left h]
    exact prod_congr rfl fun i _ => (ite_eq_left (h i)).symm
  · obtain ⟨i, hi⟩ := not_forall.1 h
    rw [ite_eq_right h]
    exact (prod_eq_zero (mem_univ i) (ite_eq_right hi)).symm

variable {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M] [DecidableEq M] {n : ℕ}

private lemma sum_ite_apply' (q : PMF X) (m₀ : M) (a : Fin n → X) :
    ∑ c : M → Fin n → X, (if c m₀ = a then ∏ j, iidProb q (c j) else 0) = iidProb q a := by
  have h := sum_prod_mul_apply (fun _ x => iidProb q x) (fun _ => sum_iidProb q n)
    (fun y => if y = a then (1 : ℝ) else 0) m₀
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h
  rw [← h]

private lemma sum_ite_apply_apply' (q : PMF X) {m₀ m₁ : M} (hm : m₀ ≠ m₁) (a a' : Fin n → X) :
    ∑ c : M → Fin n → X, (if c m₀ = a ∧ c m₁ = a' then ∏ j, iidProb q (c j) else 0) =
      iidProb q a * iidProb q a' := by
  have h := sum_prod_mul_apply_apply (fun _ x => iidProb q x) (fun _ => sum_iidProb q n)
    (fun y y' => if y = a ∧ y' = a' then (1 : ℝ) else 0) hm
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h, sum_eq_single a (fun b _ hb => sum_eq_zero fun b' _ => by simp [hb]) (by simp),
    sum_eq_single a' (fun b _ hb => by simp [hb]) (by simp)]
  simp

end Average

section Book

variable {K : ℕ} {X M : Fin K → Type*} [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]
  [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)] {n : ℕ}

private lemma sum_ite_book_eq (p : ∀ k, PMF (X k)) (m : ∀ k, M k) (l : Fin K) {m' : M l}
    (hm : m' ≠ m l) (a : Fin n → X l) (x : Fin n → ∀ k, X k) :
    ∑ C : ∀ k, M k → Fin n → X k,
      (if C l m' = a ∧ MACK.codeInput C m = x then MACK.codebookWeight p C else 0) =
        iidProb (p l) a * iidProb (piPMF p) x := by
  classical
  set cond : ∀ k, (M k → Fin n → X k) → Prop := fun k c =>
    c (m k) = (fun i => x i k) ∧ ∀ h : l = k, c (h ▸ m') = h ▸ a with hcond
  have hc : ∀ C : ∀ k, M k → Fin n → X k,
      (if C l m' = a ∧ MACK.codeInput C m = x then MACK.codebookWeight p C else 0) =
        ∏ k, if cond k (C k) then ∏ j, iidProb (p k) (C k j) else 0 := by
    intro C
    rw [← ite_forall_eq_prod']
    refine if_congr ⟨fun h k => ⟨?_, fun hk => ?_⟩, fun h => ⟨?_, ?_⟩⟩
      (by unfold MACK.codebookWeight; rfl) rfl
    · rw [← h.2]
      rfl
    · subst hk
      exact h.1
    · exact (h l).2 rfl
    · funext i k
      exact congrFun (h k).1 i
  simp_rw [hc]
  have hk : ∀ k ∈ univ.erase l, ∑ c : M k → Fin n → X k,
      (if cond k c then ∏ j, iidProb (p k) (c j) else 0) = iidProb (p k) (fun i => x i k) := by
    intro k hk
    have e : ∀ c : M k → Fin n → X k, cond k c ↔ c (m k) = fun i => x i k := fun c =>
      ⟨And.left, fun h => ⟨h, fun h' => absurd h'.symm (ne_of_mem_erase hk)⟩⟩
    simp only [e]
    exact sum_ite_apply' (p k) (m k) _
  have hl : ∑ c : M l → Fin n → X l, (if cond l c then ∏ j, iidProb (p l) (c j) else 0) =
      iidProb (p l) (fun i => x i l) * iidProb (p l) a := by
    have e : ∀ c : M l → Fin n → X l, cond l c ↔ c (m l) = (fun i => x i l) ∧ c m' = a :=
      fun c => ⟨fun h => ⟨h.1, h.2 rfl⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
    simp only [e]
    exact sum_ite_apply_apply' (p l) (Ne.symm hm) _ _
  calc _ = ∏ k, ∑ c : M k → Fin n → X k, (if cond k c then ∏ j, iidProb (p k) (c j) else 0) :=
        (Fintype.prod_sum _).symm
    _ = _ := by
        rw [← mul_prod_erase univ _ (mem_univ l), hl, prod_congr rfl hk, iidProb_piPMF,
          ← mul_prod_erase univ (fun k => iidProb (p k) (fun i => x i k)) (mem_univ l)]
        ring

end Book

section Code

variable {K : ℕ} [NeZero K] {A : Type*} {B : Fin K → Type*} {V : Fin K → Type*}
  [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, MeasurableSpace (V i)]
  [∀ i, MeasurableSingletonClass (V i)] [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)]
  [∀ k, MeasurableSingletonClass (B k)]

omit [NeZero K] in
private theorem build_eq_of_forall {U : Fin K → Type*} (d : ∀ j, U j)
    (t : ∀ l, (∀ j, U j) → U l) (m : ∀ j, U j) (k : Fin K)
    (h : ∀ l, k ≤ l → ∀ m' : ∀ j, U j, (∀ j, l < j → m' j = m j) → t l m' = m l) :
    build d t k = m k := by
  rw [build]
  refine h k le_rfl _ fun j hj => ?_
  rw [dite_eq_left hj]
  exact build_eq_of_forall d t m j fun l hl => h l (hj.le.trans hl)
termination_by K - k.val
decreasing_by
  have := Fin.lt_def.1 hj
  have := j.isLt
  omega

private abbrev Book (V : Fin K → Type*) (L : Fin K → ℕ) (n : ℕ) : Type _ :=
  ∀ l, Fin (L l) → Fin n → Inp V l

private noncomputable def stepLaw (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (d : ∀ i, V i)
    (f : V 0 → A) (k l : Fin K) : PMF (Inp V l × (B k × MACK.Masked (Inp V))) :=
  DMC.jointPMF (stepChannel W law d f k l) (inputPMF law d l)

private noncomputable def stepDec (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (d : ∀ i, V i)
    (f : V 0 → A) (n : ℕ) (ε : ℝ) {L : Fin K → ℕ} (C : Book V L n) (m₀ : ∀ l, Fin (L l))
    (k : Fin K) (y : Fin n → B k) (l : Fin K) (m : ∀ j, Fin (L j)) : Fin (L l) :=
  BlockCode.typicalDecoder (C l) (jointlyTypicalSet (stepLaw W law d f k l) n ε) (m₀ l)
    fun i => (y i, MACK.mask (above l) (MACK.codeInput C m i))

private noncomputable def bcCode (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (d : ∀ i, V i)
    (f : V 0 → A) (n : ℕ) (ε : ℝ) {L : Fin K → ℕ} (C : Book V L n) (m₀ : ∀ l, Fin (L l)) :
    BCKCode (fun k => Fin (L k)) A B n where
  enc m i := f (build d (MACK.codeInput C m i) 0)
  dec k y := build m₀ (stepDec W law d f n ε C m₀ k y) k

omit [∀ i, MeasurableSingletonClass (V i)] [∀ k, MeasurableSingletonClass (B k)] in
private lemma stepDec_congr (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (d : ∀ i, V i)
    (f : V 0 → A) (n : ℕ) (ε : ℝ) {L : Fin K → ℕ} (C : Book V L n) (m₀ : ∀ l, Fin (L l))
    (k : Fin K) (y : Fin n → B k) (l : Fin K) {m m' : ∀ j, Fin (L j)}
    (h : ∀ j, l < j → m' j = m j) :
    stepDec W law d f n ε C m₀ k y l m' = stepDec W law d f n ε C m₀ k y l m := by
  have e : ∀ i, MACK.mask (above l) (MACK.codeInput C m' i) =
      MACK.mask (above l) (MACK.codeInput C m i) := by
    intro i
    funext j
    by_cases hj : j ∈ above l
    · have hlj : l < j := by simpa [above] using hj
      simp [MACK.mask, MACK.codeInput, hj, h j hlj]
    · simp [MACK.mask, hj]
  simp only [stepDec, e]

omit [∀ i, MeasurableSingletonClass (V i)] [∀ k, MeasurableSingletonClass (B k)] in
private lemma ite_dec_le (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (d : ∀ i, V i)
    (f : V 0 → A) (n : ℕ) (ε : ℝ) {L : Fin K → ℕ} (C : Book V L n) (m₀ : ∀ l, Fin (L l))
    (k : Fin K) (y : Fin n → B k) (m : ∀ j, Fin (L j)) :
    (if (bcCode W law d f n ε C m₀).dec k y = m k then (0 : ℝ) else 1) ≤
      ∑ l ∈ layer k, if stepDec W law d f n ε C m₀ k y l m = m l then (0 : ℝ) else 1 := by
  by_cases h : ∀ l ∈ layer k, stepDec W law d f n ε C m₀ k y l m = m l
  · have : (bcCode W law d f n ε C m₀).dec k y = m k :=
      build_eq_of_forall m₀ _ m k fun l hl m' hm' => by
        rw [stepDec_congr W law d f n ε C m₀ k y l hm']
        exact h l (by simpa [layer] using hl)
    rw [ite_eq_left this]
    exact sum_nonneg fun _ _ => by split_ifs <;> norm_num
  · push Not at h
    obtain ⟨l, hl, hne⟩ := h
    calc (if (bcCode W law d f n ε C m₀).dec k y = m k then (0 : ℝ) else 1) ≤ 1 := by
          split_ifs <;> norm_num
      _ = if stepDec W law d f n ε C m₀ k y l m = m l then (0 : ℝ) else 1 := by
          rw [ite_eq_right hne]
      _ ≤ _ := single_le_sum (f := fun l => if stepDec W law d f n ε C m₀ k y l m = m l
          then (0 : ℝ) else 1) (fun _ _ => by split_ifs <;> norm_num) hl

omit [∀ i, MeasurableSingletonClass (V i)] [∀ k, MeasurableSingletonClass (B k)] in
private lemma errorProb_toReal_le (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i))
    (d : ∀ i, V i) (f : V 0 → A) (n : ℕ) (ε : ℝ) {L : Fin K → ℕ} (C : Book V L n)
    (m₀ m : ∀ l, Fin (L l)) :
    ((bcCode W law d f n ε C m₀).errorProb W m).toReal ≤
      ∑ k, ∑ l ∈ layer k, ∑ y : Fin n → B k,
        if stepDec W law d f n ε C m₀ k y l m = m l then 0 else
          (DMC.blockProb (out W k) ((bcCode W law d f n ε C m₀).enc m) y).toReal := by
  classical
  set c := bcCode W law d f n ε C m₀
  rw [BCKCode.errorProb,
    ENNReal.toReal_sum fun y _ => by split_ifs <;> simp [DMC.blockProb_ne_top]]
  have h1 : ∀ y : Fin n → ∀ k, B k,
      (if c.decode y = m then 0 else DMC.blockProb W (c.enc m) y).toReal ≤
        ∑ k, (DMC.blockProb W (c.enc m) y).toReal *
          (if c.dec k (fun i => y i k) = m k then (0 : ℝ) else 1) := by
    intro y
    by_cases hy : c.decode y = m
    · rw [ite_eq_left hy, ENNReal.toReal_zero]
      exact sum_nonneg fun k _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)
    · rw [ite_eq_right hy]
      obtain ⟨k, hk⟩ : ∃ k, c.dec k (fun i => y i k) ≠ m k := by
        by_contra hc
        push Not at hc
        exact hy (funext hc)
      refine le_trans (le_of_eq ?_) (single_le_sum (f := fun k =>
        (DMC.blockProb W (c.enc m) y).toReal *
          (if c.dec k (fun i => y i k) = m k then (0 : ℝ) else 1))
        (fun k _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)) (mem_univ k))
      simp [hk]
  refine (sum_le_sum fun y _ => h1 y).trans ?_
  rw [sum_comm]
  refine sum_le_sum fun k _ => ?_
  calc _ = ∑ y' : Fin n → B k, (DMC.blockProb (out W k) (c.enc m) y').toReal *
        (if c.dec k y' = m k then (0 : ℝ) else 1) :=
        DMC.sum_blockProb_mul_comp W (fun b => b k) (c.enc m)
          (fun y' => if c.dec k y' = m k then (0 : ℝ) else 1)
    _ ≤ ∑ y' : Fin n → B k, (DMC.blockProb (out W k) (c.enc m) y').toReal *
        ∑ l ∈ layer k, (if stepDec W law d f n ε C m₀ k y' l m = m l then (0 : ℝ) else 1) :=
        sum_le_sum fun y' _ => mul_le_mul_of_nonneg_left
          (ite_dec_le W law d f n ε C m₀ k y' m) ENNReal.toReal_nonneg
    _ = _ := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun l _ => sum_congr rfl fun y' _ => ?_
        split_ifs <;> simp

end Code

section Random

variable {K : ℕ} [NeZero K] {A : Type*} {B : Fin K → Type*} {V : Fin K → Type*}
  [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, MeasurableSpace (V i)]
  [∀ i, MeasurableSingletonClass (V i)] [∀ k, Fintype (B k)] [∀ k, MeasurableSpace (B k)]
  [∀ k, MeasurableSingletonClass (B k)]

omit [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ k, MeasurableSpace (B k)]
  [∀ k, MeasurableSingletonClass (B k)] in
private lemma sum_iidProb_step_eq (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i))
    (d : ∀ i, V i) (f : V 0 → A) (k l : Fin K) {n : ℕ}
    (G : (Fin n → Inp V l) → (Fin n → B k × MACK.Masked (Inp V)) → ℝ) :
    ∑ x : Fin n → ∀ j, Inp V j, iidProb (repPMF law d) x *
      ∑ y : Fin n → B k, (DMC.blockProb (out W k) (fun i => f (build d (x i) 0)) y).toReal *
        G (fun i => x i l) (fun i => (y i, MACK.mask (above l) (x i))) =
    ∑ a : Fin n → Inp V l, iidProb (inputPMF law d l) a *
      ∑ z, (DMC.blockProb (stepChannel W law d f k l) a z).toReal * G a z := by
  have e1 := sum_arrow_prod (fun w : Fin n → (∀ j, Inp V j) × B k =>
    iidProb (repJoint W law d f k) w *
      G (fun i => (w i).1 l) (fun i => ((w i).2, MACK.mask (above l) (w i).1)))
  have e2 := sum_iidProb_mul_comp (repJoint W law d f k)
    (fun ω : (∀ j, Inp V j) × B k => (ω.1 l, (ω.2, MACK.mask (above l) ω.1)))
    (fun w' : Fin n → Inp V l × (B k × MACK.Masked (Inp V)) =>
      G (fun i => (w' i).1) (fun i => (w' i).2))
  have e3 := sum_arrow_prod (fun w' : Fin n → Inp V l × (B k × MACK.Masked (Inp V)) =>
    iidProb (stepLaw W law d f k l) w' * G (fun i => (w' i).1) (fun i => (w' i).2))
  rw [← jointPMF_stepChannel] at e2
  calc _ = ∑ x : Fin n → ∀ j, Inp V j, ∑ y : Fin n → B k,
        iidProb (repJoint W law d f k) (fun i => (x i, y i)) *
          G (fun i => x i l) (fun i => (y i, MACK.mask (above l) (x i))) := by
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun y _ => ?_
        rw [repJoint, DMC.iidProb_jointPMF, mul_assoc]
        rfl
    _ = ∑ a : Fin n → Inp V l, ∑ z : Fin n → B k × MACK.Masked (Inp V),
        iidProb (stepLaw W law d f k l) (fun i => (a i, z i)) * G a z :=
        e1.symm.trans (e2.trans e3)
    _ = _ := by
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun z _ => ?_
        rw [stepLaw, DMC.iidProb_jointPMF, mul_assoc]

omit [∀ i, MeasurableSingletonClass (V i)] [∀ k, MeasurableSingletonClass (B k)] in
private lemma sum_weight_mul_step_le (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i))
    (d : ∀ i, V i) (f : V 0 → A) (n : ℕ) (ε : ℝ) {L : Fin K → ℕ} (m₀ m : ∀ l, Fin (L l))
    (k l : Fin K) :
    ∑ C : Book V L n, MACK.codebookWeight (inputPMF law d) C *
      ∑ y : Fin n → B k, (if stepDec W law d f n ε C m₀ k y l m = m l then 0 else
        (DMC.blockProb (out W k) (fun i => f (build d (MACK.codeInput C m i) 0)) y).toReal) ≤
      (1 - ∑ xy ∈ jointlyTypicalSet (stepLaw W law d f k l) n ε,
          iidProb (stepLaw W law d f k l) (fun i => (xy.1 i, xy.2 i))) +
        ((L l : ℝ) - 1) * Real.exp (-(n * ((stepChannel W law d f k l).inputMutualInfo
          (inputPMF law d l) - 3 * ε))) := by
  classical
  set J := jointlyTypicalSet (stepLaw W law d f k l) n ε with hJ
  set e := Real.exp (-(n * ((stepChannel W law d f k l).inputMutualInfo
    (inputPMF law d l) - 3 * ε))) with he
  set b : (Fin n → ∀ j, Inp V j) → (Fin n → B k) → ℝ := fun x y =>
    (DMC.blockProb (out W k) (fun i => f (build d (x i) 0)) y).toReal with hb
  set z : (Fin n → ∀ j, Inp V j) → (Fin n → B k) → Fin n → B k × MACK.Masked (Inp V) :=
    fun x y i => (y i, MACK.mask (above l) (x i)) with hz
  have hw : ∀ C : Book V L n, 0 ≤ MACK.codebookWeight (inputPMF law d) C :=
    fun C => prod_nonneg fun _ _ => prod_nonneg fun _ _ => iidProb_nonneg _ _
  have hpt : ∀ (C : Book V L n) (y : Fin n → B k),
      (if stepDec W law d f n ε C m₀ k y l m = m l then 0 else b (MACK.codeInput C m) y) ≤
        (if ((fun i => MACK.codeInput C m i l), z (MACK.codeInput C m) y) ∈ J then 0
          else b (MACK.codeInput C m) y) +
          ∑ m' ∈ univ.erase (m l), (if (C l m', z (MACK.codeInput C m) y) ∈ J then (1 : ℝ)
            else 0) * b (MACK.codeInput C m) y := by
    intro C y
    have h := BlockCode.ite_comp_typicalDecoder_le id (C l) J (m₀ l) (m l)
      (z (MACK.codeInput C m) y) (b := b (MACK.codeInput C m) y) ENNReal.toReal_nonneg
    simp only [id, filter_ne'] at h
    exact h
  have T1 : ∑ C : Book V L n, MACK.codebookWeight (inputPMF law d) C *
      ∑ y, (if ((fun i => MACK.codeInput C m i l), z (MACK.codeInput C m) y) ∈ J then 0
        else b (MACK.codeInput C m) y) =
      1 - ∑ xy ∈ J, iidProb (stepLaw W law d f k l) (fun i => (xy.1 i, xy.2 i)) := by
    have key := MACK.sum_mul_comp_eq (MACK.codebookWeight (inputPMF law d))
      (fun C : Book V L n => MACK.codeInput C m)
      (fun x => ∑ y, if ((fun i => x i l), z x y) ∈ J then 0 else b x y)
    refine key.trans ?_
    simp_rw [MACK.sum_ite_codeInput_eq]
    have hG : ∀ x : Fin n → ∀ j, Inp V j,
        (∑ y, if ((fun i => x i l), z x y) ∈ J then (0 : ℝ) else b x y) =
          ∑ y, b x y * if ((fun i => x i l), z x y) ∈ J then (0 : ℝ) else 1 :=
      fun x => sum_congr rfl fun y _ => by split_ifs <;> simp
    simp_rw [hG]
    refine (sum_iidProb_step_eq W law d f k l
      (fun a z' => if (a, z') ∈ J then (0 : ℝ) else 1)).trans ?_
    refine Eq.trans ?_ (DMC.sum_iidProb_mul_sum_ite_jointPMF (stepChannel W law d f k l)
      (inputPMF law d l) J)
    refine sum_congr rfl fun a _ => congrArg _ (sum_congr rfl fun z' _ => ?_)
    split_ifs <;> simp
  have T2 : ∀ m' ∈ univ.erase (m l), ∑ C : Book V L n, MACK.codebookWeight (inputPMF law d) C *
      ∑ y, (if (C l m', z (MACK.codeInput C m) y) ∈ J then (1 : ℝ) else 0) *
        b (MACK.codeInput C m) y ≤ e := by
    intro m' hm'
    have key := MACK.sum_mul_comp_eq (MACK.codebookWeight (inputPMF law d))
      (fun C : Book V L n => (C l m', MACK.codeInput C m))
      (fun ax => ∑ y, (if (ax.1, z ax.2 y) ∈ J then (1 : ℝ) else 0) * b ax.2 y)
    refine (key.trans ?_).trans_le (DMC.sum_iidProb_mul_iidProb_mul_sum_le
      (stepChannel W law d f k l) (inputPMF law d l) n ε)
    have hp : ∀ ax : (Fin n → Inp V l) × (Fin n → ∀ j, Inp V j),
        (∑ C : Book V L n, if (C l m', MACK.codeInput C m) = ax then
          MACK.codebookWeight (inputPMF law d) C else 0) =
        iidProb (inputPMF law d l) ax.1 * iidProb (repPMF law d) ax.2 := by
      intro ax
      refine Eq.trans ?_ (sum_ite_book_eq (inputPMF law d) m l (ne_of_mem_erase hm') ax.1 ax.2)
      refine sum_congr rfl fun C _ => ?_
      simp only [Prod.ext_iff]
    simp_rw [hp]
    rw [Fintype.sum_prod_type]
    have hx : ∀ a' : Fin n → Inp V l,
        ∑ x : Fin n → ∀ j, Inp V j, iidProb (inputPMF law d l) a' * iidProb (repPMF law d) x *
          ∑ y, (if (a', z x y) ∈ J then (1 : ℝ) else 0) * b x y =
        iidProb (inputPMF law d l) a' * ∑ a : Fin n → Inp V l, iidProb (inputPMF law d l) a *
          ∑ z', (DMC.blockProb (stepChannel W law d f k l) a z').toReal *
            (if (a', z') ∈ J then (1 : ℝ) else 0) := by
      intro a'
      rw [← sum_iidProb_step_eq W law d f k l (fun _ z' => if (a', z') ∈ J then (1 : ℝ) else 0),
        mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [mul_assoc]
      congr 2
      refine sum_congr rfl fun y _ => ?_
      ring
    simp_rw [hx, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => sum_congr rfl fun z' _ => ?_
    rw [show J = jointlyTypicalSet ((stepChannel W law d f k l).jointPMF (inputPMF law d l)) n ε
      from rfl]
    ring
  calc _ ≤ ∑ C : Book V L n, MACK.codebookWeight (inputPMF law d) C *
        (∑ y, (if ((fun i => MACK.codeInput C m i l), z (MACK.codeInput C m) y) ∈ J then 0
          else b (MACK.codeInput C m) y) +
        ∑ m' ∈ univ.erase (m l), ∑ y, (if (C l m', z (MACK.codeInput C m) y) ∈ J then (1 : ℝ)
            else 0) * b (MACK.codeInput C m) y) := by
        refine sum_le_sum fun C _ => mul_le_mul_of_nonneg_left ?_ (hw C)
        rw [sum_comm (s := univ.erase (m l)), ← sum_add_distrib]
        exact sum_le_sum fun y _ => hpt C y
    _ = (1 - ∑ xy ∈ J, iidProb (stepLaw W law d f k l) (fun i => (xy.1 i, xy.2 i))) +
        ∑ m' ∈ univ.erase (m l), ∑ C : Book V L n, MACK.codebookWeight (inputPMF law d) C *
          ∑ y, (if (C l m', z (MACK.codeInput C m) y) ∈ J then (1 : ℝ) else 0) *
            b (MACK.codeInput C m) y := by
        rw [← T1]
        simp only [mul_add, sum_add_distrib, mul_sum]
        rw [sum_comm (s := univ) (t := univ.erase (m l))]
    _ ≤ (1 - ∑ xy ∈ J, iidProb (stepLaw W law d f k l) (fun i => (xy.1 i, xy.2 i))) +
        ∑ m' ∈ univ.erase (m l), e := add_le_add le_rfl (sum_le_sum T2)
    _ = _ := by
        rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_sub (Fin.pos (m l)), Nat.cast_one]

omit [NeZero K] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, MeasurableSpace (V i)]
  [∀ i, MeasurableSingletonClass (V i)] [∀ k, MeasurableSpace (B k)]
  [∀ k, MeasurableSingletonClass (B k)] in
private lemma avgError_eq_block {L : Fin K → ℕ} {n : ℕ} (c : BCKCode (fun k => Fin (L k)) A B n)
    (W : DMC A (∀ k, B k)) :
    (⟨c.enc, c.decode⟩ : BlockCode (∀ k, Fin (L k)) A (∀ k, B k) n).avgError W = c.avgError W := by
  rw [BlockCode.avgError, BCKCode.avgError, Fintype.card_pi, Nat.cast_prod]
  rfl

omit [∀ i, MeasurableSingletonClass (V i)] [∀ k, MeasurableSingletonClass (B k)] in
private lemma exists_book (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (d : ∀ i, V i)
    (f : V 0 → A) (n : ℕ) (ε : ℝ) {L : Fin K → ℕ} (m₀ : ∀ l, Fin (L l)) :
    ∃ C : Book V L n, (bcCode W law d f n ε C m₀).avgError W ≤ ENNReal.ofReal
      (∑ k, ∑ l ∈ layer k,
        ((1 - ∑ xy ∈ jointlyTypicalSet (stepLaw W law d f k l) n ε,
            iidProb (stepLaw W law d f k l) (fun i => (xy.1 i, xy.2 i))) +
          ((L l : ℝ) - 1) * Real.exp (-(n * ((stepChannel W law d f k l).inputMutualInfo
            (inputPMF law d l) - 3 * ε))))) := by
  classical
  set β := ∑ k, ∑ l ∈ layer k,
    ((1 - ∑ xy ∈ jointlyTypicalSet (stepLaw W law d f k l) n ε,
        iidProb (stepLaw W law d f k l) (fun i => (xy.1 i, xy.2 i))) +
      ((L l : ℝ) - 1) * Real.exp (-(n * ((stepChannel W law d f k l).inputMutualInfo
        (inputPMF law d l) - 3 * ε))))
  have hw : ∀ C : Book V L n, 0 ≤ MACK.codebookWeight (inputPMF law d) C :=
    fun C => prod_nonneg fun _ _ => prod_nonneg fun _ _ => iidProb_nonneg _ _
  have h1 : ∑ C : Book V L n, MACK.codebookWeight (inputPMF law d) C = 1 := by
    unfold MACK.codebookWeight
    calc ∑ C : Book V L n, ∏ k, ∏ j, iidProb (inputPMF law d k) (C k j) =
        ∏ k, ∑ c : Fin (L k) → Fin n → Inp V k, ∏ j, iidProb (inputPMF law d k) (c j) :=
          (Fintype.prod_sum fun k (c : Fin (L k) → Fin n → Inp V k) =>
            ∏ j, iidProb (inputPMF law d k) (c j)).symm
      _ = 1 := prod_eq_one fun k _ =>
        sum_prod (fun _ x => iidProb (inputPMF law d k) x) (fun _ => sum_iidProb _ n)
  have hm : ∀ m : ∀ l, Fin (L l), ∑ C : Book V L n, MACK.codebookWeight (inputPMF law d) C *
      ((bcCode W law d f n ε C m₀).errorProb W m).toReal ≤ β := by
    intro m
    calc _ ≤ ∑ C : Book V L n, MACK.codebookWeight (inputPMF law d) C *
          ∑ k, ∑ l ∈ layer k, ∑ y : Fin n → B k,
            (if stepDec W law d f n ε C m₀ k y l m = m l then 0 else
              (DMC.blockProb (out W k) (fun i => f (build d (MACK.codeInput C m i) 0))
                y).toReal) :=
          sum_le_sum fun C _ => mul_le_mul_of_nonneg_left
            (errorProb_toReal_le W law d f n ε C m₀ m) (hw C)
      _ = ∑ k, ∑ l ∈ layer k, ∑ C : Book V L n, MACK.codebookWeight (inputPMF law d) C *
            ∑ y : Fin n → B k,
              (if stepDec W law d f n ε C m₀ k y l m = m l then 0 else
                (DMC.blockProb (out W k) (fun i => f (build d (MACK.codeInput C m i) 0))
                  y).toReal) := by
          simp only [mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun k _ => ?_
          rw [sum_comm]
      _ ≤ β := sum_le_sum fun k _ => sum_le_sum fun l _ =>
          sum_weight_mul_step_le W law d f n ε m₀ m k l
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le (w := MACK.codebookWeight (inputPMF law d))
    (f := fun C : Book V L n => ∑ m, ((bcCode W law d f n ε C m₀).errorProb W m).toReal)
    (t := Fintype.card (∀ k, Fin (L k)) * β) hw h1 (by
      simp only [mul_sum]
      rw [sum_comm]
      calc _ ≤ ∑ m : ∀ k, Fin (L k), β := sum_le_sum fun m _ => hm m
        _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul])
  refine ⟨C, ?_⟩
  have : Nonempty (∀ k, Fin (L k)) := ⟨m₀⟩
  rw [← avgError_eq_block]
  exact BlockCode.avgError_le_ofReal _ W hC

private theorem achievable_of_lt (W : DMC A (∀ k, B k)) (law : PMF (∀ i, V i)) (d : ∀ i, V i)
    (f : V 0 → A) {R : Fin K → ℝ}
    (h : ∀ k l, k ≤ l → R l < (stepChannel W law d f k l).inputMutualInfo (inputPMF law d l)) :
    Achievable W R := by
  classical
  intro ε hε
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  set I : Fin K → Fin K → ℝ := fun k l =>
    (stepChannel W law d f k l).inputMutualInfo (inputPMF law d l) with hI
  set g : Fin K × Fin K → ℝ := fun p => if p.1 ≤ p.2 then I p.1 p.2 - R p.2 else 1 with hg
  set η := univ.inf' univ_nonempty g / 4 with hη
  have hη0 : 0 < η := by
    refine div_pos ((lt_inf'_iff _).2 fun p _ => ?_) (by norm_num)
    by_cases hp : p.1 ≤ p.2
    · simp only [g, hp, ite_true]
      linarith [h p.1 p.2 hp]
    · simp [g, hp]
  have hηkl : ∀ k l, k ≤ l → 4 * η ≤ I k l - R l := by
    intro k l hkl
    have := inf'_le g (mem_univ (k, l))
    simp only [g, hkl, ite_true] at this
    rw [hη]
    linarith
  set P : Fin K → Fin K → ℕ → ℝ := fun k l n =>
    1 - ∑ xy ∈ jointlyTypicalSet (stepLaw W law d f k l) n η,
      iidProb (stepLaw W law d f k l) (fun i => (xy.1 i, xy.2 i)) with hP
  have hPt : ∀ k l, Tendsto (P k l) atTop (𝓝 0) := fun k l => by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_jointlyTypicalSet (stepLaw W law d f k l) hη0)
  have hE := tendsto_exp_nat_mul (neg_neg_of_pos hη0)
  have hsum : Tendsto (fun n : ℕ => ∑ k, ∑ l ∈ layer k, (P k l n + Real.exp (n * -η))) atTop
      (𝓝 0) := by
    have := tendsto_finsetSum (univ : Finset (Fin K)) fun k _ =>
      tendsto_finsetSum (layer k) fun l _ => (hPt k l).add hE
    simpa using this
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  set L : Fin K → ℕ := fun k => ⌈Real.exp (n * R k)⌉₊
  have hL : ∀ k, 0 < L k := fun k => Nat.ceil_pos.2 (Real.exp_pos _)
  have hL' : ∀ k, (L k : ℝ) - 1 ≤ Real.exp (n * R k) := fun k => by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (n * R k)).le]
  refine ⟨L, fun k => Nat.le_ceil _, ?_⟩
  obtain ⟨C, hC⟩ := exists_book W law d f n η (fun k => (⟨0, hL k⟩ : Fin (L k)))
  refine ⟨_, hC.trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hδε.le)⟩
  refine le_trans ?_ (hN n hn).le
  refine sum_le_sum fun k _ => sum_le_sum fun l hl => add_le_add le_rfl ?_
  have hkl : k ≤ l := by simpa [layer] using hl
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc ((L l : ℝ) - 1) * Real.exp (-(n * (I k l - 3 * η))) ≤
        Real.exp (n * R l) * Real.exp (-(n * (I k l - 3 * η))) :=
        mul_le_mul_of_nonneg_right (hL' l) (Real.exp_pos _).le
    _ = Real.exp (n * R l - n * (I k l - 3 * η)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (n * -η) := Real.exp_le_exp.2 (by nlinarith [hηkl k l hkl])

end Random

section Closure

variable {K : ℕ} {A : Type*} {B : Fin K → Type*} [∀ k, Fintype (B k)]

private theorem Achievable.max_zero' {W : DMC A (∀ k, B k)} {R : Fin K → ℝ}
    (h : Achievable W R) : Achievable W fun k => max (R k) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨L, hL, c, hc⟩ := hN n hn
  exact ⟨L, fun k => exp_mul_max_le (hL k), c, hc⟩

private theorem mem_closure_of_forall {W : DMC A (∀ k, B k)} {R : Fin K → ℝ}
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
    (h (η / 2) (by positivity)).max_zero'⟩, (dist_pi_lt_iff hη).2 fun k => key _ (h0 k)⟩

variable [NeZero K] [∀ k, MeasurableSpace (B k)] [∀ k, MeasurableSingletonClass (B k)]
  {V : Fin K → Type*} [∀ i, Fintype (V i)] [∀ i, MeasurableSpace (V i)]
  [∀ i, MeasurableSingletonClass (V i)]

private lemma regionTerm_eq_out (W : DMC A (∀ k, B k)) (law : PMF (∀ j, V j)) (f : V 0 → A)
    (k : Fin K) :
    I[fun ω : (∀ j, V j) × (∀ k, B k) => MACK.mask (layer k) ω.1 : fun ω => ω.2 k |
        fun ω => MACK.mask (above k) ω.1 ; (layerPMF W law f).toMeasure] =
      I[fun ω : (∀ j, V j) × B k => MACK.mask (layer k) ω.1 : fun ω => ω.2 |
        fun ω => MACK.mask (above k) ω.1 ; (outPMF W law f k).toMeasure] := by
  have e : (layerPMF W law f).map (fun ω => (ω.1, ω.2 k)) = outPMF W law f k := by
    simp only [layerPMF, outPMF, out, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [← e, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _)]
  rfl

private theorem superpositionRegion_subset_closure {W : DMC A (∀ k, B k)} (hW : IsDegraded W)
    (law : PMF (∀ i, V i)) (f : V 0 → A) :
    superpositionRegion W law f ⊆ closure (achievableRegion W) := by
  classical
  rintro R ⟨h0, hR⟩
  obtain ⟨d, -⟩ := law.support_nonempty
  refine mem_closure_of_forall h0 fun δ hδ => achievable_of_lt W law d f fun k l hkl => ?_
  obtain ⟨D, hD⟩ := hW k l hkl
  have h1 := hR l
  rw [regionTerm_eq_out] at h1
  have h2 := regionTerm_le_of_degraded W law f D hD
  have h3 := regionTerm_le_step W law d f k l
  linarith

theorem superpositionUnion_subset_closure_achievableRegion {W : DMC A (∀ k, B k)}
    (hW : IsDegraded W) : superpositionUnion W ⊆ closure (achievableRegion W) := by
  intro R hR
  simp only [superpositionUnion, Set.mem_iUnion] at hR
  obtain ⟨s, law, f, hR⟩ := hR
  exact superpositionRegion_subset_closure hW law f hR

end Closure

end BCK

end Meat
