import Meat.Continuous.AWGNQuantization

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Meat

namespace AWGN

theorem sum_blockChannel_toReal_mul {A B : Type*} [Fintype B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (N : ℝ) {L : ℕ} (a : A → Fin L → ℝ) {q : (Fin L → ℝ) → B}
    (hq : Measurable q) (x : A) (g : B → ℝ) :
    ∑ b, (blockChannel N a q x b).toReal * g b = ∫ z, g (q (a x + z)) ∂noise N L := by
  have hφ : Measurable fun z => q (a x + z) := hq.comp (measurable_const_add _)
  rw [← integral_map hφ.aemeasurable Integrable.of_finite.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  simp [blockChannel, Measure.toPMF_apply, measureReal_def, smul_eq_mul]

private lemma integral_comp_of_measurePreserving {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {f : α → β}
    (hf : MeasurePreserving f μ ν) {g : β → ℝ} (hg : AEStronglyMeasurable g ν) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := by
  rw [← hf.map_eq] at hg
  rw [← integral_map hf.measurable.aemeasurable hg, hf.map_eq]

theorem measurable_log_letterRatio {α : Type*} [MeasurableSpace α] (θ N : ℝ) (n : ℕ)
    {f : α → ℝ} {g : α → Level n} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => Real.log (letterRatio θ N n (f a) (g a)) := by
  have hv : Measurable fun a => θ / (θ + N) * value n (g a) :=
    ((measurable_of_finite (value n)).comp hg).const_mul _
  have h1 : Measurable fun a => gaussianPDFReal (θ / (θ + N) * value n (g a))
      (θ * N / (θ + N)).toNNReal (f a) :=
    measurable_uncurry_gaussianPDFReal.comp (hv.prodMk (measurable_const.prodMk hf))
  have h2 : Measurable fun a => gaussianPDFReal 0 θ.toNNReal (f a) :=
    (measurable_gaussianPDFReal _ _).comp hf
  exact Real.measurable_log.comp (h1.div h2)

theorem integrable_log_letterRatio_level {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n : ℕ) :
    Integrable (fun w : ℝ × ℝ => Real.log (letterRatio θ N n w.1
        (level n (value n (level n w.1) + w.2))))
      ((gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 N.toNNReal)) := by
  have hα0 : 0 ≤ θ / (θ + N) := by positivity
  have hα1 : θ / (θ + N) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have h2 : Integrable (fun w : ℝ × ℝ => (1 / 2) * Real.log (θ / (θ * N / (θ + N)))
      + w.1 ^ 2 / (2 * θ)) ((gaussianReal 0 θ.toNNReal).prod (gaussianReal 0 N.toNNReal)) :=
    (integrable_const _).add (((integrable_sq_gaussianReal _).comp_fst _).div_const _)
  simp_rw [log_letterRatio hθ hN]
  exact h2.sub ((integrable_post_sq θ N hα0 hα1 n).div_const _)

theorem abs_log_letterRatio_sub_le {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n : ℕ) (t : ℝ)
    (b b' : Level n) :
    |Real.log (letterRatio θ N n t b) - Real.log (letterRatio θ N n t b')|
      ≤ (4 * n * |t| + 4 * n ^ 2) / (2 * (θ * N / (θ + N))) := by
  have hs : 0 < θ * N / (θ + N) := by positivity
  have hα0 : 0 ≤ θ / (θ + N) := by positivity
  have hα1 : θ / (θ + N) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  rw [log_letterRatio hθ hN, log_letterRatio hθ hN,
    show ∀ A B C D E : ℝ, (A + B - C / E) - (A + B - D / E) = (D - C) / E from
      fun _ _ _ _ _ => by ring]
  set α := θ / (θ + N)
  set s := θ * N / (θ + N)
  have hc : ∀ k : Level n, |α * value n k| ≤ n := fun k => by
    rw [abs_mul, abs_of_nonneg hα0]
    exact (mul_le_of_le_one_left (abs_nonneg _) hα1).trans (abs_value_le n k)
  rw [show (t - α * value n b') ^ 2 - (t - α * value n b) ^ 2
      = (α * value n b - α * value n b') * (2 * t - α * value n b - α * value n b') by ring,
    abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * s),
    div_le_div_iff_of_pos_right (by positivity), abs_mul]
  have h1 : |α * value n b - α * value n b'| ≤ 2 * n :=
    (abs_sub _ _).trans (by linarith [hc b, hc b'])
  have h2 : |2 * t - α * value n b - α * value n b'| ≤ 2 * |t| + 2 * n := by
    refine (abs_sub _ _).trans ?_
    have := (abs_sub (2 * t) (α * value n b))
    rw [abs_mul, abs_two] at this
    linarith [hc b, hc b']
  calc |α * value n b - α * value n b'| * |2 * t - α * value n b - α * value n b'|
      ≤ (2 * n) * (2 * |t| + 2 * n) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 4 * n * |t| + 4 * n ^ 2 := by ring

noncomputable def clipValue (n L : ℕ) (P : ℝ) (x : Fin L → Level n) : Fin L → ℝ :=
  if ∑ l, value n (x l) ^ 2 ≤ L * P then fun l => value n (x l) else 0

theorem sum_sq_clipValue_le {P : ℝ} (hP : 0 ≤ P) (n L : ℕ) (x : Fin L → Level n) :
    ∑ l, clipValue n L P x l ^ 2 ≤ L * P := by
  unfold clipValue
  split_ifs with h
  · exact h
  · simpa using mul_nonneg (Nat.cast_nonneg L) hP

noncomputable def blockInput (n L : ℕ) (P : ℝ) (x : Fin (Fintype.card (Fin L → Level n))) :
    Fin L → ℝ :=
  clipValue n L P ((Fintype.equivFin (Fin L → Level n)).symm x)

noncomputable def blockQuant (n L : ℕ) (y : Fin L → ℝ) : Fin (Fintype.card (Fin L → Level n)) :=
  Fintype.equivFin (Fin L → Level n) fun l => level n (y l)

theorem measurable_blockQuant (n L : ℕ) : Measurable (blockQuant n L) :=
  (measurable_of_finite (Fintype.equivFin (Fin L → Level n))).comp
    (measurable_pi_iff.2 fun l => (measurable_level n).comp (measurable_pi_apply l))

noncomputable def blockLaw (θ : ℝ) (n L : ℕ) : PMF (Fin (Fintype.card (Fin L → Level n))) :=
  ((Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal).map (blockQuant n L)).toPMF

theorem integral_blockGain_le {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n L : ℕ) (P : ℝ) :
    ∫ t, ∫ z, ∑ l, Real.log (letterRatio θ N n (t l)
        (level n (clipValue n L P (fun k => level n (t k)) l + z l))) ∂noise N L
      ∂Measure.pi (fun _ : Fin L => gaussianReal 0 θ.toNNReal)
      ≤ (blockChannel N (blockInput n L P) (blockQuant n L)).inputMutualInfo
          (blockLaw θ n L) := by
  set μL := Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal
  set e := Fintype.equivFin (Fin L → Level n)
  have hs : 0 < θ * N / (θ + N) := by positivity
  set u : (Fin L → ℝ) → Fin (Fintype.card (Fin L → Level n)) → ℝ :=
    fun t b => ∏ l, letterRatio θ N n (t l) (e.symm b l)
  have hu : ∀ t b, 0 < u t b := fun t b => Finset.prod_pos fun l _ => postRatio_pos hθ hs _ _
  have hlogu : ∀ t b, Real.log (u t b) = ∑ l, Real.log (letterRatio θ N n (t l) (e.symm b l)) :=
    fun t b => Real.log_prod fun l _ => (postRatio_pos hθ hs _ _).ne'
  have hmp : ∀ l : Fin L, MeasurePreserving (fun t : Fin L → ℝ => t l) μL
      (gaussianReal 0 θ.toNNReal) := fun l => measurePreserving_eval _ l
  have hu1 : ∀ b, ∫ t, u t b ∂μL = 1 := fun b => by
    simp only [u, μL]
    rw [integral_fintype_prod_eq_prod (fun l t => letterRatio θ N n t (e.symm b l))]
    exact Finset.prod_eq_one fun l _ => integral_postRatio hθ hs _
  have hlog : ∀ b, Integrable (fun t => Real.log (u t b)) μL := fun b => by
    simp_rw [hlogu]
    exact integrable_finsetSum _ fun l _ =>
      (hmp l).integrable_comp_of_integrable (integrable_log_postRatio hθ hs _)
  have hp : ∀ x, (blockLaw θ n L x).toReal = μL.real (blockQuant n L ⁻¹' {x}) := fun x => by
    rw [blockLaw, Measure.toPMF_apply,
      Measure.map_apply (measurable_blockQuant n L) (measurableSet_singleton _), measureReal_def]
  refine le_of_eq_of_le ?_ (DMC.integral_sum_mul_log_le_inputMutualInfo _ _
    (measurable_blockQuant n L) hp u hu hu1 hlog)
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  rw [sum_blockChannel_toReal_mul N _ (measurable_blockQuant n L)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp [hlogu, blockQuant, blockInput, e]

def badSet (n L : ℕ) (P : ℝ) : Set (Fin L → ℝ) :=
  {t | L * P < ∑ l, value n (level n (t l)) ^ 2}

theorem measurableSet_badSet (n L : ℕ) (P : ℝ) : MeasurableSet (badSet n L P) :=
  measurableSet_lt measurable_const (Finset.measurable_sum _ fun l _ =>
    ((measurable_value_level n).comp (measurable_pi_apply l)).pow_const 2)

theorem clipValue_of_notMem_badSet {n L : ℕ} {P : ℝ} {t : Fin L → ℝ} (ht : t ∉ badSet n L P) :
    clipValue n L P (fun k => level n (t k)) = fun l => value n (level n (t l)) := by
  have ht' : ∑ l, value n (level n (t l)) ^ 2 ≤ L * P := not_lt.1 ht
  simp [clipValue, ht']

theorem measurable_clipValue_level (n L : ℕ) (P : ℝ) :
    Measurable fun t : Fin L → ℝ => clipValue n L P (fun k => level n (t k)) :=
  (measurable_of_finite (clipValue n L P)).comp
    (measurable_pi_iff.2 fun k => (measurable_level n).comp (measurable_pi_apply k))

private lemma measurable_blockSummand (θ N : ℝ) (n L : ℕ) (P : ℝ) (l : Fin L) :
    Measurable fun w : (Fin L → ℝ) × (Fin L → ℝ) => Real.log (letterRatio θ N n (w.1 l)
      (level n (clipValue n L P (fun k => level n (w.1 k)) l + w.2 l))) :=
  measurable_log_letterRatio θ N n ((measurable_pi_apply l).comp measurable_fst)
    ((measurable_level n).comp ((((measurable_pi_apply l).comp
      (measurable_clipValue_level n L P)).comp measurable_fst).add
      ((measurable_pi_apply l).comp measurable_snd)))

private lemma abs_le_add_sq_div {c : ℝ} (hc : 0 < c) (t : ℝ) : |t| ≤ c + t ^ 2 / c := by
  rw [← sq_abs t]
  have h : c * |t| ≤ c * c + |t| ^ 2 := by nlinarith [sq_nonneg (|t| - c), abs_nonneg t]
  rw [show c + |t| ^ 2 / c = (c * c + |t| ^ 2) / c by field_simp]
  rw [le_div_iff₀ hc]
  linarith

theorem integral_blockGain_ge {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n L : ℕ) (P : ℝ) {c : ℝ}
    (hc : 0 < c) :
    L * letterGain θ N n - L * ((4 * n * c + 4 * n ^ 2)
        * (Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal).real (badSet n L P)
        + 4 * n / c * θ) / (2 * (θ * N / (θ + N)))
      ≤ ∫ t, ∫ z, ∑ l, Real.log (letterRatio θ N n (t l)
        (level n (clipValue n L P (fun k => level n (t k)) l + z l))) ∂noise N L
      ∂Measure.pi (fun _ : Fin L => gaussianReal 0 θ.toNNReal) := by
  set μ := gaussianReal 0 θ.toNNReal
  set ν := gaussianReal 0 N.toNNReal
  set μL := Measure.pi fun _ : Fin L => μ
  set νL := noise N L
  set s := θ * N / (θ + N)
  have hs : 0 < s := by positivity
  set G : (Fin L → ℝ) × (Fin L → ℝ) → ℝ := fun w => ∑ l, Real.log (letterRatio θ N n (w.1 l)
    (level n (clipValue n L P (fun k => level n (w.1 k)) l + w.2 l)))
  set g : ℝ × ℝ → ℝ := fun w => Real.log (letterRatio θ N n w.1
    (level n (value n (level n w.1) + w.2)))
  set Gu : (Fin L → ℝ) × (Fin L → ℝ) → ℝ := fun w => ∑ l, g (w.1 l, w.2 l)
  set ind : (Fin L → ℝ) → ℝ := (badSet n L P).indicator 1
  set E : (Fin L → ℝ) × (Fin L → ℝ) → ℝ := fun w =>
    ∑ l, ((4 * n * c + 4 * n ^ 2) * ind w.1 + 4 * n / c * w.1 l ^ 2) / (2 * s)
  have hmp : ∀ l : Fin L, MeasurePreserving (fun t : Fin L → ℝ => t l) μL μ :=
    fun l => measurePreserving_eval _ l
  have hmp2 : ∀ l : Fin L, MeasurePreserving (fun w : (Fin L → ℝ) × (Fin L → ℝ) => (w.1 l, w.2 l))
      (μL.prod νL) (μ.prod ν) := fun l =>
    (measurePreserving_eval (fun _ : Fin L => μ) l).prod
      (measurePreserving_eval (fun _ : Fin L => ν) l)
  have hg : Integrable g (μ.prod ν) := integrable_log_letterRatio_level hθ hN n
  have hGu : Integrable Gu (μL.prod νL) :=
    integrable_finsetSum _ fun l _ => (hmp2 l).integrable_comp_of_integrable hg
  have hGu_eq : ∫ w, Gu w ∂(μL.prod νL) = L * letterGain θ N n := by
    simp only [Gu]
    rw [integral_finsetSum (f := fun l (w : (Fin L → ℝ) × (Fin L → ℝ)) => g (w.1 l, w.2 l)) _
      fun l _ => (hmp2 l).integrable_comp_of_integrable hg]
    simp_rw [integral_comp_of_measurePreserving (hmp2 _) hg.aestronglyMeasurable]
    simp [g, letterGain, μ, ν]
  have hbad := measurableSet_badSet n L P
  have hind : Integrable ind μL := (integrable_const 1).indicator hbad
  have hsq : ∀ l : Fin L, Integrable (fun t : Fin L → ℝ => t l ^ 2) μL := fun l =>
    (hmp l).integrable_comp_of_integrable (integrable_sq_gaussianReal _)
  have hE : Integrable E (μL.prod νL) :=
    integrable_finsetSum _ fun l _ =>
      (((hind.comp_fst νL).const_mul _).add (((hsq l).comp_fst νL).const_mul _)).div_const _
  have hE_eq : ∫ w, E w ∂(μL.prod νL)
      = L * ((4 * n * c + 4 * n ^ 2) * μL.real (badSet n L P) + 4 * n / c * θ) / (2 * s) := by
    have h1 : ∀ l : Fin L, ∫ w, ((4 * n * c + 4 * n ^ 2) * ind w.1 + 4 * n / c * w.1 l ^ 2)
        / (2 * s) ∂(μL.prod νL)
        = ((4 * n * c + 4 * n ^ 2) * μL.real (badSet n L P) + 4 * n / c * θ) / (2 * s) := by
      intro l
      have h3 : Integrable (fun w : (Fin L → ℝ) × (Fin L → ℝ) =>
          (4 * n * c + 4 * n ^ 2) * ind w.1) (μL.prod νL) := (hind.comp_fst νL).const_mul _
      have h4 : Integrable (fun w : (Fin L → ℝ) × (Fin L → ℝ) =>
          4 * n / c * w.1 l ^ 2) (μL.prod νL) := ((hsq l).comp_fst νL).const_mul _
      rw [integral_div, integral_add h3 h4, integral_const_mul, integral_const_mul,
        integral_fun_fst ind, integral_fun_fst (fun t : Fin L → ℝ => t l ^ 2),
        integral_indicator_one hbad,
        integral_comp_of_measurePreserving (hmp l) (by fun_prop : AEStronglyMeasurable
          (fun t : ℝ => t ^ 2) μ), integral_sq_gaussianReal]
      simp [Real.coe_toNNReal _ hθ.le]
    simp only [E]
    rw [integral_finsetSum (f := fun l (w : (Fin L → ℝ) × (Fin L → ℝ)) =>
      ((4 * n * c + 4 * n ^ 2) * ind w.1 + 4 * n / c * w.1 l ^ 2) / (2 * s)) _ fun l _ =>
      (((hind.comp_fst νL).const_mul _).add (((hsq l).comp_fst νL).const_mul _)).div_const _]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hGm : Measurable G :=
    Finset.measurable_sum _ fun l _ => measurable_blockSummand θ N n L P l
  have hpt : ∀ w, |G w - Gu w| ≤ E w := by
    intro w
    simp only [G, Gu, E, g, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    by_cases hw : w.1 ∈ badSet n L P
    · have hi : ind w.1 = 1 := by simp [ind, hw]
      rw [hi]
      refine (abs_log_letterRatio_sub_le hθ hN n _ _ _).trans ?_
      rw [div_le_div_iff_of_pos_right (by positivity)]
      have := abs_le_add_sq_div hc (w.1 l)
      have h4 : (4 * n : ℝ) * |w.1 l| ≤ 4 * n * (c + w.1 l ^ 2 / c) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      have h5 : 4 * n / c * w.1 l ^ 2 = 4 * n * (w.1 l ^ 2 / c) := by ring
      nlinarith
    · rw [clipValue_of_notMem_badSet hw, sub_self, abs_zero]
      have : 0 ≤ ind w.1 := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      positivity
  have hdiff : Integrable (fun w => G w - Gu w) (μL.prod νL) :=
    hE.mono' (hGm.aestronglyMeasurable.sub hGu.aestronglyMeasurable)
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hpt w)
  have hG : Integrable G (μL.prod νL) := (hGu.add hdiff).congr (ae_of_all _ fun w => by simp)
  have hprod := integral_prod G hG
  simp only [G] at hprod
  rw [← hprod, ← hGu_eq, ← hE_eq, ← integral_sub hGu hE]
  exact integral_mono (hGu.sub hE) hG fun w => by
    have := hpt w
    simp only
    linarith [neg_abs_le (G w - Gu w)]

theorem measureReal_badSet_le {θ : ℝ} (n : ℕ) {L : ℕ} (hL : 0 < L) {P : ℝ}
    (hm : ∫ t, value n (level n t) ^ 2 ∂gaussianReal 0 θ.toNNReal < P) :
    (Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal).real (badSet n L P)
      ≤ Var[fun t => value n (level n t) ^ 2; gaussianReal 0 θ.toNNReal]
        / (L * (P - ∫ t, value n (level n t) ^ 2 ∂gaussianReal 0 θ.toNNReal) ^ 2) := by
  set μ := gaussianReal 0 θ.toNNReal
  set μL := Measure.pi fun _ : Fin L => μ
  set Y : ℝ → ℝ := fun t => value n (level n t) ^ 2
  set m := ∫ t, Y t ∂μ
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  have hPm : 0 < P - m := sub_pos.2 hm
  have hYm : Measurable Y := (measurable_value_level n).pow_const 2
  have hY : MemLp Y 2 μ := MemLp.of_bound hYm.aestronglyMeasurable ((n : ℝ) ^ 2)
    (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_value_le n _) 2)
  have hmp : ∀ l : Fin L, MeasurePreserving (fun t : Fin L → ℝ => t l) μL μ :=
    fun l => measurePreserving_eval _ l
  set S : (Fin L → ℝ) → ℝ := ∑ l : Fin L, fun t => Y (t l)
  have hSapp : ∀ t, S t = ∑ l, Y (t l) := fun t => by simp [S, Finset.sum_apply]
  have hS : MemLp S 2 μL := memLp_finsetSum' _ fun l _ => hY.comp_measurePreserving (hmp l)
  have hVar : Var[S; μL] = L * Var[Y; μ] := by
    rw [variance_sum_pi (fun _ => hY)]
    simp
  have hmean : μL[S] = L * m := by
    simp_rw [hSapp]
    rw [integral_finsetSum (f := fun l (t : Fin L → ℝ) => Y (t l)) _ fun l _ =>
      (hmp l).integrable_comp_of_integrable (hY.integrable one_le_two)]
    simp_rw [integral_comp_of_measurePreserving (hmp _) hYm.aestronglyMeasurable]
    simp [m]
  have hsub : badSet n L P ⊆ {t | L * (P - m) ≤ |S t - μL[S]|} := fun t ht => by
    have ht' : L * P < ∑ l, Y (t l) := ht
    change L * (P - m) ≤ |S t - μL[S]|
    rw [hmean, hSapp, abs_of_pos (by nlinarith)]
    nlinarith
  have hcheb := meas_ge_le_variance_div_sq hS (mul_pos hL' hPm)
  have hV : 0 ≤ Var[S; μL] / (L * (P - m)) ^ 2 := div_nonneg (variance_nonneg _ _) (by positivity)
  calc μL.real (badSet n L P) ≤ μL.real {t | L * (P - m) ≤ |S t - μL[S]|} :=
        measureReal_mono hsub
    _ ≤ Var[S; μL] / (L * (P - m)) ^ 2 := ENNReal.toReal_le_of_le_ofReal hV hcheb
    _ = Var[Y; μ] / (L * (P - m) ^ 2) := by
      rw [hVar]
      field_simp

theorem exists_blockQuantization {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    ∀ R, 0 ≤ R → R < awgnCapacity P N →
      ∃ (L s t : ℕ) (a : Fin s → Fin L → ℝ) (q : (Fin L → ℝ) → Fin t) (p : PMF (Fin s)),
        0 < L ∧ (∀ x, ∑ l, a x l ^ 2 ≤ L * P) ∧ Measurable q ∧
          L * R < (blockChannel N a q).inputMutualInfo p := by
  intro R hR hRC
  have hPpos : 0 < P := by
    refine hP.lt_of_ne fun h => ?_
    subst h
    simp [awgnCapacity] at hRC
    linarith
  have hcont : ContinuousAt (fun θ => awgnCapacity θ N) P := by
    unfold awgnCapacity
    exact continuousAt_const.mul ((continuousAt_const.add (continuousAt_id.div_const N)).log
      (ne_of_gt (by have := div_nonneg hP hN.le; simp only [Pi.add_apply, id]; linarith)))
  obtain ⟨θ, hθC, hθ0, hθP⟩ : ∃ θ, R < awgnCapacity θ N ∧ 0 < θ ∧ θ < P := by
    have h1 : ∀ᶠ θ in 𝓝[<] P, R < awgnCapacity θ N :=
      nhdsWithin_le_nhds (hcont.eventually (lt_mem_nhds hRC))
    have h2 : ∀ᶠ θ in 𝓝[<] P, θ ∈ Set.Ioo 0 P := Ioo_mem_nhdsLT hPpos
    exact (h1.and h2).exists.imp fun θ h => ⟨h.1, h.2.1, h.2.2⟩
  set η := (awgnCapacity θ N - R) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hT2 := tendsto_integral_sq_value_level θ
  rw [Real.coe_toNNReal _ hθ0.le] at hT2
  obtain ⟨n, hn1, hn2⟩ := (((tendsto_letterGain hθ0 hN).eventually
    (lt_mem_nhds (show R + 3 * η < awgnCapacity θ N by linarith))).and
    (hT2.eventually (gt_mem_nhds hθP))).exists
  set m := ∫ t, value n (level n t) ^ 2 ∂gaussianReal 0 θ.toNNReal
  set V := Var[fun t => value n (level n t) ^ 2; gaussianReal 0 θ.toNNReal]
  set s := θ * N / (θ + N)
  have hs : 0 < s := by positivity
  have hPm : 0 < P - m := sub_pos.2 hn2
  set c := 4 * n * θ / (2 * s * η) + 1
  have hc : 0 < c := by positivity
  have h5 : 4 * n / c * θ / (2 * s) < η := by
    have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * s * η)).1
      (lt_add_one (4 * n * θ / (2 * s * η)))
    rw [show 4 * n / c * θ / (2 * s) = 4 * n * θ / (c * (2 * s)) by field_simp,
      div_lt_iff₀ (by positivity)]
    nlinarith
  set A := 4 * n * c + 4 * (n : ℝ) ^ 2
  have hA : 0 ≤ A := by positivity
  set K := A * V / (P - m) ^ 2 / (2 * s)
  set L := ⌈K / η⌉₊ + 1
  have hL : 0 < L := Nat.succ_pos _
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  have h4 : K < L * η := by
    have := Nat.le_ceil (K / η)
    have h' : K / η < L := by
      simp only [L, Nat.cast_add, Nat.cast_one]
      linarith
    rwa [div_lt_iff₀ hη0] at h'
  have hβ := measureReal_badSet_le (L := L) (P := P) n hL hn2
  have hV : 0 ≤ V := variance_nonneg _ _
  have h2 : L * (A * (Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal).real
      (badSet n L P)) / (2 * s) ≤ K := by
    calc L * (A * (Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal).real
          (badSet n L P)) / (2 * s)
        ≤ L * (A * (V / (L * (P - m) ^ 2))) / (2 * s) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hβ hA) hL'.le) (by positivity)
      _ = K := by
          simp only [K]
          field_simp
  have h1 := (integral_blockGain_ge hθ0 hN n L P hc).trans (integral_blockGain_le hθ0 hN n L P)
  refine ⟨L, _, _, blockInput n L P, blockQuant n L, blockLaw θ n L, hL,
    fun x => sum_sq_clipValue_le hP n L _, measurable_blockQuant n L, ?_⟩
  have e1 : L * (A * (Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal).real (badSet n L P)
      + 4 * n / c * θ) / (2 * s)
      = L * (A * (Measure.pi fun _ : Fin L => gaussianReal 0 θ.toNNReal).real
          (badSet n L P)) / (2 * s) + L * (4 * n / c * θ / (2 * s)) := by ring
  have e3 := mul_lt_mul_of_pos_left h5 hL'
  have e4 := mul_lt_mul_of_pos_left hn1 hL'
  have e5 := mul_pos hL' hη0
  linarith

theorem closure_achievable_eq {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable P N R} = Set.Icc 0 (awgnCapacity P N) :=
  closure_achievable_eq_of_quantization hP hN (exists_blockQuantization hP hN)

end AWGN

end Meat
