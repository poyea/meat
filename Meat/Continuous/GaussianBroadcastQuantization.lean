import Meat.Continuous.GaussianMACQuantization

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Meat

namespace GaussianBroadcast

open AWGN GaussianMAC

noncomputable def sumClip (L : ℕ) (P : ℝ) (w : Fin L → ℝ) : Fin L → ℝ :=
  if ∑ l, w l ^ 2 ≤ L * P then w else 0

theorem sum_sq_sumClip_le {P : ℝ} (hP : 0 ≤ P) (L : ℕ) (w : Fin L → ℝ) :
    ∑ l, sumClip L P w l ^ 2 ≤ L * P := by
  unfold sumClip
  split_ifs with h
  · exact h
  · simpa using mul_nonneg (Nat.cast_nonneg L) hP

noncomputable def sumSignal (n L : ℕ) (P : ℝ) (t : (Fin L → ℝ) × (Fin L → ℝ)) : Fin L → ℝ :=
  sumClip L P fun l => value n (level n (t.1 l)) + value n (level n (t.2 l))

def sumBad (n L : ℕ) (P : ℝ) : Set ((Fin L → ℝ) × (Fin L → ℝ)) :=
  {t | L * P < ∑ l, (value n (level n (t.1 l)) + value n (level n (t.2 l))) ^ 2}

theorem measurableSet_sumBad (n L : ℕ) (P : ℝ) : MeasurableSet (sumBad n L P) :=
  measurableSet_lt measurable_const (Finset.measurable_sum _ fun l _ =>
    ((((measurable_value_level n).comp ((measurable_pi_apply l).comp measurable_fst)).add
      ((measurable_value_level n).comp ((measurable_pi_apply l).comp measurable_snd)))).pow_const 2)

theorem sumSignal_of_notMem {n L : ℕ} {P : ℝ} {t : (Fin L → ℝ) × (Fin L → ℝ)}
    (ht : t ∉ sumBad n L P) :
    sumSignal n L P t = fun l => value n (level n (t.1 l)) + value n (level n (t.2 l)) := by
  have ht' : ∑ l, (value n (level n (t.1 l)) + value n (level n (t.2 l))) ^ 2 ≤ L * P :=
    not_lt.1 ht
  simp [sumSignal, sumClip, ht']

theorem measurable_sumSignal (n L : ℕ) (P : ℝ) : Measurable (sumSignal n L P) := by
  have h : Measurable fun t : (Fin L → ℝ) × (Fin L → ℝ) =>
      (fun l => value n (level n (t.1 l)) + value n (level n (t.2 l))) :=
    measurable_pi_iff.2 fun l =>
      ((measurable_value_level n).comp ((measurable_pi_apply l).comp measurable_fst)).add
        ((measurable_value_level n).comp ((measurable_pi_apply l).comp measurable_snd))
  have hs : MeasurableSet {w : Fin L → ℝ | ∑ l, w l ^ 2 ≤ L * P} :=
    measurableSet_le (Finset.measurable_sum _ fun l _ => (measurable_pi_apply l).pow_const 2)
      measurable_const
  exact (Measurable.ite hs measurable_id measurable_const).comp h

private lemma integral_comp_of_measurePreserving' {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {f : α → β}
    (hf : MeasurePreserving f μ ν) {g : β → ℝ} (hg : AEStronglyMeasurable g ν) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := by
  rw [← hf.map_eq] at hg
  rw [← integral_map hf.measurable.aemeasurable hg, hf.map_eq]

private lemma abs_le_add_sq_div' {c : ℝ} (hc : 0 < c) (t : ℝ) : |t| ≤ c + t ^ 2 / c := by
  rw [← sq_abs t]
  have h : c * |t| ≤ c * c + |t| ^ 2 := by nlinarith [sq_nonneg (|t| - c), abs_nonneg t]
  rw [show c + |t| ^ 2 / c = (c * c + |t| ^ 2) / c by field_simp]
  rw [le_div_iff₀ hc]
  linarith

private lemma diff_le {θ N : ℝ} (hθ : 0 < θ) (hN : 0 < N) (n : ℕ) {c : ℝ} (hc : 0 < c)
    {i : ℝ} (hi : 1 ≤ i) (t : ℝ) (b b' : Level n) :
    |Real.log (letterRatio θ N n t b) - Real.log (letterRatio θ N n t b')|
      ≤ ((4 * n * c + 4 * n ^ 2) * i + 4 * n / c * t ^ 2) / (2 * (θ * N / (θ + N))) := by
  have hs : 0 < θ * N / (θ + N) := by positivity
  refine (abs_log_letterRatio_sub_le hθ hN n _ _ _).trans ?_
  rw [div_le_div_iff_of_pos_right (by positivity)]
  have := abs_le_add_sq_div' hc t
  have h4 : (4 * n : ℝ) * |t| ≤ 4 * n * (c + t ^ 2 / c) :=
    mul_le_mul_of_nonneg_left this (by positivity)
  have h5 : 4 * n / c * t ^ 2 = 4 * n * (t ^ 2 / c) := by ring
  have hA : 0 ≤ 4 * n * c + 4 * (n : ℝ) ^ 2 := by positivity
  nlinarith

theorem integral_cloudGain_ge {θ₁ θ₂ N : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hN : 0 < N)
    (n L : ℕ) (P : ℝ) {c : ℝ} (hc : 0 < c) :
    L * tinGain θ₁ θ₂ N n - L * ((4 * n * c + 4 * n ^ 2)
        * ((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
          (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal)).real (sumBad n L P)
        + 4 * n / c * θ₂) / (2 * (θ₂ * (θ₁ + N) / (θ₂ + (θ₁ + N))))
      ≤ ∫ t, ∫ z, ∑ l, Real.log (letterRatio θ₂ (θ₁ + N) n (t.2 l)
          (level n (sumSignal n L P t l + z l))) ∂noise N L
        ∂((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
          (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal)) := by
  have hM : 0 < θ₁ + N := by linarith
  set M := θ₁ + N
  set μ₁ := gaussianReal 0 θ₁.toNNReal
  set μ₂ := gaussianReal 0 θ₂.toNNReal
  set ν := gaussianReal 0 N.toNNReal
  set μ₁L := Measure.pi fun _ : Fin L => μ₁
  set μ₂L := Measure.pi fun _ : Fin L => μ₂
  set νL := noise N L
  set s := θ₂ * M / (θ₂ + M)
  have hs : 0 < s := by positivity
  set A := 4 * n * c + 4 * (n : ℝ) ^ 2
  set G : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) → ℝ := fun w =>
    ∑ l, Real.log (letterRatio θ₂ M n (w.1.2 l) (level n (sumSignal n L P w.1 l + w.2 l)))
  set g : (ℝ × ℝ) × ℝ → ℝ := fun x => Real.log (letterRatio θ₂ M n x.1.2
    (level n (value n (level n x.1.1) + value n (level n x.1.2) + x.2)))
  set Gu : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) → ℝ := fun w =>
    ∑ l, g ((w.1.1 l, w.1.2 l), w.2 l)
  set ind : (Fin L → ℝ) × (Fin L → ℝ) → ℝ := (sumBad n L P).indicator 1
  set E : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) → ℝ := fun w =>
    ∑ l, (A * ind w.1 + 4 * n / c * w.1.2 l ^ 2) / (2 * s)
  have hmp2 : ∀ l : Fin L, MeasurePreserving
      (fun w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) => ((w.1.1 l, w.1.2 l), w.2 l))
      ((μ₁L.prod μ₂L).prod νL) ((μ₁.prod μ₂).prod ν) := fun l =>
    ((measurePreserving_eval (fun _ : Fin L => μ₁) l).prod
      (measurePreserving_eval (fun _ : Fin L => μ₂) l)).prod
      (measurePreserving_eval (fun _ : Fin L => ν) l)
  have hg : Integrable g ((μ₁.prod μ₂).prod ν) :=
    integrable_log_letterRatio hθ₂ hM n (measurable_snd.comp measurable_fst)
      ((measurable_level n).comp ((((measurable_value_level n).comp
        (measurable_fst.comp measurable_fst)).add ((measurable_value_level n).comp
          (measurable_snd.comp measurable_fst))).add measurable_snd))
      (((integrable_sq_gaussianReal _).comp_snd _).comp_fst _)
  have hGu : Integrable Gu ((μ₁L.prod μ₂L).prod νL) :=
    integrable_finsetSum _ fun l _ => (hmp2 l).integrable_comp_of_integrable hg
  have hGu_eq : ∫ w, Gu w ∂((μ₁L.prod μ₂L).prod νL) = L * tinGain θ₁ θ₂ N n := by
    simp only [Gu]
    rw [integral_finsetSum (f := fun l (w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ)) =>
      g ((w.1.1 l, w.1.2 l), w.2 l)) _ fun l _ => (hmp2 l).integrable_comp_of_integrable hg]
    simp_rw [integral_comp_of_measurePreserving' (hmp2 _) hg.aestronglyMeasurable]
    simp [g, tinGain, μ₁, μ₂, ν, M]
  have hbad := measurableSet_sumBad n L P
  have hind : Integrable ind (μ₁L.prod μ₂L) := (integrable_const (1 : ℝ)).indicator hbad
  have hind_eq : ∫ t, ind t ∂(μ₁L.prod μ₂L) = (μ₁L.prod μ₂L).real (sumBad n L P) :=
    integral_indicator_one hbad
  have hsq : ∀ l : Fin L, Integrable (fun w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) =>
      w.1.2 l ^ 2) ((μ₁L.prod μ₂L).prod νL) := fun l =>
    ((((measurePreserving_eval (fun _ : Fin L => μ₂) l).integrable_comp_of_integrable
      (integrable_sq_gaussianReal _)).comp_snd μ₁L).comp_fst νL)
  have hsq_eq : ∀ l : Fin L, ∫ w, w.1.2 l ^ 2 ∂((μ₁L.prod μ₂L).prod νL) = θ₂ := fun l => by
    rw [integral_fun_fst (fun t : (Fin L → ℝ) × (Fin L → ℝ) => t.2 l ^ 2),
      integral_fun_snd (fun t : Fin L → ℝ => t l ^ 2),
      integral_comp_of_measurePreserving' (measurePreserving_eval (fun _ : Fin L => μ₂) l)
        (by fun_prop : AEStronglyMeasurable (fun t : ℝ => t ^ 2) μ₂), integral_sq_gaussianReal]
    simp [Real.coe_toNNReal _ hθ₂.le]
  have hE : Integrable E ((μ₁L.prod μ₂L).prod νL) :=
    integrable_finsetSum _ fun l _ =>
      (((hind.comp_fst νL).const_mul _).add ((hsq l).const_mul _)).div_const _
  have hE_eq : ∫ w, E w ∂((μ₁L.prod μ₂L).prod νL)
      = L * (A * (μ₁L.prod μ₂L).real (sumBad n L P) + 4 * n / c * θ₂) / (2 * s) := by
    have h1 : ∀ l : Fin L, ∫ w, (A * ind w.1 + 4 * n / c * w.1.2 l ^ 2) / (2 * s)
        ∂((μ₁L.prod μ₂L).prod νL)
        = (A * (μ₁L.prod μ₂L).real (sumBad n L P) + 4 * n / c * θ₂) / (2 * s) := by
      intro l
      rw [integral_div, integral_add ((hind.comp_fst νL).const_mul _) ((hsq l).const_mul _),
        integral_const_mul, integral_const_mul, integral_fun_fst ind, hind_eq, hsq_eq]
      simp
    simp only [E]
    rw [integral_finsetSum (f := fun l (w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ)) =>
      (A * ind w.1 + 4 * n / c * w.1.2 l ^ 2) / (2 * s)) _ fun l _ =>
      (((hind.comp_fst νL).const_mul _).add ((hsq l).const_mul _)).div_const _]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hGm : Measurable G :=
    Finset.measurable_sum _ fun l _ => measurable_log_letterRatio θ₂ M n
      ((measurable_pi_apply l).comp (measurable_snd.comp measurable_fst))
      ((measurable_level n).comp ((((measurable_pi_apply l).comp
        (measurable_sumSignal n L P)).comp measurable_fst).add
        ((measurable_pi_apply l).comp measurable_snd)))
  have hpt : ∀ w, |G w - Gu w| ≤ E w := by
    intro w
    simp only [G, Gu, E, g, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    by_cases hw : w.1 ∈ sumBad n L P
    · have hi : ind w.1 = 1 := by simp [ind, hw]
      rw [hi]
      exact diff_le hθ₂ hM n hc le_rfl _ _ _
    · rw [sumSignal_of_notMem hw, sub_self, abs_zero]
      have : 0 ≤ ind w.1 := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      positivity
  have hdiff : Integrable (fun w => G w - Gu w) ((μ₁L.prod μ₂L).prod νL) :=
    hE.mono' (hGm.aestronglyMeasurable.sub hGu.aestronglyMeasurable)
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hpt w)
  have hG : Integrable G ((μ₁L.prod μ₂L).prod νL) :=
    (hGu.add hdiff).congr (ae_of_all _ fun w => by simp)
  have hprod := integral_prod G hG
  simp only [G] at hprod
  rw [← hprod, ← hGu_eq, ← hE_eq, ← integral_sub hGu hE]
  exact integral_mono (hGu.sub hE) hG fun w => by
    have := hpt w
    simp only
    linarith [neg_abs_le (G w - Gu w)]

theorem integral_satGain_ge {θ₁ θ₂ N : ℝ} (hθ₁ : 0 < θ₁) (hN : 0 < N)
    (n L : ℕ) (P : ℝ) {c : ℝ} (hc : 0 < c) :
    L * letterGain θ₁ N n - L * ((4 * n * c + 4 * n ^ 2)
        * ((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
          (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal)).real (sumBad n L P)
        + 4 * n / c * θ₁) / (2 * (θ₁ * N / (θ₁ + N)))
      ≤ ∫ t, ∫ z, ∑ l, Real.log (letterRatio θ₁ N n (t.1 l)
          (level n (sumSignal n L P t l - value n (level n (t.2 l)) + z l))) ∂noise N L
        ∂((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
          (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal)) := by
  set μ₁ := gaussianReal 0 θ₁.toNNReal
  set μ₂ := gaussianReal 0 θ₂.toNNReal
  set ν := gaussianReal 0 N.toNNReal
  set μ₁L := Measure.pi fun _ : Fin L => μ₁
  set μ₂L := Measure.pi fun _ : Fin L => μ₂
  set νL := noise N L
  set s := θ₁ * N / (θ₁ + N)
  have hs : 0 < s := by positivity
  set A := 4 * n * c + 4 * (n : ℝ) ^ 2
  set G : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) → ℝ := fun w =>
    ∑ l, Real.log (letterRatio θ₁ N n (w.1.1 l)
      (level n (sumSignal n L P w.1 l - value n (level n (w.1.2 l)) + w.2 l)))
  set g : ℝ × ℝ → ℝ := fun x => Real.log (letterRatio θ₁ N n x.1
    (level n (value n (level n x.1) + x.2)))
  set Gu : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) → ℝ := fun w =>
    ∑ l, g (w.1.1 l, w.2 l)
  set ind : (Fin L → ℝ) × (Fin L → ℝ) → ℝ := (sumBad n L P).indicator 1
  set E : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) → ℝ := fun w =>
    ∑ l, (A * ind w.1 + 4 * n / c * w.1.1 l ^ 2) / (2 * s)
  have hfst : MeasurePreserving Prod.fst (μ₁L.prod μ₂L) μ₁L :=
    ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
  have hmp2 : ∀ l : Fin L, MeasurePreserving
      (fun w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) => (w.1.1 l, w.2 l))
      ((μ₁L.prod μ₂L).prod νL) (μ₁.prod ν) := fun l =>
    ((measurePreserving_eval (fun _ : Fin L => μ₁) l).comp hfst).prod
      (measurePreserving_eval (fun _ : Fin L => ν) l)
  have hg : Integrable g (μ₁.prod ν) := integrable_log_letterRatio_level hθ₁ hN n
  have hGu : Integrable Gu ((μ₁L.prod μ₂L).prod νL) :=
    integrable_finsetSum _ fun l _ => (hmp2 l).integrable_comp_of_integrable hg
  have hGu_eq : ∫ w, Gu w ∂((μ₁L.prod μ₂L).prod νL) = L * letterGain θ₁ N n := by
    simp only [Gu]
    rw [integral_finsetSum (f := fun l (w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ)) =>
      g (w.1.1 l, w.2 l)) _ fun l _ => (hmp2 l).integrable_comp_of_integrable hg]
    simp_rw [integral_comp_of_measurePreserving' (hmp2 _) hg.aestronglyMeasurable]
    simp [g, letterGain, μ₁, ν]
  have hbad := measurableSet_sumBad n L P
  have hind : Integrable ind (μ₁L.prod μ₂L) := (integrable_const (1 : ℝ)).indicator hbad
  have hind_eq : ∫ t, ind t ∂(μ₁L.prod μ₂L) = (μ₁L.prod μ₂L).real (sumBad n L P) :=
    integral_indicator_one hbad
  have hsq : ∀ l : Fin L, Integrable (fun w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ) =>
      w.1.1 l ^ 2) ((μ₁L.prod μ₂L).prod νL) := fun l =>
    ((((measurePreserving_eval (fun _ : Fin L => μ₁) l).integrable_comp_of_integrable
      (integrable_sq_gaussianReal _)).comp_fst μ₂L).comp_fst νL)
  have hsq_eq : ∀ l : Fin L, ∫ w, w.1.1 l ^ 2 ∂((μ₁L.prod μ₂L).prod νL) = θ₁ := fun l => by
    rw [integral_fun_fst (fun t : (Fin L → ℝ) × (Fin L → ℝ) => t.1 l ^ 2),
      integral_fun_fst (fun t : Fin L → ℝ => t l ^ 2),
      integral_comp_of_measurePreserving' (measurePreserving_eval (fun _ : Fin L => μ₁) l)
        (by fun_prop : AEStronglyMeasurable (fun t : ℝ => t ^ 2) μ₁), integral_sq_gaussianReal]
    simp [Real.coe_toNNReal _ hθ₁.le]
  have hE : Integrable E ((μ₁L.prod μ₂L).prod νL) :=
    integrable_finsetSum _ fun l _ =>
      (((hind.comp_fst νL).const_mul _).add ((hsq l).const_mul _)).div_const _
  have hE_eq : ∫ w, E w ∂((μ₁L.prod μ₂L).prod νL)
      = L * (A * (μ₁L.prod μ₂L).real (sumBad n L P) + 4 * n / c * θ₁) / (2 * s) := by
    have h1 : ∀ l : Fin L, ∫ w, (A * ind w.1 + 4 * n / c * w.1.1 l ^ 2) / (2 * s)
        ∂((μ₁L.prod μ₂L).prod νL)
        = (A * (μ₁L.prod μ₂L).real (sumBad n L P) + 4 * n / c * θ₁) / (2 * s) := by
      intro l
      rw [integral_div, integral_add ((hind.comp_fst νL).const_mul _) ((hsq l).const_mul _),
        integral_const_mul, integral_const_mul, integral_fun_fst ind, hind_eq, hsq_eq]
      simp
    simp only [E]
    rw [integral_finsetSum (f := fun l (w : ((Fin L → ℝ) × (Fin L → ℝ)) × (Fin L → ℝ)) =>
      (A * ind w.1 + 4 * n / c * w.1.1 l ^ 2) / (2 * s)) _ fun l _ =>
      (((hind.comp_fst νL).const_mul _).add ((hsq l).const_mul _)).div_const _]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hGm : Measurable G :=
    Finset.measurable_sum _ fun l _ => measurable_log_letterRatio θ₁ N n
      ((measurable_pi_apply l).comp (measurable_fst.comp measurable_fst))
      ((measurable_level n).comp (((((measurable_pi_apply l).comp
        (measurable_sumSignal n L P)).comp measurable_fst).sub
        ((measurable_value_level n).comp ((measurable_pi_apply l).comp
          (measurable_snd.comp measurable_fst)))).add
        ((measurable_pi_apply l).comp measurable_snd)))
  have hpt : ∀ w, |G w - Gu w| ≤ E w := by
    intro w
    simp only [G, Gu, E, g, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    by_cases hw : w.1 ∈ sumBad n L P
    · have hi : ind w.1 = 1 := by simp [ind, hw]
      rw [hi]
      exact diff_le hθ₁ hN n hc le_rfl _ _ _
    · rw [sumSignal_of_notMem hw]
      simp only [add_sub_cancel_right, sub_self, abs_zero]
      have : 0 ≤ ind w.1 := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      positivity
  have hdiff : Integrable (fun w => G w - Gu w) ((μ₁L.prod μ₂L).prod νL) :=
    hE.mono' (hGm.aestronglyMeasurable.sub hGu.aestronglyMeasurable)
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hpt w)
  have hG : Integrable G ((μ₁L.prod μ₂L).prod νL) :=
    (hGu.add hdiff).congr (ae_of_all _ fun w => by simp)
  have hprod := integral_prod G hG
  simp only [G] at hprod
  rw [← hprod, ← hGu_eq, ← hE_eq, ← integral_sub hGu hE]
  exact integral_mono (hGu.sub hE) hG fun w => by
    have := hpt w
    simp only
    linarith [neg_abs_le (G w - Gu w)]

private lemma measureReal_sum_gt_le {α : Type*} [MeasurableSpace α] (ρ : Measure α)
    [IsProbabilityMeasure ρ] {Y : α → ℝ} (hYm : Measurable Y) (hY : MemLp Y 2 ρ) {L : ℕ}
    (hL : 0 < L) {P : ℝ} (hm : ∫ a, Y a ∂ρ < P) :
    (Measure.pi fun _ : Fin L => ρ).real {f | L * P < ∑ l, Y (f l)}
      ≤ Var[Y; ρ] / (L * (P - ∫ a, Y a ∂ρ) ^ 2) := by
  set μL := Measure.pi fun _ : Fin L => ρ
  set m := ∫ a, Y a ∂ρ
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  have hPm : 0 < P - m := sub_pos.2 hm
  have hmp : ∀ l : Fin L, MeasurePreserving (fun f : Fin L → α => f l) μL ρ :=
    fun l => measurePreserving_eval _ l
  set S : (Fin L → α) → ℝ := ∑ l : Fin L, fun f => Y (f l)
  have hSapp : ∀ f, S f = ∑ l, Y (f l) := fun f => by simp [S, Finset.sum_apply]
  have hS : MemLp S 2 μL := memLp_finsetSum' _ fun l _ => hY.comp_measurePreserving (hmp l)
  have hVar : Var[S; μL] = L * Var[Y; ρ] := by
    rw [variance_sum_pi (fun _ => hY)]
    simp
  have hmean : μL[S] = L * m := by
    simp_rw [hSapp]
    rw [integral_finsetSum (f := fun l (f : Fin L → α) => Y (f l)) _ fun l _ =>
      (hmp l).integrable_comp_of_integrable (hY.integrable one_le_two)]
    simp_rw [integral_comp_of_measurePreserving' (hmp _) hYm.aestronglyMeasurable]
    simp [m]
  have hsub : {f : Fin L → α | L * P < ∑ l, Y (f l)} ⊆ {f | L * (P - m) ≤ |S f - μL[S]|} :=
    fun f hf => by
      have hf' : L * P < ∑ l, Y (f l) := hf
      change L * (P - m) ≤ |S f - μL[S]|
      rw [hmean, hSapp, abs_of_pos (by nlinarith)]
      nlinarith
  have hcheb := meas_ge_le_variance_div_sq hS (mul_pos hL' hPm)
  have hV : 0 ≤ Var[S; μL] / (L * (P - m)) ^ 2 :=
    div_nonneg (variance_nonneg _ _) (by positivity)
  calc μL.real {f | L * P < ∑ l, Y (f l)} ≤ μL.real {f | L * (P - m) ≤ |S f - μL[S]|} :=
        measureReal_mono hsub
    _ ≤ Var[S; μL] / (L * (P - m)) ^ 2 := ENNReal.toReal_le_of_le_ofReal hV hcheb
    _ = Var[Y; ρ] / (L * (P - m) ^ 2) := by
      rw [hVar]
      field_simp

private lemma measurable_sumSq (n : ℕ) :
    Measurable fun x : ℝ × ℝ => (value n (level n x.1) + value n (level n x.2)) ^ 2 :=
  (((measurable_value_level n).comp measurable_fst).add
    ((measurable_value_level n).comp measurable_snd)).pow_const 2

private lemma measureReal_sumBad_le {θ₁ θ₂ : ℝ} (n : ℕ) {L : ℕ} (hL : 0 < L) {P : ℝ}
    (hm : ∫ x, (value n (level n x.1) + value n (level n x.2)) ^ 2
      ∂(gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal) < P) :
    ((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
        (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal)).real (sumBad n L P)
      ≤ Var[fun x : ℝ × ℝ => (value n (level n x.1) + value n (level n x.2)) ^ 2;
          (gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)]
        / (L * (P - ∫ x, (value n (level n x.1) + value n (level n x.2)) ^ 2
          ∂(gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)) ^ 2) := by
  have hY : MemLp (fun x : ℝ × ℝ => (value n (level n x.1) + value n (level n x.2)) ^ 2) 2
      ((gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)) :=
    MemLp.of_bound (measurable_sumSq n).aestronglyMeasurable ((2 * n : ℝ) ^ 2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        have h1 := abs_value_le n (level n x.1)
        have h2 := abs_value_le n (level n x.2)
        exact (abs_add_le _ _).trans (by linarith))
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin L)
    (fun _ => gaussianReal 0 θ₁.toNNReal) (fun _ => gaussianReal 0 θ₂.toNNReal)
  rw [← hmp.measureReal_preimage (measurableSet_sumBad n L P).nullMeasurableSet]
  exact measureReal_sum_gt_le _ (measurable_sumSq n) hY hL hm

private lemma tendsto_integral_sumSq {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    Tendsto (fun n => ∫ x, (value n (level n x.1) + value n (level n x.2)) ^ 2
      ∂(gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)) atTop (𝓝 (θ₁ + θ₂)) := by
  set μ₁ := gaussianReal 0 θ₁.toNNReal
  set μ₂ := gaussianReal 0 θ₂.toNNReal
  have i1 : Integrable (fun x : ℝ × ℝ => x.1 ^ 2) (μ₁.prod μ₂) :=
    (integrable_sq_gaussianReal _).comp_fst μ₂
  have i2 : Integrable (fun x : ℝ × ℝ => x.2 ^ 2) (μ₁.prod μ₂) :=
    (integrable_sq_gaussianReal _).comp_snd μ₁
  have hid : ∀ v : ℝ≥0, Integrable (fun t : ℝ => t) (gaussianReal 0 v) := fun v =>
    (memLp_id_gaussianReal' 1 (by simp)).integrable le_rfl
  have i3 : Integrable (fun x : ℝ × ℝ => x.1 * x.2) (μ₁.prod μ₂) := (hid _).mul_prod (hid _)
  have hlim : ∫ x, (x.1 + x.2) ^ 2 ∂(μ₁.prod μ₂) = θ₁ + θ₂ := by
    have e : ∀ x : ℝ × ℝ, (x.1 + x.2) ^ 2 = x.1 ^ 2 + x.2 ^ 2 + 2 * (x.1 * x.2) :=
      fun x => by ring
    have i12 : Integrable (fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2) (μ₁.prod μ₂) := i1.add i2
    simp_rw [e]
    rw [integral_add i12 (i3.const_mul _), integral_add i1 i2, integral_const_mul,
      integral_prod_mul (fun t => t) (fun t => t), integral_fun_fst (fun t => t ^ 2),
      integral_fun_snd (fun t => t ^ 2)]
    simp [μ₁, μ₂, integral_sq_gaussianReal, integral_id_gaussianReal,
      Real.coe_toNNReal _ hθ₁.le, Real.coe_toNNReal _ hθ₂.le]
  rw [← hlim]
  refine tendsto_integral_of_dominated_convergence (fun x : ℝ × ℝ => 3 * x.1 ^ 2 + 3 * x.2 ^ 2 + 12)
    (fun n => (measurable_sumSq n).aestronglyMeasurable)
    (((i1.const_mul 3).add (i2.const_mul 3)).add (integrable_const _))
    (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_value_level_le n x.1
    have h2 := abs_value_level_le n x.2
    have h3 : |value n (level n x.1) + value n (level n x.2)| ≤ |x.1| + |x.2| + 2 :=
      (abs_add_le _ _).trans (by linarith)
    have h := pow_le_pow_left₀ (abs_nonneg _) h3 2
    rw [sq_abs] at h
    nlinarith [sq_abs x.1, sq_abs x.2, sq_nonneg (|x.1| - |x.2|), sq_nonneg (|x.1| - 2),
      sq_nonneg (|x.2| - 2)]
  · exact ((tendsto_value_level tendsto_const_nhds).add
      (tendsto_value_level tendsto_const_nhds)).pow 2

theorem eventually_tendsto_sumBad {θ₁ θ₂ P : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hP : θ₁ + θ₂ < P) : ∀ᶠ n in atTop, Tendsto (fun L : ℕ =>
      ((Measure.pi fun _ : Fin L => gaussianReal 0 θ₁.toNNReal).prod
        (Measure.pi fun _ : Fin L => gaussianReal 0 θ₂.toNNReal)).real (sumBad n L P))
      atTop (𝓝 0) := by
  filter_upwards [(tendsto_integral_sumSq hθ₁ hθ₂).eventually (gt_mem_nhds hP)] with n hn
  have hPm := sub_pos.2 hn
  have hlim : Tendsto (fun L : ℕ =>
      Var[fun x : ℝ × ℝ => (value n (level n x.1) + value n (level n x.2)) ^ 2;
          (gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)]
        / (L * (P - ∫ x, (value n (level n x.1) + value n (level n x.2)) ^ 2
          ∂(gaussianReal 0 θ₁.toNNReal).prod (gaussianReal 0 θ₂.toNNReal)) ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity))
  refine squeeze_zero' (Eventually.of_forall fun L => measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with L hL
  exact measureReal_sumBad_le n hL hn

end GaussianBroadcast

end Meat
