import Meat.Shannon.Binning
import Meat.Shannon.Iid
import Meat.Shannon.Inequalities
import Meat.Source.SlepianWolf

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace SWCode

variable {M₁ M₂ S T : Type*} {n : ℕ}

noncomputable def typicalDecoder (f₁ : (Fin n → S) → M₁) (f₂ : (Fin n → T) → M₂)
    (J : Finset ((Fin n → S) × (Fin n → T))) (d : (Fin n → S) × (Fin n → T)) (m : M₁ × M₂) :
    (Fin n → S) × (Fin n → T) := by
  classical
  exact if h : ∃ xy ∈ J, f₁ xy.1 = m.1 ∧ f₂ xy.2 = m.2 then h.choose else d

noncomputable def binningCode (f₁ : (Fin n → S) → M₁) (f₂ : (Fin n → T) → M₂)
    (J : Finset ((Fin n → S) × (Fin n → T))) (d : (Fin n → S) × (Fin n → T)) :
    SWCode M₁ M₂ S T n :=
  ⟨f₁, f₂, typicalDecoder f₁ f₂ J d⟩

theorem ite_typicalDecoder_le [DecidableEq S] [DecidableEq T] [DecidableEq M₁] [DecidableEq M₂]
    (f₁ : (Fin n → S) → M₁) (f₂ : (Fin n → T) → M₂) (J : Finset ((Fin n → S) × (Fin n → T)))
    (d xy : (Fin n → S) × (Fin n → T)) :
    (if typicalDecoder f₁ f₂ J d (f₁ xy.1, f₂ xy.2) = xy then (0 : ℝ) else 1)
      ≤ (if xy ∈ J then 0 else 1) + ∑ z ∈ J.erase xy,
        (if f₁ z.1 = f₁ xy.1 then (1 : ℝ) else 0) * (if f₂ z.2 = f₂ xy.2 then 1 else 0) := by
  have hs : 0 ≤ ∑ z ∈ J.erase xy,
      (if f₁ z.1 = f₁ xy.1 then (1 : ℝ) else 0) * (if f₂ z.2 = f₂ xy.2 then 1 else 0) :=
    sum_nonneg fun z _ => mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
  by_cases hd : typicalDecoder f₁ f₂ J d (f₁ xy.1, f₂ xy.2) = xy
  · rw [ite_eq_left hd]
    exact add_nonneg (by split_ifs <;> norm_num) hs
  rw [ite_eq_right hd]
  by_cases hJ : xy ∈ J
  · have he : ∃ z ∈ J, f₁ z.1 = (f₁ xy.1, f₂ xy.2).1 ∧ f₂ z.2 = (f₁ xy.1, f₂ xy.2).2 :=
      ⟨xy, hJ, rfl, rfl⟩
    have hz : typicalDecoder f₁ f₂ J d (f₁ xy.1, f₂ xy.2) = he.choose := by
      simp only [typicalDecoder, he, dite_true]
    obtain ⟨hzJ, h1, h2⟩ := he.choose_spec
    rw [ite_eq_left hJ, zero_add]
    calc (1 : ℝ) = (if f₁ he.choose.1 = f₁ xy.1 then (1 : ℝ) else 0) *
          (if f₂ he.choose.2 = f₂ xy.2 then 1 else 0) := by
          rw [ite_eq_left h1, ite_eq_left h2, one_mul]
      _ ≤ _ := single_le_sum (f := fun z => (if f₁ z.1 = f₁ xy.1 then (1 : ℝ) else 0) *
          (if f₂ z.2 = f₂ xy.2 then 1 else 0))
          (fun z _ => mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num))
          (mem_erase.2 ⟨fun h => hd (hz.trans h), hzJ⟩)
  · rw [ite_eq_right hJ]
    exact le_add_of_nonneg_right hs

variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

theorem errorProb_ne_top (c : SWCode M₁ M₂ S T n) (p : PMF (S × T)) : c.errorProb p ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun xy _ => by
    split_ifs
    · exact ENNReal.zero_ne_top
    · exact ENNReal.prod_ne_top fun i _ => p.apply_ne_top _

theorem errorProb_toReal (c : SWCode M₁ M₂ S T n) (p : PMF (S × T)) :
    (c.errorProb p).toReal = ∑ xy : (Fin n → S) × (Fin n → T),
      (if c.dec (c.enc₁ xy.1, c.enc₂ xy.2) = xy then 0 else 1) *
        iidProb p (fun i => (xy.1 i, xy.2 i)) := by
  rw [errorProb, ENNReal.toReal_sum fun xy _ => by
    split_ifs
    · exact ENNReal.zero_ne_top
    · exact ENNReal.prod_ne_top fun i _ => p.apply_ne_top _]
  refine sum_congr rfl fun xy _ => ?_
  split_ifs <;> simp [iidProb, ENNReal.toReal_prod]

end SWCode

namespace SlepianWolf

open SWCode

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [Fintype T] [MeasurableSpace T]
  [DecidableEq S] [DecidableEq T] {n : ℕ}

private lemma sum_pair_mul_mul {A B : Type*} [Fintype A] [Fintype B] (u v : ℝ) (g : A → ℝ)
    (h : B → ℝ) : ∑ f : A × B, (u * v) * (g f.1 * h f.2) = (∑ a, u * g a) * ∑ b, v * h b := by
  rw [Fintype.sum_prod_type, sum_mul_sum]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

private lemma sum_weight_pair {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] {k₁ k₂ : ℕ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    ∑ _f : (A → Fin k₁) × (B → Fin k₂), (∏ _x : A, (k₁ : ℝ)⁻¹) * ∏ _y : B, (k₂ : ℝ)⁻¹ = 1 := by
  rw [Fintype.sum_prod_type]
  refine (sum_congr rfl fun f₁ _ => ?_).trans (sum_uniform hk₁)
  rw [← mul_sum, sum_uniform hk₂, mul_one]

omit [Fintype S] [MeasurableSpace S] [Fintype T] [MeasurableSpace T] in
private lemma mul_le_of_ne {k₁ k₂ : ℕ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (z xy : (Fin n → S) × (Fin n → T)) (hz : z ≠ xy) :
    (if z.1 = xy.1 then 1 else (k₁ : ℝ)⁻¹) * (if z.2 = xy.2 then 1 else (k₂ : ℝ)⁻¹)
      ≤ (if z.2 = xy.2 then (1 : ℝ) else 0) / k₁ + (if z.1 = xy.1 then (1 : ℝ) else 0) / k₂
        + 1 / (k₁ * k₂) := by
  have h1 : (0 : ℝ) ≤ (k₁ : ℝ)⁻¹ := by positivity
  have h2 : (0 : ℝ) ≤ (k₂ : ℝ)⁻¹ := by positivity
  have h12 : (0 : ℝ) ≤ ((k₁ : ℝ) * k₂)⁻¹ := by positivity
  by_cases ha : z.1 = xy.1
  · have hb : z.2 ≠ xy.2 := fun hb => hz (Prod.ext ha hb)
    simp only [ha, hb, ite_true, ite_false, one_mul, zero_div, zero_add, one_div]
    linarith
  · by_cases hb : z.2 = xy.2
    · simp only [ha, hb, ite_true, ite_false, mul_one, zero_div, add_zero, one_div]
      linarith
    · simp only [ha, hb, ite_false, zero_div, zero_add, one_div, mul_inv]
      exact le_rfl

theorem sum_errorProb_binningCode_le (p : PMF (S × T)) (ε : ℝ) (d : (Fin n → S) × (Fin n → T))
    {k₁ k₂ : ℕ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    ∑ f : ((Fin n → S) → Fin k₁) × ((Fin n → T) → Fin k₂),
        ((∏ _x : Fin n → S, (k₁ : ℝ)⁻¹) * ∏ _y : Fin n → T, (k₂ : ℝ)⁻¹) *
          ((binningCode f.1 f.2 (jointlyTypicalSet p n ε) d).errorProb p).toReal
      ≤ (1 - ∑ xy ∈ jointlyTypicalSet p n ε, iidProb p (fun i => (xy.1 i, xy.2 i))) +
        (Real.exp (n * (measureEntropy p.toMeasure - measureEntropy (p.map Prod.snd).toMeasure
            + 2 * ε)) / k₁ +
          Real.exp (n * (measureEntropy p.toMeasure - measureEntropy (p.map Prod.fst).toMeasure
            + 2 * ε)) / k₂ +
          Real.exp (n * (measureEntropy p.toMeasure + ε)) / (k₁ * k₂)) := by
  have huv1 := sum_weight_pair (A := Fin n → S) (B := Fin n → T) hk₁ hk₂
  set J := jointlyTypicalSet p n ε
  set u := ∏ _x : Fin n → S, (k₁ : ℝ)⁻¹
  set v := ∏ _y : Fin n → T, (k₂ : ℝ)⁻¹
  set P : (Fin n → S) × (Fin n → T) → ℝ := fun xy => iidProb p (fun i => (xy.1 i, xy.2 i))
  set A₁ := Real.exp (n * (measureEntropy p.toMeasure - measureEntropy (p.map Prod.snd).toMeasure
    + 2 * ε))
  set A₂ := Real.exp (n * (measureEntropy p.toMeasure - measureEntropy (p.map Prod.fst).toMeasure
    + 2 * ε))
  set A₃ := Real.exp (n * (measureEntropy p.toMeasure + ε))
  set β := A₁ / k₁ + A₂ / k₂ + A₃ / (k₁ * k₂)
  have hk₁' : (0 : ℝ) < k₁ := Nat.cast_pos.2 hk₁
  have hk₂' : (0 : ℝ) < k₂ := Nat.cast_pos.2 hk₂
  have huv : 0 ≤ u * v := by positivity
  have hpt : ∀ xy : (Fin n → S) × (Fin n → T),
      ∑ f : ((Fin n → S) → Fin k₁) × ((Fin n → T) → Fin k₂), (u * v) *
        (if (binningCode f.1 f.2 J d).dec ((binningCode f.1 f.2 J d).enc₁ xy.1,
          (binningCode f.1 f.2 J d).enc₂ xy.2) = xy then (0 : ℝ) else 1)
        ≤ (if xy ∈ J then 0 else 1) + β := by
    intro xy
    have hcoll : ∀ z : (Fin n → S) × (Fin n → T),
        ∑ f : ((Fin n → S) → Fin k₁) × ((Fin n → T) → Fin k₂), (u * v) *
          ((if f.1 z.1 = f.1 xy.1 then (1 : ℝ) else 0) * (if f.2 z.2 = f.2 xy.2 then 1 else 0))
          = (if z.1 = xy.1 then 1 else (k₁ : ℝ)⁻¹) * (if z.2 = xy.2 then 1 else (k₂ : ℝ)⁻¹) := by
      intro z
      exact (sum_pair_mul_mul u v
        (fun f₁ : (Fin n → S) → Fin k₁ => if f₁ z.1 = f₁ xy.1 then (1 : ℝ) else 0)
        (fun f₂ : (Fin n → T) → Fin k₂ => if f₂ z.2 = f₂ xy.2 then (1 : ℝ) else 0)).trans
        (congrArg₂ (· * ·) (sum_uniform_mul_ite_eq hk₁ z.1 xy.1)
          (sum_uniform_mul_ite_eq hk₂ z.2 xy.2))
    calc _ ≤ ∑ f : ((Fin n → S) → Fin k₁) × ((Fin n → T) → Fin k₂), (u * v) *
          ((if xy ∈ J then 0 else 1) + ∑ z ∈ J.erase xy,
            (if f.1 z.1 = f.1 xy.1 then (1 : ℝ) else 0) * (if f.2 z.2 = f.2 xy.2 then 1 else 0)) :=
          sum_le_sum fun f _ => mul_le_mul_of_nonneg_left
            (ite_typicalDecoder_le f.1 f.2 J d xy) huv
      _ = (if xy ∈ J then 0 else 1) + ∑ z ∈ J.erase xy, (if z.1 = xy.1 then 1 else (k₁ : ℝ)⁻¹) *
            (if z.2 = xy.2 then 1 else (k₂ : ℝ)⁻¹) := by
        have e1 : ∑ f : ((Fin n → S) → Fin k₁) × ((Fin n → T) → Fin k₂), (u * v) *
            (if xy ∈ J then (0 : ℝ) else 1) = if xy ∈ J then (0 : ℝ) else 1 := by
          rw [← sum_mul, huv1, one_mul]
        have e2 : ∑ f : ((Fin n → S) → Fin k₁) × ((Fin n → T) → Fin k₂), ∑ z ∈ J.erase xy,
            (u * v) * ((if f.1 z.1 = f.1 xy.1 then (1 : ℝ) else 0) *
              (if f.2 z.2 = f.2 xy.2 then 1 else 0))
            = ∑ z ∈ J.erase xy, (if z.1 = xy.1 then 1 else (k₁ : ℝ)⁻¹) *
              (if z.2 = xy.2 then 1 else (k₂ : ℝ)⁻¹) := by
          rw [sum_comm]
          exact sum_congr rfl fun z _ => hcoll z
        refine Eq.trans ?_ (congrArg₂ (· + ·) e1 e2)
        rw [← sum_add_distrib]
        exact sum_congr rfl fun f _ => by rw [mul_add, mul_sum]
      _ ≤ (if xy ∈ J then 0 else 1) + ∑ z ∈ J,
          ((if z.2 = xy.2 then (1 : ℝ) else 0) / k₁ + (if z.1 = xy.1 then (1 : ℝ) else 0) / k₂
            + 1 / (k₁ * k₂)) := by
        refine add_le_add le_rfl ((sum_le_sum fun z hz =>
          mul_le_of_ne hk₁ hk₂ z xy (ne_of_mem_erase hz)).trans ?_)
        exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun z _ _ => by positivity
      _ ≤ _ := by
        refine add_le_add le_rfl ?_
        rw [sum_add_distrib, sum_add_distrib, ← sum_div, ← sum_div, sum_boole, sum_boole,
          sum_const, nsmul_eq_mul, mul_one_div]
        have c1 := card_filter_snd_jointlyTypicalSet_le p n ε xy.2
        have c2 := card_filter_fst_jointlyTypicalSet_le p n ε xy.1
        have c3 := card_jointlyTypicalSet_le p n ε
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact div_le_div_of_nonneg_right c1 hk₁'.le
        · exact div_le_div_of_nonneg_right c2 hk₂'.le
        · exact div_le_div_of_nonneg_right c3 (by positivity)
  have hP0 : ∀ xy, 0 ≤ P xy := fun xy => iidProb_nonneg _ _
  calc _ = ∑ xy, P xy * ∑ f : ((Fin n → S) → Fin k₁) × ((Fin n → T) → Fin k₂), (u * v) *
        (if (binningCode f.1 f.2 J d).dec ((binningCode f.1 f.2 J d).enc₁ xy.1,
          (binningCode f.1 f.2 J d).enc₂ xy.2) = xy then (0 : ℝ) else 1) := by
        simp_rw [errorProb_toReal, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun xy _ => sum_congr rfl fun f _ => by ring
    _ ≤ ∑ xy, P xy * ((if xy ∈ J then 0 else 1) + β) :=
        sum_le_sum fun xy _ => mul_le_mul_of_nonneg_left (hpt xy) (hP0 xy)
    _ = (1 - ∑ xy ∈ J, P xy) + β := by
      simp_rw [mul_add, sum_add_distrib, ← sum_mul, mul_ite, mul_zero, mul_one]
      rw [sum_ite_mem_zero, sum_iidProb_pair, one_mul]

theorem exists_binningCode_errorProb_le (p : PMF (S × T)) (ε : ℝ)
    (d : (Fin n → S) × (Fin n → T)) {k₁ k₂ : ℕ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    ∃ f₁ : (Fin n → S) → Fin k₁, ∃ f₂ : (Fin n → T) → Fin k₂,
      (binningCode f₁ f₂ (jointlyTypicalSet p n ε) d).errorProb p ≤
        ENNReal.ofReal ((1 - ∑ xy ∈ jointlyTypicalSet p n ε,
            iidProb p (fun i => (xy.1 i, xy.2 i))) +
          (Real.exp (n * (measureEntropy p.toMeasure - measureEntropy (p.map Prod.snd).toMeasure
              + 2 * ε)) / k₁ +
            Real.exp (n * (measureEntropy p.toMeasure - measureEntropy (p.map Prod.fst).toMeasure
              + 2 * ε)) / k₂ +
            Real.exp (n * (measureEntropy p.toMeasure + ε)) / (k₁ * k₂))) := by
  obtain ⟨f, hf⟩ := exists_le_of_sum_mul_le
    (w := fun f : ((Fin n → S) → Fin k₁) × ((Fin n → T) → Fin k₂) =>
      (∏ _x : Fin n → S, (k₁ : ℝ)⁻¹) * ∏ _y : Fin n → T, (k₂ : ℝ)⁻¹)
    (f := fun f => ((binningCode f.1 f.2 (jointlyTypicalSet p n ε) d).errorProb p).toReal)
    (fun f => by positivity) (sum_weight_pair hk₁ hk₂) (sum_errorProb_binningCode_le p ε d hk₁ hk₂)
  exact ⟨f.1, f.2, (ENNReal.le_ofReal_iff_toReal_le (errorProb_ne_top _ p)
    ((ENNReal.toReal_nonneg).trans hf)).2 hf⟩

private lemma inv_floor_exp_le {x : ℝ} (hx : 0 ≤ x) :
    0 < ⌊Real.exp x⌋₊ ∧ ((⌊Real.exp x⌋₊ : ℕ) : ℝ)⁻¹ ≤ 2 * Real.exp (-x) := by
  have he : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hk : 0 < ⌊Real.exp x⌋₊ := Nat.floor_pos.2 he
  have h1 : (1 : ℝ) ≤ ⌊Real.exp x⌋₊ := by exact_mod_cast hk
  have hlt := Nat.lt_floor_add_one (Real.exp x)
  refine ⟨hk, ?_⟩
  calc ((⌊Real.exp x⌋₊ : ℕ) : ℝ)⁻¹ = 2 * (2 * (⌊Real.exp x⌋₊ : ℝ))⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
    _ ≤ 2 * Real.exp (-x) := by
        rw [Real.exp_neg]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (Real.exp_pos x) (by linarith)) two_pos.le

theorem achievable_of_lt [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (p : PMF (S × T)) {R₁ R₂ : ℝ}
    (h₁ : condEntropy (fun ω : S × T => ω.1) (fun ω => ω.2) p.toMeasure < R₁)
    (h₂ : condEntropy (fun ω : S × T => ω.2) (fun ω => ω.1) p.toMeasure < R₂)
    (h₃ : entropy (fun ω : S × T => ω) p.toMeasure < R₁ + R₂) : Achievable p R₁ R₂ := by
  have hR₁ : 0 ≤ R₁ := (condEntropy_nonneg p.toMeasure measurable_fst measurable_snd).trans h₁.le
  have hR₂ : 0 ≤ R₂ := (condEntropy_nonneg p.toMeasure measurable_snd measurable_fst).trans h₂.le
  rw [condEntropy_fst_snd_toMeasure] at h₁
  rw [condEntropy_snd_fst_toMeasure] at h₂
  have hH : entropy (fun ω : S × T => ω) p.toMeasure = measureEntropy p.toMeasure := by
    rw [entropy, Measure.map_id']
  rw [hH] at h₃
  set H := measureEntropy p.toMeasure
  set H₁ := measureEntropy (p.map Prod.fst).toMeasure
  set H₂ := measureEntropy (p.map Prod.snd).toMeasure
  set η := min (min (R₁ - (H - H₂)) (R₂ - (H - H₁))) (R₁ + R₂ - H) / 4 with hη
  have hη0 : 0 < η := by
    rw [hη]
    exact div_pos (lt_min (lt_min (by linarith) (by linarith)) (by linarith)) four_pos
  have hη1 : 4 * η ≤ R₁ - (H - H₂) := by
    rw [hη, mul_div_cancel₀ _ four_ne_zero]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : 4 * η ≤ R₂ - (H - H₁) := by
    rw [hη, mul_div_cancel₀ _ four_ne_zero]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : 4 * η ≤ R₁ + R₂ - H := by
    rw [hη, mul_div_cancel₀ _ four_ne_zero]
    exact min_le_right _ _
  intro ε hε
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  have hJ : Tendsto (fun n : ℕ => 1 - ∑ xy ∈ jointlyTypicalSet p n η,
      iidProb p (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_jointlyTypicalSet p hη0)
  have hsum := ((hJ.add ((tendsto_exp_nat_mul (c := H - H₂ + 2 * η - R₁) (by linarith)).const_mul
    2)).add ((tendsto_exp_nat_mul (c := H - H₁ + 2 * η - R₂) (by linarith)).const_mul 2)).add
    ((tendsto_exp_nat_mul (c := H + η - (R₁ + R₂)) (by linarith)).const_mul 4)
  simp only [mul_zero, add_zero] at hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ))
  obtain ⟨st⟩ : Nonempty (S × T) := ⟨p.support_nonempty.some⟩
  refine ⟨N, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  obtain ⟨hk₁, hinv₁⟩ := inv_floor_exp_le (mul_nonneg hn0 hR₁)
  obtain ⟨hk₂, hinv₂⟩ := inv_floor_exp_le (mul_nonneg hn0 hR₂)
  refine ⟨_, _, Nat.floor_le (Real.exp_pos _).le, Nat.floor_le (Real.exp_pos _).le, ?_⟩
  obtain ⟨f₁, f₂, hf⟩ := exists_binningCode_errorProb_le (n := n) p η
    (fun _ => st.1, fun _ => st.2) hk₁ hk₂
  refine ⟨_, hf.trans ((ENNReal.ofReal_le_ofReal ?_).trans hδε.le)⟩
  set k₁ := ⌊Real.exp (n * R₁)⌋₊
  set k₂ := ⌊Real.exp (n * R₂)⌋₊
  have e1 : Real.exp (n * (H - H₂ + 2 * η)) / k₁ ≤ 2 * Real.exp (n * (H - H₂ + 2 * η - R₁)) :=
    calc _ = Real.exp (n * (H - H₂ + 2 * η)) * (k₁ : ℝ)⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp (n * (H - H₂ + 2 * η)) * (2 * Real.exp (-(n * R₁))) :=
          mul_le_mul_of_nonneg_left hinv₁ (Real.exp_pos _).le
      _ = _ := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have e2 : Real.exp (n * (H - H₁ + 2 * η)) / k₂ ≤ 2 * Real.exp (n * (H - H₁ + 2 * η - R₂)) :=
    calc _ = Real.exp (n * (H - H₁ + 2 * η)) * (k₂ : ℝ)⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp (n * (H - H₁ + 2 * η)) * (2 * Real.exp (-(n * R₂))) :=
          mul_le_mul_of_nonneg_left hinv₂ (Real.exp_pos _).le
      _ = _ := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have e3 : Real.exp (n * (H + η)) / (k₁ * k₂) ≤ 4 * Real.exp (n * (H + η - (R₁ + R₂))) :=
    calc _ = Real.exp (n * (H + η)) * ((k₁ : ℝ)⁻¹ * (k₂ : ℝ)⁻¹) := by rw [div_eq_mul_inv, mul_inv]
      _ ≤ Real.exp (n * (H + η)) * ((2 * Real.exp (-(n * R₁))) * (2 * Real.exp (-(n * R₂)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hinv₁ hinv₂ (by positivity) (by positivity))
            (Real.exp_pos _).le
      _ = _ := by
          rw [show Real.exp (n * (H + η)) * ((2 * Real.exp (-(n * R₁))) *
              (2 * Real.exp (-(n * R₂)))) = 4 * (Real.exp (n * (H + η)) *
                Real.exp (-(n * R₁)) * Real.exp (-(n * R₂))) by ring,
            ← Real.exp_add, ← Real.exp_add]
          congr 2
          ring
  linarith [hN n hn]

end SlepianWolf

end Meat
