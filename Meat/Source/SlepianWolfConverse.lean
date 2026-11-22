import Meat.Shannon.Fano
import Meat.Shannon.Iid
import Meat.Source.SlepianWolf

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

namespace SlepianWolf

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
private lemma sum_prod_pmf (p : PMF (S × T)) (n : ℕ) :
    ∑ xy : (Fin n → S) × (Fin n → T), ∏ i, p (xy.1 i, xy.2 i) = 1 := by
  classical
  have h : ∑ xy : (Fin n → S) × (Fin n → T), ∏ i, p (xy.1 i, xy.2 i)
      = ∑ z : Fin n → S × T, ∏ i, p (z i) :=
    Equiv.sum_comp (Equiv.arrowProdEquivProdArrow _ _ _).symm fun z => ∏ i, p (z i)
  rw [h, ← Fintype.prod_sum, sum_pmf_eq_one, prod_const_one]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
noncomputable def seqMeasure (p : PMF (S × T)) (n : ℕ) : Measure ((Fin n → S) × (Fin n → T)) :=
  (PMF.ofFintype _ (sum_prod_pmf p n)).toMeasure

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
instance isProbabilityMeasure_seqMeasure (p : PMF (S × T)) (n : ℕ) :
    IsProbabilityMeasure (seqMeasure p n) := by
  unfold seqMeasure
  infer_instance

theorem seqMeasure_real_singleton (p : PMF (S × T)) {n : ℕ} (xy : (Fin n → S) × (Fin n → T)) :
    (seqMeasure p n).real {xy} = iidProb p (fun i => (xy.1 i, xy.2 i)) := by
  rw [measureReal_def, seqMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.ofFintype_apply, ENNReal.toReal_prod]
  rfl

theorem entropy_seqMeasure (p : PMF (S × T)) (n : ℕ) :
    H[fun ω => ω ; seqMeasure p n] = n * measureEntropy p.toMeasure := by
  rw [entropy_def, ← sum_negMulLog_iidProb p n]
  simp_rw [Measure.map_id', seqMeasure_real_singleton]
  exact Equiv.sum_comp (Equiv.arrowProdEquivProdArrow _ _ _).symm
    fun z => Real.negMulLog (iidProb p z)

theorem entropy_fst_seqMeasure (p : PMF (S × T)) (n : ℕ) :
    H[fun ω => ω.1 ; seqMeasure p n] = n * measureEntropy (p.map Prod.fst).toMeasure := by
  classical
  rw [entropy_def, ← sum_negMulLog_iidProb _ n]
  refine sum_congr rfl fun x _ => congrArg Real.negMulLog ?_
  rw [measureReal_map_singleton, ← sum_iidProb_pair_right p x, sum_filter, Fintype.sum_prod_type]
  simp [seqMeasure_real_singleton]

theorem entropy_snd_seqMeasure (p : PMF (S × T)) (n : ℕ) :
    H[fun ω => ω.2 ; seqMeasure p n] = n * measureEntropy (p.map Prod.snd).toMeasure := by
  classical
  rw [entropy_def, ← sum_negMulLog_iidProb _ n]
  refine sum_congr rfl fun y _ => congrArg Real.negMulLog ?_
  rw [measureReal_map_singleton, ← sum_iidProb_pair_left p y, sum_filter,
    Fintype.sum_prod_type_right]
  simp [seqMeasure_real_singleton]

variable {M₁ M₂ : Type*} [Fintype M₁] [MeasurableSpace M₁] [MeasurableSingletonClass M₁]
  [Fintype M₂] [MeasurableSpace M₂] [MeasurableSingletonClass M₂]
  [DecidableEq S] [DecidableEq T] {n : ℕ}

omit [Fintype M₁] [MeasurableSpace M₁] [MeasurableSingletonClass M₁] [Fintype M₂]
  [MeasurableSpace M₂] [MeasurableSingletonClass M₂] in
theorem measureReal_dec_ne (c : SWCode M₁ M₂ S T n) (p : PMF (S × T)) :
    (seqMeasure p n).real {ω | c.dec (c.enc₁ ω.1, c.enc₂ ω.2) ≠ ω} = (c.errorProb p).toReal := by
  rw [measureReal_def, seqMeasure, PMF.toMeasure_apply_fintype, SWCode.errorProb]
  refine congrArg ENNReal.toReal (sum_congr rfl fun xy _ => ?_)
  by_cases h : c.dec (c.enc₁ xy.1, c.enc₂ xy.2) = xy <;> simp [Set.indicator, h]

theorem condEntropy_seqMeasure_le (c : SWCode M₁ M₂ S T n) (p : PMF (S × T)) :
    H[fun ω => ω | fun ω => (c.enc₁ ω.1, c.enc₂ ω.2) ; seqMeasure p n]
      ≤ Real.log 2 + (c.errorProb p).toReal *
        (n * (Real.log (Fintype.card S) + Real.log (Fintype.card T))) := by
  obtain ⟨st⟩ : Nonempty (S × T) := ⟨p.support_nonempty.some⟩
  have h := condEntropy_le_log_two_add_mul_log_card (μ := seqMeasure p n)
    (X := fun ω : (Fin n → S) × (Fin n → T) => ω) (Y := fun ω => (c.enc₁ ω.1, c.enc₂ ω.2))
    measurable_id (measurable_of_finite _) c.dec
  rw [measureReal_dec_ne] at h
  have hS : (0 : ℝ) < Fintype.card S := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨st.1⟩)
  have hT : (0 : ℝ) < Fintype.card T := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨st.2⟩)
  have hcard : Real.log (Fintype.card ((Fin n → S) × (Fin n → T)))
      = n * (Real.log (Fintype.card S) + Real.log (Fintype.card T)) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_pow, Real.log_mul (pow_ne_zero _ hS.ne') (pow_ne_zero _ hT.ne'),
      Real.log_pow, Real.log_pow]
    ring
  rwa [hcard] at h

omit [DecidableEq S] [DecidableEq T] in
private lemma entropy_eq_add (c : SWCode M₁ M₂ S T n) (p : PMF (S × T)) :
    H[fun ω => ω ; seqMeasure p n]
      = H[fun ω => (c.enc₁ ω.1, c.enc₂ ω.2) ; seqMeasure p n]
        + H[fun ω => ω | fun ω => (c.enc₁ ω.1, c.enc₂ ω.2) ; seqMeasure p n] := by
  have h := entropy_pair_comp (seqMeasure p n) (X := fun ω : (Fin n → S) × (Fin n → T) => ω)
    fun ω => (c.enc₁ ω.1, c.enc₂ ω.2)
  rw [condEntropy_def, h]
  ring

omit [Fintype M₂] in
theorem mul_condEntropy_fst_snd_le [Finite M₂] (c : SWCode M₁ M₂ S T n) (p : PMF (S × T)) :
    n * condEntropy (fun ω : S × T => ω.1) (fun ω => ω.2) p.toMeasure
      ≤ Real.log (Fintype.card M₁) + Real.log 2 + (c.errorProb p).toReal *
        (n * (Real.log (Fintype.card S) + Real.log (Fintype.card T))) := by
  have := Fintype.ofFinite M₂
  set μ := seqMeasure p n
  have h1 := entropy_eq_add c p
  have h2 := entropy_pair_le_add μ (X := fun ω : (Fin n → S) × (Fin n → T) => c.enc₁ ω.1)
    (Y := fun ω => c.enc₂ ω.2) (measurable_of_finite _) (measurable_of_finite _)
  have h3 := entropy_le_log_card μ (X := fun ω : (Fin n → S) × (Fin n → T) => c.enc₁ ω.1)
  have h4 : H[fun ω : (Fin n → S) × (Fin n → T) => c.enc₂ ω.2 ; μ] ≤ H[fun ω => ω.2 ; μ] :=
    entropy_comp_le μ (X := fun ω : (Fin n → S) × (Fin n → T) => ω.2) measurable_snd c.enc₂
  have h5 := condEntropy_seqMeasure_le c p
  rw [condEntropy_fst_snd_toMeasure, mul_sub, ← entropy_seqMeasure, ← entropy_snd_seqMeasure]
  linarith

omit [Fintype M₁] in
theorem mul_condEntropy_snd_fst_le [Finite M₁] (c : SWCode M₁ M₂ S T n) (p : PMF (S × T)) :
    n * condEntropy (fun ω : S × T => ω.2) (fun ω => ω.1) p.toMeasure
      ≤ Real.log (Fintype.card M₂) + Real.log 2 + (c.errorProb p).toReal *
        (n * (Real.log (Fintype.card S) + Real.log (Fintype.card T))) := by
  have := Fintype.ofFinite M₁
  set μ := seqMeasure p n
  have h1 := entropy_eq_add c p
  have h2 := entropy_pair_le_add μ (X := fun ω : (Fin n → S) × (Fin n → T) => c.enc₁ ω.1)
    (Y := fun ω => c.enc₂ ω.2) (measurable_of_finite _) (measurable_of_finite _)
  have h3 := entropy_le_log_card μ (X := fun ω : (Fin n → S) × (Fin n → T) => c.enc₂ ω.2)
  have h4 : H[fun ω : (Fin n → S) × (Fin n → T) => c.enc₁ ω.1 ; μ] ≤ H[fun ω => ω.1 ; μ] :=
    entropy_comp_le μ (X := fun ω : (Fin n → S) × (Fin n → T) => ω.1) measurable_fst c.enc₁
  have h5 := condEntropy_seqMeasure_le c p
  rw [condEntropy_snd_fst_toMeasure, mul_sub, ← entropy_seqMeasure, ← entropy_fst_seqMeasure]
  linarith

theorem mul_entropy_le (c : SWCode M₁ M₂ S T n) (p : PMF (S × T)) :
    n * entropy (fun ω : S × T => ω) p.toMeasure
      ≤ Real.log (Fintype.card M₁) + Real.log (Fintype.card M₂) + Real.log 2 +
        (c.errorProb p).toReal *
          (n * (Real.log (Fintype.card S) + Real.log (Fintype.card T))) := by
  set μ := seqMeasure p n
  have h1 := entropy_eq_add c p
  have h2 := entropy_pair_le_add μ (X := fun ω : (Fin n → S) × (Fin n → T) => c.enc₁ ω.1)
    (Y := fun ω => c.enc₂ ω.2) (measurable_of_finite _) (measurable_of_finite _)
  have h3 := entropy_le_log_card μ (X := fun ω : (Fin n → S) × (Fin n → T) => c.enc₁ ω.1)
  have h4 := entropy_le_log_card μ (X := fun ω : (Fin n → S) × (Fin n → T) => c.enc₂ ω.2)
  have h5 := condEntropy_seqMeasure_le c p
  have hH : entropy (fun ω : S × T => ω) p.toMeasure = measureEntropy p.toMeasure := by
    rw [entropy, Measure.map_id']
  rw [hH, ← entropy_seqMeasure]
  linarith

omit [Fintype M₁] [MeasurableSpace M₁] [MeasurableSingletonClass M₁] [Fintype M₂]
  [MeasurableSpace M₂] [MeasurableSingletonClass M₂] in
theorem mem_rateRegion_of_achievable (p : PMF (S × T)) {R₁ R₂ : ℝ} (h : Achievable p R₁ R₂) :
    (R₁, R₂) ∈ rateRegion p := by
  obtain ⟨st⟩ : Nonempty (S × T) := ⟨p.support_nonempty.some⟩
  set L := Real.log (Fintype.card S) + Real.log (Fintype.card T)
  have hL : 0 ≤ L := add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have key : ∀ δ : ℝ, 0 < δ →
      condEntropy (fun ω : S × T => ω.1) (fun ω => ω.2) p.toMeasure ≤ R₁ + δ ∧
      condEntropy (fun ω : S × T => ω.2) (fun ω => ω.1) p.toMeasure ≤ R₂ + δ ∧
      entropy (fun ω : S × T => ω) p.toMeasure ≤ R₁ + R₂ + δ := by
    intro δ hδ
    set e := δ / (2 * (L + 1)) with he
    have he0 : 0 < e := by positivity
    have heL1 : e * (L + 1) = δ / 2 := by
      rw [he]
      field_simp
    have heL : e * L ≤ δ / 2 := by
      rw [mul_add, mul_one] at heL1
      linarith
    obtain ⟨N, hN⟩ := h (ENNReal.ofReal e) (ENNReal.ofReal_pos.2 he0)
    obtain ⟨n0, hn0⟩ := exists_nat_gt (2 * Real.log 2 / δ)
    obtain ⟨n, hNn, hn0n⟩ : ∃ n : ℕ, N ≤ n ∧ n0 ≤ n :=
      ⟨max N n0, le_max_left _ _, le_max_right _ _⟩
    obtain ⟨k₁, k₂, hk₁, hk₂, c, hc⟩ := hN n hNn
    have hn : 2 * Real.log 2 < n * δ := by
      rw [← div_lt_iff₀ hδ]
      exact hn0.trans_le (by exact_mod_cast hn0n)
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hnpos : (0 : ℝ) < n := lt_of_not_ge fun h0 => by nlinarith
    have hPe : (c.errorProb p).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
    have hk₁0 : (0 : ℝ) < k₁ := Nat.cast_pos.2 (Fin.pos (c.enc₁ fun _ => st.1))
    have hk₂0 : (0 : ℝ) < k₂ := Nat.cast_pos.2 (Fin.pos (c.enc₂ fun _ => st.2))
    have hl₁ : Real.log k₁ ≤ n * R₁ := (Real.log_le_iff_le_exp hk₁0).2 hk₁
    have hl₂ : Real.log k₂ ≤ n * R₂ := (Real.log_le_iff_le_exp hk₂0).2 hk₂
    have hF : (c.errorProb p).toReal * (n * L) ≤ n * (δ / 2) :=
      calc _ ≤ e * (n * L) := mul_le_mul_of_nonneg_right hPe (by positivity)
        _ = n * (e * L) := by ring
        _ ≤ n * (δ / 2) := mul_le_mul_of_nonneg_left heL hnpos.le
    have b1 := mul_condEntropy_fst_snd_le c p
    have b2 := mul_condEntropy_snd_fst_le c p
    have b3 := mul_entropy_le c p
    simp only [Fintype.card_fin] at b1 b2 b3
    refine ⟨le_of_mul_le_mul_left ?_ hnpos, le_of_mul_le_mul_left ?_ hnpos,
      le_of_mul_le_mul_left ?_ hnpos⟩ <;> nlinarith
  exact ⟨le_of_forall_pos_le_add fun δ hδ => (key δ hδ).1,
    le_of_forall_pos_le_add fun δ hδ => (key δ hδ).2.1,
    le_of_forall_pos_le_add fun δ hδ => (key δ hδ).2.2⟩

end SlepianWolf

end Meat
