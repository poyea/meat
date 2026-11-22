import Meat.Shannon.Covering
import Meat.Shannon.LargeNumbers
import Meat.Shannon.TypicalIntersection
import Meat.Source.RateDistortion

open MeasureTheory Finset Filter Topology

namespace Meat

namespace RateDistortion

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

noncomputable def distortionTypicalSet (q : PMF (S × T)) (d : S → T → ℝ) (n : ℕ) (ε : ℝ) :
    Finset ((Fin n → S) × (Fin n → T)) := by
  classical
  exact {xy ∈ jointlyTypicalSet q n ε |
    ∑ i, d (xy.1 i) (xy.2 i) ≤ n * (∑ z, (q z).toReal * d z.1 z.2 + ε)}

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem distortionTypicalSet_subset (q : PMF (S × T)) (d : S → T → ℝ) (n : ℕ) (ε : ℝ) :
    distortionTypicalSet q d n ε ⊆ jointlyTypicalSet q n ε := by
  classical
  unfold distortionTypicalSet
  convert filter_subset _ _

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem sum_le_of_mem_distortionTypicalSet {q : PMF (S × T)} {d : S → T → ℝ} {n : ℕ} {ε : ℝ}
    {xy : (Fin n → S) × (Fin n → T)} (h : xy ∈ distortionTypicalSet q d n ε) :
    ∑ i, d (xy.1 i) (xy.2 i) ≤ n * (∑ z, (q z).toReal * d z.1 z.2 + ε) := by
  simp only [distortionTypicalSet, mem_filter] at h
  exact h.2

theorem tendsto_sum_iidProb_distortionTypicalSet (q : PMF (S × T)) (d : S → T → ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun n => ∑ xy ∈ distortionTypicalSet q d n ε, iidProb q (fun i => (xy.1 i, xy.2 i)))
      atTop (𝓝 1) := by
  classical
  set m := ∑ z, (q z).toReal * d z.1 z.2
  have ht : Tendsto (fun n : ℕ => ∑ xy : (Fin n → S) × (Fin n → T) with
      ∑ i, d (xy.1 i) (xy.2 i) ≤ n * (m + ε), iidProb q (fun i => (xy.1 i, xy.2 i)))
      atTop (𝓝 1) := by
    refine (tendsto_sum_iidProb_sum_le q (fun z => d z.1 z.2) hε).congr fun n => ?_
    rw [sum_filter, sum_filter]
    exact (Equiv.sum_comp (Equiv.arrowProdEquivProdArrow _ _ _).symm (fun z =>
      if ∑ i, d (z i).1 (z i).2 ≤ n * (m + ε) then iidProb q z else 0)).symm
  refine tendsto_sum_of_mem_iff_and (fun n xy => iidProb_nonneg _ _)
    (fun n => (sum_iidProb_pair q n).le) (fun n xy => ?_)
    (tendsto_sum_iidProb_jointlyTypicalSet q hε) ht
  refine ⟨fun h => ⟨distortionTypicalSet_subset q d n ε h, mem_filter.2 ⟨mem_univ _,
    sum_le_of_mem_distortionTypicalSet h⟩⟩, fun h => ?_⟩
  simp only [distortionTypicalSet, mem_filter]
  exact ⟨h.1, (mem_filter.1 h.2).2⟩

variable {n k : ℕ}

noncomputable def coveringEncoder (C : Fin k → Fin n → T) (J : Finset ((Fin n → S) × (Fin n → T)))
    (m₀ : Fin k) (x : Fin n → S) : Fin k := by
  classical
  exact if h : ∃ m, (x, C m) ∈ J then h.choose else m₀

noncomputable def coveringCode (C : Fin k → Fin n → T) (J : Finset ((Fin n → S) × (Fin n → T)))
    (m₀ : Fin k) : LossyCode S T n k :=
  ⟨coveringEncoder C J m₀, C⟩

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype T] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
theorem coveringEncoder_mem {C : Fin k → Fin n → T} {J : Finset ((Fin n → S) × (Fin n → T))}
    (m₀ : Fin k) {x : Fin n → S} (h : ∃ m, (x, C m) ∈ J) :
    (x, C (coveringEncoder C J m₀ x)) ∈ J := by
  simp only [coveringEncoder, h, dite_true]
  exact h.choose_spec

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
theorem expDist_eq_sum_jointPMF (p : PMF S) (d : S → T → ℝ) (W : DMC S T) :
    ∑ z, (DMC.jointPMF W p z).toReal * d z.1 z.2 = expDist p d W := by
  rw [Fintype.sum_prod_type, expDist]
  simp [DMC.jointPMF_apply, ENNReal.toReal_mul]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
theorem blockDist_le_sum {d : S → T → ℝ} (hd : ∀ s t, 0 ≤ d s t) (hn : 0 < n) (x : Fin n → S)
    (y : Fin n → T) : blockDist d x y ≤ ∑ s, ∑ t, d s t := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1 : ∀ s t, d s t ≤ ∑ s, ∑ t, d s t := fun s t =>
    (single_le_sum (fun t _ => hd s t) (mem_univ t)).trans
      (single_le_sum (f := fun s => ∑ t, d s t) (fun s _ => sum_nonneg fun t _ => hd s t)
        (mem_univ s))
  rw [blockDist, div_le_iff₀ hn']
  calc ∑ i, d (x i) (y i) ≤ ∑ _i : Fin n, ∑ s, ∑ t, d s t := sum_le_sum fun i _ => h1 _ _
    _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

theorem exists_coveringCode_distortion_le (p : PMF S) {d : S → T → ℝ} (hd : ∀ s t, 0 ≤ d s t)
    (W : DMC S T) (hn : 0 < n) (hk : 0 < k) {η : ℝ} (hη : 0 < η) :
    ∃ c : LossyCode S T n k, c.distortion p d ≤ expDist p d W + η + (∑ s, ∑ t, d s t) *
      ((1 - ∑ xy ∈ distortionTypicalSet (DMC.jointPMF W p) d n η,
          iidProb (DMC.jointPMF W p) (fun i => (xy.1 i, xy.2 i))) +
        Real.exp (-(k * Real.exp (-(n * (W.inputMutualInfo p + 3 * η)))))) := by
  classical
  set q := DMC.jointPMF W p
  set J := distortionTypicalSet q d n η
  set E := expDist p d W
  set M := ∑ s, ∑ t, d s t
  set q₂ := q.map Prod.snd
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hM0 : 0 ≤ M := sum_nonneg fun s _ => sum_nonneg fun t _ => hd s t
  have hE0 : 0 ≤ E := sum_nonneg fun s _ => sum_nonneg fun t _ =>
    mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (hd s t)
  have hJd : ∀ xy ∈ J, blockDist d xy.1 xy.2 ≤ E + η := fun xy h => by
    have h' := sum_le_of_mem_distortionTypicalSet h
    rw [expDist_eq_sum_jointPMF] at h'
    rw [blockDist, div_le_iff₀ hn']
    linarith
  set m₀ : Fin k := ⟨0, hk⟩
  set g : (Fin n → S) → (Fin n → T) → ℝ := fun x y => if (x, y) ∈ J then 0 else 1
  have hg0 : ∀ x y, 0 ≤ g x y := fun x y => by
    simp only [g]
    split_ifs <;> norm_num
  have hpt : ∀ (C : Fin k → Fin n → T) (x : Fin n → S),
      blockDist d x ((coveringCode C J m₀).dec ((coveringCode C J m₀).enc x))
        ≤ E + η + M * ∏ m, g x (C m) := by
    intro C x
    change blockDist d x (C (coveringEncoder C J m₀ x)) ≤ _
    by_cases hex : ∃ m, (x, C m) ∈ J
    · have h1 := hJd _ (coveringEncoder_mem m₀ hex)
      have h2 : 0 ≤ M * ∏ m, g x (C m) := mul_nonneg hM0 (prod_nonneg fun m _ => hg0 _ _)
      linarith
    · have hg : ∏ m, g x (C m) = 1 := prod_eq_one fun m _ => by
        simp only [g]
        rw [ite_eq_right_iff.2 fun h => absurd ⟨m, h⟩ hex]
      rw [hg, mul_one]
      linarith [blockDist_le_sum hd hn x (C (coveringEncoder C J m₀ x))]
  have hrow : ∀ x : Fin n → S, ∑ y, iidProb q₂ y * g x y
      = 1 - ∑ y : Fin n → T with (x, y) ∈ J, iidProb q₂ y := fun x => by
    rw [← sum_iidProb q₂ n, sum_filter, ← sum_sub_distrib]
    refine sum_congr rfl fun y _ => ?_
    simp only [g]
    split_ifs <;> simp
  have hw : ∀ C : Fin k → Fin n → T, 0 ≤ ∏ m, iidProb q₂ (C m) :=
    fun C => prod_nonneg fun m _ => iidProb_nonneg _ _
  have hw1 : ∑ C : Fin k → Fin n → T, ∏ m, iidProb q₂ (C m) = 1 :=
    sum_prod _ fun _ => sum_iidProb q₂ n
  have hinner : ∀ x : Fin n → S, ∑ C : Fin k → Fin n → T, (∏ m, iidProb q₂ (C m)) *
      (E + η + M * ∏ m, g x (C m))
        = E + η + M * (1 - ∑ y : Fin n → T with (x, y) ∈ J, iidProb q₂ y) ^ k := fun x => by
    have h := sum_prod_mul_prod (fun (_ : Fin k) y => iidProb q₂ y) fun _ y => g x y
    simp only [hrow, prod_const, card_univ, Fintype.card_fin] at h
    have e : ∀ C : Fin k → Fin n → T, (∏ m, iidProb q₂ (C m)) * (E + η + M * ∏ m, g x (C m))
        = (E + η) * ∏ m, iidProb q₂ (C m) + M * ((∏ m, iidProb q₂ (C m)) * ∏ m, g x (C m)) :=
      fun C => by ring
    rw [sum_congr rfl fun C _ => e C, sum_add_distrib, ← mul_sum, ← mul_sum, hw1, h, mul_one]
  have havg : ∑ C : Fin k → Fin n → T, (∏ m, iidProb q₂ (C m)) *
      (coveringCode C J m₀).distortion p d
        ≤ E + η + M * ∑ x, iidProb p x *
          (1 - ∑ y : Fin n → T with (x, y) ∈ J, iidProb q₂ y) ^ k := by
    calc _ ≤ ∑ C : Fin k → Fin n → T, (∏ m, iidProb q₂ (C m)) *
          ∑ x, iidProb p x * (E + η + M * ∏ m, g x (C m)) :=
          sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (hpt C x) (iidProb_nonneg p x)) (hw C)
      _ = ∑ x, iidProb p x * ∑ C : Fin k → Fin n → T, (∏ m, iidProb q₂ (C m)) *
          (E + η + M * ∏ m, g x (C m)) := by
          simp only [mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun x _ => sum_congr rfl fun C _ => by ring
      _ = _ := by
          rw [sum_congr rfl fun x _ => by rw [hinner x]]
          have e : ∀ x : Fin n → S, iidProb p x *
              (E + η + M * (1 - ∑ y : Fin n → T with (x, y) ∈ J, iidProb q₂ y) ^ k)
              = (E + η) * iidProb p x +
                M * (iidProb p x * (1 - ∑ y : Fin n → T with (x, y) ∈ J, iidProb q₂ y) ^ k) :=
            fun x => by ring
          rw [sum_congr rfl fun x _ => e x, sum_add_distrib, ← mul_sum, ← mul_sum, sum_iidProb,
            mul_one]
  have hcov := sum_iidProb_mul_one_sub_pow_le q hη.le (distortionTypicalSet_subset q d n η) k
  rw [DMC.jointPMF_map_fst] at hcov
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le hw hw1
    (havg.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcov hM0)))
  exact ⟨coveringCode C J m₀, hC⟩

theorem achievable_of_lt (p : PMF S) {d : S → T → ℝ} (hd : ∀ s t, 0 ≤ d s t) (W : DMC S T)
    {R : ℝ} (h : W.inputMutualInfo p < R) : Achievable p d R (expDist p d W) := by
  intro ε hε
  set I := W.inputMutualInfo p
  set M := ∑ s, ∑ t, d s t
  set q := DMC.jointPMF W p
  have hI0 : 0 ≤ I := DMC.inputMutualInfo_nonneg W p
  set η := min (ε / 2) ((R - I) / 4) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hηε : η ≤ ε / 2 := min_le_left _ _
  have hηR : η ≤ (R - I) / 4 := min_le_right _ _
  set c := R - I - 3 * η
  have hc : 0 < c := by linarith
  have hJ : Tendsto (fun n : ℕ => 1 - ∑ xy ∈ distortionTypicalSet q d n η,
      iidProb q (fun i => (xy.1 i, xy.2 i))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_distortionTypicalSet q d hη0)
  have hka : ∀ n : ℕ, n * c / 2 ≤
      (⌊Real.exp (n * R)⌋₊ : ℝ) * Real.exp (-(n * (I + 3 * η))) := fun n => by
    have hR0 : 0 ≤ n * R := mul_nonneg (Nat.cast_nonneg n) (by linarith)
    have h1 : Real.exp (n * R) / 2 ≤ ⌊Real.exp (n * R)⌋₊ := by
      have hlt := Nat.lt_floor_add_one (Real.exp (n * R))
      have hge : (1 : ℝ) ≤ ⌊Real.exp (n * R)⌋₊ :=
        Nat.one_le_cast.2 (Nat.le_floor (by simpa using Real.one_le_exp hR0))
      linarith
    have h2 : Real.exp (n * R) * Real.exp (-(n * (I + 3 * η))) = Real.exp (n * c) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : n * c ≤ Real.exp (n * c) := by linarith [Real.add_one_le_exp (n * c)]
    calc n * c / 2 ≤ Real.exp (n * R) / 2 * Real.exp (-(n * (I + 3 * η))) := by
          rw [div_mul_eq_mul_div, h2]
          linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hX : Tendsto (fun n : ℕ =>
      Real.exp (-((⌊Real.exp (n * R)⌋₊ : ℝ) * Real.exp (-(n * (I + 3 * η)))))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_exp_nat_mul (show -(c / 2) < 0 by linarith)) (fun n => (Real.exp_pos _).le)
      fun n => Real.exp_le_exp.2 ?_
    have := hka n
    linarith
  have hsum := (hJ.add hX).const_mul M
  rw [add_zero, mul_zero] at hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hsum.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))).and
      (eventually_gt_atTop 0))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hlt, hn0⟩ := hN n hn
  set k := ⌊Real.exp (n * R)⌋₊
  have hR0 : 0 ≤ n * R := mul_nonneg (Nat.cast_nonneg n) (by linarith)
  have hk : 0 < k := Nat.floor_pos.2 (by simpa using Real.one_le_exp hR0)
  refine ⟨k, Nat.floor_le (Real.exp_pos _).le, ?_⟩
  obtain ⟨C, hC⟩ := exists_coveringCode_distortion_le p hd W hn0 hk hη0
  exact ⟨C, hC.trans (by linarith)⟩

end RateDistortion

end Meat
