import Meat.Source.RateDistortionAchievability
import Meat.Source.RateDistortionConverse

open Filter Topology

namespace Meat

namespace RateDistortion

variable {S T : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype T] [MeasurableSpace T]
  [MeasurableSingletonClass T] in
theorem Achievable.mono {p : PMF S} {d : S → T → ℝ} {R R' D D' : ℝ} (h : Achievable p d R D)
    (hR : R ≤ R') (hD : D ≤ D') : Achievable p d R' D' := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hn
  exact ⟨k, hk.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg n))),
    c, hc.trans (by linarith)⟩

theorem achievable_of_rdf_lt [Nonempty T] {p : PMF S} {d : S → T → ℝ} (hd : ∀ s t, 0 ≤ d s t)
    {R D : ℝ} (hD : minDist p d ≤ D) (h : rdf p d D < R) : Achievable p d R D := by
  obtain ⟨W, hW, hI⟩ := exists_rdf_eq p d hD
  exact (achievable_of_lt p hd W (hI ▸ h)).mono le_rfl hW

omit [Fintype T] in
theorem not_achievable_of_lt_minDist [Finite T] [Nonempty T] {p : PMF S} {d : S → T → ℝ}
    {R D : ℝ} (hD : D < minDist p d) : ¬Achievable p d R D := by
  have := Fintype.ofFinite T
  exact fun h => absurd (mem_rateRegion_of_achievable h).1 (not_le.2 hD)

theorem closure_achievableRegion_eq [Nonempty T] (p : PMF S) {d : S → T → ℝ}
    (hd : ∀ s t, 0 ≤ d s t) : closure (achievableRegion p d) = rateRegion p d := by
  refine subset_antisymm (closure_minimal (fun RD h => mem_rateRegion_of_achievable h)
    (isClosed_rateRegion p d)) fun RD hRD => ?_
  have ht : Tendsto (fun δ : ℝ => (RD.1 + δ, RD.2)) (𝓝[>] 0) (𝓝 RD) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : Continuous fun δ : ℝ => (RD.1 + δ, RD.2) :=
      (continuous_const.add continuous_id).prodMk continuous_const
    simpa using hc.tendsto 0
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ (hδ : 0 < δ) => ?_)
  exact achievable_of_rdf_lt hd hRD.1 (by linarith [hRD.2])

theorem sInf_achievable_eq [Nonempty T] (p : PMF S) {d : S → T → ℝ} (hd : ∀ s t, 0 ≤ d s t)
    {D : ℝ} (hD : minDist p d ≤ D) : sInf {R | Achievable p d R D} = rdf p d D := by
  have hlow : ∀ R ∈ {R | Achievable p d R D}, rdf p d D ≤ R :=
    fun R h => (mem_rateRegion_of_achievable h).2
  refine le_antisymm (le_of_forall_pos_lt_add fun δ hδ => ?_)
    (le_csInf ⟨rdf p d D + 1, achievable_of_rdf_lt hd hD (by linarith)⟩ hlow)
  calc sInf {R | Achievable p d R D} ≤ rdf p d D + δ / 2 :=
        csInf_le ⟨_, hlow⟩ (achievable_of_rdf_lt hd hD (by linarith))
    _ < rdf p d D + δ := by linarith

end RateDistortion

end Meat
