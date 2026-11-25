import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Meat.Continuous.ParallelGaussian

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Meat

namespace MIMO

private theorem pi_pi_swap {κ : Type*} [Fintype κ] {n : ℕ} (μ : κ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi fun _ : Fin n => Measure.pi fun i : κ => μ i).map (fun w i t => w t i) =
      Measure.pi fun i : κ => Measure.pi fun _ : Fin n => μ i := by
  have hm : Measurable fun (w : Fin n → κ → ℝ) (i : κ) (t : Fin n) => w t i := by fun_prop
  refine (Measure.pi_eq_generateFrom (μ := fun i => Measure.pi fun _ : Fin n => μ i)
    (C := fun _ : κ => Set.univ.pi '' Set.univ.pi
    fun _ : Fin n => {s : Set ℝ | MeasurableSet s})
    (fun _ => generateFrom_pi (ι := Fin n) (α := fun _ => ℝ))
    (fun _ => isPiSystem_pi (ι := Fin n) (α := fun _ => ℝ))
    (fun i => ⟨fun _ => Set.univ, fun _ => ⟨fun _ => Set.univ,
      fun _ _ => (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ)),
      Set.pi_univ _⟩, fun _ => measure_lt_top _ _, Set.iUnion_const _⟩) fun s hs => ?_).symm
  choose A hA hAs using hs
  have hpre : (fun (w : Fin n → κ → ℝ) (i : κ) (t : Fin n) => w t i) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun t => Set.univ.pi fun i => A i t := by
    ext w
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, ← hAs]
    exact forall_comm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi fun i => by
    rw [← hAs i]; exact MeasurableSet.univ_pi fun t => hA i t (Set.mem_univ t)), hpre,
    Measure.pi_pi]
  simp_rw [Measure.pi_pi, ← hAs, Measure.pi_pi]
  exact prod_comm

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

structure SVD (H : E →ₗ[ℝ] F) (ι κ : Type*) [Fintype ι] [Fintype κ] where
  v : OrthonormalBasis ι ℝ E
  u : OrthonormalBasis κ ℝ F
  σ : ι → ℝ
  e : ι → κ
  σ_nonneg : ∀ j, 0 ≤ σ j
  injOn : ∀ j j', 0 < σ j → 0 < σ j' → e j = e j' → j = j'
  apply_v : ∀ j, H (v j) = σ j • u (e j)

namespace SVD

variable {H : E →ₗ[ℝ] F} (d : SVD H ι κ)

abbrev Active := {j // 0 < d.σ j}

private theorem e_injective : Function.Injective fun j : d.Active => d.e j :=
  fun j j' h => Subtype.ext (d.injOn j j' j.2 j'.2 h)

private theorem orthonormal_u_e : Orthonormal ℝ fun j : d.Active => d.u (d.e j) :=
  d.u.orthonormal.comp _ d.e_injective

private theorem inner_u_e_H_sum (a : d.Active → ℝ) (j : d.Active) :
    inner ℝ (d.u (d.e j)) (H (∑ k : d.Active, a k • d.v k)) = d.σ j * a j := by
  have h : H (∑ k : d.Active, a k • d.v k) = ∑ k : d.Active, (d.σ k * a k) • d.u (d.e k) := by
    simp only [map_sum, map_smul, d.apply_v, smul_smul, mul_comm]
  rw [h]
  exact d.orthonormal_u_e.inner_right_fintype _ j

private theorem norm_sq_sum (a : d.Active → ℝ) :
    ‖∑ k : d.Active, a k • d.v k‖ ^ 2 = ∑ k, a k ^ 2 := by
  have ho : Orthonormal ℝ fun k : d.Active => d.v k :=
    d.v.orthonormal.comp _ Subtype.val_injective
  rw [← real_inner_self_eq_norm_sq, ho.inner_sum]
  simp [sq]

end SVD

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

variable (F) in
noncomputable def noiseLetter (N : ℝ) : Measure F :=
  (stdGaussian F).map fun z => √N • z

variable (F) in
noncomputable def noise (N : ℝ) (n : ℕ) : Measure (Fin n → F) :=
  Measure.pi fun _ => noiseLetter F N

instance isProbabilityMeasure_noiseLetter (N : ℝ) : IsProbabilityMeasure (noiseLetter F N) := by
  unfold noiseLetter
  infer_instance

instance isProbabilityMeasure_noise (N : ℝ) (n : ℕ) : IsProbabilityMeasure (noise F N n) := by
  unfold noise
  infer_instance

private theorem map_stdGaussian_inner {κ : Type*} [Fintype κ] (b : OrthonormalBasis κ ℝ F) :
    (stdGaussian F).map (fun z i => inner ℝ (b i) z) =
      Measure.pi fun _ : κ => gaussianReal 0 1 := by
  have e : (fun z i => inner ℝ (b i) z) = (fun x : EuclideanSpace ℝ κ => x.ofLp) ∘ b.repr :=
    funext fun z => funext fun i => (b.repr_apply_apply z i).symm
  have h1 := stdGaussian_map b.repr
  have h2 := map_pi_eq_stdGaussian (ι := κ)
  rw [e, ← Measure.map_map (by fun_prop) (by fun_prop), h1, ← h2,
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

private theorem map_noiseLetter_inner {κ : Type*} [Fintype κ] (b : OrthonormalBasis κ ℝ F) {N : ℝ}
    (hN : 0 ≤ N) :
    (noiseLetter F N).map (fun z i => inner ℝ (b i) z) =
      Measure.pi fun _ : κ => gaussianReal 0 N.toNNReal := by
  have e : (fun z i => inner ℝ (b i) z) ∘ (fun z : F => √N • z) =
      (fun w (i : κ) => √N * w i) ∘ fun z i => inner ℝ (b i) z := by
    funext z i
    simp [inner_smul_right]
  have hg : ∀ i : κ, (gaussianReal 0 1).map (fun x => √N * x) = gaussianReal 0 N.toNNReal := by
    intro i
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · ext
      simp [Real.sq_sqrt hN, hN]
  rw [noiseLetter, Measure.map_map (by fun_prop) (by fun_prop), e,
    ← Measure.map_map (by fun_prop) (by fun_prop), map_stdGaussian_inner,
    Measure.pi_map_pi fun i => (measurable_const_mul _).aemeasurable]
  exact congrArg Measure.pi (funext hg)

private theorem map_noise_inner {κ : Type*} [Fintype κ] (b : OrthonormalBasis κ ℝ F) {N : ℝ}
    (hN : 0 ≤ N) (n : ℕ) :
    (noise F N n).map (fun z i t => inner ℝ (b i) (z t)) = Parallel.noise (fun _ : κ => N) n := by
  have e : (fun (z : Fin n → F) (i : κ) (t : Fin n) => inner ℝ (b i) (z t)) =
      (fun (w : Fin n → κ → ℝ) i t => w t i) ∘
        fun z t => (fun y i => inner ℝ (b i) y) (z t) := rfl
  have : ∀ t : Fin n, SigmaFinite ((noiseLetter F N).map fun y i => inner ℝ (b i) y) := fun t => by
    rw [map_noiseLetter_inner b hN]
    infer_instance
  rw [e, ← Measure.map_map (by fun_prop) (by fun_prop), noise,
    Measure.pi_map_pi fun t => (by fun_prop : Measurable fun y i => inner ℝ (b i) y).aemeasurable]
  simp_rw [map_noiseLetter_inner b hN]
  rw [pi_pi_swap]
  rfl

private theorem pi_map_comp_injective {α κ K : Type*} [MeasurableSpace α] [Fintype κ] [Fintype K]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : K → κ} (hf : Function.Injective f) :
    (Measure.pi fun _ : κ => μ).map (fun w j => w (f j)) = Measure.pi fun _ : K => μ := by
  classical
  refine (Measure.pi_eq fun s hs => ?_).symm
  set s' : κ → Set α := Function.extend f s fun _ => Set.univ
  have hpre : (fun (w : κ → α) j => w (f j)) ⁻¹' Set.univ.pi s = Set.univ.pi s' := by
    ext w
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i
      by_cases hi : ∃ j, f j = i
      · obtain ⟨j, rfl⟩ := hi
        rw [show s' (f j) = s j from hf.extend_apply _ _ j]
        exact h j
      · rw [show s' i = Set.univ from Function.extend_apply' _ _ _ hi]
        exact Set.mem_univ _
    · intro h j
      have := h (f j)
      rwa [show s' (f j) = s j from hf.extend_apply _ _ j] at this
  have hs' : ∀ i, MeasurableSet (s' i) := fun i => by
    by_cases hi : ∃ j, f j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [show s' (f j) = s j from hf.extend_apply _ _ j]
      exact hs j
    · rw [show s' i = Set.univ from Function.extend_apply' _ _ _ hi]
      exact MeasurableSet.univ
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi]
  refine (Fintype.prod_of_injective f hf _ _ (fun i hi => ?_) fun j => ?_).symm
  · rw [show s' i = Set.univ from Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hi ⟨j, hj⟩,
      measure_univ]
  · rw [show s' (f j) = s j from hf.extend_apply _ _ j]

variable (E F) in
structure Code (P : ℝ) (n k : ℕ) where
  enc : Fin k → Fin n → E
  power : ∀ m, ∑ t, ‖enc m t‖ ^ 2 ≤ n * P
  dec : (Fin n → F) → Fin k
  measurable_dec : Measurable dec

namespace Code

variable {P : ℝ} {n k : ℕ}

noncomputable def errorProb (c : Code E F P n k) (H : E →ₗ[ℝ] F) (N : ℝ) (m : Fin k) : ℝ≥0∞ :=
  noise F N n {z | c.dec (fun t => H (c.enc m t) + z t) ≠ m}

noncomputable def avgError (c : Code E F P n k) (H : E →ₗ[ℝ] F) (N : ℝ) : ℝ≥0∞ :=
  (∑ m, c.errorProb H N m) / k

end Code

def Achievable (H : E →ₗ[ℝ] F) (P N R : ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ k : ℕ, Real.exp (n * R) ≤ k ∧ ∃ c : Code E F P n k, c.avgError H N ≤ ε

omit [BorelSpace F] in
theorem achievable_zero (H : E →ₗ[ℝ] F) {P : ℝ} (hP : 0 ≤ P) (N : ℝ) : Achievable H P N 0 := by
  intro ε _
  refine ⟨0, fun n _ => ⟨1, by simp, ⟨fun _ _ => 0, fun _ => by
    simpa using mul_nonneg n.cast_nonneg hP,
    fun _ => 0, measurable_const⟩, ?_⟩⟩
  simp [Code.avgError, Code.errorProb, Subsingleton.elim _ (0 : Fin 1)]

namespace SVD

variable {H : E →ₗ[ℝ] F} (d : SVD H ι κ)

noncomputable def project {n : ℕ} (z : Fin n → F) (j : d.Active) (t : Fin n) : ℝ :=
  (d.σ j)⁻¹ * inner ℝ (d.u (d.e j)) (z t)

omit [FiniteDimensional ℝ F] in
private theorem measurable_project (n : ℕ) : Measurable (d.project (n := n)) := by
  unfold project
  fun_prop

theorem map_noise_project {N : ℝ} (hN : 0 ≤ N) (n : ℕ) :
    (noise F N n).map (d.project (n := n)) =
      Parallel.noise (fun j : d.Active => N / d.σ j ^ 2) n := by
  have e : d.project (n := n) =
      (fun (w : d.Active → Fin n → ℝ) (j : d.Active) (t : Fin n) => (d.σ j)⁻¹ * w j t) ∘
      (fun (w : κ → Fin n → ℝ) (j : d.Active) => w (d.e j)) ∘
        fun (z : Fin n → F) (i : κ) (t : Fin n) => inner ℝ (d.u i) (z t) := rfl
  have hg : ∀ j : d.Active, (gaussianReal 0 N.toNNReal).map (fun x => (d.σ j)⁻¹ * x) =
      gaussianReal 0 (N / d.σ j ^ 2).toNNReal := by
    intro j
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · ext
      have hσ := j.2.ne'
      simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hN,
        Real.coe_toNNReal _ (div_nonneg hN (sq_nonneg _))]
      field_simp
  have : ∀ (j : d.Active) (t : Fin n),
      SigmaFinite ((gaussianReal 0 N.toNNReal).map fun x => (d.σ j)⁻¹ * x) := fun j t => by
    rw [hg]
    infer_instance
  have : ∀ j : d.Active, SigmaFinite ((AWGN.noise N n).map
      fun w (t : Fin n) => (d.σ j)⁻¹ * w t) := fun j => by
    rw [AWGN.noise, Measure.pi_map_pi fun t => (measurable_const_mul _).aemeasurable]
    infer_instance
  rw [e, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop), map_noise_inner d.u hN, Parallel.noise,
    pi_map_comp_injective _ d.e_injective]
  have hpm := Measure.pi_map_pi (μ := fun _ : d.Active => AWGN.noise N n)
    (f := fun j (w : Fin n → ℝ) (t : Fin n) => (d.σ j)⁻¹ * w t)
    (fun j => (by fun_prop : Measurable fun (w : Fin n → ℝ) (t : Fin n) =>
      (d.σ j)⁻¹ * w t).aemeasurable)
  refine hpm.trans ?_
  unfold Parallel.noise
  congr 1
  funext j
  rw [AWGN.noise, Measure.pi_map_pi fun t => (measurable_const_mul _).aemeasurable]
  exact congrArg Measure.pi (funext fun t => hg j)

noncomputable def ofParallel {P : ℝ} {n k : ℕ} (c : Parallel.Code d.Active P n k) :
    Code E F P n k where
  enc m t := ∑ j : d.Active, c.enc m j t • d.v j
  power m := by
    simp_rw [d.norm_sq_sum]
    rw [Finset.sum_comm]
    exact c.power m
  dec y := c.dec (d.project y)
  measurable_dec := c.measurable_dec.comp (d.measurable_project n)

omit [FiniteDimensional ℝ F] in
private theorem project_add {P : ℝ} {n k : ℕ} (c : Parallel.Code d.Active P n k) (m : Fin k)
    (z : Fin n → F) :
    d.project (fun t => H ((d.ofParallel c).enc m t) + z t) = c.enc m + d.project z := by
  funext j t
  simp only [project, ofParallel, inner_add_right, d.inner_u_e_H_sum, Pi.add_apply]
  field_simp [j.2.ne']

theorem avgError_ofParallel {P N : ℝ} (hN : 0 ≤ N) {n k : ℕ}
    (c : Parallel.Code d.Active P n k) :
    (d.ofParallel c).avgError H N = c.avgError fun j : d.Active => N / d.σ j ^ 2 := by
  unfold Code.avgError Parallel.Code.avgError
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hs : MeasurableSet {w : d.Active → Fin n → ℝ | c.dec (c.enc m + w) ≠ m} :=
    (c.measurable_dec.comp (measurable_const_add _)) (measurableSet_singleton m).compl
  rw [Parallel.Code.errorProb, ← d.map_noise_project hN n,
    Measure.map_apply (d.measurable_project n) hs, Code.errorProb]
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, ofParallel, ← d.project_add c m z]

theorem achievable_of_lt [Nonempty d.Active] {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) {R : ℝ}
    (hR : R < WaterFilling.capacity (fun j : d.Active => N / d.σ j ^ 2) P) :
    Achievable H P N R := by
  have h := Parallel.achievable_of_lt hP (fun j : d.Active => div_pos hN (pow_pos j.2 2)) hR
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h ε hε
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hn₀ n hn
  exact ⟨k, hk, d.ofParallel c, by rw [d.avgError_ofParallel hN.le]; exact hc⟩

end SVD

namespace SVD

variable {H : E →ₗ[ℝ] F} (d : SVD H ι κ)

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
private theorem inner_u_H (i : κ) (x : E) :
    inner ℝ (d.u i) (H x) = ∑ j, inner ℝ (d.v j) x * d.σ j * inner ℝ (d.u i) (d.u (d.e j)) := by
  conv_lhs => rw [← d.v.sum_repr' x]
  simp only [map_sum, map_smul, d.apply_v, inner_sum, inner_smul_right, smul_smul]

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
private theorem inner_u_e_H (j : d.Active) (x : E) :
    inner ℝ (d.u (d.e j)) (H x) = d.σ j * inner ℝ (d.v j) x := by
  classical
  rw [d.inner_u_H, sum_eq_single (j : ι)]
  · rw [d.u.inner_eq_ite, ite_eq_left rfl]
    ring
  · intro k _ hk
    rcases (d.σ_nonneg k).eq_or_lt with h | h
    · rw [← h]
      ring
    · rw [d.u.inner_eq_ite, ite_eq_right fun h' => hk (d.injOn k j h j.2 h'.symm), mul_zero]
  · simp

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
private theorem inner_u_H_eq_zero {i : κ} (hi : i ∉ Set.range fun j : d.Active => d.e j) (x : E) :
    inner ℝ (d.u i) (H x) = 0 := by
  classical
  rw [d.inner_u_H]
  refine sum_eq_zero fun k _ => ?_
  rcases (d.σ_nonneg k).eq_or_lt with h | h
  · rw [← h]
    ring
  · rw [d.u.inner_eq_ite, ite_eq_right fun h' => hi ⟨⟨k, h⟩, h'.symm⟩, mul_zero]

end SVD

private lemma avg_aux {k : ℕ} (hk : 0 < k) {N : ℝ} (hN : 0 < N) (x : Fin k → ℝ)
    {Pb : ℝ} (hPb : Pb = (∑ a, x a ^ 2) / k) :
    ∑ a, (k : ℝ)⁻¹ * (1 / 2 * Real.log ((Pb + N) / N) - 1 / 2 + (x a ^ 2 + N) / (2 * (Pb + N)))
      = awgnCapacity Pb N := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hPb0 : 0 ≤ Pb := by rw [hPb]; positivity
  have hS : 0 < Pb + N := by linarith
  have hsq : ∑ a, x a ^ 2 = k * Pb := by rw [hPb]; field_simp
  have hlog : (Pb + N) / N = 1 + Pb / N := by field_simp; ring
  rw [← mul_sum, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← sum_div, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hsq,
    hlog]
  unfold awgnCapacity
  field_simp
  ring

namespace Code

variable {P : ℝ} {n k : ℕ}

omit [FiniteDimensional ℝ F] in
private theorem measurable_dec_add (c : Code E F P n k) (H : E →ₗ[ℝ] F) (m : Fin k) :
    Measurable fun z : Fin n → F => c.dec (fun t => H (c.enc m t) + z t) :=
  c.measurable_dec.comp (measurable_pi_iff.2 fun t => (measurable_pi_apply t).const_add _)

noncomputable def channel (c : Code E F P n k) (H : E →ₗ[ℝ] F) (N : ℝ) : DMC (Fin k) (Fin k) :=
  fun m => ((noise F N n).map fun z => c.dec (fun t => H (c.enc m t) + z t)).toPMF

private def toBlockCode (k : ℕ) : BlockCode (Fin k) (Fin k) (Fin k) 1 :=
  ⟨fun m _ => m, fun y => y 0⟩

private lemma avgError_toBlockCode (c : Code E F P n k) (H : E →ₗ[ℝ] F) (N : ℝ) :
    (toBlockCode k).avgError (c.channel H N) = c.avgError H N := by
  classical
  simp only [BlockCode.avgError, avgError, Fintype.card_fin]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [BlockCode.errorProb, ← (Equiv.funUnique (Fin 1) (Fin k)).symm.sum_comp]
  simp only [DMC.blockProb, toBlockCode, Fin.prod_univ_one]
  have h : ∀ j : Fin k, (Equiv.funUnique (Fin 1) (Fin k)).symm j 0 = j := fun j => rfl
  simp only [h, channel, Measure.toPMF_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, sum_measure_singleton,
    Measure.map_apply (c.measurable_dec_add H m) (Finset.measurableSet _), errorProb]
  congr 1
  ext z
  simp

private lemma inputLaw_toBlockCode (hk : 0 < k) (a : Fin k) :
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    ((toBlockCode k).inputLaw 0 a).toReal = (k : ℝ)⁻¹ := by
  simp only [BlockCode.inputLaw, toBlockCode, PMF.map_apply, PMF.ofFintype_apply, Fintype.card_fin]
  rw [tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
  simp

variable {H : E →ₗ[ℝ] F} (d : SVD H ι κ)

private theorem channel_toReal (c : Code E F P n k) {N : ℝ} (hN : 0 ≤ N) (m j : Fin k) :
    (c.channel H N m j).toReal =
      ((Parallel.noise (fun _ : κ => N) n).map fun w =>
        (fun i t => inner ℝ (d.u i) (H (c.enc m t))) + w).real
        ((c.dec ∘ fun (w : κ → Fin n → ℝ) t => ∑ i, w i t • d.u i) ⁻¹' {j}) := by
  have hrot : Measurable fun (z : Fin n → F) (i : κ) (t : Fin n) => inner ℝ (d.u i) (z t) := by
    fun_prop
  have hun : Measurable fun (w : κ → Fin n → ℝ) t => ∑ i, w i t • d.u i := by fun_prop
  have hd' : Measurable (c.dec ∘ fun (w : κ → Fin n → ℝ) t => ∑ i, w i t • d.u i) :=
    c.measurable_dec.comp hun
  have hs : MeasurableSet ((c.dec ∘ fun (w : κ → Fin n → ℝ) t => ∑ i, w i t • d.u i) ⁻¹' {j}) :=
    hd' (measurableSet_singleton j)
  rw [channel, Measure.toPMF_apply, Measure.map_apply (c.measurable_dec_add H m)
    (measurableSet_singleton j), measureReal_def, ← map_noise_inner d.u hN n,
    Measure.map_map (measurable_const_add _) hrot, Measure.map_apply
      ((measurable_const_add _).comp hrot) hs]
  congr 2
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply, Pi.add_apply,
    ← inner_add_right, d.u.sum_repr']

theorem inputMutualInfo_channel_le [Nonempty d.Active] (c : Code E F P n k) (hP : 0 ≤ P)
    {N : ℝ} (hN : 0 < N) (p : PMF (Fin k)) (hp : ∀ a, (p a).toReal = (k : ℝ)⁻¹) :
    (c.channel H N).inputMutualInfo p ≤
      n * WaterFilling.capacity (fun j : d.Active => N / d.σ j ^ 2) P := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact absurd (p.tsum_coe) (by simp)
  set M : Fin k → κ → Fin n → ℝ := fun m i t => inner ℝ (d.u i) (H (c.enc m t))
  set Pb : κ → Fin n → ℝ := fun i t => (∑ m, M m i t ^ 2) / k
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hPb : ∀ i t, 0 ≤ Pb i t := fun i t =>
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hk'.le
  set S : κ → Fin n → ℝ := fun i t => Pb i t + N
  have hS : ∀ i t, 0 < S i t := fun i t => by simp only [S]; linarith [hPb i t]
  set ρ := Measure.pi fun i : κ => Measure.pi fun t : Fin n => gaussianReal 0 (S i t).toNNReal
  set dec' := c.dec ∘ fun (w : κ → Fin n → ℝ) t => ∑ i, w i t • d.u i
  have hd' : Measurable dec' := c.measurable_dec.comp (by fun_prop)
  set r : Fin k → ℝ := fun j => ρ.real (dec' ⁻¹' {j})
  have hsum : ∑ j, r j = 1 := by
    have h : ∀ j, r j = (ρ.map dec').real {j} := fun j =>
      (map_measureReal_apply hd' (measurableSet_singleton j)).symm
    simp only [h]
    exact sum_measureReal_singleton_eq_one _
  have hz : ∀ a j, r j = 0 → (c.channel H N a j).toReal = 0 := by
    intro a j hj
    rw [channel_toReal d c hN.le, measureReal_def,
      Parallel.map_noise_add_absolutelyContinuous (fun _ => hN) (M a) S hS
        ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 hj), ENNReal.toReal_zero]
  refine (DMC.inputMutualInfo_le_sum_mul_log_sub _ p (fun _ => measureReal_nonneg)
    hsum.le hz).trans ?_
  have hper : ∀ a, ∑ j, (c.channel H N a j).toReal
      * (Real.log (c.channel H N a j).toReal - Real.log (r j))
      ≤ ∑ i, ∑ t, (1 / 2 * Real.log (S i t / N) - 1 / 2 + (M a i t ^ 2 + N) / (2 * S i t)) := by
    intro a
    simp only [channel_toReal d c hN.le]
    exact Parallel.sum_mul_log_sub_log_le (fun _ => hN) (M a) S hS hd'
  refine (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hper a)
    (by rw [hp]; positivity)).trans ?_
  have havg : ∑ a, (p a).toReal * ∑ i, ∑ t, (1 / 2 * Real.log (S i t / N) - 1 / 2 +
        (M a i t ^ 2 + N) / (2 * S i t)) = ∑ i, ∑ t, awgnCapacity (Pb i t) N := by
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => avg_aux hk hN (fun a => M a i t) rfl
  rw [havg]
  set Q : d.Active → Fin n → ℝ := fun j t => (∑ m, inner ℝ (d.v j) (c.enc m t) ^ 2) / k
  have hQ : ∀ j t, 0 ≤ Q j t := fun j t =>
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hk'.le
  have hre : ∑ i, ∑ t, awgnCapacity (Pb i t) N =
      ∑ j : d.Active, ∑ t, awgnCapacity (Q j t) (N / d.σ j ^ 2) := by
    refine (Fintype.sum_of_injective (fun j : d.Active => d.e j) d.e_injective _ _
      (fun i hi => ?_) fun j => ?_).symm
    · refine sum_eq_zero fun t _ => ?_
      have : Pb i t = 0 := by
        simp only [Pb, M, d.inner_u_H_eq_zero hi]
        simp
      rw [this, awgnCapacity]
      simp
    · refine sum_congr rfl fun t _ => ?_
      have hσ := j.2.ne'
      have : Pb (d.e j) t = d.σ j ^ 2 * Q j t := by
        simp only [Pb, Q, M, d.inner_u_e_H, mul_pow, ← mul_sum]
        ring
      rw [this]
      unfold awgnCapacity
      congr 2
      field_simp
  rw [hre]
  refine Parallel.sum_awgnCapacity_le hP (fun j => div_pos hN (pow_pos j.2 2)) Q
    hQ ?_
  simp only [Q, ← Finset.sum_div]
  rw [div_le_iff₀ hk']
  have hpar : ∀ x : E, ∑ j : d.Active, inner ℝ (d.v j) x ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x
    calc ∑ j : d.Active, inner ℝ (d.v j) x ^ 2 ≤ ∑ j : ι, inner ℝ (d.v j) x ^ 2 := by
          rw [← Finset.sum_subtype (univ.filter fun j => 0 < d.σ j) (by simp)
            (fun j => inner ℝ (d.v j) x ^ 2)]
          exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => sq_nonneg _
      _ = ‖x‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq, ← d.v.sum_inner_mul_inner x x]
          exact sum_congr rfl fun j _ => by rw [real_inner_comm, sq]
  calc ∑ j : d.Active, ∑ t, ∑ m, inner ℝ (d.v j) (c.enc m t) ^ 2 =
        ∑ m, ∑ t, ∑ j : d.Active, inner ℝ (d.v j) (c.enc m t) ^ 2 := by
        rw [Finset.sum_comm]
        refine (Finset.sum_congr rfl fun t _ => Finset.sum_comm).trans ?_
        exact Finset.sum_comm
    _ ≤ ∑ m, ∑ t, ‖c.enc m t‖ ^ 2 :=
        Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun t _ => hpar _
    _ ≤ ∑ _m : Fin k, (n * P) := Finset.sum_le_sum fun m _ => c.power m
    _ = n * P * k := by simp [mul_comm]

theorem one_sub_mul_log_le [Nonempty d.Active] (c : Code E F P n k) (hP : 0 ≤ P) {N : ℝ}
    (hN : 0 < N) (hk : 0 < k) :
    (1 - (c.avgError H N).toReal) * Real.log k ≤
      n * WaterFilling.capacity (fun j : d.Active => N / d.σ j ^ 2) P + Real.log 2 := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h1 := (toBlockCode k).mutualInfo_le_sum_inputMutualInfo (c.channel H N)
  rw [Fin.sum_univ_one] at h1
  have h2 := (toBlockCode k).condEntropy_fst_snd_codeMeasure_le (c.channel H N)
  have h3 := mutualInfo_eq_entropy_sub_condEntropy Prod.fst Prod.snd
    ((toBlockCode k).codeMeasure (c.channel H N))
  rw [BlockCode.entropy_fst_codeMeasure] at h3
  rw [avgError_toBlockCode] at h2
  have h4 := inputMutualInfo_channel_le d c hP hN _ (inputLaw_toBlockCode hk)
  rw [Fintype.card_fin] at h2 h3
  nlinarith

end Code

namespace SVD

variable {H : E →ₗ[ℝ] F} (d : SVD H ι κ)

theorem le_capacity_of_achievable [Nonempty d.Active] {P N R : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (h : Achievable H P N R) :
    R ≤ WaterFilling.capacity (fun j : d.Active => N / d.σ j ^ 2) P := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hC := Parallel.capacity_nonneg hP fun j : d.Active => div_pos hN (pow_pos j.2 2)
  set C := WaterFilling.capacity (fun j : d.Active => N / d.σ j ^ 2) P
  set δ := R - C with hδ
  have hδ0 : 0 < δ := by linarith
  have hR : 0 < R := by linarith
  set e := δ / (2 * R) with he
  have he0 : 0 < e := by positivity
  have he1 : e * R = δ / 2 := by
    rw [he]
    field_simp
  have he2 : 0 < 1 - e := by nlinarith
  obtain ⟨n₀, hn₀⟩ := h (ENNReal.ofReal e) (ENNReal.ofReal_pos.2 he0)
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (2 * Real.log 2 / δ)
  obtain ⟨n, hNn, hn0n⟩ : ∃ n : ℕ, n₀ ≤ n ∧ m₀ ≤ n :=
    ⟨max n₀ m₀, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨k, hk, c, hc⟩ := hn₀ n hNn
  have hn : 2 * Real.log 2 < n * δ := by
    rw [← div_lt_iff₀ hδ0]
    exact hm₀.trans_le (by exact_mod_cast hn0n)
  have hk0 : (0 : ℝ) < k := (Real.exp_pos _).trans_le hk
  have key := Code.one_sub_mul_log_le d c hP hN (by exact_mod_cast hk0)
  have hPe : (c.avgError H N).toReal ≤ e := ENNReal.toReal_le_of_le_ofReal he0.le hc
  have hlog : n * R ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have h1 : (1 - e) * Real.log k ≤ n * C + Real.log 2 :=
    (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg k)).trans key
  have h2 : (1 - e) * (n * R) ≤ (1 - e) * Real.log k := mul_le_mul_of_nonneg_left hlog he2.le
  have h3 : (1 - e) * (n * R) = n * C + n * (δ / 2) := by
    linear_combination (-(n : ℝ)) * he1 - (n : ℝ) * hδ
  linarith

theorem closure_achievable_eq [Nonempty d.Active] {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    closure {R : ℝ | 0 ≤ R ∧ Achievable H P N R} =
      Set.Icc 0 (WaterFilling.capacity (fun j : d.Active => N / d.σ j ^ 2) P) := by
  refine subset_antisymm (closure_minimal (fun R hR => ⟨hR.1, d.le_capacity_of_achievable hP hN
    hR.2⟩) isClosed_Icc) fun R hR => ?_
  rcases (Parallel.capacity_nonneg hP fun j : d.Active =>
    div_pos hN (pow_pos j.2 2)).eq_or_lt with h | h
  · rw [← h, Set.Icc_self, Set.mem_singleton_iff] at hR
    exact subset_closure ⟨hR.symm ▸ le_rfl, hR ▸ achievable_zero H hP N⟩
  · rw [← closure_Ico h.ne] at hR
    refine closure_mono (fun R (hR : R ∈ Set.Ico 0
      (WaterFilling.capacity (fun j : d.Active => N / d.σ j ^ 2) P)) => ?_) hR
    exact ⟨hR.1, d.achievable_of_lt hP hN hR.2⟩

end SVD

section Existence

variable [FiniteDimensional ℝ E]

omit [MeasurableSpace F] [BorelSpace F] in
theorem isSymmetric_gram (H : E →ₗ[ℝ] F) : (LinearMap.adjoint H ∘ₗ H).IsSymmetric := by
  intro x y
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]

omit [MeasurableSpace F] [BorelSpace F] in
theorem exists_svd (H : E →ₗ[ℝ] F) (hH : H ≠ 0) :
    ∃ d : SVD H (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ F)), Nonempty d.Active ∧
      ∀ j, (LinearMap.adjoint H ∘ₗ H) (d.v j) = d.σ j ^ 2 • d.v j := by
  classical
  set hT := isSymmetric_gram H
  set v := hT.eigenvectorBasis rfl
  set lam := hT.eigenvalues rfl
  have hTv : ∀ j, (LinearMap.adjoint H ∘ₗ H) (v j) = lam j • v j := fun j =>
    hT.apply_eigenvectorBasis rfl j
  have hHH : ∀ j k, inner ℝ (H (v j)) (H (v k)) = if j = k then lam k else 0 := by
    intro j k
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, hTv, inner_smul_right,
      v.inner_eq_ite]
    split_ifs <;> simp
  have hlam : ∀ j, 0 ≤ lam j := fun j => by
    have := hHH j j
    rw [ite_eq_left rfl, real_inner_self_eq_norm_sq] at this
    rw [← this]
    positivity
  set σ : Fin (Module.finrank ℝ E) → ℝ := fun j => √(lam j)
  have hσ2 : ∀ j, σ j ^ 2 = lam j := fun j => Real.sq_sqrt (hlam j)
  set A := {j // 0 < σ j}
  set u' : A → F := fun j => (σ j)⁻¹ • H (v j)
  have hu' : Orthonormal ℝ u' := by
    rw [orthonormal_iff_ite]
    intro j k
    simp only [u', inner_smul_left, inner_smul_right, hHH]
    by_cases h : j = k
    · subst h
      have := j.2.ne'
      rw [ite_eq_left rfl, ite_eq_left rfl, ← hσ2]
      simp
      field_simp
    · have h' : (j : Fin (Module.finrank ℝ E)) ≠ k := fun e => h (Subtype.ext e)
      simp [h, h']
  have hA : Nonempty A := by
    by_contra h0
    apply hH
    refine v.toBasis.ext fun j => ?_
    have hj : σ j = 0 := le_antisymm (not_lt.1 fun h => h0 ⟨⟨j, h⟩⟩) (Real.sqrt_nonneg _)
    have hn := hHH j j
    rw [ite_eq_left rfl, real_inner_self_eq_norm_sq, ← hσ2, hj] at hn
    simpa using hn
  have hcard : Fintype.card A ≤ Fintype.card (Fin (Module.finrank ℝ F)) := by
    rw [Fintype.card_fin]
    exact hu'.linearIndependent.fintype_card_le_finrank
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨a₀⟩ := hA
  set vF : Fin (Module.finrank ℝ F) → F := fun i =>
    if h : ∃ a, emb a = i then u' h.choose else 0
  have hvF : ∀ a, vF (emb a) = u' a := fun a => by
    have h : ∃ a', emb a' = emb a := ⟨a, rfl⟩
    simp only [vF, dite_eq_left h]
    rw [emb.injective h.choose_spec]
  have hon : Orthonormal ℝ ((Set.range emb).domRestrict vF) := by
    set g : Set.range emb → A := fun i => i.2.choose
    have hg : Function.Injective g := fun i i' h => Subtype.ext (by
      rw [← i.2.choose_spec, ← i'.2.choose_spec]
      exact congrArg emb h)
    have he : (Set.range emb).domRestrict vF = u' ∘ g := by
      funext i
      simp only [Set.domRestrict_apply, Function.comp_apply, g]
      rw [← hvF, i.2.choose_spec]
    rw [he]
    exact hu'.comp g hg
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hon
  set e : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ F) := fun j =>
    if h : 0 < σ j then emb ⟨j, h⟩ else emb a₀
  refine ⟨⟨v, b, σ, e, fun j => Real.sqrt_nonneg _, fun j j' h h' hjj => ?_, fun j => ?_⟩,
    ⟨a₀⟩, fun j => by rw [hTv, ← hσ2]⟩
  · simp only [e, dite_eq_left h, dite_eq_left h'] at hjj
    exact congrArg Subtype.val (emb.injective hjj)
  · by_cases h : 0 < σ j
    · simp only [e, dite_eq_left h]
      rw [hb _ ⟨_, rfl⟩, hvF]
      simp only [u', smul_smul, mul_inv_cancel₀ h.ne', one_smul]
    · have hj : σ j = 0 := le_antisymm (not_lt.1 h) (Real.sqrt_nonneg _)
      have hn := hHH j j
      rw [ite_eq_left rfl, real_inner_self_eq_norm_sq, ← hσ2, hj] at hn
      rw [hj, zero_smul]
      simpa using hn

theorem closure_achievable_eq (H : E →ₗ[ℝ] F) (hH : H ≠ 0) {P N : ℝ}
    (hP : 0 ≤ P) (hN : 0 < N) :
    ∃ d : SVD H (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ F)),
      (∀ j, (LinearMap.adjoint H ∘ₗ H) (d.v j) = d.σ j ^ 2 • d.v j) ∧
      closure {R : ℝ | 0 ≤ R ∧ Achievable H P N R} =
        Set.Icc 0 (WaterFilling.capacity (fun j : d.Active => N / d.σ j ^ 2) P) := by
  obtain ⟨d, hd, hv⟩ := exists_svd H hH
  exact ⟨d, hv, d.closure_achievable_eq hP hN⟩

end Existence

end MIMO

end Meat
