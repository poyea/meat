import Meat.Open.RelayDecodeForward

open MeasureTheory Finset Filter Topology
open scoped ENNReal

namespace Meat

namespace RelayCode

variable {M M' A A₁ B B₁ : Type*} {n : ℕ}

def relabel (c : RelayCode M A A₁ B B₁ n) (e : M ≃ M') : RelayCode M' A A₁ B B₁ n :=
  ⟨fun m => c.enc (e.symm m), c.relay, c.causal, fun y => e (c.dec y)⟩

theorem avgError_relabel [Fintype B] [Fintype B₁] [Fintype M] [Fintype M'] [DecidableEq M]
    [DecidableEq M'] (c : RelayCode M A A₁ B B₁ n) (W : DMC (A × A₁) (B × B₁)) (e : M ≃ M') :
    (c.relabel e).avgError W = c.avgError W := by
  have h : ∀ m, (c.relabel e).errorProb W (e m) = c.errorProb W m := fun m => by
    simp only [errorProb, relabel, seqProb, Equiv.symm_apply_apply, e.apply_eq_iff_eq]
  rw [avgError, avgError, ← Fintype.sum_equiv e (fun m => c.errorProb W m)
    (fun m' => (c.relabel e).errorProb W m') fun m => (h m).symm, Fintype.card_congr e]

def pad (c : RelayCode M A A₁ B B₁ n) (r : ℕ) (a₀ : A) (a₁ : A₁) :
    RelayCode M A A₁ B B₁ (n + r) where
  enc m := Fin.append (c.enc m) fun _ => a₀
  relay t y := Fin.addCases (fun s => c.relay s fun u => y (Fin.castAdd r u)) (fun _ => a₁) t
  causal t y y' h := by
    induction t using Fin.addCases with
    | left s =>
      simp only [Fin.addCases_left]
      exact c.causal s _ _ fun u hu => h _ (show (u : ℕ) < s from hu)
    | right s => simp only [Fin.addCases_right]
  dec y := c.dec fun u => y (Fin.castAdd r u)

def splitEquiv {S : Type*} (n r : ℕ) : (Fin (n + r) → S) ≃ (Fin n → S) × (Fin r → S) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl S)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem splitEquiv_symm_castAdd {S : Type*} (n r : ℕ) (u : Fin n → S) (v : Fin r → S)
    (s : Fin n) : (splitEquiv n r).symm (u, v) (Fin.castAdd r s) = u s := by
  simp [splitEquiv, Equiv.arrowCongr]

theorem splitEquiv_symm_natAdd {S : Type*} (n r : ℕ) (u : Fin n → S) (v : Fin r → S)
    (s : Fin r) : (splitEquiv n r).symm (u, v) (Fin.natAdd n s) = v s := by
  simp [splitEquiv, Equiv.arrowCongr]

theorem errorProb_pad [Fintype B] [Fintype B₁] [DecidableEq M] (c : RelayCode M A A₁ B B₁ n)
    (r : ℕ) (a₀ : A) (a₁ : A₁) (W : DMC (A × A₁) (B × B₁)) (m : M) :
    (c.pad r a₀ a₁).errorProb W m = c.errorProb W m := by
  rw [errorProb, ← Fintype.sum_equiv (splitEquiv n r).symm (fun uv : (Fin n → B × B₁) ×
    (Fin r → B × B₁) => if (c.pad r a₀ a₁).dec (fun i => ((splitEquiv n r).symm uv i).1) = m
      then 0 else (c.pad r a₀ a₁).seqProb W m ((splitEquiv n r).symm uv)) _ fun _ => rfl,
    Fintype.sum_prod_type]
  have hs : ∀ (u : Fin n → B × B₁) (v : Fin r → B × B₁),
      (c.pad r a₀ a₁).seqProb W m ((splitEquiv n r).symm (u, v)) =
        c.seqProb W m u * ∏ s, W (a₀, a₁) (v s) := by
    intro u v
    simp only [seqProb, pad, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
      Fin.addCases_left, Fin.addCases_right, splitEquiv_symm_castAdd, splitEquiv_symm_natAdd]
  have hd : ∀ (u : Fin n → B × B₁) (v : Fin r → B × B₁),
      (c.pad r a₀ a₁).dec (fun i => ((splitEquiv n r).symm (u, v) i).1) =
        c.dec (fun i => (u i).1) := by
    intro u v
    simp only [pad, splitEquiv_symm_castAdd]
  have hv : ∑ v : Fin r → B × B₁, ∏ s, W (a₀, a₁) (v s) = 1 := DMC.sum_blockProb_eq_one W _
  rw [errorProb]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [hs, hd]
  by_cases h : c.dec (fun i => (u i).1) = m
  · simp [h]
  · simp only [h, ite_false, ← Finset.mul_sum, hv, mul_one]

theorem avgError_pad [Fintype B] [Fintype B₁] [Fintype M] [DecidableEq M]
    (c : RelayCode M A A₁ B B₁ n) (r : ℕ) (a₀ : A) (a₁ : A₁) (W : DMC (A × A₁) (B × B₁)) :
    (c.pad r a₀ a₁).avgError W = c.avgError W := by
  simp only [avgError, errorProb_pad]

end RelayCode

namespace Relay

variable {A A₁ B B₁ : Type*}

theorem exists_input_decomp [Finite A] [Finite A₁] (p : PMF (A × A₁)) :
    ∃ (pU : PMF A₁) (pX : A₁ → PMF A), pU.bind (fun u => (pX u).map fun x => (x, u)) = p := by
  classical
  have := Fintype.ofFinite A
  have := Fintype.ofFinite A₁
  set q := p.map Prod.swap
  have hτ : ∀ u, (q.map Prod.fst) u = ∑ x, q (u, x) := by
    intro u
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
    simp only
    rw [Finset.sum_eq_single u (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  have hsum : ∀ u, (q.map Prod.fst) u ≠ 0 → ∑ x, q (u, x) / (q.map Prod.fst) u = 1 := by
    intro u hu
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← hτ]
    exact ENNReal.mul_inv_cancel hu (PMF.apply_ne_top _ _)
  let pX : A₁ → PMF A := fun u => if hu : (q.map Prod.fst) u = 0 then q.map Prod.snd
    else PMF.ofFintype (fun x => q (u, x) / (q.map Prod.fst) u) (hsum u hu)
  have hfac : ∀ u x, q (u, x) = (q.map Prod.fst) u * pX u x := by
    intro u x
    by_cases hu : (q.map Prod.fst) u = 0
    · have hle : q (u, x) ≤ (q.map Prod.fst) u := by
        rw [hτ]
        exact Finset.single_le_sum (f := fun x => q (u, x)) (fun _ _ => zero_le)
          (Finset.mem_univ x)
      rw [hu] at hle
      rw [hu, zero_mul]
      exact le_zero_iff.1 hle
    · simp only [pX, hu, dite_false, PMF.ofFintype_apply]
      rw [div_eq_mul_inv, mul_comm (q _), ← mul_assoc,
        ENNReal.mul_inv_cancel hu (PMF.apply_ne_top _ _), one_mul]
  refine ⟨q.map Prod.fst, pX, ?_⟩
  have hj : DMC.jointPMF pX (q.map Prod.fst) = q := by
    ext ⟨u, x⟩
    rw [DMC.jointPMF_apply, hfac]
  have e : (q.map Prod.fst).bind (fun u => (pX u).map fun x => (x, u)) =
      (DMC.jointPMF pX (q.map Prod.fst)).map Prod.swap := by
    simp only [DMC.jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.swap_prod_mk]
  rw [e, hj, PMF.map_comp]
  have : (Prod.swap ∘ Prod.swap : A × A₁ → A × A₁) = id := funext fun _ => rfl
  rw [this, PMF.map_id]

theorem law₁_relayBC (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁) (pX : A₁ → PMF A) :
    BC.law₁ (relayBC W) pU (satLaw pX) =
      (DMC.jointPMF W (pU.bind fun u => (pX u).map fun x => (x, u))).map
        fun ω => ((ω.1.2, (ω.1.2, ω.1.1)), ω.2.2) := by
  simp only [BC.law₁, DMC.jointPMF, BC.channel₁, relayBC, satLaw, PMF.map_bind, PMF.bind_map,
    PMF.bind_bind, PMF.map_comp, Function.comp_def]
  rfl

theorem law₁_destBC (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁) (pX : A₁ → PMF A) :
    BC.law₁ (destBC W) pU (satLaw pX) =
      (DMC.jointPMF W (pU.bind fun u => (pX u).map fun x => (x, u))).map
        fun ω => ((ω.1.2, (ω.1.2, ω.1.1)), ω.2.1) := by
  simp only [BC.law₁, DMC.jointPMF, BC.channel₁, destBC, satLaw, PMF.map_bind, PMF.bind_map,
    PMF.bind_bind, PMF.map_comp, Function.comp_def]

section Info

variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A₁]
  [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [Fintype B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]

omit [Fintype B] in
theorem relayInfo_eq [Finite B] (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁) (pX : A₁ → PMF A) :
    I[fun ω : (A₁ × A₁ × A) × B₁ => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
        (BC.law₁ (relayBC W) pU (satLaw pX)).toMeasure] =
      I[fun ω : (A × A₁) × B × B₁ => ω.1.1 : fun ω => ω.2.2 | fun ω => ω.1.2 ;
        W.jointMeasure (pU.bind fun u => (pX u).map fun x => (x, u))] := by
  set p := pU.bind fun u => (pX u).map fun x => (x, u)
  rw [law₁_relayBC, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    condMutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _),
    condMutualInfo_eq_condEntropy_sub_condEntropy, condMutualInfo_eq_condEntropy_sub_condEntropy]
  congr 1
  exact condEntropy_cond_of_injective _ (Z := fun ω : (A × A₁) × B × B₁ => (ω.1.1, ω.1.2))
    (e := fun t => ((t.2, t.1), t.2)) (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1.2 h.2) fun _ => rfl

omit [Fintype B₁] in
theorem destInfo_eq [Finite B₁] (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁) (pX : A₁ → PMF A) :
    I[fun ω : (A₁ × A₁ × A) × B => ω.1.2 : fun ω => ω.2 ;
        (BC.law₁ (destBC W) pU (satLaw pX)).toMeasure] =
      I[fun ω : (A × A₁) × B × B₁ => ω.1 : fun ω => ω.2.1 ;
        W.jointMeasure (pU.bind fun u => (pX u).map fun x => (x, u))] := by
  rw [law₁_destBC, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    mutualInfo_map _ (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _),
    mutualInfo_comm, mutualInfo_comm (X := fun ω : (A × A₁) × B × B₁ => ω.1)]
  exact mutualInfo_comp_right_of_injective _ (X := fun ω : (A × A₁) × B × B₁ => ω.2.1)
    (Y := fun ω => ω.1) (f := Prod.swap) Prod.swap_injective

end Info

end Relay

namespace Relay

section Trivial

variable {A A₁ B B₁ : Type*}

theorem achievable_of_nonpos [Nonempty A] [Nonempty A₁] [Fintype B] [Fintype B₁]
    (W : DMC (A × A₁) (B × B₁)) {R : ℝ} (hR : R ≤ 0) :
    Achievable W R := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨1, ?_, ⟨fun _ _ => Classical.arbitrary A,
    fun _ _ => Classical.arbitrary A₁, fun _ _ _ _ => rfl, fun _ => 0⟩, ?_⟩⟩
  · rw [Nat.cast_one, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hR
  · have : ∀ m : Fin 1, (⟨fun _ _ => Classical.arbitrary A, fun _ _ => Classical.arbitrary A₁,
        fun _ _ _ _ => rfl, fun _ => 0⟩ : RelayCode (Fin 1) A A₁ B B₁ n).errorProb W m = 0 :=
      fun m => by simp [RelayCode.errorProb, Subsingleton.elim m 0]
    simp [RelayCode.avgError, this]

theorem achievable_mono [Fintype B] [Fintype B₁] (W : DMC (A × A₁) (B × B₁)) {R R' : ℝ}
    (h : Achievable W R') (hRR : R ≤ R') : Achievable W R := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, c, hc⟩ := hN n hn
  exact ⟨k, (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hRR (Nat.cast_nonneg _))).trans hk,
    c, hc⟩

end Trivial

end Relay

namespace Relay

variable {A A₁ B B₁ : Type*}
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Nonempty A₁]
  [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype B₁] [Nonempty B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]

theorem achievable_of_lt_info (W : DMC (A × A₁) (B × B₁)) (pU : PMF A₁) (pX : A₁ → PMF A)
    {R : ℝ} (hR0 : 0 < R)
    (h₁ : R < I[fun ω : (A₁ × A₁ × A) × B₁ => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
        (BC.law₁ (relayBC W) pU (satLaw pX)).toMeasure])
    (h₂ : R < I[fun ω : (A₁ × A₁ × A) × B => ω.1.2 : fun ω => ω.2 ;
        (BC.law₁ (destBC W) pU (satLaw pX)).toMeasure]) :
    Achievable W R := by
  classical
  set I₁ := I[fun ω : (A₁ × A₁ × A) × B₁ => ω.1.2 : fun ω => ω.2 | fun ω => ω.1.1 ;
    (BC.law₁ (relayBC W) pU (satLaw pX)).toMeasure]
  set I₂ := I[fun ω : (A₁ × A₁ × A) × B => ω.1.2 : fun ω => ω.2 ;
    (BC.law₁ (destBC W) pU (satLaw pX)).toMeasure]
  set g := min I₁ I₂ - R with hg
  have hg0 : 0 < g := by rw [hg]; exact sub_pos.2 (lt_min h₁ h₂)
  have hg₁ : g ≤ I₁ - R := by rw [hg]; linarith [min_le_left I₁ I₂]
  have hg₂ : g ≤ I₂ - R := by rw [hg]; linarith [min_le_right I₁ I₂]
  set ε := g / 16
  set R'' := R + g / 2
  set nb : ℕ := ⌈2 * R / g⌉₊ + 1
  have hnb : R < nb * (g / 2) := by
    have h1 : 2 * R / g < nb := by
      have := Nat.le_ceil (2 * R / g)
      have : (⌈2 * R / g⌉₊ : ℝ) + 1 = nb := by simp [nb]
      linarith
    rw [div_lt_iff₀ hg0] at h1
    linarith
  set k : ℕ → ℕ := fun m => ⌈Real.exp (m * R'')⌉₊
  have hk0 : ∀ m, 0 < k m := fun m => Nat.ceil_pos.2 (Real.exp_pos _)
  have hk1 : ∀ m, ((k m : ℕ) : ℝ) - 1 ≤ Real.exp (m * R'') := fun m => by
    linarith [Nat.ceil_lt_add_one (Real.exp_pos (m * R'')).le]
  set L₁ := BC.law₁ (relayBC W) pU (satLaw pX)
  set L₂ := BC.law₁ (destBC W) pU (satLaw pX)
  set U : ℕ → ℝ := fun m =>
    nb * ((1 - ∑ z ∈ superpositionTypicalSet L₁ m ε, iidProb L₁ (fun i => (z.1 i, z.2 i))) +
      Real.exp (m * (R'' - (I₁ - 4 * ε)))) +
    nb * ((1 - ∑ z ∈ superpositionTypicalSet L₂ m ε, iidProb L₂ (fun i => (z.1 i, z.2 i))) +
      Real.exp (m * (R'' - (I₂ - 3 * ε))))
  have hε0 : 0 < ε := by positivity
  have hU : Tendsto U atTop (𝓝 0) := by
    have e₁ : R'' - (I₁ - 4 * ε) < 0 := by simp only [R'', ε]; linarith
    have e₂ : R'' - (I₂ - 3 * ε) < 0 := by simp only [R'', ε]; linarith
    have t₁ := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_superpositionTypicalSet L₁ hε0)
    have t₂ := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_superpositionTypicalSet L₂ hε0)
    have := ((tendsto_const_nhds (x := (nb : ℝ))).mul (t₁.add (tendsto_exp_nat_mul e₁))).add
      ((tendsto_const_nhds (x := (nb : ℝ))).mul (t₂.add (tendsto_exp_nat_mul e₂)))
    simpa using this
  have hbound : ∀ m, dfBound W pU pX ε nb m (Fintype.card (Fin (k m))) ≤ U m := by
    intro m
    rw [dfBound, Fintype.card_fin]
    have hk := hk1 m
    have hk' : (0 : ℝ) ≤ (k m : ℝ) - 1 := by
      have : (1 : ℝ) ≤ k m := by exact_mod_cast hk0 m
      linarith
    have b₁ : ((k m : ℝ) - 1) * Real.exp (-(m * (I₁ - 4 * ε))) ≤
        Real.exp (m * (R'' - (I₁ - 4 * ε))) :=
      calc _ ≤ Real.exp (m * R'') * Real.exp (-(m * (I₁ - 4 * ε))) :=
            mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; ring_nf
    have b₂ : ((k m : ℝ) - 1) * Real.exp (-(m * (I₂ - 3 * ε))) ≤
        Real.exp (m * (R'' - (I₂ - 3 * ε))) :=
      calc _ ≤ Real.exp (m * R'') * Real.exp (-(m * (I₂ - 3 * ε))) :=
            mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; ring_nf
    have hnb0 : (0 : ℝ) ≤ nb := Nat.cast_nonneg _
    simp only [U]
    gcongr
  intro ε' hε'
  obtain ⟨δ, -, hδ0, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε'
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 (hU.eventually (gt_mem_nhds hδ))
  obtain ⟨M₂, hM₂⟩ := exists_nat_gt ((nb + 1) * R / (nb * (g / 2) - R))
  set M₀ := max M₁ M₂
  refine ⟨(nb + 1) * (M₀ + 1), fun n hn => ?_⟩
  obtain ⟨m, r, rfl, hm⟩ : ∃ m r, n = (nb + 1) * m + r ∧ M₀ ≤ m ∧ r < nb + 1 :=
    ⟨n / (nb + 1), n % (nb + 1), (Nat.div_add_mod n (nb + 1)).symm,
      (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith), Nat.mod_lt _ (by omega)⟩
  obtain ⟨hm, hr⟩ := hm
  obtain ⟨Cu, Cx, hc⟩ := exists_dfCode_avgError_le (K := Fin (k m)) (nb := nb) (m := m) W pU pX ε
    ⟨0, hk0 m⟩
  set c := ((dfCode (nb := nb) W pU pX ε ⟨0, hk0 m⟩ Cu Cx).relabel
    (Fintype.equivFin (Fin nb → Fin (k m)))).pad r (Classical.arbitrary A)
      (Classical.arbitrary A₁)
  refine ⟨Fintype.card (Fin nb → Fin (k m)), ?_, c, ?_⟩
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
    have hkm : (m : ℝ) * R'' ≤ Real.log (k m) :=
      (Real.le_log_iff_exp_le (by exact_mod_cast hk0 m)).2 (Nat.le_ceil _)
    have hm₂ : ((nb + 1) * R / (nb * (g / 2) - R) : ℝ) < m := by
      have : (M₂ : ℝ) ≤ m := by exact_mod_cast le_trans (le_max_right _ _) hm
      linarith
    have hpos : 0 < (nb : ℝ) * (g / 2) - R := by linarith
    rw [div_lt_iff₀ hpos] at hm₂
    have hr' : (r : ℝ) ≤ nb := by
      have : r ≤ nb := by omega
      exact_mod_cast this
    have key : ((((nb + 1) * m + r : ℕ) : ℝ)) * R ≤ nb * Real.log (k m) := by
      push_cast
      have : (nb : ℝ) * (m * R'') ≤ nb * Real.log (k m) :=
        mul_le_mul_of_nonneg_left hkm (Nat.cast_nonneg _)
      simp only [R''] at this ⊢
      nlinarith
    calc Real.exp ((((nb + 1) * m + r : ℕ) : ℝ) * R) ≤ Real.exp (nb * Real.log (k m)) :=
          Real.exp_le_exp.2 key
      _ = (k m : ℝ) ^ nb := by
          rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hk0 m)]
  · rw [RelayCode.avgError_pad, RelayCode.avgError_relabel]
    refine hc.trans ((ENNReal.ofReal_le_ofReal ((hbound m).trans (hM₁ m
      (le_trans (le_max_left _ _) hm)).le)).trans hδε.le)

end Relay

namespace Relay

variable {A A₁ B B₁ : Type*}
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  [Fintype A₁] [MeasurableSpace A₁] [MeasurableSingletonClass A₁] [Nonempty A₁]
  [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype B₁] [Nonempty B₁] [MeasurableSpace B₁] [MeasurableSingletonClass B₁]

theorem achievable_of_lt_decodeForwardRate (W : DMC (A × A₁) (B × B₁)) (p : PMF (A × A₁))
    {R : ℝ} (h : R < decodeForwardRate W p) : Achievable W R := by
  by_cases hR : R ≤ 0
  · exact achievable_of_nonpos W hR
  obtain ⟨pU, pX, hp⟩ := exists_input_decomp p
  rw [decodeForwardRate, ← hp] at h
  refine achievable_of_lt_info W pU pX (not_le.1 hR) ?_ ?_
  · rw [relayInfo_eq]
    exact h.trans_le (min_le_right _ _)
  · rw [destInfo_eq]
    exact h.trans_le (min_le_left _ _)

omit [Nonempty A] [Nonempty A₁] [Nonempty B] [Nonempty B₁] in
theorem decodeForwardBound_nonneg (W : DMC (A × A₁) (B × B₁)) : 0 ≤ decodeForwardBound W :=
  Real.iSup_nonneg fun _ => le_min (mutualInfo_nonneg _ (measurable_of_finite _)
    (measurable_of_finite _)) (condMutualInfo_nonneg _ (measurable_of_finite _)
      (measurable_of_finite _) (measurable_of_finite _))

theorem Icc_decodeForwardBound_subset (W : DMC (A × A₁) (B × B₁)) :
    Set.Icc 0 (decodeForwardBound W) ⊆ closure (achievableRates W) := by
  intro R hR
  rcases (decodeForwardBound_nonneg W).eq_or_lt with h | h
  · rw [← h, Set.Icc_self, Set.mem_singleton_iff] at hR
    exact subset_closure ⟨hR.symm ▸ le_rfl, achievable_of_nonpos W hR.le⟩
  · rw [← closure_Ico h.ne] at hR
    refine closure_mono (fun R (hR : R ∈ Set.Ico 0 (decodeForwardBound W)) => ?_) hR
    have hb : BddAbove (Set.range (decodeForwardRate W)) :=
      ⟨_, Set.forall_mem_range.2 fun p =>
        (decodeForwardRate_le_cutSetRate W p).trans (cutSetRate_le_log_card W p)⟩
    obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup (hR.2.trans_eq rfl : R < ⨆ p, decodeForwardRate W p)
    exact ⟨hR.1, achievable_of_lt_decodeForwardRate W p hp⟩

theorem closure_achievableRates_eq_of_isDegraded {W : DMC (A × A₁) (B × B₁)}
    (h : IsDegraded W) : closure (achievableRates W) = Set.Icc 0 (decodeForwardBound W) :=
  le_antisymm (closure_achievableRates_subset_of_isDegraded h) (Icc_decodeForwardBound_subset W)

end Relay

end Meat
