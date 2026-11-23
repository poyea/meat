import Meat.Shannon.Superposition
import Meat.Open.SecretKey

open MeasureTheory Finset
open scoped ENNReal

namespace Meat

namespace SecretKey

open RateDistortion

section Info

variable {Ω A B C D : Type*} [MeasurableSpace Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
  (μ : Measure Ω)

private lemma cmi_pair_eq {X : Ω → A} {Y : Ω → B} {Z : Ω → C} {W : Ω → D} :
    I[X : fun ω => (Y ω, W ω) | Z ; μ] =
      I[X : Y | Z ; μ] + I[X : W | fun ω => (Y ω, Z ω) ; μ] := by
  have e1 : H[fun ω => (X ω, (Y ω, Z ω)) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    (entropy_assoc μ).symm
  have e2 : H[fun ω => (W ω, (Y ω, Z ω)) ; μ] = H[fun ω => ((Y ω, W ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((Y ω, W ω), Z ω))
      (f := fun p => (p.1.2, (p.1.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.2.1 h.1) h.2.2
  have e3 : H[fun ω => ((X ω, W ω), (Y ω, Z ω)) ; μ]
      = H[fun ω => ((X ω, (Y ω, W ω)), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, (Y ω, W ω)), Z ω))
      (f := fun p => ((p.1.1, p.1.2.2), (p.1.2.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 (Prod.ext h.2.1 h.1.2)) h.2.2
  simp only [condMutualInfo_def, condEntropy_def]
  rw [e1, e2, e3]
  ring

private lemma cmi_cond_swap {X : Ω → A} {Y : Ω → B} {Z : Ω → C} {W : Ω → D} :
    I[X : Y | fun ω => (Z ω, W ω) ; μ] = I[X : Y | fun ω => (W ω, Z ω) ; μ] := by
  have h1 : H[fun ω => (X ω, (Z ω, W ω)) ; μ] = H[fun ω => (X ω, (W ω, Z ω)) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, (W ω, Z ω)))
      (f := fun p => (p.1, p.2.swap)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (Prod.swap_injective h.2)
  have h2 : H[fun ω => (Y ω, (Z ω, W ω)) ; μ] = H[fun ω => (Y ω, (W ω, Z ω)) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (Y ω, (W ω, Z ω)))
      (f := fun p => (p.1, p.2.swap)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (Prod.swap_injective h.2)
  have h3 : H[fun ω => ((X ω, Y ω), (Z ω, W ω)) ; μ] = H[fun ω => ((X ω, Y ω), (W ω, Z ω)) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), (W ω, Z ω)))
      (f := fun p => (p.1, p.2.swap)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (Prod.swap_injective h.2)
  have h4 : H[fun ω => (Z ω, W ω) ; μ] = H[fun ω => (W ω, Z ω) ; μ] := entropy_comm μ
  simp only [condMutualInfo_def, condEntropy_def]
  rw [h1, h2, h3, h4]

private lemma cmi_fun_le [IsProbabilityMeasure μ] {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (f : A → C → D) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    I[fun ω => f (X ω) (Z ω) : Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  have hf : Measurable fun ω => (f (X ω) (Z ω), Z ω) :=
    (measurable_of_finite (fun q : A × C => (f q.1 q.2, q.2))).comp (hX.prodMk hZ)
  have h0 := condMutualInfo_nonneg μ hX hY hf
  have r1 : H[fun ω => (X ω, (f (X ω) (Z ω), Z ω)) ; μ] = H[fun ω => (X ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Z ω))
      (f := fun p => (p.1, (f p.1 p.2, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 h.2.2
  have r2 : H[fun ω => (Y ω, (f (X ω) (Z ω), Z ω)) ; μ]
      = H[fun ω => ((f (X ω) (Z ω), Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((f (X ω) (Z ω), Y ω), Z ω))
      (f := fun p => (p.1.2, (p.1.1, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.2.1 h.1) h.2.2
  have r3 : H[fun ω => ((X ω, Y ω), (f (X ω) (Z ω), Z ω)) ; μ]
      = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω))
      (f := fun p => (p.1, (f p.1.1 p.2, p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 h.2.2
  simp only [condMutualInfo_def, condEntropy_def] at h0 ⊢
  rw [r1, r2, r3] at h0
  linarith

end Info

section Iid

variable {A W V : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
  [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

private lemma map_iid (q : PMF A) (n : ℕ) (g : A → W) :
    (iidMeasure q n).map (fun ω i => g (ω i)) = iidMeasure (q.map g) n := by
  classical
  refine Measure.ext_of_singleton fun y => ?_
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top _ _)]
  congr 1
  rw [measureReal_map_singleton, iidMeasure_real_singleton, iidProb_map]
  simp_rw [iidMeasure_real_singleton]

private lemma entropy_iid (q : PMF A) (n : ℕ) (φ : A → W) :
    H[fun ω : Fin n → A => fun i => φ (ω i) ; iidMeasure q n] = n * H[φ ; q.toMeasure] := by
  have h := entropy_iidMeasure (q.map φ) n
  rw [entropy, Measure.map_id'] at h
  rw [entropy, map_iid, h, entropy, PMF.toMeasure_map _ _ (measurable_of_finite φ)]

private lemma entropy_iid_pair (q : PMF A) (n : ℕ) (φ : A → W) (ψ : A → V) :
    H[fun ω : Fin n → A => ((fun i => φ (ω i)), fun i => ψ (ω i)) ; iidMeasure q n]
      = n * H[fun a => (φ a, ψ a) ; q.toMeasure] := by
  rw [← entropy_iid q n (fun a => (φ a, ψ a))]
  exact entropy_comp_of_injective (iidMeasure q n)
    (X := fun ω : Fin n → A => fun i => (φ (ω i), ψ (ω i)))
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => W) (fun _ => V)).injective

end Iid

section DataProcessing

variable {Ω A B C D V : Type*} [MeasurableSpace Ω]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
  [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

private lemma dp {K : Ω → A} {F : Ω → B} {Zs : Ω → C} {Zb : Ω → D} {X : Ω → V}
    (g : V → B × A) (hg : ∀ ω, (F ω, K ω) = g (X ω)) (hX : Measurable X) (hZs : Measurable Zs)
    (hZb : Measurable Zb) (h : I[X : Zb | Zs ; μ] = 0) :
    I[K : fun ω => (Zb ω, F ω) ; μ] ≤ I[K : fun ω => (Zs ω, F ω) ; μ] := by
  have hK : Measurable K := by
    have : K = fun ω => (g (X ω)).2 := funext fun ω => by rw [← hg ω]
    rw [this]
    exact (measurable_of_finite (fun v => (g v).2)).comp hX
  have hF : Measurable F := by
    have : F = fun ω => (g (X ω)).1 := funext fun ω => by rw [← hg ω]
    rw [this]
    exact (measurable_of_finite (fun v => (g v).1)).comp hX
  have a := mutualInfo_pair_eq_add_condMutualInfo μ (X := K) (Y := Zs)
    (Z := fun ω => (Zb ω, F ω))
  have b : I[K : fun ω => (Zs ω, (Zb ω, F ω)) ; μ] = I[K : fun ω => (Zb ω, (Zs ω, F ω)) ; μ] :=
    mutualInfo_comp_right_of_injective μ (X := K) (Y := fun ω => (Zb ω, (Zs ω, F ω)))
      (f := fun q => (q.2.1, (q.1, q.2.2))) fun x y h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)
  have c := mutualInfo_pair_eq_add_condMutualInfo μ (X := K) (Y := Zb)
    (Z := fun ω => (Zs ω, F ω))
  have a0 := condMutualInfo_nonneg μ hK hZs (hZb.prodMk hF)
  have d1 := condMutualInfo_comm μ (X := K) (Y := Zb) (Z := fun ω => (Zs ω, F ω))
  have d2 := cmi_cond_swap μ (X := Zb) (Y := K) (Z := Zs) (W := F)
  have d3 := cmi_pair_eq μ (X := Zb) (Y := F) (W := K) (Z := Zs)
  have d4 := condMutualInfo_nonneg μ hZb hF hZs
  have d5 := condMutualInfo_comm μ (X := Zb) (Y := fun ω => (F ω, K ω)) (Z := Zs)
  have hfun : (fun ω => (F ω, K ω)) = fun ω => (fun v (_ : C) => g v) (X ω) (Zs ω) :=
    funext hg
  have d6 : I[fun ω => (F ω, K ω) : Zb | Zs ; μ] ≤ I[X : Zb | Zs ; μ] := by
    rw [hfun]
    exact cmi_fun_le μ (fun v (_ : C) => g v) hX hZb hZs
  have d7 := condMutualInfo_nonneg μ hK hZb (hZs.prodMk hF)
  linarith

end DataProcessing

section CouplePMF

variable {S T E : Type*} {m : ℕ}

private noncomputable def couple (p : PMF (S × T × E)) (W : E → PMF (Fin m)) :
    PMF ((S × T × E) × Fin m) :=
  p.bind fun a => (W a.2.2).map fun z => (a, z)

private lemma couple_apply [Finite S] [Finite T] [Finite E] (p : PMF (S × T × E))
    (W : E → PMF (Fin m)) (a : S × T × E) (z : Fin m) : couple p W (a, z) = p a * W a.2.2 z := by
  classical
  have := Fintype.ofFinite S
  have := Fintype.ofFinite T
  have := Fintype.ofFinite E
  rw [couple, PMF.bind_apply, tsum_fintype, sum_eq_single a]
  · rw [PMF.map_apply, tsum_fintype, sum_eq_single z]
    · simp
    · intro z' _ hz'
      simp [Ne.symm hz']
    · simp
  · intro a' _ ha'
    rw [PMF.map_apply, tsum_fintype]
    simp [Ne.symm ha']
  · simp

private lemma couple_fst (p : PMF (S × T × E)) (W : E → PMF (Fin m)) :
    (couple p W).map Prod.fst = p := by
  rw [couple, PMF.map_bind]
  simp only [PMF.map_comp]
  conv_rhs => rw [← PMF.bind_pure p]
  congr 1
  funext a
  exact PMF.map_const _ _

private lemma couple_snd (p : PMF (S × T × E)) (W : E → PMF (Fin m)) :
    (couple p W).map (fun b => (b.1.1, b.1.2.1, b.2)) =
      p.bind fun a => (W a.2.2).map fun z => (a.1, a.2.1, z) := by
  rw [couple, PMF.map_bind]
  simp only [PMF.map_comp]
  rfl

end CouplePMF

section Coupling

variable {S T E : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E] {m : ℕ}

private lemma markov_couple (p : PMF (S × T × E)) (W : E → PMF (Fin m)) :
    I[fun b : (S × T × E) × Fin m => (b.1.1, b.1.2.1) : fun b => b.2 | fun b => b.1.2.2 ;
      (couple p W).toMeasure] = 0 := by
  classical
  have hreal : ∀ (Q : (S × T × E) × Fin m → Prop) [DecidablePred Q],
      (couple p W).toMeasure.real {b | Q b} =
        ∑ b, if Q b then (p b.1).toReal * (W b.1.2.2 b.2).toReal else 0 := by
    intro Q _
    rw [measureReal_def, PMF.toMeasure_apply_fintype, ENNReal.toReal_sum fun _ _ =>
      ne_top_of_le_ne_top (PMF.apply_ne_top _ _) (Set.indicator_le_self _ _ _)]
    refine sum_congr rfl fun b _ => ?_
    by_cases hb : Q b
    · simp only [Set.indicator_of_mem (show b ∈ {b | Q b} from hb), hb, ite_true]
      rw [← Prod.mk.eta (p := b), couple_apply, ENNReal.toReal_mul]
    · simp only [Set.indicator_of_notMem (show b ∉ {b | Q b} from hb), hb, ite_false,
        ENNReal.toReal_zero]
  refine (markovChain_iff (measurable_of_finite _) (measurable_of_finite _)
    (measurable_of_finite _)).2 fun v e z => ?_
  rcases v with ⟨x₀, y₀⟩
  have hw : ∀ e', ∑ z', (W e' z').toReal = 1 := fun e' => sum_toReal_pmf_eq_one (W e')
  simp only [hreal, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp only [Finset.sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true,
    ← mul_sum, hw, mul_one]
  rw [mul_assoc]
  congr 1
  rw [mul_sum]
  exact sum_congr rfl fun x _ => by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => mul_comm _ _

private lemma markov_iid (p : PMF (S × T × E)) (W : E → PMF (Fin m)) (n : ℕ) :
    I[fun ω : Fin n → (S × T × E) × Fin m => fun i => ((ω i).1.1, (ω i).1.2.1) :
      fun ω i => (ω i).2 | fun ω i => (ω i).1.2.2 ; iidMeasure (couple p W) n] = 0 := by
  set q := couple p W
  have h0 := markov_couple p W
  rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def] at h0
  have r : H[fun ω : Fin n → (S × T × E) × Fin m =>
      ((fun i => ((ω i).1.1, (ω i).1.2.1), fun i => (ω i).2), fun i => (ω i).1.2.2) ;
        iidMeasure q n] =
      H[fun ω : Fin n → (S × T × E) × Fin m =>
        (fun i => (((ω i).1.1, (ω i).1.2.1), (ω i).2), fun i => (ω i).1.2.2) ;
          iidMeasure q n] :=
    entropy_comp_of_injective (iidMeasure q n)
      (X := fun ω : Fin n → (S × T × E) × Fin m =>
        (fun i => (((ω i).1.1, (ω i).1.2.1), (ω i).2), fun i => (ω i).1.2.2))
      (f := fun t => ((fun i => (t.1 i).1, fun i => (t.1 i).2), t.2)) fun a b h => by
        simp only [Prod.mk.injEq] at h
        refine Prod.ext (funext fun i => Prod.ext (congrFun h.1.1 i) (congrFun h.1.2 i)) h.2
  rw [condMutualInfo_def, condEntropy_def, condEntropy_def, condEntropy_def, r,
    entropy_iid_pair q n (fun b => (b.1.1, b.1.2.1)) (fun b => b.1.2.2),
    entropy_iid_pair q n (fun b => b.2) (fun b => b.1.2.2),
    entropy_iid_pair q n (fun b => ((b.1.1, b.1.2.1), b.2)) (fun b => b.1.2.2),
    entropy_iid q n (fun b => b.1.2.2)]
  linear_combination (n : ℝ) * h0

theorem achievable_eveChannel {p : PMF (S × T × E)} {R : ℝ} (h : Achievable p R)
    (W : E → PMF (Fin m)) :
    Achievable (p.bind fun a => (W a.2.2).map fun z => (a.1, a.2.1, z)) R := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨r, L, k, hk, P, herr, hsec, hunif⟩ := hN n hn
  set q := couple p W
  set ν := iidMeasure q n
  set pr₁ : (Fin n → (S × T × E) × Fin m) → Fin n → S × T × E := fun ω i => (ω i).1
  set pr₂ : (Fin n → (S × T × E) × Fin m) → Fin n → S × T × Fin m :=
    fun ω i => ((ω i).1.1, (ω i).1.2.1, (ω i).2)
  have hpr₁ : Measurable pr₁ := measurable_of_finite _
  have hpr₂ : Measurable pr₂ := measurable_of_finite _
  have h₁ : iidMeasure p n = ν.map pr₁ := by
    rw [show ν.map pr₁ = iidMeasure (q.map Prod.fst) n from map_iid q n Prod.fst, couple_fst]
  have h₂ : iidMeasure (p.bind fun a => (W a.2.2).map fun z => (a.1, a.2.1, z)) n = ν.map pr₂ := by
    rw [show ν.map pr₂ = iidMeasure (q.map fun b => (b.1.1, b.1.2.1, b.2)) n from
      map_iid q n (fun b : (S × T × E) × Fin m => (b.1.1, b.1.2.1, b.2)), couple_snd]
  refine ⟨r, L, k, hk, P, ?_, ?_, ?_⟩
  · rw [h₂, map_measureReal_apply hpr₂ (Set.toFinite _).measurableSet]
    rw [h₁, map_measureReal_apply hpr₁ (Set.toFinite _).measurableSet] at herr
    exact herr
  · rw [h₂, mutualInfo_map ν hpr₂ (measurable_of_finite _) (measurable_of_finite _)]
    rw [h₁, mutualInfo_map ν hpr₁ (measurable_of_finite _) (measurable_of_finite _)] at hsec
    refine le_trans ?_ hsec
    exact dp ν (X := fun ω : Fin n → (S × T × E) × Fin m => fun i => ((ω i).1.1, (ω i).1.2.1))
      (fun v => (P.transcript (fun i => (v i).1) (fun i => (v i).2) r,
        P.keyA (fun i => (v i).1) (P.transcript (fun i => (v i).1) (fun i => (v i).2) r)))
      (fun ω => rfl) (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
      (markov_iid p W n)
  · rw [h₂, entropy_map ν hpr₂ (measurable_of_finite _)]
    rw [h₁, entropy_map ν hpr₁ (measurable_of_finite _)] at hunif
    exact hunif

theorem capacity_le_eveChannel (p : PMF (S × T × E)) (W : E → PMF (Fin m)) :
    capacity p ≤ I[fun ω : S × T × Fin m => ω.1 : fun ω => ω.2.1 | fun ω => ω.2.2 ;
      (p.bind fun a => (W a.2.2).map fun z => (a.1, a.2.1, z)).toMeasure] := by
  refine le_trans ?_ (capacity_le (p.bind fun a => (W a.2.2).map fun z => (a.1, a.2.1, z)))
  exact csSup_le_csSup ⟨_, fun _ hR => le_condMutualInfo_of_achievable hR⟩
    ⟨0, achievable_zero p⟩ fun _ hR => achievable_eveChannel hR W

theorem capacity_le_intrinsicInfo (p : PMF (S × T × E)) : capacity p ≤ intrinsicInfo p :=
  le_csInf ⟨_, 1, fun _ => PMF.pure 0, rfl⟩ (by
    rintro v ⟨m, W, rfl⟩
    exact capacity_le_eveChannel p W)

end Coupling

end SecretKey

end Meat
