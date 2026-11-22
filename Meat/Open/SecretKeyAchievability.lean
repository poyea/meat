import Meat.Shannon.ChainRule
import Meat.Source.SlepianWolfAchievability
import Meat.Open.SecretKey

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Meat

namespace SecretKey

open SWCode SlepianWolf

section Binning

variable {S T E : Type*} [Fintype S] [MeasurableSpace S] [DecidableEq S]
  [Fintype T] [MeasurableSpace T] [DecidableEq T] [Fintype E] [MeasurableSpace E]
  [DecidableEq E] {n : ℕ}

noncomputable def swBound {A B : Type*} [Fintype A] [MeasurableSpace A] [Fintype B]
    [MeasurableSpace B] (q : PMF (A × B)) (n : ℕ) (γ : ℝ) (k₁ k₂ : ℕ) : ℝ :=
  (1 - ∑ xy ∈ jointlyTypicalSet q n γ, iidProb q (fun i => (xy.1 i, xy.2 i))) +
    (Real.exp (n * (measureEntropy q.toMeasure - measureEntropy (q.map Prod.snd).toMeasure
        + 2 * γ)) / k₁ +
      Real.exp (n * (measureEntropy q.toMeasure - measureEntropy (q.map Prod.fst).toMeasure
        + 2 * γ)) / k₂ +
      Real.exp (n * (measureEntropy q.toMeasure + γ)) / (k₁ * k₂))

private lemma exists_le_avg {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 ≤ c)
    (h1 : ∑ _i : ι, c = 1) (F : ι → ℝ) : ∃ i, F i ≤ ∑ j, c * F j := by
  obtain ⟨i, hi⟩ := exists_le_of_sum_mul_le (w := fun _ : ι => c) (f := F) (fun _ => hc) h1
    le_rfl
  exact ⟨i, hi⟩

theorem exists_binning_two (qY : PMF (S × T)) (qZ : PMF (S × E)) (γ : ℝ)
    (dY : (Fin n → S) × (Fin n → T)) (dZ : (Fin n → S) × (Fin n → E)) {k L K₂ K₃ : ℕ}
    (hk : 0 < k) (hL : 0 < L) (hK₂ : 0 < K₂) (hK₃ : 0 < K₃) :
    ∃ κ : (Fin n → S) → Fin k, ∃ f : (Fin n → S) → Fin L, ∃ f₂ : (Fin n → T) → Fin K₂,
      ∃ g₂ : (Fin n → E) → Fin K₃,
        ((binningCode f f₂ (jointlyTypicalSet qY n γ) dY).errorProb qY).toReal +
          ((binningCode (fun x => finProdFinEquiv (κ x, f x)) g₂ (jointlyTypicalSet qZ n γ)
            dZ).errorProb qZ).toReal
          ≤ swBound qY n γ L K₂ + swBound qZ n γ (k * L) K₃ := by
  have hkL : 0 < k * L := Nat.mul_pos hk hL
  have hBob := sum_errorProb_binningCode_le qY γ dY hL hK₂
  have hEve := sum_errorProb_binningCode_le qZ γ dZ hkL hK₃
  set cA := ∏ _x : Fin n → S, (k : ℝ)⁻¹
  set cB := ∏ _x : Fin n → S, (L : ℝ)⁻¹
  set cC := ∏ _y : Fin n → T, (K₂ : ℝ)⁻¹
  set cD := ∏ _z : Fin n → E, (K₃ : ℝ)⁻¹
  set cG := ∏ _x : Fin n → S, ((k * L : ℕ) : ℝ)⁻¹
  set bob : ((Fin n → S) → Fin L) → ((Fin n → T) → Fin K₂) → ℝ := fun f f₂ =>
    ((binningCode f f₂ (jointlyTypicalSet qY n γ) dY).errorProb qY).toReal
  set eve : ((Fin n → S) → Fin (k * L)) → ((Fin n → E) → Fin K₃) → ℝ := fun g g₂ =>
    ((binningCode g g₂ (jointlyTypicalSet qZ n γ) dZ).errorProb qZ).toReal
  set pr : ((Fin n → S) → Fin k) → ((Fin n → S) → Fin L) → (Fin n → S) → Fin (k * L) :=
    fun κ f x => finProdFinEquiv (κ x, f x)
  have hA : ∑ _κ : (Fin n → S) → Fin k, cA = 1 := sum_uniform hk
  have hB : ∑ _f : (Fin n → S) → Fin L, cB = 1 := sum_uniform hL
  have hC : ∑ _f : (Fin n → T) → Fin K₂, cC = 1 := sum_uniform hK₂
  have hD : ∑ _g : (Fin n → E) → Fin K₃, cD = 1 := sum_uniform hK₃
  have hAD : ∑ _q : ((Fin n → S) → Fin k) × ((Fin n → E) → Fin K₃), cA * cD = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [sum_const, card_univ, nsmul_eq_mul] at hA hD ⊢
    linear_combination (↑(Fintype.card ((Fin n → E) → Fin K₃)) * cD) * hA + hD
  have hcG : cA * cB = cG := by
    simp only [cA, cB, cG, ← prod_mul_distrib, Nat.cast_mul, mul_inv]
  set Φ : ((Fin n → S) → Fin L) → ℝ := fun f => ∑ f₂, cC * bob f f₂
  set Ψ : ((Fin n → S) → Fin L) → ℝ := fun f => ∑ q : ((Fin n → S) → Fin k) ×
    ((Fin n → E) → Fin K₃), (cA * cD) * eve (pr q.1 f) q.2
  have hΦ : ∑ f, cB * Φ f ≤ swBound qY n γ L K₂ := by
    refine le_of_eq_of_le ?_ hBob
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun f _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun f₂ _ => by ring
  have hΨ : ∑ f, cB * Ψ f ≤ swBound qZ n γ (k * L) K₃ := by
    refine le_of_eq_of_le ?_ hEve
    have e : ∀ F : ((Fin n → S) → Fin (k * L)) → ℝ, ∑ g, F g =
        ∑ q : ((Fin n → S) → Fin k) × ((Fin n → S) → Fin L), F (pr q.1 q.2) := fun F =>
      (Equiv.sum_comp ((Equiv.arrowProdEquivProdArrow _ _ _).symm.trans
        (Equiv.arrowCongr (Equiv.refl _) finProdFinEquiv)) F).symm
    rw [Fintype.sum_prod_type, e, Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun f _ => ?_
    simp only [Ψ, Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun κ _ => sum_congr rfl fun g₂ _ => ?_
    rw [← hcG]
    ring
  obtain ⟨f, hf⟩ := exists_le_avg (by positivity) hB (fun f => Φ f + Ψ f)
  obtain ⟨f₂, hf₂⟩ := exists_le_avg (by positivity) hC (bob f)
  obtain ⟨q, hq⟩ := exists_le_avg (by positivity) hAD (fun q => eve (pr q.1 f) q.2)
  refine ⟨q.1, f, f₂, q.2, ?_⟩
  have hsum : ∑ f, cB * (Φ f + Ψ f) = ∑ f, cB * Φ f + ∑ f, cB * Ψ f := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun _ _ => mul_add _ _ _
  change bob f f₂ + eve (pr q.1 f) q.2 ≤ _
  linarith

end Binning

section Protocol

variable {S T E : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [DecidableEq S] [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] [DecidableEq T]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E] [DecidableEq E] {n : ℕ}

open RateDistortion

omit [DecidableEq T] [DecidableEq E] in
private lemma measureReal_le_errorProb {W M₁ M₂ : Type*} [Fintype W] [DecidableEq W]
    (p : PMF (S × T × E)) (g : S × T × E → S × W) (c : SWCode M₁ M₂ S W n)
    (Q : (Fin n → S × T × E) → Prop)
    (hQ : ∀ ω, Q ω → c.dec (c.enc₁ (fun i => (g (ω i)).1), c.enc₂ (fun i => (g (ω i)).2)) ≠
      (fun i => (g (ω i)).1, fun i => (g (ω i)).2)) :
    (iidMeasure p n).real {ω | Q ω} ≤ (c.errorProb (p.map g)).toReal := by
  classical
  set D : (Fin n → S) × (Fin n → W) → ℝ := fun xy =>
    if c.dec (c.enc₁ xy.1, c.enc₂ xy.2) = xy then 0 else 1
  have h1 : (iidMeasure p n).real {ω | Q ω} ≤ (iidMeasure p n).real
      {ω | c.dec (c.enc₁ (fun i => (g (ω i)).1), c.enc₂ (fun i => (g (ω i)).2)) ≠
        (fun i => (g (ω i)).1, fun i => (g (ω i)).2)} := measureReal_mono fun ω h => hQ ω h
  have h2 : (iidMeasure p n).real
      {ω | c.dec (c.enc₁ (fun i => (g (ω i)).1), c.enc₂ (fun i => (g (ω i)).2)) ≠
        (fun i => (g (ω i)).1, fun i => (g (ω i)).2)} =
      ∑ ω, iidProb p ω * D (fun i => (g (ω i)).1, fun i => (g (ω i)).2) := by
    rw [← Finset.coe_filter_univ, ← sum_measureReal_singleton, sum_filter]
    refine sum_congr rfl fun ω _ => ?_
    simp only [D, iidMeasure_real_singleton]
    split_ifs <;> simp_all
  have h3 := sum_iidProb_mul_comp p g (fun y => D (fun i => (y i).1, fun i => (y i).2))
  have h4 : ∑ y : Fin n → S × W, iidProb (p.map g) y * D (fun i => (y i).1, fun i => (y i).2) =
      ∑ xy : (Fin n → S) × (Fin n → W), D xy * iidProb (p.map g) (fun i => (xy.1 i, xy.2 i)) := by
    rw [← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => S) fun _ => W).symm]
    exact sum_congr rfl fun xy _ => mul_comm _ _
  rw [errorProb_toReal]
  exact h1.trans (le_of_eq (h2.trans (h3.trans h4)))

omit [DecidableEq S] [DecidableEq T] [DecidableEq E] in
private lemma entropy_iid_map {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (p : PMF (S × T × E)) (n : ℕ) (φ : S × T × E → W) :
    H[fun ω : Fin n → S × T × E => fun i => φ (ω i) ; iidMeasure p n]
      = n * H[φ ; p.toMeasure] := by
  classical
  rw [entropy_def, entropy, PMF.toMeasure_map _ _ (measurable_of_finite φ),
    ← sum_negMulLog_iidProb]
  refine sum_congr rfl fun y _ => congrArg Real.negMulLog ?_
  rw [measureReal_map_singleton, iidProb_map]
  simp_rw [iidMeasure_real_singleton]

omit [DecidableEq S] [DecidableEq T] [DecidableEq E] in
private lemma entropy_iid_pair {V W : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    (p : PMF (S × T × E)) (n : ℕ) (φ : S × T × E → V) (ψ : S × T × E → W) :
    H[fun ω : Fin n → S × T × E => ((fun i => φ (ω i)), fun i => ψ (ω i)) ; iidMeasure p n]
      = n * H[fun a => (φ a, ψ a) ; p.toMeasure] := by
  rw [← entropy_iid_map p n (fun a => (φ a, ψ a))]
  exact entropy_comp_of_injective (iidMeasure p n)
    (X := fun ω : Fin n → S × T × E => fun i => (φ (ω i), ψ (ω i)))
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => V) (fun _ => W)).injective

private def proto {k L : ℕ} (κ : (Fin n → S) → Fin k) (f : (Fin n → S) → Fin L)
    (dB : (Fin n → T) → Fin L → Fin n → S) (m₀ : Fin L) : SKProtocol S T n 1 L k :=
  ⟨fun _ x _ => f x, fun _ _ _ => m₀, fun x _ => κ x, fun y τ => κ (dB y (τ 0))⟩

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq S] [Fintype T]
  [MeasurableSpace T] [MeasurableSingletonClass T] [DecidableEq T] [Fintype E]
  [MeasurableSpace E] [MeasurableSingletonClass E] [DecidableEq E] in
private lemma proto_pub {k L : ℕ} (κ : (Fin n → S) → Fin k) (f : (Fin n → S) → Fin L)
    (dB : (Fin n → T) → Fin L → Fin n → S) (m₀ : Fin L) (ω : Fin n → S × T × E) :
    (proto κ f dB m₀).pub ω = Fin.snoc (α := fun _ => Fin L) Fin.elim0 (f fun i => (ω i).1) := by
  simp [SKProtocol.pub, SKProtocol.transcript, proto]

omit [DecidableEq S] [DecidableEq T] [DecidableEq E] in
private lemma proto_secrecy (p : PMF (S × T × E)) {k L : ℕ} (κ : (Fin n → S) → Fin k)
    (f : (Fin n → S) → Fin L) (dB : (Fin n → T) → Fin L → Fin n → S) (m₀ : Fin L)
    (dE : (Fin L × Fin k) × (Fin n → E) → Fin n → S) :
    max (I[(proto κ f dB m₀).keyAlice : fun ω => (eveSeq ω, (proto κ f dB m₀).pub ω) ;
        iidMeasure p n])
      (Real.log k - H[(proto κ f dB m₀).keyAlice ; iidMeasure p n]) ≤
      Real.log k + Real.log L -
        n * (H[fun a : S × T × E => (a.1, a.2.2) ; p.toMeasure] -
          H[fun a : S × T × E => a.2.2 ; p.toMeasure]) + Real.log 2 +
        (iidMeasure p n).real {ω | dE ((f fun i => (ω i).1, κ fun i => (ω i).1),
          fun i => (ω i).2.2) ≠ fun i => (ω i).1} * (n * Real.log (Fintype.card S)) := by
  classical
  set μ := iidMeasure p n
  set P := proto κ f dB m₀
  set X : (Fin n → S × T × E) → Fin n → S := fun ω i => (ω i).1
  set Z : (Fin n → S × T × E) → Fin n → E := fun ω i => (ω i).2.2
  set Fm : (Fin n → S × T × E) → Fin L := fun ω => f (X ω)
  set K : (Fin n → S × T × E) → Fin k := fun ω => κ (X ω)
  set G : (Fin n → S × T × E) → Fin L × Fin k := fun ω => (Fm ω, K ω)
  have hX : Measurable X := measurable_of_finite _
  have hZ : Measurable Z := measurable_of_finite _
  have hK : Measurable K := measurable_of_finite _
  have hF : Measurable Fm := measurable_of_finite _
  have hKA : P.keyAlice = K := rfl
  have s1 : H[fun ω => (G ω, X ω) | Z ; μ] = H[X | Z ; μ] :=
    condEntropy_comp_of_injective μ (X := X) (f := fun x => ((f x, κ x), x))
      fun a b h => congrArg Prod.snd h
  have s2 : H[fun ω => (G ω, X ω) | Z ; μ] = H[G | Z ; μ] + H[X | fun ω => (G ω, Z ω) ; μ] :=
    condEntropy_pair_eq_add μ
  have s3 : H[G | Z ; μ] = H[Fm | Z ; μ] + H[K | fun ω => (Fm ω, Z ω) ; μ] :=
    condEntropy_pair_eq_add μ
  have s4 : H[Fm | Z ; μ] ≤ Real.log L := by
    have := entropy_le_log_card μ (X := Fm)
    rw [Fintype.card_fin] at this
    exact (condEntropy_le_entropy μ hF hZ).trans this
  have s5 : H[K | fun ω => (eveSeq ω, P.pub ω) ; μ] = H[K | fun ω => (Fm ω, Z ω) ; μ] :=
    condEntropy_cond_of_injective μ
      (e := fun q : Fin L × (Fin n → E) => (q.2, Fin.snoc (α := fun _ => Fin L) Fin.elim0 q.1))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        have h2 := congrFun h.2 (Fin.last 0)
        simp only [Fin.snoc_last] at h2
        exact Prod.ext h2 h.1)
      fun ω => Prod.ext rfl (proto_pub κ f dB m₀ ω)
  have s6 := condEntropy_le_log_two_add_mul_log_card (μ := μ) hX
    ((measurable_of_finite (fun ω => G ω)).prodMk hZ) dE
  have hcard : Real.log (Fintype.card (Fin n → S)) = n * Real.log (Fintype.card S) := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  rw [hcard] at s6
  have s7 : H[X | Z ; μ] = n * (H[fun a : S × T × E => (a.1, a.2.2) ; p.toMeasure] -
      H[fun a : S × T × E => a.2.2 ; p.toMeasure]) := by
    rw [condEntropy_def, mul_sub]
    congr 1
    · exact entropy_iid_pair p n (fun a => a.1) (fun a => a.2.2)
    · exact entropy_iid_map p n (fun a => a.2.2)
  have s8 := entropy_le_log_card μ (X := K)
  rw [Fintype.card_fin] at s8
  have s9 := condEntropy_le_entropy μ hK (measurable_of_finite fun ω => (eveSeq ω, P.pub ω))
  have s10 := mutualInfo_eq_entropy_sub_condEntropy K (fun ω => (eveSeq ω, P.pub ω)) μ
  have hset : {ω | dE ((f fun i => (ω i).1, κ fun i => (ω i).1), fun i => (ω i).2.2) ≠
      fun i => (ω i).1} = {ω | dE (G ω, Z ω) ≠ X ω} := rfl
  rw [hKA, hset]
  refine max_le ?_ ?_
  · rw [s10]
    linarith
  · linarith

end Protocol

section Main

variable {S T E : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]

open RateDistortion

private lemma exp_div_le {x y K : ℝ} (hK : Real.exp x ≤ K) :
    Real.exp y / K ≤ Real.exp (y - x) := by
  rw [Real.exp_sub]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hK

private lemma ceil_exp {a : ℝ} (ha : 0 ≤ a) :
    0 < ⌈Real.exp a⌉₊ ∧ Real.exp a ≤ ⌈Real.exp a⌉₊ ∧
      Real.log ⌈Real.exp a⌉₊ ≤ Real.log 2 + a := by
  have h1 : 1 ≤ Real.exp a := Real.one_le_exp ha
  have hpos : 0 < ⌈Real.exp a⌉₊ := Nat.ceil_pos.2 (Real.exp_pos a)
  have hle : Real.exp a ≤ ⌈Real.exp a⌉₊ := Nat.le_ceil _
  have hlt : (⌈Real.exp a⌉₊ : ℝ) < Real.exp a + 1 := Nat.ceil_lt_add_one (Real.exp_pos a).le
  refine ⟨hpos, hle, ?_⟩
  calc Real.log ⌈Real.exp a⌉₊ ≤ Real.log (2 * Real.exp a) :=
        Real.log_le_log (Nat.cast_pos.2 hpos) (by linarith)
    _ = Real.log 2 + a := by rw [Real.log_mul two_ne_zero (Real.exp_pos a).ne', Real.log_exp]

private lemma swBound_le {A B : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (q : PMF (A × B)) {n : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 4) {k₁ k₂ : ℕ}
    (hk₁ : Real.exp (n * (measureEntropy q.toMeasure - measureEntropy (q.map Prod.snd).toMeasure
      + 4 * γ)) ≤ k₁)
    (hk₂ : Real.exp (n * (Real.log (Fintype.card B) + 1)) ≤ k₂) :
    swBound q n γ k₁ k₂ ≤
      (1 - ∑ xy ∈ jointlyTypicalSet q n γ, iidProb q (fun i => (xy.1 i, xy.2 i))) +
        3 * Real.exp (n * -γ) := by
  set H := measureEntropy q.toMeasure
  set H₁ := measureEntropy (q.map Prod.fst).toMeasure
  set H₂ := measureEntropy (q.map Prod.snd).toMeasure
  set cB := Real.log (Fintype.card B)
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hB₁ : H - H₁ ≤ cB := by
    rw [← condEntropy_snd_fst_toMeasure]
    exact (condEntropy_le_entropy _ measurable_snd measurable_fst).trans
      (entropy_le_log_card _)
  have hB₂ : H₂ ≤ cB := by
    have := entropy_le_log_card q.toMeasure (X := Prod.snd)
    rw [entropy] at this
    rwa [show H₂ = measureEntropy (q.map Prod.snd).toMeasure from rfl,
      ← PMF.toMeasure_map _ _ measurable_snd]
  have hk₁0 : 0 < (k₁ : ℝ) := (Real.exp_pos _).trans_le hk₁
  have hk₂0 : 0 < (k₂ : ℝ) := (Real.exp_pos _).trans_le hk₂
  have t1 : Real.exp (n * (H - H₂ + 2 * γ)) / k₁ ≤ Real.exp (n * -γ) :=
    (exp_div_le hk₁).trans (Real.exp_le_exp.2 (by nlinarith))
  have t2 : Real.exp (n * (H - H₁ + 2 * γ)) / k₂ ≤ Real.exp (n * -γ) :=
    (exp_div_le hk₂).trans (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hB₁ hn]))
  have hk12 : Real.exp (n * (H - H₂ + 4 * γ) + n * (cB + 1)) ≤ (k₁ : ℝ) * k₂ := by
    rw [Real.exp_add]
    exact mul_le_mul hk₁ hk₂ (Real.exp_pos _).le hk₁0.le
  have t3 : Real.exp (n * (H + γ)) / (k₁ * k₂) ≤ Real.exp (n * -γ) :=
    (exp_div_le hk12).trans (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hB₂ hn]))
  unfold swBound
  linarith

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass E] in
private lemma achievable_mono {p : PMF (S × T × E)} {R R' : ℝ} (h : Achievable p R)
    (hR : R' ≤ R) : Achievable p R' := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨r, L, k, hk, P, h1, h2, h3⟩ := hN n hn
  exact ⟨r, L, k, (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith)
    n.cast_nonneg)).trans hk, P, h1, h2, h3⟩

theorem achievable_of_lt {p : PMF (S × T × E)} {R : ℝ}
    (h : R < I[fun a : S × T × E => a.1 : fun a => a.2.1 ; p.toMeasure] -
      I[fun a : S × T × E => a.1 : fun a => a.2.2 ; p.toMeasure]) : Achievable p R := by
  classical
  rcases le_or_gt R 0 with hR | hR
  · exact achievable_mono (achievable_zero p) hR
  set gY : S × T × E → S × T := fun a => (a.1, a.2.1)
  set gZ : S × T × E → S × E := fun a => (a.1, a.2.2)
  set qY := p.map gY with hqY
  set qZ := p.map gZ with hqZ
  set Hy := measureEntropy qY.toMeasure - measureEntropy (qY.map Prod.snd).toMeasure with hHy'
  set Hz := measureEntropy qZ.toMeasure - measureEntropy (qZ.map Prod.snd).toMeasure with hHz'
  have hHy : Hy = H[fun a : S × T × E => (a.1, a.2.1) ; p.toMeasure] -
      H[fun a : S × T × E => a.2.1 ; p.toMeasure] := by
    rw [hHy', hqY, PMF.map_comp, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
      ← PMF.toMeasure_map _ _ (measurable_of_finite _)]
    rfl
  have hHz : Hz = H[fun a : S × T × E => (a.1, a.2.2) ; p.toMeasure] -
      H[fun a : S × T × E => a.2.2 ; p.toMeasure] := by
    rw [hHz', hqZ, PMF.map_comp, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
      ← PMF.toMeasure_map _ _ (measurable_of_finite _)]
    rfl
  have hgap : R < Hz - Hy := by
    rw [hHy, hHz]
    rw [mutualInfo_def, mutualInfo_def] at h
    linarith
  have hHy0 : 0 ≤ Hy := by
    rw [hHy', ← condEntropy_fst_snd_toMeasure]
    exact condEntropy_nonneg _ measurable_fst measurable_snd
  intro ε hε
  set γ := min (ε / 32) (1 / 4) with hγdef
  have hγ0 : 0 < γ := lt_min (by positivity) (by norm_num)
  have hγ1 : γ ≤ 1 / 4 := min_le_right _ _
  have hγε : γ ≤ ε / 32 := min_le_left _ _
  set cS := Real.log (Fintype.card S)
  have hcS : 0 ≤ cS := Real.log_natCast_nonneg _
  set δ := min (ε / 2) (ε / (4 * (cS + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ ε := (min_le_left _ _).trans (by linarith)
  have hδ2 : δ * cS ≤ ε / 4 := by
    have h' : δ ≤ ε / (4 * (cS + 1)) := min_le_right _ _
    calc δ * cS ≤ ε / (4 * (cS + 1)) * cS := mul_le_mul_of_nonneg_right h' hcS
      _ ≤ ε / 4 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hsum : Tendsto (fun n : ℕ =>
      ((1 - ∑ xy ∈ jointlyTypicalSet qY n γ, iidProb qY (fun i => (xy.1 i, xy.2 i))) +
        3 * Real.exp (n * -γ)) +
      ((1 - ∑ xy ∈ jointlyTypicalSet qZ n γ, iidProb qZ (fun i => (xy.1 i, xy.2 i))) +
        3 * Real.exp (n * -γ))) atTop (𝓝 0) := by
    have he := tendsto_exp_nat_mul (c := -γ) (by linarith)
    have := (((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_sum_iidProb_jointlyTypicalSet qY hγ0)).add
      (he.const_mul 3)).add (((tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_sum_iidProb_jointlyTypicalSet qZ hγ0)).add (he.const_mul 3))
    simpa using this
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ0))
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (12 * Real.log 2 / ε)
  obtain ⟨st, -⟩ := p.support_nonempty
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hlog2 : 12 * Real.log 2 < n * ε := by
    rw [← div_lt_iff₀ hε]
    exact hN₂.trans_le (by exact_mod_cast (le_max_right N₁ N₂).trans hn)
  obtain ⟨hL0, hLe, hLlog⟩ := ceil_exp (a := n * (Hy + 4 * γ)) (mul_nonneg hn0 (by linarith))
  obtain ⟨hk0, hke, hklog⟩ := ceil_exp (a := n * (Hz - Hy)) (mul_nonneg hn0 (by linarith))
  obtain ⟨hK₂0, hK₂e, -⟩ := ceil_exp (a := n * (Real.log (Fintype.card T) + 1))
    (mul_nonneg hn0 (by positivity))
  obtain ⟨hK₃0, hK₃e, -⟩ := ceil_exp (a := n * (Real.log (Fintype.card E) + 1))
    (mul_nonneg hn0 (by positivity))
  set L := ⌈Real.exp (n * (Hy + 4 * γ))⌉₊
  set k := ⌈Real.exp (n * (Hz - Hy))⌉₊
  set K₂ := ⌈Real.exp (n * (Real.log (Fintype.card T) + 1))⌉₊
  set K₃ := ⌈Real.exp (n * (Real.log (Fintype.card E) + 1))⌉₊
  set dY : (Fin n → S) × (Fin n → T) := (fun _ => st.1, fun _ => st.2.1)
  set dZ : (Fin n → S) × (Fin n → E) := (fun _ => st.1, fun _ => st.2.2)
  obtain ⟨κ, f, f₂, g₂, hbin⟩ := exists_binning_two qY qZ γ dY dZ hk0 hL0 hK₂0 hK₃0
  have hY := swBound_le qY hγ0.le hγ1 (n := n) (k₁ := L) (k₂ := K₂) hLe hK₂e
  have hkL : Real.exp (n * (Hz + 4 * γ)) ≤ ((k * L : ℕ) : ℝ) := by
    rw [Nat.cast_mul, show n * (Hz + 4 * γ) = n * (Hz - Hy) + n * (Hy + 4 * γ) by ring,
      Real.exp_add]
    exact mul_le_mul hke hLe (Real.exp_pos _).le (Nat.cast_nonneg _)
  have hZ := swBound_le qZ hγ0.le hγ1 (n := n) (k₁ := k * L) (k₂ := K₃) hkL hK₃e
  have hb := hN₁ n ((le_max_left N₁ N₂).trans hn)
  set pr : (Fin n → S) → Fin (k * L) := fun x => finProdFinEquiv (κ x, f x)
  have hbob0 := (ENNReal.toReal_nonneg (a :=
    (binningCode f f₂ (jointlyTypicalSet qY n γ) dY).errorProb qY))
  have heve0 := (ENNReal.toReal_nonneg (a :=
    (binningCode pr g₂ (jointlyTypicalSet qZ n γ) dZ).errorProb qZ))
  set dB : (Fin n → T) → Fin L → Fin n → S := fun y m =>
    (typicalDecoder f f₂ (jointlyTypicalSet qY n γ) dY (m, f₂ y)).1
  set dE : (Fin L × Fin k) × (Fin n → E) → Fin n → S := fun q =>
    (typicalDecoder pr g₂ (jointlyTypicalSet qZ n γ) dZ (finProdFinEquiv (q.1.2, q.1.1),
      g₂ q.2)).1
  set m₀ : Fin L := ⟨0, hL0⟩
  have hPe := measureReal_le_errorProb p gY (binningCode f f₂ (jointlyTypicalSet qY n γ) dY)
    (fun ω => (proto κ f dB m₀).keyAlice ω ≠ (proto κ f dB m₀).keyBob ω) fun ω hne heq => by
      apply hne
      have hp0 : (proto κ f dB m₀).pub ω 0 = f fun i => (ω i).1 := by
        rw [proto_pub]
        rfl
      change κ (fun i => (ω i).1) = κ (dB (fun i => (ω i).2.1) ((proto κ f dB m₀).pub ω 0))
      rw [hp0]
      exact congrArg κ (congrArg Prod.fst heq).symm
  have hPeE := measureReal_le_errorProb p gZ (binningCode pr g₂ (jointlyTypicalSet qZ n γ) dZ)
    (fun ω => dE ((f fun i => (ω i).1, κ fun i => (ω i).1), fun i => (ω i).2.2) ≠
      fun i => (ω i).1) fun ω hne heq => hne (congrArg Prod.fst heq)
  have hps := proto_secrecy p κ f dB m₀ dE
  rw [← hHz] at hps
  have hEv : (iidMeasure p n).real {ω | dE ((f fun i => (ω i).1, κ fun i => (ω i).1),
      fun i => (ω i).2.2) ≠ fun i => (ω i).1} ≤ δ := by
    change _ ≤ _ at hPeE
    linarith
  have hEv' := mul_le_mul_of_nonneg_right hEv (mul_nonneg hn0 hcS)
  have hδn := mul_le_mul_of_nonneg_left hδ2 hn0
  have hγn := mul_le_mul_of_nonneg_left hγε hn0
  have hB : (iidMeasure p n).real {ω | (proto κ f dB m₀).keyAlice ω ≠
      (proto κ f dB m₀).keyBob ω} ≤ ε := by
    change _ ≤ _ at hPe
    linarith
  have hbound : Real.log k + Real.log L - n * Hz + Real.log 2 +
      (iidMeasure p n).real {ω | dE ((f fun i => (ω i).1, κ fun i => (ω i).1),
        fun i => (ω i).2.2) ≠ fun i => (ω i).1} * (n * cS) ≤ n * ε := by
    nlinarith
  refine ⟨1, L, k, ?_, proto κ f dB m₀, hB, ((le_max_left _ _).trans hps).trans hbound,
    ((le_max_right _ _).trans hps).trans hbound⟩
  exact (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hn0)).trans hke

theorem sub_le_capacity (p : PMF (S × T × E)) :
    I[fun a : S × T × E => a.1 : fun a => a.2.1 ; p.toMeasure] -
      I[fun a : S × T × E => a.1 : fun a => a.2.2 ; p.toMeasure] ≤ capacity p := by
  by_contra hlt
  obtain ⟨R, hR1, hR2⟩ := exists_between (lt_of_not_ge hlt)
  exact absurd (le_csSup ⟨_, fun _ hR => le_condMutualInfo_of_achievable hR⟩
    (achievable_of_lt hR2)) (not_le.2 hR1)

end Main

end SecretKey

end Meat
