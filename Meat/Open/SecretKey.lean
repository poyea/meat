import Meat.Shannon.Fano
import Meat.Shannon.Superposition
import Meat.Source.RateDistortionConverse

open MeasureTheory Finset

namespace Meat

structure SKProtocol (S T : Type*) (n r L k : ℕ) where
  alice : (j : ℕ) → (Fin n → S) → (Fin j → Fin L) → Fin L
  bob : (j : ℕ) → (Fin n → T) → (Fin j → Fin L) → Fin L
  keyA : (Fin n → S) → (Fin r → Fin L) → Fin k
  keyB : (Fin n → T) → (Fin r → Fin L) → Fin k

namespace SKProtocol

variable {S T E : Type*} {n r L k : ℕ}

def transcript (P : SKProtocol S T n r L k) (x : Fin n → S) (y : Fin n → T) :
    (j : ℕ) → Fin j → Fin L
  | 0 => Fin.elim0
  | j + 1 => Fin.snoc (α := fun _ => Fin L) (P.transcript x y j)
      (if Even j then P.alice j x (P.transcript x y j) else P.bob j y (P.transcript x y j))

def pub (P : SKProtocol S T n r L k) (ω : Fin n → S × T × E) : Fin r → Fin L :=
  P.transcript (fun i => (ω i).1) (fun i => (ω i).2.1) r

def keyAlice (P : SKProtocol S T n r L k) (ω : Fin n → S × T × E) : Fin k :=
  P.keyA (fun i => (ω i).1) (P.pub ω)

def keyBob (P : SKProtocol S T n r L k) (ω : Fin n → S × T × E) : Fin k :=
  P.keyB (fun i => (ω i).2.1) (P.pub ω)

end SKProtocol

namespace SecretKey

variable {S T E : Type*}

def eveSeq {n : ℕ} (ω : Fin n → S × T × E) : Fin n → E := fun i => (ω i).2.2

def Achievable [Fintype S] [MeasurableSpace S] [Fintype T] [MeasurableSpace T] [Fintype E]
    [MeasurableSpace E] (p : PMF (S × T × E)) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ r L k : ℕ, Real.exp (n * (R - ε)) ≤ k ∧
    ∃ P : SKProtocol S T n r L k,
      (RateDistortion.iidMeasure p n).real {ω | P.keyAlice ω ≠ P.keyBob ω} ≤ ε ∧
      I[P.keyAlice : fun ω => (eveSeq ω, P.pub ω) ; RateDistortion.iidMeasure p n] ≤ n * ε ∧
      Real.log k - H[P.keyAlice ; RateDistortion.iidMeasure p n] ≤ n * ε

variable [Fintype S] [MeasurableSpace S] [Fintype T] [MeasurableSpace T] [Fintype E]
  [MeasurableSpace E]

noncomputable def capacity (p : PMF (S × T × E)) : ℝ :=
  sSup {R | Achievable p R}

noncomputable def intrinsicInfo (p : PMF (S × T × E)) : ℝ :=
  sInf {v | ∃ (m : ℕ) (W : E → PMF (Fin m)),
    v = I[fun ω : S × T × Fin m => ω.1 : fun ω => ω.2.1 | fun ω => ω.2.2 ;
      (p.bind fun a => (W a.2.2).map fun z => (a.1, a.2.1, z)).toMeasure]}

end SecretKey

def BoundInformationProblem : Prop :=
  ∃ (S T E : Type) (_ : Fintype S) (_ : MeasurableSpace S) (_ : MeasurableSingletonClass S)
    (_ : Fintype T) (_ : MeasurableSpace T) (_ : MeasurableSingletonClass T)
    (_ : Fintype E) (_ : MeasurableSpace E) (_ : MeasurableSingletonClass E)
    (p : PMF (S × T × E)), 0 < SecretKey.intrinsicInfo p ∧ SecretKey.capacity p = 0

namespace SecretKey

section Info

variable {Ω A B C D B' : Type*} [MeasurableSpace Ω]
  [Fintype B'] [MeasurableSpace B'] [MeasurableSingletonClass B']
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
  (μ : Measure Ω) {X : Ω → A} {Y : Ω → B} {Z : Ω → C}

private lemma condMutualInfo_cond_inj {e : C → D} (he : Function.Injective e) :
    I[X : Y | fun ω => e (Z ω) ; μ] = I[X : Y | Z ; μ] := by
  have h1 : H[fun ω => (X ω, e (Z ω)) ; μ] = H[fun ω => (X ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Z ω)) (f := fun p => (p.1, e p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (he h.2)
  have h2 : H[fun ω => (Y ω, e (Z ω)) ; μ] = H[fun ω => (Y ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (Y ω, Z ω)) (f := fun p => (p.1, e p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (he h.2)
  have h3 : H[fun ω => ((X ω, Y ω), e (Z ω)) ; μ] = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω)) (f := fun p => (p.1, e p.2))
      fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (he h.2)
  have h4 : H[fun ω => e (Z ω) ; μ] = H[Z ; μ] := entropy_comp_of_injective μ he
  simp only [condMutualInfo_def, condEntropy_def]
  rw [h1, h2, h3, h4]

private lemma condMutualInfo_cond_inj' {Z' : Ω → D} {e : C → D} (he : Function.Injective e)
    (hZ : ∀ ω, Z' ω = e (Z ω)) : I[X : Y | Z' ; μ] = I[X : Y | Z ; μ] := by
  obtain rfl : Z' = fun ω => e (Z ω) := funext hZ
  exact condMutualInfo_cond_inj μ he

variable [IsProbabilityMeasure μ]

private lemma condMutualInfo_msg_le (g : A → C → D) (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) :
    I[X : Y | fun ω => (Z ω, g (X ω) (Z ω)) ; μ] ≤ I[X : Y | Z ; μ] := by
  have hg : Measurable fun ω => g (X ω) (Z ω) :=
    (measurable_of_finite (fun q : A × C => g q.1 q.2)).comp (hX.prodMk hZ)
  have h0 := condMutualInfo_nonneg μ hg hY hZ
  have r1 : H[fun ω => (X ω, (Z ω, g (X ω) (Z ω))) ; μ] = H[fun ω => (X ω, Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => (X ω, Z ω))
      (f := fun p => (p.1, (p.2, g p.1 p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 h.2.1
  have r2 : H[fun ω => (Y ω, (Z ω, g (X ω) (Z ω))) ; μ]
      = H[fun ω => ((g (X ω) (Z ω), Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((g (X ω) (Z ω), Y ω), Z ω))
      (f := fun p => (p.1.2, (p.2, p.1.1))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.2.2 h.1) h.2.1
  have r3 : H[fun ω => ((X ω, Y ω), (Z ω, g (X ω) (Z ω))) ; μ]
      = H[fun ω => ((X ω, Y ω), Z ω) ; μ] :=
    entropy_comp_of_injective μ (X := fun ω => ((X ω, Y ω), Z ω))
      (f := fun p => (p.1, (p.2, g p.1.1 p.2))) fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 h.2.1
  have r4 : H[fun ω => (Z ω, g (X ω) (Z ω)) ; μ] = H[fun ω => (g (X ω) (Z ω), Z ω) ; μ] :=
    entropy_comm μ
  simp only [condMutualInfo_def, condEntropy_def] at h0 ⊢
  rw [r1, r2, r3, r4]
  linarith

private lemma condMutualInfo_fun_le (f : A → C → D) (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) :
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

private lemma fun_le' {X' : Ω → D} (f : A → C → D) (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hX' : ∀ ω, X' ω = f (X ω) (Z ω)) :
    I[X' : Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  obtain rfl : X' = fun ω => f (X ω) (Z ω) := funext hX'
  exact condMutualInfo_fun_le μ f hX hY hZ

omit [Fintype D] in
private lemma msg_step [Finite D] {W : Ω → B'} {e : C × D → B'} (he : Function.Injective e)
    (g : A → C → D) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hW : ∀ ω, W ω = e (Z ω, g (X ω) (Z ω))) : I[X : Y | W ; μ] ≤ I[X : Y | Z ; μ] := by
  have := Fintype.ofFinite D
  rw [condMutualInfo_cond_inj' μ he hW]
  exact condMutualInfo_msg_le μ g hX hY hZ

end Info

variable {S T E : Type*} [Fintype S] [MeasurableSpace S] [Fintype T] [MeasurableSpace T]
  [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  [MeasurableSingletonClass E]

open RateDistortion

private lemma entropy_map_iid {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (p : PMF (S × T × E)) (n : ℕ) (φ : S × T × E → W) :
    H[fun ω : Fin n → S × T × E => fun i => φ (ω i) ; iidMeasure p n]
      = n * H[φ ; p.toMeasure] := by
  classical
  rw [entropy_def, entropy, PMF.toMeasure_map _ _ (measurable_of_finite φ),
    ← sum_negMulLog_iidProb]
  refine sum_congr rfl fun y _ => congrArg Real.negMulLog ?_
  rw [measureReal_map_singleton, iidProb_map]
  simp_rw [iidMeasure_real_singleton]

private lemma entropy_pair_iid {V W : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    (p : PMF (S × T × E)) (n : ℕ) (φ : S × T × E → V) (ψ : S × T × E → W) :
    H[fun ω : Fin n → S × T × E => ((fun i => φ (ω i)), fun i => ψ (ω i)) ; iidMeasure p n]
      = n * H[fun a => (φ a, ψ a) ; p.toMeasure] := by
  rw [← entropy_map_iid p n (fun a => (φ a, ψ a))]
  exact entropy_comp_of_injective (iidMeasure p n)
    (X := fun ω : Fin n → S × T × E => fun i => (φ (ω i), ψ (ω i)))
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => V) (fun _ => W)).injective

private lemma entropy_triple_iid (p : PMF (S × T × E)) (n : ℕ) :
    H[fun ω : Fin n → S × T × E =>
        (((fun i => (ω i).1), fun i => (ω i).2.1), fun i => (ω i).2.2) ; iidMeasure p n]
      = n * H[fun a : S × T × E => ((a.1, a.2.1), a.2.2) ; p.toMeasure] := by
  rw [← entropy_map_iid p n (fun a => ((a.1, a.2.1), a.2.2))]
  have hf : Function.Injective fun g : Fin n → (S × T) × E =>
      (((fun i => (g i).1.1), fun i => (g i).1.2), fun i => (g i).2) := fun a b h => by
    simp only [Prod.mk.injEq] at h
    funext i
    exact Prod.ext (Prod.ext (congrFun h.1.1 i) (congrFun h.1.2 i)) (congrFun h.2 i)
  exact entropy_comp_of_injective (iidMeasure p n)
    (X := fun ω : Fin n → S × T × E => fun i => (((ω i).1, (ω i).2.1), (ω i).2.2)) hf

theorem condMutualInfo_iid (p : PMF (S × T × E)) (n : ℕ) :
    I[fun ω : Fin n → S × T × E => fun i => (ω i).1 : fun ω => fun i => (ω i).2.1 |
        eveSeq ; iidMeasure p n]
      = n * I[fun a : S × T × E => a.1 : fun a => a.2.1 | fun a => a.2.2 ; p.toMeasure] := by
  have hE : (eveSeq : (Fin n → S × T × E) → Fin n → E) = fun ω i => (ω i).2.2 := rfl
  rw [hE]
  simp only [condMutualInfo_def, condEntropy_def]
  rw [entropy_pair_iid p n (fun a => a.1) (fun a => a.2.2),
    entropy_pair_iid p n (fun a => a.2.1) (fun a => a.2.2), entropy_triple_iid,
    entropy_map_iid p n (fun a => a.2.2)]
  ring

variable {n r L k : ℕ}

theorem condMutualInfo_transcript_le (p : PMF (S × T × E)) (P : SKProtocol S T n r L k)
    (j : ℕ) :
    I[fun ω : Fin n → S × T × E => fun i => (ω i).1 : fun ω => fun i => (ω i).2.1 |
        fun ω => (eveSeq ω, P.transcript (fun i => (ω i).1) (fun i => (ω i).2.1) j) ;
        iidMeasure p n]
      ≤ I[fun ω : Fin n → S × T × E => fun i => (ω i).1 : fun ω => fun i => (ω i).2.1 |
        eveSeq ; iidMeasure p n] := by
  have hx : Measurable fun ω : Fin n → S × T × E => fun i => (ω i).1 := measurable_of_finite _
  have hy : Measurable fun ω : Fin n → S × T × E => fun i => (ω i).2.1 :=
    measurable_of_finite _
  induction j with
  | zero =>
    exact (condMutualInfo_cond_inj' (iidMeasure p n) (Z := eveSeq)
      (e := fun z : Fin n → E => (z, (Fin.elim0 : Fin 0 → Fin L)))
      (fun a b h => congrArg Prod.fst h) fun ω => rfl).le
  | succ j ih =>
    have hz : Measurable fun ω : Fin n → S × T × E =>
        (eveSeq ω, P.transcript (fun i => (ω i).1) (fun i => (ω i).2.1) j) :=
      measurable_of_finite _
    have he : Function.Injective fun q : ((Fin n → E) × (Fin j → Fin L)) × Fin L =>
        (q.1.1, Fin.snoc (α := fun _ => Fin L) q.1.2 q.2) := by
      rintro ⟨⟨z, t⟩, m⟩ ⟨⟨z', t'⟩, m'⟩ h
      simp only [Prod.mk.injEq] at h
      have h1 := congrArg Fin.init h.2
      have h2 := congrFun h.2 (Fin.last j)
      simp only [Fin.init_snoc, Fin.snoc_last] at h1 h2
      rw [h.1, h1, h2]
    by_cases hj : Even j
    · refine (msg_step (iidMeasure p n) he (fun a c => P.alice j a c.2) hx hy hz
        fun ω => ?_).trans ih
      simp only [SKProtocol.transcript, hj, ite_true]
    · rw [condMutualInfo_comm]
      refine (msg_step (iidMeasure p n) he (fun a c => P.bob j a c.2) hy hx hz
        fun ω => ?_).trans ?_
      · simp only [SKProtocol.transcript, hj, ite_false]
      · rw [condMutualInfo_comm]
        exact ih

theorem condMutualInfo_keys_le (p : PMF (S × T × E)) (P : SKProtocol S T n r L k) :
    I[P.keyAlice : P.keyBob | fun ω => (eveSeq ω, P.pub ω) ; iidMeasure p n]
      ≤ n * I[fun a : S × T × E => a.1 : fun a => a.2.1 | fun a => a.2.2 ; p.toMeasure] := by
  set μ := iidMeasure p n
  have hx : Measurable fun ω : Fin n → S × T × E => fun i => (ω i).1 := measurable_of_finite _
  have hy : Measurable fun ω : Fin n → S × T × E => fun i => (ω i).2.1 :=
    measurable_of_finite _
  have hC : Measurable fun ω : Fin n → S × T × E => (eveSeq ω, P.pub ω) :=
    measurable_of_finite _
  have hB : Measurable (P.keyBob (E := E)) := measurable_of_finite _
  have h1 : I[P.keyAlice : P.keyBob | fun ω => (eveSeq ω, P.pub ω) ; μ]
      ≤ I[fun ω : Fin n → S × T × E => fun i => (ω i).1 : P.keyBob |
        fun ω => (eveSeq ω, P.pub ω) ; μ] :=
    fun_le' μ (fun a c => P.keyA a c.2) hx hB hC fun ω => rfl
  have h2 : I[P.keyBob : fun ω : Fin n → S × T × E => fun i => (ω i).1 |
        fun ω => (eveSeq ω, P.pub ω) ; μ]
      ≤ I[fun ω : Fin n → S × T × E => fun i => (ω i).2.1 :
        fun ω : Fin n → S × T × E => fun i => (ω i).1 | fun ω => (eveSeq ω, P.pub ω) ; μ] :=
    fun_le' μ (fun a c => P.keyB a c.2) hy hx hC fun ω => rfl
  have h3 := condMutualInfo_transcript_le p P r
  rw [condMutualInfo_comm μ (X := fun ω : Fin n → S × T × E => fun i => (ω i).1)] at h1
  rw [condMutualInfo_comm μ (X := fun ω : Fin n → S × T × E => fun i => (ω i).2.1)] at h2
  rw [← condMutualInfo_iid p n]
  exact h1.trans (h2.trans h3)

theorem log_card_le (p : PMF (S × T × E)) (P : SKProtocol S T n r L k) :
    (1 - (iidMeasure p n).real {ω | P.keyAlice ω ≠ P.keyBob ω}) * Real.log k
      ≤ n * I[fun a : S × T × E => a.1 : fun a => a.2.1 | fun a => a.2.2 ; p.toMeasure] +
        Real.log 2 + I[P.keyAlice : fun ω => (eveSeq ω, P.pub ω) ; iidMeasure p n] +
        (Real.log k - H[P.keyAlice ; iidMeasure p n]) := by
  set μ := iidMeasure p n
  have hA : Measurable (P.keyAlice (E := E)) := measurable_of_finite _
  have hB : Measurable (P.keyBob (E := E)) := measurable_of_finite _
  have hC : Measurable fun ω : Fin n → S × T × E => (eveSeq ω, P.pub ω) :=
    measurable_of_finite _
  have a1 := mutualInfo_eq_entropy_sub_condEntropy (P.keyAlice (E := E))
    (fun ω => (eveSeq ω, P.pub ω)) μ
  have a2 := condMutualInfo_eq_condEntropy_sub_condEntropy μ (X := P.keyBob (E := E))
    (Y := P.keyAlice) (Z := fun ω => (eveSeq ω, P.pub ω))
  have a3 : H[P.keyAlice | fun ω => (P.keyBob ω, (eveSeq ω, P.pub ω)) ; μ]
      ≤ H[P.keyAlice | P.keyBob ; μ] :=
    condEntropy_le_condEntropy_comp hA (hB.prodMk hC) Prod.fst
  have a4 := condEntropy_le_log_two_add_mul_log_card (μ := μ) hA hB id
  have hset : {ω : Fin n → S × T × E | id (P.keyBob ω) ≠ P.keyAlice ω}
      = {ω | P.keyAlice ω ≠ P.keyBob ω} :=
    Set.ext fun _ => ne_comm
  rw [hset, Fintype.card_fin] at a4
  have a5 := condMutualInfo_keys_le p P
  rw [condMutualInfo_comm] at a2
  rw [sub_mul, one_mul]
  linarith

theorem le_condMutualInfo_of_achievable {p : PMF (S × T × E)} {R : ℝ} (h : Achievable p R) :
    R ≤ I[fun a : S × T × E => a.1 : fun a => a.2.1 | fun a => a.2.2 ; p.toMeasure] := by
  set I₁ := I[fun a : S × T × E => a.1 : fun a => a.2.1 | fun a => a.2.2 ; p.toMeasure]
  by_contra hlt'
  have hlt := lt_of_not_ge hlt'
  set g := R - I₁ with hg
  have hg0 : 0 < g := by linarith
  set ε := min (1 / 2) (g / (2 * (|R| + 4))) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (div_pos hg0 (by positivity))
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hε2 : ε * (|R| + 4) ≤ g / 2 := by
    have := min_le_right (1 / 2 : ℝ) (g / (2 * (|R| + 4)))
    rw [← hε] at this
    calc ε * (|R| + 4) ≤ g / (2 * (|R| + 4)) * (|R| + 4) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = g / 2 := by field_simp
  obtain ⟨N, hN⟩ := h ε hε0
  obtain ⟨n0, hn0⟩ := exists_nat_gt (Real.log 2 / ε)
  set n := max N n0 with hndef
  obtain ⟨r, L, k, hk, P, hPe, hsec, hunif⟩ := hN n (le_max_left _ _)
  have hn : Real.log 2 < n * ε := by
    rw [← div_lt_iff₀ hε0]
    exact hn0.trans_le (by exact_mod_cast le_max_right N n0)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hnpos : (0 : ℝ) < n := by
    by_contra h0
    have h0 := le_of_not_gt h0
    nlinarith
  have hk0 : (0 : ℝ) < k := (Real.exp_pos _).trans_le hk
  have hlog : n * (R - ε) ≤ Real.log k := (Real.le_log_iff_exp_le hk0).2 hk
  have hlogk : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  have key := log_card_le p P
  have e1 : (1 - ε) * Real.log k ≤
      (1 - (iidMeasure p n).real {ω | P.keyAlice ω ≠ P.keyBob ω}) * Real.log k :=
    mul_le_mul_of_nonneg_right (by linarith) hlogk
  have e2 : (1 - ε) * (n * (R - ε)) ≤ (1 - ε) * Real.log k :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  have e3 : n * ((1 - ε) * (R - ε)) < n * (I₁ + 3 * ε) := by nlinarith
  have e4 : (1 - ε) * (R - ε) < I₁ + 3 * ε := lt_of_mul_lt_mul_left e3 hnpos.le
  have e5 : ε * R ≤ ε * |R| := mul_le_mul_of_nonneg_left (le_abs_self R) hε0.le
  nlinarith [sq_nonneg ε]

theorem achievable_zero (p : PMF (S × T × E)) : Achievable p 0 := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  set P0 : SKProtocol S T n 0 1 1 := ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩
  refine ⟨0, 1, 1, ?_, P0, ?_, ?_, ?_⟩
  · rw [Nat.cast_one, Real.exp_le_one_iff]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · have : {ω : Fin n → S × T × E | P0.keyAlice ω ≠ P0.keyBob ω} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω h => h (Subsingleton.elim _ _)
    rw [this, measureReal_empty]
    exact hε.le
  · have hA : Measurable (P0.keyAlice (E := E)) := measurable_of_finite _
    have hC : Measurable fun ω : Fin n → S × T × E => (eveSeq ω, P0.pub ω) :=
      measurable_of_finite _
    have h0 := entropy_le_log_card (iidMeasure p n) (X := P0.keyAlice (E := E) (n := n))
    have h1 := condEntropy_nonneg (iidMeasure p n) hA hC
    simp only [Fintype.card_fin, Nat.cast_one, Real.log_one] at h0
    rw [mutualInfo_eq_entropy_sub_condEntropy]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · have h0 := entropy_nonneg (iidMeasure p n) (P0.keyAlice (E := E))
    rw [Nat.cast_one, Real.log_one]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem capacity_le (p : PMF (S × T × E)) :
    capacity p ≤ I[fun a : S × T × E => a.1 : fun a => a.2.1 | fun a => a.2.2 ; p.toMeasure] :=
  Real.sSup_le (fun _ hR => le_condMutualInfo_of_achievable hR)
    (condMutualInfo_nonneg _ measurable_fst (measurable_of_finite _) (measurable_of_finite _))

theorem capacity_nonneg (p : PMF (S × T × E)) : 0 ≤ capacity p :=
  le_csSup ⟨_, fun _ hR => le_condMutualInfo_of_achievable hR⟩ (achievable_zero p)

end SecretKey

end Meat
