import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Meat.Shannon.ChainRule

open MeasureTheory Finset Filter Topology

namespace Meat

variable {Ω S : Type*} [MeasurableSpace Ω] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

def block (X : ℕ → Ω → S) (n : ℕ) (ω : Ω) : Fin n → S := fun i => X i ω

def shiftBlock (X : ℕ → Ω → S) (k n : ℕ) (ω : Ω) : Fin n → S := fun i => X (i + k) ω

def Stationary (X : ℕ → Ω → S) (μ : Measure Ω) : Prop :=
  ∀ n k, μ.map (shiftBlock X k n) = μ.map (block X n)

def IsMarkovProcess (X : ℕ → Ω → S) (μ : Measure Ω) : Prop :=
  ∀ n, MarkovChain (block X n) (X n) (X (n + 1)) μ

noncomputable def entropyRate (X : ℕ → Ω → S) (μ : Measure Ω) : ℝ :=
  ⨅ n, H[X n | block X n ; μ]

section

variable (μ : Measure Ω) {X : ℕ → Ω → S}

theorem entropy_shiftBlock_succ (k n : ℕ) :
    H[shiftBlock X k (n + 1) ; μ] = H[shiftBlock X k n ; μ] +
      H[X (n + k) | shiftBlock X k n ; μ] := by
  rw [← entropy_pair_eq_add_condEntropy]
  refine (entropy_comp_of_injective μ (X := shiftBlock X k (n + 1))
    (f := fun y => (y (Fin.last n), Fin.init y)) fun a b h => ?_).symm
  simp only [Prod.mk.injEq] at h
  rw [← Fin.snoc_init_self a, ← Fin.snoc_init_self b, h.1, h.2]

theorem entropy_block_succ (n : ℕ) :
    H[block X (n + 1) ; μ] = H[block X n ; μ] + H[X n | block X n ; μ] :=
  entropy_shiftBlock_succ μ 0 n

theorem entropy_block_eq_sum [IsProbabilityMeasure μ] (n : ℕ) :
    H[block X n ; μ] = ∑ i ∈ range n, H[X i | block X i ; μ] := by
  induction n with
  | zero =>
    rw [sum_range_zero]
    have h := entropy_le_log_card μ (X := block X 0)
    simp only [Fintype.card_unique, Nat.cast_one, Real.log_one] at h
    exact le_antisymm h (entropy_nonneg μ _)
  | succ n ih => rw [entropy_block_succ, ih, sum_range_succ]

variable [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
private lemma entropy_eq_of_map_eq {T : Type*} [MeasurableSpace T] {A B : Ω → T}
    (h : μ.map A = μ.map B) {U : Type*} [Fintype U] [MeasurableSpace U]
    (hA : Measurable A) (hB : Measurable B) (f : T → U)
    (hf : Measurable f) : H[f ∘ A ; μ] = H[f ∘ B ; μ] := by
  rw [entropy, entropy, ← Measure.map_map hf hA, ← Measure.map_map hf hB, h]

theorem condEntropy_succ_le (hX : ∀ i, Measurable (X i)) (hst : Stationary X μ) (n : ℕ) :
    H[X (n + 1) | block X (n + 1) ; μ] ≤ H[X n | block X n ; μ] := by
  have hB : ∀ m, Measurable (block X m) := fun m => measurable_pi_iff.2 fun i => hX i
  have hS : ∀ k m, Measurable (shiftBlock X k m) := fun k m => measurable_pi_iff.2 fun i => hX _
  have h1 : H[X (n + 1) | block X (n + 1) ; μ] ≤
      H[X (n + 1) | (fun y : Fin (n + 1) → S => fun i : Fin n => y i.succ) ∘ block X (n + 1) ;
        μ] := condEntropy_le_condEntropy_comp (hX _) (hB _) _
  have h2 : (fun y : Fin (n + 1) → S => fun i : Fin n => y i.succ) ∘ block X (n + 1) =
      shiftBlock X 1 n := rfl
  have h3 := entropy_shiftBlock_succ μ (X := X) 1 n
  have hE : ∀ m, H[shiftBlock X 1 m ; μ] = H[block X m ; μ] := fun m => by
    rw [entropy, entropy, hst m 1]
  have h4 := entropy_block_succ μ (X := X) n
  rw [h2] at h1
  rw [hE, hE] at h3
  linarith

theorem condEntropy_antitone (hX : ∀ i, Measurable (X i)) (hst : Stationary X μ) :
    Antitone fun n => H[X n | block X n ; μ] :=
  antitone_nat_of_succ_le (condEntropy_succ_le μ hX hst)

theorem tendsto_condEntropy (hX : ∀ i, Measurable (X i)) (hst : Stationary X μ) :
    Tendsto (fun n => H[X n | block X n ; μ]) atTop (𝓝 (entropyRate X μ)) :=
  tendsto_atTop_ciInf (condEntropy_antitone μ hX hst) ⟨0, by
    rintro _ ⟨n, rfl⟩
    exact condEntropy_nonneg μ (hX n) (measurable_pi_iff.2 fun i => hX i)⟩

theorem tendsto_entropy_div (hX : ∀ i, Measurable (X i)) (hst : Stationary X μ) :
    Tendsto (fun n : ℕ => H[block X n ; μ] / n) atTop (𝓝 (entropyRate X μ)) := by
  have h := (tendsto_condEntropy μ hX hst).cesaro
  refine h.congr fun n => ?_
  rw [entropy_block_eq_sum, div_eq_inv_mul]

theorem entropyRate_of_markov (hX : ∀ i, Measurable (X i)) (hst : Stationary X μ)
    (hM : IsMarkovProcess X μ) : entropyRate X μ = H[X 1 | X 0 ; μ] := by
  have hB : ∀ m, Measurable (block X m) := fun m => measurable_pi_iff.2 fun i => hX i
  have hS : ∀ k m, Measurable (shiftBlock X k m) := fun k m => measurable_pi_iff.2 fun i => hX _
  have hc : ∀ m, H[X (m + 1) | block X (m + 1) ; μ] = H[X 1 | X 0 ; μ] := fun m => by
    have e1 : H[X (m + 1) | block X (m + 1) ; μ] =
        H[X (m + 1) | fun ω => (block X m ω, X m ω) ; μ] :=
      condEntropy_cond_of_injective μ (e := fun q => Fin.snoc (α := fun _ => S) q.1 q.2)
        (fun a b h => by
          have h1 := congrArg Fin.init h
          have h2 := congrFun h (Fin.last m)
          simp only [Fin.init_snoc, Fin.snoc_last] at h1 h2
          exact Prod.ext h1 h2)
        fun ω => by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [block]
    have e2 := condMutualInfo_eq_condEntropy_sub_condEntropy μ (X := block X m)
      (Y := X (m + 1)) (Z := X m)
    have e3 : I[block X m : X (m + 1) | X m ; μ] = 0 := hM m
    have f1 : (fun ω => (X (m + 1) ω, X m ω)) =
        (fun y : Fin 2 → S => (y 1, y 0)) ∘ shiftBlock X m 2 := funext fun ω => by
      simp [shiftBlock, add_comm]
    have f2 : X m = (fun y : Fin 2 → S => y 0) ∘ shiftBlock X m 2 := funext fun ω => by
      simp [shiftBlock]
    have g1 := entropy_eq_of_map_eq μ (hst 2 m) (hS m 2) (hB 2)
      (fun y : Fin 2 → S => (y 1, y 0)) (measurable_of_finite _)
    have g2 := entropy_eq_of_map_eq μ (hst 2 m) (hS m 2) (hB 2)
      (fun y : Fin 2 → S => y 0) (measurable_of_finite _)
    have e4 : H[X (m + 1) | X m ; μ] = H[X 1 | X 0 ; μ] := by
      rw [condEntropy_def, condEntropy_def, f1, f2, g1, g2]
      rfl
    rw [e1]
    linarith
  have hanti := condEntropy_antitone μ hX hst
  refine le_antisymm ((ciInf_le ⟨0, ?_⟩ 1).trans (hc 0).le) (le_ciInf fun n => ?_)
  · rintro _ ⟨n, rfl⟩
    exact condEntropy_nonneg μ (hX n) (hB n)
  · rcases n with _ | m
    · exact (hc 0).symm.le.trans (hanti (Nat.zero_le 1))
    · exact (hc m).ge

end

end Meat
