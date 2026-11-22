import Meat.Shannon.Entropy

open MeasureTheory

namespace Meat

variable {Ω S T U : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S]
  [Fintype T] [MeasurableSpace T]
  [Fintype U] [MeasurableSpace U]

noncomputable def natsToBits (x : ℝ) : ℝ := x / Real.log 2

noncomputable def bitsToNats (x : ℝ) : ℝ := x * Real.log 2

theorem log_two_ne_zero : Real.log 2 ≠ 0 :=
  (Real.log_pos one_lt_two).ne'

theorem bitsToNats_natsToBits (x : ℝ) : bitsToNats (natsToBits x) = x := by
  have h := log_two_ne_zero
  unfold bitsToNats natsToBits
  field_simp

theorem natsToBits_bitsToNats (x : ℝ) : natsToBits (bitsToNats x) = x := by
  have h := log_two_ne_zero
  unfold bitsToNats natsToBits
  field_simp

noncomputable def entropyBits (X : Ω → S) (μ : Measure Ω) : ℝ :=
  natsToBits H[X ; μ]

notation3:max "H₂[" X " ; " μ "]" => entropyBits X μ

noncomputable def condEntropyBits (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  natsToBits H[X | Y ; μ]

notation3:max "H₂[" X " | " Y " ; " μ "]" => condEntropyBits X Y μ

noncomputable def mutualInfoBits (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  natsToBits I[X : Y ; μ]

notation3:max "I₂[" X " : " Y " ; " μ "]" => mutualInfoBits X Y μ

noncomputable def condMutualInfoBits
    (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) : ℝ :=
  natsToBits I[X : Y | Z ; μ]

notation3:max "I₂[" X " : " Y " | " Z " ; " μ "]" => condMutualInfoBits X Y Z μ

section Basic

variable (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω)

theorem entropyBits_def : H₂[X ; μ] = H[X ; μ] / Real.log 2 := rfl

theorem condEntropyBits_def : H₂[X | Y ; μ] = H[X | Y ; μ] / Real.log 2 := rfl

theorem mutualInfoBits_def : I₂[X : Y ; μ] = I[X : Y ; μ] / Real.log 2 := rfl

theorem condMutualInfoBits_def :
    I₂[X : Y | Z ; μ] = I[X : Y | Z ; μ] / Real.log 2 := rfl

theorem entropyBits_pair_eq_add_condEntropyBits :
    H₂[fun ω => (X ω, Y ω) ; μ] = H₂[Y ; μ] + H₂[X | Y ; μ] := by
  simp only [entropyBits, condEntropyBits, natsToBits, condEntropy]
  ring

theorem mutualInfoBits_eq_entropyBits_sub_condEntropyBits :
    I₂[X : Y ; μ] = H₂[X ; μ] - H₂[X | Y ; μ] := by
  simp only [mutualInfoBits, entropyBits, condEntropyBits, natsToBits, mutualInfo, condEntropy]
  ring

end Basic

end Meat
