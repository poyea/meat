import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.Map

open MeasureTheory

namespace Meat

variable {Ω S T U : Type*} [MeasurableSpace Ω]
  [Fintype S] [MeasurableSpace S]
  [Fintype T] [MeasurableSpace T]
  [Fintype U] [MeasurableSpace U]

noncomputable def measureEntropy (ν : Measure S) : ℝ :=
  ∑ s, Real.negMulLog (ν.real {s})

noncomputable def entropy (X : Ω → S) (μ : Measure Ω) : ℝ :=
  measureEntropy (μ.map X)

notation3:max "H[" X " ; " μ "]" => entropy X μ

noncomputable def condEntropy (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  H[fun ω => (X ω, Y ω) ; μ] - H[Y ; μ]

notation3:max "H[" X " | " Y " ; " μ "]" => condEntropy X Y μ

noncomputable def mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[fun ω => (X ω, Y ω) ; μ]

notation3:max "I[" X " : " Y " ; " μ "]" => mutualInfo X Y μ

noncomputable def condMutualInfo (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) : ℝ :=
  H[X | Z ; μ] + H[Y | Z ; μ] - H[fun ω => (X ω, Y ω) | Z ; μ]

notation3:max "I[" X " : " Y " | " Z " ; " μ "]" => condMutualInfo X Y Z μ

section Basic

variable (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω)

theorem entropy_def : H[X ; μ] = ∑ s, Real.negMulLog ((μ.map X).real {s}) := rfl

theorem condEntropy_def : H[X | Y ; μ] = H[fun ω => (X ω, Y ω) ; μ] - H[Y ; μ] := rfl

theorem mutualInfo_def :
    I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[fun ω => (X ω, Y ω) ; μ] := rfl

theorem condMutualInfo_def :
    I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z ; μ] - H[fun ω => (X ω, Y ω) | Z ; μ] := rfl

theorem entropy_pair_eq_add_condEntropy :
    H[fun ω => (X ω, Y ω) ; μ] = H[Y ; μ] + H[X | Y ; μ] := by
  simp only [condEntropy]
  ring

theorem mutualInfo_eq_entropy_sub_condEntropy :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  simp only [mutualInfo, condEntropy]
  ring

end Basic

end Meat
