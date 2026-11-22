import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace Meat

private lemma div_mul_div_eq {a b B : ℝ} (hB : B ≠ 0) (h : b = 0 → a = 0) :
    b / B * (a / b) = a / B := by
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb, h hb]
  · field_simp

private lemma div_mul_mul_log_eq {a b B : ℝ} (hB : B ≠ 0) (h : b = 0 → a = 0) :
    b / B * (a / b * Real.log (a / b)) = a * Real.log (a / b) / B := by
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb, h hb]
  · field_simp

theorem add_mul_log_div_add_le {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁)
    (hb₂ : 0 ≤ b₂) (h₁ : b₁ = 0 → a₁ = 0) (h₂ : b₂ = 0 → a₂ = 0) :
    (a₁ + a₂) * Real.log ((a₁ + a₂) / (b₁ + b₂)) ≤
      a₁ * Real.log (a₁ / b₁) + a₂ * Real.log (a₂ / b₂) := by
  rcases (add_nonneg hb₁ hb₂).eq_or_lt with hB | hB
  · have e₁ : b₁ = 0 := by linarith
    have e₂ : b₂ = 0 := by linarith
    simp [h₁ e₁, h₂ e₂]
  have hc := Real.convexOn_mul_log.2 (Set.mem_Ici.2 (div_nonneg ha₁ hb₁))
    (Set.mem_Ici.2 (div_nonneg ha₂ hb₂)) (div_nonneg hb₁ hB.le) (div_nonneg hb₂ hB.le)
    (by field_simp)
  simp only [smul_eq_mul] at hc
  rw [div_mul_div_eq hB.ne' h₁, div_mul_div_eq hB.ne' h₂, div_mul_mul_log_eq hB.ne' h₁,
    div_mul_mul_log_eq hB.ne' h₂, ← add_div, ← add_div, le_div_iff₀ hB] at hc
  have e : (a₁ + a₂) / (b₁ + b₂) * Real.log ((a₁ + a₂) / (b₁ + b₂)) * (b₁ + b₂)
      = (a₁ + a₂) * Real.log ((a₁ + a₂) / (b₁ + b₂)) := by
    field_simp
  linarith

end Meat
