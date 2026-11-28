import PintzWeilTestWindow

open MeasureTheory Set Filter

namespace PintzWeilMultiplier

/-- All multipliers in the critical strip are uniformly bounded by exp δ. -/
theorem norm_le_exp {g : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hg : Continuous g) (hn : ∀ u, 0 ≤ g u)
    (hl : ∀ v ≤ -δ, g v = 0) (hr : ∀ v ≥ δ, g v = 0)
    (hm : (∫ v in (-δ)..δ, g v) = 1) {s : ℂ} (hs₀ : 0 ≤ s.re) (hs₁ : s.re ≤ 1) :
    ‖∫ v : ℝ, (g v:ℂ) * Complex.exp ((v:ℂ)*s)‖ ≤ Real.exp δ := by
  have hs : Function.support g ⊆ Ioc (-δ) δ := by
    intro v hv
    exact ⟨lt_of_not_ge (fun h => hv (hl v h)), (lt_of_not_ge (fun h => hv (hr v h))).le⟩
  have hi : Integrable g := hg.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset isClosed_closure
      (closure_minimal (hs.trans Ioc_subset_Icc_self) isClosed_Icc))
  have he : ∫ v : ℝ, g v = 1 := by
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
    exact hm
  have H : ‖∫ v : ℝ, (g v:ℂ) * Complex.exp ((v:ℂ)*s)‖ ≤
      ∫ v : ℝ, Real.exp δ * g v := by
    apply norm_integral_le_of_norm_le (hi.const_mul _) (Eventually.of_forall _)
    intro v
    by_cases hv : g v = 0
    · simp [hv]
    have hmem := hs hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn v),
      Complex.norm_exp, Complex.re_ofReal_mul, mul_comm (g v)]
    have hb : v * s.re ≤ δ :=
      (mul_le_mul_of_nonneg_right hmem.2 hs₀).trans (by nlinarith [mul_nonneg hδ (sub_nonneg.mpr hs₁)])
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb) (hn v)
  simpa [integral_const_mul,he] using H

#print axioms norm_le_exp
end PintzWeilMultiplier
