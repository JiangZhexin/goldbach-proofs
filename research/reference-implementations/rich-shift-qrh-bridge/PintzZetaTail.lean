import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation

open Set MeasureTheory ZetaPartialSum ZetaAbelFractKernel

namespace PintzZetaTail

/-- The exact Abel remainder at a nontrivial zero, prior to subtracting
the even terms from the Dirichlet polynomial. -/
theorem partial_at_zero {s : ℂ} (hd : s ∈ zetaAbelContinuationDomain)
    (hz : riemannZeta s = 0) (K : ℕ) (hK : 1 ≤ K) :
    zetaPartialSum s K - (K:ℂ)^(1-s)/(1-s) =
      s * ∫ u in Ioi (K:ℝ), zetaAbelFractKernel s u := by
  have hKR : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hI : IntegrableOn (fun u => zetaAbelFractKernel s u) (Ioi (1:ℝ)) := ZetaAbelFractKernel.integrableOn_Ioi s (zetaAbelContinuationDomain_re_pos hd)
  have htail := hI.mono_set (Ioi_subset_Ioi hKR)
  have he := intervalIntegral.integral_interval_add_Ioi hI htail
  have hr := riemannZeta_eq_zetaAbelContinuationFormula s hd
  rw [hz,zetaAbelContinuationFormula] at hr
  rw [← he, intervalIntegral.integral_of_le hKR] at hr
  rw [ZetaPartialSum.abel_formula s hd.1 K hK, intervalIntegral.integral_of_le hKR]
  linear_combination -hr

theorem partial_at_zero_norm {s : ℂ} (hd : s ∈ zetaAbelContinuationDomain)
    (hz : riemannZeta s = 0) (K : ℕ) (hK : 1 ≤ K) :
    ‖zetaPartialSum s K - (K:ℂ)^(1-s)/(1-s)‖ ≤
      ‖s‖ / s.re * (K:ℝ)^(-s.re) := by
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  have hs : 0 < s.re := zetaAbelContinuationDomain_re_pos hd
  have hbound : ‖∫ u in Ioi (K:ℝ), zetaAbelFractKernel s u‖ ≤
      ∫ u in Ioi (K:ℝ), u^(-s.re-1) := by
    apply norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt (by linarith) hKR)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_zetaAbelFractKernel_le u ((show (1:ℝ) ≤ K by exact_mod_cast hK).trans hu.le) s
  have hI : (∫ u in Ioi (K:ℝ), u^(-s.re-1)) = (K:ℝ)^(-s.re)/s.re := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hKR,
      show -s.re-1+1 = -s.re by ring]
    ring
  rw [partial_at_zero hd hz K hK,norm_mul]
  calc
    _ ≤ ‖s‖ * ((K:ℝ)^(-s.re)/s.re) := mul_le_mul_of_nonneg_left (hbound.trans_eq hI) (norm_nonneg _)
    _ = _ := by ring

/-- Subtract the dilated partial sum. The two pole terms cancel exactly. -/
theorem even_difference_bound {s : ℂ} (hd : s ∈ zetaAbelContinuationDomain)
    (hz : riemannZeta s = 0) (K : ℕ) (hK : 1 ≤ K) :
    ‖zetaPartialSum s (2*K) - (2:ℂ)^(1-s)*zetaPartialSum s K‖ ≤
      3*(‖s‖/s.re)*(K:ℝ)^(-s.re) := by
  have hβ := zetaAbelContinuationDomain_re_pos hd
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  have h2K : 1 ≤ 2*K := by omega
  let r (n : ℕ) := zetaPartialSum s n - (n:ℂ)^(1-s)/(1-s)
  have he : zetaPartialSum s (2*K) - (2:ℂ)^(1-s)*zetaPartialSum s K =
      r (2*K) - (2:ℂ)^(1-s)*r K := by
    dsimp [r]
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    push_cast
    ring
  have htwo : ‖(2:ℂ)^(1-s)‖ ≤ 2 := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2)]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show (1-s).re ≤ 1 by simp; linarith)
  have hh := partial_at_zero_norm hd hz (2*K) h2K
  have hpow : ((2*K:ℕ):ℝ)^(-s.re) ≤ (K:ℝ)^(-s.re) := by
    apply Real.rpow_le_rpow_of_nonpos hk _ (by linarith)
    push_cast
    linarith
  have hM : 0 ≤ ‖s‖/s.re := by positivity
  rw [he]
  calc
    _ ≤ ‖r (2*K)‖ + ‖(2:ℂ)^(1-s)*r K‖ := norm_sub_le _ _
    _ ≤ (‖s‖/s.re)*(K:ℝ)^(-s.re) + 2*((‖s‖/s.re)*(K:ℝ)^(-s.re)) := by
      rw [norm_mul]
      exact add_le_add (hh.trans (mul_le_mul_of_nonneg_left hpow hM))
        (mul_le_mul htwo (partial_at_zero_norm hd hz K hK) (norm_nonneg _) (by norm_num))
    _ = _ := by ring

#print axioms even_difference_bound
#print axioms partial_at_zero_norm
end PintzZetaTail
