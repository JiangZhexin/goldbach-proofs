import PintzPoleArithmetic
import PintzPoleRamanujan

open Finset
namespace PintzPoleWeightedError

open PintzPoleArithmetic PintzPoleRamanujan PintzPoleKernelTail

theorem local_divisor_envelope {q m : ℕ} (hq : 0 < q) (hm : 0 < m) :
    (q:ℝ) * ‖weight q * ramanujan q m‖ ≤
      15 * (∑ d ∈ m.divisors.filter (fun d => d ∣ q), (d:ℝ)/Real.sqrt (q:ℝ)) := by
  have hs : q.divisors.filter (fun d => d ∣ m) = m.divisors.filter (fun d => d ∣ q) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨fun h => ⟨⟨h.2,hm.ne'⟩,h.1.1⟩, fun h => ⟨⟨h.2,hq.ne'⟩,h.1.1⟩⟩
  by_cases hsq : Squarefree q
  · have hφ : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
    have hμ : ‖(ArithmeticFunction.moebius q:ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
    have hμ2 : ‖(ArithmeticFunction.moebius q:ℂ)‖^2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (norm_nonneg _) hμ 2
    have hw : ‖weight q‖ ≤ 1 / ((q.totient:ℝ)^2) := by
      rw [weight,norm_div, norm_pow, norm_pow, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right hμ2 (by positivity)
    have hR := ramanujan_bound hq m
    rw [hs] at hR
    calc
      _ = (q:ℝ)* (‖weight q‖ * ‖ramanujan q m‖) := by rw [norm_mul]
      _ ≤ (q:ℝ)* ((1 / (q.totient:ℝ)^2) * ‖ramanujan q m‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hw (norm_nonneg _)) (by positivity)
      _ = ((q:ℝ) / (q.totient:ℝ)^2)*‖ramanujan q m‖ := by ring
      _ ≤ (15 / Real.sqrt (q:ℝ)) * (∑ d ∈ m.divisors.filter (fun d => d ∣ q), (d:ℝ)) := by
        exact mul_le_mul (root_denominator_bound hsq) hR (norm_nonneg _) (by positivity)
      _ = _ := by
        simp only [div_eq_mul_inv, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
  · simp only [weight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq,
      Int.cast_zero, zero_pow (by decide : (2:ℕ) ≠ 0), zero_div, zero_mul,
      norm_zero, mul_zero]
    positivity

/-- Fully explicit weighted pole truncation bound. It uses neither a
totient asymptotic nor any results on exceptional zeros. -/
theorem weighted_coefficient_error_divisors (P X L N m : ℕ)
    (hP : 0 < P) (hPX : 2*P ≤ X) (hm : 2*L ≤ m) (hmp : 0 < m)
    (ht : m-2*L < N) :
    ‖weightedPole P X L N m - truncatedSeries P m * ((m-2*L+1 : ℕ):ℂ)‖ ≤
      (15*(X:ℝ) / Real.sqrt (P:ℝ)) * (m.divisors.card:ℝ) := by
  have he := weighted_divisor_sum_bound m P 15 (by norm_num)
    (fun q => (q:ℝ)*‖weight q * ramanujan q m‖)
    (fun q hq => local_divisor_envelope (Finset.mem_Icc.mp hq).1 hmp)
  have h := weighted_coefficient_error_of_sum_bound P X L N m hP hPX hm ht he
  have hPr : 0 < (P:ℝ) := by exact_mod_cast hP
  have hsq := Real.sq_sqrt hPr.le
  have hs : Real.sqrt (P:ℝ) ≠ 0 := (Real.sqrt_pos.2 hPr).ne'
  refine h.trans_eq ?_
  field_simp
  rw [hsq]

#print axioms weighted_coefficient_error_divisors
end PintzPoleWeightedError
