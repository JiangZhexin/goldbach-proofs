import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory Filter Set

namespace PintzFixedWindowGram

/-- Oscillatory power integral for the fixed-length Gallagher approach.
The real exponent -1 is included; there is then at most one extra logarithm. -/
theorem oscillatory_bound {a b N : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ N) (z : ℂ) (hz : -1 ≤ z.re) :
    ‖∫ x : ℝ in a..b, (x:ℂ)^z‖ ≤
      4*(1+Real.log N)*N^(z.re+1)/(1+|z.im|) := by
  have hN1 : 1 ≤ N := ha.trans (hab.trans hb)
  have hN : 0 < N := zero_lt_one.trans_le hN1
  have hLog : 0 ≤ Real.log N := Real.log_nonneg hN1
  let d := z.re+1
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have Hd : 0 ≤ N^d := Real.rpow_nonneg hN.le _
  have Ha : (0:ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    exact (zero_lt_one.trans_le ha).not_ge h.1
  by_cases hγ : |z.im| ≤ 1
  · have hI : IntervalIntegrable (fun x : ℝ => N^d / x) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      exact continuousOn_const.div continuous_id.continuousOn (fun x hx =>
        (zero_lt_one.trans_le (ha.trans hx.1)).ne')
    have hi : ‖∫ x : ℝ in a..b, (x:ℂ)^z‖ ≤ ∫ x : ℝ in a..b, N^d/x := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab _ hI
      filter_upwards with x hx
      have hx0 : 0 < x := zero_lt_one.trans_le (ha.trans hx.1.le)
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      apply (le_div_iff₀ hx0).2
      rw [← Real.rpow_add_one hx0.ne']
      exact Real.rpow_le_rpow hx0.le (hx.2.trans hb) hd
    have he : (∫ x : ℝ in a..b, N^d/x) = N^d*(Real.log b-Real.log a) := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul, integral_inv Ha]
      rw [Real.log_div (zero_lt_one.trans_le (ha.trans hab)).ne'
        (zero_lt_one.trans_le ha).ne']
    rw [he] at hi
    apply hi.trans
    apply (le_div_iff₀ (by positivity : 0 < 1+|z.im|)).2
    have hl : 0 ≤ Real.log b - Real.log a :=
      sub_nonneg.mpr (Real.log_le_log (zero_lt_one.trans_le ha) hab)
    have hl' : Real.log b - Real.log a ≤ Real.log N := by
      have H := Real.log_le_log (zero_lt_one.trans_le (ha.trans hab)) hb
      linarith [Real.log_nonneg ha]
    have h1 := mul_le_mul_of_nonneg_left hl' Hd
    have h2 := mul_le_mul_of_nonneg_left (show 1+|z.im| ≤ 2 by linarith)
      (show 0 ≤ N^d*(Real.log b-Real.log a) by positivity)
    change N^d*(Real.log b-Real.log a)*(1+|z.im|) ≤ 4*(1+Real.log N)*N^d
    nlinarith only [h1,h2,Hd,mul_nonneg hLog Hd]
  · have him : 1 < |z.im| := lt_of_not_ge hγ
    have Hγ : |z.im| ≤ ‖z+1‖ := by simpa using Complex.abs_im_le_norm (z+1)
    have hzn : z+1 ≠ 0 := by
      intro e
      rw [e,norm_zero] at Hγ
      linarith
    have hw : z ≠ -1 := fun h => hzn (by simp [h])
    rw [integral_cpow (Or.inr ⟨hw,Ha⟩), norm_div]
    have hs : ‖(b:ℂ)^(z+1) - (a:ℂ)^(z+1)‖ ≤ 2*N^d := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le (ha.trans hab)),
        Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le ha)]
      simp only [Complex.add_re, Complex.one_re]
      change b^d + a^d ≤ 2*N^d
      linarith only [Real.rpow_le_rpow (by linarith : 0 ≤ a) (hab.trans hb) hd,
        Real.rpow_le_rpow (by linarith : 0 ≤ b) hb hd]
    have h1 := div_le_div_of_nonneg_right hs (norm_nonneg (z+1))
    refine h1.trans ?_
    have hden : 1+|z.im| ≤ 2*‖z+1‖ := by linarith
    change 2*N^d/‖z+1‖ ≤ 4*(1+Real.log N)*N^d/(1+|z.im|)
    apply (div_le_div_iff₀ (norm_pos_iff.mpr hzn) (by positivity)).2
    have HH := mul_le_mul_of_nonneg_left hden (show 0 ≤ 2*N^d by positivity)
    nlinarith only [HH, mul_nonneg (mul_nonneg hLog Hd) (norm_nonneg (z+1))]

#print axioms oscillatory_bound
end PintzFixedWindowGram
