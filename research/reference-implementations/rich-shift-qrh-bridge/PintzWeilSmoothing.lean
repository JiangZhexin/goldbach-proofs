import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Filter Set
open scoped Topology

namespace PintzWeilSmoothing

/-- The exponential moment of a translated bump separates the endpoint
from the test function. This is a Lebesgue integral, with no sign convention
for Fourier transforms involved. -/
theorem translate_moment (g : ℝ → ℂ) (s : ℂ) (a : ℝ) :
    (∫ u, g (u-a) * Complex.exp ((u:ℂ)*s)) =
      Complex.exp ((a:ℂ)*s) * ∫ v, g v * Complex.exp ((v:ℂ)*s) := by
  let f : ℝ → ℂ := fun v => g v * Complex.exp ((v:ℂ)*s)
  have h := integral_add_right_eq_self (μ := volume) f (-a)
  change (∫ u, g (u-a) * Complex.exp ((u:ℂ)*s)) = Complex.exp ((a:ℂ)*s)*(∫ v, f v)
  rw [← h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  dsimp [f]
  rw [sub_eq_add_neg]
  have he : Complex.exp ((u:ℂ)*s) =
      Complex.exp ((a:ℂ)*s) * Complex.exp (((u + -a : ℝ):ℂ)*s) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Integration by parts turns a translated-CDF difference into the
exact signed kernel multiplied by the single bump moment. -/
theorem cdf_difference_moment (u g : ℝ → ℂ) (s : ℂ) (hs : s ≠ 0) (a b : ℝ)
    (hu : ∀ x : ℝ, HasDerivAt u (g (x-a) - g (x-b)) x)
    (hInt : Integrable fun x : ℝ => u x * (Complex.exp ((x:ℂ)*s)*s))
    (hDer : Integrable fun x : ℝ => (g (x-a) - g (x-b)) * Complex.exp ((x:ℂ)*s))
    (hₐ : Integrable fun x : ℝ => g (x-a) * Complex.exp ((x:ℂ)*s))
    (hᵦ : Integrable fun x : ℝ => g (x-b) * Complex.exp ((x:ℂ)*s))
    (hBot : Tendsto (fun x : ℝ => u x * Complex.exp ((x:ℂ)*s)) atBot (𝓝 0))
    (hTop : Tendsto (fun x : ℝ => u x * Complex.exp ((x:ℂ)*s)) atTop (𝓝 0)) :
    (∫ x : ℝ, u x * Complex.exp ((x:ℂ)*s)) =
      (∫ v : ℝ, g v * Complex.exp ((v:ℂ)*s)) *
      ((Complex.exp ((b:ℂ)*s) - Complex.exp ((a:ℂ)*s))/s) := by
  have hExp (x : ℝ) : HasDerivAt (fun y : ℝ => Complex.exp ((y:ℂ)*s))
      (Complex.exp ((x:ℂ)*s)*s) x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const s).cexp
  have H := MeasureTheory.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hu x) (fun x _ => hExp x) hInt hDer hBot hTop
  change (∫ x : ℝ, u x * (Complex.exp ((x:ℂ)*s)*s)) =
    0 - 0 - ∫ x : ℝ, (g (x-a) - g (x-b)) * Complex.exp ((x:ℂ)*s) at H
  simp only [sub_mul, zero_sub, sub_zero, integral_sub hₐ hᵦ] at H
  rw [translate_moment g s a, translate_moment g s b] at H
  simp_rw [← mul_assoc] at H
  rw [integral_mul_const] at H
  rw [← mul_div_assoc]
  apply (eq_div_iff hs).mpr
  simpa only [mul_div_assoc] using (show
      (∫ x : ℝ, u x * Complex.exp ((x:ℂ)*s))*s =
      (∫ v : ℝ, g v * Complex.exp ((v:ℂ)*s)) *
      (Complex.exp ((b:ℂ)*s)-Complex.exp ((a:ℂ)*s)) by
        linear_combination H)

/-- At the Weil transform argument (s-1/2)/i, the compensating
exponential e^(u/2) converts the test function to an ordinary Mellin
moment in logarithmic coordinates. Its kernel is exactly Pintz's. -/
theorem weil_window_cpow (u g : ℝ → ℂ) (s : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hMoment : (∫ t : ℝ, u t * Complex.exp ((t:ℂ)*s)) =
      (∫ v : ℝ, g v * Complex.exp ((v:ℂ)*s)) *
      ((Complex.exp ((Real.log y:ℂ)*s) - Complex.exp ((Real.log x:ℂ)*s))/s)) :
    (∫ t : ℝ, (Complex.exp ((t:ℂ)/2)*u t) *
      Complex.exp (Complex.I * ((s-1/2)/Complex.I) * (t:ℂ))) =
      (∫ v : ℝ, g v * Complex.exp ((v:ℂ)*s)) * (((y:ℂ)^s-(x:ℂ)^s)/s) := by
  have hExp (z : ℝ) (hz : 0 < z) : Complex.exp ((Real.log z:ℂ)*s) = (z:ℂ)^s := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hz.ne'),
      Complex.ofReal_log hz.le]
  rw [← hExp x hx, ← hExp y hy, ← hMoment]
  apply integral_congr_ae
  filter_upwards with t
  rw [mul_comm _ (u t), mul_assoc, ← Complex.exp_add]
  have he : Complex.I * ((s-1/2)/Complex.I) = s-1/2 := by
    rw [mul_comm, div_mul_cancel₀ _ Complex.I_ne_zero]
  rw [he, show (t:ℂ)/2 + (s-1/2)*(t:ℂ) = (t:ℂ)*s by ring]

#print axioms weil_window_cpow

/-- A nonnegative normalized bump of support radius δ changes low
frequencies by at most 2δ‖s‖. -/
theorem multiplier_near_one (g : ℝ → ℝ) (s : ℂ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hs : δ*‖s‖ ≤ 1) (hg : Continuous g)
    (hpos : ∀ x ∈ Icc (-δ) δ, 0 ≤ g x) (hMass : (∫ x in (-δ)..δ, g x) = 1) :
    ‖(∫ x in (-δ)..δ, (g x : ℂ)*Complex.exp ((x:ℂ)*s))-1‖ ≤ 2*δ*‖s‖ := by
  have hG : (∫ x in (-δ)..δ, (g x:ℂ)) = 1 := by
    rw [intervalIntegral.integral_ofReal, hMass, Complex.ofReal_one]
  have hc : Continuous (fun x : ℝ => (g x:ℂ)*Complex.exp ((x:ℂ)*s)) :=
    (Complex.continuous_ofReal.comp hg).mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const))
  have hgc : Continuous (fun x : ℝ => (g x:ℂ)) := Complex.continuous_ofReal.comp hg
  rw [← hG, ← intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
  have hB : Continuous (fun x : ℝ => (2*δ*‖s‖)*g x) := continuous_const.mul hg
  have I := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun x => (g x:ℂ)*Complex.exp ((x:ℂ)*s)-(g x:ℂ))
    (by linarith : -δ ≤ δ) (g := fun x => (2*δ*‖s‖)*g x) ?_ (hB.intervalIntegrable (μ := volume) _ _)
  · rwa [intervalIntegral.integral_const_mul, hMass, mul_one] at I
  · filter_upwards with x hx
    have hpx := hpos x ⟨hx.1.le,hx.2⟩
    have hxn : ‖(x:ℂ)*s‖ ≤ δ*‖s‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨hx.1.le,hx.2⟩) (norm_nonneg _)
    rw [show (g x:ℂ)*Complex.exp ((x:ℂ)*s)-(g x:ℂ) =
      (g x:ℂ)*(Complex.exp ((x:ℂ)*s)-1) by ring, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hpx]
    have H := (Complex.norm_exp_sub_one_le (hxn.trans hs)).trans
      (mul_le_mul_of_nonneg_left hxn (by norm_num : (0:ℝ) ≤ 2))
    simpa [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_left H hpx

/-- One integration by parts for an exponential moment whose boundary
terms vanish. This is also used for a derivative of the same bump. -/
theorem integral_moment_parts (g g' : ℝ → ℂ) (s : ℂ) {a b : ℝ}
    (hc : Continuous g) (hc' : Continuous g')
    (hd : ∀ x : ℝ, HasDerivAt g (g' x) x) (ha : g a = 0) (hb : g b = 0) :
    (∫ x in a..b, g x * Complex.exp ((x:ℂ)*s))*s =
      -(∫ x in a..b, g' x * Complex.exp ((x:ℂ)*s)) := by
  let v : ℝ → ℂ := fun x => Complex.exp ((x:ℂ)*s)
  have hv : Continuous v := Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hvd (x : ℝ) : HasDerivAt v (v x*s) x := by
    simpa only [v, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
      using ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const s).cexp
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := a) (b := b) hc.continuousOn hv.continuousOn (fun x _ => hd x) (fun x _ => hvd x)
    (hc'.intervalIntegrable _ _) ((hv.mul continuous_const).intervalIntegrable _ _)
  simpa only [ha, hb, zero_mul, sub_self, zero_sub, ← mul_assoc,
    intervalIntegral.integral_mul_const, v] using H

/-- The two vanishing boundary pairs leave a factor s⁻². No assumptions
about zeta zeros enter the integration-by-parts step. -/
theorem moment_eq_second_deriv (g g' g'' : ℝ → ℂ) (s : ℂ) (hs : s ≠ 0) {a b : ℝ}
    (hc : Continuous g) (hc' : Continuous g') (hc'' : Continuous g'')
    (hd : ∀ x : ℝ, HasDerivAt g (g' x) x) (hd' : ∀ x : ℝ, HasDerivAt g' (g'' x) x)
    (ha : g a = 0) (hb : g b = 0) (ha' : g' a = 0) (hb' : g' b = 0) :
    (∫ x in a..b, g x * Complex.exp ((x:ℂ)*s)) =
      (∫ x in a..b, g'' x * Complex.exp ((x:ℂ)*s))/s^2 := by
  apply (eq_div_iff (pow_ne_zero _ hs)).2
  have H := integral_moment_parts g g' s hc hc' hd ha hb
  have H' := integral_moment_parts g' g'' s hc' hc'' hd' ha' hb'
  rw [pow_two, ← mul_assoc, H, neg_mul, H', neg_neg]

#print axioms moment_eq_second_deriv

/-- The power envelope for the contribution of a uniform signed-window
error of size N^(2/3), with conductor cutoff at most N^(21/100).
Logarithms and any absolute constants are not part of this algebraic step. -/
theorem smoothing_error_power {N P E : ℝ} (hN : 0 < N)
    (hP : 0 ≤ P) (hP' : P ≤ N^(21/100:ℝ))
    (hE : 0 ≤ E) (hE' : E ≤ N^(2/3:ℝ)) :
    E^2*P^2/N ≤ N^(113/150:ℝ) := calc
  _ ≤ (N^(2/3:ℝ))^2*(N^(21/100:ℝ))^2/N := by gcongr
  _ = _ := by
    rw [← Real.rpow_natCast (N^(2/3:ℝ)), ← Real.rpow_natCast (N^(21/100:ℝ)),
      ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le, ← Real.rpow_add hN,
      ← Real.rpow_sub_one hN.ne']
    congr 1
    norm_num

#print axioms smoothing_error_power
#print axioms translate_moment
#print axioms cdf_difference_moment
#print axioms multiplier_near_one
end PintzWeilSmoothing
