import PintzWeilPrimeDesmoothing
import PintzWeilZetaWindow
import Zeta23.Poisson.PaperFT

noncomputable section
open MeasureTheory Set Zeta23 PintzWeilTestWindow
namespace PintzWeilZetaPoles

private theorem integral_to_window {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hL : ∀ t ≤ a, f t = 0) (hR : ∀ t ≥ b, f t = 0) :
    (∫ t, f t) = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc]
  congr 1
  funext t
  by_cases ht : t ∈ Ioc a b
  · simp [ht]
  · rw [indicator_of_notMem ht]
    by_cases hta : t ≤ a
    · exact hL _ hta
    · exact hR _ (le_of_not_ge (fun htb => ht ⟨lt_of_not_ge hta, htb⟩))

theorem negative_pole_error {g : ℝ → ℝ} {δ x y N : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ N)
    (ha : δ < Real.log x) (hg : ContDiff ℝ 1 g) (hn : ∀ v, 0 ≤ g v)
    (hl : ∀ v ≤ -δ, g v = 0) (hr : ∀ v ≥ δ, g v = 0)
    (hm : (∫ v in (-δ)..δ, g v) = 1) :
    ‖paperFT (test g δ (Real.log x) (Real.log y)) (-Complex.I/2) - ((y-x:ℝ):ℂ)‖ ≤ 2*δ*N := by
  have hγ : gammaOf 1 = -Complex.I / 2 := by
    apply Complex.ext <;> norm_num [gammaOf, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  rw [← hγ, PintzWeilZetaWindow.evaluated_test 1 one_ne_zero hδ hx hxy ha hg hl hr hm]
  rw [integral_to_window (a := -δ) (b := δ) (by linarith)
      (fun v hv => by simp [hl v hv]) (fun v hv => by simp [hr v hv])]
  simp only [Complex.cpow_one, div_one, mul_one, Complex.ofReal_sub]
  rw [show _ * ((y : ℂ) - (x : ℂ)) - ((y : ℂ) - (x : ℂ)) =
    ((∫ v in -δ..δ, (g v : ℂ) * Complex.exp (v : ℂ)) - 1) * ((y : ℂ) - (x : ℂ)) from by ring, norm_mul]
  have hM := PintzWeilSmoothing.multiplier_near_one g 1 hδ (by simpa using hδ1)
    hg.continuous (fun v _ => hn v) hm
  simp only [norm_one, mul_one] at hM
  exact mul_le_mul hM (by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hxy)]; linarith) (norm_nonneg _) (by positivity)

theorem positive_pole_bound {g : ℝ → ℝ} {δ a b : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (hg : Continuous g) (hn : ∀ v, 0 ≤ g v)
    (hl : ∀ v ≤ -δ, g v = 0) (hr : ∀ v ≥ δ, g v = 0)
    (hm : (∫ v in (-δ)..δ, g v) = 1) :
    ‖paperFT (test g δ a b) (Complex.I/2)‖ ≤ b-a+2*δ := by
  have he (u : ℝ) : test g δ a b u * Complex.exp (Complex.I * (Complex.I/2) * (u:ℂ)) =
      (diff g δ a b u : ℂ) := by
    unfold test
    rw [mul_right_comm, ← Complex.exp_add]
    have H : (u:ℂ)/2 + Complex.I * (Complex.I/2) * (u:ℂ) = 0 := by
      rw [show Complex.I * (Complex.I/2) = -1/2 by rw [← mul_div_assoc, Complex.I_mul_I]]
      ring
    rw [H, Complex.exp_zero, one_mul]
  have hdiff (u : ℝ) : 0 ≤ diff g δ a b u ∧ diff g δ a b u ≤ 1 := by
    unfold diff
    have H := PintzWeilPrimeDesmoothing.monotone_cdf hg hn hl (show u-b ≤ u-a by linarith)
    have h₁ := PintzWeilPrimeDesmoothing.cdf_unit hδ hg hn hl hr hm (u-a)
    have h₂ := PintzWeilPrimeDesmoothing.cdf_unit hδ hg hn hl hr hm (u-b)
    constructor <;> linarith [h₁.2, h₂.1]
  rw [paperFT_def]
  simp_rw [he]
  have hw : a-δ ≤ b+δ := by linarith
  rw [integral_to_window hw]
  · have H := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun u : ℝ => (diff g δ a b u : ℂ)) hw (g := fun _ => (1:ℝ)) ?_
      (continuous_const.intervalIntegrable (μ := volume) _ _)
    · rw [intervalIntegral.integral_const] at H
      simpa [smul_eq_mul, show b+δ-(a-δ) = b-a+2*δ by ring] using H
    · filter_upwards with u _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hdiff u).1]
      exact (hdiff u).2
  · intro u hu
    unfold diff
    rw [cdf_left hl (show u-a ≤ -δ by linarith), cdf_left hl (show u-b ≤ -δ by linarith)]
    simp
  · intro u hu
    unfold diff
    rw [cdf_right hδ hg hr hm (show δ ≤ u-a by linarith), cdf_right hδ hg hr hm (show δ ≤ u-b by linarith)]
    simp

theorem poles_error {g : ℝ → ℝ} {δ x y N : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ N)
    (ha : δ < Real.log x) (hg : ContDiff ℝ 1 g) (hn : ∀ v, 0 ≤ g v)
    (hl : ∀ v ≤ -δ, g v = 0) (hr : ∀ v ≥ δ, g v = 0)
    (hm : (∫ v in (-δ)..δ, g v) = 1) :
    let k := test g δ (Real.log x) (Real.log y)
    ‖paperFT k (Complex.I/2) + paperFT k (-Complex.I/2) - ((y-x:ℝ):ℂ)‖ ≤
      2*δ*N + Real.log N + 2 := by
  dsimp only
  rw [add_sub_assoc]
  refine (norm_add_le _ _).trans ?_
  have h₁ := positive_pole_bound hδ (Real.log_le_log hx hxy) hg.continuous hn hl hr hm
  have h₂ := negative_pole_error hδ hδ1 hx hxy hy ha hg hn hl hr hm
  linarith [Real.log_le_log (hx.trans_le hxy) hy]

#print axioms poles_error
end PintzWeilZetaPoles
