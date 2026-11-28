import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Complex MeasureTheory Set Filter

namespace PintzJutilaMellin

def line (t : ℝ) : ℂ := 1 + t * Complex.I

@[simp] theorem line_re (t : ℝ) : (line t).re = 1 := by simp [line]
@[simp] theorem line_im (t : ℝ) : (line t).im = t := by simp [line]

/-- The defining Euler integral bounds complex Γ by real Γ. -/
theorem norm_gamma_le_real {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  unfold Complex.GammaIntegral
  apply MeasureTheory.norm_integral_le_of_norm_le (Real.GammaIntegral_convergent hs)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp

/-- No Stirling formula is needed for the integrable right-line majorant:
shift Γ twice to the right and use the Euler integral there. -/
theorem gamma_line_bound (t : ℝ) : ‖Complex.Gamma (line t)‖ ≤ 2/(1+t^2) := by
  let w := line t
  have hwRe : w.re = 1 := line_re t
  have hwIm : w.im = t := line_im t
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos (by rw [hwRe]; norm_num)
  have hw10 : w+1 ≠ 0 := Complex.ne_zero_of_re_pos (by simp [hwRe])
  have h1 : ‖w‖^2 = 1+t^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,hwRe,hwIm]; ring
  have h2 : ‖w‖ ≤ ‖w+1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [h1,Complex.sq_norm,Complex.normSq_apply]
    simp [hwRe,hwIm]
    linarith
  have hΓR : Real.Gamma ((w+1+1).re) = 2 := by
    rw [Complex.add_re,Complex.add_re,hwRe,Complex.one_re]
    norm_num only
    simp
  have hΓ := (norm_gamma_le_real (s := w+1+1) (by norm_num [hwRe])).trans_eq hΓR
  rw [Complex.Gamma_add_one (w+1) hw10,Complex.Gamma_add_one w hw0,norm_mul,norm_mul] at hΓ
  rw [le_div_iff₀ (by positivity)]
  calc
    _ = ‖w‖ * (‖w‖ * ‖Complex.Gamma w‖) := by rw [← h1]; ring
    _ ≤ ‖w+1‖ * (‖w‖ * ‖Complex.Gamma w‖) :=
      mul_le_mul_of_nonneg_right h2 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ _ := hΓ

private theorem continuous_gamma_line : Continuous (fun t : ℝ => Complex.Gamma (line t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hG : ContinuousAt Complex.Gamma (line t) := by
    apply Complex.continuousAt_Gamma
    intro n e
    have H := congrArg Complex.re e
    simp at H
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact hG.comp (show ContinuousAt line t by unfold line; fun_prop)

theorem integrable_gamma_line : Integrable (fun t : ℝ => Complex.Gamma (line t)) := by
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul 2) continuous_gamma_line.aestronglyMeasurable
  filter_upwards [] with t
  simpa only [div_eq_mul_inv] using gamma_line_bound t

/-- Mellin inversion at abscissa 1 for the exponential kernel, with the
real-line normalization 1/(2π) (the i from ds is canceled). -/
theorem gamma_inverse {x : ℝ} (hx : 0 < x) :
    (1/(2*Real.pi):ℂ) * ∫ t : ℝ, (x:ℂ)^(-line t)*Complex.Gamma (line t) =
      (Real.exp (-x):ℂ) := by
  let f (u : ℝ) : ℂ := Real.exp (-u)
  have hm (s : ℂ) (hs : 0 < s.re) : mellin f s = Complex.Gamma s := by
    rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral_eq_mellin]
  have hf : MellinConvergent f ((1:ℝ):ℂ) := by
    have H := Complex.GammaIntegral_convergent (s := ((1:ℝ):ℂ)) (by simp)
    refine H.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul,f,mul_comm]
  have hv : Complex.VerticalIntegrable (mellin f) 1 := by
    change Integrable (fun t => mellin f (line t))
    simpa only [hm _ (by simp : 0 < (line _).re)] using integrable_gamma_line
  have hc : ContinuousAt f x := by unfold f; fun_prop
  have H := mellinInv_mellin_eq 1 f hx hf hv hc
  rw [mellinInv, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat] at H
  simp only [smul_eq_mul] at H
  change (1/(2*Real.pi):ℂ) * (∫ t : ℝ, (x:ℂ)^(-line t)*mellin f (line t)) = _ at H
  simp_rw [hm _ (by simp : 0 < (line _).re)] at H
  exact H

/-- Individual summands in the exponentially smoothed Dirichlet series. -/
def integrandTerm (a : ℕ → ℂ) (s : ℂ) (X : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (X:ℂ)^line t * Complex.Gamma (line t) * LSeries.term a (s+line t) n

theorem term_factor (a : ℕ → ℂ) (s : ℂ) {X : ℝ} (hX : 0 < X)
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    integrandTerm a s X n t =
      LSeries.term a s n * (((n:ℝ)/X:ℝ):ℂ)^(-line t)*Complex.Gamma (line t) := by
  let w := line t
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hXC : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hpow (z : ℂ) : (n:ℂ)^z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  have hpowX (z : ℂ) : (X:ℂ)^z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hXC)
  unfold integrandTerm
  change (X:ℂ)^w * Complex.Gamma w * LSeries.term a (s+w) n =
    LSeries.term a s n * (((n:ℝ)/X:ℝ):ℂ)^(-w)*Complex.Gamma w
  rw [LSeries.term_of_ne_zero hn.ne',LSeries.term_of_ne_zero hn.ne',
    Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hnR.le hX.le, Complex.ofReal_natCast,
    Complex.cpow_add _ _ hnC, Complex.cpow_neg, Complex.cpow_neg]
  field_simp [hpow,hpowX]

private theorem integrable_kernel {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => (x:ℂ)^(-line t)*Complex.Gamma (line t)) := by
  have hcont : Continuous (fun t : ℝ => (x:ℂ)^(-line t)*Complex.Gamma (line t)) := by
    apply Continuous.mul _ continuous_gamma_line
    apply Continuous.const_cpow (by unfold line; fun_prop)
    exact Or.inl (by exact_mod_cast hx.ne')
  refine Integrable.mono' (integrable_gamma_line.norm.const_mul (x⁻¹))
    hcont.aestronglyMeasurable ?_
  filter_upwards [] with t
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re, line_re, Real.rpow_neg_one]

theorem integrable_term (a : ℕ → ℂ) (s : ℂ) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    Integrable (integrandTerm a s X n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : integrandTerm a s X 0 = (0 : ℝ → ℂ) := by
      funext t; simp [integrandTerm, LSeries.term_zero]
    rw [h]
    exact integrable_zero _ _ _
  · have h : integrandTerm a s X n =
        fun t => LSeries.term a s n * ((((n:ℝ)/X:ℝ):ℂ)^(-line t)*Complex.Gamma (line t)) := by
      funext t
      rw [term_factor a s hX hn t,mul_assoc]
    rw [h]
    exact (integrable_kernel (div_pos (by exact_mod_cast hn) hX)).const_mul _

theorem integral_term (a : ℕ → ℂ) (s : ℂ) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    (1/(2*Real.pi):ℂ) * ∫ t : ℝ, integrandTerm a s X n t =
      LSeries.term a s n * (Real.exp (-(n:ℝ)/X):ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [integrandTerm,LSeries.term_zero]
  · have h : integrandTerm a s X n =
        fun t => LSeries.term a s n * ((((n:ℝ)/X:ℝ):ℂ)^(-line t)*Complex.Gamma (line t)) := by
      funext t
      rw [term_factor a s hX hn t,mul_assoc]
    rw [h,integral_const_mul,mul_left_comm,gamma_inverse (div_pos (by exact_mod_cast hn) hX),neg_div]

theorem term_norm (a : ℕ → ℂ) (s : ℂ) {X : ℝ} (hX : 0 < X) (n : ℕ) (t : ℝ) :
    ‖integrandTerm a s X n t‖ = (X * ‖LSeries.term a (s+1) n‖)*‖Complex.Gamma (line t)‖ := by
  have hre : (s+line t).re = (s+1).re := by simp
  have hn : ‖LSeries.term a (s+line t) n‖ = ‖LSeries.term a (s+1) n‖ := by
    rw [LSeries.norm_term_eq,LSeries.norm_term_eq,hre]
  rw [integrandTerm,norm_mul,norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, line_re, Real.rpow_one,hn]
  ring

/-- Exponentially weighted Dirichlet series as an absolutely convergent
right-line Γ integral, without a finite-sum restriction. -/
theorem exponential_dirichlet_integral (a : ℕ → ℂ) (s : ℂ) {X : ℝ} (hX : 0 < X)
    (ha : LSeriesSummable a (s+1)) :
    (∑' n : ℕ, LSeries.term a s n * (Real.exp (-(n:ℝ)/X):ℂ)) =
      (1/(2*Real.pi):ℂ) * ∫ t : ℝ,
        (X:ℂ)^line t * Complex.Gamma (line t) * LSeries a (s+line t) := by
  let f := integrandTerm a s X
  have hf (n : ℕ) : Integrable (f n) := integrable_term a s hX n
  have hs : Summable (fun n => ∫ t : ℝ, ‖f n t‖) := by
    have he (n) : (∫ t : ℝ, ‖f n t‖) =
        (X * (∫ t : ℝ, ‖Complex.Gamma (line t)‖)) * ‖LSeries.term a (s+1) n‖ := by
      simp_rw [f,term_norm a s hX n,integral_const_mul]
      ring
    simp_rw [he]
    exact (summable_norm_iff.mpr ha).mul_left _
  have hswap := (MeasureTheory.hasSum_integral_of_summable_integral_norm hf hs).tsum_eq
  calc
    _ = ∑' n, (1/(2*Real.pi):ℂ) * ∫ t : ℝ, f n t := by
      apply tsum_congr
      intro n
      exact (integral_term a s hX n).symm
    _ = (1/(2*Real.pi):ℂ) * ∫ t : ℝ, ∑' n, f n t := by
      rw [tsum_mul_left,hswap]
    _ = _ := by
      apply congrArg (fun z : ℂ => (1/(2*Real.pi):ℂ)*z)
      apply integral_congr_ae
      filter_upwards [] with t
      unfold f integrandTerm LSeries
      rw [tsum_mul_left]

#print axioms gamma_line_bound
#print axioms gamma_inverse
#print axioms exponential_dirichlet_integral
end PintzJutilaMellin
