import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open MeasureTheory Set
namespace PintzWeilBump

noncomputable def unitBump : ContDiffBump (0:ℝ) :=
  ⟨1/2,1, by norm_num, by norm_num⟩

noncomputable def base : ℝ → ℝ := unitBump.normed volume

theorem base_contDiff : ContDiff ℝ 2 base := unitBump.contDiff_normed

theorem base_nonneg (x : ℝ) : 0 ≤ base x := unitBump.nonneg_normed x

theorem base_zero {x : ℝ} (hx : 1 ≤ |x|) : base x = 0 := by
  have hh : x ∉ Function.support base := by
    change x ∉ Function.support (unitBump.normed volume)
    rw [unitBump.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact not_lt.mpr hx
  exact Function.notMem_support.mp hh

theorem base_mass : (∫ x in (-1:ℝ)..1, base x) = 1 := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · exact unitBump.integral_normed
  · intro x hx
    have h : |x| < 1 := by
      by_contra! hh
      exact hx (base_zero hh)
    exact ⟨(abs_lt.mp h).1,(abs_lt.mp h).2.le⟩

noncomputable def scaled (δ : ℝ) (x : ℝ) : ℝ := δ⁻¹ * base (x/δ)

theorem scaled_contDiff (δ : ℝ) : ContDiff ℝ 2 (scaled δ) :=
  contDiff_const.mul (base_contDiff.comp (contDiff_id.div_const _))

theorem scaled_nonneg {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : 0 ≤ scaled δ x :=
  mul_nonneg (inv_nonneg.mpr hδ.le) (base_nonneg _)

theorem scaled_zero_left {δ : ℝ} (hδ : 0 < δ) (x : ℝ) (hx : x ≤ -δ) :
    scaled δ x = 0 := by
  have h : x/δ ≤ -1 := (div_le_iff₀ hδ).2 (by linarith)
  have h₁ : 1 ≤ |x/δ| := (by linarith : 1 ≤ -(x/δ)).trans (neg_le_abs _)
  simp [scaled, base_zero h₁]

theorem scaled_zero_right {δ : ℝ} (hδ : 0 < δ) (x : ℝ) (hx : δ ≤ x) :
    scaled δ x = 0 := by
  have h : 1 ≤ x/δ := (le_div_iff₀ hδ).2 (by linarith)
  simp [scaled, base_zero (h.trans (le_abs_self _))]

theorem scaled_mass {δ : ℝ} (hδ : 0 < δ) : (∫ x in (-δ)..δ, scaled δ x) = 1 := by
  simp only [scaled]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div _ hδ.ne',
    neg_div, div_self hδ.ne', base_mass, smul_eq_mul, mul_one, inv_mul_cancel₀ hδ.ne']

private noncomputable def baseC (x : ℝ) : ℂ := (base x:ℂ)
private noncomputable def baseC₂ (x : ℝ) : ℂ := deriv (deriv baseC) x

private theorem baseC_contDiff : ContDiff ℝ 2 baseC :=
  Complex.ofRealCLM.contDiff.comp base_contDiff

private theorem baseC_deriv_contDiff : ContDiff ℝ 1 (deriv baseC) :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) baseC from baseC_contDiff)).2.2

theorem base_deriv₂_integrable : Integrable (fun x => ‖deriv (deriv (fun u => (base u : ℂ))) x‖) := by
  have hs : HasCompactSupport baseC := unitBump.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  exact (baseC_deriv_contDiff.continuous_deriv_one.norm).integrable_of_hasCompactSupport hs.deriv.deriv.norm

private theorem deriv_scale (f : ℝ → ℂ) (a δ : ℝ) (hf : Differentiable ℝ f) :
    deriv (fun x => a • f (x/δ)) = fun x => (a*δ⁻¹) • deriv f (x/δ) := by
  funext x
  have hg : HasDerivAt (fun x : ℝ => x/δ) δ⁻¹ x := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id x).div_const δ
  have H := (((hf (x/δ)).hasDerivAt.scomp x hg).const_smul a).deriv
  change deriv (fun y => a • f (y/δ)) x = a • (δ⁻¹ • deriv f (x/δ)) at H
  simpa only [smul_smul] using H

theorem scaled_deriv₂_identity {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : ℝ, ‖deriv (deriv (fun u => (scaled δ u:ℂ))) x‖) =
      δ⁻¹^2 * ∫ x : ℝ, ‖deriv (deriv (fun u => (base u:ℂ))) x‖ := by
  have hd : (fun x : ℝ => (scaled δ x:ℂ)) = fun x => δ⁻¹ • baseC (x/δ) := by
    funext x
    simp [scaled,baseC,Complex.real_smul]
  rw [hd, deriv_scale _ _ _ (baseC_contDiff.differentiable (by norm_num)),
    deriv_scale _ _ _ (baseC_deriv_contDiff.differentiable (by norm_num))]
  change (∫ x : ℝ, ‖(δ⁻¹*δ⁻¹*δ⁻¹) • baseC₂ (x/δ)‖) =
    δ⁻¹^2 * ∫ x : ℝ, ‖baseC₂ x‖
  simp only [norm_smul, Real.norm_of_nonneg (show 0 ≤ δ⁻¹*δ⁻¹*δ⁻¹ by positivity)]
  rw [integral_const_mul, Measure.integral_comp_div (fun x => ‖baseC₂ x‖) δ,abs_of_pos hδ,smul_eq_mul]
  field_simp [hδ.ne']

/-- Smooth, nonnegative, unit-mass logarithmic window cutoff with a
fixed L¹ second-derivative constant after scaling. -/
theorem exists_normalized_smooth :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℝ, 0 < δ → ∃ g : ℝ → ℝ,
      ContDiff ℝ 2 g ∧ (∀ x, 0 ≤ g x) ∧
      (∀ x ≤ -δ, g x = 0) ∧ (∀ x ≥ δ, g x = 0) ∧
      (∫ x in (-δ)..δ, g x) = 1 ∧
      (∫ x : ℝ, ‖deriv (deriv (fun u => (g u:ℂ))) x‖) = K/δ^2 := by
  let K := ∫ x : ℝ, ‖baseC₂ x‖
  refine ⟨K,integral_nonneg (fun x => norm_nonneg _),fun δ hδ =>
    ⟨scaled δ,scaled_contDiff δ,scaled_nonneg hδ,scaled_zero_left hδ,scaled_zero_right hδ,
      scaled_mass hδ,?_⟩⟩
  rw [scaled_deriv₂_identity hδ]
  change δ⁻¹^2*K = K/δ^2
  field_simp [hδ.ne']

#print axioms exists_normalized_smooth
#print axioms base_deriv₂_integrable
end PintzWeilBump
