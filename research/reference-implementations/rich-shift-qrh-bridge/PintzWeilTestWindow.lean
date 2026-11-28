import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set
open scoped Topology ContDiff

namespace PintzWeilTestWindow

noncomputable def cdf (g : ℝ → ℝ) (δ u : ℝ) : ℝ := ∫ v in (-δ)..u, g v

theorem cdf_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (δ u : ℝ) :
    HasDerivAt (cdf g δ) (g u) u :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

theorem cdf_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (δ : ℝ) :
    ContDiff ℝ 2 (cdf g δ) := by
  rw [show (2:ℕ∞ω) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun u => (cdf_hasDerivAt hg.continuous δ u).differentiableAt,
    by simp, ?_⟩
  have he : deriv (cdf g δ) = g := funext fun u => (cdf_hasDerivAt hg.continuous δ u).deriv
  rwa [he]

theorem cdf_left {g : ℝ → ℝ} {δ u : ℝ} (hz : ∀ v ≤ -δ, g v = 0) (hu : u ≤ -δ) :
    cdf g δ u = 0 := by
  unfold cdf
  rw [intervalIntegral.integral_symm]
  have H : (∫ v in u..-δ, g v) = ∫ _v in u..-δ, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hu]
    exact fun v hv => hz v hv.2
  rw [H, intervalIntegral.integral_zero, neg_zero]

theorem cdf_right {g : ℝ → ℝ} {δ u : ℝ} (_hδ : 0 ≤ δ) (hg : Continuous g)
    (hz : ∀ v ≥ δ, g v = 0) (hMass : (∫ v in (-δ)..δ, g v) = 1) (hu : δ ≤ u) :
    cdf g δ u = 1 := by
  unfold cdf
  have H : (∫ v in δ..u, g v) = ∫ _v in δ..u, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hu]
    exact fun v hv => hz v hv.1
  rw [intervalIntegral.integral_zero] at H
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), hMass, H, add_zero]

noncomputable def diff (g : ℝ → ℝ) (δ a b u : ℝ) : ℝ :=
  cdf g δ (u-a) - cdf g δ (u-b)

noncomputable def test (g : ℝ → ℝ) (δ a b : ℝ) (u : ℝ) : ℂ :=
  Complex.exp ((u:ℂ)/2) * (diff g δ a b u : ℂ)

theorem test_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (δ a b : ℝ) :
    ContDiff ℝ 2 (test g δ a b) := by
  have H : ContDiff ℝ 2 (diff g δ a b) :=
    ((cdf_contDiff hg δ).comp (contDiff_id.sub contDiff_const)).sub
      ((cdf_contDiff hg δ).comp (contDiff_id.sub contDiff_const))
  have hreal : ContDiff ℝ 2 (fun u : ℝ => Real.exp (u/2)) :=
    Real.contDiff_exp.comp (contDiff_id.div_const (2:ℝ))
  have he : ContDiff ℝ 2 (fun u : ℝ => (Real.exp (u/2):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hreal
  have he' : ContDiff ℝ 2 (fun u : ℝ => Complex.exp ((u:ℂ)/2)) := by
    convert he using 1
    funext u
    rw [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_ofNat]
  exact he'.mul (Complex.ofRealCLM.contDiff.comp H)

theorem test_support {g : ℝ → ℝ} {δ a b : ℝ} (hδ : 0 ≤ δ) (hab : a ≤ b) (hg : Continuous g)
    (hl : ∀ v ≤ -δ, g v = 0) (hr : ∀ v ≥ δ, g v = 0)
    (hm : (∫ v in (-δ)..δ, g v) = 1) :
    tsupport (test g δ a b) ⊆ Icc (a-δ) (b+δ) := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  by_contra h
  have hz : test g δ a b u = 0 := by
    unfold test diff
    by_cases H : u < a-δ
    · rw [cdf_left hl (show u-a ≤ -δ by linarith), cdf_left hl (show u-b ≤ -δ by linarith)]
      simp
    · have H' : b+δ < u := by
        simp only [mem_Icc, not_and] at h
        exact lt_of_not_ge (h (le_of_not_gt H))
      rw [cdf_right hδ hg hr hm (show δ ≤ u-a by linarith),
        cdf_right hδ hg hr hm (show δ ≤ u-b by linarith)]
      simp
  exact (Function.mem_support.mp hu) hz

/-- This is the smooth positive-support test needed by the ζ Weil formula. -/
theorem admissible {g : ℝ → ℝ} {δ a b : ℝ} (hδ : 0 ≤ δ) (ha : δ < a) (hab : a ≤ b)
    (hg : ContDiff ℝ 1 g) (hl : ∀ v ≤ -δ, g v = 0) (hr : ∀ v ≥ δ, g v = 0)
    (hm : (∫ v in (-δ)..δ, g v) = 1) :
    ContDiff ℝ 2 (test g δ a b) ∧ HasCompactSupport (test g δ a b) ∧
      ∀ u ≤ 0, test g δ a b u = 0 := by
  have H := test_support hδ hab hg.continuous hl hr hm
  refine ⟨test_contDiff hg δ a b, isCompact_Icc.of_isClosed_subset isClosed_closure H, ?_⟩
  intro u hu
  by_contra hn
  have hs : u ∈ tsupport (test g δ a b) :=
    subset_tsupport _ (Function.mem_support.mpr hn)
  have h₁ := (H hs).1
  linarith

/-- The exponential prefactor cancels the square-root factor in the
prime term of Weil's explicit formula. The reflected evaluation is zero. -/
theorem prime_weight {g : ℝ → ℝ} {δ a b : ℝ}
    (hneg : ∀ u ≤ 0, test g δ a b u = 0) (n : ℕ) :
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (test g δ a b (Real.log n) + test g δ a b (-Real.log n)) =
      (ArithmeticFunction.vonMangoldt n : ℂ) * (diff g δ a b (Real.log n) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  rw [hneg (-Real.log n) (neg_nonpos.mpr (Real.log_nonneg hn1)), add_zero, test]
  have hs : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]
    congr 1
    ring
  have he : Complex.exp ((Real.log n:ℂ)/2) = (Real.sqrt n:ℂ) := by
    rw [show ((2:ℂ)) = ((2:ℝ):ℂ) by norm_num, ← Complex.ofReal_div, ← Complex.ofReal_exp, hs]
  rw [he, ← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ (Real.sqrt_pos.2 hn0).ne']

#print axioms prime_weight
#print axioms admissible
end PintzWeilTestWindow
