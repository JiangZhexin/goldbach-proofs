import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open scoped BigOperators
open MeasureTheory Set

namespace PintzPoleKernelTail

noncomputable def phase (u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (↑(2 * Real.pi * u) : ℂ))

noncomputable def kernel (L N : ℕ) (u : ℝ) : ℂ :=
  phase u ^ L * ∑ j ∈ Finset.range N, phase u ^ j

theorem norm_phase (u : ℝ) : ‖phase u‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem chord_lower {u : ℝ} (hu : |u| ≤ 1/2) :
    4 * |u| ≤ ‖phase u - 1‖ := by
  have h₀ : 0 < Real.pi := Real.pi_pos
  have h₁ : |Real.pi * u| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos h₀]
    linarith [mul_le_mul_of_nonneg_left hu h₀.le]
  have h₂ := Real.mul_abs_le_abs_sin h₁
  rw [abs_mul, abs_of_pos h₀] at h₂
  have h₃ : 2 / Real.pi * (Real.pi * |u|) = 2 * |u| := by
    rw [← mul_assoc, div_mul_cancel₀ _ h₀.ne']
  rw [h₃] at h₂
  rw [phase, Complex.norm_exp_I_mul_ofReal_sub_one,
    show 2 * Real.pi * u / 2 = Real.pi * u by ring, Real.norm_eq_abs, abs_mul]
  norm_num
  linarith only [h₂]

theorem norm_kernel_le {u : ℝ} (hu : |u| ≤ 1/2) (hu0 : u ≠ 0)
    (L N : ℕ) : ‖kernel L N u‖ ≤ 1 / (2*|u|) := by
  have hapos : 0 < |u| := abs_pos.mpr hu0
  have hnum : ‖phase u ^ N - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖phase u ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = _ := by simp [norm_pow, norm_phase]; norm_num
  have hmul : ‖kernel L N u‖ * ‖phase u - 1‖ = ‖phase u ^ N - 1‖ := by
    simp [kernel, norm_pow, norm_phase, ← norm_mul, geom_sum_mul]
  apply (le_div_iff₀ (by positivity)).2
  have h := mul_le_mul_of_nonneg_left (chord_lower hu) (norm_nonneg (kernel L N u))
  linarith only [hmul, h, hnum]

/-- The integrated cost of removing a positive frequency tail. The proof
uses only the pointwise majorant and works for an arbitrary twist. -/
theorem one_sided_integral {b r : ℝ} (hr : 0 < r) (hrb : r ≤ b)
    (f : ℝ → ℂ) (hf : Continuous f)
    (hF : ∀ x ∈ Icc r b, ‖f x‖ ≤ 1 / (4*x^2)) :
    ‖∫ x in r..b, f x‖ ≤ 1 / (4*r) := by
  have hzero : (0 : ℝ) ∉ uIcc r b := by
    rw [uIcc_of_le hrb]
    intro h
    exact hr.not_ge h.1
  have hc : IntervalIntegrable (fun x : ℝ => 1/(4*x^2)) volume r b := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div ((continuous_id.pow 2).const_mul 4).continuousOn
      (fun x hx => by
        change (4:ℝ)*x^2 ≠ 0
        exact mul_ne_zero (by norm_num) (pow_ne_zero _ (fun he => hzero (he ▸ hx))))
  have hid : (∫ x in r..b, 1/(4*x^2)) = (r⁻¹-b⁻¹)/4 := by
    simp_rw [show ∀ x : ℝ, 1/(4*x^2) = (1/4) * x ^ (-2 : ℤ) by
      intro x
      rw [show (-2 : ℤ) = -((2:ℕ):ℤ) by norm_num, zpow_neg, zpow_natCast,
        one_div, mul_inv_rev]
      norm_num; ring]
    rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, hzero⟩)]
    norm_num
    ring
  have h := (intervalIntegral.norm_integral_le_integral_norm (f := f) hrb).trans
    (intervalIntegral.integral_mono_on hrb (hf.norm.intervalIntegrable _ _) hc hF)
  rw [hid] at h
  apply h.trans
  have hb : 0 < b := hr.trans_le hrb
  rw [mul_comm 4 r, ← div_div, one_div]
  linarith [inv_nonneg.mpr hb.le]

noncomputable def poleIntegrand (L N : ℕ) (m : ℝ) (u : ℝ) : ℂ :=
  kernel L N u ^ 2 * phase (-m*u)

theorem continuous_poleIntegrand (L N : ℕ) (m : ℝ) : Continuous (poleIntegrand L N m) := by
  unfold poleIntegrand kernel phase
  fun_prop

theorem pointwise_poleIntegrand {u : ℝ} (hu : |u| ≤ 1/2) (h0 : u ≠ 0)
    (L N : ℕ) (m : ℝ) : ‖poleIntegrand L N m u‖ ≤ 1/(4*u^2) := by
  rw [poleIntegrand, norm_mul, norm_pow, norm_phase, mul_one]
  have h := pow_le_pow_left₀ (norm_nonneg (kernel L N u)) (norm_kernel_le hu h0 L N) 2
  rw [one_div_pow, mul_pow, sq_abs] at h
  norm_num at h
  simpa [one_div,mul_inv_rev,mul_comm] using h

/-- The ideal full-period pole coefficient differs from the localized
coefficient by at most `1/(2*r)`, uniformly in length, start, and
target Fourier frequency. -/
theorem truncation_error {r : ℝ} (hr : 0 < r) (hrb : r ≤ 1/2)
    (L N : ℕ) (m : ℝ) :
    ‖(∫ u in (-(1/2 : ℝ))..(1/2 : ℝ), poleIntegrand L N m u) -
        ∫ u in (-r)..r, poleIntegrand L N m u‖ ≤ 1/(2*r) := by
  let f := poleIntegrand L N m
  have hcf : Continuous f := continuous_poleIntegrand L N m
  have hp : ‖∫ x in r..(1/2 : ℝ), f x‖ ≤ 1 / (4*r) :=
    one_sided_integral hr hrb f hcf (fun x hx =>
      pointwise_poleIntegrand (by rw [abs_of_pos (hr.trans_le hx.1)]; exact hx.2) (hr.trans_le hx.1).ne' L N m)
  have hn : ‖∫ x in (-(1/2 : ℝ))..(-r), f x‖ ≤ 1/(4*r) := by
    rw [← intervalIntegral.integral_comp_neg (a := r) (b := 1/2)]
    exact one_sided_integral hr hrb (fun x => f (-x)) (hcf.comp continuous_neg) (by
      intro x hx
      simpa only [neg_sq] using pointwise_poleIntegrand
        (by rw [abs_neg, abs_of_pos (hr.trans_le hx.1)]; exact hx.2)
        (neg_ne_zero.mpr (hr.trans_le hx.1).ne') L N m)
  change ‖(∫ u in (-(1/2 : ℝ))..(1/2 : ℝ), f u) -
        ∫ u in (-r)..r, f u‖ ≤ 1/(2*r)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcf.intervalIntegrable (-(1/2:ℝ)) r) (hcf.intervalIntegrable r (1/2:ℝ)),
    ← intervalIntegral.integral_add_adjacent_intervals
    (hcf.intervalIntegrable (-(1/2:ℝ)) (-r)) (hcf.intervalIntegrable (-r) r)]
  rw [show ∀ a b c : ℂ, a+b+c-b = a+c by intro a b c; ring]
  refine (norm_add_le _ _).trans ?_
  linarith [hn,hp, show 1/(4*r) + 1/(4*r) = 1/(2*r) by ring]

theorem phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_nat_mul (k : ℕ) (x : ℝ) : phase ((k:ℝ)*x) = phase x ^ k := by
  induction k with
  | zero => simp [phase]
  | succ k ih =>
    push_cast
    rw [add_mul, one_mul, phase_add, ih, pow_succ]

theorem phase_int (k : ℤ) : phase k = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  push_cast
  ring

/-- Exact orthogonality for the centered period. -/
theorem integral_phase_int (k : ℤ) :
    (∫ x in (-(1/2:ℝ))..(1/2:ℝ), phase ((k:ℝ)*x)) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst k
    norm_num [phase]
  · let c : ℂ := Complex.I * (2 * (Real.pi:ℂ) * (k:ℂ))
    have hc : c ≠ 0 := by
      unfold c
      exact mul_ne_zero Complex.I_ne_zero (mul_ne_zero
        (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) (by exact_mod_cast hk))
    have he (x : ℝ) : phase ((k:ℝ)*x) = Complex.exp (c * x) := by
      unfold phase c
      congr 1
      push_cast
      ring
    simp_rw [he]
    rw [integral_exp_mul_complex hc]
    have hper : phase ((k:ℝ)*(1/2:ℝ)) = phase ((k:ℝ)*(-(1/2:ℝ))) := by
      rw [show (k:ℝ)*(1/2:ℝ) = ((k:ℝ)*(-(1/2:ℝ))) + (k:ℝ) by ring,
        phase_add, phase_int, mul_one]
    rw [he, he] at hper
    rw [hper, sub_self, zero_div]

/-- The centered full-period coefficient is the exact number of ordered
pairs in the contiguous integer block with sum m. No analytic assumptions. -/
theorem period_coefficient (L N m : ℕ) :
    (∫ u in (-(1/2 : ℝ))..(1/2 : ℝ), poleIntegrand L N m u) =
      ((((Finset.range N).product (Finset.range N)).filter
        (fun p => 2*L + p.1 + p.2 = m)).card : ℂ) := by
  classical
  let s := (Finset.range N).product (Finset.range N)
  let freq (p : ℕ × ℕ) : ℤ := 2*(L:ℤ) + p.1 + p.2 - m
  have he (u : ℝ) : poleIntegrand L N m u = ∑ p ∈ s, phase ((freq p : ℝ)*u) := by
    have hrhs :
        (∑ p ∈ s, phase ((freq p : ℝ)*u)) =
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, phase ((freq (i,j) : ℝ)*u) :=
      Finset.sum_product (Finset.range N) (Finset.range N) (fun p => phase ((freq p:ℝ)*u))
    rw [hrhs]
    unfold poleIntegrand kernel
    rw [pow_two]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    unfold freq
    push_cast
    rw [show ((2*(L:ℝ)+(i:ℝ)+(j:ℝ)-(m:ℝ))*u) =
      (((L:ℝ)*u+(i:ℝ)*u)+((L:ℝ)*u+(j:ℝ)*u))+ (-(m:ℝ)*u) by ring]
    simp only [phase_add, phase_nat_mul]
    ac_rfl
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun p hp =>
    ((by unfold phase; fun_prop : Continuous (fun u : ℝ => phase ((freq p : ℝ)*u)))).intervalIntegrable _ _)]
  simp_rw [integral_phase_int]
  have hf (p : ℕ × ℕ) : freq p = 0 ↔ 2*L+p.1+p.2 = m := by
    unfold freq
    omega
  simp only [hf, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, s]

/-- On the increasing half of the triangular representation profile,
the full-period pole coefficient is exactly m - 2L + 1. -/
theorem early_pair_count (L N m : ℕ) (hm : 2*L ≤ m) (ht : m-2*L < N) :
    (((Finset.range N).product (Finset.range N)).filter
      (fun p => 2*L + p.1 + p.2 = m)).card = m-2*L+1 := by
  rw [← Finset.card_range (m-2*L+1)]
  symm
  apply Finset.card_bij (fun i _ => (i, m-2*L-i))
  · intro i hi
    simp only [Finset.mem_range] at hi
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
    · dsimp
      omega
  · intro a _ b _ hab
    exact congrArg Prod.fst hab
  · rintro ⟨i,j⟩ h
    have hh := (Finset.mem_filter.mp h).2
    dsimp at hh
    exact ⟨i, Finset.mem_range.mpr (by omega), Prod.ext rfl (by dsimp; omega)⟩

/-- Exact local lower bound for the real coefficient of the pole model on
the first half of the triangular profile. -/
theorem early_pole_lower {r : ℝ} (hr : 0 < r) (hrb : r ≤ 1/2)
    (L N m : ℕ) (hm : 2*L ≤ m) (ht : m-2*L < N) :
    ((m-2*L+1 : ℕ):ℝ) - 1/(2*r) ≤
      (∫ u in (-r)..r, poleIntegrand L N m u).re := by
  have h := truncation_error hr hrb L N (m:ℝ)
  rw [period_coefficient, early_pair_count L N m hm ht] at h
  have hn := (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans h)
  simpa [Complex.sub_re, Complex.natCast_re, sub_le_iff_le_add, sub_add_eq_add_sub,
    add_assoc, add_comm, add_left_comm] using
      (show ((m-2*L+1:ℕ):ℝ) - (∫ u in (-r)..r, poleIntegrand L N m u).re ≤ 1/(2*r) by
        simpa [Complex.sub_re, Complex.natCast_re] using hn)

/-- The Ramanujan sum in the Fourier sign convention used by the pole. -/
noncomputable def ramanujan (q m : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), phase (-(m:ℝ)*(a:ℝ)/q)

noncomputable def weight (q : ℕ) : ℂ :=
  (ArithmeticFunction.moebius q : ℂ)^2 / ((q.totient : ℂ)^2)

noncomputable def truncatedSeries (P m : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 P, weight q * ramanujan q m

/-- The pole model integral with polynomial widths, after translating each
major arc to zero. The arcs at denominator q share width P/(qX), so the
numerator phases have already been summed into the Ramanujan sum. -/
noncomputable def weightedPole (P X L N m : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 P, (weight q * ramanujan q m) *
    (∫ u in (-(P:ℝ)/((q:ℝ)*X))..((P:ℝ)/((q:ℝ)*X)), poleIntegrand L N m u)

/-- The summed truncation error retains numerator cancellation before one
takes norms. In particular, the individual bound is exactly q X/(2P),
uniform in the interval length and target. -/
theorem weighted_coefficient_error (P X L N m : ℕ)
    (hP : 0 < P) (hPX : 2 * P ≤ X) (hm : 2*L ≤ m) (ht : m-2*L < N) :
    ‖weightedPole P X L N m - truncatedSeries P m * ((m-2*L+1 : ℕ):ℂ)‖ ≤
      ∑ q ∈ Finset.Icc 1 P,
        ‖weight q * ramanujan q m‖ * ((q:ℝ)*X/(2*P)) := by
  unfold weightedPole truncatedSeries
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
  rw [← mul_sub, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  let r : ℝ := (P:ℝ)/((q:ℝ)*X)
  have hqr : (1:ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hXr : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hPr : (0:ℝ) < P := by exact_mod_cast hP
  have hPXr : 2*(P:ℝ) ≤ X := by exact_mod_cast hPX
  have hr : 0 < r := by dsimp [r]; positivity
  have hr2 : r ≤ 1/2 := by
    unfold r
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hPXr, mul_le_mul_of_nonneg_right hqr hXr.le]
  have h := truncation_error hr hr2 L N (m:ℝ)
  rw [period_coefficient, early_pair_count L N m hm ht, norm_sub_rev] at h
  have he : 1/(2*r) = (q:ℝ)*X/(2*P) := by
    unfold r
    have hq0 : (q:ℝ) ≠ 0 := by positivity
    field_simp [hq0, hXr.ne', hPr.ne']
  rw [he] at h
  simpa only [r, neg_div] using h

theorem weighted_coefficient_error_of_sum_bound (P X L N m : ℕ)
    (hP : 0 < P) (hPX : 2 * P ≤ X) (hm : 2*L ≤ m) (ht : m-2*L < N)
    {B : ℝ}
    (hB : (∑ q ∈ Finset.Icc 1 P, (q:ℝ) * ‖weight q * ramanujan q m‖) ≤ B) :
    ‖weightedPole P X L N m - truncatedSeries P m * ((m-2*L+1 : ℕ):ℂ)‖ ≤
      ((X:ℝ)/(2*P))*B := by
  apply (weighted_coefficient_error P X L N m hP hPX hm ht).trans
  calc
    _ = ((X:ℝ)/(2*P)) * (∑ q ∈ Finset.Icc 1 P, (q:ℝ) * ‖weight q * ramanujan q m‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)

#print axioms weighted_coefficient_error_of_sum_bound
#print axioms weighted_coefficient_error
#print axioms early_pole_lower
#print axioms period_coefficient
#print axioms truncation_error
#print axioms norm_kernel_le

end PintzPoleKernelTail
