import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset

namespace PintzExplicitRounding

/-- Each true-zero term in the truncated explicit formula costs at most
the endpoint displacement when replacing a real endpoint by its floor. -/
theorem kernel_lipschitz {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {z : ℂ} (hz : z ≠ 0) (hre : z.re ≤ 1) :
    ‖(b : ℂ)^z / z - (a : ℂ)^z / z‖ ≤ b-a := by
  let f := fun t : ℝ => (t : ℂ)^z / z
  let f' := fun t : ℝ => (t : ℂ)^(z-1)
  have hfd (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt f (f' t) (Set.Icc a b) t := by
    have ht0 : 0 < t := zero_lt_one.trans_le (ha.trans ht.1)
    have H := (hasDerivAt_ofReal_cpow_const ht0.ne' hz).div_const z
    have he : z * (t : ℂ) ^ (z-1) / z = f' t := by
      dsimp [f']
      rw [mul_comm, mul_div_cancel_right₀ _ hz]
    rw [he] at H
    exact H.hasDerivWithinAt
  have hnorm (t : ℝ) (ht : t ∈ Set.Ico a b) : ‖f' t‖ ≤ 1 := by
    have ht1 := ha.trans ht.1
    dsimp [f']
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le ht1)]
    have he : (z-1).re ≤ 0 := by simpa using sub_nonpos.mpr hre
    simpa using Real.rpow_le_rpow_of_exponent_le ht1 he
  simpa [f] using
    norm_image_sub_le_of_norm_deriv_le_segment' hfd hnorm b (Set.right_mem_Icc.mpr hab)

/-- One real endpoint costs at most one per occurrence of a zero,
with each occurrence counted with its analytic multiplicity. -/
theorem zero_sum_rounding {ι : Type*} (Z : Finset ι) (rho : ι → ℂ)
    (mult : ι → ℕ) {x : ℝ} (hx : 1 ≤ x)
    (h0 : ∀ i ∈ Z, rho i ≠ 0) (h1 : ∀ i ∈ Z, (rho i).re ≤ 1) :
    ‖(∑ i ∈ Z, (mult i : ℂ) * ((x : ℂ)^(rho i) / rho i)) -
      ∑ i ∈ Z, (mult i : ℂ) * (((⌊x⌋₊ : ℕ) : ℂ)^(rho i) / rho i)‖ ≤
        ∑ i ∈ Z, (mult i : ℝ) := by
  have hf : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hF : 1 ≤ (⌊x⌋₊ : ℝ) := by
    have h : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hx)
    exact_mod_cast h
  have hd : x - (⌊x⌋₊ : ℝ) ≤ 1 := by
    have H := Nat.lt_floor_add_one x
    linarith
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_natCast]
  refine mul_le_of_le_one_right (Nat.cast_nonneg _) ?_
  exact (kernel_lipschitz hF hf (h0 i hi) (h1 i hi)).trans hd

#print axioms kernel_lipschitz
#print axioms zero_sum_rounding

end PintzExplicitRounding
