import PintzWeilSmoothing
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset

namespace PintzWindowErrorBudget

/-- Explicit sum of 1/r over the conductors in [1,P]. -/
theorem reciprocal_conductors (P : ℕ) :
    (∑ r ∈ Icc 1 P, (r:ℝ)⁻¹) ≤ 1+Real.log P := by
  have h := harmonic_le_one_add_log P
  have he : (harmonic P : ℝ) = ∑ r ∈ Icc 1 P, (r:ℝ)⁻¹ := by
    unfold harmonic
    push_cast
    apply sum_bij (fun n _ => n+1)
    · intro n hn
      have hn' := mem_range.mp hn
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n hn m hm hEq
      omega
    · intro m hm
      obtain ⟨hm1,hmP⟩ := mem_Icc.mp hm
      exact ⟨m-1,mem_range.mpr (by omega),by omega⟩
    · intros n hn
      push_cast
      rfl
  rwa [← he]

/-- Sum the actual conductor-indexed L² error envelope. For a fixed
conductor r, the number of characters is at most r, the support has
length at most 2X, and the normalization is Y=rX/(2P). -/
theorem conductor_budget {X E : ℝ} (hX : 0 < X) {P : ℕ} (hP : 0 < P)
    (W : ℕ → ℝ)
    (hb : ∀ r ∈ Icc 1 P, W r ≤ 2*X*(r:ℝ)*(E/((r:ℝ)*X/(2*(P:ℝ))))^2) :
    (∑ r ∈ Icc 1 P, W r) ≤ 8*(E^2*(P:ℝ)^2/X)*(1+Real.log P) := by
  have hPReal : (0:ℝ) < P := by exact_mod_cast hP
  calc
    _ ≤ ∑ r ∈ Icc 1 P, (8*(E^2*(P:ℝ)^2/X))*((r:ℝ)⁻¹) := by
      apply sum_le_sum
      intro r hr
      have hrR : (0:ℝ) < r := by exact_mod_cast (mem_Icc.mp hr).1
      calc
        _ ≤ _ := hb r hr
        _ = _ := by
          field_simp [hX.ne',hPReal.ne',hrR.ne']
          <;> ring
    _ = (8*(E^2*(P:ℝ)^2/X))*(∑ r ∈ Icc 1 P, (r:ℝ)⁻¹) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_conductors P) (by positivity)

/-- The smoothing remainder envelope has a strict power saving after
all conductors are summed, with the fixed logarithmic losses exposed. -/
theorem smooth_budget {X E : ℝ} (hX : 1 ≤ X) {P : ℕ} (hP : 0 < P)
    (hcut : (P:ℝ) ≤ X^(21/100:ℝ)) (hE : 0 ≤ E)
    {k : ℕ} (hsm : E ≤ X^(2/3:ℝ)*(1+Real.log X)^k)
    (W : ℕ → ℝ)
    (hW : ∀ r ∈ Icc 1 P, W r ≤ 2*X*(r:ℝ)*(E/((r:ℝ)*X/(2*(P:ℝ))))^2) :
    (∑ r ∈ Icc 1 P, W r) ≤ 8*X^(113/150:ℝ)*(1+Real.log X)^(2*k+1) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hP0 : (0:ℝ) < P := by exact_mod_cast hP
  let L := 1+Real.log X
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hX]
  have hlog : 1+Real.log P ≤ L := by
    have ht := Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (21/100:ℝ) ≤ 1)
    rw [Real.rpow_one] at ht
    exact add_le_add le_rfl (Real.log_le_log hP0 (hcut.trans ht))
  have hPL : 0 ≤ 1+Real.log P := by
    have hP1 : (1:ℝ) ≤ P := by exact_mod_cast hP
    linarith [Real.log_nonneg hP1]
  have hU := PintzWeilSmoothing.smoothing_error_power hX0 hP0.le hcut
    (show 0 ≤ E/L^k by positivity) ((div_le_iff₀ (by positivity : 0 < L^k)).2 hsm)
  have hid : E^2*(P:ℝ)^2/X = ((E/L^k)^2*(P:ℝ)^2/X)*L^(2*k) := by
    rw [mul_comm 2 k, pow_mul]
    field_simp [hL.ne',hX0.ne'] <;> ring
  have hsum := conductor_budget hX0 hP W hW
  calc
    _ ≤ 8*(E^2*(P:ℝ)^2/X)*(1+Real.log P) := hsum
    _ = 8*(((E/L^k)^2*(P:ℝ)^2/X)*L^(2*k))*(1+Real.log P) := by rw [hid]
    _ ≤ 8*(X^(113/150:ℝ)*L^(2*k))*L :=
      mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hU (by positivity)) (by norm_num))
        hlog hPL (by positivity)
    _ = _ := by rw [pow_succ]; ring

#print axioms smooth_budget
#print axioms reciprocal_conductors
#print axioms conductor_budget
end PintzWindowErrorBudget
