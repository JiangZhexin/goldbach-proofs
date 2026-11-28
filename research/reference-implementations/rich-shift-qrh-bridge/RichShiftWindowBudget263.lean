import PintzWindowErrorBudget

open Finset
namespace RichShiftWindowBudget263

theorem smoothing_error_power {N P E : ℝ} (hN : 0 < N)
    (hP : 0 ≤ P) (hP' : P ≤ N^(263/1000:ℝ))
    (hE : 0 ≤ E) (hE' : E ≤ N^(2/3:ℝ)) :
    E^2*P^2/N ≤ N^(1289/1500:ℝ) := calc
  _ ≤ (N^(2/3:ℝ))^2*(N^(263/1000:ℝ))^2/N := by gcongr
  _ = _ := by
    rw [← Real.rpow_natCast (N^(2/3:ℝ)), ← Real.rpow_natCast (N^(263/1000:ℝ)),
      ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le, ← Real.rpow_add hN,
      ← Real.rpow_sub_one hN.ne']
    congr 1
    norm_num

theorem smooth_budget {X E : ℝ} (hX : 1 ≤ X) {P : ℕ} (hP : 0 < P)
    (hcut : (P:ℝ) ≤ X^(263/1000:ℝ)) (hE : 0 ≤ E)
    {k : ℕ} (hsm : E ≤ X^(2/3:ℝ)*(1+Real.log X)^k)
    (W : ℕ → ℝ)
    (hW : ∀ r ∈ Icc 1 P, W r ≤ 2*X*(r:ℝ)*(E/((r:ℝ)*X/(2*(P:ℝ))))^2) :
    (∑ r ∈ Icc 1 P, W r) ≤ 8*X^(1289/1500:ℝ)*(1+Real.log X)^(2*k+1) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hP0 : (0:ℝ) < P := by exact_mod_cast hP
  let L := 1+Real.log X
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hX]
  have hlog : 1+Real.log P ≤ L := by
    have ht := Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (263/1000:ℝ) ≤ 1)
    rw [Real.rpow_one] at ht
    exact add_le_add le_rfl (Real.log_le_log hP0 (hcut.trans ht))
  have hPL : 0 ≤ 1+Real.log P := by
    have hP1 : (1:ℝ) ≤ P := by exact_mod_cast hP
    linarith [Real.log_nonneg hP1]
  have hU := smoothing_error_power hX0 hP0.le hcut
    (show 0 ≤ E/L^k by positivity) ((div_le_iff₀ (by positivity : 0 < L^k)).2 hsm)
  have hid : E^2*(P:ℝ)^2/X = ((E/L^k)^2*(P:ℝ)^2/X)*L^(2*k) := by
    rw [mul_comm 2 k, pow_mul]
    field_simp [hL.ne',hX0.ne'] <;> ring
  have hsum := PintzWindowErrorBudget.conductor_budget hX0 hP W hW
  calc
    _ ≤ 8*(E^2*(P:ℝ)^2/X)*(1+Real.log P) := hsum
    _ = 8*(((E/L^k)^2*(P:ℝ)^2/X)*L^(2*k))*(1+Real.log P) := by rw [hid]
    _ ≤ 8*(X^(1289/1500:ℝ)*L^(2*k))*L :=
      mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hU (by positivity)) (by norm_num))
        hlog hPL (by positivity)
    _ = _ := by rw [pow_succ]; ring


#print axioms smooth_budget
end RichShiftWindowBudget263
