import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PintzLogWindow

/-- An interval of width h in log frequency cuts each dyadic block into an
interval of integer frequencies of width at most 2Uh. -/
theorem diameter {U n m x h : ℝ} (hn : 0 < n) (hnm : n ≤ m) (hm : m ≤ 2*U)
    (hL : x < Real.log n) (hR : Real.log m ≤ x+h) : m-n ≤ 2*U*h := by
  have hm₀ := hn.trans_le hnm
  have hl := Real.log_le_sub_one_of_pos (div_pos hn hm₀)
  rw [Real.log_div hn.ne' hm₀.ne'] at hl
  have hlog : 0 ≤ Real.log m - Real.log n := sub_nonneg.mpr (Real.log_le_log hn hnm)
  have hlow : m-n ≤ m*(Real.log m - Real.log n) := by
    have hh : 1 - (Real.log m - Real.log n) ≤ n/m := by linarith
    have hv := (le_div_iff₀ hm₀).mp hh
    linarith
  calc
    _ ≤ m*(Real.log m - Real.log n) := hlow
    _ ≤ (2*U)*(Real.log m - Real.log n) := mul_le_mul_of_nonneg_right hm hlog
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (hm₀.le.trans hm)

#print axioms diameter
end PintzLogWindow
