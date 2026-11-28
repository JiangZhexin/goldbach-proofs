import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace RichShiftDetectorBudgetWide263

noncomputable def a (h : ℝ) : ℝ := (263/1000 * (5 + 2/1000) / (1-h) - 2)*h
noncomputable def d (h : ℝ) : ℝ := (3 + 2/1000)*h/(1-h) - 1

theorem low_deficit_bounds {h : ℝ} (h0 : 0 ≤ h) (hhi : h ≤ 533/2000) :
    a h ≤ -h/30 ∧ a h + d h/2 ≤ -h/30 := by
  have hd : 0 < 1-h := by linarith
  constructor
  · unfold a
    have H : (263/1000 * (5 + 2/1000) : ℝ) ≤ (2-1/30)*(1-h) := by linarith
    have H' := (div_le_iff₀ hd).mpr H
    have := mul_le_mul_of_nonneg_right (show
      (263/1000 * (5 + 2/1000) : ℝ)/(1-h)-2 ≤ -1/30 by linarith) h0
    linarith
  · unfold a d
    have H : ((263/1000*(5+2/1000) : ℝ)/(1-h)-2)*h +
        (((3+2/1000)*h/(1-h)-1)/2) ≤ -h/30 ↔
        (263/1000*(5+2/1000)-2*(1-h))*h +
          ((3+2/1000)*h-(1-h))/2 ≤ (-h/30)*(1-h) := by
      constructor <;> intro H
      · have H' := mul_le_mul_of_nonneg_right H hd.le
        convert H' using 1 <;> field_simp [hd.ne']
      · apply (le_of_mul_le_mul_right ?_ hd)
        convert H using 1 <;> field_simp [hd.ne']
    apply H.mpr
    nlinarith [mul_nonneg h0 (show 0 ≤ 533/2000-h by linarith)]

theorem weighted_saving {N M h : ℝ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hMN : M ≤ N^(1/2:ℝ)) (h0 : 0 ≤ h) (hhi : h ≤ 533/2000) :
    N^(a h) * M^(d h) ≤ N^(-h/30) := by
  have ⟨ha, had⟩ := low_deficit_bounds h0 hhi
  have hpos : 0 < N := zero_lt_one.trans_le hN
  by_cases hD : 0 ≤ d h
  · calc
      _ ≤ N^(a h) * (N^(1/2:ℝ))^(d h) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hMN hD) (by positivity)
      _ = N^(a h + d h/2) := by
        rw [← Real.rpow_mul hpos.le, ← Real.rpow_add hpos]; congr 1 <;> ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN had
  · have hb : M^(d h) ≤ 1 := calc
      _ ≤ M^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hM (le_of_not_ge hD)
      _ = _ := Real.rpow_zero M
    calc
      _ ≤ N^(a h) * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ _ := by rw [mul_one]; exact Real.rpow_le_rpow_of_exponent_le hN ha

#print axioms weighted_saving
end RichShiftDetectorBudgetWide263
