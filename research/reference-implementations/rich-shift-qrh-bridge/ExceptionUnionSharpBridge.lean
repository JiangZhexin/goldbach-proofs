import ExceptionUnionBridge

open Filter

namespace ExceptionUnionBridge

/-- An ordinary exception exponent strictly below 4/5 suffices, with any
fixed constant and with any fixed log losses absorbed into the exponent first.
The output is the exact natural-number inequality of the frozen task. -/
theorem complete_of_strict_exception_exponent {δ C : ℝ} (hδ : δ < 4/5)
    (hcount : ∀ᶠ X : ℕ in atTop, ((bad (2*X)).card : ℝ) ≤ C*(X:ℝ)^δ) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (fails X).card^5 ≤ X^4 := by
  let ε : ℝ := 4/5-δ
  let A : ℝ := max C 1
  have hε : 0 < ε := sub_pos.mpr hδ
  have hA : 0 < A := zero_lt_one.trans_le (le_max_right _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (s := ε) hε).bound (div_pos hlog2 hA)
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  apply eventually_atTop.mp
  filter_upwards [ht.eventually hp, hcount, eventually_ge_atTop (8 : ℕ)] with X hX hc h8
  have hx : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hx1 : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hl : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg hx1
  have hlog : (Nat.log 2 X : ℝ) * Real.log 2 ≤ Real.log (X : ℝ) := by
    have hab : (2 : ℝ)^(Nat.log 2 X) ≤ (X : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : X ≠ 0)
    have hh := Real.log_le_log (by positivity) hab
    rwa [Real.log_pow] at hh
  have hdiv : ((Nat.log 2 X / 2 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (X : ℝ) := by
    exact (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.div_le_self (Nat.log 2 X) 2) hlog2.le).trans hlog
  have hlogBudget : Real.log (X:ℝ) ≤ Real.log 2 / A * (X:ℝ)^ε := by
    simpa [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg hl,
      abs_of_nonneg (Real.rpow_nonneg hx.le ε)] using hX
  have hshift : ((Nat.log 2 X / 2 : ℕ) : ℝ)*A ≤ (X:ℝ)^ε := by
    have H := hdiv.trans hlogBudget
    rw [show Real.log 2 / A * (X:ℝ)^ε = ((X:ℝ)^ε/A)*Real.log 2 by ring] at H
    exact (le_div_iff₀ hA).mp (le_of_mul_le_mul_right H hlog2)
  have hfail : ((fails X).card : ℝ) ≤ (X:ℝ)^(4/5:ℝ) := calc
    _ ≤ ((Nat.log 2 X / 2 : ℕ) : ℝ) * ((bad (2*X)).card : ℝ) := by
      exact_mod_cast card_fails X h8
    _ ≤ ((Nat.log 2 X / 2 : ℕ) : ℝ) * (A * (X:ℝ)^δ) := by
      gcongr
      exact hc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    _ ≤ (X:ℝ)^ε * (X:ℝ)^δ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hshift (by positivity)
    _ = _ := by rw [← Real.rpow_add hx]; congr 1; dsimp [ε]; ring
  have H := pow_le_pow_left₀ (show 0 ≤ ((fails X).card : ℝ) by positivity) hfail 5
  have hEq : (((X:ℝ)^(4/5:ℝ))^(5:ℕ)) = (X:ℝ)^(4:ℕ) := by
    rw [← Real.rpow_natCast ((X:ℝ)^(4/5:ℝ)), ← Real.rpow_mul hx.le,
      show (4/5:ℝ)*(5:ℕ) = 4 by norm_num, Real.rpow_ofNat]
  rw [hEq] at H
  exact_mod_cast H

#print axioms complete_of_strict_exception_exponent
end ExceptionUnionBridge
