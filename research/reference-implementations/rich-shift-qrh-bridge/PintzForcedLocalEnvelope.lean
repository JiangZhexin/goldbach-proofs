import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace PintzForcedLocalEnvelope

/-- Classical local Goldbach factor at (p), with (
u=v_p(m)). -/
def ordinary (p ν : ℕ) : ℝ :=
  if ν = 0 then (p:ℝ) * (p-2:ℝ) / (p-1:ℝ)^2 else (p:ℝ)/(p-1:ℝ)

theorem small_branch {p ν : ℕ} (hp : p.Prime) (hm : p = 2 → 0 < ν) :
    (p:ℝ)/(p-1:ℝ)^2 ≤ ordinary p ν := by
  have h₂ : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hd : 0 < (p-1:ℝ) := by linarith
  unfold ordinary
  split_ifs with hν
  · have h₃ : (3:ℝ) ≤ p := by
      exact_mod_cast (show 3 ≤ p by have := hp.two_le; by_contra! h; exact (Nat.ne_of_lt (hm (by omega))) hν.symm)
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ (p:ℝ) by positivity) (show 0 ≤ (p:ℝ)-3 by linarith)]
  · apply div_le_div_of_nonneg_left (by positivity) hd
    nlinarith [mul_nonneg hd.le (show 0 ≤ (p:ℝ)-2 by linarith)]

/-- Both primitive inputs, nonprincipal product. The exceptional small primes
are expressed by the two local conductor facts, leaving a purely real bound. -/
theorem nonprincipal_branch {p α β ν : ℕ} (hp : p.Prime)
    (hβ : 0 < β) (hα : β ≤ α) (hν : α-β = ν)
    (hm : p = 2 → 0 < ν) (hβ₂ : p = 2 → 2 ≤ β)
    (h₃ : p = 3 → α = 1 → β = 0) :
    ((p:ℝ)/(p-1:ℝ))^2 * (p:ℝ)^(-((β:ℝ)/2)) ≤ ordinary p ν := by
  have h₂ : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0:ℝ) < p := by linarith
  have hd : 0 < (p-1:ℝ) := by linarith
  let x : ℝ := (p:ℝ)^((β:ℝ)/2)
  have hx : 0 < x := Real.rpow_pos_of_pos hpos _
  rw [Real.rpow_neg hpos.le]
  change ((p:ℝ)/(p-1:ℝ))^2 * x⁻¹ ≤ ordinary p ν
  have hsqrt : Real.sqrt (p:ℝ) ≤ x := by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have : (1:ℝ) ≤ β := by exact_mod_cast hβ
    linarith
  unfold ordinary
  split_ifs with hz
  · have hh : (p:ℝ) ≤ ((p:ℝ)-2)*x := by
      by_cases hp3 : p = 3
      · have hn : 2 ≤ β := by
          by_contra! hf
          have hα1 : α = 1 := by omega
          have := h₃ hp3 hα1
          omega
        have hpx : (p:ℝ) ≤ x := by
          conv_lhs => rw [← Real.rpow_one (p:ℝ)]
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          have : (2:ℝ) ≤ β := by exact_mod_cast hn
          linarith
        norm_num [hp3] at hpx ⊢
        exact hpx
      · have hp5 : 5 ≤ p := by
          have hpne2 : p ≠ 2 := fun e => (Nat.ne_of_lt (hm e)) hz.symm
          have hpne4 : p ≠ 4 := by
            rintro rfl
            exact Nat.not_prime_mul (a := 2) (b := 2) (by decide) (by decide) hp
          have := hp.two_le
          omega
        have hp5R : (5:ℝ) ≤ p := by exact_mod_cast hp5
        have hs : 2 ≤ Real.sqrt (p:ℝ) := (Real.le_sqrt (by norm_num) hpos.le).mpr (by linarith)
        have hs' : (p:ℝ) ≤ ((p:ℝ)-2) * Real.sqrt (p:ℝ) := by
          have he := Real.sq_sqrt hpos.le
          have h : Real.sqrt (p:ℝ) ≤ (p:ℝ)-2 := by
            nlinarith [mul_nonneg (show 0 ≤ Real.sqrt (p:ℝ)-2 by linarith) (Real.sqrt_nonneg (p:ℝ))]
          nlinarith [mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg (p:ℝ))]
        exact hs'.trans (mul_le_mul_of_nonneg_left hsqrt (by linarith))
    have hprim : (p:ℝ)^2 ≤ (p:ℝ) * ((p:ℝ)-2) * x := by nlinarith [mul_le_mul_of_nonneg_left hh hpos.le]
    rw [div_pow, ← div_eq_mul_inv, div_div]
    exact (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hd) hx) (sq_pos_of_pos hd)).mpr
      (by simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hprim (sq_nonneg ((p:ℝ)-1)))
  · have hh : (p:ℝ) ≤ ((p:ℝ)-1)*x := by
      by_cases h : p = 2
      · have hpx : (p:ℝ) ≤ x := by
          conv_lhs => rw [← Real.rpow_one (p:ℝ)]
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          have : (2:ℝ) ≤ β := by exact_mod_cast hβ₂ h
          linarith
        norm_num [h] at hpx ⊢
        exact hpx
      · have hp3 : (3:ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
        have he := Real.sq_sqrt hpos.le
        have h1 : 1 ≤ Real.sqrt (p:ℝ) := (Real.le_sqrt (by norm_num) hpos.le).mpr (by linarith)
        have hs : Real.sqrt (p:ℝ) ≤ (p:ℝ)-1 := by
          by_contra! hh
          have hs' := mul_lt_mul_of_pos_right hh (show 0 < (p:ℝ)-1 - Real.sqrt (p:ℝ) + 2*Real.sqrt (p:ℝ) by linarith)
          nlinarith [mul_nonneg (show 0 ≤ (p:ℝ)-3 by linarith) (show 0 ≤ (p:ℝ)-1 by linarith)]
        have h' := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (p:ℝ))
        exact (show (p:ℝ) ≤ ((p:ℝ)-1)*Real.sqrt (p:ℝ) by nlinarith).trans
          (mul_le_mul_of_nonneg_left hsqrt hd.le)
    rw [div_pow, ← div_eq_mul_inv, div_div]
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hd) hx) hd).mpr
    have hm' := mul_le_mul_of_nonneg_right hh (mul_nonneg hpos.le hd.le)
    nlinarith

/-- Ramanujan branch for a principal product (both original factors primitive). -/
theorem principal_branch {p α ν : ℕ} (hp : p.Prime) (hα : 0 < α)
    (hm : p = 2 → 0 < ν) :
    (if α ≤ ν then (p:ℝ)/(p-1:ℝ) else
        if α = ν+1 then (p:ℝ)/(p-1:ℝ)^2 else 0) ≤ ordinary p ν := by
  by_cases h : α ≤ ν
  · have hν : ν ≠ 0 := by omega
    simp [ordinary, h, hν]
  · by_cases h' : α = ν+1
    · simpa [h, h'] using small_branch hp hm
    · have h₂ : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
      simp only [ite_eq_right h, ite_eq_right h', ordinary]
      split_ifs <;> exact div_nonneg (by first | positivity | nlinarith) (by first | positivity | linarith)

#print axioms small_branch
#print axioms nonprincipal_branch
#print axioms principal_branch
end PintzForcedLocalEnvelope
