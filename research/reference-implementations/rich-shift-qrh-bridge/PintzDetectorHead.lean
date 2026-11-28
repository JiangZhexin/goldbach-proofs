import PintzDetectorFinite
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

open Finset

namespace PintzDetectorHead

noncomputable def twist {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) : ℂ :=
  χ (n : ZMod q) * (n : ℂ)^(-s)

theorem twist_mul {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (d k : ℕ) :
    twist χ s (d*k) = twist χ s d * twist χ s k := by
  unfold twist
  rw [show ((d*k : ℕ):ZMod q) = (d:ZMod q)*(k:ZMod q) by push_cast; rfl, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

theorem twist_norm {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) {n : ℕ} (hn : 0 < n) :
    ‖twist χ s n‖ ≤ (n : ℝ)^(-s.re) := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn : (0:ℝ) < n) (-s)
  rw [Complex.ofReal_natCast, Complex.neg_re] at h
  rw [twist, norm_mul, h]
  exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)

/-- The fixed two-term Möbius head is bounded away from zero in the retained
zero-detector band; no estimate on the imaginary part is needed. -/
theorem head_lower {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) {b : ℝ}
    (hs : s.re ≤ 1-b) :
    min 1 ((2:ℝ)^b - 1) ≤ ‖twist χ s 1 - 2*twist χ s 2‖ := by
  have h1 : twist χ s 1 = 1 := by simp [twist]
  rw [h1]
  by_cases hu : IsUnit (2 : ZMod q)
  · have hχ : ‖χ (2 : ZMod q)‖ = 1 := χ.unit_norm_eq_one hu.unit
    have he : ‖(2:ℂ)*twist χ s 2‖ = (2:ℝ)^(1-s.re) := by
      simp only [twist, Nat.cast_ofNat, norm_mul, Complex.norm_ofNat, hχ, one_mul]
      rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos
        (by norm_num : (0:ℝ) < 2), Complex.neg_re, sub_eq_add_neg,
        Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
    have hp : (2:ℝ)^b ≤ (2:ℝ)^(1-s.re) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have H := norm_add_le (1:ℂ) (2*twist χ s 2-1)
    rw [add_sub_cancel, norm_one, norm_sub_rev, he] at H
    exact (min_le_right _ _).trans (by linarith)
  · have hχ := χ.map_nonunit hu
    have h2 : twist χ s 2 = 0 := by simp [twist, hχ]
    rw [h2, mul_zero, sub_zero, norm_one]
    exact min_le_left _ _

theorem head_constant_pos {b : ℝ} (hb : 0 < b) :
    0 < min 1 ((2:ℝ)^b-1) :=
  lt_min zero_lt_one (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hb))

#print axioms twist_mul
#print axioms twist_norm
#print axioms head_lower
#print axioms head_constant_pos

end PintzDetectorHead
