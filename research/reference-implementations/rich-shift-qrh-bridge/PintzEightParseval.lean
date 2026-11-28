import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
open Finset
open scoped ComplexConjugate Classical
namespace PintzEightParseval

variable {q : ℕ} [NeZero q]

private theorem charGram (χ ψ : DirichletCharacter ℂ q) :
    (∑ a : ZMod q, χ a * conj (ψ a)) =
      if χ = ψ then (q.totient : ℂ) else 0 := by
  classical
  simp only [← Complex.star_def, MulChar.star_apply', ← MulChar.mul_apply]
  split_ifs with h
  · subst ψ
    rw [mul_inv_cancel, MulChar.sum_one_eq_card_units]
    simp [ZMod.card_units_eq_totient]
  · exact MulChar.sum_eq_zero_of_ne_one (fun e => h (mul_inv_eq_one.mp e))

theorem pointwise_parseval (c : DirichletCharacter ℂ q → ℂ) :
    (∑ a : ZMod q, ‖∑ χ : DirichletCharacter ℂ q, χ a * c χ‖ ^ 2) =
      (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖c χ‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, sum_mul, mul_sum]
  rw [sum_comm]
  simp_rw [sum_comm (s := (univ : Finset (ZMod q)))]
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
        (c χ * conj (c ψ)) * ∑ a : ZMod q, χ a * conj (ψ a) := by
      simp_rw [mul_sum]
      congr 1; ext χ
      congr 1; ext ψ
      exact sum_congr rfl fun _ _ => by ring
    _ = _ := by
      simp only [charGram, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
      exact sum_congr rfl fun _ _ => by ring

#print axioms pointwise_parseval
end PintzEightParseval
