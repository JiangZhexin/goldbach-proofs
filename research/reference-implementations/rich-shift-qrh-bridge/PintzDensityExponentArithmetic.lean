import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace PintzDensityExponentArithmetic

/-- Real-power budget after choosing the common detector cutoff. The factor
`M⁻¹` is retained before majorizing by `M ≤ N^(1/2)`. -/
theorem cutoff_budget {N M P J C h : ℝ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hP : 0 ≤ P) (hJ : 0 ≤ J) (hC : 1 ≤ C)
    (hMN : M ≤ N ^ (1/2:ℝ)) (hPN : P ≤ N ^ (21/100:ℝ))
    (hh : 0 ≤ h) (hhmax : h ≤ 11/50)
    (hcut : J ≤ C * (P^3 * M^2)^(13/10:ℝ)) :
    M⁻¹ * N ^ (-2*h) * J ^ (2*h) ≤ C ^ (11/25:ℝ) * N ^ (-(191/5500:ℝ)*h) := by
  have hNp : 0 < N := by linarith
  have hMp : 0 < M := by linarith
  have hCp : 0 < C := by linarith
  have hp : P^3 ≤ N ^ ((63/100:ℝ)) := by
    calc
      _ ≤ (N ^ (21/100:ℝ)) ^ (3:ℕ) := pow_le_pow_left₀ hP hPN 3
      _ = _ := by rw [← Real.rpow_natCast (N ^ (21/100:ℝ)) 3, ← Real.rpow_mul hNp.le]; norm_num
  have hcut' : J ≤ C * (N^(63/100:ℝ)*M^2)^(13/10:ℝ) :=
    hcut.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_right hp (by positivity)) (by norm_num)) (by positivity))
  have hJpower := Real.rpow_le_rpow hJ hcut' (show 0 ≤ 2*h by positivity)
  have hcalc :
      M⁻¹ * N ^ (-2*h) * (C * (N^(63/100:ℝ)*M^2)^(13/10:ℝ)) ^ (2*h)
        = C^(2*h)*N^ (-(181/500:ℝ)*h)*M^((26/5:ℝ)*h-1) := by
    rw [Real.mul_rpow hCp.le (by positivity), ← Real.rpow_mul (by positivity),
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hNp.le,
      ← Real.rpow_natCast_mul hMp.le]
    simp only [Nat.cast_ofNat]
    rw [← Real.rpow_neg_one]
    rw [show (M ^ (-1:ℝ) * N ^ (-2*h) *
       (C^(2*h) * (N^((63/100:ℝ)*((13/10:ℝ)*(2*h))) * M^(2*((13/10:ℝ)*(2*h)))))) =
      C^(2*h) * (N^(-2*h) * N^((63/100:ℝ)*((13/10:ℝ)*(2*h)))) *
        (M^(-1:ℝ) * M^(2*((13/10:ℝ)*(2*h)))) by ring]
    rw [← Real.rpow_add hNp, ← Real.rpow_add hMp]
    congr 2 <;> ring
  have hMm : M^((26/5:ℝ)*h-1) ≤ N^((18/55:ℝ)*h) := by
    calc
      _ ≤ M^((36/55:ℝ)*h) := Real.rpow_le_rpow_of_exponent_le hM (by linarith)
      _ ≤ (N^(1/2:ℝ)) ^ ((36/55:ℝ)*h) := Real.rpow_le_rpow (by positivity) hMN (by positivity)
      _ = _ := by rw [← Real.rpow_mul hNp.le]; congr 1; ring
  have hCC : C^(2*h) ≤ C^(11/25:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  calc
    _ ≤ M⁻¹ * N ^ (-2*h) * (C * (N^(63/100:ℝ)*M^2)^(13/10:ℝ)) ^ (2*h) :=
      mul_le_mul_of_nonneg_left hJpower (by positivity)
    _ = C^(2*h)*N^ (-(181/500:ℝ)*h)*M^((26/5:ℝ)*h-1) := hcalc
    _ ≤ C^(11/25:ℝ)*N^ (-(181/500:ℝ)*h)*N^((18/55:ℝ)*h) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hCC (by positivity)) hMm (by positivity) (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hNp]; congr 2; ring

theorem cutoff_budget_h40 {N M P J C h : ℝ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hP : 0 ≤ P) (hJ : 0 ≤ J) (hC : 1 ≤ C)
    (hMN : M ≤ N ^ (1/2:ℝ)) (hPN : P ≤ N ^ (21/100:ℝ))
    (hh : 0 ≤ h) (hhmax : h ≤ 11/50)
    (hcut : J ≤ C * (P^3 * M^2)^(13/10:ℝ)) :
    M⁻¹ * N ^ (-2*h) * J ^ (2*h) ≤ C ^ (11/25:ℝ) * N ^ (-h/40) := by
  refine (cutoff_budget hN hM hP hJ hC hMN hPN hh hhmax hcut).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
    (by positivity)

#print axioms cutoff_budget
#print axioms cutoff_budget_h40
end PintzDensityExponentArithmetic
