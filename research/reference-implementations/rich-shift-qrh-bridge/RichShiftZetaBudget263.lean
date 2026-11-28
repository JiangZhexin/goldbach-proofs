import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace RichShiftZetaBudget263

theorem low {N P M T h C J : ℝ} (hN : 1 ≤ N) (hP : 1 ≤ P) (hM : 1 ≤ M)
    (hPN : P ≤ N^(263/1000:ℝ)) (hT : 0 ≤ T) (hTM : T ≤ 4*P*M)
    (hC : 1 ≤ C) (hJ0 : 0 ≤ J) (hJ : J ≤ C*(1+T)^(13/5:ℝ))
    (hh : 0 ≤ h) (hhi : h ≤ 67/500) :
    M⁻¹ * N^(-2*h) * J^(2*h) ≤ (5*C) * N^(-h/40) := by
  have hNp : 0 < N := by linarith
  have hMp : 0 < M := by linarith
  have hprod : 1 ≤ P*M := one_le_mul_of_one_le_of_one_le hP hM
  have hT' : 1+T ≤ 5*N^(263/1000:ℝ)*M := by
    have haux := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPN (by norm_num : (0:ℝ) ≤ 5)) hMp.le
    nlinarith only [haux, hprod, hTM]
  have hJ' : J^(2*h) ≤ (C*(5*N^(263/1000:ℝ)*M)^(13/5:ℝ))^(2*h) := by
    refine Real.rpow_le_rpow hJ0 ?_ (by positivity)
    exact hJ.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hT' (by norm_num)) (by linarith))
  have hfact :
      M⁻¹*N^(-2*h)*(C*(5*N^(263/1000:ℝ)*M)^(13/5:ℝ))^(2*h) =
        C^(2*h)*5^((26/5:ℝ)*h)*N^(-(1581/2500:ℝ)*h)*M^((26/5:ℝ)*h-1) := by
    rw [Real.mul_rpow (by linarith : 0 ≤ C) (by positivity), ← Real.rpow_mul (by positivity)]
    rw [Real.mul_rpow (by positivity) hMp.le, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 5) (by positivity), ← Real.rpow_mul hNp.le]
    rw [← Real.rpow_neg_one]
    rw [show M^(-1:ℝ)*N^(-2*h)*(C^(2*h)*
          (5^((13/5:ℝ)*(2*h))*N^((263/1000:ℝ)*((13/5:ℝ)*(2*h)))*M^((13/5:ℝ)*(2*h)))) =
        C^(2*h)*5^((13/5:ℝ)*(2*h))*(N^(-2*h)*N^((263/1000:ℝ)*((13/5:ℝ)*(2*h))))*
         (M^(-1:ℝ)*M^((13/5:ℝ)*(2*h))) by ring]
    rw [← Real.rpow_add hNp, ← Real.rpow_add hMp]
    rw [show (13/5:ℝ)*(2*h) = (26/5:ℝ)*h by ring]
    rw [show -(2:ℝ)*h + (263/1000)*(26/5*h) = -(1581/2500)*h by ring,
      show (-1:ℝ)+26/5*h = 26/5*h-1 by ring]
  have h1 : C^(2*h) ≤ C := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hC (by linarith : 2*h ≤ 1)
  have h2 : (5:ℝ)^((26/5)*h) ≤ 5 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤5)
      (by linarith : (26/5)*h ≤ 1)
  have h3 : N^(-(1581/2500:ℝ)*h) ≤ N^(-h/40) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h4 : M^((26/5:ℝ)*h-1) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hM (by linarith : (26/5)*h-1 ≤ 0)
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ' (by positivity)
    _ = _ := hfact
    _ ≤ C*5*N^(-h/40)*1 := by gcongr
    _ = _ := by ring

theorem high {N P M T h C D : ℝ} (hN : 1 ≤ N) (hP : 1 ≤ P) (hM : 1 ≤ M)
    (hPN : P ≤ N^(263/1000:ℝ)) (hT : 0 ≤ T) (hTM : T ≤ 4*P*M)
    (hC : 0 ≤ C) (hh : 67/500 ≤ h) (hD : D ≤ C*(2*T+1)) :
    M⁻¹ * N^(-2*h) * D ≤ (9*C) * N^(-h/40) := by
  have hNp : 0 < N := by linarith
  have hMp : 0 < M := by linarith
  have hprod : 1 ≤ P*M := one_le_mul_of_one_le_of_one_le hP hM
  have hD' : D ≤ (9*C)*P*M := by
    have ht : 2*T+1 ≤ 9*(P*M) := by nlinarith only [hTM,hprod]
    exact hD.trans ((mul_le_mul_of_nonneg_left ht hC).trans_eq (by ring))
  calc
    _ ≤ M⁻¹*N^(-2*h)*((9*C)*P*M) := mul_le_mul_of_nonneg_left hD' (by positivity)
    _ = (9*C)*N^(-2*h)*P := by field_simp [hMp.ne']
    _ ≤ (9*C)*N^(-2*h)*N^(263/1000:ℝ) := mul_le_mul_of_nonneg_left hPN (by positivity)
    _ = (9*C)*N^(-2*h+263/1000) := by rw [mul_assoc, ← Real.rpow_add hNp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by positivity)

#print axioms low
#print axioms high
end RichShiftZetaBudget263
