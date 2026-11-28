import RichShiftCutoffs263
import RichShiftDetectorBudgetWide263
import PintzDetectorLogBudget

noncomputable section
open Finset PintzSieveToHybrid PintzJutilaDetectorSplit RichShiftMobiusDetector
namespace RichShiftCountTransfer263

theorem scale_transfer {N P M h C J : ℝ}
    (hN : 1 ≤ N) (hP : 1 ≤ P) (hM : 1 ≤ M) (hC : 1 ≤ C)
    (hPN : P ≤ N^(263/1000:ℝ)) (hMN : M ≤ N^(1/2:ℝ))
    (h0 : 0 ≤ h) (hh : h ≤ 533/2000) (hJ0 : 0 ≤ J)
    (hJ : J ≤ C*P^((2501/1000)/(1-h))*M^((1501/1000)/(1-h))) :
    J ≤ C*N^3 ∧ M⁻¹*N^(-2*h)*J^(2*h) ≤ C*N^(-h/40) := by
  have hN0 : 0 < N := by linarith
  have hP0 : 0 < P := by linarith
  have hM0 : 0 < M := by linarith
  have hd : 0 < 1-h := by linarith
  constructor
  · have hp : (2501/1000:ℝ)/(1-h) ≤ 4 := (div_le_iff₀ hd).mpr (by linarith)
    have hm : (1501/1000:ℝ)/(1-h) ≤ 3 := (div_le_iff₀ hd).mpr (by linarith)
    have hP' : P^((2501/1000)/(1-h)) ≤ N^(1052/1000:ℝ) := by
      calc
        _ ≤ P^(4:ℝ) := Real.rpow_le_rpow_of_exponent_le hP hp
        _ ≤ (N^(263/1000:ℝ))^(4:ℝ) := Real.rpow_le_rpow hP0.le hPN (by norm_num)
        _ = _ := by rw [← Real.rpow_mul hN0.le]; congr 1 <;> norm_num
    have hM' : M^((1501/1000)/(1-h)) ≤ N^(3/2:ℝ) := by
      calc
        _ ≤ M^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hM hm
        _ ≤ (N^(1/2:ℝ))^(3:ℝ) := Real.rpow_le_rpow hM0.le hMN (by norm_num)
        _ = _ := by rw [← Real.rpow_mul hN0.le]; congr 1 <;> norm_num
    refine hJ.trans ?_
    calc
      _ ≤ C*N^(1052/1000:ℝ)*N^(3/2:ℝ) := by gcongr
      _ = C*N^(1052/1000+3/2:ℝ) := by rw [mul_assoc,← Real.rpow_add hN0]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  · let p := (2501/1000:ℝ)/(1-h)
    let m := (1501/1000:ℝ)/(1-h)
    have hp : 0 ≤ p := by dsimp [p]; positivity
    have hm : 0 ≤ m := by dsimp [m]; positivity
    have hH : 0 ≤ 2*h := by linarith
    have hpow := Real.rpow_le_rpow hJ0 hJ hH
    change J^(2*h) ≤ (C*P^p*M^m)^(2*h) at hpow
    rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by linarith) (by positivity),
      ← Real.rpow_mul hP0.le,← Real.rpow_mul hM0.le] at hpow
    have hCv : C^(2*h) ≤ C := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hC (by linarith : 2*h ≤ 1)
    have hP' : P^(p*(2*h)) ≤ N^((263/1000)*(p*(2*h))) := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow hP0.le hPN (by positivity)
    have hc : J^(2*h) ≤ C*N^((263/1000)*(p*(2*h)))*M^(m*(2*h)) :=
      hpow.trans (by gcongr)
    calc
      _ ≤ M⁻¹*N^(-2*h)*(C*N^((263/1000)*(p*(2*h)))*M^(m*(2*h))) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = C*(N^(RichShiftDetectorBudgetWide263.a h)*M^(RichShiftDetectorBudgetWide263.d h)) := by
        rw [show M⁻¹ = M^(-1:ℝ) by rw [Real.rpow_neg_one]]
        calc
          _ = C*(N^(-2*h)*N^((263/1000)*(p*(2*h)))*(M^(-1:ℝ)*M^(m*(2*h)))) := by ring
          _ = _ := by
            rw [← Real.rpow_add hN0,← Real.rpow_add hM0]
            have ha : -2*h+263/1000*(p*(2*h)) = RichShiftDetectorBudgetWide263.a h := by
              dsimp [RichShiftDetectorBudgetWide263.a,p]; ring
            have hb : -1+m*(2*h) = RichShiftDetectorBudgetWide263.d h := by
              dsimp [RichShiftDetectorBudgetWide263.d,m]; ring
            rw [ha,hb]
      _ ≤ C*N^(-h/30) := mul_le_mul_of_nonneg_left
        (RichShiftDetectorBudgetWide263.weighted_saving hN hM hMN h0 hh) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by linarith)

#print axioms scale_transfer
end RichShiftCountTransfer263
