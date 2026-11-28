import PintzLowRealBlock
open Finset PintzSieveToHybrid PintzLowRealBlock
namespace RichShiftLowReal263
theorem low_real_budget {N P R M T Q C h V : ℝ}
    (hN : 1 ≤ N) (hP : P ≤ N^(263/1000:ℝ))
    (hR : 0 < R) (hRP : R ≤ P) (hM : 1 ≤ M)
    (hQ : 0 ≤ Q) (hQR : Q ≤ 2*R)
    (hT : 0 ≤ T) (hTupper : T ≤ 4*P*M/R)
    (hC : 0 ≤ C) (hh : (533/2000:ℝ) ≤ h)
    (hV : V ≤ Q^2*((2*T+1)*C)) :
    M⁻¹ * N^(-2*h) * V ≤ 36*C*N^(-h/40) := by
  have hNp : 0 < N := by linarith
  have hPp : 0 < P := hR.trans_le hRP
  have hMp : 0 < M := by linarith
  have hTR := (le_div_iff₀ hR).mp hTupper
  have hR2 : R^2 ≤ P^2 := pow_le_pow_left₀ hR.le hRP _
  have hPM : P^2 ≤ P^2*M := le_mul_of_one_le_right (sq_nonneg _) hM
  have hRTR : R*(T*R) ≤ P*(4*P*M) := mul_le_mul hRP hTR (by positivity) hPp.le
  have hRbound : R^2*(2*T+1) ≤ 9*(P^2*M) := by nlinarith only [hPM,hR2,hRTR]
  have hVR : V ≤ 36*C*(P^2*M) := calc
    _ ≤ Q^2*((2*T+1)*C) := hV
    _ ≤ (2*R)^2*((2*T+1)*C) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hQ hQR 2) (by positivity)
    _ = 4*C*(R^2*(2*T+1)) := by ring
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hRbound (show 0 ≤ 4*C by positivity)]
  have hPow : P^2 * N^(-2*h) ≤ N^(-h/40) := calc
    _ ≤ (N^(263/1000:ℝ))^2 * N^(-2*h) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hPp.le hP 2) (by positivity)
    _ = N^(526/1000 + -2*h) := by
      rw [← Real.rpow_mul_natCast hNp.le, ← Real.rpow_add hNp]
      push_cast
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  calc
    _ ≤ M⁻¹ * N^(-2*h) * (36*C*(P^2*M)) :=
      mul_le_mul_of_nonneg_left hVR (by positivity)
    _ = 36*C*(P^2*N^(-2*h)) := by field_simp [hMp.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hPow (by positivity)

theorem actual_low_real_budget {N P R M T h : ℝ} {Q : ℕ}
    (hN : 1 ≤ N) (hP : P ≤ N^(263/1000:ℝ))
    (hR : 0 < R) (hRP : R ≤ P) (hM : 1 ≤ M) (hQR : (Q:ℝ) ≤ 2*R)
    (hT : 0 ≤ T) (hTupper : T ≤ 4*P*M/R) (hh : (533/2000:ℝ) ≤ h)
    (A : (Σ k : ℕ, DirichletCharacter ℂ (k+1)) → Finset ℂ)
    (hz : ∀ j ∈ family Q, ∀ ρ ∈ A j, 1/2 ≤ ρ.re ∧ ρ.re < 1)
    (hx : ∀ j ∈ family Q, ∀ ρ ∈ A j, |ρ.im| ≤ T) :
    M⁻¹ * N^(-2*h) * (∑ j ∈ family Q, ∑ ρ ∈ A j, (analyticOrderNatAt j.2.LFunction ρ : ℝ)) ≤
      36*actualC Q T*N^(-h/40) := by
  have hC : 0 ≤ actualC Q T := by
    refine le_trans ?_ (le_max_right _ _)
    exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg T])) (Real.log_nonneg (by norm_num))
  exact low_real_budget hN hP hR hRP hM (Nat.cast_nonneg _) hQR hT hTupper hC hh
    (block_count hT hC A (fun j ρ => (analyticOrderNatAt j.2.LFunction ρ : ℝ))
      (fun _ _ _ _ => Nat.cast_nonneg _) hx (actual_local_count hT A hz))


#print axioms actual_low_real_budget
end RichShiftLowReal263
