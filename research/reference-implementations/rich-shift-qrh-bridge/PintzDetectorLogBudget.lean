import PintzActualWeightedZeta
import PintzActualWeightedNonprincipal

namespace PintzDetectorLogBudget

theorem detector_poly {N P M C : ℝ} {J : ℕ} (hN : 1 ≤ N)
    (hP : 0 ≤ P) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hPN : P ≤ N^(21/100:ℝ)) (hMN : M ≤ N^(1/2:ℝ))
    (hJ : (J:ℝ) ≤ C*(P^3*M^2)^(13/10:ℝ)) :
    (J:ℝ) ≤ C*N^3 := by
  have hN0 : 0 < N := by linarith
  have hPN' : P ≤ N^(1/3:ℝ) := hPN.trans
    (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
  have h1 : P^3 ≤ N := calc
    _ ≤ (N^(1/3:ℝ))^3 := pow_le_pow_left₀ hP hPN' _
    _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have h2 : M^2 ≤ N := calc
    _ ≤ (N^(1/2:ℝ))^2 := pow_le_pow_left₀ hM hMN _
    _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hProd : P^3*M^2 ≤ N^2 := by
    simpa only [pow_two] using mul_le_mul h1 h2 (by positivity) (by positivity)
  have hp : (P^3*M^2)^(13/10:ℝ) ≤ N^3 := calc
    _ ≤ (N^2)^(13/10:ℝ) := Real.rpow_le_rpow (by positivity) hProd (by norm_num)
    _ = N^(13/5:ℝ) := by rw [← Real.rpow_natCast_mul hN0.le]; norm_num
    _ ≤ N^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    _ = _ := by norm_num
  exact hJ.trans (mul_le_mul_of_nonneg_left hp hC)

theorem raw_log_factor {N C D : ℝ} {J L : ℕ}
    (hN : 1 ≤ N) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hJ : 1 ≤ J) (hL : 1 ≤ L) (hLJ : L ≤ J) (hJL : (J:ℝ) ≤ C*N^3)
    {B : ℕ} (hB : (B:ℝ) ≤ D*(1+Real.log N)) :
    (B:ℝ)*(((Nat.log 2 (J/L)).succ:ℕ):ℝ)^2*(1+Real.log (2*J:ℝ))^7 ≤
      (D*(1+(3+Real.log (2*C))/Real.log 2)^2*(4+Real.log (2*C))^7) *
        (1+Real.log N)^10 := by
  let u := 1 + Real.log N
  let a := Real.log (2*C)
  have hu : 1 ≤ u := by dsimp [u]; linarith [Real.log_nonneg hN]
  have ha : 0 ≤ a := Real.log_nonneg (by linarith)
  have ha2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 < C := by linarith
  have hN0 : 0 < N := by linarith
  have h2J : (0:ℝ) < 2*J := by positivity
  have hlog : Real.log (2*J:ℝ) ≤ a+3*Real.log N := by
    have h := Real.log_le_log h2J (show (2*J:ℝ) ≤ (2*C)*N^3 by linarith)
    rwa [Real.log_mul (x := 2*C) (y := N^3) (by positivity) (by positivity), Real.log_pow, Nat.cast_ofNat] at h
  have hJ2 : 1 ≤ J/L := Nat.div_pos hLJ hL
  have hPow : (2:ℝ)^(Nat.log 2 (J/L)) ≤ (J:ℝ) := by
    exact_mod_cast (Nat.pow_log_le_self 2 (by omega : J/L ≠ 0)).trans (Nat.div_le_self J L)
  have hh := Real.log_le_log (by positivity) hPow
  rw [Real.log_pow] at hh
  have hNat : ((Nat.log 2 (J/L):ℕ):ℝ) ≤ (a+3*Real.log N)/Real.log 2 := by
    apply (le_div_iff₀ ha2).2
    exact hh.trans ((Real.log_le_log (by positivity : 0 < (J:ℝ)) (by nlinarith [Nat.cast_nonneg (α := ℝ) J] : (J:ℝ) ≤ 2*J)).trans hlog)
  have hK : (((Nat.log 2 (J/L)).succ:ℕ):ℝ) ≤ (1+(3+a)/Real.log 2)*u := by
    rw [Nat.cast_succ]
    calc
      _ ≤ (a+3*Real.log N)/Real.log 2+1 := by linarith
      _ ≤ ((3+a)*u)/Real.log 2+u := by
        apply add_le_add _ hu
        apply div_le_div_of_nonneg_right _ ha2.le
        dsimp [u]
        nlinarith [mul_nonneg ha (Real.log_nonneg hN)]
      _ = _ := by ring
  have hLog : 1+Real.log (2*J:ℝ) ≤ (4+a)*u := by
    dsimp [u]
    nlinarith [mul_nonneg ha (Real.log_nonneg hN)]
  change _ ≤ (D*(1+(3+a)/Real.log 2)^2*(4+a)^7)*u^10
  calc
    _ ≤ (D*u)*(((1+(3+a)/Real.log 2)*u)^2)*(((4+a)*u)^7) := by
      apply mul_le_mul
      · exact mul_le_mul hB (pow_le_pow_left₀ (by positivity) hK _) (by positivity) (by positivity)
      · apply pow_le_pow_left₀ _ hLog
        have hh := Real.log_nonneg (show (1:ℝ) ≤ 2*J by
          have h : (1:ℝ) ≤ J := by exact_mod_cast hJ
          linarith)
        linarith
      · have hh := Real.log_nonneg (show (1:ℝ) ≤ 2*J by
          have h : (1:ℝ) ≤ J := by exact_mod_cast hJ
          linarith)
        positivity
      · positivity
    _ = _ := by ring

#print axioms detector_poly
#print axioms raw_log_factor
end PintzDetectorLogBudget
