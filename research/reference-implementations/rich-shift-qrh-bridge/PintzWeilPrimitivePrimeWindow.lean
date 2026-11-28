import PintzWeilZetaPrimeWindow
import PintzWeilChiPrimeWindow
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

open Finset MeasureTheory Zeta23 Zeta23.ThmE

namespace PintzWeilPrimitivePrimeWindow

/-- Canonical primitive-character Weil zero data. Conductor one is the
Riemann zeta case, not the pole-free completed Dirichlet L-function case. -/
def zeroConfig {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) : ZeroConfig :=
  if h : q = 1 then zetaZeroConfig else
    LZeros (LSeam_of (Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (Ne.symm h)) hprim)

@[simp] theorem zeroConfig_one {χ : DirichletCharacter ℂ 1} (hprim : χ.IsPrimitive) :
    zeroConfig hprim = zetaZeroConfig := by simp [zeroConfig]

theorem zeroConfig_eq_zeta {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hq : q = 1) :
    zeroConfig hprim = zetaZeroConfig := by simp [zeroConfig, hq]

@[simp] theorem zeroConfig_eq_LZeros {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hq : 1 < q) :
    zeroConfig hprim = LZeros (LSeam_of hq hprim) := by
  simp [zeroConfig, ne_of_gt hq]

/-- Modulus-one coefficients are identically one, including at n = 0. -/
@[simp] theorem coeff_conductor_one (χ : DirichletCharacter ℂ 1) (n : ℕ) :
    coeff χ n = 1 := by
  change χ (n : ZMod 1) = 1
  rw [Subsingleton.elim (n : ZMod 1) 1, map_one]

def poleCoeff (q : ℕ) : ℂ := if q = 1 then 1 else 0

/-- Finite signed zero kernel at the shared scaling of the primitive-character window. -/
def zeroWindow (Z : ZeroConfig) (N x y : ℝ) : ℂ :=
  let g := PintzWeilBump.scaled (PintzWeilScaleBudget.delta N)
  ∑ ρ ∈ (PintzWeilChiWindow.finite_low_ordinates Z (Real.sqrt N)).toFinset,
    (Z.mult ρ : ℂ) * PintzWeilChiWindow.windowTerm g x y ρ

/-- Single sharp log-prime formula for all primitive χ (including conductor one).
The truncation height is √N and the common normalized smoothing scale is N^(-1/3).
Only the conductor-one case has an increment from the pole at s = 1. -/
theorem sharp_prime_window :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hprim : χ.IsPrimitive) {N x y : ℝ},
      4 ≤ N → (q : ℝ) ≤ N → 1 ≤ x → x ≤ y → y ≤ N →
      PintzWeilScaleBudget.delta N < Real.log x →
      ‖(∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (Real.log n:ℂ)*coeff χ n)
        - poleCoeff q * ((y:ℂ)-(x:ℂ)) + zeroWindow (zeroConfig hprim) N x y‖ ≤
        C*N^(2/3:ℝ)*(1+Real.log N)^2 := by
  obtain ⟨Cζ,hCζ,hζ⟩ := PintzWeilZetaPrimeWindow.estimate
  obtain ⟨Cχ,hCχ,hχ⟩ := PintzWeilChiPrimeWindow.sharp_prime_window
  refine ⟨max Cζ Cχ, hCζ.trans (le_max_left _ _), ?_⟩
  intro q _ χ hp N x y hN hqN hx hxy hyN hlog
  have hN1 : 1 ≤ N := by linarith
  have hln : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hL : 1 + Real.log N ≤ (1+Real.log N)^2 := by nlinarith [sq_nonneg (Real.log N)]
  have hF : 0 ≤ N^(2/3:ℝ) := Real.rpow_nonneg (by linarith) _
  by_cases hq : q = 1
  · subst q
    simp only [coeff_conductor_one, mul_one, poleCoeff, ite_true, one_mul, zeroConfig_one]
    have H := hζ hN hx hxy hyN hlog
    change ‖(∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (Real.log n:ℂ))
      - ((y:ℂ)-(x:ℂ)) + zeroWindow zetaZeroConfig N x y‖ ≤ _ at H
    exact H.trans ((mul_le_mul_of_nonneg_left hL (mul_nonneg hCζ hF)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hF) (sq_nonneg _)))
  · have hq' : 1 < q := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (Ne.symm hq)
    simp only [poleCoeff, hq, ite_false, zero_mul, sub_zero, zeroConfig_eq_LZeros hp hq']
    have H := hχ q χ hq' hp hN hqN hx hxy hyN hlog
    change ‖(∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (Real.log n:ℂ)*coeff χ n) +
      zeroWindow (LZeros (LSeam_of hq' hp)) N x y‖ ≤ _ at H
    exact H.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hF)
      (sq_nonneg _))

/-- For the actual short-interval regime the logarithmic support condition
is automatic, even as far down as x=2. -/
theorem delta_lt_log_of_two_le {N x : ℝ} (hN : 4 ≤ N) (hx : 2 ≤ x) :
    PintzWeilScaleBudget.delta N < Real.log x := by
  let δ := PintzWeilScaleBudget.delta N
  have hN0 : 0 < N := by linarith
  have hδcube : δ^3 = N⁻¹ := by
    dsimp only [δ, PintzWeilScaleBudget.delta]
    rw [← Real.rpow_mul_natCast hN0.le]
    rw [show -(1/3:ℝ) * ((3:ℕ):ℝ) = -(1:ℝ) by norm_num, Real.rpow_neg hN0.le, Real.rpow_one]
  have hδ₂ : δ < 2/3 := by
    by_contra! H
    have h := pow_le_pow_left₀ (show (0:ℝ) ≤ 2/3 by norm_num) H 3
    rw [hδcube] at h
    have hinv : N⁻¹ ≤ (4:ℝ)⁻¹ := inv_anti₀ (by norm_num) hN
    norm_num at hinv h
    linarith
  exact hδ₂.trans ((by linarith [Real.log_two_gt_d9] : (2/3:ℝ) < Real.log 2).trans_le
    (Real.log_le_log (by norm_num) hx))

/-- User-facing version for (2\le x\le y\le N): no smoothing side
condition needs to be checked separately. -/
theorem sharp_prime_window_of_two_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hprim : χ.IsPrimitive) {N x y : ℝ},
      4 ≤ N → (q : ℝ) ≤ N → 2 ≤ x → x ≤ y → y ≤ N →
      ‖(∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (Real.log n:ℂ)*coeff χ n)
        - poleCoeff q * ((y:ℂ)-(x:ℂ)) + zeroWindow (zeroConfig hprim) N x y‖ ≤
        C*N^(2/3:ℝ)*(1+Real.log N)^2 := by
  obtain ⟨C,hC,H⟩ := sharp_prime_window
  refine ⟨C,hC,?_⟩
  intro q _ χ hp N x y hN hqN hx hxy hyN
  exact H q χ hp hN hqN (by linarith) hxy hyN (delta_lt_log_of_two_le hN hx)

#print axioms zeroConfig
#print axioms coeff_conductor_one
#print axioms sharp_prime_window
#print axioms sharp_prime_window_of_two_le

end PintzWeilPrimitivePrimeWindow
