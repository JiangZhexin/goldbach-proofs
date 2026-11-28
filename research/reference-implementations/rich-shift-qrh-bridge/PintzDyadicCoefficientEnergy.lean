import PintzHybridStripOverlap
import PintzDetectorFinite
import OAI.NumberTheory.Ostmann.Arithmetic.DivisorSquareMean

open Finset PintzHybridDiscrete PintzHybridStrip

namespace PintzDyadicCoefficientEnergy

/-- The clipped dyadic energy with up to k logarithmic derivatives of the
actual nonprincipal detector coefficients. -/
theorem energy {U : ℕ} (hU : 1 ≤ U) (L J k : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑ n ∈ (Ioc U (2*U)).filter (fun n => L < n ∧ n ≤ J),
        ‖reScale (PintzDetectorFinite.coeff L) σ n‖ ^ 2 * (Real.log n) ^ (2*k)) ≤
      2 * (1 + Real.log (2*U : ℝ)) ^ (3+2*k) * (U:ℝ) ^ (1-2*σ) := by
  have hUR : (1:ℝ) ≤ U := by exact_mod_cast hU
  have hUp : (0:ℝ) < U := by positivity
  let Z : ℝ := 1 + Real.log (2*U:ℝ)
  have hZ : 0 ≤ Z := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 2*U by linarith)
    dsimp [Z]; linarith
  let C : ℝ := (U:ℝ)^(-2*σ) * Z^(2*k)
  have hc : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ n ∈ (Ioc U (2*U)).filter (fun n => L < n ∧ n ≤ J),
        C * (n.divisors.card:ℝ)^2 := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hnU, hn2⟩ := mem_Ioc.mp (mem_filter.mp hn).1
      have hnU' : (U:ℝ) ≤ n := by exact_mod_cast hnU.le
      have hn2' : (n:ℝ) ≤ 2*U := by exact_mod_cast hn2
      have hnp : (0:ℝ) < n := hUp.trans_le hnU'
      have hn1 : (1:ℝ) ≤ n := hUR.trans hnU'
      have hl : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
      have hlZ : Real.log (n:ℝ) ≤ Z := (Real.log_le_log hnp hn2').trans
        (by dsimp [Z]; linarith)
      have hpow : (n:ℝ)^(-2*σ) ≤ (U:ℝ)^(-2*σ) :=
        Real.rpow_le_rpow_of_nonpos hUp hnU' (by linarith)
      have hdiv := pow_le_pow_left₀ (norm_nonneg _) (PintzDetectorFinite.coeff_norm L n) 2
      have hlog := pow_le_pow_left₀ hl hlZ (2*k)
      have heq : Real.exp (-σ * Real.log n)^2 = (n:ℝ)^(-2*σ) := by
        rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos hnp]
        congr 1
        ring
      rw [reScale, norm_mul, Complex.norm_exp, mul_pow]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, mul_zero, sub_zero]
      rw [heq]
      dsimp [C]
      calc
        _ ≤ ((n.divisors.card:ℝ)^2 * (U:ℝ)^(-2*σ)) * Z^(2*k) :=
          mul_le_mul (mul_le_mul hdiv hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity))
            hlog (by positivity) (by positivity)
        _ = _ := by ring
    _ ≤ C * ((2*U:ℝ) * Z^3) := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ hc
      refine (sum_le_sum_of_subset_of_nonneg (t := Icc 1 (2*U)) ?_ (fun n _ _ => by positivity)).trans ?_
      · intro n hn
        obtain ⟨hnU, hn2⟩ := mem_Ioc.mp (mem_filter.mp hn).1
        exact mem_Icc.mpr ⟨by omega, hn2⟩
      · simpa [Z] using OAI.Ostmann.Arithmetic.DivisorSquareMean.divisor_square_mean (2*U)
    _ = _ := by
      dsimp [C]
      rw [show (1-2*σ : ℝ) = 1+(-2*σ) by ring, Real.rpow_add hUp, Real.rpow_one, pow_add]
      dsimp [Z]
      ring

#print axioms energy
end PintzDyadicCoefficientEnergy
