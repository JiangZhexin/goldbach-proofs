import PintzJutilaMollifierBound

open Finset

noncomputable section
namespace PintzJutilaLogRamp

def ramp (z₁ z₂ : ℝ) (d : ℕ) : ℝ :=
  if d = 0 then 0 else
  if (d:ℝ) ≤ z₁ then 1 else
  if (d:ℝ) ≤ z₂ then (Real.log z₂-Real.log d)/(Real.log z₂-Real.log z₁) else 0

def coeff (z₁ z₂ : ℝ) (d : ℕ) : ℂ := (ArithmeticFunction.moebius d:ℂ) * (ramp z₁ z₂ d:ℂ)

theorem ramp_mem {z₁ z₂ : ℝ} (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (d : ℕ) :
    ramp z₁ z₂ d ∈ Set.Icc (0:ℝ) 1 := by
  unfold ramp
  split_ifs with h0 hd1 hd2 <;> try simp
  have hd : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero h0
  have h := Real.log_lt_log h₁ h₁₂
  have hL := Real.log_le_log hd hd2
  have hU := Real.log_le_log h₁ (le_of_not_ge hd1)
  exact ⟨div_nonneg (by linarith) (by linarith),
    (div_le_iff₀ (by linarith)).mpr (by linarith)⟩

theorem coeff_norm {z₁ z₂ : ℝ} (h₁ : 0 < z₁) (h₁₂ : z₁ < z₂) (d : ℕ) :
    ‖coeff z₁ z₂ d‖ ≤ 1 := by
  have h := ramp_mem h₁ h₁₂ d
  have hμ : ‖(ArithmeticFunction.moebius d:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one : |ArithmeticFunction.moebius d| ≤ 1)
  rw [coeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1]
  exact mul_le_one₀ hμ h.1 h.2

theorem coeff_support (z₁ z₂ : ℝ) (d : ℕ) (hd : d ∉ Icc 1 ⌊z₂⌋₊)
    (hz : z₁ ≤ z₂) : coeff z₁ z₂ d = 0 := by
  by_cases h0 : d = 0
  · simp [coeff, ramp, h0]
  · have h2 : ¬(d:ℝ) ≤ z₂ := fun h => hd
      (mem_Icc.mpr ⟨Nat.pos_of_ne_zero h0,Nat.le_floor h⟩)
    have h1 : ¬(d:ℝ) ≤ z₁ := fun h => h2 (h.trans hz)
    simp [coeff, ramp, h0, h1, h2]

theorem coeff_short {z₁ z₂ : ℝ} {d : ℕ} (hd0 : d ≠ 0) (hd : (d:ℝ) ≤ z₁) :
    coeff z₁ z₂ d = (ArithmeticFunction.moebius d:ℂ) := by
  simp [coeff, ramp, hd0, hd]

theorem divisor_short {z₁ z₂ : ℝ} {n : ℕ}
    (hn₀ : 0 < n) (hn₁ : (n:ℝ) ≤ z₁) :
    (∑ d ∈ n.divisors, coeff z₁ z₂ d) = if n=1 then 1 else 0 := by
  have h (d) (hd : d ∈ n.divisors) :
      coeff z₁ z₂ d = (ArithmeticFunction.moebius d:ℂ) :=
    coeff_short (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn₀).ne'
      ((by exact_mod_cast Nat.le_of_dvd hn₀ (Nat.dvd_of_mem_divisors hd) : (d:ℝ) ≤ n).trans hn₁)
  rw [sum_congr rfl h, ← Int.cast_sum]
  have H := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta n
  rw [ArithmeticFunction.coe_mul_zeta_apply] at H
  rw [H, ArithmeticFunction.one_apply]
  split <;> simp

#print axioms coeff_norm
#print axioms coeff_support
#print axioms divisor_short
end PintzJutilaLogRamp
