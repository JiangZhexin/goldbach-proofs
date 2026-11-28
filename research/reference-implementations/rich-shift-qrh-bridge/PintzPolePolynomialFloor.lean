import PintzPoleFiniteSeries
import PintzPoleDivisorSubpower

open Filter

namespace PintzPolePolynomialFloor

open PintzPoleKernelTail PintzPoleFiniteSeries

/-- The divisor cutoff needed for the pole floor is automatic for every
fixed positive polynomial scale of P, uniformly for 0<m≤X. -/
theorem uniform_small_divisor_loss {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ X : ℕ in atTop, ∀ P m : ℕ, (X:ℝ)^θ ≤ (P:ℝ) →
      0 < m → m ≤ X → 360*(m.divisors.card:ℝ) ≤ Real.sqrt (P:ℝ) := by
  let ε := θ/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C,hC,hdiv⟩ := PintzPoleDivisorSubpower.quadratic_divisor_bound ε hε
  have hlimit := (tendsto_rpow_atTop hε).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun X : ℕ => (X:ℝ)) atTop atTop)
  filter_upwards [hlimit.eventually_ge_atTop (360*C)] with X hX
  change 360*C ≤ (X:ℝ)^ε at hX
  intro P m hP hm hmX
  have hmXr : (m:ℝ) ≤ X := by exact_mod_cast hmX
  have hmR : 0 ≤ (m:ℝ) := by positivity
  have hXR : 0 < (X:ℝ) := by exact_mod_cast hm.trans_le hmX
  have h := (hdiv m hm.ne').trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hmR hmXr hε.le) hC.le)
  calc
    _ ≤ (360*C)*((X:ℝ)^ε) := by
      have ht := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 360)
      linarith only [ht]
    _ ≤ (X:ℝ)^ε * (X:ℝ)^ε := mul_le_mul_of_nonneg_right hX (by positivity)
    _ = (X:ℝ)^(θ/2) := by
      rw [← Real.rpow_add hXR, show ε+ε = θ/2 by dsimp [ε]; ring]
    _ ≤ Real.sqrt (P:ℝ) := by
      rw [Real.sqrt_eq_rpow, show θ/2 = θ*(1/2) by ring, Real.rpow_mul hXR.le]
      exact Real.rpow_le_rpow (by positivity) hP (by norm_num)

/-- Eventual linear lower bound for the explicit pole model with any fixed
positive polynomial width parameter. This statement contains no assumptions
on zero locations or any convergence of a singular series. -/
theorem polynomial_pole_floor {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ X : ℕ in atTop, ∀ P L N m : ℕ, 2 ≤ P → 2*P ≤ X →
      (X:ℝ)^θ ≤ (P:ℝ) → 0 < m → m ≤ X → Even m →
      2*L ≤ m → m-2*L < N → X ≤ 4*(m-2*L+1) →
      (X:ℝ)/8 ≤ (weightedPole P X L N m).re := by
  filter_upwards [uniform_small_divisor_loss hθ] with X hX
  intro P L N m hP hPX hpow hm hmX he hLm hN hs
  exact pole_model_floor P X L N m hP hPX hm he hLm hN hs (hX P m hpow hm hmX)

#print axioms polynomial_pole_floor
end PintzPolePolynomialFloor
