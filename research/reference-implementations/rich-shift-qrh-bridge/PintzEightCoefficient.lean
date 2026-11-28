import PintzEightPrimitiveEnergy

noncomputable section
open Finset MeasureTheory PintzEightEnergy PintzEightConductors PintzEightRegroup
open scoped Classical
namespace PintzEightCoefficient

def slice (q : ℕ) [NeZero q] (a : ZMod q)
    (F : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ) (x : ℝ) :=
  (∑ χ : DirichletCharacter ℂ q,
      χ a * gaussSum χ⁻¹ ZMod.stdAddChar * F χ.conductor χ.primitiveCharacter x) / (q.totient : ℂ)

def coeff (Q : ℝ) (q : ℕ) (B : (q : ℕ) → ZMod q → ℝ → ℂ)
    (F : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ a : ZMod q, ∫ x in -(width Q q)..width Q q, (@slice q ⟨hq⟩ a F x)^2 * B q a x

theorem coeff_le_energy {P : ℕ} {Q : ℝ} (hQ : 0 < Q)
    (F : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ)
    (B : (q : ℕ) → ZMod q → ℝ → ℂ) (hB : ∀ q a x, ‖B q a x‖ = 1) :
    ‖∑ q ∈ Icc 1 P, coeff Q q B F‖ ≤
      ∑ q ∈ Icc 1 P, PintzEightPrimitiveEnergy.arcEnergy Q q F := by
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro q hq
  have hqp : 0 < q := (mem_Icc.mp hq).1
  rw [coeff, PintzEightPrimitiveEnergy.arcEnergy, dite_eq_right hqp.ne', dite_eq_right hqp.ne']
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro a _
  have hu : 0 ≤ width Q q := by unfold width; positivity
  refine (intervalIntegral.norm_integral_le_integral_norm (by linarith : -(width Q q) ≤ width Q q)).trans_eq ?_
  apply intervalIntegral.integral_congr
  intro x _
  change ‖(@slice q ⟨hqp.ne'⟩ a F x)^2 * B q a x‖ = ‖@slice q ⟨hqp.ne'⟩ a F x‖^2
  rw [norm_mul, hB, mul_one, norm_pow]

#print axioms coeff_le_energy
end PintzEightCoefficient
