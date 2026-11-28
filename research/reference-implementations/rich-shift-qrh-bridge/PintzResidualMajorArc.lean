import PintzPrimitiveDensityEnergy
import PintzEightCoefficient
import PintzConductorReindex

open Finset MeasureTheory PintzWeilPrimitivePrimeWindow PintzPrimitiveResidual
open PintzEightRegroup PintzEightEnergy PintzEightConductors PintzSieveToHybrid

namespace PintzResidualMajorArc

/-- The actual finite primitive-character Fourier residual used in (8.25),
using the discrete increments of the common pole/near-zero model. -/
noncomputable def residual (N a v b : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (η : ℝ) : ℂ := by
  classical
  exact if hq : q ≠ 0 then
    letI : NeZero q := ⟨hq⟩
    if hp : χ.IsPrimitive then
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊v⌋₊, (primeCoeff χ n -
        PintzDiscreteZeroModel.increment (retainedModel (zeroConfig hp) q N b) n) *
          Complex.exp ((2*Real.pi*η*Complex.I)*(n:ℝ))
    else 0
  else 0

theorem residual_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (N a v b η : ℝ) :
    residual N a v b q χ η =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊v⌋₊, (primeCoeff χ n -
        PintzDiscreteZeroModel.increment (retainedModel (zeroConfig hp) q N b) n) *
          Complex.exp ((2*Real.pi*η*Complex.I)*(n:ℝ)) := by
  classical simp [residual, NeZero.ne q, hp]

theorem residual_continuous (N a v b : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) :
    Continuous (residual N a v b q χ) := by
  change Continuous (fun η => residual N a v b q χ η)
  by_cases hq : q = 0
  · have he (η : ℝ) : residual N a v b q χ η = 0 := by classical simp [residual,hq]
    simp_rw [he]
    exact continuous_const
  letI : NeZero q := ⟨hq⟩
  by_cases hp : χ.IsPrimitive
  · simp_rw [residual_eq χ hp]
    fun_prop
  · have he (η : ℝ) : residual N a v b q χ η = 0 := by classical simp [residual,hq,hp]
    simp_rw [he]
    exact continuous_const

theorem primitive_sum (P : ℕ) (Q : ℝ)
    (F : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℂ) :
    (∑ r ∈ Icc 1 P, primEnergy Q F r) =
      ∑ j ∈ family P, intervalEnergy (PintzEightRegroup.width Q (j.1+1)) (F (j.1+1) j.2) := by
  classical
  rw [family, sum_sigma]
  refine Finset.sum_bij (fun r _ => r-1) ?_ ?_ ?_ ?_
  · intro r hr
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp hr
    exact mem_range.mpr (by omega)
  · intro r hr s hs h
    have hr₁ := (mem_Icc.mp hr).1
    have hs₁ := (mem_Icc.mp hs).1
    omega
  · intro k hk
    have hk' := mem_range.mp hk
    exact ⟨k+1, mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro r hr
    have h : r-1+1=r := by have := (mem_Icc.mp hr).1; omega
    let G (r : ℕ) := ∑ χ ∈ prims r, intervalEnergy (PintzEightRegroup.width Q r) (F r χ)
    change G r = G (r-1+1)
    rw [h]

theorem window_width {N : ℝ} {P r : ℕ} (hN : 0 < N) (hP : 0 < P) (hr : 0 < r) :
    PintzEightRegroup.width (N/(P:ℝ)) r =
      1/(2*PintzPrimitiveDensityEnergy.width N P r) := by
  have hP' : (0:ℝ) < P := by exact_mod_cast hP
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  unfold PintzEightRegroup.width PintzPrimitiveDensityEnergy.width
  field_simp [hP'.ne',hr'.ne',hN.ne']

/-- Once the actual primitive sum is bounded, reconstruction on every
translated major arc costs only the previously checked two logarithms. -/
theorem coefficient_transfer :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) {N a v b V : ℝ}, 1 ≤ P → 0 < N →
      (∑ j ∈ family P,
        intervalEnergy (1/(2*PintzPrimitiveDensityEnergy.width N P (j.1+1)))
          (residual N a v b (j.1+1) j.2)) ≤ V →
      ∀ (B : (q : ℕ) → ZMod q → ℝ → ℂ), (∀ q a t, ‖B q a t‖ = 1) →
      ‖∑ q ∈ Icc 1 P, PintzEightCoefficient.coeff (N/(P:ℝ)) q B (residual N a v b)‖ ≤
        A*(1+Real.log P)^2*V := by
  obtain ⟨A,hA,hS⟩ := PintzEightPrimitiveEnergy.energy_log_squared
  refine ⟨A,hA,?_⟩
  intro P N a v b V hP hN hV B hB
  have hP0 : 0 < P := hP
  have hQ : 0 < N/(P:ℝ) := by positivity
  have hE := hS P (N/(P:ℝ)) hP hQ (residual N a v b) (residual_continuous N a v b)
  rw [primitive_sum] at hE
  refine (PintzEightCoefficient.coeff_le_energy hQ (residual N a v b) B hB).trans
    (hE.trans ?_)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  convert hV using 1
  apply sum_congr rfl
  intro j _
  rw [window_width hN hP0 (by omega)]
  push_cast
  rfl

#print axioms residual_eq
#print axioms primitive_sum
#print axioms coefficient_transfer
end PintzResidualMajorArc
