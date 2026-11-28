import PintzFiniteArcDifference
import PintzMajorArcPrimeEnergy

open Finset MeasureTheory Zeta23.ThmE
open PintzEightLiteralReconstruction PintzEightCoefficient
open PintzResidualMajorArc PintzWeilPrimitivePrimeWindow PintzPrimitiveResidual

namespace PintzSection8LiteralModels

noncomputable def primes (a v : ℝ) : Finset ℕ := (Ioc ⌊a⌋₊ ⌊v⌋₊).filter Nat.Prime

noncomputable def full (a v : ℝ) (θ : ℝ) : ℂ :=
  PintzMajorArcPrimeEnergy.poly (primes a v) (fun n => (Real.log n:ℂ)) θ

/-- On primitive characters only, this is exactly the polynomial of
the discretized pole/near-zero model. On nonprimitive characters the
value is immaterial since reconstruction always uses χ*. -/
noncomputable def retained (N a v b : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (η : ℝ) : ℂ :=
  primeTwist (primes a v) (fun n => (Real.log n:ℂ)) q χ η -
    residual N a v b q χ η

private theorem phase_eq (x : ℝ) :
    PintzEightGauss.additivePhase x = PintzPoleKernelTail.phase x := by
  unfold PintzEightGauss.additivePhase PintzPoleKernelTail.phase
  simp [circleMap]
  congr 1
  ring

private theorem phase_shift (n : ℕ) (η : ℝ) :
    PintzEightGauss.additivePhase ((n:ℝ)*η) =
      Complex.exp ((2*Real.pi*η*Complex.I)*(n:ℝ)) := by
  unfold PintzEightGauss.additivePhase
  simp only [circleMap,Complex.ofReal_one,one_mul,zero_add]
  congr 1
  push_cast
  ring

theorem retained_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (N a v b η : ℝ) :
    retained N a v b q χ η =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊v⌋₊,
        PintzDiscreteZeroModel.increment (retainedModel (zeroConfig hp) q N b) n *
          Complex.exp ((2*Real.pi*η*Complex.I)*(n:ℝ)) := by
  classical
  unfold retained primeTwist primes
  rw [residual_eq χ hp, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  rw [phase_shift]
  unfold primeCoeff Zeta23.ThmE.coeff
  by_cases hn : n.Prime <;> simp only [hn, ite_true, ite_false, zero_sub, zero_mul] <;> ring

/-- Literal prime model decomposition on each reduced translated arc.
It is an identity, with no size estimate or disjointness assumption. -/
theorem actual_slice {q a₀ : ℕ} [NeZero q] (ha₀ : a₀.Coprime q)
    {N a v b : ℝ} (ha : (q:ℝ) ≤ a) (η : ℝ) :
    slice q (a₀:ZMod q) (residual N a v b) η =
      full a v (η+(a₀:ℝ)/q) - slice q (a₀:ZMod q) (retained N a v b) η := by
  have ht (n) (hn : n ∈ primes a v) : q<n ∧ n.Prime := by
    obtain ⟨hl,hp⟩ := mem_filter.mp hn
    have h := (Nat.floor_lt ((Nat.cast_nonneg (α:=ℝ) q).trans ha : 0 ≤ a)).mp (mem_Ioc.mp hl).1
    exact ⟨by exact_mod_cast ha.trans_lt h,hp⟩
  have h := reconstruct_residual ha₀ (primes a v) ht (fun n => (Real.log n:ℂ)) η (retained N a v b)
  have he :
      (fun r χ x => primeTwist (primes a v) (fun n => (Real.log n:ℂ)) r χ x - retained N a v b r χ x)
        = residual N a v b := by
    funext r χ x
    unfold retained
    ring
  rw [he] at h
  simpa only [full,PintzMajorArcPrimeEnergy.poly, phase_eq, add_comm η ((a₀:ℝ)/q)] using h

#print axioms retained_eq
#print axioms actual_slice
end PintzSection8LiteralModels
