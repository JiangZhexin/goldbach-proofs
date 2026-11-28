import PintzSignedSingularSum

noncomputable section
open Finset PintzGlobalPairArithmetic PintzGlobalPairSum PintzSignedSingularSum
open scoped Classical ArithmeticFunction.Moebius
namespace PintzSignedSpecialPairs

theorem ramanujan_gauss {q : ℕ} [NeZero q] (m : ℕ) :
    gaussSum (1 : DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift (-(m:ZMod q))) =
      PintzPoleKernelTail.ramanujan q m := by
  rw [PintzPoleEuler.pole_ramanujan_eq_crt]
  unfold PintzPoleEuler.ramanujanSum PintzPoleEuler.unitSum gaussSum
  apply sum_congr rfl
  intro a _
  rw [AddChar.mulShift_apply]
  by_cases H : IsUnit a
  · rw [ite_eq_left H, MulChar.one_apply H, one_mul]
  · rw [ite_eq_right H, MulChar.map_nonunit _ H, zero_mul]

theorem principal_std_moebius {q : ℕ} [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar = (μ q : ℂ) := by
  have HE := ramanujan_gauss (q:=q) 1
  rw [principal_neg, Nat.cast_one, AddChar.mulShift_one] at HE
  rw [HE, PintzPoleRamanujan.ramanujan_eq_conj_sum]
  rw [PintzPoleRamanujan.ramanujanSum_divisor_formula q 1]
  have hS :
      (∑ d ∈ q.divisorsAntidiagonal, (μ d.1 : ℂ) *
        (if d.2 ∣ (1:ℕ) then (d.2:ℂ) else 0)) = (μ q : ℂ) := by
    rw [sum_eq_single (q,1)]
    · simp
    · intro d hd hn
      have h : ¬d.2 ∣ 1 := by
        intro H
        have h1 := Nat.dvd_one.mp H
        have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
        rw [h1,mul_one] at he
        exact hn (Prod.ext he h1)
      simp [h]
    · intro H
      exfalso
      exact H (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one _,NeZero.ne _⟩)
  rw [hS]
  simp

theorem primitive_τ_mul_inv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar = χ (-1) * (q:ℂ) := by
  rw [gaussSum_inv_eq_conj, mul_left_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    DirichletCharacter.norm_gaussSum_stdAddChar hχ, Real.sq_sqrt (Nat.cast_nonneg _),
    Complex.ofReal_natCast]

theorem actual_mixed {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (m : ℕ) :
    actual χ 1 m = (μ q : ℂ) * χ (m:ZMod q) * (q:ℂ) / (q.totient:ℂ)^2 := by
  unfold actual
  rw [mul_one χ, gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ.inv, inv_inv,
    principal_std_moebius]
  have h (x y z w : ℂ) : x*y*(z*w) = y*z*(x*w) := by ring
  rw [h, primitive_τ_mul_inv hχ, ← mul_assoc,
    mul_assoc (μ q:ℂ) (χ (-(m:ZMod q))) (χ (-1)), ← map_mul]
  simp

theorem actual_inverse_pair {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (m : ℕ) :
    actual χ χ⁻¹ m = χ (-1) * (q:ℂ) * PintzPoleKernelTail.ramanujan q m / (q.totient:ℂ)^2 := by
  unfold actual
  rw [mul_inv_cancel, inv_one, ramanujan_gauss, primitive_τ_mul_inv hχ]

theorem actual_quadratic_diag {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hQ : χ*χ = 1) (m : ℕ) :
    actual χ χ m = χ (-1) * (q:ℂ) * PintzPoleKernelTail.ramanujan q m / (q.totient:ℂ)^2 := by
  have he : χ = χ⁻¹ := by
    calc
      χ = χ * (χ * χ⁻¹) := by simp
      _ = χ⁻¹ := by rw [← mul_assoc, hQ, one_mul]
  nth_rw 2 [he]
  exact actual_inverse_pair hχ m

theorem singular_mixed {q m : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hm : m ≠ 0) (he : Even m) :
    twistedSeries χ (1 : DirichletCharacter ℂ 1) m =
      ((μ q : ℂ) * χ (m:ZMod q) * (q:ℂ) / (q.totient:ℂ)^2) *
        (singularSeries m / forcedProduct q m : ℝ) := by
  have h1 : (1 : DirichletCharacter ℂ 1).IsPrimitive := DirichletCharacter.conductor_one
  rw [twistedSeries_ratio hχ h1 hm he, Nat.lcm_one_right, row, dite_eq_right (NeZero.ne q),
    dite_eq_left (show q ∣ q ∧ 1 ∣ q from ⟨dvd_refl _,one_dvd _⟩),
    DirichletCharacter.changeLevel_self, DirichletCharacter.changeLevel_one, actual_mixed hχ]

theorem singular_quadratic_diag {q m : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hQ : χ*χ = 1) (hm : m ≠ 0) (he : Even m) :
    twistedSeries χ χ m =
      (χ (-1) * (q:ℂ) * PintzPoleKernelTail.ramanujan q m / (q.totient:ℂ)^2) *
        (singularSeries m / forcedProduct q m : ℝ) := by
  rw [twistedSeries_ratio hχ hχ hm he, Nat.lcm_self, row, dite_eq_right (NeZero.ne q),
    dite_eq_left (show q ∣ q ∧ q ∣ q from ⟨dvd_refl _,dvd_refl _⟩),
    DirichletCharacter.changeLevel_self, actual_quadratic_diag hχ hQ]

#print axioms singular_mixed
#print axioms singular_quadratic_diag
#print axioms actual_mixed
#print axioms actual_quadratic_diag
end PintzSignedSpecialPairs
