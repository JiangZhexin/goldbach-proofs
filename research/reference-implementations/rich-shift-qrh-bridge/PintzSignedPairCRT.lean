import PintzFixedLCMRow

noncomputable section
open Finset PintzGaussCRT PintzCRTConductor PintzGlobalPairArithmetic PintzGlobalPairSum
namespace PintzSignedPairCRT

theorem left_inv {a b : ℕ} (h : a.Coprime b) (χ : DirichletCharacter ℂ (a*b)) :
    left h χ⁻¹ = (left h χ)⁻¹ := by
  ext1 x
  change χ⁻¹ ((ZMod.chineseRemainder h).symm (↑x,1)) = _
  rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv']
  rfl

theorem right_inv {a b : ℕ} (h : a.Coprime b) (χ : DirichletCharacter ℂ (a*b)) :
    right h χ⁻¹ = (right h χ)⁻¹ := by
  ext1 x
  change χ⁻¹ ((ZMod.chineseRemainder h).symm (1,↑x)) = _
  rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv']
  rfl

theorem shift_phase {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (u : (ZMod q)ˣ) (x : ZMod q) :
    gaussSum χ ((ZMod.stdAddChar.mulShift u).mulShift x) =
      χ⁻¹ u * gaussSum χ (ZMod.stdAddChar.mulShift x) := by
  have he : (ZMod.stdAddChar.mulShift u).mulShift x = (ZMod.stdAddChar.mulShift x).mulShift u := by
    rw [AddChar.mulShift_mulShift, AddChar.mulShift_mulShift, mul_comm (u : ZMod q)]
  rw [he, gaussSum_mulShift_eq]

theorem std_shift_phase {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (u : (ZMod q)ˣ) :
    gaussSum χ (ZMod.stdAddChar.mulShift u) = χ⁻¹ u * gaussSum χ ZMod.stdAddChar := by
  simpa only [AddChar.mulShift_one] using shift_phase χ u 1

theorem unit_cancel {q : ℕ} (χ ψ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    χ⁻¹ u * ψ⁻¹ u * (χ*ψ) u = 1 := by
  rw [← MulChar.mul_apply, ← MulChar.mul_apply]
  rw [show χ⁻¹ * ψ⁻¹ * (χ*ψ) = 1 by
    calc
      _ = (χ⁻¹*χ)*(ψ⁻¹*ψ) := by ac_rfl
      _ = _ := by simp]
  exact MulChar.one_apply_coe _

set_option maxHeartbeats 1000000 in
/-- The CRT unit phases in all three Gauss factors of the exact complex
pair coefficient cancel. -/
theorem exact_actual_crt {a b : ℕ} [NeZero a] [NeZero b] [NeZero (a*b)] (h : a.Coprime b)
    (χ ψ : DirichletCharacter ℂ (a*b)) (m : ℕ) :
    actual χ ψ m = actual (left h χ) (left h ψ) m * actual (right h χ) (right h ψ) m := by
  let e := (ZMod.chineseRemainder h).symm
  have hg (η : DirichletCharacter ℂ (a*b)) :
      gaussSum η ZMod.stdAddChar =
        gaussSum (left h η) (ZMod.stdAddChar.mulShift (leftUnit h)) *
        gaussSum (right h η) (ZMod.stdAddChar.mulShift (rightUnit h)) := by
    have H := exact_crt h η ZMod.stdAddChar (1,1)
    dsimp only at H
    have he : (ZMod.chineseRemainder h).symm (1,1) = 1 := map_one e
    simpa only [he, Prod.fst, Prod.snd, AddChar.mulShift_one, left_add_normalize h, right_add_normalize h]
      using H
  have hn (η : DirichletCharacter ℂ (a*b)) :
      gaussSum η (ZMod.stdAddChar.mulShift (-(m:ZMod (a*b)))) =
        gaussSum (left h η) ((ZMod.stdAddChar.mulShift (leftUnit h)).mulShift (-(m:ZMod a))) *
        gaussSum (right h η) ((ZMod.stdAddChar.mulShift (rightUnit h)).mulShift (-(m:ZMod b))) := by
    have H := exact_crt h η ZMod.stdAddChar (-(m:ZMod a),-(m:ZMod b))
    dsimp only at H
    have he : (ZMod.chineseRemainder h).symm (-(m:ZMod a),-(m:ZMod b)) = -(m:ZMod (a*b)) := by
      change e (-(m:ZMod a × ZMod b)) = _
      rw [map_neg,map_natCast]
    simpa only [he, left_add_normalize h, right_add_normalize h] using H
  unfold actual
  rw [hg χ, hg ψ, hn (χ*ψ)⁻¹, left_inv, right_inv, left_mul, right_mul]
  simp_rw [std_shift_phase, shift_phase, inv_inv, Nat.totient_mul h, Nat.cast_mul, mul_pow,
    div_eq_mul_inv, mul_inv_rev]
  have ha := unit_cancel (left h χ) (left h ψ) (leftUnit h)
  have hb := unit_cancel (right h χ) (right h ψ) (rightUnit h)
  -- Move each coordinate's three unit phases together before cancelling them.
  calc
    _ = ((left h χ)⁻¹ (leftUnit h) * (left h ψ)⁻¹ (leftUnit h) *
        (left h χ*left h ψ) (leftUnit h)) *
        ((right h χ)⁻¹ (rightUnit h) * (right h ψ)⁻¹ (rightUnit h) *
        (right h χ*right h ψ) (rightUnit h)) *
        ((gaussSum (left h χ) ZMod.stdAddChar * gaussSum (left h ψ) ZMod.stdAddChar *
          gaussSum ((left h ψ)⁻¹*(left h χ)⁻¹) (ZMod.stdAddChar.mulShift (-(m:ZMod a))) *
          ((a.totient:ℂ)^2)⁻¹) *
         (gaussSum (right h χ) ZMod.stdAddChar * gaussSum (right h ψ) ZMod.stdAddChar *
          gaussSum ((right h ψ)⁻¹*(right h χ)⁻¹) (ZMod.stdAddChar.mulShift (-(m:ZMod b))) *
          ((b.totient:ℂ)^2)⁻¹)) := by ring
    _ = _ := by rw [ha,hb,one_mul,one_mul]

#print axioms exact_actual_crt
end PintzSignedPairCRT
