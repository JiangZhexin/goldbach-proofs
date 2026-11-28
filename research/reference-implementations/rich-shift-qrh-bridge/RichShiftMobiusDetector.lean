import PintzJutilaDetectorExact
import PintzJutilaMollifierBound

noncomputable section
open Complex Finset PintzJutilaMellinShift PintzJutilaAnalytic

namespace RichShiftMobiusDetector

def cutMu (L d : ℕ) : ℂ :=
  if d ∈ Finset.Icc 1 L then (ArithmeticFunction.moebius d : ℂ) else 0

theorem contour_at_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (L : ℕ) {ρ : ℂ} (hβ : 0 < ρ.re) (hρ : χ.LFunction ρ = 0)
    {Y : ℝ} (hY : 0 < Y) :
    ((∑' n : ℕ, LSeries.term (twisted (fun n => χ n) (cutMu L) 1) ρ n *
        (Real.exp (-(n:ℝ)/Y):ℂ)) =
      (1/(2*Real.pi):ℂ) * ∫ u : ℝ,
        (Y:ℂ)^(verticalPoint (-ρ.re) u) * Complex.Gamma (verticalPoint (-ρ.re) u) *
          (χ.LFunction (verticalPoint 0 (ρ.im+u)) *
            mollifier χ (cutMu L) (Finset.Icc 1 L) 1 (verticalPoint 0 (ρ.im+u)))) ∧
      MeasureTheory.Integrable (fun u : ℝ =>
        (Y:ℂ)^(verticalPoint (-ρ.re) u) * Complex.Gamma (verticalPoint (-ρ.re) u) *
          (χ.LFunction (verticalPoint 0 (ρ.im+u)) *
            mollifier χ (cutMu L) (Finset.Icc 1 L) 1 (verticalPoint 0 (ρ.im+u)))) := by
  have H := PintzJutilaDetectorExact.equation_2_11_shift_package χ hχ
    (cutMu L) (Finset.Icc 1 L) (by simp) (fun d hd => by simp [cutMu, hd])
    (r := 1) (by simp) hβ hρ hY (η := 0) le_rfl hβ
  simpa only [zero_sub] using H

theorem mollifier_le_length {q : ℕ} (χ : DirichletCharacter ℂ q) (L : ℕ)
    {s : ℂ} (hs : s.re = 0) :
    ‖mollifier χ (cutMu L) (Finset.Icc 1 L) 1 s‖ ≤ (L:ℝ) := by
  have H := PintzJutilaMollifierBound.norm_mollifier χ hs (cutMu L) (Finset.Icc 1 L)
    (by simp) (fun d hd => by
      rw [cutMu, ite_eq_left hd, Complex.norm_intCast, ← Int.cast_abs]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one :
        |ArithmeticFunction.moebius d| ≤ 1)) (r := 1) (by simp)
  simpa [PintzJutilaMollifierBound.envelope] using H

#print axioms contour_at_zero
#print axioms mollifier_le_length
end RichShiftMobiusDetector
