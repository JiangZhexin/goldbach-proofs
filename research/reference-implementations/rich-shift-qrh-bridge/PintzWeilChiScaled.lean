import PintzWeilScaleBudget
import PintzWeilChiWindow

noncomputable section
open Set Finset MeasureTheory Zeta23 Zeta23.ThmE Zeta23.Tail
open ArithmeticFunction PintzWeilTestWindow PintzWeilChiWindow
namespace PintzWeilChiScaled

/-- The primitive-character finite-zero formula at the canonical Pintz scale.
The gamma term stays explicit, independently of the truncation and endpoint bounds. -/
theorem sharp_prime_finite_zeros_scaled :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hq : 1 < q) (hprim : χ.IsPrimitive) {N x y : ℝ},
      4 ≤ N → (q : ℝ) ≤ N → 1 ≤ x → x ≤ y → y ≤ N →
      PintzWeilScaleBudget.delta N < Real.log x →
      let δ := PintzWeilScaleBudget.delta N
      let g := PintzWeilBump.scaled δ
      let Z := LZeros (LSeam_of hq hprim)
      let k := test g δ (Real.log x) (Real.log y)
      let low := (finite_low_ordinates Z (Real.sqrt N)).toFinset
      let f := fun ρ : Z.carrier => (Z.mult ρ : ℂ) * windowTerm g x y ρ
      let rhs := -(∑' n : ℕ, (vonMangoldt n:ℂ) * coeff χ n *
        (PintzWeilPrimeDesmoothing.sharp x y n:ℂ)) + gammaTerm (parity χ) q k
      ‖rhs - (∑ ρ ∈ low, f ρ)‖ ≤ C*N^(2/3:ℝ)*(1+Real.log N)^2 := by
  obtain ⟨A,hA,H⟩ := PintzWeilChiWindow.sharp_prime_finite_zeros
  let K := ∫ x : ℝ, ‖deriv (deriv (fun u => (PintzWeilBump.base u:ℂ))) x‖
  have hK : 0 ≤ K := integral_nonneg (fun _ => norm_nonneg _)
  have hA₀ : 0 ≤ A := by linarith
  refine ⟨20*Real.exp 1*A*K+8, by positivity, ?_⟩
  intro q _ χ hq hprim N x y hN hqN hx hxy hyN hlog
  dsimp only
  let δ := PintzWeilScaleBudget.delta N
  let g := PintzWeilBump.scaled δ
  have hN1 : 1 ≤ N := by linarith
  have hδ : 0 < δ := PintzWeilScaleBudget.delta_pos (by linarith)
  have hT : 2 ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have H₀ := H q χ hq hprim (g := g) (T := Real.sqrt N) hδ.le
    (PintzWeilScaleBudget.delta_le_one hN1) hx hxy hlog hT
    (PintzWeilBump.scaled_contDiff δ) (PintzWeilBump.scaled_nonneg hδ)
    (PintzWeilBump.scaled_zero_left hδ) (PintzWeilBump.scaled_zero_right hδ)
    (PintzWeilBump.scaled_mass hδ)
  dsimp only at H₀
  refine H₀.trans ?_
  let D := ∫ v : ℝ, ‖deriv (deriv (fun u => (g u:ℂ))) v‖
  have hD₀ : 0 ≤ D := integral_nonneg (fun _ => norm_nonneg _)
  have hD : D ≤ K/δ^2 := by
    dsimp only [D,g]
    rw [PintzWeilBump.scaled_deriv₂_identity hδ]
    change δ⁻¹^2*K ≤ K/δ^2
    rw [inv_pow, div_eq_mul_inv, mul_comm]
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq.le
  have hqlog := Real.log_nonneg hq1
  have hNlog := Real.log_nonneg hN1
  have hlogs := Real.log_le_log (zero_lt_one.trans_le hq1) hqN
  have hb := PintzWeilScaleBudget.tail_plus_endpoint_budget
    hN (show (1:ℝ) ≤ 1 by rfl) hN1
    (show 0 ≤ A * (1 + Real.log q) by positivity) hK hD₀ hD hx hxy hyN
  simp only [one_mul] at hb
  refine hb.trans ?_
  have hcoeff : 20 * Real.exp 1 * (A * (1 + Real.log q)) * K + 8 ≤
      (20 * Real.exp 1 * A * K + 8) * (1 + Real.log N) := by
    have h₁ := mul_le_mul_of_nonneg_left (show 1 + Real.log q ≤ 1 + Real.log N by linarith)
      (show 0 ≤ 20 * Real.exp 1 * A * K by positivity)
    have h₂ : (8:ℝ) ≤ 8 * (1 + Real.log N) := by linarith
    nlinarith [h₁, h₂]
  convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ N^(2/3:ℝ) by positivity)) (show 0 ≤ 1 + Real.log N by positivity) using 1; ring

#print axioms sharp_prime_finite_zeros_scaled
end PintzWeilChiScaled
