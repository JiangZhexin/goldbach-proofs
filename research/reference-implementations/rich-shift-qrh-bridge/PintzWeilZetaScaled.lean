import PintzWeilScaleBudget
import PintzWeilZetaTruncation

open Set Finset MeasureTheory Zeta23 Zeta23.Tail
noncomputable section
namespace PintzWeilZetaScaled

theorem finite_zeta_low (T : ℝ) : {ρ : zetaZeroConfig.carrier | |(ρ:ℂ).im| ≤ T}.Finite := by
  have hfin := (zetaZeroConfig.finite_window (-T-1) T).preimage_embedding
    (Function.Embedding.subtype (· ∈ zetaZeroConfig.carrier))
  refine hfin.subset ?_
  intro ρ hρ
  have h := abs_le.mp (show |(ρ:ℂ).im| ≤ T from hρ)
  refine ⟨ρ.2, ?_, h.2⟩
  change -T-1 < (ρ:ℂ).im
  linarith [h.1]

/-- The actual ζ truncation-and-desmoothing statement at the scale N.
The gamma term is still explicit in rhs; its estimation is independent. -/
theorem sharp_prime_finite_zeros_scaled :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N x y : ℝ}, 4 ≤ N → 1 ≤ x → x ≤ y → y ≤ N →
      PintzWeilScaleBudget.delta N < Real.log x →
      let δ := PintzWeilScaleBudget.delta N
      let g := PintzWeilBump.scaled δ
      let Z := zetaZeroConfig
      let k := PintzWeilTestWindow.test g δ (Real.log x) (Real.log y)
      let G := fun s : ℂ => ∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*s)
      let low := (finite_zeta_low (Real.sqrt N)).toFinset
      let term := fun ρ : Z.carrier =>
        (Z.mult ρ : ℂ) * (G ρ * (((y:ℂ)^(ρ:ℂ)-(x:ℂ)^(ρ:ℂ))/(ρ:ℂ)))
      let rhs := paperFT k (Complex.I/2) + paperFT k (-Complex.I/2) -
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          (PintzWeilPrimeDesmoothing.sharp x y n : ℂ)) +
        (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r:ℂ)
      ‖rhs - (∑ ρ ∈ low, term ρ)‖ ≤ C*N^(2/3:ℝ)*(1+Real.log N) := by
  obtain ⟨A,hA,H⟩ := PintzWeilZetaTruncation.zeta_sharp_prime_finite_zeros
  let K := ∫ x : ℝ, ‖deriv (deriv (fun u => (PintzWeilBump.base u:ℂ))) x‖
  have hK : 0 ≤ K := integral_nonneg (fun _ => norm_nonneg _)
  have hA₀ : 0 ≤ A := by linarith
  refine ⟨20*Real.exp 1*A*K+8, by positivity, ?_⟩
  intro N x y hN hx hxy hyN hlog
  dsimp only
  let δ := PintzWeilScaleBudget.delta N
  let g := PintzWeilBump.scaled δ
  have hN1 : 1 ≤ N := by linarith
  have hδ : 0 < δ := PintzWeilScaleBudget.delta_pos (by linarith)
  have hT : 2 ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have H₀ := H (g := g) (T := Real.sqrt N) hδ.le
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
  simpa only [one_mul] using PintzWeilScaleBudget.tail_plus_endpoint_budget
    hN (show (1:ℝ) ≤ 1 by rfl) hN1 hA₀ hK hD₀ hD hx hxy hyN

#print axioms sharp_prime_finite_zeros_scaled
end PintzWeilZetaScaled
