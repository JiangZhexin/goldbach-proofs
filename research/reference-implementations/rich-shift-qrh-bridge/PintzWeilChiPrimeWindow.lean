import PintzWeilChiScaled
import PintzWeilChiArchimedean
import PintzPrimePowerRemoval

noncomputable section
open Set Finset MeasureTheory Zeta23 Zeta23.ThmE Zeta23.Tail
open ArithmeticFunction PintzWeilTestWindow PintzWeilChiWindow
namespace PintzWeilChiPrimeWindow
set_option maxHeartbeats 1000000

private theorem combine (P X H V : ℂ) :
    ‖P+X‖ ≤ ‖H‖ + ‖-V+H-X‖ + ‖V-P‖ := by
  have E : P+X = H-(-V+H-X)-(V-P) := by ring
  rw [E]
  exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)

/-- The weighted primitive-character prime sum on a sharp interval, with
the absolutely uniform error including the gamma term and prime powers. -/
theorem sharp_prime_window :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hq : 1 < q) (hprim : χ.IsPrimitive) {N x y : ℝ},
      4 ≤ N → (q : ℝ) ≤ N → 1 ≤ x → x ≤ y → y ≤ N →
      PintzWeilScaleBudget.delta N < Real.log x →
      let δ := PintzWeilScaleBudget.delta N
      let g := PintzWeilBump.scaled δ
      let Z := LZeros (LSeam_of hq hprim)
      let low := (finite_low_ordinates Z (Real.sqrt N)).toFinset
      let f := fun ρ : Z.carrier => (Z.mult ρ : ℂ) * windowTerm g x y ρ
      ‖(∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
        (Real.log n:ℂ)*coeff χ n) + (∑ ρ ∈ low, f ρ)‖ ≤
          C*N^(2/3:ℝ)*(1+Real.log N)^2 := by
  obtain ⟨C,hC,hsharp⟩ := PintzWeilChiScaled.sharp_prime_finite_zeros_scaled
  let K := ∫ x : ℝ, ‖deriv (deriv (fun u => (PintzWeilBump.base u:ℂ))) x‖
  have hK : 0 ≤ K := integral_nonneg (fun _ => norm_nonneg _)
  obtain ⟨A,hA,hgamma⟩ := PintzWeilChiArchimedean.chi_archimedean_2third_power
    (show 0 < K+1 by positivity)
  refine ⟨C+A+2, by positivity, ?_⟩
  intro q _ χ hq hprim N x y hN hqN hx hxy hyN hlog
  dsimp only
  let δ := PintzWeilScaleBudget.delta N
  let g := PintzWeilBump.scaled δ
  have hδ := PintzWeilScaleBudget.delta_pos (N := N) (by linarith)
  have hD : (∫ v, ‖deriv (deriv (fun u => (g u : ℂ))) v‖) ≤ (K+1)*δ^(-2:ℝ) := by
    dsimp only [g]
    rw [PintzWeilBump.scaled_deriv₂_identity hδ]
    rw [Real.rpow_neg hδ.le]
    norm_num only [Real.rpow_ofNat]
    rw [inv_pow]
    calc (δ^2)⁻¹ * K = K * (δ^2)⁻¹ := mul_comm ..
      _ ≤ (K+1)*(δ^2)⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hδeq : N^(-1/3:ℝ) = δ := by rw [neg_div]; rfl
  have G₀ := hgamma (κ := parity χ) (q := q) (g := g) (N := N) (x := x) (y := y)
    (parity_le_one' χ) hq.le hqN hx hxy hyN
  simp only [hδeq] at G₀
  have G := G₀ hlog
    (PintzWeilBump.scaled_contDiff δ) (PintzWeilBump.scaled_nonneg hδ)
    (PintzWeilBump.scaled_zero_left hδ) (PintzWeilBump.scaled_zero_right hδ)
    (PintzWeilBump.scaled_mass hδ)
    hD
  have S := hsharp q χ hq hprim hN hqN hx hxy hyN hlog
  dsimp only at S
  have R := PintzPrimePowerRemoval.sharp_weighted hx hxy (coeff χ)
    (fun n => DirichletCharacter.norm_le_one χ _)
  have hN1 : 1 ≤ N := by linarith
  have hy1 := hx.trans hxy
  have hNlog := Real.log_nonneg hN1
  have hys : Real.sqrt y ≤ N^(2/3:ℝ) := by
    refine (Real.sqrt_le_sqrt hyN).trans ?_
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hyl : Real.log y ≤ (1+Real.log N)^2 := by
    have := Real.log_le_log (zero_lt_one.trans_le hy1) hyN
    nlinarith [sq_nonneg (Real.log N)]
  have hpw : 2*Real.sqrt y*Real.log y ≤ 2*N^(2/3:ℝ)*(1+Real.log N)^2 := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hys (by norm_num)) hyl (Real.log_nonneg hy1) (by positivity)
  have hgrow : (1+Real.log N) ≤ (1+Real.log N)^2 := by nlinarith [sq_nonneg (Real.log N)]
  have hgB : A*N^(2/3:ℝ)*(1+Real.log N) ≤ A*N^(2/3:ℝ)*(1+Real.log N)^2 := by
    exact mul_le_mul_of_nonneg_left hgrow (by positivity)
  let Z := LZeros (LSeam_of hq hprim)
  let X := ∑ ρ ∈ (finite_low_ordinates Z (Real.sqrt N)).toFinset,
    (Z.mult ρ : ℂ) * windowTerm g x y ρ
  let H := gammaTerm (parity χ) q (test g δ (Real.log x) (Real.log y))
  let P := ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (Real.log n:ℂ)*coeff χ n
  let V := ∑' n : ℕ, (vonMangoldt n:ℂ)*coeff χ n*(PintzWeilPrimeDesmoothing.sharp x y n:ℂ)
  change ‖P+X‖ ≤ _
  change ‖-V+H-X‖ ≤ _ at S
  change ‖H‖ ≤ _ at G
  change ‖V-P‖ ≤ _ at R
  calc
    ‖P+X‖ ≤ (‖H‖+‖-V+H-X‖)+‖V-P‖ := combine P X H V
    _ ≤ A*N^(2/3:ℝ)*(1+Real.log N)^2+C*N^(2/3:ℝ)*(1+Real.log N)^2+
        2*N^(2/3:ℝ)*(1+Real.log N)^2 :=
      add_le_add (add_le_add (G.trans hgB) S) (R.trans hpw)
    _ = _ := by ring

#print axioms sharp_prime_window
end PintzWeilChiPrimeWindow
