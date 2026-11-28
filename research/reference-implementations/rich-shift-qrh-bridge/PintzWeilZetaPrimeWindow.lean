import PintzWeilZetaScaled
import PintzWeilZetaArchimedean
import PintzWeilZetaPoles
import PintzPrimePowerRemoval

open Real Finset MeasureTheory Zeta23

namespace PintzWeilZetaPrimeWindow
set_option maxHeartbeats 700000

private theorem join_error (U D S P H W : ℂ) {a b c d : ℝ}
    (h1 : ‖P-W+H-S‖ ≤ a) (h2 : ‖W-U‖ ≤ b) (h3 : ‖P-D‖ ≤ c) (h4 : ‖H‖ ≤ d) :
    ‖U-D+S‖ ≤ c+d+(a+b) := by
  rw [show U-D+S = ((P-D)+H)-((P-W+H-S)+(W-U)) by ring]
  exact (norm_sub_le _ _).trans
    ((add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans
      (add_le_add (add_le_add h3 h4) (add_le_add h1 h2)))

/-- With one common bump at scale N, the actual log-prime interval sum equals
the pole increment minus the corresponding finite signed zero kernel, with
a uniform O(N^(2/3) log N) error. -/
theorem estimate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N x y : ℝ}, 4 ≤ N → 1 ≤ x → x ≤ y → y ≤ N →
      PintzWeilScaleBudget.delta N < Real.log x →
      let δ := PintzWeilScaleBudget.delta N
      let g := PintzWeilBump.scaled δ
      let Z := zetaZeroConfig
      let low := (PintzWeilZetaScaled.finite_zeta_low (Real.sqrt N)).toFinset
      let G := fun s : ℂ => ∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*s)
      let term := fun ρ : Z.carrier =>
        (Z.mult ρ : ℂ) * (G ρ * (((y:ℂ)^(ρ:ℂ)-(x:ℂ)^(ρ:ℂ))/(ρ:ℂ)))
      ‖(∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (Real.log n:ℂ)) -
        ((y:ℂ)-(x:ℂ)) + (∑ ρ ∈ low, term ρ)‖ ≤
        C*N^(2/3:ℝ)*(1+Real.log N) := by
  obtain ⟨A,hA,hS⟩ := PintzWeilZetaScaled.sharp_prime_finite_zeros_scaled
  let K := ∫ x : ℝ, ‖deriv (deriv (fun u => (PintzWeilBump.base u:ℂ))) x‖
  have hK : 0 ≤ K := by positivity
  obtain ⟨B,hB,hΓ⟩ := PintzWeilZetaArchimedean.archimedean_2third_power
    (C := K+1) (by linarith)
  refine ⟨A+B+8,by positivity,?_⟩
  intro N x y hN hx hxy hyN hlog
  dsimp only
  let δ := PintzWeilScaleBudget.delta N
  let g := PintzWeilBump.scaled δ
  let k := PintzWeilTestWindow.test g δ (Real.log x) (Real.log y)
  let Z := zetaZeroConfig
  let low := (PintzWeilZetaScaled.finite_zeta_low (Real.sqrt N)).toFinset
  let G := fun s : ℂ => ∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*s)
  let S := ∑ ρ ∈ low, (Z.mult ρ : ℂ) * (G ρ * (((y:ℂ)^(ρ:ℂ)-(x:ℂ)^(ρ:ℂ))/(ρ:ℂ)))
  let P := paperFT k (Complex.I/2) + paperFT k (-Complex.I/2)
  let H := (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r:ℂ)
  let W := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n:ℂ) *
          (PintzWeilPrimeDesmoothing.sharp x y n : ℂ)
  let U := ∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (Real.log n:ℂ)
  let D := (y:ℂ)-(x:ℂ)
  let F := N^(2/3:ℝ)
  let L := 1+Real.log N
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hδ : 0 < δ := PintzWeilScaleBudget.delta_pos hN0
  have hδ1 : δ ≤ 1 := PintzWeilScaleBudget.delta_le_one hN1
  have hg := PintzWeilBump.scaled_contDiff δ
  have hp := PintzWeilBump.scaled_nonneg hδ
  have hl := PintzWeilBump.scaled_zero_left hδ
  have hr := PintzWeilBump.scaled_zero_right hδ
  have hm := PintzWeilBump.scaled_mass hδ
  have hDg : (∫ v : ℝ, ‖deriv (deriv (fun u : ℝ => (g u:ℂ))) v‖) ≤
      (K+1)*δ^(-2:ℝ) := by
    rw [show g = PintzWeilBump.scaled δ from rfl, PintzWeilBump.scaled_deriv₂_identity hδ]
    change δ⁻¹^2*K ≤ (K+1)*δ^(-2:ℝ)
    rw [Real.rpow_neg hδ.le, Real.rpow_two, inv_pow]
    calc (δ^2)⁻¹ * K ≤ (δ^2)⁻¹ * (K+1) := by gcongr; linarith
      _ = _ := mul_comm ..
  have hδeq : N^(-1/3:ℝ) = δ := by rw [neg_div]; rfl
  have Γ0 := hΓ (g := g) (N := N) (x := x) (y := y) hx hxy hyN
  simp only [hδeq] at Γ0
  have Γ := Γ0 hlog hg hp hl hr hm hDg
  change ‖H‖ ≤ B*F at Γ
  have hH := Γ
  have h1 := hS (N := N) (x := x) (y := y) hN hx hxy hyN hlog
  change ‖P-W+H-S‖ ≤ A*F*L at h1
  have h2 : ‖W-U‖ ≤ 2*Real.sqrt y*Real.log y := by
    simpa only [mul_one,W,U] using
      PintzPrimePowerRemoval.sharp_weighted hx hxy (fun _ => (1:ℂ)) (by simp)
  have h3 := PintzWeilZetaPoles.poles_error
     (g := g) (δ := δ) (x := x) (y := y) (N := N) hδ.le hδ1
       (zero_lt_one.trans_le hx) hxy hyN hlog (hg.of_le (by norm_num)) hp hl hr hm
  rw [Complex.ofReal_sub] at h3
  change ‖P-D‖ ≤ _ at h3
  have hF : 1 ≤ F := Real.one_le_rpow hN1 (by norm_num)
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hδF : δ*N = F := by
    dsimp [δ,PintzWeilScaleBudget.delta,F]
    conv_lhs => rhs; rw [← Real.rpow_one N]
    rw [← Real.rpow_add hN0]
    norm_num
  have hsqrt : Real.sqrt y ≤ F := calc
    _ ≤ Real.sqrt N := Real.sqrt_le_sqrt hyN
    _ ≤ _ := by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (hx.trans hxy)
  have h2' : ‖W-U‖ ≤ 2*F*L := h2.trans (by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
      (by dsimp [L]; linarith [Real.log_le_log (show 0 < y by linarith) hyN])
      hlogy (by positivity))
  have h3' : ‖P-D‖ ≤ 6*F*L := h3.trans (by
    rw [show 2*δ*N=2*F by rw [mul_assoc,hδF]]
    have hFL : F ≤ F*L := le_mul_of_one_le_right (by positivity) hL
    have hLN : Real.log N+2 ≤ 2*L := by dsimp [L]; linarith [Real.log_nonneg hN1]
    have hLF : L ≤ F*L := le_mul_of_one_le_left (by positivity) hF
    linarith)
  have hH' : ‖H‖ ≤ B*F*L := hH.trans (le_mul_of_one_le_right (by positivity) hL)
  change ‖U-D+S‖ ≤ (A+B+8)*F*L
  apply (join_error U D S P H W h1 h2' h3' hH').trans_eq
  change 6*F*L+B*F*L+(A*F*L+2*F*L) = (A+B+8)*F*L
  ring

#print axioms estimate
end PintzWeilZetaPrimeWindow
