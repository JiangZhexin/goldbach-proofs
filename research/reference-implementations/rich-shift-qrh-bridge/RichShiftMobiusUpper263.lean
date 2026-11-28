import RichShiftMobiusDetector
import RichShiftGammaHalf
import PintzJutilaEdgeL

open Complex PintzJutilaMellinShift PintzJutilaAnalytic RichShiftMobiusDetector
namespace RichShiftMobiusUpper263

theorem upper {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      1 < q → χ.IsPrimitive → ∀ (L : ℕ) {ρ : ℂ}, 1/2 ≤ ρ.re → χ.LFunction ρ = 0 →
      ∀ {Y : ℝ}, 0 < Y →
      ‖∑' n : ℕ, LSeries.term (twisted (fun n => χ n) (cutMu L) 1) ρ n *
        (Real.exp (-(n:ℝ)/Y):ℂ)‖ ≤
      C*Y^(-ρ.re)*((q:ℝ)*(1+|ρ.im|))^(1/2+ε)*L*
        (1+Real.log ((1-ρ.re)⁻¹)) := by
  obtain ⟨C,hC,H⟩ := RichShiftGammaHalf.exact_detector_norm_bound
  obtain ⟨A,hA,HA⟩ := PintzJutilaEdgeL.edge_bound hε
  refine ⟨C*A,by positivity,?_⟩
  intro q _ χ hq hp L ρ hβ hρ Y hY
  have hχ : χ ≠ 1 := by
    intro h
    rw [DirichletCharacter.IsPrimitive,h,DirichletCharacter.conductor_one] at hp
    omega
  let Q := (q:ℝ)*(1+|ρ.im|)
  let p : ℝ := 1/2+ε
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  have hL (u : ℝ) : ‖χ.LFunction ((ρ.im+u:ℝ)*Complex.I)‖ ≤ A*Q^p*(1+|u|) := by
    have H' := HA q χ hq hp (ρ.im+u)
    have hE (t : ℝ) : PintzJutilaGammaRatio.z 0 t = (t:ℂ)*Complex.I := by
      simp [PintzJutilaGammaRatio.z,mul_comm]
    rw [hE] at H'
    have hqU : (q:ℝ)*(1+|ρ.im+u|) ≤ Q*(1+|u|) := by
      have he : 1+|ρ.im+u| ≤ (1+|ρ.im|)*(1+|u|) := by
        nlinarith [abs_add_le ρ.im u,mul_nonneg (abs_nonneg ρ.im) (abs_nonneg u)]
      dsimp [Q]
      exact (mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ q)).trans_eq (by ring)
    calc
      _ ≤ A*((q:ℝ)*(1+|ρ.im+u|))^p := H'
      _ ≤ A*(Q*(1+|u|))^p := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hqU hp0) hA.le
      _ = A*Q^p*(1+|u|)^p := by rw [Real.mul_rpow (by dsimp [Q]; positivity) (by positivity)]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp [Q]; positivity)
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (show (1:ℝ) ≤ 1+|u| by linarith [abs_nonneg u]) hp1
  have hM (u : ℝ) :
      ‖mollifier χ (cutMu L) (Finset.Icc 1 L) 1 ((ρ.im+u:ℝ)*Complex.I)‖ ≤ (L:ℝ) :=
    mollifier_le_length χ L (by simp [Complex.mul_re])
  have hb := H q χ hχ (cutMu L) (Finset.Icc 1 L) (by simp)
    (fun d hd => by simp [cutMu,hd]) (r:=1) (by simp) hβ hρ hY
    (show 0 ≤ A*Q^p by dsimp [Q]; positivity) (by positivity : (0:ℝ) ≤ L) hL hM
  exact hb.trans_eq (by dsimp [Q,p]; ring)

#print axioms upper
end RichShiftMobiusUpper263
