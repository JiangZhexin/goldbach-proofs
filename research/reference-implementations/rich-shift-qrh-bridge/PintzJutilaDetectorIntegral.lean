import PintzJutilaMellinShift
import PintzJutilaAnalytic
import Zeta23.ThmE.LGrowth

noncomputable section

open Complex Finset PintzJutilaAnalytic PintzJutilaMellinShift

namespace PintzJutilaDetectorIntegral

variable {q : ℕ}

/-- The finite corrected mollifier is bounded on the whole closed right
half-plane (no t-dependence). This is only used to justify contour shifting;
it is not the quantitative mollifier bound in the detection argument. -/
theorem mollifier_bounded (χ : DirichletCharacter ℂ q) (ξ : ℕ → ℂ) (K : Finset ℕ)
    (hK0 : 0 ∉ K) (r : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, 0 ≤ s.re → ‖mollifier χ ξ K r s‖ ≤ D := by
  let D (d : ℕ) : ℝ := ‖ξ d * (PintzJutilaPseudo.psi r d:ℂ) * χ d‖ *
    ∏ p ∈ (r/r.gcd d).primeFactors, (1+(p:ℝ))
  refine ⟨∑ d ∈ K, D d, ?_, ?_⟩
  · exact sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (prod_nonneg fun _ _ => by positivity)
  intro s hs
  have hb (n : ℕ) (hn : 0 < n) : 1 ≤ ‖(n:ℂ)^s‖ := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    exact Real.one_le_rpow (by exact_mod_cast hn) hs
  unfold mollifier
  refine (norm_sum_le _ _).trans (sum_le_sum fun d hd => ?_)
  have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h => hK0 (h ▸ hd))
  rw [norm_mul,norm_prod]
  apply mul_le_mul _ _ (prod_nonneg fun _ _ => norm_nonneg _) (norm_nonneg _)
  · rw [norm_div]
    exact div_le_self (norm_nonneg _) (hb _ hd0)
  · apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro p hp
    have hpp := (Nat.prime_of_mem_primeFactors hp).pos
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one,norm_div,norm_mul,Complex.norm_natCast]
    refine add_le_add le_rfl ?_
    calc
      _ ≤ (p:ℝ)*‖χ p‖ := div_le_self (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (hb _ hpp)
      _ ≤ (p:ℝ) := mul_le_of_le_one_right (Nat.cast_nonneg _) (χ.norm_le_one _)

def detectorF [NeZero q] (χ : DirichletCharacter ℂ q) (ξ : ℕ → ℂ) (K : Finset ℕ) (r : ℕ)
    (ρ w : ℂ) : ℂ :=
  χ.LFunction (ρ+w) * mollifier χ ξ K r (ρ+w)

set_option maxHeartbeats 800000 in
/-- Actual Jutila detector identity on a shifted line where Re(ρ+w) ≥ 0.15.
The gamma pole at w = 0 contributes no residue because L(ρ,χ) = 0.
This is the identity before estimating the left integral or truncating the
exponentially weighted sum. -/
theorem exponential_detector_shift [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (ξ : ℕ → ℂ) (K : Finset ℕ) (hK0 : 0 ∉ K) (hK : ∀ d ∉ K, ξ d = 0)
    {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 3/4 ≤ ρ.re) (hρ : χ.LFunction ρ = 0)
    {X aleft : ℝ} (hX : 0 < X) (haleft : -1 < aleft) (ha0 : aleft < 0)
    (hmin : (0.15:ℝ) ≤ ρ.re + aleft) :
    (∑' n : ℕ, LSeries.term (twisted (fun n => χ n) ξ r) ρ n * (Real.exp (-(n:ℝ)/X):ℂ)) =
      (1/(2*Real.pi):ℂ) * ∫ t : ℝ,
        (X:ℂ)^(verticalPoint aleft t) * Complex.Gamma (verticalPoint aleft t) *
          detectorF χ ξ K r ρ (verticalPoint aleft t) := by
  let a : ℕ → ℂ := twisted (fun n => χ n) ξ r
  let F : ℂ → ℂ := detectorF χ ξ K r ρ
  have hS : LSeriesSummable a (ρ+1) :=
    (equation_2_2 χ (s := ρ+1) (by rw [Complex.add_re,Complex.one_re]; linarith) ξ K hK0 hK hr).LSeriesSummable
  have hEq (t : ℝ) : LSeries a (ρ+PintzJutilaMellin.line t) = F (PintzJutilaMellin.line t) :=
    (equation_2_2 χ (s := ρ+PintzJutilaMellin.line t)
      (by rw [Complex.add_re,PintzJutilaMellin.line_re]; linarith)
      ξ K hK0 hK hr).LSeries_eq
  have hF0 : F 0 = 0 := by simp [F,detectorF,hρ]
  have hA (w : ℂ) : AnalyticAt ℂ F w := by
    have hL := (DirichletCharacter.differentiable_LFunction hχ1).analyticAt (ρ+w)
    have hM := (mollifier_entire χ ξ K hK0 r).analyticAt (ρ+w)
    have ha : AnalyticAt ℂ (fun w : ℂ => ρ+w) w := analyticAt_const.add analyticAt_id
    exact (hL.mul hM).comp ha
  obtain ⟨D,hD,hDb⟩ := mollifier_bounded χ ξ K hK0 r
  let B := (8*(q:ℝ)*(|ρ.im|+3))*D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlin (σ t : ℝ) (hσ : aleft ≤ σ) (_ : σ ≤ 1) :
      ‖F (verticalPoint σ t)‖ ≤ B*(1+|t|) := by
    let z := ρ+verticalPoint σ t
    have hRe : z.re = ρ.re+σ := by simp [z]
    have hIm : z.im = ρ.im+t := by simp [z]
    have hR : (0.15 : ℝ) ≤ z.re := by rw [hRe]; linarith
    have hL := Zeta23.ThmE.LFunction_growth_right_uniform hχ1 hR
    rw [hIm] at hL
    have hL' : ‖χ.LFunction z‖ ≤ 8*(q:ℝ)*((|ρ.im|+3)*(1+|t|)) := by
      refine hL.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have ht := abs_add_le ρ.im t
      nlinarith [mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t),abs_nonneg t]
    change ‖χ.LFunction z * mollifier χ ξ K r z‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ (8*(q:ℝ)*((|ρ.im|+3)*(1+|t|)))*D :=
        mul_le_mul hL' (hDb z (by linarith)) (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [B]; ring
  have hshift := shift_at_zero_of_linear_growth hX hF0 (a := aleft)
    haleft ha0 (fun w _ _ => hA w) hB hlin
  have H := PintzJutilaMellin.exponential_dirichlet_integral a ρ hX hS
  simp_rw [hEq] at H
  change _ = (1/(2*Real.pi):ℂ) * ∫ t : ℝ,
    (X:ℂ)^(verticalPoint 1 t) * Complex.Gamma (verticalPoint 1 t) * F (verticalPoint 1 t) at H
  rw [hshift] at H
  exact H

#print axioms mollifier_bounded
#print axioms exponential_detector_shift
end PintzJutilaDetectorIntegral
