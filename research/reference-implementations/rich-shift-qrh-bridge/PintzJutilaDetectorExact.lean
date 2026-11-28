import PintzJutilaDetectorIntegral
import PintzJutilaSecondAbel

noncomputable section

open Complex Finset PintzJutilaMellinShift PintzJutilaAnalytic PintzJutilaDetectorIntegral

namespace PintzJutilaDetectorExact

variable {q : ℕ} [NeZero q]

/-- Jutila detector contour identity with any nonnegative target abscissa before combining
the finitely many squarefree parameters r. The analytic change of line
uses only polynomial growth; its quantitative bound is a separate result. -/
theorem equation_2_11_shift_package (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (ξ : ℕ → ℂ) (K : Finset ℕ) (hK0 : 0 ∉ K) (hK : ∀ d ∉ K, ξ d = 0)
    {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 0 < ρ.re) (hρ : χ.LFunction ρ = 0)
    {X η : ℝ} (hX : 0 < X) (hη : 0 ≤ η) (hηβ : η < ρ.re) :
    ((∑' n : ℕ, LSeries.term (twisted (fun n => χ n) ξ r) ρ n * (Real.exp (-(n:ℝ)/X):ℂ)) =
      (1/(2*Real.pi):ℂ) * ∫ u : ℝ,
        (X:ℂ)^(verticalPoint (η-ρ.re) u) * Complex.Gamma (verticalPoint (η-ρ.re) u) *
          (χ.LFunction (verticalPoint η (ρ.im+u)) * mollifier χ ξ K r (verticalPoint η (ρ.im+u)))) ∧
      MeasureTheory.Integrable (fun u : ℝ =>
        (X:ℂ)^(verticalPoint (η-ρ.re) u) * Complex.Gamma (verticalPoint (η-ρ.re) u) *
          (χ.LFunction (verticalPoint η (ρ.im+u)) * mollifier χ ξ K r (verticalPoint η (ρ.im+u)))) := by
  let a : ℕ → ℂ := twisted (fun n => χ n) ξ r
  let F : ℂ → ℂ := detectorF χ ξ K r ρ
  have hβ1 : ρ.re < 1 := by
    by_contra! H
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) H) hρ
  have hS : LSeriesSummable a (ρ+1) :=
    (equation_2_2 χ (s := ρ+1) (by rw [Complex.add_re,Complex.one_re]; linarith)
      ξ K hK0 hK hr).LSeriesSummable
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
  obtain ⟨A,hA0,hLq⟩ := PintzJutilaSecondAbel.quadratic_growth_closed hχ1
  let B := A*D*(1+|ρ.im|)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlin (σ t : ℝ) (hσ : η-ρ.re ≤ σ) (hσ1 : σ ≤ 1) :
      ‖F (verticalPoint σ t)‖ ≤ B*(1+|t|)^2 := by
    let z := ρ+verticalPoint σ t
    have hRe : z.re = ρ.re+σ := by simp [z]
    have hIm : z.im = ρ.im+t := by simp [z]
    have hR₀ : 0 ≤ z.re := by rw [hRe]; linarith
    have hR₂ : z.re ≤ 2 := by rw [hRe]; linarith
    have hL := hLq z hR₀ hR₂
    rw [hIm] at hL
    have hT : 1+|ρ.im+t| ≤ (1+|ρ.im|)*(1+|t|) := by
      nlinarith [abs_add_le ρ.im t, mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]
    have hL' : ‖χ.LFunction z‖ ≤ A*((1+|ρ.im|)*(1+|t|))^2 :=
      hL.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hT 2) hA0)
    change ‖χ.LFunction z * mollifier χ ξ K r z‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ (A*((1+|ρ.im|)*(1+|t|))^2)*D :=
        mul_le_mul hL' (hDb z hR₀) (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [B]; ring
  obtain ⟨hshift,hI⟩ := shift_at_zero_quadratic_package hX hF0 (a := η-ρ.re)
    (by linarith) (by linarith) (fun w _ _ => hA w) hB hlin
  have H := PintzJutilaMellin.exponential_dirichlet_integral a ρ hX hS
  simp_rw [hEq] at H
  change _ = (1/(2*Real.pi):ℂ) * ∫ t : ℝ,
    (X:ℂ)^(verticalPoint 1 t) * Complex.Gamma (verticalPoint 1 t) * F (verticalPoint 1 t) at H
  rw [hshift] at H
  have hre (u : ℝ) : ρ+verticalPoint (η-ρ.re) u = verticalPoint η (ρ.im+u) := by
    apply Complex.ext <;> simp
  have B (u : ℝ) : F (verticalPoint (η-ρ.re) u) =
      χ.LFunction (verticalPoint η (ρ.im+u)) * mollifier χ ξ K r (verticalPoint η (ρ.im+u)) := by
    dsimp only [F,detectorF]
    rw [hre u]
  refine ⟨?_,?_⟩
  · simp_rw [B] at H
    exact H
  · simp_rw [B] at hI
    exact hI

/-- Exact contour equality on the Re(L-argument) = η line. -/
theorem equation_2_11_shift (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (ξ : ℕ → ℂ) (K : Finset ℕ) (hK0 : 0 ∉ K) (hK : ∀ d ∉ K, ξ d = 0)
    {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 0 < ρ.re) (hρ : χ.LFunction ρ = 0)
    {X η : ℝ} (hX : 0 < X) (hη : 0 ≤ η) (hηβ : η < ρ.re) :
    (∑' n : ℕ, LSeries.term (twisted (fun n => χ n) ξ r) ρ n * (Real.exp (-(n:ℝ)/X):ℂ)) =
      (1/(2*Real.pi):ℂ) * ∫ u : ℝ,
        (X:ℂ)^(verticalPoint (η-ρ.re) u) * Complex.Gamma (verticalPoint (η-ρ.re) u) *
          (χ.LFunction (verticalPoint η (ρ.im+u)) * mollifier χ ξ K r (verticalPoint η (ρ.im+u))) :=
  (equation_2_11_shift_package χ hχ1 ξ K hK0 hK hr hβ hρ hX hη hηβ).1

theorem equation_2_11_single (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (ξ : ℕ → ℂ) (K : Finset ℕ) (hK0 : 0 ∉ K) (hK : ∀ d ∉ K, ξ d = 0)
    {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 0 < ρ.re) (hρ : χ.LFunction ρ = 0)
    {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ, LSeries.term (twisted (fun n => χ n) ξ r) ρ n * (Real.exp (-(n:ℝ)/X):ℂ)) =
      (1/(2*Real.pi):ℂ) * ∫ u : ℝ,
        (X:ℂ)^(verticalPoint (-ρ.re) u) * Complex.Gamma (verticalPoint (-ρ.re) u) *
          (χ.LFunction ((ρ.im+u:ℝ)*Complex.I) * mollifier χ ξ K r ((ρ.im+u:ℝ)*Complex.I)) := by
  simpa [verticalPoint] using
    equation_2_11_shift χ hχ1 ξ K hK0 hK hr hβ hρ hX (η := 0) le_rfl hβ

#print axioms equation_2_11_shift
#print axioms equation_2_11_single
end PintzJutilaDetectorExact
