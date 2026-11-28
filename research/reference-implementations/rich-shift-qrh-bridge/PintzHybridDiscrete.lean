import PintzSieveToHybrid
import PintzSeparatedSampling
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

open Finset MeasureTheory Set intervalIntegral
open scoped BigOperators
namespace PintzHybridDiscrete
open PintzSieveToHybrid

noncomputable def P (s : Finset ℕ) (a : ℕ → ℂ)
    (j : Σ k : ℕ, DirichletCharacter ℂ (k+1)) (t : ℝ) : ℂ :=
  ∑ n ∈ s, (j.2 (n : ZMod (j.1+1)) * a n) *
    Complex.exp (((t:ℂ) * Complex.I) * Real.log (n:ℝ))

noncomputable def logCoeff (a : ℕ → ℂ) (n : ℕ) :=
  a n * (Complex.I * Real.log (n:ℝ))

theorem hasDerivAt_P (s : Finset ℕ) (a : ℕ → ℂ)
    (j : Σ k : ℕ, DirichletCharacter ℂ (k+1)) (t : ℝ) :
    HasDerivAt (P s a j) (P s (logCoeff a) j t) t := by
  have hd (n : ℕ) :
      HasDerivAt (fun x : ℝ => Complex.exp (((x:ℂ) * Complex.I) * Real.log (n:ℝ)))
        (Complex.exp (((t:ℂ) * Complex.I) * Real.log (n:ℝ)) * (Complex.I * Real.log (n:ℝ))) t := by
    have H := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).mul_const
      ((Real.log (n:ℝ)):ℂ)
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using H.cexp
  unfold P
  apply HasDerivAt.fun_sum
  intro n hn
  convert (hd n).const_mul (j.2 (n : ZMod (j.1+1)) * a n) using 1
  unfold logCoeff
  ring

private theorem integral_increase {f : ℝ → ℝ} (hf : Continuous f) (h₀ : ∀ x, 0 ≤ f x)
    {a b c d : ℝ} (ha : c ≤ a) (hab : a ≤ b) (hb : b ≤ d) :
    (∫ x in a..b, f x) ≤ ∫ x in c..d, f x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le (ha.trans (hab.trans hb))]
  exact setIntegral_mono_set (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ h₀) (ae_of_all _ fun _ hx => ⟨ha.trans_lt hx.1,hx.2.trans hb⟩)

/-- Discrete hybrid sieve, at unit-separated ordinates for each primitive
character independently. The derivative only changes the coefficients
by the factor i log n. -/
theorem sampled_energy {Q : ℕ} (hQ : 1 ≤ Q) (s : Finset ℕ) (a : ℕ → ℂ)
    {U T : ℝ} (hT : 0 ≤ T) (hs : ∀ n ∈ s, 0 < n ∧ (n:ℝ) ≤ 2*U)
    {ι : Type*} (A : (Σ k : ℕ, DirichletCharacter ℂ (k+1)) → Finset ι)
    (t : (Σ k : ℕ, DirichletCharacter ℂ (k+1)) → ι → ℝ)
    (hpt : ∀ j ∈ family Q, ∀ i ∈ A j, t j i ∈ Icc (-T) T)
    (hsep : ∀ j ∈ family Q, (↑(A j) : Set ι).Pairwise fun i k => 1 ≤ |t j i - t j k|) :
    (∑ j ∈ family Q, ∑ i ∈ A j, ‖P s a j (t j i)‖ ^ 2) ≤
      (Real.pi ^ 2 * (T+1) / 2) * ((⌊U * (2*Real.pi/(T+1))⌋₊:ℝ)+1+2*(Q:ℝ)^2) *
        (2 * (∑ n ∈ s, ‖a n‖ ^ 2) + ∑ n ∈ s, ‖logCoeff a n‖ ^ 2) := by
  let R := T+1
  let M := (Real.pi ^ 2 * R / 2) * ((⌊U * (2*Real.pi/R)⌋₊:ℝ)+1+2*(Q:ℝ)^2)
  have hR : 0 < R := by dsimp [R]; linarith
  have hp (u : ℕ → ℂ) := hybrid_ordinate hQ s u (U := U) hR hs
  change (∑ j ∈ family Q, ∑ i ∈ A j, ‖P s a j (t j i)‖ ^ 2) ≤
    M * (2 * (∑ n ∈ s, ‖a n‖ ^ 2) + ∑ n ∈ s, ‖logCoeff a n‖ ^ 2)
  have hj (j) (hj : j ∈ family Q) : (∑ i ∈ A j, ‖P s a j (t j i)‖ ^ 2) ≤
      2 * (∫ x in (-R)..R, ‖P s a j x‖^2) + (∫ x in (-R)..R, ‖P s (logCoeff a) j x‖^2) := by
    have hd := hasDerivAt_P s a j
    have hf : Continuous (P s a j) := continuous_iff_continuousAt.mpr
      (fun x => (hd x).continuousAt)
    have hc : Continuous (P s (logCoeff a) j) := continuous_iff_continuousAt.mpr
      (fun x => (hasDerivAt_P s (logCoeff a) j x).continuousAt)
    have H := PintzSeparatedSampling.finset_sample_sq (A j) (t j) (P s a j)
      (P s (logCoeff a) j) hd hc (a := -T) (b := T) (h := 1)
      (by linarith) zero_le_one (hpt j hj) (hsep j hj)
    simp only [one_mul, mul_one] at H
    have hmain : (∫ x in (-T)..(T+1), ‖P s a j x‖ ^ 2) ≤
        ∫ x in (-R)..R, ‖P s a j x‖ ^ 2 :=
      integral_increase (hf.norm.pow _) (fun x => sq_nonneg _) (by dsimp [R]; linarith)
        (by linarith) le_rfl
    have hprod : (∫ x in (-T)..(T+1), 2*(‖P s a j x‖ * ‖P s (logCoeff a) j x‖))
        ≤ ∫ x in (-T)..(T+1), ‖P s a j x‖^2 + ‖P s (logCoeff a) j x‖^2 := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (continuous_const.mul (hf.norm.mul hc.norm)).intervalIntegrable _ _
      · exact ((hf.norm.pow 2).add (hc.norm.pow 2)).intervalIntegrable _ _
      · intro x _
        nlinarith [sq_nonneg (‖P s a j x‖ - ‖P s (logCoeff a) j x‖)]
    have hfi : IntervalIntegrable (fun x => ‖P s a j x‖^2) volume (-T) (T+1) :=
      (hf.norm.pow 2).intervalIntegrable _ _
    have hci : IntervalIntegrable (fun x => ‖P s (logCoeff a) j x‖^2) volume (-T) (T+1) :=
      (hc.norm.pow 2).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hfi hci] at hprod
    have hderiv : (∫ x in (-T)..(T+1), ‖P s (logCoeff a) j x‖ ^ 2) ≤
        ∫ x in (-R)..R, ‖P s (logCoeff a) j x‖ ^ 2 :=
      integral_increase (hc.norm.pow _) (fun x => sq_nonneg _) (by dsimp [R]; linarith)
        (by linarith) le_rfl
    linarith
  calc
    _ ≤ ∑ j ∈ family Q, (2 * (∫ x in (-R)..R, ‖P s a j x‖^2) +
            (∫ x in (-R)..R, ‖P s (logCoeff a) j x‖^2)) := Finset.sum_le_sum hj
    _ = 2 * (∑ j ∈ family Q, ∫ x in (-R)..R, ‖P s a j x‖^2) +
          (∑ j ∈ family Q, ∫ x in (-R)..R, ‖P s (logCoeff a) j x‖^2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (M * ∑ n ∈ s, ‖a n‖^2) + M * ∑ n ∈ s, ‖logCoeff a n‖^2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hp a) (by norm_num)) (hp (logCoeff a))
    _ = _ := by ring

#print axioms hasDerivAt_P
#print axioms sampled_energy
end PintzHybridDiscrete
