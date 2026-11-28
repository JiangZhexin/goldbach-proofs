import PintzHybridDiscrete
import PintzOverlapSampling

open Finset MeasureTheory Set intervalIntegral
open scoped BigOperators
namespace PintzHybridOverlap
open PintzSieveToHybrid PintzHybridDiscrete

private theorem integral_increase {f : ℝ → ℝ} (hf : Continuous f) (h₀ : ∀ x, 0 ≤ f x)
    {a b c d : ℝ} (ha : c ≤ a) (hab : a ≤ b) (hb : b ≤ d) :
    (∫ x in a..b, f x) ≤ ∫ x in c..d, f x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le (ha.trans (hab.trans hb))]
  exact setIntegral_mono_set (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ h₀) (ae_of_all _ fun _ hx => ⟨ha.trans_lt hx.1,hx.2.trans hb⟩)

/-- Discrete hybrid sieve, at bounded-overlap ordinates for each primitive
character independently. The derivative only changes the coefficients
by the factor i log n. -/
theorem sampled_energy_overlap {Q : ℕ} (hQ : 1 ≤ Q) (s : Finset ℕ) (a : ℕ → ℂ)
    {U T : ℝ} (hT : 0 ≤ T) (hs : ∀ n ∈ s, 0 < n ∧ (n:ℝ) ≤ 2*U)
    {ι : Type*} (A : (Σ k : ℕ, DirichletCharacter ℂ (k+1)) → Finset ι)
    (t : (Σ k : ℕ, DirichletCharacter ℂ (k+1)) → ι → ℝ)
    (hpt : ∀ j ∈ family Q, ∀ i ∈ A j, t j i ∈ Icc (-T) T)
    (B : ℕ)
    (hover : ∀ j ∈ family Q, ∀ x, ((A j).filter (fun i => t j i < x ∧ x ≤ t j i + 1)).card ≤ B) :
    (∑ j ∈ family Q, ∑ i ∈ A j, ‖P s a j (t j i)‖ ^ 2) ≤
      (B:ℝ) * ((Real.pi ^ 2 * (T+1) / 2) * ((⌊U * (2*Real.pi/(T+1))⌋₊:ℝ)+1+2*(Q:ℝ)^2) *
        (2 * (∑ n ∈ s, ‖a n‖ ^ 2) + ∑ n ∈ s, ‖logCoeff a n‖ ^ 2)) := by
  let R := T+1
  let M := (Real.pi ^ 2 * R / 2) * ((⌊U * (2*Real.pi/R)⌋₊:ℝ)+1+2*(Q:ℝ)^2)
  have hR : 0 < R := by dsimp [R]; linarith
  have hp (u : ℕ → ℂ) := hybrid_ordinate hQ s u (U := U) hR hs
  change (∑ j ∈ family Q, ∑ i ∈ A j, ‖P s a j (t j i)‖ ^ 2) ≤
    (B:ℝ) * (M * (2 * (∑ n ∈ s, ‖a n‖ ^ 2) + ∑ n ∈ s, ‖logCoeff a n‖ ^ 2))
  have hj (j) (hj : j ∈ family Q) : (∑ i ∈ A j, ‖P s a j (t j i)‖ ^ 2) ≤
      (B:ℝ) * (2 * (∫ x in (-R)..R, ‖P s a j x‖^2) + (∫ x in (-R)..R, ‖P s (logCoeff a) j x‖^2)) := by
    have hd := hasDerivAt_P s a j
    have hf : Continuous (P s a j) := continuous_iff_continuousAt.mpr
      (fun x => (hd x).continuousAt)
    have hc : Continuous (P s (logCoeff a) j) := continuous_iff_continuousAt.mpr
      (fun x => (hasDerivAt_P s (logCoeff a) j x).continuousAt)
    have H := PintzOverlapSampling.finset_sample_sq_overlap (A j) (t j) (P s a j)
      (P s (logCoeff a) j) hd hc (a := -T) (b := T) (h := 1)
      (by linarith) zero_le_one B (hpt j hj) (hover j hj)
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
    refine H.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg B))
    linarith
  calc
    _ ≤ ∑ j ∈ family Q, (B:ℝ) * (2 * (∫ x in (-R)..R, ‖P s a j x‖^2) +
            (∫ x in (-R)..R, ‖P s (logCoeff a) j x‖^2)) := Finset.sum_le_sum hj
    _ = (B:ℝ) * (2 * (∑ j ∈ family Q, ∫ x in (-R)..R, ‖P s a j x‖^2) +
          (∑ j ∈ family Q, ∫ x in (-R)..R, ‖P s (logCoeff a) j x‖^2)) := by
      conv_rhs => rw [Finset.mul_sum (family Q) _ (2:ℝ), ← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (B:ℝ) * (2 * (M * ∑ n ∈ s, ‖a n‖^2) + M * ∑ n ∈ s, ‖logCoeff a n‖^2) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (hp a) (by norm_num))
        (hp (logCoeff a))) (Nat.cast_nonneg B)
    _ = _ := by ring

#print axioms sampled_energy_overlap
end PintzHybridOverlap
