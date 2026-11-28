import PintzHybridStripOverlap

open Finset

namespace PintzDyadicDetectorCounting

/-- Cauchy-Schwarz with an explicit finite block count. -/
theorem norm_sum_sq {κ : Type*} (K : Finset κ) (z : κ → ℂ) :
    ‖∑ k ∈ K, z k‖ ^ 2 ≤ (K.card : ℝ) * ∑ k ∈ K, ‖z k‖ ^ 2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
  simpa using (Finset.sum_mul_sq_le_sq_mul_sq K (fun _ => (1 : ℝ)) (fun k => ‖z k‖))

theorem weighted_count {ι κ : Type*} (A : Finset ι) (K : Finset κ) (w : ι → ℕ)
    (z : ι → κ → ℂ) {c : ℝ} (hc : 0 < c)
    (hdet : ∀ i ∈ A, c ≤ ‖∑ k ∈ K, z i k‖) :
    (∑ i ∈ A, (w i : ℝ)) ≤ ((K.card : ℝ) / c ^ 2) *
      ∑ k ∈ K, ∑ i ∈ A, (w i : ℝ) * ‖z i k‖ ^ 2 := by
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  rw [sum_mul]
  calc
    _ ≤ ∑ i ∈ A, (w i : ℝ) * ((K.card : ℝ) * ∑ k ∈ K, ‖z i k‖ ^ 2) :=
      sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ hc.le (hdet i hi) 2).trans (norm_sum_sq K (z i))) (Nat.cast_nonneg _))
    _ = _ := by
      simp_rw [mul_left_comm (↑(w _) : ℝ) (K.card : ℝ), ← Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm

#print axioms weighted_count
end PintzDyadicDetectorCounting
