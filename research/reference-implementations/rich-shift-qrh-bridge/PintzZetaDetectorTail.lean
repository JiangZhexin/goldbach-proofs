import PintzDetectorTail
import PintzZetaTail

open Finset PintzDetectorFinite

namespace PintzZetaDetectorTail

open ZetaPartialSum

/-- The integer-indexed and interval-indexed zeta prefixes coincide. -/
theorem partial_eq_sum (s : ℂ) (N : ℕ) :
    zetaPartialSum s N = ∑ n ∈ Icc 1 N, (n:ℂ)^(-s) := by
  unfold zetaPartialSum
  apply Finset.sum_bij (fun n _ => n+1)
  · intro n hn
    have := mem_range.mp hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro n hn m hm h
    omega
  · intro m hm
    obtain ⟨h1,h2⟩ := mem_Icc.mp hm
    exact ⟨m-1, mem_range.mpr (by omega), by omega⟩
  · intro n hn
    push_cast
    rfl

/-- The same alternating coefficient family works for conductor one.
The two pole terms cancel on even cutoffs, and odd cutoffs cost one term. -/
theorem at_zero {s : ℂ} (hd : s ∈ zetaAbelContinuationDomain)
    (hz : riemannZeta s = 0) (hre : s.re ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖∑ n ∈ Icc 1 N, (n:ℂ)^(-s) * alternation n‖ ≤
      (9*(‖s‖/s.re)+1)*(N:ℝ)^(-s.re) := by
  have hp := zetaAbelContinuationDomain_re_pos hd
  let g : ℕ → ℂ := fun n => (n:ℂ)^(-s)
  have hg (d k : ℕ) : g (d*k) = g d*g k := by
    simp only [g, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  have hn (n : ℕ) (hn : 0 < n) : ‖g n‖ ≤ (n:ℝ)^(-s.re) := by
    have H := Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn : (0:ℝ) < n) (-s)
    simpa only [g, Complex.ofReal_natCast, Complex.neg_re, le_refl] using H.le
  have he (k : ℕ) (hk : 1 ≤ k) :
      ‖∑ n ∈ Icc 1 (2*k), g n * alternation n‖ ≤
        (3*(‖s‖/s.re))*(k:ℝ)^(-s.re) := by
    rw [alternating_even k _ hg]
    have ht : 2 * g 2 = (2:ℂ)^(1-s) := by
      dsimp [g]
      rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
    simp only [g] at ht ⊢
    rw [ht, ← partial_eq_sum, ← partial_eq_sum]
    exact PintzZetaTail.even_difference_bound hd hz k hk
  have H := PintzDetectorTail.from_even g hp.le hre
    (show (0:ℝ) ≤ 3*(‖s‖/s.re) by positivity) hn he N hN
  convert H using 1
  ring

#print axioms at_zero
end PintzZetaDetectorTail
