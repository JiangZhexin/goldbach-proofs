import PintzDyadicCoefficientEnergy
import PintzDetectorHead

open Finset PintzHybridDiscrete PintzHybridStrip PintzDetectorHead

namespace PintzDyadicPolynomial

def scale (L k : ℕ) : ℕ := L * 2^k

theorem scale_mono (L : ℕ) : Monotone (scale L) :=
  fun _ _ h => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) h)

def block (L J k : ℕ) : Finset ℕ := (Ioc (scale L k) (2 * scale L k)).filter
  (fun n => L < n ∧ n ≤ J)

theorem sum_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    (L J K : ℕ) (hJ : J ≤ scale L K) :
    ∑ k ∈ range K, ∑ n ∈ block L J k, f n = ∑ n ∈ Ioc L J, f n := by
  have H (m : ℕ) : ∑ k ∈ range m, ∑ n ∈ block L J k, f n =
      ∑ n ∈ (Ioc L (scale L m)).filter (fun n => L < n ∧ n ≤ J), f n := by
    induction m with
    | zero => simp [scale]
    | succ m ih =>
      rw [sum_range_succ, ih]
      have hd : scale L (m+1) = 2 * scale L m := by simp [scale, pow_succ, mul_assoc, mul_left_comm, mul_comm]
      have hl : L ≤ scale L m := by simpa [scale] using scale_mono L (Nat.zero_le m)
      have hr : scale L m ≤ 2 * scale L m := by omega
      unfold block
      rw [hd, ← Ioc_union_Ioc_eq_Ioc hl hr, filter_union, sum_union]
      exact (Ioc_disjoint_Ioc_of_le le_rfl).mono (filter_subset _ _) (filter_subset _ _)
  rw [H]
  congr 1
  ext n
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨⟨h.1, h.2.trans hJ⟩, h⟩

theorem P_eq_detector (s : Finset ℕ) (a : ℕ → ℂ)
    (j : Σ k : ℕ, DirichletCharacter ℂ (k+1)) (ρ : ℂ)
    (hs : ∀ n ∈ s, 0 < n) :
    P s (reScale a ρ.re) j (-ρ.im) = ∑ n ∈ s, twist j.2 ρ n * a n := by
  unfold P
  apply sum_congr rfl
  intro n hn
  have hnp : (0:ℝ) < n := by exact_mod_cast hs n hn
  rw [twist, reScale, Complex.cpow_def_of_ne_zero (by exact_mod_cast (hs n hn).ne')]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnp.le]
  have he : Complex.exp (-(ρ.re:ℂ) * Real.log (n:ℝ)) *
      Complex.exp ((((-ρ.im:ℝ):ℂ) * Complex.I) * Real.log (n:ℝ)) =
      Complex.exp ((Real.log (n:ℝ):ℂ) * -ρ) := by
    rw [← Complex.exp_add]
    congr 1
    conv_rhs => rw [← Complex.re_add_im ρ]
    push_cast
    ring_nf
  rw [show ((j.2 (n : ZMod (j.1 + 1)) * (a n * Complex.exp (-(ρ.re:ℂ) * ↑(Real.log n)))) *
    Complex.exp (((↑(-ρ.im) : ℂ) * Complex.I) * ↑(Real.log n))) =
    (j.2 (n : ZMod (j.1 + 1)) * a n) *
    (Complex.exp (-(ρ.re:ℂ) * Real.log n) *
      Complex.exp (((↑(-ρ.im) : ℂ) * Complex.I) * Real.log n)) by ring, he]
  ring

#print axioms sum_blocks
#print axioms P_eq_detector
end PintzDyadicPolynomial
