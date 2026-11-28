import PintzSieveSparse
import LeanLab.PNTPort.LargeSieve.Multiplicative
import PintzHybridGallagher
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.GCongr

open Finset
open scoped BigOperators
namespace PintzSieveToHybrid

noncomputable def family (Q : ℕ) :
    Finset (Σ k : ℕ, DirichletCharacter ℂ (k+1)) :=
  (range Q).sigma (fun k => (univ : Finset (DirichletCharacter ℂ (k+1))).filter
    (fun χ => χ.IsPrimitive))

/-- Unweighted multiplicative sieve on an arbitrary filtered support. -/
theorem sparse_sieve {Q : ℕ} (hQ : 1 ≤ Q) (m L : ℕ)
    (v : Finset ℕ) (a : ℕ → ℂ) (hv : v ⊆ Icc m (m+L)) :
    (∑ j ∈ family Q, ‖∑ n ∈ v, j.2 (n : ZMod (j.1+1)) * a n‖ ^ 2) ≤
      ((L:ℝ)+1+2*(Q:ℝ)^2) * ∑ n ∈ v, ‖a n‖^2 := by
  have H := LeanLab.PNTPort.LargeSieve.multiplicative_large_sieve hQ (sparse v a) ((m:ℤ)-1) (L+1)
  simp_rw [sparse_character_sum m L _ _ v a hv, sparse_energy m L v a hv, Nat.cast_add,
    Nat.cast_one] at H
  rw [family, sum_sigma]
  refine (sum_le_sum (fun k _ => ?_)).trans H
  have hpos : (0:ℝ) < (k+1).totient := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < k+1)
  have hφ : (1:ℝ) ≤ ((k+1:ℕ):ℝ)/(k+1).totient := by
    apply (le_div_iff₀ hpos).mpr
    rw [one_mul]
    exact_mod_cast Nat.totient_le (k+1)
  simp_rw [mul_comm (a _) (_ : ℂ)] at H ⊢
  exact le_mul_of_one_le_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by simpa only [Nat.cast_add, Nat.cast_one] using hφ)

/-- A normalized hybrid estimate with an unconditional integer large-sieve
input, including all primitive characters of moduli up to Q. -/
theorem hybrid {Q : ℕ} (hQ : 1 ≤ Q) (s : Finset ℕ) (a : ℕ → ℂ)
    {U D : ℝ} (hD : 0 < D) (hs : ∀ n ∈ s, 0 < n ∧ (n:ℝ) ≤ 2*U) :
    (∑ j ∈ family Q, ∫ t in (-1/D)..(1/D), ‖∑ n ∈ s, (j.2 (n : ZMod (j.1+1)) * a n) *
        Complex.exp ((2 * Real.pi * t * Complex.I) * Real.log (n:ℝ))‖ ^ 2) ≤
      (Real.pi ^ 2 / (2*D)) * ((⌊U*D⌋₊:ℝ)+1+2*(Q:ℝ)^2) * ∑ n ∈ s, ‖a n‖ ^ 2 :=
  PintzHybridGallagher.hybrid_log_of_integer_sieve s (family Q) a (fun j n => j.2 n) hD hs
    (fun m v hv => sparse_sieve hQ m _ v a hv)


/-- Hybrid large sieve on the actual analytic ordinate interval [-T,T],
rather than the Fourier variable divided by 2π. -/
theorem hybrid_ordinate {Q : ℕ} (hQ : 1 ≤ Q) (s : Finset ℕ) (a : ℕ → ℂ)
    {U T : ℝ} (hT : 0 < T) (hs : ∀ n ∈ s, 0 < n ∧ (n:ℝ) ≤ 2*U) :
    (∑ j ∈ family Q, ∫ t in (-T)..T, ‖∑ n ∈ s, (j.2 (n : ZMod (j.1+1)) * a n) *
        Complex.exp (((t:ℂ) * Complex.I) * Real.log (n:ℝ))‖ ^ 2) ≤
      (Real.pi ^ 2 * T / 2) * ((⌊U * (2*Real.pi/T)⌋₊:ℝ)+1+2*(Q:ℝ)^2) *
        ∑ n ∈ s, ‖a n‖ ^ 2 := by
  let D := 2*Real.pi/T
  let c := 2*Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := div_pos hc hT
  let F (j : Σ k : ℕ, DirichletCharacter ℂ (k+1)) (t : ℝ) : ℝ :=
    ‖∑ n ∈ s, (j.2 (n : ZMod (j.1+1)) * a n) *
        Complex.exp (((t:ℂ) * Complex.I) * Real.log (n:ℝ))‖ ^ 2
  have ht : c * (1/D) = T := by
    change c * (1/(c/T)) = T
    field_simp
  have he (j : Σ k : ℕ, DirichletCharacter ℂ (k+1)) :
      (∫ t in (-T)..T, F j t) = c * ∫ t in (-1/D)..(1/D), F j (c*t) := by
    rw [← smul_eq_mul, intervalIntegral.smul_integral_comp_mul_left]
    rw [show c * (-1/D) = -T by rw [neg_div, mul_neg, ht], ht]
  have ho (j : Σ k : ℕ, DirichletCharacter ℂ (k+1)) (t : ℝ) :
      F j (c*t) = ‖∑ n ∈ s, (j.2 (n : ZMod (j.1+1)) * a n) *
        Complex.exp ((2 * Real.pi * t * Complex.I) * Real.log (n:ℝ))‖ ^ 2 := by
    simp [F, c, mul_assoc]
  have H := hybrid hQ s a hD hs
  change (∑ j ∈ family Q, ∫ t in (-T)..T, F j t) ≤ _
  simp_rw [he, ho]
  rw [← Finset.mul_sum]
  calc
    _ ≤ c * ((Real.pi ^ 2 / (2*D)) * ((⌊U*D⌋₊:ℝ)+1+2*(Q:ℝ)^2) *
        ∑ n ∈ s, ‖a n‖ ^ 2) := mul_le_mul_of_nonneg_left H hc.le
    _ = _ := by
      have hcoeff : c * (Real.pi ^ 2 / (2*D)) = Real.pi ^ 2 * T / 2 := by
        change c * (Real.pi ^ 2 / (2*(c/T))) = _
        field_simp
      rw [← mul_assoc, ← mul_assoc, hcoeff]

#print axioms sparse_sieve
#print axioms hybrid
#print axioms hybrid_ordinate
end PintzSieveToHybrid
