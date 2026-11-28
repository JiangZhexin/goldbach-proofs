import PintzDirichletGrowthBase
import PintzLocalJensen
import PintzHarmonicRow
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set Finset
open scoped ArithmeticFunction.Moebius

namespace PintzLocalDirichlet

open OAI.Ostmann.Dirichlet

theorem growth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ q * ‖s‖ / s.re := by
  rw [LFunction_eq_partial_sum_integral_of_re_pos χ hχ hs, norm_mul]
  have hi : ‖∫ t : ℝ in Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) *
      (t : ℂ) ^ (-(s + 1))‖ ≤ ∫ t : ℝ in Ioi 1, (q:ℝ) * t ^ (-s.re - 1) := by
    apply norm_integral_le_of_norm_le
      ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) zero_lt_one).const_mul (q:ℝ))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht₀]
    have he : (-(s+1)).re = -s.re-1 := by simp; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le
      (Real.rpow_nonneg ht₀.le _)
  have he : (∫ t : ℝ in Ioi 1, (q:ℝ) * t ^ (-s.re - 1)) = q / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) zero_lt_one]
    rw [show -s.re-1+1 = -s.re by ring, Real.one_rpow]
    ring
  rw [he] at hi
  exact (mul_le_mul_of_nonneg_left hi (norm_nonneg s)).trans_eq (by ring)

theorem inverse_center {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 2 ≤ s.re) : ‖(χ.LFunction s)⁻¹‖ ≤ 3 := by
  let f : ℕ → ℂ := fun n => χ (n : ZMod q) * (ArithmeticFunction.moebius n : ℂ)
  have hs' : 1 < s.re := by linarith
  have hf : LSeriesSummable f s :=
    DirichletCharacter.LSeriesSummable_mul χ (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs')
  have hi : χ.LFunction s * LSeries f s = 1 := by
    rw [χ.LFunction_eq_LSeries hs']
    exact DirichletCharacter.LSeries.mul_mu_eq_one χ hs'
  have hz : χ.LFunction s ≠ 0 := by intro h; simp [h] at hi
  have hEq : (χ.LFunction s)⁻¹ = LSeries f s :=
    (eq_inv_of_mul_eq_one_right (by simpa only [mul_comm] using hi)).symm
  rw [hEq]
  have hm (n : ℕ) : ‖LSeries.term f s n‖ ≤ (1:ℝ) / (n:ℝ)^2 := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne', norm_div, Complex.norm_natCast_cpow_of_pos hn]
      have hfₙ : ‖f n‖ ≤ 1 := by
        dsimp [f]
        rw [norm_mul]
        have hb : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
          norm_cast
          exact ArithmeticFunction.abs_moebius_le_one
        exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans hb
      have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hd : (n:ℝ)^2 ≤ (n:ℝ)^s.re := by
        simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hN hs
      exact div_le_div₀ (by norm_num) hfₙ (by positivity) hd
  exact (norm_tsum_le_tsum_norm hf.norm).trans
    ((hf.norm.tsum_le_tsum hm hasSum_zeta_two.summable).trans
      (hasSum_zeta_two.tsum_eq ▸ (by nlinarith [Real.pi_lt_four, Real.pi_pos] :
        Real.pi^2/6 ≤ (3:ℝ))))

/-- Explicit full-strip count for a nonprincipal character, with a uniform
constant coming from the absolutely convergent inverse L-series. -/
theorem local_count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, 1/2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im-t| ≤ 1/2) :
    (∑ z ∈ S, ((analyticOrderAt χ.LFunction z).toNat : ℝ)) ≤
      Real.log (12 * q * (|t|+6)) / Real.log (55/52) := by
  let c : ℂ := ⟨3,t⟩
  let M : ℝ := 4 * q * (|t|+6)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hMt : 1 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t]
  have hB (z : ℂ) (hz : z ∈ Metric.sphere c (11/4)) : ‖χ.LFunction z‖ ≤ M := by
    have hD := Metric.mem_closedBall.mp (Metric.sphere_subset_closedBall hz)
    rw [dist_eq_norm] at hD
    have hreal : (1/4:ℝ) ≤ z.re := by
      have hr := (abs_le.mp ((Complex.abs_re_le_norm (z-c)).trans hD)).1
      simp only [Complex.sub_re,c] at hr
      linarith
    have hc : ‖c‖ ≤ 3+|t| := by
      have he : c = 3 + (t:ℂ)*Complex.I := by apply Complex.ext <;> simp [c]
      rw [he]
      simpa [norm_mul] using norm_add_le (3:ℂ) ((t:ℂ)*Complex.I)
    have hnorm : ‖z‖ ≤ |t|+6 := by
      have hh := norm_add_le (z-c) c
      rw [sub_add_cancel] at hh
      linarith
    calc
      _ ≤ (q:ℝ)*‖z‖/z.re := growth χ hχ (by linarith)
      _ ≤ 4 * q * ‖z‖ := by
        apply (div_le_iff₀ (by linarith : 0 < z.re)).2
        have hp := mul_le_mul_of_nonneg_left hreal (show 0 ≤ 4*(q:ℝ)*‖z‖ by positivity)
        linarith
      _ ≤ M := mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hc₀ : 0 < ‖χ.LFunction c‖ := norm_pos_iff.mpr
    (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num [c]))
  have hcInv := inverse_center χ (s := c) (by norm_num [c])
  rw [norm_inv] at hcInv
  refine (PintzLocalJensen.full_strip_nonprincipal χ hχ t M S hMt hS hB).trans ?_
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 55/52))
  apply Real.log_le_log (div_pos (by linarith) hc₀)
  rw [div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left hcInv (by linarith : 0 ≤ M)).trans_eq (by dsimp [M]; ring)

/-- The full-strip harmonic row (8.22) for every nonprincipal character,
including actual analytic multiplicities in each unit-height bin. -/
theorem harmonic_zero_row {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (T γ : ℝ) (hT : 0 ≤ T) (hγ : |γ| ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, 1/2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) :
    (∑ z ∈ S, ((analyticOrderAt χ.LFunction z).toNat : ℝ) / (1 + |z.im-γ|)) ≤
      2 * (Real.log (12*q*(T+13/2)) / Real.log (55/52)) * (1+Real.log (2*T+1)) := by
  classical
  let C := Real.log (12*q*(T+13/2)) / Real.log (55/52)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hCp : 0 ≤ C := by
    apply div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by norm_num))
    nlinarith only [mul_nonneg (show 0 ≤ (q:ℝ)-1 by linarith) hT, hq, hT]
  apply PintzHarmonicRow.row_at_height S Complex.im
    (fun z => ((analyticOrderAt χ.LFunction z).toNat : ℝ)) γ T C hT hγ hCp
    (fun _ _ => Nat.cast_nonneg _) (fun z hz => (hS z hz).2.2)
  intro t ht
  have hh := local_count χ hχ t (S.filter (fun z => |z.im-t| ≤ 1/2)) (fun z hz =>
    ⟨(hS z (mem_filter.mp hz).1).1, (hS z (mem_filter.mp hz).1).2.1, (mem_filter.mp hz).2⟩)
  exact hh.trans (div_le_div_of_nonneg_right (Real.log_le_log (by positivity)
    (mul_le_mul_of_nonneg_left (by linarith) (by positivity))) (Real.log_nonneg (by norm_num)))

#print axioms harmonic_zero_row
#print axioms local_count
#print axioms growth
#print axioms inverse_center
end PintzLocalDirichlet
