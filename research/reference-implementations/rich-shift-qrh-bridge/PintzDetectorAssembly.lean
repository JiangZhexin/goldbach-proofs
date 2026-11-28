import PintzDetectorTail
import PintzDetectorBound
import PintzZetaTail

open Finset PintzDetectorHead PintzDetectorFinite

namespace PintzDetectorAssembly

/-- The localized finite polynomial detects each true nonprincipal zero
in the retained band, at the explicit real-power cutoff. No density axiom. -/
theorem nonprincipal_detector {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hz : χ.LFunction s = 0)
    {b : ℝ} (hb : 0 < b) (hlo : (39/50:ℝ) ≤ s.re) (hhi : s.re ≤ 1-b)
    {L J : ℕ} (hL : 2 ≤ L) (hLJ : L ≤ J)
    (hJ : let c := min 1 ((2:ℝ)^b-1)
          let A := 9*(q*(1+‖s‖/s.re))+1
          (4*(L:ℝ)*A/c)^(13/10:ℝ) ≤ (J:ℝ)) :
    min 1 ((2:ℝ)^b-1)/2 ≤ ‖∑ n ∈ Ioc L J, twist χ s n * coeff L n‖ := by
  let c := min 1 ((2:ℝ)^b-1)
  let A : ℝ := 9*(q*(1+‖s‖/s.re))+1
  have hc : 0 < c := head_constant_pos hb
  have hc1 : c ≤ 1 := min_le_left _ _
  have hP : 0 < s.re := by linarith
  have hA : 1 ≤ A := by
    have h : 0 ≤ 9*(q*(1+‖s‖/s.re)) := by positivity
    dsimp [A]
    linarith
  have hL' : (2:ℝ) ≤ L := by exact_mod_cast hL
  apply PintzDetectorBound.detector_lower hL hLJ _ (head_lower χ s hhi)
  have h := PintzDetectorBound.full_bound hLJ (twist χ s) (twist_mul χ s) hP.le
    (by linarith : s.re ≤ 1) (by linarith : 0 ≤ A)
    (fun n hn => twist_norm χ s (mem_Icc.mp hn).1) (fun d hd => ?_)
  · have hcut : A*(J:ℝ)^(-s.re) ≤ 1 / (4*(L:ℝ)/c) := by
      have hpos : 0 < 4*(L:ℝ)/c := by positivity
      have hprod : 1 ≤ (4*(L:ℝ)/c)*A := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hc).mpr
        have hLA := mul_le_mul hL' hA (by norm_num) (by positivity)
        rw [one_mul]
        nlinarith only [hLA, hc1]
      apply PintzDetectorCutoff.cutoff_decay hpos hprod hlo
      rw [div_mul_eq_mul_div]
      exact hJ
    have he : 1 / (4*(L:ℝ)/c) = c / (4*(L:ℝ)) := by
      rw [one_div, inv_div]
    rw [he] at hcut
    have hc4 : 0 < 4*(L:ℝ) := by positivity
    have hh := (le_div_iff₀ hc4).mp hcut
    exact h.trans (by nlinarith only [hh])
  · apply PintzDetectorTail.nonprincipal_at_zero χ hχ hP (by linarith) hz
    exact Nat.div_pos ((mem_Icc.mp hd).2.trans hLJ) (mem_Icc.mp hd).1

#print axioms nonprincipal_detector
end PintzDetectorAssembly
