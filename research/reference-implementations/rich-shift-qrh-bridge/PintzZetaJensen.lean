import PintzLocalJensen
import PintzLocalDirichlet
import Mathlib.Analysis.Complex.RemovableSingularity

open Set Finset Filter
open scoped Topology

namespace PintzZetaJensen

noncomputable def regularZeta : ℂ → ℂ :=
  Function.update (fun z => (z-1)*riemannZeta z) 1 1

theorem regular_off {z : ℂ} (hz : z ≠ 1) :
    regularZeta z = (z-1)*riemannZeta z := by simp [regularZeta,hz]

theorem regular_analytic (z : ℂ) : AnalyticAt ℂ regularZeta z := by
  have hoff (s : ℂ) (hs : s ≠ 1) : AnalyticAt ℂ regularZeta s := by
    have he : regularZeta =ᶠ[𝓝 s] (fun w => (w - 1) * riemannZeta w) := by
      filter_upwards [isOpen_ne.mem_nhds hs] with w hw
      exact regular_off hw
    exact ((analyticAt_id.sub analyticAt_const).mul (analyticOn_riemannZeta s hs)).congr he.symm
  by_cases hz : z = 1
  · subst z
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact (hoff w hw).differentiableAt
    · exact continuousAt_update_same.mpr riemannZeta_residue_one
  · exact hoff z hz

theorem box_to_disk (t : ℝ) {z : ℂ} (hlo : 1/2 ≤ z.re) (hhi : z.re ≤ 1)
    (ht : |z.im-t| ≤ 1/2) : z ∈ Metric.closedBall (⟨2,t⟩:ℂ) (33/20) := by
  rw [Metric.mem_closedBall,dist_eq_norm]
  obtain ⟨ha,hb⟩ := abs_le.mp ht
  have h : ‖z - (⟨2,t⟩:ℂ)‖ ^ 2 = (z.re-2)^2+(z.im-t)^2 := by
    simp [Complex.sq_norm,Complex.normSq_apply]
    ring
  have hR : (z.re-2)^2 ≤ (3/2:ℝ)^2 := by nlinarith
  have hI : (z.im-t)^2 ≤ (1/2:ℝ)^2 := by nlinarith
  nlinarith [norm_nonneg (z - (⟨2,t⟩:ℂ))]

theorem center_lower (t : ℝ) : 1/3 ≤ ‖regularZeta (⟨2,t⟩:ℂ)‖ := by
  let s : ℂ := ⟨2,t⟩
  have hs : s ≠ 1 := by intro h; have he := congrArg Complex.re h; norm_num [s] at he
  have hinv := PintzLocalDirichlet.inverse_center (1 : DirichletCharacter ℂ 1)
    (s := s) (by norm_num [s])
  rw [DirichletCharacter.LFunction_modOne_eq] at hinv
  have hp : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr
    (riemannZeta_ne_zero_of_one_le_re (by norm_num [s]))
  rw [norm_inv, inv_le_iff_one_le_mul₀ hp] at hinv
  have hζ : 1/3 ≤ ‖riemannZeta s‖ := by linarith
  have H : 1 ≤ ‖s - 1‖ := by have h := Complex.re_le_norm (s-1); simp only [Complex.sub_re,Complex.one_re,s] at h; linarith
  rw [regular_off hs, norm_mul]
  calc
    _ ≤ 1 * ‖riemannZeta s‖ := by simpa using hζ
    _ ≤ _ := mul_le_mul_of_nonneg_right H hp.le

theorem count_of_growth (t M : ℝ) (S : Finset ℂ) (hM : 1 ≤ M)
    (hS : ∀ z ∈ S, 1/2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im-t| ≤ 1/2)
    (hB : ∀ z ∈ Metric.sphere (⟨2,t⟩:ℂ) (9/5), ‖regularZeta z‖ ≤ M) :
    (∑ z ∈ S, ((analyticOrderAt regularZeta z).toNat : ℝ)) ≤
      Real.log (3*M)/Real.log (12/11) := by
  have hc : 0 < ‖regularZeta (⟨2,t⟩:ℂ)‖ := lt_of_lt_of_le (by norm_num) (center_lower t)
  have hF := PintzLocalJensen.count_of_analytic regular_analytic S
    (show (0:ℝ) < 33/20 by norm_num) (show (33/20:ℝ) < 9/5 by norm_num) hM
    (norm_pos_iff.mp hc) (fun z hz => box_to_disk t (hS z hz).1 (hS z hz).2.1 (hS z hz).2.2) hB
  rw [show (9/5:ℝ)/(33/20)=12/11 by norm_num] at hF
  refine hF.trans (div_le_div_of_nonneg_right (Real.log_le_log (by positivity) ?_)
    (Real.log_nonneg (by norm_num)))
  apply (div_le_iff₀ hc).2
  nlinarith [mul_le_mul_of_nonneg_left (center_lower t) (show 0 ≤ 3*M by positivity)]

#print axioms count_of_growth
end PintzZetaJensen
