import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped ENNReal

namespace PintzFixedWindowL2

/-- Averaging a complex function over translates of a fixed real interval
does not increase its squared L2 norm. The function can already include any
clipping indicator. -/
theorem moving_average_sq_le {Y : ℝ} (hY : 0 < Y) {f : ℝ → ℂ}
    (hm : Measurable f) (h₁ : Integrable f)
    (h₂ : Integrable (fun x => ‖f x‖ ^ 2)) :
    (∫ x : ℝ, ‖Y⁻¹ • (∫ t in Ioc (0 : ℝ) Y, f (x+t))‖ ^ 2) ≤
    ∫ x : ℝ, ‖f x‖ ^ 2 := by
  let s := Ioc (0 : ℝ) Y
  let ν : Measure ℝ := volume.restrict s
  have hr : ν.real univ = Y := by
    change ((volume.restrict (Ioc (0 : ℝ) Y)) univ).toReal = Y
    rw [Measure.restrict_apply_univ]
    simpa only [sub_zero, measureReal_def] using Real.volume_real_Ioc_of_le hY.le
  have hν0 : volume s ≠ 0 := by
    intro h
    have h' : ν.real univ = 0 := by
      simp [ν, measureReal_def, h]
    linarith
  have hνtop : volume s ≠ ⊤ := by simp [s, Real.volume_Ioc]
  have hconv : ConvexOn ℝ (univ : Set ℂ) (fun z => ‖z‖ ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    have ht : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] using
        norm_add_le (a • x) (b • y)
    have ht2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    calc
      _ ≤ (a * ‖x‖ + b * ‖y‖)^2 := ht2
      _ ≤ _ := by
        have hd : a*b*(‖x‖-‖y‖)^2 ≥ 0 := by positivity
        nlinarith only [hd, hab, congrArg (fun t : ℝ => t * (a * ‖x‖^2 + b * ‖y‖^2)) hab]
  let g : ℝ → ℝ := fun x => ‖f x‖ ^ 2
  have hgm : Measurable g := hm.norm.pow_const 2
  have hmove {E : Type} [NormedAddCommGroup E] {F : ℝ → E} (hF : Integrable F) (x : ℝ) :
      Integrable (fun t : ℝ => F (t + x)) := by
    exact (measurePreserving_add_right (volume : Measure ℝ) x).integrable_comp_of_integrable hF
  have hpt (x : ℝ) :
      ‖Y⁻¹ • (∫ t, f (x+t) ∂ν)‖ ^ 2 ≤ Y⁻¹ * ∫ t, g (x+t) ∂ν := by
    have hfi : IntegrableOn (fun t => f (x+t)) s := by
      simpa only [add_comm x] using (hmove h₁ x).integrableOn (s := s)
    have hgi : IntegrableOn (fun t => g (x+t)) s := by
      simpa only [add_comm x] using (hmove h₂ x).integrableOn (s := s)
    have H := hconv.map_set_average_le
      (continuous_norm.pow 2).continuousOn isClosed_univ hν0 hνtop
      (Filter.Eventually.of_forall fun _ => mem_univ _) hfi hgi
    simpa only [average_eq, ← hr, smul_eq_mul] using H
  have hp : Integrable (fun p : ℝ × ℝ => g (p.1 + p.2)) (volume.prod ν) := by
    have hpg : Measurable (fun p : ℝ × ℝ => g (p.1 + p.2)) :=
      hgm.comp (measurable_fst.add measurable_snd)
    apply (integrable_prod_iff' hpg.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun t => hmove h₂ t
    · have hn (x : ℝ) : ‖g x‖ = g x := Real.norm_of_nonneg (sq_nonneg _)
      simp only [hn]
      simp_rw [integral_add_right_eq_self g]
      exact integrable_const _
  have hright := hp.integral_prod_left
  have hri : Integrable (fun x => Y⁻¹ * ∫ t, g (x+t) ∂ν) := by
    exact hright.const_mul _
  have hml : AEStronglyMeasurable (fun x : ℝ => ‖Y⁻¹ • (∫ t, f (x+t) ∂ν)‖ ^ 2) volume := by
    have hF : Measurable (fun p : ℝ × ℝ => f (p.1+p.2)) :=
      hm.comp (measurable_fst.add measurable_snd)
    have hF' := hF.stronglyMeasurable.integral_prod_right' (ν := ν)
    exact ((hF'.const_smul (Y⁻¹ : ℝ)).norm.pow 2).aestronglyMeasurable
  have hli : Integrable (fun x : ℝ => ‖Y⁻¹ • (∫ t, f (x+t) ∂ν)‖ ^ 2) := by
    refine hri.mono' hml (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt x
  have hswap : (∫ x : ℝ, ∫ t, g (x+t) ∂ν) = ∫ t, (∫ x : ℝ, g (x+t)) ∂ν := by
    exact integral_integral_swap (f := fun x t => g (x+t)) hp
  calc
    _ ≤ ∫ x : ℝ, Y⁻¹ * ∫ t, g (x+t) ∂ν := integral_mono hli hri hpt
    _ = _ := by
      rw [integral_const_mul, hswap]
      simp only [integral_add_right_eq_self g, integral_const, hr, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hY.ne', one_mul]

#print axioms moving_average_sq_le

/-- A translated fixed-length average of the zero extension of a block
is the integral over the clipped window (also when that window is empty). -/
theorem translated_indicator_integral {Y lo hi x : ℝ} (hY : 0 ≤ Y) (f : ℝ → ℂ) :
    (∫ t in Ioc (0 : ℝ) Y, (Ioc lo hi).indicator f (x+t)) =
      ∫ t in Ioc (max x lo) (min (x+Y) hi), f t := by
  rw [← intervalIntegral.integral_of_le hY, intervalIntegral.integral_comp_add_left]
  rw [add_zero, intervalIntegral.integral_of_le (le_add_of_nonneg_right hY)]
  rw [setIntegral_indicator measurableSet_Ioc, Set.Ioc_inter_Ioc]

/-- Exact contraction for the clipped Gallagher window, with no separate
loss at either end of the block. -/
theorem clipped_moving_average_sq_le {Y lo hi : ℝ} (hY : 0 < Y) {f : ℝ → ℂ}
    (hm : Measurable f) (h₁ : IntegrableOn f (Ioc lo hi))
    (h₂ : IntegrableOn (fun x => ‖f x‖ ^ 2) (Ioc lo hi)) :
    (∫ x : ℝ, ‖Y⁻¹ • (∫ t in Ioc (max x lo) (min (x+Y) hi), f t)‖ ^ 2) ≤
      ∫ x in Ioc lo hi, ‖f x‖ ^ 2 := by
  have hsq : (fun t => ‖(Ioc lo hi).indicator f t‖ ^ 2) =
      (Ioc lo hi).indicator (fun t => ‖f t‖ ^ 2) := by
    funext t
    by_cases ht : t ∈ Ioc lo hi <;> simp [ht]
  have hclip := h₁.integrable_indicator measurableSet_Ioc
  have hi₂ : Integrable (fun t => ‖(Ioc lo hi).indicator f t‖ ^ 2) := by
    rw [hsq]
    exact h₂.integrable_indicator measurableSet_Ioc
  have H := moving_average_sq_le hY (hm.indicator measurableSet_Ioc) hclip hi₂
  simp_rw [translated_indicator_integral hY.le, hsq, integral_indicator measurableSet_Ioc] at H
  exact H

#print axioms clipped_moving_average_sq_le
end PintzFixedWindowL2
