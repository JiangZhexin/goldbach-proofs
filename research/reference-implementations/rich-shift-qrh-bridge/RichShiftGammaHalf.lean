import PintzJutilaMellinShift
import PintzJutilaDetectorExact
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Complex MeasureTheory Set Filter
open PintzJutilaMellinShift

namespace RichShiftGammaHalf

/-- Uniform Γ bound at the center of the left line.  The only blowup is
from the nearby pole at −1, with distance controlled by δ + |t|. -/
theorem central_gamma :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {β t : ℝ}, 1/2 ≤ β → β < 1 → |t| ≤ 1 →
      ‖Complex.Gamma (verticalPoint (-β) t)‖ * (1+|t|) ≤ 8*M/(1-β+|t|) := by
  have hc : ContinuousOn (fun r : ℝ => Complex.Gamma (r:ℂ)) (Icc 1 2) := by
    intro r hr
    have hd : ContinuousAt Complex.Gamma (r:ℂ) := by
      apply Complex.continuousAt_Gamma
      intro n hn
      have H := congrArg Complex.re hn
      simp at H
      linarith [hr.1,Nat.cast_nonneg (α := ℝ) n]
    exact (hd.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro β t hβ hβ1 ht
  let w := verticalPoint (-β) t
  have hR : w.re = -β := verticalPoint_re _ _
  have hI : w.im = t := verticalPoint_im _ _
  have hw : w ≠ 0 := by intro e; rw [e,Complex.zero_re] at hR; linarith
  have hw1 : w+1 ≠ 0 := Complex.ne_zero_of_re_pos (by simp [hR]; linarith)
  have hRw : (w+1+1).re = 2-β := by simp [hR]; ring
  have hRw' : 2-β ∈ Icc (1:ℝ) 2 := ⟨by linarith,by linarith⟩
  have hf := hM _ hRw'
  rw [Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs] at hf
  have hΓ : ‖Complex.Gamma (w+1+1)‖ ≤ max M 0 := (PintzJutilaMellin.norm_gamma_le_real (s := w+1+1) (by rw [hRw]; linarith)).trans
    ((by rw [hRw]; exact (le_abs_self _).trans hf : Real.Gamma (w+1+1).re ≤ M).trans (le_max_left _ _))
  rw [Complex.Gamma_add_one _ hw1, Complex.Gamma_add_one _ hw, norm_mul, norm_mul] at hΓ
  have hwB : (1/2:ℝ) ≤ ‖w‖ := by
    have H := Complex.abs_re_le_norm w
    rw [hR,abs_neg,abs_of_nonneg (by linarith)] at H
    linarith
  have hw1δ : 1-β ≤ ‖w+1‖ := by
    have H := Complex.abs_re_le_norm (w+1)
    rw [Complex.add_re,hR,Complex.one_re,abs_of_nonneg (by linarith)] at H
    linarith
  have hw1t : |t| ≤ ‖w+1‖ := by simpa [hI] using Complex.abs_im_le_norm (w+1)
  have hden : 0 < 1-β+|t| := by linarith [abs_nonneg t]
  have hb : 1-β+|t| ≤ 4*‖w+1‖*‖w‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hwB (show 0 ≤ ‖w+1‖ by positivity)]
  rw [le_div_iff₀ hden]
  calc
    ‖Complex.Gamma w‖*(1+|t|)*(1-β+|t|) ≤ ‖Complex.Gamma w‖*2*(4*‖w+1‖*‖w‖) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)) hb hden.le (by positivity)
    _ = 8*(‖w+1‖*(‖w‖*‖Complex.Gamma w‖)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hΓ (by norm_num)

theorem inv_abs_core {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in Icc (-1:ℝ) 1, 1/(δ+|t|)) = 2*Real.log ((δ+1)/δ) := by
  let f (t : ℝ) := 1/(δ+|t|)
  have hc : Continuous f := by
    unfold f
    exact continuous_const.div (continuous_const.add continuous_abs)
      (fun t => (add_pos_of_pos_of_nonneg hδ (abs_nonneg t)).ne')
  have hr : (∫ t in (0:ℝ)..1, f t) = Real.log ((δ+1)/δ) := by
    calc
      _ = ∫ t in (0:ℝ)..1, 1/(δ+t) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le zero_le_one]
        intro t ht
        simp [f,abs_of_nonneg ht.1]
      _ = ∫ t in δ..δ+1, 1/t := by
        simpa only [add_zero] using intervalIntegral.integral_comp_add_left
          (a := 0) (b := 1) (fun t : ℝ => 1/t) δ
      _ = _ := by
        apply integral_one_div
        rw [uIcc_of_le (by linarith)]
        intro H
        linarith [H.1]
  have hl : (∫ t in (-1:ℝ)..0, f t) = ∫ t in (0:ℝ)..1, f t := by
    have H := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := 0) f
    simpa [f,abs_neg] using H
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  change (∫ t in (-1:ℝ)..1, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    hl,hr]
  ring

private theorem continuous_left_gamma {β : ℝ} (hβ : 1/2 ≤ β) (hβ1 : β < 1) :
    Continuous (fun t : ℝ => Complex.Gamma (verticalPoint (-β) t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hc : ContinuousAt Complex.Gamma (verticalPoint (-β) t) := by
    apply Complex.continuousAt_Gamma
    intro n hn
    have H := congrArg Complex.re hn
    simp at H
    have hN : (n:ℝ) < 1 := by linarith
    have hn1 : n < 1 := by exact_mod_cast hN
    have hn0 : n = 0 := by omega
    simp [hn0] at H
    linarith
  exact hc.comp (show ContinuousAt (verticalPoint (-β)) t by unfold verticalPoint; fun_prop)

/-- Integrability and the logarithmic loss from the Γ pole at −1.
The constant is absolute and does not depend on β. -/
theorem weighted_gamma_integral :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {β : ℝ}, 1/2 ≤ β → β < 1 →
      let g : ℝ → ℝ := fun t => ‖Complex.Gamma (verticalPoint (-β) t)‖*(1+|t|)
      Integrable g ∧ ∫ t : ℝ, g t ≤ C*(1+Real.log ((1-β)⁻¹)) := by
  obtain ⟨M,hM,hsmall⟩ := central_gamma
  obtain ⟨A,hA,hbig⟩ := gamma_strip_quartic_tail_uniform
  let J : ℝ := ∫ t : ℝ, (1+t^2)⁻¹
  have hJ : 0 ≤ J := integral_nonneg fun _ => by positivity
  refine ⟨16*M+4*A*J,by positivity,?_⟩
  intro β hβ hβ1
  dsimp only
  let δ := 1-β
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  let g : ℝ → ℝ := fun t => ‖Complex.Gamma (verticalPoint (-β) t)‖*(1+|t|)
  let G : ℝ → ℝ := (Icc (-1:ℝ) 1).indicator (fun t => 1/(δ+|t|))
  let R : ℝ → ℝ := fun t => (1+t^2)⁻¹
  have hgc : Continuous g := (continuous_left_gamma hβ hβ1).norm.mul (continuous_const.add continuous_abs)
  have hG : Integrable G := by
    dsimp [G]
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    have hc : Continuous (fun t : ℝ => 1/(δ+|t|)) :=
      continuous_const.div (continuous_const.add continuous_abs)
        (fun t => (add_pos_of_pos_of_nonneg hδ (abs_nonneg t)).ne')
    exact hc.continuousOn.integrableOn_Icc
  have hR : Integrable R := integrable_inv_one_add_sq
  have hbound (t : ℝ) : g t ≤ 8*M*G t + 4*A*R t := by
    by_cases ht : |t| ≤ 1
    · have hs : t ∈ Icc (-1:ℝ) 1 := abs_le.mp ht
      have H := hsmall hβ hβ1 ht
      unfold G
      rw [Set.indicator_of_mem hs, ← div_eq_mul_one_div]
      exact H.trans (le_add_of_nonneg_right (by dsimp [R]; positivity))
    · have hta : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
      have hp : 0 < |t| := by linarith
      have H := hbig (-β) t (by linarith) (by linarith) hta
      have ht2 : 1+t^2 ≤ 2*|t|^3 := by
        have hsq : 1 ≤ |t|^2 := by simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hta 2
        have hpow : |t|^2 ≤ |t|^3 := by nlinarith [mul_nonneg (sq_nonneg |t|) (sub_nonneg.mpr hta)]
        rw [sq_abs] at hsq hpow
        linarith
      have htar : g t ≤ 4*A*R t := by
        calc
          _ ≤ (A/|t|^4)*(2*|t|) := by
            exact mul_le_mul H (by linarith) (by positivity) (by positivity)
          _ = (2*A)/|t|^3 := by field_simp
          _ ≤ _ := by
            dsimp [R]
            rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
            exact (mul_le_mul_of_nonneg_left ht2 (by positivity)).trans_eq (by ring)
      have hG0 : G t = 0 := Set.indicator_of_notMem (fun hs : t ∈ Icc (-1:ℝ) 1 => ht (abs_le.mpr hs)) _
      simpa only [hG0,mul_zero,zero_add] using htar
  have hMaj : Integrable (fun t => 8*M*G t+4*A*R t) := (hG.const_mul _).add (hR.const_mul _)
  have hgI : Integrable g := by
    apply hMaj.mono' hgc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => by rw [Real.norm_of_nonneg (by dsimp [g]; positivity)]; exact hbound t)
  refine ⟨hgI,?_⟩
  have hcore : (∫ t, G t) ≤ 2*(1+Real.log δ⁻¹) := by
    change (∫ t : ℝ, (Icc (-1:ℝ) 1).indicator (fun u => 1/(δ+|u|)) t) ≤ _
    rw [integral_indicator measurableSet_Icc,inv_abs_core hδ, Real.log_div (by positivity) hδ.ne',
      Real.log_inv]
    have H := Real.log_le_sub_one_of_pos (show 0 < δ+1 by linarith)
    linarith
  have hL : 1 ≤ 1+Real.log δ⁻¹ := by
    have hh : 1 ≤ δ⁻¹ := one_le_inv₀ hδ |>.2 hδ1
    linarith [Real.log_nonneg hh]
  calc
    _ ≤ ∫ t : ℝ, 8*M*G t+4*A*R t := integral_mono hgI hMaj hbound
    _ = 8*M*(∫ t : ℝ, G t)+4*A*J := by
      rw [integral_add (hG.const_mul _) (hR.const_mul _),integral_const_mul,integral_const_mul]
    _ ≤ 8*M*(2*(1+Real.log δ⁻¹)) + (4*A*J)*(1+Real.log δ⁻¹) :=
      add_le_add (mul_le_mul_of_nonneg_left hcore (by positivity)) (le_mul_of_one_le_right (by positivity) hL)
    _ = _ := by ring

/-- Quantitative detector bridge: any uniform linear envelope for the
actual left-line L-function and uniform mollifier bound produce the
corresponding logarithmic Γ loss in the exact exponentially smoothed sum. -/
theorem exact_detector_norm_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
      (ξ : ℕ → ℂ) (K : Finset ℕ) (hK0 : 0 ∉ K) (hK : ∀ d ∉ K, ξ d = 0)
      {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 1/2 ≤ ρ.re) (hρ : χ.LFunction ρ = 0)
      {X A B : ℝ}, 0 < X → 0 ≤ A → 0 ≤ B →
      (∀ u : ℝ, ‖χ.LFunction ((ρ.im+u:ℝ)*Complex.I)‖ ≤ A*(1+|u|)) →
      (∀ u : ℝ, ‖PintzJutilaAnalytic.mollifier χ ξ K r ((ρ.im+u:ℝ)*Complex.I)‖ ≤ B) →
      ‖∑' n : ℕ, LSeries.term (PintzJutilaAnalytic.twisted (fun n => χ n) ξ r) ρ n *
        (Real.exp (-(n:ℝ)/X):ℂ)‖ ≤
      C*(X^(-ρ.re)*A*B)*(1+Real.log ((1-ρ.re)⁻¹)) := by
  obtain ⟨C,hC,H⟩ := weighted_gamma_integral
  refine ⟨C/(2*Real.pi), by positivity,?_⟩
  intro q _ χ hχ ξ K hK0 hK r hr ρ hβ hρ X A B hX hA hB hL hM
  have hβ' : 0 < ρ.re := by linarith
  have hβ1 : ρ.re < 1 := by
    by_contra! H'
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) H') hρ
  obtain ⟨hg,hgb⟩ := H hβ hβ1
  dsimp only at hg hgb
  rw [PintzJutilaDetectorExact.equation_2_11_single χ hχ ξ K hK0 hK hr hβ' hρ hX,norm_mul]
  have hc : ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) := by
    rw [← ofReal_ofNat (n := 2), ← ofReal_mul, ← ofReal_one, ← ofReal_div, norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hc]
  have hXAB : 0 ≤ X^(-ρ.re)*A*B := by positivity
  have hb : ‖∫ u : ℝ, (X:ℂ)^(verticalPoint (-ρ.re) u) * Gamma (verticalPoint (-ρ.re) u) *
      (χ.LFunction ((ρ.im+u:ℝ)*Complex.I) *
        PintzJutilaAnalytic.mollifier χ ξ K r ((ρ.im+u:ℝ)*Complex.I))‖ ≤
      (X^(-ρ.re)*A*B) * ∫ u : ℝ, ‖Gamma (verticalPoint (-ρ.re) u)‖*(1+|u|) := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hg.const_mul _)
    filter_upwards [] with u
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,verticalPoint_re]
    calc
      _ ≤ (X^(-ρ.re)*‖Gamma (verticalPoint (-ρ.re) u)‖)*((A*(1+|u|))*B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hL u) (hM u) (norm_nonneg _) (by positivity)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (1/(2*Real.pi))*((X^(-ρ.re)*A*B)*(C*(1+Real.log ((1-ρ.re)⁻¹)))) :=
      mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hgb hXAB)) (by positivity)
    _ = _ := by ring

#print axioms central_gamma
#print axioms inv_abs_core
#print axioms weighted_gamma_integral
#print axioms exact_detector_norm_bound
end RichShiftGammaHalf
