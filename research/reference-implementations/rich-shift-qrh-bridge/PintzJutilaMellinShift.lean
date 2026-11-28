import PintzJutilaMellin
import Zeta23.WeilEF.VerticalLine
import Mathlib.Analysis.Calculus.DSlope

noncomputable section
open Complex MeasureTheory Set Filter Topology

namespace PintzJutilaMellinShift

def verticalPoint (σ t : ℝ) : ℂ := (σ:ℂ)+t*Complex.I

@[simp] theorem verticalPoint_re (σ t : ℝ) : (verticalPoint σ t).re = σ := by simp [verticalPoint]
@[simp] theorem verticalPoint_im (σ t : ℝ) : (verticalPoint σ t).im = t := by simp [verticalPoint]

/-- Analytic representative of (X^w Γ(w) F(w)) when (F(0)=0). -/
def regular (X : ℝ) (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  (X:ℂ)^w * Complex.Gamma (w+1) * dslope F 0 w

theorem regular_eq {X : ℝ} {F : ℂ → ℂ} (hF : F 0 = 0) {w : ℂ} (hw : w ≠ 0) :
    regular X F w = (X:ℂ)^w * Complex.Gamma w * F w := by
  rw [regular, dslope_of_ne _ hw, slope_def_field, sub_zero, hF, sub_zero, Complex.Gamma_add_one _ hw]
  field_simp

theorem regular_differentiable {X : ℝ} (hX : 0 < X) {F : ℂ → ℂ} {w : ℂ} (hw : -1 < w.re)
    (hF : AnalyticAt ℂ F w) : DifferentiableAt ℂ (regular X F) w := by
  have hX0 : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hXp : DifferentiableAt ℂ (fun z : ℂ => (X:ℂ)^z) w :=
    differentiableAt_id.const_cpow (Or.inl hX0)
  have hΓ (n : ℕ) : w+1 ≠ -(n:ℂ) := by
    intro H
    have hn := congrArg Complex.re H
    simp at hn
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hΓd : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z+1)) w :=
    (Complex.differentiableAt_Gamma (w+1) hΓ).comp w (differentiableAt_id.add_const 1)
  exact (hXp.mul hΓd).mul (hF.dslope 0).differentiableAt

/-- Conditional strip shift reduced to one explicit integrable majorant.
At a true detector zero the pole of Γ at 0 is removable, so there is no
residue term to add. -/
theorem shift_at_zero_of_majorant {X : ℝ} (hX : 0 < X) {F : ℂ → ℂ}
    (hzero : F 0 = 0) {a : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ 1 → AnalyticAt ℂ F z)
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hbound : ∀ σ t : ℝ, a ≤ σ → σ ≤ 1 → ‖regular X F (verticalPoint σ t)‖ ≤ φ t)
    (hφtop : Tendsto φ atTop (𝓝 0)) (hφbot : Tendsto φ atBot (𝓝 0)) :
    (∫ t : ℝ, (X:ℂ)^(verticalPoint 1 t) * Complex.Gamma (verticalPoint 1 t) * F (verticalPoint 1 t)) =
    ∫ t : ℝ, (X:ℂ)^(verticalPoint a t) * Complex.Gamma (verticalPoint a t) * F (verticalPoint a t) := by
  have HA : ∀ z : ℂ, a ≤ z.re → z.re ≤ 1 → DifferentiableAt ℂ (regular X F) z :=
    fun z h1 h2 => regular_differentiable hX (ha.trans_le h1) (hF z h1 h2)
  have hshift : (∫ t : ℝ, regular X F (verticalPoint 1 t)) =
      ∫ t : ℝ, regular X F (verticalPoint a t) :=
    Zeta23.WeilEF.vertical_line_shift (by linarith) HA hφ hbound hφtop hφbot
  have H (σ : ℝ) (hσ : σ ≠ 0) :
      (∫ t : ℝ, regular X F (verticalPoint σ t)) =
        ∫ t : ℝ, (X:ℂ)^(verticalPoint σ t) * Complex.Gamma (verticalPoint σ t) * F (verticalPoint σ t) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    apply regular_eq hzero
    intro h
    apply hσ
    simpa using congrArg Complex.re h
  rw [H 1 one_ne_zero,H a ha0.ne] at hshift
  exact hshift

/-- A uniform cubic Γ bound away from the bounded part of the strip.
Three recurrences suffice; no Stirling bounds are needed. -/
theorem gamma_strip_tail {a : ℝ} (ha : -1 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ t : ℝ, a ≤ σ → σ ≤ 1 → 1 ≤ |t| →
      ‖Complex.Gamma (verticalPoint σ t)‖ ≤ M / |t|^3 := by
  have hcont : ContinuousOn (fun r : ℝ => Complex.Gamma (r:ℂ)) (Icc 2 4) := by
    intro r hr
    have hG : ContinuousAt Complex.Gamma (r:ℂ) := by
      apply Complex.continuousAt_Gamma
      intro n hn
      have H := congrArg Complex.re hn
      simp at H
      linarith [hr.1,Nat.cast_nonneg (α := ℝ) n]
    exact (hG.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro σ t hσ hσ1 ht
  let w := verticalPoint σ t
  have hwI : w.im = t := verticalPoint_im σ t
  have hwR : w.re = σ := verticalPoint_re σ t
  have ht0 : 0 < |t| := by linarith
  have hn0 : w ≠ 0 := by intro e; rw [e,Complex.zero_im] at hwI; norm_num [← hwI] at ht
  have hn1 : w+1 ≠ 0 := by
    intro e
    have H := congrArg Complex.im e
    simp [hwI] at H
    norm_num [H] at ht
  have hn2 : w+1+1 ≠ 0 := by
    intro e
    have H := congrArg Complex.im e
    simp [hwI] at H
    norm_num [H] at ht
  have D (n : ℕ) : |t| ≤ ‖w+(n:ℂ)‖ := by simpa [hwI] using Complex.abs_im_le_norm (w+(n:ℂ))
  have h1 : |t| ≤ ‖w‖ := by simpa using D 0
  have h2 : |t| ≤ ‖w+1‖ := by simpa using D 1
  have h3 : |t| ≤ ‖w+1+1‖ := by
    rw [add_assoc,show (1:ℂ)+1=2 by norm_num]
    exact D 2
  have hre : (w+1+1+1).re = σ+3 := by simp [hwR]; ring
  have hsmall : σ+3 ∈ Icc (2:ℝ) 4 := ⟨by linarith,by linarith⟩
  have hΓR : Real.Gamma (σ+3) ≤ max M 0 := by
    have H := hM (σ+3) hsmall
    rw [Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs] at H
    exact (le_abs_self _).trans (H.trans (le_max_left _ _))
  have hΓ := (PintzJutilaMellin.norm_gamma_le_real (s := w+1+1+1) (by rw [hre]; linarith)).trans
    (by rwa [hre] : Real.Gamma (w+1+1+1).re ≤ max M 0)
  rw [Complex.Gamma_add_one _ hn2,Complex.Gamma_add_one _ hn1,Complex.Gamma_add_one _ hn0,
    norm_mul,norm_mul,norm_mul] at hΓ
  apply (le_div_iff₀ (show 0 < |t|^3 by positivity)).mpr
  calc
    _ = |t| * (|t| * (|t| * ‖Complex.Gamma w‖)) := by ring
    _ ≤ _ := by
      exact (mul_le_mul h3 (mul_le_mul h2 (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
        (by positivity) (norm_nonneg _)) (by positivity) (norm_nonneg _)).trans hΓ

/-- Shift the canonical detector integral from 1 to the chosen line in ((-1,0)).
Linear growth of the other factors along the strip is enough, as the pole
cancels at the input zero. -/
theorem shift_at_zero_of_linear_growth {X : ℝ} (hX : 0 < X) {F : ℂ → ℂ}
    (hzero : F 0 = 0) {a : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ 1 → AnalyticAt ℂ F z)
    {B : ℝ} (hB : 0 ≤ B)
    (hlin : ∀ σ t : ℝ, a ≤ σ → σ ≤ 1 → ‖F (verticalPoint σ t)‖ ≤ B*(1+|t|)) :
    (∫ t : ℝ, (X:ℂ)^(verticalPoint 1 t) * Complex.Gamma (verticalPoint 1 t) * F (verticalPoint 1 t)) =
    ∫ t : ℝ, (X:ℂ)^(verticalPoint a t) * Complex.Gamma (verticalPoint a t) * F (verticalPoint a t) := by
  obtain ⟨M,hM,hΓ⟩ := gamma_strip_tail ha
  have hXc : Continuous (fun σ : ℝ => X^σ) := by
    simp_rw [Real.rpow_def_of_pos hX]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  obtain ⟨U,hU⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a 1) hXc.continuousOn
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 1 ⟨by linarith,le_rfl⟩)
  have hXb (σ : ℝ) (hσ : σ ∈ Icc a 1) : X^σ ≤ U := (Real.le_norm_self _).trans (hU σ hσ)
  let box := Complex.reProdIm (Set.Icc a 1) (Set.Icc (-1) 1)
  have hbcompact : IsCompact box := isCompact_Icc.reProdIm isCompact_Icc
  have hbcont : ContinuousOn (regular X F) box := by
    intro z hz
    have H : z.re ∈ Icc a 1 := (Complex.mem_reProdIm.mp hz).1
    exact (regular_differentiable hX (ha.trans_le H.1) (hF z H.1 H.2)).continuousAt.continuousWithinAt
  obtain ⟨V,hV⟩ := hbcompact.exists_bound_of_continuousOn hbcont
  let C := 4*(U*M*B) + 2*(max V 0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm (σ t : ℝ) (hσ : a ≤ σ) (hσ1 : σ ≤ 1) :
      ‖regular X F (verticalPoint σ t)‖ ≤ C/(1+t^2) := by
    by_cases ht : 1 ≤ |t|
    · have htn : verticalPoint σ t ≠ 0 := by
        intro e
        have H := congrArg Complex.im e
        simp at H
        norm_num [H] at ht
      rw [regular_eq hzero htn,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,verticalPoint_re]
      have hta : 0 < |t| := by linarith
      have ht₁ : 1+|t| ≤ 2*|t| := by linarith
      have ht₂ : 1+t^2 ≤ 2*|t|^2 := by
        have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) ht 2
        rw [sq_abs] at *
        linarith
      have hC' : 4*(U*M*B) ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
      calc
        _ ≤ (U * (M/|t|^3)) * (B*(1+|t|)) :=
          mul_le_mul (mul_le_mul (hXb σ ⟨hσ,hσ1⟩) (hΓ σ t hσ hσ1 ht) (norm_nonneg _) hU0)
            (hlin σ t hσ hσ1) (norm_nonneg _) (by positivity)
        _ ≤ (U * (M/|t|^3)) * (B*(2*|t|)) := by gcongr
        _ = (2*(U*M*B))/|t|^2 := by field_simp
        _ ≤ (4*(U*M*B))/(1+t^2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          exact (mul_le_mul_of_nonneg_left ht₂ (by positivity)).trans_eq (by ring)
        _ ≤ _ := div_le_div_of_nonneg_right hC' (by positivity)
    · have hmem : verticalPoint σ t ∈ box := by
        apply Complex.mem_reProdIm.mpr
        simp only [verticalPoint_re,verticalPoint_im]
        obtain ⟨h₁,h₂⟩ := abs_le.mp (le_of_not_ge ht)
        exact ⟨⟨hσ,hσ1⟩,h₁,h₂⟩
      have hv : ‖regular X F (verticalPoint σ t)‖ ≤ max V 0 := (hV _ hmem).trans (le_max_left _ _)
      refine hv.trans ?_
      rw [le_div_iff₀ (by positivity)]
      have hts : t^2 ≤ 1 := by
        have := pow_le_pow_left₀ (abs_nonneg t) (le_of_not_ge ht) 2
        simpa using this
      have H := mul_le_mul_of_nonneg_left (show 1+t^2 ≤ 2 by linarith) (le_max_right V 0)
      dsimp [C]
      nlinarith [mul_nonneg (mul_nonneg hU0 hM) hB]
  have hφ : Integrable (fun t : ℝ => C/(1+t^2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C
  have htPow : Tendsto (fun t : ℝ => 1+t^2) atTop atTop := by
    exact tendsto_atTop_mono (fun t : ℝ => by linarith) (tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num))
  have htop := htPow.const_div_atTop C
  have hbot : Tendsto (fun t : ℝ => C/(1+t^2)) atBot (𝓝 0) := by
    simpa only [Function.comp_def, neg_sq] using htop.comp tendsto_neg_atBot_atTop
  exact shift_at_zero_of_majorant hX hzero ha ha0 hF hφ hm htop hbot

/-- A uniform quartic Γ bound away from the bounded part of the strip.
Four recurrences suffice; no Stirling bounds are needed. -/
theorem gamma_strip_quartic_tail_uniform :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ t : ℝ, -1 < σ → σ ≤ 1 → 1 ≤ |t| →
      ‖Complex.Gamma (verticalPoint σ t)‖ ≤ M / |t|^4 := by
  have hcont : ContinuousOn (fun r : ℝ => Complex.Gamma (r:ℂ)) (Icc 3 5) := by
    intro r hr
    have hG : ContinuousAt Complex.Gamma (r:ℂ) := by
      apply Complex.continuousAt_Gamma
      intro n hn
      have H := congrArg Complex.re hn
      simp at H
      linarith [hr.1,Nat.cast_nonneg (α := ℝ) n]
    exact (hG.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro σ t hσ hσ1 ht
  let w := verticalPoint σ t
  have hwI : w.im = t := verticalPoint_im σ t
  have hwR : w.re = σ := verticalPoint_re σ t
  have ht0 : 0 < |t| := by linarith
  have hn0 : w ≠ 0 := by intro e; rw [e,Complex.zero_im] at hwI; norm_num [← hwI] at ht
  have hn1 : w+1 ≠ 0 := by
    intro e
    have H := congrArg Complex.im e
    simp [hwI] at H
    norm_num [H] at ht
  have hn2 : w+1+1 ≠ 0 := by
    intro e
    have H := congrArg Complex.im e
    simp [hwI] at H
    norm_num [H] at ht
  have hn3 : w+1+1+1 ≠ 0 := by
    intro e
    have H := congrArg Complex.im e
    simp [hwI] at H
    norm_num [H] at ht
  have D (n : ℕ) : |t| ≤ ‖w+(n:ℂ)‖ := by simpa [hwI] using Complex.abs_im_le_norm (w+(n:ℂ))
  have h1 : |t| ≤ ‖w‖ := by simpa using D 0
  have h2 : |t| ≤ ‖w+1‖ := by simpa using D 1
  have h3 : |t| ≤ ‖w+1+1‖ := by
    rw [add_assoc,show (1:ℂ)+1=2 by norm_num]
    exact D 2
  have h4 : |t| ≤ ‖w+1+1+1‖ := by
    rw [show w+1+1+1=w+3 by ring]
    exact D 3
  have hre : (w+1+1+1+1).re = σ+4 := by simp [hwR]; ring
  have hsmall : σ+4 ∈ Icc (3:ℝ) 5 := ⟨by linarith,by linarith⟩
  have hΓR : Real.Gamma (σ+4) ≤ max M 0 := by
    have H := hM (σ+4) hsmall
    rw [Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs] at H
    exact (le_abs_self _).trans (H.trans (le_max_left _ _))
  have hΓ := (PintzJutilaMellin.norm_gamma_le_real (s := w+1+1+1+1) (by rw [hre]; linarith)).trans
    (by rwa [hre] : Real.Gamma (w+1+1+1+1).re ≤ max M 0)
  rw [Complex.Gamma_add_one _ hn3,Complex.Gamma_add_one _ hn2,Complex.Gamma_add_one _ hn1,Complex.Gamma_add_one _ hn0,
    norm_mul,norm_mul,norm_mul,norm_mul] at hΓ
  apply (le_div_iff₀ (show 0 < |t|^4 by positivity)).mpr
  calc
    _ = |t| * (|t| * (|t| * (|t| * ‖Complex.Gamma w‖))) := by ring
    _ ≤ _ := by
      exact (mul_le_mul h4 (mul_le_mul h3 (mul_le_mul h2 (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
        (by positivity) (norm_nonneg _)) (by positivity) (norm_nonneg _)) (by positivity) (norm_nonneg _)).trans hΓ

theorem gamma_strip_quartic_tail {a : ℝ} (ha : -1 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ t : ℝ, a ≤ σ → σ ≤ 1 → 1 ≤ |t| →
      ‖Complex.Gamma (verticalPoint σ t)‖ ≤ M / |t|^4 := by
  obtain ⟨M,hM,H⟩ := gamma_strip_quartic_tail_uniform
  exact ⟨M,hM,fun σ t h => H σ t (ha.trans_le h)⟩

/-- Shift the canonical detector integral from 1 to the chosen line in ((-1,0)).
Quadratic growth of the other factors along the strip is enough, as the pole
cancels at the input zero. -/
theorem shift_at_zero_quadratic_package {X : ℝ} (hX : 0 < X) {F : ℂ → ℂ}
    (hzero : F 0 = 0) {a : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ 1 → AnalyticAt ℂ F z)
    {B : ℝ} (hB : 0 ≤ B)
    (hlin : ∀ σ t : ℝ, a ≤ σ → σ ≤ 1 → ‖F (verticalPoint σ t)‖ ≤ B*(1+|t|)^2) :
    ((∫ t : ℝ, (X:ℂ)^(verticalPoint 1 t) * Complex.Gamma (verticalPoint 1 t) * F (verticalPoint 1 t)) =
    ∫ t : ℝ, (X:ℂ)^(verticalPoint a t) * Complex.Gamma (verticalPoint a t) * F (verticalPoint a t)) ∧
      Integrable (fun t : ℝ => (X:ℂ)^(verticalPoint a t) * Complex.Gamma (verticalPoint a t) * F (verticalPoint a t)) := by
  obtain ⟨M,hM,hΓ⟩ := gamma_strip_quartic_tail ha
  have hXc : Continuous (fun σ : ℝ => X^σ) := by
    simp_rw [Real.rpow_def_of_pos hX]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  obtain ⟨U,hU⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a 1) hXc.continuousOn
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 1 ⟨by linarith,le_rfl⟩)
  have hXb (σ : ℝ) (hσ : σ ∈ Icc a 1) : X^σ ≤ U := (Real.le_norm_self _).trans (hU σ hσ)
  let box := Complex.reProdIm (Set.Icc a 1) (Set.Icc (-1) 1)
  have hbcompact : IsCompact box := isCompact_Icc.reProdIm isCompact_Icc
  have hbcont : ContinuousOn (regular X F) box := by
    intro z hz
    have H : z.re ∈ Icc a 1 := (Complex.mem_reProdIm.mp hz).1
    exact (regular_differentiable hX (ha.trans_le H.1) (hF z H.1 H.2)).continuousAt.continuousWithinAt
  obtain ⟨V,hV⟩ := hbcompact.exists_bound_of_continuousOn hbcont
  let C := 8*(U*M*B) + 2*(max V 0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm (σ t : ℝ) (hσ : a ≤ σ) (hσ1 : σ ≤ 1) :
      ‖regular X F (verticalPoint σ t)‖ ≤ C/(1+t^2) := by
    by_cases ht : 1 ≤ |t|
    · have htn : verticalPoint σ t ≠ 0 := by
        intro e
        have H := congrArg Complex.im e
        simp at H
        norm_num [H] at ht
      rw [regular_eq hzero htn,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,verticalPoint_re]
      have hta : 0 < |t| := by linarith
      have ht₁ : 1+|t| ≤ 2*|t| := by linarith
      have ht₂ : 1+t^2 ≤ 2*|t|^2 := by
        have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) ht 2
        rw [sq_abs] at *
        linarith
      have hC' : 8*(U*M*B) ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
      calc
        _ ≤ (U * (M/|t|^4)) * (B*(1+|t|)^2) :=
          mul_le_mul (mul_le_mul (hXb σ ⟨hσ,hσ1⟩) (hΓ σ t hσ hσ1 ht) (norm_nonneg _) hU0)
            (hlin σ t hσ hσ1) (norm_nonneg _) (by positivity)
        _ ≤ (U * (M/|t|^4)) * (B*(2*|t|)^2) := by gcongr
        _ = (4*(U*M*B))/|t|^2 := by field_simp; norm_num
        _ ≤ (8*(U*M*B))/(1+t^2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          exact (mul_le_mul_of_nonneg_left ht₂ (by positivity)).trans_eq (by ring)
        _ ≤ _ := div_le_div_of_nonneg_right hC' (by positivity)
    · have hmem : verticalPoint σ t ∈ box := by
        apply Complex.mem_reProdIm.mpr
        simp only [verticalPoint_re,verticalPoint_im]
        obtain ⟨h₁,h₂⟩ := abs_le.mp (le_of_not_ge ht)
        exact ⟨⟨hσ,hσ1⟩,h₁,h₂⟩
      have hv : ‖regular X F (verticalPoint σ t)‖ ≤ max V 0 := (hV _ hmem).trans (le_max_left _ _)
      refine hv.trans ?_
      rw [le_div_iff₀ (by positivity)]
      have hts : t^2 ≤ 1 := by
        have := pow_le_pow_left₀ (abs_nonneg t) (le_of_not_ge ht) 2
        simpa using this
      have H := mul_le_mul_of_nonneg_left (show 1+t^2 ≤ 2 by linarith) (le_max_right V 0)
      dsimp [C]
      nlinarith [mul_nonneg (mul_nonneg hU0 hM) hB]
  have hφ : Integrable (fun t : ℝ => C/(1+t^2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C
  have htPow : Tendsto (fun t : ℝ => 1+t^2) atTop atTop := by
    exact tendsto_atTop_mono (fun t : ℝ => by linarith) (tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num))
  have htop := htPow.const_div_atTop C
  have hbot : Tendsto (fun t : ℝ => C/(1+t^2)) atBot (𝓝 0) := by
    simpa only [Function.comp_def, neg_sq] using htop.comp tendsto_neg_atBot_atTop
  refine ⟨shift_at_zero_of_majorant hX hzero ha ha0 hF hφ hm htop hbot, ?_⟩
  have hI : Integrable (fun t : ℝ => regular X F (verticalPoint a t)) :=
    Zeta23.WeilEF.integrable_line
      (fun t => regular_differentiable hX (by simpa using ha) (hF _ (by simp) (by simpa using (show a ≤ 1 by linarith))))
      hφ (hm a · le_rfl (by linarith))
  refine hI.congr (Filter.Eventually.of_forall fun t => ?_)
  apply regular_eq hzero
  intro e
  exact ha0.ne (by simpa using congrArg Complex.re e)

theorem shift_at_zero_of_quadratic_growth {X : ℝ} (hX : 0 < X) {F : ℂ → ℂ}
    (hzero : F 0 = 0) {a : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ 1 → AnalyticAt ℂ F z)
    {B : ℝ} (hB : 0 ≤ B)
    (hlin : ∀ σ t : ℝ, a ≤ σ → σ ≤ 1 → ‖F (verticalPoint σ t)‖ ≤ B*(1+|t|)^2) :
    (∫ t : ℝ, (X:ℂ)^(verticalPoint 1 t) * Complex.Gamma (verticalPoint 1 t) * F (verticalPoint 1 t)) =
    ∫ t : ℝ, (X:ℂ)^(verticalPoint a t) * Complex.Gamma (verticalPoint a t) * F (verticalPoint a t) :=
  (shift_at_zero_quadratic_package hX hzero ha ha0 hF hB hlin).1

#print axioms shift_at_zero_of_majorant
#print axioms gamma_strip_tail
#print axioms shift_at_zero_of_linear_growth
#print axioms gamma_strip_quartic_tail
#print axioms shift_at_zero_of_quadratic_growth
end PintzJutilaMellinShift
