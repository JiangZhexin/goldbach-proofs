import Zeta23.GammaFacts.StirlingVert
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open Set
namespace PintzJutilaGammaRatio

def z (x t : ℝ) : ℂ := (x:ℂ) + Complex.I*t
def L (x t : ℝ) : ℝ := Real.log ‖Complex.Gamma (z x t)‖

@[simp] theorem re_z (x t : ℝ) : (z x t).re = x := by simp [z]
@[simp] theorem im_z (x t : ℝ) : (z x t).im = t := by simp [z]

theorem gamma_hasDeriv {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (fun x => Complex.Gamma (z x t)) (deriv Complex.Gamma (z x t)) x := by
  have hD := (Complex.differentiableAt_Gamma (z x t) (fun m e => by
    have he := congrArg Complex.re e
    simp at he
    linarith [Nat.cast_nonneg (α := ℝ) m])).hasDerivAt
  have hZ : HasDerivAt (fun x => z x t) (1:ℂ) x :=
    ((hasDerivAt_id x).ofReal_comp).add_const _
  have H := (hD.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x hZ
  simpa [Function.comp_def] using H

theorem log_gamma_hasDeriv {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (fun x => L x t) (Complex.digamma (z x t)).re x := by
  let G := fun x => Complex.Gamma (z x t)
  have hz : G x ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hx)
  have hn : 0 < ‖G x‖ := norm_pos_iff.mpr hz
  have H := ((gamma_hasDeriv hx t).norm_sq.log (pow_ne_zero 2 hn.ne')).div_const (2:ℝ)
  have he : (fun u => Real.log (‖G u‖^2)/2) = fun u => L u t := by
    funext u
    rw [Real.log_pow]
    unfold L G
    push_cast
    ring
  rw [he] at H
  convert H using 1
  rw [Complex.digamma_def, logDeriv_apply, Complex.div_re, Complex.normSq_eq_norm_sq]
  change _ = (2 * @inner ℝ ℂ _ (G x) (deriv Complex.Gamma (z x t)) / ‖G x‖^2) / 2
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  change _ = (2 * ((starRingEnd ℂ) (G x) * deriv Complex.Gamma (z x t)).re / ‖G x‖^2) / 2
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  dsimp [G] at hn ⊢
  field_simp
  <;> ring

private theorem digamma_continuousAt {w : ℂ} (hw : 0 < w.re) :
    ContinuousAt Complex.digamma w := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGamD : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := fun s hs =>
    (Complex.differentiableAt_Gamma s (fun m e => by
      have he := congrArg Complex.re e
      simp at he
      change 0 < s.re at hs
      linarith [Nat.cast_nonneg (α := ℝ) m])).differentiableWithinAt
  have hA := hGamD.analyticOnNhd hU w hw
  exact (hA.deriv.continuousAt.div hA.continuousAt (Complex.Gamma_ne_zero_of_re_pos hw)).congr
    (Filter.Eventually.of_forall fun x => by rw [Complex.digamma_def, logDeriv_apply]; rfl)

private theorem large_height {B x t : ℝ} (hx : 0 < x) (hB : x ≤ B) (ht : 1 ≤ |t|) :
    |(Complex.digamma (z x t)).re - Real.log (1+|t|)| ≤ 4 + Real.log (B+1) + Real.log 2 := by
  let w := z x t
  have him : w.im = t := im_z _ _
  have hw : 0 < w.re := by simpa [w] using hx
  have hwNorm : |t| ≤ ‖w‖ := by simpa only [him] using Complex.abs_im_le_norm w
  have hT : 0 < |t| := by linarith
  have hn : 0 < ‖w‖ := hT.trans_le hwNorm
  have hS := Zeta23.StirlingVert.digamma_stirling hw (by rw [him]; linarith)
  rw [him] at hS
  have hT2 : 1 ≤ t^2 := by rw [← sq_abs]; nlinarith
  have hE : |(Complex.digamma w - Complex.log w + (1/2:ℂ)/w).re| ≤ 3 :=
    ((Complex.abs_re_le_norm _).trans hS).trans (by
      apply div_le_of_le_mul₀ (by positivity) (by norm_num); linarith)
  have hI : |(((1/2:ℂ)/w).re)| ≤ 1 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, norm_div, norm_one, show ‖(2:ℂ)‖ = 2 by norm_num]
    apply (div_le_iff₀ hn).mpr
    linarith
  have hupper : ‖w‖ ≤ (B+1)*(1+|t|) := by
    calc
      _ ≤ x+|t| := by
        have H := norm_add_le (x:ℂ) (Complex.I*(t:ℂ))
        simpa only [w,z,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx] using H
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ B by linarith) (abs_nonneg t)]
  have hlower : 1+|t| ≤ 2*‖w‖ := by linarith
  have hLogUpper := Real.log_le_log hn hupper
  have hLogLower := Real.log_le_log (by positivity : 0 < 1+|t|) hlower
  rw [Real.log_mul (by linarith : B+1 ≠ 0) (by positivity)] at hLogUpper
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hn.ne'] at hLogLower
  rw [Complex.add_re, Complex.sub_re, Complex.log_re] at hE
  have H1 := abs_le.mp hE
  have H2 := abs_le.mp hI
  apply abs_le.mpr
  have hBLog : 0 ≤ Real.log (B+1) := Real.log_nonneg (by linarith)
  have h2Log : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  change -_ ≤ (Complex.digamma w).re - Real.log (1+|t|) ∧ _ ≤ _
  constructor <;> linarith

private theorem uniform_digamma {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc A B, ∀ t : ℝ,
      |(Complex.digamma (z x t)).re - Real.log (1+|t|)| ≤ K := by
  let X := (Icc A B) ×ˢ (Icc (-1:ℝ) 1)
  let f (p : ℝ × ℝ) := |(Complex.digamma (z p.1 p.2)).re - Real.log (1+|p.2|)|
  have hX : IsCompact X := isCompact_Icc.prod isCompact_Icc
  have hf : ContinuousOn f X := by
    intro p hp
    have hzC : ContinuousAt (fun p : ℝ × ℝ => z p.1 p.2) p := by unfold z; fun_prop
    have hd : 0 < (z p.1 p.2).re := by simpa using hA.trans_le hp.1.1
    have hD : ContinuousAt (fun p : ℝ × ℝ => Complex.digamma (z p.1 p.2)) p :=
      (digamma_continuousAt hd).comp (x := p) hzC
    have hre : ContinuousAt (fun p : ℝ × ℝ => (Complex.digamma (z p.1 p.2)).re) p :=
      Complex.continuous_re.continuousAt.comp hD
    have hbase : ContinuousAt (fun p : ℝ × ℝ => 1+|p.2|) p :=
      continuousAt_const.add continuous_snd.continuousAt.abs
    have hL : ContinuousAt (fun p : ℝ × ℝ => Real.log (1+|p.2|)) p :=
      hbase.log (show (1:ℝ)+|p.2| ≠ 0 by positivity)
    exact (hre.sub hL).abs.continuousWithinAt
  obtain ⟨J, hJ⟩ := hX.bddAbove_image hf
  let K := max 0 (max J (4 + Real.log (B+1) + Real.log 2))
  refine ⟨K, le_max_left _ _, ?_⟩
  intro x hx t
  by_cases ht : 1 ≤ |t|
  · exact (large_height (hA.trans_le hx.1) hx.2 ht).trans
      ((le_max_right J _).trans (le_max_right 0 _))
  · have hxt : (x,t) ∈ X := ⟨hx, abs_le.mp (le_of_not_ge ht)⟩
    exact (hJ (mem_image_of_mem f hxt)).trans
      ((le_max_left J _).trans (le_max_right 0 _))

set_option backward.isDefEq.respectTransparency false in
/-- Uniform vertical Gamma comparison on any compact positive real strip.
The ordinate is unrestricted and the power is exactly the difference of
the real parts. -/
theorem gamma_ratio {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc A B, ∀ b ∈ Icc A B, ∀ t : ℝ,
      ‖Complex.Gamma (z a t)‖ / ‖Complex.Gamma (z b t)‖ ≤
        C*(1+|t|)^(a-b) := by
  obtain ⟨K,hK,h⟩ := uniform_digamma hA hAB
  refine ⟨Real.exp (K*(B-A)), Real.exp_pos _, ?_⟩
  intro a ha b hb t
  let u := 1+|t|
  have hu : 0 < u := by dsimp [u]; positivity
  let F (x : ℝ) := L x t - x*Real.log u
  have hd (x : ℝ) (hx : x ∈ Icc A B) :
      HasDerivAt F ((Complex.digamma (z x t)).re - Real.log u) x := by
    have H := (log_gamma_hasDeriv (hA.trans_le hx.1) t).sub ((hasDerivAt_id x).mul_const (Real.log u))
    convert H using 1
    · rfl
    · simp
  have order_bound (x y : ℝ) (hx : x ∈ Icc A B) (hy : y ∈ Icc A B) (hxy : x ≤ y) :
      |F y - F x| ≤ K*(B-A) := by
    have H := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := x) (b := y) (f := F)
      (f' := fun x => (Complex.digamma (z x t)).re - Real.log u)
      (fun w hw => (hd w ⟨hx.1.trans hw.1, hw.2.trans hy.2⟩).hasDerivWithinAt)
      (fun w hw => by
        rw [Real.norm_eq_abs]
        exact h w ⟨hx.1.trans hw.1, hw.2.le.trans hy.2⟩ t)
      y (right_mem_Icc.mpr hxy)
    rw [Real.norm_eq_abs] at H
    exact H.trans (mul_le_mul_of_nonneg_left (by linarith [hx.1,hy.2]) hK)
  have hBd : |F a - F b| ≤ K*(B-A) := by
    rcases le_total b a with hab|hab
    · exact order_bound b a hb ha hab
    · rw [abs_sub_comm]
      exact order_bound a b ha hb hab
  have hga : 0 < ‖Complex.Gamma (z a t)‖ := norm_pos_iff.mpr
    (Complex.Gamma_ne_zero_of_re_pos (by simpa using hA.trans_le ha.1))
  have hgb : 0 < ‖Complex.Gamma (z b t)‖ := norm_pos_iff.mpr
    (Complex.Gamma_ne_zero_of_re_pos (by simpa using hA.trans_le hb.1))
  have H : Real.log (‖Complex.Gamma (z a t)‖ / ‖Complex.Gamma (z b t)‖) ≤
      K*(B-A)+(a-b)*Real.log u := by
    rw [Real.log_div hga.ne' hgb.ne']
    have H := (abs_le.mp hBd).2
    dsimp [F,L] at H
    linarith
  have H' := Real.exp_le_exp.mpr H
  rw [Real.exp_log (div_pos hga hgb), Real.exp_add] at H'
  change _ ≤ Real.exp _ * u^(a-b)
  rw [Real.rpow_def_of_pos hu]
  simpa [u, mul_comm (Real.log u)] using H'

#print axioms gamma_ratio
#print axioms log_gamma_hasDeriv
end PintzJutilaGammaRatio
