import PintzWeilZetaWindow
import Zeta23.WeilEF.VerticalLine
import Zeta23.Poisson.PaperFT
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open MeasureTheory Set Filter Zeta23 Zeta23.WeilEF
namespace PintzWeilZetaArchimedean

private def line (r : ℝ) : ℂ := 1/2+Complex.I*r

private theorem line_re (r : ℝ) : (line r).re = 1/2 := by norm_num [line,Complex.mul_re]
private theorem line_im (r : ℝ) : (line r).im = r := by norm_num [line,Complex.mul_im]

private theorem line_norm (r : ℝ) : 1+|r| ≤ 3*‖line r‖ := by
  have h₁ := Complex.abs_re_le_norm (line r)
  have h₂ := Complex.abs_im_le_norm (line r)
  rw [line_re, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h₁
  rw [line_im] at h₂
  linarith

/-- The archimedean bracket has a harmless one-quarter power envelope. -/
theorem gamma_quarter_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, |EF.gammaBracket r| ≤ C*(1+|r|)^(1/4:ℝ) := by
  obtain ⟨A,hA,hψ⟩ := digamma_growth_strip
  refine ⟨8*A+|Real.log Real.pi|, by positivity, ?_⟩
  intro r
  let s : ℂ := 1/4+Complex.I*r/2
  have hs : s.re = 1/4 := by norm_num [s,Complex.mul_re,Complex.div_ofNat_re]
  have hi : s.im = r/2 := by norm_num [s,Complex.mul_im,Complex.div_ofNat_im]
  have hq : 1 ≤ (1+|r|)^(1/4:ℝ) := Real.one_le_rpow (by linarith [abs_nonneg r]) (by norm_num)
  have hL : Real.log (2+|s.im|) ≤ 8*(1+|r|)^(1/4:ℝ) := by
    have H := Real.log_le_rpow_div (x := 2+|s.im|) (by positivity) (by norm_num : (0:ℝ)<1/4)
    have H₁ : (2+|s.im|)^(1/4:ℝ) ≤ (2*(1+|r|))^(1/4:ℝ) := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      rw [hi, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      linarith [abs_nonneg r]
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity)] at H₁
    have H₂ : (2:ℝ)^(1/4:ℝ) ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
        (by norm_num : (1/4:ℝ)≤1)
    nlinarith only [H,H₁,mul_le_mul_of_nonneg_right H₂ (by positivity : 0 ≤ (1+|r|)^(1/4:ℝ))]
  change |(Complex.digamma s).re-Real.log Real.pi| ≤ _
  calc
    _ ≤ |(Complex.digamma s).re| + |Real.log Real.pi| := abs_sub _ _
    _ ≤ ‖Complex.digamma s‖ + |Real.log Real.pi| := add_le_add (Complex.abs_re_le_norm _) le_rfl
    _ ≤ A*Real.log (2+|s.im|) + |Real.log Real.pi| :=
      add_le_add (hψ s (by linarith) (by linarith)) le_rfl
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hL hA.le,
      mul_le_mul_of_nonneg_left hq (abs_nonneg (Real.log Real.pi))]

private theorem normalized_bump_laplace {g : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hg : Continuous g) (hn : ∀ u, 0 ≤ g u)
    (hl : ∀ v ≤ -δ, g v = 0) (hr : ∀ v ≥ δ, g v = 0)
    (hm : (∫ v in (-δ)..δ, g v) = 1) (r : ℝ) :
    ‖∫ v : ℝ, (g v:ℂ) * Complex.exp ((v:ℂ)*line r)‖ ≤ Real.exp δ := by
  have hs : Function.support g ⊆ Ioc (-δ) δ := by
    intro v hv
    exact ⟨lt_of_not_ge (fun h => hv (hl v h)), (lt_of_not_ge (fun h => hv (hr v h))).le⟩
  have hi : Integrable g := hg.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset isClosed_closure
      (closure_minimal (hs.trans Ioc_subset_Icc_self) isClosed_Icc))
  have he : ∫ v : ℝ, g v = 1 := by
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
    exact hm
  have H : ‖∫ v : ℝ, (g v:ℂ) * Complex.exp ((v:ℂ)*line r)‖ ≤
      ∫ v : ℝ, Real.exp δ * g v := by
    apply norm_integral_le_of_norm_le (hi.const_mul _) (Eventually.of_forall _)
    intro v
    by_cases hv : g v = 0
    · simp [hv]
    have hmem := hs hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn v),
      Complex.norm_exp, Complex.re_ofReal_mul, line_re, mul_comm (g v)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hmem.2])) (hn v)
  simpa [integral_const_mul,he] using H

private theorem decaying_bump_laplace {g : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hg : ContDiff ℝ 2 g)
    (hgs : ∀ u, g u ≠ 0 → |u| ≤ δ) (r : ℝ) :
    ‖∫ v : ℝ, (g v:ℂ) * Complex.exp ((v:ℂ)*line r)‖ ≤
      9*Real.exp δ*(∫ v, ‖deriv (deriv (fun u : ℝ => (g u : ℂ))) v‖) / (1+|r|)^2 := by
  let f : ℝ → ℂ := fun u => g u
  let z : ℂ := -Complex.I * line r
  have hf : ContDiff ℝ 2 f := Complex.ofRealCLM.contDiff.comp hg
  have hfs (u : ℝ) (hu : f u ≠ 0) : |u| ≤ δ := hgs _ (by simpa [f] using hu)
  have hnorm : ‖z‖ = ‖line r‖ := by simp [z]
  have hnz : 0 < ‖z‖ := by rw [hnorm]; linarith [line_norm r, abs_nonneg r]
  have him : z.im = -(line r).re := by simp [z, Complex.mul_im]
  have hE : Real.exp (|z.im| * δ) ≤ Real.exp δ := by
    rw [him, line_re, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hG : (∫ v : ℝ, (g v:ℂ) * Complex.exp ((v:ℂ)*line r)) = paperFT f z := by
    unfold paperFT
    apply integral_congr_ae
    filter_upwards [] with v
    change (g v:ℂ) * Complex.exp ((v:ℂ)*line r) = (g v:ℂ) * Complex.exp (Complex.I*z*(v:ℂ))
    have he : Complex.I * z = line r := by
      rw [show Complex.I * z = -(Complex.I*Complex.I)*line r by dsimp [z]; ring, ← pow_two, Complex.I_sq]
      ring
    rw [he, mul_comm (line r) (v:ℂ)]
  rw [hG]
  refine (norm_paperFT_le_div hf hfs (norm_pos_iff.mp hnz)).trans ?_
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+|r|) (line_norm r) 2
  rw [hnorm]
  have he₁ := mul_le_mul_of_nonneg_right hE (by positivity : 0 ≤ ∫ v, ‖deriv (deriv f) v‖)
  have he₂ := mul_le_mul_of_nonneg_right he₁ (by positivity : 0 ≤ (1+|r|)^2)
  have he₃ := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ Real.exp δ*(∫ v, ‖deriv (deriv f) v‖))
  nlinarith only [he₂,he₃]

private theorem laplace_interpolate {A B δ w u : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ) (hw : 0 < w) (hu : 0 ≤ u)
    (h₁ : u ≤ A) (h₂ : u ≤ B*A*δ^(-2:ℝ)/w^2) :
    u ≤ A*B^(1/4:ℝ)*δ^(-1/2:ℝ)*w^(-1/2:ℝ) := by
  calc
    _ = u^(3/4:ℝ)*u^(1/4:ℝ) := by rw [← Real.rpow_add' hu (by norm_num), show (3/4+1/4:ℝ)=1 by norm_num, Real.rpow_one]
    _ ≤ A^(3/4:ℝ)*(B*A*δ^(-2:ℝ)/w^2)^(1/4:ℝ) := by
      gcongr
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hB.le hA.le, ← Real.rpow_mul hδ.le, ← Real.rpow_natCast_mul hw.le]
      simp only [Nat.cast_ofNat, show (-2:ℝ)*(1/4) = -1/2 by norm_num,
        show (2:ℝ)*(1/4) = 1/2 by norm_num]
      rw [div_eq_mul_inv (B^(1/4:ℝ)*A^(1/4:ℝ)*δ^(-1/2:ℝ)) (w^(1/2:ℝ)),
        ← Real.rpow_neg hw.le]
      rw [show -(1/2:ℝ) = -1/2 by ring]
      rw [show A^(3/4:ℝ)*(B^(1/4:ℝ)*A^(1/4:ℝ)*δ^(-1/2:ℝ)*w^(-1/2:ℝ)) =
        A^(3/4:ℝ)*A^(1/4:ℝ)*B^(1/4:ℝ)*δ^(-1/2:ℝ)*w^(-1/2:ℝ) by ring,
        ← Real.rpow_add hA, show (3/4+1/4:ℝ)=1 by norm_num, Real.rpow_one]

private theorem signed_on_line {x y N : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyN : y ≤ N) (r : ℝ) :
    ‖(((y:ℂ)^(line r)-(x:ℂ)^(line r))/line r)‖ ≤ 6*N^(1/2:ℝ)*(1+|r|)^(-1:ℝ) := by
  have hnorm : 0 < ‖line r‖ := by linarith [line_norm r,abs_nonneg r]
  rw [norm_div,Real.rpow_neg_one]
  have hp (v : ℝ) (hv : 1 ≤ v) (hvN : v ≤ N) : ‖(v:ℂ)^(line r)‖ ≤ N^(1/2:ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hv),line_re]
    exact Real.rpow_le_rpow (by linarith) hvN (by norm_num)
  have hsub := (norm_sub_le ((y:ℂ)^(line r)) ((x:ℂ)^(line r))).trans
    (add_le_add (hp y (hx.trans hxy) hyN) (hp x hx (hxy.trans hyN)))
  refine (div_le_div_of_nonneg_right hsub hnorm.le).trans ?_
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ hnorm (by positivity)).mpr
  have hN : 0 ≤ N := by linarith
  have hh := mul_le_mul_of_nonneg_left (line_norm r) (by positivity : 0 ≤ 2*N^(1/2:ℝ))
  nlinarith only [hh]

/-- Uniform (O(N^{2/3})) Γ-integral envelope for δ=N^{-1/3}.
Only the bump-scale second derivative L¹ bound is an input. -/
theorem archimedean_2third_power {C : ℝ} (hC : 0 < C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {g : ℝ → ℝ} {N x y : ℝ}, 1 ≤ x → x ≤ y → y ≤ N →
      let δ := N^(-1/3:ℝ)
      δ < Real.log x → ContDiff ℝ 2 g → (∀ v, 0 ≤ g v) →
      (∀ v ≤ -δ, g v = 0) → (∀ v ≥ δ, g v = 0) →
      (∫ v in (-δ)..δ, g v) = 1 →
      (∫ v, ‖deriv (deriv (fun u : ℝ => (g u : ℂ))) v‖) ≤ C*δ^(-2:ℝ) →
      let k := PintzWeilTestWindow.test g δ (Real.log x) (Real.log y)
      ‖(1/(2*Real.pi):ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r:ℂ)‖ ≤ A*N^(2/3:ℝ) := by
  obtain ⟨D,hD,hbound⟩ := gamma_quarter_bound
  let w (r : ℝ) := (1+|r|)^(-5/4:ℝ)
  let K := 6*Real.exp 1*(9*C)^(1/4:ℝ)*D
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨(2*Real.pi)⁻¹*K*(∫ r : ℝ, w r), by positivity, ?_⟩
  intro g N x y hx hxy hyN
  dsimp only
  let δ := N^(-1/3:ℝ)
  intro hdx hg hn hl hr hm hDg
  let k := PintzWeilTestWindow.test g δ (Real.log x) (Real.log y)
  have hN : 0 < N := zero_lt_one.trans_le ((hx.trans hxy).trans hyN)
  have hp : 0 < δ := Real.rpow_pos_of_pos hN _
  have hδ : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ((hx.trans hxy).trans hyN) (by norm_num)
  have hgs (v : ℝ) (hv : g v ≠ 0) : |v| ≤ δ :=
    abs_le.mpr ⟨(lt_of_not_ge (fun H => hv (hl v H))).le, (lt_of_not_ge (fun H => hv (hr v H))).le⟩
  have hmaj (r : ℝ) : ‖paperFT k r * (EF.gammaBracket r:ℂ)‖ ≤ (K*N^(2/3:ℝ))*w r := by
    have hnline : line r ≠ 0 := by intro h; simpa [h] using line_re r
    have hcont : ContDiff ℝ 1 g := hg.of_le (by norm_num)
    have hγ : gammaOf (line r) = (r:ℂ) := by unfold gammaOf line; ring_nf; field_simp [Complex.I_ne_zero]
    have hE := PintzWeilZetaWindow.evaluated_test (line r) hnline hp.le
      (zero_lt_one.trans_le hx) hxy hdx hcont hl hr hm
    rw [hγ] at hE
    change ‖paperFT k r * (EF.gammaBracket r:ℂ)‖ ≤ _
    rw [hE,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    let u := ‖∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*line r)‖
    have h₁ : u ≤ Real.exp δ := normalized_bump_laplace hp.le hg.continuous hn hl hr hm r
    have h₂ : u ≤ (9*C)*Real.exp δ*δ^(-2:ℝ)/(1+|r|)^2 := by
      refine (decaying_bump_laplace hp.le hg hgs r).trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      change (∫ v, ‖deriv (deriv (fun u : ℝ => (g u : ℂ))) v‖) ≤ C*δ^(-2:ℝ) at hDg
      convert mul_le_mul_of_nonneg_left hDg (by positivity : 0 ≤ 9*Real.exp δ) using 1 <;> ring
    have hu := laplace_interpolate (Real.exp_pos δ) (by positivity : 0 < 9*C) hp
      (by positivity : 0 < 1+|r|) (show 0 ≤ u by positivity) h₁ h₂
    have hb := signed_on_line hx hxy hyN r
    have hpow : δ^(-1/2:ℝ) = N^(1/6:ℝ) := by
      dsimp [δ]; rw [← Real.rpow_mul hN.le]; norm_num
    calc
      _ ≤ (Real.exp δ*(9*C)^(1/4:ℝ)*δ^(-1/2:ℝ)*(1+|r|)^(-1/2:ℝ)) *
           (6*N^(1/2:ℝ)*(1+|r|)^(-1:ℝ)) * (D*(1+|r|)^(1/4:ℝ)) := by
        exact mul_le_mul (mul_le_mul hu hb (by positivity) (by positivity)) (hbound r)
          (by positivity) (by positivity)
      _ ≤ (Real.exp 1*(9*C)^(1/4:ℝ)*δ^(-1/2:ℝ)*(1+|r|)^(-1/2:ℝ)) *
           (6*N^(1/2:ℝ)*(1+|r|)^(-1:ℝ)) * (D*(1+|r|)^(1/4:ℝ)) := by
         gcongr
      _ = _ := by
        dsimp [K,w]
        rw [hpow]
        let z := 1+|r|
        have hz : 0 < z := by dsimp [z]; positivity
        change _ = (6*Real.exp 1*(9*C)^(1/4:ℝ)*D*N^(2/3:ℝ))*z^(-5/4:ℝ)
        calc
          _ = (6*Real.exp 1*(9*C)^(1/4:ℝ)*D)*(N^(1/6:ℝ)*N^(1/2:ℝ)) *
              (z^(-1/2:ℝ)*z^(-1:ℝ)*z^(1/4:ℝ)) := by dsimp [z]; ring
          _ = _ := by rw [← Real.rpow_add hN,← Real.rpow_add hz,← Real.rpow_add hz]; norm_num
  have hi : Integrable w := by
    simpa [w,Real.norm_eq_abs,show (-5/4:ℝ) = -(5/4:ℝ) by norm_num] using
      (integrable_one_add_norm (μ := volume) (E := ℝ) (r := 5/4) (by simp; norm_num))
  have H := norm_integral_le_of_norm_le (hi.const_mul (K*N^(2/3:ℝ)))
    (Eventually.of_forall hmaj)
  rw [integral_const_mul] at H
  change ‖(1/(2*Real.pi):ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r:ℂ)‖ ≤ _
  rw [norm_mul,norm_div,norm_one,show (2*Real.pi:ℂ) = ((2*Real.pi:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi),one_div]
  calc
    _ ≤ (2*Real.pi)⁻¹*((K*N^(2/3:ℝ))*(∫ r : ℝ, w r)) :=
      mul_le_mul_of_nonneg_left H (by positivity)
    _ = _ := by ring

#print axioms archimedean_2third_power
#print axioms gamma_quarter_bound
#print axioms normalized_bump_laplace
#print axioms decaying_bump_laplace
end PintzWeilZetaArchimedean
