import PintzWeilSmoothing
import PintzWeilTestWindow
import Zeta23.WeilEF.Main

open MeasureTheory Set Filter
open scoped Topology

namespace PintzWeilZetaWindow
open PintzWeilTestWindow

/-- The actual canonical ζ explicit formula applied to the admissible
logarithmic bump. This identity is not yet a truncated estimate. -/
theorem zeta_window_identity {g : ℝ → ℝ} {δ a b : ℝ}
    (hδ : 0 ≤ δ) (ha : δ < a) (hab : a ≤ b)
    (hg : ContDiff ℝ 1 g) (hl : ∀ v ≤ -δ, g v = 0) (hr : ∀ v ≥ δ, g v = 0)
    (hm : (∫ v in (-δ)..δ, g v) = 1) :
    let k := test g δ a b
    let Z := Zeta23.zetaZeroConfig
    (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)) =
      Zeta23.paperFT k (Complex.I/2) + Zeta23.paperFT k (-Complex.I/2) -
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          (diff g δ a b (Real.log n):ℂ)) +
        (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r:ℂ) := by
  dsimp only
  obtain ⟨hc,hcs,hn⟩ := admissible hδ ha hab hg hl hr hm
  have H := (Zeta23.WeilEF.EF_lit_zetaZeroConfig _ hc hcs).2
  unfold Zeta23.EF.literatureRHS at H
  simp_rw [prime_weight hn] at H
  exact H

/-- Evaluate the transform of the actual admissible test. This packages
the support and regularity inputs to the common multiplier identity. -/
theorem evaluated_test {g : ℝ → ℝ} {δ x y : ℝ} (s : ℂ) (hs : s ≠ 0)
    (hδ : 0 ≤ δ) (hx : 0 < x) (hxy : x ≤ y) (ha : δ < Real.log x)
    (hg : ContDiff ℝ 1 g) (hl : ∀ v ≤ -δ, g v = 0) (hr : ∀ v ≥ δ, g v = 0)
    (hm : (∫ v in (-δ)..δ, g v) = 1) :
    Zeta23.paperFT (test g δ (Real.log x) (Real.log y)) (Zeta23.gammaOf s) =
      (∫ v : ℝ, (g v:ℂ) * Complex.exp ((v:ℂ)*s))*(((y:ℂ)^s-(x:ℂ)^s)/s) := by
  let a := Real.log x
  let b := Real.log y
  let u : ℝ → ℂ := fun t => (diff g δ a b t:ℂ)
  let G : ℝ → ℂ := fun t => (g t:ℂ)
  let v : ℝ → ℂ := fun t => Complex.exp ((t:ℂ)*s)
  have hy : 0 < y := hx.trans_le hxy
  have hab : a ≤ b := Real.log_le_log hx hxy
  have hu (t : ℝ) : HasDerivAt u (G (t-a) - G (t-b)) t := by
    have hd (k : ℝ) : HasDerivAt (fun w => cdf g δ (w-k)) (g (t-k)) t := by
      have H := (cdf_hasDerivAt hg.continuous δ (t-k)).comp t ((hasDerivAt_id t).sub_const k)
      simpa only [Function.comp_def,id_eq,mul_one] using H
    simpa [u,G,diff] using ((hd a).sub (hd b)).ofReal_comp
  have htc := (admissible hδ ha hab hg hl hr hm).2.1
  have huc : HasCompactSupport u := by
    have hEq : (fun t : ℝ => Complex.exp (-((t:ℂ)/2))) * test g δ a b = u := by
      funext t
      change Complex.exp (-((t:ℂ)/2)) * (Complex.exp ((t:ℂ)/2) * u t) = u t
      rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
    rw [← hEq]
    exact htc.mul_left
  have uDiff : Differentiable ℝ u := fun t => (hu t).differentiableAt
  have ucont : Continuous u := uDiff.continuous
  have vcont : Continuous v := Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hgshift (c : ℝ) : HasCompactSupport (fun t => G (t-c)) := by
    refine (isCompact_Icc (a := c-δ) (b := c+δ)).of_isClosed_subset isClosed_closure
      (closure_minimal ?_ isClosed_Icc)
    intro t ht
    by_contra H
    have Ht : t-c ≤ -δ ∨ δ ≤ t-c := by
      simp only [mem_Icc,not_and] at H
      by_cases ht' : c-δ ≤ t
      · right; linarith [lt_of_not_ge (H ht')]
      · left; linarith [lt_of_not_ge ht']
    apply (Function.mem_support.mp ht)
    rcases Ht with h|h
    · simp [G, hl _ h]
    · simp [G, hr _ h]
  have hgcont : Continuous G := Complex.continuous_ofReal.comp hg.continuous
  have hint (c : ℝ) : Integrable (fun t => G (t-c)*v t) :=
    ((hgcont.comp (continuous_id.sub continuous_const)).mul vcont).integrable_of_hasCompactSupport
      (hgshift c).mul_right
  have bot : Tendsto (fun t => u t*v t) atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_le_atBot (a-δ)] with t ht
    have h0 : u t = 0 := by
      unfold u diff
      rw [cdf_left hl (show t-a ≤ -δ by linarith), cdf_left hl (show t-b ≤ -δ by linarith)]
      simp
    rw [h0,zero_mul]
  have top : Tendsto (fun t => u t*v t) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (b+δ)] with t ht
    have h0 : u t = 0 := by
      unfold u diff
      rw [cdf_right hδ hg.continuous hr hm (show δ ≤ t-a by linarith),
        cdf_right hδ hg.continuous hr hm (show δ ≤ t-b by linarith)]
      simp
    rw [h0,zero_mul]
  have hI : Integrable (fun t => u t * (v t * s)) :=
    (ucont.mul (vcont.mul continuous_const)).integrable_of_hasCompactSupport huc.mul_right
  have hD : Integrable (fun t => (G (t-a)-G (t-b))*v t) := by
    simpa only [sub_mul, Pi.sub_def] using (hint a).sub (hint b)
  have hM := PintzWeilSmoothing.cdf_difference_moment u G s hs a b hu hI hD
    (hint a) (hint b) bot top
  exact PintzWeilSmoothing.weil_window_cpow u G s hx hy hM

/-- The canonical ζ smooth window formula with every zero term
expressed as the signed short-interval kernel. The absolutely convergent
zero sum is not yet truncated, and the Γ term is still explicit. -/
theorem zeta_signed_kernel_identity {g : ℝ → ℝ} {δ x y : ℝ}
    (hδ : 0 ≤ δ) (hx : 0 < x) (hxy : x ≤ y) (ha : δ < Real.log x)
    (hg : ContDiff ℝ 1 g) (hl : ∀ v ≤ -δ, g v = 0) (hr : ∀ v ≥ δ, g v = 0)
    (hm : (∫ v in (-δ)..δ, g v) = 1) :
    let Z := Zeta23.zetaZeroConfig
    let k := test g δ (Real.log x) (Real.log y)
    let G := fun s : ℂ => ∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*s)
    (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * (G ρ * (((y:ℂ)^(ρ:ℂ)-(x:ℂ)^(ρ:ℂ))/(ρ:ℂ)))) =
      Zeta23.paperFT k (Complex.I/2) + Zeta23.paperFT k (-Complex.I/2) -
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          (diff g δ (Real.log x) (Real.log y) (Real.log n):ℂ)) +
        (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r:ℂ) := by
  dsimp only
  have H := zeta_window_identity hδ ha (Real.log_le_log hx hxy) hg hl hr hm
  dsimp only at H
  have he (ρ : Zeta23.zetaZeroConfig.carrier) :
      Zeta23.paperFT (test g δ (Real.log x) (Real.log y)) (Zeta23.gammaOf ρ) =
      (∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*(ρ:ℂ))) *
        (((y:ℂ)^(ρ:ℂ)-(x:ℂ)^(ρ:ℂ))/(ρ:ℂ)) := by
    have hz : Zeta23.IsNontrivialZero (ρ:ℂ) := ρ.property
    exact evaluated_test _ (Complex.ne_zero_of_re_pos hz.2.1) hδ hx hxy ha hg hl hr hm
  simpa only [he] using H

#print axioms zeta_signed_kernel_identity
#print axioms evaluated_test
#print axioms zeta_window_identity
end PintzWeilZetaWindow
