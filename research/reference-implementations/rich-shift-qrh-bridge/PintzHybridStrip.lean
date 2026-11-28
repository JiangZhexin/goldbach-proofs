import PintzHybridDiscrete
import Mathlib.Tactic.GCongr

open Finset MeasureTheory Set intervalIntegral
open scoped BigOperators
namespace PintzHybridStrip
open PintzSieveToHybrid PintzHybridDiscrete

noncomputable def reScale (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℂ :=
  a n * Complex.exp (-(σ:ℂ) * Real.log (n:ℝ))

noncomputable def reCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * -((Real.log (n:ℝ)):ℂ)

theorem hasDeriv_reScale_P (s : Finset ℕ) (a : ℕ → ℂ)
    (j : Σ k : ℕ, DirichletCharacter ℂ (k+1)) (t σ : ℝ) :
    HasDerivAt (fun x : ℝ => P s (reScale a x) j t)
      (P s (reScale (reCoeff a) σ) j t) σ := by
  have hd (n : ℕ) :
      HasDerivAt (fun x : ℝ => Complex.exp (-(x:ℂ) * Real.log (n:ℝ)))
        (Complex.exp (-(σ:ℂ) * Real.log (n:ℝ)) * -((Real.log (n:ℝ)):ℂ)) σ := by
    have H := ((Complex.ofRealCLM.hasDerivAt (x := σ)).neg).mul_const
      ((Real.log (n:ℝ)):ℂ)
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, Pi.neg_apply, neg_mul, one_mul] using H.cexp
  unfold P
  apply HasDerivAt.fun_sum
  intro n hn
  convert ((hd n).const_mul (j.2 (n : ZMod (j.1+1)) * a n)).mul_const
    (Complex.exp (((t:ℂ) * Complex.I) * Real.log (n:ℝ))) using 1
  · ext x; unfold reScale; ring
  · unfold reScale reCoeff; ring

theorem norm_reScale_mono (a : ℕ → ℂ) {c σ : ℝ} (hσ : c ≤ σ)
    {n : ℕ} (hn : 0 < n) : ‖reScale a σ n‖ ≤ ‖reScale a c n‖ := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hl := Real.log_nonneg hn'
  unfold reScale
  simp only [norm_mul, Complex.norm_exp, neg_mul, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (norm_nonneg _)

/-- The discrete hybrid sieve for unit-separated ordinates and sample-dependent
real parts in [c,d]. Only coefficients damped at c appear in the upper bound;
one additional logarithmic weight comes from taking a real-part derivative. -/
theorem strip_energy {Q : ℕ} (hQ : 1 ≤ Q) (s : Finset ℕ) (a : ℕ → ℂ)
    {U T : ℝ} (hT : 0 ≤ T) (hs : ∀ n ∈ s, 0 < n ∧ (n:ℝ) ≤ 2*U)
    {ι : Type*} (A : (Σ k : ℕ, DirichletCharacter ℂ (k+1)) → Finset ι)
    (t β : (Σ k : ℕ, DirichletCharacter ℂ (k+1)) → ι → ℝ)
    (hpt : ∀ j ∈ family Q, ∀ i ∈ A j, t j i ∈ Icc (-T) T)
    (hsep : ∀ j ∈ family Q, (↑(A j) : Set ι).Pairwise fun i k => 1 ≤ |t j i - t j k|)
    {c d : ℝ} (hcd : c ≤ d) (hβ : ∀ j ∈ family Q, ∀ i ∈ A j, β j i ∈ Icc c d) :
    let M := (Real.pi ^ 2 * (T+1) / 2) * ((⌊U * (2*Real.pi/(T+1))⌋₊:ℝ)+1+2*(Q:ℝ)^2)
    let E := fun b : ℕ → ℂ => M *
      (2 * (∑ n ∈ s, ‖reScale b c n‖ ^ 2) + ∑ n ∈ s, ‖logCoeff (reScale b c) n‖ ^ 2)
    (∑ j ∈ family Q, ∑ i ∈ A j, ‖P s (reScale a (β j i)) j (t j i)‖^2) ≤
      E a + (d-c)*(E a + E (reCoeff a)) := by
  classical
  let M := (Real.pi ^ 2 * (T+1) / 2) * ((⌊U * (2*Real.pi/(T+1))⌋₊:ℝ)+1+2*(Q:ℝ)^2)
  let E := fun b : ℕ → ℂ => M *
    (2 * (∑ n ∈ s, ‖reScale b c n‖ ^ 2) + ∑ n ∈ s, ‖logCoeff (reScale b c) n‖ ^ 2)
  change _ ≤ E a + (d-c)*(E a + E (reCoeff a))
  let K := (family Q).sigma A
  let V := Σ j : (Σ k : ℕ, DirichletCharacter ℂ (k+1)), (fun _ => ι) j
  let F (p : V) (x : ℝ) := ‖P s (reScale a x) p.1 (t p.1 p.2)‖^2
  let G (p : V) (x : ℝ) := 2 * inner ℝ
    (P s (reScale a x) p.1 (t p.1 p.2)) (P s (reScale (reCoeff a) x) p.1 (t p.1 p.2))
  have hd (p : V) (hp : p ∈ K) (x : ℝ) : HasDerivAt (F p) (G p x) x :=
    (hasDeriv_reScale_P s a p.1 (t p.1 p.2) x).norm_sq
  have hc (p : V) (hp : p ∈ K) : Continuous (G p) := by
    have h1 : Continuous (fun x => P s (reScale a x) p.1 (t p.1 p.2)) :=
      continuous_iff_continuousAt.mpr
        (fun x => (hasDeriv_reScale_P s a p.1 (t p.1 p.2) x).continuousAt)
    have h2 : Continuous (fun x => P s (reScale (reCoeff a) x) p.1 (t p.1 p.2)) :=
      continuous_iff_continuousAt.mpr
        (fun x => (hasDeriv_reScale_P s (reCoeff a) p.1 (t p.1 p.2) x).continuousAt)
    have hh := Complex.continuous_re.comp (h1.inner (𝕜 := ℂ) h2)
    exact continuous_const.mul hh
  have hb (p : V) (hp : p ∈ K) : β p.1 p.2 ∈ Icc c d := by
    have hh := Finset.mem_sigma.mp hp
    exact hβ _ hh.1 _ hh.2
  have hsample := PintzSeparatedSampling.varying_real_part K F G
    (fun p => β p.1 p.2) hcd hb hd hc
  have hfixed (b : ℕ → ℂ) (σ : ℝ) (hσ : c ≤ σ) :
      (∑ j ∈ family Q, ∑ i ∈ A j, ‖P s (reScale b σ) j (t j i)‖^2) ≤ E b := by
    refine (sampled_energy hQ s (reScale b σ) hT hs A t hpt hsep).trans ?_
    have hM : 0 ≤ M := by dsimp [M]; positivity
    apply mul_le_mul_of_nonneg_left _ hM
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (sum_le_sum fun n hn =>
        pow_le_pow_left₀ (norm_nonneg _) (norm_reScale_mono b hσ (hs n hn).1) _) (by norm_num)
    · apply sum_le_sum
      intro n hn
      apply pow_le_pow_left₀ (norm_nonneg _)
      simp only [logCoeff, norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_reScale_mono b hσ (hs n hn).1) (by positivity)
  have hF : (∑ p ∈ K, F p c) ≤ E a := by
    simp only [K, F, Finset.sum_sigma]
    exact hfixed a c le_rfl
  have hpoint (x : ℝ) (hx : x ∈ Icc c d) :
      (∑ p ∈ K, |G p x|) ≤ E a + E (reCoeff a) := by
    have hterm (p : V) (hp : p ∈ K) :
        |G p x| ≤ ‖P s (reScale a x) p.1 (t p.1 p.2)‖^2 +
          ‖P s (reScale (reCoeff a) x) p.1 (t p.1 p.2)‖^2 := by
      simp only [G, abs_mul, Nat.abs_ofNat]
      refine (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num : (0:ℝ)≤2)).trans ?_
      nlinarith [sq_nonneg (‖P s (reScale a x) p.1 (t p.1 p.2)‖ -
        ‖P s (reScale (reCoeff a) x) p.1 (t p.1 p.2)‖)]
    refine (sum_le_sum hterm).trans ?_
    rw [sum_add_distrib]
    dsimp only [K]
    rw [Finset.sum_sigma, Finset.sum_sigma]
    exact add_le_add (hfixed a x hx.1) (hfixed (reCoeff a) x hx.1)
  have hi : (∫ x in c..d, ∑ p ∈ K, |G p x|) ≤ (d-c)*(E a + E (reCoeff a)) := by
    have hcont : Continuous (fun x : ℝ => ∑ p ∈ K, |G p x|) :=
      continuous_finsetSum K (fun p hp => (hc p hp).abs)
    have hh := intervalIntegral.integral_mono_on (μ := volume) hcd
      (hcont.intervalIntegrable c d)
      (continuous_const.intervalIntegrable c d) hpoint
    rwa [intervalIntegral.integral_const, smul_eq_mul] at hh
  have hlast := hsample.trans (add_le_add hF hi)
  simpa only [K, F, Finset.sum_sigma] using hlast

#print axioms strip_energy
end PintzHybridStrip
