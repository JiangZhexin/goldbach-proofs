import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

open Set MeasureTheory intervalIntegral
open scoped Function
namespace PintzSeparatedSampling

theorem point_sample (f df : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (df x) x)
    (hc : Continuous df) (t h : ℝ) (hh : 0 ≤ h) :
    h * f t ≤ (∫ x in t..t+h, f x) + h * (∫ x in t..t+h, |df x|) := by
  have hth : t ≤ t+h := by linarith
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  let D := ∫ x in t..t+h, |df x|
  have hbound (x : ℝ) (hx : x ∈ Icc t (t+h)) : f t ≤ f x + D := by
    have he := integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hc.intervalIntegrable t x)
    have hn := intervalIntegral.norm_integral_le_integral_norm (f := df) (μ := volume) hx.1
    rw [he, Real.norm_eq_abs] at hn
    have hi : (∫ y in t..x, ‖df y‖) ≤ D := by
      rw [show D = (∫ y in t..t+h, |df y|) by rfl,
        intervalIntegral.integral_of_le hx.1, intervalIntegral.integral_of_le hth]
      simp only [Real.norm_eq_abs]
      exact setIntegral_mono_set (hc.abs.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (ae_of_all _ fun y => abs_nonneg _) (ae_of_all _ fun y hy => Ioc_subset_Ioc_right hx.2 hy)
    have ha := (neg_le_abs (f x - f t)).trans (hn.trans hi)
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hth
    (continuous_const.intervalIntegrable t (t+h))
    ((hf.add continuous_const).intervalIntegrable t (t+h)) hbound
  change (∫ _ in t..t+h, f t) ≤ ∫ x in t..t+h, f x + D at hi
  rwa [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul, smul_eq_mul] at hi

/-- Sampling a nonnegative differentiable function at (h)-separated points
uses only its integral and the integral of the absolute derivative. The
interval is enlarged on the right to avoid clipping the last sample window. -/
theorem finset_sample {ι : Type*} (S : Finset ι) (p : ι → ℝ)
    (f df : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (df x) x)
    (hc : Continuous df) (hf₀ : ∀ x, 0 ≤ f x)
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h)
    (hpoints : ∀ i ∈ S, p i ∈ Icc a b)
    (hsep : (↑S : Set ι).Pairwise fun i j => h ≤ |p i - p j|) :
    h * (∑ i ∈ S, f (p i)) ≤
      (∫ x in a..b+h, f x) + h * (∫ x in a..b+h, |df x|) := by
  classical
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have habh : a ≤ b+h := by linarith
  let I (i : ι) := Ioc (p i) (p i+h)
  have hI (i) (hi : i ∈ S) : I i ⊆ Ioc a (b+h) := by
    intro x hx
    have pi := hpoints i hi
    exact ⟨lt_of_le_of_lt pi.1 hx.1, hx.2.trans (by linarith [pi.2])⟩
  have hdis : (↑S : Set ι).Pairwise (Disjoint on I) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hs := hsep hi hj hij
    change h ≤ |p i - p j| at hs
    rw [le_abs] at hs
    rcases hs with hs|hs
    · have hxi₁ := hxi.1
      have hxj₂ := hxj.2
      change p i < x at hxi₁
      change x ≤ p j + h at hxj₂
      linarith
    · have hxj₁ := hxj.1
      have hxi₂ := hxi.2
      change p j < x at hxj₁
      change x ≤ p i + h at hxi₂
      linarith
  have hsum (g : ℝ → ℝ) (hg : Continuous g) (hg₀ : ∀ x, 0 ≤ g x) :
      (∑ i ∈ S, ∫ x in p i..p i+h, g x) ≤ ∫ x in a..b+h, g x := by
    have heq (i : ι) : (∫ x in p i..p i+h, g x) = ∫ x in I i, g x :=
      intervalIntegral.integral_of_le (le_add_of_nonneg_right hh)
    simp_rw [heq, intervalIntegral.integral_of_le habh]
    change (∑ i ∈ S, ∫ x in I i, g x) ≤ ∫ x in Ioc a (b+h), g x
    rw [← integral_biUnion_finset S (fun i _ => measurableSet_Ioc) hdis
      (fun i _ => hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
    refine setIntegral_mono_set (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (ae_of_all _ hg₀) ?_
    exact ae_of_all _ fun x hx => (iUnion₂_subset hI) hx
  calc
    _ = ∑ i ∈ S, h * f (p i) := Finset.mul_sum S _ _
    _ ≤ ∑ i ∈ S, ((∫ x in p i..p i+h, f x) + h*(∫ x in p i..p i+h, |df x|)) :=
      Finset.sum_le_sum fun i _ => point_sample f df hd hc (p i) h hh
    _ = (∑ i ∈ S, ∫ x in p i..p i+h, f x) + h*(∑ i ∈ S, ∫ x in p i..p i+h, |df x|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add (hsum f hf hf₀)
      (mul_le_mul_of_nonneg_left (hsum (fun x => |df x|) hc.abs (fun x => abs_nonneg _)) hh)


/-- A version directly applicable to the energy of a Dirichlet polynomial.
Separation may be taken to be one; no dyadic-density assumption is used in
this analytic step. -/
theorem finset_sample_sq {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Finset ι) (p : ι → ℝ)
    (f df : ℝ → E) (hd : ∀ x, HasDerivAt f (df x) x)
    (hc : Continuous df)
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h)
    (hpoints : ∀ i ∈ S, p i ∈ Icc a b)
    (hsep : (↑S : Set ι).Pairwise fun i j => h ≤ |p i - p j|) :
    h * (∑ i ∈ S, ‖f (p i)‖ ^ 2) ≤
      (∫ x in a..b+h, ‖f x‖ ^ 2) +
        (2*h) * (∫ x in a..b+h, ‖f x‖ * ‖df x‖) := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  let D (x : ℝ) := 2 * inner ℝ (f x) (df x)
  have hD : Continuous D := continuous_const.mul (hf.inner hc)
  have hFd (x : ℝ) : HasDerivAt (fun x => ‖f x‖ ^ 2) (D x) x := (hd x).norm_sq
  have h₁ := finset_sample S p _ D hFd hD (fun x => sq_nonneg _) hab hh hpoints hsep
  have h₂ : (∫ x in a..b+h, |D x|) ≤ ∫ x in a..b+h, 2 * (‖f x‖ * ‖df x‖) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact hD.abs.intervalIntegrable _ _
    · exact (continuous_const.mul (hf.norm.mul hc.norm)).intervalIntegrable _ _
    · intro x _
      rw [show |D x| = 2 * |inner ℝ (f x) (df x)| by simp [D, abs_mul]]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
  rw [intervalIntegral.integral_const_mul] at h₂
  refine h₁.trans (add_le_add le_rfl ?_)
  rw [mul_comm (2 : ℝ) h, mul_assoc]
  exact mul_le_mul_of_nonneg_left h₂ hh

/-- The real parts of the zero samples need not be equal. Compare each
sample with the left face, then integrate the absolute real-part derivatives.
This form can consume fixed-line sampling estimates subsequently. -/
theorem varying_real_part {ι : Type*} (S : Finset ι)
    (f df : ι → ℝ → ℝ) (p : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hpel : ∀ i ∈ S, p i ∈ Icc a b)
    (hd : ∀ i ∈ S, ∀ x, HasDerivAt (f i) (df i x) x)
    (hc : ∀ i ∈ S, Continuous (df i)) :
    ∑ i ∈ S, f i (p i) ≤ (∑ i ∈ S, f i a) +
      (∫ x in a..b, ∑ i ∈ S, |df i x|) := by
  have hsingle (i) (hi : i ∈ S) :
      f i (p i) ≤ f i a + ∫ x in a..b, |df i x| := by
    have hp := hpel i hi
    have he := integral_eq_sub_of_hasDerivAt (fun x _ => hd i hi x)
      ((hc i hi).intervalIntegrable a (p i))
    have hn := intervalIntegral.norm_integral_le_integral_norm (f := df i)
      (μ := volume) hp.1
    rw [he, Real.norm_eq_abs] at hn
    simp only [Real.norm_eq_abs] at hn
    have hmono : (∫ x in a..p i, |df i x|) ≤ ∫ x in a..b, |df i x| := by
      rw [intervalIntegral.integral_of_le hp.1, intervalIntegral.integral_of_le hab]
      exact setIntegral_mono_set ((hc i hi).abs.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (ae_of_all _ fun y => abs_nonneg _) (ae_of_all _ fun y hy => Ioc_subset_Ioc_right hp.2 hy)
    have hv := (le_abs_self (f i (p i) - f i a)).trans (hn.trans hmono)
    linarith
  calc
    _ ≤ ∑ i ∈ S, (f i a + (∫ x in a..b, |df i x|)) := Finset.sum_le_sum hsingle
    _ = _ := by
      rw [Finset.sum_add_distrib, intervalIntegral.integral_finsetSum]
      exact fun i hi => (hc i hi).abs.intervalIntegrable _ _

#print axioms point_sample
#print axioms finset_sample
#print axioms finset_sample_sq
#print axioms varying_real_part
end PintzSeparatedSampling
