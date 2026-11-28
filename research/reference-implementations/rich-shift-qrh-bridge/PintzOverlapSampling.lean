import PintzSeparatedSampling
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open Set MeasureTheory intervalIntegral Finset
namespace PintzOverlapSampling

/-- Finite overlap gives a *linear* multiplicity loss when summing integrals
of a nonnegative function. -/
theorem sum_local_integrals {ι : Type*} (S : Finset ι) (p : ι → ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) (hg₀ : ∀ x, 0 ≤ g x)
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) (B : ℕ)
    (hpoints : ∀ i ∈ S, p i ∈ Set.Icc a b)
    (hover : ∀ x, (S.filter (fun i => p i < x ∧ x ≤ p i+h)).card ≤ B) :
    (∑ i ∈ S, ∫ x in p i..p i+h, g x) ≤
      (B:ℝ) * ∫ x in a..b+h, g x := by
  classical
  let J (i : ι) := Set.Ioc (p i) (p i+h)
  let K := Set.Ioc a (b+h)
  have hK : a ≤ b+h := by linarith
  have hJK (i) (hi : i ∈ S) : J i ⊆ K := by
    intro x hx
    have H := hpoints i hi
    exact ⟨H.1.trans_lt hx.1, hx.2.trans (by linarith only [H.2])⟩
  have igJ (i : ι) : Integrable ((J i).indicator g) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have igK : Integrable (K.indicator g) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hpoint (x : ℝ) : (∑ i ∈ S, (J i).indicator g x) ≤ (B:ℝ) * K.indicator g x := by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      have he : (∑ i ∈ S, (J i).indicator g x) =
          ((S.filter (fun i => p i < x ∧ x ≤ p i+h)).card:ℝ) * g x := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : x ∈ J i
        · have hip : p i < x ∧ x ≤ p i+h := hi
          simp [indicator_of_mem hi, hip]
        · have hip : ¬ (p i < x ∧ x ≤ p i+h) := hi
          simp [indicator_of_notMem hi, hip]
      rw [he]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hover x) (hg₀ x)
    · rw [indicator_of_notMem hx, mul_zero]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro i hi
      exact indicator_of_notMem (fun hj => hx (hJK i hi hj)) _
  have hi := MeasureTheory.integral_mono (integrable_finsetSum S (fun i _ => igJ i))
    (igK.const_mul (B:ℝ)) hpoint
  rw [integral_finsetSum S (fun i _ => igJ i), MeasureTheory.integral_const_mul] at hi
  have hEq (i : ι) :
      (∫ x in p i..p i+h, g x) = ∫ x, (J i).indicator g x := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioc, integral_of_le (le_add_of_nonneg_right hh)]
  simp_rw [← hEq] at hi
  rw [show (∫ x, K.indicator g x) = ∫ x in a..b+h, g x by
    rw [MeasureTheory.integral_indicator measurableSet_Ioc, integral_of_le hK]] at hi
  exact hi

/-- Sample bound for arbitrarily repeated/nearby sample points, controlled
by a bound on the number of unit windows covering each point. -/
theorem finset_sample_overlap {ι : Type*} (S : Finset ι) (p : ι → ℝ)
    (f df : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (df x) x)
    (hc : Continuous df) (hf₀ : ∀ x, 0 ≤ f x)
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) (B : ℕ)
    (hpoints : ∀ i ∈ S, p i ∈ Set.Icc a b)
    (hover : ∀ x, (S.filter (fun i => p i < x ∧ x ≤ p i+h)).card ≤ B) :
    h * (∑ i ∈ S, f (p i)) ≤
      (B:ℝ) * ((∫ x in a..b+h, f x) + h * (∫ x in a..b+h, |df x|)) := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have h1 := sum_local_integrals S p f hf hf₀ hab hh B hpoints hover
  have h2 := sum_local_integrals S p (fun x => |df x|) hc.abs (fun x => abs_nonneg _) hab hh B hpoints hover
  calc
    _ = ∑ i ∈ S, h * f (p i) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ S, ((∫ x in p i..p i+h, f x) + h*(∫ x in p i..p i+h, |df x|)) :=
      Finset.sum_le_sum fun i _ => PintzSeparatedSampling.point_sample f df hd hc (p i) h hh
    _ = (∑ i ∈ S, ∫ x in p i..p i+h, f x) + h*(∑ i ∈ S, ∫ x in p i..p i+h, |df x|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
      rw [mul_add,mul_left_comm (B:ℝ) h]
      exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hh)


/-- The width-one local zero count controls overlap of the right-facing
unit windows, even if different zero records have identical ordinates. -/
theorem width_one_overlap {ι : Type*} (S : Finset ι) (p : ι → ℝ) (B : ℕ)
    (hLocal : ∀ c : ℝ, (S.filter (fun i => |p i - c| ≤ 1/2)).card ≤ B) :
    ∀ x : ℝ, (S.filter (fun i => p i < x ∧ x ≤ p i+1)).card ≤ B := by
  intro x
  refine (Finset.card_le_card ?_).trans (hLocal (x-1/2))
  intro i hi
  obtain ⟨hS,hL,hR⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hS, abs_le.mpr ⟨by linarith,by linarith⟩⟩

/-- Squared-energy bound with linear overlap, valid also on complex-valued
polynomials with their real inner product. -/
theorem finset_sample_sq_overlap {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Finset ι) (p : ι → ℝ)
    (f df : ℝ → E) (hd : ∀ x, HasDerivAt f (df x) x)
    (hc : Continuous df)
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) (B : ℕ)
    (hpoints : ∀ i ∈ S, p i ∈ Set.Icc a b)
    (hover : ∀ x, (S.filter (fun i => p i < x ∧ x ≤ p i+h)).card ≤ B) :
    h * (∑ i ∈ S, ‖f (p i)‖ ^ 2) ≤
      (B:ℝ) * ((∫ x in a..b+h, ‖f x‖ ^ 2) +
        (2*h) * (∫ x in a..b+h, ‖f x‖ * ‖df x‖)) := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  let D (x : ℝ) := 2 * inner ℝ (f x) (df x)
  have hD : Continuous D := continuous_const.mul (hf.inner hc)
  have hFd (x : ℝ) : HasDerivAt (fun x => ‖f x‖ ^ 2) (D x) x := (hd x).norm_sq
  have h₁ := finset_sample_overlap S p _ D hFd hD (fun x => sq_nonneg _) hab hh B hpoints hover
  have h₂ : (∫ x in a..b+h, |D x|) ≤ ∫ x in a..b+h, 2 * (‖f x‖ * ‖df x‖) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact hD.abs.intervalIntegrable _ _
    · exact (continuous_const.mul (hf.norm.mul hc.norm)).intervalIntegrable _ _
    · intro x _
      rw [show |D x| = 2 * |inner ℝ (f x) (df x)| by simp [D, abs_mul]]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
  rw [intervalIntegral.integral_const_mul] at h₂
  refine h₁.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Nat.cast_nonneg B))
  rw [mul_comm (2 : ℝ) h, mul_assoc]
  exact mul_le_mul_of_nonneg_left h₂ hh


/-- Expand a weighted finite zero set into records with distinct labels. -/
def records {ι : Type*} (S : Finset ι) (w : ι → ℕ) :
    Finset (Σ _ : ι, ℕ) :=
  S.sigma (fun i => Finset.range (w i))

theorem count_records {ι : Type*} (S : Finset ι) (w : ι → ℕ)
    (P : ι → Prop) [DecidablePred P] :
    ((records S w).filter (fun r => P r.1)).card = ∑ i ∈ S.filter P, w i := by
  have he : (records S w).filter (fun r => P r.1) = records (S.filter P) w := by
    ext r
    simp only [records, Finset.mem_filter, Finset.mem_sigma]
    tauto
  rw [he, records, Finset.card_sigma]
  exact Finset.sum_congr rfl (fun i _ => Finset.card_range (w i))

theorem overlap_records_of_width_one {ι : Type*} (S : Finset ι) (w : ι → ℕ)
    (p : ι → ℝ) (B : ℕ)
    (hLocal : ∀ c : ℝ, (∑ i ∈ S.filter (fun i => |p i - c| ≤ 1/2), w i) ≤ B) :
    ∀ x : ℝ, ((records S w).filter (fun r => p r.1 < x ∧ x ≤ p r.1+1)).card ≤ B := by
  apply width_one_overlap (records S w) (fun r => p r.1) B
  intro c
  rw [count_records S w (fun i => |p i - c| ≤ 1/2)]
  exact hLocal c

/-- Summing a statistic on occurrence records is exactly the weighted
sum on the underlying distinct roots. -/
theorem sum_records {ι : Type*} (S : Finset ι) (w : ι → ℕ) (f : ι → ℝ) :
    (∑ r ∈ records S w, f r.1) = ∑ i ∈ S, (w i:ℝ) * f i := by
  rw [records, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

#print axioms sum_local_integrals
#print axioms finset_sample_overlap
#print axioms width_one_overlap
#print axioms finset_sample_sq_overlap
#print axioms overlap_records_of_width_one
#print axioms sum_records
end PintzOverlapSampling
