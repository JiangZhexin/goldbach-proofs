import PintzGallagherReal
import PintzLogWindow
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped BigOperators
namespace PintzHybridGallagher

/-- A coefficient is present in a translated logarithmic window precisely
for an interval of window origins of length h. -/
theorem overlap_integral {ι : Type*} (s : Finset ι) (freq w : ι → ℝ)
    {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun x => ∑ n ∈ s.filter (fun n => x < freq n ∧ freq n ≤ x+h), w n) ∧
    (∫ x : ℝ, ∑ n ∈ s.filter (fun n => x < freq n ∧ freq n ≤ x+h), w n)
      = h * ∑ n ∈ s, w n := by
  classical
  let g (n : ι) := (Ico (freq n - h) (freq n)).indicator (fun _ : ℝ => w n)
  have he (x : ℝ) :
      (∑ n ∈ s.filter (fun n => x < freq n ∧ freq n ≤ x+h), w n) = ∑ n ∈ s, g n x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hx : (x < freq n ∧ freq n ≤ x+h) ↔ x ∈ Ico (freq n - h) (freq n) := by
      rw [mem_Ico, sub_le_iff_le_add]
      tauto
    simp [g, hx, Set.indicator_apply]
  have hg (n : ι) : Integrable (g n) := by
    exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (by
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top))
  simp_rw [he]
  refine ⟨integrable_finsetSum _ (fun n _ => hg n), ?_⟩
  rw [integral_finsetSum _ (fun n _ => hg n), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [g]
  rw [integral_indicator_const _ measurableSet_Ico,
    Real.volume_real_Ico_of_le (by linarith : freq n - h ≤ freq n), smul_eq_mul]
  ring

/-- Compose the real-frequency Gallagher estimate with a pointwise finite
large sieve valid on the (moving) finite support and integrate the support
energy exactly. The input constant C is any uniform sieve constant. -/
theorem hybrid_of_pointwise {ι κ : Type*} (s : Finset ι) (J : Finset κ)
    (freq : ι → ℝ) (a : ι → ℂ) (χ : κ → ι → ℂ)
    {D C : ℝ} (hD : 0 < D)
    (hsieve : ∀ x : ℝ,
      (∑ j ∈ J, ‖∑ n ∈ s.filter (fun n => x < freq n ∧ freq n ≤ x + D/2), χ j n * a n‖ ^ 2)
        ≤ C * (∑ n ∈ s.filter (fun n => x < freq n ∧ freq n ≤ x + D/2), ‖a n‖ ^ 2)) :
    (∑ j ∈ J, ∫ t in (-1/D)..(1/D), ‖∑ n ∈ s, (χ j n * a n) *
        Complex.exp ((2 * Real.pi * t * Complex.I) * (freq n))‖ ^ 2) ≤
      (Real.pi ^ 2 / (2*D)) * C * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  classical
  let W (j : κ) (x : ℝ) : ℝ :=
    ‖∑ n ∈ s.filter (fun n => x < freq n ∧ freq n ≤ x + D/2), χ j n * a n‖ ^ 2
  have hW (j : κ) : Integrable (W j) := by
    let F := PintzGallagherReal.window s freq (fun n => χ j n * a n) (D/2)
    have hf : MemLp F 2 := PintzGallagherReal.window_memLp _ _ _ _ _
    have hfi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
    simpa only [W, F, PintzGallagherReal.window_eq_sum_filter] using hfi
  obtain ⟨heI, he⟩ := overlap_integral s freq (fun n => ‖a n‖ ^ 2) (by positivity : 0 ≤ D/2)
  have hi := integral_mono (integrable_finsetSum J (fun j _ => hW j)) (heI.const_mul C) hsieve
  rw [integral_const_mul, he] at hi
  calc
    _ ≤ ∑ j ∈ J, (Real.pi^2/D^2) * ∫ x : ℝ, W j x :=
      Finset.sum_le_sum (fun j _ => PintzGallagherReal.pintz_window s freq (fun n => χ j n*a n) hD)
    _ = (Real.pi^2/D^2) * ∫ x : ℝ, ∑ j ∈ J, W j x := by
      rw [integral_finsetSum _ (fun j _ => hW j), Finset.mul_sum]
    _ ≤ (Real.pi^2/D^2) * (C * ((D/2) * ∑ n ∈ s, ‖a n‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by field_simp


/-- Localizing logarithms of positive integers n ≤ 2U to a window of
length D/2 confines all selected n to an integer interval of length
at most floor(U D), using the first selected integer as the left end. -/
theorem log_support_interval (s : Finset ℕ) {U D : ℝ}
    (hs : ∀ n ∈ s, 0 < n ∧ (n:ℝ) ≤ 2*U) (x : ℝ) :
    ∃ m : ℕ, s.filter (fun n : ℕ => x < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ x+D/2) ⊆
      Finset.Icc m (m+⌊U*D⌋₊) := by
  classical
  let V := s.filter (fun n : ℕ => x < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ x+D/2)
  change ∃ m, V ⊆ _
  by_cases hVe : V.Nonempty
  · let m := V.min' hVe
    have hm := Finset.mem_filter.mp (V.min'_mem hVe)
    use m
    intro n hn
    have hmn := V.min'_le n hn
    have hv := Finset.mem_filter.mp hn
    have hdiam := PintzLogWindow.diameter
      (show (0:ℝ) < m by exact_mod_cast (hs m hm.1).1)
      (show (m:ℝ) ≤ n by exact_mod_cast hmn)
      (hs n hv.1).2 hm.2.1 hv.2.2
    have hdiam' : ((n-m : ℕ) : ℝ) ≤ U*D := by
      rw [Nat.cast_sub hmn]
      linarith
    have hfloor := Nat.le_floor hdiam'
    have hright : n ≤ m + ⌊U*D⌋₊ := by omega
    exact Finset.mem_Icc.mpr ⟨hmn,hright⟩
  · exact ⟨0, (Finset.not_nonempty_iff_eq_empty.mp hVe).symm ▸ Finset.empty_subset _⟩

/-- On a dyadic polynomial of scale U, only a uniform arithmetic sieve
for subsets of integer intervals of length floor(U D) is needed. -/
theorem hybrid_log_of_integer_sieve {κ : Type*} (s : Finset ℕ) (J : Finset κ)
    (a : ℕ → ℂ) (χ : κ → ℕ → ℂ)
    {U D C : ℝ} (hD : 0 < D)
    (hs : ∀ n ∈ s, 0 < n ∧ (n:ℝ) ≤ 2*U)
    (hsieve : ∀ (m : ℕ) (v : Finset ℕ), v ⊆ Finset.Icc m (m+⌊U*D⌋₊) →
      (∑ j ∈ J, ‖∑ n ∈ v, χ j n * a n‖ ^ 2) ≤ C * (∑ n ∈ v, ‖a n‖ ^ 2)) :
    (∑ j ∈ J, ∫ t in (-1/D)..(1/D), ‖∑ n ∈ s, (χ j n * a n) *
        Complex.exp ((2 * Real.pi * t * Complex.I) * Real.log (n:ℝ))‖ ^ 2) ≤
      (Real.pi ^ 2 / (2*D)) * C * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  refine hybrid_of_pointwise s J (fun n => Real.log (n:ℝ)) a χ hD ?_
  intro x
  obtain ⟨m, hm⟩ := log_support_interval (D := D) s hs x
  exact hsieve m _ hm

#print axioms overlap_integral
#print axioms hybrid_of_pointwise
#print axioms log_support_interval
#print axioms hybrid_log_of_integer_sieve
end PintzHybridGallagher
