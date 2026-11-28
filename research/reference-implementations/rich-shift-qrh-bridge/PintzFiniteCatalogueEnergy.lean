import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Finset MeasureTheory Filter
open scoped BigOperators
namespace PintzFiniteCatalogueEnergy

theorem finite_energy_pointwise {κ : Type*} (K : Finset κ) (z : κ → ℂ) :
    ‖∑ k ∈ K, z k‖^2 ≤ (K.card:ℝ) * ∑ k ∈ K, ‖z k‖^2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
  simpa using (Finset.sum_mul_sq_le_sq_mul_sq K (fun _ => (1:ℝ)) (fun k => ‖z k‖))

/-- Finite energy splitting, without an extra integrability assumption for
the global sum. Integrable block energies already supply an integral majorant. -/
theorem sum_energy {Ω κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (K : Finset κ) (f : κ → Ω → ℂ)
    (h : ∀ k ∈ K, Integrable (fun x => ‖f k x‖^2) μ) :
    (∫ x, ‖∑ k ∈ K, f k x‖^2 ∂μ) ≤ (K.card:ℝ) *
      ∑ k ∈ K, ∫ x, ‖f k x‖^2 ∂μ := by
  have hi : Integrable (fun x => (K.card:ℝ)*∑ k ∈ K, ‖f k x‖^2) μ :=
    (integrable_finsetSum K h).const_mul _
  have hb := integral_mono_of_nonneg
    (Eventually.of_forall (fun x => sq_nonneg ‖∑ k ∈ K, f k x‖)) hi
    (Eventually.of_forall (fun x => finite_energy_pointwise K (fun k => f k x)))
  rwa [integral_const_mul,integral_finsetSum K h] at hb

/-- Group an arbitrary finite catalogue by its labels, counting no empty
blocks. Take f to be the individual clipped-window zero contribution. -/
theorem labelled_energy {Ω ι κ : Type*} [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) (S : Finset ι) (label : ι → κ) (f : ι → Ω → ℂ)
    (h : ∀ k ∈ S.image label,
      Integrable (fun x => ‖∑ i ∈ S.filter (fun i => label i = k), f i x‖^2) μ) :
    (∫ x, ‖∑ i ∈ S, f i x‖^2 ∂μ) ≤ ((S.image label).card:ℝ) *
      ∑ k ∈ S.image label, ∫ x, ‖∑ i ∈ S.filter (fun i => label i = k), f i x‖^2 ∂μ := by
  have he (x : Ω) :
      (∑ k ∈ S.image label, ∑ i ∈ S.filter (fun i => label i = k), f i x) =
        ∑ i ∈ S, f i x :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem label hi) _
  simpa only [he] using sum_energy μ (S.image label)
    (fun k x => ∑ i ∈ S.filter (fun i => label i = k), f i x) h

/-- A bounded pointwise error supported in the whole clipped window has
energy ≤ E²(v-u+Y), with no pointwise regularity requirement. -/
theorem pointwise_error_energy {a b E : ℝ} (hab : a ≤ b) (_hE : 0 ≤ E)
    (e : ℝ → ℂ) (hEbound : ∀ x, ‖e x‖ ≤ E)
    (hs : ∀ x ∉ Set.Icc a b, e x = 0) :
    (∫ x : ℝ, ‖e x‖^2) ≤ (b-a)*E^2 := by
  let s := Set.Icc a b
  have hi : Integrable (s.indicator (fun _ : ℝ => E^2)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const isCompact_Icc.measure_ne_top)
  have hb := integral_mono_of_nonneg
    (Eventually.of_forall (fun x => sq_nonneg ‖e x‖)) hi
    (Eventually.of_forall (fun x => show ‖e x‖^2 ≤ s.indicator (fun _ => E^2) x from by
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx]; exact pow_le_pow_left₀ (norm_nonneg _) (hEbound x) 2
      · simp [Set.indicator_of_notMem hx, hs x hx]))
  rwa [integral_indicator measurableSet_Icc,setIntegral_const,Real.volume_real_Icc_of_le hab,smul_eq_mul] at hb

private theorem energy_add_pointwise (z w : ℂ) : ‖z+w‖^2 ≤ 2*(‖z‖^2+‖w‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le z w) 2
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

/-- Simultaneously aggregate the catalogue and a uniform error on its compact
support. The factor 2 may be removed when there is no error. -/
theorem labelled_energy_with_error {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (label : ι → κ) (f : ι → ℝ → ℂ)
    (h : ∀ k ∈ S.image label,
      Integrable (fun x => ‖∑ i ∈ S.filter (fun i => label i = k), f i x‖^2))
    {a b E : ℝ} (hab : a ≤ b) (_hE : 0 ≤ E)
    (e : ℝ → ℂ) (hEbound : ∀ x, ‖e x‖ ≤ E)
    (hs : ∀ x ∉ Set.Icc a b, e x = 0) :
    (∫ x : ℝ, ‖(∑ i ∈ S, f i x)+e x‖^2) ≤
      2*(((S.image label).card:ℝ) *
        (∑ k ∈ S.image label, ∫ x : ℝ, ‖∑ i ∈ S.filter (fun i => label i = k), f i x‖^2)
        +(b-a)*E^2) := by
  let K := S.image label
  let F (k : κ) (x : ℝ) : ℂ := ∑ i ∈ S.filter (fun i => label i = k), f i x
  let err (x : ℝ) : ℝ := (Set.Icc a b).indicator (fun _ : ℝ => E^2) x
  have h₁ : Integrable (fun x : ℝ => (K.card:ℝ)*∑ k ∈ K, ‖F k x‖^2) :=
    (integrable_finsetSum K h).const_mul _
  have h₂ : Integrable err :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const isCompact_Icc.measure_ne_top)
  have hsum (x : ℝ) : (∑ k ∈ K, F k x) = ∑ i ∈ S, f i x :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem label hi) _
  have hlocal (x : ℝ) : ‖e x‖^2 ≤ err x := by
    by_cases hx : x ∈ Set.Icc a b
    · change ‖e x‖^2 ≤ (Set.Icc a b).indicator (fun _ => E^2) x
      rw [Set.indicator_of_mem hx]
      exact pow_le_pow_left₀ (norm_nonneg _) (hEbound x) 2
    · simp [err, Set.indicator_of_notMem hx, hs x hx]
  have hdom (x : ℝ) :
      ‖(∑ i ∈ S, f i x)+e x‖^2 ≤ 2*((K.card:ℝ)*(∑ k ∈ K, ‖F k x‖^2)+err x) := by
    refine (energy_add_pointwise _ _).trans ?_
    rw [← hsum x]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (finite_energy_pointwise K (fun k => F k x)) (hlocal x)) (by norm_num)
  have hb := integral_mono_of_nonneg (Eventually.of_forall (fun x => sq_nonneg _))
    ((h₁.add h₂).const_mul 2) (Eventually.of_forall hdom)
  have herr : (∫ x : ℝ, err x) = (b-a)*E^2 := by
    dsimp [err]
    rw [integral_indicator measurableSet_Icc,setIntegral_const,Real.volume_real_Icc_of_le hab,smul_eq_mul]
  change (∫ x : ℝ, ‖(∑ i ∈ S, f i x)+e x‖^2) ≤
    ∫ x : ℝ, 2*((K.card:ℝ)*(∑ k ∈ K, ‖F k x‖^2)+err x) at hb
  rw [integral_const_mul,integral_add h₁ h₂,integral_const_mul,integral_finsetSum K h,herr] at hb
  exact hb

/-- For clipping by a common compact interval, continuity is needed only
on that interval, not everywhere. This discharges the block integrability
input uniformly for any partition of the finite catalogue. -/
theorem clipped_sum_sq_integrable {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (a b : ℝ) (hc : ∀ i ∈ S, ContinuousOn (f i) (Set.Icc a b)) :
    Integrable (fun x : ℝ => ‖∑ i ∈ S, (Set.Icc a b).indicator (f i) x‖^2) := by
  let F (x : ℝ) := ‖∑ i ∈ S, f i x‖^2
  have hi : Integrable ((Set.Icc a b).indicator F) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (((continuousOn_finsetSum S hc).norm.pow 2).integrableOn_Icc)
  convert hi using 1
  funext x
  by_cases hx : x ∈ Set.Icc a b
  · simp [F, Set.indicator_of_mem hx]
  · simp [F, Set.indicator_of_notMem hx]

/-- The catalogue partition applies to the actual clipped model by using
term-wise continuity only on [a,b]. -/
theorem clipped_labelled_energy {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (label : ι → κ) (f : ι → ℝ → ℂ) (a b : ℝ)
    (hc : ∀ i ∈ S, ContinuousOn (f i) (Set.Icc a b)) :
    let F := fun i => (Set.Icc a b).indicator (f i)
    (∫ x : ℝ, ‖∑ i ∈ S, F i x‖^2) ≤ ((S.image label).card:ℝ) *
      ∑ k ∈ S.image label, ∫ x : ℝ, ‖∑ i ∈ S.filter (fun i => label i = k), F i x‖^2 := by
  dsimp only
  apply labelled_energy
  intro k hk
  exact clipped_sum_sq_integrable _ f a b (fun i hi => hc i (Finset.mem_filter.mp hi).1)

/-- The signed endpoint-model convention of the high-window estimates. -/
noncomputable def signedEndpointModel {ι : Type*} (S : Finset ι)
    (ρ c : ι → ℂ) (m : ι → ℝ) (a b Y x : ℝ) : ℂ :=
  let f (t : ℝ) := ∑ i ∈ S, (m i:ℂ)*c i*(t:ℂ)^(ρ i)/((Y:ℂ)*ρ i)
  if a < x+Y ∧ x < b then f (min (x+Y) b)-f (max x a) else 0

private noncomputable def endpointTerm {ι : Type*} (ρ c : ι → ℂ) (m : ι → ℝ)
    (a b Y : ℝ) (i : ι) (x : ℝ) : ℂ :=
  (m i:ℂ)*c i*((min (x+Y) b:ℝ):ℂ)^(ρ i)/((Y:ℂ)*ρ i) -
  (m i:ℂ)*c i*((max x a:ℝ):ℂ)^(ρ i)/((Y:ℂ)*ρ i)

private theorem endpointTerm_continuousOn {ι : Type*} (ρ c : ι → ℂ) (m : ι → ℝ)
    {a b Y : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (i : ι) :
    ContinuousOn (endpointTerm ρ c m a b Y i) (Set.Icc (a-Y) b) := by
  have hmin : ContinuousOn (fun x : ℝ => ((min (x+Y) b:ℝ):ℂ)^(ρ i)) (Set.Icc (a-Y) b) := by
    intro x hx
    have hp : 0 < min (x+Y) b := lt_min (by linarith [hx.1]) (by linarith)
    have hh : Continuous (fun t : ℝ => min (t+Y) b) :=
      (continuous_id.add continuous_const).min continuous_const
    have hc := Complex.continuousAt_ofReal_cpow_const (min (x+Y) b) (ρ i) (Or.inr hp.ne')
    exact (ContinuousAt.comp (f := fun t : ℝ => min (t+Y) b) (x := x) hc hh.continuousAt).continuousWithinAt
  have hmax : ContinuousOn (fun x : ℝ => ((max x a:ℝ):ℂ)^(ρ i)) (Set.Icc (a-Y) b) := by
    intro x hx
    have hp : 0 < max x a := lt_of_lt_of_le (by linarith : 0 < a) (le_max_right _ _)
    have hh : Continuous (fun t : ℝ => max t a) := continuous_id.max continuous_const
    have hc := Complex.continuousAt_ofReal_cpow_const (max x a) (ρ i) (Or.inr hp.ne')
    exact (ContinuousAt.comp (f := fun t : ℝ => max t a) (x := x) hc hh.continuousAt).continuousWithinAt
  exact ((continuousOn_const.mul hmin).div_const _).sub ((continuousOn_const.mul hmax).div_const _)

private theorem signedEndpointModel_eq_sum {ι : Type*} (S : Finset ι)
    (ρ c : ι → ℂ) (m : ι → ℝ) {a b Y : ℝ} (hab : a ≤ b) (hY : 0 ≤ Y) (x : ℝ) :
    signedEndpointModel S ρ c m a b Y x =
      ∑ i ∈ S, (Set.Icc (a-Y) b).indicator (endpointTerm ρ c m a b Y i) x := by
  classical
  by_cases hx : a < x+Y ∧ x < b
  · have hxI : x ∈ Set.Icc (a-Y) b := ⟨by linarith [hx.1],hx.2.le⟩
    simp only [signedEndpointModel, ite_eq_left hx, Set.indicator_of_mem hxI, endpointTerm, sum_sub_distrib]
  · rw [signedEndpointModel, ite_eq_right hx]
    by_cases hI : x ∈ Set.Icc (a-Y) b
    · have he : min (x+Y) b = max x a := by
        by_cases hL : a < x+Y
        · have hxB : x = b := le_antisymm hI.2 (le_of_not_gt (fun h => hx ⟨hL,h⟩))
          subst x
          rw [min_eq_right (by linarith),max_eq_left hab]
        · have hxA : x+Y = a := le_antisymm (le_of_not_gt hL) (by linarith [hI.1])
          rw [hxA,min_eq_left hab,max_eq_right (by linarith)]
      simp [Set.indicator_of_mem hI, endpointTerm, he]
    · simp [Set.indicator_of_notMem hI]

/-- Energy aggregation for the exact signed endpoint zero model, including a
pointwise error supported on [a-Y,b]. It directly consumes block bounds on
the same window convention as the high-window estimates. -/
theorem signed_endpoint_energy_with_error {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (label : ι → κ) (ρ c : ι → ℂ) (m : ι → ℝ)
    {a b Y E : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (e : ℝ → ℂ) (hbound : ∀ x, ‖e x‖ ≤ E)
    (hs : ∀ x ∉ Set.Icc (a-Y) b, e x = 0) :
    (∫ x : ℝ, ‖signedEndpointModel S ρ c m a b Y x+e x‖^2) ≤
      2*(((S.image label).card:ℝ) *
        (∑ k ∈ S.image label, ∫ x : ℝ,
          ‖signedEndpointModel (S.filter (fun i => label i=k)) ρ c m a b Y x‖^2)
        +(b-(a-Y))*E^2) := by
  simp_rw [signedEndpointModel_eq_sum _ ρ c m hab hY]
  apply labelled_energy_with_error S label _ _ (by linarith) hE e hbound hs
  intro k hk
  exact clipped_sum_sq_integrable _ _ _ _ (fun i hi => endpointTerm_continuousOn ρ c m ha hab i)

#print axioms signed_endpoint_energy_with_error
#print axioms clipped_labelled_energy
#print axioms labelled_energy_with_error
#print axioms labelled_energy
#print axioms pointwise_error_energy
end PintzFiniteCatalogueEnergy
