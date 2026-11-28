import PintzSection8Coefficient
import PintzExceptionalMinorPower

open Finset Set MeasureTheory PintzMajorArcGeometry PintzPoleKernelTail
open PintzMajorArcPrimeEnergy

namespace PintzPrimePairCoefficient

noncomputable def f (s : Finset ℕ) (w : ℕ → ℂ) (m : ℕ) (t : ℝ) : ℂ :=
  (poly s w t)^2*phase (-(m:ℝ)*t)

theorem continuous_f (s : Finset ℕ) (w : ℕ → ℂ) (m : ℕ) :
    Continuous (f s w m) := by
  unfold f
  apply ((poly_cont s w).pow 2).mul
  unfold phase
  fun_prop

theorem periodic_f (s : Finset ℕ) (w : ℕ → ℂ) (m : ℕ) :
    Function.Periodic (f s w m) 1 := by
  intro t
  have he : -(m:ℝ)*(t+1) = -(m:ℝ)*t+((-(m:ℤ)):ℝ) := by push_cast; ring
  have hz := phase_int (-(m:ℤ))
  simp only [Int.cast_neg,Int.cast_natCast] at hz
  simp only [f,poly_periodic s w t,he,phase_add,Int.cast_neg,Int.cast_natCast,hz,mul_one]

/-- Exact pair coefficient of a finite prime polynomial on any period. -/
theorem period (s : Finset ℕ) (w : ℕ → ℂ) (m : ℕ) (a : ℝ) :
    (∫ t in a..a+1, f s w m t) =
      ∑ p∈s, ∑ q∈s, if p+q=m then w p*w q else 0 := by
  classical
  rw [(periodic_f s w m).intervalIntegral_add_eq _ (-(1/2:ℝ)),
    show -(1/2:ℝ)+1=(1/2:ℝ) by ring]
  let entry (p q : ℕ) (t : ℝ) := w p*w q*phase (((p:ℤ)+(q:ℤ)-m:ℤ)*t)
  have hE (p q : ℕ) : Continuous (entry p q) := by dsimp [entry]; unfold phase; fun_prop
  have hM (t : ℝ) : f s w m t = ∑ p∈s, ∑ q∈s, entry p q t := by
    unfold f poly
    rw [pow_two, sum_mul_sum, Finset.sum_mul]
    apply sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply sum_congr rfl
    intro q _
    have H : (((p:ℤ)+(q:ℤ)-m:ℤ):ℝ)*t=(p:ℝ)*t+(q:ℝ)*t+(-(m:ℝ)*t) := by
      push_cast
      ring
    dsimp only [entry]
    rw [H,phase_add,phase_add]
    ring
  simp_rw [hM]
  rw [intervalIntegral.integral_finsetSum (fun p _ =>
    (continuous_finsetSum _ (fun q _ => hE p q)).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro p _
  rw [intervalIntegral.integral_finsetSum (fun q _ => (hE p q).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro q _
  unfold entry
  rw [intervalIntegral.integral_const_mul,integral_phase_int]
  by_cases hp : p+q=m
  · have hi : (p:ℤ)+(q:ℤ)-m=0 := by omega
    simp [hp,hi]
  · have hi : (p:ℤ)+(q:ℤ)-m≠0 := by omega
    simp [hp,hi]

theorem no_pairs_period {s : Finset ℕ} {m : ℕ} (w : ℕ → ℂ) (a : ℝ)
    (hNo : ∀ p∈s, ∀ q∈s, p+q ≠ m) :
    (∫ t in a..a+1, f s w m t) = 0 := by
  rw [period]
  exact sum_eq_zero (fun p hp => sum_eq_zero (fun q hq => if_neg (hNo p hp q hq)))

noncomputable def periodSet (P : ℕ) (N : ℝ) : Set ℝ := Set.Ioc (-(P:ℝ)/N) (1-(P:ℝ)/N)
noncomputable def majorSet (P : ℕ) (N : ℝ) : Set ℝ := ⋃ i ∈ reduced P, arc P N i
noncomputable def minorSet (P : ℕ) (N : ℝ) : Set ℝ := SDiff.sdiff (periodSet P N) (majorSet P N)

theorem major_measurable (P : ℕ) (N : ℝ) : MeasurableSet (majorSet P N) := by
  apply Finset.measurableSet_biUnion
  intro i _
  exact measurableSet_Ioc

/-- On a nonrepresentation, the exact minor coefficient is minus the
major coefficient. No comparison of oscillatory integrals across masks. -/
theorem minor_eq_neg_major {P : ℕ} {N : ℝ} (hP : 1 ≤ P) (hN : 2*(P:ℝ)^2 < N)
    {s : Finset ℕ} {m : ℕ} (w : ℕ → ℂ) (hNo : ∀ p∈s, ∀ q∈s, p+q ≠ m) :
    (∫ t in minorSet P N, f s w m t) =
      -(∫ t in majorSet P N, f s w m t) := by
  have hSub : majorSet P N ⊆ periodSet P N :=
    Set.iUnion₂_subset (fun i hi => arcs_contained hP hN hi)
  have hI : IntegrableOn (f s w m) (periodSet P N) :=
    (continuous_f s w m).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hM := major_measurable P N
  have hPeriod : (∫ t in periodSet P N, f s w m t) = 0 := by
    unfold periodSet
    rw [show 1-(P:ℝ)/N = -(P:ℝ)/N+1 by ring,
      ← intervalIntegral.integral_of_le (by linarith)]
    exact no_pairs_period w (-(P:ℝ)/N) hNo
  have hh := setIntegral_sdiff hM hI hSub
  rw [hPeriod,zero_sub] at hh
  exact hh

#print axioms period
#print axioms minor_eq_neg_major
end PintzPrimePairCoefficient
