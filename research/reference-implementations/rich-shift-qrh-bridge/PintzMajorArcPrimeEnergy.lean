import PintzMajorArcGeometry
import PintzPoleKernelTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
open Finset Set MeasureTheory PintzMajorArcGeometry PintzPoleKernelTail
open scoped ComplexConjugate
namespace PintzMajorArcPrimeEnergy

def poly (s : Finset ℕ) (w : ℕ → ℂ) (t : ℝ) := ∑ n ∈ s, w n * phase ((n:ℝ)*t)

theorem poly_cont (s : Finset ℕ) (w : ℕ → ℂ) : Continuous (poly s w) := by
  unfold poly phase
  fun_prop

theorem poly_periodic (s : Finset ℕ) (w : ℕ → ℂ) : Function.Periodic (poly s w) 1 := by
  intro t
  unfold poly
  apply sum_congr rfl
  intro n _
  have h := phase_int (n:ℤ)
  simp only [Int.cast_natCast] at h
  rw [mul_add, mul_one, phase_add, h, mul_one]

private theorem phase_mul_star (n m : ℕ) (t : ℝ) :
    phase ((n:ℝ)*t) * star (phase ((m:ℝ)*t)) = phase ((((n:ℤ)-(m:ℤ)):ℝ)*t) := by
  unfold phase
  change Complex.exp _ * conj (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  have htwo : (starRingEnd ℂ) 2 = 2 := by
    simpa only [Nat.cast_ofNat] using (map_natCast (starRingEnd ℂ) 2)
  simp [Complex.conj_I, htwo]
  push_cast
  ring

theorem parseval_centered (s : Finset ℕ) (w : ℕ → ℂ) :
    (∫ t in (-(1/2 : ℝ))..(1/2:ℝ), ‖poly s w t‖^2) =
      ∑ n ∈ s, ‖w n‖^2 := by
  classical
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  push_cast
  let entry (n m : ℕ) (t : ℝ) :=
    (w n * star (w m)) * phase ((((n:ℤ)-(m:ℤ)):ℝ)*t)
  have hC (n m) : Continuous (entry n m) := by dsimp [entry]; unfold phase; fun_prop
  calc
    _ = ∫ t in (-(1/2 : ℝ))..(1/2:ℝ), ∑ n ∈ s, ∑ m ∈ s, entry n m t := by
      apply intervalIntegral.integral_congr
      intro t _
      change ((‖poly s w t‖ : ℝ):ℂ)^2 = _
      rw [← Complex.mul_conj']
      change poly s w t * star (poly s w t) = _
      unfold poly
      rw [star_sum, sum_mul_sum]
      refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
      rw [star_mul]
      calc
        _ = (w n * star (w m)) * (phase ((n:ℝ)*t) * star (phase ((m:ℝ)*t))) := by ac_rfl
        _ = _ := by rw [phase_mul_star]
    _ = ∑ n ∈ s, ∑ m ∈ s, ∫ t in (-(1/2 : ℝ))..(1/2:ℝ), entry n m t := by
      rw [intervalIntegral.integral_finsetSum]
      · apply sum_congr rfl
        intro n _
        rw [intervalIntegral.integral_finsetSum]
        exact fun m _ => (hC n m).intervalIntegrable _ _
      · intro n _
        exact (continuous_finsetSum _ (fun m _ => hC n m)).intervalIntegrable _ _
    _ = _ := by
      refine sum_congr rfl fun n hn => ?_
      rw [sum_eq_single_of_mem n hn]
      · simp only [entry, intervalIntegral.integral_const_mul]
        rw [← Int.cast_sub, integral_phase_int]
        simp [Complex.mul_conj'] 
      · intro m _ hmn
        have hz : (n:ℤ)-(m:ℤ) ≠ 0 := by omega
        simp only [entry, intervalIntegral.integral_const_mul]
        rw [← Int.cast_sub, integral_phase_int, ite_eq_right hz, mul_zero]

theorem arc_energy_le_total {P : ℕ} {N : ℝ} (hP : 1 ≤ P) (hPN : 2*(P:ℝ)^2 < N)
    (s : Finset ℕ) (w : ℕ → ℂ) :
    (∑ i ∈ reduced P, ∫ x in -(radius P N i)..radius P N i,
        ‖poly s w (x+center i)‖^2) ≤ ∑ n ∈ s, ‖w n‖^2 := by
  let f := fun t => ‖poly s w t‖^2
  have hf : Continuous f := (poly_cont s w).norm.pow 2
  have hPer : Function.Periodic f 1 := fun t => by dsimp [f]; rw [poly_periodic s w t]
  have hN : 0 < N := by nlinarith [sq_nonneg (P:ℝ)]
  have hAll : IntegrableOn f (Ioc (-(P:ℝ)/N) (1-(P:ℝ)/N)) :=
    hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  calc
    _ = ∑ i ∈ reduced P, ∫ t in arc P N i, f t := by
      apply sum_congr rfl
      intro i hi
      change (∫ x in -(radius P N i)..radius P N i, f (x + center i)) = _
      rw [intervalIntegral.integral_comp_add_right]
      simp only [arc, sub_eq_add_neg, add_comm (center i)]
      apply intervalIntegral.integral_of_le
      have hRad : 0 ≤ radius P N i := by unfold radius; positivity
      linarith
    _ = ∫ t in ⋃ i ∈ reduced P, arc P N i, f t := by
      symm
      apply integral_biUnion_finset
      · exact fun i _ => measurableSet_Ioc
      · intro i hi j hj hij
        exact arcs_disjoint hPN hi hj hij
      · intro i hi
        exact hAll.mono_set (arcs_contained hP hPN hi)
    _ ≤ ∫ t in Ioc (-(P:ℝ)/N) (1-(P:ℝ)/N), f t := by
      apply setIntegral_mono_set hAll (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      exact Filter.Eventually.of_forall (iUnion₂_subset (fun i hi => arcs_contained hP hPN hi))
    _ = _ := by
      rw [← intervalIntegral.integral_of_le (by rw [show 1-(P:ℝ)/N = -(P:ℝ)/N+1 by ring]; exact le_add_of_nonneg_right (by norm_num) : -(P:ℝ)/N ≤ 1-(P:ℝ)/N)]
      rw [show 1-(P:ℝ)/N = -(P:ℝ)/N+1 by ring, hPer.intervalIntegral_add_eq _ (-(1/2:ℝ))]
      convert parseval_centered s w using 2 <;> ring

theorem prime_energy {P : ℕ} {N : ℝ} (hP : 1 ≤ P) (hPN : 2*(P:ℝ)^2 < N)
    (s : Finset ℕ) (hs : ∀ n ∈ s, n.Prime ∧ (n:ℝ) ≤ N) :
    (∑ i ∈ reduced P, ∫ x in -(radius P N i)..radius P N i,
        ‖poly s (fun n => (Real.log n : ℂ)) (x+center i)‖^2) ≤ N*(Real.log N)^2 := by
  refine (arc_energy_le_total hP hPN s _).trans ?_
  have hsub : s ⊆ Finset.Icc 1 ⌊N⌋₊ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(hs n hn).1.one_le, Nat.le_floor (hs n hn).2⟩
  have hCard : (s.card : ℝ) ≤ N := by
    have H := Finset.card_le_card hsub
    simp at H
    calc
      _ ≤ (⌊N⌋₊:ℝ) := by exact_mod_cast H
      _ ≤ _ := Nat.floor_le (by nlinarith [sq_nonneg (P:ℝ)])
  calc
    _ ≤ ∑ n ∈ s, (Real.log N)^2 := by
      apply sum_le_sum
      intro n hn
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have h : (1:ℝ) ≤ n := by exact_mod_cast (hs n hn).1.one_le
      exact pow_le_pow_left₀ (Real.log_nonneg h)
        (Real.log_le_log (by linarith) (hs n hn).2) 2
    _ = (s.card : ℝ)*(Real.log N)^2 := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hCard (sq_nonneg _)

#print axioms arc_energy_le_total
#print axioms prime_energy
end PintzMajorArcPrimeEnergy
