import RichShiftDyadic
import RichShiftMinorPower263
import PintzExceptionFinalReduction

open Finset Filter MeasureTheory Set
open PintzPrimePairCoefficient PintzExceptionFinalReduction
namespace RichShift263
open RichShift

theorem truncated_real_coefficient_le_weighted {N P m : ℕ} (a : ℝ)
    (hP : 1 ≤ P) (hSep : 2*(P:ℝ)^2 < (N:ℝ)) :
    (majorCoeff N P a m + PintzMinorPRMoment.localCoeff N P a m).re ≤ weighted m := by
  rw [minor_coeff_eq]
  unfold majorCoeff
  let S := actualPrimes N a
  let w : ℕ → ℂ := fun p => (Real.log p:ℂ)
  let F := f S w m
  change ((∫ t in majorSet P N, F t)+(∫ t in minorSet P N, F t)).re ≤ _
  have hSub : majorSet P N ⊆ periodSet P N :=
    Set.iUnion₂_subset (fun i hi => PintzMajorArcGeometry.arcs_contained hP hSep hi)
  have hI : IntegrableOn F (periodSet P N) :=
    (continuous_f S w m).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hPer : (∫ t in periodSet P N, F t) =
      ∑ p∈S, ∑ q∈S, if p+q=m then w p*w q else 0 := by
    unfold periodSet
    rw [show 1-(P:ℝ)/(N:ℝ) = -(P:ℝ)/(N:ℝ)+1 by ring,
      ← intervalIntegral.integral_of_le (by linarith)]
    exact period S w m _
  have hsd := setIntegral_sdiff (major_measurable P N) hI hSub
  change (∫ t in minorSet P N, F t) =
      (∫ t in periodSet P N, F t) - (∫ t in majorSet P N, F t) at hsd
  rw [hsd, add_sub_cancel, hPer]
  classical
  let T := S.filter (fun p => p ≤ m ∧ m-p ∈ S)
  have hsum (p : ℕ) :
      (∑ q∈S, if p+q=m then w p*w q else 0) =
        if p ≤ m ∧ m-p ∈ S then w p*w (m-p) else 0 := by
    by_cases hp : p ≤ m
    · simp only [hp, true_and]
      have eq (q : ℕ) : p+q=m ↔ q=m-p := by omega
      simp_rw [eq]
      rw [Finset.sum_ite_eq']
    · have eq (q : ℕ) : ¬ p+q=m := by omega
      simp [hp,eq]
  simp_rw [hsum]
  rw [← Finset.sum_filter]
  change (∑ p∈T, w p*w (m-p)).re ≤ _
  have hsub : T ⊆ reps m := by
    intro p hp
    obtain ⟨hs, hle, hmem⟩ := mem_filter.mp hp
    have hprime := (mem_filter.mp hs).2
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.two_le, hle⟩,
      hprime, (mem_filter.mp hmem).2⟩
  have hre : (∑ p∈T, w p*w (m-p)).re =
      ∑ p∈T, Real.log (p:ℝ)*Real.log ((m-p:ℕ):ℝ) := by
    rw [← Complex.reCLM_apply, map_sum]
    simp only [Complex.reCLM_apply, w, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre]
  unfold weighted
  exact sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
    mul_nonneg (Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ p from (mem_filter.mp hp).2.1.one_lt.le)))
      (Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ m-p from (mem_filter.mp hp).2.2.one_lt.le))))

theorem lowWeighted_of_major
    (hMajor : ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ X : ℕ in atTop,
      ∃ (P : ℕ) (a : ℝ), 1 ≤ P ∧ P ≤ 2*X ∧ ⌊a⌋₊ ≤ 2*X ∧
        2*(P:ℝ)^2 < ((2*X:ℕ):ℝ) ∧ ((2*X:ℕ):ℝ)^(263/1000:ℝ) ≤ 2*(P:ℝ) ∧
        ∀ m ∈ Finset.Icc X (2*X), Even m → 2*κ*((2*X:ℕ):ℝ) ≤ (majorCoeff (2*X) P a m).re) :
    ∃ κ A : ℝ, 0 < κ ∧ 0 < A ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
      ((lowWeighted X (2*X) (κ*X)).card : ℝ) ≤ A*(X:ℝ) ^ (37/50:ℝ) := by
  obtain ⟨κ,hκ,hM⟩ := hMajor
  obtain ⟨C,hC,hE⟩ := RichShiftMinorPower263.literalCount hκ
  let U : ℝ := 2^(37/50:ℝ)
  refine ⟨κ,C*U,hκ,by dsimp [U]; positivity,?_⟩
  apply eventually_atTop.mp
  have hTwice : Tendsto (fun X : ℕ => 2*X) atTop atTop :=
    tendsto_atTop_mono (fun X => by change X ≤ 2*X; omega) tendsto_id
  filter_upwards [hM,hTwice.eventually hE] with X hM hE
  obtain ⟨P,a,hP,hPN,ha,hSep,hCut,hFloor⟩ := hM
  let E := (Finset.Icc X (2*X)).filter (fun m => κ*((2*X:ℕ):ℝ) ≤
    ‖PintzMinorPRMoment.localCoeff (2*X) P a m‖)
  have hsub : lowWeighted X (2*X) (κ*X) ⊆ E := by
    intro m hm
    obtain ⟨hi, he, hlow⟩ := mem_filter.mp hm
    refine mem_filter.mpr ⟨hi,?_⟩
    have hfloor := hFloor m hi he
    have htr := truncated_real_coefficient_le_weighted (m:=m) a hP hSep
    rw [Complex.add_re] at htr
    have hnorm := Complex.abs_re_le_norm (PintzMinorPRMoment.localCoeff (2*X) P a m)
    have hneg := (abs_le.mp hnorm).1
    push_cast at hfloor hneg ⊢
    nlinarith [show (0:ℝ) ≤ κ*(X:ℝ) by positivity]
  refine (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans ((hE P a _ hP hPN ha hSep hCut).trans_eq ?_)
  push_cast
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)]
  dsimp [U]
  ring

#print axioms lowWeighted_of_major
theorem frozen_target_of_major
    (hMajor : ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ X : ℕ in atTop,
      ∃ (P : ℕ) (a : ℝ), 1 ≤ P ∧ P ≤ 2*X ∧ ⌊a⌋₊ ≤ 2*X ∧
        2*(P:ℝ)^2 < ((2*X:ℕ):ℝ) ∧ ((2*X:ℕ):ℝ)^(263/1000:ℝ) ≤ 2*(P:ℝ) ∧
        ∀ m ∈ Finset.Icc X (2*X), Even m → 2*κ*((2*X:ℕ):ℝ) ≤ (majorCoeff (2*X) P a m).re) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
      ∀ e ∈ Finset.Icc 1 (Nat.log 2 X/2),
        (((Finset.Ico X (2*X)).filter (fun n => Even n ∧
          (((Finset.Icc 2 (n-2^e)).filter
            (fun p => Nat.Prime p ∧ Nat.Prime ((n-2^e)-p))).card:ℝ)
            < c*(X:ℝ)/Real.log (X:ℝ)^2)).card : ℝ)
          ≤ C*(X:ℝ) ^ (37/50:ℝ) :=
  shift_of_dyadic_floor (lowWeighted_of_major hMajor)

#print axioms frozen_target_of_major
end RichShift263
