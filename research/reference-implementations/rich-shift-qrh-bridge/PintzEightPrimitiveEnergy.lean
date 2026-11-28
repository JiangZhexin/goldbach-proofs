import PintzEightLog

noncomputable section
open Finset MeasureTheory PintzEightEnergy PintzEightConductors PintzEightRegroup
open scoped Classical
namespace PintzEightPrimitiveEnergy

def arcEnergy (Q : ℝ) (q : ℕ) (F : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ) :=
  if hq : q = 0 then 0 else @energy Q q ⟨hq⟩ F

theorem energy_log_squared :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℕ) (Q : ℝ), 1 ≤ P → 0 < Q →
    ∀ (F : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ), (∀ r χ, Continuous (F r χ)) →
      (∑ q ∈ Icc 1 P, arcEnergy Q q F) ≤
        C * (1 + Real.log P)^2 * ∑ r ∈ Icc 1 P, primEnergy Q F r := by
  obtain ⟨A, hA, hAall⟩ := PintzEightLog.exists_reciprocal_totient_sum_bound
  refine ⟨Real.exp 4 * A, by positivity, ?_⟩
  intro P Q hP hQ F hF
  have hlog : 0 ≤ 1 + Real.log P := by
    have hp : (1 : ℝ) ≤ P := by exact_mod_cast hP
    linarith [Real.log_nonneg hp]
  calc
    _ ≤ ∑ q ∈ Icc 1 P, ∑ r ∈ q.divisors,
        if (q/r).Coprime r then (r : ℝ) / (q.totient : ℝ) * primEnergy Q F r else 0 := by
      apply sum_le_sum
      intro q hq
      have hp : q ≠ 0 := (show 0 < q from (mem_Icc.mp hq).1).ne'
      rw [arcEnergy, dite_eq_right hp]
      exact @modulus_bound q ⟨hp⟩ Q hQ F hF
    _ = _ := PintzEightSummation.regroup_totient P _
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro r hr
      have hrp : 0 < r := (mem_Icc.mp hr).1
      have hru := (mem_Icc.mp hr).2
      have hdiv (d) (hd : d ∈ r.divisors) : d ∈ Ioc 0 P :=
        mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors hd, (Nat.le_of_dvd hrp (Nat.dvd_of_mem_divisors hd)).trans hru⟩
      have ha : (r : ℝ) / (r.totient : ℝ) ≤ Real.exp 4 * (1 + Real.log P) := by
        refine (PintzEightLog.totient_ratio_le_divisor_reciprocals hrp).trans ?_
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact (sum_le_sum_of_subset_of_nonneg hdiv (fun _ _ _ => by positivity)).trans
          (PintzEightLog.reciprocal_initial_sum P)
      have hb : (∑ l ∈ (Icc 1 (P/r)).filter (·.Coprime r), (1 : ℝ) / (l.totient : ℝ)) ≤
          A * (1 + Real.log P) := by
        refine (sum_le_sum_of_subset_of_nonneg (t := Icc 1 P) ?_ (fun _ _ _ => by positivity)).trans ?_
        · exact (filter_subset _ _).trans (Icc_subset_Icc le_rfl (Nat.div_le_self P r))
        · simpa only [one_div] using hAall P hP
      have he : 0 ≤ primEnergy Q F r := by
        unfold primEnergy
        apply sum_nonneg
        intro χ _
        apply intervalIntegral.integral_nonneg
        · have hu : 0 ≤ width Q r := by unfold width; positivity
          linarith
        · exact fun _ _ => sq_nonneg _
      apply mul_le_mul_of_nonneg_right _ he
      calc
        _ ≤ (Real.exp 4 * (1 + Real.log P)) * (A * (1 + Real.log P)) := by
          exact mul_le_mul ha hb (sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = _ := by ring

#print axioms energy_log_squared
end PintzEightPrimitiveEnergy
