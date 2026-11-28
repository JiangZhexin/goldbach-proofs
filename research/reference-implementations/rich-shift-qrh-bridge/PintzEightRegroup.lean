import PintzEightConductors

noncomputable section
open Finset MeasureTheory PintzEightEnergy PintzEightConductors
open scoped Classical
namespace PintzEightRegroup

def width (Q : ℝ) (q : ℕ) := 1 / ((q : ℝ) * Q)

def energy (Q : ℝ) (q : ℕ) [NeZero q]
    (F : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ) :=
  ∑ a : ZMod q, intervalEnergy (width Q q) (fun x =>
    (∑ χ : DirichletCharacter ℂ q,
      χ a * gaussSum χ⁻¹ ZMod.stdAddChar * F χ.conductor χ.primitiveCharacter x) / (q.totient : ℂ))

def primEnergy (Q : ℝ) (F : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ) (r : ℕ) :=
  ∑ χ ∈ prims r, intervalEnergy (width Q r) (F r χ)

theorem modulus_bound {q : ℕ} [NeZero q] {Q : ℝ} (hQ : 0 < Q)
    (F : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ) (hF : ∀ r χ, Continuous (F r χ)) :
    energy Q q F ≤ ∑ r ∈ q.divisors,
      if (q / r).Coprime r then (r : ℝ) / (q.totient : ℝ) * primEnergy Q F r else 0 := by
  rw [energy, diagonal _ _ _ (fun χ => hF _ _)]
  have hp : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [sum_div]
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q,
        (if (q / χ.conductor).Coprime χ.conductor then
          (χ.conductor : ℝ) / (q.totient : ℝ) *
          intervalEnergy (width Q χ.conductor) (F χ.conductor χ.primitiveCharacter) else 0) := by
      apply sum_le_sum
      intro χ _
      have hr : 0 < χ.conductor := Nat.pos_of_ne_zero fun hz =>
        NeZero.ne q (DirichletCharacter.conductor_eq_zero_iff_level_eq_zero.mp hz)
      letI : NeZero χ.conductor := ⟨hr.ne'⟩
      have hg := PintzEightGauss.standard_gauss_vanish_or_bound
        χ.conductor_dvd_level χ.primitiveCharacter_isPrimitive
      rw [DirichletCharacter.changeLevel_primitiveCharacter] at hg
      rw [DirichletCharacter.norm_gaussSum_inv]
      have hu : 0 ≤ width Q q := by unfold width; positivity
      have hm : width Q q ≤ width Q χ.conductor := by
        unfold width
        apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level) hQ.le
      by_cases hc : (q / χ.conductor).Coprime χ.conductor
      · rw [ite_eq_left hc] at hg ⊢
        have hn : 0 ≤ intervalEnergy (width Q q) (F χ.conductor χ.primitiveCharacter) :=
          intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
        have hs : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 ≤ (χ.conductor : ℝ) :=
          (pow_le_pow_left₀ (norm_nonneg _) hg 2).trans_eq (Real.sq_sqrt (Nat.cast_nonneg _))
        rw [← div_mul_eq_mul_div]
        exact mul_le_mul (div_le_div_of_nonneg_right hs hp.le)
          (intervalEnergy_mono hu hm (hF _ _)) hn (by positivity)
      · rw [ite_eq_right hc] at hg ⊢
        rw [norm_le_zero_iff.mp hg, norm_zero, zero_pow (by decide), zero_mul, zero_div]
    _ = _ := by
      change (∑ χ : DirichletCharacter ℂ q,
          (fun z : (r : ℕ) × DirichletCharacter ℂ r =>
            if (q / z.1).Coprime z.1 then (z.1 : ℝ) / (q.totient : ℝ) *
              intervalEnergy (width Q z.1) (F z.1 z.2) else 0) (pack χ)) = _
      rw [sum_to_primitives (fun z : (r : ℕ) × DirichletCharacter ℂ r =>
        if (q / z.1).Coprime z.1 then (z.1 : ℝ) / (q.totient : ℝ) *
          intervalEnergy (width Q z.1) (F z.1 z.2) else 0)]
      apply sum_congr rfl
      intro r hr
      by_cases hc : (q / r).Coprime r <;> simp [hc, primEnergy, mul_sum]

#print axioms modulus_bound
end PintzEightRegroup
