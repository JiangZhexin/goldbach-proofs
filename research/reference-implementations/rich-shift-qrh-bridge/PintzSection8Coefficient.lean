import PintzSection8LiteralModels
import PintzReducedArcEnergy

open Finset Filter MeasureTheory PintzMajorArcGeometry
open PintzSection8LiteralModels PintzEightEnergy

namespace PintzSection8Coefficient

private theorem arcs_separated {P : ℕ} {N : ℝ} (hN : 4 ≤ N)
    (hcut : (P:ℝ) ≤ N^(21/100:ℝ)) : 2*(P:ℝ)^2 < N := by
  have hN1 : 1 < N := by linarith
  have hN0 : 0 < N := by linarith
  have hP : (P:ℝ)^2 ≤ N^(42/100:ℝ) := by
    calc
      _ ≤ (N^(21/100:ℝ))^2 := pow_le_pow_left₀ (by positivity) hcut 2
      _ = _ := by rw [← Real.rpow_mul_natCast hN0.le]; norm_num
  have hs : 2 ≤ N^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow,Real.le_sqrt (by norm_num) hN0.le]
    linarith
  have ht : (2:ℝ) < N^(58/100:ℝ) := hs.trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num))
  calc
    _ ≤ 2*N^(42/100:ℝ) := mul_le_mul_of_nonneg_left hP (by norm_num)
    _ < N^(58/100:ℝ)*N^(42/100:ℝ) := mul_lt_mul_of_pos_right ht (by positivity)
    _ = _ := by rw [← Real.rpow_add hN0]; norm_num

/-- An actual form of Pintz I (8.28), with the discretized near-zero
model, on the same translated reduced major arcs. The full term is the
literal finite prime polynomial, not a postulated Fourier data term. -/
theorem coefficient_eventual {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (P : ℕ) (a v : ℝ),
      1 ≤ P → (P:ℝ) ≤ (n:ℝ)^(21/100:ℝ) → (P:ℝ) ≤ a →
      2 ≤ a → a ≤ v → v ≤ (n:ℝ) →
      ∀ (B : ℕ×ℕ → ℝ → ℂ), (∀ i∈reduced P, Continuous (B i)) →
      (∀ i∈reduced P, ∀ x, ‖B i x‖ ≤ 1) →
      ‖(∑ i ∈ reduced P, ∫ x in -(radius P n i)..radius P n i,
          (full a v (x+center i))^2*B i x) -
        (∑ i ∈ reduced P, ∫ x in -(radius P n i)..radius P n i,
          (PintzReducedArcEnergy.slice (retained n a v b) i x)^2*B i x)‖ ≤
        C*(n:ℝ)^(1-b/82)*(1+Real.log (n:ℝ))^2 := by
  obtain ⟨D,hD,hR⟩ := PintzSection8Bound.arc_bound_eventual hb hb2
  refine ⟨1+2*D,by positivity,?_⟩
  filter_upwards [hR,eventually_ge_atTop (4:ℕ)] with n hR hn
  intro P a v hP hcut haP ha hav hv B hB hBn
  have hN : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0:ℝ) < n := by linarith
  have hN1 : (1:ℝ) ≤ n := by linarith
  let J := reduced P
  let u := radius P n
  let S (i : ℕ×ℕ) (x : ℝ) := full a v (x+center i)
  let R := PintzReducedArcEnergy.slice (PintzResidualMajorArc.residual n a v b)
  let G := PintzReducedArcEnergy.slice (retained n a v b)
  have hu (i) (hi : i ∈ J) : 0 ≤ u i := by dsimp [u,radius]; positivity
  have hs (i) (hi : i ∈ J) : Continuous (S i) := (PintzMajorArcPrimeEnergy.poly_cont _ _).comp
    (continuous_id.add continuous_const)
  have hr (i) (hi : i ∈ J) : Continuous (R i) :=
    PintzReducedArcEnergy.continuous_slice _ (PintzResidualMajorArc.residual_continuous _ _ _ _) i
  have hfull : (∑ i ∈ J, ∫ x in -(u i)..u i, ‖S i x‖^2) ≤
      1*(n:ℝ)*(1+Real.log (n:ℝ))^2 := by
    refine (PintzMajorArcPrimeEnergy.prime_energy hP (arcs_separated hN hcut)
      (primes a v) (fun m hm => ?_)).trans ?_
    · have h := Finset.mem_filter.mp hm
      exact ⟨h.2,((Nat.le_floor_iff (by linarith : 0 ≤ v)).mp (mem_Ioc.mp h.1).2).trans hv⟩
    · rw [one_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (Real.log_nonneg hN1) (by linarith) _
  have herr : (∑ i ∈ J, ∫ x in -(u i)..u i, ‖R i x‖^2) ≤ D*(n:ℝ)^(1-b/41) :=
    (PintzReducedArcEnergy.reduced_energy_le P n hP hN0 _).trans (hR P a v hP hcut ha hav hv)
  have hSplit (i : ℕ×ℕ) (hi : i ∈ J) (x : ℝ) : S i x - R i x = G i x := by
    obtain ⟨hq,hqP,haq,hcop⟩ := mem_reduced.mp hi
    letI : NeZero i.1 := ⟨hq.ne'⟩
    have hqa : (i.1:ℝ) ≤ a := (by exact_mod_cast hqP : (i.1:ℝ) ≤ P).trans haP
    have hh := actual_slice (N := (n:ℝ)) (a := a) (v := v) (b := b) hcop hqa x
    have he (F : PintzReducedArcEnergy.Data) :
        PintzReducedArcEnergy.slice F i x =
          PintzEightCoefficient.slice i.1 (i.2:ZMod i.1) F x := by
      rw [PintzReducedArcEnergy.slice,dite_eq_right hq.ne']
      rfl
    dsimp only [S,R,G,center]
    rw [he,he,hh]
    ring
  have H := PintzFiniteArcDifference.transfer J u S R B hu hs hr hB hBn
    (ell := (n:ℝ)^(-b/82)) (Real.rpow_pos_of_pos hN0 _)
  have hbnd := PintzFiniteArcDifference.normalize hN1 hb (show (0:ℝ) ≤ 1 by norm_num)
    hD hfull herr
  have hEq : (∑ i ∈ J, ∫ x in -(u i)..u i, (S i x-R i x)^2*B i x) =
      ∑ i ∈ J, ∫ x in -(u i)..u i, (G i x)^2*B i x := by
    apply sum_congr rfl
    intro i hi
    apply intervalIntegral.integral_congr
    intro x _
    change (S i x-R i x)^2*B i x=(G i x)^2*B i x
    rw [hSplit i hi x]
  rw [hEq] at H
  exact H.trans hbnd

#print axioms coefficient_eventual
end PintzSection8Coefficient
