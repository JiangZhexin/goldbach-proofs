import PintzMinorPRMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Filter Finset

namespace RichShiftMinorPower263

/-- Standard Bessel-to-count transfer with a fixed linear coefficient margin,
allowing a power-sized cutoff to vary. -/
theorem countAbove {N P C θ c : ℝ} {D : Finset ℕ} (F : ℕ → ℂ) (k : ℕ)
    (hN : 1 ≤ N) (hP : N^θ ≤ 2*P) (hθ : θ ≤ 2/5)
    (hC : 0 ≤ C) (hc : 0 < c)
    (hEnergy : (∑ m ∈ D, ‖F m‖^2) ≤
      C*(N^3/P+N^(13/5 : ℝ))* (Real.log N)^k) :
    (((D.filter (fun m => c*N ≤ ‖F m‖)).card):ℝ) ≤
      (3*C/c^2)*N^(1-θ)*(Real.log N)^k := by
  classical
  let T : ℝ := c*N
  let E : Finset ℕ := D.filter (fun m => T ≤ ‖F m‖)
  have hN' : 0 < N := zero_lt_one.trans_le hN
  have hT : 0 < T := mul_pos hc hN'
  have hP' : 0 < P := by
    have := Real.rpow_pos_of_pos hN' θ
    linarith
  have hC' : 0 ≤ C*(Real.log N)^k :=
    mul_nonneg hC (pow_nonneg (Real.log_nonneg hN) _)
  have hA : N^3/P ≤ 2*N^(3-θ) := by
    have hB := mul_le_mul_of_nonneg_left hP
      (Real.rpow_nonneg hN'.le (3-θ))
    rw [← Real.rpow_add hN', show (3-θ+θ : ℝ) = 3 by ring,
      Real.rpow_ofNat] at hB
    apply (div_le_iff₀ hP').2
    nlinarith only [hB]
  have hB : N^(13/5 : ℝ) ≤ N^(3-θ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hh := mul_le_mul_of_nonneg_left (show N^3/P+N^(13/5 : ℝ) ≤
    3*N^(3-θ) by linarith only [hA,hB]) hC'
  have hE : (E.card:ℝ)*T^2 ≤ 3*C*N^(3-θ)*(Real.log N)^k := by
    calc
      _ = ∑ _m ∈ E, T^2 := by simp
      _ ≤ ∑ m ∈ E, ‖F m‖^2 := by
        apply sum_le_sum
        intro m hm
        exact pow_le_pow_left₀ hT.le (mem_filter.mp hm).2 2
      _ ≤ ∑ m ∈ D, ‖F m‖^2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := hEnergy.trans (by nlinarith only [hh])
  change (E.card:ℝ) ≤ _
  have H := (le_div_iff₀ (sq_pos_of_pos hT)).2 hE
  refine H.trans_eq ?_
  dsimp [T]
  rw [mul_pow]
  have h2 : N^2 = N^(2:ℝ) := (Real.rpow_ofNat N 2).symm
  have hc0 : c^2 ≠ 0 := pow_ne_zero _ hc.ne'
  have hN0 : N^(2:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hN' _).ne'
  rw [h2, show 3*C*N^(3-θ)*(Real.log N)^k/(c^2*N^(2:ℝ)) =
      (3*C/c^2)*(N^(3-θ)/N^(2:ℝ))*(Real.log N)^k by field_simp]
  rw [← Real.rpow_sub hN']
  congr 2
  ring

theorem literalCount {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
    ∀ P : ℕ, ∀ a : ℝ, ∀ D : Finset ℕ,
      1 ≤ P → P ≤ N → ⌊a⌋₊ ≤ N → 2*(P:ℝ)^2 < (N:ℝ) →
      (N:ℝ)^(263/1000:ℝ) ≤ 2*(P:ℝ) →
      (((D.filter (fun m => c*(N:ℝ) ≤ ‖PintzMinorPRMoment.localCoeff N P a m‖)).card):ℝ)
        ≤ B*(N:ℝ)^(37/50:ℝ) := by
  classical
  let B : ℝ := 3*(4*100000^2)/c^2
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  have hAbsorb := (isLittleO_log_rpow_rpow_atTop (10:ℝ) (s := (3/1000:ℝ))
    (by norm_num)).bound (by norm_num : (0:ℝ) < 1)
  have hLimit : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [PintzMinorPRMoment.literal_energy_finset, hLimit.eventually hAbsorb,
    eventually_ge_atTop (1:ℕ)] with N hEnergy hLog hN P a D hP hPN ha hSep hlo
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN' : (0:ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hL := Real.log_nonneg hN1
  have hlog : Real.log (N:ℝ)^10 ≤ (N:ℝ)^(3/1000:ℝ) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hL _),
      Real.norm_of_nonneg (Real.rpow_nonneg hN'.le _), one_mul, Real.rpow_ofNat] at hLog
    exact hLog
  have hb := countAbove (PintzMinorPRMoment.localCoeff N P a) 10 hN1 hlo
    (by norm_num : (263/1000:ℝ) ≤ 2/5) (by positivity) hc (hEnergy P a D hP hPN ha hSep)
  refine hb.trans ?_
  change B*(N:ℝ)^(1-263/1000:ℝ)*Real.log (N:ℝ)^10 ≤ B*(N:ℝ)^(37/50:ℝ)
  calc
    _ ≤ B*(N:ℝ)^(1-263/1000:ℝ)*(N:ℝ)^(3/1000:ℝ) := by
      exact mul_le_mul_of_nonneg_left hlog (by dsimp [B]; positivity)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hN']; norm_num

#print axioms literalCount

end RichShiftMinorPower263
