import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Finset Filter

namespace PintzExceptionalMinorPower

/-- At the real-zero-safe threshold N^(1-ε), Bessel's power saving loses
exactly 2ε. Bessel energy and the cut P are explicit analytic inputs. -/
theorem count_above_power_threshold
    {N P C ε : ℝ} {D : Finset ℕ} (F : ℕ → ℂ) (k : ℕ)
    (hN : 1 ≤ N) (hP : N^(41/200 : ℝ) ≤ 2*P) (hC : 0 ≤ C)
    (hEnergy : (∑ m ∈ D, ‖F m‖^2) ≤
      C*(N^3/P+N^(13/5 : ℝ))* (Real.log N)^k) :
    (((D.filter (fun m => N^(1-ε) ≤ ‖F m‖)).card):ℝ) ≤
      3*C*N^(159/200+2*ε)*(Real.log N)^k := by
  classical
  let T : ℝ := N^(1-ε)
  let E : Finset ℕ := D.filter (fun m => T ≤ ‖F m‖)
  have hN' : 0 < N := zero_lt_one.trans_le hN
  have hT : 0 < T := Real.rpow_pos_of_pos hN' _
  have hP' : 0 < P := by
    have h := Real.rpow_pos_of_pos hN' (41/200 : ℝ)
    linarith
  have hC' : 0 ≤ C*(Real.log N)^k :=
    mul_nonneg hC (pow_nonneg (Real.log_nonneg hN) _)
  have hA : N^3/P ≤ 2*N^(559/200 : ℝ) := by
    have hB := mul_le_mul_of_nonneg_left hP
      (Real.rpow_nonneg hN'.le (559/200 : ℝ))
    rw [← Real.rpow_add hN', show (559/200+41/200 : ℝ) = 3 by norm_num,
      Real.rpow_ofNat] at hB
    apply (div_le_iff₀ hP').2
    nlinarith only [hB]
  have hB : N^(13/5 : ℝ) ≤ N^(559/200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have hh := mul_le_mul_of_nonneg_left (show N^3/P+N^(13/5 : ℝ) ≤
    3*N^(559/200 : ℝ) by linarith only [hA,hB]) hC'
  have hE : (E.card:ℝ)*T^2 ≤ 3*C*N^(559/200 : ℝ)*(Real.log N)^k := by
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
  rw [← Real.rpow_mul_natCast hN'.le (1-ε) 2]
  rw [show 3*C*N^(559/200 : ℝ)*(Real.log N)^k /
    N^((1-ε)*(2:ℕ)) = 3*C*(N^(559/200 : ℝ) / N^((1-ε)*(2:ℕ)))*(Real.log N)^k by ring]
  rw [← Real.rpow_sub hN', show (559/200 - (1-ε)*(2:ℕ) : ℝ) = 159/200+2*ε by push_cast; ring]

/-- A logarithmic real-zero gap at conductor q≤N^θ implies a uniform
gap at the N scale. This is only a transfer of a supplied lower bound on
the real zero defect δ, not a zero-free theorem. The asymptotic θ+ν
allows an arbitrarily small blowup in the logarithmic coefficient. -/
theorem eventually_transfer_real_zero_gap {c θ ν : ℝ}
    (hθ : 0 ≤ θ) (hν : 0 < ν) :
    ∀ᶠ N : ℝ in atTop, ∀ q δ : ℝ, 0 ≤ q → q ≤ N^θ → 0 ≤ δ →
      c ≤ δ*Real.log (q+2) → c/(θ+ν) ≤ δ*Real.log N := by
  have hlarge := Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 3 / ν)
  filter_upwards [hlarge,eventually_ge_atTop (1:ℝ)] with N hLarge hN q δ hq hqN hδ hgap
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hp : 1 ≤ N^θ := Real.one_le_rpow hN hθ
  have hqin : 0 < q+2 := by linarith
  have hq2 : q+2 ≤ 3*N^θ := by linarith
  have hL := Real.log_le_log hqin hq2
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hN0 _).ne',
    Real.log_rpow hN0] at hL
  have hconst := (div_le_iff₀ hν).1 hLarge
  have hmajor : Real.log (q+2) ≤ (θ+ν)*Real.log N := by
    nlinarith only [hL,hconst]
  have hscale := hgap.trans (mul_le_mul_of_nonneg_left hmajor hδ)
  exact (div_le_iff₀ (by linarith : 0 < θ+ν)).2 (by nlinarith only [hscale])

/-- Small-threshold Chebyshev count preserves the necessary strict margin
below exponent 0.8 when the single-zero power loss is at most .001. -/
theorem count_above_small_power_threshold
    {N P C ε : ℝ} {D : Finset ℕ} (F : ℕ → ℂ) (k : ℕ)
    (hN : 1 ≤ N) (hP : N^(41/200 : ℝ) ≤ 2*P) (hC : 0 ≤ C)
    (hε : ε ≤ 1/1000)
    (hEnergy : (∑ m ∈ D, ‖F m‖^2) ≤
      C*(N^3/P+N^(13/5 : ℝ))* (Real.log N)^k) :
    (((D.filter (fun m => N^(1-ε) ≤ ‖F m‖)).card):ℝ) ≤
      3*C*N^(797/1000 : ℝ)*(Real.log N)^k := by
  refine (count_above_power_threshold F k hN hP hC hEnergy).trans ?_
  have hp := Real.rpow_le_rpow_of_exponent_le (x := N) hN
    (show (159/200+2*ε : ℝ) ≤ 797/1000 by linarith)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity))
    (pow_nonneg (Real.log_nonneg hN) _)

#print axioms count_above_power_threshold
#print axioms count_above_small_power_threshold
#print axioms eventually_transfer_real_zero_gap

end PintzExceptionalMinorPower
