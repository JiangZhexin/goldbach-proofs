import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

open scoped BigOperators
open Filter

namespace ExceptionUnionBridge

def G (m : ℕ) : ℕ :=
  ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card

def bad (m : ℕ) : Finset ℕ :=
  (Finset.range (m+1)).filter (fun n => 4 ≤ n ∧ Even n ∧ G n = 0)

def shifts (X : ℕ) : Finset ℕ := Finset.Icc 1 (Nat.log 2 X / 2)

def fails (X : ℕ) : Finset ℕ :=
  (Finset.Ico X (2*X)).filter
    (fun n => Even n ∧ 0 < ((shifts X).filter (fun e => G (n-2^e)=0)).card)

theorem card_fails (X : ℕ) (hX : 8 ≤ X) :
    (fails X).card ≤ (Nat.log 2 X / 2) * (bad (2*X)).card := by
  classical
  have hsub : fails X ⊆ (shifts X).biUnion
      (fun e => (bad (2*X)).image (fun m => m + 2^e)) := by
    intro n hn
    simp only [fails, Finset.mem_filter, Finset.mem_Ico] at hn
    obtain ⟨⟨hXn, hnX⟩, hnEven, hpos⟩ := hn
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    obtain ⟨hes, hG⟩ := Finset.mem_filter.mp he
    obtain ⟨he1, hel⟩ := Finset.mem_Icc.mp hes
    have hpow : 2^e * 2 ≤ X := by
      rw [← pow_succ]
      exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)).trans
        (Nat.pow_log_le_self 2 (by omega))
    have hev : Even (2^e : ℕ) := by
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
      rw [pow_succ]
      exact ⟨2^k, by omega⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨e, hes, Finset.mem_image.mpr ⟨n-2^e, ?_, by omega⟩⟩
    simp only [bad, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega, (by obtain ⟨a, ha⟩ := hnEven; obtain ⟨b, hb⟩ := hev; exact ⟨a-b, by omega⟩), hG⟩
  calc
    _ ≤ ((shifts X).biUnion
      (fun e => (bad (2*X)).image (fun m => m + 2^e))).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ shifts X, ((bad (2*X)).image (fun m => m + 2^e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ shifts X, (bad (2*X)).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = _ := by simp [shifts, Nat.card_Icc]

/-- The fixed multiplicative loss and the twentieth power of the number of
shifts are eventually dominated by one power of the scale. -/
theorem log_budget (A : ℕ) :
    ∀ᶠ X : ℕ in atTop, (Nat.log 2 X / 2)^20 * A ≤ X := by
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hc : (0 : ℝ) < Real.log 2 ^ (20 : ℕ) / ((A : ℝ) + 1) := by
    exact div_pos (pow_pos (Real.log_pos (by norm_num)) _) (by positivity)
  have h := (isLittleO_log_rpow_rpow_atTop (20 : ℝ) (s := (1 : ℝ)) (by norm_num)).bound hc
  filter_upwards [ht.eventually h, eventually_ge_atTop (1 : ℕ)] with X hX h1
  have hlog : (Nat.log 2 X : ℝ) * Real.log 2 ≤ Real.log (X : ℝ) := by
    have hp : (2 : ℝ)^(Nat.log 2 X) ≤ (X : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : X ≠ 0)
    have hh := Real.log_le_log (by positivity) hp
    rwa [Real.log_pow] at hh
  have hdiv : ((Nat.log 2 X / 2 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (X : ℝ) := by
    have hl : ((Nat.log 2 X / 2 : ℕ) : ℝ) ≤ (Nat.log 2 X : ℝ) := by
      exact_mod_cast Nat.div_le_self (Nat.log 2 X) 2
    exact (mul_le_mul_of_nonneg_right hl (Real.log_pos (by norm_num)).le).trans hlog
  have hp := pow_le_pow_left₀ (show 0 ≤ ((Nat.log 2 X / 2 : ℕ) : ℝ) * Real.log 2 by positivity) hdiv 20
  rw [mul_pow] at hp
  have hreal : Real.log (X : ℝ) ^ (20 : ℕ) ≤ Real.log 2 ^ (20 : ℕ) / ((A : ℝ) + 1) * (X : ℝ) := by
    calc
      _ ≤ |Real.log (X : ℝ) ^ (20 : ℕ)| := le_abs_self _
      _ ≤ _ := by
        simpa only [Real.rpow_ofNat, Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg X : (0 : ℝ) ≤ (X : ℝ)), Function.comp_apply] using hX
  have hp' := hp.trans hreal
  have hf : (Real.log 2 ^ (20 : ℕ) / ((A : ℝ) + 1)) * (X : ℝ) =
      ((X : ℝ) / ((A : ℝ) + 1)) * Real.log 2 ^ (20 : ℕ) := by ring
  rw [hf] at hp'
  have hz := le_of_mul_le_mul_right hp' (pow_pos (Real.log_pos (by norm_num)) 20)
  have hAA : (A : ℝ) ≤ (A : ℝ) + 1 := by linarith
  have hmul : ((Nat.log 2 X / 2 : ℕ) : ℝ) ^ 20 * (A : ℝ) ≤ (X : ℝ) :=
    (mul_le_mul_of_nonneg_left hAA (by positivity)).trans
      ((le_div_iff₀ (by positivity : 0 < (A : ℝ) + 1)).mp hz)
  exact_mod_cast hmul

/-- Exact target reduction, taking only an unconditional order (X^{3/4})
exception-count theorem as input. -/
theorem complete_of_power_bound
    (hbound : ∃ C X₀ : ℕ, ∀ X ≥ X₀, (bad X).card^4 ≤ C*X^3) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (fails X).card^5 ≤ X^4 := by
  obtain ⟨C, X₀, hC⟩ := hbound
  obtain ⟨N, hN⟩ := eventually_atTop.mp (log_budget ((8*C)^5))
  refine ⟨max (max N X₀) 8, fun X hX => ?_⟩
  have hn : N ≤ X := by omega
  have h8 : 8 ≤ X := by omega
  have h2 : X₀ ≤ 2*X := by omega
  have ha : (bad (2*X)).card^4 ≤ (8*C)*X^3 := by
    convert hC (2*X) h2 using 1
    ring
  have hw : ((fails X).card^5)^4 ≤ (X^4)^4 := by
    calc
      _ = (fails X).card^20 := by rw [← pow_mul]
      _ ≤ ((Nat.log 2 X / 2) * (bad (2*X)).card)^20 :=
        Nat.pow_le_pow_left (card_fails X h8) _
      _ = (Nat.log 2 X / 2)^20 * ((bad (2*X)).card^4)^5 := by rw [mul_pow, ← pow_mul]
      _ ≤ (Nat.log 2 X / 2)^20 * (((8*C)*X^3)^5) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ha _)
      _ = ((Nat.log 2 X / 2)^20 * (8*C)^5)*X^15 := by ring
      _ ≤ X * X^15 := Nat.mul_le_mul_right _ (hN X hn)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (4 : ℕ) ≠ 0)).mp hw

#print axioms complete_of_power_bound
#print axioms card_fails

end ExceptionUnionBridge
