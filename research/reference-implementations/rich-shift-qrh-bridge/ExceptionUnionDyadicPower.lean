import ExceptionUnionSharpBridge

open Filter
open scoped BigOperators
namespace ExceptionUnionBridge

def dyadicBad (j : ℕ) : Finset ℕ :=
  (Finset.Ico (2^j) (2^(j+1))).filter (fun n => 4 ≤ n ∧ Even n ∧ G n = 0)

theorem bad_le_dyadic_sum (Y : ℕ) :
    (bad Y).card ≤ ∑ j ∈ Finset.range (Nat.log 2 Y+1), (dyadicBad j).card := by
  classical
  have hi : bad Y ⊆ (Finset.range (Nat.log 2 Y+1)).biUnion dyadicBad := by
    intro n hn
    simp only [bad, Finset.mem_filter, Finset.mem_range] at hn
    have hnY : n ≤ Y := by omega
    have hj := Nat.log_mono_right (b := 2) hnY
    refine Finset.mem_biUnion.mpr ⟨Nat.log 2 n, Finset.mem_range.mpr (by omega), ?_⟩
    unfold dyadicBad
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by decide : 1 < 2) n⟩,
      hn.2⟩
  exact (Finset.card_le_card hi).trans Finset.card_biUnion_le

/-- A fixed real logarithmic loss can be absorbed into any positive power margin. -/
theorem eventual_log_loss {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∀ᶠ X : ℕ in atTop, (Real.log (X : ℝ))^k ≤ (X : ℝ)^ε := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (s := ε) hε).bound (show (0:ℝ) < 1 by norm_num)
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually h, eventually_ge_atTop (1:ℕ)] with X hX h1
  have hp : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast h1
  simpa [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.log_nonneg hp) k), abs_of_nonneg (Real.log_nonneg hp),
    abs_of_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ X) ε)] using hX

/-- Logarithmic losses on ordinary Goldbach exception counts are harmless with a strict exponent margin. -/
theorem complete_of_log_loss {δ C : ℝ} (hδ : δ < 4/5) (hC : 0 ≤ C) (k : ℕ)
    (hcount : ∀ᶠ X : ℕ in atTop,
      ((bad (2*X)).card : ℝ) ≤ C*(X:ℝ)^δ*(Real.log (X:ℝ))^k) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (fails X).card^5 ≤ X^4 := by
  let ε : ℝ := (4/5-δ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  apply complete_of_strict_exception_exponent (δ := δ + ε) (C := C) (by dsimp [ε]; linarith)
  filter_upwards [hcount, eventual_log_loss hε k, eventually_ge_atTop (1:ℕ)] with X hc hl h1
  have hp : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  calc
    _ ≤ C*(X:ℝ)^δ*(Real.log (X:ℝ))^k := hc
    _ ≤ C*(X:ℝ)^δ*(X:ℝ)^ε := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = C*(X:ℝ)^(δ+ε) := by rw [Real.rpow_add hp, mul_assoc]

theorem complete_of_eventual_dyadic_power {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 4/5)
    (hC : 0 ≤ C) (h : ∀ᶠ j : ℕ in atTop,
      ((dyadicBad j).card : ℝ) ≤ C * ((2:ℝ)^j)^δ) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (fails X).card^5 ≤ X^4 := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp h
  let A : ℝ := max C ((2:ℝ)^(J+1))
  have hA : 0 ≤ A := hC.trans (le_max_left _ _)
  have hall (j : ℕ) : ((dyadicBad j).card : ℝ) ≤ A * ((2:ℝ)^j)^δ := by
    by_cases hj : J ≤ j
    · exact (hJ _ hj).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have hcard : (dyadicBad j).card ≤ 2^(j+1) := by
        exact Finset.card_le_card (fun n hn => Finset.mem_range.mpr
          (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).2)
          |>.trans_eq (by simp)
      have hj' : j+1 ≤ J+1 := by omega
      calc
        _ ≤ (2:ℝ)^(j+1) := by exact_mod_cast hcard
        _ ≤ (2:ℝ)^(J+1) := pow_le_pow_right₀ (by norm_num) hj'
        _ ≤ A := le_max_right _ _
        _ ≤ A * ((2:ℝ)^j)^δ := by
          have hpow : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
          simpa using mul_le_mul_of_nonneg_left (Real.one_le_rpow hpow hδ0) hA
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply complete_of_log_loss hδ
    (C := (3/Real.log 2)*A*(2:ℝ)^δ) (by positivity) 1
  filter_upwards [eventually_ge_atTop (2:ℕ)] with X hX
  have hXr : (2:ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : 0 < (X:ℝ) := by positivity
  let L := Nat.log 2 (2*X)
  have hpowL : (2:ℝ)^L ≤ 2*(X:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : 2*X ≠ 0)
  have hlogL : (L:ℝ)*Real.log 2 ≤ Real.log 2 + Real.log (X:ℝ) := by
    have hh := Real.log_le_log (by positivity) hpowL
    rwa [Real.log_pow, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hXpos.ne'] at hh
  have hLL : ((L:ℝ)+1) ≤ 3/Real.log 2 * Real.log (X:ℝ) := by
    have hd := Real.log_le_log (by norm_num : (0:ℝ) < 2) hXr
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hlog2).mpr (by linarith)
  have hblock (j : ℕ) (hj : j ∈ Finset.range (L+1)) :
      ((dyadicBad j).card : ℝ) ≤ A*(2*(X:ℝ))^δ := by
    have hpow : (2:ℝ)^j ≤ 2*(X:ℝ) :=
      (pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hj; omega)).trans hpowL
    exact (hall j).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hpow hδ0) hA)
  calc
    _ ≤ ∑ j ∈ Finset.range (L+1), ((dyadicBad j).card : ℝ) := by
      exact_mod_cast bad_le_dyadic_sum (2*X)
    _ ≤ ∑ _j ∈ Finset.range (L+1), A*(2*(X:ℝ))^δ := Finset.sum_le_sum hblock
    _ = ((L:ℝ)+1)*(A*(2*(X:ℝ))^δ) := by simp
    _ ≤ (3/Real.log 2 * Real.log (X:ℝ))*(A*(2*(X:ℝ))^δ) :=
      mul_le_mul_of_nonneg_right hLL (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hXpos.le, pow_one]; ring

/-- The input can be an eventual dyadic estimate with any fixed logarithmic loss.
In particular the power 159/200 = 0.795 is strictly below the threshold. -/
theorem complete_of_eventual_dyadic_log_loss {δ C : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ < 4/5) (hC : 0 ≤ C) (k : ℕ)
    (h : ∀ᶠ j : ℕ in atTop, ((dyadicBad j).card : ℝ) ≤
       C * ((2:ℝ)^j)^δ * (Real.log ((2:ℝ)^j))^k) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (fails X).card^5 ≤ X^4 := by
  let ε : ℝ := (4/5-δ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hT : Tendsto (fun j : ℕ => (2:ℕ)^j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ))
  apply complete_of_eventual_dyadic_power (δ := δ+ε) (C := C)
    (by positivity) (by dsimp [ε]; linarith) hC
  filter_upwards [h, hT.eventually (eventual_log_loss hε k)] with j hj hk
  have hp : (0:ℝ) < (2:ℝ)^j := by positivity
  have hk' : (Real.log ((2:ℝ)^j))^k ≤ ((2:ℝ)^j)^ε := by
    simpa only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat] using hk
  calc
    _ ≤ C*((2:ℝ)^j)^δ*(Real.log ((2:ℝ)^j))^k := hj
    _ ≤ C*((2:ℝ)^j)^δ*((2:ℝ)^j)^ε := mul_le_mul_of_nonneg_left hk' (by positivity)
    _ = _ := by rw [Real.rpow_add hp, mul_assoc]

/-- The analytic dyadic exponent 0.795 with fixed logarithmic losses meets
the frozen exception-union target, with the original prime representation count. -/
theorem frozen_target_of_dyadic_795 {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (h : ∀ᶠ j : ℕ in atTop, ((dyadicBad j).card : ℝ) ≤
       C * ((2:ℝ)^j)^(159/200:ℝ) * (Real.log ((2:ℝ)^j))^k) :
    let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card
    ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2
    let E := (Finset.Ico X (2*X)).filter
      (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card)
    E.card^5 ≤ X^4 := by
  exact complete_of_eventual_dyadic_log_loss (δ := 159/200) (by norm_num) (by norm_num) hC k h

#print axioms frozen_target_of_dyadic_795
#print axioms complete_of_eventual_dyadic_log_loss
#print axioms complete_of_eventual_dyadic_power
#print axioms bad_le_dyadic_sum
#print axioms complete_of_log_loss
end ExceptionUnionBridge
