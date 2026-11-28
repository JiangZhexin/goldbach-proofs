import PintzPrimePairCoefficient
import PintzMinorPRMoment

open Finset Filter MeasureTheory Set
open ExceptionUnionBridge PintzPrimePairCoefficient

namespace PintzExceptionFinalReduction

noncomputable def actualPrimes (N : ℕ) (a : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊a⌋₊ N).filter Nat.Prime

noncomputable def majorCoeff (N P : ℕ) (a : ℝ) (m : ℕ) : ℂ :=
  ∫ t in majorSet P N, f (actualPrimes N a) (fun n => (Real.log n:ℂ)) m t

theorem minor_coeff_eq (N P : ℕ) (a : ℝ) (m : ℕ) :
    PintzMinorPRMoment.localCoeff N P a m =
      ∫ t in minorSet P N, f (actualPrimes N a) (fun n => (Real.log n:ℂ)) m t := by
  rw [PintzMinorPRMoment.localCoeff_phase]
  have h : -(P:ℝ)/(N:ℝ) ≤ 1-(P:ℝ)/(N:ℝ) := by ring_nf; linarith
  rw [intervalIntegral.integral_of_le h]
  change (∫ t in periodSet P N, (majorSet P N)ᶜ.indicator
    (f (actualPrimes N a) (fun n => (Real.log n:ℂ)) m) t) = _
  rw [setIntegral_indicator (major_measurable P N).compl]
  simp only [minorSet,Set.sdiff_eq_compl_inter,inter_comm]

theorem no_representations {m : ℕ} (h : G m = 0)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) : p+q ≠ m := by
  intro hsum
  have hmem : p ∈ (range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p)) := by
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),hp,by
      rwa [show m-p=q by omega]⟩
  have hG : (0:ℕ) < G m := Finset.card_pos.mpr ⟨p,hmem⟩
  omega

private theorem separated {N P : ℕ} (hN : 4 ≤ N)
    (hcut : (P:ℝ) ≤ (N:ℝ)^(21/100:ℝ)) : 2*(P:ℝ)^2 < (N:ℝ) := by
  have hNR : (4:ℝ) ≤ N := by exact_mod_cast hN
  have h₀ : (0:ℝ) < N := by linarith
  have h₁ : (1:ℝ) < N := by linarith
  have ht : (2:ℝ) < (N:ℝ)^(58/100:ℝ) := by
    apply lt_of_le_of_lt _ (Real.rpow_lt_rpow_of_exponent_lt h₁
      (show (1/2:ℝ) < 58/100 by norm_num))
    rw [← Real.sqrt_eq_rpow,Real.le_sqrt (by norm_num) h₀.le]
    linarith
  have hP : (P:ℝ)^2 ≤ (N:ℝ)^(42/100:ℝ) := calc
    _ ≤ ((N:ℝ)^(21/100:ℝ))^2 := pow_le_pow_left₀ (by positivity) hcut 2
    _ = _ := by rw [← Real.rpow_mul_natCast h₀.le]; norm_num
  calc
    _ ≤ 2*(N:ℝ)^(42/100:ℝ) := mul_le_mul_of_nonneg_left hP (by norm_num)
    _ < (N:ℝ)^(58/100:ℝ)*(N:ℝ)^(42/100:ℝ) := mul_lt_mul_of_pos_right ht (by positivity)
    _ = _ := by rw [← Real.rpow_add h₀]; norm_num

/-- All the outer analytic/counting reduction is now actual, including
the published minor-arc estimate. The only hypothesis is the genuinely
missing lower bound for the major coefficient of the literal polynomial. -/
theorem from_major_lower
    (hMajor : ∀ᶠ j : ℕ in atTop,
      let N : ℕ := 2^(j+1)
      ∃ (P : ℕ) (a : ℝ), 1 ≤ P ∧ (P:ℝ) ≤ (N:ℝ)^(21/100:ℝ) ∧
        (N:ℝ)^(41/200:ℝ) ≤ 2*(P:ℝ) ∧ a ≤ (N:ℝ) ∧
        ∀ m ∈ dyadicBad j, (N:ℝ)^(1-1/1000:ℝ) ≤ (majorCoeff N P a m).re) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (fails X).card^5 ≤ X^4 := by
  have hPows : Tendsto (fun j : ℕ => 2^(j+1)) atTop atTop := by
    exact tendsto_atTop_mono (fun j => Nat.pow_le_pow_right (by decide) (by omega))
      (tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2:ℕ) by decide))
  let C : ℝ := 4*100000^2
  have hC : 0 ≤ C := by positivity
  apply complete_of_eventual_dyadic_log_loss (δ := 797/1000)
    (C := 3*C*2^(797/1000:ℝ)*2^10) (by norm_num) (by norm_num) (by positivity) 10
  filter_upwards [hMajor,hPows.eventually PintzMinorPRMoment.literal_energy_finset,
    eventually_ge_atTop (1:ℕ),hPows.eventually (eventually_ge_atTop (4:ℕ))] with j hM hE hj hN
  let N : ℕ := 2^(j+1)
  let D := dyadicBad j
  obtain ⟨P,a,hP,hcut,hlo,ha,hmain⟩ := hM
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0:ℝ) < N := by linarith
  have hPN : P ≤ N := by
    have hu := Real.rpow_le_rpow_of_exponent_le hN1 (show (21/100:ℝ) ≤ 1 by norm_num)
    change (P:ℝ) ≤ (N:ℝ)^(21/100:ℝ) at hcut
    have hh : (P:ℝ) ≤ N := hcut.trans (by simpa using hu)
    exact_mod_cast hh
  have hSep := separated hN hcut
  have haFloor : ⌊a⌋₊ ≤ N := (Nat.floor_mono ha).trans_eq (Nat.floor_natCast N)
  have hT := hE P a D hP hPN haFloor hSep
  have hco (m : ℕ) (hm : m ∈ D) :
      (N:ℝ)^(1-1/1000:ℝ) ≤ ‖PintzMinorPRMoment.localCoeff N P a m‖ := by
    have hn := (mem_filter.mp hm).2.2.2
    have hNo : ∀ p ∈ actualPrimes N a, ∀ q ∈ actualPrimes N a, p+q ≠ m := fun p hp q hq =>
      no_representations hn (mem_filter.mp hp).2 (mem_filter.mp hq).2
    rw [minor_coeff_eq,minor_eq_neg_major hP hSep _ hNo,norm_neg]
    exact (hmain m hm).trans (Complex.re_le_norm _)
  have hSet : D.filter (fun m => (N:ℝ)^(1-1/1000:ℝ) ≤
      ‖PintzMinorPRMoment.localCoeff N P a m‖) = D :=
    filter_eq_self.mpr hco
  have hh := PintzExceptionalMinorPower.count_above_small_power_threshold
    (PintzMinorPRMoment.localCoeff N P a) (ε := (1/1000:ℝ)) 10 hN1 hlo hC le_rfl hT
  rw [hSet] at hh
  let W := (2:ℝ)^j
  have hW : 0 < W := by dsimp [W]; positivity
  have hW2 : (2:ℝ) ≤ W := by
    have hh := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hj
    simpa [W] using hh
  have hN_eq : (N:ℝ) = 2*W := by
    dsimp [N,W]
    push_cast
    rw [pow_succ,mul_comm]
  have hlog : Real.log (N:ℝ) ≤ 2*Real.log W := by
    rw [hN_eq,Real.log_mul (by norm_num) hW.ne']
    linarith [Real.log_le_log (show (2:ℝ)>0 by norm_num) hW2]
  refine hh.trans ?_
  rw [hN_eq, Real.mul_rpow (by norm_num) hW.le]
  rw [hN_eq] at hlog
  have hlog0 : 0 ≤ Real.log (2*W) := Real.log_nonneg (by nlinarith)
  change _ ≤ (3*C*2^(797/1000:ℝ)*2^10)*W^(797/1000:ℝ)*(Real.log W)^10
  calc
    _ ≤ 3*C*(2^(797/1000:ℝ)*W^(797/1000:ℝ))*(2*Real.log W)^10 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog _) (by positivity)
    _ = _ := by rw [mul_pow] <;> ring

#print axioms minor_coeff_eq
#print axioms no_representations
#print axioms from_major_lower
end PintzExceptionFinalReduction
