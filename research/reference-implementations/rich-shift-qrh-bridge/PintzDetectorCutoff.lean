import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace PintzDetectorCutoff

open Finset

/-- Floor loss is at most a factor two for every divisor in the shortened product. -/
theorem div_lower {J d : ℕ} (hd : 0 < d) (hJ : d ≤ J) :
    (J : ℝ) ≤ 2 * (d : ℝ) * ((J/d : ℕ) : ℝ) := by
  have hK : 1 ≤ J/d := Nat.div_pos hJ hd
  have hdK : d ≤ d*(J/d) := Nat.le_mul_of_pos_right _ hK
  have hrem : J%d ≤ d*(J/d) := (Nat.mod_lt _ hd).le.trans hdK
  have he := Nat.mod_add_div J d
  have hs : J ≤ 2*d*(J/d) := by
    calc
      J = J%d+d*(J/d) := he.symm
      _ ≤ d*(J/d)+d*(J/d) := Nat.add_le_add_right hrem _
      _ = _ := by ring
  exact_mod_cast hs

/-- The norm envelope of an outer Möbius summand times its inner tail.
The divisor cancels, leaving only the final cutoff. -/
theorem tail_cancellation {J d : ℕ} (hd : 0 < d) (hJ : d ≤ J)
    {β B : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) (hB : 0 ≤ B)
    (u v : ℂ) (hu : ‖u‖ ≤ (d:ℝ)^(-β))
    (hv : ‖v‖ ≤ B*((J/d : ℕ):ℝ)^(-β)) :
    ‖u*v‖ ≤ 2*B*(J:ℝ)^(-β) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hJR : (0:ℝ) < J := by exact_mod_cast hd.trans_le hJ
  have hkR : (0:ℝ) < (J/d : ℕ) := by exact_mod_cast Nat.div_pos hJ hd
  have h := div_lower hd hJ
  have htwo : (2:ℝ)^β ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hβ'
  have hdprod : (J:ℝ)/2 ≤ (d:ℝ)*((J/d : ℕ):ℝ) := by linarith
  have hP := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < (J:ℝ)/2)
    hdprod (neg_nonpos.mpr hβ)
  rw [Real.div_rpow hJR.le (by norm_num : (0:ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    div_inv_eq_mul] at hP
  calc
    ‖u*v‖ ≤ (d:ℝ)^(-β) * (B * ((J/d : ℕ):ℝ)^(-β)) := by
      rw [norm_mul]
      exact mul_le_mul hu hv (norm_nonneg _) (by positivity)
    _ = B*((d:ℝ)*((J/d : ℕ):ℝ))^(-β) := by rw [Real.mul_rpow hdR.le hkR.le]; ring
    _ ≤ B*((J:ℝ)^(-β)*(2:ℝ)^β) := mul_le_mul_of_nonneg_left hP hB
    _ ≤ _ := by
      calc
        _ ≤ B*((J:ℝ)^(-β)*2) := by gcongr
        _ = _ := by ring

/-- The chosen cutoff makes the full truncated product uniformly small
as soon as the real part is at least 39/50. -/
theorem cutoff_decay {A B J β : ℝ} (hA : 0 < A) (hAB : 1 ≤ A*B)
    (hβ : (39/50:ℝ) ≤ β) (hJ : (A*B)^(13/10:ℝ) ≤ J) :
    B * J^(-β) ≤ 1/A := by
  have hp : 0 < A*B := lt_of_lt_of_le zero_lt_one hAB
  have hpJ : 0 < J := (Real.rpow_pos_of_pos hp _).trans_le hJ
  have hβp : 0 ≤ β := by linarith
  have hv : A*B ≤ J^β := calc
    _ ≤ (A*B)^((13/10:ℝ)*β) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hAB (show 1 ≤ (13/10:ℝ)*β by linarith)
    _ = ((A*B)^(13/10:ℝ))^β := Real.rpow_mul hp.le _ _
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hJ hβp
  rw [Real.rpow_neg hpJ.le, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hpJ _) hA).2
  simpa [mul_comm] using hv

#print axioms cutoff_decay
#print axioms div_lower
#print axioms tail_cancellation
end PintzDetectorCutoff
