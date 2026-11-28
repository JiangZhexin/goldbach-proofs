import RichShiftBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset
namespace RichShift

noncomputable def lowWeighted (a b : ℕ) (t : ℝ) : Finset ℕ :=
  (Icc a b).filter fun m => Even m ∧ weighted m < t

theorem weighted_dyadic_union (X Y : ℕ) (κ A : ℝ) (hX : 2 ≤ X)
    (hY : Y = X / 2) (hκ : 0 < κ) (hA : 0 ≤ A)
    (hlo : ((lowWeighted Y (2*Y) (κ*Y)).card : ℝ) ≤ A*(Y:ℝ) ^ (37/50:ℝ))
    (hhi : ((lowWeighted X (2*X) (κ*X)).card : ℝ) ≤ A*(X:ℝ) ^ (37/50:ℝ)) :
    ((lowWeighted (X/2) (2*X) ((κ/3)*X)).card : ℝ) ≤
      (2*A)*(X:ℝ) ^ (37/50:ℝ) := by
  have hX3Y : (X:ℝ) ≤ 3*(Y:ℝ) := by
    exact_mod_cast (show X ≤ 3*Y by omega)
  have h3 : (κ/3)*(X:ℝ) ≤ κ*Y := by nlinarith
  have h4 : (κ/3)*(X:ℝ) ≤ κ*X := by nlinarith
  have hs : lowWeighted (X/2) (2*X) ((κ/3)*X) ⊆
      lowWeighted Y (2*Y) (κ*Y) ∪ lowWeighted X (2*X) (κ*X) := by
    intro m hm
    obtain ⟨hmI, hme, hmW⟩ := mem_filter.mp hm
    obtain ⟨hmlo, hmhi⟩ := mem_Icc.mp hmI
    by_cases hmX : m < X
    · exact mem_union_left _ (mem_filter.mpr
        ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hme, hmW.trans_le h3⟩)
    · exact mem_union_right _ (mem_filter.mpr
        ⟨mem_Icc.mpr ⟨by omega, hmhi⟩, hme, hmW.trans_le h4⟩)
  have hmono : (Y:ℝ) ^ (37/50:ℝ) ≤ (X:ℝ) ^ (37/50:ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast (show Y ≤ X by omega)) (by norm_num)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  have hr : ((lowWeighted (X/2) (2*X) ((κ/3)*X)).card : ℝ) ≤
      (lowWeighted Y (2*Y) (κ*Y)).card + (lowWeighted X (2*X) (κ*X)).card := by
    exact_mod_cast hc
  linarith [mul_le_mul_of_nonneg_left hmono hA]

theorem shift_of_dyadic_floor
    (h : ∃ κ A : ℝ, 0 < κ ∧ 0 < A ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
      ((lowWeighted X (2*X) (κ*X)).card : ℝ) ≤ A*(X:ℝ) ^ (37/50:ℝ)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
      ∀ e ∈ Icc 1 (Nat.log 2 X/2),
        (((Ico X (2*X)).filter (fun n => Even n ∧
          ((reps (n-2^e)).card:ℝ) < c*(X:ℝ)/Real.log (X:ℝ)^2)).card : ℝ)
          ≤ C*(X:ℝ) ^ (37/50:ℝ) := by
  obtain ⟨κ, A, hκ, hA, X₀, hb⟩ := h
  refine ⟨(κ/3)/4, 2*A, by positivity, by positivity, 2*(X₀+1), ?_⟩
  intro X hX e he
  have htwo : 2 ≤ X := by omega
  have hbound := weighted_dyadic_union X (X/2) κ A htwo rfl hκ hA.le
      (hb (X/2) (by omega)) (hb X (by omega))
  exact shift_bound_of_weighted htwo he hbound

#print axioms shift_of_dyadic_floor
end RichShift
