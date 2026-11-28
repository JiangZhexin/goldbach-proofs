import PintzDensityBlockBudget
import PintzDensityCutoffBridge

open Finset PintzDyadicStripCount PintzSieveToHybrid

namespace PintzWeightedNonprincipalCount

/-- Density bound with conductor and ordinate cutoffs instantiated at the
parameters of a single dyadic block. The factor 1/M is the window weight. -/
theorem weighted_count {N P R M T b σ : ℝ} {Q : ℕ} (hQ : 1 ≤ Q)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRP : R ≤ P) (hM : 1 ≤ M)
    (hMN : M ≤ N^(1/2:ℝ)) (hPN : P ≤ N^(21/100:ℝ))
    (hT : 0 ≤ T) (hQR : (Q:ℝ) ≤ 2*R) (hTM : T ≤ 2*P*M/R)
    (hb : 0 < b) (hσ : (39/50:ℝ) ≤ σ) (hcd : σ ≤ 1-b)
    (A : PintzDyadicStripCount.Char → Finset ℂ) (w : PintzDyadicStripCount.Char → ℂ → ℕ)
    (hpt : ∀ j ∈ family Q, ∀ ρ ∈ A j, |ρ.im| ≤ T)
    (B : ℕ) (hLocal : ∀ j ∈ family Q, ∀ x,
      ∑ ρ ∈ (A j).filter (fun ρ => |-ρ.im-x| ≤ 1/2), w j ρ ≤ B)
    (hβ : ∀ j ∈ family Q, ∀ ρ ∈ A j, ρ.re ∈ Set.Icc σ (1-b))
    (hnp : ∀ j ∈ family Q, ∀ ρ ∈ A j, j.2 ≠ 1)
    (hz : ∀ j ∈ family Q, ∀ ρ ∈ A j, j.2.LFunction ρ = 0)
    (hq : ∀ j ∈ family Q, j.1+1 ≤ Q) :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      (J:ℝ) ≤ PintzDensityCutoffBridge.detectorConstant b * (P^3*M^2)^(13/10:ℝ) ∧
      let K := (Nat.log 2 (J/L)).succ
      let c := min 1 ((2:ℝ)^b-1)/2
      M⁻¹ * N ^ (-2*(1-σ)) *
        (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ)) ≤
        (1584*(B:ℝ)*(K:ℝ)^2/c^2)*(1+Real.log (2*J:ℝ))^7 *
          (PintzDensityCutoffBridge.detectorConstant b)^(11/25:ℝ) * N ^ (-(1-σ)/40) := by
  obtain ⟨L,J,hL,hLJ,hBal,hJ,hC,hCut⟩ :=
    PintzDensityCutoffBridge.cutoffs hR hRP hM hT hQR hTM hb
  refine ⟨L,J,hL,hLJ,hJ,?_⟩
  dsimp only
  have ht' (j) (hj : j ∈ family Q) (ρ) (hr : ρ ∈ A j) :
      -ρ.im ∈ Set.Icc (-T) T := by
    rw [Set.mem_Icc, ← abs_le, abs_neg]
    exact hpt j hj ρ hr
  have hcut (j) (hj : j ∈ family Q) (ρ) (hr : ρ ∈ A j) :
      (4*(L:ℝ)*(9*(((j.1+1:ℕ):ℝ)*(1+‖ρ‖/ρ.re))+1) /
        min 1 ((2:ℝ)^b-1))^(13/10:ℝ) ≤ (J:ℝ) :=
    hCut (j.1+1) ρ (hq j hj) (hpt j hj ρ hr) (hσ.trans (hβ j hj ρ hr).1)
      (by have := (hβ j hj ρ hr).2; linarith)
  have hc := PintzDensityBlockBudget.global_finite_count hQ hL hLJ hT
    hBal A w ht' B hLocal hb hσ hcd hβ hnp hz hcut
  dsimp only at hc
  have hp := PintzDensityExponentArithmetic.cutoff_budget_h40 hN hM
    (show 0 ≤ P by linarith) (Nat.cast_nonneg (α := ℝ) J) hC hMN hPN
    (show 0 ≤ 1-σ by linarith) (show 1-σ ≤ 11/50 by linarith) hJ
  let V := (1584*(B:ℝ)*(((Nat.log 2 (J/L)).succ:ℕ):ℝ)^2 /
    (min 1 ((2:ℝ)^b-1)/2)^2)*(1+Real.log (2*J:ℝ))^7
  have hlog : 0 ≤ 1 + Real.log (2*J:ℝ) := by
    apply le_trans (by norm_num : (0:ℝ) ≤ 1)
    have hj : (2:ℝ) ≤ J := by exact_mod_cast hL.trans hLJ
    linarith [Real.log_nonneg (show (1:ℝ) ≤ 2*J by linarith)]
  change _ ≤ V * PintzDensityCutoffBridge.detectorConstant b^(11/25:ℝ) * N^(-(1-σ)/40)
  change _ ≤ V * _ at hc
  calc
    _ ≤ M⁻¹ * N ^ (-2*(1-σ)) * (V*(J:ℝ)^(2*(1-σ))) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = V * (M⁻¹ * N ^ (-2*(1-σ)) * (J:ℝ)^(2*(1-σ))) := by ring
    _ ≤ V * (PintzDensityCutoffBridge.detectorConstant b ^ (11/25:ℝ) *
          N ^ (-(1-σ)/40)) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

#print axioms weighted_count
end PintzWeightedNonprincipalCount
