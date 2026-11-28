import PintzZetaDyadicCount
import PintzDensityCutoffBridge

open Finset PintzSieveToHybrid

namespace PintzWeightedZetaCount

noncomputable def principal : PintzDyadicStripCount.Char :=
  ⟨0, (1 : DirichletCharacter ℂ 1)⟩

theorem principal_mem : principal ∈ family 1 := by
  classical
  rw [family, mem_sigma]
  exact ⟨by decide, mem_filter.mpr ⟨mem_univ _, by
    simp [principal, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]⟩⟩

/-- Conducter-one version of the finite dyadic density estimate, with ζ's
analytic zeros and arbitrary natural multiplicity weights. -/
theorem weighted_count {N P M T b σ : ℝ}
    (hN : 1 ≤ N) (hP : 1 ≤ P) (hM : 1 ≤ M)
    (hMN : M ≤ N^(1/2:ℝ)) (hPN : P ≤ N^(21/100:ℝ))
    (hT : 0 ≤ T) (hTM : T ≤ 2*P*M)
    (hb : 0 < b) (hσ : (39/50:ℝ) ≤ σ) (hcd : σ ≤ 1-b)
    (S : Finset ℂ) (w : ℂ → ℕ)
    (hpt : ∀ ρ ∈ S, |ρ.im| ≤ T)
    (B : ℕ) (hLocal : ∀ x, ∑ ρ ∈ S.filter (fun ρ => |-ρ.im-x| ≤ 1/2), w ρ ≤ B)
    (hβ : ∀ ρ ∈ S, ρ.re ∈ Set.Icc σ (1-b))
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      (J:ℝ) ≤ PintzDensityCutoffBridge.detectorConstant b * (P^3*M^2)^(13/10:ℝ) ∧
      let K := (Nat.log 2 (J/L)).succ
      let c := min 1 ((2:ℝ)^b-1)/2
      M⁻¹ * N ^ (-2*(1-σ)) * (∑ ρ ∈ S, (w ρ:ℝ)) ≤
        (1584*(B:ℝ)*(K:ℝ)^2/c^2)*(1+Real.log (2*J:ℝ))^7 *
          (PintzDensityCutoffBridge.detectorConstant b)^(11/25:ℝ) * N ^ (-(1-σ)/40) := by
  classical
  obtain ⟨L,J,hL,hLJ,hBal,hJ,hC,hCut⟩ :=
    PintzDensityCutoffBridge.cutoffs (R := 1) (Q := 1) le_rfl hP hM hT
      (by norm_num) (by simpa using hTM) hb
  refine ⟨L,J,hL,hLJ,hJ,?_⟩
  dsimp only
  let A (j : PintzDyadicStripCount.Char) := if j = principal then S else ∅
  have hm (j) (ρ : ℂ) (hr : ρ ∈ A j) : j = principal ∧ ρ ∈ S := by
    by_cases hj : j = principal <;> simp_all [A]
  have ht' (j) (_ : j ∈ family 1) (ρ) (hr : ρ ∈ A j) :
      -ρ.im ∈ Set.Icc (-T) T := by
    rw [Set.mem_Icc, ← abs_le, abs_neg]
    exact hpt ρ (hm j ρ hr).2
  have hLoc' (j) (_ : j ∈ family 1) (x : ℝ) :
      ∑ ρ ∈ (A j).filter (fun ρ => |-ρ.im-x| ≤ 1/2), w ρ ≤ B := by
    by_cases hj : j = principal
    · simpa [A, hj] using hLocal x
    · simp [A, hj]
  have hβ' (j) (_ : j ∈ family 1) (ρ) (hr : ρ ∈ A j) :
      ρ.re ∈ Set.Icc σ (1-b) := hβ ρ (hm j ρ hr).2
  have hdet (j) (_ : j ∈ family 1) (ρ) (hr : ρ ∈ A j) :
      min 1 ((2:ℝ)^b-1)/2 ≤
        ‖∑ n ∈ Ioc L J, PintzDetectorHead.twist j.2 ρ n * PintzDetectorFinite.coeff L n‖ := by
    obtain ⟨rfl,hρ⟩ := hm j ρ hr
    have hlo := hσ.trans (hβ ρ hρ).1
    have hhi := (hβ ρ hρ).2
    have hcut := hCut 1 ρ le_rfl (hpt ρ hρ) hlo (by linarith)
    exact PintzZetaDetectorAssembly.zeta_detector (hz ρ hρ) hb hlo hhi hL hLJ
      (by simpa using hcut)
  have hc := PintzZetaDyadicCount.hybrid_global_finite_count (Q := 1) le_rfl
    hL hLJ hT hBal A (fun _ => w) ht' B hLoc' hb hσ hcd hβ' hdet
  dsimp only at hc
  have hsum : (∑ j ∈ family 1, ∑ ρ ∈ A j, (w ρ:ℝ)) = ∑ ρ ∈ S, (w ρ:ℝ) := by
    rw [Finset.sum_eq_single_of_mem principal principal_mem]
    · simp [A]
    · intro j _ hj
      simp [A, hj]
  rw [hsum] at hc
  have hp := PintzDensityExponentArithmetic.cutoff_budget_h40 hN hM
    (show 0 ≤ P by linarith) (Nat.cast_nonneg (α := ℝ) J) hC hMN hPN
    (show 0 ≤ 1-σ by linarith) (show 1-σ ≤ 11/50 by linarith) hJ
  let V := (1584*(B:ℝ)*(((Nat.log 2 (J/L)).succ:ℕ):ℝ)^2 /
    (min 1 ((2:ℝ)^b-1)/2)^2)*(1+Real.log (2*J:ℝ))^7
  have hlog : 0 ≤ 1 + Real.log (2*J:ℝ) := by
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
end PintzWeightedZetaCount
