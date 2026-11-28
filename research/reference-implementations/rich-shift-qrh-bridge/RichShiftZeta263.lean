import PintzWeightedZetaCount
import PintzActualWeightedZeta
import PintzUniformDensityLog

open Finset PintzSieveToHybrid PintzWeightedZetaCount

namespace RichShiftZeta263

theorem raw_bound {T b σ : ℝ}
    (hT : 0 ≤ T) (hb : 0 < b) (hσ : (39/50:ℝ) ≤ σ) (hcd : σ ≤ 1-b)
    (S : Finset ℂ) (w : ℂ → ℕ)
    (hpt : ∀ ρ ∈ S, |ρ.im| ≤ T)
    (B : ℕ) (hLocal : ∀ x, ∑ ρ ∈ S.filter (fun ρ => |-ρ.im-x| ≤ 1/2), w ρ ≤ B)
    (hβ : ∀ ρ ∈ S, ρ.re ∈ Set.Icc σ (1-b))
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      (J:ℝ) ≤ PintzDensityCutoffBridge.detectorConstant b * (1+T)^(13/5:ℝ) ∧
      let K := (Nat.log 2 (J/L)).succ
      let c := min 1 ((2:ℝ)^b-1)/2
      (∑ ρ ∈ S, (w ρ:ℝ)) ≤
        (1584*(B:ℝ)*(K:ℝ)^2/c^2)*(1+Real.log (2*J:ℝ))^7 *
          (J:ℝ)^(2*(1-σ)) := by
  classical
  obtain ⟨L,J,hL,hLJ,hBal,hJ,hC,hCut⟩ :=
    PintzDensityCutoffBridge.cutoffs (P := 1) (M := 1+T) (R := 1) (Q := 1)
      le_rfl le_rfl (by linarith) hT (by norm_num) (by linarith) hb
  have hJ' : (J:ℝ) ≤ PintzDensityCutoffBridge.detectorConstant b * (1+T)^(13/5:ℝ) := by
    refine hJ.trans_eq ?_
    rw [one_pow, one_mul, ← Real.rpow_natCast_mul (by positivity)]
    norm_num
  refine ⟨L,J,hL,hLJ,hJ',?_⟩
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
  exact hc

#print axioms raw_bound
end RichShiftZeta263
