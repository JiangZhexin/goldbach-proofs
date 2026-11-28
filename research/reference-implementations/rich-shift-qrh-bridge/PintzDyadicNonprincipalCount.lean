import PintzDyadicStripCount
import PintzDetectorAssembly

open Finset PintzSieveToHybrid PintzHybridDiscrete PintzHybridStrip
open PintzDyadicDetectorCounting PintzDyadicPolynomial PintzDyadicStripCount

namespace PintzDyadicNonprincipalCount

/-- Finite weighted count for true primitive nonprincipal zeros, with
arithmetic detector cutoff and unit local count made explicit. -/
theorem zero_count {Q : ℕ} (hQ : 1 ≤ Q) {L J K : ℕ}
    (hL : 2 ≤ L) (hLJ : L ≤ J) (hJ : J ≤ scale L K)
    {T : ℝ} (hT : 0 ≤ T) (A : PintzDyadicStripCount.Char → Finset ℂ) (w : PintzDyadicStripCount.Char → ℂ → ℕ)
    (hpt : ∀ j ∈ family Q, ∀ ρ ∈ A j, -ρ.im ∈ Set.Icc (-T) T)
    (B : ℕ) (hLocal : ∀ j ∈ family Q, ∀ x,
      ∑ ρ ∈ (A j).filter (fun ρ => |-ρ.im-x| ≤ 1/2), w j ρ ≤ B)
    {b σ : ℝ} (hb : 0 < b) (hσ : (39/50:ℝ) ≤ σ) (hcd : σ ≤ 1-b)
    (hβ : ∀ j ∈ family Q, ∀ ρ ∈ A j, ρ.re ∈ Set.Icc σ (1-b))
    (hnp : ∀ j ∈ family Q, ∀ ρ ∈ A j, j.2 ≠ 1)
    (hz : ∀ j ∈ family Q, ∀ ρ ∈ A j, j.2.LFunction ρ = 0)
    (hcut : ∀ j ∈ family Q, ∀ ρ ∈ A j,
      (4*(L:ℝ)*(9*(((j.1+1:ℕ):ℝ)*(1+‖ρ‖/ρ.re))+1) /
        min 1 ((2:ℝ)^b-1))^(13/10:ℝ) ≤ (J:ℝ)) :
    let F := fun U k : ℕ => kernel B Q T U *
      (2*energyMajorant U k σ + energyMajorant U (k+1) σ)
    (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ)) ≤
      ((K:ℝ) / (min 1 ((2:ℝ)^b-1)/2)^2) *
        (∑ k ∈ range K, (F (scale L k) 0 +
          (1-b-σ)*(F (scale L k) 0 + F (scale L k) 1))) := by
  classical
  dsimp only
  let S := (family Q).sigma A
  let a := PintzDetectorFinite.coeff L
  let C := min 1 ((2:ℝ)^b-1)/2
  let z (p : Σ _ : PintzDyadicStripCount.Char, ℂ) (k : ℕ) :=
    P (block L J k) (reScale a p.2.re) p.1 (-p.2.im)
  have hc : 0 < C := div_pos (PintzDetectorHead.head_constant_pos hb) (by norm_num)
  have hd (p : Σ _ : PintzDyadicStripCount.Char, ℂ) (hp : p ∈ S) : C ≤ ‖∑ k ∈ range K, z p k‖ := by
    obtain ⟨hj,hρ⟩ := mem_sigma.mp hp
    have hi (k : ℕ) :
        z p k = ∑ n ∈ block L J k, PintzDetectorHead.twist p.1.2 p.2 n * a n := by
      apply P_eq_detector
      intro n hn
      have := (mem_Ioc.mp (mem_filter.mp hn).1).1
      omega
    simp_rw [hi]
    rw [sum_blocks _ L J K hJ]
    exact PintzDetectorAssembly.nonprincipal_detector p.1.2 (hnp _ hj _ hρ) (hz _ hj _ hρ)
      hb (hσ.trans (hβ _ hj _ hρ).1) (hβ _ hj _ hρ).2 hL hLJ (hcut _ hj _ hρ)
  have H := weighted_count S (range K) (fun p => w p.1 p.2) z hc hd
  simp only [S, sum_sigma, card_range] at H
  refine H.trans (mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => ?_) (by positivity))
  have hU : 1 ≤ scale L k := by
    have hs := scale_mono L (Nat.zero_le k)
    simp [scale] at hs ⊢
    omega
  exact block_energy hQ hU L J hT A w hpt B hLocal (by linarith) hcd hβ

#print axioms zero_count
end PintzDyadicNonprincipalCount
