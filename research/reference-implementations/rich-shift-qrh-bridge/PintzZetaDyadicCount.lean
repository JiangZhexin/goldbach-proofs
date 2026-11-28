import PintzDensityBlockBudget
import PintzZetaDetectorAssembly

open Finset PintzSieveToHybrid PintzHybridDiscrete PintzHybridStrip
open PintzDensityBlockBudget
open PintzDyadicDetectorCounting PintzDyadicPolynomial PintzDyadicStripCount

namespace PintzZetaDyadicCount

/-- Finite weighted count for true primitive nonprincipal zeros, with
arithmetic detector cutoff and unit local count made explicit. -/
theorem hybrid_detector_count {Q : ℕ} (hQ : 1 ≤ Q) {L J K : ℕ}
    (hL : 2 ≤ L) (hLJ : L ≤ J) (hJ : J ≤ scale L K)
    {T : ℝ} (hT : 0 ≤ T) (A : PintzDyadicStripCount.Char → Finset ℂ) (w : PintzDyadicStripCount.Char → ℂ → ℕ)
    (hpt : ∀ j ∈ family Q, ∀ ρ ∈ A j, -ρ.im ∈ Set.Icc (-T) T)
    (B : ℕ) (hLocal : ∀ j ∈ family Q, ∀ x,
      ∑ ρ ∈ (A j).filter (fun ρ => |-ρ.im-x| ≤ 1/2), w j ρ ≤ B)
    {b σ : ℝ} (hb : 0 < b) (hσ : (39/50:ℝ) ≤ σ) (hcd : σ ≤ 1-b)
    (hβ : ∀ j ∈ family Q, ∀ ρ ∈ A j, ρ.re ∈ Set.Icc σ (1-b))
    (hdet : ∀ j ∈ family Q, ∀ ρ ∈ A j,
      min 1 ((2:ℝ)^b-1)/2 ≤
        ‖∑ n ∈ Ioc L J, PintzDetectorHead.twist j.2 ρ n * PintzDetectorFinite.coeff L n‖) :
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
    exact hdet _ hj _ hρ
  have H := weighted_count S (range K) (fun p => w p.1 p.2) z hc hd
  simp only [S, sum_sigma, card_range] at H
  refine H.trans (mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => ?_) (by positivity))
  have hU : 1 ≤ scale L k := by
    have hs := scale_mono L (Nat.zero_le k)
    simp [scale] at hs ⊢
    omega
  exact block_energy hQ hU L J hT A w hpt B hLocal (by linarith) hcd hβ

theorem hybrid_global_finite_count {Q : ℕ} (hQ : 1 ≤ Q) {L J : ℕ}
    (hL : 2 ≤ L) (hLJ : L ≤ J) {T : ℝ} (hT : 0 ≤ T)
    (hbal : (T+1)*(Q:ℝ)^2 ≤ L)
    (A : PintzDyadicStripCount.Char → Finset ℂ) (w : PintzDyadicStripCount.Char → ℂ → ℕ)
    (hpt : ∀ j ∈ family Q, ∀ ρ ∈ A j, -ρ.im ∈ Set.Icc (-T) T)
    (B : ℕ) (hLocal : ∀ j ∈ family Q, ∀ x,
      ∑ ρ ∈ (A j).filter (fun ρ => |-ρ.im-x| ≤ 1/2), w j ρ ≤ B)
    {b σ : ℝ} (hb : 0 < b) (hσ : (39/50:ℝ) ≤ σ) (hcd : σ ≤ 1-b)
    (hβ : ∀ j ∈ family Q, ∀ ρ ∈ A j, ρ.re ∈ Set.Icc σ (1-b))
    (hdet : ∀ j ∈ family Q, ∀ ρ ∈ A j,
      min 1 ((2:ℝ)^b-1)/2 ≤
        ‖∑ n ∈ Ioc L J, PintzDetectorHead.twist j.2 ρ n * PintzDetectorFinite.coeff L n‖) :
    let K := (Nat.log 2 (J/L)).succ
    let c := min 1 ((2:ℝ)^b-1)/2
    (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ)) ≤
      (1584*(B:ℝ)*(K:ℝ)^2/c^2)*(1+Real.log (2*J:ℝ))^7*(J:ℝ)^(2*(1-σ)) := by
  let K := (Nat.log 2 (J/L)).succ
  let c := min 1 ((2:ℝ)^b-1)/2
  rcases dyadic_cover (by omega : 1 ≤ L) hLJ with ⟨hJK,hU⟩
  have hM := hybrid_detector_count hQ hL hLJ hJK hT A w hpt B hLocal hb hσ hcd
    hβ hdet
  let F := fun U k : ℕ => kernel B Q T U * (2*energyMajorant U k σ + energyMajorant U (k+1) σ)
  let V := 1584*(B:ℝ)*(1+Real.log (2*J:ℝ))^7*(J:ℝ)^(2*(1-σ))
  have hS : (∑ k ∈ range K, (F (scale L k) 0 +
      (1-b-σ)*(F (scale L k) 0 + F (scale L k) 1))) ≤ (K:ℝ)*V := by
    calc
      _ ≤ ∑ k ∈ range K, V := by
        apply sum_le_sum
        intro k hk
        let U := scale L k
        have hmin : L ≤ U := by simpa [U,scale] using scale_mono L (Nat.zero_le k)
        have hbig : U ≤ J := hU k (mem_range.mp hk)
        have hU1 : 1 ≤ U := by omega
        have hUR : (1:ℝ) ≤ U := by exact_mod_cast hU1
        have H := block_budget (B := B) hQ hU1 hT
          (hbal.trans (by exact_mod_cast hmin))
          (show 0 ≤ 1-b-σ by linarith) (show 1-b-σ ≤ 1 by linarith)
        apply H.trans
        have hURJ : (U:ℝ) ≤ J := by exact_mod_cast hbig
        have hlog := Real.log_le_log (show 0 < (2*U:ℝ) by linarith)
          (show (2*U:ℝ) ≤ 2*J by linarith)
        have hlogpos : 0 ≤ 1+Real.log (2*U:ℝ) := by
          linarith [Real.log_nonneg (show (1:ℝ) ≤ 2*(U:ℝ) by linarith)]
        have hp := Real.rpow_le_rpow (show (0:ℝ) ≤ U by positivity) hURJ
          (show 0 ≤ 2*(1-σ) by linarith)
        have hl : (1+Real.log (2*U:ℝ))^7 ≤ (1+Real.log (2*J:ℝ))^7 :=
          pow_le_pow_left₀ hlogpos (add_le_add le_rfl hlog) _
        dsimp [V]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hl (by positivity)) hp
          (by positivity) (mul_nonneg (by positivity) (hlogpos |> fun h => (pow_nonneg h (7:ℕ)).trans hl))
      _ = _ := by simp
  change (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ)) ≤ _
  change (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ)) ≤
    ((K:ℝ)/c^2)*(∑ k ∈ range K, (F (scale L k) 0 +
      (1-b-σ)*(F (scale L k) 0 + F (scale L k) 1))) at hM
  apply hM.trans
  calc
    _ ≤ ((K:ℝ)/c^2)*((K:ℝ)*V) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by dsimp [V,K,c]; ring


#print axioms hybrid_detector_count
#print axioms hybrid_global_finite_count
end PintzZetaDyadicCount
