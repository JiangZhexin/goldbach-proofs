import PintzDyadicNonprincipalCount
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Log

open Finset PintzDyadicStripCount PintzDyadicDetectorCounting PintzDyadicPolynomial PintzSieveToHybrid

namespace PintzDensityBlockBudget

/-- Balance the length and conductor terms in the proven hybrid sieve. -/
theorem kernel_budget {B Q U : ℕ} (hQ : 1 ≤ Q) {T : ℝ} (hT : 0 ≤ T)
    (hU : (T+1)*(Q:ℝ)^2 ≤ U) :
    kernel B Q T U ≤ 88*(B:ℝ)*(U:ℝ) := by
  have hTp : 0 < T+1 := by linarith
  have hqr : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hqs : (1:ℝ) ≤ (Q:ℝ)^2 := by nlinarith
  have hk : T+1 ≤ U := (le_mul_of_one_le_right hTp.le hqs).trans hU
  have hf : (⌊(U:ℝ)*(2*Real.pi/(T+1))⌋₊:ℝ) ≤ (U:ℝ)*(2*Real.pi/(T+1)) :=
    Nat.floor_le (by positivity)
  have hpi : Real.pi^2/2 ≤ (8:ℝ) := by nlinarith [Real.pi_lt_four,Real.pi_pos]
  have hP : Real.pi^2*(T+1)/2 ≤ 8*(T+1) := by
    nlinarith only [mul_le_mul_of_nonneg_right hpi hTp.le]
  have hC : (T+1)*((U:ℝ)*(2*Real.pi/(T+1))) ≤ 8*U := by
    rw [show (T+1)*((U:ℝ)*(2*Real.pi/(T+1))) = (2*Real.pi)*U by
      field_simp [hTp.ne']]
    exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) (by positivity)
  unfold kernel
  change (B:ℝ)*_ ≤ _
  calc
    _ ≤ (B:ℝ)*(8*(T+1)*((U:ℝ)*(2*Real.pi/(T+1))+1+2*(Q:ℝ)^2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      apply mul_le_mul hP _ (by positivity) (by positivity)
      linarith [hf]
    _ ≤ (B:ℝ)*(88*(U:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      nlinarith only [hC,hk,hU]
    _ = _ := by ring

/-- Collapse a dyadic block to the explicit power of U that appears in
the global zero-density upper bound. The exponent does not depend on B. -/
theorem block_budget {B Q U : ℕ} (hQ : 1 ≤ Q) (hU1 : 1 ≤ U)
    {T : ℝ} (hT : 0 ≤ T) (hU : (T+1)*(Q:ℝ)^2 ≤ U)
    {σ d : ℝ} (hs : 0 ≤ d-σ) (hd : d-σ ≤ 1) :
    let F := fun k : ℕ => kernel B Q T U *
      (2*energyMajorant U k σ + energyMajorant U (k+1) σ)
    F 0 + (d-σ)*(F 0 + F 1) ≤
      1584*(B:ℝ)*(1+Real.log (2*U:ℝ))^7*(U:ℝ)^(2*(1-σ)) := by
  dsimp only
  let L := 1+Real.log (2*U:ℝ)
  let A := (U:ℝ)^(1-2*σ)
  have hU' : (1:ℝ) ≤ U := by exact_mod_cast hU1
  have hU0 : (0:ℝ) < U := by linarith
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ 2*(U:ℝ))]
  have hL0 : 0 ≤ L := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE (k : ℕ) (hk : k ≤ 2) :
      energyMajorant U k σ ≤ 2 * L^7 * A := by
    have hh := pow_le_pow_right₀ hL (by omega : 3+2*k ≤ 7)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num)) hA
  have hz (k : ℕ) : 0 ≤ energyMajorant U k σ := by
    change 0 ≤ 2*L^(3+2*k)*A
    positivity
  let V := 88*(B:ℝ)*(U:ℝ)*(6*L^7*A)
  have hBp (k : ℕ) (hk : k ≤ 1) :
      kernel B Q T U * (2*energyMajorant U k σ + energyMajorant U (k+1) σ) ≤ V := by
    have H0 := hE k (by omega)
    have H1 := hE (k+1) (by omega)
    exact mul_le_mul (kernel_budget hQ hT hU) (by linarith)
      (by linarith [hz k,hz (k+1)]) (by positivity)
  have hV : 0 ≤ V := by change 0 ≤ 88*(B:ℝ)*(U:ℝ)*(6*L^7*A); positivity
  have h0 := hBp 0 (by decide)
  have h1 := hBp 1 (by decide)
  have hPow : (U:ℝ)*A = (U:ℝ)^(2*(1-σ)) := by
    calc
      _ = (U:ℝ)^(1:ℝ) * (U:ℝ)^(1-2*σ) := by rw [Real.rpow_one]
      _ = (U:ℝ)^(2*(1-σ)) := by rw [← Real.rpow_add hU0]; congr 1; ring
  calc
    _ ≤ V+(d-σ)*(V+V) :=
      add_le_add h0 (mul_le_mul_of_nonneg_left (add_le_add h0 h1) hs)
    _ ≤ V+1*(V+V) := add_le_add le_rfl (mul_le_mul_of_nonneg_right hd (by positivity))
    _ = _ := by
      change V+1*(V+V) = 1584*(B:ℝ)*L^7*(U:ℝ)^(2*(1-σ))
      rw [← hPow]
      dsimp [V]
      ring

/-- Choose the exact finite dyadic cover, with all occupied block
scales no larger than the detector cutoff. -/
theorem dyadic_cover {L J : ℕ} (hL : 1 ≤ L) (hLJ : L ≤ J) :
    let K := (Nat.log 2 (J/L)).succ
    J ≤ scale L K ∧ ∀ k < K, scale L k ≤ J := by
  dsimp only
  have hf : 1 ≤ J/L := Nat.div_pos hLJ hL
  constructor
  · have H := Nat.lt_pow_succ_log_self (by decide : 1 < (2:ℕ)) (J/L)
    exact (by
      rw [scale,mul_comm]
      exact ((Nat.div_lt_iff_lt_mul hL).mp H).le)
  · intro k hk
    have H : 2^k ≤ J/L := Nat.pow_le_of_le_log (by omega) (by omega)
    exact (Nat.mul_le_mul_left L H).trans (Nat.mul_div_le J L)

/-- Summing the proven block-energy bound costs only the square of
the number of blocks. No nonexplicit big-O or zero-density assumption
is used in this final finite simplification. -/
theorem global_finite_count {Q : ℕ} (hQ : 1 ≤ Q) {L J : ℕ}
    (hL : 2 ≤ L) (hLJ : L ≤ J) {T : ℝ} (hT : 0 ≤ T)
    (hbal : (T+1)*(Q:ℝ)^2 ≤ L)
    (A : PintzDyadicStripCount.Char → Finset ℂ) (w : PintzDyadicStripCount.Char → ℂ → ℕ)
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
    let K := (Nat.log 2 (J/L)).succ
    let c := min 1 ((2:ℝ)^b-1)/2
    (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ)) ≤
      (1584*(B:ℝ)*(K:ℝ)^2/c^2)*(1+Real.log (2*J:ℝ))^7*(J:ℝ)^(2*(1-σ)) := by
  let K := (Nat.log 2 (J/L)).succ
  let c := min 1 ((2:ℝ)^b-1)/2
  rcases dyadic_cover (by omega : 1 ≤ L) hLJ with ⟨hJK,hU⟩
  have hM := PintzDyadicNonprincipalCount.zero_count hQ hL hLJ hJK hT A w hpt B hLocal hb hσ hcd
    hβ hnp hz hcut
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

#print axioms dyadic_cover
#print axioms global_finite_count
#print axioms kernel_budget
#print axioms block_budget
end PintzDensityBlockBudget
