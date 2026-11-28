import PintzDensityBlockBudget
import OAI.NumberTheory.Ostmann.Arithmetic.DivisorSquareMean

open Finset PintzSieveToHybrid PintzHybridDiscrete PintzHybridStrip
open PintzDyadicDetectorCounting PintzDyadicPolynomial PintzDyadicStripCount PintzDensityBlockBudget
noncomputable section
namespace RichShiftGenericSampler263
set_option maxHeartbeats 800000

theorem energy {U : ℕ} (hU : 1 ≤ U) (L J k : ℕ) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ n.divisors.card) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑ n ∈ (Ioc U (2*U)).filter (fun n => L < n ∧ n ≤ J),
        ‖reScale a σ n‖ ^ 2 * (Real.log n) ^ (2*k)) ≤
      2 * (1 + Real.log (2*U : ℝ)) ^ (3+2*k) * (U:ℝ) ^ (1-2*σ) := by
  have hUR : (1:ℝ) ≤ U := by exact_mod_cast hU
  have hUp : (0:ℝ) < U := by positivity
  let Z : ℝ := 1 + Real.log (2*U:ℝ)
  have hZ : 0 ≤ Z := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 2*U by linarith)
    dsimp [Z]; linarith
  let C : ℝ := (U:ℝ)^(-2*σ) * Z^(2*k)
  have hc : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ n ∈ (Ioc U (2*U)).filter (fun n => L < n ∧ n ≤ J),
        C * (n.divisors.card:ℝ)^2 := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hnU, hn2⟩ := mem_Ioc.mp (mem_filter.mp hn).1
      have hnU' : (U:ℝ) ≤ n := by exact_mod_cast hnU.le
      have hn2' : (n:ℝ) ≤ 2*U := by exact_mod_cast hn2
      have hnp : (0:ℝ) < n := hUp.trans_le hnU'
      have hn1 : (1:ℝ) ≤ n := hUR.trans hnU'
      have hl : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
      have hlZ : Real.log (n:ℝ) ≤ Z := (Real.log_le_log hnp hn2').trans
        (by dsimp [Z]; linarith)
      have hpow : (n:ℝ)^(-2*σ) ≤ (U:ℝ)^(-2*σ) :=
        Real.rpow_le_rpow_of_nonpos hUp hnU' (by linarith)
      have hdiv := pow_le_pow_left₀ (norm_nonneg _) (ha n) 2
      have hlog := pow_le_pow_left₀ hl hlZ (2*k)
      have heq : Real.exp (-σ * Real.log n)^2 = (n:ℝ)^(-2*σ) := by
        rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos hnp]
        congr 1
        ring
      rw [reScale, norm_mul, Complex.norm_exp, mul_pow]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, mul_zero, sub_zero]
      rw [heq]
      dsimp [C]
      calc
        _ ≤ ((n.divisors.card:ℝ)^2 * (U:ℝ)^(-2*σ)) * Z^(2*k) :=
          mul_le_mul (mul_le_mul hdiv hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity))
            hlog (by positivity) (by positivity)
        _ = _ := by ring
    _ ≤ C * ((2*U:ℝ) * Z^3) := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ hc
      refine (sum_le_sum_of_subset_of_nonneg (t := Icc 1 (2*U)) ?_ (fun n _ _ => by positivity)).trans ?_
      · intro n hn
        obtain ⟨hnU, hn2⟩ := mem_Ioc.mp (mem_filter.mp hn).1
        exact mem_Icc.mpr ⟨by omega, hn2⟩
      · simpa [Z] using OAI.Ostmann.Arithmetic.DivisorSquareMean.divisor_square_mean (2*U)
    _ = _ := by
      dsimp [C]
      rw [show (1-2*σ : ℝ) = 1+(-2*σ) by ring, Real.rpow_add hUp, Real.rpow_one, pow_add]
      dsimp [Z]
      ring

theorem block_energy {Q : ℕ} (hQ : 1 ≤ Q) {U : ℕ} (hU : 1 ≤ U)
    (L J : ℕ) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ n.divisors.card) {T : ℝ} (hT : 0 ≤ T)
    (A : PintzDyadicStripCount.Char → Finset ℂ) (w : PintzDyadicStripCount.Char → ℂ → ℕ)
    (hpt : ∀ j ∈ family Q, ∀ ρ ∈ A j, -ρ.im ∈ Set.Icc (-T) T)
    (B : ℕ) (hLocal : ∀ j ∈ family Q, ∀ x,
      ∑ ρ ∈ (A j).filter (fun ρ => |-ρ.im - x| ≤ 1/2), w j ρ ≤ B)
    {σ d : ℝ} (hσ : 0 ≤ σ) (hcd : σ ≤ d)
    (hβ : ∀ j ∈ family Q, ∀ ρ ∈ A j, ρ.re ∈ Set.Icc σ d) :
    let s := (Ioc U (2*U)).filter (fun n => L < n ∧ n ≤ J)
    let F := fun k : ℕ => kernel B Q T U *
      (2*energyMajorant U k σ + energyMajorant U (k+1) σ)
    (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ) * ‖P s (reScale a ρ.re) j (-ρ.im)‖^2) ≤
      F 0 + (d-σ)*(F 0 + F 1) := by
  dsimp only
  let s := (Ioc U (2*U)).filter (fun n => L < n ∧ n ≤ J)
  have hs (n) (hn : n ∈ s) : 0 < n ∧ (n:ℝ) ≤ 2*(U:ℝ) := by
    obtain ⟨h1,h2⟩ := mem_Ioc.mp (mem_filter.mp hn).1
    exact ⟨by omega, by exact_mod_cast h2⟩
  let E (b : ℕ → ℂ) := kernel B Q T U *
      (2 * (∑ n ∈ s, ‖reScale b σ n‖^2) + ∑ n ∈ s, ‖logCoeff (reScale b σ) n‖^2)
  let F (k : ℕ) := kernel B Q T U * (2 * energyMajorant U k σ + energyMajorant U (k+1) σ)
  have H : (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ) * ‖P s (reScale a ρ.re) j (-ρ.im)‖^2)
      ≤ E a + (d-σ)*(E a + E (reCoeff a)) :=
    PintzHybridOverlap.weighted_strip_energy hQ s a hT hs A
      (fun _ ρ => -ρ.im) (fun _ ρ => ρ.re) w hpt B hLocal hcd hβ
  have En (k : ℕ) : (∑ n ∈ s, ‖reScale a σ n‖^2 * Real.log n ^ (2*k)) ≤ energyMajorant U k σ :=
    energy hU L J k a ha hσ
  have hf (n) (hn : n ∈ s) : 0 ≤ Real.log (n:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (hs n hn).1)
  have hw : 0 ≤ kernel B Q T U := by unfold kernel; positivity
  have hc (n) (hn : n ∈ s) : ‖reScale (reCoeff a) σ n‖ = ‖reScale a σ n‖ * Real.log n := by
    simp only [reScale, reCoeff, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf n hn)]
    ring
  have hl (b : ℕ → ℂ) (n) (hn : n ∈ s) :
      ‖logCoeff (reScale b σ) n‖ = ‖reScale b σ n‖ * Real.log n := by
    simp only [logCoeff, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf n hn), one_mul]
  have hE : E a ≤ F 0 := by
    apply mul_le_mul_of_nonneg_left _ hw
    apply add_le_add
    · simpa using mul_le_mul_of_nonneg_left (En 0) (by norm_num : (0:ℝ) ≤ 2)
    · convert En 1 using 1
      apply sum_congr rfl
      intro n hn
      rw [hl a n hn, mul_pow]
  have hE' : E (reCoeff a) ≤ F 1 := by
    apply mul_le_mul_of_nonneg_left _ hw
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      convert En 1 using 1
      apply sum_congr rfl
      intro n hn
      rw [hc n hn, mul_pow]
    · convert En 2 using 1
      apply sum_congr rfl
      intro n hn
      rw [hl _ n hn, hc n hn]
      ring
  exact H.trans (add_le_add hE
    (mul_le_mul_of_nonneg_left (add_le_add hE hE') (sub_nonneg.mpr hcd)))

theorem zero_count {Q : ℕ} (hQ : 1 ≤ Q) {L J K : ℕ}
    (hL : 2 ≤ L) (hJ : J ≤ scale L K)
    {T : ℝ} (hT : 0 ≤ T) (A : PintzDyadicStripCount.Char → Finset ℂ) (w : PintzDyadicStripCount.Char → ℂ → ℕ)
    (hpt : ∀ j ∈ family Q, ∀ ρ ∈ A j, -ρ.im ∈ Set.Icc (-T) T)
    (B : ℕ) (hLocal : ∀ j ∈ family Q, ∀ x,
      ∑ ρ ∈ (A j).filter (fun ρ => |-ρ.im-x| ≤ 1/2), w j ρ ≤ B)
    {σ d c : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ) (hcd : σ ≤ d)
    (hβ : ∀ j ∈ family Q, ∀ ρ ∈ A j, ρ.re ∈ Set.Icc σ d)
    (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ n.divisors.card)
    (hdet : ∀ j ∈ family Q, ∀ ρ ∈ A j,
      c ≤ ‖∑ n ∈ Ioc L J, PintzDetectorHead.twist j.2 ρ n*a n‖) :
    let F := fun U k : ℕ => kernel B Q T U *
      (2*energyMajorant U k σ + energyMajorant U (k+1) σ)
    (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ)) ≤
      ((K:ℝ) / (c)^2) *
        (∑ k ∈ range K, (F (scale L k) 0 +
          (d-σ)*(F (scale L k) 0 + F (scale L k) 1))) := by
  classical
  dsimp only
  let S := (family Q).sigma A
  let z (p : Σ _ : PintzDyadicStripCount.Char, ℂ) (k : ℕ) :=
    P (block L J k) (reScale a p.2.re) p.1 (-p.2.im)
  have hd (p : Σ _ : PintzDyadicStripCount.Char, ℂ) (hp : p ∈ S) : c ≤ ‖∑ k ∈ range K, z p k‖ := by
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
  exact block_energy hQ hU L J a ha hT A w hpt B hLocal hσ hcd hβ

theorem global_finite_count {Q : ℕ} (hQ : 1 ≤ Q) {L J : ℕ}
    (hL : 2 ≤ L) (hLJ : L ≤ J) {T : ℝ} (hT : 0 ≤ T)
    (hbal : (T+1)*(Q:ℝ)^2 ≤ L)
    (A : PintzDyadicStripCount.Char → Finset ℂ) (w : PintzDyadicStripCount.Char → ℂ → ℕ)
    (hpt : ∀ j ∈ family Q, ∀ ρ ∈ A j, -ρ.im ∈ Set.Icc (-T) T)
    (B : ℕ) (hLocal : ∀ j ∈ family Q, ∀ x,
      ∑ ρ ∈ (A j).filter (fun ρ => |-ρ.im-x| ≤ 1/2), w j ρ ≤ B)
    {σ d c : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ) (hcd : σ ≤ d) (hd : d ≤ 1)
    (hβ : ∀ j ∈ family Q, ∀ ρ ∈ A j, ρ.re ∈ Set.Icc σ d)
    (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ n.divisors.card)
    (hdet : ∀ j ∈ family Q, ∀ ρ ∈ A j,
      c ≤ ‖∑ n ∈ Ioc L J, PintzDetectorHead.twist j.2 ρ n*a n‖) :
    let K := (Nat.log 2 (J/L)).succ
    (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ)) ≤
      (1584*(B:ℝ)*(K:ℝ)^2/c^2)*(1+Real.log (2*J:ℝ))^7*(J:ℝ)^(2*(1-σ)) := by
  let K := (Nat.log 2 (J/L)).succ
  rcases dyadic_cover (by omega : 1 ≤ L) hLJ with ⟨hJK,hU⟩
  have hM := zero_count hQ hL hJK hT A w hpt B hLocal hc hσ hcd hβ a ha hdet
  let F := fun U k : ℕ => kernel B Q T U * (2*energyMajorant U k σ + energyMajorant U (k+1) σ)
  let V := 1584*(B:ℝ)*(1+Real.log (2*J:ℝ))^7*(J:ℝ)^(2*(1-σ))
  have hS : (∑ k ∈ range K, (F (scale L k) 0 +
      (d-σ)*(F (scale L k) 0 + F (scale L k) 1))) ≤ (K:ℝ)*V := by
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
          (show 0 ≤ d-σ by linarith) (show d-σ ≤ 1 by linarith)
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
      (d-σ)*(F (scale L k) 0 + F (scale L k) 1))) at hM
  apply hM.trans
  calc
    _ ≤ ((K:ℝ)/c^2)*((K:ℝ)*V) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by dsimp [V,K]; ring

#print axioms global_finite_count
end RichShiftGenericSampler263
