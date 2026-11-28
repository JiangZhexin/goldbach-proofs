import PintzJutilaMollifierTail
import PintzJutilaLogRamp

open Finset PintzJutilaAnalytic PintzJutilaPseudo
noncomputable section

namespace PintzJutilaDetectorSplit

def detectorTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (ξ : ℕ → ℂ)
    (ρ : ℂ) (X : ℝ) (r n : ℕ) : ℂ :=
  LSeries.term (twisted (fun n => χ n) ξ r) ρ n * (Real.exp (-(n:ℝ)/X):ℂ)

def averageDetector {q : ℕ} (χ : DirichletCharacter ℂ q) (ξ : ℕ → ℂ)
    (ρ : ℂ) (X : ℝ) (S : Finset ℕ) : ℂ :=
  ∑ r ∈ S, ((r:ℂ)⁻¹) * ∑' n, detectorTerm χ ξ ρ X r n

def core {q : ℕ} (χ : DirichletCharacter ℂ q) (ξ : ℕ → ℂ)
    (ρ : ℂ) (X z₁ x : ℝ) (S : Finset ℕ) : ℂ :=
  ∑ r ∈ S, ((r:ℂ)⁻¹) * ∑ n ∈ Ioc ⌊z₁⌋₊ ⌊x⌋₊, detectorTerm χ ξ ρ X r n

def main (X : ℝ) (S : Finset ℕ) : ℂ :=
  (Real.exp (-1/X):ℂ) * ∑ r ∈ S, (r:ℂ)⁻¹

theorem single_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z₁ z₂ x X : ℝ} (hz₁ : 1 ≤ z₁) (hz₂ : z₁ < z₂) (hzx : z₁ ≤ x)
    (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 ≤ ρ.re) {r : ℕ} (hr : r ≠ 0) :
    let f := detectorTerm χ (PintzJutilaLogRamp.coeff z₁ z₂) ρ X r
    Summable f ∧
    ‖(r:ℂ)⁻¹ * ((∑' n, f n) -
      ((Real.exp (-1/X):ℂ) + ∑ n ∈ Ioc ⌊z₁⌋₊ ⌊x⌋₊, f n))‖ ≤
      20*X^2*Real.exp (-x/(2*X)) := by
  classical
  dsimp only
  let f := detectorTerm χ (PintzJutilaLogRamp.coeff z₁ z₂) ρ X r
  let g (n : ℕ) := if x < n then (r:ℂ)⁻¹ * f n else 0
  let top := Icc 1 ⌊x⌋₊
  let init (n : ℕ) := if n ∈ top then f n else 0
  have H := PintzJutilaMollifierTail.truncated_tail_simple χ
    (PintzJutilaLogRamp.coeff z₁ z₂)
    (PintzJutilaLogRamp.coeff_norm (by linarith) hz₂) hρ hr (x := x) hX
  have hn (n : ℕ) : ‖g n‖ =
      (if x < n then (r:ℝ)⁻¹ *
        ‖LSeries.term (twisted (fun n => χ n) (PintzJutilaLogRamp.coeff z₁ z₂) r) ρ n‖ *
          Real.exp (-(n:ℝ)/X) else 0) := by
    unfold g f detectorTerm
    split_ifs
    · rw [norm_mul, norm_inv, Complex.norm_natCast, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), mul_assoc]
    · exact norm_zero
  have hg : Summable g := summable_norm_iff.mp (by simpa only [hn] using H.1)
  have hf0 : f 0 = 0 := by simp [f, detectorTerm]
  have hi : HasSum init (∑ n ∈ top, f n) := by
    have H : HasSum init (∑ n ∈ top, init n) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => ite_eq_right hn)
    convert H using 1
    exact sum_congr rfl (fun n hn => (ite_eq_left hn).symm)
  have hfun : f = fun n => init n + (r:ℂ)*g n := by
    funext n
    by_cases hx : x < n
    · have ht : n ∉ top := fun ht => (not_le_of_gt hx)
        ((by exact_mod_cast (mem_Icc.mp ht).2 : (n:ℝ) ≤ (⌊x⌋₊:ℕ)).trans
          (Nat.floor_le (by linarith)))
      dsimp [init,g]
      rw [ite_eq_right ht, ite_eq_left hx, zero_add, ← mul_assoc,
        mul_inv_cancel₀ (by exact_mod_cast hr), one_mul]
    · rw [show g n = 0 from ite_eq_right hx, mul_zero, add_zero]
      by_cases hn0 : n = 0
      · subst n
        simp [init, hf0]
      · have ht : n ∈ top := mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn0, Nat.le_floor (le_of_not_gt hx)⟩
        exact (ite_eq_left ht).symm
  have hfS : HasSum f ((∑ n ∈ top, f n) + (r:ℂ)*∑' n, g n) := by
    have H : HasSum (fun n => init n + (r:ℂ)*g n)
        ((∑ n ∈ top, f n) + (r:ℂ)*∑' n, g n) := hi.add (hg.hasSum.mul_left (r:ℂ))
    rwa [← hfun] at H
  have hL : ⌊z₁⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hzx
  have hL1 : 1 ≤ ⌊z₁⌋₊ := Nat.le_floor (by simpa using hz₁)
  have hinit : (∑ n ∈ top, f n) =
      (Real.exp (-1/X):ℂ) + ∑ n ∈ Ioc ⌊z₁⌋₊ ⌊x⌋₊, f n := by
    have hpart : (Icc 1 ⌊z₁⌋₊) ∪ (Ioc ⌊z₁⌋₊ ⌊x⌋₊) = top := by
      ext n
      simp only [top,mem_union,mem_Icc,mem_Ioc]
      omega
    have hdis : Disjoint (Icc 1 ⌊z₁⌋₊) (Ioc ⌊z₁⌋₊ ⌊x⌋₊) := by
      apply disjoint_left.mpr
      intro n hn hm
      exact (not_lt_of_ge (mem_Icc.mp hn).2) (mem_Ioc.mp hm).1
    rw [← hpart, sum_union hdis, sum_eq_single_of_mem 1 (mem_Icc.mpr ⟨le_rfl,hL1⟩)]
    · have H := PintzJutilaLogRamp.divisor_short (n := 1) (z₂ := z₂) (by decide)
        (by simpa using hz₁)
      simp at H
      simp [f, detectorTerm, twisted, H, psi]
    · intro n hn hn1
      have hle : (n:ℝ) ≤ z₁ := (by exact_mod_cast (mem_Icc.mp hn).2 :
        (n:ℝ) ≤ (⌊z₁⌋₊:ℕ)).trans (Nat.floor_le (by linarith))
      have hpos : 0 < n := (mem_Icc.mp hn).1
      have H := PintzJutilaLogRamp.divisor_short (z₂ := z₂) hpos hle
      simp [f, detectorTerm, LSeries.term_of_ne_zero hpos.ne', twisted, H, hn1]
  refine ⟨hfS.summable,?_⟩
  change ‖(r:ℂ)⁻¹ * ((∑' n, f n) - _)‖ ≤ _
  rw [hfS.tsum_eq, hinit, add_sub_cancel_left, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hr), one_mul]
  exact (norm_tsum_le_tsum_norm (summable_norm_iff.mpr hg)).trans (by simpa only [hn] using H.2)

theorem average_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z₁ z₂ x X : ℝ} (hz₁ : 1 ≤ z₁) (hz₂ : z₁ < z₂) (hzx : z₁ ≤ x)
    (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 ≤ ρ.re) (S : Finset ℕ) (hS : 0 ∉ S) :
    let ξ := PintzJutilaLogRamp.coeff z₁ z₂
    ‖averageDetector χ ξ ρ X S - (main X S + core χ ξ ρ X z₁ x S)‖ ≤
      20*(S.card:ℝ)*X^2*Real.exp (-x/(2*X)) := by
  dsimp only [averageDetector, main, core]
  rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ r ∈ S, 20*X^2*Real.exp (-x/(2*X)) := by
      apply sum_le_sum
      intro r hr
      have hnr : r ≠ 0 := fun h => hS (h ▸ hr)
      have H := (single_split χ hz₁ hz₂ hzx hX hρ hnr).2
      rw [mul_sub,mul_add,mul_comm (r:ℂ)⁻¹ (Real.exp (-1/X):ℂ)] at H
      exact H
    _ = _ := by simp; ring

#print axioms single_split
#print axioms average_split
end PintzJutilaDetectorSplit
