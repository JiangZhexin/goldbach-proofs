import PintzDetectorFinite
import PintzDetectorCutoff
import Mathlib.Tactic.Linarith

open Finset
namespace PintzDetectorBound
open PintzDetectorFinite

theorem head_value {L : ℕ} (hL : 2 ≤ L) (g : ℕ → ℂ) :
    (∑ n ∈ Icc 1 L, g n * coeff L n) = g 1 - 2*g 2 := by
  classical
  calc
    _ = ∑ n ∈ Icc 1 L, ((if n = 1 then g n else 0) -
        2*(if n = 2 then g n else 0)) := by
      apply sum_congr rfl
      intro n hn
      rw [coeff_head (mem_Icc.mp hn).1 (mem_Icc.mp hn).2]
      by_cases h1 : n = 1 <;> by_cases h2 : n = 2 <;> simp [h1,h2,mul_comm]
    _ = _ := by
      rw [sum_sub_distrib,← mul_sum]
      have h1 : 1 ∈ Icc 1 L := mem_Icc.mpr ⟨by decide, by omega⟩
      have h2 : 2 ∈ Icc 1 L := mem_Icc.mpr ⟨by decide, hL⟩
      simp [h1,h2]

theorem full_bound {L J : ℕ} (hLJ : L ≤ J) (g : ℕ → ℂ)
    (hg : ∀ d k, g (d*k) = g d * g k)
    {β B : ℝ} (hβ : 0 ≤ β) (hβ₁ : β ≤ 1) (hB : 0 ≤ B)
    (hdecay : ∀ d ∈ Icc 1 L, ‖g d‖ ≤ (d:ℝ)^(-β))
    (htail : ∀ d ∈ Icc 1 L,
      ‖∑ k ∈ Icc 1 (J/d), g k * alternation k‖ ≤ B*((J/d : ℕ):ℝ)^(-β)) :
    ‖∑ n ∈ Icc 1 J, g n * coeff L n‖ ≤ 2*B*L*(J:ℝ)^(-β) := by
  rw [detector_product L J g hg]
  calc
    _ ≤ ∑ d ∈ Icc 1 L, ‖g d * (ArithmeticFunction.moebius d : ℂ) *
        (∑ k ∈ Icc 1 (J/d), g k * alternation k)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ Icc 1 L, 2*B*(J:ℝ)^(-β) := by
      apply sum_le_sum
      intro d hd
      have hm : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        norm_cast
        exact ArithmeticFunction.abs_moebius_le_one
      apply PintzDetectorCutoff.tail_cancellation (mem_Icc.mp hd).1
        ((mem_Icc.mp hd).2.trans hLJ) hβ hβ₁ hB
      · calc
          _ ≤ ‖g d‖ := by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hm
          _ ≤ _ := hdecay d hd
      · exact htail d hd
    _ = _ := by simp; ring

theorem detector_lower {L J : ℕ} (hL : 2 ≤ L) (hLJ : L ≤ J) (g : ℕ → ℂ)
    {b : ℝ}
    (hhead : b ≤ ‖g 1 - 2*g 2‖)
    (hfull : ‖∑ n ∈ Icc 1 J, g n * coeff L n‖ ≤ b/2) :
    b/2 ≤ ‖∑ n ∈ Ioc L J, g n * coeff L n‖ := by
  let f : ℕ → ℂ := fun n => g n * coeff L n
  have hd : Disjoint (Icc 1 L) (Ioc L J) := by
    apply disjoint_left.mpr
    intro n ha hb
    exact ((mem_Ioc.mp hb).1.not_ge (mem_Icc.mp ha).2)
  have he : Icc 1 L ∪ Ioc L J = Icc 1 J := by
    ext n
    simp only [mem_union,mem_Icc,mem_Ioc]
    omega
  have hsplit : (∑ n ∈ Icc 1 J, f n) = (∑ n ∈ Icc 1 L, f n) + ∑ n ∈ Ioc L J, f n := by
    rw [← he,sum_union hd]
  have hh : g 1 - 2*g 2 = (∑ n ∈ Icc 1 J, f n) - ∑ n ∈ Ioc L J, f n := by
    rw [hsplit,add_sub_cancel_right]
    exact (head_value hL g).symm
  rw [hh] at hhead
  have hb := hhead.trans (norm_sub_le (∑ n ∈ Icc 1 J, f n) (∑ n ∈ Ioc L J, f n))
  change ‖∑ n ∈ Icc 1 J, f n‖ ≤ b/2 at hfull
  change b / 2 ≤ ‖∑ n ∈ Ioc L J, f n‖
  linarith

#print axioms head_value
#print axioms full_bound
#print axioms detector_lower
end PintzDetectorBound
