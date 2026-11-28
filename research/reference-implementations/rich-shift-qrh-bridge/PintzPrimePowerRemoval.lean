import PintzWeilPrimeDesmoothing
import Mathlib.NumberTheory.Chebyshev

open Finset ArithmeticFunction

namespace PintzPrimePowerRemoval

/-- Absolute error in removing all higher prime powers, with any twist
bounded by one and on any subset of the cutoff interval. -/
theorem finite_weighted {y : ℝ} (hy : 1 ≤ y) (s : Finset ℕ)
    (hs : s ⊆ Ioc 0 ⌊y⌋₊) (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) :
    ‖(∑ n ∈ s, (vonMangoldt n:ℂ)*w n) -
      ∑ n ∈ s.filter Nat.Prime, (Real.log n:ℂ)*w n‖ ≤ 2*Real.sqrt y*Real.log y := by
  classical
  have he : (∑ n ∈ s, (vonMangoldt n:ℂ)*w n) -
      ∑ n ∈ s.filter Nat.Prime, (Real.log n:ℂ)*w n =
      ∑ n ∈ s.filter (fun n => ¬n.Prime), (vonMangoldt n:ℂ)*w n := by
    have hePrime : (∑ n ∈ s.filter Nat.Prime, (vonMangoldt n:ℂ)*w n) =
        ∑ n ∈ s.filter Nat.Prime, (Real.log n:ℂ)*w n := by
      refine sum_congr rfl ?_
      intro n hn
      rw [vonMangoldt_apply_prime (mem_filter.mp hn).2]
    rw [← sum_filter_add_sum_filter_not s Nat.Prime, hePrime]
    abel
  rw [he]
  calc
    _ ≤ ∑ n ∈ s.filter (fun n => ¬n.Prime), ‖(vonMangoldt n:ℂ)*w n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s.filter (fun n => ¬n.Prime), vonMangoldt n := by
      apply sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_of_le_one_right vonMangoldt_nonneg (hw n)
    _ ≤ ∑ n ∈ (Ioc 0 ⌊y⌋₊).filter (fun n => ¬n.Prime), vonMangoldt n :=
      sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hs)
        (fun _ _ _ => vonMangoldt_nonneg)
    _ ≤ _ := by
      rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime]
      exact Chebyshev.psi_sub_theta_le hy

theorem sharp_weighted {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) :
    ‖(∑' n : ℕ, (vonMangoldt n:ℂ)*w n*(PintzWeilPrimeDesmoothing.sharp x y n:ℂ)) -
      ∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (Real.log n:ℂ)*w n‖ ≤ 2*Real.sqrt y*Real.log y := by
  classical
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hmem (n : ℕ) : n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊ ↔ x < (n:ℝ) ∧ (n:ℝ) ≤ y := by
    rw [mem_Ioc, Nat.floor_lt hx0, Nat.le_floor_iff hy0]
  rw [tsum_eq_sum (s := Ioc ⌊x⌋₊ ⌊y⌋₊) (fun n hn => by
    have hd : ¬ (x < (n:ℝ) ∧ (n:ℝ) ≤ y) := fun h => hn ((hmem n).2 h)
    rw [PintzWeilPrimeDesmoothing.sharp, if_neg hd, Complex.ofReal_zero, mul_zero])]
  have H : (∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊,
      (vonMangoldt n:ℂ)*w n*(PintzWeilPrimeDesmoothing.sharp x y n:ℂ)) =
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (vonMangoldt n:ℂ)*w n := by
    apply sum_congr rfl
    intro n hn
    simp [PintzWeilPrimeDesmoothing.sharp,(hmem n).1 hn]
  rw [H]
  exact finite_weighted (hx.trans hxy) _ (Ioc_subset_Ioc_left (Nat.zero_le _)) w hw

#print axioms finite_weighted
#print axioms sharp_weighted
end PintzPrimePowerRemoval
