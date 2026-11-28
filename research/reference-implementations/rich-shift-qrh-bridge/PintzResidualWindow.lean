import PintzDiscreteZeroModel

open Finset PintzDiscreteZeroModel

namespace PintzResidualWindow

/-- Move from a pointwise sharp-interval explicit formula to the precise
sequence fed into Gallagher. Here K is the retained pole/near-zero model
and F is the omitted zero primitive, with its natural positive sign. -/
theorem estimate {p : ℕ → ℂ} {K F : ℝ → ℂ} {u v x Y E R : ℝ}
    (hu : 1 ≤ u) (hE : 0 ≤ E) (hR : 0 ≤ R)
    (hK : ∀ t, 1 ≤ t → ‖K t - K (⌊t⌋₊:ℕ)‖ ≤ R)
    (hformula : ∀ a b : ℝ, u ≤ a → a ≤ b → b ≤ v →
      ‖((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, p n)) - (K b - K a) + (F b - F a)‖ ≤ E) :
    let B := (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) ≤ x+Y)
    let J := if max u x ≤ min v (x+Y) then F (min v (x+Y)) - F (max u x) else 0
    ‖((∑ n ∈ B, (p n - increment K n))) + J‖ ≤ E+2*R := by
  dsimp only
  rw [sum_sub_distrib]
  let a := max u x
  let b := min v (x+Y)
  let B := (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) ≤ x+Y)
  change ‖((∑ n ∈ B, p n) - (∑ n ∈ B, increment K n)) +
    (if a ≤ b then F b - F a else 0)‖ ≤ _
  have hB : B = Ioc ⌊a⌋₊ ⌊b⌋₊ := filter_clipped u v x Y (by linarith)
  have hKr := clipped_increments (F := K) (v := v) (x := x) (Y := Y) hu hR hK
  change ‖(∑ n ∈ B, increment K n) - (if a ≤ b then K b - K a else 0)‖ ≤ _ at hKr
  split_ifs with h
  · rw [if_pos h] at hKr
    let S := ∑ n ∈ B, p n
    let D := ∑ n ∈ B, increment K n
    change ‖S-D+(F b-F a)‖ ≤ E+2*R
    have hS := hformula a b (le_max_left _ _) h (min_le_left _ _)
    rw [← hB] at hS
    change ‖S-(K b-K a)+(F b-F a)‖ ≤ E at hS
    rw [show S-D+(F b-F a) =
      (S-(K b-K a)+(F b-F a)) - (D-(K b-K a)) by ring]
    exact (norm_sub_le _ _).trans (add_le_add hS hKr)
  · rw [hB, Ioc_eq_empty_of_le (Nat.floor_mono (le_of_not_ge h))]
    simp [show 0 ≤ E+2*R by positivity]

#print axioms estimate
end PintzResidualWindow
