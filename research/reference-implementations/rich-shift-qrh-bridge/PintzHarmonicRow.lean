import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

namespace PintzHarmonicRow

/-- The one-sided row estimate in Pintz I (8.22). The weights can be
analytic multiplicities, and the local bound is a centered unit-height box. -/
theorem half_row {ι : Type*} (S : Finset ι) (x w : ι → ℝ) (c H C : ℝ)
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hx : ∀ i ∈ S, c ≤ x i ∧ x i - c ≤ H)
    (hlocal : ∀ t : ℝ,
      (∑ i ∈ S.filter (fun i => |x i - t| ≤ 1/2), w i) ≤ C) :
    (∑ i ∈ S, w i / (1 + |x i - c|)) ≤ C * (1 + Real.log (H+1)) := by
  classical
  let n := ⌊H⌋₊ + 1
  let f (i : ι) := ⌊x i-c⌋₊
  have hmaps (i : ι) (hi : i ∈ S) : f i ∈ range n :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (hx i hi).2))
  have hrow (j : ℕ) :
      (∑ i ∈ S.filter (fun i => f i = j), w i / (1 + |x i - c|)) ≤ C * (1+ (j:ℝ))⁻¹ := by
    have hmem (i : ι) (hi : i ∈ S.filter (fun i => f i = j)) :
        (j:ℝ) ≤ x i-c ∧ x i-c < (j:ℝ)+1 := by
      obtain ⟨his, hij⟩ := mem_filter.mp hi
      have hh := sub_nonneg.mpr (hx i his).1
      rw [← hij]
      exact ⟨Nat.floor_le hh, Nat.lt_floor_add_one _⟩
    have hsub : S.filter (fun i => f i = j) ⊆
        S.filter (fun i => |x i - (c+j+1/2)| ≤ 1/2) := by
      intro i hi
      have hj := hmem i hi
      exact mem_filter.mpr ⟨(mem_filter.mp hi).1, abs_le.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩⟩
    calc
      _ ≤ ∑ i ∈ S.filter (fun i => f i = j), w i * (1+ (j:ℝ))⁻¹ := by
        apply sum_le_sum
        intro i hi
        have hiS := (mem_filter.mp hi).1
        rw [abs_of_nonneg (sub_nonneg.mpr (hx i hiS).1), div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          (inv_anti₀ (by positivity) (by linarith [(hmem i hi).1])) (hw i hiS)
      _ = (∑ i ∈ S.filter (fun i => f i = j), w i) * (1+ (j:ℝ))⁻¹ := by rw [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hw i (mem_filter.mp hi).1)).trans
          (hlocal (c+j+1/2))) (by positivity)
  have hn : (n:ℝ) ≤ H+1 := by
    dsimp [n]
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add_left (Nat.floor_le hH) 1
  have hn₀ : (0:ℝ) < n := by exact_mod_cast (Nat.succ_pos ⌊H⌋₊)
  have hhar : (∑ j ∈ range n, (1+ (j:ℝ))⁻¹) = (harmonic n : ℝ) := by
    simp [harmonic, add_comm]
  calc
    _ = ∑ j ∈ range n, ∑ i ∈ S.filter (fun i => f i = j), w i / (1 + |x i - c|) :=
      (sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ j ∈ range n, C * (1+ (j:ℝ))⁻¹ := sum_le_sum (fun j _ => hrow j)
    _ = C * (harmonic n : ℝ) := by rw [← mul_sum, hhar]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((harmonic_le_one_add_log n).trans (add_le_add_right (Real.log_le_log hn₀ hn) 1)) hC

/-- The two-sided harmonic row with multiplicities. -/
theorem full_row {ι : Type*} (S : Finset ι) (x w : ι → ℝ) (c H C : ℝ)
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hx : ∀ i ∈ S, |x i - c| ≤ H)
    (hlocal : ∀ t : ℝ,
      (∑ i ∈ S.filter (fun i => |x i - t| ≤ 1/2), w i) ≤ C) :
    (∑ i ∈ S, w i / (1 + |x i - c|)) ≤ 2 * C * (1 + Real.log (H+1)) := by
  classical
  let A := S.filter (fun i => c ≤ x i)
  let B := S.filter (fun i => ¬ c ≤ x i)
  have ha : (∑ i ∈ A, w i / (1 + |x i - c|)) ≤ C * (1 + Real.log (H+1)) :=
    half_row A x w c H C hH hC (fun i hi => hw i (mem_filter.mp hi).1)
      (fun i hi => ⟨(mem_filter.mp hi).2, (abs_le.mp (hx i (mem_filter.mp hi).1)).2⟩)
      (by
        intro t
        refine (sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (hlocal t)
        · intro i hi
          exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hi).1).1, (mem_filter.mp hi).2⟩
        · intro i hi _
          exact hw i (mem_filter.mp hi).1)
  have hb' := half_row B (fun i => -x i) w (-c) H C hH hC
    (fun i hi => hw i (mem_filter.mp hi).1)
    (fun i hi => ⟨by linarith [lt_of_not_ge (mem_filter.mp hi).2],
      by linarith [(abs_le.mp (hx i (mem_filter.mp hi).1)).1]⟩)
    (by
      intro t
      refine (sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (hlocal (-t))
      · intro i hi
        have he : x i - (-t) = -(-x i - t) := by ring
        exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hi).1).1,
          by rw [he,abs_neg]; exact (mem_filter.mp hi).2⟩
      · intro i hi _
        exact hw i (mem_filter.mp hi).1)
  have hb : (∑ i ∈ B, w i / (1 + |x i - c|)) ≤ C * (1 + Real.log (H+1)) := by
    simpa only [neg_sub_neg, abs_sub_comm c] using hb'
  calc
    _ = (∑ i ∈ A, w i / (1 + |x i - c|)) + ∑ i ∈ B, w i / (1 + |x i - c|) :=
      (sum_filter_add_sum_filter_not S (fun i => c ≤ x i) _).symm
    _ ≤ _ := by linarith only [add_le_add ha hb]

/-- A unit-box bound need only hold for centers within half a unit of the
actual height cutoff. The row gains just one harmonic logarithm. -/
theorem row_at_height {ι : Type*} (S : Finset ι) (x w : ι → ℝ) (c T C : ℝ)
    (hT : 0 ≤ T) (hc : |c| ≤ T) (hC : 0 ≤ C)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hx : ∀ i ∈ S, |x i| ≤ T)
    (hlocal : ∀ t : ℝ, |t| ≤ T+1/2 →
      (∑ i ∈ S.filter (fun i => |x i - t| ≤ 1/2), w i) ≤ C) :
    (∑ i ∈ S, w i / (1 + |x i - c|)) ≤ 2 * C * (1 + Real.log (2*T+1)) := by
  classical
  refine full_row S x w c (2*T) C (by positivity) hC hw ?_ ?_
  · intro i hi
    simpa only [two_mul] using (abs_sub (x i) c).trans (add_le_add (hx i hi) hc)
  · intro t
    by_cases ht : |t| ≤ T+1/2
    · exact hlocal t ht
    · have he : S.filter (fun i => |x i-t| ≤ 1/2) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hs, hd⟩ := mem_filter.mp hi
        have hh : |t| ≤ |x i| + |x i-t| := calc
          _ = |x i - (x i - t)| := by rw [sub_sub_cancel]
          _ ≤ _ := abs_sub _ _
        exact ht (hh.trans (add_le_add (hx i hs) hd))
      rw [he,sum_empty]
      exact hC

#print axioms row_at_height
#print axioms full_row
#print axioms half_row
end PintzHarmonicRow
