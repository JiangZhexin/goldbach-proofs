import PintzEightRegroup

noncomputable section
open Finset MeasureTheory PintzEightEnergy PintzEightConductors PintzEightRegroup
open scoped Classical
namespace PintzEightSummation

theorem regroup_totient (P : ℕ) (E : ℕ → ℝ) :
    (∑ q ∈ Icc 1 P, ∑ r ∈ q.divisors,
        if (q / r).Coprime r then (r : ℝ) / (q.totient : ℝ) * E r else 0) =
      ∑ r ∈ Icc 1 P,
        ((r : ℝ) / (r.totient : ℝ) * ∑ l ∈ (Icc 1 (P/r)).filter (·.Coprime r),
           (1 : ℝ) / (l.totient : ℝ)) * E r := by
  calc
    _ = ∑ q ∈ Icc 1 P, ∑ r ∈ Icc 1 P,
        if r ∣ q then (if (q/r).Coprime r then (r : ℝ) / (q.totient : ℝ) * E r else 0) else 0 := by
      apply sum_congr rfl
      intro q hq
      rw [← sum_filter (s := Icc 1 P)]
      congr 1
      ext r
      have hqp : 0 < q := (mem_Icc.mp hq).1
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      exact ⟨fun hd => ⟨⟨Nat.pos_of_dvd_of_pos hd.1 hqp, (Nat.le_of_dvd hqp hd.1).trans (mem_Icc.mp hq).2⟩, hd.1⟩, fun h => ⟨h.2, hqp.ne'⟩⟩
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r hr
      have hrp : 0 < r := (mem_Icc.mp hr).1
      simp_rw [mul_assoc, sum_mul, mul_sum]
      rw [← sum_filter, ← sum_filter]
      rw [filter_filter]
      symm
      apply sum_bij (fun l _ => l * r)
      · intro l hl
        obtain ⟨hl', hc⟩ := mem_filter.mp hl
        obtain ⟨hlp, hlu⟩ := mem_Icc.mp hl'
        rw [mem_filter, mem_Icc]
        exact ⟨⟨Nat.mul_pos hlp hrp, (Nat.le_div_iff_mul_le hrp).mp hlu⟩,
          ⟨dvd_mul_left r l, by simpa [Nat.mul_div_cancel _ hrp] using hc⟩⟩
      · intro l _ k _ hk
        exact Nat.eq_of_mul_eq_mul_right hrp hk
      · intro q hq
        obtain ⟨hq', hd, hc⟩ := mem_filter.mp hq
        obtain ⟨hqp, hqu⟩ := mem_Icc.mp hq'
        refine ⟨q/r, mem_filter.mpr ⟨mem_Icc.mpr
          ⟨Nat.div_pos (Nat.le_of_dvd hqp hd) hrp, Nat.div_le_div_right hqu⟩, hc⟩, Nat.div_mul_cancel hd⟩
      · intro l hl
        have hc := (mem_filter.mp hl).2
        rw [Nat.totient_mul hc, Nat.cast_mul]
        ring

#print axioms regroup_totient
end PintzEightSummation
