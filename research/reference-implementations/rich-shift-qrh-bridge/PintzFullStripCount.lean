import PintzZeroReflection
import PintzLocalDirichlet

open Finset

namespace PintzFullStripCount

/-- The explicit local multiplicity bound on both halves of the critical
strip. The left half uses the inverse primitive character at ordinate -t. -/
theorem local_count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (t : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, 0 < z.re ∧ z.re < 1 ∧ |z.im-t| ≤ 1/2) :
    (∑ z ∈ S, ((analyticOrderAt χ.LFunction z).toNat : ℝ)) ≤
      2 * (Real.log (12 * q * (|t|+6)) / Real.log (55/52)) := by
  classical
  let f : ℂ → ℝ := fun z => (analyticOrderNatAt χ.LFunction z : ℝ)
  let R := S.filter (fun z => 1/2 ≤ z.re)
  let L := S.filter (fun z => ¬ 1/2 ≤ z.re)
  have hR : (∑ z ∈ R, f z) ≤ Real.log (12*q*(|t|+6))/Real.log (55/52) := by
    apply PintzLocalDirichlet.local_count χ hχ t
    intro z hz
    obtain ⟨hs, hr⟩ := mem_filter.mp hz
    exact ⟨hr, (hS z hs).2.1.le, (hS z hs).2.2⟩
  let g : ℂ → ℝ := fun z => (analyticOrderNatAt χ⁻¹.LFunction z : ℝ)
  have heq : (∑ z ∈ L.image (fun z => 1-z), g z) = ∑ z ∈ L, f z := by
    rw [sum_image (fun a _ b _ h => sub_right_injective h)]
    apply sum_congr rfl
    intro z hz
    have hzS := hS z (mem_filter.mp hz).1
    dsimp [f,g]
    rw [PintzZeroReflection.primitive_mult_reflection508 χ hprim hzS.1 hzS.2.1]
  have hL : (∑ z ∈ L, f z) ≤ Real.log (12*q*(|t|+6))/Real.log (55/52) := by
    rw [← heq, ← abs_neg t]
    apply PintzLocalDirichlet.local_count χ⁻¹ (inv_ne_one.mpr hχ) (-t)
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    obtain ⟨hzS,hzL⟩ := mem_filter.mp hz
    obtain ⟨hpos, hlt, him⟩ := hS z hzS
    simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,zero_sub]
    refine ⟨by linarith [lt_of_not_ge hzL], by linarith, ?_⟩
    rw [show -z.im - -t = -(z.im-t) by ring, abs_neg]
    exact him
  have hsplit : (∑ z ∈ R, f z) + ∑ z ∈ L, f z = ∑ z ∈ S, f z :=
    sum_filter_add_sum_filter_not S (fun z => 1/2 ≤ z.re) f
  change (∑ z ∈ S, f z) ≤ _
  linarith only [hR, hL, hsplit]

#print axioms local_count
end PintzFullStripCount
