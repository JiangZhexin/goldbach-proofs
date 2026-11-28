import PintzFullStripCount

open Finset

namespace PintzDavenportCount

/-- Uniform wider-window version of the actual primitive nonprincipal zero
count, in the normalization required by Davenport's modified-height proof. -/
theorem window_count : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ (t : ℝ) (S : Finset ℂ),
      (∀ z ∈ S, 0 < z.re ∧ z.re < 1 ∧ |z.im-t| ≤ 1) →
      (∑ z ∈ S, (analyticOrderNatAt χ.LFunction z : ℝ)) ≤
        A * Real.log ((q:ℝ)*(|t|+2)) := by
  let D := Real.log (55/52)
  have hD : 0 < D := Real.log_pos (by norm_num)
  refine ⟨28 / D, by positivity, ?_⟩
  intro q _ χ hp hn t S hS
  classical
  let f : ℂ → ℝ := fun z => (analyticOrderNatAt χ.LFunction z : ℝ)
  let U := S.filter (fun z => t ≤ z.im)
  let L := S.filter (fun z => ¬ t ≤ z.im)
  let X : ℝ := q*(|t|+2)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hX : 2 ≤ X := by
    dsimp [X]
    nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]
  have hlog (c : ℝ) (hc : |c-t| ≤ 1/2) : Real.log (12*q*(|c|+6)) ≤ 7*Real.log X := by
    have ht := (abs_sub_abs_le_abs_sub c t).trans hc
    have hq0 : (0:ℝ) < q := by linarith
    have h1 : 12*q*(|c|+6) ≤ 48*X := by
      have H : |c| + 6 ≤ 4*(|t|+2) := by linarith [abs_nonneg t]
      dsimp [X]
      nlinarith only [mul_le_mul_of_nonneg_left H (show 0 ≤ (q:ℝ) by positivity)]
    have hPow : (2:ℝ)^6 ≤ X^6 := pow_le_pow_left₀ (by norm_num) hX _
    have h2 : 48*X ≤ X^7 := by
      rw [show (7:ℕ) = 6+1 by norm_num, pow_succ]
      have h64 : 48 ≤ X^6 := by linarith [hPow]
      exact mul_le_mul_of_nonneg_right h64 (by linarith)
    have H := Real.log_le_log (by positivity : 0 < 12*q*(|c|+6)) (h1.trans h2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using H
  have hB (F : Finset ℂ) (c : ℝ) (hc : |c-t| ≤ 1/2)
      (hF : ∀ z ∈ F, 0 < z.re ∧ z.re < 1 ∧ |z.im-c| ≤ 1/2) :
      (∑ z ∈ F, f z) ≤ (14 / D) * Real.log X := by
    have H := PintzFullStripCount.local_count χ hn hp c F hF
    change (∑ z ∈ F, f z) ≤ 2*(Real.log (12*q*(|c|+6))/D) at H
    exact H.trans (by
      calc
        _ ≤ 2*(7*Real.log X/D) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (hlog c hc) hD.le) (by norm_num)
        _ = _ := by ring)
  have hU := hB U (t+1/2) (by rw [add_sub_cancel_left, abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]) (by
    intro z hz
    obtain ⟨hz,h⟩ := mem_filter.mp hz
    obtain ⟨hp,hl,ht⟩ := hS z hz
    rw [abs_le] at ht
    exact ⟨hp,hl,abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  have hL := hB L (t-1/2) (by rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]) (by
    intro z hz
    obtain ⟨hz,h⟩ := mem_filter.mp hz
    obtain ⟨hp,hl,ht⟩ := hS z hz
    rw [abs_le] at ht
    have h' := lt_of_not_ge h
    exact ⟨hp,hl,abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  have hsplit : (∑ z ∈ U, f z) + ∑ z ∈ L, f z = ∑ z ∈ S, f z :=
    sum_filter_add_sum_filter_not S (fun z => t ≤ z.im) f
  change (∑ z ∈ S, f z) ≤ (28/D)*Real.log X
  rw [← hsplit]
  calc
    _ ≤ (14/D)*Real.log X+(14/D)*Real.log X := add_le_add hU hL
    _ = _ := by ring

#print axioms window_count
end PintzDavenportCount
