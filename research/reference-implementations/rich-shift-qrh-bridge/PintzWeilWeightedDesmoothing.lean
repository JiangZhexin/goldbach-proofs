import PintzWeilPrimeDesmoothing

open Finset MeasureTheory PintzWeilTestWindow ArithmeticFunction PintzWeilPrimeDesmoothing

namespace PintzWeilWeightedDesmoothing

/-- The exact endpoint-band error persists under any complex twists of
norm at most one, in particular primitive Dirichlet characters. -/
theorem desmooth_weighted_window {g : ℝ → ℝ} {δ x y : ℝ}
    (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hx : 1 ≤ x) (hxy : x ≤ y) (hg : Continuous g)
    (hn : ∀ u, 0 ≤ g u) (hl : ∀ u ≤ -δ, g u = 0) (hr : ∀ u ≥ δ, g u = 0)
    (hm : (∫ u in (-δ)..δ, g u) = 1) :
    ‖(∑' n : ℕ, (vonMangoldt n:ℂ) * w n * (diff g δ (Real.log x) (Real.log y) (Real.log n):ℂ)) -
      (∑' n : ℕ, (vonMangoldt n:ℂ) * w n * (sharp x y n:ℂ))‖ ≤
      (3 * δ * (x+y) + 2) * Real.log (y * Real.exp δ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hy : 1 ≤ y := hx.trans hxy
  have hlogs : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  let M := y * Real.exp δ
  have hM : y ≤ M := by
    dsimp [M]
    simpa using mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr hδ) hy0.le
  have hM₀ : 0 ≤ M := hy0.le.trans hM
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (hy.trans hM)
  let sm (n : ℕ) := (vonMangoldt n:ℂ) * w n * (diff g δ (Real.log x) (Real.log y) (Real.log n):ℂ)
  let sh (n : ℕ) := (vonMangoldt n:ℂ) * w n * (sharp x y n:ℂ)
  let band := endpointBand x δ ∪ endpointBand y δ
  let sup := Finset.range (⌊M⌋₊+1)
  have hsh (n : ℕ) (hnout : n ∉ sup) : sh n = 0 := by
    have H : M < (n:ℝ) := lt_of_not_ge (fun hnM => hnout (Finset.mem_range.mpr
      (Nat.lt_succ_of_le ((Nat.le_floor_iff hM₀).mpr hnM))))
    unfold sh sharp
    rw [ite_eq_right (fun h => not_le_of_gt (lt_of_le_of_lt hM H) h.2), Complex.ofReal_zero, mul_zero]
  have hsm (n : ℕ) (hnout : n ∉ sup) : sm n = 0 := by
    have H : M < (n:ℝ) := lt_of_not_ge (fun hnM => hnout (Finset.mem_range.mpr
      (Nat.lt_succ_of_le ((Nat.le_floor_iff hM₀).mpr hnM))))
    have hnR : 0 < (n:ℝ) := lt_of_le_of_lt hM₀ H
    have hi : Real.log y + δ ≤ Real.log n := (Real.le_log_iff_exp_le hnR).mpr (by
      rw [Real.exp_add, Real.exp_log hy0]; exact H.le)
    unfold sm diff
    rw [cdf_right hδ hg hr hm (by linarith), cdf_right hδ hg hr hm (by linarith),
      sub_self, Complex.ofReal_zero, mul_zero]
  have hout (n : ℕ) (hnout : n ∉ band) : sm n - sh n = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn₀
    · simp [sm, sh]
    have H := pointwise_outside_endpoints hδ hx0 hxy hg hl hr hm hn₀
      (fun hh => hnout (mem_union_left _ hh)) (fun hh => hnout (mem_union_right _ hh))
    simp [sm, sh, H]
  have hsmS : Summable sm := summable_of_ne_finset_zero hsm
  have hshS : Summable sh := summable_of_ne_finset_zero hsh
  change ‖(∑' n, sm n) - ∑' n, sh n‖ ≤ _
  rw [← hsmS.tsum_sub hshS, tsum_eq_sum hout]
  have hbd (n : ℕ) (hnb : n ∈ band) : ‖sm n-sh n‖ ≤ Real.log M := by
    have hdiff : 0 ≤ diff g δ (Real.log x) (Real.log y) (Real.log n) ∧
        diff g δ (Real.log x) (Real.log y) (Real.log n) ≤ 1 := by
      unfold diff
      have H := monotone_cdf hg hn hl (show Real.log n - Real.log y ≤ Real.log n - Real.log x by linarith)
      have h₁ := cdf_unit hδ hg hn hl hr hm (Real.log n - Real.log x)
      have h₂ := cdf_unit hδ hg hn hl hr hm (Real.log n - Real.log y)
      exact ⟨by linarith, by linarith [h₁.2,h₂.1]⟩
    have hsharp : 0 ≤ sharp x y n ∧ sharp x y n ≤ 1 := by unfold sharp; split <;> norm_num
    have hD : |diff g δ (Real.log x) (Real.log y) (Real.log n) - sharp x y n| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hdiff.1,hsharp.2], by linarith [hdiff.2,hsharp.1]⟩
    have hnM : (n:ℝ) ≤ M := by
      rcases mem_union.mp hnb with hb|hb
      · exact ((mem_endpointBand hx0.le n).mp hb).2.trans
          (mul_le_mul_of_nonneg_right hxy (Real.exp_pos _).le)
      · exact ((mem_endpointBand hy0.le n).mp hb).2
    have hv : vonMangoldt n ≤ Real.log M := by
      rcases Nat.eq_zero_or_pos n with rfl | h₀
      · simpa using hlogM
      · exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast h₀) hnM)
    rw [show sm n-sh n = (vonMangoldt n:ℂ) * w n *
      (((diff g δ (Real.log x) (Real.log y) (Real.log n)-sharp x y n):ℝ):ℂ) by
        unfold sm sh; rw [Complex.ofReal_sub,mul_sub],
      norm_mul, norm_mul]
    simp only [Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    calc
      _ ≤ vonMangoldt n * |diff g δ (Real.log x) (Real.log y) (Real.log n) - sharp x y n| :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right vonMangoldt_nonneg (hw n)) (abs_nonneg _)
      _ ≤ vonMangoldt n := mul_le_of_le_one_right vonMangoldt_nonneg hD
      _ ≤ _ := hv
  have hc : (band.card : ℝ) ≤ 3*δ*(x+y)+2 := by
    have H : (band.card : ℝ) ≤ (endpointBand x δ).card + (endpointBand y δ).card := by
      exact_mod_cast card_union_le (endpointBand x δ) (endpointBand y δ)
    linarith [card_endpointBand_small hx0.le hδ hδ₁, card_endpointBand_small hy0.le hδ hδ₁]
  calc
    _ ≤ ∑ n ∈ band, ‖sm n-sh n‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ band, Real.log M := sum_le_sum hbd
    _ = (band.card : ℝ) * Real.log M := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hlogM

#print axioms desmooth_weighted_window
end PintzWeilWeightedDesmoothing
