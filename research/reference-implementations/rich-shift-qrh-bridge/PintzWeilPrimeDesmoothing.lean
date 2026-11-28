import PintzWeilTestWindow
import Mathlib.Order.Interval.Finset.Nat

noncomputable section
open Finset MeasureTheory
open PintzWeilTestWindow ArithmeticFunction

namespace PintzWeilPrimeDesmoothing

theorem monotone_cdf {g : ℝ → ℝ} {δ : ℝ} (hg : Continuous g)
    (hn : ∀ u, 0 ≤ g u) (hl : ∀ u ≤ -δ, g u = 0) : Monotone (cdf g δ) := by
  intro a b hab
  by_cases ha : -δ ≤ a
  · exact intervalIntegral.integral_mono_interval le_rfl ha hab
      (Filter.Eventually.of_forall hn) (hg.intervalIntegrable _ _)
  by_cases hb : -δ ≤ b
  · rw [cdf_left hl (le_of_not_ge ha)]
    exact intervalIntegral.integral_nonneg hb (fun u _ => hn u)
  · rw [cdf_left hl (le_of_not_ge ha),cdf_left hl (le_of_not_ge hb)]

theorem cdf_unit {g : ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hg : Continuous g)
    (hn : ∀ u, 0 ≤ g u) (hl : ∀ u ≤ -δ, g u = 0) (hr : ∀ u ≥ δ, g u = 0)
    (hm : (∫ u in (-δ)..δ, g u) = 1) (v : ℝ) : 0 ≤ cdf g δ v ∧ cdf g δ v ≤ 1 := by
  have H := monotone_cdf hg hn hl
  have H₀ := cdf_left hl (le_refl (-δ))
  have H₁ := cdf_right hδ hg hr hm (le_refl δ)
  constructor
  · by_cases hv : -δ ≤ v
    · simpa [H₀] using H hv
    · simp [cdf_left hl (le_of_not_ge hv)]
  · by_cases hv : v ≤ δ
    · simpa [H₁] using H hv
    · simp [cdf_right hδ hg hr hm (le_of_not_ge hv)]

def sharp (x y : ℝ) (n : ℕ) : ℝ := if x < n ∧ (n:ℝ) ≤ y then 1 else 0

def endpointBand (x δ : ℝ) : Finset ℕ :=
  Finset.Icc ⌈x * Real.exp (-δ)⌉₊ ⌊x * Real.exp δ⌋₊

theorem mem_endpointBand {x δ : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    n ∈ endpointBand x δ ↔ x * Real.exp (-δ) ≤ n ∧ (n:ℝ) ≤ x * Real.exp δ := by
  simp only [endpointBand, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (mul_nonneg hx (Real.exp_pos _).le)]

theorem card_endpointBand {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ) :
    ((endpointBand x δ).card : ℝ) ≤ x * (Real.exp δ - Real.exp (-δ)) + 1 := by
  have H : x * Real.exp (-δ) ≤ x * Real.exp δ :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hx
  unfold endpointBand
  rw [Nat.card_Icc]
  by_cases h : ⌈x * Real.exp (-δ)⌉₊ ≤ ⌊x * Real.exp δ⌋₊ + 1
  · rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le (mul_nonneg hx (Real.exp_nonneg δ)), Nat.le_ceil (x*Real.exp (-δ))]
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), Nat.cast_zero]
    linarith

theorem card_endpointBand_small {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    ((endpointBand x δ).card : ℝ) ≤ 3 * δ * x + 1 := by
  have H := Real.norm_exp_sub_one_sub_id_le (x := δ) (by simpa [Real.norm_eq_abs, abs_of_nonneg hδ] using hδ₁)
  rw [Real.norm_eq_abs] at H
  have hpos : Real.exp δ - 1 - δ ≤ δ^2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hδ] at H
    exact (le_abs_self _).trans H
  have hneg := Real.add_one_le_exp (-δ)
  have hsq : δ^2 ≤ δ := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ₁)]
  refine (card_endpointBand hx hδ).trans ?_
  have H' : Real.exp δ - Real.exp (-δ) ≤ 3*δ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left H' hx]

theorem pointwise_outside_endpoints {g : ℝ → ℝ} {δ x y : ℝ}
    (hδ : 0 ≤ δ) (hx : 0 < x) (hxy : x ≤ y) (hg : Continuous g)
    (hl : ∀ u ≤ -δ, g u = 0) (hr : ∀ u ≥ δ, g u = 0)
    (hm : (∫ u in (-δ)..δ, g u) = 1) {n : ℕ} (hn : 0 < n)
    (hxout : n ∉ endpointBand x δ) (hyout : n ∉ endpointBand y δ) :
    diff g δ (Real.log x) (Real.log y) (Real.log n) = sharp x y n := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have per {a : ℝ} (ha : 0 < a) (ho : n ∉ endpointBand a δ) :
      cdf g δ (Real.log n - Real.log a) = if a < (n:ℝ) then 1 else 0 := by
    rw [mem_endpointBand ha.le] at ho
    simp only [not_and_or, not_le] at ho
    rcases ho with h|h
    · have he : (n:ℝ) ≤ Real.exp (Real.log a - δ) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log ha]
        exact h.le
      have hln := (Real.log_le_iff_le_exp hnR).mpr he
      have hna : (n:ℝ) ≤ a := h.le.trans (by
        simpa using mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by linarith : -δ ≤ 0)) ha.le)
      rw [ite_eq_right (not_lt_of_ge hna), cdf_left hl (by linarith)]
    · have he : Real.exp (Real.log a + δ) ≤ (n:ℝ) := by
        rw [Real.exp_add, Real.exp_log ha]
        exact h.le
      have hln := (Real.le_log_iff_exp_le hnR).mpr he
      have han : a < (n:ℝ) := lt_of_le_of_lt (by
        simpa using mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr hδ) ha.le) h
      rw [ite_eq_left han, cdf_right hδ hg hr hm (by linarith)]
  rw [diff, per hx hxout, per (hx.trans_le hxy) hyout, sharp]
  split_ifs <;> simp_all <;> linarith

/-- Removing the smoothing costs only the two endpoint bands. For delta ≤ 1,
their total number of integers is ≤ 3 delta (x+y)+2. -/
theorem desmooth_prime_window {g : ℝ → ℝ} {δ x y : ℝ}
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hx : 1 ≤ x) (hxy : x ≤ y) (hg : Continuous g)
    (hn : ∀ u, 0 ≤ g u) (hl : ∀ u ≤ -δ, g u = 0) (hr : ∀ u ≥ δ, g u = 0)
    (hm : (∫ u in (-δ)..δ, g u) = 1) :
    |(∑' n : ℕ, vonMangoldt n * diff g δ (Real.log x) (Real.log y) (Real.log n)) -
      (∑' n : ℕ, vonMangoldt n * sharp x y n)| ≤
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
  let sm (n : ℕ) := vonMangoldt n * diff g δ (Real.log x) (Real.log y) (Real.log n)
  let sh (n : ℕ) := vonMangoldt n * sharp x y n
  let band := endpointBand x δ ∪ endpointBand y δ
  let sup := Finset.range (⌊M⌋₊+1)
  have hsh (n : ℕ) (hnout : n ∉ sup) : sh n = 0 := by
    have H : M < (n:ℝ) := lt_of_not_ge (fun hnM => hnout (Finset.mem_range.mpr
      (Nat.lt_succ_of_le ((Nat.le_floor_iff hM₀).mpr hnM))))
    unfold sh sharp
    exact mul_eq_zero_of_right _ (ite_eq_right (fun h => not_le_of_gt (lt_of_le_of_lt hM H) h.2))
  have hsm (n : ℕ) (hnout : n ∉ sup) : sm n = 0 := by
    have H : M < (n:ℝ) := lt_of_not_ge (fun hnM => hnout (Finset.mem_range.mpr
      (Nat.lt_succ_of_le ((Nat.le_floor_iff hM₀).mpr hnM))))
    have hnR : 0 < (n:ℝ) := lt_of_le_of_lt hM₀ H
    have hi : Real.log y + δ ≤ Real.log n := (Real.le_log_iff_exp_le hnR).mpr (by
      rw [Real.exp_add, Real.exp_log hy0]; exact H.le)
    unfold sm diff
    rw [cdf_right hδ hg hr hm (by linarith), cdf_right hδ hg hr hm (by linarith),
      sub_self, mul_zero]
  have hout (n : ℕ) (hnout : n ∉ band) : sm n - sh n = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn₀
    · simp [sm, sh]
    have H := pointwise_outside_endpoints hδ hx0 hxy hg hl hr hm hn₀
      (fun hh => hnout (mem_union_left _ hh)) (fun hh => hnout (mem_union_right _ hh))
    simp [sm, sh, H]
  have hsmS : Summable sm := summable_of_ne_finset_zero hsm
  have hshS : Summable sh := summable_of_ne_finset_zero hsh
  change |(∑' n, sm n) - ∑' n, sh n| ≤ _
  rw [← hsmS.tsum_sub hshS, tsum_eq_sum hout]
  have hbd (n : ℕ) (hnb : n ∈ band) : |sm n-sh n| ≤ Real.log M := by
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
    rw [show sm n-sh n = vonMangoldt n *
      (diff g δ (Real.log x) (Real.log y) (Real.log n)-sharp x y n) by
        unfold sm sh; rw [mul_sub], abs_mul, abs_of_nonneg vonMangoldt_nonneg]
    exact (mul_le_of_le_one_right vonMangoldt_nonneg hD).trans hv
  have hc : (band.card : ℝ) ≤ 3*δ*(x+y)+2 := by
    have H : (band.card : ℝ) ≤ (endpointBand x δ).card + (endpointBand y δ).card := by
      exact_mod_cast card_union_le (endpointBand x δ) (endpointBand y δ)
    linarith [card_endpointBand_small hx0.le hδ hδ₁, card_endpointBand_small hy0.le hδ hδ₁]
  calc
    _ ≤ ∑ n ∈ band, |sm n-sh n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ band, Real.log M := sum_le_sum hbd
    _ = (band.card : ℝ) * Real.log M := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hlogM

#print axioms card_endpointBand_small
#print axioms pointwise_outside_endpoints
#print axioms desmooth_prime_window
end PintzWeilPrimeDesmoothing
