import PintzZetaJensen
import PintzHarmonicRow
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation

open Set Finset Filter
open scoped Topology

namespace PintzZetaLocal

open PintzZetaJensen

theorem regular_growth {s : ℂ} (hs : (1/5:ℝ) ≤ s.re) :
    ‖regularZeta s‖ ≤ ‖s-1‖ + 1 + 5*‖s-1‖*‖s‖ := by
  by_cases he : s = 1
  · subst s
    simp [regularZeta]
  have hd : s ∈ zetaAbelContinuationDomain := ⟨he, by
    change (1/10:ℝ) < s.re
    linarith⟩
  have hb := norm_zetaAbelContinuationFormula_le s hd
  rw [← riemannZeta_eq_zetaAbelContinuationFormula s hd] at hb
  rw [regular_off he, norm_mul]
  have hn : 0 < ‖s-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hs₀ : 0 < s.re := by linarith
  have hD : ‖s‖/s.re ≤ 5*‖s‖ := by
    apply (div_le_iff₀ hs₀).2
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 5*‖s‖ by positivity)
    linarith
  have hh := mul_le_mul_of_nonneg_left hb hn.le
  rw [one_div, norm_inv, mul_add, mul_add, mul_one, mul_inv_cancel₀ hn.ne'] at hh
  nlinarith [mul_le_mul_of_nonneg_left hD hn.le]

theorem disk_bound (t : ℝ) {s : ℂ} (hs : s ∈ Metric.sphere (⟨2,t⟩:ℂ) (9/5)) :
    ‖regularZeta s‖ ≤ 8*(|t|+5)^2 := by
  let c : ℂ := ⟨2,t⟩
  have hd := Metric.mem_sphere.mp hs
  change dist s c = _ at hd
  rw [dist_eq_norm] at hd
  have hsr := (abs_le.mp ((Complex.abs_re_le_norm (s-c)).trans hd.le)).1
  simp only [Complex.sub_re,c] at hsr
  have hr : 1/5 ≤ s.re := by linarith
  have hc : ‖c‖ ≤ 2+|t| := by
    have he : c = 2+(t:ℂ)*Complex.I := by apply Complex.ext <;> simp [c]
    rw [he]
    simpa [norm_mul] using norm_add_le (2:ℂ) ((t:ℂ)*Complex.I)
  have hns : ‖s‖ ≤ |t|+4 := by
    have h := norm_add_le (s-c) c
    rw [sub_add_cancel,hd] at h
    linarith
  have hns' : ‖s-1‖ ≤ |t|+5 := by
    have h := norm_sub_le s 1
    rw [norm_one] at h
    linarith
  have hm := mul_le_mul hns' hns (norm_nonneg s)
    (show 0 ≤ |t|+5 by positivity)
  nlinarith [regular_growth hr, abs_nonneg t, sq_nonneg |t|]

theorem order_eq {z : ℂ} (hz : z ≠ 1) :
    analyticOrderAt regularZeta z = analyticOrderAt riemannZeta z := by
  have he : regularZeta =ᶠ[𝓝 z] (fun w => (w-1)*riemannZeta w) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact regular_off hw
  have hA : AnalyticAt ℂ (fun w : ℂ => w-1) z := analyticAt_id.sub analyticAt_const
  have hZ := analyticOn_riemannZeta z hz
  rw [analyticOrderAt_congr he]
  change analyticOrderAt ((fun w : ℂ => w-1)*riemannZeta) z = _
  rw [analyticOrderAt_mul hA hZ,
    hA.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz), zero_add]

theorem local_count (t : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ≠ 1 ∧ 1/2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im-t| ≤ 1/2) :
    (∑ z ∈ S, ((analyticOrderAt riemannZeta z).toNat : ℝ)) ≤
      Real.log (24*(|t|+5)^2)/Real.log (12/11) := by
  have hM : 1 ≤ 8*(|t|+5)^2 := by nlinarith [abs_nonneg t,sq_nonneg |t|]
  have h := count_of_growth t _ S hM (fun z hz => (hS z hz).2) (fun _ hz => disk_bound t hz)
  calc
    _ = ∑ z ∈ S, ((analyticOrderAt regularZeta z).toNat : ℝ) :=
      sum_congr rfl (fun z hz => by rw [order_eq (hS z hz).1])
    _ ≤ _ := h.trans_eq (by ring_nf)

theorem harmonic_zero_row (T γ : ℝ) (hT : 0 ≤ T) (hγ : |γ| ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ≠ 1 ∧ 1/2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) :
    (∑ z ∈ S, ((analyticOrderAt riemannZeta z).toNat : ℝ)/(1+|z.im-γ|)) ≤
      2 * (Real.log (24*(T+11/2)^2)/Real.log (12/11)) * (1+Real.log (2*T+1)) := by
  classical
  let C := Real.log (24*(T+11/2)^2)/Real.log (12/11)
  have hC : 0 ≤ C := by
    apply div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by norm_num))
    nlinarith [sq_nonneg T]
  apply PintzHarmonicRow.row_at_height S Complex.im
    (fun z => ((analyticOrderAt riemannZeta z).toNat : ℝ)) γ T C hT hγ hC
    (fun _ _ => Nat.cast_nonneg _) (fun z hz => (hS z hz).2.2.2)
  intro t ht
  have h := local_count t (S.filter (fun z => |z.im-t| ≤ 1/2)) (by
    intro z hz
    obtain ⟨hs,ht'⟩ := mem_filter.mp hz
    exact ⟨(hS z hs).1,(hS z hs).2.1,(hS z hs).2.2.1,ht'⟩)
  refine h.trans (div_le_div_of_nonneg_right (Real.log_le_log (by positivity) ?_)
    (Real.log_nonneg (by norm_num)))
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by norm_num)

#print axioms local_count
#print axioms harmonic_zero_row
end PintzZetaLocal
