import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Finset MeromorphicOn

namespace PintzLocalJensen

/-- A finite compact-strip sum can be bounded by Jensen's divisor sum, without
forgetting multiplicities. This also applies to the regularized principal case. -/
theorem count_of_analytic {F : ℂ → ℂ} (hF : ∀ z, AnalyticAt ℂ F z)
    (S : Finset ℂ) {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hM : 1 ≤ M) (hc : F c ≠ 0)
    (hS : ∀ z ∈ S, z ∈ Metric.closedBall c r)
    (hB : ∀ z ∈ Metric.sphere c R, ‖F z‖ ≤ M) :
    (∑ z ∈ S, ((analyticOrderAt F z).toNat : ℝ)) ≤
      Real.log (M / ‖F c‖) / Real.log (R / r) := by
  classical
  have hA : AnalyticOnNhd ℂ F (Metric.closedBall c r) := fun z _ => hF z
  let d := MeromorphicOn.divisor F (Metric.closedBall c r)
  have hfin := d.finiteSupport (isCompact_closedBall c r)
  let U := S ∪ hfin.toFinset
  have hsupport : Function.support d ⊆ (U : Set ℂ) :=
    fun z hz => mem_union_right _ (hfin.mem_toFinset.mpr hz)
  have hf (z : ℂ) : analyticOrderAt F z ≠ ⊤ := by
    intro h
    have hzero := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hF).mp h
    exact hc (congrFun hzero c)
  have hle : (∑ z ∈ S, ((analyticOrderAt F z).toNat : ℤ)) ≤ ∑ᶠ z, d z := by
    rw [finsum_eq_finsetSum_of_support_subset d hsupport]
    calc
      _ = ∑ z ∈ S, d z := by
        apply sum_congr rfl
        intro z hz
        dsimp only [d]
        rw [hA.divisor_apply (hS z hz), ← ENat.natCast_toNat (hf z)]
        simp
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg subset_union_left
        (fun z _ _ => hA.divisor_nonneg z)
  have hj := AnalyticOnNhd.sum_divisor_le (r := r) (R := R) (M := M)
    (by simpa [abs_of_pos hr] using hr)
    (by simpa [abs_of_pos hr, abs_of_pos (hr.trans hrR)] using hrR)
    hM (fun z _ => hF z) hc (by simpa [abs_of_pos (hr.trans hrR)] using hB)
  rw [abs_of_pos hr] at hj
  apply le_trans _ hj
  exact_mod_cast hle

/-- A single analytic count works across the full half strip. At this layer
the circle bound and nonvanishing at the indicated center are hypotheses. -/
theorem full_strip_nonprincipal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t M : ℝ)
    (S : Finset ℂ) (hM : 1 ≤ M)
    (hS : ∀ z ∈ S, 1/2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im-t| ≤ 1/2)
    (hB : ∀ z ∈ Metric.sphere (⟨3,t⟩ : ℂ) (11/4), ‖χ.LFunction z‖ ≤ M) :
    (∑ z ∈ S, ((analyticOrderAt χ.LFunction z).toNat : ℝ)) ≤
      Real.log (M / ‖χ.LFunction (⟨3,t⟩ : ℂ)‖) / Real.log (55/52) := by
  have hc : χ.LFunction (⟨3,t⟩ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  have hG (z : ℂ) (hz : z ∈ S) : z ∈ Metric.closedBall (⟨3,t⟩ : ℂ) (13/5) := by
    obtain ⟨hlo,hhi,him⟩ := hS z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm : ‖z - (⟨3,t⟩ : ℂ)‖^2 = (z.re-3)^2 + (z.im-t)^2 := by
      simp [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hr : (z.re-3)^2 ≤ (5/2:ℝ)^2 := by nlinarith
    have hi : (z.im-t)^2 ≤ (1/2:ℝ)^2 := by
      obtain ⟨ha,hb⟩ := abs_le.mp him
      nlinarith
    nlinarith [norm_nonneg (z - (⟨3,t⟩ : ℂ))]
  have hh := count_of_analytic (fun z => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z)
    S (by norm_num) (by norm_num) hM hc hG hB
  convert hh using 1; norm_num

#print axioms count_of_analytic
#print axioms full_strip_nonprincipal
end PintzLocalJensen
