import PintzEightGauss

/- Finite, translated interval form of the character-diagonal part of Pintz (8.2). -/
noncomputable section
open Finset MeasureTheory
open scoped Classical
namespace PintzEightEnergy

def intervalEnergy (u : ℝ) (f : ℝ → ℂ) :=
  ∫ x in -u..u, ‖f x‖ ^ 2

theorem intervalEnergy_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    {f : ℝ → ℂ} (hf : Continuous f) :
    intervalEnergy u f ≤ intervalEnergy v f := by
  rw [intervalEnergy, intervalEnergy,
    intervalIntegral.integral_of_le (by linarith : -u ≤ u),
    intervalIntegral.integral_of_le (by linarith : -v ≤ v)]
  exact setIntegral_mono_set
    ((hf.norm.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall fun x hx => ⟨by linarith [hx.1], hx.2.trans huv⟩)

private theorem integral_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (a b : ℝ)
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    (∫ x in a..b, ∑ i ∈ s, f i x) = ∑ i ∈ s, ∫ x in a..b, f i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs (j) (hj : j ∈ s) := h j (mem_insert_of_mem hj)
    simp_rw [Finset.sum_insert hi]
    have hSum : IntervalIntegrable (fun x => ∑ j ∈ s, f j x) volume a b := by
      rw [show (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, f j from funext fun x => (Finset.sum_apply x s f).symm]
      exact IntervalIntegrable.sum s hs
    rw [intervalIntegral.integral_add (h i (mem_insert_self _ _)) hSum, ih hs]

theorem diagonal {q : ℕ} [NeZero q] (u : ℝ)
    (g : DirichletCharacter ℂ q → ℂ) (f : DirichletCharacter ℂ q → ℝ → ℂ)
    (hf : ∀ χ, Continuous (f χ)) :
    (∑ a : ZMod q, intervalEnergy u (fun x =>
      (∑ χ : DirichletCharacter ℂ q, χ a * g χ * f χ x) / (q.totient : ℂ))) =
      (∑ χ : DirichletCharacter ℂ q, ‖g χ‖ ^ 2 * intervalEnergy u (f χ)) / (q.totient : ℝ) := by
  have hp : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hq : (q.totient : ℝ) ≠ 0 := hp.ne'
  unfold intervalEnergy
  rw [← integral_sum]
  · calc
      _ = ∫ x in -u..u, (∑ χ : DirichletCharacter ℂ q, ‖g χ‖ ^ 2 * ‖f χ x‖ ^ 2) /
          (q.totient : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x _
        simp_rw [norm_div, div_pow, Complex.norm_natCast, mul_assoc]
        rw [← Finset.sum_div, PintzEightParseval.pointwise_parseval]
        simp only [norm_mul, mul_pow]
        field_simp
      _ = _ := by
        simp_rw [div_eq_mul_inv, intervalIntegral.integral_mul_const]
        rw [integral_sum]
        · simp_rw [intervalIntegral.integral_const_mul]
        · intro χ _
          exact (((hf χ).norm.pow 2).const_mul (‖g χ‖ ^ 2)).intervalIntegrable _ _
  · intro a _
    apply Continuous.intervalIntegrable
    fun_prop

#print axioms diagonal
#print axioms intervalEnergy_mono
end PintzEightEnergy
