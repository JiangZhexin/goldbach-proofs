import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.PSeries
import PintzDirichletTail
import Mathlib.NumberTheory.Harmonic.Bounds

open DirichletCharacter OAI.Ostmann.Dirichlet Finset

namespace PintzJutilaLeftGrowth

/-- Absolute primitive functional equation with the conductor exponent
visible. No gamma-ratio estimate is assumed in this identity. -/
theorem functional_abs {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 1 < q) (hp : χ.IsPrimitive) {s : ℂ} (hγ : gammaFactor χ s ≠ 0)
    (hγ' : gammaFactor χ⁻¹ (1-s) ≠ 0) :
    ‖χ.LFunction s‖ = (q:ℝ)^(1/2-s.re) *
      (‖gammaFactor χ⁻¹ (1-s)‖/‖gammaFactor χ s‖) *
        ‖(χ⁻¹).LFunction (1-s)‖ := by
  have hq0 : (0:ℕ) < q := NeZero.pos q
  have hF := hp.completedLFunction_one_sub (1-s)
  rw [sub_sub_cancel] at hF
  rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inr (ne_of_gt hq)),hF,
    norm_div,norm_mul,norm_mul,norm_rootNumber hp,
    Complex.norm_natCast_cpow_of_pos hq0]
  rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1-s) (Or.inr (ne_of_gt hq)),
    norm_div]
  have hh : ((1/2:ℂ)).re = (1/2:ℝ) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,Complex.ofReal_re]
  simp only [Complex.sub_re,Complex.one_re,hh,mul_one]
  rw [show (1:ℝ)-s.re-1/2 = 1/2-s.re by ring]
  field_simp [norm_ne_zero_iff.mpr hγ,norm_ne_zero_iff.mpr hγ']
  <;> ring

/-- Uniform on the closed right half-plane Re s ≥ 1+ε; obtained
directly from the absolute Dirichlet series, independently of q. -/
theorem right_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      1+ε ≤ s.re → ‖χ.LFunction s‖ ≤ C := by
  let v (n : ℕ) : ℝ := 1/(n:ℝ)^(1+ε)
  have hv : Summable v := Real.summable_one_div_nat_rpow.mpr (by linarith)
  refine ⟨∑' n, v n,tsum_nonneg (fun n => by dsimp [v]; positivity),?_⟩
  intro q _ χ s hs
  have hσ : 1 < s.re := by linarith
  rw [χ.LFunction_eq_LSeries hσ]
  have hsum := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hσ
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  apply hsum.norm.tsum_le_tsum _ hv
  intro n
  by_cases hn : n = 0
  · simp [hn, LSeries.term,v, Real.zero_rpow (show (1:ℝ)+ε ≠ 0 by linarith)]
  have hp : 0 < n := Nat.pos_of_ne_zero hn
  rw [LSeries.term_of_ne_zero hn,norm_div,Complex.norm_natCast_cpow_of_pos hp]
  apply (div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)).trans
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) hs

theorem left_uniform_of_gamma {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      1 < q → χ.IsPrimitive → s.re ≤ -ε →
      gammaFactor χ s ≠ 0 → gammaFactor χ⁻¹ (1-s) ≠ 0 →
      ∀ D : ℝ, 0 ≤ D →
      ‖gammaFactor χ⁻¹ (1-s)‖/‖gammaFactor χ s‖ ≤ D*(1+|s.im|)^(1/2-s.re) →
      ‖χ.LFunction s‖ ≤ C*D*((q:ℝ)*(1+|s.im|))^(1/2-s.re) := by
  obtain ⟨C,hC,hL⟩ := right_uniform hε
  refine ⟨C,hC,?_⟩
  intro q _ χ s hq hp hs hγ hγ' D hD hR
  rw [functional_abs χ hq hp hγ hγ',Real.mul_rpow (by positivity) (by positivity)]
  have h := hL q χ⁻¹ (1-s) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  calc
    _ ≤ ((q:ℝ)^(1/2-s.re)*(D*(1+|s.im|)^(1/2-s.re)))*C :=
      mul_le_mul (mul_le_mul_of_nonneg_left hR (by positivity)) h (by positivity) (by positivity)
    _ = _ := by ring

/-- Conditional convergence at the boundary causes no conductor power
penalty. Cut the Euler-Abel prefix at q(1+‖s‖) and bound it by a harmonic sum. -/
theorem right_edge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hn : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖χ.LFunction s‖ ≤ 2+Real.log (2*(q:ℝ)*(1+‖s‖)) := by
  let A := (q:ℝ)*(1+‖s‖)
  let n := ⌈A⌉₊
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hA : 1 ≤ A := by
    dsimp [A]
    have hh := mul_nonneg (show (0:ℝ) ≤ q by positivity) (norm_nonneg s)
    nlinarith only [hq,hh]
  have ha : A ≤ (n:ℝ) := Nat.le_ceil _
  have hn1 : (1:ℝ) ≤ n := hA.trans ha
  have hnn : 1 ≤ n := by exact_mod_cast hn1
  have hnp : 0 < (n:ℝ) := by linarith
  have hU : (n:ℝ) ≤ 2*A := by linarith [Nat.ceil_lt_add_one (show 0 ≤ A by linarith)]
  have he := norm_LFunction_sub_dirichletPolynomial_le χ hn (by linarith : 0 < s.re) hnn
  have h1 : ‖χ.LFunction s - dirichletPolynomial χ n s‖ ≤ 1 := by
    refine he.trans ?_
    have H := Real.rpow_le_rpow_of_exponent_le hn1 (show -s.re ≤ -1 by linarith)
    rw [Real.rpow_neg_one] at H
    have H' : ‖s‖/s.re ≤ ‖s‖ := div_le_self (norm_nonneg _) hs
    have H'' : 1+‖s‖/s.re ≤ 1+‖s‖ := by linarith
    calc
      _ ≤ A*(n:ℝ)⁻¹ := mul_le_mul (mul_le_mul_of_nonneg_left H'' (by positivity)) H (by positivity) (by linarith)
      _ ≤ 1 := by rw [← div_eq_mul_inv]; exact (div_le_one hnp).2 ha
  have hH : (∑ j ∈ Icc 1 n, (j:ℝ)⁻¹) ≤ 1+Real.log n := by
    have h := harmonic_le_one_add_log n
    have hEq : (harmonic n:ℝ) = ∑ j ∈ Icc 1 n, (j:ℝ)⁻¹ := by
      unfold harmonic
      push_cast
      apply Finset.sum_bij (fun j _ => j+1)
      · intro j hj
        obtain H := mem_range.mp hj
        exact mem_Icc.mpr ⟨by omega,by omega⟩
      · intro i _ j _ h; omega
      · intro j hj; obtain ⟨h₁,h₂⟩ := mem_Icc.mp hj
        exact ⟨j-1,mem_range.mpr (by omega),by omega⟩
      · intro j _; push_cast; rfl
    rwa [← hEq]
  have hP : ‖dirichletPolynomial χ n s‖ ≤ 1+Real.log n := by
    unfold dirichletPolynomial
    refine (norm_sum_le _ _).trans ((sum_le_sum ?_).trans hH)
    intro j hj
    have hp : 0 < j := (mem_Icc.mp hj).1
    have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hp
    rw [norm_mul,Complex.norm_natCast_cpow_of_pos hp,Complex.neg_re]
    refine (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (χ.norm_le_one _)).trans ?_
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
  have hL := Real.log_le_log hnp hU
  have h := norm_add_le (χ.LFunction s-dirichletPolynomial χ n s) (dirichletPolynomial χ n s)
  rw [sub_add_cancel] at h
  have heq : 2*A = 2*(q:ℝ)*(1+‖s‖) := by dsimp [A]; ring
  linarith only [h,h1,hP,heq ▸ hL]

#print axioms right_edge
#print axioms functional_abs
#print axioms right_uniform
#print axioms left_uniform_of_gamma
end PintzJutilaLeftGrowth
