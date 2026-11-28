import PintzJutilaMollifierBound

open Finset PintzJutilaPseudo PintzJutilaAnalytic

namespace PintzJutilaMollifierTail

theorem psi_bound {r : ℕ} (hr : r ≠ 0) (n : ℕ) : ‖(psi r n:ℂ)‖ ≤ (r:ℝ) := by
  rw [psi, Int.cast_mul, Int.cast_natCast, norm_mul, Complex.norm_natCast]
  have ha : ‖((ArithmeticFunction.moebius (r.gcd n):ℤ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one : |ArithmeticFunction.moebius (r.gcd n)| ≤ 1)
  have ht := (r.gcd n).totient_le
  have hh := Nat.gcd_le_left n (Nat.pos_of_ne_zero hr)
  exact (mul_le_of_le_one_left (by positivity) ha).trans (by exact_mod_cast ht.trans hh)

theorem term_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (ξ : ℕ → ℂ)
    (hξ : ∀ d, ‖ξ d‖ ≤ 1) {ρ : ℂ} (hρ : 0 ≤ ρ.re) {r : ℕ} (hr : r ≠ 0) (n : ℕ) :
    ‖LSeries.term (twisted (fun n => χ n) ξ r) ρ n‖ ≤ (r:ℝ)*n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, norm_div]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnpos : (0:ℝ) < n := by positivity
  have hcp : (1:ℝ) ≤ ‖(n:ℂ)^ρ‖ := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    exact Real.one_le_rpow hn1 hρ
  refine (div_le_self (norm_nonneg _) hcp).trans ?_
  unfold twisted
  rw [norm_mul, norm_mul]
  have hsum : ‖∑ d ∈ n.divisors, ξ d‖ ≤ (n:ℝ) := by
    refine (norm_sum_le _ _).trans ((sum_le_sum (fun d _ => hξ d)).trans ?_)
    simpa using (show (n.divisors.card:ℝ) ≤ n by exact_mod_cast Nat.card_divisors_le_self n)
  exact mul_le_mul
    ((mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (psi_bound hr n))
    hsum (norm_nonneg _) (by positivity)

/-- Uniform smoothed truncation on the detector side; all constants explicit. -/
theorem truncated_tail {q : ℕ} (χ : DirichletCharacter ℂ q) (ξ : ℕ → ℂ)
    (hξ : ∀ d, ‖ξ d‖ ≤ 1) {ρ : ℂ} (hρ : 0 ≤ ρ.re)
    {r : ℕ} (hr : r ≠ 0) {X x : ℝ} (hX : 0 < X) :
    let A := fun n : ℕ => if x < n then
      (r:ℝ)⁻¹ * ‖LSeries.term (twisted (fun n => χ n) ξ r) ρ n‖ *
        Real.exp (-(n:ℝ)/X) else 0
    Summable A ∧
      (∑' n, A n) ≤ (4*X*Real.exp (-x/(2*X)))*(1-Real.exp (-1/(4*X)))⁻¹ := by
  let A := fun n : ℕ => if x < n then
    (r:ℝ)⁻¹ * ‖LSeries.term (twisted (fun n => χ n) ξ r) ρ n‖ *
      Real.exp (-(n:ℝ)/X) else 0
  let a := Real.exp (-1/(4*X))
  let C := 4*X*Real.exp (-x/(2*X))
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) (by positivity))
  have hrpos : (0:ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
  have hmp (n : ℕ) : A n ≤ C*a^n := by
    by_cases hxn : x < n
    · dsimp [A]
      rw [ite_eq_left hxn]
      have hterm := mul_le_mul_of_nonneg_left (term_bound χ ξ hξ hρ hr n) (inv_nonneg.mpr hrpos.le)
      have hterm' : (r:ℝ)⁻¹ * ‖LSeries.term (twisted (fun n => χ n) ξ r) ρ n‖ ≤ n := by
        rwa [← mul_assoc, inv_mul_cancel₀ hrpos.ne', one_mul] at hterm
      have hnl : (n:ℝ) ≤ 4*X*Real.exp ((n:ℝ)/(4*X)) := by
        have HE := Real.add_one_le_exp ((n:ℝ)/(4*X))
        have H' := mul_le_mul_of_nonneg_left HE (show 0 ≤ 4*X by positivity)
        have hmul : 4*X*((n:ℝ)/(4*X)+1) = (n:ℝ)+4*X := by field_simp
        rw [hmul] at H'
        linarith
      have hE : Real.exp ((n:ℝ)/(4*X)) * Real.exp (-(n:ℝ)/X) ≤
          Real.exp (-x/(2*X)) * a^n := by
        dsimp [a]
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
        have HF := div_le_div_of_nonneg_right hxn.le (show 0 ≤ 2*X by positivity)
        have he : (n:ℝ)/(4*X)+(-(n:ℝ)/X) =
          -(n:ℝ)/(2*X)+(n:ℝ)*(-1/(4*X)) := by field_simp; ring
        rw [he]
        simpa only [neg_div, add_comm] using add_le_add_right (neg_le_neg HF) ((n:ℝ)*(-1/(4*X)))
      calc
        _ ≤ (n:ℝ)*Real.exp (-(n:ℝ)/X) :=
          mul_le_mul_of_nonneg_right hterm' (by positivity)
        _ ≤ (4*X*Real.exp ((n:ℝ)/(4*X)))*Real.exp (-(n:ℝ)/X) :=
          mul_le_mul_of_nonneg_right hnl (by positivity)
        _ ≤ _ := by
          dsimp [C]
          rw [mul_assoc (4*X), mul_assoc (4*X)]
          exact mul_le_mul_of_nonneg_left hE (show 0 ≤ 4*X by positivity)
    · dsimp [A]
      rw [ite_eq_right hxn]
      exact mul_nonneg (by dsimp [C]; positivity) (pow_nonneg ha.le _)
  have hnon (n : ℕ) : 0 ≤ A n := by
    dsimp [A]
    split <;> positivity
  have hgeo := (hasSum_geometric_of_lt_one ha.le ha1).mul_left C
  have hs : Summable A := hgeo.summable.of_nonneg_of_le hnon hmp
  exact ⟨hs,(hs.tsum_le_tsum hmp hgeo.summable).trans_eq hgeo.tsum_eq⟩

theorem inv_exp_gap {u : ℝ} (hu : 0 < u) :
    (1 - Real.exp (-u))⁻¹ ≤ 1 + u⁻¹ := by
  have hpos : 0 < 1 - Real.exp (-u) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))
  rw [← one_div]
  apply (div_le_iff₀ hpos).mpr
  have hE : Real.exp (-u) ≤ (u+1)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr (Real.add_one_le_exp u)
  have hB := mul_le_mul_of_nonneg_left (sub_le_sub_left hE 1)
    (show 0 ≤ 1 + u⁻¹ by positivity)
  have hEq : (1+u⁻¹)*(1-(u+1)⁻¹)=1 := by
    field_simp
    ring
  rwa [hEq] at hB

theorem tail_constant_simple {X : ℝ} (hX : 1 ≤ X) (x : ℝ) :
    (4*X*Real.exp (-x/(2*X)))*(1-Real.exp (-1/(4*X)))⁻¹ ≤
      20*X^2*Real.exp (-x/(2*X)) := by
  have HX : 0 < X := lt_of_lt_of_le zero_lt_one hX
  let a : ℝ := 4*X
  let g : ℝ := Real.exp (-x/(2*X))
  have ha : 0 < a := by dsimp only [a]; positivity
  have H : (1 - Real.exp (-a⁻¹))⁻¹ ≤ 1+a := by
    simpa only [inv_inv] using inv_exp_gap (inv_pos.mpr ha)
  have h5 : 1+a ≤ 5*X := by dsimp only [a]; linarith only [hX]
  have hcore : (a*g)*(1 - Real.exp (-a⁻¹))⁻¹ ≤ (a*g)*(5*X) :=
    mul_le_mul_of_nonneg_left (H.trans h5) (mul_nonneg ha.le (Real.exp_pos _).le)
  rw [show -1/(4*X) = -a⁻¹ by dsimp only [a]; simp only [neg_div, one_div]]
  refine hcore.trans_eq ?_
  change (4*X*Real.exp (-x/(2*X)))*(5*X) = _
  ring

theorem truncated_tail_simple {q : ℕ} (χ : DirichletCharacter ℂ q) (ξ : ℕ → ℂ)
    (hξ : ∀ d, ‖ξ d‖ ≤ 1) {ρ : ℂ} (hρ : 0 ≤ ρ.re)
    {r : ℕ} (hr : r ≠ 0) {X x : ℝ} (hX : 1 ≤ X) :
    let A := fun n : ℕ => if x < n then
      (r:ℝ)⁻¹ * ‖LSeries.term (twisted (fun n => χ n) ξ r) ρ n‖ *
        Real.exp (-(n:ℝ)/X) else 0
    Summable A ∧ (∑' n, A n) ≤ 20*X^2*Real.exp (-x/(2*X)) := by
  have HX : 0 < X := by linarith
  have A := truncated_tail χ ξ hξ hρ hr (x := x) HX
  dsimp only at A ⊢
  refine ⟨A.1,A.2.trans ?_⟩
  exact tail_constant_simple hX x

#print axioms truncated_tail_simple
#print axioms truncated_tail
end PintzJutilaMollifierTail
