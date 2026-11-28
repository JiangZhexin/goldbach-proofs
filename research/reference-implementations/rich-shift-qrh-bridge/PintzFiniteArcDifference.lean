import PintzSection8Bound

open Finset MeasureTheory

namespace PintzFiniteArcDifference

private theorem young {ell f g : ℝ} (hell : 0 < ell) :
    2*f*g ≤ ell*f^2+ell⁻¹*g^2 := by
  apply le_of_mul_le_mul_left _ hell
  have he : ell*(ell*f^2+ell⁻¹*g^2)=ell^2*f^2+g^2 := by
    rw [mul_add,
      show ell*(ell⁻¹*g^2)=g^2 by rw [← mul_assoc,mul_inv_cancel₀ hell.ne',one_mul]]
    ring
  rw [he]
  nlinarith only [sq_nonneg (ell*f-g)]

private theorem pointwise (f g w : ℂ) (ell : ℝ) (hell : 0 < ell) (hw : ‖w‖ ≤ 1) :
    ‖f^2*w-(f-g)^2*w‖ ≤ ell*‖f‖^2+(1+ell⁻¹)*‖g‖^2 := by
  rw [show f^2*w-(f-g)^2*w = (2*(f*g)-g^2)*w by ring,norm_mul]
  apply (mul_le_of_le_one_right (norm_nonneg _) hw).trans
  have h := norm_sub_le (2*(f*g)) (g^2)
  rw [norm_mul,norm_mul,Complex.norm_ofNat,norm_pow] at h
  calc
    _ ≤ 2*(‖f‖*‖g‖)+‖g‖^2 := h
    _ ≤ (ell*‖f‖^2+ell⁻¹*‖g‖^2)+‖g‖^2 := by
      rw [← mul_assoc]
      exact add_le_add (young hell) le_rfl
    _ = _ := by ring

/-- The exact Fourier coefficient replacement on a finite translated
arc system. A tunable Young weight avoids a separate summation Cauchy
Schwarz and works with any continuous unit-modulus phase. -/
theorem transfer {ι : Type*} (J : Finset ι) (u : ι → ℝ) (S R B : ι → ℝ → ℂ)
    (hu : ∀ i ∈ J, 0 ≤ u i)
    (hS : ∀ i ∈ J, Continuous (S i)) (hR : ∀ i ∈ J, Continuous (R i))
    (hB : ∀ i ∈ J, Continuous (B i)) (hBn : ∀ i ∈ J, ∀ t, ‖B i t‖ ≤ 1)
    {ell : ℝ} (hell : 0 < ell) :
    ‖(∑ i ∈ J, ∫ t in -(u i)..u i, (S i t)^2*B i t) -
      (∑ i ∈ J, ∫ t in -(u i)..u i, (S i t-R i t)^2*B i t)‖ ≤
      ell*(∑ i ∈ J, ∫ t in -(u i)..u i, ‖S i t‖^2) +
       (1+ell⁻¹)*(∑ i ∈ J, ∫ t in -(u i)..u i, ‖R i t‖^2) := by
  rw [← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  have hs (i) (hi : i ∈ J) : Continuous (fun t => ‖S i t‖^2) := (hS i hi).norm.pow 2
  have hr (i) (hi : i ∈ J) : Continuous (fun t => ‖R i t‖^2) := (hR i hi).norm.pow 2
  calc
    _ ≤ ∑ i ∈ J, (ell*(∫ t in -(u i)..u i, ‖S i t‖^2) +
      (1+ell⁻¹)*(∫ t in -(u i)..u i, ‖R i t‖^2)) := by
      apply sum_le_sum
      intro i hi
      have hs' : Continuous (fun t => (S i t)^2*B i t) := ((hS i hi).pow 2).mul (hB i hi)
      have hs'' : Continuous (fun t => (S i t-R i t)^2*B i t) := (((hS i hi).sub (hR i hi)).pow 2).mul (hB i hi)
      have huv : -u i ≤ u i := by linarith [hu i hi]
      rw [← intervalIntegral.integral_sub (hs'.intervalIntegrable _ _) (hs''.intervalIntegrable _ _)]
      apply (intervalIntegral.norm_integral_le_integral_norm huv).trans
      have hb' : Continuous (fun t => ell*‖S i t‖^2+(1+ell⁻¹)*‖R i t‖^2) :=
        (continuous_const.mul (hs i hi)).add (continuous_const.mul (hr i hi))
      have hm := intervalIntegral.integral_mono_on (μ := volume) huv
        ((hs'.sub hs'').norm.intervalIntegrable _ _) (hb'.intervalIntegrable _ _)
        (fun t _ => pointwise (S i t) (R i t) (B i t) ell hell (hBn i hi t))
      have hli : IntervalIntegrable (fun t => ell*‖S i t‖^2) volume (-u i) (u i) :=
        (continuous_const.mul (hs i hi)).intervalIntegrable _ _
      have hri : IntervalIntegrable (fun t => (1+ell⁻¹)*‖R i t‖^2) volume (-u i) (u i) :=
        (continuous_const.mul (hr i hi)).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hli hri,
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hm
      exact hm
    _ = _ := by rw [sum_add_distrib,← mul_sum,← mul_sum]

/-- Absorb the fixed log factor of the full prime sum and choose the
coefficient comparison weight N^(-b/82). -/
theorem normalize {N b D A F E : ℝ} (hN : 1 ≤ N) (hb : 0 < b)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hF : F ≤ A*N*(1+Real.log N)^2) (hE : E ≤ D*N^(1-b/41)) :
    let ell := N^(-b/82)
    ell*F+(1+ell⁻¹)*E ≤ (A+2*D)*N^(1-b/82)*(1+Real.log N)^2 := by
  dsimp only
  let ell := N^(-b/82)
  let L := 1+Real.log N
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hell : 0 < ell := Real.rpow_pos_of_pos hN0 _
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN]
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  have hI : ell⁻¹ = N^(b/82) := by dsimp [ell]; rw [← Real.rpow_neg hN0.le]; congr 1; ring
  have hP1 : ell*N = N^(1-b/82) := by
    dsimp [ell]
    conv_lhs => rhs; rw [← Real.rpow_one N]
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hP2 : N^(b/82)*N^(1-b/41) = N^(1-b/82) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hI' : 1+ell⁻¹ ≤ 2*N^(b/82) := by
    rw [hI]
    linarith [Real.one_le_rpow hN (show 0 ≤ b/82 by positivity)]
  have hFp := mul_le_mul_of_nonneg_left hF hell.le
  have hEp := (mul_le_mul_of_nonneg_left hE (show 0 ≤ 1+ell⁻¹ by positivity)).trans
    (mul_le_mul_of_nonneg_right hI' (by positivity : 0 ≤ D*N^(1-b/41)))
  change ell*F+(1+ell⁻¹)*E ≤ (A+2*D)*N^(1-b/82)*L^2
  have h₁ : ell*F ≤ A*N^(1-b/82)*L^2 := by
    refine hFp.trans_eq ?_
    rw [show ell*(A*N*L^2) = A*(ell*N)*L^2 by ring, hP1]
  have h₂ : (1+ell⁻¹)*E ≤ (2*D)*N^(1-b/82) := by
    refine hEp.trans_eq ?_
    rw [show 2*N^(b/82)*(D*N^(1-b/41)) = (2*D)*(N^(b/82)*N^(1-b/41)) by ring,hP2]
  exact (add_le_add h₁ (h₂.trans (le_mul_of_one_le_right (by positivity) hL2))).trans_eq (by ring)

#print axioms transfer
#print axioms normalize
end PintzFiniteArcDifference
