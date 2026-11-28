import PintzJutilaGammaRatio
import PintzJutilaLeftGrowth

open Set Complex DirichletCharacter PintzJutilaGammaRatio
open scoped ComplexConjugate

namespace PintzJutilaGammaEdge

private theorem half_z (a t : ℝ) : z a t/2 = z (a/2) (t/2) := by
  unfold z
  push_cast
  ring

private theorem gammaR_norm (a t : ℝ) :
    ‖Gammaℝ (z a t)‖ = Real.pi^(-a/2)*‖Gamma (z (a/2) (t/2))‖ := by
  rw [Gammaℝ, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    show -z a t / 2 = -(z a t / 2) by ring, half_z,
    Complex.neg_re,re_z]
  congr 2 <;> ring

private theorem gamma_sym (a t : ℝ) : ‖Gamma (z a (-t))‖ = ‖Gamma (z a t)‖ := by
  have H : z a (-t) = conj (z a t) := by apply Complex.ext <;> simp [z]
  rw [H,Gamma_conj,norm_conj]

/-- The two standard archimedean parity factors on the edge Re(s)=0
have a uniform square-root ratio (also valid if the denominator is
zero under Lean's zero-division convention). -/
theorem arch_edge :
    ∃ C : ℝ, 0 < C ∧ ∀ (t k : ℝ), k = 0 ∨ k = 1 →
      ‖Gammaℝ (z (1+k) (-t))‖ / ‖Gammaℝ (z k t)‖ ≤
        C*(1+|t|)^(1/2:ℝ) := by
  obtain ⟨C,hC,hR⟩ := gamma_ratio (A := (1/2:ℝ)) (B := 1) (by norm_num) (by norm_num)
  let A := Real.pi^(-(1/2:ℝ))
  have hA : 0 < A := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨A*C,mul_pos hA hC,?_⟩
  intro t k hk
  let u := 1+|t|/2
  let v := 1+|t|
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have huv : u ≤ v := by dsimp [u,v]; linarith [abs_nonneg t]
  have hpow : u^(1/2:ℝ) ≤ v^(1/2:ℝ) :=
    Real.rpow_le_rpow hu.le huv (by norm_num)
  rcases hk with rfl|rfl
  · by_cases ht : t = 0
    · subst t
      simp [z, Gammaℝ, Complex.Gamma_zero]
      positivity
    have htC : z 0 (t/2) ≠ 0 := by
      intro he
      have h := congrArg Complex.im he
      simp only [im_z,Complex.zero_im] at h
      exact ht (by linarith)
    have htNorm : ‖z 0 (t/2)‖ = |t|/2 := by
      unfold z
      simp [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_div]
    have hg : ‖Gamma (z 1 (t/2))‖ =
        (|t|/2)*‖Gamma (z 0 (t/2))‖ := by
      rw [show z 1 (t/2)=z 0 (t/2)+1 by dsimp [z]; simp [add_comm],
        Gamma_add_one _ htC,norm_mul,htNorm]
    have hn : 0 < |t|/2 := by exact div_pos (abs_pos.mpr ht) (by norm_num)
    have hgn : ‖Gamma (z 1 (t/2))‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      refine Gamma_ne_zero ?_
      intro m h
      have hh := congrArg Complex.re h
      simp at hh
      linarith [Nat.cast_nonneg (α:=ℝ) m]
    have hd : ‖Gamma (z 0 (t/2))‖ ≠ 0 := fun h => hgn (by simp [hg,h])
    have hratio :
        ‖Gammaℝ (z (1+0) (-t))‖ / ‖Gammaℝ (z 0 t)‖ =
          A*(|t|/2)*(‖Gamma (z (1/2) (t/2))‖/‖Gamma (z 1 (t/2))‖) := by
      rw [gammaR_norm,gammaR_norm]
      norm_num only [add_zero, neg_div, zero_div, neg_zero, Real.rpow_zero, one_mul]
      rw [gamma_sym, hg]
      dsimp [A]
      field_simp [hd,hn.ne']
      <;> ring
    rw [hratio]
    have hR' := hR (1/2) (by norm_num) 1 (by norm_num) (t/2)
    have hR'' :
        ‖Gamma (z (1/2) (t/2))‖ / ‖Gamma (z 1 (t/2))‖ ≤ C*u^(-1/2:ℝ) := by
      rw [show (1/2-1:ℝ)=(-1/2:ℝ) by norm_num] at hR'
      simpa [u,abs_div] using hR'
    calc
      _ ≤ A*(|t|/2)*(C*u^(-1/2:ℝ)) := mul_le_mul_of_nonneg_left hR'' (by positivity)
      _ ≤ A*u*(C*u^(-1/2:ℝ)) := by
        have he : |t|/2 ≤ u := by dsimp [u]; linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hA.le) (by positivity)
      _ = A*C*u^(1/2:ℝ) := by
        rw [show A*u*(C*u^(-1/2:ℝ))=A*C*(u*u^(-1/2:ℝ)) by ring]
        congr 1
        conv_lhs => lhs; rw [← Real.rpow_one u]
        rw [← Real.rpow_add hu]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  · have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hg : ‖Gamma (z (1/2) (t/2))‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      refine Gamma_ne_zero ?_
      intro m hm
      have hh := congrArg Complex.re hm
      simp at hh
      linarith [Nat.cast_nonneg (α:=ℝ) m]
    have heq :
        ‖Gammaℝ (z (1+1) (-t))‖ / ‖Gammaℝ (z 1 t)‖ =
          A*(‖Gamma (z 1 (t/2))‖/‖Gamma (z (1/2) (t/2))‖) := by
      rw [gammaR_norm,gammaR_norm]
      norm_num only [one_add_one_eq_two, neg_div, show (2/2:ℝ)=1 by norm_num]
      rw [gamma_sym]
      have hA2 : Real.pi^(-1:ℝ)=A*A := by
        dsimp [A]
        rw [← Real.rpow_add Real.pi_pos]
        norm_num
      rw [hA2]
      change A*A*‖Gamma (z 1 (t/2))‖/(A*‖Gamma (z (1/2) (t/2))‖) = _
      field_simp [hA.ne',hg]
    rw [heq]
    have hh := hR 1 (by norm_num) (1/2) (by norm_num) (t/2)
    have H : ‖Gamma (z 1 (t/2))‖ / ‖Gamma (z (1/2) (t/2))‖ ≤ C*u^(1/2:ℝ) := by
      rw [show (1-1/2:ℝ) = (1/2:ℝ) by norm_num] at hh
      simpa [u,abs_div] using hh
    exact (mul_le_mul_of_nonneg_left H hA.le).trans
      (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hpow (by positivity))

#print axioms arch_edge
end PintzJutilaGammaEdge
