import PintzJutilaGammaEdge

open Complex DirichletCharacter PintzJutilaGammaRatio

namespace PintzJutilaEdgeL
set_option maxHeartbeats 600000

private theorem abs_s (t : ℝ) : ‖z 0 t‖ = |t| := by simp [z,Real.norm_eq_abs]

private theorem one_sub_z (t : ℝ) : (1:ℂ)-z 0 t = z 1 (-t) := by
  unfold z
  push_cast
  ring

private theorem z_add_one (a t : ℝ) : z a t+1=z (a+1) t := by
  unfold z
  push_cast
  ring

private theorem gammaR_nonzero_of_pos {s : ℂ} (h : 0 < s.re) :
    Gammaℝ s ≠ 0 := by
  rw [ne_eq,Gammaℝ_eq_zero_iff]
  rintro ⟨n,hn⟩
  have hnR := congrArg Complex.re hn
  simp at hnR
  linarith [Nat.cast_nonneg (α:=ℝ) n]

private theorem char_ratio {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (A t : ℝ) (hArch : ∀ t k : ℝ, k=0 ∨ k=1 →
      ‖Gammaℝ (z (1+k) (-t))‖/‖Gammaℝ (z k t)‖ ≤ A*(1+|t|)^(1/2:ℝ)) :
    ‖gammaFactor χ⁻¹ (1-z 0 t)‖/‖gammaFactor χ (z 0 t)‖ ≤ A*(1+|t|)^(1/2:ℝ) := by
  rw [one_sub_z]
  rcases χ.even_or_odd with he|ho
  · have he1 : χ (-1) = 1 := he
    have hei : (χ⁻¹).Even := by
      change χ⁻¹ (-1)=1
      rw [MulChar.inv_apply_eq_inv',he1,inv_one]
    rw [hei.gammaFactor_def,he.gammaFactor_def]
    simpa only [add_zero] using hArch t 0 (Or.inl rfl)
  · have ho1 : χ (-1) = -1 := ho
    have hoi : (χ⁻¹).Odd := by
      change χ⁻¹ (-1) = (-1:ℂ)
      rw [MulChar.inv_apply_eq_inv',ho1,inv_neg,inv_one]
    rw [hoi.gammaFactor_def,ho.gammaFactor_def,z_add_one,z_add_one,zero_add]
    exact hArch t 1 (Or.inr rfl)

/-- The precise critical left boundary in Jutila Lemma 6 and the
half-exponent saving, without a general convexity theorem. -/
theorem edge_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      1 < q → χ.IsPrimitive → ∀ t : ℝ,
      ‖χ.LFunction (z 0 t)‖ ≤ C*((q:ℝ)*(1+|t|))^(1/2+ε) := by
  obtain ⟨A,hA,hArch⟩ := PintzJutilaGammaEdge.arch_edge
  refine ⟨A*(2+(4:ℝ)^ε/ε),by positivity,?_⟩
  intro q _ χ hq hp t
  let s := z 0 t
  let D := (q:ℝ)*(1+|t|)
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq.le
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le hq1 (by linarith [abs_nonneg t])
  have hD0 : 0 < D := by linarith
  have hs : s.re = 0 := re_z 0 t
  have hsr : (1-s).re = 1 := by simp [hs]
  have hχ : χ ≠ 1 := by
    intro h
    rw [IsPrimitive,h,conductor_one] at hp
    omega
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have hL := PintzJutilaLeftGrowth.right_edge χ⁻¹ hχi (s := 1-s) hsr.ge
  have hS : ‖(1:ℂ)-s‖ ≤ 1+|t| := by
    exact (norm_sub_le _ _).trans_eq (by rw [norm_one,show ‖s‖ = |t| from abs_s t])
  have hlog : Real.log (2*(q:ℝ)*(1+‖(1:ℂ)-s‖)) ≤ Real.log (4*D) := by
    apply Real.log_le_log (by positivity)
    have HH := mul_le_mul_of_nonneg_left hS (show 0 ≤ 2*(q:ℝ) by positivity)
    dsimp [D]
    nlinarith only [HH,mul_nonneg (show (0:ℝ) ≤ q by positivity) (abs_nonneg t)]
  have hLD : ‖(χ⁻¹).LFunction (1-s)‖ ≤ (2+(4:ℝ)^ε/ε)*D^ε := by
    have hDP : 1 ≤ D^ε := Real.one_le_rpow hD hε.le
    have hlogR : Real.log (4*D) ≤ ((4*D)^ε)/ε := by
      have r := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (show 0 < 4*D by positivity) ε)
      rw [Real.log_rpow (show 0 < 4*D by positivity)] at r
      exact (le_div_iff₀ hε).2 (by linarith)
    rw [Real.mul_rpow (by norm_num) hD0.le] at hlogR
    have h2 := mul_le_mul_of_nonneg_left hDP (show (0:ℝ) ≤ 2 by norm_num)
    calc
      _ ≤ 2+Real.log (4*D) := hL.trans (add_le_add_right hlog 2)
      _ ≤ (2+(4:ℝ)^ε/ε)*D^ε := by
        rw [show (4:ℝ)^ε*D^ε/ε=((4:ℝ)^ε/ε)*D^ε by ring] at hlogR
        linarith only [hlogR,h2]
  have hRat : ‖gammaFactor χ⁻¹ (1-s)‖/‖gammaFactor χ s‖ ≤ A*(1+|t|)^(1/2:ℝ) :=
    char_ratio χ A t hArch
  have hγ' : gammaFactor χ⁻¹ (1-s) ≠ 0 := by
    rcases (χ⁻¹).even_or_odd with h|h
    · rw [h.gammaFactor_def]
      exact gammaR_nonzero_of_pos (by rw [hsr]; norm_num)
    · rw [h.gammaFactor_def]
      exact gammaR_nonzero_of_pos (by simp only [Complex.add_re,hsr,Complex.one_re]; norm_num)
  by_cases hγ : gammaFactor χ s = 0
  · rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inr (ne_of_gt hq)),hγ,div_zero,norm_zero]
    positivity
  · rw [PintzJutilaLeftGrowth.functional_abs χ hq hp hγ hγ',hs,sub_zero]
    calc
      _ ≤ ((q:ℝ)^(1/2:ℝ)*(A*(1+|t|)^(1/2:ℝ)))*((2+(4:ℝ)^ε/ε)*D^ε) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hRat (by positivity)) hLD (by positivity) (by positivity)
      _ = A*(2+(4:ℝ)^ε/ε)*D^(1/2+ε) := by
        rw [Real.rpow_add hD0,show D^(1/2:ℝ)=(q:ℝ)^(1/2:ℝ)*(1+|t|)^(1/2:ℝ) by
          dsimp [D]; rw [Real.mul_rpow (by positivity) (by positivity)]]
        ring
      _ = _ := rfl

#print axioms edge_bound
end PintzJutilaEdgeL
