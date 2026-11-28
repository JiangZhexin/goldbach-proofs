import RichShiftEligibleGapPlug
import RichShiftNonprincipalDensity263

namespace RichShiftFinal263

theorem assembled_nonprincipal : RichShiftDensityCombine263.NonprincipalDensityBound := by
  obtain ⟨D,hD,H⟩ := RichShiftNonprincipalDensity263.estimate
  refine ⟨D,hD,?_⟩
  intro N P R M T b h Q hQ hN hR hRP hM hMN hPN hT hQR hTM hQN hTN hb hbh hh S hs
  apply H hQ hN hR hRP hM hMN hPN hT hQR hTM hQN hTN hb hbh hh S
  · exact fun j hj z hz => (hs j hj z hz).2
  · intro j hj z hz hχ
    have hk : 0 < j.1 := (hs j hj z hz).1
    have hp := (PintzActualNonprincipalCatalogue.mem_family hj).2
    have hc : j.2.conductor = j.1+1 := hp
    rw [hχ, DirichletCharacter.conductor_one] at hc
    omega

theorem exact_statement_of_public_zero_free_strip
    (hDir : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
      (7/8:ℝ) < s.re → ¬(χ = 1 ∧ s = 1) → χ.LFunction s ≠ 0) :
(have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.Icc (2 : ℕ) x1 | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∃ (x2 : ℝ) (x3 : ℝ), (0 : ℝ) < x2 ∧ (0 : ℝ) < x3 ∧ ∃ (x4 : ℕ), ∀ x5 ≥ x4, ∀ x7 ∈ Finset.Icc (1 : ℕ) (Nat.log (2 : ℕ) x5 / (2 : ℕ)), ↑{x9 ∈ Finset.Ico x5 ((2 : ℕ) * x5) | Even x9 ∧ ↑(x1 (x9 - (2 : ℕ) ^ x7)) < x2 * ↑x5 / Real.log ↑x5 ^ (2 : ℕ)}.card ≤ x3 * ↑x5 ^ (37 / 50 : ℝ)) := by
  apply RichShiftEligibleGapPlug.target_from_eligible_fixed_strip assembled_nonprincipal hDir
  intro s hs
  by_cases h : s = 1
  · subst s
    exact riemannZeta_one_ne_zero
  · rw [← DirichletCharacter.LFunction_modOne_eq]
    exact hDir (1 : DirichletCharacter ℂ 1) hs (fun hh => h hh.2)

#print axioms exact_statement_of_public_zero_free_strip
end RichShiftFinal263
