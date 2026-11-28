import RichShiftDensityGroup263
import RichShiftLowReal263
import RichShiftZetaLog263

open Finset PintzSieveToHybrid
namespace RichShiftDensityCombine263

-- This is the sole input still needed from the short-Möbius detector in the section 8 estimate.
def NonprincipalDensityBound : Prop :=
    ∃ D : ℝ → ℝ, (∀ b, 0 ≤ D b) ∧ ∀ {N P R M T b h : ℝ} {Q : ℕ},
      1 ≤ Q → 2 ≤ N → 1 ≤ R → R ≤ P → 1 ≤ M →
      M ≤ N^(1/2:ℝ) → P ≤ N^(263/1000:ℝ) →
      0 ≤ T → (Q:ℝ) ≤ 2*R → T ≤ 4*P*M/R →
      (Q:ℝ) ≤ N → T ≤ N →
      0 < b → b ≤ h → h ≤ 533/2000 →
      ∀ S : PintzDyadicStripCount.Char → Finset ℂ,
      (∀ j ∈ family Q, ∀ z ∈ S j, 0 < j.1 ∧
        j.2.LFunction z = 0 ∧ z.re ∈ Set.Icc (1-h) (1-b) ∧ |z.im| ≤ T) →
    M⁻¹ * N^(-2*h) * (∑ j ∈ family Q, ∑ z ∈ S j, (analyticOrderNatAt j.2.LFunction z : ℝ)) ≤
      D b * (1+Real.log N)^10 * N^(-h/40)

theorem combined (hNon : NonprincipalDensityBound) : RichShiftDensityGroup263.DensityBound := by
  classical
  obtain ⟨Dn,hDn,Hn⟩ := hNon
  obtain ⟨Dz,hDz,Hz⟩ := RichShiftZetaLog263.estimate_small
  obtain ⟨Ez,hEz,Hze⟩ := RichShiftZetaLog263.estimate_large
  let Cl : ℝ := 36*(18/Real.log (55/52)+11/Real.log (12/11))
  have hCl : 0 ≤ Cl := by
    have H₁ : 0 < Real.log (55/52) := Real.log_pos (by norm_num)
    have H₂ : 0 < Real.log (12/11) := Real.log_pos (by norm_num)
    dsimp [Cl]; positivity
  refine ⟨fun b => Dn b + Dz b + Ez + Cl, fun b => by positivity [hDn b,hDz b],?_⟩
  intro N P R M T b h Q hQ hN hR hRP hM hMN hPN hT hQR hTM hQN hTN hb hbh hh S hs
  have hN1 : 1 ≤ N := by linarith
  have hp1 : 1 ≤ P := hR.trans hRP
  have hlog : 1 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN1]
  have hlpow : Real.log N ≤ (1+Real.log N)^10 := by
    have H := pow_le_pow_right₀ hlog (by norm_num : (1:ℕ) ≤ 10)
    rw [pow_one] at H
    linarith
  have hp0 : 0 ≤ (1+Real.log N)^10 := by positivity
  have hr0 : 0 ≤ N^(-h/40) := by positivity
  by_cases hh' : h ≤ 533/2000
  · let j₀ := PintzWeightedZetaCount.principal
    let U : PintzDyadicStripCount.Char → Finset ℂ := fun j => if j=j₀ then ∅ else S j
    have hj₀ : j₀ ∈ family Q := PintzUniformDensitySubsets.principal_mem hQ
    have hT' : T ≤ 4*P*M := hTM.trans (div_le_self (by positivity) hR)
    have hs0 (z : ℂ) (hz : z ∈ S j₀) :
        riemannZeta z=0 ∧ z.re ∈ Set.Icc (1-h) (1-b) ∧ |z.im| ≤ T := by
      have H := hs j₀ hj₀ z hz
      change (1 : DirichletCharacter ℂ 1).LFunction z = 0 ∧ _ at H
      rwa [DirichletCharacter.LFunction_modOne_eq] at H
    have hsu (j) (hj : j ∈ family Q) (z : ℂ) (hz : z ∈ U j) : 0 < j.1 ∧
        j.2.LFunction z = 0 ∧ z.re ∈ Set.Icc (1-h) (1-b) ∧ |z.im| ≤ T := by
      have hjne : j ≠ j₀ := by intro he; simp [U,he] at hz
      have hz' : z ∈ S j := by simpa [U,hjne] using hz
      refine ⟨?_,hs j hj z hz'⟩
      obtain ⟨k,χ⟩ := j
      by_contra! h
      change k ≤ 0 at h
      have hk : k = 0 := by omega
      subst k
      have hχ : χ = 1 := DirichletCharacter.level_one' χ (by omega)
      exact hjne (by rw [hχ]; rfl)
    have hn := Hn hQ hN hR hRP hM hMN hPN hT hQR hTM hQN hTN hb hbh hh' U hsu
    have hz : M⁻¹*N^(-2*h)*(∑ z ∈ S j₀, (Zeta23.zetaZeroConfig.mult z:ℝ)) ≤
        (Dz b + Ez)*(1+Real.log N)^10*N^(-h/40) := by
      by_cases hcase : h ≤ 67/500
      · exact (Hz hN1 hp1 hM hPN hT hTN hT' hb hbh hcase _ hs0).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hp0) hr0)
      · exact (Hze hN1 hp1 hM hPN hT hTN hT' hb (le_of_lt (lt_of_not_ge hcase)) hh _ hs0).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [hDz b]) hp0) hr0)
    have hsplit : (∑ j ∈ family Q, ∑ z ∈ S j, (analyticOrderNatAt j.2.LFunction z:ℝ)) =
        (∑ j ∈ family Q, ∑ z ∈ U j, (analyticOrderNatAt j.2.LFunction z:ℝ)) +
        ∑ z ∈ S j₀, (Zeta23.zetaZeroConfig.mult z:ℝ) := by
      rw [← sum_erase_add _ _ hj₀]
      have he : (∑ j ∈ family Q, ∑ z ∈ U j, (analyticOrderNatAt j.2.LFunction z:ℝ)) =
          ∑ j ∈ (family Q).erase j₀, ∑ z ∈ S j, (analyticOrderNatAt j.2.LFunction z:ℝ) := by
        rw [← sum_erase_add _ _ hj₀]
        simp only [U, if_pos rfl, sum_empty, add_zero]
        apply sum_congr rfl
        intro j hj
        rw [if_neg (mem_erase.mp hj).1]
      rw [he]
      simp [j₀,PintzUniformDensitySubsets.multiplicity_principal]
    rw [hsplit,mul_add]
    refine (add_le_add hn hz).trans ?_
    have H : Dn b + (Dz b+Ez) ≤ Dn b+Dz b+Ez+Cl := by linarith
    calc
      _ = (Dn b + (Dz b+Ez))*(1+Real.log N)^10*N^(-h/40) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H hp0) hr0
  · have H := RichShiftLowReal263.actual_low_real_budget hN1 hPN
      (show 0<R by linarith) hRP hM hQR hT hTM (le_of_lt (lt_of_not_ge hh')) S
      (fun j hj z hz => ⟨by linarith [(hs j hj z hz).2.1.1],
        by linarith [(hs j hj z hz).2.1.2]⟩) (fun j hj z hz => (hs j hj z hz).2.2)
    refine H.trans (mul_le_mul_of_nonneg_right ?_ hr0)
    have hC := PintzLowRealBlock.actualC_log_bound hN hQ (by linarith) hT hTN
    have hC' : 36*PintzLowRealBlock.actualC Q T ≤ Cl*Real.log N := by
      dsimp only [Cl]
      nlinarith only [hC]
    exact hC'.trans ((mul_le_mul_of_nonneg_left hlpow hCl).trans
      (mul_le_mul_of_nonneg_right (by linarith [hDn b,hDz b]) hp0))

#print axioms combined
end RichShiftDensityCombine263
