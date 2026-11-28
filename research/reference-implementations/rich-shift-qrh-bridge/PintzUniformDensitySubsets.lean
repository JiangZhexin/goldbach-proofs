import PintzUniformDensityLog
import PintzLowRealBlock

open Finset PintzSieveToHybrid PintzUniformDensityLog

namespace PintzUniformDensitySubsets

abbrev Char := PintzDyadicStripCount.Char

theorem primitive_principal_unique {Q : ℕ} {j : PintzDyadicStripCount.Char}
    (hj : j ∈ family Q) (he : j.2 = 1) : j = PintzWeightedZetaCount.principal := by
  obtain ⟨k,χ⟩ := j
  have hprim := (PintzActualNonprincipalCatalogue.mem_family hj).2
  have hχ : χ = 1 := he
  let : NeZero (k+1) := ⟨by omega⟩
  change χ.IsPrimitive at hprim
  rw [hχ, DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hprim
  have hk : k = 0 := by omega
  subst k
  subst χ
  rfl

theorem multiplicity_principal (z : ℂ) :
    analyticOrderNatAt PintzWeightedZetaCount.principal.2.LFunction z = Zeta23.zetaZeroConfig.mult z := by
  change analyticOrderNatAt (1 : DirichletCharacter ℂ 1).LFunction z = _
  rw [DirichletCharacter.LFunction_modOne_eq]
  rfl

theorem principal_mem {Q : ℕ} (hQ : 1 ≤ Q) : PintzWeightedZetaCount.principal ∈ family Q := by
  classical
  rw [family, mem_sigma]
  exact ⟨mem_range.mpr (by change 0 < Q; omega), mem_filter.mpr ⟨mem_univ _, by
    simp [PintzWeightedZetaCount.principal, DirichletCharacter.isPrimitive_def,
      DirichletCharacter.conductor_one]⟩⟩

theorem high :
    ∃ D : ℝ → ℝ, (∀ b, 0 ≤ D b) ∧ ∀ {N P R M T b h : ℝ} {Q : ℕ}
      (hQ : 1 ≤ Q) (hN : 1 ≤ N) (hR : 1 ≤ R) (hRP : R ≤ P) (hM : 1 ≤ M)
      (hMN : M ≤ N^(1/2:ℝ)) (hPN : P ≤ N^(21/100:ℝ))
      (hT : 0 ≤ T) (hQR : (Q:ℝ) ≤ 2*R) (hTM : T ≤ 2*P*M/R)
      (hQN : (Q:ℝ) ≤ N) (hTN : T ≤ N)
      (hb : 0 < b) (hbh : b ≤ h) (hh : h ≤ 11/50)
      (S : PintzDyadicStripCount.Char → Finset ℂ)
      (hS : ∀ j ∈ family Q, ∀ z ∈ S j,
        j.2.LFunction z = 0 ∧ z.re ∈ Set.Icc (1-h) (1-b) ∧ |z.im| ≤ T),
    M⁻¹ * N^(-2*h) * (∑ j ∈ family Q, ∑ z ∈ S j, (analyticOrderNatAt j.2.LFunction z : ℝ)) ≤
      D b * (1+Real.log N)^10 * N^(-h/40) := by
  classical
  obtain ⟨Az,hAz,hZ⟩ := PintzUniformDensityLog.zeta
  obtain ⟨An,hAn,hNpr⟩ := PintzUniformDensityLog.nonprincipal
  refine ⟨fun b => |uniformConstant Az b + uniformConstant An b|, fun _ => abs_nonneg _, ?_⟩
  intro N P R M T b h Q hQ hN hR hRP hM hMN hPN hT hQR hTM hQN hTN hb hbh hh S hS
  let j₀ := PintzWeightedZetaCount.principal
  have hj₀ : j₀ ∈ family Q := principal_mem hQ
  have hP : 1 ≤ P := hR.trans hRP
  have hTM' : T ≤ 2*P*M := hTM.trans (div_le_self (by positivity) hR)
  have hs : 0 < 1-h := by linarith
  have hrσ : (39/50:ℝ) ≤ 1-h := by linarith
  have hσb : 1-h ≤ 1-b := by linarith
  let Z := PintzActualWeightedZeta.catalogue T b (1-h) hb hs
  let U := PintzActualNonprincipalCatalogue.catalogue T b (1-h) hs.le hb.le
  have hzs : S j₀ ⊆ Z := by
    intro z hz
    have H := hS j₀ hj₀ z hz
    apply (PintzActualWeightedZeta.mem_catalogue T b (1-h) hb hs z).mpr
    change (1:DirichletCharacter ℂ 1).LFunction z = 0 ∧ _ at H
    rwa [DirichletCharacter.LFunction_modOne_eq] at H
  have hns (j) (hj : j ∈ family Q) (hne : j ≠ j₀) : S j ⊆ U j := by
    intro z hz
    apply (PintzActualNonprincipalCatalogue.mem_catalogue T b (1-h) hs.le hb.le j z).mpr
    exact ⟨fun he => hne (primitive_principal_unique hj he), hS j hj z hz⟩
  let f (j : PintzDyadicStripCount.Char) (z : ℂ) : ℝ := analyticOrderNatAt j.2.LFunction z
  have hle : (∑ j ∈ family Q, ∑ z ∈ S j, f j z) ≤
      (∑ z ∈ Z, (Zeta23.zetaZeroConfig.mult z : ℝ)) + (∑ j ∈ family Q, ∑ z ∈ U j, f j z) := by
    rw [← Finset.sum_erase_add _ _ hj₀, add_comm]
    apply add_le_add
    · simpa only [f, j₀, multiplicity_principal] using
        (sum_le_sum_of_subset_of_nonneg hzs (fun z _ _ => Nat.cast_nonneg (α := ℝ)
          (Zeta23.zetaZeroConfig.mult z)))
    · calc
        _ ≤ ∑ j ∈ (family Q).erase j₀, ∑ z ∈ U j, f j z := by
          apply sum_le_sum
          intro j hj
          obtain ⟨jne,jmem⟩ := mem_erase.mp hj
          exact sum_le_sum_of_subset_of_nonneg (hns j jmem jne) (fun _ _ _ => by unfold f; positivity)
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ =>
          sum_nonneg (fun _ _ => by unfold f; positivity))
  have HZ := hZ hN hP hM hMN hPN hT hTM' hTN hb hrσ hσb
  have HN := hNpr hQ hN hR hRP hM hMN hPN hT hQR hTM hQN hTN hb hrσ hσb
  have he : 1-(1-h) = h := by ring
  simp only [he] at HZ HN
  have HH := mul_le_mul_of_nonneg_left hle (show 0 ≤ M⁻¹*N^(-2*h) by positivity)
  simp only [mul_add] at HH
  refine HH.trans ((add_le_add HZ HN).trans ?_)
  calc
    _ = (uniformConstant Az b + uniformConstant An b) * (1+Real.log N)^10 * N^(-h/40) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) (by positivity)

theorem low {N P R M T h : ℝ} {Q : ℕ}
    (hQ : 1 ≤ Q) (hN : 2 ≤ N) (hP : P ≤ N^(21/100:ℝ))
    (hR : 0 < R) (hRP : R ≤ P) (hM : 1 ≤ M)
    (hQR : (Q:ℝ) ≤ 2*R) (hQN : (Q:ℝ) ≤ N)
    (hT : 0 ≤ T) (hTupper : T ≤ 4*P*M/R) (hTN : T ≤ N)
    (hh : (11/50:ℝ) ≤ h) (hhmax : h ≤ 1/2)
    (S : PintzDyadicStripCount.Char → Finset ℂ)
    (hz : ∀ j ∈ family Q, ∀ ρ ∈ S j, 1/2 ≤ ρ.re ∧ ρ.re < 1)
    (hx : ∀ j ∈ family Q, ∀ ρ ∈ S j, |ρ.im| ≤ T) :
    M⁻¹ * N^(-2*h) * (∑ j ∈ family Q, ∑ ρ ∈ S j, (analyticOrderNatAt j.2.LFunction ρ : ℝ)) ≤
      (36*(18/Real.log (55/52)+11/Real.log (12/11))) * (1+Real.log N)^10 * N^(-h/40) := by
  have h1 : 1 ≤ N := by linarith
  have H := PintzLowRealBlock.actual_low_real_budget h1 hP hR hRP hM hQR hT hTupper hh S hz hx
  have HC := PintzLowRealBlock.actualC_log_bound hN hQ (by linarith) hT hTN
  have HD₁ : 0 < Real.log (55/52) := Real.log_pos (by norm_num)
  have HD₂ : 0 < Real.log (12/11) := Real.log_pos (by norm_num)
  have hln : 0 ≤ Real.log N := Real.log_nonneg h1
  have hl : Real.log N ≤ (1+Real.log N)^10 := by
    refine (le_add_of_nonneg_left zero_le_one).trans ?_
    simpa using pow_le_pow_right₀ (show 1 ≤ 1+Real.log N by linarith)
      (show (1:ℕ) ≤ 10 by decide)
  refine H.trans ?_
  calc
    _ ≤ (36*((18/Real.log (55/52)+11/Real.log (12/11))*Real.log N))*N^(-(1/50:ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left HC (by norm_num)) (by positivity)
    _ = (36*(18/Real.log (55/52)+11/Real.log (12/11)))*Real.log N*N^(-(1/50:ℝ)) := by ring
    _ ≤ _ := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hl (by positivity))
        (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (by positivity) (by positivity)

/-- Uniform bound over both ranges and through the full dyadic height.
The high range is evaluated at the comparable larger scale 4N and 2M. -/
theorem combined :
    ∃ D : ℝ → ℝ, (∀ b, 0 ≤ D b) ∧ ∀ {N P R M T b h : ℝ} {Q : ℕ}
      (_hQ : 1 ≤ Q) (_hN : 2 ≤ N) (_hR : 1 ≤ R) (_hRP : R ≤ P) (_hM : 1 ≤ M)
      (_hMN : M ≤ N^(1/2:ℝ)) (_hPN : P ≤ N^(21/100:ℝ))
      (_hT : 0 ≤ T) (_hQR : (Q:ℝ) ≤ 2*R) (_hTM : T ≤ 4*P*M/R)
      (_hQN : (Q:ℝ) ≤ N) (_hTN : T ≤ N)
      (_hb : 0 < b) (_hbh : b ≤ h) (_hh : h ≤ 1/2)
      (S : PintzDyadicStripCount.Char → Finset ℂ)
      (_hS : ∀ j ∈ family Q, ∀ z ∈ S j,
        j.2.LFunction z = 0 ∧ z.re ∈ Set.Icc (1-h) (1-b) ∧ |z.im| ≤ T),
    M⁻¹ * N^(-2*h) * (∑ j ∈ family Q, ∑ z ∈ S j, (analyticOrderNatAt j.2.LFunction z : ℝ)) ≤
      D b * (1+Real.log N)^10 * N^(-h/40) := by
  obtain ⟨D,hD,hH⟩ := high
  let C : ℝ := 36*(18/Real.log (55/52)+11/Real.log (12/11))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity [Real.log_pos (show (1:ℝ) < 55/52 by norm_num),
      Real.log_pos (show (1:ℝ) < 12/11 by norm_num)]
  let E : ℝ := 8*(1+Real.log 4)^10
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨fun b => E*D b+C, fun b => by positivity [hD b],?_⟩
  intro N P R M T b h Q hQ hN hR hRP hM hMN hPN hT hQR hTM hQN hTN hb hbh hh S hS
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hh0 : 0 ≤ h := by linarith
  by_cases hu : h ≤ 11/50
  · have hM4 : 2*M ≤ (4*N)^(1/2:ℝ) := by
      rw [Real.mul_rpow (by norm_num) hN0.le]
      have he : (4:ℝ)^(1/2:ℝ) = 2 := by
        rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
        norm_num
      rw [he]
      linarith
    have hP4 := hPN.trans (Real.rpow_le_rpow hN0.le
      (show N ≤ 4*N by linarith) (by norm_num : (0:ℝ) ≤ 21/100))
    have ht4 : T ≤ 2*P*(2*M)/R := by
      convert hTM using 2 <;> ring
    have H := hH hQ (show 1 ≤ 4*N by linarith) hR hRP (show 1 ≤ 2*M by linarith)
      hM4 hP4 hT hQR ht4 (hQN.trans (by linarith)) (hTN.trans (by linarith)) hb hbh hu S hS
    let V := ∑ j ∈ family Q, ∑ z ∈ S j, (analyticOrderNatAt j.2.LFunction z : ℝ)
    change (2*M)⁻¹*(4*N)^(-2*h)*V ≤ _ at H
    have H' := mul_le_mul_of_nonneg_left H (show 0 ≤ 2*(4:ℝ)^(2*h) by positivity)
    have he : 2*(4:ℝ)^(2*h)*((2*M)⁻¹*(4*N)^(-2*h)*V) = M⁻¹*N^(-2*h)*V := by
      rw [Real.mul_rpow (by norm_num) hN0.le, mul_inv, show (-2*h) = -(2*h) by ring,
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
      field_simp [show (4:ℝ)^(2*h) ≠ 0 by positivity]
    rw [he] at H'
    have h4 : (4:ℝ)^(2*h) ≤ 4 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) (by linarith : 2*h ≤ 1)
    have hl : 1+Real.log (4*N) ≤ (1+Real.log 4)*(1+Real.log N) := by
      rw [Real.log_mul (by norm_num) hN0.ne']
      nlinarith [mul_nonneg (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)) (Real.log_nonneg hN1)]
    have hn : (4*N)^(-h/40) ≤ N^(-h/40) :=
      Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
    refine H'.trans ?_
    calc
      _ ≤ (2*4)*(D b * (((1+Real.log 4)*(1+Real.log N))^10) * N^(-h/40)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h4 (by norm_num)
        · simp only [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (hD b)
          exact mul_le_mul (pow_le_pow_left₀ (by
            have H := Real.log_nonneg (show 1 ≤ 4*N by linarith)
            linarith) hl 10) hn (by positivity) (by positivity)
        · positivity [hD b]
        · norm_num
      _ = (E*D b)* (1+Real.log N)^10 * N^(-h/40) := by dsimp [E]; ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show E*D b ≤ E*D b+C by linarith)
          (by positivity)) (by positivity)
  · have H := low hQ hN hPN (show 0 < R by linarith) hRP hM hQR hQN hT hTM hTN
      (le_of_lt (lt_of_not_ge hu)) hh S
      (fun j hj z hz => ⟨by linarith [(hS j hj z hz).2.1.1],by linarith [(hS j hj z hz).2.1.2]⟩)
      (fun j hj z hz => (hS j hj z hz).2.2)
    refine H.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (show C ≤ E*D b+C by linarith [mul_nonneg hE (hD b)]) (by positivity)) (by positivity)

#print axioms combined
#print axioms high
#print axioms low
end PintzUniformDensitySubsets
