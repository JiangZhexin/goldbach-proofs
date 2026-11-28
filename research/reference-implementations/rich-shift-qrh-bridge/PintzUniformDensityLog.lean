import PintzDetectorLogBudget

open Finset PintzSieveToHybrid PintzDetectorLogBudget

namespace PintzUniformDensityLog

theorem ceiling_budget {A N q T : ℝ} (hA : 0 ≤ A) (hN : 1 ≤ N)
    (hq0 : 0 < q) (hq : q ≤ N) (hT : 0 ≤ T) (hTN : T ≤ N) :
    (⌈A*Real.log (q*(T+5))⌉₊:ℝ) ≤ (A*(Real.log 6+2)+1)*(1+Real.log N) := by
  have hN0 : 0 < N := by linarith
  have hT5 : T+5 ≤ 6*N := by linarith
  have hp : q*(T+5) ≤ 6*N^2 := by
    have H := mul_le_mul hq hT5 (by positivity) (by positivity)
    nlinarith only [H]
  have H := Real.log_le_log (show 0 < q*(T+5) by positivity) hp
  rw [Real.log_mul (by norm_num : (6:ℝ) ≠ 0) (by positivity), Real.log_pow, Nat.cast_ofNat] at H
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have h6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have H' := mul_le_mul_of_nonneg_left H hA
  have hn : 0 ≤ A*(Real.log 6+2*Real.log N) := by positivity
  have hceil := Nat.ceil_lt_add_one hn
  calc
    _ ≤ (⌈A*(Real.log 6+2*Real.log N)⌉₊:ℝ) := by exact_mod_cast Nat.ceil_mono H'
    _ ≤ A*(Real.log 6+2*Real.log N)+1 := hceil.le
    _ ≤ _ := by nlinarith only [hlog, mul_nonneg hA (mul_nonneg h6 hlog), hA]

noncomputable def uniformConstant (A b : ℝ) : ℝ :=
  let C := PintzDensityCutoffBridge.detectorConstant b
  let c := min 1 ((2:ℝ)^b-1)/2
  let D := A*(Real.log 6+2)+1
  let E := D*(1+(3+Real.log (2*C))/Real.log 2)^2*(4+Real.log (2*C))^7
  (1584/c^2)*E*C^(11/25:ℝ)

theorem renormalize {A b N P M h q T : ℝ} {L J B : ℕ}
    (hA : 0 ≤ A) (hb : 0 < b) (hN : 1 ≤ N) (hP : 0 ≤ P) (hM : 0 ≤ M)
    (hPN : P ≤ N^(21/100:ℝ)) (hMN : M ≤ N^(1/2:ℝ))
    (hq0 : 0 < q) (hq : q ≤ N) (hT : 0 ≤ T) (hTN : T ≤ N)
    (hL : 1 ≤ L) (hLJ : L ≤ J)
    (hJ : (J:ℝ) ≤ PintzDensityCutoffBridge.detectorConstant b * (P^3*M^2)^(13/10:ℝ))
    (hB : B ≤ ⌈A*Real.log (q*(T+5))⌉₊) :
    let C := PintzDensityCutoffBridge.detectorConstant b
    let c := min 1 ((2:ℝ)^b-1)/2
    let K := (Nat.log 2 (J/L)).succ
    (1584*(B:ℝ)*(K:ℝ)^2/c^2)*(1+Real.log (2*J:ℝ))^7*C^(11/25:ℝ)*N^(-h/40) ≤
      uniformConstant A b * (1+Real.log N)^10 * N^(-h/40) := by
  let C := PintzDensityCutoffBridge.detectorConstant b
  let c := min 1 ((2:ℝ)^b-1)/2
  let D := A*(Real.log 6+2)+1
  let E := D*(1+(3+Real.log (2*C))/Real.log 2)^2*(4+Real.log (2*C))^7
  have hC : 1 ≤ C := by
    let c₀ := min 1 ((2:ℝ)^b-1)
    have hc := PintzDetectorHead.head_constant_pos hb
    have hc₁ : c₀ ≤ 1 := min_le_left _ _
    have hz : 1 ≤ 9000/c₀ := (le_div_iff₀ hc).mpr (by linarith)
    have hw := Real.one_le_rpow hz (by norm_num : (0:ℝ) ≤ 13/10)
    change 1 ≤ 2*(9000/c₀)^(13/10:ℝ)
    linarith
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity [Real.log_nonneg (show (1:ℝ) ≤ 6 by norm_num)]
  have hBN : (B:ℝ) ≤ D*(1+Real.log N) :=
    (by exact_mod_cast hB : (B:ℝ) ≤ (⌈A*Real.log (q*(T+5))⌉₊:ℕ)).trans
      (ceiling_budget hA hN hq0 hq hT hTN)
  have H := raw_log_factor hN hC hD (hL.trans hLJ) hL hLJ
    (detector_poly hN hP hM (by linarith) hPN hMN hJ) hBN
  have H' := mul_le_mul_of_nonneg_left H
    (show 0 ≤ (1584/c^2)*C^(11/25:ℝ)*N^(-h/40) by positivity)
  dsimp only
  change _ ≤ ((1584/c^2)*E*C^(11/25:ℝ))*(1+Real.log N)^10*N^(-h/40)
  convert H' using 1 <;> ring

/-- Uniform high-real-part density for the canonical zeta zeros. -/
theorem zeta :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {N P M T b σ : ℝ}
      (hN : 1 ≤ N) (hP : 1 ≤ P) (hM : 1 ≤ M)
      (hMN : M ≤ N^(1/2:ℝ)) (hPN : P ≤ N^(21/100:ℝ))
      (hT : 0 ≤ T) (hTM : T ≤ 2*P*M) (hTN : T ≤ N)
      (hb : 0 < b) (hσ : (39/50:ℝ) ≤ σ) (hcd : σ ≤ 1-b),
    M⁻¹ * N ^ (-2*(1-σ)) *
      (∑ ρ ∈ PintzActualWeightedZeta.catalogue T b σ hb (by linarith),
        (Zeta23.zetaZeroConfig.mult ρ:ℝ)) ≤
      uniformConstant A b * (1+Real.log N)^10 * N ^ (-(1-σ)/40) := by
  obtain ⟨A,hA,hraw⟩ := PintzActualWeightedZeta.estimate
  refine ⟨A,hA,?_⟩
  intro N P M T b σ hN hP hM hMN hPN hT hTM hTN hb hσ hcd
  obtain ⟨L,J,hL,hLJ,hJ,hraw⟩ := hraw hN hP hM hMN hPN hT hTM hb hσ hcd
  dsimp only at hraw
  refine hraw.trans (renormalize (q := 1) (h := 1-σ) hA hb hN
    (by linarith) (by linarith) hPN hMN one_pos hN hT hTN (by omega) hLJ hJ ?_)
  simp

/-- Uniform high-real-part density for actual primitive nonprincipal zeros. -/
theorem nonprincipal :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {N P R M T b σ : ℝ} {Q : ℕ} (hQ : 1 ≤ Q)
      (hN : 1 ≤ N) (hR : 1 ≤ R) (hRP : R ≤ P) (hM : 1 ≤ M)
      (hMN : M ≤ N^(1/2:ℝ)) (hPN : P ≤ N^(21/100:ℝ))
      (hT : 0 ≤ T) (hQR : (Q:ℝ) ≤ 2*R) (hTM : T ≤ 2*P*M/R)
      (hQN : (Q:ℝ) ≤ N) (hTN : T ≤ N)
      (hb : 0 < b) (hσ : (39/50:ℝ) ≤ σ) (hcd : σ ≤ 1-b),
    M⁻¹ * N ^ (-2*(1-σ)) *
      (∑ j ∈ family Q, ∑ z ∈ PintzActualNonprincipalCatalogue.catalogue T b σ
        (by linarith) hb.le j, (analyticOrderNatAt j.2.LFunction z : ℝ)) ≤
      uniformConstant A b * (1+Real.log N)^10 * N ^ (-(1-σ)/40) := by
  obtain ⟨A,hA,hraw⟩ := PintzActualWeightedNonprincipal.estimate
  refine ⟨A,hA,?_⟩
  intro N P R M T b σ Q hQ hN hR hRP hM hMN hPN hT hQR hTM hQN hTN hb hσ hcd
  obtain ⟨L,J,hL,hLJ,hJ,hraw⟩ := hraw hQ hN hR hRP hM hMN hPN hT hQR hTM hb hσ hcd
  dsimp only at hraw
  have hq0 : 0 < (Q:ℝ) := by exact_mod_cast hQ
  refine hraw.trans (renormalize (q := (Q:ℝ)) (h := 1-σ) hA hb hN
    (by linarith) (by linarith) hPN hMN hq0 hQN hT hTN (by omega) hLJ hJ ?_)
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ hA
  exact Real.log_le_log (by positivity) (by gcongr; norm_num)

#print axioms zeta
#print axioms nonprincipal
#print axioms ceiling_budget
#print axioms renormalize
end PintzUniformDensityLog
