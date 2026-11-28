import PintzActualNonprincipalCatalogue

open Finset PintzSieveToHybrid PintzActualNonprincipalCatalogue

namespace PintzActualWeightedNonprincipal

/-- The actual finite family, with no hypotheses on its local counts or
enumeration. The coefficient retains the explicit detector logs. -/
theorem estimate :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {N P R M T b σ : ℝ} {Q : ℕ} (hQ : 1 ≤ Q)
      (hN : 1 ≤ N) (hR : 1 ≤ R) (hRP : R ≤ P) (hM : 1 ≤ M)
      (hMN : M ≤ N^(1/2:ℝ)) (hPN : P ≤ N^(21/100:ℝ))
      (hT : 0 ≤ T) (hQR : (Q:ℝ) ≤ 2*R) (hTM : T ≤ 2*P*M/R)
      (hb : 0 < b) (hσ : (39/50:ℝ) ≤ σ) (hcd : σ ≤ 1-b),
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      (J:ℝ) ≤ PintzDensityCutoffBridge.detectorConstant b * (P^3*M^2)^(13/10:ℝ) ∧
      let K := (Nat.log 2 (J/L)).succ
      let c := min 1 ((2:ℝ)^b-1)/2
      let B := ⌈A*Real.log (Q*(T+3))⌉₊
      M⁻¹ * N ^ (-2*(1-σ)) *
        (∑ j ∈ family Q, ∑ z ∈ catalogue T b σ (by linarith) hb.le j,
          (analyticOrderNatAt j.2.LFunction z : ℝ)) ≤
        (1584*(B:ℝ)*(K:ℝ)^2/c^2)*(1+Real.log (2*J:ℝ))^7 *
          (PintzDensityCutoffBridge.detectorConstant b)^(11/25:ℝ) * N ^ (-(1-σ)/40) := by
  obtain ⟨A,hA,hLoc⟩ := uniform_local
  refine ⟨A,hA,?_⟩
  intro N P R M T b σ Q hQ hN hR hRP hM hMN hPN hT hQR hTM hb hσ hcd
  have hpos : 0 < σ := by linarith
  let S := catalogue T b σ hpos.le hb.le
  let w := fun (j : PintzDyadicStripCount.Char) z => analyticOrderNatAt j.2.LFunction z
  have hS (j : PintzDyadicStripCount.Char) (z : ℂ) (hz : z ∈ S j) :=
    (mem_catalogue T b σ hpos.le hb.le j z).mp hz
  exact PintzWeightedNonprincipalCount.weighted_count hQ hN hR hRP hM hMN hPN hT hQR hTM hb hσ hcd
    S w (fun j _ z hz => (hS j z hz).2.2.2) _ (hLoc hQ hT hb hpos)
    (fun j _ z hz => (hS j z hz).2.2.1) (fun j _ z hz => (hS j z hz).1)
    (fun j _ z hz => (hS j z hz).2.1) (fun _ hj => (mem_family hj).1)

#print axioms estimate
end PintzActualWeightedNonprincipal
