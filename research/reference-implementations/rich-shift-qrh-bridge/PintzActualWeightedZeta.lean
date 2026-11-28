import PintzWeilZetaTruncation
import PintzWeightedZetaCount

open Finset Zeta23

namespace PintzActualWeightedZeta

theorem finite_zeros (T b σ : ℝ) (hb : 0 < b) (hσ : 0 < σ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re ∈ Set.Icc σ (1-b) ∧ |ρ.im| ≤ T}.Finite := by
  apply (zetaZeroConfig.finite_window (-T-1) T).subset
  rintro ρ ⟨hz, hre, ht⟩
  have him := abs_le.mp ht
  refine ⟨⟨hz,hσ.trans_le hre.1,by linarith [hre.2]⟩,?_,him.2⟩
  linarith [him.1]

noncomputable def catalogue (T b σ : ℝ) (hb : 0 < b) (hσ : 0 < σ) : Finset ℂ :=
  (finite_zeros T b σ hb hσ).toFinset

theorem mem_catalogue (T b σ : ℝ) (hb : 0 < b) (hσ : 0 < σ) (ρ : ℂ) :
    ρ ∈ catalogue T b σ hb hσ ↔ riemannZeta ρ = 0 ∧ ρ.re ∈ Set.Icc σ (1-b) ∧ |ρ.im| ≤ T :=
  (finite_zeros T b σ hb hσ).mem_toFinset

/-- The half-open canonical RvM windows cover the reflected, closed
unit sampling window using two adjacent windows. -/
theorem uniform_local :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {T b σ : ℝ} (hT : 0 ≤ T) (hb : 0 < b) (hσ : 0 < σ) (x : ℝ),
      ∑ ρ ∈ (catalogue T b σ hb hσ).filter (fun ρ => |-ρ.im-x| ≤ 1/2),
        zetaZeroConfig.mult ρ ≤ ⌈A*Real.log (T+5)⌉₊ := by
  classical
  obtain ⟨A,hA⟩ := PintzWeilZetaTruncation.canonical_local_count
  refine ⟨2*A,by positivity [hA.A₀_pos],?_⟩
  intro T b σ hT hb hσ x
  let s := (catalogue T b σ hb hσ).filter (fun ρ => |-ρ.im-x| ≤ 1/2)
  change (∑ ρ ∈ s, zetaZeroConfig.mult ρ) ≤ _
  have hs (ρ) (hρ : ρ ∈ s) := (mem_filter.mp hρ)
  have hz (ρ) (hρ : ρ ∈ s) : ρ ∈ zetaZeroConfig.carrier := by
    obtain ⟨hzero,hre,_⟩ := (mem_catalogue T b σ hb hσ ρ).mp (hs ρ hρ).1
    exact ⟨hzero,hσ.trans_le hre.1,by linarith [hre.2]⟩
  by_cases hn : s.Nonempty
  · obtain ⟨ρ,hρ⟩ := hn
    have hx : |x| ≤ T + 1 := by
      have ht := abs_add_le (-ρ.im-x) ρ.im
      rw [show -ρ.im-x+ρ.im = -x by ring, abs_neg] at ht
      linarith [(mem_catalogue T b σ hb hσ ρ).mp (hs ρ hρ).1 |>.2.2,(hs ρ hρ).2]
    let e : {ρ : ℂ // ρ ∈ s} ↪ zetaZeroConfig.carrier :=
      ⟨fun u => ⟨u.1,hz u.1 u.2⟩, fun u v h => Subtype.ext (congrArg (fun y : zetaZeroConfig.carrier => (y:ℂ)) h)⟩
    let v := s.attach.map e
    have hv (u : zetaZeroConfig.carrier) (hu : u ∈ v) : (u:ℂ) ∈ s := by
      obtain ⟨r, _, rfl⟩ := mem_map.mp hu
      exact r.2
    let v₁ := v.filter (fun u : zetaZeroConfig.carrier => (u:ℂ).im ≤ -x)
    let v₂ := v.filter (fun u : zetaZeroConfig.carrier => ¬ (u:ℂ).im ≤ -x)
    have hleft := hA.window (-x-1) v₁ (by
      intro u hu
      obtain ⟨hu, hle⟩ := mem_filter.mp hu
      have H := abs_le.mp (hs (u:ℂ) (hv u hu)).2
      constructor <;> linarith [H.1,H.2])
    have hright := hA.window (-x) v₂ (by
      intro u hu
      obtain ⟨hu, hle⟩ := mem_filter.mp hu
      have H := abs_le.mp (hs (u:ℂ) (hv u hu)).2
      have hlt := lt_of_not_ge hle
      constructor <;> linarith [H.1,H.2])
    have hl : |-x-1| + 3 ≤ T+5 := by
      have H := abs_add_le (-x) (-1:ℝ)
      simp only [sub_eq_add_neg, abs_neg, abs_one] at H ⊢
      linarith
    have hr : |-x| + 3 ≤ T+5 := by rw [abs_neg]; linarith
    have htotal :
        (∑ u ∈ v, (zetaZeroConfig.mult u : ℝ)) ≤ 2*A*Real.log (T+5) := by
      rw [← sum_filter_add_sum_filter_not v (fun u : zetaZeroConfig.carrier => (u:ℂ).im ≤ -x)]
      exact (add_le_add hleft hright).trans (by
        have H₁ := mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hl) hA.A₀_pos.le
        have H₂ := mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hr) hA.A₀_pos.le
        linarith)
    dsimp only [v] at htotal
    rw [Finset.sum_map] at htotal
    change (∑ r ∈ s.attach, (zetaZeroConfig.mult r.1 : ℝ)) ≤ _ at htotal
    rw [Finset.sum_attach s (fun z : ℂ => (zetaZeroConfig.mult z : ℝ))] at htotal
    exact_mod_cast htotal.trans (Nat.le_ceil _)
  · rw [Finset.not_nonempty_iff_eq_empty] at hn
    simp [hn]

/-- Actual ζ zeros in the retained band, with the canonical analytic
multiplicities and a uniform logarithmic local count. -/
theorem estimate :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {N P M T b σ : ℝ}
      (hN : 1 ≤ N) (hP : 1 ≤ P) (hM : 1 ≤ M)
      (hMN : M ≤ N^(1/2:ℝ)) (hPN : P ≤ N^(21/100:ℝ))
      (hT : 0 ≤ T) (hTM : T ≤ 2*P*M)
      (hb : 0 < b) (hσ : (39/50:ℝ) ≤ σ) (hcd : σ ≤ 1-b),
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      (J:ℝ) ≤ PintzDensityCutoffBridge.detectorConstant b * (P^3*M^2)^(13/10:ℝ) ∧
      let K := (Nat.log 2 (J/L)).succ
      let c := min 1 ((2:ℝ)^b-1)/2
      let B := ⌈A*Real.log (T+5)⌉₊
      M⁻¹ * N ^ (-2*(1-σ)) *
        (∑ ρ ∈ catalogue T b σ hb (by linarith), (zetaZeroConfig.mult ρ:ℝ)) ≤
        (1584*(B:ℝ)*(K:ℝ)^2/c^2)*(1+Real.log (2*J:ℝ))^7 *
          (PintzDensityCutoffBridge.detectorConstant b)^(11/25:ℝ) * N ^ (-(1-σ)/40) := by
  obtain ⟨A,hA,hL⟩ := uniform_local
  refine ⟨A,hA,?_⟩
  intro N P M T b σ hN hP hM hMN hPN hT hTM hb hσ hcd
  have hs : 0 < σ := by linarith
  let S := catalogue T b σ hb hs
  have hm (ρ) (hρ : ρ ∈ S) := (mem_catalogue T b σ hb hs ρ).mp hρ
  exact PintzWeightedZetaCount.weighted_count hN hP hM hMN hPN hT hTM hb hσ hcd S
    zetaZeroConfig.mult (fun ρ hρ => (hm ρ hρ).2.2) _ (hL hT hb hs)
    (fun ρ hρ => (hm ρ hρ).2.1) (fun ρ hρ => (hm ρ hρ).1)

#print axioms finite_zeros
#print axioms uniform_local
#print axioms estimate
end PintzActualWeightedZeta
