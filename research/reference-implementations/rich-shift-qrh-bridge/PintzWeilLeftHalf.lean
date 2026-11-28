import PintzWeilScaleBudget
import PintzWeilMultiplier
import PintzWeilChiWindow
import PintzHarmonicRow

noncomputable section
open Set Finset MeasureTheory
namespace PintzWeilLeftHalf

private theorem root_bound {N u β : ℝ} (hu : 1 ≤ u) (huN : u ≤ N) (hβ : β ≤ 1/2) :
    u^β ≤ Real.sqrt N := by
  rw [Real.sqrt_eq_rpow]
  exact (Real.rpow_le_rpow_of_exponent_le hu hβ).trans
    (Real.rpow_le_rpow (by linarith) huN (by norm_num))

private theorem small {N x y : ℝ} {z : ℂ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyN : y ≤ N)
    (hz : 0 < z.re) (hβ : z.re ≤ 1/2) :
    ‖((y:ℂ)^z-(x:ℂ)^z)/z‖ ≤ 2*Real.sqrt N := by
  have hc (t : ℝ) (ht : t ∈ Icc x y) : 0 < t := by linarith [ht.1]
  have hi : IntervalIntegrable (fun t : ℝ => t^(-1/2:ℝ)) volume x y := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hxy]
    exact continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (hc t ht)))
  have hk : (∫ t in x..y, (t:ℂ)^(z-1)) = ((y:ℂ)^z-(x:ℂ)^z)/z := by
    rw [integral_cpow]
    · rw [sub_add_cancel]
    · left
      simp only [Complex.sub_re, Complex.one_re]
      linarith
  rw [← hk]
  refine (intervalIntegral.norm_integral_le_of_norm_le hxy ?_ hi).trans ?_
  · apply Filter.Eventually.of_forall
    intro t ht₀
    have ht := Ioc_subset_Icc_self ht₀
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hc t ht), Complex.sub_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_exponent_le (hx.trans ht.1) (by linarith)
  · rw [integral_rpow]
    · have hh : (-(1:ℝ) / 2 + 1) = 1/2 := by norm_num
      rw [hh, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_le_sqrt hyN]
    · left
      norm_num

private theorem pointwise {N x y : ℝ} {z : ℂ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyN : y ≤ N)
    (hz : 0 < z.re) (hβ : z.re ≤ 1/2) :
    ‖((y:ℂ)^z-(x:ℂ)^z)/z‖ ≤ 4*Real.sqrt N/(1+|z.im|) := by
  by_cases ht : |z.im| ≤ 1
  · refine (small hx hxy hyN hz hβ).trans ?_
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [Real.sqrt_nonneg N, mul_nonneg (Real.sqrt_nonneg N) (sub_nonneg.mpr ht)]
  · have ht' : 1 < |z.im| := lt_of_not_ge ht
    have hz' := Complex.abs_im_le_norm z
    have hden : 0 < ‖z‖ := by linarith
    have hb : ‖(y:ℂ)^z-(x:ℂ)^z‖ ≤ 2*Real.sqrt N := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (show 0 < y by linarith),
        Complex.norm_cpow_eq_rpow_re_of_pos (show 0 < x by linarith)]
      linarith [root_bound (hx.trans hxy) hyN hβ, root_bound hx (hxy.trans hyN) hβ]
    rw [norm_div]
    refine (div_le_div_of_nonneg_right hb hden.le).trans ?_
    apply (div_le_div_iff₀ hden (by positivity)).2
    have hh : 0 ≤ Real.sqrt N * (‖z‖ - |z.im|) :=
      mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hz')
    have hh' : 0 ≤ Real.sqrt N * (|z.im|-1) :=
      mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr ht'.le)
    nlinarith

theorem finite_left_half {ι : Type*} (S : Finset ι) (z c : ι → ℂ) (m : ι → ℝ)
    {N x y T C B : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyN : y ≤ N)
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hc : ∀ i ∈ S, ‖c i‖ ≤ B)
    (hβ : ∀ i ∈ S, 0 < (z i).re ∧ (z i).re ≤ 1/2)
    (hγ : ∀ i ∈ S, |(z i).im| ≤ T)
    (hlocal : ∀ t : ℝ, |t| ≤ T+1/2 →
      (∑ i ∈ S.filter (fun i => |(z i).im-t| ≤ 1/2), m i) ≤ C) :
    ‖∑ i ∈ S, (m i:ℂ)*c i*(((y:ℂ)^(z i)-(x:ℂ)^(z i))/(z i))‖ ≤
      (4*B*Real.sqrt N)*(2*C*(1+Real.log (2*T+1))) := by
  classical
  have H := PintzHarmonicRow.row_at_height S (fun i => (z i).im) m 0 T C
    hT (by simpa using hT) hC hm hγ hlocal
  simp only [sub_zero] at H
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ S, (4*B*Real.sqrt N)*(m i/(1+|(z i).im|)) := by
      apply sum_le_sum
      intro i hi
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm i hi)]
      have h1 := mul_le_mul_of_nonneg_left (hc i hi) (hm i hi)
      have h2 := pointwise hx hxy hyN (hβ i hi).1 (hβ i hi).2
      calc
        _ ≤ (m i*B)*(4*Real.sqrt N/(1+|(z i).im|)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (hm i hi) hB)
        _ = _ := by ring
    _ = (4*B*Real.sqrt N) * (∑ i ∈ S, m i/(1+|(z i).im|)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left H (by positivity)

#print axioms finite_left_half

open Zeta23 Zeta23.ThmE PintzWeilChiWindow

private theorem window_sum_le (Z : ZeroConfig) (s : Finset Z.carrier) (a b : ℝ)
    (h : ∀ ρ ∈ s, a < (ρ:ℂ).im ∧ (ρ:ℂ).im ≤ b) :
    (∑ ρ ∈ s, (Z.mult ρ:ℝ)) ≤ (Z.N a b:ℝ) := by
  classical
  have hfin : (Z.window a b).Finite := Z.finite_window a b
  unfold ZeroConfig.N
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
    intro r hr
    obtain ⟨ρ,hρ,rfl⟩ := mem_map.mp hr
    exact hfin.mem_toFinset.mpr ⟨ρ.2,(h ρ hρ).1,(h ρ hρ).2⟩
  have H := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
  rw [sum_map] at H
  exact_mod_cast H

private theorem two_box (Z : ZeroConfig) (s : Finset Z.carrier) (t : ℝ)
    (h : ∀ ρ ∈ s, |(ρ:ℂ).im-t| ≤ 1/2) :
    (∑ ρ ∈ s, (Z.mult ρ:ℝ)) ≤ (Z.N (t-1) t:ℝ)+(Z.N t (t+1):ℝ) := by
  classical
  rw [← sum_filter_add_sum_filter_not s (fun ρ => (ρ:ℂ).im ≤ t)]
  apply add_le_add
  · apply window_sum_le
    intro ρ hρ
    obtain ⟨hs, ht⟩ := mem_filter.mp hρ
    exact ⟨by linarith [(abs_le.mp (h ρ hs)).1],ht⟩
  · apply window_sum_le
    intro ρ hρ
    obtain ⟨hs, ht⟩ := mem_filter.mp hρ
    exact ⟨lt_of_not_ge ht,by linarith [(abs_le.mp (h ρ hs)).2]⟩

private theorem log_q_height {q N u : ℝ} (hN : 4 ≤ N) (hq : 1 ≤ q) (hqN : q ≤ N)
    (hu : |u| ≤ Real.sqrt N+3/2) :
    Real.log (q*(|u|+3)) ≤ 3*(1+Real.log N) := by
  have hN1 : 1 ≤ N := by linarith
  have hsq : Real.sqrt N ≤ N := by
    rw [Real.sqrt_eq_rpow]
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 (show (1/2:ℝ) ≤ 1 by norm_num)
  have H := Real.log_le_log (show 0 < |u|+3 by positivity)
    (show |u|+3 ≤ 3*N by linarith)
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by linarith)] at H
  rw [Real.log_mul (by linarith : q ≠ 0) (by positivity)]
  have Hq := Real.log_le_log (show 0 < q by linarith) hqN
  have H3 : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) (by linarith)
  linarith

theorem actual_config_left_half :
    ∀ {N x y A : ℝ} (Z : ZeroConfig) (S : Finset Z.carrier),
      4 ≤ N → 1 ≤ x → x ≤ y → y ≤ N → 0 ≤ A →
      (∀ t : ℝ, |t| ≤ Real.sqrt N+3/2 → (Z.N t (t+1):ℝ) ≤ A*(1+Real.log N)) →
      (∀ ρ ∈ S, 0 < (ρ:ℂ).re ∧ (ρ:ℂ).re ≤ 1/2) →
      (∀ ρ ∈ S, |(ρ:ℂ).im| ≤ Real.sqrt N) →
      ‖∑ ρ ∈ S, (Z.mult ρ:ℂ)*windowTerm (PintzWeilBump.scaled
        (PintzWeilScaleBudget.delta N)) x y ρ‖ ≤
        (48*Real.exp 1*A)*Real.sqrt N*(1+Real.log N)^2 := by
  intro N x y A Z S hN hx hxy hyN hA hlocal hβ hγ
  classical
  let δ := PintzWeilScaleBudget.delta N
  let g := PintzWeilBump.scaled δ
  have hN1 : 1 ≤ N := by linarith
  have hδ := PintzWeilScaleBudget.delta_pos (N := N) (by linarith)
  have hp : ∀ ρ ∈ S, ‖∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*(ρ:ℂ))‖ ≤ Real.exp 1 := by
    intro ρ hρ
    refine (PintzWeilMultiplier.norm_le_exp hδ.le (PintzWeilBump.scaled_contDiff δ).continuous
      (PintzWeilBump.scaled_nonneg hδ) (PintzWeilBump.scaled_zero_left hδ)
      (PintzWeilBump.scaled_zero_right hδ) (PintzWeilBump.scaled_mass hδ)
      (hβ ρ hρ).1.le (by linarith [(hβ ρ hρ).2])).trans ?_
    exact Real.exp_le_exp.mpr (PintzWeilScaleBudget.delta_le_one hN1)
  have hlogpos : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN1]
  have hbox (t : ℝ) (ht : |t| ≤ Real.sqrt N + 1/2) :
      (∑ ρ ∈ S.filter (fun ρ : Z.carrier => |(ρ:ℂ).im-t| ≤ 1/2), (Z.mult ρ:ℝ)) ≤
        2*A*(1+Real.log N) := by
    refine (two_box Z _ t (fun ρ hρ => (mem_filter.mp hρ).2)).trans ?_
    have ht' : |t-1| ≤ Real.sqrt N+3/2 := by linarith [abs_sub t (1:ℝ), abs_one (α := ℝ)]
    have H := hlocal (t-1) ht'
    rw [sub_add_cancel] at H
    linarith [hlocal t (by linarith)]
  have H := finite_left_half S (fun ρ : Z.carrier => (ρ:ℂ))
    (fun ρ => ∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*(ρ:ℂ))) (fun ρ => (Z.mult ρ:ℝ))
    hx hxy hyN (Real.sqrt_nonneg N) (show 0 ≤ 2*A*(1+Real.log N) by positivity)
    (Real.exp_pos 1).le (fun ρ _ => Nat.cast_nonneg _) hp hβ hγ hbox
  simp only [windowTerm, ← mul_assoc, Complex.ofReal_natCast] at H ⊢
  refine H.trans ?_
  have hs : Real.sqrt N ≤ N := by
    rw [Real.sqrt_eq_rpow]
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 (show (1/2:ℝ) ≤ 1 by norm_num)
  have hl := Real.log_le_log (show 0 < 2*Real.sqrt N+1 by positivity)
    (show 2*Real.sqrt N+1 ≤ N*N by nlinarith)
  rw [Real.log_mul (by linarith : N ≠ 0) (by linarith)] at hl
  have hmono := mul_le_mul_of_nonneg_left
    (show 1+Real.log (2*Real.sqrt N+1) ≤ 3*(1+Real.log N) by
      linarith [Real.log_nonneg hN1])
    (show 0 ≤ (4*Real.exp 1*Real.sqrt N)*(2*(2*A*(1+Real.log N))) by positivity)
  convert hmono using 1 <;> ring

#print axioms actual_config_left_half

theorem chi_left_half :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hq : 1 < q) (hprim : χ.IsPrimitive) {N x y : ℝ},
      4 ≤ N → (q:ℝ) ≤ N → 1 ≤ x → x ≤ y → y ≤ N →
      let Z := LZeros (LSeam_of hq hprim)
      ∀ S : Finset Z.carrier, (∀ ρ ∈ S, (ρ:ℂ).re ≤ 1/2) →
      (∀ ρ ∈ S, |(ρ:ℂ).im| ≤ Real.sqrt N) →
      ‖∑ ρ ∈ S, (Z.mult ρ:ℂ)*windowTerm (PintzWeilBump.scaled
        (PintzWeilScaleBudget.delta N)) x y ρ‖ ≤
        C*Real.sqrt N*(1+Real.log N)^2 := by
  obtain ⟨A,hA,H⟩ := localCountChi_uniform_proof
  have hAn : 0 ≤ A := by linarith
  refine ⟨48*Real.exp 1*(3*A), by positivity, ?_⟩
  intro q _ χ hq hprim N x y hN hqN hx hxy hyN
  dsimp only
  intro S hβ hγ
  refine actual_config_left_half (LZeros (LSeam_of hq hprim)) S hN hx hxy hyN
    (show 0 ≤ 3*A by positivity) ?_ (fun ρ hρ => ⟨ρ.2.2.1,hβ ρ hρ⟩) hγ
  intro t ht
  rw [LZeros_N]
  refine (H q χ hq hprim t).trans ?_
  have L := log_q_height hN (show (1:ℝ) ≤ q by exact_mod_cast hq.le) hqN ht
  convert mul_le_mul_of_nonneg_left L hAn using 1; ring

theorem zeta_left_half :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N x y : ℝ}, 4 ≤ N → 1 ≤ x → x ≤ y → y ≤ N →
      ∀ S : Finset zetaZeroConfig.carrier, (∀ ρ ∈ S, (ρ:ℂ).re ≤ 1/2) →
      (∀ ρ ∈ S, |(ρ:ℂ).im| ≤ Real.sqrt N) →
      ‖∑ ρ ∈ S, (zetaZeroConfig.mult ρ:ℂ)*windowTerm (PintzWeilBump.scaled
        (PintzWeilScaleBudget.delta N)) x y ρ‖ ≤
        C*Real.sqrt N*(1+Real.log N)^2 := by
  obtain ⟨A,hA,H⟩ := RvM.zetaZeroConfig_local_count
  have hAn : 0 ≤ A := by linarith
  refine ⟨48*Real.exp 1*(3*A), by positivity, ?_⟩
  intro N x y hN hx hxy hyN S hβ hγ
  refine actual_config_left_half zetaZeroConfig S hN hx hxy hyN
    (show 0 ≤ 3*A by positivity) ?_ (fun ρ hρ => ⟨ρ.2.2.1,hβ ρ hρ⟩) hγ
  intro t ht
  refine (H t).trans ?_
  have L := log_q_height hN (show (1:ℝ) ≤ 1 by rfl) (show 1 ≤ N by linarith) ht
  rw [one_mul] at L
  convert mul_le_mul_of_nonneg_left L hAn using 1; ring

#print axioms chi_left_half
#print axioms zeta_left_half
end PintzWeilLeftHalf
