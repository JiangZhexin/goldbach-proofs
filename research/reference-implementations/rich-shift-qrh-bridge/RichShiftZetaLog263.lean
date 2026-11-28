import RichShiftZeta263
import RichShiftZetaBudget263
import PintzFixedWindowHigh

open Finset Zeta23
namespace RichShiftZetaLog263

theorem estimate_small :
    ∃ A : ℝ → ℝ, (∀ b, 0 ≤ A b) ∧ ∀ {N P M T b h : ℝ},
      1 ≤ N → 1 ≤ P → 1 ≤ M → P ≤ N^(263/1000:ℝ) →
      0 ≤ T → T ≤ N → T ≤ 4*P*M →
      0 < b → b ≤ h → h ≤ 67/500 →
      ∀ S : Finset ℂ, (∀ ρ ∈ S, riemannZeta ρ=0 ∧ ρ.re ∈ Set.Icc (1-h) (1-b) ∧ |ρ.im| ≤ T) →
      M⁻¹ * N^(-2*h) * (∑ ρ ∈ S, (zetaZeroConfig.mult ρ:ℝ)) ≤
        A b * (1+Real.log N)^10 * N^(-h/40) := by
  obtain ⟨D, hD, hDloc⟩ := PintzActualWeightedZeta.uniform_local
  let C := PintzDensityCutoffBridge.detectorConstant
  let C' (b : ℝ) := max 1 (C b * (2:ℝ)^(13/5:ℝ))
  let c (b : ℝ) := min 1 ((2:ℝ)^b-1)/2
  let E := D*(Real.log 6+2)+1
  let V (b : ℝ) := E*(1+(3+Real.log (2*C' b))/Real.log 2)^2*(4+Real.log (2*C' b))^7
  have hE : 0 ≤ E := by dsimp [E]; positivity [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 6)]
  have hcC (b) : 1 ≤ C' b := le_max_left _ _
  have hV (b) : 0 ≤ V b := by
    have hLog : 0 ≤ Real.log (2*C' b) := Real.log_nonneg (by linarith [hcC b])
    dsimp [V]
    positivity
  have hC (b : ℝ) (hb : 0 < b) : 1 ≤ C b := by
    have hi := PintzDetectorHead.head_constant_pos hb
    have hmin : min (1:ℝ) ((2:ℝ)^b-1) ≤ 1 := min_le_left _ _
    have hbase : (1:ℝ) ≤ 9000 / min 1 ((2:ℝ)^b-1) :=
      (le_div_iff₀ hi).2 (by linarith)
    have h := Real.one_le_rpow hbase (by norm_num : (0:ℝ) ≤ 13/10)
    change 1 ≤ 2*(9000 / min 1 (2^b-1))^(13/10:ℝ)
    linarith
  refine ⟨fun b => 1584/(c b)^2*V b*(5*max 1 (C b)), fun b => by positivity [hV b],?_⟩
  intro N P M T b h hN hP hM hPN hT hTN hTM hb hbh hh S hS
  have hσ : 0 < 1-h := by linarith
  let S' := PintzActualWeightedZeta.catalogue T b (1-h) hb hσ
  have hsub : S ⊆ S' := fun ρ hρ =>
    (PintzActualWeightedZeta.mem_catalogue T b (1-h) hb hσ ρ).2 (hS ρ hρ)
  let B := ⌈D*Real.log (T+5)⌉₊
  have hz (ρ) (hρ : ρ ∈ S') := (PintzActualWeightedZeta.mem_catalogue T b (1-h) hb hσ ρ).1 hρ
  obtain ⟨L,J,hL,hLJ,hJ,hcount⟩ := RichShiftZeta263.raw_bound hT hb
    (by linarith : (39/50:ℝ) ≤ 1-h) (by linarith) S' zetaZeroConfig.mult
    (fun ρ hρ => (hz ρ hρ).2.2) B (hDloc hT hb hσ)
    (fun ρ hρ => (hz ρ hρ).2.1) (fun ρ hρ => (hz ρ hρ).1)
  have hTN' : 1+T ≤ 2*N := by linarith
  have hJ' : (J:ℝ) ≤ C' b*N^3 := by
    calc
      _ ≤ C b * (1+T)^(13/5:ℝ) := hJ
      _ ≤ C b*(2*N)^(13/5:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hTN' (by norm_num)) (by linarith [hC b hb])
      _ = (C b*2^(13/5:ℝ))*N^(13/5:ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ N)]; ring
      _ ≤ _ := by
        rw [← Real.rpow_natCast]
        exact mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
          (by positivity) (by linarith [hcC b])
  have hB : (B:ℝ) ≤ E*(1+Real.log N) := by
    simpa [B,E] using PintzUniformDensityLog.ceiling_budget hD hN (q:=1)
      (by norm_num) hN hT hTN
  have hlog := PintzDetectorLogBudget.raw_log_factor hN (hcC b) hE
      (by omega : 1 ≤ J) (by omega : 1 ≤ L) hLJ hJ' hB
  have hpow := RichShiftZetaBudget263.low hN hP hM hPN hT hTM (hC b hb)
    (Nat.cast_nonneg (α := ℝ) J) hJ (by linarith : 0 ≤ h) hh
  have hcount' := (sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ => by positivity)).trans hcount
  change _ ≤ (1584*(B:ℝ)*(((Nat.log 2 (J/L)).succ:ℕ):ℝ)^2/(c b)^2) *
      (1+Real.log (2*J:ℝ))^7 * (J:ℝ)^(2*(1-(1-h))) at hcount'
  rw [show 1-(1-h) = h by ring] at hcount'
  have hU := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1584/(c b)^2 by positivity)
  have hlog' : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hA : 0 ≤ 1584/(c b)^2*V b*(1+Real.log N)^10 := by positivity [hV b]
  calc
    _ ≤ M⁻¹*N^(-2*h)*((1584*(B:ℝ)*(((Nat.log 2 (J/L)).succ:ℕ):ℝ)^2/(c b)^2) *
        (1+Real.log (2*J:ℝ))^7 * (J:ℝ)^(2*h)) :=
      mul_le_mul_of_nonneg_left hcount' (by positivity)
    _ = (1584/(c b)^2* ((B:ℝ)*(((Nat.log 2 (J/L)).succ:ℕ):ℝ)^2*
        (1+Real.log (2*J:ℝ))^7)) * (M⁻¹*N^(-2*h)*(J:ℝ)^(2*h)) := by ring
    _ ≤ (1584/(c b)^2*V b*(1+Real.log N)^10)*((5*C b)*N^(-h/40)) := by
      apply mul_le_mul _ hpow (by positivity) hA
      simpa only [V, mul_assoc] using hU
    _ ≤ _ := by
      have hmax := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) (C b)) (by norm_num : (0:ℝ) ≤ 5))
        (Real.rpow_nonneg (show 0 ≤ N by linarith) (-h/40))
      exact (mul_le_mul_of_nonneg_left hmax hA).trans_eq (by ring)

#print axioms estimate_small
theorem estimate_large :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {N P M T b h : ℝ},
      1 ≤ N → 1 ≤ P → 1 ≤ M → P ≤ N^(263/1000:ℝ) →
      0 ≤ T → T ≤ N → T ≤ 4*P*M →
      0 < b → 67/500 ≤ h → h ≤ 1/2 →
      ∀ S : Finset ℂ, (∀ ρ ∈ S, riemannZeta ρ=0 ∧ ρ.re ∈ Set.Icc (1-h) (1-b) ∧ |ρ.im| ≤ T) →
      M⁻¹ * N^(-2*h) * (∑ ρ ∈ S, (zetaZeroConfig.mult ρ:ℝ)) ≤
        A * (1+Real.log N)^10 * N^(-h/40) := by
  obtain ⟨D,hD,hL⟩ := PintzActualWeightedZeta.uniform_local
  let E := D*(Real.log 6+2)+1
  have hE : 0 ≤ E := by dsimp [E]; positivity [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 6)]
  refine ⟨9*E,by positivity,?_⟩
  intro N P M T b h hN hP hM hPN hT hTN hTM hb hh hhi S hS
  have hσ : 0 < 1-h := by linarith
  let B : ℕ := ⌈D*Real.log (T+5)⌉₊
  let S' := PintzActualWeightedZeta.catalogue T b (1-h) hb hσ
  have hsub : S ⊆ S' := fun ρ hρ =>
    (PintzActualWeightedZeta.mem_catalogue T b (1-h) hb hσ ρ).2 (hS ρ hρ)
  have hLocal (t : ℝ) (_ht : |t| ≤ T+1/2) :
      (∑ ρ ∈ S.filter (fun ρ => |ρ.im-t| ≤ 1/2), (zetaZeroConfig.mult ρ:ℝ)) ≤ B := by
    have hs : S.filter (fun ρ => |ρ.im-t| ≤ 1/2) ⊆
        S'.filter (fun ρ => |-ρ.im-(-t)| ≤ 1/2) := by
      intro ρ hρ
      obtain ⟨hρ,h⟩ := mem_filter.mp hρ
      refine mem_filter.mpr ⟨hsub hρ,?_⟩
      rw [show -ρ.im-(-t) = -(ρ.im-t) by ring, abs_neg]
      exact h
    exact_mod_cast (Finset.sum_le_sum_of_subset_of_nonneg hs (fun z _ _ =>
      Nat.zero_le (zetaZeroConfig.mult z))).trans (hL hT hb hσ (-t))
  have hc := PintzFixedWindowHigh.count_of_unit_boxes S Complex.im
      (fun ρ => (zetaZeroConfig.mult ρ:ℝ)) hT (Nat.cast_nonneg (α:=ℝ) B)
      (fun _ _ => by positivity) (fun ρ hρ => (hS ρ hρ).2.2) hLocal
  have hcount : (∑ ρ ∈ S, (zetaZeroConfig.mult ρ:ℝ)) ≤ (B:ℝ)*(2*T+1) :=
    hc.trans_eq (mul_comm _ _)
  have H := RichShiftZetaBudget263.high hN hP hM hPN hT hTM
    (Nat.cast_nonneg (α:=ℝ) B) hh hcount
  have hB : (B:ℝ) ≤ E*(1+Real.log N) := by
    simpa [B,E] using PintzUniformDensityLog.ceiling_budget hD hN (q:=1)
      (by norm_num) hN hT hTN
  have hl : 1 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hp : 1+Real.log N ≤ (1+Real.log N)^10 := by
    simpa using pow_le_pow_right₀ hl (by norm_num : (1:ℕ) ≤ 10)
  refine H.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (show 0 ≤ N by linarith) _))
  have HB := hB.trans (mul_le_mul_of_nonneg_left hp hE)
  nlinarith only [HB]

#print axioms estimate_large
end RichShiftZetaLog263
