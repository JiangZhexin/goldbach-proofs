import RichShiftCountTransfer263
import PintzConductorReindex

noncomputable section
open Finset PintzSieveToHybrid PintzJutilaDetectorSplit RichShiftMobiusDetector
namespace RichShiftNonprincipalDensity263

set_option maxHeartbeats 1000000 in
theorem estimate :
    ∃ D : ℝ → ℝ, (∀ b, 0 ≤ D b) ∧ ∀ {N P R M T b h : ℝ} {Q : ℕ}
      (hQ : 1 ≤ Q) (hN : 2 ≤ N) (hR : 1 ≤ R) (hRP : R ≤ P) (hM : 1 ≤ M)
      (hMN : M ≤ N^(1/2:ℝ)) (hPN : P ≤ N^(263/1000:ℝ))
      (hT : 0 ≤ T) (hQR : (Q:ℝ) ≤ 2*R) (hTM : T ≤ 4*P*M/R)
      (hQN : (Q:ℝ) ≤ N) (hTN : T ≤ N)
      (hb : 0 < b) (hbh : b ≤ h) (hh : h ≤ 533/2000)
      (S : PintzDyadicStripCount.Char → Finset ℂ)
      (hS : ∀ j ∈ family Q, ∀ z ∈ S j,
        j.2.LFunction z = 0 ∧ z.re ∈ Set.Icc (1-h) (1-b) ∧ |z.im| ≤ T)
      (hNP : ∀ j ∈ family Q, ∀ z ∈ S j, j.2 ≠ 1),
    M⁻¹ * N^(-2*h) * (∑ j ∈ family Q, ∑ z ∈ S j, (analyticOrderNatAt j.2.LFunction z : ℝ)) ≤
      D b * (1+Real.log N)^10 * N^(-h/40) := by
  obtain ⟨C,hC,hUpper⟩ := RichShiftMobiusUpper263.upper
    (show (0:ℝ) < 1/2000 by norm_num) (show (1:ℝ)/2000 ≤ 1/2 by norm_num)
  let E (b : ℝ) := max 1 (1+Real.log b⁻¹)
  let W (b : ℝ) := max (Real.exp 20) (12*C*22*(10:ℝ)^((1:ℝ)/2+1/2000)*E b)
  let X (b : ℝ) := 144000000*(W b)^3
  let A := 18/Real.log ((55:ℝ)/52)+11/Real.log ((12:ℝ)/11)
  have hA : 0 ≤ A := by
    have h1 := Real.log_pos (show (1:ℝ)<55/52 by norm_num)
    have h2 := Real.log_pos (show (1:ℝ)<12/11 by norm_num)
    unfold A
    positivity
  have hW (b : ℝ) : 1 ≤ W b := (Real.one_le_exp (by norm_num)).trans (le_max_left _ _)
  have hX (b : ℝ) : 1 ≤ X b := by dsimp [X]; nlinarith [one_le_pow₀ (hW b) (n:=3)]
  let V (b : ℝ) := (A+1)*(1+(3+Real.log (2*X b))/Real.log 2)^2*(4+Real.log (2*X b))^7
  have hV (b : ℝ) : 0 ≤ V b := by
    unfold V
    positivity [Real.log_nonneg (show (1:ℝ) ≤ 2*X b by linarith [hX b])]
  refine ⟨fun b => (1584*36)*V b*X b,fun b => by have := hV b; have := hX b; positivity,?_⟩
  intro N P R M T b h Q hQ hN hR hRP hM hMN hPN hT hQR hTM hQN hTN hb hbh hh S hS hNP
  have hp : 1 ≤ P := hR.trans hRP
  have hh0 : 0 ≤ h := hb.le.trans hbh
  obtain ⟨L,hL,hbal,hLcap⟩ := RichShiftCutoffs263.cutoff hR hRP hM hT hQR hTM
  let p : ℝ := 1/2+1/2000
  let Z := W b*P^(25005/10000:ℝ)*M^(15005/10000:ℝ)
  let Y := Z^(1/(1-h))
  let x := Y*(Real.log Z)^2
  obtain ⟨hZ,hY,hZY,hYY,hYx,hTail,hXlim⟩ :=
    RichShiftCutoffs263.stretch (le_max_left _ _ : Real.exp 20 ≤ W b) hp hM hh0 hh
  change 1 ≤ Y at hY
  change Z ≤ Y at hZY
  change Y^(1-h) = Z at hYY
  change Y ≤ x at hYx
  change 20*Y^2*Real.exp (-x/(2*Y)) ≤ 1/12 at hTail
  change x ≤ X b*P^((2501/1000)/(1-h))*M^((1501/1000)/(1-h)) at hXlim
  have hP0 : 0 < P := by linarith
  have hM0 : 0 < M := by linarith
  have hY0 : 0 < Y := by linarith
  have hPM : P^2*M ≤ P^(25005/10000:ℝ)*M^(15005/10000:ℝ) := by
    have hP2 : P^2 ≤ P^(25005/10000:ℝ) := by
      rw [← Real.rpow_natCast P 2]
      exact Real.rpow_le_rpow_of_exponent_le hp (by norm_num)
    have hM1 : M ≤ M^(15005/10000:ℝ) := by
      conv_lhs => rw [← Real.rpow_one M]
      exact Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
    exact mul_le_mul hP2 hM1 hM0.le (by positivity)
  have hW22 : 22 ≤ W b := by
    have h : 22 ≤ Real.exp 20 := by
      have hx := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) Real.exp_one_gt_two.le 20
      rw [← Real.exp_nat_mul] at hx
      norm_num at hx
      linarith
    exact h.trans (le_max_left _ _)
  have hLZ : 22*P^2*M ≤ Z := by
    have H := mul_le_mul hW22 hPM (by positivity : 0≤P^2*M) (by positivity : 0≤W b)
    simpa only [Z,mul_assoc] using H
  have hLx : (L:ℝ) ≤ x := hLcap.trans (hLZ.trans (hZY.trans hYx))
  have hSmall (j : PintzDyadicStripCount.Char) (hj : j ∈ family Q) (z : ℂ) (hz : z ∈ S j) :
      ‖∑' n, detectorTerm j.2 (cutMu L) z Y 1 n‖ ≤ (1:ℝ)/12 := by
    have hjD := PintzConductorReindex.mem_family.mp hj
    have hq1 : 1 < j.1+1 := by
      by_contra! H
      exact hNP j hj z hz (j.2.level_one' (by omega))
    obtain ⟨hzero,hβ,ht⟩ := hS j hj z hz
    have hβ0 : (1:ℝ)/2 ≤ z.re := by linarith [hβ.1]
    have hqT := RichShiftCutoffs263.conductor_height hR hRP hM hQR hTM hjD.1 ht
    have hbz : 0 < 1-z.re := by linarith [hβ.2]
    have hLog : 1+Real.log ((1-z.re)⁻¹) ≤ E b :=
      (add_le_add le_rfl (Real.log_le_log (inv_pos.mpr hbz)
        (inv_anti₀ hb (by linarith [hβ.2])))).trans (le_max_right _ _)
    have hLog0 : 0 ≤ 1+Real.log ((1-z.re)⁻¹) := by
      have h1 := (one_le_inv₀ hbz).mpr (show 1-z.re ≤ 1 by linarith)
      linarith [Real.log_nonneg h1]
    have hUpper' := hUpper (j.1+1) j.2 hq1 hjD.2 L hβ0 hzero hY0
    change ‖∑' n, detectorTerm j.2 (cutMu L) z Y 1 n‖ ≤
      C*Y^(-z.re)*(((j.1+1:ℕ):ℝ)*(1+|z.im|))^p*L*
        (1+Real.log ((1-z.re)⁻¹)) at hUpper'
    have hhP : 0 ≤ p := by dsimp [p]; norm_num
    have hQ := Real.rpow_le_rpow (show 0 ≤ ((j.1+1:ℕ):ℝ)*(1+|z.im|) by positivity) hqT hhP
    have hYβ : Y^(-z.re) ≤ Y^(-(1-h)) :=
      Real.rpow_le_rpow_of_exponent_le hY (by linarith [hβ.1])
    calc
      _ ≤ C*Y^(-(1-h))*(10*P*M)^p*(22*P^2*M)*E b := by
        refine hUpper'.trans ?_
        gcongr
      _ = ((12*C*22*(10:ℝ)^p*E b)*P^(25005/10000:ℝ)*M^(15005/10000:ℝ))*Y^(-(1-h))/12 := by
        rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by norm_num) hP0.le]
        have hPP : P^p*P^2 = P^(25005/10000:ℝ) := by
          rw [← Real.rpow_natCast P 2,← Real.rpow_add hP0]
          congr 1
          dsimp [p]
          norm_num
        have hMM : M^p*M = M^(15005/10000:ℝ) := by
          conv_lhs => arg 2; rw [← Real.rpow_one M]
          rw [← Real.rpow_add hM0]
          congr 1
          dsimp [p]
          norm_num
        rw [← hPP,← hMM]
        ring
      _ ≤ Z*Y^(-(1-h))/12 := by
        dsimp only [Z]
        gcongr
        exact le_max_right _ _
      _ = _ := by
        rw [Real.rpow_neg hY0.le,hYY,mul_inv_cancel₀ (by
          dsimp [Z]; positivity [hW b])]
  let J := ⌊x⌋₊
  let K := (Nat.log 2 (J/L)).succ
  let B := ⌈PintzLowRealBlock.actualC Q T⌉₊
  have hLJ : L ≤ J := Nat.le_floor hLx
  have hJ1 : 1 ≤ J := (show 1≤L by omega).trans hLJ
  have hJ := (Nat.floor_le (show 0 ≤ x by linarith)).trans hXlim
  have hCnt := RichShiftActualSampler263.actual_finite_count hQ hL hY hLx hT hbal
    (show (1:ℝ)/2 ≤ 1-h by linarith) (show 1-h ≤ 1-b by linarith)
    (show 1-b < 1 by linarith) S (fun j hj z hz => (hS j hj z hz).2.2)
    (fun j hj z hz => (hS j hj z hz).2.1) hSmall hTail
  change _ ≤ (1584*(B:ℝ)*(K:ℝ)^2/((1:ℝ)/6)^2)*(1+Real.log (2*J:ℝ))^7*(J:ℝ)^(2*(1-(1-h))) at hCnt
  rw [show 1-(1-h)=h by ring] at hCnt
  have hN1 : 1 ≤ N := by linarith
  have hB : (B:ℝ) ≤ (A+1)*(1+Real.log N) := by
    have hCA := PintzLowRealBlock.actualC_log_bound hN hQ (by linarith) hT hTN
    have hNlog : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hC0 : 0 ≤ PintzLowRealBlock.actualC Q T := by
      unfold PintzLowRealBlock.actualC
      apply le_trans _ (le_max_right _ _)
      exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg T])) (Real.log_nonneg (by norm_num))
    have hCeil := Nat.ceil_lt_add_one hC0
    change (B:ℝ) < PintzLowRealBlock.actualC Q T+1 at hCeil
    change PintzLowRealBlock.actualC Q T ≤ A*Real.log N at hCA
    nlinarith
  obtain ⟨hJpoly,hWeight⟩ := RichShiftCountTransfer263.scale_transfer
    hN1 hp hM (hX b) hPN hMN hh0 hh (Nat.cast_nonneg J) hJ
  have hLog := PintzDetectorLogBudget.raw_log_factor hN1 (hX b) (by positivity : 0≤A+1)
    hJ1 (by omega : 1≤L) hLJ hJpoly hB
  change (B:ℝ)*(K:ℝ)^2*(1+Real.log (2*J:ℝ))^7 ≤ V b*(1+Real.log N)^10 at hLog
  have hFront := mul_le_mul_of_nonneg_left hCnt (show 0≤M⁻¹*N^(-2*h) by positivity)
  refine hFront.trans ?_
  have hVb := hV b
  calc
    _ = (1584*36)*((B:ℝ)*(K:ℝ)^2*(1+Real.log (2*J:ℝ))^7)*(M⁻¹*N^(-2*h)*(J:ℝ)^(2*h)) := by ring
    _ ≤ (1584*36)*(V b*(1+Real.log N)^10)*(X b*N^(-h/40)) := by
      gcongr
    _ = _ := by ring

#print axioms estimate
end RichShiftNonprincipalDensity263
