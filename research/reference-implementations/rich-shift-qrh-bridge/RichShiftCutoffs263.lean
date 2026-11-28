import RichShiftActualSampler263
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open Finset PintzSieveToHybrid PintzJutilaDetectorSplit RichShiftMobiusDetector
namespace RichShiftCutoffs263

theorem cutoff {P R M T : ℝ} {Q : ℕ} (hR : 1 ≤ R) (hRP : R ≤ P)
    (hM : 1 ≤ M) (hT : 0 ≤ T) (hQR : (Q:ℝ) ≤ 2*R) (hTM : T ≤ 4*P*M/R) :
    ∃ L : ℕ, 2 ≤ L ∧ (T+1)*(Q:ℝ)^2 ≤ L ∧ (L:ℝ) ≤ 22*P^2*M := by
  let L := max 2 ⌈(T+1)*(Q:ℝ)^2⌉₊
  have hR0 : 0 < R := by linarith
  have hP : 1 ≤ P := hR.trans hRP
  have hA : 1 ≤ P^2*M := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hP) hM
  have hQR2 := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) Q) hQR 2
  have hTR := (le_div_iff₀ hR0).mp hTM
  have hR2 := pow_le_pow_left₀ (show 0 ≤ R by linarith) hRP 2
  have hP1 := mul_le_mul_of_nonneg_left hRP (show 0 ≤ P*M by positivity)
  have hP2 := mul_le_mul_of_nonneg_right hTR (show 0 ≤ R by linarith)
  have hP3 := mul_le_mul_of_nonneg_left hQR2 (show 0 ≤ T+1 by linarith)
  have hR22 := mul_le_mul_of_nonneg_left hR2 (show 0 ≤ (4:ℝ) by norm_num)
  have hPR2 := mul_le_mul_of_nonneg_left hM (show 0 ≤ P^2 by positivity)
  have hD : (T+1)*(Q:ℝ)^2 ≤ 20*P^2*M := by nlinarith only [hP1,hP2,hP3,hR22,hPR2]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (T+1)*(Q:ℝ)^2 by positivity)
  have hCL : ((⌈(T+1)*(Q:ℝ)^2⌉₊:ℕ):ℝ) ≤ (L:ℝ) := Nat.cast_le.mpr (le_max_right _ _)
  refine ⟨L,le_max_left _ _,(Nat.le_ceil _).trans hCL,?_⟩
  simp only [L,Nat.cast_max,Nat.cast_ofNat]
  apply max_le
  · linarith
  · linarith

theorem conductor_height {P R M T : ℝ} {Q q : ℕ} (hR : 1 ≤ R) (hRP : R ≤ P)
    (hM : 1 ≤ M) (hQR : (Q:ℝ) ≤ 2*R) (hTM : T ≤ 4*P*M/R)
    (hq : q ≤ Q) {v : ℝ} (hv : |v| ≤ T) :
    (q:ℝ)*(1+|v|) ≤ 10*P*M := by
  have hR0 : 0 < R := by linarith
  have hTR := (le_div_iff₀ hR0).mp hTM
  have hqR : (q:ℝ) ≤ 2*R := (show (q:ℝ) ≤ Q by exact_mod_cast hq).trans hQR
  have h₁ := mul_le_mul hqR hv (by positivity : 0 ≤ |v|) (by positivity : 0 ≤ 2*R)
  have hp := mul_le_mul_of_nonneg_left hM (show 0 ≤ P by linarith)
  nlinarith only [hTR,hqR,h₁,hRP,hp]

theorem stretch {D P M h : ℝ} (hD : Real.exp 20 ≤ D) (hP : 1 ≤ P) (hM : 1 ≤ M)
    (hh₀ : 0 ≤ h) (hh₁ : h ≤ 533/2000) :
    let Z := D*P^(25005/10000:ℝ)*M^(15005/10000:ℝ)
    let Y := Z^(1/(1-h))
    let x := Y*(Real.log Z)^2
    Z ≥ D ∧ 1 ≤ Y ∧ Z ≤ Y ∧ Y^(1-h) = Z ∧ Y ≤ x ∧
      20*Y^2*Real.exp (-x/(2*Y)) ≤ 1/12 ∧
      x ≤ (144000000*D^3)*P^((2501/1000)/(1-h))*M^((1501/1000)/(1-h)) := by
  dsimp only
  let Z := D*P^(25005/10000:ℝ)*M^(15005/10000:ℝ)
  let Y := Z^(1/(1-h))
  let x := Y*(Real.log Z)^2
  have hD1 : 1 ≤ D := (Real.one_le_exp (by norm_num)).trans hD
  have hP0 : 0 < P := by linarith
  have hM0 : 0 < M := by linarith
  have hZ : D ≤ Z := (le_mul_of_one_le_right (by linarith : 0 ≤ D)
      (Real.one_le_rpow hP (by norm_num : 0 ≤ (25005/10000:ℝ)))).trans
    (le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hM (by norm_num)))
  have hZ1 : 1 ≤ Z := hD1.trans hZ
  have hZ0 : 0 < Z := by linarith
  have hh : 0 < 1-h := by linarith
  have hE1 : 1 ≤ 1/(1-h) := (le_div_iff₀ hh).2 (by linarith)
  have hE2 : 1/(1-h) ≤ 2 := (div_le_iff₀ hh).2 (by linarith)
  have hZY : Z ≤ Y := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ1 hE1
  have hY1 : 1 ≤ Y := hZ1.trans hZY
  have hl : 20 ≤ Real.log Z := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 20) (hD.trans hZ)
  have hZ240 : 240 ≤ Z := by
    have he2 : (2:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
    have he := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he2 20
    rw [← Real.exp_nat_mul] at he
    norm_num at he
    linarith only [hZ,hD,he]
  have hYx : Y ≤ x := le_mul_of_one_le_right (by linarith) (by nlinarith only [hl,sq_nonneg (Real.log Z-20)])
  have hYY : Y^(1-h) = Z := by
    dsimp [Y]
    rw [← Real.rpow_mul hZ0.le,div_mul_cancel₀ 1 hh.ne',Real.rpow_one]
  have htail : 20*Y^2*Real.exp (-x/(2*Y)) ≤ 1/12 :=
    RichShiftMobiusTail263.tail_log_squared hZ240 hY1
      (by simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hZ1 hE2)
      (by linarith)
  refine ⟨hZ,hY1,hZY,hYY,hYx,htail,?_⟩
  have hl₁ := Real.log_le_rpow_div hZ0.le (show 0 < (1/12000:ℝ) by norm_num)
  have hlogSq : (Real.log Z)^2 ≤ 144000000*Z^(1/6000:ℝ) := by
    have H := pow_le_pow_left₀ (show 0 ≤ Real.log Z by linarith) hl₁ 2
    rw [div_pow,← Real.rpow_natCast (Z^(1/12000:ℝ)),← Real.rpow_mul hZ0.le] at H
    norm_num at H
    convert H using 1 <;> ring
  let e : ℝ := 1/(1-h)+1/6000
  have he : e ≤ 3 := by dsimp [e]; linarith
  have hPE : (25005/10000:ℝ)*e ≤ (2501/1000)/(1-h) := by
    dsimp [e]
    rw [div_eq_mul_inv (2501/1000:ℝ),one_div]
    have hE := hE1
    rw [one_div] at hE
    nlinarith only [hE]
  have hME : (15005/10000:ℝ)*e ≤ (1501/1000)/(1-h) := by
    dsimp [e]
    rw [div_eq_mul_inv (1501/1000:ℝ),one_div]
    have hE := hE1
    rw [one_div] at hE
    nlinarith only [hE]
  calc
    _ ≤ Y*(144000000*Z^(1/6000:ℝ)) := mul_le_mul_of_nonneg_left hlogSq (by linarith)
    _ = 144000000*Z^e := by
      dsimp only [Y,e]
      rw [Real.rpow_add hZ0]
      ring
    _ = 144000000*(D^e*P^((25005/10000:ℝ)*e)*M^((15005/10000:ℝ)*e)) := by
      dsimp only [Z]
      rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by linarith) (by positivity),
        ← Real.rpow_mul hP0.le,← Real.rpow_mul hM0.le]
    _ ≤ _ := by
      rw [← Real.rpow_natCast D 3]
      calc
        _ ≤ 144000000*(D^(3:ℝ)*P^((2501/1000)/(1-h))*M^((1501/1000)/(1-h))) := by
          gcongr
        _ = _ := by simp only [mul_assoc,Nat.cast_ofNat]

#print axioms stretch
#print axioms cutoff
end RichShiftCutoffs263
