import PintzDensityExponentArithmetic
import PintzDetectorHead
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Semiring

namespace PintzDensityCutoffBridge

noncomputable def detectorConstant (b : ℝ) : ℝ :=
  2 * (9000 / min 1 ((2:ℝ)^b-1))^(13/10:ℝ)

/-- The choices of natural L,J for real dyadic height T.  The range permits
T as large as 2PM/R; Q may be any integer at most 2R. -/
theorem cutoffs {P R M T b : ℝ} {Q : ℕ}
    (hR : 1 ≤ R) (hRP : R ≤ P) (hM : 1 ≤ M) (hT : 0 ≤ T)
    (hQ : (Q:ℝ) ≤ 2*R) (hTM : T ≤ 2*P*M/R) (hb : 0 < b) :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧ (T+1)*(Q:ℝ)^2 ≤ L ∧
      (J:ℝ) ≤ detectorConstant b * (P^3*M^2)^(13/10:ℝ) ∧
      1 ≤ detectorConstant b ∧
      ∀ (q : ℕ) (ρ : ℂ), q ≤ Q → |ρ.im| ≤ T →
        (39/50:ℝ) ≤ ρ.re → ρ.re ≤ 1 →
        (4*(L:ℝ)*(9*((q:ℝ)*(1+‖ρ‖/ρ.re))+1) /
          min 1 ((2:ℝ)^b-1))^(13/10:ℝ) ≤ (J:ℝ) := by
  let c := min 1 ((2:ℝ)^b-1)
  have hc : 0 < c := PintzDetectorHead.head_constant_pos hb
  have hc1 : c ≤ 1 := min_le_left _ _
  have hRp : 0 < R := by linarith
  have hP : 1 ≤ P := hR.trans hRP
  have hPR : R ≤ P*M := by nlinarith [mul_nonneg (show 0 ≤ P by linarith) (sub_nonneg.mpr hM)]
  have hPM : 1 ≤ P*M := hR.trans hPR
  have hRT : R*T ≤ 2*P*M := by
    have H := (le_div_iff₀ hRp).mp hTM
    nlinarith only [H]
  have hbal : (T+1)*(Q:ℝ)^2 ≤ 12*P^2*M := by
    have hQsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) Q) hQ 2
    have HA : (T+1)*(Q:ℝ)^2 ≤ (T+1)*(2*R)^2 :=
      mul_le_mul_of_nonneg_left hQsq (by positivity)
    have HB : R*(T+1) ≤ 3*P*M := by nlinarith only [hRT,hPR]
    have HC : 4*R*(R*(T+1)) ≤ 4*P*(3*P*M) :=
      mul_le_mul (by linarith only [hRP]) HB (by positivity) (by positivity)
    nlinarith only [HA, HC]
  let L := 2 + ⌈(T+1)*(Q:ℝ)^2⌉₊
  have hL : 2 ≤ L := by dsimp [L]; omega
  have hLlo : (T+1)*(Q:ℝ)^2 ≤ L :=
    (Nat.le_ceil _).trans (by simp [L])
  have hLhi : (L:ℝ) ≤ 15*P^2*M := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (T+1)*(Q:ℝ)^2 by positivity)
    have hz : 1 ≤ P^2*M := by
      have := mul_le_mul_of_nonneg_right (show 1 ≤ P^2 by nlinarith) (show 0 ≤ M by linarith)
      linarith
    dsimp [L]
    push_cast
    linarith
  let X := 4*(L:ℝ)*(150*P*M)/c
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hXL : (L:ℝ) ≤ X := by
    apply (le_div_iff₀ hc).mpr
    have h1 := mul_le_mul_of_nonneg_left hc1 (show (0:ℝ) ≤ L by positivity)
    have h2 := mul_le_mul_of_nonneg_left hPM (show 0 ≤ 600*(L:ℝ) by positivity)
    nlinarith only [h1,h2,hLR]
  have hX : 1 ≤ X := by linarith
  let J := ⌈X^(13/10:ℝ)⌉₊
  have hXpow : X ≤ X^(13/10:ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1:ℝ) ≤ 13/10)
  have hLJ : L ≤ J := by exact_mod_cast hXL.trans (hXpow.trans (Nat.le_ceil _))
  have hXR : X ≤ (9000/c)*(P^3*M^2) := by
    dsimp [X]
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hc).mpr
    have H := mul_le_mul_of_nonneg_right hLhi (show 0 ≤ 4*(150*P*M) by positivity)
    nlinarith only [H]
  have hJhi : (J:ℝ) ≤ detectorConstant b * (P^3*M^2)^(13/10:ℝ) := by
    have H := Nat.ceil_lt_add_one (show 0 ≤ X^(13/10:ℝ) by positivity)
    have Hpow := Real.rpow_le_rpow (show 0 ≤ X by linarith) hXR
      (by norm_num : (0:ℝ) ≤ 13/10)
    rw [Real.mul_rpow (by positivity) (by positivity)] at Hpow
    change (J:ℝ) ≤ (2*(9000/c)^(13/10:ℝ)) * (P^3*M^2)^(13/10:ℝ)
    dsimp [J]
    nlinarith only [H, Hpow, hXpow, hX]
  have hCb : 1 ≤ detectorConstant b := by
    have h1 : 1 ≤ 9000/c := (le_div_iff₀ hc).mpr (by linarith)
    have h2 : 1 ≤ (9000/c)^(13/10:ℝ) := Real.one_le_rpow h1 (by norm_num)
    change 1 ≤ 2*(9000/c)^(13/10:ℝ)
    linarith
  refine ⟨L,J,hL,hLJ,hLlo,hJhi,hCb,?_⟩
  intro q ρ hq him hre hre1
  have hq' : (q:ℝ) ≤ 2*R := (by exact_mod_cast hq : (q:ℝ) ≤ Q).trans hQ
  have hρ : ‖ρ‖ ≤ T+1 := by
    have H := norm_add_le ((ρ.re:ℂ)) ((ρ.im:ℂ)*Complex.I)
    rw [Complex.re_add_im, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ ρ.re)] at H
    linarith
  have hρdiv : ‖ρ‖ / ρ.re ≤ 2*(T+1) := by
    apply (div_le_iff₀ (by linarith : 0 < ρ.re)).mpr
    nlinarith only [hρ, mul_nonneg (show 0 ≤ T+1 by positivity) (show 0 ≤ 2*ρ.re-1 by linarith)]
  have hA : 9*((q:ℝ)*(1+‖ρ‖/ρ.re))+1 ≤ 150*P*M := by
    have H := mul_le_mul hq' (show 1+‖ρ‖/ρ.re ≤ 1+2*(T+1) by linarith)
      (by positivity) (by positivity)
    nlinarith only [H,hRT,hPR,hPM]
  refine (Real.rpow_le_rpow (by positivity) ?_ (by norm_num : (0:ℝ) ≤ 13/10)).trans (Nat.le_ceil _)
  change 4*(L:ℝ)*(9*((q:ℝ)*(1+‖ρ‖/ρ.re))+1)/c ≤ X
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by positivity)) hc.le

#print axioms cutoffs
end PintzDensityCutoffBridge
