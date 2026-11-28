import RichShiftMobiusUpper263
import PintzJutilaDetectorSplit
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset PintzJutilaAnalytic PintzJutilaPseudo PintzJutilaDetectorSplit RichShiftMobiusDetector
noncomputable section
namespace RichShiftMobiusTail263

theorem cut_norm (L d : ℕ) : ‖cutMu L d‖ ≤ 1 := by
  unfold cutMu
  split_ifs
  · rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one :
        |ArithmeticFunction.moebius d| ≤ 1)
  · simp

theorem divisor_cut {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    (∑ d ∈ n.divisors, cutMu L d) = if n=1 then 1 else 0 := by
  have hd (d : ℕ) (hd : d ∈ n.divisors) :
      cutMu L d = (ArithmeticFunction.moebius d:ℂ) := by
    have h := Nat.dvd_of_mem_divisors hd
    simp only [cutMu,ite_eq_left (mem_Icc.mpr
      ⟨Nat.pos_of_dvd_of_pos h hn,(Nat.le_of_dvd hn h).trans hL⟩)]
  rw [sum_congr rfl hd, ← Int.cast_sum]
  have H := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta n
  rw [ArithmeticFunction.coe_mul_zeta_apply] at H
  rw [H, ArithmeticFunction.one_apply]
  split <;> simp

theorem single_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    {L : ℕ} {x X : ℝ} (hL1 : 1 ≤ L) (hLx : (L:ℝ) ≤ x)
    (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 ≤ ρ.re) {r : ℕ} (hr : r ≠ 0) :
    let f := detectorTerm χ (cutMu L) ρ X r
    Summable f ∧
    ‖(r:ℂ)⁻¹ * ((∑' n, f n) -
      ((Real.exp (-1/X):ℂ) + ∑ n ∈ Ioc L ⌊x⌋₊, f n))‖ ≤
      20*X^2*Real.exp (-x/(2*X)) := by
  classical
  have hz₁ : (1:ℝ) ≤ L := by exact_mod_cast hL1
  dsimp only
  let f := detectorTerm χ (cutMu L) ρ X r
  let g (n : ℕ) := if x < n then (r:ℂ)⁻¹ * f n else 0
  let top := Icc 1 ⌊x⌋₊
  let init (n : ℕ) := if n ∈ top then f n else 0
  have H := PintzJutilaMollifierTail.truncated_tail_simple χ
    (cutMu L)
    (cut_norm L) hρ hr (x := x) hX
  have hn (n : ℕ) : ‖g n‖ =
      (if x < n then (r:ℝ)⁻¹ *
        ‖LSeries.term (twisted (fun n => χ n) (cutMu L) r) ρ n‖ *
          Real.exp (-(n:ℝ)/X) else 0) := by
    unfold g f detectorTerm
    split_ifs
    · rw [norm_mul, norm_inv, Complex.norm_natCast, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), mul_assoc]
    · exact norm_zero
  have hg : Summable g := summable_norm_iff.mp (by simpa only [hn] using H.1)
  have hf0 : f 0 = 0 := by simp [f, detectorTerm]
  have hi : HasSum init (∑ n ∈ top, f n) := by
    have H : HasSum init (∑ n ∈ top, init n) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => ite_eq_right hn)
    convert H using 1
    exact sum_congr rfl (fun n hn => (ite_eq_left hn).symm)
  have hfun : f = fun n => init n + (r:ℂ)*g n := by
    funext n
    by_cases hx : x < n
    · have ht : n ∉ top := fun ht => (not_le_of_gt hx)
        ((by exact_mod_cast (mem_Icc.mp ht).2 : (n:ℝ) ≤ (⌊x⌋₊:ℕ)).trans
          (Nat.floor_le (by linarith)))
      dsimp [init,g]
      rw [ite_eq_right ht, ite_eq_left hx, zero_add, ← mul_assoc,
        mul_inv_cancel₀ (by exact_mod_cast hr), one_mul]
    · rw [show g n = 0 from ite_eq_right hx, mul_zero, add_zero]
      by_cases hn0 : n = 0
      · subst n
        simp [init, hf0]
      · have ht : n ∈ top := mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn0, Nat.le_floor (le_of_not_gt hx)⟩
        exact (ite_eq_left ht).symm
  have hfS : HasSum f ((∑ n ∈ top, f n) + (r:ℂ)*∑' n, g n) := by
    have H : HasSum (fun n => init n + (r:ℂ)*g n)
        ((∑ n ∈ top, f n) + (r:ℂ)*∑' n, g n) := hi.add (hg.hasSum.mul_left (r:ℂ))
    rwa [← hfun] at H
  have hL : L ≤ ⌊x⌋₊ := Nat.le_floor hLx
  have hinit : (∑ n ∈ top, f n) =
      (Real.exp (-1/X):ℂ) + ∑ n ∈ Ioc L ⌊x⌋₊, f n := by
    have hpart : (Icc 1 L) ∪ (Ioc L ⌊x⌋₊) = top := by
      ext n
      simp only [top,mem_union,mem_Icc,mem_Ioc]
      omega
    have hdis : Disjoint (Icc 1 L) (Ioc L ⌊x⌋₊) := by
      apply disjoint_left.mpr
      intro n hn hm
      exact (not_lt_of_ge (mem_Icc.mp hn).2) (mem_Ioc.mp hm).1
    rw [← hpart, sum_union hdis, sum_eq_single_of_mem 1 (mem_Icc.mpr ⟨le_rfl,hL1⟩)]
    · have H := divisor_cut (n := 1) (by decide) hL1
      simp at H
      simp [f, detectorTerm, twisted, H, psi]
    · intro n hn hn1
      have hpos : 0 < n := (mem_Icc.mp hn).1
      have H := divisor_cut hpos (mem_Icc.mp hn).2
      simp [f, detectorTerm, LSeries.term_of_ne_zero hpos.ne', twisted, H, hn1]
  refine ⟨hfS.summable,?_⟩
  change ‖(r:ℂ)⁻¹ * ((∑' n, f n) - _)‖ ≤ _
  rw [hfS.tsum_eq, hinit, add_sub_cancel_left, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hr), one_mul]
  exact (norm_tsum_le_tsum_norm (summable_norm_iff.mpr hg)).trans (by simpa only [hn] using H.2)

/-- A small smoothed detector and its exponentially small remainder force a
genuine finite detector over exactly the Möbius cutoffs. -/
theorem finite_detector_lower {q : ℕ} (χ : DirichletCharacter ℂ q)
    {L : ℕ} (hL : 1 ≤ L) {Y x : ℝ} (hY : 1 ≤ Y) (hLx : (L:ℝ) ≤ x)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re)
    (hsmall : ‖∑' n, detectorTerm χ (cutMu L) ρ Y 1 n‖ ≤ (1:ℝ)/12)
    (htail : 20*Y^2*Real.exp (-x/(2*Y)) ≤ (1:ℝ)/12) :
    (1:ℝ)/6 ≤ ‖∑ n ∈ Ioc L ⌊x⌋₊, detectorTerm χ (cutMu L) ρ Y 1 n‖ := by
  let F := ∑ n ∈ Ioc L ⌊x⌋₊, detectorTerm χ (cutMu L) ρ Y 1 n
  let E := (Real.exp (-1/Y):ℂ)
  let T := ∑' n, detectorTerm χ (cutMu L) ρ Y 1 n
  have ht := (single_split χ hL hLx hY hρ (r:=1) (by decide)).2
  change ‖(↑(1:ℕ):ℂ)⁻¹*(T-(E+F))‖ ≤ _ at ht
  simp only [Nat.cast_one,inv_one,one_mul] at ht
  have herr : ‖T-(E+F)‖ ≤ (1:ℝ)/12 := ht.trans htail
  have hmain0 : (1:ℝ)/3 ≤ Real.exp (-1/Y) := by
    have hY0 : 0 < Y := zero_lt_one.trans_le hY
    have hX : -1 ≤ -1/Y := (le_div_iff₀ hY0).2 (by linarith)
    calc
      _ ≤ Real.exp (-1) := by
        rw [Real.exp_neg,← one_div]
        exact (le_div_iff₀ (Real.exp_pos 1)).2 (by linarith [Real.exp_one_lt_three])
      _ ≤ _ := Real.exp_le_exp.mpr hX
  have hmain : (1:ℝ)/3 ≤ ‖E‖ := by
    simpa only [E,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)] using hmain0
  have hA := norm_sub_le T (T-(E+F))
  rw [show T-(T-(E+F)) = E+F by ring] at hA
  have hB := norm_sub_le (E+F) F
  rw [add_sub_cancel_right] at hB
  change ‖T‖ ≤ (1:ℝ)/12 at hsmall
  change (1:ℝ)/6 ≤ ‖F‖
  linarith only [hA,hB,hsmall,herr,hmain]

theorem tail_log_squared {D Y K : ℝ} (hD : 240 ≤ D) (hY : 1 ≤ Y)
    (hYB : Y ≤ D^K) (hlog : 4*K+2 ≤ Real.log D) :
    20*Y^2*Real.exp (-(Y*(Real.log D)^2)/(2*Y)) ≤ (1:ℝ)/12 := by
  have hD0 : 0 < D := by linarith
  have hY0 : 0 < Y := by linarith
  have hℓ : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
  have hs := pow_le_pow_left₀ (show 0 ≤ Y by linarith) hYB 2
  have heq : (D^K)^(2:ℕ) = Real.exp (2*K*Real.log D) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hD0.le,Real.rpow_def_of_pos hD0]
    congr 1
    push_cast
    ring
  rw [heq] at hs
  rw [show -(Y*(Real.log D)^2)/(2*Y)=-(Real.log D)^2/2 by field_simp]
  calc
    _ ≤ 20*Real.exp (2*K*Real.log D)*Real.exp (-(Real.log D)^2/2) := by gcongr
    _ = 20*Real.exp (2*K*Real.log D-(Real.log D)^2/2) := by rw [mul_assoc,← Real.exp_add]; ring_nf
    _ ≤ 20*Real.exp (-Real.log D) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      nlinarith [mul_nonneg hℓ (sub_nonneg.mpr hlog)]
    _ ≤ _ := by
      rw [Real.exp_neg,Real.exp_log hD0,← div_eq_mul_inv]
      exact (div_le_iff₀ hD0).2 (by linarith)

#print axioms finite_detector_lower
#print axioms tail_log_squared
#print axioms divisor_cut
#print axioms single_split
end RichShiftMobiusTail263
