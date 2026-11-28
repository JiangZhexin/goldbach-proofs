import RichShiftGenericSampler263
import RichShiftMobiusTail263
import PintzLowRealBlock

noncomputable section
open Finset PintzSieveToHybrid RichShiftMobiusDetector PintzJutilaAnalytic PintzJutilaPseudo
open PintzJutilaDetectorSplit
namespace RichShiftActualSampler263

def coeff (L : ℕ) (Y : ℝ) (n : ℕ) : ℂ :=
  (∑ d ∈ n.divisors, cutMu L d) * (Real.exp (-(n:ℝ)/Y):ℂ)

theorem coeff_bound (L : ℕ) {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    ‖coeff L Y n‖ ≤ n.divisors.card := by
  have hc : ‖∑ d ∈ n.divisors, cutMu L d‖ ≤ n.divisors.card :=
    (norm_sum_le _ _).trans (by simpa using
      (sum_le_sum (fun d (_hd : d ∈ n.divisors) => RichShiftMobiusTail263.cut_norm L d)))
  unfold coeff
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply (mul_le_of_le_one_right (norm_nonneg _) _).trans hc
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) hY.le)

theorem term_eq (L : ℕ) (Y : ℝ) (j : PintzDyadicStripCount.Char) (ρ : ℂ) {n : ℕ} (hn : 0 < n) :
    detectorTerm j.2 (cutMu L) ρ Y 1 n = PintzDetectorHead.twist j.2 ρ n * coeff L Y n := by
  rw [detectorTerm,LSeries.term_of_ne_zero hn.ne']
  simp only [twisted,psi,Nat.gcd_one_left,ArithmeticFunction.moebius_apply_one,Nat.totient_one,
    Int.cast_one,mul_one]
  rw [PintzDetectorHead.twist,coeff,Complex.cpow_neg,div_eq_mul_inv]
  ring

theorem actual_local_nat {Q : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (A : PintzDyadicStripCount.Char → Finset ℂ)
    (hz : ∀ j ∈ family Q, ∀ z ∈ A j, 1/2 ≤ z.re ∧ z.re < 1)
    (hi : ∀ j ∈ family Q, ∀ z ∈ A j, |z.im| ≤ T) :
    ∀ j ∈ family Q, ∀ x : ℝ, (∑ z ∈ (A j).filter (fun z => |-z.im-x| ≤ 1/2),
      analyticOrderNatAt j.2.LFunction z) ≤ ⌈PintzLowRealBlock.actualC Q T⌉₊ := by
  classical
  intro j hj x
  by_cases hx : |x| ≤ T+1/2
  · have he : (A j).filter (fun z => |-z.im-x| ≤ 1/2) =
        (A j).filter (fun z => |z.im - -x| ≤ 1/2) := by
      ext z
      simp only [mem_filter]
      rw [show -z.im-x = -(z.im - -x) by ring, abs_neg]
    rw [he]
    exact_mod_cast (PintzLowRealBlock.actual_local_count hT A hz j hj (-x)
      (by simpa only [abs_neg] using hx)).trans (Nat.le_ceil _)
  · have he : (A j).filter (fun z => |-z.im-x| ≤ 1/2) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz'
      obtain ⟨hzA,hb⟩ := mem_filter.mp hz'
      have he' : |x| ≤ |z.im|+|-z.im-x| := by
        simpa only [show z.im+(-z.im-x) = -x by ring,abs_neg] using abs_add_le z.im (-z.im-x)
      exact hx (by linarith [hi j hj z hzA])
    rw [he,sum_empty]
    exact Nat.zero_le _

theorem actual_finite_count {Q L : ℕ} (hQ : 1 ≤ Q) (hL : 2 ≤ L)
    {Y x T σ d : ℝ} (hY : 1 ≤ Y) (hLx : (L:ℝ) ≤ x) (hT : 0 ≤ T)
    (hbal : (T+1)*(Q:ℝ)^2 ≤ L) (hσ : 1/2 ≤ σ) (hcd : σ ≤ d) (hd : d < 1)
    (A : PintzDyadicStripCount.Char → Finset ℂ)
    (hpt : ∀ j ∈ family Q, ∀ ρ ∈ A j, |ρ.im| ≤ T)
    (hβ : ∀ j ∈ family Q, ∀ ρ ∈ A j, ρ.re ∈ Set.Icc σ d)
    (hSmall : ∀ j ∈ family Q, ∀ ρ ∈ A j,
      ‖∑' n, detectorTerm j.2 (cutMu L) ρ Y 1 n‖ ≤ (1:ℝ)/12)
    (hTail : 20*Y^2*Real.exp (-x/(2*Y)) ≤ (1:ℝ)/12) :
    let J := ⌊x⌋₊
    let K := (Nat.log 2 (J/L)).succ
    let B := ⌈PintzLowRealBlock.actualC Q T⌉₊
    (∑ j ∈ family Q, ∑ ρ ∈ A j, (analyticOrderNatAt j.2.LFunction ρ:ℝ)) ≤
      (1584*(B:ℝ)*(K:ℝ)^2/((1:ℝ)/6)^2)*(1+Real.log (2*J:ℝ))^7*(J:ℝ)^(2*(1-σ)) := by
  classical
  dsimp only
  let w := fun (j : PintzDyadicStripCount.Char) z => analyticOrderNatAt j.2.LFunction z
  let B := ⌈PintzLowRealBlock.actualC Q T⌉₊
  have hDet (j : PintzDyadicStripCount.Char) (hj : j ∈ family Q) (ρ : ℂ) (hr : ρ ∈ A j) :
      (1:ℝ)/6 ≤ ‖∑ n ∈ Ioc L ⌊x⌋₊, PintzDetectorHead.twist j.2 ρ n*coeff L Y n‖ := by
    have h := RichShiftMobiusTail263.finite_detector_lower j.2 (by omega : 1≤L) hY hLx
      (show 0 ≤ ρ.re by linarith [(hβ j hj ρ hr).1]) (hSmall j hj ρ hr) hTail
    have he : (∑ n ∈ Ioc L ⌊x⌋₊, detectorTerm j.2 (cutMu L) ρ Y 1 n) =
        ∑ n ∈ Ioc L ⌊x⌋₊, PintzDetectorHead.twist j.2 ρ n*coeff L Y n :=
      sum_congr rfl (fun n hn => term_eq L Y j ρ (by have := (mem_Ioc.mp hn).1; omega))
    rwa [he] at h
  have ht (j : PintzDyadicStripCount.Char) (hj : j ∈ family Q) (ρ : ℂ) (hr : ρ ∈ A j) :
      -ρ.im ∈ Set.Icc (-T) T := by rw [Set.mem_Icc,← abs_le,abs_neg]; exact hpt j hj ρ hr
  have hLoc := actual_local_nat hT A
    (fun j hj z hz => ⟨hσ.trans (hβ j hj z hz).1,(hβ j hj z hz).2.trans_lt hd⟩) hpt
  exact RichShiftGenericSampler263.global_finite_count hQ hL (Nat.le_floor hLx) hT hbal A w ht B hLoc
    (by norm_num : 0 < (1:ℝ)/6) (by linarith) hcd hd.le hβ (coeff L Y)
    (coeff_bound L (by linarith)) hDet

#print axioms actual_finite_count
end RichShiftActualSampler263
