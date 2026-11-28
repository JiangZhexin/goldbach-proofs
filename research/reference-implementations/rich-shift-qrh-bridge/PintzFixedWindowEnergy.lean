import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import PintzFixedWindowGram
import PintzFixedWindowL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import PintzHarmonicRow
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Finset
namespace PintzFixedWindowEnergy

/-- Weighted Schur bound for a finite nonnegative symmetric kernel. -/
theorem weighted_symmetric_row {ι : Type*} (S : Finset ι) (m a : ι → ℝ)
    (K : ι → ι → ℝ) (B : ℝ)
    (hm : ∀ i ∈ S, 0 ≤ m i)
    (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsym : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, (∑ j ∈ S, m j * K i j) ≤ B) :
    (∑ i ∈ S, ∑ j ∈ S, m i * m j * K i j * a i * a j) ≤
      B * (∑ i ∈ S, m i * (a i)^2) := by
  let U := fun i j => m i * m j * K i j * (a i)^2
  have hx : (∑ i ∈ S, ∑ j ∈ S, U j i) = ∑ i ∈ S, ∑ j ∈ S, U i j := by
    exact Finset.sum_comm
  have hs : (∑ i ∈ S, ∑ j ∈ S, 2*(m i*m j*K i j*a i*a j)) ≤
      ∑ i ∈ S, ∑ j ∈ S, (U i j + U j i) := by
    refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
    have h := mul_nonneg (mul_nonneg (mul_nonneg (hm i hi) (hm j hj)) (hK i hi j hj))
      (sq_nonneg (a i-a j))
    dsimp only [U]
    rw [← hsym i hi j hj]
    linarith only [show 0 ≤ m i*m j*K i j*(a i)^2 + m j*m i*K i j*(a j)^2 -
      2*(m i*m j*K i j*a i*a j) by
        convert h using 1; ring]
  simp_rw [sum_add_distrib, ← mul_sum] at hs
  rw [hx] at hs
  have hh : (∑ i ∈ S, ∑ j ∈ S, U i j) ≤ B*(∑ i ∈ S, m i*(a i)^2) := by
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    calc
      _ = (m i*(a i)^2) * ∑ j ∈ S, m j*K i j := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by dsimp [U]; ring
      _ ≤ (m i*(a i)^2)*B := mul_le_mul_of_nonneg_left (hrow i hi)
        (mul_nonneg (hm i hi) (sq_nonneg _))
      _ = _ := mul_comm _ _
  linarith only [hs,hh]

/-- Harmonic denominator Gram form, with entries weighted by multiplicities. -/
theorem harmonic_quadratic {ι : Type*} (S : Finset ι) (x m a : ι → ℝ) (T C : ℝ)
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hx : ∀ i ∈ S, |x i| ≤ T)
    (hlocal : ∀ t : ℝ, |t| ≤ T+1/2 →
      (∑ i ∈ S.filter (fun i => |x i - t| ≤ 1/2), m i) ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, m i*m j*(1/(1+|x i-x j|))*a i*a j) ≤
      (2*C*(1+Real.log (2*T+1)))*(∑ i ∈ S, m i*(a i)^2) := by
  classical
  refine weighted_symmetric_row S m a _ _ hm (fun i _ j _ => by positivity)
    (fun i _ j _ => by rw [abs_sub_comm]) ?_
  intro i hi
  simpa [div_eq_mul_inv, abs_sub_comm] using
    PintzHarmonicRow.row_at_height S x m (x i) T C hT (hx i hi) hC hm hx hlocal

#print axioms weighted_symmetric_row
#print axioms harmonic_quadratic

open MeasureTheory Set Complex
open scoped ComplexConjugate

private theorem cpow_contOn_Icc {a b : ℝ} (ha : 1 ≤ a) (z : ℂ) :
    ContinuousOn (fun t : ℝ => (t:ℂ)^z) (Icc a b) := by
  intro t ht
  exact (Complex.continuousAt_ofReal_cpow_const t z
    (Or.inr (zero_lt_one.trans_le (ha.trans ht.1)).ne')).continuousWithinAt

private theorem cpow_product {x : ℝ} (hx : 0 < x) (z w : ℂ) :
    (x:ℂ)^z * conj ((x:ℂ)^w) = (x:ℂ)^(z + conj w) := by
  rw [Complex.cpow_add _ _ (by exact_mod_cast hx.ne'),
    Complex.cpow_conj _ _ (by simpa [Complex.arg_ofReal_of_nonneg hx.le] using Real.pi_pos.ne)]
  simp

/-- Bounding finite complex power-sum energy by the harmonic Gram form. -/
theorem power_sum_energy {ι : Type*} (S : Finset ι) (z c : ι → ℂ)
    {a b N : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ N)
    (hz : ∀ i ∈ S, -1/2 ≤ (z i).re) :
    (∫ x in Ioc a b, ‖∑ i ∈ S, c i*(x:ℂ)^(z i)‖^2) ≤
      (4*(1+Real.log N)) * ∑ i ∈ S, ∑ j ∈ S,
        ‖c i‖ * ‖c j‖ * (1/(1+|(z i).im-(z j).im|)) *
          N^((z i).re+1/2) * N^((z j).re+1/2) := by
  let f (x : ℝ) := ∑ i ∈ S, c i*(x:ℂ)^(z i)
  let h (i j : ι) (x : ℝ) := c i * conj (c j) * (x:ℂ)^(z i+conj (z j))
  have hInt (i j : ι) :
      Integrable (h i j) (volume.restrict (Ioc a b)) := by
    have hc : ContinuousOn (h i j) (Icc a b) := continuousOn_const.mul (cpow_contOn_Icc ha _)
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have heq (x : ℝ) (hx : x ∈ Ioc a b) :
      (‖f x‖^2 : ℂ) = ∑ i ∈ S, ∑ j ∈ S, h i j x := by
    rw [← Complex.mul_conj', show f x = ∑ i ∈ S, c i*(x:ℂ)^(z i) from rfl,
      map_sum, Finset.sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [map_mul]
    dsimp only [h]
    have hp := cpow_product (zero_lt_one.trans_le (ha.trans hx.1.le)) (z i) (z j)
    rw [← hp]
    ring
  have hint : (∫ x in Ioc a b, (‖f x‖ ^ 2 : ℂ)) = ∑ i ∈ S, ∑ j ∈ S, ∫ x in Ioc a b, h i j x := by
    rw [setIntegral_congr_fun measurableSet_Ioc heq, integral_finsetSum]
    · refine sum_congr rfl fun i hi => ?_
      exact integral_finsetSum S (fun j hj => hInt i j)
    · exact fun i hi => integrable_finsetSum S (fun j hj => hInt i j)
  have H : (∫ x in Ioc a b, ‖f x‖^2) ≤ ∑ i ∈ S, ∑ j ∈ S, ‖∫ x in Ioc a b, h i j x‖ := by
    have hnon : 0 ≤ ∫ x in Ioc a b, ‖f x‖^2 := integral_nonneg fun x => sq_nonneg _
    have hh := congrArg norm hint
    rw [show (fun x : ℝ => (‖f x‖^2 : ℂ)) = fun x => ((‖f x‖^2 : ℝ):ℂ) from
      funext fun x => (Complex.ofReal_pow _ _).symm, integral_complex_ofReal,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnon] at hh
    rw [hh]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => norm_sum_le _ _)
  have hN : 0 < N := by linarith
  change (∫ x in Ioc a b, ‖f x‖^2) ≤ _
  apply H.trans
  simp only [Finset.mul_sum]
  refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
  change ‖∫ x in Ioc a b, c i * conj (c j) * (x:ℂ)^(z i+conj (z j))‖ ≤ _
  rw [integral_const_mul, norm_mul, norm_mul, Complex.norm_conj]
  rw [← intervalIntegral.integral_of_le hab]
  have he : -1 ≤ (z i+conj (z j)).re := by simp only [Complex.add_re, Complex.conj_re]; linarith [hz i hi,hz j hj]
  have hosc := PintzFixedWindowGram.oscillatory_bound ha hab hb _ he
  calc
    _ ≤ ‖c i‖*‖c j‖*(4*(1+Real.log N)*N^((z i+conj (z j)).re+1)/(1+|(z i+conj (z j)).im|)) :=
      mul_le_mul_of_nonneg_left hosc (by positivity)
    _ = _ := by
      simp only [Complex.add_re, Complex.conj_re, Complex.add_im, Complex.conj_im, ← sub_eq_add_neg]
      rw [show (z i).re+(z j).re+1 = ((z i).re+1/2)+((z j).re+1/2) by ring,
        Real.rpow_add hN]
      ring

#print axioms power_sum_energy

/-- Fixed-length power-sum energy after clipping, and after summing the
harmonic Gram form using local density at each ordinate. -/
theorem clipped_power_sum_energy {ι : Type*} (S : Finset ι) (z c : ι → ℂ) (m : ι → ℝ)
    {a b N Y T C : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ N) (hY : 0 < Y)
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hm : ∀ i ∈ S, 0 ≤ m i)
    (hz : ∀ i ∈ S, -1/2 ≤ (z i).re) (hx : ∀ i ∈ S, |(z i).im| ≤ T)
    (hlocal : ∀ t : ℝ, |t| ≤ T+1/2 →
      (∑ i ∈ S.filter (fun i => |(z i).im-t| ≤ 1/2), m i) ≤ C) :
    (∫ x : ℝ, ‖Y⁻¹ • (∫ t in Ioc (max x a) (min (x+Y) b),
        ∑ i ∈ S, (m i:ℂ) * c i * (t:ℂ)^(z i))‖^2) ≤
      (4*(1+Real.log N))*(2*C*(1+Real.log (2*T+1)))*
        (∑ i ∈ S, m i*(‖c i‖*N^((z i).re+1/2))^2) := by
  let f (x : ℝ) := ∑ i ∈ S, (m i:ℂ)*c i*(x:ℂ)^(z i)
  have hcon : ContinuousOn f (Icc a b) := continuousOn_finsetSum _ fun i hi =>
    continuousOn_const.mul (cpow_contOn_Icc ha _)
  have hMeas : Measurable f := by
    classical
    apply Finset.measurable_fun_sum
    intro i hi
    apply Measurable.const_mul
    simp_rw [Complex.cpow_def]
    exact Measurable.ite (measurableSet_eq_fun Complex.measurable_ofReal measurable_const)
      measurable_const (Complex.continuous_exp.measurable.comp
        ((Complex.measurable_log.comp Complex.measurable_ofReal).mul_const _))
  refine (PintzFixedWindowL2.clipped_moving_average_sq_le hY hMeas
    (hcon.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((hcon.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)).trans ?_
  let W (i : ι) := ‖c i‖*N^((z i).re+1/2)
  have hcomb := harmonic_quadratic S (fun i => (z i).im) m W T C hT hC hm hx hlocal
  have hf : 0 ≤ 4*(1+Real.log N) := by
    have hN : 1 ≤ N := ha.trans (hab.trans hb)
    linarith [Real.log_nonneg hN]
  have H := power_sum_energy S z (fun i => (m i:ℂ)*c i) ha hab hb hz
  refine H.trans ?_
  have heq :
      (∑ i ∈ S, ∑ j ∈ S, ‖(m i:ℂ)*c i‖ * ‖(m j:ℂ)*c j‖ *
        (1/(1+|(z i).im-(z j).im|))*N^((z i).re+1/2)*N^((z j).re+1/2)) =
      ∑ i ∈ S, ∑ j ∈ S, m i*m j*(1/(1+|(z i).im-(z j).im|))*W i*W j := by
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    simp only [W, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm i hi),
      abs_of_nonneg (hm j hj)]
    ring
  rw [heq]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcomb hf

#print axioms clipped_power_sum_energy

/-- Literal low-height zero kernels with both endpoints clipped. -/
theorem clipped_zero_energy {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ) (m : ι → ℝ)
    {a b N Y T C : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ N) (hY : 0 < Y)
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hm : ∀ i ∈ S, 0 ≤ m i)
    (hz : ∀ i ∈ S, 1/2 ≤ (ρ i).re) (hx : ∀ i ∈ S, |(ρ i).im| ≤ T)
    (hlocal : ∀ t : ℝ, |t| ≤ T+1/2 →
      (∑ i ∈ S.filter (fun i => |(ρ i).im-t| ≤ 1/2), m i) ≤ C) :
    (∫ x : ℝ, ‖Y⁻¹ • (if max x a ≤ min (x+Y) b then
        ∑ i ∈ S, (m i:ℂ) * c i *
          (((min (x+Y) b:ℝ):ℂ)^(ρ i) - ((max x a:ℝ):ℂ)^(ρ i))/(ρ i)
        else 0)‖^2) ≤
      (4*(1+Real.log N))*(2*C*(1+Real.log (2*T+1)))*
        (∑ i ∈ S, m i*(‖c i‖*N^((ρ i).re-1/2))^2) := by
  have H := clipped_power_sum_energy S (fun i => ρ i - 1) c m ha hab hb hY hT hC hm
    (by intro i hi; simp only [Complex.sub_re, Complex.one_re]; linarith [hz i hi])
    (by simpa only [Complex.sub_im, Complex.one_im, sub_zero] using hx)
    (by simpa only [Complex.sub_im, Complex.one_im, sub_zero] using hlocal)
  have he (x : ℝ) :
      (∫ t in Ioc (max x a) (min (x+Y) b),
        ∑ i ∈ S, (m i:ℂ) * c i * (t:ℂ)^(ρ i - 1)) =
      (if max x a ≤ min (x+Y) b then
        ∑ i ∈ S, (m i:ℂ) * c i *
          (((min (x+Y) b:ℝ):ℂ)^(ρ i) - ((max x a:ℝ):ℂ)^(ρ i))/(ρ i)
        else 0) := by
    split_ifs with h
    · have ha' : 1 ≤ max x a := ha.trans (le_max_right _ _)
      rw [integral_finsetSum]
      · refine sum_congr rfl fun i hi => ?_
        rw [integral_const_mul, ← intervalIntegral.integral_of_le h, integral_cpow]
        · rw [sub_add_cancel, mul_div_assoc]
        · left
          simp only [Complex.sub_re, Complex.one_re]
          linarith [hz i hi]
      · intro i hi
        have hc : ContinuousOn (fun t : ℝ => (m i:ℂ)*c i*(t:ℂ)^(ρ i-1))
            (Icc (max x a) (min (x+Y) b)) := continuousOn_const.mul (cpow_contOn_Icc ha' _)
        exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · simp [Set.Ioc_eq_empty (fun hlt => h hlt.le)]
  simp_rw [he, Complex.sub_re, Complex.one_re,
    show ∀ i, (ρ i).re - 1 + 1/2 = (ρ i).re - 1/2 by intro i; ring] at H
  exact H

#print axioms clipped_zero_energy
end PintzFixedWindowEnergy
