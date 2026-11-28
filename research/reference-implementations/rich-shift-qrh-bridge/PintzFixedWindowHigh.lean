import PintzFixedWindowEnergy
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory Set
namespace PintzFixedWindowHigh
set_option maxHeartbeats 220000

private noncomputable def endpointDiff (a b Y : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  if a < x+Y ∧ x < b then f (min (x+Y) b) - f (max x a) else 0

private noncomputable def endpointDom (a b Y : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  let q := fun x : ℝ => ‖f x‖^2
  let g := (Ioc a b).indicator q
  let L := (Ioc (a-Y) a).indicator (fun _ : ℝ => q a)
  let R := (Ioc (b-Y) b).indicator (fun _ : ℝ => q b)
  2*(g x + g (x+Y) + L x + R x)

private theorem endpointDom_bound (a b Y : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    ‖endpointDiff a b Y f x‖^2 ≤ endpointDom a b Y f x := by
  let q := fun x : ℝ => ‖f x‖^2
  let g := (Ioc a b).indicator q
  let L := (Ioc (a-Y) a).indicator (fun _ : ℝ => q a)
  let R := (Ioc (b-Y) b).indicator (fun _ : ℝ => q b)
  let d := endpointDiff a b Y f
  change ‖d x‖^2 ≤ 2*(g x + g (x+Y) + L x + R x)
  have hg (t : ℝ) : 0 ≤ g t := by dsimp [g,q]; exact indicator_nonneg (fun (u : ℝ) _ => sq_nonneg ‖f u‖) t
  have hl : 0 ≤ L x := by dsimp [L,q]; exact indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hr : 0 ≤ R x := by dsimp [R,q]; exact indicator_nonneg (fun _ _ => sq_nonneg _) _
  by_cases hx : a < x+Y ∧ x < b
  · have hlow : q (max x a) ≤ g x + L x := by
      by_cases hax : a < x
      · have hdom : x ∈ Ioc a b := ⟨hax,hx.2.le⟩
        simp only [max_eq_left hax.le, g, indicator_of_mem hdom]
        linarith only [hl]
      · have hax' := le_of_not_gt hax
        have hdom : x ∈ Ioc (a-Y) a := ⟨by linarith [hx.1],hax'⟩
        simp only [max_eq_right hax', L, indicator_of_mem hdom]
        linarith only [hg x]
    have hhigh : q (min (x+Y) b) ≤ g (x+Y) + R x := by
      by_cases hxb : x+Y ≤ b
      · have hdom : x+Y ∈ Ioc a b := ⟨hx.1,hxb⟩
        simp only [min_eq_left hxb, g, indicator_of_mem hdom]
        linarith only [hr]
      · have hxb' := lt_of_not_ge hxb
        have hdom : x ∈ Ioc (b-Y) b := ⟨by linarith,hx.2.le⟩
        simp only [min_eq_right hxb'.le, R, indicator_of_mem hdom]
        linarith only [hg (x+Y)]
    dsimp only [d, endpointDiff]
    rw [ite_eq_left hx]
    have H := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sub_le (f (min (x+Y) b)) (f (max x a))) 2
    have H₂ := sq_nonneg (‖f (min (x+Y) b)‖ - ‖f (max x a)‖)
    dsimp [q] at hlow hhigh
    nlinarith only [H,H₂,hlow,hhigh]
  · simp only [d, endpointDiff, ite_eq_right hx, norm_zero, zero_pow (show (2:ℕ) ≠ 0 by decide)]
    linarith only [hg x,hg (x+Y),hl,hr]

private theorem measurable_endpointDiff (a b Y : ℝ) {f : ℝ → ℂ} (hfm : Measurable f) :
    Measurable (endpointDiff a b Y f) := by
  unfold endpointDiff
  have hAdd : Measurable (fun x : ℝ => x + Y) := measurable_id.add_const _
  have hLow : Measurable (fun x : ℝ => max x a) := measurable_id.max measurable_const
  have hHi : Measurable (fun x : ℝ => min (x+Y) b) := hAdd.min measurable_const
  exact Measurable.ite ((measurableSet_lt measurable_const hAdd).inter
      (measurableSet_lt measurable_id measurable_const))
    ((hfm.comp hHi).sub (hfm.comp hLow)) measurable_const

/-- Endpoint evaluation in a clipped window is controlled by the interior
energy and two constant endpoint costs, each supported over length Y. -/
theorem endpoint_window_sq_le {a b Y : ℝ} (hY : 0 ≤ Y) {f : ℝ → ℂ}
    (hfm : Measurable f) (hf₂ : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioc a b)) :
    (∫ x : ℝ, ‖if a < x+Y ∧ x < b then f (min (x+Y) b) - f (max x a) else 0‖^2) ≤
      4*(∫ x in Ioc a b, ‖f x‖^2) + 2*Y*(‖f a‖^2+‖f b‖^2) := by
  let q := fun x : ℝ => ‖f x‖^2
  let g := (Ioc a b).indicator q
  let L := (Ioc (a-Y) a).indicator (fun _ : ℝ => q a)
  let R := (Ioc (b-Y) b).indicator (fun _ : ℝ => q b)
  let d (x : ℝ) := if a < x+Y ∧ x < b then f (min (x+Y) b) - f (max x a) else 0
  have hpt (x : ℝ) : ‖d x‖^2 ≤ 2*(g x + g (x+Y) + L x + R x) :=
    endpointDom_bound a b Y f x
  have hi : Integrable g := hf₂.integrable_indicator measurableSet_Ioc
  have hshift : Integrable (fun x => g (x+Y)) :=
    by
      change Integrable (g ∘ (fun x : ℝ => x+Y)) volume
      exact (measurePreserving_add_right (volume : Measure ℝ) Y).integrable_comp_of_integrable (g := g) hi
  have hconst (p q c : ℝ) : IntegrableOn (fun _ : ℝ => c) (Ioc p q) :=
    integrableOn_const (by simp [Real.volume_Ioc])
  have hl : Integrable L :=
    (hconst (a-Y) a (q a)).integrable_indicator measurableSet_Ioc
  have hr : Integrable R :=
    (hconst (b-Y) b (q b)).integrable_indicator measurableSet_Ioc
  have hI : Integrable (fun x => 2*(g x + g (x+Y) + L x + R x)) :=
    (((hi.add hshift).add hl).add hr).const_mul _
  have hmd : Measurable d := measurable_endpointDiff a b Y hfm
  have hd : Integrable (fun x => ‖d x‖^2) := by
    refine hI.mono' (hmd.norm.pow_const _).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt x
  have hlE : (∫ x, L x) = Y * q a := by
    rw [show L = (Ioc (a-Y) a).indicator (fun _ : ℝ => q a) from rfl,
      integral_indicator measurableSet_Ioc, setIntegral_const,
      Real.volume_real_Ioc_of_le (by linarith : a-Y ≤ a), smul_eq_mul]
    ring
  have hrE : (∫ x, R x) = Y * q b := by
    rw [show R = (Ioc (b-Y) b).indicator (fun _ : ℝ => q b) from rfl,
      integral_indicator measurableSet_Ioc, setIntegral_const,
      Real.volume_real_Ioc_of_le (by linarith : b-Y ≤ b), smul_eq_mul]
    ring
  change (∫ x, ‖d x‖^2) ≤ _
  refine (integral_mono hd hI hpt).trans_eq ?_
  have hadd₁ := integral_add ((hi.add hshift).add hl) hr
  have hadd₂ := integral_add (hi.add hshift) hl
  have hadd₃ := integral_add hi hshift
  simp only [Pi.add_apply] at hadd₁ hadd₂ hadd₃
  rw [integral_const_mul, hadd₁, hadd₂, hadd₃,
    integral_add_right_eq_self (μ := volume) g Y, hlE, hrE]
  have hgE : (∫ x, g x) = ∫ x in Ioc a b, q x := integral_indicator measurableSet_Ioc
  rw [hgE]
  dsimp [q]
  ring

#print axioms endpoint_window_sq_le

/-- A constant clipped endpoint of a high-height zero sum. The denominator
is at least the lower height of the block and finite Cauchy–Schwarz costs
only the total multiplicity. -/
theorem constant_endpoint_sq_le {ι : Type*} (S : Finset ι)
    (ρ c : ι → ℂ) (m : ι → ℝ) {Y M N v : ℝ}
    (hY : 0 < Y) (hM : 0 < M) (hv : 0 < v) (hN : v ≤ N)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hβ : ∀ i ∈ S, 0 ≤ (ρ i).re)
    (hγ : ∀ i ∈ S, M*N/Y ≤ |(ρ i).im|) :
    ‖∑ i ∈ S, (m i:ℂ) * c i * (v:ℂ)^(ρ i) / ((Y:ℂ)*ρ i)‖^2 ≤
      (∑ i ∈ S, m i) * ∑ i ∈ S, m i*(‖c i‖*N^((ρ i).re)/(M*N))^2 := by
  have hMN : 0 < M*N := mul_pos hM (hv.trans_le hN)
  let W (i : ι) := ‖c i‖*N^((ρ i).re)/(M*N)
  have hpt (i : ι) (hi : i ∈ S) :
      ‖(m i:ℂ) * c i * (v:ℂ)^(ρ i) / ((Y:ℂ)*ρ i)‖ ≤ m i * W i := by
    have hden : M*N ≤ Y*‖ρ i‖ := by
      have H := (hγ i hi).trans (Complex.abs_im_le_norm (ρ i))
      have H' := (div_le_iff₀ hY).mp H
      simpa [mul_comm] using H'
    rw [norm_div, norm_mul (Y:ℂ), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm i hi),
      Complex.norm_cpow_eq_rpow_re_of_pos hv]
    calc
      _ ≤ m i*‖c i‖*N^((ρ i).re)/(Y*‖ρ i‖) := by
        apply div_le_div_of_nonneg_right _ (mul_nonneg hY.le (norm_nonneg _))
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hm i hi) (norm_nonneg _))
        exact Real.rpow_le_rpow hv.le hN (hβ i hi)
      _ ≤ m i*‖c i‖*N^((ρ i).re)/(M*N) :=
        div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (hm i hi) (norm_nonneg _)) (Real.rpow_nonneg (hv.le.trans hN) _)) hMN hden
      _ = _ := by dsimp [W]; ring
  have hn : ‖∑ i ∈ S, (m i:ℂ) * c i * (v:ℂ)^(ρ i) / ((Y:ℂ)*ρ i)‖ ≤
      ∑ i ∈ S, m i*W i := (norm_sum_le _ _).trans (Finset.sum_le_sum hpt)
  refine (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans ?_
  have H := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (m i))
    (fun i => Real.sqrt (m i) * W i)
  have h₁ : (∑ i ∈ S, Real.sqrt (m i) * (Real.sqrt (m i) * W i)) =
      ∑ i ∈ S, m i * W i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hm i hi)]
  have h₂ : (∑ i ∈ S, Real.sqrt (m i)^2) = ∑ i ∈ S, m i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hm i hi)
  have h₃ : (∑ i ∈ S, (Real.sqrt (m i)*W i)^2) =
      ∑ i ∈ S, m i*(W i)^2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_pow, Real.sq_sqrt (hm i hi)]
  rwa [h₁,h₂,h₃] at H

#print axioms constant_endpoint_sq_le

open Finset Complex

/-- Clipped window energy of a high-height block. The moving endpoints
cost N times the harmonic row factor, while the stationary endpoints cost
Y times the total multiplicity, both times the same squared amplitudes. -/
theorem high_zero_window_energy {ι : Type*} (S : Finset ι)
    (ρ c : ι → ℂ) (m : ι → ℝ) {Y M N a b T C : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ N)
    (hY : 0 < Y) (hM : 0 < M) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hβ : ∀ i ∈ S, 0 ≤ (ρ i).re)
    (hγ : ∀ i ∈ S, M*N/Y ≤ |(ρ i).im|) (hx : ∀ i ∈ S, |(ρ i).im| ≤ T)
    (hlocal : ∀ t : ℝ, |t| ≤ T+1/2 →
      (∑ i ∈ S.filter (fun i => |(ρ i).im-t| ≤ 1/2), m i) ≤ C) :
    let f (t : ℝ) := ∑ i ∈ S, (m i:ℂ)*c i*(t:ℂ)^(ρ i)/((Y:ℂ)*ρ i)
    (∫ x : ℝ, ‖if a < x+Y ∧ x < b then f (min (x+Y) b)-f (max x a) else 0‖^2) ≤
      (4*(4*(1+Real.log N))*(2*C*(1+Real.log (2*T+1)))*N + 4*Y*(∑ i ∈ S,m i)) *
        ∑ i ∈ S, m i*(‖c i‖*N^((ρ i).re)/(M*N))^2 := by
  dsimp only
  let f (t : ℝ) := ∑ i ∈ S, (m i:ℂ)*c i*(t:ℂ)^(ρ i)/((Y:ℂ)*ρ i)
  let k (i : ι) := c i/((Y:ℂ)*ρ i)
  let W (i : ι) := ‖c i‖*N^((ρ i).re)/(M*N)
  let V (i : ι) := ‖k i‖*N^((ρ i).re+1/2)
  have hf (t : ℝ) : f t = ∑ i ∈ S, (m i:ℂ)*k i*(t:ℂ)^(ρ i) := by
    exact sum_congr rfl fun i _ => by dsimp [f,k]; ring
  have hN : 0 < N := by linarith
  have hMN : 0 < M*N := mul_pos hM hN
  have hmeas : Measurable f := by
    classical
    change Measurable (fun t => f t)
    simp only [hf]
    apply Finset.measurable_fun_sum
    intro i hi
    apply Measurable.const_mul
    simp_rw [Complex.cpow_def]
    exact Measurable.ite (measurableSet_eq_fun Complex.measurable_ofReal measurable_const)
      measurable_const (Complex.continuous_exp.measurable.comp
        ((Complex.measurable_log.comp Complex.measurable_ofReal).mul_const _))
  have hcon : ContinuousOn f (Icc a b) := by
    change ContinuousOn (fun t => f t) (Icc a b)
    simp only [hf]
    apply continuousOn_finsetSum _ fun i hi => continuousOn_const.mul ?_
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const t (ρ i)
      (Or.inr (zero_lt_one.trans_le (ha.trans ht.1)).ne')).continuousWithinAt
  have hsplit := endpoint_window_sq_le hY.le hmeas
    ((hcon.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hₐ : ‖f a‖^2 ≤ (∑ i ∈ S,m i)*∑ i ∈ S,m i*(W i)^2 :=
    constant_endpoint_sq_le S ρ c m hY hM (by linarith) (hab.trans hb) hm hβ hγ
  have hᵦ : ‖f b‖^2 ≤ (∑ i ∈ S,m i)*∑ i ∈ S,m i*(W i)^2 :=
    constant_endpoint_sq_le S ρ c m hY hM (by linarith) hb hm hβ hγ
  have hp := PintzFixedWindowEnergy.power_sum_energy S ρ (fun i => (m i:ℂ)*k i) ha hab hb
    (by intro i hi; linarith [hβ i hi])
  have hq := PintzFixedWindowEnergy.harmonic_quadratic S (fun i => (ρ i).im) m V T C
    hT hC hm hx hlocal
  have hA : 0 ≤ 4*(1+Real.log N) := by linarith [Real.log_nonneg (ha.trans (hab.trans hb))]
  have hB : 0 ≤ 2*C*(1+Real.log (2*T+1)) := by
    have := Real.log_nonneg (show 1 ≤ 2*T+1 by linarith)
    positivity
  have hh : (∫ x in Ioc a b, ‖f x‖^2) ≤
      (4*(1+Real.log N))*(2*C*(1+Real.log (2*T+1))) * ∑ i ∈ S,m i*(V i)^2 := by
    simp_rw [hf]
    refine hp.trans ?_
    have heq :
        (∑ i ∈ S, ∑ j ∈ S, ‖(m i:ℂ)*k i‖ * ‖(m j:ℂ)*k j‖ *
          (1/(1+|(ρ i).im-(ρ j).im|))*N^((ρ i).re+1/2)*N^((ρ j).re+1/2)) =
        ∑ i ∈ S, ∑ j ∈ S, m i*m j*(1/(1+|(ρ i).im-(ρ j).im|))*V i*V j := by
      refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
      simp only [V, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm i hi),
        abs_of_nonneg (hm j hj)]
      ring
    rw [heq]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hq hA
  have hV : (∑ i ∈ S,m i*(V i)^2) ≤ N*∑ i ∈ S,m i*(W i)^2 := by
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hden : M*N ≤ Y*‖ρ i‖ := by
      have H := (hγ i hi).trans (Complex.abs_im_le_norm (ρ i))
      simpa [mul_comm] using (div_le_iff₀ hY).mp H
    have hk : ‖k i‖ ≤ ‖c i‖/(M*N) := by
      dsimp [k]
      rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hMN hden
    have hv : V i ≤ W i * Real.sqrt N := by
      dsimp [V,W]
      rw [Real.rpow_add hN, Real.sqrt_eq_rpow]
      calc
        _ ≤ (‖c i‖/(M*N))*(N^((ρ i).re)*N^(1/2:ℝ)) :=
          mul_le_mul_of_nonneg_right hk (by positivity)
        _ = _ := by ring
    have hs := pow_le_pow_left₀ (show 0 ≤ V i by dsimp [V]; positivity) hv 2
    rw [mul_pow (W i) (Real.sqrt N),Real.sq_sqrt hN.le] at hs
    calc
      _ ≤ m i*((W i)^2*N) := mul_le_mul_of_nonneg_left hs (hm i hi)
      _ = _ := by ring
  have hmove := hh.trans (mul_le_mul_of_nonneg_left hV (mul_nonneg hA hB))
  change (∫ x : ℝ, ‖if a < x+Y ∧ x < b then f (min (x+Y) b)-f (max x a) else 0‖^2) ≤ _
  refine hsplit.trans ?_
  have H₁ := mul_le_mul_of_nonneg_left hmove (by norm_num : (0:ℝ) ≤ 4)
  have H₂ := mul_le_mul_of_nonneg_left (add_le_add hₐ hᵦ) (by positivity : 0 ≤ 2*Y)
  change 4*(∫ x in Ioc a b, ‖f x‖^2) + 2*Y*(‖f a‖^2+‖f b‖^2) ≤
      (4*(4*(1+Real.log N))*(2*C*(1+Real.log (2*T+1)))*N + 4*Y*(∑ i ∈ S,m i)) *
        ∑ i ∈ S, m i*(W i)^2
  nlinarith only [H₁,H₂]

#print axioms high_zero_window_energy

/-- Count all weighted ordinates in the bounded band by centered unit bins. -/
theorem count_of_unit_boxes {ι : Type*} (S : Finset ι) (x m : ι → ℝ) {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hm : ∀ i ∈ S, 0 ≤ m i)
    (hx : ∀ i ∈ S, |x i| ≤ T)
    (hlocal : ∀ t : ℝ, |t| ≤ T+1/2 →
      (∑ i ∈ S.filter (fun i => |x i-t| ≤ 1/2), m i) ≤ C) :
    (∑ i ∈ S,m i) ≤ (2*T+1)*C := by
  classical
  let n := ⌊2*T⌋₊ + 1
  let f (i : ι) := ⌊x i+T⌋₊
  have hmaps (i : ι) (hi : i ∈ S) : f i ∈ range n :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (by linarith [(abs_le.mp (hx i hi)).2])))
  have hn : (n:ℝ) ≤ 2*T+1 := by
    dsimp [n]
    push_cast
    exact add_le_add_left (Nat.floor_le (show 0 ≤ 2*T by positivity)) _
  have hrow (j : ℕ) (hj : j ∈ range n) :
      (∑ i ∈ S.filter (fun i => f i = j), m i) ≤ C := by
    have hsub : S.filter (fun i => f i = j) ⊆
        S.filter (fun i => |x i - ((j:ℝ)+1/2-T)| ≤ 1/2) := by
      intro i hi
      obtain ⟨his, hij⟩ := mem_filter.mp hi
      have hp : 0 ≤ x i+T := by linarith [(abs_le.mp (hx i his)).1]
      have h₁ : ((f i:ℕ):ℝ) ≤ x i+T := Nat.floor_le hp
      have h₂ : x i+T < (f i:ℝ)+1 := Nat.lt_floor_add_one _
      rw [hij] at h₁ h₂
      exact mem_filter.mpr ⟨his,abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have hj' : (j:ℝ) ≤ 2*T := by
      have h : j ≤ ⌊2*T⌋₊ := Nat.le_of_lt_succ (mem_range.mp hj)
      exact (by exact_mod_cast h : (j:ℝ) ≤ ⌊2*T⌋₊).trans (Nat.floor_le (by positivity))
    refine ((sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hm i (mem_filter.mp hi).1))).trans
      (hlocal _ (abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α:=ℝ) j], by linarith⟩))
  calc
    _ = ∑ j ∈ range n, ∑ i ∈ S.filter (fun i => f i = j), m i := (sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ _j ∈ range n,C := sum_le_sum hrow
    _ = (n:ℝ)*C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hn hC

#print axioms count_of_unit_boxes

/-- Dyadic high-height block in the N/M normalization required by
the density sum, after applying the unit-box count to the edge terms. -/
theorem high_zero_window_energy_normalized {ι : Type*} (S : Finset ι)
    (ρ c : ι → ℂ) (m : ι → ℝ) {Y M N a b T C : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ N)
    (hY : 0 < Y) (hYN : Y ≤ N) (hM : 1 ≤ M)
    (hT : 0 ≤ T) (hTupper : T ≤ 2*(M*N/Y)) (hC : 0 ≤ C)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hβ : ∀ i ∈ S, 0 ≤ (ρ i).re)
    (hγ : ∀ i ∈ S, M*N/Y ≤ |(ρ i).im|) (hx : ∀ i ∈ S, |(ρ i).im| ≤ T)
    (hlocal : ∀ t : ℝ, |t| ≤ T+1/2 →
      (∑ i ∈ S.filter (fun i => |(ρ i).im-t| ≤ 1/2), m i) ≤ C) :
    let f (t : ℝ) := ∑ i ∈ S, (m i:ℂ)*c i*(t:ℂ)^(ρ i)/((Y:ℂ)*ρ i)
    (∫ x : ℝ, ‖if a < x+Y ∧ x < b then f (min (x+Y) b)-f (max x a) else 0‖^2) ≤
      (4*(4*(1+Real.log N))*(2*C*(1+Real.log (2*T+1))) + 20*C)*(N/M) *
        ∑ i ∈ S,m i*(‖c i‖*N^((ρ i).re-1))^2 := by
  dsimp only
  have hNp : 0 < N := by linarith
  have hMp : 0 < M := by linarith
  refine (high_zero_window_energy S ρ c m ha hab hb hY hMp hT hC hm hβ hγ hx hlocal).trans ?_
  let D := 4*(4*(1+Real.log N))*(2*C*(1+Real.log (2*T+1)))
  let A := ∑ i ∈ S,m i*(‖c i‖*N^((ρ i).re-1))^2
  have hD : 0 ≤ D := by
    have hL₁ := Real.log_nonneg (ha.trans (hab.trans hb))
    have hL₂ := Real.log_nonneg (show 1 ≤ 2*T+1 by linarith)
    dsimp [D]
    positivity
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i hi => mul_nonneg (hm i hi) (sq_nonneg _))
  have hcount := count_of_unit_boxes S (fun i => (ρ i).im) m hT hC hm hx hlocal
  have hcount' : Y*(∑ i ∈ S,m i) ≤ 5*C*(M*N) := by
    have hHt : T*Y ≤ 2*M*N := (le_div_iff₀ hY).mp (by
      convert hTupper using 1
      ring)
    have hMY : Y ≤ M*N := hYN.trans (by nlinarith only [mul_nonneg (sub_nonneg.mpr hM) hNp.le])
    calc
      _ ≤ Y*((2*T+1)*C) := mul_le_mul_of_nonneg_left hcount hY.le
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_left hHt (show 0 ≤ 2*C by positivity),
          mul_le_mul_of_nonneg_left hMY hC]
  have hEq : (∑ i ∈ S,m i*(‖c i‖*N^((ρ i).re)/(M*N))^2) = A/M^2 := by
    dsimp [A]
    rw [Finset.sum_div]
    refine sum_congr rfl (fun i hi => ?_)
    rw [Real.rpow_sub_one hNp.ne']
    field_simp [hNp.ne',hMp.ne']
  change (D*N + 4*Y*(∑ i ∈ S,m i))*_ ≤ (D+20*C)*(N/M)*A
  rw [hEq]
  -- Cancel the positive power of the height ratio; the moving term
  -- has an extra factor M⁻¹ and may be bounded by M≥1.
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hMp)).2
  rw [show (D+20*C)*(N/M)*A*M^2 = ((D+20*C)*(N*M))*A by field_simp]
  apply mul_le_mul_of_nonneg_right _ hA
  have hMN : D*N ≤ D*(N*M) := by
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hNp.le hM) hD
  nlinarith only [hcount',hMN]

#print axioms high_zero_window_energy_normalized
end PintzFixedWindowHigh
