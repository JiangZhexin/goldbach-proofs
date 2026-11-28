import Zeta23.ThmE.LGrowth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Complex Set MeasureTheory Filter Topology Finset
open scoped Asymptotics
open Zeta23.ThmE

namespace PintzJutilaSecondAbel

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

private def prefixNat (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (n+1), χ (j:ZMod q)) - χ 0

omit [NeZero q] in
private theorem prefixNat_eq (n : ℕ) :
    prefixNat χ n = ∑ j ∈ Finset.Icc 1 n, χ (j:ZMod q) := by
  unfold prefixNat
  have h : ∑ j ∈ Finset.range (n+1), χ (j:ZMod q) =
      χ 0 + ∑ j ∈ Finset.Icc 1 n, χ (j:ZMod q) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n)]
    simp only [Nat.cast_zero,zero_add]
    have H : Finset.Ico 1 (n+1) = Finset.Icc 1 n := by ext j; simp only [Finset.mem_Ico,Finset.mem_Icc]; omega
    rw [H]
  rw [h]
  ring

private theorem prefixNat_mod (hχ : χ ≠ 1) (n : ℕ) :
    prefixNat χ (n%q) = prefixNat χ n := by
  have H : n+1 = n%q+1+q*(n/q) := by
    have h := Nat.mod_add_div n q
    omega
  unfold prefixNat
  conv_rhs => lhs; rw [H,sum_range_add_mul_period hχ]

/-- A periodic extension of the real character partial-sum function. -/
def periodicPrefix (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  prefixNat χ ((⌊t⌋ : ℤ) % (q:ℤ)).toNat

omit [NeZero q] in
theorem periodic_periodicPrefix (χ : DirichletCharacter ℂ q) :
    Function.Periodic (periodicPrefix χ) (q:ℝ) := by
  intro t
  simp only [periodicPrefix, Int.floor_add_natCast, Int.add_emod_right]

theorem periodicPrefix_eq (hχ : χ ≠ 1) {t : ℝ} (ht : 0 ≤ t) :
    periodicPrefix χ t = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q) := by
  rw [periodicPrefix, ← Int.natCast_floor_eq_floor ht, ← Int.natCast_mod, Int.toNat_natCast,
    prefixNat_mod hχ, prefixNat_eq]

theorem periodicPrefix_norm (hχ : χ ≠ 1) (t : ℝ) : ‖periodicPrefix χ t‖ ≤ q := by
  rw [periodicPrefix,prefixNat_eq]
  exact norm_sum_Icc_le hχ _

omit [NeZero q] in
theorem periodicPrefix_measurable (χ : DirichletCharacter ℂ q) :
    Measurable (periodicPrefix χ) := by
  unfold periodicPrefix
  exact (measurable_of_countable (fun k : ℤ => prefixNat χ (k%(q:ℤ)).toNat)).comp Int.measurable_floor

def mean (χ : DirichletCharacter ℂ q) : ℂ :=
  (∫ t in (1:ℝ)..1+(q:ℝ), periodicPrefix χ t)/(q:ℂ)

def centered (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ := periodicPrefix χ t - mean χ

def secondPrefix (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∫ u in (1:ℝ)..t, centered χ u

omit [NeZero q] in
theorem measurable_centered (χ : DirichletCharacter ℂ q) : Measurable (centered χ) :=
  (periodicPrefix_measurable χ).sub measurable_const

theorem norm_centered_le (hχ : χ ≠ 1) (t : ℝ) : ‖centered χ t‖ ≤ (q:ℝ)+‖mean χ‖ :=
  (norm_sub_le _ _).trans (add_le_add (periodicPrefix_norm hχ t) le_rfl)

theorem intervalIntegrable_centered (hχ : χ ≠ 1) (a b : ℝ) :
    IntervalIntegrable (centered χ) volume a b := by
  rw [intervalIntegrable_iff]
  have hc : IntegrableOn (fun _ : ℝ => (q:ℝ) + ‖mean χ‖) (Set.uIoc a b) :=
    (intervalIntegrable_iff.mp (intervalIntegrable_const (μ := volume)))
  exact hc.mono' (measurable_centered χ).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_centered_le hχ))

theorem secondPrefix_periodic (hχ : χ ≠ 1) :
    Function.Periodic (secondPrefix χ) (q:ℝ) := by
  have hf : Function.Periodic (centered χ) (q:ℝ) := fun t => by
    simp only [centered,periodic_periodicPrefix χ t]
  have h0 : (∫ t in (1:ℝ)..1+(q:ℝ), centered χ t) = 0 := by
    unfold centered
    have hint (a b : ℝ) : IntervalIntegrable (periodicPrefix χ) volume a b := by
      rw [intervalIntegrable_iff]
      have hc : IntegrableOn (fun _ : ℝ => (q:ℝ)) (Set.uIoc a b) :=
        (intervalIntegrable_iff.mp (intervalIntegrable_const (μ := volume)))
      exact hc.mono' (periodicPrefix_measurable χ).aestronglyMeasurable
        (Filter.Eventually.of_forall (periodicPrefix_norm hχ))
    rw [intervalIntegral.integral_sub (hint _ _) intervalIntegrable_const, intervalIntegral.integral_const,
      add_sub_cancel_left,Complex.real_smul,mean]
    have hqC : (q:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
    push_cast
    field_simp
    ring
  intro t
  unfold secondPrefix
  rw [hf.intervalIntegral_add_eq_add 1 t (intervalIntegrable_centered hχ),h0,add_zero]

theorem secondPrefix_continuous (hχ : χ ≠ 1) : Continuous (secondPrefix χ) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_centered hχ) 1

theorem secondPrefix_bounded (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖secondPrefix χ t‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := (q:ℝ))).exists_bound_of_continuousOn
    (secondPrefix_continuous hχ).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro t
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  let u := Int.fract (t/(q:ℝ))*(q:ℝ)
  have hu : u ∈ Set.Ico (0:ℝ) (q:ℝ) := Int.fract_div_mul_self_mem_Ico _ _ hq
  have he : u + ⌊t/(q:ℝ)⌋ • (q:ℝ) = t := Int.fract_div_mul_self_add_zsmul_eq _ _ hq.ne'
  rw [← he,(secondPrefix_periodic hχ).zsmul _ u]
  exact (hC _ ⟨hu.1,hu.2.le⟩).trans (le_max_left _ _)

/-- A triangular Fubini identity proves the second Abel integration without
requiring the discontinuous step-function prefix to be a derivative at its jumps. -/
theorem primitive_fubini (g : ℝ → ℂ) (hg : Measurable g) {D : ℝ} (hD : 0 ≤ D)
    (hgb : ∀ t, ‖g t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioi (1:ℝ), (∫ u in (1:ℝ)..t, g u) * (t:ℂ)^(-(s+2))) =
      (∫ u in Ioi (1:ℝ), g u * (u:ℂ)^(-(s+1))) / (s+1) := by
  let k (t : ℝ) := Complex.exp ((Real.log t:ℂ)*(-(s+2)))
  have hk : Measurable k := Complex.continuous_exp.measurable.comp
    ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).mul measurable_const)
  have hk_eq {t : ℝ} (ht : 0 < t) : k t = (t:ℂ)^(-(s+2)) := by
    have htC : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    dsimp only [k]
    rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht.le]
  let H (u t : ℝ) : ℂ := if u ≤ t then g u*k t else 0
  let μ := volume.restrict (Ioi (1:ℝ))
  have hHm : Measurable (Function.uncurry H) :=
    ((hg.comp measurable_fst).mul (hk.comp measurable_snd)).piecewise
      (measurableSet_le measurable_fst measurable_snd) measurable_const
  have hHsec (t : ℝ) :
      (fun u => H u t) = (Iic t).indicator (fun u => g u*k t) := by
    funext u; rfl
  have hGI (t : ℝ) : IntegrableOn g (Ioc 1 t) := by
    refine (integrableOn_const (s := Ioc 1 t) (C := D) (by simp [Real.volume_Ioc])).mono'
      hg.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
  have hsect (t : ℝ) : Integrable (fun u => H u t) μ := by
    rw [hHsec, integrable_indicator_iff measurableSet_Iic, IntegrableOn]
    dsimp [μ]
    rw [Measure.restrict_restrict measurableSet_Iic, inter_comm, Ioi_inter_Iic]
    exact (hGI t).mul_const _
  have hnormSec (t : ℝ) :
      (fun u => ‖H u t‖) = (Iic t).indicator (fun u => ‖g u*k t‖) := by
    funext u
    by_cases hu : u ≤ t <;> simp [H, Set.indicator,hu]
  have hsectNorm (t : ℝ) (ht : 1 < t) :
      (∫ u, ‖H u t‖ ∂μ) ≤ D*t^(-s.re-1) := by
    change (∫ u in Ioi (1:ℝ), ‖H u t‖) ≤ _
    rw [hnormSec, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hRe : (-(s+2)).re = -s.re-2 := by simp; ring
    have hkn : ‖k t‖ = t^(-s.re-2) := by
      rw [hk_eq ht0, Complex.norm_cpow_eq_rpow_re_of_pos ht0,hRe]
    calc
      _ ≤ ∫ u in Ioc (1:ℝ) t, D*t^(-s.re-2) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (integrableOn_const (by simp [Real.volume_Ioc]))
        filter_upwards [] with u
        rw [norm_mul,hkn]
        exact mul_le_mul_of_nonneg_right (hgb _) (Real.rpow_nonneg ht0.le _)
      _ = (t-1)*(D*t^(-s.re-2)) := by
        rw [integral_const,measureReal_def,Measure.restrict_apply MeasurableSet.univ,
          Set.univ_inter,Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),smul_eq_mul]
      _ ≤ t*(D*t^(-s.re-2)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by
        rw [show -s.re-2 = (-s.re-1)-1 by ring, Real.rpow_sub_one ht0.ne']
        field_simp
  have hMaj : Integrable (fun t : ℝ => D*t^(-s.re-1)) μ :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have hprod : Integrable (Function.uncurry H) (μ.prod μ) := by
    apply (integrable_prod_iff' hHm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hsect, ?_⟩
    apply hMaj.mono' hHm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hsectNorm t ht
  have HU (t : ℝ) (ht : 1 < t) :
      (∫ u, H u t ∂μ) = (∫ u in (1:ℝ)..t, g u) * (t:ℂ)^(-(s+2)) := by
    change (∫ u in Ioi (1:ℝ), H u t) = _
    rw [hHsec,setIntegral_indicator measurableSet_Iic,Ioi_inter_Iic,integral_mul_const,
      ← intervalIntegral.integral_of_le ht.le,hk_eq (zero_lt_one.trans ht)]
  have HT (u : ℝ) (hu : 1 < u) :
      (∫ t, H u t ∂μ) = g u * (u:ℂ)^(-(s+1))/(s+1) := by
    have he : H u = (Ici u).indicator (fun t => g u*k t) := by funext t; rfl
    change (∫ t in Ioi (1:ℝ), H u t) = _
    rw [he,setIntegral_indicator measurableSet_Ici,
      show Ioi (1:ℝ) ∩ Ici u = Ici u by exact inter_eq_right.mpr (fun x hx => hu.trans_le hx),
      integral_Ici_eq_integral_Ioi,integral_const_mul]
    have hkInt : (∫ t in Ioi u, k t) = ∫ t in Ioi u, (t:ℂ)^(-(s+2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hk_eq (zero_lt_one.trans (hu.trans ht))
    rw [hkInt,integral_Ioi_cpow_of_lt (by simp; linarith) (zero_lt_one.trans hu)]
    rw [show -(s+2)+1 = -(s+1) by ring,div_neg,neg_div,neg_neg]
    ring
  calc
    _ = ∫ t, ∫ u, H u t ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (HU t ht).symm
    _ = ∫ u, ∫ t, H u t ∂μ ∂μ := (integral_integral_swap hprod).symm
    _ = ∫ u in Ioi (1:ℝ), g u*(u:ℂ)^(-(s+1))/(s+1) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact HT u hu
    _ = _ := by simp_rw [div_eq_mul_inv, integral_mul_const]

/-- Second Abel representation on the overlap with the standard first
Abel formula. The constant part of the periodic prefix integrates to its mean. -/
theorem second_abel_positive (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    χ.LFunction s = mean χ+s*(s+1)*∫ t in Ioi (1:ℝ), secondPrefix χ t * (t:ℂ)^(-(s+2)) := by
  rw [LFunction_eq_mul_integral hχ hs]
  have hP := primitive_fubini (centered χ) (measurable_centered χ)
    (show 0 ≤ (q:ℝ)+‖mean χ‖ by positivity) (norm_centered_le hχ) hs
  have hpow : IntegrableOn (fun t : ℝ => (t:ℂ)^(-(s+1))) (Ioi (1:ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hcg : IntegrableOn (fun t : ℝ => centered χ t*(t:ℂ)^(-(s+1))) (Ioi (1:ℝ)) :=
    hpow.bdd_mul (measurable_centered χ).aestronglyMeasurable (Filter.Eventually.of_forall (norm_centered_le hχ))
  have hfg : IntegrableOn (fun t : ℝ => mean χ*(t:ℂ)^(-(s+1))) (Ioi (1:ℝ)) := hpow.const_mul _
  have hEq : (∫ t : ℝ in Ioi (1:ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t:ℂ)^(-(s+1))) =
      ∫ t in Ioi (1:ℝ), centered χ t*(t:ℂ)^(-(s+1))+mean χ*(t:ℂ)^(-(s+1)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [← periodicPrefix_eq hχ (zero_lt_one.trans ht).le,centered]
    ring
  have hMean : (∫ t : ℝ in Ioi (1:ℝ), mean χ*(t:ℂ)^(-(s+1))) = mean χ/s := by
    rw [integral_const_mul,integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one,
      show -(s+1)+1 = -s by ring,Complex.ofReal_one,Complex.one_cpow,div_neg,neg_div,neg_neg]
    ring
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hs1 : s+1 ≠ 0 := Complex.ne_zero_of_re_pos (by simp; linarith)
  unfold secondPrefix
  rw [hEq,integral_add hcg hfg,hMean,hP]
  field_simp
  ring

private def cutoffPrefix (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1:ℝ)).indicator (secondPrefix χ)

private theorem mellin_cutoffPrefix (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (cutoffPrefix χ) (-(s+1)) =
      ∫ t in Ioi (1:ℝ), secondPrefix χ t * (t:ℂ)^(-(s+2)) := by
  unfold mellin cutoffPrefix
  have he (t : ℝ) : (t:ℂ)^(-(s+1)-1) • (Ioi (1:ℝ)).indicator (secondPrefix χ) t =
      (Ioi (1:ℝ)).indicator (fun t => secondPrefix χ t*(t:ℂ)^(-(s+2))) t := by
    by_cases ht : t ∈ Ioi (1:ℝ)
    · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht,smul_eq_mul,
        show -(s+1)-1 = -(s+2) by ring,mul_comm]
    · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem ht,smul_zero]
  simp_rw [he]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

private theorem differentiableAt_cutoffPrefix (hχ : χ ≠ 1) {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ (fun z => mellin (cutoffPrefix χ) (-(z+1))) s := by
  obtain ⟨C,hC,hCb⟩ := secondPrefix_bounded hχ
  have hcn (t : ℝ) : ‖cutoffPrefix χ t‖ ≤ C := by
    by_cases ht : t ∈ Ioi (1:ℝ)
    · rw [cutoffPrefix,Set.indicator_of_mem ht]; exact hCb t
    · rw [cutoffPrefix,Set.indicator_of_notMem ht,norm_zero]; exact hC
  have hm : Measurable (cutoffPrefix χ) :=
    (secondPrefix_continuous hχ).measurable.indicator measurableSet_Ioi
  have hloc : LocallyIntegrable (cutoffPrefix χ) := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    refine Measure.integrableOn_of_bounded (M := C) hK.measure_lt_top.ne
      hm.aestronglyMeasurable (Filter.Eventually.of_forall hcn)
  have htop : cutoffPrefix χ =O[atTop] (fun t : ℝ => t ^ (-(0:ℝ))) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [neg_zero,Real.rpow_zero,norm_one,mul_one]
    exact hcn t
  have hbot : cutoffPrefix χ =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(-(s.re+2)))) := by
    have hev : cutoffPrefix χ =ᶠ[𝓝[>] 0] (fun _ => (0:ℂ)) := by
      have HH : Iio (1:ℝ) ∈ 𝓝[>] (0:ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
      filter_upwards [HH] with t ht
      apply Set.indicator_of_notMem
      change ¬1 < t
      change t < 1 at ht
      linarith
    exact (Asymptotics.isBigO_zero _ _).congr' hev.symm EventuallyEq.rfl
  have h := mellin_differentiableAt_of_isBigO_rpow (E := ℂ) (a := 0) (b := -(s.re+2))
    (f := cutoffPrefix χ) (s := -(s+1)) (hloc.locallyIntegrableOn _)
    htop (by simp; linarith) hbot (by simp)
  have hd : DifferentiableAt ℂ (fun z : ℂ => -(z+1)) s := (differentiableAt_id.add_const (1:ℂ)).neg
  change DifferentiableAt ℂ ((mellin (cutoffPrefix χ)) ∘ (fun z : ℂ => -(z+1))) s
  exact h.comp s hd

/-- Second Abel continues the integral through the entire closed right
half-plane, in fact to Re(s)>−1. -/
theorem second_abel (hχ : χ ≠ 1) {s : ℂ} (hs : -1 < s.re) :
    χ.LFunction s = mean χ+s*(s+1)*∫ t in Ioi (1:ℝ), secondPrefix χ t * (t:ℂ)^(-(s+2)) := by
  let F (z : ℂ) := mean χ+z*(z+1)*mellin (cutoffPrefix χ) (-(z+1))
  have hU : IsOpen {z : ℂ | -1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hA : AnalyticOnNhd ℂ F {z : ℂ | -1 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hf := differentiableAt_cutoffPrefix hχ hz
    exact ((differentiableAt_const (mean χ)).add
      ((differentiableAt_id.mul (differentiableAt_id.add_const (1:ℂ))).mul hf)).differentiableWithinAt
  have hL : AnalyticOnNhd ℂ χ.LFunction {z : ℂ | -1 < z.re} :=
    (LFunction_analyticOnNhd hχ).mono (Set.subset_univ _)
  have hEq : χ.LFunction =ᶠ[𝓝 (2:ℂ)] F := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2:ℂ) ∈ {z : ℂ | 0 < z.re} by norm_num)] with z hz
    dsimp only [F]
    rw [second_abel_positive hχ hz, mellin_cutoffPrefix]
  have hh := hL.eqOn_of_preconnected_of_eventuallyEq hA (convex_halfSpace_re_gt (-1)).isPreconnected
    (show (2:ℂ) ∈ {z : ℂ | -1 < z.re} by norm_num) hEq
  simpa only [F,mellin_cutoffPrefix] using hh hs

/-- Polynomial growth of the actual nonprincipal L-function down to the
imaginary axis. The constant is allowed to depend on the character. -/
theorem quadratic_growth_closed (hχ : χ ≠ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 2 → ‖χ.LFunction z‖ ≤ D*(1+|z.im|)^2 := by
  obtain ⟨C,hC,H⟩ := secondPrefix_bounded hχ
  refine ⟨‖mean χ‖+6*C,by positivity,?_⟩
  intro z hz hz₂
  have hid := second_abel hχ (s := z) (by linarith)
  have hmaj : IntegrableOn (fun t : ℝ => C*t^(-z.re-2)) (Ioi (1:ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have hI : ‖∫ t in Ioi (1:ℝ), secondPrefix χ t*(t:ℂ)^(-(z+2))‖ ≤ C := by
    have hb : ‖∫ t in Ioi (1:ℝ), secondPrefix χ t*(t:ℂ)^(-(z+2))‖ ≤
        ∫ t in Ioi (1:ℝ), C*t^(-z.re-2) := by
      apply norm_integral_le_of_norm_le hmaj
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht),
        show (-(z+2)).re = -z.re-2 by simp; ring]
      exact mul_le_mul_of_nonneg_right (H _) (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
    refine hb.trans ?_
    rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,Real.one_rpow,
      show -z.re-2+1 = -(z.re+1) by ring,div_neg,neg_div,neg_neg,one_div,← div_eq_mul_inv]
    exact div_le_self hC (by linarith)
  have hz1 : ‖z‖ ≤ 2*(1+|z.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [abs_of_nonneg hz]
    linarith [abs_nonneg z.im]
  have hz' : ‖z+1‖ ≤ 3*(1+|z.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,add_zero,abs_of_nonneg (by linarith)]
    linarith [abs_nonneg z.im]
  have den : 1 ≤ (1+|z.im|)^2 := by nlinarith [abs_nonneg z.im,sq_nonneg |z.im|]
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul,norm_mul]
  calc
    _ ≤ ‖mean χ‖ + (2*(1+|z.im|))*(3*(1+|z.im|))*C :=
      add_le_add le_rfl (mul_le_mul (mul_le_mul hz1 hz' (norm_nonneg _) (by positivity)) hI
        (norm_nonneg _) (by positivity))
    _ ≤ ‖mean χ‖ * (1+|z.im|)^2 + (2*(1+|z.im|))*(3*(1+|z.im|))*C :=
      add_le_add (le_mul_of_one_le_right (norm_nonneg _) den) le_rfl
    _ = _ := by ring

#print axioms primitive_fubini
#print axioms second_abel
#print axioms quadratic_growth_closed
#print axioms secondPrefix_periodic
#print axioms secondPrefix_bounded
end PintzJutilaSecondAbel
