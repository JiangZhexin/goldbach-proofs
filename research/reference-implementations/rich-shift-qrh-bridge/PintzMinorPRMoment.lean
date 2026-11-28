import PintzMinorPRFoundationAudit
import PintzMinorArcTransport
import PintzMajorArcPrimeEnergy
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/- Narrow transfer of the exact Vaughan prefix theorem and masked Bessel
from workbench PR #3782 (commit 66b7bb6) and its upstream Estermann file.
Only the minor-arc theorem is used, not any of the PR's major-arc inputs. -/
open Finset Filter MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped BigOperators Topology
noncomputable section
namespace PintzMinorPRMoment
def primeLog (k : ℕ) := if k.Prime then Real.log (k:ℝ) else 0
def wave (z : ℝ) := Complex.exp (((2*Real.pi*z : ℝ) : ℂ)*Complex.I)
def series (n : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ range (n+1), (u k : ℂ)*wave ((k : ℝ)*t)
def tailWeight (Y k : ℕ) := if Y < k then primeLog k else 0
abbrev arcs := PintzMinorArcTransport.published
def coeff (n Y m : ℕ) (A : Set ℝ) := intervalIntegral (A.indicator
  (fun t => (series n (tailWeight Y) t)^2 * wave (-(m : ℝ)*t))) 0 1 volume

private theorem vaughan_denominator_terms {x q P T : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hP : 0 < P) (hTsize : T ≤ Real.sqrt P) (hlow : P ≤ q) (hhigh : q ≤ x/P) :
    x / Real.sqrt q ≤ x/T ∧ Real.sqrt (x*q) ≤ x/T := by
  have hq := hP.trans_le hlow
  have hT2 : T^2 ≤ P := (Real.le_sqrt (by positivity) hP.le).mp hTsize
  constructor
  · exact div_le_div_of_nonneg_left hx.le hT (hTsize.trans (Real.sqrt_le_sqrt hlow))
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hprod := (le_div_iff₀ hP).mp hhigh
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT2 hq.le) hx.le,
      mul_le_mul_of_nonneg_left hprod hx.le]

private theorem minor_approximant (Q n : ℕ) (t : ℝ) (hQ : 1 ≤ Q) (hQn : Q ≤ n)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hminor : t ∉ {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ (Q:ℝ)/(q*n)}) :
    ∃ q a : ℕ, Q < q ∧ q ≤ n / Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ 1 / ((q:ℝ)*((n/Q : ℕ)+1 : ℝ)) := by
  let B := n / Q
  have hB : 0 < B := Nat.div_pos hQn hQ
  obtain ⟨s,hs,hd⟩ := Real.exists_rat_abs_sub_le_and_den_le t hB
  have hdpos : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hQB : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Rat.cast_def, mul_comm ((B : ℝ) + 1) (s.den : ℝ)] at hs
  have hclose : |t * s.den - s.num| < 1 := by
    have h := (mul_le_mul_of_nonneg_right hs hdpos.le)
    rw [← abs_of_pos hdpos, ← abs_mul, abs_of_pos hdpos] at h
    rw [sub_mul, div_mul_cancel₀ _ hdpos.ne'] at h
    refine h.trans_lt ?_
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hl,hu⟩ := abs_lt.mp hclose
  have ht0 : 0 ≤ t * s.den := mul_nonneg ht.1 hdpos.le
  have ht1 : t * s.den ≤ s.den := by simpa using mul_le_mul_of_nonneg_right ht.2 hdpos.le
  have hnlo : (-1 : ℤ) < s.num := by exact_mod_cast (show (-1 : ℝ) < s.num by linarith)
  have hnhi : s.num < (s.den : ℤ) + 1 := by exact_mod_cast (show (s.num : ℝ) < s.den + 1 by linarith)
  have hcast : (s.num.natAbs : ℤ) = s.num := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
  have hcast' : (s.num.natAbs : ℝ) = s.num := by
    calc (s.num.natAbs : ℝ) = ((s.num.natAbs : ℤ) : ℝ) := by simp
         _ = _ := congrArg (fun z : ℤ => (z : ℝ)) hcast
  have hle : s.num.natAbs ≤ s.den := by exact_mod_cast (show (s.num.natAbs : ℤ) ≤ s.den by omega)
  rw [← hcast'] at hs
  refine ⟨s.den, s.num.natAbs, ?_, hd, hle, s.reduced, hs⟩
  by_contra! hsmall
  apply hminor
  refine ⟨s.den, s.num.natAbs, s.pos, hsmall, hle, s.reduced, hs.trans ?_⟩
  have hbound : (n : ℝ) < Q * ((B : ℝ) + 1) := by exact_mod_cast Nat.lt_mul_div_succ n hQ
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hbound.le hdpos.le]

private theorem mangoldt_pointwise_bridge (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let e := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
    ‖∑ k ∈ Finset.range (n+1), ((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ ≤
      2 * Real.sqrt n * Real.log n := by
  intro w e
  have hnon (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k - w k := by
    by_cases hk : k.Prime <;> simp [w,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k) := by
      simp only [norm_mul,e,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hnon _)]
    _ = Chebyshev.psi n - Chebyshev.theta n := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simp [Chebyshev.psi,Chebyshev.theta,w,Finset.sum_filter,Finset.sum_sub_distrib]
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)

private theorem prime_mass (Y : ℕ) (t : ℝ) :
    ‖series Y primeLog t‖ ≤ 2*(Y : ℝ) := by
  have hnon (k : ℕ) : |primeLog k| = primeLog k := abs_of_nonneg (by
    by_cases hk : k.Prime <;> simp [primeLog,hk,Real.log_natCast_nonneg])
  have h4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num1
    linarith [Real.log_two_lt_d9]
  calc
  _ ≤ ∑ k ∈ range (Y+1), ‖(primeLog k : ℂ)*wave ((k : ℝ)*t)‖ := norm_sum_le _ _
  _ = Chebyshev.theta Y := by
    simp only [wave, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hnon]
    unfold primeLog
    rw [← Finset.sum_filter, Chebyshev.theta_eq_sum_primesLE_log]
    congr 1
  _ ≤ _ := (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Y)).trans
    (mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg Y))

private theorem prime_approx (Y q : ℕ) (t : ℝ) (hY : 1 ≤ Y)
    (h : ‖OAI.Problem337.Vaughan.weightedSum (Ioc 0 Y)
      (fun k => OAI.Problem337.VaughanBilinear.phase (t*k)) ArithmeticFunction.vonMangoldt‖ ≤
      16200*(Real.log Y)^4*OAI.Problem337.Vaughan.approximationEnvelope Y q) :
    ‖series Y primeLog t‖ ≤ 16200*(Real.log Y)^4*OAI.Problem337.Vaughan.approximationEnvelope Y q
      + 2*Real.sqrt Y*Real.log Y := by
  have heq : series Y ArithmeticFunction.vonMangoldt t =
      OAI.Problem337.Vaughan.weightedSum (Ioc 0 Y)
        (fun k => OAI.Problem337.VaughanBilinear.phase (t*k)) ArithmeticFunction.vonMangoldt := by
    dsimp [series,wave,OAI.Problem337.Vaughan.weightedSum,OAI.Problem337.VaughanBilinear.phase]
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le Y)]
    simp only [ArithmeticFunction.map_zero,Complex.ofReal_zero,zero_mul,zero_add,Real.fourierChar_apply]
    apply Finset.sum_congr rfl
    intro k _; rw [mul_comm t (k : ℝ)]
  have herr : ‖series Y ArithmeticFunction.vonMangoldt t-series Y primeLog t‖ ≤
      2*Real.sqrt Y*Real.log Y := by
    simpa only [series, wave, primeLog, ← sum_sub_distrib, ← sub_mul,
      ← Complex.ofReal_sub] using mangoldt_pointwise_bridge Y hY t
  have htr := norm_sub_le (series Y ArithmeticFunction.vonMangoldt t)
    (series Y ArithmeticFunction.vonMangoldt t-series Y primeLog t)
  rw [sub_sub_cancel] at htr
  exact htr.trans (add_le_add (heq ▸ h) herr)

def scale (n P : ℕ) : ℝ := (n : ℝ)/Real.sqrt P+(n : ℝ)^(4/5 : ℝ)

/-- One reduced approximation controls all prefix lengths, including those
shorter than its denominator. This permits the lower cutoff in Pintz's sum. -/
theorem prefix_bound : ∀ᶠ n : ℕ in atTop, ∀ P : ℕ, 1 ≤ P → P ≤ n →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ arcs n P → ∀ Y ≤ n,
    ‖series Y primeLog t‖ ≤ 50000*(Real.log n)^4*scale n P := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 OAI.Problem337.Vaughan.eventually_vonMangoldt_sum_log_bound
  have ht := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [eventually_ge_atTop ((max N 1)^2),
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1] with n hn hL
  intro P hP hPn t ht' hminor Y hYn
  have hpr : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsr : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.2 hpr
  have hs1 : 1 ≤ Real.sqrt (P : ℝ) := (Real.le_sqrt (by norm_num) hpr.le).2 (by exact_mod_cast hP)
  have hsP : Real.sqrt (P : ℝ) ≤ P := by
    nlinarith only [Real.sq_sqrt hpr.le, mul_nonneg (sub_nonneg.mpr hs1) hsr.le]
  have hns := Real.sqrt_le_sqrt (by exact_mod_cast hPn : (P : ℝ) ≤ n)
  have hroot : Real.sqrt (n : ℝ) ≤ (n : ℝ)/Real.sqrt P := by
    apply (le_div_iff₀ hsr).2
    exact (mul_le_mul_of_nonneg_left hns (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hnr.le)
  have hNn : (N : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (Nat.cast_nonneg N) hnr.le).2
    exact_mod_cast (Nat.pow_le_pow_left (le_max_left N 1) 2).trans hn
  obtain ⟨q,a,hPq,hqB,_,hcop,happ⟩ := minor_approximant P n t hP hPn ht' hminor
  have hq : 0 < q := by omega
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hhigh : (q : ℝ) ≤ (n : ℝ)/P := (le_div_iff₀ hpr).2
    (by exact_mod_cast (Nat.le_div_iff_mul_le hP).1 hqB)
  have hcut : (n : ℝ)/Real.sqrt P ≤ scale n P := le_add_of_nonneg_right (Real.rpow_nonneg hnr.le _)
  have hB := div_le_div_of_nonneg_left hnr.le hsr hsP
  have hscale : 0 ≤ scale n P := by dsimp [scale]; positivity
  have hL' : 1 ≤ Real.log (n : ℝ) := hL
  have hl4 : 1 ≤ (Real.log n)^4 := one_le_pow₀ hL'
  by_cases hsmall : Y ≤ q ∨ Y ≤ N
  · have hY : (Y : ℝ) ≤ scale n P := hsmall.elim
      (fun h => (Nat.cast_le.mpr h).trans (hhigh.trans (hB.trans hcut)))
      (fun h => (Nat.cast_le.mpr h).trans (hNn.trans (hroot.trans hcut)))
    exact (prime_mass Y t).trans ((mul_le_mul_of_nonneg_left hY (by norm_num)).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hl4]) hscale))
  push Not at hsmall
  have happrox : |t-(a:ℝ)/q| ≤ 1/(q:ℝ)^2 := by
    apply happ.trans
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ_of_le hqB) hqr.le
  have hval := hN Y hsmall.2.le t (a:ℤ) q hq hcop.isCoprime (by simpa using happrox) hsmall.1.le
  have hYp : 0 < Y := by omega
  have hYr : (0 : ℝ) < Y := Nat.cast_pos.mpr hYp
  have hYn' : (Y : ℝ) ≤ n := by exact_mod_cast hYn
  obtain ⟨hu,hv⟩ := vaughan_denominator_terms hnr hsr hpr le_rfl (by exact_mod_cast hPq.le) hhigh
  have hen : OAI.Problem337.Vaughan.approximationEnvelope Y q ≤ 2*scale n P := by
    dsimp [OAI.Problem337.Vaughan.approximationEnvelope,scale]
    have h₁ := (div_le_div_of_nonneg_right hYn' (Real.sqrt_nonneg _)).trans hu
    have h₂ := Real.rpow_le_rpow hYr.le hYn' (by norm_num : (0 : ℝ) ≤ 4/5)
    have h₃ := (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hYn' hqr.le)).trans hv
    linarith only [h₁,h₂,h₃,Real.rpow_nonneg hnr.le (4/5)]
  have hlY := Real.log_le_log hYr hYn'
  have hlog4 := pow_le_pow_left₀ (Real.log_natCast_nonneg Y) hlY 4
  have ham := mul_le_mul (mul_le_mul_of_nonneg_left hlog4 (by norm_num : (0:ℝ)≤16200))
    hen (OAI.Problem337.Vaughan.approximationEnvelope_nonneg _ _ hYr.le) (by positivity)
  have hlogpow : Real.log (n : ℝ) ≤ (Real.log n)^4 := by
    simpa using pow_le_pow_right₀ hL' (by decide : 1 ≤ 4)
  have hres := mul_le_mul (mul_le_mul_of_nonneg_left
    ((Real.sqrt_le_sqrt hYn').trans (hroot.trans hcut)) (by norm_num : (0:ℝ)≤2))
    (hlY.trans hlogpow) (Real.log_natCast_nonneg Y) (by positivity)
  apply (prime_approx Y q t hYp hval).trans
  nlinarith only [add_le_add ham hres, mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) 4) hscale]

private theorem tail_series (n Y : ℕ) (hYn : Y ≤ n) (t : ℝ) :
    series n (tailWeight Y) t = series n primeLog t-series Y primeLog t := by
  classical
  let f (k : ℕ) := (primeLog k : ℂ)*wave ((k : ℝ)*t)
  have hfilters : (range (n+1)).filter (fun k => ¬ Y < k) = range (Y+1) := by
    ext k
    simp only [mem_filter,mem_range,not_lt]
    omega
  have hs := sum_filter_add_sum_filter_not (range (n+1)) (fun k => Y < k) f
  rw [hfilters] at hs
  have ht : series n (tailWeight Y) t = ∑ k ∈ (range (n+1)).filter (fun k => Y < k), f k := by
    rw [sum_filter]
    unfold series
    apply sum_congr rfl
    intro k _
    by_cases h : Y < k <;> simp [f,tailWeight,h]
  exact (eq_sub_iff_add_eq).2 (by rw [ht]; exact hs)

private theorem scale_sq_le {n P : ℕ} (hn : 0 < (n : ℝ)) (hP : 0 < (P : ℝ)) :
    (scale n P)^2 ≤ 2*((n : ℝ)*((n : ℝ)/P+(n : ℝ)^(3/5 : ℝ))) := by
  let u := (n : ℝ)/Real.sqrt P
  let v := (n : ℝ)^(4/5 : ℝ)
  have hu : u^2 = (n : ℝ)*((n : ℝ)/P) := by
    dsimp [u]; rw [div_pow,Real.sq_sqrt hP.le]; ring
  have hv : v^2 = (n : ℝ)*(n : ℝ)^(3/5 : ℝ) := by
    dsimp [v]; rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_one_add' hn.le (by norm_num)]
    norm_num
  change (u+v)^2 ≤ _
  calc (u+v)^2 ≤ 2*(u^2+v^2) := by nlinarith only [sq_nonneg (u-v)]
       _ = _ := by rw [hu,hv]; ring

private theorem maskedBessel :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (X : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (X+1), (u k : ℂ) * E ((k : ℝ)*t); ∀ (X M : ℕ) (u : ℕ → ℝ) (A : Set ℝ), MeasurableSet A → (∑ m ∈ Finset.range M, ‖intervalIntegral (A.indicator (fun t => (S X u t)^2 * E (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume‖^2) ≤ intervalIntegral (A.indicator (fun t => ‖S X u t‖^4)) (0 : ℝ) 1 MeasureTheory.volume := by
  intro E S X M u A hA
  let f := A.indicator (fun t => (S X u t)^2)
  let μ := volume.restrict (Set.Ioc (0:ℝ) 1)
  have hc : Continuous (fun t => (S X u t)^2) := by dsimp [S,E]; fun_prop
  have hmem : MemLp f 2 μ := by
    apply MemLp.indicator hA.nullMeasurableSet
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
    exact ((hc.norm.pow 2).intervalIntegrable (μ := volume) 0 1).1
  have hcoeff (m : ℕ) : fourierCoeffOn zero_lt_one f (m:ℤ) =
      ∫ t in (0:ℝ)..1, A.indicator (fun t => (S X u t)^2 * E (-(m:ℝ)*t)) t := by
    rw [fourierCoeffOn_eq_integral, sub_zero, one_div_one, one_smul]
    apply intervalIntegral.integral_congr
    intro t _
    by_cases h : t ∈ A
    · simp only [f, Set.indicator_of_mem h, smul_eq_mul, fourier_coe_apply]
      rw [mul_comm]
      congr 2
      dsimp [E]
      push_cast
      ring
    · simp [f,h]
  let s : Finset ℤ := (Finset.range M).map ⟨Int.ofNat, fun _ _ h => Int.ofNat_inj.mp h⟩
  have hParse := hasSum_sq_fourierCoeffOn zero_lt_one hmem
  have hbound := sum_le_hasSum s (fun i _ => sq_nonneg ‖fourierCoeffOn zero_lt_one f i‖) hParse
  have hpoint (t : ℝ) : ‖f t‖^2 = A.indicator (fun t => ‖S X u t‖ ^ 4) t := by
    by_cases ht : t ∈ A
    · simp only [f,Set.indicator_of_mem ht,norm_pow]; ring
    · simp [f, ht]
  simp only [s, Finset.sum_map, sub_zero, inv_one, one_smul, hpoint] at hbound
  change (∑ m ∈ Finset.range M, ‖fourierCoeffOn zero_lt_one f (m : ℤ)‖^2) ≤ _ at hbound
  simp_rw [hcoeff] at hbound
  exact hbound


private theorem published_energy_bound :
    ∀ᶠ N : ℕ in atTop, ∀ P Y M : ℕ, 1 ≤ P → P ≤ N → Y ≤ N →
      (∑ m ∈ range M, ‖coeff N Y m (arcs N P)ᶜ‖^2) ≤
        (4*100000^2:ℝ)*((N:ℝ)^3/P+(N:ℝ)^(13/5:ℝ))*(Real.log N)^10 := by
  classical
  filter_upwards [prefix_bound,eventually_ge_atTop (2:ℕ)] with N hsup hN
  intro P Y M hP hPN hYN
  let L := Real.log (N:ℝ)
  let U := 100000*L^4*scale N P
  have h0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hU : 0 ≤ U := by dsimp [U,scale]; positivity
  have hs : ∀ t ∈ Set.Icc (0:ℝ) 1, t ∉ arcs N P → ‖series N (tailWeight Y) t‖ ≤ U := by
    intro t ht ha
    rw [tail_series N Y hYN t]
    have H := hsup P hP hPN t ht ha
    exact (norm_sub_le _ _).trans ((add_le_add (H N le_rfl) (H Y hYN)).trans_eq (by dsimp [U,L]; ring))
  let F := series N (tailWeight Y)
  have hf : Continuous F := by
    change Continuous (fun t => ∑ k ∈ range (N+1), (tailWeight Y k : ℂ) *
      Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))
    fun_prop
  have hA : MeasurableSet (arcs N P) := PintzMinorArcTransport.published_meas N P
  have h4 : IntervalIntegrable ((arcs N P)ᶜ.indicator (fun t => ‖F t‖^4)) volume 0 1 :=
    ⟨((hf.norm.pow 4).intervalIntegrable _ _).1.indicator hA.compl,
      ((hf.norm.pow 4).intervalIntegrable _ _).2.indicator hA.compl⟩
  have hFour : (∑ m ∈ range M, ‖coeff N Y m (arcs N P)ᶜ‖^2) ≤
      U^2 * ∫ t in (0:ℝ)..1, ‖F t‖^2 := by
    refine (maskedBessel N M (tailWeight Y) (arcs N P)ᶜ hA.compl).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on zero_le_one h4
      ((continuous_const.mul (hf.norm.pow 2)).intervalIntegrable _ _)
    intro t ht
    by_cases hx : t ∈ (arcs N P)ᶜ
    · rw [Set.indicator_of_mem hx, show ‖F t‖^4 = ‖F t‖^2 * ‖F t‖^2 by ring]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hs t ht hx) 2) (sq_nonneg _)
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hF : F = PintzMajorArcPrimeEnergy.poly (range (N+1)) (fun n => (tailWeight Y n : ℂ)) := by
    funext t
    unfold F series PintzMajorArcPrimeEnergy.poly
    exact sum_congr rfl fun n _ => by
      congr 1
      unfold wave PintzPoleKernelTail.phase
      rw [mul_comm]
  have hParse : (∫ t in (0:ℝ)..1, ‖F t‖^2) = ∑ n ∈ range (N+1), ‖(tailWeight Y n : ℂ)‖^2 := by
    rw [hF]
    let f := fun t => ‖PintzMajorArcPrimeEnergy.poly (range (N+1)) (fun n => (tailWeight Y n : ℂ)) t‖^2
    have hp : Function.Periodic f 1 := fun t => by dsimp [f]; rw [PintzMajorArcPrimeEnergy.poly_periodic]
    have H := hp.intervalIntegral_add_eq 0 (-(1/2:ℝ))
    rw [zero_add, show -(1/2:ℝ)+1 = 1/2 by norm_num] at H
    exact H.trans (PintzMajorArcPrimeEnergy.parseval_centered _ _)
  have hMass : (∑ n ∈ range (N+1), ‖(tailWeight Y n : ℂ)‖^2) ≤ 2*(N:ℝ)*L^2 := by
    calc
      _ ≤ ∑ _ ∈ range (N+1), L^2 := by
        apply sum_le_sum
        intro n hn
        by_cases hp : n.Prime ∧ Y < n
        · rw [tailWeight, if_pos hp.2, primeLog, if_pos hp.1, Complex.norm_real,
            Real.norm_eq_abs, sq_abs]
          have hle : (n:ℝ) ≤ N := by exact_mod_cast (show n ≤ N from Nat.le_of_lt_succ (mem_range.mp hn))
          exact pow_le_pow_left₀ (Real.log_natCast_nonneg _) (Real.log_le_log (by exact_mod_cast hp.1.pos) hle) 2
        · by_cases H : Y < n
          · simp [tailWeight,H,primeLog,show ¬ n.Prime from fun hp' => hp ⟨hp',H⟩, sq_nonneg]
          · simp [tailWeight,H,sq_nonneg]
      _ = ((N:ℝ)+1)*L^2 := by simp [nsmul_eq_mul]
      _ ≤ _ := by
        have H : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hScale := scale_sq_le h0 (by exact_mod_cast (show 0 < P from hP))
  have hpow : (N:ℝ)^2*(N:ℝ)^(3/5:ℝ) = (N:ℝ)^(13/5:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add h0]
    norm_num
  rw [hParse] at hFour
  calc
    _ ≤ _ := hFour
    _ ≤ U^2 * (2*(N:ℝ)*L^2) := mul_le_mul_of_nonneg_left hMass (sq_nonneg _)
    _ = (2*100000^2:ℝ)*(N:ℝ)*(scale N P)^2*L^10 := by dsimp [U]; ring
    _ ≤ (2*100000^2:ℝ)*(N:ℝ)*(2*((N:ℝ)*((N:ℝ)/P+(N:ℝ)^(3/5:ℝ))))*L^10 := by gcongr
    _ = _ := by
      rw [show (2*100000^2:ℝ)*(N:ℝ)*(2*((N:ℝ)*((N:ℝ)/P+(N:ℝ)^(3/5:ℝ))))*L^10 =
        (4*100000^2:ℝ)*((N:ℝ)^3/P+(N:ℝ)^2*(N:ℝ)^(3/5:ℝ))*L^10 by ring, hpow]

def localCoeff (N P : ℕ) (a : ℝ) (m : ℕ) : ℂ :=
  ∫ t in (-(P:ℝ)/N)..(1-(P:ℝ)/N),
    (PintzMinorArcTransport.localUnion N P)ᶜ.indicator
      (fun t => (PintzMajorArcPrimeEnergy.poly ((Ioc ⌊a⌋₊ N).filter Nat.Prime)
        (fun n => (Real.log n : ℂ)) t)^2*wave (-(m:ℝ)*t)) t

private theorem series_eq_literal (N Y : ℕ) :
    series N (tailWeight Y) =
      PintzMajorArcPrimeEnergy.poly ((Ioc Y N).filter Nat.Prime) (fun n => (Real.log n : ℂ)) := by
  classical
  funext t
  have hs : ((Ioc Y N).filter Nat.Prime) = (range (N+1)).filter (fun n => Y<n ∧ n.Prime) := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_range]
    exact ⟨fun h => ⟨by omega, h.1.1, h.2⟩, fun h => ⟨⟨h.2.1, by omega⟩, h.2.2⟩⟩
  rw [PintzMajorArcPrimeEnergy.poly, hs, sum_filter]
  unfold series
  apply sum_congr rfl
  intro n hn
  by_cases h : Y < n <;> by_cases hp : n.Prime <;>
    simp only [tailWeight, h, hp, primeLog, true_and, false_and, ite_true, ite_false,
      Complex.ofReal_zero, zero_mul, and_false]
  unfold wave PintzPoleKernelTail.phase
  rw [show (((2*Real.pi*((n:ℝ)*t):ℝ):ℂ)*Complex.I) =
    Complex.I * ((2*Real.pi*((n:ℝ)*t):ℝ):ℂ) by ring]

/-- The PR's uniform Vaughan estimate controls the literal log-prime
polynomial on the complement of our exact half-open shifted-period arcs.
The sixth decimal choice of P is not part of the hypotheses. -/
theorem literal_energy :
    ∀ᶠ N : ℕ in atTop, ∀ P M : ℕ, ∀ a : ℝ,
      1 ≤ P → P ≤ N → ⌊a⌋₊ ≤ N → 2*(P:ℝ)^2 < (N:ℝ) →
      (∑ m ∈ range M, ‖localCoeff N P a m‖^2) ≤
        (4*100000^2:ℝ)*((N:ℝ)^3/P+(N:ℝ)^(13/5:ℝ))*(Real.log N)^10 := by
  filter_upwards [published_energy_bound] with N hN
  intro P M a hP hPN ha hcut
  have hEq (m : ℕ) : coeff N ⌊a⌋₊ m (arcs N P)ᶜ = localCoeff N P a m := by
    unfold coeff localCoeff
    rw [series_eq_literal]
    apply PintzMinorArcTransport.exact_minor_transport hP hcut
    unfold wave
    exact ((PintzMajorArcPrimeEnergy.poly_cont _ _).pow 2).mul (by fun_prop)
  simp_rw [← hEq]
  exact hN P ⌊a⌋₊ M hP hPN ha

theorem localCoeff_phase (N P : ℕ) (a : ℝ) (m : ℕ) :
    localCoeff N P a m =
      ∫ t in (-(P:ℝ)/N)..(1-(P:ℝ)/N),
        (PintzMinorArcTransport.localUnion N P)ᶜ.indicator
          (fun t => (PintzMajorArcPrimeEnergy.poly ((Ioc ⌊a⌋₊ N).filter Nat.Prime)
            (fun n => (Real.log n : ℂ)) t)^2*PintzPoleKernelTail.phase (-(m:ℝ)*t)) t := by
  have he (u : ℝ) : wave u = PintzPoleKernelTail.phase u := by
    unfold wave PintzPoleKernelTail.phase
    rw [mul_comm]
  simp only [localCoeff, he]

theorem literal_energy_finset :
    ∀ᶠ N : ℕ in atTop, ∀ P : ℕ, ∀ a : ℝ, ∀ D : Finset ℕ,
      1 ≤ P → P ≤ N → ⌊a⌋₊ ≤ N → 2*(P:ℝ)^2 < (N:ℝ) →
      (∑ m ∈ D, ‖localCoeff N P a m‖^2) ≤
        (4*100000^2:ℝ)*((N:ℝ)^3/P+(N:ℝ)^(13/5:ℝ))*(Real.log N)^10 := by
  filter_upwards [literal_energy] with N hN
  intro P a D hP hPN ha hcut
  let M := D.sup id + 1
  have hD : D ⊆ range M := fun i hi => mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := id) hi))
  exact (sum_le_sum_of_subset_of_nonneg hD (fun _ _ _ => sq_nonneg _)).trans (hN P M a hP hPN ha hcut)

#print axioms literal_energy_finset
#print axioms literal_energy
#print axioms prefix_bound
end PintzMinorPRMoment
