import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PintzExceptionFinalReduction
import PintzPolePolynomialFloor
import PintzReducedArcEnergy
import PintzSection8LiteralModels
import PintzSignedSpecialPairs

open Finset Zeta23 Zeta23.ThmE
open PintzWeilPrimitivePrimeWindow PintzPrimitiveResidual
namespace PintzConditionalPoleOnly

/-- Explicit unproved hypotheses for the simplified pure-pole route. -/
def Gap : Prop :=
  (∀ z : ℂ, (7/8:ℝ) < z.re → riemannZeta z ≠ 0) ∧
  (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q →
    χ.IsPrimitive → ∀ z : ℂ, (7/8:ℝ) < z.re → χ.LFunction z ≠ 0)

theorem retainedModel_pole (hGap : Gap) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (N t : ℝ) :
    retainedModel (zeroConfig hp) q N (1/100) t = poleCoeff q*(t:ℂ) := by
  unfold retainedModel PintzResidualPartition.retained
  have He : PintzResidualPartition.near (trunc (zeroConfig hp) N)
      (fun i => (i:ℂ)) (1/100) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hre := (PintzResidualPartition.mem_near _ _ _ _ |>.mp hi).2
    have hr : (7/8:ℝ) < (i:ℂ).re := by linarith
    by_cases hq : q=1
    · have Hc : i.val ∈ zetaZeroConfig.carrier :=
        (congrArg (fun Z : ZeroConfig => i.val ∈ Z.carrier) (zeroConfig_eq_zeta hp hq)).mp i.2
      exact hGap.1 i hr Hc.1
    · have hq1 : 1 < q := Nat.lt_of_le_of_ne (NeZero.one_le) (Ne.symm hq)
      have Hc : i.val ∈ (LZeros (LSeam_of hq1 hp)).carrier :=
        (congrArg (fun Z : ZeroConfig => i.val ∈ Z.carrier) (zeroConfig_eq_LZeros hp hq1)).mp i.2
      exact hGap.2 q χ hq1 hp i hr Hc.1
  rw [He]
  simp [PintzResidualGallagher.zeroPrimitive]

theorem retained_pole (hGap : Gap) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (N a v η : ℝ) :
    PintzSection8LiteralModels.retained N a v (1/100) q χ η =
      poleCoeff q * (∑ n ∈ Ioc ⌊a⌋₊ ⌊v⌋₊, PintzPoleKernelTail.phase ((n:ℝ)*η)) := by
  rw [PintzSection8LiteralModels.retained_eq χ hp, mul_sum]
  apply sum_congr rfl
  intro n hn
  unfold PintzDiscreteZeroModel.increment
  rw [retainedModel_pole hGap hp, retainedModel_pole hGap hp]
  have hf : PintzPoleKernelTail.phase ((n:ℝ)*η) = Complex.exp ((2*Real.pi*η*Complex.I)*(n:ℝ)) := by
    unfold PintzPoleKernelTail.phase
    congr 1
    push_cast
    ring
  rw [hf]
  push_cast
  ring

theorem pole_slice (hGap : Gap) {q : ℕ} [NeZero q] (a₀ : ZMod q) (ha₀ : IsUnit a₀)
    (N a v η : ℝ) :
    PintzReducedArcEnergy.residue q (PintzSection8LiteralModels.retained N a v (1/100)) a₀ η =
      ((ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ)) *
        (∑ n ∈ Ioc ⌊a⌋₊ ⌊v⌋₊, PintzPoleKernelTail.phase ((n:ℝ)*η)) := by
  classical
  unfold PintzReducedArcEnergy.residue
  let W := ∑ n ∈ Ioc ⌊a⌋₊ ⌊v⌋₊, PintzPoleKernelTail.phase ((n:ℝ)*η)
  have hS : (∑ χ : DirichletCharacter ℂ q, χ a₀ * gaussSum χ⁻¹ ZMod.stdAddChar *
      PintzSection8LiteralModels.retained N a v (1/100) χ.conductor χ.primitiveCharacter η) =
      (ArithmeticFunction.moebius q:ℂ)*W := by
    rw [sum_eq_single (1 : DirichletCharacter ℂ q)]
    · let χ₀ : DirichletCharacter ℂ q := 1
      let : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
      change χ₀ a₀ * gaussSum χ₀⁻¹ ZMod.stdAddChar *
        PintzSection8LiteralModels.retained N a v (1/100) χ₀.conductor χ₀.primitiveCharacter η = _
      rw [retained_pole hGap χ₀.primitiveCharacter χ₀.primitiveCharacter_isPrimitive,
        show χ₀ = 1 by rfl, MulChar.one_apply ha₀, inv_one,PintzSignedSpecialPairs.principal_std_moebius]
      have ho : (1 : DirichletCharacter ℂ q).conductor = 1 :=
        DirichletCharacter.eq_one_iff_conductor_eq_one.mp rfl
      simp [poleCoeff,ho,W]
    · intro χ hχ hχ₁
      let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      rw [retained_pole hGap χ.primitiveCharacter χ.primitiveCharacter_isPrimitive]
      have hq₁ : χ.conductor ≠ 1 := fun H => hχ₁ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr H)
      simp [poleCoeff,hq₁]
    · simp
  rw [hS]
  change _ = (ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ)*W
  ring

#print axioms retainedModel_pole
#print axioms pole_slice

open PintzMajorArcGeometry PintzPoleKernelTail MeasureTheory Set

theorem major_translated (N P : ℕ) (a : ℝ) (m : ℕ) (hN : 0 < N)
    (hSep : 2*(P:ℝ)^2 < N) :
    PintzExceptionFinalReduction.majorCoeff N P a m =
      ∑ i ∈ reduced P, ∫ x in -(radius P N i)..radius P N i,
        (PintzSection8LiteralModels.full a N (x+center i))^2*phase (-(m:ℝ)*(x+center i)) := by
  unfold PintzExceptionFinalReduction.majorCoeff PintzPrimePairCoefficient.majorSet
  let F := PintzPrimePairCoefficient.f (PintzExceptionFinalReduction.actualPrimes N a)
    (fun n => (Real.log n:ℂ)) m
  change (∫ t in ⋃ i ∈ reduced P, arc P N i, F t) = _
  rw [integral_biUnion_finset (reduced P)]
  · apply sum_congr rfl
    intro i hi
    have hr : 0 ≤ radius P N i := by unfold radius; positivity
    unfold arc
    rw [← intervalIntegral.integral_of_le (show center i - radius P N i ≤
      center i + radius P N i by linarith)]
    rw [show center i - radius P N i = -(radius P N i)+center i by ring,
      add_comm (center i) (radius P N i),← intervalIntegral.integral_comp_add_right]
    have he : PintzSection8LiteralModels.primes a (N:ℝ) = PintzExceptionFinalReduction.actualPrimes N a := by
      simp [PintzSection8LiteralModels.primes,PintzExceptionFinalReduction.actualPrimes]
    unfold F PintzPrimePairCoefficient.f PintzSection8LiteralModels.full
    rw [he]
  · intro i hi
    exact measurableSet_Ioc
  · intro i hi j hj hij
    exact arcs_disjoint hSep hi hj hij
  · intro i hi
    exact (PintzPrimePairCoefficient.continuous_f _ _ _).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

private theorem phase_kernel (a N : ℕ) (ha : a ≤ N) (t : ℝ) :
    (∑ n ∈ Finset.Ioc a N, phase ((n:ℝ)*t)) = kernel (a+1) (N-a) t := by
  unfold kernel
  rw [mul_sum]
  symm
  apply sum_bij (fun n _ => a+1+n)
  · intro n hn
    have ht := mem_range.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro n hn m hm HE
    omega
  · intro n hn
    obtain ⟨h₁,h₂⟩ := Finset.mem_Ioc.mp hn
    exact ⟨n-a-1,mem_range.mpr (by omega),by omega⟩
  · intro n hn
    simp only [phase_nat_mul,pow_add]

theorem retained_translated_eq_pole (hGap : Gap) (N P : ℕ) (a : ℝ) (m : ℕ)
    (ha : ⌊a⌋₊ ≤ N) :
    (∑ i ∈ reduced P, ∫ x in -(radius P N i)..radius P N i,
      (PintzReducedArcEnergy.slice (PintzSection8LiteralModels.retained N a N (1/100)) i x)^2*
        phase (-(m:ℝ)*(x+center i))) =
      weightedPole P N (⌊a⌋₊+1) (N-⌊a⌋₊) m := by
  classical
  let L := ⌊a⌋₊+1
  let K := N-⌊a⌋₊
  have H (i : ℕ×ℕ) (hi : i ∈ reduced P) (t : ℝ) :
      (PintzReducedArcEnergy.slice (PintzSection8LiteralModels.retained N a N (1/100)) i t)^2*
        phase (-(m:ℝ)*(t+center i)) =
        (PintzPoleKernelTail.weight i.1*phase (-(m:ℝ)*(i.2:ℝ)/(i.1:ℝ)))*poleIntegrand L K m t := by
    obtain ⟨hi0,_,_,hc⟩ := mem_reduced.mp hi
    let : NeZero i.1 := ⟨hi0.ne'⟩
    rw [PintzReducedArcEnergy.slice, dite_eq_right hi0.ne',
      pole_slice hGap _ ((ZMod.isUnit_iff_coprime _ _).mpr hc)]
    simp only [Nat.floor_natCast]
    rw [phase_kernel _ _ ha]
    unfold poleIntegrand
    rw [show -(m:ℝ)*(t+center i) = -(m:ℝ)*t + (-(m:ℝ)*(i.2:ℝ)/(i.1:ℝ)) by unfold PintzMajorArcGeometry.center; ring,
      phase_add, mul_pow, div_pow]
    unfold PintzPoleKernelTail.weight
    ring
  calc
    _ = ∑ i ∈ reduced P, (PintzPoleKernelTail.weight i.1*phase (-(m:ℝ)*(i.2:ℝ)/(i.1:ℝ))) *
      ∫ x in -(radius P N i)..radius P N i, poleIntegrand L K m x := by
      apply sum_congr rfl
      intro i hi
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun t _ => H i hi t)
    _ = _ := by
      have HE := sum_reduced P (fun q a => (PintzPoleKernelTail.weight q*phase (-(m:ℝ)*(a:ℝ)/(q:ℝ))) *
        ∫ x in -(radius P N (q,a))..radius P N (q,a), poleIntegrand L K m x)
      rw [HE]
      unfold weightedPole
      apply sum_congr rfl
      intro q hq
      unfold ramanujan radius
      simp only [neg_div, mul_sum, sum_mul]
      rfl

#print axioms major_translated
#print axioms retained_translated_eq_pole

open Filter ExceptionUnionBridge

private theorem pow_unbounded {u : ℝ} (hu : 0 < u) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K ≤ (n:ℝ)^u :=
  ((tendsto_rpow_atTop hu).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)).eventually_ge_atTop K

private theorem absorb_error (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, C*(n:ℝ)^(1-1/8200:ℝ)*(1+Real.log (n:ℝ))^2 ≤ (n:ℝ)/16 := by
  let u : ℝ := 1/16400
  have hu : 0 < u := by norm_num [u]
  have H₀ : ∀ᶠ x : ℝ in atTop, ‖(Real.log x)^(2:ℝ)‖ ≤ 1*‖x^u‖ :=
    (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s := u) hu).bound (by norm_num : (0:ℝ)<1)
  have H := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually H₀
  have Hl := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  filter_upwards [H,Hl.eventually_ge_atTop (1:ℝ),pow_unbounded hu (64*C),
    eventually_ge_atTop (2:ℕ)] with n H hlog H' hn
  change 1 ≤ Real.log (n:ℝ) at hlog
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hL : (Real.log (n:ℝ))^2 ≤ (n:ℝ)^u := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0.le u),
      abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ Real.log (n:ℝ) by linarith) (2:ℝ)),
      Real.rpow_ofNat] using H
  have hp : (1+Real.log (n:ℝ))^2 ≤ 4*((n:ℝ)^u) := by
    have H := pow_le_pow_left₀ (show 0 ≤ 1+Real.log (n:ℝ) by linarith)
      (show 1+Real.log (n:ℝ) ≤ 2*Real.log (n:ℝ) by linarith) 2
    nlinarith
  calc
    _ ≤ C*(n:ℝ)^(1-1/8200:ℝ)*(4*((n:ℝ)^u)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 4*C*(n:ℝ)^(1-u) := by
      rw [show (1-1/8200:ℝ)=1-u-u by norm_num [u]]
      rw [show C*(n:ℝ)^(1-u-u)*(4*(n:ℝ)^u) = 4*C*((n:ℝ)^(1-u-u)*(n:ℝ)^u) by ring]
      rw [← Real.rpow_add hn0,sub_add_cancel]
    _ = ((4*C)*(n:ℝ))/((n:ℝ)^u) := by rw [Real.rpow_sub hn0,Real.rpow_one,mul_div_assoc]
    _ ≤ _ := (div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)).2 (by
      have HH := mul_le_mul_of_nonneg_left H' hn0.le
      linarith)

private theorem target_small : ∀ᶠ n : ℕ in atTop, (n:ℝ)^(1-1/1000:ℝ) ≤ (n:ℝ)/16 := by
  filter_upwards [pow_unbounded (show (0:ℝ)<1/1000 by norm_num) 16,
    eventually_ge_atTop (2:ℕ)] with n h hh
  have hn : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  rw [Real.rpow_sub hn,Real.rpow_one]
  exact div_le_div_of_nonneg_left hn.le (by norm_num) h

private theorem sep {n P : ℕ} (hn : (4:ℝ) ≤ n)
    (hP : (P:ℝ) ≤ (n:ℝ)^(21/100:ℝ)) : 2*(P:ℝ)^2 < n := by
  have hn0 : (0:ℝ) < n := by linarith
  have hn1 : (1:ℝ) ≤ n := by linarith
  have hN : (2:ℝ) ≤ (n:ℝ)^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) hn0.le]
    linarith
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) P) hP 2
  rw [← Real.rpow_mul_natCast hn0.le] at hp
  norm_num at hp
  calc
    _ ≤ 2*(n:ℝ)^(21/50:ℝ) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ (n:ℝ)^(1/2:ℝ)*(n:ℝ)^(21/50:ℝ) := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = (n:ℝ)^(23/25:ℝ) := by rw [← Real.rpow_add hn0]; norm_num
    _ < _ := by
      simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt (show (1:ℝ)<n by linarith)
        (by norm_num : (23/25:ℝ)<1)

theorem conditional_major_lower (hGap : Gap) :
    ∀ᶠ j : ℕ in atTop,
      let N : ℕ := 2^(j+1)
      ∃ (P : ℕ) (a : ℝ), 1 ≤ P ∧ (P:ℝ) ≤ (N:ℝ)^(21/100:ℝ) ∧
        (N:ℝ)^(41/200:ℝ) ≤ 2*(P:ℝ) ∧ a ≤ (N:ℝ) ∧
        ∀ m ∈ dyadicBad j, (N:ℝ)^(1-1/1000:ℝ) ≤
          (PintzExceptionFinalReduction.majorCoeff N P a m).re := by
  obtain ⟨C,hC,Hsec⟩ := PintzSection8Coefficient.coefficient_eventual
    (show (0:ℝ)<1/100 by norm_num) (show (1/100:ℝ)≤1/2 by norm_num)
  have hPows : Tendsto (fun j : ℕ => 2^(j+1)) atTop atTop := by
    exact tendsto_atTop_mono (fun j => Nat.pow_le_pow_right (by decide) (by omega))
      (tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2:ℕ) by decide))
  filter_upwards [hPows.eventually Hsec,
    hPows.eventually (PintzPolePolynomialFloor.polynomial_pole_floor (θ := 1/5) (by norm_num)),
    hPows.eventually (absorb_error C hC), hPows.eventually target_small,
    hPows.eventually (pow_unbounded (show (0:ℝ)<1/100 by norm_num) 2),
    hPows.eventually (pow_unbounded (show (0:ℝ)<79/100 by norm_num) 12),
    hPows.eventually (eventually_ge_atTop (48:ℕ))] with j H F hE hT hpower hA hN
  let N : ℕ := 2^(j+1)
  let p : ℝ := (N:ℝ)^(21/100:ℝ)
  let P : ℕ := ⌊p⌋₊
  let a : ℝ := (N:ℝ)/12
  have hN48 : (48:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hNp : N > 0 := by exact_mod_cast hN0
  have hp : 0 ≤ p := by positivity
  have hpN : p ≤ (N:ℝ) := by
    simpa only [p,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
      (show (21/100:ℝ)≤1 by norm_num)
  have hp2 : 2 ≤ p := by
    refine hpower.trans ?_
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1/100:ℝ)≤21/100)
  have hPcut : (P:ℝ) ≤ p := Nat.floor_le hp
  have hPlt : p < (P:ℝ)+1 := Nat.lt_floor_add_one p
  have hP2 : 2 ≤ P := Nat.le_floor (by exact_mod_cast hp2)
  have hPlow : p ≤ 2*(P:ℝ) := by linarith
  have hLow : (N:ℝ)^(41/200:ℝ) ≤ 2*(P:ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (41/200:ℝ)≤21/100)).trans hPlow
  have hPθ : (N:ℝ)^(1/5:ℝ) ≤ P := by
    have hc : 2*(N:ℝ)^(1/5:ℝ) ≤ p := by
      unfold p
      rw [show (21/100:ℝ)=1/100+1/5 by norm_num,Real.rpow_add hN0]
      exact mul_le_mul_of_nonneg_right hpower (by positivity)
    linarith
  have hpa : p ≤ a := by
    change p ≤ (N:ℝ)/12
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<12)).2
    have h1 : (N:ℝ)^(79/100:ℝ)*p = (N:ℝ) := by
      unfold p
      rw [← Real.rpow_add hN0,show (79/100:ℝ)+21/100=1 by norm_num,Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_right hA hp]
  have hpa' : (P:ℝ) ≤ a := hPcut.trans hpa
  have ha2 : 2 ≤ a := by dsimp [a]; linarith
  have haN : a ≤ N := by dsimp [a]; linarith
  have hP1 : 1 ≤ P := by omega
  have hP_N : 2*P ≤ N := by
    have H : 2*(P:ℝ) ≤ N := by dsimp [a] at hpa'; linarith
    exact_mod_cast H
  let L := ⌊a⌋₊+1
  let Len := N-⌊a⌋₊
  have hFloor : (⌊a⌋₊:ℝ) ≤ a := Nat.floor_le (by linarith)
  have hflN : ⌊a⌋₊ ≤ N := by exact_mod_cast hFloor.trans haN
  have hSep := sep (show (4:ℝ)≤N by linarith) (show (P:ℝ)≤(N:ℝ)^(21/100:ℝ) from hPcut)
  refine ⟨P,a,hP1,hPcut,hLow,haN,?_⟩
  intro m hm
  obtain ⟨hmI,hm4,hmEven,hmFail⟩ := Finset.mem_filter.mp hm
  obtain ⟨hml,hmN⟩ := Finset.mem_Ico.mp hmI
  change m < N at hmN
  have hmHalf : (N:ℝ)/2 ≤ m := by
    have H : (N:ℝ) ≤ 2*(m:ℝ) := by
      exact_mod_cast (show N ≤ 2*m by dsimp [N]; rw [pow_succ,mul_comm]; omega)
    linarith
  have hLm : 2*L ≤ m := by
    have Hr : 2*(L:ℝ) ≤ m := by
      unfold L
      push_cast
      dsimp [a] at hFloor
      linarith
    exact_mod_cast Hr
  have hKN : m-2*L < Len := by dsimp [Len,L] at *; omega
  have hk : N ≤ 4*(m-2*L+1) := by
    have Hr : (N:ℝ) ≤ 4*((m:ℝ)-2*(L:ℝ)+1) := by
      unfold L
      push_cast
      dsimp [a] at hFloor
      linarith
    have Hr' : (N:ℝ) ≤ 4*((m-2*L+1:ℕ):ℝ) := by
      rw [Nat.cast_add,Nat.cast_sub hLm,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      exact Hr
    exact_mod_cast Hr'
  have hFloorPole := F P L Len m hP2 hP_N hPθ (by omega) hmN.le hmEven hLm hKN hk
  let B (i : ℕ×ℕ) (u : ℝ) := phase (-(m:ℝ)*(u+PintzMajorArcGeometry.center i))
  have Hbound := H P a N hP1 hPcut hpa' ha2 haN le_rfl B
    (fun i _ => by unfold B phase; fun_prop) (fun i _ u => by unfold B; rw [norm_phase])
  change ‖(∑ i ∈ reduced P, ∫ x in -(radius P N i)..radius P N i,
    (PintzSection8LiteralModels.full a N (x+PintzMajorArcGeometry.center i))^2*
        phase (-(m:ℝ)*(x+PintzMajorArcGeometry.center i))) -
      (∑ i ∈ reduced P, ∫ x in -(radius P N i)..radius P N i,
       (PintzReducedArcEnergy.slice (PintzSection8LiteralModels.retained N a N (1/100)) i x)^2*
        phase (-(m:ℝ)*(x+PintzMajorArcGeometry.center i)))‖ ≤ _ at Hbound
  rw [← major_translated N P a m hNp hSep,
    retained_translated_eq_pole hGap N P a m hflN] at Hbound
  have Herr : ‖PintzExceptionFinalReduction.majorCoeff N P a m - weightedPole P N L Len m‖ ≤
      (N:ℝ)/16 := Hbound.trans (by norm_num [N] at hE ⊢; exact hE)
  have Hre := (Complex.abs_re_le_norm _).trans Herr
  rw [Complex.sub_re] at Hre
  have hh := (abs_le.mp Hre).1
  linarith [hFloorPole,hT]

theorem conditional_exception_union (hGap : Gap) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (fails X).card^5 ≤ X^4 :=
  PintzExceptionFinalReduction.from_major_lower (conditional_major_lower hGap)

#print axioms conditional_exception_union
end PintzConditionalPoleOnly
