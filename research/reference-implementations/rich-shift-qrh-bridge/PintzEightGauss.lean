import PintzEightParseval
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/- Narrow port of Conjectures/Goldbach/B13BilateralVaughanReduction.lean:
   additive phase, Moebius induction, and induced Gauss support/norm (Pintz 4.2). -/
open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open scoped Classical
namespace PintzEightGauss
noncomputable section
def additivePhase (x : ℝ) : ℂ := circleMap 0 1 (2 * Real.pi * x)

theorem additivePhase_add (x y : ℝ) : additivePhase (x + y) = additivePhase x * additivePhase y := by
  dsimp [additivePhase]
  rw [circleMap_zero_mul, one_mul, mul_add]
theorem sum_natCast_range_eq_zmod {R : Type*} [AddCommMonoid R] {q : ℕ} [NeZero q] (f : ZMod q → R) :
    ∑ u ∈ range q, f (u : ZMod q) = ∑ z : ZMod q, f z := by
  apply sum_bij (s := range q) (t := (univ : Finset (ZMod q))) (fun u _ => (u : ZMod q))
  · simp
  · intro u uMember v vMember equal
    have valEqual := congrArg ZMod.val equal
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp uMember),
      Nat.mod_eq_of_lt (mem_range.mp vMember)] using valEqual
  · intro z _
    exact ⟨z.val, mem_range.mpr (ZMod.val_lt z), ZMod.natCast_zmod_val z⟩
  · intro u _; rfl
theorem sum_range_blocks {R : Type*} [AddCommMonoid R] (d f : ℕ) (F : ℕ → R) :
    ∑ x ∈ range (d * f), F x = ∑ j ∈ range f, ∑ a ∈ range d, F (d * j + a) := by
  induction f with
  | zero => simp
  | succ f ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

theorem stdAddChar_nat_fraction {q : ℕ} [NeZero q] (k : ℕ) :
    ZMod.stdAddChar (k : ZMod q) = additivePhase ((k : ℝ) / q) := by
  rw [← Int.cast_natCast k, ZMod.stdAddChar_coe]
  unfold additivePhase
  rw [circleMap_zero, Complex.ofReal_one, one_mul]
  push_cast
  congr 1
  ring

theorem stdAddChar_mul_nat_fraction {q : ℕ} [NeZero q] (k a : ℕ) :
    ZMod.stdAddChar ((k : ZMod q) * (a : ZMod q)) = additivePhase ((k : ℝ) * a / q) := by
  rw [← Nat.cast_mul, stdAddChar_nat_fraction, Nat.cast_mul]

set_option maxHeartbeats 600000 in
theorem sum_phase_fraction_eq_if_dvd {q : ℕ} [NeZero q] (k : ℕ) :
    (∑ a ∈ range q, additivePhase ((k : ℝ) * a / q)) = if q ∣ k then (q : ℂ) else 0 := by
  simp_rw [← stdAddChar_mul_nat_fraction]
  rw [sum_natCast_range_eq_zmod (fun z => ZMod.stdAddChar ((k : ZMod q) * z))]
  simp_rw [mul_comm (k : ZMod q)]
  rw [AddChar.sum_mulShift (k : ZMod q) (ZMod.isPrimitive_stdAddChar q), ZMod.card]
  have zeroIff : (k : ZMod q) = 0 ↔ q ∣ k := by rw [ZMod.natCast_eq_zero_iff]
  by_cases divides : q ∣ k
  · simp [divides, zeroIff.mpr divides]
  · have nonzero : (k : ZMod q) ≠ 0 := fun zero => divides (zeroIff.mp zero)
    simp [divides, nonzero]

theorem gaussSum_as_fraction_sum {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum χ (ZMod.stdAddChar.mulShift (k : ZMod d)) =
      ∑ a ∈ range d, χ (a : ZMod d) * additivePhase ((k : ℝ) * a / d) := by
  unfold gaussSum
  rw [← sum_natCast_range_eq_zmod]
  simp_rw [AddChar.mulShift_apply, stdAddChar_mul_nat_fraction]

set_option maxHeartbeats 600000 in
theorem lift_gaussSum {d f : ℕ} [NeZero d] [NeZero f]
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    (∑ u ∈ range (d * f), χ (u : ZMod d) * additivePhase ((k : ℝ) * u / ((d : ℝ) * f))) =
      if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
  have dNonzero : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have fNonzero : (f : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne f
  rw [sum_range_blocks, Finset.sum_comm]
  have liftEntry (a j : ℕ) :
      χ ((d * j + a : ℕ) : ZMod d) * additivePhase ((k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f)) =
        (χ (a : ZMod d) * additivePhase ((k : ℝ) * a / ((d : ℝ) * f))) *
          additivePhase ((k : ℝ) * j / f) := by
    have angle : (k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f) =
        (k : ℝ) * a / ((d : ℝ) * f) + (k : ℝ) * j / f := by
      push_cast
      field_simp
      ring
    rw [angle, additivePhase_add, ← mul_assoc]
    have same : ((d * j + a : ℕ) : ZMod d) = (a : ZMod d) := by push_cast; simp
    rw [same]
  simp_rw [liftEntry, ← mul_sum, sum_phase_fraction_eq_if_dvd]
  by_cases divisible : f ∣ k
  · simp only [if_pos divisible, ← Finset.sum_mul, gaussSum_as_fraction_sum]
    rw [mul_comm _ (f : ℂ)]
    apply congrArg (fun z : ℂ => (f : ℂ) * z)
    refine sum_congr rfl fun a _ => ?_
    have h : (k : ℝ) = ((k / f : ℕ) : ℝ) * f := by
      exact_mod_cast (Nat.div_mul_cancel divisible).symm
    have sameAngle : (k : ℝ) * a / ((d : ℝ) * f) = (((k / f : ℕ) : ℝ)) * a / d := by
      conv_lhs => rw [h]
      field_simp
    rw [sameAngle]
  · simp [divisible]

def moebiusComplex (m : ℕ) : ℂ := (μ m : ℂ)

theorem norm_moebiusComplex_le_one (m : ℕ) : ‖moebiusComplex m‖ ≤ 1 := by
  rw [moebiusComplex, Complex.norm_intCast]
  exact_mod_cast (abs_moebius_le_one (n := m))

theorem moebius_coprime_indicator {M : ℕ} (MPositive : 0 < M) (u : ℕ) :
    (∑ e ∈ M.divisors.filter (fun e => e ∣ u), moebiusComplex e) =
      if u.Coprime M then (1 : ℂ) else 0 := by
  let g := u.gcd M
  have gPositive : 0 < g := Nat.gcd_pos_of_pos_right u MPositive
  have divisorsEquality : M.divisors.filter (fun e => e ∣ u) = g.divisors := by
    ext e
    rw [mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨eDividesM, _⟩, eDividesU⟩
      exact ⟨Nat.dvd_gcd eDividesU eDividesM, gPositive.ne'⟩
    · rintro ⟨eDividesG, _⟩
      exact ⟨⟨eDividesG.trans (Nat.gcd_dvd_right u M), MPositive.ne'⟩,
        eDividesG.trans (Nat.gcd_dvd_left u M)⟩
  have convolution : (∑ e ∈ g.divisors, μ e) = (1 : ArithmeticFunction ℤ) g := by
    rw [← coe_mul_zeta_apply (f := μ), moebius_mul_coe_zeta]
  rw [divisorsEquality]
  simp_rw [moebiusComplex, ← Int.cast_sum, convolution]
  change (((1 : ArithmeticFunction ℤ) g : ℤ) : ℂ) = if g = 1 then (1 : ℂ) else 0
  by_cases one : g = 1
  · simp [one, one_apply]
  · simp [one, one_apply]

theorem changeLevel_nat_indicator {d M : ℕ} (dDivides : d ∣ M) (χ : DirichletCharacter ℂ d)
    (u : ℕ) : DirichletCharacter.changeLevel dDivides χ (u : ZMod M) =
      (if u.Coprime M then (1 : ℂ) else 0) * χ (u : ZMod d) := by
  by_cases coprime : u.Coprime M
  · rw [if_pos coprime, one_mul]
    have same := DirichletCharacter.changeLevel_eq_cast_of_dvd χ dDivides (ZMod.unitOfCoprime u coprime)
    rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast dDivides] at same
    exact same
  · rw [if_neg coprime, zero_mul]
    exact MulChar.map_nonunit _ (fun unit => coprime ((ZMod.isUnit_iff_coprime u M).mp unit))

theorem sum_filter_dvd_range {R : Type*} [AddCommMonoid R] {e M : ℕ}
    (ePositive : 0 < e) (eDivides : e ∣ M) (F : ℕ → R) :
    (∑ u ∈ (range M).filter (fun u => e ∣ u), F u) = ∑ v ∈ range (M / e), F (e * v) := by
  have quotient : e * (M / e) = M := Nat.mul_div_cancel' eDivides
  symm
  apply sum_bij (s := range (M / e)) (t := (range M).filter (fun u => e ∣ u)) (fun v _ => e * v)
  · intro v vMember
    refine mem_filter.mpr ⟨mem_range.mpr ?_, dvd_mul_right e v⟩
    rw [← quotient]
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp vMember) ePositive
  · intro v _ w _ eq
    exact Nat.eq_of_mul_eq_mul_left ePositive eq
  · intro u uMember
    obtain ⟨uRange, v, h⟩ := mem_filter.mp uMember
    refine ⟨v, mem_range.mpr ?_, h.symm⟩
    have prodLt : e * v < e * (M / e) := h ▸ quotient.symm ▸ mem_range.mp uRange
    exact Nat.lt_of_mul_lt_mul_left prodLt
  · intro v _
    rfl

theorem sum_inducedGauss_moebius {d M : ℕ} [NeZero M] (dDivides : d ∣ M)
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M)) =
      ∑ e ∈ M.divisors, moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) * additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) := by
  rw [gaussSum_as_fraction_sum]
  calc
    _ = ∑ u ∈ range M, ∑ e ∈ M.divisors.filter (fun e => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      refine sum_congr rfl fun u _ => ?_
      rw [changeLevel_nat_indicator, ← moebius_coprime_indicator (NeZero.pos M), mul_assoc, sum_mul]
    _ = ∑ e ∈ M.divisors, ∑ u ∈ (range M).filter (fun u => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = _ := by
      refine sum_congr rfl fun e eMember => ?_
      have eDivides := (Nat.mem_divisors.mp eMember).1
      have ePositive := Nat.pos_of_mem_divisors eMember
      have eNonzero : (e : ℝ) ≠ 0 := by exact_mod_cast ePositive.ne'
      have MNonzero : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
      have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
      have quotientNonzero : ((M / e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast quotientPositive.ne'
      have quotient : (M : ℝ) = e * ((M / e : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' eDivides).symm
      rw [sum_filter_dvd_range ePositive eDivides, mul_sum]
      refine sum_congr rfl fun v _ => ?_
      have scales : (k : ℝ) * (e * v : ℕ) / M = (k : ℝ) * v / ((M / e : ℕ) : ℝ) := by
        push_cast
        rw [quotient]
        field_simp
      rw [scales, Nat.cast_mul, map_mul]
      ring

theorem norm_primitive_gauss_shift_le {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (primitive : χ.IsPrimitive) (x : ZMod d) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ ≤ Real.sqrt d := by
  rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar primitive, norm_mul,
    DirichletCharacter.norm_gaussSum_stdAddChar primitive]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (DirichletCharacter.norm_le_one _ _)

theorem conductor_cofactor {M d e : ℕ} [NeZero d] [NeZero M] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (coprime : e.Coprime d) :
    0 < M / e / d ∧ d * (M / e / d) = M / e ∧ e * (d * (M / e / d)) = M := by
  have eDivides := (Nat.mem_divisors.mp eMember).1
  have ePositive := Nat.pos_of_mem_divisors eMember
  have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
  have joint : e * d ∣ M := coprime.mul_dvd_of_dvd_of_dvd eDivides dDivides
  have dividesQuotient : d ∣ M / e := (Nat.dvd_div_iff_mul_dvd eDivides).mpr (by simpa [mul_comm] using joint)
  have quotient := Nat.mul_div_cancel' dividesQuotient
  exact ⟨Nat.div_pos (Nat.le_of_dvd quotientPositive dividesQuotient) (NeZero.pos d), quotient,
    by rw [quotient, Nat.mul_div_cancel' eDivides]⟩

theorem norm_induced_gauss_term {M d e : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (k : ℕ) {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) :
    ‖moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) *
          additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ)))‖ ≤
      if e.Coprime d ∧ (M / e / d) ∣ k then ((M / e / d : ℕ) : ℝ) * Real.sqrt d else 0 := by
  by_cases coprime : e.Coprime d
  · obtain ⟨fPositive, hFactor, _⟩ := conductor_cofactor dDivides eMember coprime
    let f := M / e / d
    letI : NeZero f := ⟨fPositive.ne'⟩
    have liftIdentity : (∑ v ∈ range (M / e), χ (v : ZMod d) *
        additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) =
        if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
      convert lift_gaussSum (f := f) χ k using 1
      rw [show (M / e : ℕ) = d * f from hFactor.symm, Nat.cast_mul]
    rw [liftIdentity]
    by_cases divides : f ∣ k
    · have divides' : (M / e / d) ∣ k := divides
      have relevant : e.Coprime d ∧ (M / e / d) ∣ k := ⟨coprime, divides'⟩
      simp only [if_pos divides, if_pos relevant, norm_mul, Complex.norm_natCast]
      have factor : ‖moebiusComplex e‖ * ‖χ (e : ZMod d)‖ ≤ 1 := by
        exact (mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)).trans
          (by simpa only [mul_one] using norm_moebiusComplex_le_one e)
      refine (mul_le_of_le_one_left (by positivity) factor).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_primitive_gauss_shift_le primitive _) (Nat.cast_nonneg _)
    · have divides' : ¬(M / e / d) ∣ k := divides
      simp [divides, divides', coprime]
  · have valZero : χ (e : ZMod d) = 0 := MulChar.map_nonunit _
      (fun h => coprime ((ZMod.isUnit_iff_coprime e d).mp h))
    simp [coprime, valZero]

theorem norm_induced_gauss_le {M d : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) (k : ℕ) (kPositive : 0 < k) :
    ‖gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M))‖ ≤
      Real.sqrt d * ∑ f ∈ k.divisors.filter (fun f => d * f ∣ M), (f : ℝ) := by
  let cof (e : ℕ) := M / e / d
  let support := M.divisors.filter (fun e => e.Coprime d ∧ cof e ∣ k)
  let bound := k.divisors.filter (fun f => d * f ∣ M)
  have imageSubset : support.image cof ⊆ bound := by
    intro f member
    obtain ⟨e, eMember, rfl⟩ := mem_image.mp member
    obtain ⟨divisor, coprime, divides⟩ := mem_filter.mp eMember
    obtain ⟨_, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨divides, kPositive.ne'⟩,
      ⟨e, by rw [mul_comm]; exact identity.symm⟩⟩
  have injectiveOn : Set.InjOn cof (support : Set ℕ) := by
    intro e eMember e' e'Member same
    obtain ⟨divisor, coprime, _⟩ := mem_filter.mp eMember
    obtain ⟨divisor', coprime', _⟩ := mem_filter.mp e'Member
    obtain ⟨fPositive, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    obtain ⟨_, _, identity'⟩ := conductor_cofactor dDivides divisor' coprime'
    change e * (d * cof e) = M at identity
    change e' * (d * cof e') = M at identity'
    rw [← same] at identity'
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (NeZero.pos d) fPositive) (identity.trans identity'.symm)
  have sumBound : (∑ e ∈ support, (cof e : ℝ)) ≤ ∑ f ∈ bound, (f : ℝ) := by
    rw [← sum_image injectiveOn]
    exact sum_le_sum_of_subset_of_nonneg imageSubset fun _ _ _ => Nat.cast_nonneg _
  rw [sum_inducedGauss_moebius]
  refine (norm_sum_le _ _).trans ?_
  have boundTerms := sum_le_sum (s := M.divisors)
    (fun e member => norm_induced_gauss_term dDivides member k primitive)
  refine boundTerms.trans ?_
  change (∑ e ∈ M.divisors, if e.Coprime d ∧ cof e ∣ k then (cof e : ℝ) * Real.sqrt d else 0) ≤
    Real.sqrt d * ∑ f ∈ bound, (f : ℝ)
  rw [← sum_filter, ← sum_mul, mul_comm (Real.sqrt d)]
  exact mul_le_mul_of_nonneg_right sumBound (Real.sqrt_nonneg _)

theorem standard_gauss_vanish_or_bound {M d : ℕ} [NeZero M] [NeZero d] (hd : d ∣ M)
    {χ : DirichletCharacter ℂ d} (hp : χ.IsPrimitive) :
    ‖gaussSum (DirichletCharacter.changeLevel hd χ) ZMod.stdAddChar‖ ≤
      if (M / d).Coprime d then Real.sqrt d else 0 := by
  by_cases hc : (M / d).Coprime d
  · have h := norm_induced_gauss_le hd hp 1 (by decide)
    rw [ite_eq_left hc]
    simpa [Nat.divisors_one, sum_filter, hd, AddChar.mulShift_one] using h
  · rw [ite_eq_right hc]
    have hz : gaussSum (DirichletCharacter.changeLevel hd χ)
        (ZMod.stdAddChar.mulShift ((1 : ℕ) : ZMod M)) = 0 := by
      rw [sum_inducedGauss_moebius]
      apply sum_eq_zero
      intro e he
      have h := norm_induced_gauss_term hd he 1 hp
      have hc' : ¬ (e.Coprime d ∧ (M / e / d) ∣ 1) := by
        rintro ⟨hec, hed⟩
        have h1 : M / e / d = 1 := Nat.dvd_one.mp hed
        obtain ⟨_, _, hm⟩ := conductor_cofactor hd he hec
        rw [h1, mul_one] at hm
        exact hc (by rwa [← hm, Nat.mul_div_cancel _ (NeZero.pos d)])
      rw [ite_eq_right hc'] at h
      exact norm_le_zero_iff.mp h
    simpa using norm_le_zero_iff.mpr (by simpa [AddChar.mulShift_one] using hz)

#print axioms standard_gauss_vanish_or_bound
end
end PintzEightGauss
