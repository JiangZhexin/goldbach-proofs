/- Adapted the root and divisor formulas from openai/math, JointDickman. -/
import PintzPoleKernelTail
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Finset Polynomial
open scoped ArithmeticFunction.Moebius ComplexConjugate

namespace PintzPoleRamanujan
theorem stdAddChar_natCast {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = Complex.exp (2 * Real.pi * Complex.I * n / q) := by
  simpa only [Int.cast_natCast] using
    ZMod.stdAddChar_coe (N := q) (n : ℤ)

theorem stdAddChar_eq_primitive_power {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = Complex.exp (2 * Real.pi * Complex.I / q) ^ n := by
  rw [stdAddChar_natCast, ← Complex.exp_nat_mul]
  congr 1
  ring

open Classical in
theorem nthRoots_image_stdAddChar (q : ℕ) [NeZero q] :
    nthRootsFinset q (1 : ℂ) = univ.image (ZMod.stdAddChar (N := q)) := by
  ext z
  rw [mem_nthRootsFinset (NeZero.pos q), mem_image]
  constructor
  · intro hz
    obtain ⟨i, _, hi⟩ := (Complex.isPrimitiveRoot_exp q (NeZero.ne q)).eq_pow_of_pow_eq_one hz
    exact ⟨(i : ZMod q), mem_univ _, (stdAddChar_eq_primitive_power i).trans hi⟩
  · rintro ⟨r, _, rfl⟩
    rw [← ZMod.natCast_zmod_val r, stdAddChar_eq_primitive_power, ← pow_mul,
      mul_comm r.val q, pow_mul, (Complex.isPrimitiveRoot_exp q (NeZero.ne q)).pow_eq_one,
      one_pow]

open Classical in
theorem primitiveRoots_image_units (q : ℕ) [NeZero q] :
    primitiveRoots q ℂ = univ.image (fun r : (ZMod q)ˣ => ZMod.stdAddChar (r : ZMod q)) := by
  ext z
  rw [mem_primitiveRoots (NeZero.pos q), mem_image]
  constructor
  · intro hz
    obtain ⟨i, _, hic, hi⟩ := (Complex.isPrimitiveRoot_iff z q (NeZero.ne q)).mp hz
    refine ⟨ZMod.unitOfCoprime i hic, mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, stdAddChar_natCast]
    calc
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((i : ℂ) / q)) := by congr 1; ring
      _ = z := hi
  · rintro ⟨r, _, rfl⟩
    have hc : (r : ZMod q).val.Coprime q := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      simpa only [ZMod.natCast_zmod_val] using r.isUnit
    rw [← ZMod.natCast_zmod_val (r : ZMod q), stdAddChar_natCast]
    have he : 2 * (Real.pi : ℂ) * Complex.I * ((r : ZMod q).val : ℂ) / q =
        2 * (Real.pi : ℂ) * Complex.I * (((r : ZMod q).val : ℂ) / q) := by ring
    rw [he]
    exact Complex.isPrimitiveRoot_exp_of_coprime _ _ (NeZero.ne q) hc

noncomputable def ramanujanSum (q : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  ∑ r : (ZMod q)ˣ, ZMod.stdAddChar (h*(r : ZMod q))

theorem sum_nthRoots_power (q : ℕ) (hq : 0 < q) (k : ℕ) :
    (∑ z ∈ Polynomial.nthRootsFinset q (1 : ℂ), z^k) =
      if q ∣ k then (q : ℂ) else 0 := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [nthRoots_image_stdAddChar,sum_image]
  · simp_rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    simp_rw [mul_comm (k : ZMod q)]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
    simp only [ZMod.card,ZMod.natCast_eq_zero_iff]
    split_ifs <;> simp
  · exact fun _ _ _ _ h => ZMod.injective_stdAddChar h

/-- Möbius inversion of the full root sums. This includes nonunit frequencies. -/
theorem sum_primitiveRoots_power (q : ℕ) (hq : 0 < q) (k : ℕ) :
    (∑ z ∈ primitiveRoots q ℂ, z^k) =
      ∑ d ∈ q.divisorsAntidiagonal, (μ d.1 : ℂ)*
        (if d.2 ∣ k then (d.2 : ℂ) else 0) := by
  have hdiv : ∀ n > 0, (∑ d ∈ n.divisors, ∑ z ∈ primitiveRoots d ℂ, z^k) =
      if n ∣ k then (n : ℂ) else 0 := by
    intro n hn
    rw [← sum_nthRoots_power n hn k,IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,sum_biUnion]
    intro i _ j _ hij
    exact IsPrimitiveRoot.disjoint hij
  exact ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hdiv) q hq).symm

theorem ramanujanSum_divisor_formula (q : ℕ) [NeZero q] (k : ℕ) :
    ramanujanSum q (k : ZMod q) =
      ∑ d ∈ q.divisorsAntidiagonal, (μ d.1 : ℂ)*
        (if d.2 ∣ k then (d.2 : ℂ) else 0) := by
  rw [← sum_primitiveRoots_power q (NeZero.pos q) k,primitiveRoots_image_units,sum_image]
  · unfold ramanujanSum
    apply sum_congr rfl
    intro r _
    rw [← AddChar.map_nsmul_eq_pow,nsmul_eq_mul]
  · exact fun _ _ _ _ h => Units.val_injective (ZMod.injective_stdAddChar h)


theorem phase_neg_eq_conj (x : ℝ) :
    PintzPoleKernelTail.phase (-x) = conj (PintzPoleKernelTail.phase x) := by
  unfold PintzPoleKernelTail.phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem ramanujan_eq_conj_sum {q : ℕ} [NeZero q] (m : ℕ) :
    PintzPoleKernelTail.ramanujan q m = conj (ramanujanSum q (m : ZMod q)) := by
  classical
  unfold PintzPoleKernelTail.ramanujan ramanujanSum
  rw [map_sum]
  apply Finset.sum_bij
    (fun a ha => ZMod.unitOfCoprime a (Finset.mem_filter.mp ha).2)
  · intro a ha
    exact Finset.mem_univ _
  · intro a ha b hb hab
    have H := congrArg (fun u : (ZMod q)ˣ => (u:ZMod q).val) hab
    simpa [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
      Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha).1),
      Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)] using H
  · intro u hu
    have hunit : IsUnit (((u:ZMod q).val : ℕ):ZMod q) := by
      rw [ZMod.natCast_zmod_val]
      exact u.isUnit
    have hc := (ZMod.isUnit_iff_coprime ((u:ZMod q).val) q).mp hunit
    refine ⟨(u:ZMod q).val, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt _),hc⟩,?_⟩
    apply Units.val_injective
    rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
  · intro a ha
    rw [ZMod.coe_unitOfCoprime, ← Nat.cast_mul, stdAddChar_natCast]
    have h := phase_neg_eq_conj (((m:ℝ)*a)/q)
    simp only [neg_div, neg_mul] at h ⊢
    rw [h]
    unfold PintzPoleKernelTail.phase
    congr 2
    push_cast
    ring

theorem ramanujan_bound {q : ℕ} (hq : 0 < q) (m : ℕ) :
    ‖PintzPoleKernelTail.ramanujan q m‖ ≤
      ∑ d ∈ q.divisors.filter (fun d => d ∣ m), (d:ℝ) := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [ramanujan_eq_conj_sum, Complex.norm_conj, ramanujanSum_divisor_formula]
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => (μ a:ℂ)*(if b ∣ m then (b:ℂ) else 0))]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul]
  split_ifs with hm
  · rw [Complex.norm_natCast]
    apply mul_le_of_le_one_left (by positivity)
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q/d))
  · simp

#print axioms ramanujan_bound
end PintzPoleRamanujan
