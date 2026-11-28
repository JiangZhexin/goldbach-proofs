/- CRT unit-sum factorization adapted from openai/math, EgyptianFractions/RamanujanProduct. -/
import PintzPoleRamanujan
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic.LinearCombination

open scoped BigOperators ComplexConjugate

namespace PintzPoleEuler
noncomputable section
/-- A character sum over the units of a finite ring, written as a sum over
the whole ring so that product-ring factorization is transparent. -/
def unitSum {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (t : R) : ℂ := by
  classical
  exact ∑ a : R, if IsUnit a then ψ (t * a) else 0

def leftChar {R S : Type*} [CommRing R] [CommRing S]
    (ψ : AddChar (R × S) ℂ) : AddChar R ℂ :=
  ψ.compAddMonoidHom (AddMonoidHom.inl R S)

def rightChar {R S : Type*} [CommRing R] [CommRing S]
    (ψ : AddChar (R × S) ℂ) : AddChar S ℂ :=
  ψ.compAddMonoidHom (AddMonoidHom.inr R S)

theorem character_prod {R S : Type*} [CommRing R] [CommRing S]
    (ψ : AddChar (R × S) ℂ) (x : R) (y : S) :
    ψ (x, y) = leftChar ψ x * rightChar ψ y := by
  change ψ (x, y) = ψ (x, 0) * ψ (0, y)
  rw [← AddChar.map_add_eq_mul]
  simp

/-- A character sum over units factors through the two coordinate
characters. No primitivity or coprimality assumption is needed here. -/
theorem unitSum_prod {R S : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] (ψ : AddChar (R × S) ℂ) (t : R × S) :
    unitSum ψ t = unitSum (leftChar ψ) t.1 * unitSum (rightChar ψ) t.2 := by
  classical
  rcases t with ⟨x, y⟩
  unfold unitSum
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Prod.isUnit_iff]
  by_cases ha : IsUnit a <;> by_cases hb : IsUnit b <;>
    simp [ha, hb, character_prod]

/-- A primitive product-ring character remains primitive on each
coordinate ring. -/
theorem leftChar_primitive {R S : Type*} [CommRing R] [CommRing S]
    (ψ : AddChar (R × S) ℂ) (hψ : ψ.IsPrimitive) :
    (leftChar ψ).IsPrimitive := by
  intro a ha hshift
  apply hψ (a := (a, 0)) (by simpa using ha)
  apply AddChar.ext
  rintro ⟨x, y⟩
  have hx := congrArg (fun χ : AddChar R ℂ => χ x) hshift
  simpa [leftChar, AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply] using hx

theorem rightChar_primitive {R S : Type*} [CommRing R] [CommRing S]
    (ψ : AddChar (R × S) ℂ) (hψ : ψ.IsPrimitive) :
    (rightChar ψ).IsPrimitive := by
  intro a ha hshift
  apply hψ (a := (0, a)) (by simpa using ha)
  apply AddChar.ext
  rintro ⟨x, y⟩
  have hx := congrArg (fun χ : AddChar S ℂ => χ y) hshift
  simpa [rightChar, AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply] using hx

/-- Transporting a primitive character along a ring equivalence preserves
primitivity. -/
theorem primitive_comp_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (ψ : AddChar S ℂ) (hψ : ψ.IsPrimitive) (e : R ≃+* S) :
    (ψ.compAddMonoidHom e.toAddMonoidHom).IsPrimitive := by
  intro a ha hshift
  apply hψ (a := e a) (by simpa using ha)
  apply AddChar.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx := congrArg (fun χ : AddChar R ℂ => χ x) hshift
  simpa [AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply] using hx

/-- The unit character sum is invariant under simultaneous transport of
the character and its argument by a ring equivalence. -/
theorem unitSum_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] (ψ : AddChar S ℂ) (e : R ≃+* S) (t : R) :
    unitSum (ψ.compAddMonoidHom e.toAddMonoidHom) t = unitSum ψ (e t) := by
  classical
  unfold unitSum
  rw [← e.toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro a ha
  simp [AddChar.compAddMonoidHom_apply]

/-- Every primitive character has the same unit sum at prime modulus. -/
theorem prime_unitSum {p : ℕ} [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ)
    (hψ : ψ.IsPrimitive) (t : ZMod p) :
    unitSum ψ t = if t = 0 then (p : ℂ) - 1 else -1 := by
  classical
  have hsum : (∑ a : ZMod p, ψ (t * a)) = if t = 0 then (p : ℂ) else 0 := by
    simpa only [mul_comm, ZMod.card, Nat.cast_ite, Nat.cast_zero] using
      AddChar.sum_mulShift t hψ
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (ZMod p))) (fun a => ψ (t * a))
    (Finset.mem_univ 0)
  simp only [mul_zero, AddChar.map_zero_eq_one] at hsplit
  rw [hsum] at hsplit
  have hunit : unitSum ψ t =
      ∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0, ψ (t * a) := by
    unfold unitSum
    simp only [isUnit_iff_ne_zero]
    rw [← Finset.sum_filter, Finset.filter_ne']
  rw [hunit]
  split_ifs at hsplit ⊢ <;> linear_combination hsplit

/-- CRT factorization of an actual unit character sum. The coordinate
characters are transported characters, so no choice of inverse CRT
coefficients is hidden in the statement. -/
theorem unitSum_chineseRemainder {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (ψ : AddChar (ZMod (m * n)) ℂ) (u : ℕ) :
    let χ := ψ.compAddMonoidHom (ZMod.chineseRemainder h).symm.toAddMonoidHom
    unitSum ψ (-(u : ZMod (m * n))) =
      unitSum (leftChar χ) (-(u : ZMod m)) *
        unitSum (rightChar χ) (-(u : ZMod n)) := by
  dsimp only
  have hcast : (ZMod.chineseRemainder h).symm
      (-(u : ZMod m), -(u : ZMod n)) = -(u : ZMod (m * n)) := by
    change (ZMod.chineseRemainder h).symm (-(u : ZMod m × ZMod n)) = _
    simp
  have htransport := unitSum_ringEquiv ψ (ZMod.chineseRemainder h).symm
    (-(u : ZMod m), -(u : ZMod n))
  rw [hcast] at htransport
  rw [← htransport, unitSum_prod]

/-- At a squarefree modulus supplied as a product of distinct primes,
every primitive character gives the expected product of Ramanujan
factors. This finite identity is independent of analytic prime estimates. -/
theorem unitSum_of_primeProduct (s : Finset ℕ) :
    ∀ (_hs : ∀ p ∈ s, p.Prime) (n : ℕ) [NeZero n],
      n = ∏ p ∈ s, p →
      ∀ (ψ : AddChar (ZMod n) ℂ), ψ.IsPrimitive → ∀ u : ℕ,
        unitSum ψ (-(u : ZMod n)) =
          ∏ p ∈ s, (if p ∣ u then (p : ℂ) - 1 else -1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro hs n hn0 hn ψ hψ u
      simp only [Finset.prod_empty] at hn ⊢
      subst n
      have hunit : ∀ x : ZMod 1, IsUnit x := by
        intro x
        have hx : x = 1 := Subsingleton.elim _ _
        rw [hx]
        exact isUnit_one
      have hchar : ∀ x : ZMod 1, ψ x = 1 := by
        intro x
        have hx : x = 0 := Subsingleton.elim _ _
        rw [hx, AddChar.map_zero_eq_one]
      simp [unitSum, hchar]
      exact Subsingleton.elim _ _
  | @insert p s hps ih =>
      intro hs n hn0 hn ψ hψ u
      have hp : p.Prime := hs p (Finset.mem_insert_self p s)
      have hspr : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      let q : ℕ := ∏ i ∈ s, i
      have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => (hspr i hi).ne_zero)
      let : NeZero q := ⟨hq0⟩
      let : Fact p.Prime := ⟨hp⟩
      have hpq : p.Coprime q := by
        apply Nat.Coprime.prod_right
        intro i hi
        apply hp.coprime_iff_not_dvd.mpr
        rw [Nat.prime_dvd_prime_iff_eq hp (hspr i hi)]
        intro heq
        exact hps (heq ▸ hi)
      have hn' : n = p * q := by simpa only [Finset.prod_insert hps] using hn
      clear hn
      subst n
      let χ : AddChar (ZMod p × ZMod q) ℂ :=
        ψ.compAddMonoidHom (ZMod.chineseRemainder hpq).symm.toAddMonoidHom
      have hχ : χ.IsPrimitive := primitive_comp_ringEquiv ψ hψ _
      have hleft := prime_unitSum (leftChar χ) (leftChar_primitive χ hχ) (-(u : ZMod p))
      have hright := ih hspr q rfl (rightChar χ) (rightChar_primitive χ hχ) u
      rw [Finset.prod_insert hps]
      rw [unitSum_chineseRemainder hpq ψ u]
      change unitSum (leftChar χ) (-(u : ZMod p)) *
        unitSum (rightChar χ) (-(u : ZMod q)) = _
      rw [hleft, hright]
      simp only [neg_eq_zero, ZMod.natCast_eq_zero_iff]

/-- The prime-product formula in the customary squarefree-modulus form. -/
theorem unitSum_squarefree {n : ℕ} [NeZero n] (hn : Squarefree n)
    (ψ : AddChar (ZMod n) ℂ) (hψ : ψ.IsPrimitive) (u : ℕ) :
    unitSum ψ (-(u : ZMod n)) =
      ∏ p ∈ n.primeFactors, (if p ∣ u then (p : ℂ) - 1 else -1) := by
  exact unitSum_of_primeProduct n.primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1) n
    (Nat.prod_primeFactors_of_squarefree hn).symm ψ hψ u

/-- The standard Ramanujan sum at any nonzero modulus, with its usual
unit-residue restriction. -/
def ramanujanSum (n : ℕ) [NeZero n] (u : ℕ) : ℂ :=
  unitSum ZMod.stdAddChar (-(u : ZMod n))

theorem ramanujanSum_squarefree {n : ℕ} [NeZero n] (hn : Squarefree n) (u : ℕ) :
    ramanujanSum n u =
      ∏ p ∈ n.primeFactors, (if p ∣ u then (p : ℂ) - 1 else -1) :=
  unitSum_squarefree hn ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar n) u


/-- Identify the exact Fourier-center sum with the CRT form of the
Ramanujan sum, including the negative Fourier sign. -/
theorem pole_ramanujan_eq_crt {q : ℕ} [NeZero q] (m : ℕ) :
    PintzPoleKernelTail.ramanujan q m = ramanujanSum q m := by
  classical
  rw [PintzPoleRamanujan.ramanujan_eq_conj_sum]
  unfold PintzPoleRamanujan.ramanujanSum ramanujanSum unitSum
  rw [map_sum]
  have he := Finset.sum_filter (s := (Finset.univ : Finset (ZMod q)))
    (p := fun a : ZMod q => IsUnit a) (f := fun a => (ZMod.stdAddChar (N:=q)) (-(m:ZMod q)*a))
  refine Eq.trans ?_ (he.trans ?_)
  swap
  · apply Finset.sum_congr rfl
    intro a _
    by_cases h : IsUnit a <;> simp [h]
  apply Finset.sum_bij
    (s := (Finset.univ : Finset (ZMod q)ˣ))
    (t := (Finset.univ : Finset (ZMod q)).filter IsUnit)
    (f := fun a => conj ((ZMod.stdAddChar (N:=q)) ((m:ZMod q)*(a:ZMod q))))
    (g := fun a => (ZMod.stdAddChar (N:=q)) (-(m:ZMod q)*a))
    (fun a _ => (a:ZMod q))
  · intro a _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.isUnit⟩
  · intro a ha b hb h
    exact Units.val_injective h
  · intro a ha
    obtain ⟨u,hu⟩ := (Finset.mem_filter.mp ha).2
    exact ⟨u,Finset.mem_univ _,hu⟩
  · intro a _
    simp only [neg_mul]
    rw [AddChar.map_neg_eq_inv]
    have hr := (ZMod.toCircle ((m:ZMod q) * (a:ZMod q))).norm_coe
    apply Eq.symm (Complex.inv_eq_conj ?_)
    exact hr

#print axioms pole_ramanujan_eq_crt
#print axioms ramanujanSum_squarefree
end
end PintzPoleEuler
