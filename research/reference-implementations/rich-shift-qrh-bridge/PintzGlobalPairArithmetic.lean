import PintzPrimePowerPair
import PintzCRTConductor

noncomputable section
open Finset PintzPrimePowerPair PintzCRTConductor PintzGaussCRT
namespace PintzGlobalPairArithmetic

theorem left_mul {a b : ℕ} (h : a.Coprime b) (χ ψ : DirichletCharacter ℂ (a*b)) :
    left h (χ*ψ) = left h χ * left h ψ := by
  ext1 x
  change (χ*ψ) ((ZMod.chineseRemainder h).symm (↑x,1)) =
    χ ((ZMod.chineseRemainder h).symm (↑x,1)) * ψ ((ZMod.chineseRemainder h).symm (↑x,1))
  exact MulChar.mul_apply ..

theorem right_mul {a b : ℕ} (h : a.Coprime b) (χ ψ : DirichletCharacter ℂ (a*b)) :
    right h (χ*ψ) = right h χ * right h ψ := by
  ext1 x
  change (χ*ψ) ((ZMod.chineseRemainder h).symm (1,↑x)) =
    χ ((ZMod.chineseRemainder h).symm (1,↑x)) * ψ ((ZMod.chineseRemainder h).symm (1,↑x))
  exact MulChar.mul_apply ..

theorem coefficient_crt {a b : ℕ} [NeZero a] [NeZero b] [NeZero (a*b)] (h : a.Coprime b)
    (χ ψ : DirichletCharacter ℂ (a*b)) (m : ℕ) :
    coefficient χ ψ m =
      coefficient (left h χ) (left h ψ) m * coefficient (right h χ) (right h ψ) m := by
  have hStd (η : DirichletCharacter ℂ (a*b)) :
      stdNorm η = stdNorm (left h η) * stdNorm (right h η) := by
    simpa only [stdNorm, Nat.cast_one, AddChar.mulShift_one] using norm_crt_nat h η 1
  have hTwist (η : DirichletCharacter ℂ (a*b)) :
      twistNorm η m = twistNorm (left h η) m * twistNorm (right h η) m :=
    norm_crt_neg h η m
  simp only [coefficient, hStd, hTwist, left_mul, right_mul, Nat.totient_mul h, Nat.cast_mul,
    mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The original complex coefficient with the inverse product twist. -/
def actual {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) : ℂ :=
  gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar *
    gaussSum (χ*ψ)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod q))) / (q.totient:ℂ)^2

theorem norm_actual {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) :
    ‖actual χ ψ m‖ = coefficient χ ψ m := by
  simp only [actual, norm_div, norm_mul, norm_pow, Complex.norm_natCast, coefficient, stdNorm]
  congr 2
  exact twist_inv (χ*ψ) m

theorem coefficient_one (χ ψ : DirichletCharacter ℂ 1) (m : ℕ) :
    coefficient χ ψ m = 1 := by
  have hg (η : DirichletCharacter ℂ 1) (e : AddChar (ZMod 1) ℂ) :
      gaussSum η e = 1 := by
    have h (x : ZMod 1) : η x * e x = 1 := by
      have hη : η x = 1 := by rw [show x = 1 from Subsingleton.elim _ _, map_one]
      have he : e x = 1 := by rw [show x = 0 from Subsingleton.elim _ _, AddChar.map_zero_eq_one]
      rw [hη,he,mul_one]
    unfold gaussSum
    simp_rw [h]
    simp
  simp [coefficient, stdNorm, twistNorm, hg]

/-- A product bound over prime powers, using any nonnegative local bound
depending only on the two local conductor exponents. -/
theorem prime_product_majorant (U : ℕ → ℕ → ℕ → ℕ → ℝ) (m : ℕ)
    (hLocal : ∀ (p a : ℕ) [NeZero (p^a)], p.Prime → 0 < a →
      ∀ χ ψ : DirichletCharacter ℂ (p^a),
        coefficient χ ψ m ≤ U p a (χ.conductor.factorization p) (ψ.conductor.factorization p))
    (hU : ∀ p a b c, 0 ≤ U p a b c)
    (s : Finset ℕ) (A : ℕ → ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 0 < A p)
    (q : ℕ) [NeZero q] (hq : q = ∏ p ∈ s, p^A p)
    (χ ψ : DirichletCharacter ℂ q) :
    coefficient χ ψ m ≤ ∏ p ∈ s,
      U p (A p) (χ.conductor.factorization p) (ψ.conductor.factorization p) := by
  classical
  induction s using Finset.induction_on generalizing q with
  | empty =>
    simp only [prod_empty] at hq ⊢
    subst q
    exact (coefficient_one χ ψ m).le
  | @insert p s hps IH =>
    obtain ⟨hp,hA⟩ := hs p (mem_insert_self _ _)
    let b := ∏ r ∈ s, r^A r
    have hpq : ¬p ∣ b := by
      intro H
      obtain ⟨r,hr,hD⟩ := (hp.prime.dvd_finsetProd_iff _).mp H
      have hpr := (hs r (mem_insert_of_mem hr)).1
      have he := (Nat.prime_dvd_prime_iff_eq hp hpr).mp (hp.dvd_of_dvd_pow hD)
      exact hps (he ▸ hr)
    have hpc : (p^A p).Coprime b :=
      (hp.coprime_iff_not_dvd.mpr hpq).pow_left _
    have hb : b ≠ 0 := prod_ne_zero_iff.mpr
      (fun r hr => pow_ne_zero _ (hs r (mem_insert_of_mem hr)).1.ne_zero)
    let : NeZero b := ⟨hb⟩
    let : NeZero (p^A p) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hq' : q = p^A p * b := by simpa only [prod_insert hps] using hq
    clear hq
    subst q
    rw [coefficient_crt hpc, prod_insert hps]
    have hLeft (η : DirichletCharacter ℂ (p^A p*b)) :
        (left hpc η).conductor.factorization p = η.conductor.factorization p := by
      rw [left_conductor_primePower hp hA hpc η, Nat.factorization_pow_self hp]
    have hRight (r) (hr : r ∈ s) (η : DirichletCharacter ℂ (p^A p*b)) :
        (right hpc η).conductor.factorization r = η.conductor.factorization r := by
      have hpr := (hs r (mem_insert_of_mem hr)).1
      have hrp : ¬r ∣ p^A p := by
        intro H
        have hh := (Nat.prime_dvd_prime_iff_eq hpr hp).mp (hpr.dvd_of_dvd_pow H)
        exact hps (hh ▸ hr)
      have hZ : (left hpc η).conductor.factorization r = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun H => hrp (H.trans (left hpc η).conductor_dvd_level))
      rw [← conductor_product hpc η,
        Nat.factorization_mul (left hpc η).conductor_ne_zero (right hpc η).conductor_ne_zero,
        Finsupp.add_apply, hZ, zero_add]
    have l := hLocal p (A p) hp hA (left hpc χ) (left hpc ψ)
    rw [hLeft χ, hLeft ψ] at l
    have r := IH (fun r hr => hs r (mem_insert_of_mem hr)) b rfl (right hpc χ) (right hpc ψ)
    have hRewrite : (∏ r ∈ s,
        U r (A r) ((right hpc χ).conductor.factorization r)
          ((right hpc ψ).conductor.factorization r)) =
        ∏ r ∈ s, U r (A r) (χ.conductor.factorization r) (ψ.conductor.factorization r) := by
      exact prod_congr rfl (fun r hr => by rw [hRight r hr χ, hRight r hr ψ])
    rw [hRewrite] at r
    exact mul_le_mul l r (by unfold coefficient stdNorm twistNorm; positivity) (hU ..)

def freeFactor (p m : ℕ) : ℝ :=
  if p ∣ m then 1/(p-1:ℝ) else 1/(p-1:ℝ)^2

def localMajor (m p a b c : ℕ) : ℝ :=
  if p.Prime then
    if b = 0 ∧ c = 0 then
      if a = 1 then freeFactor p m else 0
    else if a = max b c then PintzForcedLocalEnvelope.ordinary p (m.factorization p) else 0
  else 0

theorem localMajor_nonneg (m p a b c : ℕ) : 0 ≤ localMajor m p a b c := by
  unfold localMajor
  split_ifs with hp hab hac hac
  · have h₁ : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    unfold freeFactor
    split_ifs <;> positivity
  · exact le_rfl
  · have h₂ : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    unfold PintzForcedLocalEnvelope.ordinary
    split_ifs
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h₂)) (sq_nonneg _)
    · exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · exact le_rfl
  · exact le_rfl

theorem conductor_exp_iff {p a : ℕ} [NeZero (p^a)] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p^a)) :
    (χ.conductor.factorization p = 0 ↔ χ = 1) ∧
      (χ.conductor.factorization p = a ↔ χ.IsPrimitive) ∧ χ.conductor.factorization p ≤ a := by
  obtain ⟨b,hb,he⟩ := conductor_power hp χ
  rw [he,Nat.factorization_pow_self hp]
  refine ⟨?_,?_,hb⟩
  · rw [DirichletCharacter.eq_one_iff_conductor_eq_one, he, ← pow_zero p (M:=ℕ)]
    exact (pow_right_injective₀ hp.pos hp.ne_one).eq_iff.symm
  · change _ ↔ χ.conductor = _
    rw [he]
    exact (pow_right_injective₀ hp.pos hp.ne_one).eq_iff.symm

theorem local_major {m p a : ℕ} [NeZero (p^a)] (hm : m ≠ 0) (he : Even m)
    (hp : p.Prime) (ha : 0 < a) (χ ψ : DirichletCharacter ℂ (p^a)) :
    coefficient χ ψ m ≤ localMajor m p a (χ.conductor.factorization p) (ψ.conductor.factorization p) := by
  by_cases hz : coefficient χ ψ m = 0
  · rw [hz]; exact localMajor_nonneg ..
  obtain ⟨hχ,hψ⟩ := zero_unless_supported hp ha χ ψ m hz
  have Hχ := conductor_exp_iff hp χ
  have Hψ := conductor_exp_iff hp ψ
  unfold localMajor
  rw [ite_eq_left hp]
  by_cases hP : χ.conductor.factorization p = 0 ∧ ψ.conductor.factorization p = 0
  · rw [ite_eq_left hP]
    rw [Hχ.1.mp hP.1, Hψ.1.mp hP.2, both_principal hp ha hm]
    by_cases H : a = 1
    · rw [ite_eq_left H, ite_eq_left H]
      have hpm : p ∣ m ↔ 1 ≤ m.factorization p := by simpa [pow_one] using hp.pow_dvd_iff_le_factorization hm (k:=1)
      simp only [freeFactor, hpm, H]
      exact le_rfl
    · rw [ite_eq_right H, ite_eq_right H]
  · have hNP : χ ≠ 1 ∨ ψ ≠ 1 := by
      by_contra! H
      exact hP ⟨Hχ.1.mpr H.1,Hψ.1.mpr H.2⟩
    have haM : a = max (χ.conductor.factorization p) (ψ.conductor.factorization p) := by
      apply le_antisymm _ (max_le Hχ.2.2 Hψ.2.2)
      rcases hNP with H|H
      · exact (Hχ.2.1.mpr (hχ.resolve_left (fun hh => H hh.1))).ge.trans (le_max_left _ _)
      · exact (Hψ.2.1.mpr (hψ.resolve_left (fun hh => H hh.1))).ge.trans (le_max_right _ _)
    rw [ite_eq_right hP, ite_eq_left haM]
    exact bound_of_nonprincipal hp ha hm he χ ψ hNP

theorem norm_actual_global_major {m q : ℕ} [NeZero q] (hm : m ≠ 0) (he : Even m)
    (χ ψ : DirichletCharacter ℂ q) :
    ‖actual χ ψ m‖ ≤ ∏ p ∈ q.primeFactors,
      localMajor m p (q.factorization p) (χ.conductor.factorization p) (ψ.conductor.factorization p) := by
  rw [norm_actual]
  apply prime_product_majorant (localMajor m) m
  · exact fun p a _ hp ha χ ψ => local_major hm he hp ha χ ψ
  · exact localMajor_nonneg m
  · intro p hp
    obtain ⟨hP,hpq,hq⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨hP, (hP.dvd_iff_one_le_factorization hq).mp hpq⟩
  · exact Nat.prod_primeFactors_pow_factorization (NeZero.ne q)

#print axioms norm_actual_global_major
#print axioms prime_product_majorant
#print axioms coefficient_crt
#print axioms norm_actual
end PintzGlobalPairArithmetic
