import PintzPrimePowerGauss
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

noncomputable section
open Finset PintzEightGauss
namespace PintzPrimePowerPrincipalGauss

theorem exact_sum {p a : ℕ} [NeZero (p^(a+1))] (hp : p.Prime) (m : ℕ) :
    gaussSum (1 : DirichletCharacter ℂ (p^(a+1)))
      (ZMod.stdAddChar.mulShift (m : ZMod (p^(a+1)))) =
    (if p^(a+1) ∣ m then (p^(a+1):ℕ) else 0 : ℂ) -
    (if p^a ∣ m then (p^a:ℕ) else 0 : ℂ) := by
  let Q := p^(a+1)
  let f : ℕ → ℂ := fun n => additivePhase ((m:ℝ)*n/Q)
  have hQ : p ∣ Q := dvd_pow_self _ (by omega)
  rw [gaussSum_as_fraction_sum]
  change (∑ n ∈ range Q, (1 : DirichletCharacter ℂ Q) (n : ZMod Q) * f n) = _
  have hχ (n : ℕ) : (1 : DirichletCharacter ℂ Q) (n : ZMod Q) =
      if p ∣ n then 0 else 1 := by
    have hunit : IsUnit (n : ZMod Q) ↔ ¬p ∣ n := by
      rw [ZMod.isUnit_iff_coprime]
      change n.Coprime (p^(a+1)) ↔ _
      rw [Nat.coprime_pow_right_iff (by omega : 0 < a+1), Nat.coprime_comm,
        hp.coprime_iff_not_dvd]
    by_cases hd : p ∣ n
    · rw [ite_eq_left hd, MulChar.map_nonunit _ (fun h => (hunit.mp h) hd)]
    · rw [ite_eq_right hd, MulChar.one_apply (hunit.mpr hd)]
  simp_rw [hχ]
  have hterm (n : ℕ) : (if p ∣ n then (0:ℂ) else 1) * f n =
      f n - (if p ∣ n then f n else 0) := by split_ifs <;> simp
  simp_rw [hterm]
  rw [sum_sub_distrib, ← sum_filter, sum_filter_dvd_range hp.pos hQ]
  have hdiv : Q/p = p^a := by
    dsimp [Q]
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  rw [hdiv]
  have hscale (n : ℕ) : f (p*n) = additivePhase ((m:ℝ)*n/(p^a:ℕ)) := by
    dsimp [f,Q]
    push_cast
    rw [pow_succ]
    have hpR : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp
  simp_rw [hscale]
  let : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [show (∑ n ∈ range Q, f n) = if Q ∣ m then (Q : ℂ) else 0 from
    sum_phase_fraction_eq_if_dvd (q:=Q) m, sum_phase_fraction_eq_if_dvd (q := p^a)]

/-- Prime-power Ramanujan norm at the actual negative shift, in valuation
form, including both nonzero cases. -/
theorem norm_valuation_neg_succ {p a m : ℕ} [NeZero (p^(a+1))]
    (hp : p.Prime) (hm : m ≠ 0) :
    ‖gaussSum (1 : DirichletCharacter ℂ (p^(a+1)))
      (ZMod.stdAddChar.mulShift (-(m : ZMod (p^(a+1)))))‖ =
      if a+1 ≤ m.factorization p then ((p^(a+1)).totient : ℝ) else
        if a = m.factorization p then (p^a : ℕ) else 0 := by
  rw [PintzPrimePowerGauss.norm_shift_neg, exact_sum hp m]
  simp only [hp.pow_dvd_iff_le_factorization hm]
  by_cases h : a+1 ≤ m.factorization p
  · have h' : a ≤ m.factorization p := by omega
    rw [ite_eq_left h, ite_eq_left h', ite_eq_left h, Nat.totient_prime_pow_succ hp]
    rw [pow_succ, ← Nat.cast_sub (show p^a ≤ p^a*p from Nat.le_mul_of_pos_right _ hp.pos),
      Complex.norm_natCast, ← Nat.mul_sub_one]
  · by_cases h' : a = m.factorization p
    · rw [ite_eq_right h, ite_eq_left (by omega : a ≤ m.factorization p), ite_eq_right h, ite_eq_left h',
        zero_sub, norm_neg, Complex.norm_natCast]
    · rw [ite_eq_right h, ite_eq_right (by omega : ¬a ≤ m.factorization p), ite_eq_right h, ite_eq_right h',
        sub_zero, norm_zero]

theorem norm_valuation_neg {p α m : ℕ} [NeZero (p^α)] (hp : p.Prime) (hα : 0 < α) (hm : m ≠ 0) :
    ‖gaussSum (1 : DirichletCharacter ℂ (p^α))
      (ZMod.stdAddChar.mulShift (-(m : ZMod (p^α))))‖ =
      if α ≤ m.factorization p then ((p^α).totient : ℝ) else
        if α = m.factorization p + 1 then (p^(α-1) : ℕ) else 0 := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hα.ne'
  simpa only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff, Nat.add_sub_cancel] using
    (norm_valuation_neg_succ (a:=a) hp hm)

theorem no_primitive_mod_two (χ : DirichletCharacter ℂ 2) : ¬χ.IsPrimitive := by
  classical
  have hc : Fintype.card (DirichletCharacter ℂ 2) = 1 := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    decide
  have he : χ = 1 := Fintype.card_le_one_iff.mp hc.le χ 1
  rw [he, DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one]
  decide

theorem mul_eq_one_mod_three {χ ψ : DirichletCharacter ℂ 3} (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    χ*ψ = 1 := by
  classical
  have hc : Fintype.card (DirichletCharacter ℂ 3) = 2 := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    decide
  by_contra h
  have he : χ*ψ ≠ χ := by
    intro he
    exact hψ (mul_left_cancel (he.trans (mul_one χ).symm))
  have hcard : ({χ*ψ, χ, 1} : Finset (DirichletCharacter ℂ 3)).card = 3 := by
    simp [Finset.card_insert_of_notMem, he, h, hχ]
  have hh := Finset.card_le_univ ({χ*ψ, χ, 1} : Finset (DirichletCharacter ℂ 3))
  omega

theorem primitive_mul_eq_one_mod_three {χ ψ : DirichletCharacter ℂ 3}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) : χ*ψ = 1 := by
  apply mul_eq_one_mod_three
  · intro H
    rw [H, DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hχ
    omega
  · intro H
    rw [H, DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hψ
    omega

#print axioms no_primitive_mod_two
#print axioms primitive_mul_eq_one_mod_three
#print axioms exact_sum
#print axioms norm_valuation_neg
end PintzPrimePowerPrincipalGauss
