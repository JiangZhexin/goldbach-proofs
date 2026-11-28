import PintzEightGauss
import Mathlib.Data.Nat.Factorization.Basic

noncomputable section
open Finset PintzEightGauss
namespace PintzPrimePowerGauss

theorem lift_eq {p α β : ℕ} [NeZero (p^α)] [NeZero (p^β)]
    (hp : p.Prime) (hβ : 0 < β) (hba : β ≤ α) (hdiv : p^β ∣ p^α)
    (χ : DirichletCharacter ℂ (p^β)) (m : ℕ) :
    gaussSum (DirichletCharacter.changeLevel hdiv χ)
      (ZMod.stdAddChar.mulShift (m : ZMod (p^α))) =
      if p^(α-β) ∣ m then ((p^(α-β) : ℕ):ℂ) *
        gaussSum χ (ZMod.stdAddChar.mulShift ((m / p^(α-β) : ℕ) : ZMod (p^β))) else 0 := by
  rw [sum_inducedGauss_moebius]
  have hcollapse :
      (∑ e ∈ (p^α).divisors, moebiusComplex e * χ (e : ZMod (p^β)) *
        (∑ v ∈ range (p^α / e), χ (v : ZMod (p^β)) *
          additivePhase ((m : ℝ) * v / ((p^α / e : ℕ) : ℝ)))) =
      ∑ v ∈ range (p^α), χ (v : ZMod (p^β)) *
          additivePhase ((m : ℝ) * v / ((p^α : ℕ) : ℝ)) := by
    rw [sum_eq_single 1]
    · simp [moebiusComplex]
    · intro e he hne
      have hed := (Nat.mem_divisors.mp he).1
      obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hed
      have hj : 0 < j := Nat.pos_of_ne_zero (fun h => hne (by simp [h]))
      have hn : ¬IsUnit ((p^j : ℕ) : ZMod (p^β)) := by
        rw [ZMod.isUnit_iff_coprime]
        intro hc
        have h₁ : p ∣ p^j := dvd_pow_self _ hj.ne'
        have h₂ : p ∣ p^β := dvd_pow_self _ hβ.ne'
        exact hp.not_dvd_one (hc ▸ Nat.dvd_gcd h₁ h₂)
      rw [MulChar.map_nonunit _ hn, mul_zero, zero_mul]
    · intro hn
      exact (hn (Nat.mem_divisors.mpr ⟨one_dvd _, NeZero.ne _⟩)).elim
  rw [hcollapse]
  let f := p^(α-β)
  let : NeZero f := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hfac : p^β * f = p^α := by rw [show f = p^(α-β) from rfl, ← pow_add, Nat.add_sub_of_le hba]
  convert lift_gaussSum (f := f) χ m using 1
  rw [hfac, ← Nat.cast_mul, hfac]

theorem norm_eq {p α β : ℕ} [NeZero (p^α)] [NeZero (p^β)]
    (hp : p.Prime) (hβ : 0 < β) (hba : β ≤ α) (hdiv : p^β ∣ p^α)
    {χ : DirichletCharacter ℂ (p^β)} (hχ : χ.IsPrimitive) (m : ℕ) :
    ‖gaussSum (DirichletCharacter.changeLevel hdiv χ)
      (ZMod.stdAddChar.mulShift (m : ZMod (p^α)))‖ =
      if p^(α-β) ∣ m ∧ ¬p^(α-β+1) ∣ m then (p^ (α-β) : ℕ) *
        Real.sqrt (p^β : ℕ) else 0 := by
  rw [lift_eq hp hβ hba hdiv χ m]
  by_cases hm : p^(α-β) ∣ m
  · rw [ite_eq_left hm, norm_mul, Complex.norm_natCast,
      gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ, norm_mul,
      DirichletCharacter.norm_gaussSum_stdAddChar hχ]
    have hu : IsUnit (((m / p^(α-β) : ℕ)) : ZMod (p^β)) ↔ ¬p^(α-β+1) ∣ m := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hβ, Nat.coprime_comm,
        hp.coprime_iff_not_dvd, Nat.dvd_div_iff_mul_dvd hm, pow_succ]
    by_cases h : IsUnit (((m / p^(α-β) : ℕ)) : ZMod (p^β))
    · rw [ite_eq_left ⟨hm, hu.mp h⟩]
      have h' := (χ⁻¹).unit_norm_eq_one h.unit
      rw [h.unit_spec] at h'
      rw [h', one_mul]
    · have hn : ¬ (p^(α-β) ∣ m ∧ ¬p^(α-β+1) ∣ m) := fun H => h (hu.mpr H.2)
      rw [ite_eq_right hn, MulChar.map_nonunit _ h, norm_zero, zero_mul, mul_zero]
  · rw [ite_eq_right hm, norm_zero, ite_eq_right (fun h => hm h.1)]

theorem norm_shift_neg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-x))‖ =
      ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ := by
  let u : (ZMod q)ˣ := -1
  have h : (ZMod.stdAddChar.mulShift x).mulShift u = ZMod.stdAddChar.mulShift (-x) := by
    rw [AddChar.mulShift_mulShift]
    congr 1
    simp [u]
  rw [← h, gaussSum_mulShift_eq, norm_mul, (χ⁻¹).unit_norm_eq_one u, one_mul]

/-- Exact nonprincipal prime-power Gauss norm and support, in valuation
form at the negative additive shift appearing in Pintz's coefficient. -/
theorem norm_eq_valuation_neg {p α β m : ℕ} [NeZero (p^α)] [NeZero (p^β)]
    (hp : p.Prime) (hβ : 0 < β) (hba : β ≤ α) (hdiv : p^β ∣ p^α)
    {χ : DirichletCharacter ℂ (p^β)} (hχ : χ.IsPrimitive) (hm : m ≠ 0) :
    ‖gaussSum (DirichletCharacter.changeLevel hdiv χ)
      (ZMod.stdAddChar.mulShift (-(m : ZMod (p^α))))‖ =
      if m.factorization p = α-β then (p : ℝ)^((α:ℝ)-(β:ℝ)/2) else 0 := by
  rw [norm_shift_neg, norm_eq hp hβ hba hdiv hχ]
  simp only [hp.pow_dvd_iff_le_factorization hm]
  have hcond : α-β ≤ m.factorization p ∧ ¬α-β+1 ≤ m.factorization p ↔
      m.factorization p = α-β := by omega
  simp only [hcond]
  split_ifs with h
  push_cast
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul, ← Real.rpow_natCast,
    ← Real.rpow_add hpR, Nat.cast_sub hba]
  congr 1
  ring
  all_goals first | exact hpR.le | rfl

#print axioms norm_eq_valuation_neg
#print axioms lift_eq
#print axioms norm_eq
end PintzPrimePowerGauss
