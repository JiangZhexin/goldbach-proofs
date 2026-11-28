import PintzPrimePowerPrincipalGauss
import PintzForcedLocalEnvelope

noncomputable section
open PintzPrimePowerPrincipalGauss
open scoped Classical
namespace PintzPrimePowerPair

def stdNorm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  ‖gaussSum χ ZMod.stdAddChar‖

def twistNorm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ) : ℝ :=
  ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(m:ZMod q)))‖

def coefficient {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) : ℝ :=
  stdNorm χ * stdNorm ψ * twistNorm (χ*ψ) m / (q.totient:ℝ)^2

theorem conductor_power {p α : ℕ} [NeZero (p^α)] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p^α)) :
    ∃ β ≤ α, χ.conductor = p^β := (Nat.dvd_prime_pow hp).mp χ.conductor_dvd_level

theorem twist_nonprincipal {p α β : ℕ} [NeZero (p^α)] (hp : p.Prime)
    (hβ : 0 < β) (hβα : β ≤ α) (χ : DirichletCharacter ℂ (p^α))
    (hχ : χ.conductor = p^β) {m : ℕ} (hm : m ≠ 0) :
    twistNorm χ m = if m.factorization p = α-β then (p:ℝ)^((α:ℝ)-(β:ℝ)/2) else 0 := by
  let : NeZero (p^β) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨hd, ψ, he⟩ : χ.FactorsThrough (p^β) := hχ ▸ χ.factorsThrough_conductor
  have H : ψ.IsPrimitive := by
    change ψ.conductor = _
    rw [he, DirichletCharacter.conductor_changeLevel] at hχ
    exact hχ
  rw [he]
  exact PintzPrimePowerGauss.norm_eq_valuation_neg hp hβ hβα hd H hm

theorem std_eq_twist_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    stdNorm χ = twistNorm χ 1 := by
  unfold stdNorm twistNorm
  rw [PintzPrimePowerGauss.norm_shift_neg, Nat.cast_one, AddChar.mulShift_one]

theorem std_principal {p α : ℕ} [NeZero (p^α)] (hp : p.Prime) (hα : 0 < α) :
    stdNorm (1 : DirichletCharacter ℂ (p^α)) = if α = 1 then 1 else 0 := by
  rw [std_eq_twist_one, twistNorm, norm_valuation_neg hp hα (by decide : (1:ℕ) ≠ 0)]
  by_cases h : α = 1 <;> simp [hα.ne', h]

theorem std_nonprincipal {p α : ℕ} [NeZero (p^α)] (hp : p.Prime)
    {χ : DirichletCharacter ℂ (p^α)} (hχ : χ ≠ 1) :
    stdNorm χ = if χ.IsPrimitive then Real.sqrt (p^α : ℕ) else 0 := by
  obtain ⟨β,hβα,hβeq⟩ := conductor_power hp χ
  have hβ : 0 < β := by
    by_contra! H
    have Hb : β = 0 := by omega
    exact hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr (by simp [hβeq, Hb]))
  rw [std_eq_twist_one, twist_nonprincipal hp hβ hβα χ hβeq (by decide : (1:ℕ) ≠ 0)]
  have hiff : χ.IsPrimitive ↔ β = α := by
    change χ.conductor = _ ↔ _
    rw [hβeq]
    exact (pow_right_injective₀ hp.pos hp.ne_one).eq_iff
  simp only [hiff, Nat.factorization_one, Finsupp.zero_apply]
  by_cases h : β = α
  · subst β
    rw [Nat.sub_self, ite_eq_left rfl, ite_eq_left rfl]
    push_cast
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  · rw [ite_eq_right (show ¬ 0 = α-β by omega), ite_eq_right h]

theorem zero_unless_supported {p α : ℕ} [NeZero (p^α)] (hp : p.Prime) (hα : 0 < α)
    (χ ψ : DirichletCharacter ℂ (p^α)) (m : ℕ) (H : coefficient χ ψ m ≠ 0) :
    (χ = 1 ∧ α = 1 ∨ χ.IsPrimitive) ∧ (ψ = 1 ∧ α = 1 ∨ ψ.IsPrimitive) := by
  have h (η : DirichletCharacter ℂ (p^α)) (hη : stdNorm η ≠ 0) :
      η = 1 ∧ α = 1 ∨ η.IsPrimitive := by
    by_cases he : η = 1
    · left
      refine ⟨he, ?_⟩
      rw [he, std_principal hp hα] at hη
      by_contra hn
      exact hη (ite_eq_right hn)
    · right
      rw [std_nonprincipal hp he] at hη
      by_contra hn
      exact hη (ite_eq_right hn)
  exact ⟨h χ (fun H' => H (by simp [coefficient, H'])),
    h ψ (fun H' => H (by simp [coefficient, H']))⟩

private theorem geom_totient {p α : ℕ} (hp : p.Prime) (hα : 0 < α) :
    ((p^α).totient : ℝ) = (p:ℝ)^(α-1:ℕ) * ((p:ℝ)-1) := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hα.ne'
  rw [Nat.totient_prime_pow_succ hp, Nat.succ_sub_one, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub hp.pos, Nat.cast_one]

private theorem geom_step {p α : ℕ} (hα : 0 < α) :
    (p:ℝ)^α = (p:ℝ)^(α-1:ℕ) * p := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hα.ne'
  rw [Nat.succ_sub_one, pow_succ]

theorem normalized_ratio {p α : ℕ} (hp : p.Prime) (hα : 0 < α) :
    ((p:ℝ)^α)^2 / ((p^α).totient:ℝ)^2 = ((p:ℝ)/(p-1:ℝ))^2 := by
  rw [geom_totient hp hα, geom_step hα, mul_pow, mul_pow, div_pow]
  have h : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ h))

theorem principal_ratio {p α m : ℕ} [NeZero (p^α)] (hp : p.Prime)
    (hα : 0 < α) (hm : m ≠ 0) :
    (p:ℝ)^α * twistNorm (1 : DirichletCharacter ℂ (p^α)) m / ((p^α).totient:ℝ)^2 =
      if α ≤ m.factorization p then (p:ℝ)/(p-1:ℝ) else
        if α = m.factorization p+1 then (p:ℝ)/(p-1:ℝ)^2 else 0 := by
  rw [twistNorm, norm_valuation_neg hp hα hm]
  have hpp : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpow : (p:ℝ)^(α-1:ℕ) ≠ 0 := pow_ne_zero _ hpp
  have hp1 : (p:ℝ)-1 ≠ 0 := by
    have hpR : (1:ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  by_cases H : α ≤ m.factorization p
  · simp only [H, ite_true]
    rw [geom_totient hp hα, geom_step hα]
    field_simp
  · by_cases H' : α = m.factorization p+1
    · rw [ite_eq_right H, ite_eq_left H', ite_eq_right H, ite_eq_left H', Nat.cast_pow]
      rw [geom_totient hp hα, geom_step hα]
      field_simp
    · simp [H,H']

private theorem no_primitive_at_two {q : ℕ} (hq : q = 2) (χ : DirichletCharacter ℂ q) :
    ¬χ.IsPrimitive := by subst q; exact no_primitive_mod_two χ

private theorem mul_primitive_at_three {q : ℕ} (hq : q = 3)
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) :
    χ*ψ = 1 := by subst q; exact primitive_mul_eq_one_mod_three hχ hψ

theorem both_principal {p α m : ℕ} [NeZero (p^α)] (hp : p.Prime)
    (hα : 0 < α) (hm : m ≠ 0) :
    coefficient (1 : DirichletCharacter ℂ (p^α)) 1 m =
      if α = 1 then
        if α ≤ m.factorization p then 1/(p-1:ℝ) else 1/(p-1:ℝ)^2
      else 0 := by
  unfold coefficient
  rw [one_mul (1 : DirichletCharacter ℂ (p^α)), std_principal hp hα]
  by_cases h : α = 1
  · subst α
    simp only [ite_true, one_mul]
    rw [twistNorm, norm_valuation_neg hp (by decide : (0:ℕ) < 1) hm]
    have hp1 : (p:ℝ)-1 ≠ 0 := by
      have hpR : (1:ℝ) < p := by exact_mod_cast hp.one_lt
      linarith
    have ht : ((p^1).totient:ℝ) = (p:ℝ)-1 := by rw [geom_totient hp (by decide)]; simp
    rw [ht]
    by_cases hv : 1 ≤ m.factorization p
    · rw [ite_eq_left hv, ite_eq_left hv]
      field_simp
    · rw [ite_eq_right hv, ite_eq_right hv, ite_eq_left (by omega : (1:ℕ) = m.factorization p + 1)]
      simp
  · simp [h]

theorem one_principal {p α m : ℕ} [NeZero (p^α)] (hp : p.Prime)
    (hα : 0 < α) (hm : m ≠ 0) {χ : DirichletCharacter ℂ (p^α)}
    (hχ : χ ≠ 1) (hc : coefficient χ 1 m ≠ 0) :
    α = 1 ∧ m.factorization p = 0 ∧ coefficient χ 1 m = (p:ℝ)/(p-1:ℝ)^2 := by
  obtain ⟨hl,hr⟩ := zero_unless_supported hp hα χ 1 m hc
  have ha : α = 1 := hr.elim And.right (fun H => by
    change (1 : DirichletCharacter ℂ (p^α)).conductor = p^α at H
    rw [DirichletCharacter.conductor_one] at H
    have hh := (pow_right_injective₀ hp.pos hp.ne_one) (show p^0 = p^α by simpa only [pow_zero] using H)
    omega)
  have hpr : χ.IsPrimitive := hl.resolve_left (fun H => hχ H.1)
  have htw := twist_nonprincipal hp hα (le_refl α) χ hpr hm
  simp only [Nat.sub_self] at htw
  have hv : m.factorization p = 0 := by
    by_contra H
    exact hc (by simp [coefficient, htw, H])
  refine ⟨ha,hv,?_⟩
  rw [coefficient, mul_one, std_principal hp hα, std_nonprincipal hp hχ, ite_eq_left hpr,
    ite_eq_left ha, mul_one, htw, ite_eq_left hv]
  have ht : ((p^α).totient:ℝ) = (p:ℝ)-1 := by
    rw [geom_totient hp hα, ha]
    simp
  rw [ht, ha]
  push_cast
  rw [pow_one, show (1:ℝ)-1/2 = 1/2 by norm_num, ← Real.sqrt_eq_rpow, ← sq,
    Real.sq_sqrt (Nat.cast_nonneg _)]

theorem coefficient_comm {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) :
    coefficient χ ψ m = coefficient ψ χ m := by
  unfold coefficient
  rw [mul_comm (stdNorm χ), mul_comm χ ψ]

theorem bound_of_nonprincipal {p α m : ℕ} [NeZero (p^α)] (hp : p.Prime)
    (hα : 0 < α) (hm : m ≠ 0) (hmEven : Even m)
    (χ ψ : DirichletCharacter ℂ (p^α)) (hNP : χ ≠ 1 ∨ ψ ≠ 1) :
    coefficient χ ψ m ≤ PintzForcedLocalEnvelope.ordinary p (m.factorization p) := by
  have hEven : p = 2 → 0 < m.factorization p := fun h =>
    (hp.pow_dvd_iff_le_factorization hm (k:=1)).mp (by simpa [h] using even_iff_two_dvd.mp hmEven)
  by_cases hC : coefficient χ ψ m = 0
  · rw [hC]
    exact (by positivity : 0 ≤ (p:ℝ)/(p-1:ℝ)^2).trans
      (PintzForcedLocalEnvelope.small_branch hp hEven)
  obtain ⟨hL,hR⟩ := zero_unless_supported hp hα χ ψ m hC
  by_cases hχ : χ = 1
  · subst χ
    rw [coefficient_comm]
    rw [(one_principal hp hα hm (hNP.resolve_left (by simp))
      (by rwa [← coefficient_comm])).2.2]
    exact PintzForcedLocalEnvelope.small_branch hp hEven
  by_cases hψ : ψ = 1
  · subst ψ
    rw [(one_principal hp hα hm hχ hC).2.2]
    exact PintzForcedLocalEnvelope.small_branch hp hEven
  have hχP : χ.IsPrimitive := hL.resolve_left (fun h => hχ h.1)
  have hψP : ψ.IsPrimitive := hR.resolve_left (fun h => hψ h.1)
  have hct : coefficient χ ψ m =
      (p:ℝ)^α * twistNorm (χ*ψ) m / ((p^α).totient:ℝ)^2 := by
    rw [coefficient, std_nonprincipal hp hχ, std_nonprincipal hp hψ,
      ite_eq_left hχP, ite_eq_left hψP, ← sq, Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_pow]
  rw [hct]
  by_cases hprod : χ*ψ = 1
  · rw [hprod, principal_ratio hp hα hm]
    exact PintzForcedLocalEnvelope.principal_branch hp hα hEven
  obtain ⟨β,hβα,hβeq⟩ := conductor_power hp (χ*ψ)
  have hβ : 0 < β := by
    by_contra! H
    exact hprod (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr
      (by simp [hβeq, show β = 0 by omega]))
  have htw := twist_nonprincipal hp hβ hβα (χ*ψ) hβeq hm
  have hv : m.factorization p = α-β := by
    by_contra H
    exact hC (by simp [hct, htw, H])
  have h₂ : p = 2 → 2 ≤ β := by
    intro he
    by_contra! h
    have hβ1 : β = 1 := by omega
    have hq : p^β = 2 := by simp [he, hβ1]
    obtain ⟨hd, η, hr⟩ : (χ*ψ).FactorsThrough (p^β) := hβeq ▸ (χ*ψ).factorsThrough_conductor
    have hη : η.IsPrimitive := by
      change η.conductor = _
      rw [hr, DirichletCharacter.conductor_changeLevel] at hβeq
      exact hβeq
    exact no_primitive_at_two hq η hη
  have h₃ : p = 3 → α = 1 → β = 0 := by
    intro hp3 ha
    exfalso
    exact hprod (mul_primitive_at_three (by simp [hp3,ha]) hχP hψP)
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hnum : (p:ℝ)^((α:ℝ)-(β:ℝ)/2) = (p:ℝ)^α * (p:ℝ)^(-((β:ℝ)/2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hpR, sub_eq_add_neg]
  rw [htw, ite_eq_left hv, hnum, ← mul_assoc, ← sq, mul_div_right_comm, normalized_ratio hp hα]
  exact PintzForcedLocalEnvelope.nonprincipal_branch hp hβ hβα hv.symm hEven h₂ h₃

theorem twist_inv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (m : ℕ) : twistNorm χ⁻¹ m = twistNorm χ m := by
  unfold twistNorm
  let x : ZMod q := (m : ZMod q)
  change ‖gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (-x))‖ =
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-x))‖
  have he : (ZMod.stdAddChar.mulShift x)⁻¹ = ZMod.stdAddChar.mulShift (-x) := by
    ext y
    simp [AddChar.mulShift_apply]
  rw [← he, ← star_gaussSum_eq, norm_star, he, PintzPrimePowerGauss.norm_shift_neg]

#print axioms twist_inv
#print axioms both_principal
#print axioms bound_of_nonprincipal
#print axioms zero_unless_supported
end PintzPrimePowerPair
