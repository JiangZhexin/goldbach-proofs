import PintzEightEnergy

noncomputable section
open Finset MeasureTheory
open scoped Classical
namespace PintzEightConductors

def prims (r : ℕ) : Finset (DirichletCharacter ℂ r) := univ.filter (·.IsPrimitive)

def pack {q : ℕ} (χ : DirichletCharacter ℂ q) : (r : ℕ) × DirichletCharacter ℂ r :=
  ⟨χ.conductor, χ.primitiveCharacter⟩

private theorem eq_lift_of_heq {q r s : ℕ}
    (hr : r ∣ q) (hs : s ∣ q) (h : r = s)
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (he : HEq χ ψ) : DirichletCharacter.changeLevel hr χ = DirichletCharacter.changeLevel hs ψ := by
  subst s
  cases he
  rfl

private theorem heq_of_eq_lift {q r s : ℕ} [NeZero q]
    (hr : r ∣ q) (hs : s ∣ q) (h : r = s)
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (he : DirichletCharacter.changeLevel hr χ = DirichletCharacter.changeLevel hs ψ) : HEq χ ψ := by
  subst s
  exact heq_of_eq (DirichletCharacter.changeLevel_injective hr he)

theorem sum_to_primitives {q : ℕ} [NeZero q] (F : ((r : ℕ) × DirichletCharacter ℂ r) → ℝ) :
    (∑ χ : DirichletCharacter ℂ q, F (pack χ)) =
      ∑ r ∈ q.divisors, ∑ χ ∈ prims r, F ⟨r, χ⟩ := by
  rw [sum_sigma' q.divisors prims (fun r χ => F ⟨r, χ⟩)]
  apply sum_bij (fun χ _ => pack χ)
  · intro χ _
    exact mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne q⟩,
      mem_filter.mpr ⟨mem_univ _, χ.primitiveCharacter_isPrimitive⟩⟩
  · intro a _ b _ hab
    unfold pack at hab
    obtain ⟨hs, he⟩ := Sigma.ext_iff.mp hab
    have eq' := eq_lift_of_heq a.conductor_dvd_level b.conductor_dvd_level hs he
    simpa only [DirichletCharacter.changeLevel_primitiveCharacter] using eq'
  · rintro ⟨r, χ⟩ h
    obtain ⟨hd, hp⟩ := mem_sigma.mp h
    let hdiv := (Nat.mem_divisors.mp hd).1
    let ψ := DirichletCharacter.changeLevel hdiv χ
    have hr : ψ.conductor = r :=
      (DirichletCharacter.conductor_changeLevel χ hdiv).trans (mem_filter.mp hp).2
    refine ⟨ψ, mem_univ _, Sigma.ext hr ?_⟩
    have he : (DirichletCharacter.changeLevel ψ.conductor_dvd_level) ψ.primitiveCharacter =
        DirichletCharacter.changeLevel hdiv χ := DirichletCharacter.changeLevel_primitiveCharacter ψ
    exact heq_of_eq_lift ψ.conductor_dvd_level hdiv hr he
  · intro χ _
    rfl

#print axioms sum_to_primitives
end PintzEightConductors
