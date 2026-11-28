import RichShiftPoleAssembly263
import RichShiftDensityCombine263

noncomputable section
open Finset
namespace RichShiftEligibleGapPlug

theorem gap_of_public_signatures
    (hDir : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
      (7/8:ℝ) < s.re → ¬(χ = 1 ∧ s = 1) → χ.LFunction s ≠ 0)
    (hZeta : ∀ {s : ℂ}, (7/8:ℝ) < s.re → riemannZeta s ≠ 0) :
    PintzConditionalPoleOnly.Gap := by
  refine ⟨fun s hs => hZeta hs, ?_⟩
  intro q _ χ hq hp s hs
  apply hDir χ hs
  rintro ⟨hχ,_⟩
  have hc : χ.conductor = q := hp
  rw [hχ, DirichletCharacter.conductor_one] at hc
  omega

theorem target_from_eligible_fixed_strip
    (hNon : RichShiftDensityCombine263.NonprincipalDensityBound)
    (hDir : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
      (7/8:ℝ) < s.re → ¬(χ = 1 ∧ s = 1) → χ.LFunction s ≠ 0)
    (hZeta : ∀ {s : ℂ}, (7/8:ℝ) < s.re → riemannZeta s ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
      ∀ e ∈ Finset.Icc 1 (Nat.log 2 X/2),
        (((Finset.Ico X (2*X)).filter (fun n => Even n ∧
          (((Finset.Icc 2 (n-2^e)).filter
            (fun p => Nat.Prime p ∧ Nat.Prime ((n-2^e)-p))).card:ℝ)
            < c*(X:ℝ)/Real.log (X:ℝ)^2)).card : ℝ)
          ≤ C*(X:ℝ) ^ (37/50:ℝ)  :=
  RichShiftPoleAssembly263.frozen_of_density_and_gap
    (gap_of_public_signatures hDir hZeta) (RichShiftDensityCombine263.combined hNon)

#print axioms target_from_eligible_fixed_strip
end RichShiftEligibleGapPlug
