import PintzDyadicDetectorCounting
import PintzDyadicPolynomial

open Finset PintzSieveToHybrid PintzHybridDiscrete PintzHybridStrip
open PintzDyadicDetectorCounting PintzDyadicPolynomial
noncomputable section
namespace PintzDyadicStripCount

abbrev Char := Σ k : ℕ, DirichletCharacter ℂ (k+1)

def kernel (B Q : ℕ) (T U : ℝ) : ℝ :=
  (B:ℝ) * ((Real.pi^2 * (T+1) / 2) *
    ((⌊U * (2*Real.pi/(T+1))⌋₊:ℝ)+1+2*(Q:ℝ)^2))

def energyMajorant (U k : ℕ) (σ : ℝ) : ℝ :=
  2 * (1 + Real.log (2*U:ℝ))^(3+2*k) * (U:ℝ)^(1-2*σ)

theorem block_energy {Q : ℕ} (hQ : 1 ≤ Q) {U : ℕ} (hU : 1 ≤ U)
    (L J : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (A : Char → Finset ℂ) (w : Char → ℂ → ℕ)
    (hpt : ∀ j ∈ family Q, ∀ ρ ∈ A j, -ρ.im ∈ Set.Icc (-T) T)
    (B : ℕ) (hLocal : ∀ j ∈ family Q, ∀ x,
      ∑ ρ ∈ (A j).filter (fun ρ => |-ρ.im - x| ≤ 1/2), w j ρ ≤ B)
    {σ d : ℝ} (hσ : 0 ≤ σ) (hcd : σ ≤ d)
    (hβ : ∀ j ∈ family Q, ∀ ρ ∈ A j, ρ.re ∈ Set.Icc σ d) :
    let s := (Ioc U (2*U)).filter (fun n => L < n ∧ n ≤ J)
    let a := PintzDetectorFinite.coeff L
    let F := fun k : ℕ => kernel B Q T U *
      (2*energyMajorant U k σ + energyMajorant U (k+1) σ)
    (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ) * ‖P s (reScale a ρ.re) j (-ρ.im)‖^2) ≤
      F 0 + (d-σ)*(F 0 + F 1) := by
  dsimp only
  let s := (Ioc U (2*U)).filter (fun n => L < n ∧ n ≤ J)
  let a := PintzDetectorFinite.coeff L
  have hs (n) (hn : n ∈ s) : 0 < n ∧ (n:ℝ) ≤ 2*(U:ℝ) := by
    obtain ⟨h1,h2⟩ := mem_Ioc.mp (mem_filter.mp hn).1
    exact ⟨by omega, by exact_mod_cast h2⟩
  let E (b : ℕ → ℂ) := kernel B Q T U *
      (2 * (∑ n ∈ s, ‖reScale b σ n‖^2) + ∑ n ∈ s, ‖logCoeff (reScale b σ) n‖^2)
  let F (k : ℕ) := kernel B Q T U * (2 * energyMajorant U k σ + energyMajorant U (k+1) σ)
  have H : (∑ j ∈ family Q, ∑ ρ ∈ A j, (w j ρ:ℝ) * ‖P s (reScale a ρ.re) j (-ρ.im)‖^2)
      ≤ E a + (d-σ)*(E a + E (reCoeff a)) :=
    PintzHybridOverlap.weighted_strip_energy hQ s a hT hs A
      (fun _ ρ => -ρ.im) (fun _ ρ => ρ.re) w hpt B hLocal hcd hβ
  have En (k : ℕ) : (∑ n ∈ s, ‖reScale a σ n‖^2 * Real.log n ^ (2*k)) ≤ energyMajorant U k σ :=
    PintzDyadicCoefficientEnergy.energy hU L J k hσ
  have hf (n) (hn : n ∈ s) : 0 ≤ Real.log (n:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (hs n hn).1)
  have hw : 0 ≤ kernel B Q T U := by unfold kernel; positivity
  have hc (n) (hn : n ∈ s) : ‖reScale (reCoeff a) σ n‖ = ‖reScale a σ n‖ * Real.log n := by
    simp only [reScale, reCoeff, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf n hn)]
    ring
  have hl (b : ℕ → ℂ) (n) (hn : n ∈ s) :
      ‖logCoeff (reScale b σ) n‖ = ‖reScale b σ n‖ * Real.log n := by
    simp only [logCoeff, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf n hn), one_mul]
  have hE : E a ≤ F 0 := by
    apply mul_le_mul_of_nonneg_left _ hw
    apply add_le_add
    · simpa using mul_le_mul_of_nonneg_left (En 0) (by norm_num : (0:ℝ) ≤ 2)
    · convert En 1 using 1
      apply sum_congr rfl
      intro n hn
      rw [hl a n hn, mul_pow]
  have hE' : E (reCoeff a) ≤ F 1 := by
    apply mul_le_mul_of_nonneg_left _ hw
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      convert En 1 using 1
      apply sum_congr rfl
      intro n hn
      rw [hc n hn, mul_pow]
    · convert En 2 using 1
      apply sum_congr rfl
      intro n hn
      rw [hl _ n hn, hc n hn]
      ring
  exact H.trans (add_le_add hE
    (mul_le_mul_of_nonneg_left (add_le_add hE hE') (sub_nonneg.mpr hcd)))

#print axioms block_energy
end PintzDyadicStripCount
