import PintzEightCoefficient

noncomputable section
open Finset
open scoped Classical
namespace PintzEightLiteralReconstruction

open PintzEightGauss PintzEightCoefficient

theorem additive_inversion {q : ℕ} [NeZero q] {b : ZMod q} (hb : IsUnit b) :
    ((∑ χ : DirichletCharacter ℂ q, χ b * gaussSum χ⁻¹ ZMod.stdAddChar) /
      (q.totient : ℂ)) = ZMod.stdAddChar b := by
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  apply (div_eq_iff hφ).mpr
  unfold gaussSum
  simp_rw [mul_sum, ← mul_assoc]
  rw [sum_comm]
  simp_rw [← sum_mul]
  calc
    _ = ∑ a : ZMod q, (if a = b then (q.totient : ℂ) else 0) * ZMod.stdAddChar a := by
      apply sum_congr rfl
      intro a _
      by_cases ha : IsUnit a
      · have heq (χ : DirichletCharacter ℂ q) : χ b * χ⁻¹ a = χ a⁻¹ * χ b := by
          rw [← ha.unit_spec, MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit, mul_comm]
        simp_rw [heq]
        rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b]
      · have hne : a ≠ b := fun h => ha (h ▸ hb)
        have hz (χ : DirichletCharacter ℂ q) : χ⁻¹ a = 0 :=
          MulChar.map_nonunit _ ha
        simp [hz, hne]
    _ = _ := by
      simp [ite_mul, mul_comm]

theorem inversion_on_prime {q a n : ℕ} [NeZero q] (hq : q < n)
    (ha : a.Coprime q) (hn : n.Prime) :
    ((∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar *
      χ.primitiveCharacter (n : ZMod χ.conductor)) / (q.totient : ℂ)) =
    additivePhase ((a:ℝ)*n/q) := by
  have hc : n.Coprime q := (hn.coprime_iff_not_dvd).mpr
    (fun hd => (not_le_of_gt hq) (Nat.le_of_dvd (NeZero.pos q) hd))
  have hcast (χ : DirichletCharacter ℂ q) :
      χ.primitiveCharacter (n : ZMod χ.conductor) = χ (n : ZMod q) := by
    simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime
      (Nat.isCoprime_iff_coprime.mpr hc)
  simp_rw [hcast, mul_right_comm _ (gaussSum _ _) _, ← map_mul]
  rw [additive_inversion, stdAddChar_mul_nat_fraction]
  exact ((ZMod.isUnit_iff_coprime a q).mpr ha).mul ((ZMod.isUnit_iff_coprime n q).mpr hc)

def primeTwist (t : Finset ℕ) (w : ℕ → ℂ) (r : ℕ)
    (χ : DirichletCharacter ℂ r) (η : ℝ) :=
  ∑ n ∈ t, w n * χ (n : ZMod r) * additivePhase ((n:ℝ)*η)

theorem reconstruct_prime_window {q a : ℕ} [NeZero q] (ha : a.Coprime q)
    (t : Finset ℕ) (ht : ∀ n ∈ t, q < n ∧ n.Prime)
    (w : ℕ → ℂ) (η : ℝ) :
    slice q (a : ZMod q) (primeTwist t w) η =
      ∑ n ∈ t, w n * additivePhase ((n:ℝ)*((a:ℝ)/q+η)) := by
  unfold slice primeTwist
  simp_rw [mul_sum]
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro n hn
  have he (χ : DirichletCharacter ℂ q) :
      χ (a : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar *
          (w n * χ.primitiveCharacter (n : ZMod χ.conductor) * additivePhase ((n:ℝ)*η)) =
      (χ (a : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar * χ.primitiveCharacter (n : ZMod χ.conductor)) *
          (w n * additivePhase ((n:ℝ)*η)) := by ring
  simp_rw [he, ← sum_mul, mul_comm _ (w n * _), mul_div_assoc,
    inversion_on_prime (ht n hn).1 ha (ht n hn).2]
  rw [show (n:ℝ)*((a:ℝ)/q+η) = (a:ℝ)*n/q+(n:ℝ)*η by ring, additivePhase_add]
  ring

theorem slice_add {q : ℕ} [NeZero q] (a : ZMod q)
    (F G : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ) (η : ℝ) :
    slice q a (fun r χ x => F r χ x + G r χ x) η = slice q a F η + slice q a G η := by
  simp only [slice, mul_add, sum_add_distrib, add_div]

theorem reconstruct_split_prime_window {q a : ℕ} [NeZero q] (ha : a.Coprime q)
    (t : Finset ℕ) (ht : ∀ n ∈ t, q < n ∧ n.Prime)
    (w : ℕ → ℂ) (η : ℝ) (F G : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ)
    (h : ∀ r χ x, F r χ x + G r χ x = primeTwist t w r χ x) :
    slice q (a : ZMod q) F η + slice q (a : ZMod q) G η =
      ∑ n ∈ t, w n * additivePhase ((n:ℝ)*((a:ℝ)/q+η)) := by
  rw [← slice_add]
  simp_rw [h]
  exact reconstruct_prime_window ha t ht w η

/-- The exact residual formed by subtracting an arbitrary retained primitive component.
For each translated reduced fraction, its reconstruction is the literal prime trigonometric
polynomial minus the retained slice. No disjointness of the arcs is required. -/
theorem reconstruct_residual {q a : ℕ} [NeZero q] (ha : a.Coprime q)
    (t : Finset ℕ) (ht : ∀ n ∈ t, q < n ∧ n.Prime)
    (w : ℕ → ℂ) (η : ℝ) (G : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ) :
    slice q (a : ZMod q) (fun r χ x => primeTwist t w r χ x - G r χ x) η =
      (∑ n ∈ t, w n * additivePhase ((n:ℝ)*((a:ℝ)/q+η))) -
        slice q (a : ZMod q) G η := by
  apply eq_sub_of_add_eq
  exact reconstruct_split_prime_window ha t ht w η _ G (by intros; exact sub_add_cancel _ _)

#print axioms reconstruct_residual
#print axioms reconstruct_split_prime_window
end PintzEightLiteralReconstruction
