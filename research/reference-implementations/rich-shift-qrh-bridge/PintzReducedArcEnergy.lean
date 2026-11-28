import PintzEightPrimitiveEnergy
import PintzMajorArcGeometry

noncomputable section
open Finset MeasureTheory PintzEightEnergy PintzEightRegroup PintzMajorArcGeometry
open scoped Classical
namespace PintzReducedArcEnergy

abbrev Data := (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ

def residue (q : ℕ) [NeZero q] (F : Data) (a : ZMod q) (x : ℝ) : ℂ :=
  (∑ χ : DirichletCharacter ℂ q,
      χ a * gaussSum χ⁻¹ ZMod.stdAddChar * F χ.conductor χ.primitiveCharacter x) / (q.totient : ℂ)

def slice (F : Data) (i : ℕ × ℕ) (x : ℝ) : ℂ :=
  if h : i.1 = 0 then 0 else @residue i.1 ⟨h⟩ F (i.2 : ZMod i.1) x

theorem continuous_slice (F : Data) (hF : ∀ r χ, Continuous (F r χ)) (i : ℕ × ℕ) :
    Continuous (slice F i) := by
  unfold slice
  by_cases h : i.1 = 0
  · simp [h, continuous_const]
  · let : NeZero i.1 := ⟨h⟩
    rw [show (fun x : ℝ => if h' : i.1 = 0 then (0:ℂ) else @residue i.1 ⟨h'⟩ F (i.2 : ZMod i.1) x) = residue i.1 F (i.2 : ZMod i.1) from funext (fun x => dite_eq_right h)]
    unfold residue
    fun_prop

theorem radius_eq_width (P : ℕ) (N : ℝ) (i : ℕ × ℕ) (_hP : 0 < P) :
    radius P N i = width (N / (P : ℝ)) i.1 := by
  unfold radius width
  rw [← mul_div_assoc, one_div_div]

/-- The reduced major arcs sample distinct residues at each modulus.
Discarding the coprimality restriction can only increase total energy. -/
theorem reduced_energy_le (P : ℕ) (N : ℝ) (hP : 0 < P) (hN : 0 < N) (F : Data) :
    (∑ i ∈ reduced P, intervalEnergy (radius P N i) (slice F i)) ≤
      ∑ q ∈ Icc 1 P, PintzEightPrimitiveEnergy.arcEnergy (N / (P : ℝ)) q F := by
  have hm : ∀ i ∈ reduced P, i.1 ∈ Icc 1 P := fun i hi =>
    mem_Icc.mpr ⟨(mem_reduced.mp hi).1, (mem_reduced.mp hi).2.1⟩
  rw [← sum_fiberwise_of_maps_to hm]
  apply sum_le_sum
  intro q hq
  have hq0 : q ≠ 0 := (show 0 < q from (mem_Icc.mp hq).1).ne'
  let : NeZero q := ⟨hq0⟩
  let s := (reduced P).filter (fun i => i.1 = q)
  let c : ℕ × ℕ → ZMod q := fun i => i.2
  have hiq (i) (hi : i ∈ s) : i.1 = q := (mem_filter.mp hi).2
  have hil (i) (hi : i ∈ s) : i.2 < q :=
    hiq i hi ▸ (mem_reduced.mp (mem_filter.mp hi).1).2.2.1
  have hinj : Set.InjOn c (↑s : Set (ℕ × ℕ)) := by
    intro i hi j hj h
    have h' := congrArg ZMod.val h
    dsimp [c] at h'
    rw [ZMod.val_natCast_of_lt (hil i hi), ZMod.val_natCast_of_lt (hil j hj)] at h'
    exact Prod.ext ((hiq i hi).trans (hiq j hj).symm) h'
  let E (a : ZMod q) := intervalEnergy (width (N/(P:ℝ)) q) (residue q F a)
  change (∑ i ∈ s, _) ≤ _
  calc
    _ = ∑ i ∈ s, E (c i) := by
      apply sum_congr rfl
      rintro ⟨r,a⟩ hi
      have hr : r = q := hiq _ hi
      subst r
      rw [radius_eq_width P N (q,a) hP]
      have hs : slice F (q,a) = residue q F (a : ZMod q) := by
        funext x
        unfold slice
        exact dite_eq_right hq0
      rw [hs]
    _ = ∑ a ∈ s.image c, E a := (sum_image hinj).symm
    _ ≤ ∑ a : ZMod q, E a := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro a _ _
      apply intervalIntegral.integral_nonneg
      · have hW : 0 ≤ width (N/(P:ℝ)) q := by unfold width; positivity
        linarith
      · exact fun _ _ => sq_nonneg _
    _ = _ := by
      rw [PintzEightPrimitiveEnergy.arcEnergy, dite_eq_right hq0]
      rfl

#print axioms continuous_slice
#print axioms reduced_energy_le
end PintzReducedArcEnergy
