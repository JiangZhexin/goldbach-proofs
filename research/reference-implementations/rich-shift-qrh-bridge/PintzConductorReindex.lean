import PintzSieveToHybrid

open Finset PintzSieveToHybrid
open scoped BigOperators
namespace PintzConductorReindex

abbrev CharIndex := Σ k : ℕ, DirichletCharacter ℂ (k+1)

def conductorLabel (j : CharIndex) : ℕ := Nat.log 2 (j.1+1)

noncomputable def conductorBlock (P k : ℕ) : Finset CharIndex :=
  (family P).filter (fun j => conductorLabel j = k)

theorem conductorLabel_spec (j : CharIndex) :
    2 ^ conductorLabel j ≤ j.1+1 ∧ j.1+1 < 2 * 2 ^ conductorLabel j := by
  unfold conductorLabel
  exact ⟨Nat.pow_log_le_self 2 (by omega),
    by simpa [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) (j.1+1)⟩

theorem mem_family {j : CharIndex} {P : ℕ} :
    j ∈ family P ↔ j.1 + 1 ≤ P ∧ j.2.IsPrimitive := by
  simp only [family, mem_sigma, mem_range, mem_filter, mem_univ, true_and]
  rw [Nat.succ_le_iff]

theorem conductorBlock_subset (P k : ℕ) :
    conductorBlock P k ⊆ family (min P (2 * 2 ^ k)) := by
  intro j hj
  obtain ⟨hP, hk⟩ := mem_filter.mp hj
  obtain ⟨hle, hprim⟩ := mem_family.mp hP
  have hb := (conductorLabel_spec j).2
  rw [hk] at hb
  exact mem_family.mpr ⟨le_min hle hb.le, hprim⟩

theorem conductorLabel_mem_range {j : CharIndex} {P : ℕ} (hj : j ∈ family P) :
    conductorLabel j ∈ range (Nat.log 2 P + 1) := by
  have h := Nat.log_mono_right (b := 2) (mem_family.mp hj).1
  change Nat.log 2 (j.1+1) ∈ range (Nat.log 2 P+1)
  exact mem_range.mpr (by omega)

theorem reindex {A : Type*} [AddCommMonoid A] (P : ℕ)
    (F : ℕ → CharIndex → A) :
    (∑ j ∈ family P, F (conductorLabel j) j) =
      ∑ k ∈ range (Nat.log 2 P+1), ∑ j ∈ conductorBlock P k, F k j := by
  classical
  calc
    _ = ∑ k ∈ range (Nat.log 2 P+1), ∑ j ∈ conductorBlock P k,
         F (conductorLabel j) j :=
      (sum_fiberwise_of_maps_to (fun j hj => conductorLabel_mem_range hj) _).symm
    _ = _ := sum_congr rfl (fun k _ =>
      sum_congr rfl (fun j hj => by rw [(mem_filter.mp hj).2]))

theorem block_sum_le (P k : ℕ) (F : CharIndex → ℝ)
    (hF : ∀ j ∈ family (min P (2 * 2 ^ k)), 0 ≤ F j) :
    (∑ j ∈ conductorBlock P k, F j) ≤ ∑ j ∈ family (min P (2 * 2 ^ k)), F j :=
  sum_le_sum_of_subset_of_nonneg (conductorBlock_subset P k) (fun j hj _ => hF j hj)

/-- Common finite horizontal/height ranges can be fixed from the start;
terms are exchanged rather than overcounted until each conductor block is
enlarged to an initial family. -/
theorem reindex_three_le {μ ν : Type*} (P : ℕ) (M : Finset μ) (V : Finset ν)
    (F : ℕ → CharIndex → μ → ν → ℝ) (hF : ∀ k j m v, 0 ≤ F k j m v) :
    (∑ j ∈ family P, ∑ m ∈ M, ∑ v ∈ V, F (conductorLabel j) j m v) ≤
      ∑ k ∈ range (Nat.log 2 P+1), ∑ m ∈ M, ∑ v ∈ V,
        ∑ j ∈ family (min P (2 * 2 ^ k)), F k j m v := by
  rw [reindex P (fun k j => ∑ m ∈ M, ∑ v ∈ V, F k j m v)]
  apply sum_le_sum
  intro k hk
  rw [sum_comm (s := conductorBlock P k) (t := M)]
  apply sum_le_sum
  intro m hm
  rw [sum_comm (s := conductorBlock P k) (t := V)]
  exact sum_le_sum (fun v _ => block_sum_le P k (fun j => F k j m v) (fun j _ => hF k j m v))

#print axioms conductorLabel_spec
#print axioms conductorBlock_subset
#print axioms reindex
#print axioms reindex_three_le
end PintzConductorReindex
