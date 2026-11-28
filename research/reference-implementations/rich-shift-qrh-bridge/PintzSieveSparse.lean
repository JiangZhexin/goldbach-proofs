import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Interval
import Lean.Elab.Tactic.Omega

open Finset
open scoped BigOperators
namespace PintzSieveToHybrid

private def castNatInt : ℕ ↪ ℤ := ⟨fun n => n, Nat.cast_injective⟩

/-- Reindex an inclusive natural interval as the corresponding integer
half-open interval. Widening to length L+1 includes the left endpoint. -/
theorem image_Icc (m L : ℕ) :
    (Icc m (m+L)).map castNatInt = Ioc ((m:ℤ)-1) ((m:ℤ)-1+((L+1:ℕ):ℤ)) := by
  ext n
  rw [mem_map, mem_Ioc]
  constructor
  · rintro ⟨k,hk,rfl⟩
    change (m:ℤ)-1 < (k:ℤ) ∧ (k:ℤ) ≤ _
    obtain ⟨hl,hu⟩ := mem_Icc.mp hk
    omega
  · intro ⟨hl,hu⟩
    have hn : 0 ≤ n := by omega
    refine ⟨n.toNat, mem_Icc.mpr ⟨?_,?_⟩,?_⟩
    · omega
    · omega
    · exact Int.toNat_of_nonneg hn

noncomputable def sparse (v : Finset ℕ) (a : ℕ → ℂ) (n : ℤ) : ℂ :=
  if n.toNat ∈ v then a n.toNat else 0

/-- Restricting an arithmetic progression sieve to a sparse support is
accomplished by extending with zeros; no spurious integer indices enter. -/
theorem sparse_character_sum (m L q : ℕ) (χ : DirichletCharacter ℂ q)
    (v : Finset ℕ) (a : ℕ → ℂ) (hv : v ⊆ Icc m (m+L)) :
    (∑ n ∈ Ioc ((m:ℤ)-1) ((m:ℤ)-1+((L+1:ℕ):ℤ)), sparse v a n * χ n) =
      ∑ n ∈ v, a n * χ (n : ZMod q) := by
  rw [← image_Icc, sum_map]
  have hfilter : (Icc m (m+L)).filter (· ∈ v) = v := by
    ext n
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hv h,h⟩⟩
  conv_rhs => rw [← hfilter, sum_filter]
  apply sum_congr rfl
  intro n hn
  by_cases h : n ∈ v <;> simp [castNatInt, sparse, h]

theorem sparse_energy (m L : ℕ)
    (v : Finset ℕ) (a : ℕ → ℂ) (hv : v ⊆ Icc m (m+L)) :
    (∑ n ∈ Ioc ((m:ℤ)-1) ((m:ℤ)-1+((L+1:ℕ):ℤ)), ‖sparse v a n‖ ^ 2) =
      ∑ n ∈ v, ‖a n‖ ^ 2 := by
  rw [← image_Icc, sum_map]
  have hfilter : (Icc m (m+L)).filter (· ∈ v) = v := by
    ext n
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hv h,h⟩⟩
  conv_rhs => rw [← hfilter, sum_filter]
  apply sum_congr rfl
  intro n hn
  by_cases h : n ∈ v <;> simp [castNatInt, sparse,h]


#print axioms sparse_character_sum
#print axioms sparse_energy
end PintzSieveToHybrid
