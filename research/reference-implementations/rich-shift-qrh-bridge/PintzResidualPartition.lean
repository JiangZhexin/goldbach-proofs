import PintzResidualGallagher

open Finset PintzResidualGallagher

namespace PintzResidualPartition

/-- Terms on the left or on the critical line; all are absorbed pointwise. -/
noncomputable def left {ι : Type*} (S : Finset ι) (ρ : ι → ℂ) : Finset ι := by
  classical exact S.filter (fun i => (ρ i).re ≤ 1/2)

/-- Terms retained in the main model close to the line Re z=1. -/
noncomputable def near {ι : Type*} (S : Finset ι) (ρ : ι → ℂ) (b : ℝ) : Finset ι := by
  classical exact S.filter (fun i => 1-b < (ρ i).re)

/-- The right-half terms treated by L² and density. -/
noncomputable def far {ι : Type*} (S : Finset ι) (ρ : ι → ℂ) (b : ℝ) : Finset ι := by
  classical exact S.filter (fun i => 1/2 < (ρ i).re ∧ (ρ i).re ≤ 1-b)

theorem mem_left {ι : Type*} (S : Finset ι) (ρ : ι → ℂ) (i : ι) :
    i ∈ left S ρ ↔ i ∈ S ∧ (ρ i).re ≤ 1/2 := by
  classical
  exact mem_filter

theorem mem_near {ι : Type*} (S : Finset ι) (ρ : ι → ℂ) (b : ℝ) (i : ι) :
    i ∈ near S ρ b ↔ i ∈ S ∧ 1-b < (ρ i).re := by
  classical
  exact mem_filter

theorem mem_far {ι : Type*} (S : Finset ι) (ρ : ι → ℂ) (b : ℝ) (i : ι) :
    i ∈ far S ρ b ↔ i ∈ S ∧ 1/2 < (ρ i).re ∧ (ρ i).re ≤ 1-b := by
  classical
  exact mem_filter

theorem split_primitive {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ) (m : ι → ℝ)
    {b : ℝ} (hb : b ≤ 1/2) (t : ℝ) :
    zeroPrimitive S ρ c m t =
      zeroPrimitive (left S ρ) ρ c m t +
      zeroPrimitive (near S ρ b) ρ c m t +
      zeroPrimitive (far S ρ b) ρ c m t := by
  classical
  let f (i : ι) := (m i:ℂ)*c i*((t:ℂ)^(ρ i)/(ρ i))
  let U := S.filter (fun i => ¬ (ρ i).re ≤ 1/2)
  have hU1 : U.filter (fun i => 1-b < (ρ i).re) = near S ρ b := by
    ext i
    simp only [U, mem_filter, mem_near]
    constructor
    · rintro ⟨⟨hS,_⟩,hp⟩
      exact ⟨hS,hp⟩
    · rintro ⟨hS,hp⟩
      exact ⟨⟨hS,by linarith⟩,hp⟩
  have hU2 : U.filter (fun i => ¬ 1-b < (ρ i).re) = far S ρ b := by
    ext i
    simp only [U, mem_filter, mem_far, not_le, not_lt]
    tauto
  have hS := sum_filter_add_sum_filter_not S (fun i => (ρ i).re ≤ 1/2) f
  have hU := sum_filter_add_sum_filter_not U (fun i => 1-b < (ρ i).re) f
  rw [hU1,hU2] at hU
  change (∑ i ∈ S, f i) = (∑ i ∈ left S ρ, f i) +
    (∑ i ∈ near S ρ b, f i) + (∑ i ∈ far S ρ b, f i)
  change (∑ i ∈ left S ρ, f i) + (∑ i ∈ U, f i) = (∑ i ∈ S, f i) at hS
  rw [← hS, ← hU, add_assoc]

noncomputable def retained {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ) (m : ι → ℝ)
    (b : ℝ) (pole : ℂ) (t : ℝ) : ℂ :=
  pole*(t:ℂ) - zeroPrimitive (near S ρ b) ρ c m t

/-- When the left-half primitive is bounded separately, the original
sharp interval formula has exactly the remainder required for Gallagher. -/
theorem residual_error {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ) (m : ι → ℝ)
    {b x y E L : ℝ} (hb : b ≤ 1/2) (pole primeSum : ℂ)
    (hsharp : ‖primeSum - pole*((y:ℂ)-(x:ℂ)) +
      (zeroPrimitive S ρ c m y-zeroPrimitive S ρ c m x)‖ ≤ E)
    (hleft : ‖zeroPrimitive (left S ρ) ρ c m y-zeroPrimitive (left S ρ) ρ c m x‖ ≤ L) :
    ‖primeSum - (retained S ρ c m b pole y-retained S ρ c m b pole x) +
      (zeroPrimitive (far S ρ b) ρ c m y-zeroPrimitive (far S ρ b) ρ c m x)‖ ≤ E+L := by
  rw [split_primitive S ρ c m hb x,split_primitive S ρ c m hb y] at hsharp
  let A := zeroPrimitive (left S ρ) ρ c m
  let B := zeroPrimitive (near S ρ b) ρ c m
  let F := zeroPrimitive (far S ρ b) ρ c m
  change ‖primeSum-(pole*(y:ℂ)-B y-(pole*(x:ℂ)-B x))+(F y-F x)‖ ≤ E+L
  rw [show primeSum-(pole*(y:ℂ)-B y-(pole*(x:ℂ)-B x))+(F y-F x) =
      (primeSum-pole*((y:ℂ)-(x:ℂ))+(A y+B y+F y-(A x+B x+F x))) - (A y-A x) by ring]
  exact (norm_sub_le _ _).trans (add_le_add hsharp hleft)

theorem retained_rounding {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ) (m : ι → ℕ)
    {b x : ℝ} (hx : 1 ≤ x) (pole : ℂ)
    (hs : ∀ i ∈ S, ρ i ≠ 0) (hre : ∀ i ∈ S, (ρ i).re ≤ 1) :
    ‖retained S ρ c (fun i => (m i:ℝ)) b pole x -
      retained S ρ c (fun i => (m i:ℝ)) b pole (⌊x⌋₊:ℕ)‖ ≤
      ‖pole‖+∑ i ∈ near S ρ b, (m i:ℝ)*‖c i‖ := by
  let D := zeroPrimitive (near S ρ b) ρ c (fun i => (m i:ℝ))
  change ‖(pole*(x:ℂ)-D x)-(pole*((⌊x⌋₊:ℕ):ℂ)-D (⌊x⌋₊:ℕ))‖ ≤ _
  rw [show (pole*(x:ℂ)-D x)-(pole*((⌊x⌋₊:ℕ):ℂ)-D (⌊x⌋₊:ℕ)) =
    pole*((x:ℂ)-((⌊x⌋₊:ℕ):ℂ)) - (D x-D (⌊x⌋₊:ℕ)) by ring]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · rw [norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le (by linarith)))]
    linarith [Nat.lt_floor_add_one x]
  · have h := PintzDiscreteZeroModel.weighted_endpoint_rounding (near S ρ b) ρ c m hx
      (fun i hi => hs i ((mem_near S ρ b i).1 hi).1)
      (fun i hi => hre i ((mem_near S ρ b i).1 hi).1)
    simpa only [D,zeroPrimitive,Complex.ofReal_natCast] using h

#print axioms residual_error
#print axioms retained_rounding
end PintzResidualPartition
