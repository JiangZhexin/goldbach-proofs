import PintzExplicitRounding
import PintzGallagherReal
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Nat

open Finset

namespace PintzDiscreteZeroModel

/-- A discrete model may be formed by increments of the continuous zero
primitive. This gives exact telescoping on the integer Gallagher windows. -/
def increment (F : ℝ → ℂ) (n : ℕ) : ℂ := F n - F ((n:ℝ)-1)

theorem sum_increments (F : ℝ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, increment F n = F b - F a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b h ih =>
      have hI : Ioc a (b+1) = insert (b+1) (Ioc a b) := by
        ext n
        simp only [mem_Ioc,mem_insert]
        omega
      rw [hI,sum_insert (by simp),ih,increment]
      push_cast
      ring

theorem filter_clipped (u v x Y : ℝ) (hu : 0 ≤ u) :
    ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) ≤ x+Y)) =
      Ioc ⌊max u x⌋₊ ⌊min v (x+Y)⌋₊ := by
  ext n
  simp only [mem_filter, mem_Ioc]
  have hm : 0 ≤ max u x := hu.trans (le_max_left _ _)
  rw [Nat.floor_lt hu, Nat.floor_lt hm, max_lt_iff]
  by_cases hv : 0 ≤ v
  · by_cases hY : 0 ≤ x+Y
    · rw [Nat.le_floor_iff hv, Nat.le_floor_iff (le_min hv hY), le_min_iff]
      aesop
    · have hneg : min v (x+Y) ≤ 0 := (min_le_right _ _).trans (lt_of_not_ge hY).le
      rw [Nat.floor_of_nonpos hneg]
      constructor
      · rintro ⟨_,_,hxY⟩
        exact False.elim (hY ((Nat.cast_nonneg (α:=ℝ) n).trans hxY))
      · rintro ⟨⟨hun,_⟩,hn⟩
        have hz : n = 0 := Nat.le_zero.mp hn
        simp [hz] at hun
        linarith
  · have hv' : v ≤ 0 := (lt_of_not_ge hv).le
    rw [Nat.floor_of_nonpos hv',Nat.floor_of_nonpos ((min_le_left _ _).trans hv')]
    constructor
    · rintro ⟨⟨hun,hn⟩,_⟩
      have hz : n = 0 := Nat.le_zero.mp hn
      simp [hz] at hun
      linarith
    · rintro ⟨⟨hun,_⟩,hn⟩
      have hz : n = 0 := Nat.le_zero.mp hn
      simp [hz] at hun
      linarith

/-- The zero primitive moves by at most its coefficient norm between
adjacent real endpoints at least one, uniformly in the ordinate. -/
theorem endpoint_rounding {s c : ℂ} (hs : s ≠ 0) (hre : s.re ≤ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖c*((x:ℂ)^s/s - ((⌊x⌋₊:ℕ):ℂ)^s/s)‖ ≤ ‖c‖ := by
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  have hf : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hF : 1 ≤ (⌊x⌋₊ : ℝ) := by
    exact_mod_cast Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hx)
  have h := PintzExplicitRounding.kernel_lipschitz hF hf hs hre
  rw [Complex.ofReal_natCast] at h
  exact h.trans (by linarith [Nat.lt_floor_add_one x])

/-- Exact discrete window to clipped continuous zero primitive, with only
the two one-unit endpoint displacements left as a bounded error. -/
theorem clipped_increments {F : ℝ → ℂ} {u v x Y E : ℝ}
    (hu : 1 ≤ u) (hE : 0 ≤ E)
    (hF : ∀ t, 1 ≤ t → ‖F t - F (⌊t⌋₊:ℕ)‖ ≤ E) :
    ‖(∑ n ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) ≤ x+Y),
      increment F n) -
      (if max u x ≤ min v (x+Y) then F (min v (x+Y)) - F (max u x) else 0)‖ ≤ 2*E := by
  rw [filter_clipped u v x Y (by linarith)]
  split_ifs with h
  · rw [sum_increments F (Nat.floor_mono h)]
    have hL : 1 ≤ max u x := hu.trans (le_max_left _ _)
    have hU : 1 ≤ min v (x+Y) := hL.trans h
    let A : ℂ := F (min v (x+Y)) - F (⌊min v (x+Y)⌋₊:ℕ)
    let B : ℂ := F (max u x) - F (⌊max u x⌋₊:ℕ)
    change ‖_ - _‖ ≤ _
    rw [show (F (⌊min v (x+Y)⌋₊:ℕ) - F (⌊max u x⌋₊:ℕ)) -
      (F (min v (x+Y)) - F (max u x)) = B-A by dsimp [A,B]; ring]
    exact (norm_sub_le B A).trans (by simpa [two_mul] using add_le_add (hF _ hL) (hF _ hU))
  · have hfl := Nat.floor_mono (le_of_not_ge h)
    rw [Ioc_eq_empty_of_le hfl]
    simp [hE]

theorem weighted_endpoint_rounding {ι : Type*} (S : Finset ι)
    (s c : ι → ℂ) (m : ι → ℕ) {t : ℝ} (ht : 1 ≤ t)
    (hs : ∀ i ∈ S, s i ≠ 0) (hre : ∀ i ∈ S, (s i).re ≤ 1) :
    ‖(∑ i ∈ S, (m i:ℂ)*c i*((t:ℂ)^(s i)/(s i))) -
      (∑ i ∈ S, (m i:ℂ)*c i*((((⌊t⌋₊:ℕ):ℂ)^(s i))/(s i)))‖ ≤
      ∑ i ∈ S, (m i:ℝ)*‖c i‖ := by
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
  rw [← mul_sub, mul_assoc, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (endpoint_rounding (hs i hi) (hre i hi) ht) (by positivity)

#print axioms clipped_increments
#print axioms weighted_endpoint_rounding
#print axioms sum_increments
#print axioms filter_clipped
#print axioms endpoint_rounding
end PintzDiscreteZeroModel
