import PintzEightGauss

noncomputable section
open Finset Set
open scoped Classical
namespace PintzMajorArcGeometry

def reduced (P : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 P).product (range P)).filter (fun i => i.2 < i.1 ∧ i.2.Coprime i.1)

def center (i : ℕ × ℕ) : ℝ := (i.2 : ℝ) / (i.1 : ℝ)
def radius (P : ℕ) (N : ℝ) (i : ℕ × ℕ) : ℝ := (P : ℝ) / ((i.1 : ℝ) * N)
def arc (P : ℕ) (N : ℝ) (i : ℕ × ℕ) : Set ℝ :=
  Ioc (center i - radius P N i) (center i + radius P N i)

theorem mem_reduced {P : ℕ} {i : ℕ × ℕ} :
    i ∈ reduced P ↔ 0 < i.1 ∧ i.1 ≤ P ∧ i.2 < i.1 ∧ i.2.Coprime i.1 := by
  rcases i with ⟨q,a⟩
  unfold reduced
  rw [Finset.mem_filter]
  have hh : (q,a) ∈ (Finset.Icc 1 P).product (Finset.range P) ↔
      q ∈ Finset.Icc 1 P ∧ a ∈ Finset.range P := Finset.mem_product (p := (q,a))
  rw [hh, Finset.mem_Icc, Finset.mem_range]
  omega

private theorem rat_denom_num {q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    (((a : ℚ) / q).den = q) ∧ (((a : ℚ) / q).num = (a : ℤ)) := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hc : Nat.Coprime (a : ℤ).natAbs (q : ℤ).natAbs := ha
  constructor
  · exact Int.ofNat_inj.mp (by simpa using Rat.den_div_eq_of_coprime hq' hc)
  · simpa using Rat.num_div_eq_of_coprime hq' hc

theorem center_inj {P : ℕ} {i j : ℕ × ℕ} (hi : i ∈ reduced P) (hj : j ∈ reduced P)
    (h : center i = center j) : i = j := by
  obtain ⟨hi, -, -, hci⟩ := mem_reduced.mp hi
  obtain ⟨hj, -, -, hcj⟩ := mem_reduced.mp hj
  have he : ((i.2 : ℚ)/i.1) = ((j.2 : ℚ)/j.1) := Rat.cast_injective (α := ℝ) (by
    push_cast
    exact h)
  obtain ⟨hi₁, hi₂⟩ := rat_denom_num hi hci
  obtain ⟨hj₁, hj₂⟩ := rat_denom_num hj hcj
  exact Prod.ext (hi₁ ▸ hj₁ ▸ congrArg Rat.den he)
    (Int.ofNat_inj.mp (hi₂ ▸ hj₂ ▸ congrArg Rat.num he))

theorem separated {P : ℕ} {N : ℝ} (hPN : 2*(P:ℝ)^2 < N)
    {i j : ℕ × ℕ} (hi : i ∈ reduced P) (hj : j ∈ reduced P)
    (hij : i ≠ j) : radius P N i + radius P N j < |center i - center j| := by
  have hi' := mem_reduced.mp hi
  have hj' := mem_reduced.mp hj
  have hN : 0 < N := by nlinarith [sq_nonneg (P:ℝ)]
  have hi0 : (0:ℝ) < i.1 := by exact_mod_cast hi'.1
  have hj0 : (0:ℝ) < j.1 := by exact_mod_cast hj'.1
  have hil : (i.1:ℝ) ≤ P := by exact_mod_cast hi'.2.1
  have hjl : (j.1:ℝ) ≤ P := by exact_mod_cast hj'.2.1
  have hCross : (i.2 : ℤ)*j.1-(j.2 : ℤ)*i.1 ≠ 0 := by
    intro h
    apply hij (center_inj hi hj ?_)
    unfold center
    apply (div_eq_div_iff hi0.ne' hj0.ne').mpr
    exact_mod_cast (sub_eq_zero.mp h)
  have hc : (1:ℝ) ≤ |(i.2:ℝ)*j.1-(j.2:ℝ)*i.1| := by
    exact_mod_cast (show (1:ℤ) ≤ |(i.2:ℤ)*j.1-(j.2:ℤ)*i.1| from
      abs_pos.mpr hCross)
  have hrad : radius P N i + radius P N j < 1 / ((i.1:ℝ)*(j.1:ℝ)) := by
    unfold radius
    apply (lt_div_iff₀ (mul_pos hi0 hj0)).mpr
    have hEq : ((P:ℝ)/((i.1:ℝ)*N)+(P:ℝ)/((j.1:ℝ)*N)) *((i.1:ℝ)*(j.1:ℝ)) =
      ((P:ℝ)*((i.1:ℝ)+(j.1:ℝ)))/N := by field_simp; ring
    rw [hEq]
    apply (div_lt_iff₀ hN).mpr
    nlinarith [mul_nonneg (show 0 ≤ (P:ℝ) by positivity) (sub_nonneg.mpr hil),
      mul_nonneg (show 0 ≤ (P:ℝ) by positivity) (sub_nonneg.mpr hjl)]
  apply hrad.trans_le
  unfold center
  rw [div_sub_div _ _ hi0.ne' hj0.ne', abs_div, abs_of_pos (mul_pos hi0 hj0)]
  exact div_le_div_of_nonneg_right (by simpa [mul_comm (j.2 : ℝ)] using hc) (by positivity)

theorem arcs_disjoint {P : ℕ} {N : ℝ} (hPN : 2*(P:ℝ)^2 < N)
    {i j : ℕ × ℕ} (hi : i ∈ reduced P) (hj : j ∈ reduced P)
    (hij : i ≠ j) : Disjoint (arc P N i) (arc P N j) := by
  refine Set.disjoint_left.mpr ?_
  intro t ht hs
  have H := separated hPN hi hj hij
  change center i - radius P N i < t ∧ t ≤ center i + radius P N i at ht
  change center j - radius P N j < t ∧ t ≤ center j + radius P N j at hs
  rcases le_total (center i) (center j) with h|h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at H
    linarith [ht.2,hs.1]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at H
    linarith [hs.2,ht.1]

theorem arcs_contained {P : ℕ} {N : ℝ} (hP : 1 ≤ P) (hPN : 2*(P:ℝ)^2 < N)
    {i : ℕ × ℕ} (hi : i ∈ reduced P) :
    arc P N i ⊆ Ioc (-(P:ℝ)/N) (1-(P:ℝ)/N) := by
  obtain ⟨hi0, hil, ha, _⟩ := mem_reduced.mp hi
  have hN : 0 < N := by nlinarith [sq_nonneg (P:ℝ)]
  have hi0' : (0:ℝ) < i.1 := by exact_mod_cast hi0
  have hi1 : (1:ℝ) ≤ i.1 := by exact_mod_cast hi0
  have hl : (i.1 : ℝ) ≤ P := by exact_mod_cast hil
  have hP' : (1:ℝ) ≤ P := by exact_mod_cast hP
  have ha' : (i.2 : ℝ)+1 ≤ i.1 := by exact_mod_cast ha
  apply Set.Ioc_subset_Ioc
  · rw [neg_div]
    have hrad : radius P N i ≤ (P:ℝ)/N := by
      unfold radius
      apply div_le_div_of_nonneg_left (by positivity) hN
      nlinarith
    have hc : 0 ≤ center i := by unfold center; positivity
    linarith
  · have hδ : radius P N i + (P:ℝ)/N ≤ 1/(i.1:ℝ) := by
      unfold radius
      apply (le_div_iff₀ hi0').mpr
      have hEq : ((P:ℝ)/((i.1:ℝ)*N)+(P:ℝ)/N)*(i.1:ℝ) = (P:ℝ)*(1+i.1)/N := by field_simp
      rw [hEq]
      apply (div_le_iff₀ hN).mpr
      nlinarith [mul_nonneg (show 0 ≤ (P:ℝ) by positivity) (sub_nonneg.mpr hl),
        mul_nonneg (show 0 ≤ (P:ℝ) by positivity) (sub_nonneg.mpr hP')]
    have hcent : center i ≤ 1-1/(i.1:ℝ) := by
      unfold center
      calc
        _ ≤ ((i.1:ℝ)-1)/(i.1:ℝ) := div_le_div_of_nonneg_right (by linarith) hi0'.le
        _ = _ := by rw [sub_div, div_self hi0'.ne']
    linarith

/-- Reindex the geometric pair sum to the nested arithmetic sum over reduced residues. -/
theorem sum_reduced {R : Type*} [AddCommMonoid R] (P : ℕ) (F : ℕ → ℕ → R) :
    (∑ i ∈ reduced P, F i.1 i.2) =
      ∑ q ∈ Finset.Icc 1 P, ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), F q a := by
  classical
  unfold reduced
  rw [Finset.sum_filter]
  change (∑ i ∈ (Finset.Icc 1 P) ×ˢ (Finset.range P),
      if i.2 < i.1 ∧ i.2.Coprime i.1 then F i.1 i.2 else 0) = _
  rw [Finset.sum_product]
  apply sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter]
  congr 1
  ext a
  have hq' := (Finset.mem_Icc.mp hq).2
  simp only [mem_filter, Finset.mem_range]
  omega

#print axioms sum_reduced
#print axioms arcs_disjoint
#print axioms arcs_contained
end PintzMajorArcGeometry
