import PintzResidualDensityGroups

open Finset PintzSieveToHybrid PintzConductorReindex PintzWeilPrimitivePrimeWindow
open PintzFiniteDyadicAggregation

namespace PintzResidualDensityGroups

noncomputable def mass {p : ℕ} {j : CharIndex} (hj : j ∈ family p)
    (N b : ℝ) (l : ℕ × ℕ) : ℝ :=
  ((2:ℝ)^l.1)⁻¹ * N^(-2*PintzResidualLabels.edge N l.2) *
    ∑ z ∈ subBlock hj N b l,
      (((zeroConfig (PintzConductorReindex.mem_family.mp hj).2).mult z : ℕ):ℝ)

theorem global_mass :
    ∃ D : ℝ → ℝ, (∀ b, 0 ≤ D b) ∧ ∀ {N b : ℝ} {p : ℕ},
      4 ≤ N → (p:ℝ) ≤ N^(21/100:ℝ) → 0 < b →
    (∑ j ∈ (family p).attach, ∑ μ ∈ range (Nat.log 2 ⌊N⌋₊+1),
      ∑ ν ∈ range (⌈Real.log N/2⌉₊+1), mass j.2 N b (μ,ν)) ≤
      D b * (1+Real.log N)^13 * N^(-b/40) := by
  classical
  obtain ⟨D,hD,hG⟩ := group_bound
  let C : ℝ := 1 / Real.log 2 + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨fun b => C*C*(5/2)*D b, fun b => by positivity [hD b],?_⟩
  intro N b p hN hp hb
  let U := range (Nat.log 2 ⌊N⌋₊+1)
  let V := range (⌈Real.log N/2⌉₊+1)
  let K := range (Nat.log 2 p+1)
  let a (μ ν : ℕ) : ℝ := ((2:ℝ)^μ)⁻¹ * N^(-2*PintzResidualLabels.edge N ν)
  let F (k : ℕ) (j : CharIndex) (μ ν : ℕ) : ℝ :=
    a μ ν * ∑ z ∈ group (p:=p) N b k (μ,ν) j, (analyticOrderNatAt j.2.LFunction z : ℝ)
  have hF (k j μ ν) : 0 ≤ F k j μ ν := by dsimp [F,a]; positivity
  have hcanon {j : CharIndex} (hj : j ∈ family p) (μ ν : ℕ) :
      mass hj N b (μ,ν) = F (conductorLabel j) j μ ν := by
    have hm : j ∈ conductorBlock p (conductorLabel j) := mem_filter.mpr ⟨hj,rfl⟩
    dsimp [mass,F,a,group]
    rw [dite_eq_left hm, Finset.sum_map]
    congr 1
    apply sum_congr rfl
    intro z _
    rw [PintzPrimitiveCatalogueLocal.mult_eq_analyticOrderNatAt]
    rfl
  have hcanonSum : (∑ j ∈ (family p).attach, ∑ μ ∈ U, ∑ ν ∈ V, mass j.2 N b (μ,ν)) =
      ∑ j ∈ family p, ∑ μ ∈ U, ∑ ν ∈ V, F (conductorLabel j) j μ ν := by
    rw [← sum_attach (family p) (fun j => ∑ μ ∈ U, ∑ ν ∈ V, F (conductorLabel j) j μ ν)]
    exact sum_congr rfl (fun j _ => sum_congr rfl (fun μ _ => sum_congr rfl (fun ν _ => hcanon j.2 μ ν)))
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hlog := PintzResidualLabels.log_ge_one hN
  have hpN : p ≤ ⌊N⌋₊ := by
    apply Nat.le_floor
    exact hp.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (21/100:ℝ) ≤ 1))
  have hcardU : (U.card:ℝ) ≤ C*(1+Real.log N)^1 := by
    have hfloor : 1 ≤ ⌊N⌋₊ := Nat.le_floor (by exact_mod_cast hN1)
    have hpow : (2:ℝ)^(Nat.log 2 ⌊N⌋₊) ≤ N := by
      have H := Nat.pow_log_le_self 2 (by omega : ⌊N⌋₊ ≠ 0)
      exact (by exact_mod_cast H : (2:ℝ)^(Nat.log 2 ⌊N⌋₊) ≤ (⌊N⌋₊:ℝ)).trans
        (Nat.floor_le hNp.le)
    have H := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at H
    have Hp := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr H
    simp only [U, C, card_range, Nat.cast_add, Nat.cast_one, pow_one, add_mul,
      div_mul_eq_mul_div, one_mul]
    rw [add_div]
    have x : 0 ≤ 1 / Real.log 2 := by positivity
    linarith
  have hcardK : (K.card:ℝ) ≤ C*(1+Real.log N)^1 := by
    have hsub : K ⊆ U := range_mono (Nat.succ_le_succ (Nat.log_mono_right hpN))
    exact (by exact_mod_cast card_le_card hsub : (K.card:ℝ) ≤ U.card).trans hcardU
  have hcardV : (V.card:ℝ) ≤ (5/2:ℝ)*(1+Real.log N)^1 := by
    rw [pow_one]
    exact (horizontal_range_count hlog).trans (by linarith)
  let G (k μ ν : ℕ) : ℝ := ∑ j ∈ family (min p (2*2^k)), F k j μ ν
  have hlocal (k μ ν : ℕ) : G k μ ν ≤ D b*(1+Real.log N)^10*N^(-b/40) := by
    let h := PintzResidualLabels.edge N ν
    by_cases hv : b ≤ h
    · have H := hG hN hp hb k (μ,ν)
      dsimp only at H
      have H' : G k μ ν ≤ D b*(1+Real.log N)^10*N^(-h/40) := by
        simpa only [G, F, ← mul_sum, a, h] using H
      exact H'.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by positivity [hD b]))
    · have he : ∀ j ∈ family (min p (2*2^k)), group (p:=p) N b k (μ,ν) j = ∅ := by
        intro j hj
        apply not_nonempty_iff_eq_empty.mp
        rintro ⟨z,hz⟩
        have H := mem_group hz
        have hh := PintzResidualLabels.horizontal (by linarith : 1 < N) hb.le
          H.2.2.1 H.2.2.2.1 p (j.1+1:ℕ)
        dsimp only at hh
        rw [H.2.2.2.2.2] at hh
        exact hv hh.2.1
      have H0 : G k μ ν = 0 := by
        apply sum_eq_zero
        intro j hj
        simp [F, he j hj]
      rw [H0]
      positivity [hD b]
  rw [hcanonSum]
  refine (reindex_three_le p U V F hF).trans ?_
  exact aggregate_three K U V G (L := 1+Real.log N) (A := N^(-b/40))
    (k₁ := 1) (k₂ := 1) (k₃ := 1) (k := 10)
    (by positivity) hC hC (by norm_num) (hD b) (by positivity)
    hcardK hcardU hcardV (fun k _ μ _ ν _ => hlocal k μ ν)

#print axioms global_mass
end PintzResidualDensityGroups
