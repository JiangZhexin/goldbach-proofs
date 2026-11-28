import PintzResidualDensityGlobal
import RichShiftSection8Bound263
import PintzUniformDensitySubsets
import PintzResidualLabels
import PintzConductorReindex

open Finset PintzSieveToHybrid PintzConductorReindex PintzWeilPrimitivePrimeWindow
open PintzPrimitiveResidual


namespace RichShiftDensityGroup263
open PintzResidualDensityGroups

def DensityBound : Prop := 
    ∃ D : ℝ → ℝ, (∀ b, 0 ≤ D b) ∧ ∀ {N P R M T b h : ℝ} {Q : ℕ}
      (_hQ : 1 ≤ Q) (_hN : 2 ≤ N) (_hR : 1 ≤ R) (_hRP : R ≤ P) (_hM : 1 ≤ M)
      (_hMN : M ≤ N^(1/2:ℝ)) (_hPN : P ≤ N^(263/1000:ℝ))
      (_hT : 0 ≤ T) (_hQR : (Q:ℝ) ≤ 2*R) (_hTM : T ≤ 4*P*M/R)
      (_hQN : (Q:ℝ) ≤ N) (_hTN : T ≤ N)
      (_hb : 0 < b) (_hbh : b ≤ h) (_hh : h ≤ 1/2)
      (S : PintzDyadicStripCount.Char → Finset ℂ)
      (_hS : ∀ j ∈ family Q, ∀ z ∈ S j,
        j.2.LFunction z = 0 ∧ z.re ∈ Set.Icc (1-h) (1-b) ∧ |z.im| ≤ T),
    M⁻¹ * N^(-2*h) * (∑ j ∈ family Q, ∑ z ∈ S j, (analyticOrderNatAt j.2.LFunction z : ℝ)) ≤
      D b * (1+Real.log N)^10 * N^(-h/40)

theorem group_bound (hDens : DensityBound) :
    ∃ D : ℝ → ℝ, (∀ b, 0 ≤ D b) ∧ ∀ {N b : ℝ} {p : ℕ}
      (_hN : 4 ≤ N) (_hp : (p:ℝ) ≤ N^(263/1000:ℝ)) (_hb : 0 < b)
      (k : ℕ) (l : ℕ × ℕ),
    let M := (2:ℝ)^l.1
    let h := PintzResidualLabels.edge N l.2
    M⁻¹ * N^(-2*h) *
      (∑ j ∈ family (min p (2*2^k)), ∑ z ∈ group (p:=p) N b k l j,
        (analyticOrderNatAt j.2.LFunction z : ℝ)) ≤
      D b * (1+Real.log N)^10 * N^(-h/40) := by
  classical
  obtain ⟨D,hD,hB⟩ := hDens
  refine ⟨D,hD,?_⟩
  intro N b p hN hp hb k l
  dsimp only
  let M := (2:ℝ)^l.1
  let h := PintzResidualLabels.edge N l.2
  let R := (2:ℝ)^k
  let Q := min p (2*2^k)
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hM : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hN1 : 1 ≤ N := by linarith
  have hs : 1 ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hsN : Real.sqrt N ≤ N := by
    nlinarith [Real.sq_sqrt (show 0 ≤ N by linarith)]
  have hQR : (Q:ℝ) ≤ 2*R := by
    dsimp [Q,R]
    exact_mod_cast (min_le_right p (2*2^k))
  have hQN : (Q:ℝ) ≤ N := by
    have HH : (Q:ℝ) ≤ p := by exact_mod_cast (min_le_left p (2*2^k))
    exact HH.trans (hp.trans (by simpa using
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (263/1000:ℝ) ≤ 1)))
  by_cases hh : ∃ j ∈ family Q, (group (p:=p) N b k l j).Nonempty
  · obtain ⟨j,hj,z,hz⟩ := hh
    have hData := mem_group hz
    have hPj := (PintzConductorReindex.mem_family.mp (mem_filter.mp hData.1).1).1
    have hRj : R ≤ (j.1+1:ℕ) := by
      have K := (conductorLabel_spec j).1
      rw [(mem_filter.mp hData.1).2] at K
      dsimp [R]
      exact_mod_cast K
    have hrP : ((j.1+1:ℕ):ℝ) ≤ p := by exact_mod_cast hPj
    have hRP : R ≤ p := hRj.trans hrP
    have hH : 1 ≤ 2*(p:ℝ)/(j.1+1:ℕ) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hHt := PintzHeightBins.bounds hH hs hData.2.2.2.2.1
    have hmj := congrArg Prod.fst hData.2.2.2.2.2
    change PintzHeightBins.idx (2*(p:ℝ)/(j.1+1:ℕ)) z.im = l.1 at hmj
    dsimp only at hHt
    rw [hmj] at hHt
    have hMN : M ≤ N^(1/2:ℝ) := by rw [← Real.sqrt_eq_rpow]; exact hHt.2.1
    have Hh := PintzResidualLabels.horizontal (by linarith : 1 < N) hb.le
      hData.2.2.1 hData.2.2.2.1 p (j.1+1:ℕ)
    dsimp only at Hh
    rw [hData.2.2.2.2.2] at Hh
    let T := min (Real.sqrt N) (4*(p:ℝ)*M/R)
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hQ : 1 ≤ Q := by have := (PintzConductorReindex.mem_family.mp hj).1; omega
    apply hB hQ (by linarith) hR hRP hM hMN hp hT hQR (min_le_right _ _)
      hQN ((min_le_left _ _).trans hsN) hb Hh.2.1 Hh.2.2.1
    intro j' hj' w hw
    have H := mem_group hw
    have hwP : ((j'.1+1:ℕ):ℝ) ≤ p := by
      exact_mod_cast (PintzConductorReindex.mem_family.mp (mem_filter.mp H.1).1).1
    have hRw : R ≤ (j'.1+1:ℕ) := by
      have K := (conductorLabel_spec j').1
      rw [(mem_filter.mp H.1).2] at K
      dsimp [R]
      exact_mod_cast K
    have hbnd := PintzResidualLabels.horizontal (by linarith : 1 < N) hb.le
      H.2.2.1 H.2.2.2.1 p (j'.1+1:ℕ)
    dsimp only at hbnd
    rw [H.2.2.2.2.2] at hbnd
    have hwin := PintzHeightBins.bounds
      ((le_div_iff₀ (by positivity : 0 < ((j'.1+1:ℕ):ℝ))).mpr
        (show (1:ℝ)*((j'.1+1:ℕ):ℝ) ≤ 2*p by linarith))
      hs H.2.2.2.2.1
    have hmw := congrArg Prod.fst H.2.2.2.2.2
    change PintzHeightBins.idx (2*(p:ℝ)/(j'.1+1:ℕ)) w.im = l.1 at hmw
    dsimp only at hwin
    rw [hmw] at hwin
    exact ⟨H.2.1, ⟨by have := hbnd.2.2.2.2; linarith,H.2.2.2.1⟩,
      PintzHeightBins.in_common_range hR hRP hRw hM H.2.2.2.2.1 hwin.2.2.1.le⟩
  · have he : ∀ j ∈ family Q, group (p:=p) N b k l j = ∅ := by
      intro j hj
      exact not_nonempty_iff_eq_empty.mp (fun hn => hh ⟨j,hj,hn⟩)
    change M⁻¹ * N^(-2*h) * (∑ j ∈ family Q, ∑ z ∈ group (p:=p) N b k l j, _) ≤ _
    have hs0 : (∑ j ∈ family Q, ∑ z ∈ group (p:=p) N b k l j,
        (analyticOrderNatAt j.2.LFunction z : ℝ)) = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [he j hj, sum_empty]
    rw [hs0, mul_zero]
    positivity [hD b]

open PintzFiniteDyadicAggregation

theorem global_mass (hDens : DensityBound) : RichShiftSection8Bound263.MassBound := by
  classical
  obtain ⟨D,hD,hG⟩ := group_bound hDens
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
    exact hp.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (263/1000:ℝ) ≤ 1))
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
end RichShiftDensityGroup263
