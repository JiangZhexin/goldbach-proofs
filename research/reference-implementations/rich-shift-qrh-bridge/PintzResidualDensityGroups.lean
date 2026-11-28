import PintzUniformDensitySubsets
import PintzResidualLabels
import PintzConductorReindex

open Finset PintzSieveToHybrid PintzConductorReindex PintzWeilPrimitivePrimeWindow
open PintzPrimitiveResidual

namespace PintzResidualDensityGroups

instance levelNonzero (j : CharIndex) : NeZero (j.1+1) := ⟨by omega⟩

/-- The actual canonical far zero block, before forgetting the carrier. -/
noncomputable def subBlock {p : ℕ} {j : CharIndex} (hj : j ∈ family p)
    (N b : ℝ) (l : ℕ × ℕ) :
    Finset (zeroConfig (PintzConductorReindex.mem_family.mp hj).2).carrier :=
  (farCatalogue _ N b).filter (fun z => PintzResidualLabels.index N p (j.1+1:ℕ) z = l)

noncomputable def group {p : ℕ} (N b : ℝ) (k : ℕ) (l : ℕ × ℕ) (j : CharIndex) :
    Finset ℂ := by
  classical
  exact if hj : j ∈ conductorBlock p k then
    (subBlock (mem_filter.mp hj).1 N b l).map (Function.Embedding.subtype _)
  else ∅

theorem mem_group {p : ℕ} {N b : ℝ} {k : ℕ} {l : ℕ × ℕ} {j : CharIndex} {z : ℂ}
    (hz : z ∈ group (p:=p) N b k l j) :
    j ∈ conductorBlock p k ∧ j.2.LFunction z = 0 ∧
      (1/2:ℝ) ≤ z.re ∧ z.re ≤ 1-b ∧ |z.im| ≤ Real.sqrt N ∧
      PintzResidualLabels.index N p (j.1+1:ℕ) z = l := by
  unfold group at hz
  split at hz
  next hj =>
    obtain ⟨u,hu, rfl⟩ := mem_map.mp hz
    obtain ⟨hf, hl⟩ := mem_filter.mp hu
    have H := (PintzResidualPartition.mem_far _ _ b u).mp hf
    have hp := (PintzConductorReindex.mem_family.mp (mem_filter.mp hj).1).2
    exact ⟨hj, ((PintzPrimitiveCatalogueLocal.mem_carrier_iff hp (u:ℂ)).mp u.2).1,
      H.2.1.le, H.2.2, (Set.Finite.mem_toFinset _).mp H.1, hl⟩
  next hj => simp at hz

theorem group_bound :
    ∃ D : ℝ → ℝ, (∀ b, 0 ≤ D b) ∧ ∀ {N b : ℝ} {p : ℕ}
      (_hN : 4 ≤ N) (_hp : (p:ℝ) ≤ N^(21/100:ℝ)) (_hb : 0 < b)
      (k : ℕ) (l : ℕ × ℕ),
    let M := (2:ℝ)^l.1
    let h := PintzResidualLabels.edge N l.2
    M⁻¹ * N^(-2*h) *
      (∑ j ∈ family (min p (2*2^k)), ∑ z ∈ group (p:=p) N b k l j,
        (analyticOrderNatAt j.2.LFunction z : ℝ)) ≤
      D b * (1+Real.log N)^10 * N^(-h/40) := by
  classical
  obtain ⟨D,hD,hB⟩ := PintzUniformDensitySubsets.combined
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
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (21/100:ℝ) ≤ 1)))
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

theorem group_sum_eq {N b : ℝ} {p k : ℕ} (l : ℕ × ℕ) :
    (∑ j ∈ family (min p (2*2^k)), ∑ z ∈ group (p:=p) N b k l j,
        (analyticOrderNatAt j.2.LFunction z : ℝ)) =
    ∑ j ∈ (conductorBlock p k).attach,
      ∑ z ∈ subBlock (mem_filter.mp j.2).1 N b l,
        (((zeroConfig (PintzConductorReindex.mem_family.mp (mem_filter.mp j.2).1).2).mult z : ℕ):ℝ) := by
  classical
  let F (j : CharIndex) : ℝ := ∑ z ∈ group (p:=p) N b k l j,
    (analyticOrderNatAt j.2.LFunction z : ℝ)
  change (∑ j ∈ family (min p (2*2^k)), F j) = _
  rw [← sum_subset (conductorBlock_subset p k) (f := F) (fun j _ hj => by simp [F,group,hj])]
  rw [← Finset.sum_attach (conductorBlock p k) F]
  apply sum_congr rfl
  intro j _
  dsimp [F, group]
  rw [dite_eq_left j.2, Finset.sum_map]
  apply sum_congr rfl
  intro z _
  rw [PintzPrimitiveCatalogueLocal.mult_eq_analyticOrderNatAt]
  rfl

theorem canonical_group_bound :
    ∃ D : ℝ → ℝ, (∀ b, 0 ≤ D b) ∧ ∀ {N b : ℝ} {p : ℕ}
      (_hN : 4 ≤ N) (_hp : (p:ℝ) ≤ N^(21/100:ℝ)) (_hb : 0 < b)
      (k : ℕ) (l : ℕ × ℕ),
    let M := (2:ℝ)^l.1
    let h := PintzResidualLabels.edge N l.2
    M⁻¹ * N^(-2*h) *
      (∑ j ∈ (conductorBlock p k).attach,
        ∑ z ∈ subBlock (mem_filter.mp j.2).1 N b l,
          (((zeroConfig (PintzConductorReindex.mem_family.mp (mem_filter.mp j.2).1).2).mult z : ℕ):ℝ)) ≤
      D b * (1+Real.log N)^10 * N^(-h/40) := by
  obtain ⟨D,hD,hG⟩ := group_bound
  refine ⟨D,hD,?_⟩
  intro N b p hN hp hb k l
  simpa only [group_sum_eq l] using hG hN hp hb k l

#print axioms canonical_group_bound
#print axioms mem_group
#print axioms group_bound
end PintzResidualDensityGroups
