import PintzResidualMajorArc
import PintzResidualDensityGlobal

open Finset MeasureTheory Zeta23
open PintzWeilPrimitivePrimeWindow PintzPrimitiveResidual PintzPrimitiveDensityEnergy
open PintzSieveToHybrid PintzConductorReindex PintzResidualDensityGroups
open PintzEightEnergy

namespace PintzSection8Row
set_option maxHeartbeats 800000

noncomputable def rowConstant : ℝ :=
  ((1/Real.log 2+1)*(5/2:ℝ)) *
  ((32*(2+Real.log 3)+20) *
    (18/Real.log (55/52)+11/Real.log (12/11)) * (Real.exp 1)^2 * Real.exp 2)

theorem rowConstant_nonneg : 0 ≤ rowConstant := by
  unfold rowConstant
  positivity [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num),
    Real.log_pos (show (1:ℝ) < 55/52 by norm_num),
    Real.log_pos (show (1:ℝ) < 12/11 by norm_num)]

theorem row :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : ℕ} {N a v b : ℝ}
      (hN : 4 ≤ N) (hcut : (P:ℝ) ≤ N^(21/100:ℝ))
      (ha : 2 ≤ a) (hav : a ≤ v) (hv : v ≤ N) (hb : 0 ≤ b) (hb₂ : b ≤ 1/2)
      (j : CharIndex) (hj : j ∈ family P),
      let Y := width N P (j.1+1:ℕ)
      intervalEnergy (1/(2*Y)) (PintzResidualMajorArc.residual N a v b (j.1+1) j.2) ≤
      (Real.pi^2/2)*(rowConstant*(1+Real.log N)^5*N *
        (∑ μ ∈ range (Nat.log 2 ⌊N⌋₊+1), ∑ ν ∈ range (⌈Real.log N/2⌉₊+1),
          mass hj N b (μ,ν)) +
        (v-(a-Y))*(C*N^(2/3:ℝ)*(1+Real.log N)^2/Y)^2) := by
  obtain ⟨C,hC,hrow⟩ := PintzPrimitiveResidualEnergy.estimate
  refine ⟨C,hC,?_⟩
  intro P N a v b hN hcut ha hav hv hb hb₂ j hj
  dsimp only
  let r := j.1+1
  letI : NeZero r := ⟨by dsimp [r]; omega⟩
  let hp := (PintzConductorReindex.mem_family.mp hj).2
  let Z := zeroConfig hp
  let S := farCatalogue Z N b
  let Y := width N P r
  let L := 1+Real.log N
  let labels (z : Z.carrier) := PintzResidualLabels.index N P r (z:ℂ)
  let Ls := S.image labels
  let M := range (Nat.log 2 ⌊N⌋₊+1)
  let V := range (⌈Real.log N/2⌉₊+1)
  let energy (k : ℕ×ℕ) :=
    ∫ x : ℝ, ‖PintzWindowBlockEnergy.model (subBlock hj N b k) (fun z => (z:ℂ))
      (fun z => weight N z) (fun z => (Z.mult z:ℝ)) a v Y x‖^2
  let B := (1/Real.log 2+1)*(5/2:ℝ)
  let D := (32*(2+Real.log 3)+20) *
    (18/Real.log (55/52)+11/Real.log (12/11)) * (Real.exp 1)^2 * Real.exp 2
  have hr : (0:ℝ) < r := by exact_mod_cast NeZero.pos r
  have hrP : (r:ℝ) ≤ P := by exact_mod_cast (PintzConductorReindex.mem_family.mp hj).1
  have hP : (P:ℝ) ≤ N := by
    refine hcut.trans ?_
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) (by norm_num : (21/100:ℝ) ≤ 1)
  have hrN : (r:ℝ) ≤ N := hrP.trans hP
  have hY : 0 < Y := width_pos (show 0 < N by linarith) hr hrP
  have hL : 0 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (show 1 ≤ N by linarith)]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num),
      Real.log_pos (show (1:ℝ) < 55/52 by norm_num),
      Real.log_pos (show (1:ℝ) < 12/11 by norm_num)]
  have hFirst := hrow r j.2 hp hN hrN ha hav hv hY hb₂ labels
  unfold intervalEnergy
  rw [← neg_div]
  simp_rw [PintzResidualMajorArc.residual_eq j.2 hp]
  apply hFirst.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_left
  have hspec (z : Z.carrier) (hz : z ∈ S) :
      1/2 ≤ (z:ℂ).re ∧ (z:ℂ).re ≤ 1-b ∧ |(z:ℂ).im| ≤ Real.sqrt N := by
    have hh := far_spec z hz
    exact ⟨hh.1.le,hh.2⟩
  have hcard : (Ls.card:ℝ) ≤ B*L^2 :=
    PintzResidualLabels.card_bound S (fun z => (z:ℂ)) hN hr hrP hb hspec
  have hLs : Ls ⊆ M.product V := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
    obtain ⟨h₁,h₂,h₃⟩ := hspec z hz
    exact PintzResidualLabels.label_range hN hr hrP hb h₁ h₂ h₃
  have hm (k : ℕ×ℕ) : 0 ≤ mass hj N b k := by unfold mass; positivity
  have hs (k : ℕ×ℕ) : energy k ≤ D*L^3*N*mass hj N b k := by
    have h := occupied_block j.2 hp hN hrP hrN ha hav hv hb k
    dsimp only at h
    refine h.trans_eq ?_
    let W := ∑ z ∈ subBlock hj N b k, (Z.mult z:ℝ)
    let H := (2:ℝ)^k.1
    let h := PintzResidualLabels.edge N k.2
    change D*L^3*(N*H⁻¹*N^(-2*h)*W) = D*L^3*N*(H⁻¹*N^(-2*h)*W)
    ring
  change (Ls.card:ℝ)*(∑ k ∈ Ls, energy k) ≤
    rowConstant*L^5*N*∑ μ ∈ M, ∑ ν ∈ V, mass hj N b (μ,ν)
  have hsum (k : ℕ×ℕ) : 0 ≤ energy k := integral_nonneg fun x => sq_nonneg _
  calc
    _ ≤ B*L^2*(∑ k ∈ M.product V, energy k) :=
      mul_le_mul hcard (sum_le_sum_of_subset_of_nonneg hLs (fun k _ _ => hsum k))
        (sum_nonneg (fun _ _ => hsum _)) (by positivity)
    _ ≤ B*L^2*(∑ k ∈ M.product V, D*L^3*N*mass hj N b k) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun k _ => hs k)) (by positivity)
    _ = _ := by
      have hprod : (∑ k ∈ M.product V, mass hj N b k) =
          ∑ μ ∈ M, ∑ ν ∈ V, mass hj N b (μ,ν) :=
        Finset.sum_product M V (mass hj N b)
      rw [← mul_sum, hprod]
      dsimp only [rowConstant,B,D]
      ring
#print axioms row
end PintzSection8Row
