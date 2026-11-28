import PintzSection8Row
import PintzWindowFamilyError
import PintzEightLiteralReconstruction

open Finset Filter MeasureTheory PintzSieveToHybrid
open PintzResidualDensityGroups PintzResidualMajorArc PintzEightEnergy
open PintzEightRegroup

namespace PintzSection8Bound

/-- Total primitive-conductor Fourier remainder, with the standard
power saving and with the logarithmic loss made explicit. -/
theorem family_bound :
    ∃ A : ℝ → ℝ, (∀ b, 0 ≤ A b) ∧ ∀ {P : ℕ} {N a v b : ℝ},
      1 ≤ P → 4 ≤ N → (P:ℝ) ≤ N^(21/100:ℝ) →
      2 ≤ a → a ≤ v → v ≤ N → 0 < b → b ≤ 1/2 →
      (∑ j ∈ family P,
        intervalEnergy (1/(2*PintzPrimitiveDensityEnergy.width N P (j.1+1:ℕ)))
          (residual N a v b (j.1+1) j.2)) ≤
      A b * N^(1-b/40) * (1+Real.log N)^18 := by
  obtain ⟨C,hC,hRow⟩ := PintzSection8Row.row
  obtain ⟨D,hD,hMass⟩ := global_mass
  let B := PintzSection8Row.rowConstant
  have hB : 0 ≤ B := PintzSection8Row.rowConstant_nonneg
  refine ⟨fun b => (Real.pi^2/2)*(B*D b+8*C^2), fun b => by positivity [hD b],?_⟩
  intro P N a v b hP hN hcut ha hav hv hb hb2
  let L := 1+Real.log N
  let A := family P
  let W (j : PintzConductorReindex.CharIndex) := PintzPrimitiveDensityEnergy.width N P (j.1+1:ℕ)
  let f (j : PintzConductorReindex.CharIndex) :=
    intervalEnergy (1/(2*W j)) (residual N a v b (j.1+1) j.2)
  let e (j : PintzConductorReindex.CharIndex) := (v-(a-W j))*(C*N^(2/3:ℝ)*L^2/W j)^2
  let m (j : {x // x ∈ A}) := ∑ μ ∈ range (Nat.log 2 ⌊N⌋₊+1),
    ∑ ν ∈ range (⌈Real.log N/2⌉₊+1), mass j.2 N b (μ,ν)
  have hsum : (∑ j ∈ A, f j) ≤
      (Real.pi^2/2)*(B*L^5*N*(∑ j ∈ A.attach,m j) + ∑ j ∈ A,e j) := by
    rw [← sum_attach A f]
    have hs : (∑ j ∈ A.attach, f j.1) ≤
        ∑ j ∈ A.attach,(Real.pi^2/2)*(B*L^5*N*m j+e j.1) := by
      apply sum_le_sum
      intro j _
      exact hRow hN hcut ha hav hv hb.le hb2 j.1 j.2
    refine hs.trans_eq ?_
    rw [← mul_sum,sum_add_distrib, ← mul_sum, sum_attach A e]
  have hm : (∑ j ∈ A.attach, m j) ≤ D b*L^13*N^(-b/40) := hMass hN hcut hb
  have he := PintzWindowFamilyError.family_error (C := C) hP ha hav hv hcut
  change (∑ j ∈ A,e j) ≤ 8*C^2*N^(113/150:ℝ)*L^5 at he
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hL : 0 ≤ L := zero_le_one.trans hL1
  have hpow : N^(113/150:ℝ) ≤ N^(1-b/40) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hpL : L^5 ≤ L^18 := pow_le_pow_right₀ hL1 (by decide)
  have hSe : (∑ j ∈ A,e j) ≤ (8*C^2)*N^(1-b/40)*L^18 :=
    he.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hpL
      (by positivity) (by positivity))
  have hSm : B*L^5*N*(∑ j ∈ A.attach,m j) ≤ (B*D b)*N^(1-b/40)*L^18 := by
    refine (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq ?_
    have hNp : N*N^(-b/40) = N^(1-b/40) := by
      conv_lhs => lhs; rw [← Real.rpow_one N]
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    rw [show B*L^5*N*(D b*L^13*N^(-b/40)) =
      (B*D b)*(N*N^(-b/40))*(L^5*L^13) by ring,
      hNp,← pow_add]
  exact hsum.trans ((mul_le_mul_of_nonneg_left (add_le_add hSm hSe) (by positivity)).trans_eq
    (by ring))

/-- Main-arc remainder L², for the discrete near-zero model. This is
the power-saving estimate of Pintz I (8.25), with extra fixed logarithms
which are absorbed in the eventual version. -/
theorem arc_bound :
    ∃ C : ℝ → ℝ, (∀ b, 0 ≤ C b) ∧ ∀ {P : ℕ} {N a v b : ℝ},
      1 ≤ P → 4 ≤ N → (P:ℝ) ≤ N^(21/100:ℝ) →
      2 ≤ a → a ≤ v → v ≤ N → 0 < b → b ≤ 1/2 →
      (∑ q ∈ Icc 1 P,
        PintzEightPrimitiveEnergy.arcEnergy (N/(P:ℝ)) q (residual N a v b)) ≤
      C b * N^(1-b/40) * (1+Real.log N)^20 := by
  obtain ⟨A,hA,hB⟩ := family_bound
  obtain ⟨B,hB₀,hE⟩ := PintzEightPrimitiveEnergy.energy_log_squared
  refine ⟨fun b => B*A b,fun b => mul_nonneg hB₀.le (hA b),?_⟩
  intro P N a v b hP hN hcut ha hav hv hb hb2
  have hN0 : 0 < N := by linarith
  have hP0 : (0:ℝ) < P := by exact_mod_cast hP
  have hP1 : (1:ℝ) ≤ P := by exact_mod_cast hP
  let L := 1+Real.log N
  have hL : 0 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (show 1 ≤ N by linarith)]
  have hP' : (P:ℝ) ≤ N := by
    refine hcut.trans ?_
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) (by norm_num : (21/100:ℝ) ≤ 1)
  have hlog : 1 + Real.log P ≤ L := add_le_add_right (Real.log_le_log hP0 hP') 1
  have hlog0 : 0 ≤ 1+Real.log P := by linarith [Real.log_nonneg hP1]
  have hE' := hE P (N/(P:ℝ)) hP (by positivity)
      (residual N a v b) (residual_continuous N a v b)
  rw [primitive_sum] at hE'
  have hEq : (∑ j ∈ family P, intervalEnergy (PintzEightRegroup.width (N/(P:ℝ)) (j.1+1))
      (residual N a v b (j.1+1) j.2)) =
      ∑ j ∈ family P, intervalEnergy (1/(2*PintzPrimitiveDensityEnergy.width N P (j.1+1:ℕ)))
      (residual N a v b (j.1+1) j.2) := by
    apply sum_congr rfl
    intro j _
    rw [window_width hN0 hP (by omega)]
  rw [hEq] at hE'
  have hp : 0 ≤ A b*N^(1-b/40)*L^18 := by positivity [hA b]
  calc
    _ ≤ _ := hE'
    _ ≤ (B*L^2)*(A b*N^(1-b/40)*L^18) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 2) hB₀.le)
        (hB hP hN hcut ha hav hv hb hb2)
        (sum_nonneg fun j _ => by
          unfold intervalEnergy
          have hu : 0 ≤ 1/(2*PintzPrimitiveDensityEnergy.width N P (j.1+1:ℕ)) := by
            unfold PintzPrimitiveDensityEnergy.width
            positivity
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact integral_nonneg fun _ => sq_nonneg _) (by positivity)
    _ = _ := by dsimp [L]; ring

theorem arc_bound_eventual {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (P : ℕ) (a v : ℝ),
      1 ≤ P → (P:ℝ) ≤ (n:ℝ)^(21/100:ℝ) →
      2 ≤ a → a ≤ v → v ≤ (n:ℝ) →
      (∑ q ∈ Icc 1 P,
        PintzEightPrimitiveEnergy.arcEnergy ((n:ℝ)/(P:ℝ)) q (residual n a v b)) ≤
          C*(n:ℝ)^(1-b/41) := by
  obtain ⟨D,hD,hA⟩ := arc_bound
  let ε := b/40-b/41
  have hε : 0 < ε := by dsimp [ε]; linarith
  refine ⟨D b*2^20,by positivity [hD b],?_⟩
  filter_upwards [ExceptionUnionBridge.eventual_log_loss hε 20,
    eventually_ge_atTop (4:ℕ)] with n hlog hn
  intro P a v hP hcut ha hav hv
  have hN : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0:ℝ) < n := by linarith
  have hL := PintzResidualLabels.log_ge_one hN
  have hpow : (1+Real.log (n:ℝ))^20 ≤ (2:ℝ)^20*(n:ℝ)^ε := by
    calc
      _ ≤ (2*Real.log (n:ℝ))^20 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 20
      _ ≤ _ := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
  refine (hA hP hN hcut ha hav hv hb hb2).trans ?_
  calc
    _ ≤ D b*(n:ℝ)^(1-b/40)*((2:ℝ)^20*(n:ℝ)^ε) :=
      mul_le_mul_of_nonneg_left hpow (by positivity [hD b])
    _ = _ := by
      rw [show D b*(n:ℝ)^(1-b/40)*((2:ℝ)^20*(n:ℝ)^ε) =
        (D b*2^20)*((n:ℝ)^(1-b/40)*(n:ℝ)^ε) by ring,
        ← Real.rpow_add hN0]
      congr 2
      dsimp [ε]
      ring

#print axioms family_bound
#print axioms arc_bound
#print axioms arc_bound_eventual
end PintzSection8Bound
