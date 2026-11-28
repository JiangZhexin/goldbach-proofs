import PintzPrimitiveResidual
import PintzPrimitiveCatalogueLocal

open Finset MeasureTheory Zeta23 Zeta23.ThmE
open PintzWeilPrimitivePrimeWindow PintzPrimitiveResidual PintzDiscreteZeroModel

namespace PintzPrimitiveResidualEnergy

theorem rounding :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hp : χ.IsPrimitive) {N b : ℝ}, 4 ≤ N → (q:ℝ) ≤ N → b ≤ 1/2 →
      let K := retainedModel (zeroConfig hp) q N b
      ∀ t, 1 ≤ t → ‖K t - K (⌊t⌋₊:ℕ)‖ ≤ C*Real.sqrt N*(1+Real.log N) := by
  obtain ⟨D,hD,hd⟩ := PintzPrimitiveCatalogueLocal.sqrt_scale_count
  refine ⟨1+Real.exp 1*D,by positivity,?_⟩
  intro q _ χ hp N b hN hqN hb
  dsimp only
  intro t ht
  let Z := zeroConfig hp
  let S := trunc Z N
  let ρ : Z.carrier → ℂ := fun z => z
  let V := PintzResidualPartition.near S ρ b
  let e : Z.carrier ↪ ℂ := Function.Embedding.subtype _
  have hS (z) (hz : z ∈ V.map e) :
      z ∈ Z.carrier ∧ 1/2 ≤ z.re ∧ |z.im| ≤ Real.sqrt N := by
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hz
    have H := (PintzResidualPartition.mem_near S ρ b i).1 hi
    exact ⟨i.2, by change 1/2 ≤ (i:ℂ).re; have hh := H.2; dsimp [ρ] at hh; linarith,
      (Set.Finite.mem_toFinset _).1 H.1⟩
  have hs := hd q χ hp hN hqN (V.map e) hS
  rw [Finset.sum_map] at hs
  have hm :
      (∑ z ∈ V, (Z.mult z:ℝ)*‖weight N z‖) ≤ (Real.exp 1*D)*Real.sqrt N*(1+Real.log N) := by
    calc
      _ ≤ ∑ z ∈ V, (Z.mult z:ℝ)*Real.exp 1 := by
        apply sum_le_sum
        intro z _
        have hq := Z.strip z z.2
        exact mul_le_mul_of_nonneg_left (weight_bound (by linarith) hq.1 hq.2) (by positivity)
      _ = Real.exp 1*(∑ z ∈ V, (Z.mult z:ℝ)) := by rw [mul_sum]; simp [mul_comm]
      _ ≤ _ := by
        change (∑ z ∈ V, (Z.mult z:ℝ)) ≤ _ at hs
        exact (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le).trans_eq (by ring)
  have hpole : ‖poleCoeff q‖ ≤ 1 := by unfold poleCoeff; split_ifs <;> norm_num
  have hR := PintzResidualPartition.retained_rounding (b := b) S ρ
    (fun i => weight N i) (fun i => Z.mult i) ht (poleCoeff q)
    (fun i hi => by
      have hβ := ((PintzPrimitiveCatalogueLocal.mem_carrier_iff hp (i:ℂ)).1 i.2).2.1
      exact Complex.ne_zero_of_re_pos hβ)
    (fun i hi => (Z.strip i i.2).2)
  have hL : 1 ≤ 1+Real.log N := by linarith [Real.log_nonneg (show 1 ≤ N by linarith)]
  have hF : 1 ≤ Real.sqrt N := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hFL : 1 ≤ Real.sqrt N*(1+Real.log N) := one_le_mul_of_one_le_of_one_le hF hL
  exact hR.trans ((add_le_add (hpole.trans hFL) hm).trans_eq (by ring))

/-- Per-character Fourier estimate for the true residual sequence with a
single scale-independent constant, before the finite density sum. -/
theorem estimate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hp : χ.IsPrimitive) {N a v Y b : ℝ}, 4 ≤ N → (q:ℝ) ≤ N →
      2 ≤ a → a ≤ v → v ≤ N → 0 < Y → b ≤ 1/2 →
      let Z := zeroConfig hp
      let K := retainedModel Z q N b
      let S := farCatalogue Z N b
      ∀ {κ : Type} [DecidableEq κ] (label : Z.carrier → κ),
      (∫ η in (-1/(2*Y))..(1/(2*Y)),
        ‖∑ n ∈ Ioc ⌊a⌋₊ ⌊v⌋₊, (primeCoeff χ n-increment K n) *
          Complex.exp ((2*Real.pi*η*Complex.I)*(n:ℝ))‖^2) ≤
      (Real.pi^2/2)*(((S.image label).card:ℝ) *
        (∑ k ∈ S.image label, ∫ x : ℝ,
          ‖PintzWindowBlockEnergy.model (S.filter (fun i => label i=k))
            (fun ρ => (ρ:ℂ)) (fun ρ => weight N ρ) (fun ρ => (Z.mult ρ:ℝ)) a v Y x‖^2)
        +(v-(a-Y))*(C*N^(2/3:ℝ)*(1+Real.log N)^2/Y)^2) := by
  obtain ⟨A,hA,hF⟩ := window
  obtain ⟨B,hB,hK⟩ := rounding
  refine ⟨A+2*B,by positivity,?_⟩
  intro q _ χ hp N a v Y b hN hqN ha hav hvN hY hb
  dsimp only
  intro κ _ label
  let Z := zeroConfig hp
  let K := retainedModel Z q N b
  let S := farCatalogue Z N b
  let E := A*N^(2/3:ℝ)*(1+Real.log N)^2
  let R := B*Real.sqrt N*(1+Real.log N)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hR : 0 ≤ R := by
    have hL := Real.log_nonneg (show 1 ≤ N by linarith)
    dsimp [R]; positivity
  have h0 := PintzResidualGallagher.estimate S label (fun ρ => (ρ:ℂ))
    (fun ρ => weight N ρ) (fun ρ => (Z.mult ρ:ℝ)) (primeCoeff χ) K
      (by linarith : 1 ≤ a) hav hY hE hR (hK q χ hp hN hqN hb)
      (fun u w hu huw hw => hF q χ hp hN hqN (ha.trans hu) huw (hw.trans hvN) hb)
  apply h0.trans
  have hR' : R ≤ B*N^(2/3:ℝ)*(1+Real.log N)^2 := by
    have hL : 1 ≤ 1+Real.log N := by linarith [Real.log_nonneg (show 1 ≤ N by linarith)]
    have hF : Real.sqrt N ≤ N^(2/3:ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    dsimp [R]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hF hB)
      (by nlinarith [sq_nonneg (Real.log N)]) (by linarith) (by positivity)
  have herror : E+2*R ≤ (A+2*B)*N^(2/3:ℝ)*(1+Real.log N)^2 := by
    dsimp [E]
    linarith only [hR']
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  exact pow_le_pow_left₀ (by positivity)
    (div_le_div_of_nonneg_right herror hY.le) 2

#print axioms rounding
#print axioms estimate
end PintzPrimitiveResidualEnergy
