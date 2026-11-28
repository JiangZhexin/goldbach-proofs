import PintzResidualPartition
import PintzWeilPrimitivePrimeWindow
import PintzWeilLeftHalf
import PintzWeilMultiplier

open Finset MeasureTheory Zeta23 Zeta23.ThmE
open PintzWeilPrimitivePrimeWindow PintzResidualGallagher

namespace PintzPrimitiveResidual

noncomputable def trunc (Z : ZeroConfig) (N : ℝ) : Finset Z.carrier :=
  (PintzWeilChiWindow.finite_low_ordinates Z (Real.sqrt N)).toFinset

noncomputable def weight (N : ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, (PintzWeilBump.scaled (PintzWeilScaleBudget.delta N) t:ℂ) *
    Complex.exp ((t:ℂ)*s)

noncomputable def primeCoeff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n.Prime then (Real.log n:ℂ)*coeff χ n else 0

noncomputable def retainedModel (Z : ZeroConfig) (q : ℕ) (N b : ℝ) (t : ℝ) : ℂ :=
  PintzResidualPartition.retained (trunc Z N)
    (fun i => (i:ℂ)) (fun i => weight N i) (fun i => (Z.mult i:ℝ)) b (poleCoeff q) t

noncomputable def farCatalogue (Z : ZeroConfig) (N b : ℝ) : Finset Z.carrier :=
  PintzResidualPartition.far (trunc Z N) (fun i => (i:ℂ)) b

theorem weight_bound {N : ℝ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖weight N s‖ ≤ Real.exp 1 := by
  have hd := PintzWeilScaleBudget.delta_pos (N := N) (by linarith)
  have H := PintzWeilMultiplier.norm_le_exp hd.le (PintzWeilBump.scaled_contDiff _).continuous
    (PintzWeilBump.scaled_nonneg hd) (PintzWeilBump.scaled_zero_left hd)
    (PintzWeilBump.scaled_zero_right hd) (PintzWeilBump.scaled_mass hd) hs h1
  exact H.trans (Real.exp_le_exp.mpr (PintzWeilScaleBudget.delta_le_one hN))

private theorem sum_primeCoeff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℕ) :
    (∑ n ∈ B, primeCoeff χ n) = ∑ n ∈ B.filter Nat.Prime, (Real.log n:ℂ)*coeff χ n := by
  rw [sum_filter]
  rfl

private theorem signed_kernel {Z : ZeroConfig} (S : Finset Z.carrier) (N u v : ℝ) :
    zeroPrimitive S (fun ρ => (ρ:ℂ)) (fun ρ => weight N ρ) (fun ρ => (Z.mult ρ:ℝ)) v -
      zeroPrimitive S (fun ρ => (ρ:ℂ)) (fun ρ => weight N ρ) (fun ρ => (Z.mult ρ:ℝ)) u =
    ∑ ρ ∈ S, (Z.mult ρ:ℂ)*PintzWeilChiWindow.windowTerm
      (PintzWeilBump.scaled (PintzWeilScaleBudget.delta N)) u v ρ := by
  rw [zeroPrimitive,zeroPrimitive,← sum_sub_distrib]
  apply sum_congr rfl
  intro ρ _
  simp only [Complex.ofReal_natCast,weight,PintzWeilChiWindow.windowTerm,sub_div,mul_sub]
  ring

private theorem left_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hp : χ.IsPrimitive) {N u v : ℝ}, 4 ≤ N → (q:ℝ) ≤ N → 1 ≤ u → u ≤ v → v ≤ N →
      let Z := zeroConfig hp
      ∀ S : Finset Z.carrier, (∀ ρ ∈ S, (ρ:ℂ).re ≤ 1/2) →
      (∀ ρ ∈ S, |(ρ:ℂ).im| ≤ Real.sqrt N) →
      ‖∑ ρ ∈ S, (Z.mult ρ:ℂ)*PintzWeilChiWindow.windowTerm
        (PintzWeilBump.scaled (PintzWeilScaleBudget.delta N)) u v ρ‖ ≤
        C*Real.sqrt N*(1+Real.log N)^2 := by
  obtain ⟨A,hA,hζ⟩ := PintzWeilLeftHalf.zeta_left_half
  obtain ⟨B,_,hχ⟩ := PintzWeilLeftHalf.chi_left_half
  refine ⟨max A B,hA.trans (le_max_left _ _),?_⟩
  intro q _ χ hp N u v hN hqN hu huv hvN
  dsimp only
  by_cases hq : q = 1
  · subst q
    rw [zeroConfig_one]
    intro S hs ht
    exact (hζ hN hu huv hvN S hs ht).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity))
  · have hq' : 1 < q := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (Ne.symm hq)
    rw [zeroConfig_eq_LZeros hp hq']
    intro S hs ht
    exact (hχ q χ hq' hp hN hqN hu huv hvN S hs ht).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity))

/-- The exact sharp discrete coefficient underlying §8. For every
clipped short interval, only right-half zero terms away from Re z=1
remain after subtracting the discrete increments of the main model.
The near-one cutoff b is independent of the smoothing width. -/
theorem window :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hp : χ.IsPrimitive) {N u v b : ℝ}, 4 ≤ N → (q:ℝ) ≤ N →
      2 ≤ u → u ≤ v → v ≤ N → b ≤ 1/2 →
      let Z := zeroConfig hp
      let K := retainedModel Z q N b
      let F := zeroPrimitive (farCatalogue Z N b)
        (fun ρ => (ρ:ℂ)) (fun ρ => weight N ρ) (fun ρ => (Z.mult ρ:ℝ))
      ‖(∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, primeCoeff χ n) - (K v-K u) + (F v-F u)‖ ≤
        C*N^(2/3:ℝ)*(1+Real.log N)^2 := by
  obtain ⟨A,hA,hS⟩ := sharp_prime_window_of_two_le
  obtain ⟨B,hB,hL⟩ := left_bound
  refine ⟨A+B,by positivity,?_⟩
  intro q _ χ hp N u v b hN hqN hu huv hvN hb
  dsimp only
  let Z := zeroConfig hp
  let S := trunc Z N
  let r : Z.carrier → ℂ := fun ρ => ρ
  let c : Z.carrier → ℂ := fun ρ => weight N ρ
  let m : Z.carrier → ℝ := fun ρ => Z.mult ρ
  let p : ℂ := ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, primeCoeff χ n
  have hsp := hS q χ hp hN hqN hu huv hvN
  rw [← sum_primeCoeff] at hsp
  have hA' : ‖p-poleCoeff q*((v:ℂ)-(u:ℂ))+
      (zeroPrimitive S r c m v-zeroPrimitive S r c m u)‖ ≤ A*N^(2/3:ℝ)*(1+Real.log N)^2 := by
    rw [show zeroPrimitive S r c m v-zeroPrimitive S r c m u =
      zeroWindow Z N u v from signed_kernel S N u v]
    exact hsp
  let S' := PintzResidualPartition.left S r
  have hβ (ρ) (hρ : ρ ∈ S') : (ρ:ℂ).re ≤ 1/2 :=
    ((PintzResidualPartition.mem_left S r ρ).1 hρ).2
  have hγ (ρ) (hρ : ρ ∈ S') : |(ρ:ℂ).im| ≤ Real.sqrt N :=
    (Set.Finite.mem_toFinset _).1 ((PintzResidualPartition.mem_left S r ρ).1 hρ).1
  have hB' := hL q χ hp hN hqN (show 1 ≤ u by linarith) huv hvN S' hβ hγ
  rw [← signed_kernel S' N u v] at hB'
  have hB'' : ‖zeroPrimitive S' r c m v-zeroPrimitive S' r c m u‖ ≤
      B*N^(2/3:ℝ)*(1+Real.log N)^2 := by
    refine hB'.trans ?_
    rw [Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) hB) (by positivity)
  exact (PintzResidualPartition.residual_error S r c m hb (poleCoeff q) p hA' hB'').trans_eq
    (by ring)

#print axioms window
end PintzPrimitiveResidual
