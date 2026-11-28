import PintzWindowErrorBudget
import PintzSieveToHybrid
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic.GCongr

open Finset PintzSieveToHybrid
namespace PintzWindowFamilyError

noncomputable def width (N : ℝ) (P r : ℕ) : ℝ := (r:ℝ)*N/(2*(P:ℝ))

theorem family_error {N a v C : ℝ} {P : ℕ} (hP : 0 < P)
    (ha : 2 ≤ a) (hav : a ≤ v) (hv : v ≤ N) (hcut : (P:ℝ) ≤ N^(21/100:ℝ)) :
    (∑ j ∈ family P, let Y := width N P (j.1+1)
      (v-(a-Y))*(C*N^(2/3:ℝ)*(1+Real.log N)^2/Y)^2) ≤
      (8*C^2)*N^(113/150:ℝ)*(1+Real.log N)^5 := by
  classical
  have hN : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hP0 : (0:ℝ) < P := by exact_mod_cast hP
  let E := N^(2/3:ℝ)*(1+Real.log N)^2
  let F := fun r : ℕ => ((univ : Finset (DirichletCharacter ℂ r)).filter
    (fun χ => χ.IsPrimitive)).card
  let W := fun r : ℕ => (F r:ℝ)*(v-(a-width N P r))*(E/width N P r)^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hW (r : ℕ) (hr : r ∈ Icc 1 P) :
      W r ≤ 2*N*(r:ℝ)*(E/((r:ℝ)*N/(2*(P:ℝ))))^2 := by
    have hri := mem_Icc.mp hr
    have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
    have hrP : (r:ℝ) ≤ P := by exact_mod_cast hri.2
    have hY0 : 0 ≤ width N P r := by unfold width; positivity
    have hY : width N P r ≤ N := by
      unfold width
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [mul_nonneg hN0.le (sub_nonneg.mpr hrP)]
    have hF : (F r:ℝ) ≤ r := by
      have hf : F r ≤ r := by
        unfold F
        refine (card_filter_le _ _).trans ?_
        rw [card_univ, ← Nat.card_eq_fintype_card]
        let : NeZero r := ⟨by omega⟩
        rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
        exact Nat.totient_le _
      exact_mod_cast hf
    have hlen : v-(a-width N P r) ≤ 2*N := by linarith
    have hlen0 : 0 ≤ v-(a-width N P r) := by linarith
    unfold W
    change (F r:ℝ)*(v-(a-width N P r))*(E/width N P r)^2 ≤ _
    rw [mul_comm (2*N) (r:ℝ)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hF hlen hlen0 hr0) (sq_nonneg _)
  have H := PintzWindowErrorBudget.smooth_budget hN hP hcut hE
    (k := 2) (show E ≤ N^(2/3:ℝ)*(1+Real.log N)^2 from le_rfl) W hW
  have HS :
      (∑ j ∈ family P, let Y := width N P (j.1+1)
        (v-(a-Y))*(C*N^(2/3:ℝ)*(1+Real.log N)^2/Y)^2) =
        C^2*(∑ r ∈ Icc 1 P, W r) := by
    rw [family, sum_sigma, mul_sum]
    have hb : (∑ r ∈ Icc 1 P, C^2*W r) =
        ∑ k ∈ range P, C^2*W (k+1) := by
      symm
      apply sum_bij (fun k _ => k+1)
      · intro k hk
        have := mem_range.mp hk
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · intro k hk j hj he
        omega
      · intro r hr
        obtain ⟨hr1,hrP⟩ := mem_Icc.mp hr
        exact ⟨r-1,mem_range.mpr (by omega),by omega⟩
      · intros
        rfl
    rw [hb]
    apply sum_congr rfl
    intro k hk
    simp only [sum_const, nsmul_eq_mul, W, F]
    dsimp [E]
    ring
  rw [HS]
  calc
    _ ≤ C^2*(8*N^(113/150:ℝ)*(1+Real.log N)^(2*2+1)) :=
      mul_le_mul_of_nonneg_left H (sq_nonneg _)
    _ = _ := by norm_num only; ring

#print axioms family_error
end PintzWindowFamilyError
