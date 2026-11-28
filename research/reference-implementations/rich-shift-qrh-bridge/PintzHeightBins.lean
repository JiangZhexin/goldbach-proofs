import PintzWindowBlockEnergy
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Semiring

namespace PintzHeightBins

/-- The dyadic height index with all endpoints deterministic, and a
single first block collecting ordinates <2H. -/
noncomputable def idx (H γ : ℝ) : ℕ := Nat.log 2 ⌊|γ|/H⌋₊

theorem bounds {H γ T : ℝ} (hH : 1 ≤ H) (hT : 1 ≤ T) (hγ : |γ| ≤ T) :
    let μ := idx H γ
    let M := (2:ℝ)^μ
    1 ≤ M ∧ M ≤ T ∧ |γ| < 2*M*H ∧ (μ ≠ 0 → M*H ≤ |γ|) := by
  dsimp only [idx]
  let v := |γ|/H
  let n := ⌊v⌋₊
  let μ := Nat.log 2 n
  let M := (2:ℝ)^μ
  have hH0 : 0 < H := by linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hM : 1 ≤ M := by dsimp [M]; exact one_le_pow₀ (by norm_num)
  have hvm : v < 2*M := by
    have hh : n < 2^(μ+1) := Nat.lt_pow_succ_log_self (by decide : 1 < (2:ℕ)) n
    have hhR : (n:ℝ) + 1 ≤ (2:ℝ)^(μ+1) := by exact_mod_cast Nat.succ_le_of_lt hh
    have hl := (Nat.lt_floor_add_one v).trans_le hhR
    simpa [M,n,pow_succ,mul_comm] using hl
  have hMv : μ ≠ 0 → M ≤ v := by
    intro hμ
    have hn : n ≠ 0 := by
      intro hz
      exact hμ (by simp [μ,hz])
    have hh : (2:ℝ)^μ ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn
    exact hh.trans (Nat.floor_le hv)
  change 1 ≤ M ∧ M ≤ T ∧ |γ| < 2*M*H ∧ (μ ≠ 0 → M*H ≤ |γ|)
  refine ⟨hM, ?_, (div_lt_iff₀ hH0).mp hvm, fun h => (le_div_iff₀ hH0).mp (hMv h)⟩
  by_cases hμ : μ = 0
  · simpa [M,hμ] using hT
  · apply (hMv hμ).trans
    apply (div_le_iff₀ hH0).2
    exact hγ.trans (le_mul_of_one_le_right (by linarith) hH)

/-- Expand the height argument for the density theorem only by a bounded
factor, and cap its normalization scale at the terminal height. -/
theorem common_density_height {T P R M : ℝ} (hT : 0 ≤ T) (hR : 1 ≤ R)
    (hRP : R ≤ P) (hM : 1 ≤ M) (hMT : M ≤ T) :
    let M' := min (2*M) T
    let T' := min T (4*P*M/R)
    1 ≤ M' ∧ M ≤ M' ∧ M' ≤ 2*M ∧ M' ≤ T ∧
      T' ≤ 2*P*M'/R := by
  dsimp only
  have hR0 : 0 < R := by linarith
  refine ⟨le_min (by linarith) (by linarith), le_min (by linarith) hMT,
    min_le_left _ _, min_le_right _ _,?_⟩
  rcases le_total (2*M) T with h|h
  · rw [min_eq_left h, show 2*P*(2*M)/R=4*P*M/R by ring]
    exact min_le_right _ _
  · rw [min_eq_right h]
    apply (min_le_left T _).trans
    exact (le_div_iff₀ hR0).2 (by
      have hh := mul_le_mul_of_nonneg_right hRP hT
      nlinarith [mul_nonneg (show 0 ≤ P by linarith) hT])

/-- A conductor between R and 2R has window H=2P/r, hence its actual
height window fits into the common rectangular bound used by density. -/
theorem in_common_range {γ T P R M r : ℝ} (hR : 1 ≤ R) (hRP : R ≤ P)
    (hr : R ≤ r) (hM : 1 ≤ M)
    (hγ : |γ| ≤ T) (hbin : |γ| ≤ 2*M*(2*P/r)) :
    |γ| ≤ min T (4*P*M/R) := by
  have hR0 : 0 < R := by linarith
  have hr0 : 0 < r := hR0.trans_le hr
  have hmul : 4*P*M/r ≤ 4*P*M/R :=
    div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) hR0 hr
  refine le_min hγ (hbin.trans ?_)
  rw [show 2*M*(2*P/r) = 4*P*M/r by ring]
  exact hmul

#print axioms bounds
#print axioms common_density_height
#print axioms in_common_range
end PintzHeightBins
