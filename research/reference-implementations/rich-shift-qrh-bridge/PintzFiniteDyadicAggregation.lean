import ExceptionUnionDyadicPower
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Semifield

open Filter
open scoped BigOperators
namespace PintzFiniteDyadicAggregation

/-- An interval of width 1/log N costs at most exp 2 when replacing the
actual horizontal deficit δ by the upper edge h in N^(-2 δ). -/
theorem horizontal_loss {N δ h : ℝ} (hN : 1 < N)
    (hd : h - 1 / Real.log N ≤ δ) :
    N ^ (-2*δ) ≤ Real.exp 2 * N ^ (-2*h) := by
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hp : 0 < N := zero_lt_one.trans hN
  have hs : -2*δ ≤ -2*h + 2/Real.log N := by
    linarith [show 2/Real.log N = 2*(1/Real.log N) by ring]
  calc
    _ ≤ N^(-2*h + 2/Real.log N) := Real.rpow_le_rpow_of_exponent_le hN.le hs
    _ = _ := by
      rw [Real.rpow_add hp, Real.rpow_def_of_pos hp (2 / Real.log N)]
      have e : Real.log N * (2 / Real.log N) = 2 := by field_simp
      rw [e,mul_comm]

/-- Three nested finite sums incur only their three cardinality losses.
The sets may be different for each N; no convergence of partitions is needed. -/
theorem aggregate_three {ι κ τ : Type*} (I : Finset ι) (J : Finset κ) (K : Finset τ)
    (F : ι → κ → τ → ℝ) {L C₁ C₂ C₃ D A : ℝ} {k₁ k₂ k₃ k : ℕ}
    (hL : 0 ≤ L) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) (_h₃ : 0 ≤ C₃)
    (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hc₁ : (I.card:ℝ) ≤ C₁*L^k₁) (hc₂ : (J.card:ℝ) ≤ C₂*L^k₂)
    (hc₃ : (K.card:ℝ) ≤ C₃*L^k₃)
    (hF : ∀ i ∈ I, ∀ j ∈ J, ∀ l ∈ K, F i j l ≤ D*L^k*A) :
    (∑ i ∈ I, ∑ j ∈ J, ∑ l ∈ K, F i j l) ≤
      C₁*C₂*C₃*D * L^(k₁+k₂+k₃+k) * A := by
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ∑ l ∈ K, D*L^k*A :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
      Finset.sum_le_sum fun l hl => hF i hi j hj l hl
    _ = (I.card:ℝ)*((J.card:ℝ)*((K.card:ℝ)*(D*L^k*A))) := by simp
    _ ≤ (C₁*L^k₁)*((C₂*L^k₂)*((C₃*L^k₃)*(D*L^k*A))) := by gcongr
    _ = _ := by simp only [pow_add]; ring

/-- After aggregation of any fixed number of dyadic/strip log factors,
the saving b/40 implies b/41 for every fixed positive cutoff b. -/
theorem absorb_log_saving {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C) (k : ℕ)
    (F : ℕ → ℝ)
    (hF : ∀ᶠ N : ℕ in atTop,
      F N ≤ C*(Real.log (N:ℝ))^k*(N:ℝ)^(1-b/40)) :
    ∀ᶠ N : ℕ in atTop, F N ≤ C*(N:ℝ)^(1-b/41) := by
  let ε : ℝ := b/40-b/41
  have hε : 0 < ε := by dsimp [ε]; linarith
  filter_upwards [hF, ExceptionUnionBridge.eventual_log_loss hε k,
    eventually_ge_atTop (1:ℕ)] with N hN hlog h1
  have hp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  calc
    _ ≤ C*(Real.log (N:ℝ))^k*(N:ℝ)^(1-b/40) := hN
    _ ≤ C*(N:ℝ)^ε*(N:ℝ)^(1-b/40) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hp]
      congr 2
      dsimp [ε]; ring

/-- Choose the horizontal zero-deficit bin of (8.9), with upper edge
ν/log N and with ν bounded by the ceiling cutoff when δ ≤ 1/2. -/
theorem choose_horizontal_bin {N b δ : ℝ} (hN : 1 < N)
    (hb : 0 ≤ b) (hbδ : b ≤ δ) (hδ : δ ≤ 1/2) :
    ∃ ν : ℕ, b*Real.log N ≤ ν ∧ ν ≤ ⌈Real.log N / 2⌉₊ ∧
      (ν:ℝ)/Real.log N - 1/Real.log N ≤ δ ∧ δ ≤ (ν:ℝ)/Real.log N := by
  let L := Real.log N
  have hp : 0 < L := Real.log_pos hN
  have hd : 0 ≤ δ*L := mul_nonneg (hb.trans hbδ) hp.le
  let ν := ⌈δ*L⌉₊
  have hlo : δ*L ≤ (ν:ℝ) := Nat.le_ceil _
  have hhi : (ν:ℝ) < δ*L+1 := Nat.ceil_lt_add_one hd
  refine ⟨ν, (mul_le_mul_of_nonneg_right hbδ hp.le).trans hlo, ?_, ?_, (le_div_iff₀ hp).mpr hlo⟩
  · exact Nat.ceil_mono (by nlinarith only [mul_le_mul_of_nonneg_right hδ hp.le])
  · rw [← sub_div]
    exact (div_le_iff₀ hp).mpr (by linarith)

/-- Both the conductor scales and the height scales counted by a binary
logarithm have at most O(log N) bins. -/
theorem binary_range_count {N : ℕ} (hN : 0 < N) (hL : 1 ≤ Real.log (N:ℝ)) :
    ((Finset.range (Nat.log 2 N+1)).card : ℝ) ≤
      (1/Real.log 2+1) * Real.log (N:ℝ) := by
  have hh : (2:ℝ)^(Nat.log 2 N) ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hN)
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := Real.log_le_log (by positivity) hh
  rw [Real.log_pow] at hp
  simp only [Finset.card_range,Nat.cast_add,Nat.cast_one,add_mul,div_mul_eq_mul_div,one_mul]
  have hb := (le_div_iff₀ h₂).mpr hp
  linarith

theorem horizontal_range_count {N : ℝ} (hL : 1 ≤ Real.log N) :
    ((Finset.range (⌈Real.log N / 2⌉₊+1)).card:ℝ) ≤ (5/2:ℝ)*Real.log N := by
  have hh := Nat.ceil_lt_add_one (show 0 ≤ Real.log N/2 by linarith)
  simp only [Finset.card_range,Nat.cast_add,Nat.cast_one]
  linarith

/-- Direct outer aggregation with the conductor and height ranges bounded
by binary logarithms and the horizontal range by its ceiling cutoff.
The two dyadic ranges may be pruned independently. -/
theorem aggregate_pintz_scales {N : ℕ} (hN : 0 < N) (hlog : 1 ≤ Real.log (N:ℝ))
    (I J K : Finset ℕ) (F : ℕ → ℕ → ℕ → ℝ)
    (hI : I ⊆ Finset.range (Nat.log 2 N+1))
    (hJ : J ⊆ Finset.range (Nat.log 2 N+1))
    (hK : K ⊆ Finset.range (⌈Real.log (N:ℝ)/2⌉₊+1))
    {D A : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) (k : ℕ)
    (hF : ∀ i ∈ I, ∀ j ∈ J, ∀ l ∈ K, F i j l ≤ D*(Real.log (N:ℝ))^k*A) :
    (∑ i ∈ I, ∑ j ∈ J, ∑ l ∈ K, F i j l) ≤
      (1/Real.log 2+1)^2*(5/2:ℝ)*D * (Real.log (N:ℝ))^(3+k) * A := by
  have h2 : 0 ≤ 1/Real.log 2+1 := by positivity
  have hcI : (I.card:ℝ) ≤ (1/Real.log 2+1) * Real.log (N:ℝ) :=
    (by exact_mod_cast Finset.card_le_card hI :
      (I.card:ℝ) ≤ ((Finset.range (Nat.log 2 N+1)).card:ℝ)).trans (binary_range_count hN hlog)
  have hcJ : (J.card:ℝ) ≤ (1/Real.log 2+1) * Real.log (N:ℝ) :=
    (by exact_mod_cast Finset.card_le_card hJ :
      (J.card:ℝ) ≤ ((Finset.range (Nat.log 2 N+1)).card:ℝ)).trans (binary_range_count hN hlog)
  have hcK : (K.card:ℝ) ≤ (5/2:ℝ) * Real.log (N:ℝ) :=
    (by exact_mod_cast Finset.card_le_card hK :
      (K.card:ℝ) ≤ ((Finset.range (⌈Real.log (N:ℝ)/2⌉₊+1)).card:ℝ)).trans
      (horizontal_range_count hlog)
  simpa only [pow_two] using
    aggregate_three I J K F (k₁ := 1) (k₂ := 1) (k₃ := 1) (k := k)
      (zero_le_one.trans hlog) h2 h2 (by norm_num : (0:ℝ) ≤ 5/2) hD hA
      (by simpa only [pow_one] using hcI) (by simpa only [pow_one] using hcJ)
      (by simpa only [pow_one] using hcK) hF

/-- If the density theorem only applies below a fixed horizontal threshold H,
clip the last bin's upper edge at H. The same width bound still applies. -/
theorem clipped_horizontal_bin {N b δ H : ℝ} (hN : 1 < N)
    (hb : 0 ≤ b) (hbδ : b ≤ δ) (hδH : δ ≤ H) (hH : H ≤ 1/2) :
    ∃ ν : ℕ, ν ≤ ⌈Real.log N / 2⌉₊ ∧
      let h := min H ((ν:ℝ)/Real.log N)
      b ≤ h ∧ h ≤ H ∧ h - 1/Real.log N ≤ δ ∧ δ ≤ h := by
  obtain ⟨ν, _, hν, hlo, hhi⟩ := choose_horizontal_bin hN hb hbδ (hδH.trans hH)
  refine ⟨ν, hν, ?_⟩
  dsimp
  have ht := le_min hδH hhi
  exact ⟨hbδ.trans ht, min_le_left _ _, (sub_le_sub_right (min_le_right _ _) _).trans hlo, ht⟩

#print axioms clipped_horizontal_bin
#print axioms aggregate_pintz_scales
#print axioms choose_horizontal_bin
#print axioms binary_range_count
#print axioms horizontal_range_count
#print axioms horizontal_loss
#print axioms aggregate_three
#print axioms absorb_log_saving
end PintzFiniteDyadicAggregation
