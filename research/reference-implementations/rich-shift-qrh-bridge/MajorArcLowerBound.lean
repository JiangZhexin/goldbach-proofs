import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Complex.Basic

open Filter
open scoped Topology

namespace BinaryShiftMajorArc

noncomputable def deficiency (R : ℕ → ℕ → ℂ) (X : ℕ) : Finset ℕ :=
  @Finset.filter ℕ
    (fun m => Even m ∧ (R X m).re < ((2*X : ℕ) : ℝ) /
      Real.sqrt (Real.log ((2*X : ℕ) : ℝ)))
    (Classical.decPred _) (Finset.Ico X (2*X))

/-- A positive singular-series floor and a relative error at most one
quarter, plus an absolute power-saving error, suffice for the threshold
used in the polynomial minor-arc reduction. Any exceptional frequencies
of the explicit formula are preserved, rather than estimated again. -/
theorem deficiency_subset_of_model
    (R : ℕ → ℕ → ℂ) (singular : ℕ → ℝ) (bad : ℕ → Finset ℕ)
    {c κ B : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (hfloor : ∀ m : ℕ, 4 ≤ m → Even m → c ≤ singular m)
    (happrox : ∀ᶠ X : ℕ in atTop, ∀ m ∈ Finset.Ico X (2*X),
      Even m → m ∉ bad X →
      ‖R X m - ((singular m * m : ℝ) : ℂ)‖ ≤
        singular m * ((2*X : ℕ) : ℝ) / 4 +
          B * ((2*X : ℕ) : ℝ)^(1-κ)) :
    ∀ᶠ X : ℕ in atTop, deficiency R X ⊆ bad X := by
  classical
  have hN : Tendsto (fun X : ℕ => ((2*X : ℕ) : ℝ)) atTop atTop := by
    have ht : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [ht.eventually_ge_atTop (max 0 b)] with X hX
    push_cast
    have hb : b ≤ max 0 b := le_max_right _ _
    have hx : 0 ≤ (X : ℝ) := Nat.cast_nonneg _
    linarith
  have hpow := ((tendsto_rpow_atTop hκ).comp hN).eventually_ge_atTop (8*B/c)
  have hlog := ((Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).comp hN).eventually_ge_atTop (8/c)
  filter_upwards [happrox,hpow,hlog,eventually_ge_atTop (4:ℕ)] with X hA hp hl hX
  intro m hm
  simp only [deficiency, Finset.mem_filter] at hm
  obtain ⟨hmI, hev, hsmall⟩ := hm
  by_contra hb
  let N : ℝ := ((2*X : ℕ) : ℝ)
  have hpos : 0 < N := by dsimp [N]; positivity
  have hκpos : 0 < N ^ κ := Real.rpow_pos_of_pos hpos _
  change 8 / c ≤ Real.sqrt (Real.log N) at hl
  have hspos : 0 < Real.sqrt (Real.log N) := lt_of_lt_of_le (by positivity : 0 < 8/c) hl
  have hmp : (N/2 : ℝ) ≤ m := by
    dsimp [N]
    push_cast
    exact (by exact_mod_cast (Finset.mem_Ico.mp hmI).1 : (X:ℝ) ≤ m) |> fun h => by linarith
  have hs : c ≤ singular m := hfloor _ (hX.trans (Finset.mem_Ico.mp hmI).1) hev
  have hmain := mul_le_mul_of_nonneg_left hmp (hc.le.trans hs)
  have hAbs : B*N^(1-κ) ≤ c*N/8 := by
    rw [Real.rpow_sub hpos, Real.rpow_one]
    rw [← mul_div_assoc, div_le_iff₀ hκpos]
    have hp' : 8*B ≤ N^κ*c := (div_le_iff₀ hc).mp hp
    have h := mul_le_mul_of_nonneg_right hp' hpos.le
    nlinarith only [h]
  have hRe := ((abs_le.mp (Complex.abs_re_le_norm (R X m - ((singular m * m : ℝ) : ℂ)))).1)
  simp only [Complex.sub_re, Complex.ofReal_re] at hRe
  have hraw := hA m hmI hev hb
  change ‖R X m - ((singular m * m : ℝ) : ℂ)‖ ≤ singular m * N / 4 + B * N^(1-κ) at hraw
  have hcs := mul_le_mul_of_nonneg_right hs hpos.le
  have hmaj : c*N/8 ≤ (R X m).re := by linarith only [hRe,hraw,hAbs,hmain,hcs]
  have hthr : N / Real.sqrt (Real.log N) ≤ c*N/8 := by
    apply (div_le_iff₀ hspos).2
    have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).mp hl) hpos.le
    nlinarith only [hh]
  exact (not_lt_of_ge (hthr.trans hmaj)) hsmall

#print axioms deficiency_subset_of_model

/-- The comparison Euler product telescopes over all integers at least 2,
providing a uniform positive bound without evaluating the twin prime constant. -/
theorem tel_product (k : ℕ) :
    (∏ j ∈ Finset.range k, (1-1/((j:ℝ)+2)^2)) = ((k:ℝ)+2)/(2*((k:ℝ)+1)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.prod_range_succ, ih]
    push_cast
    have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    field_simp; ring

/-- Every finite truncation of the usual Goldbach singular product is at
least one, even before including the favorable factors from primes dividing m. -/
theorem singular_product_floor (s : Finset ℕ) (hs : ∀ p ∈ s, 3 ≤ p)
    (m : ℕ) :
    1 ≤ (2:ℝ) * (∏ p ∈ s, (1-1/((p:ℝ)-1)^2)) *
      ∏ p ∈ s.filter (fun p => p ∣ m), (((p:ℝ)-1)/((p:ℝ)-2)) := by
  classical
  let k := s.sup id
  let f := fun j : ℕ => (1-1/((j:ℝ)+2)^2)
  let a := s.image (fun p => p-3)
  have hsub : a ⊆ Finset.range k := by
    intro j hj
    obtain ⟨p,hps,rfl⟩ := Finset.mem_image.mp hj
    have hpk : p ≤ k := Finset.le_sup (f := id) hps
    have hp := hs _ hps
    exact Finset.mem_range.mpr (by omega)
  have hinj : Set.InjOn (fun p : ℕ => p-3) (↑s : Set ℕ) := by
    intro i hi j hj hij
    have hi' := hs i hi
    have hj' := hs j hj
    change i - 3 = j - 3 at hij
    omega
  have hreprod : (∏ p ∈ s, (1-1/((p:ℝ)-1)^2)) = ∏ j ∈ a, f j := by
    rw [Finset.prod_image hinj]
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [f]
    rw [Nat.cast_sub (hs p hp)]
    push_cast
    ring_nf
  have hf01 (j : ℕ) : 0 ≤ f j ∧ f j ≤ 1 := by
    have h : (1:ℝ) ≤ ((j:ℝ)+2)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
    constructor
    · exact sub_nonneg.mpr ((div_le_iff₀ (by linarith : 0 < ((j:ℝ)+2)^2)).mpr (by simpa using h))
    · dsimp [f]
      exact sub_le_self _ (by positivity)
  have hle : (∏ j ∈ Finset.range k, f j) ≤ ∏ j ∈ a, f j :=
    Finset.prod_le_prod_of_subset_of_le_one₀ hsub (fun j _ => (hf01 j).1)
      (fun j _ _ => (hf01 j).2)
  have hhalf : (1:ℝ)/2 ≤ ∏ j ∈ Finset.range k, f j := by
    dsimp [f]
    rw [tel_product]
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have hcor : (1:ℝ) ≤ ∏ p ∈ s.filter (fun p => p ∣ m), (((p:ℝ)-1)/((p:ℝ)-2)) := by
    apply Finset.one_le_prod₀
    intro p hp
    have hp' : (3:ℝ) ≤ p := by exact_mod_cast hs p (Finset.mem_filter.mp hp).1
    apply (le_div_iff₀ (by linarith : 0 < (p:ℝ)-2)).mpr
    linarith
  rw [hreprod]
  have hmain : (1:ℝ) ≤ 2 * (∏ j ∈ a, f j) := by linarith [hhalf.trans hle]
  calc
    1 ≤ 2 * (∏ j ∈ a, f j) := hmain
    _ ≤ _ := le_mul_of_one_le_right (zero_le_one.trans hmain) hcor

#print axioms singular_product_floor

/-- Pass the truncation floor to the conventional infinite singular series. -/
theorem singular_limit_floor
    (s : ℕ → Finset ℕ) (hs : ∀ j p, p ∈ s j → 3 ≤ p)
    (m : ℕ) (S : ℝ)
    (h : Tendsto (fun j => (2:ℝ) * (∏ p ∈ s j, (1-1/((p:ℝ)-1)^2)) *
      ∏ p ∈ (s j).filter (fun p => p ∣ m), (((p:ℝ)-1)/((p:ℝ)-2))) atTop (𝓝 S)) :
    1 ≤ S :=
  ge_of_tendsto h (Eventually.of_forall fun j => singular_product_floor (s j) (hs j) m)

/-- A uniform fixed zero-free half-plane excludes all zeros from a
logarithmically narrowing window for every fixed H. -/
theorem eventually_above_fixed_line {θ H : ℝ} (hθ : θ < 1) :
    ∀ᶠ X : ℕ in atTop, θ < 1-H/Real.log ((2*X : ℕ) : ℝ) := by
  have hn : Tendsto (fun X : ℕ => ((2*X : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ) < 2)).2
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Real.tendsto_log_atTop.comp hn
  have hd := tendsto_const_nhds.div_atTop ht (a := H)
  have h : Tendsto (fun X : ℕ => 1-H/Real.log ((2*X : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Function.comp_apply, sub_zero] using
      (tendsto_const_nhds.sub hd : Tendsto _ atTop (𝓝 ((1:ℝ)-0)))
  exact h.eventually (lt_mem_nhds hθ)

#print axioms singular_limit_floor
#print axioms eventually_above_fixed_line

/-- Consume the exact two-scale error pattern in Pintz's zero-free
specialization. The power-saving constant may depend on the chosen H;
the relative-error prefactor A and decay d must not. -/
theorem deficiency_subset_of_exponential_model
    (R : ℝ → ℕ → ℕ → ℂ) (singular : ℕ → ℝ) (bad : ℕ → Finset ℕ)
    {c κ A d H₀ : ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hA : 0 ≤ A) (hd : 0 < d)
    (hfloor : ∀ m : ℕ, 4 ≤ m → Even m → c ≤ singular m)
    (happrox : ∀ H : ℝ, H₀ ≤ H → ∃ B : ℝ,
      ∀ᶠ X : ℕ in atTop, ∀ m ∈ Finset.Ico X (2*X), Even m → m ∉ bad X →
      ‖R H X m - ((singular m * m : ℝ) : ℂ)‖ ≤
        (A * Real.exp (-d*H)) * (singular m * ((2*X : ℕ) : ℝ)) +
          B * ((2*X : ℕ) : ℝ)^(1-κ)) :
    ∃ H : ℝ, H₀ ≤ H ∧ ∀ᶠ X : ℕ in atTop, deficiency (R H) X ⊆ bad X := by
  let D : ℝ := max 1 (4*A)
  let H : ℝ := max H₀ (Real.log D / d)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hD' : 4*A ≤ D := le_max_right _ _
  have hH : Real.log D / d ≤ H := le_max_right _ _
  have hlog : Real.log D ≤ d*H := by simpa [mul_comm] using (div_le_iff₀ hd).mp hH
  have hE : Real.exp (-d*H) ≤ D⁻¹ := calc
    _ ≤ Real.exp (-Real.log D) := Real.exp_le_exp.mpr (by linarith only [hlog])
    _ = _ := by rw [Real.exp_neg, Real.exp_log hD]
  have hquarter : A * Real.exp (-d*H) ≤ 1/4 := calc
    _ ≤ A * D⁻¹ := mul_le_mul_of_nonneg_left hE hA
    _ ≤ _ := by
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ hD).mpr
      linarith only [hD']
  obtain ⟨B,hB⟩ := happrox H (le_max_left _ _)
  refine ⟨H, le_max_left _ _, ?_⟩
  apply deficiency_subset_of_model (R H) singular bad hc hκ hfloor (B := B)
  filter_upwards [hB,eventually_ge_atTop (4:ℕ)] with X hX h4 m hm hev hmb
  have hs : 0 ≤ singular m := hc.le.trans (hfloor _ (h4.trans (Finset.mem_Ico.mp hm).1) hev)
  have hcomp := mul_le_mul_of_nonneg_right hquarter
    (mul_nonneg hs (Nat.cast_nonneg (2*X)))
  have hY := hX m hm hev hmb
  linarith only [hcomp,hY]

#print axioms deficiency_subset_of_exponential_model
end BinaryShiftMajorArc
