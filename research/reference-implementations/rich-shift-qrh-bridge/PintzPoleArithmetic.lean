import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset
namespace PintzPoleArithmetic

theorem totient_real_prod {q : ℕ} (hq : Squarefree q) :
    (q.totient:ℝ) = ∏ p ∈ q.primeFactors, ((p:ℝ)-1) := by
  have ht : q.totient = ∏ p ∈ q.primeFactors, (p-1) := by
    rw [Nat.totient_eq_div_primeFactors_mul q,
      Nat.prod_primeFactors_of_squarefree hq,
      Nat.div_self (Nat.pos_of_ne_zero hq.ne_zero), one_mul]
  rw [ht, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.mem_primeFactors.mp hp).1.one_le, Nat.cast_one]

theorem prime_factor_bound {p : ℕ} (hp : p.Prime) :
    (p:ℝ)^3 ≤ (if p ≤ 3 then (p:ℝ)^3 else 1) * ((p:ℝ)-1)^4 := by
  have hpr : 1 ≤ (p:ℝ)-1 := by
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  split_ifs with h
  · apply le_mul_of_one_le_right (by positivity)
    exact one_le_pow₀ hpr
  · have h4 : 4 ≤ (p:ℝ) := by exact_mod_cast (show 4 ≤ p by omega)
    let t : ℝ := (p:ℝ)-4
    have ht : 0 ≤ t := by dsimp [t]; linarith
    rw [one_mul, show (p:ℝ) = t+4 by simp [t]]
    nlinarith [sq_nonneg t, pow_nonneg ht 3, pow_nonneg ht 4]

theorem cube_le_const_totient_fourth {q : ℕ} (hq : Squarefree q) :
    (q:ℝ)^3 ≤ 216 * (q.totient:ℝ)^4 := by
  let f := fun p : ℕ => if p ≤ 3 then (p:ℝ)^3 else 1
  have hB : (∏ p ∈ q.primeFactors, f p) ≤ 216 := by
    have hsmall : q.primeFactors.filter (fun p => p ≤ 3) ⊆ ({2,3}:Finset ℕ) := by
      intro p hp
      obtain ⟨hpq,hp3⟩ := Finset.mem_filter.mp hp
      have hp2 := (Nat.mem_primeFactors.mp hpq).1.two_le
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have he : (∏ p ∈ q.primeFactors, f p) =
        ∏ p ∈ q.primeFactors.filter (fun p => p ≤ 3), (p:ℝ)^3 := by
      rw [Finset.prod_filter]
    rw [he]
    calc
      _ ≤ ∏ p ∈ ({2,3}:Finset ℕ), (p:ℝ)^3 := by
        apply Finset.prod_le_prod_of_subset_of_one_le₀ hsmall (fun p _ => by positivity)
        intro p hp _
        have h2 : 1 ≤ (p:ℝ) := by
          simp at hp
          rcases hp with rfl | rfl <;> norm_num
        exact one_le_pow₀ h2
      _ = 216 := by norm_num
  have hqprod : (q:ℝ) = ∏ p ∈ q.primeFactors, (p:ℝ) := by
    simpa only [Nat.cast_prod] using congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_primeFactors_of_squarefree hq).symm
  calc
    (q:ℝ)^3 = ∏ p ∈ q.primeFactors, (p:ℝ)^3 := by rw [hqprod, Finset.prod_pow]
    _ ≤ ∏ p ∈ q.primeFactors, f p * ((p:ℝ)-1)^4 := by
      apply Finset.prod_le_prod₀ (fun p _ => by positivity)
      intro p hp
      exact prime_factor_bound (Nat.mem_primeFactors.mp hp).1
    _ = (∏ p ∈ q.primeFactors, f p) * (q.totient:ℝ)^4 := by
      rw [Finset.prod_mul_distrib, totient_real_prod hq, Finset.prod_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_right hB (by positivity)

theorem root_denominator_bound {q : ℕ} (hq : Squarefree q) :
    (q:ℝ) / (q.totient:ℝ)^2 ≤ 15 / Real.sqrt (q:ℝ) := by
  have hqpos : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq.ne_zero
  have ht : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq.ne_zero)
  apply (div_le_div_iff₀ (by positivity) (Real.sqrt_pos.2 hqpos)).2
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (2:ℕ) ≠ 0)).1
  rw [mul_pow, Real.sq_sqrt hqpos.le, mul_pow]
  have H := cube_le_const_totient_fourth hq
  nlinarith [pow_nonneg ht.le 4]


theorem inverse_sqrt_sum (T : ℕ) :
    (∑ k ∈ Finset.Icc 1 T, (Real.sqrt (k:ℝ))⁻¹) ≤ 2 * Real.sqrt (T:ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T+1)]
    rw [Nat.cast_succ]
    have hu := Real.sq_sqrt (show (0:ℝ) ≤ T by positivity)
    have hv := Real.sq_sqrt (show (0:ℝ) ≤ (T:ℝ)+1 by positivity)
    have hs : Real.sqrt ((T:ℝ)+1) > 0 := by positivity
    have hc : (Real.sqrt ((T:ℝ)+1))⁻¹ ≤
        2 * (Real.sqrt ((T:ℝ)+1) - Real.sqrt T) := by
      rw [← one_div, div_le_iff₀ hs]
      have hm : Real.sqrt (T:ℝ) ≤ Real.sqrt ((T:ℝ)+1) :=
        Real.sqrt_le_sqrt (by linarith)
      nlinarith [sq_nonneg (Real.sqrt ((T:ℝ)+1) - Real.sqrt (T:ℝ))]
    linarith

theorem weighted_multiples_bound (P d : ℕ) (hd : 0 < d) :
    (∑ q ∈ (Finset.Icc 1 P).filter (fun q => d ∣ q),
      (d:ℝ) / Real.sqrt (q:ℝ)) ≤ 2 * Real.sqrt (P:ℝ) := by
  have he :
      (∑ k ∈ Finset.Icc 1 (P/d), (d:ℝ) / Real.sqrt ((d*k:ℕ):ℝ)) =
      ∑ q ∈ (Finset.Icc 1 P).filter (fun q => d ∣ q), (d:ℝ) / Real.sqrt (q:ℝ) := by
    classical
    apply Finset.sum_bij (fun k _ => d*k)
    · intro k hk
      obtain ⟨hk1,hk2⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd (by omega),
          by rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hd).mp hk2⟩, dvd_mul_right _ _⟩
    · intro a ha b hb h
      exact (Nat.eq_of_mul_eq_mul_left hd h)
    · intro q hq
      obtain ⟨hqI, k, rfl⟩ := Finset.mem_filter.mp hq
      obtain ⟨h1,hP⟩ := Finset.mem_Icc.mp hqI
      refine ⟨k, Finset.mem_Icc.mpr ⟨?_,?_⟩, rfl⟩
      · by_contra! h
        have : k = 0 := by omega
        simp [this] at h1
      · apply (Nat.le_div_iff_mul_le hd).2
        rwa [Nat.mul_comm]
    · simp
  rw [← he]
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have he' (k : ℕ) : (d:ℝ) / Real.sqrt ((d*k:ℕ):ℝ) =
      Real.sqrt (d:ℝ) * (Real.sqrt (k:ℝ))⁻¹ := by
    rw [Nat.cast_mul, Real.sqrt_mul hdR.le]
    calc
      _ = (Real.sqrt (d:ℝ)*Real.sqrt (d:ℝ)) /
          (Real.sqrt (d:ℝ)*Real.sqrt (k:ℝ)) := by rw [← pow_two,Real.sq_sqrt hdR.le]
      _ = _ := by rw [mul_div_mul_left _ _ (Real.sqrt_pos.2 hdR).ne', div_eq_mul_inv]
  simp_rw [he', ← Finset.mul_sum]
  calc
    _ ≤ Real.sqrt (d:ℝ) * (2 * Real.sqrt ((P/d : ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left (inverse_sqrt_sum _) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (((d*(P/d):ℕ):ℝ)) := by
      rw [Nat.cast_mul, Real.sqrt_mul hdR.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.mul_div_le P d)) (by norm_num)

/-- Elementary denominator summation under the local divisor envelope. -/
theorem weighted_divisor_sum_bound (m P : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (T : ℕ → ℝ)
    (hT : ∀ q ∈ Finset.Icc 1 P, T q ≤ C * (∑ d ∈ m.divisors.filter (fun d => d ∣ q),
      (d:ℝ)/Real.sqrt (q:ℝ))) :
    (∑ q ∈ Finset.Icc 1 P, T q) ≤ 2 * C * Real.sqrt (P:ℝ) * (m.divisors.card:ℝ) := by
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 P, C * (∑ d ∈ m.divisors.filter (fun d => d ∣ q),
      (d:ℝ)/Real.sqrt (q:ℝ)) := Finset.sum_le_sum hT
    _ = C * (∑ d ∈ m.divisors, ∑ q ∈ (Finset.Icc 1 P).filter (fun q => d ∣ q),
      (d:ℝ)/Real.sqrt (q:ℝ)) := by
      simp only [Finset.sum_filter, ← Finset.mul_sum]
      apply congrArg (fun x : ℝ => C*x)
      exact Finset.sum_comm
    _ ≤ C * (∑ _ ∈ m.divisors, 2 * Real.sqrt (P:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum (fun d hd => weighted_multiples_bound P d (Nat.pos_of_mem_divisors hd))
    _ = _ := by simp; ring

#print axioms weighted_divisor_sum_bound
#print axioms root_denominator_bound
end PintzPoleArithmetic
