import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

open Finset

namespace PintzDetectorFinite

/-- Finite final-index convolution, regrouped without any tail argument. -/
theorem regroup {A : Type*} [AddCommMonoid A] (L J : ℕ) (F : ℕ → ℕ → A) :
    (∑ n ∈ Icc 1 J, ∑ d ∈ n.divisors.filter (fun d => d ≤ L), F d (n/d)) =
      ∑ d ∈ Icc 1 L, ∑ k ∈ Icc 1 (J/d), F d k := by
  classical
  let U := ((Icc 1 L) ×ˢ (Icc 1 J)).filter (fun p : ℕ × ℕ => p.1*p.2 ≤ J)
  let m (p : ℕ × ℕ) := p.1*p.2
  have hm (p : ℕ × ℕ) (hp : p ∈ U) : m p ∈ Icc 1 J := by
    have h := mem_filter.mp hp
    obtain ⟨hd,hk⟩ := mem_product.mp h.1
    exact mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp hd).1 (mem_Icc.mp hk).1,h.2⟩
  have h₁ (n : ℕ) (hn : n ∈ Icc 1 J) :
      (∑ d ∈ n.divisors.filter (fun d => d ≤ L), F d (n/d)) =
        ∑ p ∈ U.filter (fun p => m p = n), F p.1 p.2 := by
    have hn₀ : n ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hn).1
    symm
    apply sum_bij (fun p _ => p.1)
    · intro p hp
      obtain ⟨hp,he⟩ := mem_filter.mp hp
      obtain ⟨hp,_⟩ := mem_filter.mp hp
      have hL := (mem_Icc.mp (mem_product.mp hp).1).2
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨p.2,he.symm⟩,hn₀⟩,hL⟩
    · intro p hp q hq hpq
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      have hpos := (mem_Icc.mp (mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1).1).1
      have he : p.1*p.2 = p.1*q.2 := by change p.1*p.2 = n at hp'; change q.1*q.2 = n at hq'; rw [hp', hpq, hq']
      exact Prod.ext hpq (Nat.eq_of_mul_eq_mul_left hpos he)
    · intro d hd
      obtain ⟨hd,hL⟩ := mem_filter.mp hd
      obtain ⟨hdiv,_⟩ := Nat.mem_divisors.mp hd
      have hd₀ := Nat.pos_of_dvd_of_pos hdiv (mem_Icc.mp hn).1
      have hdN := Nat.le_of_dvd (mem_Icc.mp hn).1 hdiv
      have hk : 1 ≤ n/d := Nat.div_pos hdN hd₀
      have he : d*(n/d) = n := Nat.mul_div_cancel' hdiv
      have hp : (d,n/d) ∈ U := mem_filter.mpr
        ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hd₀,hL⟩,
          mem_Icc.mpr ⟨hk,(Nat.div_le_self _ _).trans (mem_Icc.mp hn).2⟩⟩,
          he.le.trans (mem_Icc.mp hn).2⟩
      exact ⟨(d,n/d),mem_filter.mpr ⟨hp,he⟩,rfl⟩
    · intro p hp
      obtain ⟨hp,he⟩ := mem_filter.mp hp
      have hd₀ := (mem_Icc.mp (mem_product.mp (mem_filter.mp hp).1).1).1
      change p.1*p.2 = n at he
      rw [← he, Nat.mul_comm, Nat.mul_div_cancel _ hd₀]
  have h₂ (d : ℕ) (hd : d ∈ Icc 1 L) :
      (∑ p ∈ U.filter (fun p => p.1 = d), F p.1 p.2) =
        ∑ k ∈ Icc 1 (J/d), F d k := by
    have hd₀ := (mem_Icc.mp hd).1
    apply sum_bij (fun p _ => p.2)
    · intro p hp
      obtain ⟨hpu,he⟩ := mem_filter.mp hp
      obtain ⟨hu,hJ⟩ := mem_filter.mp hpu
      refine mem_Icc.mpr ⟨(mem_Icc.mp (mem_product.mp hu).2).1,(Nat.le_div_iff_mul_le hd₀).2 ?_⟩
      simpa [he,Nat.mul_comm] using hJ
    · intro p hp q hq he
      exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) he
    · intro k hk
      have hk' := mem_Icc.mp hk
      have hJ : d*k ≤ J := by
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd₀).1 hk'.2
      have hp : (d,k) ∈ U := mem_filter.mpr
        ⟨mem_product.mpr ⟨hd,mem_Icc.mpr ⟨hk'.1,hk'.2.trans (Nat.div_le_self _ _)⟩⟩,hJ⟩
      exact ⟨(d,k),mem_filter.mpr ⟨hp,rfl⟩,rfl⟩
    · intro p hp
      rw [(mem_filter.mp hp).2]
  calc
    _ = ∑ n ∈ Icc 1 J, ∑ p ∈ U.filter (fun p => m p = n), F p.1 p.2 := sum_congr rfl h₁
    _ = ∑ p ∈ U, F p.1 p.2 := sum_fiberwise_of_maps_to hm _
    _ = ∑ d ∈ Icc 1 L, ∑ p ∈ U.filter (fun p => p.1 = d), F p.1 p.2 :=
      (sum_fiberwise_of_maps_to (fun p hp => (mem_product.mp (mem_filter.mp hp).1).1) _).symm
    _ = _ := sum_congr rfl h₂

noncomputable def alternation (n : ℕ) : ℂ := if 2 ∣ n then -1 else 1

noncomputable def coeff (L n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ L), (ArithmeticFunction.moebius d : ℂ) * alternation (n/d)

theorem coeff_norm (L n : ℕ) : ‖coeff L n‖ ≤ n.divisors.card := by
  classical
  unfold coeff
  calc
    _ ≤ ∑ d ∈ n.divisors.filter (fun d => d ≤ L),
        ‖(ArithmeticFunction.moebius d : ℂ) * alternation (n/d)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors.filter (fun d => d ≤ L), (1:ℝ) := by
      apply sum_le_sum
      intro d _
      have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        norm_cast
        exact ArithmeticFunction.abs_moebius_le_one
      rw [norm_mul, show ‖alternation (n/d)‖ = 1 by unfold alternation; split <;> simp, mul_one]
      exact hμ
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast card_le_card (filter_subset _ _)

/-- The same final cutoff works for all characters and spectral parameters:
specialize the multiplicative weight to χ(n)n^(-ρ). -/
theorem detector_product (L J : ℕ) (g : ℕ → ℂ)
    (hg : ∀ d k, g (d*k) = g d * g k) :
    (∑ n ∈ Icc 1 J, g n * coeff L n) =
      ∑ d ∈ Icc 1 L, g d * (ArithmeticFunction.moebius d : ℂ) *
        (∑ k ∈ Icc 1 (J/d), g k * alternation k) := by
  classical
  calc
    _ = ∑ n ∈ Icc 1 J, ∑ d ∈ n.divisors.filter (fun d => d ≤ L),
        (g d * (ArithmeticFunction.moebius d : ℂ)) * (g (n/d)*alternation (n/d)) := by
      apply sum_congr rfl
      intro n hn
      rw [coeff, mul_sum]
      apply sum_congr rfl
      intro d hd
      have hdiv := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
      have h : g n = g d * g (n/d) :=
        (congrArg g (Nat.mul_div_cancel' hdiv)).symm.trans (hg d (n/d))
      rw [h]
      ring
    _ = ∑ d ∈ Icc 1 L, ∑ k ∈ Icc 1 (J/d),
        (g d * (ArithmeticFunction.moebius d : ℂ)) * (g k*alternation k) := regroup L J (fun d k => (g d * (ArithmeticFunction.moebius d : ℂ)) * (g k*alternation k))
    _ = _ := by simp only [mul_sum]

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable def deltaTwo : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 2 then 1 else 0, by simp⟩

open ArithmeticFunction in
private theorem deltaTwo_zeta_apply {n : ℕ} (hn : n ≠ 0) :
    ((ζ : ArithmeticFunction ℂ) * deltaTwo) n = if 2 ∣ n then 1 else 0 := by
  classical
  rw [coe_zeta_mul_apply]
  change (∑ d ∈ n.divisors, if d = 2 then (1:ℂ) else 0) = _
  simp [Nat.mem_divisors,hn]

/-- The alternating convolution head has only the indices 1 and 2. -/
theorem coeff_head {L n : ℕ} (hn : 0 < n) (hnL : n ≤ L) :
    coeff L n = (if n = 1 then (1:ℂ) else 0) - 2*(if n = 2 then 1 else 0) := by
  classical
  let Z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
  let A : ArithmeticFunction ℂ := Z - (Z * deltaTwo + Z * deltaTwo)
  have hA {m : ℕ} (hm : m ≠ 0) : A m = alternation m := by
    change Z m - ((Z * deltaTwo) m + (Z * deltaTwo) m) = _
    change ((ζ : ArithmeticFunction ℂ) m) - (((ζ : ArithmeticFunction ℂ) * deltaTwo) m + ((ζ : ArithmeticFunction ℂ) * deltaTwo) m) = _
    rw [deltaTwo_zeta_apply hm]
    change ((ArithmeticFunction.zeta m : ℕ) : ℂ) - ((if 2 ∣ m then 1 else 0) + _) = _
    rw [ArithmeticFunction.zeta_apply_ne hm]
    unfold alternation
    split <;> simp [*]
  have hμA : (ArithmeticFunction.moebius * A : ArithmeticFunction ℂ) = 1-(deltaTwo+deltaTwo) := by
    dsimp [A,Z]
    rw [mul_sub,mul_add,← mul_assoc,ArithmeticFunction.coe_moebius_mul_coe_zeta,one_mul]
  have he : coeff L n = (ArithmeticFunction.moebius * A : ArithmeticFunction ℂ) n := by
    unfold coeff
    have hfilter : n.divisors.filter (fun d => d ≤ L) = n.divisors := by
      apply filter_true_of_mem
      intro d hd
      exact (Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1).trans hnL
    rw [hfilter,ArithmeticFunction.mul_apply]
    change (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℂ)*alternation (n/d)) =
      ∑ p ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1:ℂ)*A p.2
    rw [Nat.sum_divisorsAntidiagonal (fun d k => (ArithmeticFunction.moebius d:ℂ)*A k)]
    apply sum_congr rfl
    intro d hd
    have hdiv := (Nat.mem_divisors.mp hd).1
    have hp : 1 ≤ n/d := Nat.div_pos (Nat.le_of_dvd hn hdiv) (Nat.pos_of_dvd_of_pos hdiv hn)
    rw [hA (Nat.ne_of_gt hp)]
  rw [he,hμA]
  change (1:ArithmeticFunction ℂ) n - (deltaTwo n + deltaTwo n) = _
  rw [ArithmeticFunction.one_apply]
  change _ - ((if n = 2 then (1:ℂ) else 0)+(if n = 2 then 1 else 0)) = _
  ring

/-- Alternation is the ordinary sum minus twice its even-indexed terms. -/
theorem alternating_even (K : ℕ) (g : ℕ → ℂ)
    (hg : ∀ d k, g (d*k) = g d * g k) :
    (∑ n ∈ Icc 1 (2*K), g n * alternation n) =
      (∑ n ∈ Icc 1 (2*K), g n) - 2*g 2*(∑ k ∈ Icc 1 K, g k) := by
  classical
  have he : (∑ n ∈ (Icc 1 (2*K)).filter (fun n => 2 ∣ n), g n) =
      ∑ k ∈ Icc 1 K, g (2*k) := by
    symm
    apply sum_bij (fun k _ => 2*k)
    · intro k hk
      obtain ⟨h₁,h₂⟩ := mem_Icc.mp hk
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,dvd_mul_right 2 k⟩
    · intro k hk l hl h
      omega
    · intro n hn
      obtain ⟨hn,hdiv⟩ := mem_filter.mp hn
      obtain ⟨k,rfl⟩ := hdiv
      obtain ⟨h₁,h₂⟩ := mem_Icc.mp hn
      exact ⟨k,mem_Icc.mpr ⟨by omega,by omega⟩,rfl⟩
    · intros
      rfl
  calc
    _ = ∑ n ∈ Icc 1 (2*K), (g n - 2*(if 2 ∣ n then g n else 0)) := by
      apply sum_congr rfl
      intro n _
      by_cases h : 2 ∣ n <;> simp [alternation,h] <;> ring
    _ = (∑ n ∈ Icc 1 (2*K), g n) -
        2*(∑ n ∈ (Icc 1 (2*K)).filter (fun n => 2 ∣ n), g n) := by
      rw [sum_sub_distrib,← mul_sum,sum_filter]
    _ = _ := by rw [he, show (∑ k ∈ Icc 1 K, g (2*k)) = g 2*(∑ k ∈ Icc 1 K, g k) by simp [hg,mul_sum]]; ring

#print axioms alternating_even
#print axioms coeff_head
#print axioms coeff_norm
#print axioms detector_product
#print axioms regroup
end PintzDetectorFinite
