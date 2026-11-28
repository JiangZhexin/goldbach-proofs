import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order

open Finset ArithmeticFunction

namespace PintzJutilaPseudo

def psi (r n : ℕ) : ℤ :=
  moebius (r.gcd n) * ((r.gcd n).totient : ℤ)

def support (r s : ℕ) : ℕ :=
  ∏ p ∈ r.primeFactors ∪ s.primeFactors, p

theorem support_squarefree (r s : ℕ) : Squarefree (support r s) :=
  squarefree_prod_of_pairwise_isCoprime
    (fun _ hp _ hq hpq => Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes ((mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors)
        ((mem_union.mp hq).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors)).mpr hpq))
    (fun _ hp => ((mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors).squarefree)

theorem support_primes (r s : ℕ) :
    (support r s).primeFactors = r.primeFactors ∪ s.primeFactors :=
  Nat.primeFactors_prod (fun _ hp => (mem_union.mp hp).elim Nat.prime_of_mem_primeFactors
    Nat.prime_of_mem_primeFactors)

def localCoeff (r s p : ℕ) : ℤ :=
  if p ∈ r.primeFactors ∧ p ∈ s.primeFactors then (p:ℤ)*((p:ℤ)-2) else -(p:ℤ)

/-- The Euler coefficient, extended by zero beyond the squarefree support. -/
def h (d r s : ℕ) : ℤ :=
  if d ∣ support r s then ∏ p ∈ d.primeFactors, localCoeff r s p else 0

theorem totient_squarefree {n : ℕ} (hn : Squarefree n) :
    (n.totient:ℤ) = ∏ p ∈ n.primeFactors, ((p:ℤ)-1) := by
  have H := Nat.totient_mul_prod_primeFactors n
  rw [Nat.prod_primeFactors_of_squarefree hn] at H
  have HH := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn.ne_zero) (H.trans (Nat.mul_comm _ _))
  rw [HH, Nat.cast_prod]
  apply prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]

/-- Purely finite Euler expansion for a squarefree support. -/
theorem expand {A : Type*} [CommSemiring A] {n : ℕ} (hn : Squarefree n) (a : ℕ → A) :
    ∑ d ∈ n.divisors, ∏ p ∈ d.primeFactors, a p = ∏ p ∈ n.primeFactors, (1+a p) := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree hn,
    Nat.sum_divisors_filter_squarefree hn.ne_zero, Nat.factors_eq]
  rw [show (fun p => 1 + a p) = fun p => a p + 1 by funext p; exact add_comm _ _,
    Finset.prod_add]
  apply sum_congr rfl
  intro t ht
  rw [prod_const_one, mul_one, t.prod_val]
  change (∏ p ∈ (∏ i ∈ t, i).primeFactors, a p) = _
  rw [Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors ((mem_powerset.mp ht) hp))]

theorem diagonal {r s : ℕ} (hr : Squarefree r) (hs : Squarefree s) :
    (∑ d ∈ (support r s).divisors, (h d r s : ℚ)/(d:ℚ)) =
    if r = s then (r.totient:ℚ) else 0 := by
  classical
  have hd (d : ℕ) (hm : d ∈ (support r s).divisors) :
      (h d r s : ℚ)/(d:ℚ) = ∏ p ∈ d.primeFactors, (localCoeff r s p : ℚ)/(p:ℚ) := by
    have hf := (support_squarefree r s).squarefree_of_dvd (Nat.dvd_of_mem_divisors hm)
    rw [h, ite_eq_left (Nat.dvd_of_mem_divisors hm), Int.cast_prod, Finset.prod_div_distrib,
      ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hf]
  rw [sum_congr rfl hd, expand (support_squarefree r s), support_primes]
  split_ifs with he
  · subst s
    rw [union_self]
    have hT : (r.totient:ℚ) = ∏ p ∈ r.primeFactors, ((p:ℚ)-1) := by
      exact_mod_cast totient_squarefree hr
    rw [hT]
    apply prod_congr rfl
    intro p hp
    have hp' : (p:ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    simp only [localCoeff, hp, and_self, ite_true, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
      Int.cast_ofNat]
    field_simp [hp']
    ring
  · have hdiff : r.primeFactors ≠ s.primeFactors := by
      intro H
      apply he
      rw [← Nat.prod_primeFactors_of_squarefree hr, ← Nat.prod_primeFactors_of_squarefree hs, H]
    have hex : ∃ p, (p ∈ r.primeFactors ∧ p ∉ s.primeFactors) ∨
        (p ∈ s.primeFactors ∧ p ∉ r.primeFactors) := by
      by_contra! H
      apply hdiff
      ext p
      grind [H p]
    obtain ⟨p,hp⟩ := hex
    have hu : p ∈ r.primeFactors ∪ s.primeFactors := mem_union.mpr (hp.elim (fun hp => Or.inl hp.1) (fun hp => Or.inr hp.1))
    have hnot : ¬ (p ∈ r.primeFactors ∧ p ∈ s.primeFactors) :=
      hp.elim (fun hp h => hp.2 h.2) (fun hp h => hp.2 h.1)
    have hprime := (mem_union.mp hu).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
    have hp' : (p:ℚ) ≠ 0 := by exact_mod_cast hprime.ne_zero
    apply Finset.prod_eq_zero hu
    rw [localCoeff, ite_eq_right hnot, Int.cast_neg, Int.cast_natCast, neg_div, div_self hp']
    ring

/-- The paper's envelope for the total absolute mass of the Euler coefficients. -/
theorem abs_envelope (r s : ℕ) :
    (∑ d ∈ (support r s).divisors, |h d r s|) ≤
      (∏ p ∈ r.primeFactors, ((p:ℤ)+1)) * ∏ p ∈ s.primeFactors, ((p:ℤ)+1) := by
  classical
  have hd (d : ℕ) (hm : d ∈ (support r s).divisors) :
      |h d r s| = ∏ p ∈ d.primeFactors, |localCoeff r s p| := by
    rw [h, ite_eq_left (Nat.dvd_of_mem_divisors hm), Finset.abs_prod]
  rw [sum_congr rfl hd, expand (support_squarefree r s), support_primes,
    ← Finset.prod_union_inter]
  have he : (∏ p ∈ r.primeFactors ∪ s.primeFactors,
      (if p ∈ r.primeFactors ∧ p ∈ s.primeFactors then ((p:ℤ)+1) else 1)) =
      ∏ p ∈ r.primeFactors ∩ s.primeFactors, ((p:ℤ)+1) := by
    rw [← Finset.prod_filter]
    congr 1
    ext p
    simp only [mem_filter, mem_union, mem_inter]
    tauto
  rw [← he, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun p _ => add_nonneg zero_le_one (abs_nonneg (localCoeff r s p))) ?_
  intro p hp
  have hprime := (mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  have h2 : (2:ℤ) ≤ p := by exact_mod_cast hprime.two_le
  by_cases hh : p ∈ r.primeFactors ∧ p ∈ s.primeFactors
  · rw [localCoeff, ite_eq_left hh, ite_eq_left hh, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h2))]
    nlinarith
  · rw [localCoeff, ite_eq_right hh, ite_eq_right hh, abs_neg, abs_of_nonneg (by positivity)]
    ring_nf
    exact le_rfl

def atom (r p : ℕ) : ℤ := if p ∈ r.primeFactors then 1-(p:ℤ) else 1

theorem psi_prod {r n : ℕ} (hr : Squarefree r) (hn : n ≠ 0) :
    psi r n = ∏ p ∈ n.primeFactors, atom r p := by
  have hg := hr.squarefree_of_dvd (Nat.gcd_dvd_left r n)
  rw [psi, ← isMultiplicative_moebius.prod_primeFactors hg, totient_squarefree hg,
    ← Finset.prod_mul_distrib, Nat.primeFactors_gcd hr.ne_zero hn]
  unfold atom
  rw [← Finset.prod_filter]
  have hf : n.primeFactors.filter (fun p => p ∈ r.primeFactors) =
      r.primeFactors ∩ n.primeFactors := by
    ext p
    simp only [mem_filter, mem_inter]
    exact and_comm
  rw [← hf]
  apply prod_congr rfl
  intro p hp
  rw [moebius_apply_prime (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)]
  ring

theorem correlation {r s n : ℕ} (hr : Squarefree r) (hs : Squarefree s) (hn : n ≠ 0) :
    psi r n * psi s n = ∑ d ∈ n.divisors, h d r s := by
  let u := support r s
  let g := u.gcd n
  have hsq := (support_squarefree r s).squarefree_of_dvd (Nat.gcd_dvd_left u n)
  have hsub : g.divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd hn (Nat.gcd_dvd_right u n)
  have he : (∑ d ∈ g.divisors, h d r s) = ∑ d ∈ n.divisors, h d r s := by
    apply sum_subset hsub
    intro d hnd hgd
    apply ite_eq_right
    intro hdu
    exact hgd (Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hdu (Nat.dvd_of_mem_divisors hnd), hsq.ne_zero⟩)
  rw [← he]
  have hd (d) (hd : d ∈ g.divisors) : h d r s = ∏ p ∈ d.primeFactors, localCoeff r s p :=
    ite_eq_left ((Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_left u n))
  rw [sum_congr rfl hd, expand hsq, psi_prod hr hn, psi_prod hs hn, ← prod_mul_distrib]
  have H : g.primeFactors = (r.primeFactors ∪ s.primeFactors) ∩ n.primeFactors := by
    rw [Nat.primeFactors_gcd (support_squarefree r s).ne_zero hn, support_primes]
  rw [H]
  calc
    _ = ∏ p ∈ (r.primeFactors ∪ s.primeFactors) ∩ n.primeFactors, atom r p * atom s p := by
      symm
      apply prod_subset inter_subset_right
      intro p hp hnot
      have hu : p ∉ r.primeFactors ∪ s.primeFactors := fun hu => hnot (mem_inter.mpr ⟨hu,hp⟩)
      have hr' : p ∉ r.primeFactors := fun hp => hu (mem_union_left _ hp)
      have hs' : p ∉ s.primeFactors := fun hp => hu (mem_union_right _ hp)
      rw [atom, atom, ite_eq_right hr', ite_eq_right hs', one_mul]
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      have hp' := mem_union.mp (mem_inter.mp hp).1
      by_cases ha : p ∈ r.primeFactors <;> by_cases hb : p ∈ s.primeFactors
      · simp only [atom, localCoeff, ha,hb,true_and,ite_true]; ring
      · simp only [atom, localCoeff, ha,hb,and_false,ite_true,ite_false]; ring
      · simp only [atom, localCoeff, ha,hb,false_and,ite_true,ite_false]; ring
      · exact False.elim (hp'.elim ha hb)

theorem psi_inter {r n : ℕ} (hr : Squarefree r) (hn : n ≠ 0) :
    psi r n = ∏ p ∈ r.primeFactors ∩ n.primeFactors, (1-(p:ℤ)) := by
  rw [psi_prod hr hn]
  unfold atom
  rw [← prod_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_inter]
  exact and_comm

/-- Finite multiplicative splitting used in the proof of Jutila Lemma 1. -/
theorem twist_split {r d n : ℕ} (hr : Squarefree r) (hd : d ≠ 0) (hn : n ≠ 0) :
    psi r (d*n) = psi r d * psi (r / r.gcd d) n := by
  classical
  have hsq : Squarefree (r / r.gcd d) :=
    hr.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r d))
  rw [psi_inter hr (mul_ne_zero hd hn), psi_inter hr hd, psi_inter hsq hn,
    Nat.primeFactors_div_gcd hr hd, Nat.primeFactors_mul hd hn]
  rw [← prod_union]
  · congr 1
    ext p
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  · apply disjoint_left.mpr
    intro p hp hq
    exact (mem_sdiff.mp (mem_inter.mp hq).1).2 (mem_inter.mp hp).2

@[simp] theorem psi_one (n : ℕ) : psi 1 n = 1 := by
  simp [psi]

/-- Coefficientwise finite identity behind the twisted Dirichlet-series
product: the inner coefficient only uses primes of r not dividing d. -/
theorem mollifier_coefficient {r n : ℕ} (hr : Squarefree r) (hn : n ≠ 0) (ξ : ℕ → ℤ) :
    (∑ d ∈ n.divisors, ξ d) * psi r n =
      ∑ d ∈ n.divisors, (ξ d * psi r d) *
        ∑ e ∈ (n/d).divisors, h e (r / r.gcd d) 1 := by
  rw [sum_mul]
  apply sum_congr rfl
  intro d hd
  obtain ⟨hdiv,_⟩ := Nat.mem_divisors.mp hd
  have hd0 : d ≠ 0 := by
    intro h0
    subst d
    exact hn (by simpa using hdiv)
  have hnd : n/d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv)
    (Nat.pos_of_ne_zero hd0)).ne'
  have hsq : Squarefree (r / r.gcd d) :=
    hr.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r d))
  have hm := correlation hsq (show Squarefree (1:ℕ) by simp) hnd
  rw [psi_one, mul_one] at hm
  rw [← hm, mul_assoc, ← twist_split hr hd0 hnd, Nat.mul_div_cancel' hdiv]

#print axioms mollifier_coefficient
#print axioms twist_split
#print axioms correlation
#print axioms abs_envelope
#print axioms expand
#print axioms diagonal
end PintzJutilaPseudo
