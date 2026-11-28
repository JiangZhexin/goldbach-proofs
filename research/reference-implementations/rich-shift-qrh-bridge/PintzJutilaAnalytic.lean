import PintzJutilaPseudo
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Bounds

open Finset PintzJutilaPseudo
open scoped LSeries.notation
noncomputable section

namespace PintzJutilaAnalytic

def seed (d : ℕ) (c : ℂ) (n : ℕ) : ℂ := if n = d then c else 0

theorem seed_hasSum {d : ℕ} (hd : d ≠ 0) (c s : ℂ) :
    LSeriesHasSum (seed d c) s (c/(d:ℂ)^s) := by
  unfold LSeriesHasSum
  convert hasSum_ite_eq d (c/(d:ℂ)^s) using 1
  funext n
  by_cases he : n = d
  · subst n
    simp [seed, LSeries.term_of_ne_zero hd]
  · by_cases hn : n = 0
    · subst n
      simp [Ne.symm hd]
    · simp [seed, he, LSeries.term_of_ne_zero hn]

def eulerCoeff (χ : ℕ → ℂ) (r n : ℕ) : ℂ := χ n * (h n r 1 : ℂ)

theorem euler_hasSum (χ : ℕ → ℂ) (hχ : ∀ a b, χ (a*b) = χ a*χ b)
    (hχ1 : χ 1 = 1) {r : ℕ} (hr : Squarefree r) (s : ℂ) :
    LSeriesHasSum (eulerCoeff χ r) s
      (∏ p ∈ r.primeFactors, (1-(p:ℂ)*χ p/(p:ℂ)^s)) := by
  have hsup : support r 1 = r := by
    simp [support, Nat.prod_primeFactors_of_squarefree hr]
  have hcalc (d : ℕ) (hd : d ∈ r.divisors) :
      LSeries.term (eulerCoeff χ r) s d =
        ∏ p ∈ d.primeFactors, (-(p:ℂ)*χ p/(p:ℂ)^s) := by
    have hdv := Nat.dvd_of_mem_divisors hd
    have hds := hr.squarefree_of_dvd hdv
    have hχp : χ d = ∏ p ∈ d.primeFactors, χ p := by
      nth_rw 1 [← Nat.prod_primeFactors_of_squarefree hds]
      generalize d.primeFactors = F
      induction F using Finset.induction_on with
      | empty => simpa using hχ1
      | insert a F ha ih => rw [prod_insert ha, hχ, ih, prod_insert ha]
    have hcp : (d:ℂ)^s = ∏ p ∈ d.primeFactors, (p:ℂ)^s := by
      nth_rw 1 [← Nat.prod_primeFactors_of_squarefree hds]
      rw [Nat.cast_prod]
      generalize d.primeFactors = F
      induction F using Finset.induction_on with
      | empty => simp
      | insert a F ha ih =>
        rw [prod_insert ha, prod_insert ha, show (∏ p ∈ F, (p:ℂ)) =
          ((∏ p ∈ F, p : ℕ):ℂ) by push_cast; rfl,
          Complex.natCast_mul_natCast_cpow]
        congr 1
        simpa only [Nat.cast_prod] using ih
    rw [LSeries.term_of_ne_zero hds.ne_zero, eulerCoeff, h, hsup, ite_eq_left hdv,
      Int.cast_prod, hχp, hcp, ← prod_mul_distrib, ← prod_div_distrib]
    apply prod_congr rfl
    intro p _
    simp [localCoeff]
    ring
  have hz (d : ℕ) (hd : d ∉ r.divisors) : LSeries.term (eulerCoeff χ r) s d = 0 := by
    have hnd : ¬d ∣ r := fun H => hd (Nat.mem_divisors.mpr ⟨H,hr.ne_zero⟩)
    simp [LSeries.term, eulerCoeff, h, hsup, hnd]
  unfold LSeriesHasSum
  have hh : HasSum (LSeries.term (eulerCoeff χ r) s)
      (∑ d ∈ r.divisors, LSeries.term (eulerCoeff χ r) s d) := hasSum_sum_of_ne_finset_zero hz
  convert hh using 1
  rw [sum_congr rfl hcalc, expand hr]
  apply prod_congr rfl
  intro p _
  ring

theorem convolution_div (f g : ℕ → ℂ) (n : ℕ) :
    (f ⍟ g) n = ∑ d ∈ n.divisors, f d * g (n/d) := by
  rw [LSeries.convolution_def]
  exact Nat.sum_divisorsAntidiagonal (fun d e => f d*g e)

theorem seed_convolution (d : ℕ) (c : ℂ) (g : ℕ → ℂ) (n : ℕ) :
    (seed d c ⍟ g) n = if d ∈ n.divisors then c*g (n/d) else 0 := by
  rw [convolution_div]
  by_cases hd : d ∈ n.divisors
  · rw [ite_eq_left hd, sum_eq_single_of_mem d hd]
    · simp [seed]
    · intro i _ hi
      simp [seed, hi]
  · rw [ite_eq_right hd]
    apply sum_eq_zero
    intro i hi
    have hne : i ≠ d := fun h => hd (h ▸ hi)
    simp [seed, hne]

theorem euler_convolution (χ : ℕ → ℂ) (hχ : ∀ a b, χ (a*b) = χ a*χ b)
    (r n : ℕ) :
    (eulerCoeff χ r ⍟ χ) n = χ n * ∑ e ∈ n.divisors, (h e r 1 : ℂ) := by
  rw [convolution_div, mul_sum]
  apply sum_congr rfl
  intro e he
  have hm := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)
  rw [eulerCoeff, ← hm, hχ]
  rw [hm]
  ring

end PintzJutilaAnalytic

namespace PintzJutilaAnalytic

def summand (χ : ℕ → ℂ) (ξ : ℕ → ℂ) (r d : ℕ) : ℕ → ℂ :=
  seed d (ξ d * (psi r d:ℂ) * χ d) ⍟ (eulerCoeff χ (r/r.gcd d) ⍟ χ)

def twisted (χ : ℕ → ℂ) (ξ : ℕ → ℂ) (r : ℕ) (n : ℕ) : ℂ :=
  χ n * (psi r n:ℂ) * ∑ d ∈ n.divisors, ξ d

theorem summands_eq (χ : ℕ → ℂ) (hχ : ∀ a b, χ (a*b) = χ a*χ b)
    (ξ : ℕ → ℂ) (K : Finset ℕ) (hK : ∀ d ∉ K, ξ d = 0)
    {r n : ℕ} (hr : Squarefree r) (hn : n ≠ 0) :
    (∑ d ∈ K, summand χ ξ r d n) = twisted χ ξ r n := by
  have he (d : ℕ) : summand χ ξ r d n =
      if d ∈ n.divisors then
        χ n * ((ξ d * (psi r d:ℂ)) *
          ∑ e ∈ (n/d).divisors, (h e (r/r.gcd d) 1 : ℂ)) else 0 := by
    rw [summand, seed_convolution]
    split
    next hd =>
      rw [euler_convolution _ hχ]
      have H : χ d * χ (n/d) = χ n := by
        rw [← hχ, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
      rw [show (ξ d * (psi r d:ℂ) * χ d) *
          (χ (n/d) * ∑ e ∈ (n/d).divisors, (h e (r/r.gcd d) 1 : ℂ)) =
          (χ d * χ (n/d)) * ((ξ d * (psi r d:ℂ)) *
            ∑ e ∈ (n/d).divisors, (h e (r/r.gcd d) 1 : ℂ)) by ring, H]
    next hd => rfl
  simp_rw [he, ← sum_filter]
  let G (d : ℕ) := χ n * ((ξ d * (psi r d:ℂ)) *
    ∑ e ∈ (n/d).divisors, (h e (r/r.gcd d) 1 : ℂ))
  have hsub : K.filter (fun d => d ∈ n.divisors) ⊆ n.divisors := fun _ h => (mem_filter.mp h).2
  change (∑ d ∈ K.filter (fun d => d ∈ n.divisors), G d) = _
  rw [sum_subset hsub (fun d hd hdn => by
    have hkn : d ∉ K := fun hc => hdn (mem_filter.mpr ⟨hc,hd⟩)
    simp [G, hK d hkn])]
  dsimp [G]
  rw [← mul_sum]
  have H : (∑ d ∈ n.divisors, ξ d) * (psi r n:ℂ) =
      ∑ d ∈ n.divisors, (ξ d * (psi r d:ℂ)) *
        ∑ e ∈ (n/d).divisors, (h e (r/r.gcd d) 1 : ℂ) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := by
      intro H
      subst d
      exact hn (by simpa using hdn)
    have hnD : n/d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn)
      (Nat.pos_of_ne_zero hd0)).ne'
    have hsq : Squarefree (r/r.gcd d) :=
      hr.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r d))
    have he : (psi (r/r.gcd d) (n/d):ℂ) =
        ∑ e ∈ (n/d).divisors, (h e (r/r.gcd d) 1 : ℂ) := by
      have H := correlation hsq (show Squarefree (1:ℕ) by simp) hnD
      rw [psi_one, mul_one] at H
      exact_mod_cast H
    rw [← he, mul_assoc, ← Int.cast_mul, ← twist_split hr hd0 hnD, Nat.mul_div_cancel' hdn]
  rw [← H, twisted]
  ring

def mollifier {q : ℕ} (χ : DirichletCharacter ℂ q) (ξ : ℕ → ℂ)
    (K : Finset ℕ) (r : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ K, (ξ d * (psi r d:ℂ) * χ d / (d:ℂ)^s) *
    ∏ p ∈ (r/r.gcd d).primeFactors, (1-(p:ℂ)*χ p/(p:ℂ)^s)

/-- Unlike the infinite Dirichlet series, this finite multiplier can be
evaluated everywhere, including on the shifted integral line. -/
theorem mollifier_entire {q : ℕ} (χ : DirichletCharacter ℂ q) (ξ : ℕ → ℂ)
    (K : Finset ℕ) (hK0 : 0 ∉ K) (r : ℕ) :
    Differentiable ℂ (mollifier χ ξ K r) := by
  have hd (d : ℕ) (hd0 : d ≠ 0) (a : ℂ) :
      Differentiable ℂ (fun s : ℂ => a/(d:ℂ)^s) := by
    have hc : (d:ℂ) ≠ 0 := by exact_mod_cast hd0
    exact (differentiable_const a : Differentiable ℂ (fun _ : ℂ => a)).div (differentiable_id.const_cpow (Or.inl hc))
      (fun s => Complex.cpow_ne_zero_iff.mpr (Or.inl hc))
  unfold mollifier
  apply Differentiable.fun_sum
  intro d hm
  have hpos : d ≠ 0 := fun h => hK0 (h ▸ hm)
  apply (hd d hpos _).mul
  apply Differentiable.fun_finsetProd
  intro p hp
  have hp0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
  exact (differentiable_const (1:ℂ) : Differentiable ℂ (fun _ : ℂ => (1:ℂ))).sub (hd p hp0 _)

/-- Jutila (2.2) with finite mollifier support and absolute convergence;
the correction Euler product ranges over primes dividing r / gcd(r,d). -/
theorem equation_2_2 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) (ξ : ℕ → ℂ) (K : Finset ℕ)
    (hK0 : 0 ∉ K) (hK : ∀ d ∉ K, ξ d = 0) {r : ℕ} (hr : Squarefree r) :
    LSeriesHasSum (twisted (fun n => χ n) ξ r) s
      (χ.LFunction s * mollifier χ ξ K r s) := by
  let ψ : ℕ → ℂ := fun n => χ n
  have hψ (a b : ℕ) : ψ (a*b) = ψ a*ψ b := by simp [ψ]
  have hψ1 : ψ 1 = 1 := by simp [ψ]
  have hsumχ : LSeriesSummable ψ s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => χ.norm_le_one _) hs
  have hχ' : LSeriesHasSum ψ s (χ.LFunction s) :=
    (χ.LFunction_eq_LSeries hs).symm ▸ hsumχ.LSeriesHasSum
  let f (d : ℕ) :=
    (ξ d * (psi r d:ℂ) * χ d / (d:ℂ)^s) *
      ∏ p ∈ (r/r.gcd d).primeFactors, (1-(p:ℂ)*χ p/(p:ℂ)^s)
  have hh (d : ℕ) (hd : d ∈ K) : LSeriesHasSum (summand ψ ξ r d) s (χ.LFunction s * f d) := by
    have hd0 : d ≠ 0 := fun h0 => hK0 (h0 ▸ hd)
    have hsq : Squarefree (r/r.gcd d) :=
      hr.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r d))
    have H := (seed_hasSum hd0 (ξ d * (psi r d:ℂ) * ψ d) s).convolution
      ((euler_hasSum ψ hψ hψ1 hsq s).convolution hχ')
    convert H using 1
    · rfl
    · dsimp only [f, ψ]
      ring
  have H := LSeriesHasSum.sum (S := K) hh
  rw [← mul_sum] at H
  refine (LSeriesHasSum_congr s _ (fun {n} hn => ?_)).mp H
  change (∑ d ∈ K, summand ψ ξ r d) n = twisted ψ ξ r n
  rw [Finset.sum_apply]
  exact summands_eq ψ hψ ξ K hK hr hn

#print axioms mollifier_entire
#print axioms equation_2_2
end PintzJutilaAnalytic
