import PintzPoleEuler
import PintzPoleArithmetic
import MajorArcLowerBound

open Finset
namespace PintzPoleEulerFloor

open PintzPoleKernelTail PintzPoleArithmetic

noncomputable def localTerm (p m : ℕ) : ℝ :=
  (if p ∣ m then (p:ℝ)-1 else -1) / ((p:ℝ)-1)^2

theorem weight_ramanujan_prod {q m : ℕ} (hq : Squarefree q) :
    weight q * ramanujan q m = ((∏ p ∈ q.primeFactors, localTerm p m : ℝ):ℂ) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  have hμ : (ArithmeticFunction.moebius q:ℂ)^2 = 1 := by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq
  have hφ :
      (q.totient : ℂ) = ∏ p ∈ q.primeFactors, ((p:ℂ)-1) := by
    have h := congrArg Complex.ofReal (totient_real_prod hq)
    simpa only [Complex.ofReal_natCast, Complex.ofReal_prod, Complex.ofReal_sub,
      Complex.ofReal_one] using h
  rw [weight, hμ, hφ, PintzPoleEuler.pole_ramanujan_eq_crt, PintzPoleEuler.ramanujanSum_squarefree hq,
    ← Finset.prod_pow, Complex.ofReal_prod, one_div, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  unfold localTerm
  simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_natCast,
    Complex.ofReal_one]
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

/-- Exact finite Euler identity: no assertion of Euler-product convergence. -/
theorem sum_divisors_weight_ramanujan {n : ℕ} (hn : Squarefree n) (m : ℕ) :
    (∑ q ∈ n.divisors, weight q * ramanujan q m) =
      ((∏ p ∈ n.primeFactors, (1 + localTerm p m):ℝ):ℂ) := by
  let f : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (fun p => localTerm p m)
  have hf : f.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hfp (p : ℕ) (hp : p ∈ n.primeFactors) : f p = localTerm p m := by
    have h := (Nat.mem_primeFactors.mp hp).1
    simp [f, ArithmeticFunction.prodPrimeFactors_apply h.ne_zero, h.primeFactors]
  have hprod :
      (∏ p ∈ n.primeFactors, (1+localTerm p m)) = ∏ p ∈ n.primeFactors, (1+f p) :=
    Finset.prod_congr rfl (fun p hp => by rw [hfp p hp])
  rw [hprod]
  change (∑ q ∈ n.divisors, weight q * ramanujan q m) =
    ((∏ p ∈ n.primeFactors, (1+f p):ℝ):ℂ) 
  rw [hf.prodPrimeFactors_one_add_of_squarefree hn, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqd := (Nat.mem_divisors.mp hq).1
  have hsq := Squarefree.squarefree_of_dvd hqd hn
  rw [weight_ramanujan_prod hsq]
  congr 1
  exact (ArithmeticFunction.prodPrimeFactors_apply hsq.ne_zero).symm

theorem local_factor_lower {p : ℕ} (hp : 3 ≤ p) (m : ℕ) :
    1 - 1/((p:ℝ)-1)^2 ≤ 1 + localTerm p m := by
  have h2 : (3:ℝ) ≤ p := by exact_mod_cast hp
  unfold localTerm
  split_ifs
  · have h : 0 ≤ ((p:ℝ)-1) / ((p:ℝ)-1)^2 :=
      div_nonneg (sub_nonneg.mpr (by linarith)) (sq_nonneg _)
    linarith [show 0 ≤ (1:ℝ)/((p:ℝ)-1)^2 by positivity]
  · ring_nf
    exact le_rfl

theorem euler_product_floor (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (h2 : 2 ∈ s) {m : ℕ} (hm : Even m) :
    1 ≤ ∏ p ∈ s, (1+localTerm p m) := by
  let t := s.erase 2
  have ht (p : ℕ) (hp : p ∈ t) : 3 ≤ p := by
    obtain ⟨hp2,hps⟩ := Finset.mem_erase.mp hp
    have hp' := (hs p hps).two_le
    omega
  have hdiv : 2 ∣ m := even_iff_two_dvd.mp hm
  have hlocal : 1 + localTerm 2 m = 2 := by
    simp only [localTerm, hdiv, ite_true]
    norm_num
  have hp := Finset.prod_erase_mul (s := s) (fun p => 1+localTerm p m) h2
  rw [hlocal] at hp
  rw [← hp]
  have hbaseline : (1:ℝ) ≤ (∏ p ∈ t, (1 - 1/((p:ℝ)-1)^2))*2 := by
    rw [mul_comm]
    have h := BinaryShiftMajorArc.singular_product_floor t ht 1
    have hf : t.filter (fun p => p ∣ 1) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro p hp
      have h3 := ht p hp
      intro hh
      have hp1 := Nat.dvd_one.mp hh
      omega
    simpa only [hf, Finset.prod_empty, mul_one] using h
  apply hbaseline.trans
  apply mul_le_mul_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
  apply Finset.prod_le_prod₀ _ (fun p hp => local_factor_lower (ht p hp) m)
  intro p hp
  have hpr : (3:ℝ) ≤ p := by exact_mod_cast ht p hp
  have hh : (1:ℝ) ≤ ((p:ℝ)-1)^2 := by nlinarith
  exact sub_nonneg.mpr ((div_le_iff₀ (by linarith : 0<((p:ℝ)-1)^2)).mpr (by simpa using hh))

#print axioms sum_divisors_weight_ramanujan
#print axioms euler_product_floor
end PintzPoleEulerFloor
