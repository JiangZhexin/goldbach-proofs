import PintzPoleEulerFloor
import PintzPoleDivisorTail

open Finset
namespace PintzPoleFiniteSeries

open PintzPoleKernelTail PintzPoleEulerFloor PintzPoleDivisorTail PintzPoleWeightedError

noncomputable def primeSet (P : ℕ) : Finset ℕ :=
  (Finset.range (P+1)).filter Nat.Prime

theorem primeSet_prime {P p : ℕ} (hp : p ∈ primeSet P) : p.Prime :=
  (Finset.mem_filter.mp hp).2

noncomputable def primeBlock (P : ℕ) : ℕ := ∏ p ∈ primeSet P, p

theorem primeBlock_factors (P : ℕ) : (primeBlock P).primeFactors = primeSet P :=
  Nat.primeFactors_prod (fun _ hp => primeSet_prime hp)

theorem primeBlock_squarefree (P : ℕ) : Squarefree (primeBlock P) := by
  unfold primeBlock
  classical
  apply squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hne
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (primeSet_prime hp) (primeSet_prime hq)).mpr hne)
  · exact fun _ hp => (primeSet_prime hp).squarefree

theorem sqfree_div_primeBlock {P q : ℕ} (h : q ≤ P) (hq : Squarefree q) :
    q ∣ primeBlock P := by
  have hsub : q.primeFactors ⊆ primeSet P := by
    intro p hp
    obtain ⟨hp',hpd,_⟩ := Nat.mem_primeFactors.mp hp
    have hpq : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq.ne_zero) hpd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hpq.trans h)),hp'⟩
  have hd := Finset.prod_dvd_prod_of_subset q.primeFactors (primeSet P) (fun p => p) hsub
  rw [Nat.prod_primeFactors_of_squarefree hq] at hd
  exact hd

theorem sum_small_primeBlock (P m : ℕ) :
    (∑ q ∈ (primeBlock P).divisors.filter (fun q => q ≤ P), weight q * ramanujan q m) =
    truncatedSeries P m := by
  unfold truncatedSeries
  classical
  apply Finset.sum_subset
  · intro q hq
    obtain ⟨hd,hP⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,hP⟩
  · intro q hq hn
    have hP := (Finset.mem_Icc.mp hq).2
    have hns : ¬Squarefree q := by
      intro hs
      apply hn
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨sqfree_div_primeBlock hP hs,(primeBlock_squarefree P).ne_zero⟩, hP⟩
    simp [weight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]

/-- A finite real lower bound for the signed denominator truncation, by
comparison with a *finite* Euler product over primes at most P. -/
theorem truncated_series_floor {P m : ℕ} (hP : 2 ≤ P) (hm : 0 < m) (he : Even m) :
    1 - (90/Real.sqrt (P:ℝ))*(m.divisors.card:ℝ) ≤ (truncatedSeries P m).re := by
  classical
  let A := (primeBlock P).divisors.filter (fun q => ¬ q ≤ P)
  let B := max P (primeBlock P)
  have hA : A ⊆ Finset.Ioc P B := by
    intro q hq
    obtain ⟨hdiv,hgt⟩ := Finset.mem_filter.mp hq
    obtain ⟨hd,hn⟩ := Nat.mem_divisors.mp hdiv
    exact Finset.mem_Ioc.mpr
      ⟨lt_of_not_ge hgt,(Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd).trans (le_max_right _ _)⟩
  have hnorm :
      ‖∑ q ∈ A, weight q * ramanujan q m‖ ≤ (90/Real.sqrt (P:ℝ))*(m.divisors.card:ℝ) :=
    (norm_sum_le _ _).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ => norm_nonneg _)).trans
      (finite_ramanujan_tail (by omega) (le_max_left _ _) hm))
  have heq :=
    Finset.sum_filter_add_sum_filter_not (primeBlock P).divisors (fun q => q ≤ P)
      (fun q => weight q * ramanujan q m)
  rw [sum_small_primeBlock, sum_divisors_weight_ramanujan (primeBlock_squarefree P),
    primeBlock_factors] at heq
  have h2 : 2 ∈ primeSet P := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega : 2 < P+1),Nat.prime_two⟩
  have hprod := euler_product_floor (primeSet P) (fun _ hp => primeSet_prime hp) h2 he
  have hre := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.ofReal_re] at hre
  have hA_re := (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans hnorm)
  linarith

/-- Linear floor for the actual finite pole model when the divisor error
parameter is small. This has not asserted any prime/zero approximation. -/
theorem pole_model_floor (P X L N m : ℕ)
    (hP : 2 ≤ P) (hPX : 2*P ≤ X) (hmp : 0 < m) (he : Even m)
    (hm : 2*L ≤ m) (ht : m-2*L < N)
    (hs : X ≤ 4*(m-2*L+1)) (hτ : 360*(m.divisors.card:ℝ) ≤ Real.sqrt (P:ℝ)) :
    (X:ℝ)/8 ≤ (weightedPole P X L N m).re := by
  have hPr : 0 < Real.sqrt (P:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0<P by omega))
  have hτ' : (m.divisors.card:ℝ)/Real.sqrt (P:ℝ) ≤ 1/360 := by
    apply (div_le_iff₀ hPr).2
    linarith
  have htau : (90/Real.sqrt (P:ℝ))*(m.divisors.card:ℝ) ≤ 1/4 := by
    calc
      _ = 90*((m.divisors.card:ℝ)/Real.sqrt (P:ℝ)) := by ring
      _ ≤ _ := by linarith
  have hseries : 3/4 ≤ (truncatedSeries P m).re := by
    have h := truncated_series_floor hP hmp he
    linarith
  let K : ℝ := ((m-2*L+1:ℕ):ℝ)
  have hK : (X:ℝ)/4 ≤ K := by
    have h : (X:ℝ) ≤ 4*K := by
      dsimp [K]
      exact_mod_cast hs
    linarith
  have hintegral := weighted_coefficient_error_divisors P X L N m (by omega) hPX hm hmp ht
  have herror : (15*(X:ℝ)/Real.sqrt (P:ℝ)) * (m.divisors.card:ℝ) ≤ (X:ℝ)/24 := by
    calc
      _ = (15*(X:ℝ)) * ((m.divisors.card:ℝ)/Real.sqrt (P:ℝ)) := by ring
      _ ≤ (15*(X:ℝ))*(1/360) := mul_le_mul_of_nonneg_left hτ' (by positivity)
      _ = _ := by ring
  have hRe := (neg_abs_le _).trans' (neg_le_neg
    ((Complex.abs_re_le_norm _).trans (hintegral.trans herror)))
  simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    mul_zero, sub_zero] at hRe

  change -((X:ℝ)/24) ≤ (weightedPole P X L N m).re - (truncatedSeries P m).re * K at hRe
  have hK0 : 0 ≤ K := by positivity
  nlinarith only [hK,hRe,mul_le_mul_of_nonneg_right hseries hK0, (show (0:ℝ) ≤ X by positivity)]

#print axioms truncated_series_floor
#print axioms pole_model_floor
end PintzPoleFiniteSeries
