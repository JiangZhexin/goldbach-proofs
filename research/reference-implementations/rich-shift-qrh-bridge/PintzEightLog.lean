import PintzEightSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/- Narrow port of OAI JointDickman TotientDivisorBound and FiniteFourier
   ConvolutionTotientHarmonic. No prime Mertens input: uses elementary harmonic bounds. -/
open Finset
namespace PintzEightLog
noncomputable section
lemma reciprocal_square_initial_sum (X : ℕ) :
    (∑ k ∈ Ioc 0 X, 1/(k:ℝ)^2) ≤ 2 := by
  have he : Ioc 0 X = Ioo 0 (X+1) := by
    ext k
    simp only [mem_Ioc,mem_Ioo]
    omega
  rw [he]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (X+1))

lemma reciprocal_initial_sum (q : ℕ) :
    (∑ r ∈ Ioc 0 q, 1/(r:ℝ)) ≤ 1+Real.log q := by
  have he : Ioc 0 q = Icc 1 q := by
    ext r
    simp only [mem_Ioc,mem_Icc]
    omega
  rw [he]
  simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using
    harmonic_le_one_add_log q

theorem log_one_sub_add_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  have hbase : |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_of_nonneg hx, add_comm] using h
  have hden : 0 < 1 - x := by linarith
  apply hbase.trans
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

theorem inverse_product_le_exp {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    (∏ i ∈ P, (1 - x i)⁻¹) ≤ Real.exp (2 * ∑ i ∈ P, x i) := by
  have hpoint (i : ι) (hi : i ∈ P) : (1 - x i)⁻¹ ≤ Real.exp (2 * x i) := by
    have hpos : 0 < 1 - x i := by linarith [(hx i hi).2]
    have herr := log_one_sub_add_error (hx i hi).1 (hx i hi).2
    have hlog : Real.log ((1 - x i)⁻¹) ≤ 2 * x i := by
      rw [Real.log_inv]
      have hmul := mul_nonneg (hx i hi).1 (show 0 ≤ 1 - 2 * x i by linarith [(hx i hi).2])
      nlinarith [(abs_le.mp herr).1]
    calc
      _ = Real.exp (Real.log ((1 - x i)⁻¹)) := (Real.exp_log (inv_pos.mpr hpos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  calc
    _ ≤ ∏ i ∈ P, Real.exp (2 * x i) := prod_le_prod₀
      (fun i hi => inv_nonneg.mpr (by linarith [(hx i hi).2])) hpoint
    _ = Real.exp (∑ i ∈ P, 2 * x i) := (Real.exp_sum P (fun i => 2 * x i)).symm
    _ = _ := by rw [← mul_sum]

theorem totient_eq_prime_product_real (q : ℕ) :
    (q.totient : ℝ) = q*∏ p ∈ q.primeFactors, (1-1/(p : ℝ)) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_prod,Rat.cast_sub,
    Rat.cast_one,Rat.cast_inv,one_div] using h

lemma prime_subset_reciprocal_product_le_divisors {n : ℕ} (hn : 0 < n) :
    (∏ p ∈ n.primeFactors, (1+1/(p:ℝ))) ≤
      ∑ d ∈ n.divisors, 1/(d:ℝ) := by
  classical
  rw [prod_one_add]
  let e := fun S : Finset ℕ => ∏ p ∈ S, p
  have hi : Set.InjOn e n.primeFactors.powerset := by
    intro S hS T hT he
    change S ∈ n.primeFactors.powerset at hS
    change T ∈ n.primeFactors.powerset at hT
    have hSP := mem_powerset.mp hS
    have hTP := mem_powerset.mp hT
    have hpS : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hSP hp)
    have hpT : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hTP hp)
    have he' := congrArg Nat.primeFactors he
    simpa only [e,Nat.primeFactors_prod hpS,Nat.primeFactors_prod hpT] using he'
  have him : n.primeFactors.powerset.image e ⊆ n.divisors := by
    intro d hd
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨
      (prod_dvd_prod_of_subset S n.primeFactors id (mem_powerset.mp hS)).trans
        (Nat.prod_primeFactors_dvd n),hn.ne'⟩
  apply sum_le_sum_of_injOn e hi him
  · intro S hS
    dsimp [e]
    simp only [Nat.cast_prod,one_div,prod_inv_distrib]
    exact le_rfl
  · intro d hd _
    positivity

lemma totient_ratio_prime_product {n : ℕ} (hn : 0 < n) :
    (n:ℝ)/n.totient = ∏ p ∈ n.primeFactors, (1-1/(p:ℝ))⁻¹ := by
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) : 0 < 1-1/(p:ℝ) := by
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have hprod : 0 < ∏ p ∈ n.primeFactors, (1-1/(p:ℝ)) := prod_pos hfactor
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [totient_eq_prime_product_real,prod_inv_distrib]
  field_simp

/-- The absolute constant is uniform in n. This is the divisor expansion
needed when summing a rational phase with weight n/φ(n). -/
theorem totient_ratio_le_divisor_reciprocals {n : ℕ} (hn : 0 < n) :
    (n:ℝ)/n.totient ≤ Real.exp 4 * ∑ d ∈ n.divisors, 1/(d:ℝ) := by
  have hp2 (p : ℕ) (hp : p ∈ n.primeFactors) : (2:ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hx (p : ℕ) (hp : p ∈ n.primeFactors) :
      0 ≤ 1/(p:ℝ)^2 ∧ 1/(p:ℝ)^2 ≤ 1/2 := by
    constructor
    · positivity
    · have hp' := hp2 p hp
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith : (0:ℝ) < p))).mpr
      nlinarith
  have hquad := inverse_product_le_exp n.primeFactors (fun p => 1/(p:ℝ)^2) hx
  have hsum : (∑ p ∈ n.primeFactors, 1/(p:ℝ)^2) ≤ 2 := by
    refine (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)).trans
      (reciprocal_square_initial_sum n)
    intro p hp
    exact mem_Ioc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).pos,Nat.le_of_mem_primeFactors hp⟩
  have hquad' : (∏ p ∈ n.primeFactors, (1-1/(p:ℝ)^2)⁻¹) ≤ Real.exp 4 :=
    hquad.trans (Real.exp_le_exp.mpr (by linarith))
  have he (p : ℕ) (hp : p ∈ n.primeFactors) :
      (1-1/(p:ℝ))⁻¹ = (1+1/(p:ℝ))*(1-1/(p:ℝ)^2)⁻¹ := by
    have hp' := hp2 p hp
    have hp0 : (p:ℝ) ≠ 0 := by linarith
    have h1 : 1-1/(p:ℝ) ≠ 0 := by
      have hh := (div_lt_one (by linarith : (0:ℝ) < p)).mpr (by linarith : (1:ℝ) < p)
      linarith
    have h2 : 1-1/(p:ℝ)^2 ≠ 0 := by linarith [(hx p hp).2]
    have hid : (1-1/(p:ℝ))*(1+1/(p:ℝ)) = 1-1/(p:ℝ)^2 := by
      field_simp
      ring
    rw [←div_eq_mul_inv]
    apply (eq_div_iff h2).mpr
    rw [←hid,←mul_assoc,inv_mul_cancel₀ h1,one_mul]
  rw [totient_ratio_prime_product hn]
  calc
    _ = (∏ p ∈ n.primeFactors, (1+1/(p:ℝ))) *
        (∏ p ∈ n.primeFactors, (1-1/(p:ℝ)^2)⁻¹) := by
      rw [←prod_mul_distrib]
      exact prod_congr rfl he
    _ ≤ (∏ p ∈ n.primeFactors, (1+1/(p:ℝ))) * Real.exp 4 :=
      mul_le_mul_of_nonneg_left hquad' (prod_nonneg (fun p hp => by positivity))
    _ ≤ Real.exp 4 * ∑ d ∈ n.divisors, 1/(d:ℝ) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (prime_subset_reciprocal_product_le_divisors hn) (Real.exp_pos 4).le

lemma sum_Ioc_divisors_reindex {R : Type*} [AddCommMonoid R]
    (G : ℕ → ℕ → R) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, ∑ d ∈ n.divisors, G d (n/d)) =
      ∑ d ∈ Ioc 0 X, ∑ k ∈ Ioc 0 (X/d), G d k := by
  have hprod : (∑ n ∈ Ioc 0 X, ∑ d ∈ n.divisors, G d (n/d)) =
      ∑ x ∈ (Ioc 0 X ×ˢ Ioc 0 X).filter (fun x => x.1*x.2 ≤ X), G x.1 x.2 := by
    calc
      _ = ∑ n ∈ Ioc 0 X, ∑ x ∈ (Ioc 0 X ×ˢ Ioc 0 X).filter
          (fun x => x.1*x.2=n), G x.1 x.2 := by
        apply sum_congr rfl
        intro n hn
        rw [←Nat.sum_divisorsAntidiagonal G,
          Nat.divisorsAntidiagonal_eq_prod_filter_of_le (mem_Ioc.mp hn).1.ne' (mem_Ioc.mp hn).2]
      _ = _ := by
        simp_rw [sum_filter]
        rw [sum_comm]
        apply sum_congr rfl
        intro x hx
        obtain ⟨hx1,hx2⟩ := mem_product.mp hx
        have hpos : 0 < x.1*x.2 := Nat.mul_pos (mem_Ioc.mp hx1).1 (mem_Ioc.mp hx2).1
        simp [hpos,eq_comm]
  rw [hprod,sum_filter,sum_product]
  apply sum_congr rfl
  intro d hd
  simp only [sum_ite,not_le,sum_const_zero,add_zero]
  congr 1
  ext k
  simp only [mem_filter,mem_Ioc]
  have hd0 := (mem_Ioc.mp hd).1
  constructor
  · rintro ⟨⟨hk0,hkX⟩,hmul⟩
    exact ⟨hk0,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hmul)⟩
  · rintro ⟨hk0,hkdiv⟩
    have hmul := (Nat.le_div_iff_mul_le hd0).mp hkdiv
    exact ⟨⟨hk0,hkdiv.trans (Nat.div_le_self _ _)⟩,by simpa [mul_comm] using hmul⟩

theorem totient_weighted_sum_le_divisor_sum (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n) (X : ℕ) :
    (∑ h ∈ Ioc 0 X, ((h:ℝ)/h.totient)*F h) ≤
      Real.exp 4 * ∑ d ∈ Ioc 0 X, (1/(d:ℝ)) * ∑ k ∈ Ioc 0 (X/d), F (d*k) := by
  have hpoint (h : ℕ) (hh : h ∈ Ioc 0 X) :
      ((h:ℝ)/h.totient)*F h ≤
        Real.exp 4 * ∑ d ∈ h.divisors, (1/(d:ℝ))*F (d*(h/d)) := by
    calc
      _ ≤ (Real.exp 4 * ∑ d ∈ h.divisors, 1/(d:ℝ))*F h :=
        mul_le_mul_of_nonneg_right (totient_ratio_le_divisor_reciprocals (mem_Ioc.mp hh).1) (hF h)
      _ = Real.exp 4 * ∑ d ∈ h.divisors, (1/(d:ℝ))*F (d*(h/d)) := by
        rw [mul_assoc,sum_mul]
        congr 1
        apply sum_congr rfl
        intro d hd
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  calc
    _ ≤ ∑ h ∈ Ioc 0 X, Real.exp 4 * ∑ d ∈ h.divisors, (1/(d:ℝ))*F (d*(h/d)) :=
      sum_le_sum hpoint
    _ = Real.exp 4 * ∑ d ∈ Ioc 0 X, ∑ k ∈ Ioc 0 (X/d), (1/(d:ℝ))*F (d*k) := by
      rw [←mul_sum]
      exact congrArg (fun x : ℝ => Real.exp 4*x)
        (sum_Ioc_divisors_reindex (fun d k => (1/(d:ℝ))*F (d*k)) X)
    _ = _ := by simp only [mul_sum]

theorem exists_reciprocal_totient_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H →
      (∑ h ∈ Icc 1 H, (h.totient : ℝ)⁻¹) ≤ C * (1 + Real.log H) := by
  refine ⟨Real.exp 4 * 2, by positivity, ?_⟩
  intro H hH
  have hint : Icc 1 H = Ioc 0 H := by ext x; simp [Nat.lt_iff_add_one_le]
  rw [hint]
  have hsum := totient_weighted_sum_le_divisor_sum (fun k => 1 / (k : ℝ))
    (fun k => by positivity) H
  have hleft (h : ℕ) (hh : h ∈ Ioc 0 H) :
      (h : ℝ) / h.totient * (1 / (h : ℝ)) = (h.totient : ℝ)⁻¹ := by
    have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.mp hh).1.ne'
    field_simp
  have hinner (d : ℕ) :
      (∑ k ∈ Ioc 0 (H / d), 1 / (k : ℝ)) ≤ 1 + Real.log H := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity))
      (reciprocal_initial_sum H)
    exact Ioc_subset_Ioc le_rfl (Nat.div_le_self H d)
  have hterm (d : ℕ) :
      1 / (d : ℝ) * ∑ k ∈ Ioc 0 (H / d), 1 / ((d*k : ℕ) : ℝ) ≤
        1 / (d : ℝ)^2 * (1 + Real.log H) := by
    simp only [Nat.cast_mul, one_div, mul_inv]
    rw [← mul_sum, ← mul_assoc, ← mul_inv, ← sq]
    exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hinner d) (by positivity)
  rw [sum_congr rfl hleft] at hsum
  calc
    _ ≤ _ := hsum
    _ ≤ Real.exp 4 * ∑ d ∈ Ioc 0 H, 1 / (d : ℝ)^2 * (1 + Real.log H) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun d _ => hterm d) (Real.exp_pos _).le
    _ = Real.exp 4 * ((∑ d ∈ Ioc 0 H, 1 / (d : ℝ)^2) * (1 + Real.log H)) := by rw [sum_mul]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (reciprocal_square_initial_sum H)
        (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ H by exact_mod_cast hH)]))
        (Real.exp_pos _).le


#print axioms exists_reciprocal_totient_sum_bound
end
end PintzEightLog
