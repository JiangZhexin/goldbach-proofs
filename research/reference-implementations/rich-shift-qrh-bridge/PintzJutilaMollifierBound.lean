import PintzJutilaAnalytic
import PintzJutilaHarmonicLower

open Finset PintzJutilaPseudo PintzJutilaAnalytic

noncomputable section
namespace PintzJutilaMollifierBound

def envelope (r : ℕ) : ℝ := ∏ p ∈ r.primeFactors, (1+(p:ℝ)⁻¹)

theorem envelope_nonneg (r : ℕ) : 0 ≤ envelope r := by
  unfold envelope
  positivity

private theorem norm_nat_cpow_re_nonneg {n : ℕ} (hn : n ≠ 0) {s : ℂ} (hs : 0 ≤ s.re) :
    1 ≤ ‖(n:ℂ)^s‖ := by
  have hn' : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn']
  exact Real.one_le_rpow hn1 hs

theorem norm_mollifier_re_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 ≤ s.re)
    (ξ : ℕ → ℂ) (K : Finset ℕ) (hK : 0 ∉ K) (hξ : ∀ d ∈ K, ‖ξ d‖ ≤ 1)
    {r : ℕ} (hr : Squarefree r) :
    ‖mollifier χ ξ K r s‖ ≤ (K.card:ℝ) * ((r:ℝ)*envelope r) := by
  classical
  have henv : (r:ℝ)*envelope r = ∏ p ∈ r.primeFactors, ((p:ℝ)+1) := by
    unfold envelope
    nth_rw 1 [← Nat.prod_primeFactors_of_squarefree hr]
    rw [Nat.cast_prod, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp
  rw [henv, mollifier]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ d ∈ K, ∏ p ∈ r.primeFactors, ((p:ℝ)+1) := by
      apply sum_le_sum
      intro d hd
      have hd0 : d ≠ 0 := fun h => hK (h ▸ hd)
      let A := r.primeFactors ∩ d.primeFactors
      let B := r.primeFactors \ d.primeFactors
      have hAB : A ∪ B = r.primeFactors := by
        ext p
        simp only [A, B, mem_union, mem_inter, mem_sdiff]
        tauto
      have hdis : Disjoint A B := by
        apply disjoint_left.mpr
        intro p hp hq
        exact (mem_sdiff.mp hq).2 (mem_inter.mp hp).2
      have hψ : ‖(psi r d:ℂ)‖ ≤ ∏ p ∈ A, ((p:ℝ)+1) := by
        rw [psi_inter hr hd0, Int.cast_prod, norm_prod]
        refine prod_le_prod₀ (fun _ _ => norm_nonneg _) ?_
        intro p hp
        have hp1 : (1:ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_inter.mp hp).1).one_lt.le
        rw [Complex.norm_intCast, Int.cast_sub, Int.cast_one, Int.cast_natCast,
          abs_of_nonpos (sub_nonpos.mpr hp1)]
        linarith
      have hB : ‖∏ p ∈ (r / r.gcd d).primeFactors, (1-(p:ℂ)*χ p/(p:ℂ)^s)‖
          ≤ ∏ p ∈ B, ((p:ℝ)+1) := by
        rw [Nat.primeFactors_div_gcd hr hd0, norm_prod]
        refine prod_le_prod₀ (fun _ _ => norm_nonneg _) ?_
        intro p hp
        have hp0 := (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1).ne_zero
        calc
          _ ≤ ‖(1:ℂ)‖ + ‖(p:ℂ)*χ p/(p:ℂ)^s‖ := norm_sub_le _ _
          _ ≤ 1 + (p:ℝ)*‖χ p‖ := by
            rw [norm_one, norm_div, norm_mul, Complex.norm_natCast]
            exact add_le_add le_rfl (div_le_self (show 0 ≤ (p:ℝ)*‖χ p‖ by positivity)
              (norm_nat_cpow_re_nonneg hp0 hs))
          _ ≤ _ := by
            have H := mul_le_mul_of_nonneg_left (χ.norm_le_one (p:ZMod q))
              (Nat.cast_nonneg (α := ℝ) p)
            linarith
      rw [norm_mul, norm_div]
      refine (mul_le_mul_of_nonneg_right
        (div_le_self (norm_nonneg _) (norm_nat_cpow_re_nonneg hd0 hs)) (norm_nonneg _)).trans ?_
      rw [norm_mul, norm_mul]
      have H : ‖ξ d‖*‖(psi r d:ℂ)‖*‖χ d‖ ≤ ‖(psi r d:ℂ)‖ := by
        exact (mul_le_of_le_one_right (by positivity) (χ.norm_le_one _)).trans
          (mul_le_of_le_one_left (by positivity) (hξ d hd))
      refine (mul_le_mul H hB (by positivity) (by positivity)).trans ?_
      rw [← hAB, prod_union hdis]
      exact mul_le_mul_of_nonneg_right hψ (by positivity)
    _ = _ := by simp

theorem normalized_mollifier_re_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 ≤ s.re)
    (ξ : ℕ → ℂ) (K : Finset ℕ) (hK : 0 ∉ K) (hξ : ∀ d ∈ K, ‖ξ d‖ ≤ 1)
    {r : ℕ} (hr : Squarefree r) :
    (r:ℝ)⁻¹ * ‖mollifier χ ξ K r s‖ ≤ (K.card:ℝ)*envelope r := by
  have hn : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne_zero
  calc
    _ ≤ (r:ℝ)⁻¹ * ((K.card:ℝ)*((r:ℝ)*envelope r)) :=
      mul_le_mul_of_nonneg_left (norm_mollifier_re_nonneg χ hs ξ K hK hξ hr) (by positivity)
    _ = _ := by field_simp

theorem envelope_le_totient_ratio {r : ℕ} (hr : r ≠ 0) :
    envelope r ≤ (r:ℝ)/r.totient := by
  have ht : (r.totient:ℝ) = r * ∏ p ∈ r.primeFactors, (1-(p:ℝ)⁻¹) := by
    have H := congrArg (fun a : ℚ => (a:ℝ)) (Nat.totient_eq_mul_prod_factors r)
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] using H
  have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast hr
  rw [ht, div_mul_eq_div_div, div_self hr0, one_div, ← Finset.prod_inv_distrib]
  unfold envelope
  refine prod_le_prod₀ (fun _ _ => by positivity) ?_
  intro p hp
  have hp1 : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hd : 0 < 1-(p:ℝ)⁻¹ :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
  calc
    _ ≤ 1/(1-(p:ℝ)⁻¹) := (le_div_iff₀ hd).mpr (by nlinarith [sq_nonneg ((p:ℝ)⁻¹)])
    _ = _ := one_div _

theorem envelope_divisors {r : ℕ} (hr : Squarefree r) :
    envelope r = ∑ d ∈ r.divisors, (d:ℝ)⁻¹ := by
  unfold envelope
  rw [← PintzJutilaPseudo.expand hr]
  apply sum_congr rfl
  intro d hd
  have hsq := hr.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]

theorem envelope_average (R : ℕ) :
    (∑ r ∈ (Icc 1 R).filter Squarefree, envelope r) ≤ (Real.pi^2/6)*R := by
  classical
  let I := Icc 1 R
  let A := I.filter Squarefree
  have hsub (r : ℕ) (hr : r ∈ A) : r.divisors ⊆ I := by
    intro d hd
    have hm := mem_Icc.mp (mem_filter.mp hr).1
    have hdn := Nat.dvd_of_mem_divisors hd
    have hp : 0 < r := hm.1
    exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdn hp,(Nat.le_of_dvd hp hdn).trans hm.2⟩
  have hsum (r) (hr : r ∈ A) : envelope r = ∑ d ∈ I, if d ∣ r then (d:ℝ)⁻¹ else 0 := by
    rw [envelope_divisors (mem_filter.mp hr).2, ← sum_filter]
    congr 1
    ext d
    exact ⟨fun hd => mem_filter.mpr ⟨hsub r hr hd,Nat.dvd_of_mem_divisors hd⟩,
      fun hd => Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2,(mem_filter.mp hr).2.ne_zero⟩⟩
  change (∑ r ∈ A, envelope r) ≤ _
  rw [sum_congr rfl hsum, sum_comm]
  have hcount (d : ℕ) (hd : d ∈ I) :
      ((I.filter (fun n => d ∣ n)).card:ℝ) ≤ (R:ℝ)/d := by
    have he : I.filter (fun n => d ∣ n) = (range R.succ).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
      ext n
      simp only [I,mem_filter,mem_Icc,mem_range,Nat.lt_succ_iff]
      omega
    rw [he, Nat.card_multiples']
    exact Nat.cast_div_le
  calc
    _ ≤ ∑ d ∈ I, (R:ℝ)*((d:ℝ)^2)⁻¹ := by
      apply sum_le_sum
      intro d hd
      have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      have hsub : A.filter (fun r => d ∣ r) ⊆ I.filter (fun r => d ∣ r) := by
        intro r hr
        exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hr).1).1,(mem_filter.mp hr).2⟩
      have hC : ((A.filter (fun r => d ∣ r)).card:ℝ) ≤ (R:ℝ)/d :=
        (by exact_mod_cast card_le_card hsub : ((A.filter (fun r => d ∣ r)).card : ℝ) ≤
          (I.filter (fun r => d ∣ r)).card).trans (hcount d hd)
      refine (mul_le_mul_of_nonneg_right hC (by positivity)).trans_eq ?_
      field_simp
    _ = (R:ℝ)*∑ d ∈ I, ((d:ℝ)^2)⁻¹ := by rw [mul_sum]
    _ ≤ _ := by
      rw [mul_comm (Real.pi^2/6)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have H := hasSum_zeta_two
      simp only [one_div] at H
      exact H.tsum_eq ▸ H.summable.sum_le_tsum I (fun _ _ => by positivity)

theorem averaged_mollifier_re_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 ≤ s.re)
    (ξ : ℕ → ℂ) (K : Finset ℕ) (hK : 0 ∉ K) (hξ : ∀ d ∈ K, ‖ξ d‖ ≤ 1)
    (R : ℕ) (A : Finset ℕ) (hA : A ⊆ (Icc 1 R).filter Squarefree) :
    (∑ r ∈ A, (r:ℝ)⁻¹ * ‖mollifier χ ξ K r s‖) ≤
      (K.card:ℝ)*((Real.pi^2/6)*R) := by
  calc
    _ ≤ ∑ r ∈ A, (K.card:ℝ)*envelope r := sum_le_sum fun r hr =>
      normalized_mollifier_re_nonneg χ hs ξ K hK hξ (mem_filter.mp (hA hr)).2
    _ ≤ ∑ r ∈ (Icc 1 R).filter Squarefree, (K.card:ℝ)*envelope r :=
      sum_le_sum_of_subset_of_nonneg hA (fun r _ _ => mul_nonneg (by positivity) (envelope_nonneg r))
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (envelope_average R) (by positivity)

theorem norm_mollifier {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = 0)
    (ξ : ℕ → ℂ) (K : Finset ℕ) (hK : 0 ∉ K) (hξ : ∀ d ∈ K, ‖ξ d‖ ≤ 1)
    {r : ℕ} (hr : Squarefree r) :
    ‖mollifier χ ξ K r s‖ ≤ (K.card:ℝ) * ((r:ℝ)*envelope r) :=
  norm_mollifier_re_nonneg χ hs.ge ξ K hK hξ hr

theorem normalized_mollifier {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = 0)
    (ξ : ℕ → ℂ) (K : Finset ℕ) (hK : 0 ∉ K) (hξ : ∀ d ∈ K, ‖ξ d‖ ≤ 1)
    {r : ℕ} (hr : Squarefree r) :
    (r:ℝ)⁻¹ * ‖mollifier χ ξ K r s‖ ≤ (K.card:ℝ)*envelope r :=
  normalized_mollifier_re_nonneg χ hs.ge ξ K hK hξ hr

theorem averaged_mollifier {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = 0)
    (ξ : ℕ → ℂ) (K : Finset ℕ) (hK : 0 ∉ K) (hξ : ∀ d ∈ K, ‖ξ d‖ ≤ 1)
    (R : ℕ) (A : Finset ℕ) (hA : A ⊆ (Icc 1 R).filter Squarefree) :
    (∑ r ∈ A, (r:ℝ)⁻¹ * ‖mollifier χ ξ K r s‖) ≤
      (K.card:ℝ)*((Real.pi^2/6)*R) :=
  averaged_mollifier_re_nonneg χ hs.ge ξ K hK hξ R A hA

#print axioms averaged_mollifier_re_nonneg
#print axioms normalized_mollifier_re_nonneg
#print axioms envelope_le_totient_ratio
#print axioms averaged_mollifier
#print axioms normalized_mollifier
end PintzJutilaMollifierBound
