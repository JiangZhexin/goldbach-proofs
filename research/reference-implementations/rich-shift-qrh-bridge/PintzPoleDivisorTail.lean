import PintzPoleWeightedError

open Finset
namespace PintzPoleDivisorTail

open PintzPoleArithmetic PintzPoleWeightedError PintzPoleKernelTail

private theorem inverse_cube_root_telescope_step {k : ℕ} (hk : 0 < k) :
    1 / (Real.sqrt ((k:ℝ)+1))^3 ≤
      2 * ((Real.sqrt (k:ℝ))⁻¹ - (Real.sqrt ((k:ℝ)+1))⁻¹) := by
  let a := Real.sqrt (k:ℝ)
  let b := Real.sqrt ((k:ℝ)+1)
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have ha : 0 < a := Real.sqrt_pos.2 hkR
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have he : b^2 - a^2 = 1 := by
    dsimp [a,b]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hkR.le]
    ring
  change 1/b^3 ≤ 2 * (a⁻¹-b⁻¹)
  have hd : 2*(a⁻¹-b⁻¹) = 2*(b-a)/(a*b) := by
    field_simp
  rw [hd]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hba : 0 ≤ b-a := sub_nonneg.mpr hab
  have H1 := mul_le_mul_of_nonneg_left (show a+b ≤ 2*b by linarith) hba
  have H2 : 1 ≤ 2*b*(b-a) := by nlinarith only [he,H1]
  have H3 := mul_le_mul_of_nonneg_right H2 (sq_nonneg b)
  have H4 := mul_le_mul_of_nonneg_right hab hb.le
  nlinarith only [H3,H4]

theorem inverse_cube_root_tail {K U : ℕ} (hK : 0 < K) (hKU : K ≤ U) :
    (∑ k ∈ Finset.Ioc K U, 1 / (Real.sqrt (k:ℝ))^3) ≤
      2 * ((Real.sqrt (K:ℝ))⁻¹ - (Real.sqrt (U:ℝ))⁻¹) := by
  induction U, hKU using Nat.le_induction with
  | base => simp
  | succ U hU ih =>
    have he : Finset.Ioc K (U+1) = insert (U+1) (Finset.Ioc K U) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [he,Finset.sum_insert (by simp)]
    have hs := inverse_cube_root_telescope_step (hK.trans_le hU)
    push_cast
    linarith

theorem inverse_cube_root_tail_weak (K U : ℕ) (hKU : K ≤ U) :
    (∑ k ∈ Finset.Ioc K U, 1 / (Real.sqrt (k:ℝ))^3) ≤
      3 / (Real.sqrt ((max 1 K:ℕ):ℝ)) := by
  by_cases hK : K = 0
  · subst K
    by_cases hU : U = 0
    · simp [hU]
    have he : Finset.Ioc 0 U = insert 1 (Finset.Ioc 1 U) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [he,Finset.sum_insert (by simp)]
    have hs := inverse_cube_root_tail (show 0 < (1:ℕ) by decide) (show 1 ≤ U by omega)
    norm_num at hs ⊢
    linarith [inv_nonneg.mpr (Real.sqrt_nonneg (U:ℝ))]
  · have hKpos : 1 ≤ K := by omega
    rw [max_eq_right hKpos]
    have hs := inverse_cube_root_tail (show 0 < K by omega) hKU
    rw [div_eq_mul_inv]
    linarith [inv_nonneg.mpr (Real.sqrt_nonneg (K:ℝ)),
      inv_nonneg.mpr (Real.sqrt_nonneg (U:ℝ))]

theorem multiples_cubic_tail {P U d : ℕ} (hP : 0 < P) (hPU : P ≤ U) (hd : 0 < d) :
    (∑ q ∈ (Finset.Ioc P U).filter (fun q => d ∣ q), (d:ℝ) / (Real.sqrt (q:ℝ))^3) ≤
      6 / Real.sqrt (P:ℝ) := by
  have he :
      (∑ k ∈ Finset.Ioc (P/d) (U/d), (d:ℝ) / (Real.sqrt ((d*k:ℕ):ℝ))^3) =
      ∑ q ∈ (Finset.Ioc P U).filter (fun q => d ∣ q), (d:ℝ) / (Real.sqrt (q:ℝ))^3 := by
    classical
    apply Finset.sum_bij (fun k _ => d*k)
    · intro k hk
      obtain ⟨hk1,hk2⟩ := Finset.mem_Ioc.mp hk
      rw [Nat.div_lt_iff_lt_mul hd, Nat.mul_comm k d] at hk1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hk1,
          by rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hd).mp hk2⟩, dvd_mul_right _ _⟩
    · intro a ha b hb h
      exact Nat.eq_of_mul_eq_mul_left hd h
    · intro q hq
      obtain ⟨hqI, k, rfl⟩ := Finset.mem_filter.mp hq
      obtain ⟨h1,hU⟩ := Finset.mem_Ioc.mp hqI
      refine ⟨k, Finset.mem_Ioc.mpr ⟨?_,?_⟩, rfl⟩
      · apply (Nat.div_lt_iff_lt_mul hd).2
        rwa [Nat.mul_comm]
      · apply (Nat.le_div_iff_mul_le hd).2
        rwa [Nat.mul_comm]
    · simp
  rw [← he]
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hsd : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.2 hdR
  have he' (k : ℕ) :
      (d:ℝ) / (Real.sqrt ((d*k:ℕ):ℝ))^3 =
      (Real.sqrt (d:ℝ))⁻¹ * (1/(Real.sqrt (k:ℝ))^3) := by
    rw [Nat.cast_mul, Real.sqrt_mul hdR.le, mul_pow, div_eq_mul_inv, mul_inv_rev]
    have hsq := Real.sq_sqrt hdR.le
    have h1 : (Real.sqrt (d:ℝ))^2 * ((Real.sqrt (d:ℝ))^3)⁻¹ = (Real.sqrt (d:ℝ))⁻¹ := by
      field_simp
    rw [one_div]
    calc
      _ = ((Real.sqrt (d:ℝ))^2 * ((Real.sqrt (d:ℝ))^3)⁻¹) *
        ((Real.sqrt (k:ℝ))^3)⁻¹ := by rw [hsq]; ring
      _ = _ := by rw [h1]
  simp_rw [he', ← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left
    (inverse_cube_root_tail_weak (P/d) (U/d) (Nat.div_le_div_right hPU))
    (inv_nonneg.mpr hsd.le)).trans
  have hNat : P ≤ 4*(d * max 1 (P/d)) := by
    have h := Nat.lt_mul_div_succ P hd
    have hA : P/d + 1 ≤ 4*max 1 (P/d) := by omega
    have H := Nat.mul_le_mul_left d hA
    nlinarith only [h,H]
  have hR : (P:ℝ) ≤ 4*((d*max 1 (P/d):ℕ):ℝ) := by exact_mod_cast hNat
  have hS := Real.sqrt_le_sqrt hR
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ)=2*2 by norm_num, Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
  rw [Real.sqrt_mul (show (0:ℝ) ≤ 4 by norm_num), h4] at hS
  have hPpos : 0 < Real.sqrt (P:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hP)
  have hMpos : 0 < Real.sqrt (↑(max 1 (P/d):ℕ):ℝ) := Real.sqrt_pos.2 (by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 (P/d))))
  rw [Nat.cast_mul, Real.sqrt_mul hdR.le] at hS
  rw [show (Real.sqrt (d:ℝ))⁻¹ * (3 / Real.sqrt (↑(max 1 (P/d):ℕ):ℝ)) =
      3 / (Real.sqrt (d:ℝ) * Real.sqrt (↑(max 1 (P/d):ℕ):ℝ)) by
    simp [div_eq_mul_inv,mul_inv_rev]; ring]
  apply (div_le_div_iff₀ (by positivity) hPpos).2
  nlinarith only [hS]


theorem local_cubic_envelope {q m : ℕ} (hq : 0 < q) (hm : 0 < m) :
    ‖weight q * ramanujan q m‖ ≤
      15 * (∑ d ∈ m.divisors.filter (fun d => d ∣ q),
        (d:ℝ) / (Real.sqrt (q:ℝ))^3) := by
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  have hs : 0 < Real.sqrt (q:ℝ) := Real.sqrt_pos.2 hqR
  have h := local_divisor_envelope hq hm
  apply (mul_le_mul_iff_right₀ hqR).mp
  rw [← mul_assoc, mul_comm (q:ℝ) 15, mul_assoc, Finset.mul_sum]
  refine h.trans_eq ?_
  apply congrArg (fun x : ℝ => 15*x)
  apply Finset.sum_congr rfl
  intro d hd
  field_simp
  rw [Real.sq_sqrt hqR.le]

/-- Uniform absolute error for every partial denominator tail; no passage to
an infinite Euler product, and no external analytic convergence input. -/
theorem finite_ramanujan_tail {P U m : ℕ} (hP : 0 < P) (hPU : P ≤ U) (hm : 0 < m) :
    (∑ q ∈ Finset.Ioc P U, ‖weight q * ramanujan q m‖) ≤
      (90 / Real.sqrt (P:ℝ)) * (m.divisors.card:ℝ) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioc P U, 15 * (∑ d ∈ m.divisors.filter (fun d => d ∣ q),
        (d:ℝ) / (Real.sqrt (q:ℝ))^3) :=
      Finset.sum_le_sum (fun q hq => local_cubic_envelope (hP.trans (Finset.mem_Ioc.mp hq).1) hm)
    _ = 15 * (∑ d ∈ m.divisors, ∑ q ∈ (Finset.Ioc P U).filter (fun q => d ∣ q),
        (d:ℝ) / (Real.sqrt (q:ℝ))^3) := by
      simp only [Finset.sum_filter, ← Finset.mul_sum]
      apply congrArg (fun x : ℝ => 15*x)
      exact Finset.sum_comm
    _ ≤ 15 * (∑ _ ∈ m.divisors, 6 / Real.sqrt (P:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun d hd => multiples_cubic_tail hP hPU (Nat.pos_of_mem_divisors hd))
    _ = _ := by simp; ring

#print axioms finite_ramanujan_tail
#print axioms multiples_cubic_tail
end PintzPoleDivisorTail
