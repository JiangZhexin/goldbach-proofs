import PintzDetectorHead
import PintzDirichletTail

open Finset PintzDetectorFinite PintzDetectorHead OAI.Ostmann.Dirichlet
set_option maxHeartbeats 800000

namespace PintzDetectorTail

/-- The alternating tail is obtained by subtracting twice the even terms.
Passing from an even cutoff to an odd one adds exactly a single term. -/
theorem from_even (g : ℕ → ℂ) {β B : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hB : 0 ≤ B) (hdec : ∀ n : ℕ, 0 < n → ‖g n‖ ≤ (n:ℝ)^(-β))
    (heven : ∀ (k : ℕ), 1 ≤ k → ‖∑ n ∈ Icc 1 (2*k), g n * alternation n‖ ≤
      B*(k:ℝ)^(-β)) (N : ℕ) (hN : 1 ≤ N) :
    ‖∑ n ∈ Icc 1 N, g n * alternation n‖ ≤ (3*B+1)*(N:ℝ)^(-β) := by
  let K := N/2
  by_cases hK : K = 0
  · have h : N = 1 := by dsimp [K] at hK; omega
    subst N
    have ht := hdec 1 (by decide)
    simp [alternation] at ht ⊢
    linarith
  have hk : 1 ≤ K := Nat.pos_of_ne_zero hK
  have hnle : N ≤ 3*K := by dsimp [K] at *; omega
  have hkpos : (0:ℝ) < K := by exact_mod_cast hk
  have hnpos : (0:ℝ) < N := by exact_mod_cast hN
  have hscale : (K:ℝ)^(-β) ≤ 3*(N:ℝ)^(-β) := by
    have he : (K:ℝ)^(-β) ≤ ((N:ℝ)/3)^(-β) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      have h : (N:ℝ) ≤ 3*(K:ℝ) := by exact_mod_cast hnle
      linarith
    rw [Real.div_rpow (by positivity) (by norm_num : (0:ℝ) ≤ 3), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3),
      div_inv_eq_mul] at he
    have h3 : (3:ℝ)^β ≤ 3 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hβ1
    exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hnpos.le (-β))])
  have hE := (heven K hk).trans (mul_le_mul_of_nonneg_left hscale hB)
  have hR : N = 2*K ∨ N = 2*K+1 := by dsimp [K]; omega
  rcases hR with h | h
  · have heq : (∑ n ∈ Icc 1 N, g n * alternation n) =
        ∑ n ∈ Icc 1 (2*K), g n * alternation n := by rw [← h]
    rw [heq]
    exact hE.trans (by nlinarith [Real.rpow_nonneg hnpos.le (-β)])
  · have hf : Icc 1 N = insert N (Icc 1 (2*K)) := by
      ext a; simp only [mem_Icc,mem_insert]; omega
    have hnot : N ∉ Icc 1 (2*K) := by simp [h]
    have hnodd : ¬ 2 ∣ N := by omega
    rw [hf, sum_insert hnot]
    have ht := (norm_add_le (g N * alternation N) (∑ n ∈ Icc 1 (2*K), g n * alternation n))
    rw [show alternation N = 1 by simp [alternation,hnodd], mul_one] at ht ⊢
    exact ht.trans (by nlinarith only [hdec N (by omega), hE])

/-- Uniform alternating Dirichlet prefix at an actual zero of a
nonprincipal character, including odd cutoffs. -/
theorem nonprincipal_at_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hp : 0 < s.re) (hre : s.re ≤ 1)
    (hz : χ.LFunction s = 0) {N : ℕ} (hN : 1 ≤ N) :
    ‖∑ n ∈ Icc 1 N, twist χ s n * alternation n‖ ≤
      (9*(q*(1+‖s‖/s.re))+1)*(N:ℝ)^(-s.re) := by
  let A : ℝ := q*(1+‖s‖/s.re)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hprefix (k : ℕ) (hk : 1 ≤ k) :
      ‖∑ n ∈ Icc 1 k, twist χ s n‖ ≤ A*(k:ℝ)^(-s.re) :=
    norm_dirichletPolynomial_at_zero_le χ hχ hp hz hk
  have htwo : ‖(2:ℂ)*twist χ s 2‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_ofNat]
    apply mul_le_of_le_one_right (by norm_num)
    exact (twist_norm χ s (by decide : 0 < (2:ℕ))).trans (by
      norm_num only [Nat.cast_ofNat]
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1:ℝ) ≤ 2) (neg_nonpos.mpr hp.le))
  have H := from_even (twist χ s) hp.le hre (show 0 ≤ 3*A by positivity)
    (fun _ hn => twist_norm χ s hn) (fun k hk => ?_) N hN
  · convert H using 1
    dsimp [A]
    ring
  · rw [alternating_even k _ (twist_mul χ s)]
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    have hpow : ((2*k:ℕ):ℝ)^(-s.re) ≤ (k:ℝ)^(-s.re) := by
      apply Real.rpow_le_rpow_of_nonpos hkR _ (by linarith)
      push_cast; linarith
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h1 := (hprefix (2*k) (by omega)).trans (mul_le_mul_of_nonneg_left hpow hA)
    have h2 := mul_le_mul htwo (hprefix k hk) (norm_nonneg _) (by norm_num)
    nlinarith only [h1,h2]

#print axioms from_even
#print axioms nonprincipal_at_zero
end PintzDetectorTail
