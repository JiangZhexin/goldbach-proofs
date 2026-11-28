import PintzFullStripCount
import PintzZetaLocal
import PintzFixedWindowHigh
import PintzSieveToHybrid
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

open Finset PintzSieveToHybrid
namespace PintzLowRealBlock

/-- There are at most Q² primitive characters of moduli through Q;
the unique conductor-one character is included. -/
theorem family_card_le (Q : ℕ) : (family Q).card ≤ Q^2 := by
  classical
  rw [family, card_sigma, pow_two]
  calc
    _ ≤ ∑ k ∈ range Q, Q := by
      refine sum_le_sum fun k hk => ?_
      refine card_filter_le _ _ |>.trans ?_
      rw [card_univ, ← Nat.card_eq_fintype_card]
      let : NeZero (k+1) := ⟨by omega⟩
      rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      exact (Nat.totient_le _).trans (by have h := mem_range.mp hk; omega)
    _ = _ := by simp

/-- Weighted count in a height block, by uniform unit-box control over
all primitive characters. This statement handles modulus one too. -/
theorem block_count {Q : ℕ} {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (A : (Σ k : ℕ, DirichletCharacter ℂ (k+1)) → Finset ℂ)
    (m : (Σ k : ℕ, DirichletCharacter ℂ (k+1)) → ℂ → ℝ)
    (hm : ∀ j ∈ family Q, ∀ ρ ∈ A j, 0 ≤ m j ρ)
    (hx : ∀ j ∈ family Q, ∀ ρ ∈ A j, |ρ.im| ≤ T)
    (hlocal : ∀ j ∈ family Q, ∀ t : ℝ, |t| ≤ T+1/2 →
      (∑ ρ ∈ (A j).filter (fun ρ => |ρ.im-t| ≤ 1/2), m j ρ) ≤ C) :
    (∑ j ∈ family Q, ∑ ρ ∈ A j, m j ρ) ≤ (Q:ℝ)^2 * ((2*T+1)*C) := by
  classical
  calc
    _ ≤ ∑ j ∈ family Q, (2*T+1)*C := by
      exact sum_le_sum fun j hj => PintzFixedWindowHigh.count_of_unit_boxes (A j)
        Complex.im (m j) hT hC (hm j hj) (hx j hj) (hlocal j hj)
    _ = (family Q).card * ((2*T+1)*C) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast family_card_le Q) (by positivity)

/-- Wide families still give a power saving on the low-real-part range.
The constant here uses Q ≤ 2R and T ≤ 4PM/R. -/
theorem low_real_budget {N P R M T Q C h V : ℝ}
    (hN : 1 ≤ N) (hP : P ≤ N^(21/100:ℝ))
    (hR : 0 < R) (hRP : R ≤ P) (hM : 1 ≤ M)
    (hQ : 0 ≤ Q) (hQR : Q ≤ 2*R)
    (hT : 0 ≤ T) (hTupper : T ≤ 4*P*M/R)
    (hC : 0 ≤ C) (hh : (11/50:ℝ) ≤ h)
    (hV : V ≤ Q^2*((2*T+1)*C)) :
    M⁻¹ * N^(-2*h) * V ≤ 36*C*N^(-(1/50:ℝ)) := by
  have hNp : 0 < N := by linarith
  have hPp : 0 < P := hR.trans_le hRP
  have hMp : 0 < M := by linarith
  have hTR := (le_div_iff₀ hR).mp hTupper
  have hR2 : R^2 ≤ P^2 := pow_le_pow_left₀ hR.le hRP _
  have hPM : P^2 ≤ P^2*M := le_mul_of_one_le_right (sq_nonneg _) hM
  have hRTR : R*(T*R) ≤ P*(4*P*M) := mul_le_mul hRP hTR (by positivity) hPp.le
  have hRbound : R^2*(2*T+1) ≤ 9*(P^2*M) := by nlinarith only [hPM,hR2,hRTR]
  have hVR : V ≤ 36*C*(P^2*M) := calc
    _ ≤ Q^2*((2*T+1)*C) := hV
    _ ≤ (2*R)^2*((2*T+1)*C) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hQ hQR 2) (by positivity)
    _ = 4*C*(R^2*(2*T+1)) := by ring
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hRbound (show 0 ≤ 4*C by positivity)]
  have hPow : P^2 * N^(-2*h) ≤ N^(-(1/50:ℝ)) := calc
    _ ≤ (N^(21/100:ℝ))^2 * N^(-2*h) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hPp.le hP 2) (by positivity)
    _ = N^(42/100 + -2*h) := by
      rw [← Real.rpow_mul_natCast hNp.le, ← Real.rpow_add hNp]
      push_cast
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  calc
    _ ≤ M⁻¹ * N^(-2*h) * (36*C*(P^2*M)) :=
      mul_le_mul_of_nonneg_left hVR (by positivity)
    _ = 36*C*(P^2*N^(-2*h)) := by field_simp [hMp.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hPow (by positivity)

#print axioms family_card_le
#print axioms block_count
#print axioms low_real_budget

noncomputable def actualC (Q : ℕ) (T : ℝ) : ℝ :=
  max (2*(Real.log (12*Q*(T+13/2))/Real.log (55/52)))
    (Real.log (24*(T+11/2)^2)/Real.log (12/11))

/-- Actual local multiplicities have a uniform cap over the family;
conductor one uses the pole-removed zeta count. -/
theorem actual_local_count {Q : ℕ} {T : ℝ} (_hT : 0 ≤ T)
    (A : (Σ k : ℕ, DirichletCharacter ℂ (k+1)) → Finset ℂ)
    (hz : ∀ j ∈ family Q, ∀ ρ ∈ A j, 1/2 ≤ ρ.re ∧ ρ.re < 1)
    (j : Σ k : ℕ, DirichletCharacter ℂ (k+1)) (hj : j ∈ family Q)
    (t : ℝ) (ht : |t| ≤ T+1/2) :
    (∑ ρ ∈ (A j).filter (fun ρ => |ρ.im-t| ≤ 1/2),
      (analyticOrderNatAt j.2.LFunction ρ : ℝ)) ≤ actualC Q T := by
  classical
  obtain ⟨k,χ⟩ := j
  let j : Σ k : ℕ, DirichletCharacter ℂ (k+1) := ⟨k,χ⟩
  change j ∈ family Q at hj
  have hm := Finset.mem_sigma.mp hj
  have hkN : k+1 ≤ Q := by
    have h : k ∈ range Q := hm.1
    exact Finset.mem_range.mp h
  have hk : ((k+1:ℕ):ℝ) ≤ Q := by exact_mod_cast hkN
  let F := (A j).filter (fun ρ => |ρ.im-t| ≤ 1/2)
  have hF (ρ : ℂ) (hρ : ρ ∈ F) : 1/2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im-t| ≤ 1/2 := by
    obtain ⟨h₁,h₂⟩ := mem_filter.mp hρ
    exact ⟨(hz j hj ρ h₁).1,(hz j hj ρ h₁).2,h₂⟩
  by_cases hzero : k=0
  · subst k
    have he : χ.LFunction = riemannZeta := DirichletCharacter.LFunction_modOne_eq
    change (∑ ρ ∈ F, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ _
    rw [he]
    refine (PintzZetaLocal.local_count t F (fun ρ hρ => ?_)).trans ?_
    · obtain ⟨h₁,h₂,h₃⟩ := hF ρ hρ
      exact ⟨fun e => by simp [e] at h₂, h₁, h₂.le, h₃⟩
    · refine le_trans ?_ (le_max_right _ _)
      apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
      apply Real.log_le_log (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by norm_num)
  · let : NeZero (k+1) := ⟨by omega⟩
    have hp : χ.IsPrimitive := (mem_filter.mp hm.2).2
    have hn : χ ≠ 1 := by
      intro h
      have he := hp
      rw [h, DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at he
      exact hzero (by omega)
    change (∑ ρ ∈ F, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ _
    refine (PintzFullStripCount.local_count χ hn hp t F (fun ρ hρ => ?_)).trans ?_
    · obtain ⟨h₁,h₂,h₃⟩ := hF ρ hρ
      exact ⟨by linarith,h₂,h₃⟩
    · refine le_trans ?_ (le_max_left _ _)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
      apply Real.log_le_log (by positivity)
      push_cast at hk ⊢
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hk (by norm_num))
        (by linarith) (by positivity) (by positivity)

#print axioms actual_local_count

/-- The actual low-real zero catalogue contributes a power-saving term,
with the explicit local count logarithms retained. -/
theorem actual_low_real_budget {N P R M T h : ℝ} {Q : ℕ}
    (hN : 1 ≤ N) (hP : P ≤ N^(21/100:ℝ))
    (hR : 0 < R) (hRP : R ≤ P) (hM : 1 ≤ M) (hQR : (Q:ℝ) ≤ 2*R)
    (hT : 0 ≤ T) (hTupper : T ≤ 4*P*M/R) (hh : (11/50:ℝ) ≤ h)
    (A : (Σ k : ℕ, DirichletCharacter ℂ (k+1)) → Finset ℂ)
    (hz : ∀ j ∈ family Q, ∀ ρ ∈ A j, 1/2 ≤ ρ.re ∧ ρ.re < 1)
    (hx : ∀ j ∈ family Q, ∀ ρ ∈ A j, |ρ.im| ≤ T) :
    M⁻¹ * N^(-2*h) * (∑ j ∈ family Q, ∑ ρ ∈ A j, (analyticOrderNatAt j.2.LFunction ρ : ℝ)) ≤
      36*actualC Q T*N^(-(1/50:ℝ)) := by
  have hC : 0 ≤ actualC Q T := by
    refine le_trans ?_ (le_max_right _ _)
    exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg T])) (Real.log_nonneg (by norm_num))
  exact low_real_budget hN hP hR hRP hM (Nat.cast_nonneg _) hQR hT hTupper hC hh
    (block_count hT hC A (fun j ρ => (analyticOrderNatAt j.2.LFunction ρ : ℝ))
      (fun _ _ _ _ => Nat.cast_nonneg _) hx (actual_local_count hT A hz))

#print axioms actual_low_real_budget

/-- On the polynomial parameter range, the explicit local cap loses just
one logarithm (including the pole-removed conductor-one estimate). -/
theorem actualC_log_bound {Q : ℕ} {N T : ℝ}
    (hN : 2 ≤ N) (hQ1 : 1 ≤ Q) (hQ : (Q:ℝ) ≤ 2*N)
    (hT : 0 ≤ T) (hTN : T ≤ N) :
    actualC Q T ≤ (18/Real.log (55/52)+11/Real.log (12/11))*Real.log N := by
  have hNp : 0 < N := by linarith
  have hLn : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hQp : (0:ℝ) < Q := by exact_mod_cast Nat.zero_lt_one.trans_le hQ1
  have hA : 12*(Q:ℝ)*(T+13/2) ≤ N^9 := by
    have h₁ : T+13/2 ≤ (17/4)*N := by linarith
    have h₂ := mul_le_mul (mul_le_mul_of_nonneg_left hQ (by norm_num : (0:ℝ) ≤ 12))
      h₁ (by positivity) (by positivity)
    have hNp7 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 7
    rw [show (9:ℕ) = 7+2 by norm_num, pow_add]
    nlinarith only [h₂,mul_le_mul_of_nonneg_right (show 102 ≤ N^7 by nlinarith [hNp7])
      (sq_nonneg N)]
  have hB : 24*(T+11/2)^2 ≤ N^11 := by
    have h₁ : T+11/2 ≤ (15/4)*N := by linarith
    have h₂ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h₁ 2)
      (by norm_num : (0:ℝ) ≤ 24)
    have hNp9 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 9
    rw [show (11:ℕ) = 9+2 by norm_num, pow_add]
    nlinarith only [h₂,mul_le_mul_of_nonneg_right (show (675/2:ℝ) ≤ N^9 by nlinarith [hNp9])
      (sq_nonneg N)]
  have hD₁ : 0 < Real.log (55/52) := Real.log_pos (by norm_num)
  have hD₂ : 0 < Real.log (12/11) := Real.log_pos (by norm_num)
  unfold actualC
  apply max_le
  · have H := Real.log_le_log (by positivity : 0 < 12*(Q:ℝ)*(T+13/2)) hA
    rw [Real.log_pow] at H
    calc
      _ ≤ 2*(9*Real.log N/Real.log (55/52)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right H hD₁.le) (by norm_num)
      _ = (18/Real.log (55/52))*Real.log N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        have : 0 ≤ 11/Real.log (12/11) := by positivity
        linarith) hLn
  · have H := Real.log_le_log (by positivity : 0 < 24*(T+11/2)^2) hB
    rw [Real.log_pow] at H
    calc
      _ ≤ 11*Real.log N/Real.log (12/11) := div_le_div_of_nonneg_right H hD₂.le
      _ = (11/Real.log (12/11))*Real.log N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        have : 0 ≤ 18/Real.log (55/52) := by positivity
        linarith) hLn

#print axioms actualC_log_bound
end PintzLowRealBlock
