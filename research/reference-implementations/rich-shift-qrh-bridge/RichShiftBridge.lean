import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic

open Finset
namespace RichShift

def reps (m : ℕ) : Finset ℕ :=
  (Icc 2 m).filter (fun p => p.Prime ∧ (m-p).Prime)

noncomputable def weighted (m : ℕ) : ℝ :=
  ∑ p ∈ reps m, Real.log (p:ℝ) * Real.log ((m-p:ℕ):ℝ)

theorem weighted_le_count (X m : ℕ) (hX : 2 ≤ X) (hm : m ≤ 2*X) :
    weighted m ≤ ((reps m).card:ℝ) * (4*(Real.log (X:ℝ))^2) := by
  have hx : (2:ℝ) ≤ X := by exact_mod_cast hX
  have hl : 0 < Real.log (X:ℝ) := Real.log_pos (by linarith)
  have h (u : ℕ) (hu : 2 ≤ u) (hu' : u ≤ 2*X) :
      0 ≤ Real.log (u:ℝ) ∧ Real.log (u:ℝ) ≤ 2*Real.log (X:ℝ) := by
    have h2 : (2:ℝ) ≤ u := by exact_mod_cast hu
    have h3 : (u:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast hu'
    refine ⟨Real.log_nonneg (by linarith), ?_⟩
    have hh := Real.log_le_log (by linarith : (0:ℝ)<u) h3
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (X:ℝ) ≠ 0)] at hh
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) hx]
  rw [weighted, ← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpm,hp',hq⟩ := mem_filter.mp hp
  have hp'Bound := (mem_Icc.mp hpm).2.trans hm
  have h₁ := h p hp'.two_le hp'Bound
  have h₂ := h (m-p) hq.two_le ((Nat.sub_le ..).trans hm)
  calc
    _ ≤ (2*Real.log (X:ℝ))*(2*Real.log (X:ℝ)) :=
      mul_le_mul h₁.2 h₂.2 h₂.1 (by positivity)
    _ = _ := by ring

theorem allowed_shift_le_half {X e : ℕ} (hX : 2 ≤ X)
    (he : e ∈ Icc 1 (Nat.log 2 X/2)) : 2^e ≤ X/2 := by
  obtain ⟨he1,he2⟩ := mem_Icc.mp he
  have hPow : 2^(e+e) ≤ X := Nat.pow_le_of_le_log (by omega) (by omega)
  rw [pow_add] at hPow
  have hp : 2 ≤ 2^e := by
    exact (show 2^1 ≤ 2^e from Nat.pow_le_pow_right (by decide) he1)
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
    ((Nat.mul_le_mul_left (2^e) hp).trans hPow)

theorem shift_bound_of_weighted {X e : ℕ} {κ L : ℝ} (hX : 2 ≤ X)
    (he : e ∈ Icc 1 (Nat.log 2 X/2))
    (h : ((Icc (X/2) (2*X)).filter (fun m => Even m ∧ weighted m < κ * X)).card ≤ L) :
    ((Ico X (2*X)).filter (fun n =>
      Even n ∧ ((reps (n-2^e)).card:ℝ) < (κ/4)*(X:ℝ)/Real.log (X:ℝ)^2)).card ≤ L := by
  classical
  let A := (Ico X (2*X)).filter (fun n =>
    Even n ∧ ((reps (n-2^e)).card:ℝ) < (κ/4)*(X:ℝ)/Real.log (X:ℝ)^2)
  let B := (Icc (X/2) (2*X)).filter (fun m => Even m ∧ weighted m < κ*X)
  let d : ℕ := 2^e
  have hd : d ≤ X/2 := allowed_shift_le_half hX he
  have hde : Even d := by
    obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show e ≠ 0 by
      have _ := (mem_Icc.mp he).1
      omega)
    dsimp [d]
    exact ⟨2^e, by rw [pow_succ]; omega⟩
  change (A.card:ℝ) ≤ L
  refine (show (A.card:ℝ) ≤ B.card from Nat.cast_le.mpr ?_).trans h
  refine Finset.card_le_card_of_injOn (fun n => n-d) ?_ ?_
  · intro n hn
    change n-d ∈ B
    obtain ⟨hn,hne,hsmall⟩ := mem_filter.mp hn
    obtain ⟨hlo,hhi⟩ := mem_Ico.mp hn
    have hd' : d ≤ n := by omega
    have hev : Even (n-d) := Nat.even_sub hd' |>.2 (⟨fun _ => hde, fun _ => hne⟩)
    have hupper : n-d ≤ 2*X := (Nat.sub_le ..).trans (le_of_lt hhi)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hupper⟩, hev, ?_⟩
    have hw := weighted_le_count X (n-d) hX hupper
    have hX' : (1:ℝ) < X := by exact_mod_cast (show 1 < X by omega)
    have hl : 0 < Real.log (X:ℝ)^2 := by positivity [Real.log_pos hX']
    have hsmall' := (lt_div_iff₀ hl).mp hsmall
    apply hw.trans_lt
    nlinarith
  · intro x hx y hy hxy
    have h1 := (mem_Ico.mp (mem_filter.mp hx).1).1
    have h2 := (mem_Ico.mp (mem_filter.mp hy).1).1
    dsimp only at hxy
    omega

end RichShift

#print axioms RichShift.shift_bound_of_weighted
