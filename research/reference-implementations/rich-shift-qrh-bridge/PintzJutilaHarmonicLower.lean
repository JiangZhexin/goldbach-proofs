import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

noncomputable section
namespace PintzJutilaHarmonicLower

def free (R : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Icc 1 R).filter (fun n => ∀ p ∈ S, ¬p ∣ n)

def H (R : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ free R S, (n:ℝ)⁻¹

theorem free_insert (R p : ℕ) (S : Finset ℕ) (hp : p.Prime) :
    (1-(p:ℝ)⁻¹)*H R S ≤ H R (insert p S) := by
  classical
  let B := (free R S).filter (fun n => p ∣ n)
  let f := fun n : ℕ => n/p
  have hb (n) (hn : n ∈ B) := mem_filter.mp hn
  have hf : B.image f ⊆ free R S := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hm
    obtain ⟨hn0,hnR⟩ := mem_Icc.mp (mem_filter.mp (hb n hn).1).1
    have hpd := hb n hn |>.2
    have H := Nat.mul_div_cancel' hpd
    have hpr := Nat.le_of_dvd (by omega : 0 < n) hpd
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨Nat.div_pos hpr hp.pos,(Nat.div_le_self _ _).trans hnR⟩,?_⟩
    intro q hq hqm
    exact (mem_filter.mp (hb n hn).1).2 q hq (hqm.trans (Nat.div_dvd_of_dvd hpd))
  have hi : Set.InjOn f B := by
    intro n hn m hm he
    change n/p = m/p at he
    rw [← Nat.mul_div_cancel' (hb n hn).2, he, Nat.mul_div_cancel' (hb m hm).2]
  have hbnd : (∑ n ∈ B, (n:ℝ)⁻¹) ≤ (p:ℝ)⁻¹ * H R S := by
    have hn (n) (hn : n ∈ B) :
        (n:ℝ)⁻¹ = (p:ℝ)⁻¹ * (f n:ℝ)⁻¹ := by
      rw [← mul_inv]
      congr 1
      exact_mod_cast (Nat.mul_div_cancel' (hb n hn).2).symm
    have Himage : (∑ m ∈ B.image f, (m:ℝ)⁻¹) = (∑ n ∈ B, (f n:ℝ)⁻¹) :=
      Finset.sum_image hi
    rw [sum_congr rfl hn, ← mul_sum, ← Himage]
    exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hf (fun _ _ _ => by positivity))
      (by positivity)
  have he : free R (insert p S) = (free R S).filter (fun n => ¬p ∣ n) := by
    ext n
    simp [free]
    tauto
  have hs := sum_filter_add_sum_filter_not (free R S) (fun n => p ∣ n)
    (fun n => (n:ℝ)⁻¹)
  change (∑ n ∈ B, (n:ℝ)⁻¹) + (∑ n ∈ (free R S).filter (fun n => ¬p ∣ n), (n:ℝ)⁻¹) = H R S at hs
  rw [← he] at hs
  change _ + H R (insert p S) = _ at hs
  rw [sub_mul, one_mul]
  linarith

theorem free_lower (R : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, (1-(p:ℝ)⁻¹)) * H R ∅ ≤ H R S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hn ih =>
    have hp := hS p (mem_insert_self _ _)
    have hp0 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hpos : 0 ≤ 1-(p:ℝ)⁻¹ :=
      sub_nonneg.mpr (inv_le_one_of_one_le₀ hp0)
    rw [prod_insert hn, mul_assoc]
    exact (mul_le_mul_of_nonneg_left (ih (fun q hq => hS q (mem_insert_of_mem hq))) hpos).trans
      (free_insert R p S hp)

theorem free_eq_coprime (R q : ℕ) (hq : q ≠ 0) :
    free R q.primeFactors = (Icc 1 R).filter (fun n => q.Coprime n) := by
  ext n
  simp only [free, mem_filter]
  constructor
  · rintro ⟨hn,h⟩
    refine ⟨hn,?_⟩
    by_contra H
    obtain ⟨p,hp,hpq,hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
    exact h p (Nat.mem_primeFactors.mpr ⟨hp,hpq,hq⟩) hpn
  · rintro ⟨hn,h⟩
    exact ⟨hn,fun p hp hpn => (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p,Nat.prime_of_mem_primeFactors hp,Nat.dvd_of_mem_primeFactors hp,hpn⟩) h⟩

theorem coprime_lower (R q : ℕ) (hq : q ≠ 0) :
    ((q.totient:ℝ)/q)*(∑ n ∈ Icc 1 R, (n:ℝ)⁻¹) ≤
      ∑ n ∈ (Icc 1 R).filter (fun n => q.Coprime n), (n:ℝ)⁻¹ := by
  have ht : (q.totient:ℝ) = q * ∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹) := by
    have H := congrArg (fun a : ℚ => (a:ℝ)) (Nat.totient_eq_mul_prod_factors q)
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] using H
  have ht' : (q.totient:ℝ)/q = ∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹) := by
    apply (div_eq_iff (by exact_mod_cast hq)).mpr
    rw [mul_comm]
    exact ht
  have HB := free_lower R q.primeFactors (fun _ => Nat.prime_of_mem_primeFactors)
  rw [← ht', H, H, free_eq_coprime R q hq] at HB
  simpa [free] using HB

theorem squarefree_loss (R q : ℕ) :
    (∑ n ∈ (Icc 1 R).filter (fun n => q.Coprime n), (n:ℝ)⁻¹) ≤
      (Real.pi^2/6) * (∑ n ∈ (Icc 1 R).filter (fun n => q.Coprime n ∧ Squarefree n), (n:ℝ)⁻¹) := by
  classical
  let I := Icc 1 R
  let A := I.filter (fun n => q.Coprime n)
  let B := I.filter (fun n => q.Coprime n ∧ Squarefree n)
  choose d e h using (fun n : ℕ => exists_sq_mul_squarefree n)
  let f (n : ℕ) := (d n,e n)
  let w (p : ℕ × ℕ) : ℝ := ((p.1:ℝ)^2)⁻¹ * (p.2:ℝ)⁻¹
  have hf : A.image f ⊆ I.product B := by
    intro p hp
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hp
    obtain ⟨hnI,hc⟩ := mem_filter.mp hn
    have hn0 : 0 < n := by have := (mem_Icc.mp hnI).1; omega
    have hdn : d n ∣ n := ⟨d n*e n, (h n).1.symm.trans (by ring)⟩
    have hen : e n ∣ n := ⟨d n^2, (h n).1.symm.trans (Nat.mul_comm _ _)⟩
    have hd0 : 0 < d n := Nat.pos_of_dvd_of_pos hdn hn0
    have he0 : 0 < e n := Nat.pos_of_dvd_of_pos hen hn0
    have hnR := (mem_Icc.mp hnI).2
    apply mem_product.mpr
    refine ⟨mem_Icc.mpr ⟨hd0,(Nat.le_of_dvd hn0 hdn).trans hnR⟩,mem_filter.mpr ?_⟩
    exact ⟨mem_Icc.mpr ⟨he0,(Nat.le_of_dvd hn0 hen).trans hnR⟩,hc.of_dvd_right hen,(h n).2⟩
  have hi : Set.InjOn f A := by
    intro n _ m _ hh
    have h₁ := congrArg Prod.fst hh
    have h₂ := congrArg Prod.snd hh
    change d n = d m at h₁
    change e n = e m at h₂
    rw [← (h n).1, h₁, h₂, (h m).1]
  have hw (n : ℕ) : (n:ℝ)⁻¹ = w (f n) := by
    have H : (d n:ℝ)^2 * (e n:ℝ) = (n:ℝ) := by exact_mod_cast (h n).1
    rw [← H, mul_inv]
  have hbase : (∑ n ∈ I, ((n:ℝ)^2)⁻¹) ≤ Real.pi^2/6 := by
    have H := hasSum_zeta_two
    simp only [one_div] at H
    exact H.tsum_eq ▸ H.summable.sum_le_tsum I (fun _ _ => by positivity)
  change (∑ n ∈ A, (n:ℝ)⁻¹) ≤ _ * (∑ n ∈ B, (n:ℝ)⁻¹)
  calc
    _ = ∑ p ∈ A.image f, w p := by rw [Finset.sum_image hi]; exact sum_congr rfl (fun n _ => hw n)
    _ ≤ ∑ p ∈ I.product B, w p := sum_le_sum_of_subset_of_nonneg hf (fun p _ _ => by
      unfold w
      positivity)
    _ = ∑ d ∈ I, ∑ e ∈ B, w (d,e) := Finset.sum_product I B w
    _ = (∑ d ∈ I, ((d:ℝ)^2)⁻¹)*(∑ e ∈ B, (e:ℝ)⁻¹) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right hbase (sum_nonneg (fun _ _ => by positivity))

/-- A uniform explicit lower bound sufficient for the lower side of
Jutila's harmonic Lemma 5; no asymptotic or error term is required. -/
theorem squarefree_coprime_lower (R q : ℕ) (hq : q ≠ 0) :
    (6 / Real.pi^2) * ((q.totient:ℝ)/q) * (∑ n ∈ Icc 1 R, (n:ℝ)⁻¹) ≤
      ∑ n ∈ (Icc 1 R).filter (fun n => q.Coprime n ∧ Squarefree n), (n:ℝ)⁻¹ := by
  have h := (coprime_lower R q hq).trans (squarefree_loss R q)
  rw [mul_assoc, show (6 / Real.pi^2 : ℝ) = (Real.pi^2/6)⁻¹ by rw [inv_div],
    mul_comm ((Real.pi^2/6)⁻¹), ← div_eq_mul_inv]
  exact (div_le_iff₀ (by positivity [Real.pi_pos])).mpr (by simpa only [mul_comm] using h)

theorem squarefree_coprime_log_lower {Y : ℝ} (hY : 0 ≤ Y) (q : ℕ) (hq : q ≠ 0) :
    (6 / Real.pi^2) * ((q.totient:ℝ)/q) * Real.log Y ≤
      ∑ n ∈ (Icc 1 ⌊Y⌋₊).filter (fun n => q.Coprime n ∧ Squarefree n), (n:ℝ)⁻¹ := by
  have H := log_le_harmonic_floor Y hY
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at H
  exact (mul_le_mul_of_nonneg_left H (by positivity)).trans
    (squarefree_coprime_lower _ q hq)

#print axioms squarefree_coprime_log_lower
#print axioms squarefree_loss
#print axioms squarefree_coprime_lower
#print axioms coprime_lower
end PintzJutilaHarmonicLower
