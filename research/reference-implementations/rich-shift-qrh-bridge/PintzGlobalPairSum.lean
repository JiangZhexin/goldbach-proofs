import PintzGlobalPairArithmetic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section
open Finset PintzGlobalPairArithmetic
open scoped Classical
namespace PintzGlobalPairSum

def cutPrimes (P : ℕ) : Finset ℕ := (range (P+1)).filter Nat.Prime

def major (r s q m : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors,
    localMajor m p (q.factorization p) (r.factorization p) (s.factorization p)

theorem free_nonneg (p m : ℕ) (hp : p.Prime) : 0 ≤ freeFactor p m := by
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  unfold freeFactor
  split_ifs <;> positivity

theorem ordinary_le_absolute {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    PintzForcedLocalEnvelope.ordinary p (m.factorization p) ≤ 1 + freeFactor p m := by
  have hpl : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp1 := (sub_pos.mpr hpl).ne'
  have hpm : p ∣ m ↔ 1 ≤ m.factorization p := by
    simpa [pow_one] using hp.pow_dvd_iff_le_factorization hm (k:=1)
  by_cases H : p ∣ m
  · have H' : m.factorization p ≠ 0 := by have := hpm.mp H; omega
    rw [PintzForcedLocalEnvelope.ordinary, ite_eq_right H', freeFactor, ite_eq_left H]
    field_simp
    linarith
  · have H' : m.factorization p = 0 := by have := mt hpm.mpr H; omega
    rw [PintzForcedLocalEnvelope.ordinary, ite_eq_left H', freeFactor, ite_eq_right H]
    field_simp
    nlinarith

theorem support_info {r s q m : ℕ} (hr : r ≠ 0) (hs : s ≠ 0) (hq : q ≠ 0)
    (hrq : r ∣ q) (hsq : s ∣ q) (H : major r s q m ≠ 0) :
    let d := r.lcm s
    (q = d*∏ p ∈ q.primeFactors \ d.primeFactors, p) ∧
      major r s q m =
        (∏ p ∈ d.primeFactors, PintzForcedLocalEnvelope.ordinary p (m.factorization p)) *
          ∏ p ∈ q.primeFactors \ d.primeFactors, freeFactor p m := by
  let d := r.lcm s
  let F := q.primeFactors \ d.primeFactors
  have hd : d ≠ 0 := Nat.lcm_ne_zero hr hs
  have hdq : d ∣ q := Nat.lcm_dvd hrq hsq
  have hdQ : d.primeFactors ⊆ q.primeFactors := Nat.primeFactors_mono hdq hq
  have hU : d.primeFactors ∪ F = q.primeFactors := union_sdiff_of_subset hdQ
  have hD : Disjoint d.primeFactors F := disjoint_sdiff
  have hlcm (p : ℕ) : d.factorization p = max (r.factorization p) (s.factorization p) := by
    rw [Nat.factorization_lcm hr hs, Finsupp.sup_apply]
  have hM (p : ℕ) (hp : p ∈ q.primeFactors) :
      localMajor m p (q.factorization p) (r.factorization p) (s.factorization p) ≠ 0 :=
    prod_ne_zero_iff.mp H p hp
  have hzero (p : ℕ) (hp : p.Prime) : d.factorization p = 0 ↔ p ∉ d.primeFactors := by
    constructor
    · intro hz H
      have hh := (hp.dvd_iff_one_le_factorization hd).mp (Nat.mem_primeFactors.mp H).2.1
      omega
    · intro H
      by_contra! hz
      exact H (Nat.mem_primeFactors.mpr ⟨hp,
        (hp.dvd_iff_one_le_factorization hd).mpr (by omega), hd⟩)
  have hForced (p : ℕ) (hp : p ∈ d.primeFactors) :
      q.factorization p = d.factorization p ∧
      localMajor m p (q.factorization p) (r.factorization p) (s.factorization p) =
        PintzForcedLocalEnvelope.ordinary p (m.factorization p) := by
    have hP := (Nat.mem_primeFactors.mp hp).1
    have hnp : ¬(r.factorization p = 0 ∧ s.factorization p = 0) := by
      rintro ⟨h₁,h₂⟩
      exact ((hzero p hP).mp (by simp [hlcm,h₁,h₂])) hp
    have hh := hM p (hdQ hp)
    rw [localMajor, ite_eq_left hP, ite_eq_right hnp] at hh ⊢
    have E : q.factorization p = max (r.factorization p) (s.factorization p) := by
      by_contra K
      rw [ite_eq_right K] at hh
      exact hh rfl
    exact ⟨E.trans (hlcm p).symm, ite_eq_left E⟩
  have hFree (p : ℕ) (hp : p ∈ F) :
      q.factorization p = 1 ∧
      localMajor m p (q.factorization p) (r.factorization p) (s.factorization p) = freeFactor p m := by
    obtain ⟨hQ,hN⟩ := mem_sdiff.mp hp
    have hP := (Nat.mem_primeFactors.mp hQ).1
    have hz := (hzero p hP).mpr hN
    have hnp : r.factorization p = 0 ∧ s.factorization p = 0 := by
      rw [hlcm] at hz
      omega
    have hh := hM p hQ
    rw [localMajor, ite_eq_left hP, ite_eq_left hnp] at hh ⊢
    have E : q.factorization p = 1 := by
      by_contra K
      rw [ite_eq_right K] at hh
      exact hh rfl
    exact ⟨E, ite_eq_left E⟩
  change q = d * (∏ p ∈ F, p) ∧ _
  constructor
  · conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hq, ← hU, prod_union hD]
    congr 1
    · calc
        _ = ∏ p ∈ d.primeFactors, p^d.factorization p :=
          prod_congr rfl (fun p hp => by rw [(hForced p hp).1])
        _ = d := (Nat.prod_primeFactors_pow_factorization hd).symm
    · exact prod_congr rfl (fun p hp => by simp [(hFree p hp).1])
  · unfold major
    change (∏ p ∈ q.primeFactors, _) = _ * ∏ p ∈ F, _
    conv_lhs => rw [← hU, prod_union hD]
    congr 1
    · exact prod_congr rfl (fun p hp => (hForced p hp).2)
    · exact prod_congr rfl (fun p hp => (hFree p hp).2)

theorem sum_major {r s m : ℕ} (hr : r ≠ 0) (hs : s ≠ 0) (hm : m ≠ 0) (P : ℕ) :
    (∑ q ∈ (Icc 1 P).filter (fun q => r ∣ q ∧ s ∣ q), major r s q m) ≤
      ∏ p ∈ cutPrimes P, (1 + freeFactor p m) := by
  let S := (Icc 1 P).filter (fun q => r ∣ q ∧ s ∣ q)
  let T := S.filter (fun q => major r s q m ≠ 0)
  let d := r.lcm s
  let G := cutPrimes P
  let W := G \ d.primeFactors
  let C := ∏ p ∈ d.primeFactors, (1 + freeFactor p m)
  let f (q : ℕ) := q.primeFactors \ d.primeFactors
  have hpC : 0 ≤ C := prod_nonneg (fun p hp => by
    have h := free_nonneg p m (Nat.mem_primeFactors.mp hp).1
    linarith)
  have hstrip : (∑ q ∈ S, major r s q m) = ∑ q ∈ T, major r s q m := by
    unfold T
    rw [sum_filter (s := S)]
    exact sum_congr rfl (fun q _ => by by_cases H : major r s q m = 0 <;> simp [H])
  rw [show (∑ q ∈ (Icc 1 P).filter (fun q => r ∣ q ∧ s ∣ q), major r s q m) =
    ∑ q ∈ S, major r s q m from rfl, hstrip]
  have hG (q : ℕ) (hq : q ∈ S) : q.primeFactors ⊆ G := by
    intro p hp
    obtain ⟨hp',hd,hz⟩ := Nat.mem_primeFactors.mp hp
    have hq' := (mem_Icc.mp (mem_filter.mp hq).1).2
    exact mem_filter.mpr ⟨mem_range.mpr ((Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hd).trans_lt
      (Nat.lt_succ_of_le hq')), hp'⟩
  have hT (q : ℕ) (hq : q ∈ T) :
      q = d*∏ p ∈ f q, p ∧ major r s q m =
        (∏ p ∈ d.primeFactors, PintzForcedLocalEnvelope.ordinary p (m.factorization p)) *
           ∏ p ∈ f q, freeFactor p m := by
    obtain ⟨hS,hMajor⟩ := mem_filter.mp hq
    obtain ⟨hQ,hrq,hsq⟩ := mem_filter.mp hS
    have hz : q ≠ 0 := (show 0 < q from (mem_Icc.mp hQ).1).ne'
    exact support_info hr hs hz hrq hsq hMajor
  by_cases hNE : T.Nonempty
  · obtain ⟨q0,hq0⟩ := hNE
    have hS0 : q0 ∈ S := (mem_filter.mp hq0).1
    obtain ⟨hQP, hrq, hsq⟩ := mem_filter.mp hS0
    have hdG : d.primeFactors ⊆ G :=
      (Nat.primeFactors_mono (Nat.lcm_dvd hrq hsq)
        (show 0 < q0 from (mem_Icc.mp hQP).1).ne').trans (hG q0 hS0)
    have hInj : Set.InjOn f (↑T : Set ℕ) := by
      intro q hq q' hq' H
      rw [(hT q hq).1, (hT q' hq').1, H]
    have hMaps (q : ℕ) (hq : q ∈ T) : f q ∈ W.powerset := by
      apply mem_powerset.mpr
      intro p hp
      obtain ⟨h₁,h₂⟩ := mem_sdiff.mp hp
      exact mem_sdiff.mpr ⟨hG q (mem_filter.mp hq).1 h₁,h₂⟩
    have hW (M : Finset ℕ) (hM : M ∈ W.powerset) :
        0 ≤ ∏ p ∈ M, freeFactor p m := by
      exact prod_nonneg (fun p hp => free_nonneg p m
        (mem_filter.mp (mem_sdiff.mp (mem_powerset.mp hM hp)).1).2)
    have hForced :
        (∏ p ∈ d.primeFactors, PintzForcedLocalEnvelope.ordinary p (m.factorization p)) ≤ C := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hp' := (Nat.mem_primeFactors.mp hp).1
        have h₂ : (2:ℝ) ≤ p := by exact_mod_cast hp'.two_le
        unfold PintzForcedLocalEnvelope.ordinary
        split_ifs
        · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h₂)) (sq_nonneg _)
        · exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · exact fun p hp => ordinary_le_absolute (Nat.mem_primeFactors.mp hp).1 hm
    calc
      _ ≤ ∑ q ∈ T, C * ∏ p ∈ f q, freeFactor p m := by
        refine sum_le_sum fun q hq => ?_
        rw [(hT q hq).2]
        exact mul_le_mul_of_nonneg_right hForced (hW _ (hMaps q hq))
      _ = C * ∑ M ∈ T.image f, ∏ p ∈ M, freeFactor p m := by
        rw [← mul_sum, sum_image hInj]
      _ ≤ C * ∑ M ∈ W.powerset, ∏ p ∈ M, freeFactor p m := by
        apply mul_le_mul_of_nonneg_left _ hpC
        apply sum_le_sum_of_subset_of_nonneg _ (fun M hM _ => hW M hM)
        intro M hM
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hM
        exact hMaps q hq
      _ = _ := by
        rw [← prod_one_add, show C = ∏ p ∈ d.primeFactors, (1+freeFactor p m) from rfl,
          ← prod_union (show Disjoint d.primeFactors W from disjoint_sdiff),
          union_sdiff_of_subset hdG]
  · have H : T = ∅ := not_nonempty_iff_eq_empty.mp hNE
    rw [H, sum_empty]
    exact prod_nonneg (fun p hp => by
      have h := free_nonneg p m (mem_filter.mp hp).2
      linarith)

/-- The actual pair row sum, zero off common divisibility. -/
def row {r s : ℕ} (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (q m : ℕ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    if h : r ∣ q ∧ s ∣ q then
      actual (DirichletCharacter.changeLevel h.1 χ) (DirichletCharacter.changeLevel h.2 ψ) m
    else 0

theorem row_sum_absolute {r s m : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (he : Even m) (P : ℕ) :
    (∑ q ∈ Icc 1 P, ‖row χ ψ q m‖) ≤ ∏ p ∈ cutPrimes P, (1 + freeFactor p m) := by
  refine le_trans ?_ (sum_major (NeZero.ne r) (NeZero.ne s) hm P)
  rw [sum_filter]
  apply sum_le_sum
  intro q hq
  have hq' : q ≠ 0 := (show 0 < q from (mem_Icc.mp hq).1).ne'
  let : NeZero q := ⟨hq'⟩
  rw [row, dite_eq_right hq']
  by_cases h : r ∣ q ∧ s ∣ q
  · rw [dite_eq_left h, ite_eq_left h]
    have H := norm_actual_global_major hm he
      (DirichletCharacter.changeLevel h.1 χ) (DirichletCharacter.changeLevel h.2 ψ)
    simpa only [major, DirichletCharacter.conductor_changeLevel, show χ.conductor = r from hχ,
      show ψ.conductor = s from hψ] using H
  · rw [dite_eq_right h, ite_eq_right h, norm_zero]

def signedProduct (P m : ℕ) : ℝ :=
  ∏ p ∈ cutPrimes P, PintzForcedLocalEnvelope.ordinary p (m.factorization p)

def eulerCorrection : ℝ := Real.exp (∑' n : ℕ, 6/(n:ℝ)^2)

theorem absolute_factor_comparison {p m : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (he : Even m) :
    1 + freeFactor p m ≤
      PintzForcedLocalEnvelope.ordinary p (m.factorization p) * (1 + 6/(p:ℝ)^2) := by
  have hpl : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp1 := (sub_pos.mpr hpl).ne'
  have hpp : (0:ℝ) < p := by linarith
  have hpm : p ∣ m ↔ 1 ≤ m.factorization p := by
    simpa [pow_one] using hp.pow_dvd_iff_le_factorization hm (k:=1)
  by_cases H : p ∣ m
  · have H' : m.factorization p ≠ 0 := by have := hpm.mp H; omega
    rw [freeFactor, ite_eq_left H, PintzForcedLocalEnvelope.ordinary, ite_eq_right H']
    have hEq : 1 + 1 / ((p:ℝ)-1) = p / ((p:ℝ)-1) := by field_simp; ring
    rw [hEq]
    exact le_mul_of_one_le_right (show 0 ≤ (p:ℝ)/((p:ℝ)-1) by positivity)
      (show (1:ℝ) ≤ 1+6/(p:ℝ)^2 by linarith [show 0 ≤ (6:ℝ)/(p:ℝ)^2 by positivity])
  · have H' : m.factorization p = 0 := by have := mt hpm.mpr H; omega
    have hp3 : (3:ℝ) ≤ p := by
      have hpne : p ≠ 2 := fun h => H (h ▸ even_iff_two_dvd.mp he)
      exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    rw [freeFactor, ite_eq_right H, PintzForcedLocalEnvelope.ordinary, ite_eq_left H']
    have Hfac : 1 + 1 / ((p:ℝ)-1)^2 =
        ((p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2) * (1 + 2/((p:ℝ)*((p:ℝ)-2))) := by
      have hp2 : (p:ℝ)-2 ≠ 0 := by linarith
      field_simp [hp2]
      ring
    rw [Hfac]
    have hp2 : 0 < (p:ℝ)-2 := by linarith
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add (le_refl _)
    apply (div_le_div_iff₀ (mul_pos hpp hp2) (sq_pos_of_pos hpp)).mpr
    nlinarith [mul_nonneg (show 0 ≤ (p:ℝ)-3 by linarith) hpp.le]

theorem absolute_product_le_signed {m : ℕ} (hm : m ≠ 0) (he : Even m) (P : ℕ) :
    (∏ p ∈ cutPrimes P, (1 + freeFactor p m)) ≤ eulerCorrection * signedProduct P m := by
  have hS : Summable (fun n : ℕ => 6/(n:ℝ)^2) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left (6:ℝ)
  unfold eulerCorrection signedProduct
  calc
    _ ≤ ∏ p ∈ cutPrimes P, PintzForcedLocalEnvelope.ordinary p (m.factorization p) *
          (1 + 6/(p:ℝ)^2) := by
      apply prod_le_prod₀
      · intro p hp
        have hh := free_nonneg p m (mem_filter.mp hp).2
        linarith
      · exact fun p hp => absolute_factor_comparison (mem_filter.mp hp).2 hm he
    _ ≤ _ := by
      rw [prod_mul_distrib, mul_comm (Real.exp _)]
      apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun p hp => by
        have hp' := (mem_filter.mp hp).2
        have h₂ : (2:ℝ) ≤ p := by exact_mod_cast hp'.two_le
        unfold PintzForcedLocalEnvelope.ordinary
        split_ifs
        · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h₂)) (sq_nonneg _)
        · exact div_nonneg (Nat.cast_nonneg _) (by linarith))
      exact (Real.prod_one_add_le_exp_sum _ (f := fun n : ℕ => 6/(n:ℝ)^2) (fun n => by positivity)).trans
        (Real.exp_le_exp.mpr (hS.sum_le_tsum _ (fun n _ => by positivity)))

theorem row_sum_signed {r s m : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (he : Even m) (P : ℕ) :
    (∑ q ∈ Icc 1 P, ‖row χ ψ q m‖) ≤ eulerCorrection * signedProduct P m :=
  (row_sum_absolute hχ hψ hm he P).trans (absolute_product_le_signed hm he P)

def signedEulerFactor (m p : ℕ) : ℝ :=
  if p.Prime then PintzForcedLocalEnvelope.ordinary p (m.factorization p) else 1

/-- The ordinary Goldbach singular series as an actual convergent Euler product. -/
def singularSeries (m : ℕ) : ℝ := ∏' p : ℕ, signedEulerFactor m p

set_option maxHeartbeats 900000 in
theorem signed_multipliable {m : ℕ} (hm : m ≠ 0) :
    Multipliable (signedEulerFactor m) := by
  let f (p : ℕ) := signedEulerFactor m p - 1
  have hS : Summable (fun n : ℕ => 4/(n:ℝ)^2) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left (4:ℝ)
  have hf : Summable f := by
    apply hS.of_norm_bounded_eventually_nat
    filter_upwards [Filter.eventually_ge_atTop (m+1)] with p hp
    by_cases hP : p.Prime
    · have H : ¬p ∣ m := fun h => by
        have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h
        omega
      have h' : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd H
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hP.two_le
      have hp1 : (0:ℝ) < (p:ℝ)-1 := by linarith
      have hpp : (0:ℝ) < p := by linarith
      have hx : ((p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2) - 1 = -1 / ((p:ℝ)-1)^2 := by
        field_simp
        ring
      simp only [f, signedEulerFactor, ite_eq_left hP, PintzForcedLocalEnvelope.ordinary,
        ite_eq_left h', hx, norm_div, norm_neg, norm_one, Real.norm_of_nonneg (sq_nonneg _)]
      apply (div_le_div_iff₀ (sq_pos_of_pos hp1) (sq_pos_of_pos hpp)).mpr
      nlinarith [mul_nonneg (show 0 ≤ (p:ℝ)-2 by linarith) hpp.le]
    · simp [f, signedEulerFactor, hP]
      positivity
  have H := Real.multipliable_one_add_of_summable hf
  have he : (fun p : ℕ => 1+f p) = signedEulerFactor m := by
    funext p
    dsimp [f]
    ring
  rwa [he] at H

open Filter Topology in
theorem signed_tendsto {m : ℕ} (hm : m ≠ 0) :
    Tendsto (fun P => signedProduct P m) atTop (𝓝 (singularSeries m)) := by
  have h := ((signed_multipliable hm).hasProd.tendsto_prod_nat).comp
    (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, signedEulerFactor, ← prod_filter] at h
  exact h

open Filter Topology in
theorem row_sum_singularSeries {r s m : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (he : Even m) (P : ℕ) :
    (∑ q ∈ Icc 1 P, ‖row χ ψ q m‖) ≤ eulerCorrection * singularSeries m := by
  apply ge_of_tendsto ((signed_tendsto hm).const_mul eulerCorrection)
  filter_upwards [eventually_ge_atTop P] with H hH
  exact (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hH)
    (fun q _ _ => norm_nonneg _)).trans (row_sum_signed hχ hψ hm he H)

#print axioms row_sum_singularSeries
#print axioms row_sum_signed
#print axioms row_sum_absolute
#print axioms support_info
end PintzGlobalPairSum
