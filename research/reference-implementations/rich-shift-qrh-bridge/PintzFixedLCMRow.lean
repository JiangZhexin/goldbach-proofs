import PintzGlobalPairSum
import PintzPoleEulerFloor
import PintzPoleDivisorTail

noncomputable section
open Finset PintzGlobalPairArithmetic PintzCRTConductor PintzPrimePowerPair PintzGlobalPairSum
open scoped Classical
namespace PintzFixedLCMRow

private theorem crt_cast_left {a b : ℕ} [NeZero (a*b)] (h : a.Coprime b) (x : ZMod (a*b)) :
    (ZMod.chineseRemainder h x).1 = (ZMod.cast x : ZMod a) := by
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.cast_natCast (dvd_mul_right a b)]
  rfl

private theorem cast_via_left {r a b : ℕ} [NeZero (a*b)] (hr : r ∣ a)
    (y : ZMod (a*b)) : (ZMod.cast y : ZMod r) = ZMod.cast (ZMod.cast y : ZMod a) := by
  have hA : (ZMod.cast (y.val : ZMod (a*b)) : ZMod a) = (y.val : ZMod a) :=
    ZMod.cast_natCast (dvd_mul_right a b) y.val
  have hR : (ZMod.cast (y.val : ZMod (a*b)) : ZMod r) = (y.val : ZMod r) :=
    ZMod.cast_natCast (hr.trans (dvd_mul_right a b)) y.val
  have hAR : (ZMod.cast (y.val : ZMod a) : ZMod r) = (y.val : ZMod r) :=
    ZMod.cast_natCast hr y.val
  conv_lhs => rw [← ZMod.natCast_zmod_val y, hR]
  conv_rhs => rw [← ZMod.natCast_zmod_val y, hA, hAR]

theorem left_induced {r a b : ℕ} [NeZero (a*b)] (h : a.Coprime b) (hr : r ∣ a)
    (χ : DirichletCharacter ℂ r) :
    left h (DirichletCharacter.changeLevel (hr.trans (dvd_mul_right a b)) χ) =
      DirichletCharacter.changeLevel hr χ := by
  ext1 x
  let e := (ZMod.chineseRemainder h).symm
  let y := e (↑x, 1)
  have hy : IsUnit y := (Prod.isUnit_iff.mpr ⟨x.isUnit,isUnit_one⟩).map e
  change (DirichletCharacter.changeLevel (hr.trans (dvd_mul_right a b)) χ) y =
    (DirichletCharacter.changeLevel hr χ) x
  rw [← hy.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, hy.unit_spec]
  congr 1
  have H : (ZMod.cast y : ZMod a) = x := by
    rw [← crt_cast_left h y]
    dsimp [y,e]
    rw [RingEquiv.apply_symm_apply]
  rw [cast_via_left hr y, H]

theorem right_induced {r a b : ℕ} [NeZero (a*b)] (h : a.Coprime b) (hr : r ∣ a)
    (χ : DirichletCharacter ℂ r) :
    right h (DirichletCharacter.changeLevel (hr.trans (dvd_mul_right a b)) χ) = 1 := by
  ext1 x
  let e := (ZMod.chineseRemainder h).symm
  let y := e (1,↑x)
  have hy : IsUnit y := (Prod.isUnit_iff.mpr ⟨isUnit_one,x.isUnit⟩).map e
  change (DirichletCharacter.changeLevel (hr.trans (dvd_mul_right a b)) χ) y =
    (1 : DirichletCharacter ℂ b) x
  rw [← hy.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd, hy.unit_spec, MulChar.one_apply_coe]
  have H : (ZMod.cast y : ZMod a) = 1 := by
    rw [← crt_cast_left h y]
    dsimp [y,e]
    rw [RingEquiv.apply_symm_apply]
  rw [cast_via_left hr y, H, show (ZMod.cast (1 : ZMod a) : ZMod r) = 1 from map_one (ZMod.castHom hr (ZMod r)),
    map_one]

/-- The coprime extension of an induced pair contributes exactly the
principal coefficient on the extended modulus. -/
theorem norm_row_mul {r s a b : ℕ} [NeZero a] [NeZero b] (h : a.Coprime b)
    (hr : r ∣ a) (hs : s ∣ a) (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (m : ℕ) :
    ‖row χ ψ (a*b) m‖ =
      ‖row χ ψ a m‖ * coefficient (1 : DirichletCharacter ℂ b) 1 m := by
  let : NeZero (a*b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  rw [row, dite_eq_right (NeZero.ne (a*b)),
    dite_eq_left (show r ∣ a*b ∧ s ∣ a*b from ⟨hr.trans (dvd_mul_right a b),hs.trans (dvd_mul_right a b)⟩),
    row, dite_eq_right (NeZero.ne a), dite_eq_left (show r ∣ a ∧ s ∣ a from ⟨hr,hs⟩),
    norm_actual, norm_actual, coefficient_crt h, left_induced h hr, left_induced h hs,
      right_induced h hr, right_induced h hs]

theorem coefficient_principal_product (m : ℕ) (hm : m ≠ 0)
    (s : Finset ℕ) (A : ℕ → ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 0 < A p)
    (q : ℕ) [NeZero q] (hq : q = ∏ p ∈ s, p^A p) :
    coefficient (1 : DirichletCharacter ℂ q) 1 m =
      ∏ p ∈ s, if A p = 1 then freeFactor p m else 0 := by
  induction s using Finset.induction_on generalizing q with
  | empty =>
    simp only [prod_empty] at hq ⊢
    subst q
    exact coefficient_one 1 1 m
  | @insert p s hps IH =>
    obtain ⟨hp,hA⟩ := hs p (mem_insert_self _ _)
    let b := ∏ r ∈ s, r^A r
    have hpq : ¬p ∣ b := by
      intro H
      obtain ⟨r,hr,hD⟩ := (hp.prime.dvd_finsetProd_iff _).mp H
      have hpr := (hs r (mem_insert_of_mem hr)).1
      have he := (Nat.prime_dvd_prime_iff_eq hp hpr).mp (hp.dvd_of_dvd_pow hD)
      exact hps (he ▸ hr)
    have hpc : (p^A p).Coprime b :=
      (hp.coprime_iff_not_dvd.mpr hpq).pow_left _
    have hb : b ≠ 0 := prod_ne_zero_iff.mpr
      (fun r hr => pow_ne_zero _ (hs r (mem_insert_of_mem hr)).1.ne_zero)
    let : NeZero b := ⟨hb⟩
    let : NeZero (p^A p) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hq' : q = p^A p * b := by simpa only [prod_insert hps] using hq
    clear hq
    subst q
    have hLeft : left hpc (1 : DirichletCharacter ℂ (p^A p*b)) = 1 := by
      simpa only [DirichletCharacter.changeLevel_one] using
        left_induced hpc (one_dvd (p^A p)) (1 : DirichletCharacter ℂ 1)
    have hRight : right hpc (1 : DirichletCharacter ℂ (p^A p*b)) = 1 := by
      simpa only [DirichletCharacter.changeLevel_one] using
        right_induced hpc (one_dvd (p^A p)) (1 : DirichletCharacter ℂ 1)
    rw [coefficient_crt hpc, hLeft, hRight, prod_insert hps,
      IH (fun r hr => hs r (mem_insert_of_mem hr)) b rfl, both_principal hp hA hm]
    by_cases h : A p = 1
    · have hpm : p ∣ m ↔ 1 ≤ m.factorization p := by
        simpa only [pow_one] using hp.pow_dvd_iff_le_factorization hm (k:=1)
      simp only [h, ite_true, freeFactor, hpm]
    · simp only [ite_eq_right h]

theorem coefficient_principal_exact {q m : ℕ} [NeZero q] (hm : m ≠ 0) :
    coefficient (1 : DirichletCharacter ℂ q) 1 m =
      if Squarefree q then ∏ p ∈ q.primeFactors, freeFactor p m else 0 := by
  have hq := NeZero.ne q
  rw [coefficient_principal_product m hm q.primeFactors q.factorization
    (fun p hp => by
      obtain ⟨hP,hpq,hq⟩ := Nat.mem_primeFactors.mp hp
      exact ⟨hP, (hP.dvd_iff_one_le_factorization hq).mp hpq⟩)
    q (Nat.prod_primeFactors_pow_factorization hq)]
  by_cases hS : Squarefree q
  · rw [ite_eq_left hS]
    apply prod_congr rfl
    intro p hp
    obtain ⟨hP,hpq,hq⟩ := Nat.mem_primeFactors.mp hp
    have h := le_antisymm ((Nat.squarefree_iff_factorization_le_one hq).mp hS p)
      ((hP.dvd_iff_one_le_factorization hq).mp hpq)
    rw [ite_eq_left h]
  · rw [ite_eq_right hS]
    have h : ∃ p, ¬q.factorization p ≤ 1 := by
      simpa only [Nat.squarefree_iff_factorization_le_one hq, not_forall] using hS
    obtain ⟨p,hp⟩ := h
    have hpp : p ∈ q.primeFactors := by
      by_contra H
      have hz : q.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        simpa only [Nat.support_factorization] using H
      omega
    exact prod_eq_zero hpp (ite_eq_right (by omega : q.factorization p ≠ 1))

theorem norm_row_lcm_mul {r s b m : ℕ} [NeZero r] [NeZero s] [NeZero b]
    (h : (r.lcm s).Coprime b) (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (hm : m ≠ 0) :
    ‖row χ ψ (r.lcm s * b) m‖ =
      ‖row χ ψ (r.lcm s) m‖ *
        (if Squarefree b then ∏ p ∈ b.primeFactors, freeFactor p m else 0) := by
  let : NeZero (r.lcm s) := ⟨Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)⟩
  rw [norm_row_mul h (Nat.dvd_lcm_left r s) (Nat.dvd_lcm_right r s), coefficient_principal_exact hm]

theorem row_support {r s q m : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (he : Even m)
    (H : row χ ψ q m ≠ 0) :
    ∃ b, q = r.lcm s * b ∧ (r.lcm s).Coprime b ∧ Squarefree b := by
  have hq : q ≠ 0 := fun h => H (by simp [row, h])
  let : NeZero q := ⟨hq⟩
  have hd : r ∣ q ∧ s ∣ q := by
    by_contra hn
    exact H (by simp [row,hq,hn])
  have hM : major r s q m ≠ 0 := by
    apply ne_of_gt
    have Hb := norm_actual_global_major hm he (DirichletCharacter.changeLevel hd.1 χ)
      (DirichletCharacter.changeLevel hd.2 ψ)
    have hrow : 0 < ‖row χ ψ q m‖ := norm_pos_iff.mpr H
    rw [row, dite_eq_right hq, dite_eq_left hd] at hrow
    exact hrow.trans_le (by
      simpa only [major, DirichletCharacter.conductor_changeLevel,
        show χ.conductor = r from hχ, show ψ.conductor = s from hψ] using Hb)
  let d := r.lcm s
  let F := q.primeFactors \ d.primeFactors
  have hi := support_info (NeZero.ne r) (NeZero.ne s) hq hd.1 hd.2 hM
  refine ⟨∏ p ∈ F, p, hi.1, Nat.coprime_prod_right_iff.mpr ?_, ?_⟩
  · intro p hp
    obtain ⟨hQ,hD⟩ := mem_sdiff.mp hp
    have hP := (Nat.mem_primeFactors.mp hQ).1
    refine (hP.coprime_iff_not_dvd.mpr ?_).symm
    exact fun h => hD (Nat.mem_primeFactors.mpr ⟨hP,h,Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)⟩)
  · exact squarefree_prod_of_pairwise_isCoprime
      (fun p hp z hz hne => Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (Nat.mem_primeFactors.mp (mem_sdiff.mp hp).1).1
          (Nat.mem_primeFactors.mp (mem_sdiff.mp hz).1).1).mpr hne))
      (fun p hp => (Nat.mem_primeFactors.mp (mem_sdiff.mp hp).1).1.prime.squarefree)

/-- Exact decomposition of the free squarefree factor into its primes
dividing m and the remaining primes. -/
theorem free_split {b m : ℕ} (hb : Squarefree b) (hm : m ≠ 0) :
    ∃ h k : ℕ, h ∣ m ∧ k.Coprime m ∧ Squarefree h ∧ Squarefree k ∧ h*k = b ∧
      (∏ p ∈ b.primeFactors, freeFactor p m) = 1/(h.totient:ℝ) * (1/(k.totient:ℝ)^2) := by
  let A := b.primeFactors.filter (fun p => p ∣ m)
  let B := b.primeFactors.filter (fun p => ¬p ∣ m)
  let h := ∏ p ∈ A, p
  let k := ∏ p ∈ B, p
  have hA (p) (hp : p ∈ A) : p.Prime := (Nat.mem_primeFactors.mp (mem_filter.mp hp).1).1
  have hB (p) (hp : p ∈ B) : p.Prime := (Nat.mem_primeFactors.mp (mem_filter.mp hp).1).1
  have ha : h.primeFactors = A := Nat.primeFactors_prod hA
  have hk : k.primeFactors = B := Nat.primeFactors_prod hB
  have hSA : Squarefree h := by
    have H := Nat.squarefree_prod_primeFactors h
    rwa [ha] at H
  have hSB : Squarefree k := by
    have H := Nat.squarefree_prod_primeFactors k
    rwa [hk] at H
  have hAl : A ⊆ m.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hA p hp,(mem_filter.mp hp).2,hm⟩
  have hHd : h ∣ m := by
    have hh := (Nat.prod_primeFactors_dvd_iff (n:=h) hm).mpr (ha ▸ hAl)
    rwa [ha] at hh
  have hKc : k.Coprime m := Nat.coprime_prod_left_iff.mpr (fun p hp =>
    (hB p hp).coprime_iff_not_dvd.mpr (mem_filter.mp hp).2)
  refine ⟨h,k,hHd,hKc,hSA,hSB,?_,?_⟩
  · dsimp [h,k,A,B]
    rw [prod_filter_mul_prod_filter_not, Nat.prod_primeFactors_of_squarefree hb]
  · have hφ := PintzPoleArithmetic.totient_real_prod hSA
    have hkφ := PintzPoleArithmetic.totient_real_prod hSB
    rw [ha] at hφ
    rw [hk] at hkφ
    rw [hφ,hkφ, ← prod_pow, one_div, one_div, ← prod_inv_distrib, ← prod_inv_distrib]
    conv_lhs => rw [← prod_filter_mul_prod_filter_not b.primeFactors (fun p => p ∣ m)]
    congr 1
    · exact prod_congr rfl (fun p hp => by simp [freeFactor,(mem_filter.mp hp).2,one_div])
    · exact prod_congr rfl (fun p hp => by simp [freeFactor,(mem_filter.mp hp).2,one_div])

theorem principal_matches_pole_weight {q m : ℕ} [NeZero q] (hm : m ≠ 0) :
    coefficient (1 : DirichletCharacter ℂ q) 1 m =
      ‖PintzPoleKernelTail.weight q * PintzPoleKernelTail.ramanujan q m‖ := by
  classical
  rw [coefficient_principal_exact hm]
  by_cases H : Squarefree q
  · rw [ite_eq_left H, PintzPoleEulerFloor.weight_ramanujan_prod H, Complex.norm_real, Real.norm_eq_abs,
      Finset.abs_prod]
    apply prod_congr rfl
    intro p hp
    have hP := (Nat.mem_primeFactors.mp hp).1
    have hp1 : (1:ℝ) < p := by exact_mod_cast hP.one_lt
    have hp0 : 0 < (p:ℝ)-1 := by linarith
    unfold PintzPoleEulerFloor.localTerm freeFactor
    by_cases hpm : p ∣ m
    · rw [ite_eq_left hpm, ite_eq_left hpm, abs_of_nonneg (by positivity)]
      field_simp
    · rw [ite_eq_right hpm, ite_eq_right hpm, abs_div, abs_neg, abs_one, abs_of_nonneg (sq_nonneg _)]
  · rw [ite_eq_right H]
    simp [PintzPoleKernelTail.weight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree H]

/-- Fixed-lcm denominator tail with the existing elementary divisor loss.
This is weaker in cutoff than Pintz (10.21), but still power-saving after
the previously checked divisor subpower estimate. -/
theorem tail_lcm {r s m : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (he : Even m)
    {T U : ℕ} (hT : 0 < T) (hTU : T ≤ U) :
    (∑ t ∈ Ioc T U, ‖row χ ψ (r.lcm s*t) m‖) ≤
      ‖row χ ψ (r.lcm s) m‖ * ((90/Real.sqrt (T:ℝ)) * (m.divisors.card:ℝ)) := by
  let d := r.lcm s
  have hd : 0 < d := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s))
  calc
    _ ≤ ∑ t ∈ Ioc T U, ‖row χ ψ d m‖ *
        ‖PintzPoleKernelTail.weight t * PintzPoleKernelTail.ramanujan t m‖ := by
      apply sum_le_sum
      intro t ht
      have ht0 : 0 < t := hT.trans (mem_Ioc.mp ht).1
      let : NeZero t := ⟨ht0.ne'⟩
      by_cases H : d.Coprime t
      · let : NeZero d := ⟨hd.ne'⟩
        rw [norm_row_mul H (Nat.dvd_lcm_left r s) (Nat.dvd_lcm_right r s),
          principal_matches_pole_weight hm]
      · have hz : row χ ψ (d*t) m = 0 := by
          by_contra hn
          obtain ⟨u, hu, huc, _⟩ := row_support hχ hψ hm he hn
          have htu : t = u := Nat.eq_of_mul_eq_mul_left hd hu
          exact H (htu ▸ huc)
        rw [hz,norm_zero]
        positivity
    _ = _ := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (PintzPoleDivisorTail.finite_ramanujan_tail hT hTU (Nat.pos_of_ne_zero hm)) (norm_nonneg _)

#print axioms tail_lcm
#print axioms free_split
#print axioms row_support
#print axioms norm_row_lcm_mul
#print axioms norm_row_mul
end PintzFixedLCMRow
