import PintzSignedPairCRT
import PintzGlobalPairSum

noncomputable section
open Finset PintzCRTConductor PintzGlobalPairArithmetic PintzGlobalPairSum PintzSignedPairCRT PintzFixedLCMRow
open scoped Classical
namespace PintzSignedSingularSum

theorem signed_row_mul {r s a b : ℕ} [NeZero a] [NeZero b] (h : a.Coprime b)
    (hr : r ∣ a) (hs : s ∣ a) (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (m : ℕ) :
    row χ ψ (a*b) m =
      row χ ψ a m * actual (1 : DirichletCharacter ℂ b) 1 m := by
  let : NeZero (a*b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  rw [row, dite_eq_right (NeZero.ne (a*b)),
    dite_eq_left (show r ∣ a*b ∧ s ∣ a*b from ⟨hr.trans (dvd_mul_right a b),hs.trans (dvd_mul_right a b)⟩),
    row, dite_eq_right (NeZero.ne a), dite_eq_left (show r ∣ a ∧ s ∣ a from ⟨hr,hs⟩),
    exact_actual_crt h, left_induced h hr, left_induced h hs, right_induced h hr, right_induced h hs]

theorem principal_neg {q : ℕ} [NeZero q] (x : ZMod q) :
    gaussSum (1 : DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift (-x)) =
      gaussSum (1 : DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift x) := by
  let u : (ZMod q)ˣ := -1
  have hu : ((ZMod.stdAddChar.mulShift u).mulShift x) = ZMod.stdAddChar.mulShift (-x) := by
    rw [AddChar.mulShift_mulShift]
    congr 1
    simp [u]
  rw [← hu, shift_phase, inv_one, MulChar.one_apply_coe, one_mul]

theorem principal_primePower {p a : ℕ} [NeZero (p^(a+1))] (hp : p.Prime) (m : ℕ) :
    actual (1 : DirichletCharacter ℂ (p^(a+1))) 1 m =
      if a = 0 then (PintzPoleEulerFloor.localTerm p m:ℂ) else 0 := by
  unfold actual
  rw [one_mul,inv_one,principal_neg]
  have hStd := PintzPrimePowerPrincipalGauss.exact_sum (a:=a) hp 1
  rw [Nat.cast_one,AddChar.mulShift_one] at hStd
  have hbig : ¬p^(a+1) ∣ 1 := by
    intro H
    exact hp.not_dvd_one ((dvd_pow_self _ (by omega : a+1 ≠ 0)).trans H)
  rw [hStd, ite_eq_right hbig]
  by_cases h : a = 0
  · subst a
    rw [ite_eq_left rfl, pow_zero, ite_eq_left (one_dvd _), Nat.cast_one, zero_sub,
      PintzPrimePowerPrincipalGauss.exact_sum hp m]
    simp only [pow_zero, ite_eq_left (one_dvd _), Nat.cast_one, neg_mul, one_mul, neg_neg]
    have hφ : ((p^1).totient:ℂ) = (p:ℂ)-1 := by
      rw [pow_one,Nat.totient_prime hp,Nat.cast_sub hp.one_le,Nat.cast_one]
    rw [hφ,PintzPoleEulerFloor.localTerm, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]
    by_cases H : p∣m <;> simp [H, sub_eq_add_neg]
  · have hsmall : ¬p^a∣1 := fun H => hp.not_dvd_one ((dvd_pow_self _ h).trans H)
    simp [h,hsmall]

theorem actual_one (m : ℕ) :
    actual (1 : DirichletCharacter ℂ 1) 1 m = 1 := by
  have hg (η : DirichletCharacter ℂ 1) (e : AddChar (ZMod 1) ℂ) :
      gaussSum η e = 1 := by
    have h (x : ZMod 1) : η x * e x = 1 := by
      have hη : η x = 1 := by rw [show x = 1 from Subsingleton.elim _ _, map_one]
      have he : e x = 1 := by rw [show x = 0 from Subsingleton.elim _ _, AddChar.map_zero_eq_one]
      rw [hη,he,mul_one]
    unfold gaussSum
    simp_rw [h]
    simp
  simp [actual,hg]

theorem principal_primePower_exp {p a : ℕ} [NeZero (p^a)] (hp : p.Prime)
    (ha : 0 < a) (m : ℕ) :
    actual (1 : DirichletCharacter ℂ (p^a)) 1 m =
      if a = 1 then (PintzPoleEulerFloor.localTerm p m:ℂ) else 0 := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  simpa only [Nat.succ_eq_add_one, show a+1=1 ↔ a=0 by omega] using
    (principal_primePower (a:=a) hp m)

theorem principal_product (m : ℕ)
    (s : Finset ℕ) (A : ℕ → ℕ) (hs : ∀ p ∈ s, p.Prime ∧ 0 < A p)
    (q : ℕ) [NeZero q] (hq : q = ∏ p ∈ s, p^A p) :
    actual (1 : DirichletCharacter ℂ q) 1 m =
      ∏ p ∈ s, if A p = 1 then (PintzPoleEulerFloor.localTerm p m:ℂ) else 0 := by
  induction s using Finset.induction_on generalizing q with
  | empty =>
    simp only [prod_empty] at hq ⊢
    subst q
    exact actual_one m
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
    rw [exact_actual_crt hpc, hLeft, hRight, prod_insert hps,
      IH (fun r hr => hs r (mem_insert_of_mem hr)) b rfl, principal_primePower_exp hp hA m]

theorem principal_exact {q m : ℕ} [NeZero q] :
    actual (1 : DirichletCharacter ℂ q) 1 m =
      if Squarefree q then ∏ p ∈ q.primeFactors, (PintzPoleEulerFloor.localTerm p m:ℂ) else 0 := by
  have hq := NeZero.ne q
  rw [principal_product m q.primeFactors q.factorization
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

/-- The signed principal factor is exactly the ordinary Möbius-weighted
Ramanujan coefficient used by the pole model. -/
theorem principal_matches_pole {q : ℕ} [NeZero q] (m : ℕ) :
    actual (1 : DirichletCharacter ℂ q) 1 m =
      PintzPoleKernelTail.weight q * PintzPoleKernelTail.ramanujan q m := by
  rw [principal_exact]
  by_cases H : Squarefree q
  · rw [ite_eq_left H, PintzPoleEulerFloor.weight_ramanujan_prod H, Complex.ofReal_prod]
  · rw [ite_eq_right H]
    simp [PintzPoleKernelTail.weight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree H]

theorem signed_row_lcm_mul {r s b : ℕ} [NeZero r] [NeZero s] [NeZero b]
    (h : (r.lcm s).Coprime b) (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (m : ℕ) :
    row χ ψ (r.lcm s * b) m = row χ ψ (r.lcm s) m *
      (PintzPoleKernelTail.weight b * PintzPoleKernelTail.ramanujan b m) := by
  let : NeZero (r.lcm s) := ⟨Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)⟩
  rw [signed_row_mul h (Nat.dvd_lcm_left r s) (Nat.dvd_lcm_right r s), principal_matches_pole]

def freeRow (d b m : ℕ) : ℂ :=
  if d.Coprime b then PintzPoleKernelTail.weight b * PintzPoleKernelTail.ramanujan b m else 0

def twistedSeries {r s : ℕ} (χ : DirichletCharacter ℂ r) (ψ : DirichletCharacter ℂ s)
    (m : ℕ) : ℂ := ∑' q : ℕ, row χ ψ q m

theorem row_lcm_mul_all {r s : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) {m : ℕ} (hm : m ≠ 0) (he : Even m) (b : ℕ) :
    row χ ψ (r.lcm s*b) m = row χ ψ (r.lcm s) m * freeRow (r.lcm s) b m := by
  let d := r.lcm s
  by_cases hb : b = 0
  · subst b
    simp [row, freeRow, PintzPoleKernelTail.weight]
  let : NeZero b := ⟨hb⟩
  by_cases h : d.Coprime b
  · rw [freeRow, ite_eq_left h, signed_row_lcm_mul h]
  · rw [freeRow, ite_eq_right h, mul_zero]
    by_contra H
    obtain ⟨c,hc,hcop,_⟩ := row_support hχ hψ hm he H
    have hd : 0 < d := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s))
    have hbc : b = c := Nat.eq_of_mul_eq_mul_left hd hc
    exact h (hbc ▸ hcop)

theorem twistedSeries_eq_lcm_times {r s : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) {m : ℕ} (hm : m ≠ 0) (he : Even m) :
    twistedSeries χ ψ m = row χ ψ (r.lcm s) m * ∑' b, freeRow (r.lcm s) b m := by
  let d := r.lcm s
  have hd : 0 < d := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s))
  have hi : Function.Injective (fun b : ℕ => d*b) :=
    fun b c h => Nat.eq_of_mul_eq_mul_left hd h
  have H : Function.support (fun q => row χ ψ q m) ⊆ Set.range (fun b : ℕ => d*b) := by
    intro q hq
    obtain ⟨b,hb,_,_⟩ := row_support hχ hψ hm he hq
    exact ⟨b,hb.symm⟩
  rw [twistedSeries, ← hi.tsum_eq H, ← tsum_mul_left]
  exact tsum_congr (row_lcm_mul_all hχ hψ hm he)

def freeLocal (d m p : ℕ) : ℝ :=
  if p.Prime ∧ ¬p ∣ d then PintzPoleEulerFloor.localTerm p m else 0

theorem summable_freeLocal_norm (d : ℕ) {m : ℕ} (hm : m ≠ 0) :
    Summable (fun p => ‖freeLocal d m p‖) := by
  have h : Summable (fun n : ℕ => 4/(n:ℝ)^2) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left (4:ℝ)
  apply h.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop (m+1)] with p hp
  by_cases H : p.Prime ∧ ¬p ∣ d
  · have hp2 : (2:ℝ) ≤ p := by exact_mod_cast H.1.two_le
    have hp1 : (0:ℝ) < (p:ℝ)-1 := by linarith
    have hpp : (0:ℝ) < p := by linarith
    have hpM : ¬p ∣ m := fun hpD => (Nat.not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hpD))
      (Nat.lt_of_succ_le hp)
    rw [norm_norm, freeLocal, ite_eq_left H, PintzPoleEulerFloor.localTerm, ite_eq_right hpM,
      norm_div, norm_neg, norm_one, Real.norm_of_nonneg (sq_nonneg _)]
    apply (div_le_div_iff₀ (sq_pos_of_pos hp1) (sq_pos_of_pos hpp)).mpr
    nlinarith [mul_nonneg (show 0 ≤ (p:ℝ)-2 by linarith) hpp.le]
  · simp [freeLocal,H]
    positivity

private def freeSubset (d m : ℕ) (F : Finset ℕ) : ℂ :=
  (∏ p ∈ F, freeLocal d m p : ℝ)

private theorem freeSubset_support {d m : ℕ} {F : Finset ℕ}
    (hF : F ∈ Function.support (freeSubset d m)) :
    ∀ p ∈ F, p.Prime ∧ ¬p ∣ d := by
  intro p hp
  by_contra H
  apply hF
  unfold freeSubset
  rw [prod_eq_zero hp (show freeLocal d m p = 0 by simp [freeLocal,H]), Complex.ofReal_zero]

private theorem freeSubset_matches {d m : ℕ} {F : Finset ℕ}
    (hf : ∀ p ∈ F, p.Prime ∧ ¬p ∣ d) :
    freeRow d (∏ p ∈ F, p) m = freeSubset d m F := by
  let b := ∏ p ∈ F, p
  have hb : b.primeFactors = F := Nat.primeFactors_prod (fun p hp => (hf p hp).1)
  have hs : Squarefree b := by
    have H := Nat.squarefree_prod_primeFactors b
    rwa [hb] at H
  have hcop : d.Coprime b := Nat.coprime_prod_right_iff.mpr
    (fun p hp => ((hf p hp).1.coprime_iff_not_dvd.mpr (hf p hp).2).symm)
  rw [freeRow, ite_eq_left hcop, PintzPoleEulerFloor.weight_ramanujan_prod hs]
  change (↑(∏ p ∈ b.primeFactors, PintzPoleEulerFloor.localTerm p m) : ℂ) = freeSubset d m F
  rw [hb]
  unfold freeSubset
  congr 1
  exact prod_congr rfl (fun p hp => by simp [freeLocal, hf p hp])

theorem freeRow_tsum_eq_subset {d m : ℕ} :
    (∑' b, freeRow d b m) = ∑' F : Finset ℕ, freeSubset d m F := by
  let i (F : Function.support (freeSubset d m)) := ∏ p ∈ F.val, p
  have he (F : Function.support (freeSubset d m)) : (i F).primeFactors = F.val :=
    Nat.primeFactors_prod (fun p hp => (freeSubset_support F.property p hp).1)
  refine tsum_eq_tsum_of_ne_zero_bij i (fun F G h => Subtype.ext ((he F).symm.trans
    ((congrArg Nat.primeFactors h).trans (he G)))) ?_ (fun F => freeSubset_matches (freeSubset_support F.property))
  intro b hb
  have hb0 : b ≠ 0 := fun h => hb (by simp [h,freeRow,PintzPoleKernelTail.weight])
  have hc : d.Coprime b := by
    by_contra H
    exact hb (by simp [freeRow,H])
  have hs : Squarefree b := by
    by_contra H
    exact hb (by simp [freeRow,PintzPoleKernelTail.weight,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree H])
  have hf (p : ℕ) (hp : p ∈ b.primeFactors) : p.Prime ∧ ¬p ∣ d := by
    obtain ⟨hp',hpb,_⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨hp',hp'.coprime_iff_not_dvd.mp (hc.symm.coprime_dvd_left hpb)⟩
  have hProd := Nat.prod_primeFactors_of_squarefree hs
  have ha : b.primeFactors ∈ Function.support (freeSubset d m) := by
    have h' := freeSubset_matches (m := m) hf
    rw [hProd] at h'
    exact fun h => hb (h'.trans h)
  exact ⟨⟨b.primeFactors,ha⟩,hProd⟩

theorem freeRow_euler {d m : ℕ} (hm : m ≠ 0) :
    (∑' b, freeRow d b m) = ((∏' p : ℕ, (1 + freeLocal d m p)) : ℝ) := by
  rw [freeRow_tsum_eq_subset]
  have h := summable_finsetProd_of_summable_norm (summable_freeLocal_norm d hm)
  unfold freeSubset
  rw [← Complex.ofReal_tsum, ← tprod_one_add h]

theorem row_summable_norm {r s : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) {m : ℕ} (hm : m ≠ 0) (he : Even m) :
    Summable (fun q => ‖row χ ψ q m‖) := by
  apply summable_of_sum_le (c := eulerCorrection * singularSeries m) (fun q => norm_nonneg _)
  intro F
  have h0 : row χ ψ 0 m = 0 := by simp [row]
  have heq : (∑ q ∈ F, ‖row χ ψ q m‖) = ∑ q ∈ F.erase 0, ‖row χ ψ q m‖ := by
    by_cases H : 0 ∈ F
    · simpa [h0] using (sum_erase_add F (fun q => ‖row χ ψ q m‖) H).symm
    · rw [erase_eq_of_notMem H]
  rw [heq]
  refine (sum_le_sum_of_subset_of_nonneg (t:=Icc 1 (F.sup id)) ?_ (fun q _ _ => norm_nonneg _)).trans ?_
  · intro q hq
    exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero (mem_erase.mp hq).1, le_sup (f := id) (mem_erase.mp hq).2⟩
  · exact row_sum_singularSeries hχ hψ hm he _

theorem twistedSeries_euler {r s : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) {m : ℕ} (hm : m ≠ 0) (he : Even m) :
    twistedSeries χ ψ m = row χ ψ (r.lcm s) m *
      ((∏' p, (1 + freeLocal (r.lcm s) m p)) : ℝ) := by
  rw [twistedSeries_eq_lcm_times hχ hψ hm he, freeRow_euler hm]

theorem add_localTerm_eq_ordinary {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    1 + PintzPoleEulerFloor.localTerm p m = PintzForcedLocalEnvelope.ordinary p (m.factorization p) := by
  have hp1 : (p:ℝ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  have hpm : p ∣ m ↔ 1 ≤ m.factorization p := by
    simpa only [pow_one] using hp.pow_dvd_iff_le_factorization hm (k:=1)
  by_cases H : p ∣ m
  · have hz : m.factorization p ≠ 0 := by have := hpm.mp H; omega
    rw [PintzPoleEulerFloor.localTerm, ite_eq_left H,
      PintzForcedLocalEnvelope.ordinary, ite_eq_right hz]
    field_simp
    ring
  · have hz : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd H
    rw [PintzPoleEulerFloor.localTerm, ite_eq_right H,
      PintzForcedLocalEnvelope.ordinary, ite_eq_left hz]
    field_simp
    ring

theorem ordinary_factor_pos {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) (he : Even m) :
    0 < PintzForcedLocalEnvelope.ordinary p (m.factorization p) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < p := by linarith
  unfold PintzForcedLocalEnvelope.ordinary
  split_ifs with h
  · have hne : p ≠ 2 := by
      intro H
      have hd : p ∣ m := H ▸ even_iff_two_dvd.mp he
      have := (hp.dvd_iff_one_le_factorization hm).mp hd
      omega
    have hp3 : (3:ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    exact div_pos (mul_pos hp0 (by linarith)) (sq_pos_of_pos (by linarith))
  · exact div_pos hp0 (by linarith)

def forcedProduct (d m : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, PintzForcedLocalEnvelope.ordinary p (m.factorization p)

theorem singularSeries_split {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) :
    singularSeries m = forcedProduct d m * (∏' p, (1 + freeLocal d m p)) := by
  let F (p : ℕ) := if p ∈ d.primeFactors then
    PintzForcedLocalEnvelope.ordinary p (m.factorization p) else 1
  have hF (p : ℕ) (hp : p ∉ d.primeFactors) : F p = 1 := ite_eq_right hp
  have hM : Multipliable F := multipliable_of_ne_finset_one hF
  have hG : Multipliable (fun p => 1 + freeLocal d m p) :=
    Real.multipliable_one_add_of_summable (summable_freeLocal_norm d hm).of_norm
  have hE (p : ℕ) : signedEulerFactor m p = F p * (1 + freeLocal d m p) := by
    by_cases H : p.Prime
    · by_cases H' : p ∣ d
      · have hx : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨H,H',hd⟩
        simp [signedEulerFactor, F, freeLocal, H,H',hd]
      · have hx : p ∉ d.primeFactors := fun hp => H' (Nat.mem_primeFactors.mp hp).2.1
        simp [signedEulerFactor, F, freeLocal, H,H', add_localTerm_eq_ordinary H hm]
    · have hx : p ∉ d.primeFactors := fun hp => H (Nat.mem_primeFactors.mp hp).1
      simp [signedEulerFactor, F, freeLocal,H]
  unfold singularSeries
  simp_rw [hE]
  rw [hM.tprod_mul hG, tprod_eq_prod hF]
  unfold forcedProduct
  congr 1
  exact prod_congr rfl fun p hp => ite_eq_left hp

/-- For every pair, the signed singular series is the ordinary one times
the exact (possibly negative or complex) ratio at the forced conductor. -/
theorem twistedSeries_ratio {r s : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) {m : ℕ} (hm : m ≠ 0) (he : Even m) :
    twistedSeries χ ψ m = row χ ψ (r.lcm s) m *
      ((singularSeries m / forcedProduct (r.lcm s) m : ℝ) : ℂ) := by
  have hp : 0 < forcedProduct (r.lcm s) m :=
    prod_pos fun p hp => ordinary_factor_pos (Nat.mem_primeFactors.mp hp).1 hm he
  rw [twistedSeries_euler hχ hψ hm he,
    singularSeries_split (Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)) hm,
    mul_div_cancel_left₀ _ hp.ne']

theorem pole_twistedSeries {m : ℕ} (hm : m ≠ 0) (he : Even m) :
    twistedSeries (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m = (singularSeries m : ℂ) := by
  have hp : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
    change (1 : DirichletCharacter ℂ 1).conductor = 1
    exact DirichletCharacter.conductor_one
  rw [twistedSeries_ratio hp hp hm he]
  simp only [Nat.lcm_one_left, forcedProduct, Nat.primeFactors_one, prod_empty, div_one]
  have hrow : row (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 1 m = 1 := by
    simp [row, actual_one]
  rw [hrow, one_mul]

open Filter Topology in
theorem singularSeries_ge_one {m : ℕ} (hm : m ≠ 0) (he : Even m) :
    1 ≤ singularSeries m := by
  apply ge_of_tendsto (signed_tendsto hm)
  filter_upwards [eventually_ge_atTop (2:ℕ)] with P hP
  unfold signedProduct
  have h2 : 2 ∈ cutPrimes P := mem_filter.mpr ⟨mem_range.mpr (by omega),Nat.prime_two⟩
  have hP (p : ℕ) (hp : p ∈ cutPrimes P) : p.Prime := (mem_filter.mp hp).2
  have h := PintzPoleEulerFloor.euler_product_floor _ hP h2 he
  have H : (∏ p ∈ cutPrimes P, (1 + PintzPoleEulerFloor.localTerm p m)) =
      (∏ p ∈ cutPrimes P, PintzForcedLocalEnvelope.ordinary p (m.factorization p)) :=
    prod_congr rfl (fun p hp => add_localTerm_eq_ordinary (hP p hp) hm)
  rwa [H] at h

theorem norm_row_lcm_le_forced {r s : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) {m : ℕ} (hm : m ≠ 0) (he : Even m) :
    ‖row χ ψ (r.lcm s) m‖ ≤ forcedProduct (r.lcm s) m := by
  let d := r.lcm s
  have hd : d ≠ 0 := Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)
  let : NeZero d := ⟨hd⟩
  have hl : r ∣ d := Nat.dvd_lcm_left _ _
  have hr : s ∣ d := Nat.dvd_lcm_right _ _
  change ‖row χ ψ d m‖ ≤ forcedProduct d m
  have H := norm_actual_global_major hm he
    (DirichletCharacter.changeLevel hl χ) (DirichletCharacter.changeLevel hr ψ)
  simp only [DirichletCharacter.conductor_changeLevel, show χ.conductor = r from hχ,
    show ψ.conductor = s from hψ] at H
  rw [row, dite_eq_right hd, dite_eq_left (show r ∣ d ∧ s ∣ d from ⟨hl,hr⟩)]
  refine H.trans (show major r s d m ≤ forcedProduct d m from ?_)
  by_cases hM : major r s d m = 0
  · rw [hM]
    exact prod_nonneg (fun p hp => (ordinary_factor_pos (Nat.mem_primeFactors.mp hp).1 hm he).le)
  · have HH := (support_info (NeZero.ne r) (NeZero.ne s) hd hl hr hM).2
    change major r s d m = forcedProduct d m *
      ∏ p ∈ d.primeFactors \ d.primeFactors, freeFactor p m at HH
    simp [HH]

/-- Pintz (7.7), signed full row: the comparison constant is exactly one. -/
theorem norm_twistedSeries_le {r s : ℕ} [NeZero r] [NeZero s]
    {χ : DirichletCharacter ℂ r} {ψ : DirichletCharacter ℂ s}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) {m : ℕ} (hm : m ≠ 0) (he : Even m) :
    ‖twistedSeries χ ψ m‖ ≤ singularSeries m := by
  have hF : 0 < forcedProduct (r.lcm s) m :=
    prod_pos fun p hp => ordinary_factor_pos (Nat.mem_primeFactors.mp hp).1 hm he
  have hS0 : 0 ≤ singularSeries m := (by norm_num : (0:ℝ) ≤ 1).trans (singularSeries_ge_one hm he)
  have hR : 0 ≤ singularSeries m / forcedProduct (r.lcm s) m := div_nonneg hS0 hF.le
  rw [twistedSeries_ratio hχ hψ hm he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR]
  calc
    _ ≤ forcedProduct (r.lcm s) m * (singularSeries m / forcedProduct (r.lcm s) m) :=
      mul_le_mul_of_nonneg_right (norm_row_lcm_le_forced hχ hψ hm he) hR
    _ = _ := mul_div_cancel₀ _ hF.ne'

#print axioms norm_twistedSeries_le
#print axioms singularSeries_ge_one
#print axioms twistedSeries_ratio
#print axioms pole_twistedSeries
#print axioms row_summable_norm
#print axioms freeRow_euler
#print axioms twistedSeries_eq_lcm_times
#print axioms signed_row_lcm_mul
#print axioms principal_matches_pole
#print axioms signed_row_mul
#print axioms principal_primePower
end PintzSignedSingularSum
