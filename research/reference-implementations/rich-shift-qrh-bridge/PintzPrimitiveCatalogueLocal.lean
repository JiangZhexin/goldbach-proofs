import PintzWeilPrimitivePrimeWindow
import PintzLowRealBlock

noncomputable section

open Finset Zeta23 Zeta23.ThmE PintzWeilPrimitivePrimeWindow

namespace PintzPrimitiveCatalogueLocal

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The same multiplicity notion is used in the analytic density statements
and the canonical Weil configuration, even for conductor one. -/
@[simp] theorem mult_eq_analyticOrderNatAt (hp : χ.IsPrimitive) (z : ℂ) :
    (zeroConfig hp).mult z = analyticOrderNatAt χ.LFunction z := by
  by_cases hq : q = 1
  · subst q
    rw [zeroConfig_one, zetaZeroConfig_mult, DirichletCharacter.LFunction_modOne_eq]
    rfl
  · have h : 1 < q := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (Ne.symm hq)
    rw [zeroConfig_eq_LZeros hp h, LZeros_mult]
    rfl

/-- The catalogue is exactly the true zeros of the indicated primitive
Dirichlet L-function in the open critical strip. -/
@[simp] theorem mem_carrier_iff (hp : χ.IsPrimitive) (z : ℂ) :
    z ∈ (zeroConfig hp).carrier ↔ χ.LFunction z = 0 ∧ 0 < z.re ∧ z.re < 1 := by
  by_cases hq : q = 1
  · subst q
    rw [zeroConfig_one, zetaZeroConfig_carrier, DirichletCharacter.LFunction_modOne_eq]
    rfl
  · have h : 1 < q := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (Ne.symm hq)
    rw [zeroConfig_eq_LZeros hp h, LZeros_carrier]
    rfl

/-- A centered, closed, unit-height box of an arbitrary finite right-half
subset of the canonical catalogue.  Endpoints are included. -/
theorem local_count_real (hp : χ.IsPrimitive) {Q : ℕ} {T : ℝ}
    (hqQ : q ≤ Q) (hT : 0 ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ (zeroConfig hp).carrier ∧ 1/2 ≤ z.re)
    (t : ℝ) (ht : |t| ≤ T+1/2) :
    (∑ z ∈ S.filter (fun z => |z.im-t| ≤ 1/2), ((zeroConfig hp).mult z : ℝ)) ≤
      PintzLowRealBlock.actualC Q T := by
  simp_rw [mult_eq_analyticOrderNatAt hp]
  have hbeta (z : ℂ) (hz : z ∈ S) : 1/2 ≤ z.re ∧ z.re < 1 :=
    ⟨(hS z hz).2, ((mem_carrier_iff hp z).mp (hS z hz).1).2.2⟩
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    classical
    let j : Σ k : ℕ, DirichletCharacter ℂ (k+1) := ⟨k,χ⟩
    have hj : j ∈ PintzSieveToHybrid.family Q := by
      apply Finset.mem_sigma.mpr
      exact ⟨Finset.mem_range.mpr hqQ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
    exact PintzLowRealBlock.actual_local_count hT (fun _ => S)
      (fun _ _ z hz => hbeta z hz) j hj t ht

/-- Total multiplicity of a finite right-half zero subset up to height T. -/
theorem block_count_real (hp : χ.IsPrimitive) {Q : ℕ} {T : ℝ}
    (hqQ : q ≤ Q) (hT : 0 ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ (zeroConfig hp).carrier ∧ 1/2 ≤ z.re ∧ |z.im| ≤ T) :
    (∑ z ∈ S, ((zeroConfig hp).mult z : ℝ)) ≤
      (2*T+1)*PintzLowRealBlock.actualC Q T := by
  have hC : 0 ≤ PintzLowRealBlock.actualC Q T := by
    refine le_trans ?_ (le_max_right _ _)
    exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg T])) (Real.log_nonneg (by norm_num))
  exact PintzFixedWindowHigh.count_of_unit_boxes S Complex.im (fun z => ((zeroConfig hp).mult z : ℝ))
    hT hC (fun _ _ => Nat.cast_nonneg _) (fun z hz => (hS z hz).2.2)
    (local_count_real hp hqQ hT S (fun z hz => ⟨(hS z hz).1,(hS z hz).2.1⟩))

theorem local_count_nat (hp : χ.IsPrimitive) {Q : ℕ} {T : ℝ} (hqQ : q ≤ Q) (hT : 0 ≤ T)
    (S : Finset ℂ) (hS : ∀ z ∈ S, z ∈ (zeroConfig hp).carrier ∧ 1/2 ≤ z.re)
    (t : ℝ) (ht : |t| ≤ T+1/2) :
    (∑ z ∈ S.filter (fun z => |z.im-t| ≤ 1/2), (zeroConfig hp).mult z) ≤
      ⌈PintzLowRealBlock.actualC Q T⌉₊ := by
  exact_mod_cast (show ((∑ z ∈ S.filter (fun z => |z.im-t| ≤ 1/2), (zeroConfig hp).mult z : ℕ) : ℝ)
    ≤ (⌈PintzLowRealBlock.actualC Q T⌉₊ : ℕ) from by
      rw [Nat.cast_sum]
      exact (local_count_real hp hqQ hT S hS t ht).trans (Nat.le_ceil _))

theorem block_count_nat (hp : χ.IsPrimitive) {Q : ℕ} {T : ℝ}
    (hqQ : q ≤ Q) (hT : 0 ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ (zeroConfig hp).carrier ∧ 1/2 ≤ z.re ∧ |z.im| ≤ T) :
    (∑ z ∈ S, (zeroConfig hp).mult z) ≤
      ⌈(2*T+1)*PintzLowRealBlock.actualC Q T⌉₊ := by
  exact_mod_cast (show ((∑ z ∈ S, (zeroConfig hp).mult z : ℕ) : ℝ)
    ≤ (⌈(2*T+1)*PintzLowRealBlock.actualC Q T⌉₊ : ℕ) from by
      rw [Nat.cast_sum]
      exact (block_count_real hp hqQ hT S hS).trans (Nat.le_ceil _))

/-- The actual right-half finite catalogue; repeated zeros appear once, with
their analytic multiplicities recovered by `mult_eq_analyticOrderNatAt`. -/
def rightHalfCatalogue (hp : χ.IsPrimitive) (T : ℝ) : Finset ℂ :=
  ((zeroConfig hp).finite_window (-T-1) T).toFinset.filter
    (fun z => 1/2 ≤ z.re ∧ |z.im| ≤ T)

@[simp] theorem mem_rightHalfCatalogue (hp : χ.IsPrimitive) (T : ℝ) (z : ℂ) :
    z ∈ rightHalfCatalogue hp T ↔ χ.LFunction z = 0 ∧ 1/2 ≤ z.re ∧ z.re < 1 ∧ |z.im| ≤ T := by
  unfold rightHalfCatalogue
  rw [Finset.mem_filter, Set.Finite.mem_toFinset]
  change (z ∈ (zeroConfig hp).carrier ∧ (-T-1 < z.im ∧ z.im ≤ T)) ∧
    (1/2 ≤ z.re ∧ |z.im| ≤ T) ↔ _
  rw [mem_carrier_iff]
  constructor
  · exact fun h => ⟨h.1.1.1,h.2.1,h.1.1.2.2,h.2.2⟩
  · intro h
    have hz := abs_le.mp h.2.2.2
    exact ⟨⟨⟨h.1,by linarith [h.2.1],h.2.2.1⟩,by linarith [hz.1],hz.2⟩,h.2.1,h.2.2.2⟩

/-- On the shared truncation scale, the multiplicity of any right-half
finite subset is at most one absolute constant times √N (1 + log N). -/
theorem sqrt_scale_count :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hp : χ.IsPrimitive) {N : ℝ}, 4 ≤ N → (q:ℝ) ≤ N → ∀ S : Finset ℂ,
      (∀ z ∈ S, z ∈ (zeroConfig hp).carrier ∧ 1/2 ≤ z.re ∧ |z.im| ≤ Real.sqrt N) →
      (∑ z ∈ S, ((zeroConfig hp).mult z : ℝ)) ≤ C * Real.sqrt N * (1+Real.log N) := by
  let D : ℝ := 18/Real.log (55/52)+11/Real.log (12/11)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg
      (div_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
      (div_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
  refine ⟨3*D,by positivity,?_⟩
  intro q _ χ hp N hN hqN S hS
  have hs1 : 1 ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hsN : Real.sqrt N ≤ N := by
    have H := Real.sq_sqrt (show 0 ≤ N by linarith)
    nlinarith
  have hC := PintzLowRealBlock.actualC_log_bound (Q := q) (T := Real.sqrt N) (N := N)
    (by linarith) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (by linarith)
    (Real.sqrt_nonneg _) hsN
  have hLN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  calc
    _ ≤ (2*Real.sqrt N+1)*PintzLowRealBlock.actualC q (Real.sqrt N) :=
      block_count_real hp le_rfl (Real.sqrt_nonneg _) S hS
    _ ≤ (2*Real.sqrt N+1)*(D*Real.log N) := mul_le_mul_of_nonneg_left hC (by positivity)
    _ ≤ (3*Real.sqrt N)*(D*(1+Real.log N)) := by
      exact mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left (by linarith) hD)
        (by positivity) (by positivity)
    _ = _ := by ring

#print axioms mult_eq_analyticOrderNatAt
#print axioms mem_carrier_iff
#print axioms local_count_real
#print axioms block_count_real
#print axioms local_count_nat
#print axioms block_count_nat
#print axioms mem_rightHalfCatalogue
#print axioms sqrt_scale_count

end PintzPrimitiveCatalogueLocal
