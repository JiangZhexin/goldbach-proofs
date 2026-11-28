import PintzWeilZetaTruncation
import PintzWeilWeightedDesmoothing
import Zeta23.ThmE.MainChi

noncomputable section
open Finset Set MeasureTheory
open Zeta23 Zeta23.ThmE Zeta23.Tail
open PintzWeilTestWindow ArithmeticFunction PintzWeilZetaTruncation

namespace PintzWeilChiWindow

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

private theorem local_count_of_window (Z : ZeroConfig) {A : ℝ} (hA : 1 ≤ A)
    (hloc : ∀ t : ℝ, (Z.N t (t+1) : ℝ) ≤ A * Real.log (|t|+3)) :
    LocalCount (fun ρ : Z.carrier => (ρ : ℂ).im) (fun ρ : Z.carrier => Z.mult ρ) A := by
  refine ⟨hA, ?_⟩
  classical
  intro t s hs
  refine le_trans ?_ (hloc t)
  have hfin : (Z.window t (t+1)).Finite := Z.finite_window t (t+1)
  unfold ZeroConfig.N
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    rw [Set.Finite.mem_toFinset]
    exact ⟨ρ.2, hs ρ hρ⟩
  have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
  rw [Finset.sum_map] at h
  exact_mod_cast h

/-- Unit-window multiplicity count with a single absolute constant controlling
all primitive characters. The finite weighted-sum interface incurs (1+log q). -/
theorem chi_local_count_uniform :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hq : 1 < q) (hprim : χ.IsPrimitive),
      let Z := LZeros (LSeam_of hq hprim)
      LocalCount (fun ρ : Z.carrier => (ρ : ℂ).im) (fun ρ : Z.carrier => Z.mult ρ)
        (A * (1 + Real.log q)) := by
  obtain ⟨A,hA,hW⟩ := localCountChi_uniform_proof
  refine ⟨A,hA,?_⟩
  intro q _ χ hq hprim
  dsimp only
  let Z := LZeros (LSeam_of hq hprim)
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.zero_lt_one.trans hq
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq.le
  have hLq := Real.log_nonneg hq1
  have hA0 : 0 ≤ A := by linarith
  refine local_count_of_window Z (by nlinarith) ?_
  intro t
  have ht1 : 1 ≤ Real.log (|t|+3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    linarith [Real.exp_one_lt_d9, abs_nonneg t]
  rw [LZeros_N]
  calc
    _ ≤ A * Real.log ((q:ℝ) * (|t|+3)) := hW q χ hq hprim t
    _ = A * (Real.log q + Real.log (|t|+3)) := by
      rw [Real.log_mul hq0.ne' (by positivity)]
    _ ≤ A * ((1+Real.log q)*Real.log (|t|+3)) := by
      apply mul_le_mul_of_nonneg_left _ hA0
      nlinarith [mul_nonneg hLq (sub_nonneg.mpr ht1)]
    _ = _ := by ring

theorem chi_local_count (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∃ A : ℝ, LocalCount (fun ρ : (LZeros (LSeam_of hq hprim)).carrier => (ρ : ℂ).im)
      (fun ρ : (LZeros (LSeam_of hq hprim)).carrier => (LZeros (LSeam_of hq hprim)).mult ρ) A := by
  obtain ⟨A,_,hA⟩ := chi_local_count_uniform
  exact ⟨A*(1+Real.log q),hA q χ hq hprim⟩

/-- Zeros retained by a real truncation height. -/
theorem finite_low_ordinates (Z : ZeroConfig) (T : ℝ) :
    {ρ : Z.carrier | |(ρ:ℂ).im| ≤ T}.Finite := by
  have hfin := (Z.finite_window (-T-1) T).preimage_embedding (Function.Embedding.subtype (· ∈ Z.carrier))
  refine hfin.subset ?_
  intro ρ hρ
  have h := abs_le.mp (show |(ρ:ℂ).im| ≤ T from hρ)
  refine ⟨ρ.2, ?_, h.2⟩
  change -T-1 < (ρ:ℂ).im
  linarith [h.1]

/-- Common normalized logarithmic-bump multiplier in the zero term. -/
def windowTerm (g : ℝ → ℝ) (x y : ℝ) (s : ℂ) : ℂ :=
  (∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*s))*(((y:ℂ)^s-(x:ℂ)^s)/s)

def gammaTerm (κ q : ℕ) (k : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r *
    (((Complex.digamma (1/4 + (κ:ℂ)/2 + Complex.I*r/2)).re + Real.log (q/Real.pi):ℝ):ℂ)

theorem prime_twist {g : ℝ → ℝ} {δ a b : ℝ}
    (hneg : ∀ u ≤ 0, test g δ a b u = 0) (w : ℕ → ℂ) (n : ℕ) :
    ((vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (w n * test g δ a b (Real.log n) +
        (starRingEnd ℂ) (w n) * test g δ a b (-Real.log n)) =
    (vonMangoldt n : ℂ) * w n * (diff g δ a b (Real.log n) : ℂ) := by
  have hz : -Real.log n ≤ 0 := neg_nonpos.mpr (Real.log_natCast_nonneg n)
  have h := PintzWeilTestWindow.prime_weight hneg n
  rw [hneg _ hz, add_zero] at h
  rw [hneg _ hz, mul_zero, add_zero, mul_left_comm, h]
  ring

/-- Exact primitive-character smoothed interval formula, with its zero
summands expressed as signed short-interval kernels. -/
theorem signed_kernel_identity (hq : 1 < q) (hprim : χ.IsPrimitive)
    {g : ℝ → ℝ} {δ x y : ℝ}
    (hδ : 0 ≤ δ) (hx : 0 < x) (hxy : x ≤ y) (ha : δ < Real.log x)
    (hg : ContDiff ℝ 1 g) (hl : ∀ v ≤ -δ, g v = 0) (hr : ∀ v ≥ δ, g v = 0)
    (hm : (∫ v in (-δ)..δ, g v) = 1) :
    let Z := LZeros (LSeam_of hq hprim)
    let k := test g δ (Real.log x) (Real.log y)
    let f := fun ρ : Z.carrier => (Z.mult ρ : ℂ) * windowTerm g x y ρ
    Summable f ∧ (∑' ρ, f ρ) =
      -(∑' n : ℕ, (vonMangoldt n : ℂ) * coeff χ n *
        (diff g δ (Real.log x) (Real.log y) (Real.log n) : ℂ)) + gammaTerm (parity χ) q k := by
  dsimp only
  let Z := LZeros (LSeam_of hq hprim)
  let k := test g δ (Real.log x) (Real.log y)
  obtain ⟨hc,hkc,hneg⟩ := admissible hδ ha (Real.log_le_log hx hxy) hg hl hr hm
  have H := EF_lit_chi_L hq hprim k hc hkc
  have he (ρ : Z.carrier) : paperFT k (gammaOf ρ) = windowTerm g x y ρ := by
    have hz : IsNontrivialZeroL χ (ρ:ℂ) := ρ.2
    exact PintzWeilZetaWindow.evaluated_test _ (Complex.ne_zero_of_re_pos hz.2.1)
      hδ hx hxy ha hg hl hr hm
  unfold literatureRHSchi at H
  simp_rw [he] at H
  have hp := fun n => prime_twist hneg (coeff χ) n
  change _ ∧ _ = -(∑' n : ℕ, ((vonMangoldt n / Real.sqrt n : ℝ):ℂ) *
    (coeff χ n * test g δ (Real.log x) (Real.log y) (Real.log n) + (starRingEnd ℂ) (coeff χ n) *
    test g δ (Real.log x) (Real.log y) (-Real.log n))) + gammaTerm (parity χ) q k at H
  simp_rw [hp] at H
  exact H

/-- Sharp χ-twisted prime interval with a finite χ-zero sum. The archimedean
term and the bump in the finite zero terms remain explicit. -/
theorem sharp_prime_finite_zeros :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (hq : 1 < q) (hprim : χ.IsPrimitive) {g : ℝ → ℝ} {δ x y T : ℝ},
      0 ≤ δ → δ ≤ 1 → 1 ≤ x → x ≤ y → δ < Real.log x → 2 ≤ T →
      ContDiff ℝ 2 g → (∀ v, 0 ≤ g v) →
      (∀ v ≤ -δ, g v = 0) → (∀ v ≥ δ, g v = 0) →
      (∫ v in (-δ)..δ, g v) = 1 →
      let Z := LZeros (LSeam_of hq hprim)
      let k := test g δ (Real.log x) (Real.log y)
      let low := (finite_low_ordinates Z T).toFinset
      let f := fun ρ : Z.carrier => (Z.mult ρ : ℂ) * windowTerm g x y ρ
      let rhs := -(∑' n : ℕ, (vonMangoldt n:ℂ) * coeff χ n *
        (PintzWeilPrimeDesmoothing.sharp x y n:ℂ)) + gammaTerm (parity χ) q k
      let K := Real.exp δ * (∫ v, ‖deriv (deriv (fun u : ℝ => (g u : ℂ))) v‖) * (x+y)
      ‖rhs - (∑ ρ ∈ low, f ρ)‖ ≤
        K * (2 * (A * (1 + Real.log q)) * (((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (T+4)+((T^2)⁻¹+T⁻¹)/(T+4))) +
          (3*δ*(x+y)+2)*Real.log (y*Real.exp δ) := by
  obtain ⟨A,hA,hLocal⟩ := chi_local_count_uniform
  refine ⟨A,hA,?_⟩
  intro q _ χ hq hprim g δ x y T hδ hδ₁ hx hxy ha hT hg hn hl hr hm
  have hLC := hLocal q χ hq hprim
  dsimp only
  let Z := LZeros (LSeam_of hq hprim)
  let k := test g δ (Real.log x) (Real.log y)
  let low := (finite_low_ordinates Z T).toFinset
  let t (ρ : Z.carrier) := (Z.mult ρ : ℂ) * windowTerm g x y ρ
  let S := ∑ ρ ∈ low, t ρ
  let H := gammaTerm (parity χ) q k
  let Sc := ∑' n : ℕ, (vonMangoldt n:ℂ) * coeff χ n *
    (diff g δ (Real.log x) (Real.log y) (Real.log n):ℂ)
  let Pc := ∑' n : ℕ, (vonMangoldt n:ℂ) * coeff χ n * (PintzWeilPrimeDesmoothing.sharp x y n:ℂ)
  let K := Real.exp δ * (∫ v, ‖deriv (deriv (fun u : ℝ => (g u : ℂ))) v‖) * (x+y)
  let E := K * (2 * (A * (1 + Real.log q)) * (((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (T+4)+((T^2)⁻¹+T⁻¹)/(T+4)))
  let D := (3*δ*(x+y)+2)*Real.log (y*Real.exp δ)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  obtain ⟨hs,hmain⟩ := signed_kernel_identity hq hprim hδ hx0 hxy ha hg1 hl hr hm
  change Summable t at hs
  change (∑' ρ, t ρ) = -Sc + H at hmain
  have hsplit := hs.sum_add_tsum_subtype_compl low
  have he : (∑' ρ : Z.carrier, t ρ) - S = (∑' ρ : {ρ // ρ ∉ low}, t ρ) := by
    rw [show (∑' ρ : Z.carrier, t ρ) = S + (∑' ρ : {ρ // ρ ∉ low}, t ρ) from hsplit.symm]
    exact add_sub_cancel_left _ _
  have hlow (ρ : Z.carrier) : ρ ∉ low ↔ T < |(ρ:ℂ).im| := by
    change ρ ∉ (finite_low_ordinates Z T).toFinset ↔ T < |(ρ:ℂ).im|
    have hi : ρ ∈ (finite_low_ordinates Z T).toFinset ↔ |(ρ:ℂ).im| ≤ T :=
      (finite_low_ordinates Z T).mem_toFinset
    exact (not_congr hi).trans not_le
  let e : {ρ : Z.carrier // ρ ∉ low} ≃ {ρ : Z.carrier // T < |(ρ:ℂ).im|} :=
    Equiv.subtypeEquivRight hlow
  have htsum :
      (∑' ρ : {r // r ∉ low}, t ρ) = ∑' ρ : {r : Z.carrier // T < |(r:ℂ).im|}, t ρ :=
    e.tsum_eq (fun ρ => t ρ)
  have htail : ‖-Sc + H - S‖ ≤ E := by
    rw [← hmain, he, htsum]
    refine (omitted_tail (K := K) hLC hT ?_ (fun ρ => windowTerm g x y (ρ:ℂ)) ?_).2
    · exact mul_nonneg (mul_nonneg (Real.exp_pos δ).le (integral_nonneg (fun _ => norm_nonneg _)))
        (by linarith)
    · intro ρ hρ
      have hz : IsNontrivialZeroL χ (ρ:ℂ) := ρ.2
      refine signed_kernel_cubic hδ hx hxy hg ?_ hz.2.1.le hz.2.2.le (by linarith)
      intro v hv
      exact abs_le.mpr ⟨lt_of_not_ge (fun J => hv (hl v J)) |>.le,
        lt_of_not_ge (fun J => hv (hr v J)) |>.le⟩
  have hD : ‖Sc-Pc‖ ≤ D :=
    PintzWeilWeightedDesmoothing.desmooth_weighted_window (coeff χ)
      (fun n => DirichletCharacter.norm_le_one χ (n : ZMod q)) hδ hδ₁ hx hxy hg.continuous hn hl hr hm
  change ‖-Pc+H-S‖ ≤ E + D
  rw [show -Pc+H-S = (-Sc+H-S)+(Sc-Pc) by ring]
  exact (norm_add_le _ _).trans (add_le_add htail hD)

#print axioms chi_local_count_uniform
#print axioms chi_local_count
#print axioms signed_kernel_identity
#print axioms sharp_prime_finite_zeros

end PintzWeilChiWindow
