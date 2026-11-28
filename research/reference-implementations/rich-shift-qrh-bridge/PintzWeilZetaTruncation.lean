import PintzWeilPrimeDesmoothing
import PintzWeilZetaWindow
import Zeta23.Tail.Count
import Zeta23.RvM.LocalCount
import Zeta23.Poisson.PaperFT

noncomputable section
open Finset Set MeasureTheory
open Zeta23 Zeta23.Tail
namespace PintzWeilZetaTruncation

/-- Absolute ordinate tail, with explicit bound at any real cutoff (T≥2). -/
theorem finite_weighted_tail {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A T : ℝ}
    (hN : LocalCount γ m A) (hT : 2 ≤ T) (s : Finset ι) (hs : ∀ ρ ∈ s, T < |γ ρ|) :
    ∑ ρ ∈ s, (m ρ : ℝ) * ((|γ ρ|) ^ 3)⁻¹
      ≤ 2 * A * (((T ^ 3)⁻¹ + (T ^ 2)⁻¹ / 2) * Real.log (T + 4)
        + ((T ^ 2)⁻¹ + T⁻¹) / (T + 4)) := by
  classical
  have hT0 : 0 < T := by linarith
  have hA := hN.A₀_pos.le
  let W : ℝ := ((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (T + 4)+((T^2)⁻¹+T⁻¹)/(T+4)
  have side (v : Finset ι) (k : ι → ℕ)
      (hk : ∀ ρ ∈ v, T + k ρ ≤ |γ ρ|)
      (hc : ∀ j : ℕ, ∑ ρ ∈ v with k ρ = j, (m ρ : ℝ) ≤ A * Real.log (T+4+j)) :
      ∑ ρ ∈ v, (m ρ : ℝ) * ((|γ ρ|) ^ 3)⁻¹ ≤ A * W := by
    let N := (v.image k).sup id + 1
    have hv : v.image k ⊆ range N := fun j hj =>
      mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := id) hj))
    let g (j : ℕ) := ((T + j) ^ 3)⁻¹ * Real.log (T+4+j)
    have hgnn (j : ℕ) : 0 ≤ g j := by
      dsimp [g]
      exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]))
    rw [← sum_fiberwise_of_maps_to (g := k) (t := v.image k)
      (fun ρ hρ => mem_image_of_mem k hρ)]
    have hf (j : ℕ) (_ : j ∈ v.image k) :
        ∑ ρ ∈ v with k ρ = j, (m ρ : ℝ) * ((|γ ρ|) ^ 3)⁻¹ ≤ A * g j := by
      calc
        _ ≤ ∑ ρ ∈ v with k ρ = j, (m ρ : ℝ) * ((T+j) ^ 3)⁻¹ := by
          apply sum_le_sum
          intro ρ hρ
          obtain ⟨hρv, hkj⟩ := mem_filter.mp hρ
          have H := hk ρ hρv
          rw [hkj] at H
          gcongr
        _ = (∑ ρ ∈ v with k ρ = j, (m ρ : ℝ)) * ((T+j) ^ 3)⁻¹ := by rw [sum_mul]
        _ ≤ (A * Real.log (T+4+j)) * ((T+j) ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right (hc j) (by positivity)
        _ = _ := by dsimp [g]; ring
    refine (sum_le_sum hf).trans ?_
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ hA
    refine (sum_le_sum_of_subset_of_nonneg hv (fun j _ _ => hgnn j)).trans ?_
    have hg (j : ℕ) (_ : j ∈ range N) :
        g j ≤ ((T+j)^3)⁻¹ * Real.log (T+4) + ((T+j)^2)⁻¹/(T+4) := by
      dsimp [g]
      have hj : (j : ℝ) ≤ T + j := by linarith
      have hL := log_add_le_log_add_div (B := T+4) (j := (j:ℝ)) (by positivity) (by positivity)
      calc
        _ ≤ ((T+j)^3)⁻¹ * (Real.log (T+4) + (T+j)/(T+4)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [div_le_div_of_nonneg_right hj (show 0 ≤ T+4 by positivity)]
        _ = _ := by field_simp
    refine (sum_le_sum hg).trans ?_
    rw [sum_add_distrib, ← sum_mul, ← sum_div]
    dsimp [W]
    gcongr
    · exact Real.log_nonneg (by linarith)
    · exact sum_inv_pow_three_le hT0 N
    · exact sum_inv_pow_two_le hT0 N
  let lo := s.filter (fun ρ => γ ρ ≤ 0)
  let hi := s.filter (fun ρ => ¬ γ ρ ≤ 0)
  have hl (ρ : ι) (hρ : ρ ∈ lo) : γ ρ < -T := by
    obtain ⟨hρs, hn⟩ := mem_filter.mp hρ
    have h := hs ρ hρs
    rw [abs_of_nonpos hn] at h
    linarith
  have hh (ρ : ι) (hρ : ρ ∈ hi) : T < γ ρ := by
    obtain ⟨hρs, hn⟩ := mem_filter.mp hρ
    simpa [abs_of_pos (lt_of_not_ge hn)] using hs ρ hρs
  have L : ∑ ρ ∈ lo, (m ρ : ℝ) * ((|γ ρ|) ^ 3)⁻¹ ≤ A * W := by
    apply side lo (fun ρ => ⌊-γ ρ-T⌋₊)
    · intro ρ hρ
      have H := Nat.floor_le (show 0 ≤ -γ ρ-T by linarith [hl ρ hρ])
      rw [abs_of_neg (show γ ρ < 0 by linarith [hl ρ hρ])]
      linarith
    · intro j
      refine (hN.window (-T-j-1) _ ?_).trans ?_
      · intro ρ hρ
        obtain ⟨hv, hq⟩ := mem_filter.mp hρ
        have H := (Nat.floor_eq_iff (show 0 ≤ -γ ρ-T by linarith [hl ρ hv])).mp hq
        constructor <;> linarith [H.1, H.2]
      · have He : |-T-(j:ℝ)-1|+3 = T+4+j := by
          rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) j])]
          ring
        rw [He]
  have R : ∑ ρ ∈ hi, (m ρ : ℝ) * ((|γ ρ|) ^ 3)⁻¹ ≤ A * W := by
    have hc1 (ρ : ι) (hρ : ρ ∈ hi) : 1 ≤ ⌈γ ρ-T⌉₊ :=
      Nat.one_le_ceil_iff.mpr (by linarith [hh ρ hρ])
    apply side hi (fun ρ => ⌈γ ρ-T⌉₊-1)
    · intro ρ hρ
      rw [Nat.cast_sub (hc1 ρ hρ), Nat.cast_one, abs_of_pos (hT0.trans (hh ρ hρ))]
      have H := Nat.ceil_lt_add_one (show 0 ≤ γ ρ-T by linarith [hh ρ hρ])
      linarith
    · intro j
      refine (hN.window (T+j) _ ?_).trans ?_
      · intro ρ hρ
        obtain ⟨hv, hq⟩ := mem_filter.mp hρ
        have hc : ⌈γ ρ-T⌉₊ = j+1 := by have := hc1 ρ hv; omega
        have H := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
        push_cast at H
        constructor <;> linarith [H.1, H.2]
      · apply mul_le_mul_of_nonneg_left _ hA
        rw [abs_of_nonneg (by positivity)]
        apply Real.log_le_log (by positivity)
        linarith
  rw [← sum_filter_add_sum_filter_not s (fun ρ => γ ρ ≤ 0)]
  calc
    _ ≤ A * W + A * W := add_le_add L R
    _ = _ := by dsimp [W]; ring
/-- The multiplicity count used in the generic bound really does hold for the
canonical zeta zeros, unconditionally. -/
theorem canonical_local_count :
    ∃ A : ℝ, LocalCount (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im)
      (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.mult ρ) A := by
  obtain ⟨A, hA, hloc⟩ := RvM.zetaZeroConfig_local_count
  refine ⟨A, hA, ?_⟩
  intro t s hs
  classical
  refine le_trans ?_ (hloc t)
  have hfin : (zetaZeroConfig.window t (t+1)).Finite := zetaZeroConfig.finite_window t (t+1)
  unfold ZeroConfig.N
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    rw [Set.Finite.mem_toFinset]
    exact ⟨ρ.2, hs ρ hρ⟩
  have h := Finset.sum_le_sum_of_subset (f := zetaZeroConfig.mult) hsub
  rw [Finset.sum_map] at h
  exact_mod_cast h

/-- A cubic bound for an individual summand gives absolute summability and
the quantitative error for the entire omitted tail, not only finite subsums. -/
theorem omitted_tail {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A T K : ℝ}
    (hN : LocalCount γ m A) (hT : 2 ≤ T) (hK : 0 ≤ K)
    (f : ι → ℂ) (hf : ∀ i, T < |γ i| → ‖f i‖ ≤ K * ((|γ i|)^3)⁻¹) :
    let G := fun x : {i : ι // T < |γ i|} => (m x.1 : ℂ) * f x.1
    Summable (fun x => ‖G x‖) ∧
      ‖∑' x, G x‖ ≤ K * (2 * A * (((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (T+4)
        + ((T^2)⁻¹+T⁻¹)/(T+4))) := by
  dsimp only
  set G := fun x : {i : ι // T < |γ i|} => (m x.1 : ℂ) * f x.1
  set W := 2 * A * (((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (T+4)+((T^2)⁻¹+T⁻¹)/(T+4))
  have hpartial (u : Finset {i : ι // T < |γ i|}) : ∑ x ∈ u, ‖G x‖ ≤ K * W := by
    classical
    let s : Finset ι := u.map (Function.Embedding.subtype _)
    have hmem (i : ι) (hi : i ∈ s) : T < |γ i| := by
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hi
      exact x.2
    calc
      _ ≤ ∑ x ∈ u, K * ((m x.1 : ℝ)*((|γ x.1|)^3)⁻¹) := by
        apply sum_le_sum
        intro x _
        rw [norm_mul, Complex.norm_natCast]
        calc
          _ ≤ (m x.1 : ℝ) * (K * ((|γ x.1|)^3)⁻¹) :=
            mul_le_mul_of_nonneg_left (hf _ x.2) (Nat.cast_nonneg _)
          _ = _ := by ring
      _ = K * ∑ i ∈ s, (m i : ℝ)*((|γ i|)^3)⁻¹ := by
        rw [← mul_sum, Finset.sum_map]; rfl
      _ ≤ K * W := mul_le_mul_of_nonneg_left (finite_weighted_tail hN hT s hmem) hK
  exact ⟨summable_of_sum_le (fun _ => norm_nonneg _) hpartial,
    (norm_tsum_le_tsum_norm (summable_of_sum_le (fun _ => norm_nonneg _) hpartial)).trans
      (Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hpartial)⟩

/-- A twice continuously differentiable bump gives two inverse powers
from its Laplace transform, and the signed interval factor gives the third. -/
theorem signed_kernel_cubic {g : ℝ → ℝ} {δ x y : ℝ}
    (hδ : 0 ≤ δ) (hx : 1 ≤ x) (hxy : x ≤ y)
    (hg : ContDiff ℝ 2 g) (hgs : ∀ u, g u ≠ 0 → |u| ≤ δ)
    {s : ℂ} (hβ0 : 0 ≤ s.re) (hβ1 : s.re ≤ 1) (hγ : 0 < |s.im|) :
    ‖(∫ v : ℝ, (g v:ℂ) * Complex.exp ((v:ℂ)*s)) *
      (((y:ℂ)^s-(x:ℂ)^s)/s)‖ ≤
      (Real.exp δ * (∫ v, ‖deriv (deriv (fun u : ℝ => (g u : ℂ))) v‖) * (x+y)) *
        ((|s.im|)^3)⁻¹ := by
  let f : ℝ → ℂ := fun u => g u
  let z : ℂ := -Complex.I * s
  let C := Real.exp δ * ∫ v, ‖deriv (deriv f) v‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hf : ContDiff ℝ 2 f := Complex.ofRealCLM.contDiff.comp hg
  have hfs (u : ℝ) (hu : f u ≠ 0) : |u| ≤ δ := hgs _ (by simpa [f] using hu)
  have hnorm : ‖z‖ = ‖s‖ := by simp [z]
  have hzpos : 0 < ‖z‖ := by rw [hnorm]; exact hγ.trans_le (Complex.abs_im_le_norm s)
  have hz : z ≠ 0 := norm_pos_iff.mp hzpos
  have him : z.im = -s.re := by simp [z, Complex.mul_im]
  have himabs : |z.im| ≤ 1 := by rw [him, abs_neg, abs_of_nonneg hβ0]; exact hβ1
  have hE : Real.exp (|z.im| * δ) ≤ Real.exp δ :=
    Real.exp_le_exp.mpr (by simpa using mul_le_mul_of_nonneg_right himabs hδ)
  have hG : (∫ v : ℝ, (g v:ℂ) * Complex.exp ((v:ℂ)*s)) = paperFT f z := by
    unfold paperFT
    apply integral_congr_ae
    filter_upwards [] with v
    change (g v:ℂ) * Complex.exp ((v:ℂ)*s) = (g v:ℂ) * Complex.exp (Complex.I*z*(v:ℂ))
    have he : Complex.I * z = s := by rw [show Complex.I * z = -(Complex.I*Complex.I)*s by dsimp [z]; ring, ← pow_two, Complex.I_sq]; ring
    rw [he, mul_comm s (v:ℂ)]
  have hA : ‖paperFT f z‖ ≤ C * ((|s.im|)^2)⁻¹ := by
    refine (norm_paperFT_le_div hf hfs hz).trans ?_
    rw [hnorm]
    calc
      _ ≤ C / ‖s‖^2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hE (by positivity)
      _ ≤ C / |s.im|^2 := by gcongr; exact Complex.abs_im_le_norm s
      _ = _ := by rw [div_eq_mul_inv]
  have hy : 1 ≤ y := hx.trans hxy
  have hpow (v : ℝ) (hv : 1 ≤ v) : ‖(v:ℂ)^s‖ ≤ v := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hv)]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hv hβ1
  have hB : ‖((y:ℂ)^s-(x:ℂ)^s)/s‖ ≤ (x+y) * |s.im|⁻¹ := by
    rw [norm_div]
    have hdiff : ‖(y:ℂ)^s - (x:ℂ)^s‖ ≤ x+y := by
      rw [add_comm x y]
      exact (norm_sub_le _ _).trans (add_le_add (hpow y hy) (hpow x hx))
    calc
      _ ≤ (x+y)/‖s‖ := div_le_div_of_nonneg_right hdiff (by positivity)
      _ ≤ (x+y)/|s.im| := by gcongr; exact Complex.abs_im_le_norm s
      _ = _ := by rw [div_eq_mul_inv]
  rw [hG, norm_mul]
  calc
    _ ≤ (C * ((|s.im|)^2)⁻¹) * ((x+y) * |s.im|⁻¹) :=
      mul_le_mul hA hB (norm_nonneg _) (by positivity)
    _ = _ := by
      dsimp [C, f]
      rw [← inv_pow, ← inv_pow]
      ring

private theorem finite_low_ordinates (T : ℝ) :
    {ρ : zetaZeroConfig.carrier | |(ρ:ℂ).im| ≤ T}.Finite := by
  have hfin := (zetaZeroConfig.finite_window (-T-1) T).preimage_embedding
    (Function.Embedding.subtype (· ∈ zetaZeroConfig.carrier))
  refine hfin.subset ?_
  intro ρ hρ
  have h := abs_le.mp (show |(ρ:ℂ).im| ≤ T from hρ)
  refine ⟨ρ.2, ?_, h.2⟩
  change -T-1 < (ρ:ℂ).im
  linarith [h.1]

/-- The actual canonical ζ formula with only finitely many zeros of height
at most T retained. Its error is from omitting the high zeros, not from
removing the smoothing or discarding the Γ term. -/
theorem zeta_signed_kernel_truncated :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {g : ℝ → ℝ} {δ x y T : ℝ},
      0 ≤ δ → 1 ≤ x → x ≤ y → δ < Real.log x → 2 ≤ T →
      ContDiff ℝ 2 g → (∀ v ≤ -δ, g v = 0) → (∀ v ≥ δ, g v = 0) →
      (∫ v in (-δ)..δ, g v) = 1 →
      let Z := zetaZeroConfig
      let k := PintzWeilTestWindow.test g δ (Real.log x) (Real.log y)
      let G := fun s : ℂ => ∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*s)
      let low := (finite_low_ordinates T).toFinset
      let term := fun ρ : Z.carrier =>
        (Z.mult ρ : ℂ) * (G ρ * (((y:ℂ)^(ρ:ℂ)-(x:ℂ)^(ρ:ℂ))/(ρ:ℂ)))
      let rhs := paperFT k (Complex.I/2) + paperFT k (-Complex.I/2) -
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          (PintzWeilTestWindow.diff g δ (Real.log x) (Real.log y) (Real.log n):ℂ)) +
        (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r:ℂ)
      let K := Real.exp δ * (∫ v, ‖deriv (deriv (fun u : ℝ => (g u : ℂ))) v‖) * (x+y)
      ‖rhs - (∑ ρ ∈ low, term ρ)‖ ≤
        K * (2 * A * (((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (T+4)+((T^2)⁻¹+T⁻¹)/(T+4))) := by
  obtain ⟨A,hA⟩ := canonical_local_count
  refine ⟨A,hA.one_le,?_⟩
  intro g δ x y T hδ hx hxy ha hT hg hl hr hm
  dsimp only
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  let Z := zetaZeroConfig
  let k := PintzWeilTestWindow.test g δ (Real.log x) (Real.log y)
  let low := (finite_low_ordinates T).toFinset
  let f (ρ : Z.carrier) :=
    (∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*(ρ:ℂ))) *
      (((y:ℂ)^(ρ:ℂ)-(x:ℂ)^(ρ:ℂ))/(ρ:ℂ))
  let term (ρ : Z.carrier) := (Z.mult ρ : ℂ) * f ρ
  have hterm (ρ : Z.carrier) : paperFT k (gammaOf ρ) = f ρ := by
    have hz : IsNontrivialZero (ρ:ℂ) := ρ.2
    exact PintzWeilZetaWindow.evaluated_test _ (Complex.ne_zero_of_re_pos hz.2.1)
      hδ hx0 hxy ha hg1 hl hr hm
  obtain ⟨hc,hcs,_⟩ := PintzWeilTestWindow.admissible hδ ha (Real.log_le_log hx0 hxy) hg1 hl hr hm
  have hs : Summable term := by
    simpa only [hterm] using (WeilEF.EF_lit_zetaZeroConfig k hc hcs).1
  have hmain := PintzWeilZetaWindow.zeta_signed_kernel_identity hδ hx0 hxy ha hg1 hl hr hm
  dsimp only at hmain
  have hsplit := hs.sum_add_tsum_subtype_compl low
  have he := calc
    (∑' ρ : Z.carrier, term ρ) - ∑ ρ ∈ low, term ρ =
        (∑ ρ ∈ low, term ρ) + (∑' ρ : {q // q ∉ low}, term ρ) - ∑ ρ ∈ low, term ρ := by rw [hsplit]
    _ = (∑' ρ : {q // q ∉ low}, term ρ) := add_sub_cancel_left _ _
  rw [← hmain]
  change ‖(∑' ρ : Z.carrier, term ρ) - ∑ ρ ∈ low, term ρ‖ ≤ _
  rw [he]
  have hlow (ρ : Z.carrier) : ρ ∉ low ↔ T < |(ρ:ℂ).im| := by
    change ρ ∉ (finite_low_ordinates T).toFinset ↔ T < |(ρ:ℂ).im|
    have hi : ρ ∈ (finite_low_ordinates T).toFinset ↔ |(ρ:ℂ).im| ≤ T :=
      (finite_low_ordinates T).mem_toFinset
    exact (not_congr hi).trans not_le
  let e : {ρ : Z.carrier // ρ ∉ low} ≃ {ρ : Z.carrier // T < |(ρ:ℂ).im|} :=
    Equiv.subtypeEquivRight hlow
  have htsum :
      (∑' ρ : {q // q ∉ low}, term ρ) = ∑' ρ : {q : Z.carrier // T < |(q:ℂ).im|}, term ρ :=
    e.tsum_eq (fun ρ => term ρ)
  rw [htsum]
  refine (omitted_tail (K := Real.exp δ * (∫ v, ‖deriv (deriv (fun u : ℝ => (g u : ℂ))) v‖) * (x+y)) hA hT ?_ f ?_).2
  · exact mul_nonneg (mul_nonneg (Real.exp_pos δ).le (integral_nonneg (fun _ => norm_nonneg _)))
      (by linarith)
  · intro ρ hρ
    have hz : IsNontrivialZero (ρ:ℂ) := ρ.2
    refine signed_kernel_cubic hδ hx hxy hg ?_ hz.2.1.le hz.2.2.le (by linarith)
    intro v hv
    exact abs_le.mpr ⟨lt_of_not_ge (fun H => hv (hl v H)) |>.le,
      lt_of_not_ge (fun H => hv (hr v H)) |>.le⟩

/-- Combined adapter: the prime sum is now sharp and the zero sum is finite.
The pole and Γ terms remain evaluated on the smooth test, and the finite
zero terms still have the bump multiplier; these are not silently replaced. -/
theorem zeta_sharp_prime_finite_zeros :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {g : ℝ → ℝ} {δ x y T : ℝ},
      0 ≤ δ → δ ≤ 1 → 1 ≤ x → x ≤ y → δ < Real.log x → 2 ≤ T →
      ContDiff ℝ 2 g → (∀ v, 0 ≤ g v) →
      (∀ v ≤ -δ, g v = 0) → (∀ v ≥ δ, g v = 0) →
      (∫ v in (-δ)..δ, g v) = 1 →
      let Z := zetaZeroConfig
      let k := PintzWeilTestWindow.test g δ (Real.log x) (Real.log y)
      let G := fun s : ℂ => ∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*s)
      let low := (finite_low_ordinates T).toFinset
      let term := fun ρ : Z.carrier =>
        (Z.mult ρ : ℂ) * (G ρ * (((y:ℂ)^(ρ:ℂ)-(x:ℂ)^(ρ:ℂ))/(ρ:ℂ)))
      let rhs := paperFT k (Complex.I/2) + paperFT k (-Complex.I/2) -
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          (PintzWeilPrimeDesmoothing.sharp x y n : ℂ)) +
        (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r:ℂ)
      let K := Real.exp δ * (∫ v, ‖deriv (deriv (fun u : ℝ => (g u : ℂ))) v‖) * (x+y)
      ‖rhs - (∑ ρ ∈ low, term ρ)‖ ≤
        K * (2 * A * (((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (T+4)+((T^2)⁻¹+T⁻¹)/(T+4))) +
          (3*δ*(x+y)+2)*Real.log (y*Real.exp δ) := by
  obtain ⟨A,hA,htr⟩ := zeta_signed_kernel_truncated
  refine ⟨A,hA,?_⟩
  intro g δ x y T hδ hδ₁ hx hxy ha hT hg hn hl hr hm
  dsimp only
  let k := PintzWeilTestWindow.test g δ (Real.log x) (Real.log y)
  let P := paperFT k (Complex.I/2) + paperFT k (-Complex.I/2)
  let H := (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r:ℂ)
  let sm (n : ℕ) := ArithmeticFunction.vonMangoldt n *
    PintzWeilTestWindow.diff g δ (Real.log x) (Real.log y) (Real.log n)
  let sh (n : ℕ) := ArithmeticFunction.vonMangoldt n * PintzWeilPrimeDesmoothing.sharp x y n
  let S : ℂ := ∑ ρ ∈ (finite_low_ordinates T).toFinset, (zetaZeroConfig.mult ρ : ℂ) *
    ((∫ v : ℝ, (g v:ℂ)*Complex.exp ((v:ℂ)*(ρ:ℂ))) * (((y:ℂ)^(ρ:ℂ)-(x:ℂ)^(ρ:ℂ))/(ρ:ℂ)))
  let Sc : ℂ := (∑' n, sm n : ℝ)
  let Pc : ℂ := (∑' n, sh n : ℝ)
  let K := Real.exp δ * (∫ v, ‖deriv (deriv (fun u : ℝ => (g u : ℂ))) v‖) * (x+y)
  let E := K * (2 * A * (((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (T+4)+((T^2)⁻¹+T⁻¹)/(T+4)))
  let D := (3*δ*(x+y)+2)*Real.log (y*Real.exp δ)
  have h1 : ‖P - Sc + H - S‖ ≤ E := by
    dsimp only [Sc, sm]
    simp only [Complex.ofReal_tsum, Complex.ofReal_mul]
    exact htr hδ hx hxy ha hT hg hl hr hm
  have h2 : ‖Sc-Pc‖ ≤ D := by
    dsimp only [Sc, Pc]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact PintzWeilPrimeDesmoothing.desmooth_prime_window hδ hδ₁ hx hxy hg.continuous hn hl hr hm
  have he : ‖P-Pc+H-S‖ ≤ E + D := by
    rw [show P-Pc+H-S = (P-Sc+H-S)+(Sc-Pc) by ring]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  simpa only [Pc, sh, Complex.ofReal_tsum, Complex.ofReal_mul] using he

#print axioms finite_weighted_tail
#print axioms canonical_local_count
#print axioms omitted_tail
#print axioms signed_kernel_cubic
#print axioms zeta_signed_kernel_truncated
#print axioms zeta_sharp_prime_finite_zeros
end PintzWeilZetaTruncation
