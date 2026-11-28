import PintzPrimitiveResidualEnergy
import PintzFiniteDyadicAggregation
import PintzHeightBins

open Finset PintzWeilPrimitivePrimeWindow PintzPrimitiveResidual

namespace PintzResidualLabels

noncomputable def index (N P r : ℝ) (z : ℂ) : ℕ × ℕ :=
  (PintzHeightBins.idx (2*P/r) z.im, ⌈(1-z.re)*Real.log N⌉₊)

noncomputable def edge (N : ℝ) (ν : ℕ) : ℝ :=
  min (1/2) (ν/Real.log N)

theorem horizontal {N b : ℝ} (hN : 1 < N) (hb : 0 ≤ b) {z : ℂ}
    (hre : 1/2 ≤ z.re) (hhi : z.re ≤ 1-b) (P r : ℝ) :
    let ν := (index N P r z).2
    let h := edge N ν
    ν ≤ ⌈Real.log N/2⌉₊ ∧ b ≤ h ∧ h ≤ 1/2 ∧
      h - 1/Real.log N ≤ 1-z.re ∧ 1-z.re ≤ h := by
  dsimp only [index,edge]
  let L := Real.log N
  let δ := 1-z.re
  let ν := ⌈δ*L⌉₊
  let h := min (1/2:ℝ) ((ν:ℝ)/L)
  have hL : 0 < L := Real.log_pos hN
  have hδ1 : δ ≤ 1/2 := by dsimp [δ]; linarith
  have hδb : b ≤ δ := by dsimp [δ]; linarith
  have hd : 0 ≤ δ*L := mul_nonneg (hb.trans hδb) hL.le
  have hlo : δ*L ≤ (ν:ℝ) := Nat.le_ceil _
  have hhi : (ν:ℝ) < δ*L+1 := Nat.ceil_lt_add_one hd
  have huu : δ ≤ (ν:ℝ)/L := (le_div_iff₀ hL).mpr hlo
  have hu : δ ≤ h := le_min hδ1 huu
  have hl : (ν:ℝ)/L - 1/L ≤ δ := by
    rw [← sub_div]
    exact (div_le_iff₀ hL).mpr (by linarith)
  change ν ≤ ⌈L/2⌉₊ ∧ b ≤ h ∧ h ≤ 1/2 ∧ h - 1/L ≤ δ ∧ δ ≤ h
  refine ⟨Nat.ceil_mono (by nlinarith only [mul_le_mul_of_nonneg_right hδ1 hL.le]),
    hδb.trans hu, min_le_left _ _, (sub_le_sub_right (min_le_right _ _) _).trans hl, hu⟩

theorem log_ge_one {N : ℝ} (hN : 4 ≤ N) : 1 ≤ Real.log N := by
  have h := Real.log_le_log (show 0 < (4:ℝ) by norm_num) hN
  rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow] at h
  norm_num at h
  linarith [Real.log_two_gt_d9]

/-- Each actual occupied label lies in the product of the standard finite
height/horizontal ranges. No artificial empty bands are counted here. -/
theorem label_range {N P r b : ℝ} (hN : 4 ≤ N) (hr : 0 < r) (hrP : r ≤ P)
    (hb : 0 ≤ b) {z : ℂ} (hβ₀ : 1/2 ≤ z.re) (hβ₁ : z.re ≤ 1-b)
    (hγ : |z.im| ≤ Real.sqrt N) :
    index N P r z ∈
      (range (Nat.log 2 ⌊N⌋₊+1)).product (range (⌈Real.log N/2⌉₊+1)) := by
  have hH : 1 ≤ 2*P/r := (le_div_iff₀ hr).2 (by linarith)
  have hS : 1 ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hSN : Real.sqrt N ≤ N := by
    have H := Real.sq_sqrt (show 0 ≤ N by linarith)
    nlinarith
  have hB := PintzHeightBins.bounds hH hS hγ
  dsimp only at hB
  have hpow : (2:ℝ)^(index N P r z).1 ≤ N := hB.2.1.trans hSN
  have hf : (2:ℕ)^(index N P r z).1 ≤ ⌊N⌋₊ := by
    apply Nat.le_floor
    exact_mod_cast hpow
  have hμ := Nat.le_log_of_pow_le (by decide : 1 < (2:ℕ)) hf
  have hν := (horizontal (by linarith : 1 < N) hb hβ₀ hβ₁ P r).1
  exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hμ),
    mem_range.mpr (Nat.lt_succ_of_le hν)⟩

theorem card_bound {ι : Type*} (S : Finset ι) (z : ι → ℂ) {N P r b : ℝ}
    (hN : 4 ≤ N) (hr : 0 < r) (hrP : r ≤ P) (hb : 0 ≤ b)
    (hz : ∀ i ∈ S, 1/2 ≤ (z i).re ∧ (z i).re ≤ 1-b ∧ |(z i).im| ≤ Real.sqrt N) :
    ((S.image (fun i => index N P r (z i))).card:ℝ) ≤
      ((1/Real.log 2+1)*(5/2:ℝ))*(1+Real.log N)^2 := by
  let A := range (Nat.log 2 ⌊N⌋₊+1)
  let B := range (⌈Real.log N/2⌉₊+1)
  have hAB : S.image (fun i => index N P r (z i)) ⊆ A.product B := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    obtain ⟨hr1,hr2,hγ⟩ := hz i hi
    exact label_range hN hr hrP hb hr1 hr2 hγ
  have hL := log_ge_one hN
  have hf : 0 < ⌊N⌋₊ := by
    have h : (1:ℕ) ≤ ⌊N⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  have hB : (B.card:ℝ) ≤ (5/2:ℝ)*Real.log N :=
    PintzFiniteDyadicAggregation.horizontal_range_count hL
  have hA : (A.card:ℝ) ≤ (1/Real.log 2+1)*Real.log N := by
    have hh : (2:ℝ)^(Nat.log 2 ⌊N⌋₊) ≤ N := by
      have h := Nat.pow_log_le_self 2 hf.ne'
      exact (by exact_mod_cast h : (2:ℝ)^(Nat.log 2 ⌊N⌋₊) ≤ (⌊N⌋₊:ℝ)).trans
        (Nat.floor_le (by linarith))
    have hlog := Real.log_le_log (by positivity) hh
    rw [Real.log_pow] at hlog
    have h₂ := Real.log_pos (by norm_num : (1:ℝ) < 2)
    have hh' := (le_div_iff₀ h₂).mpr hlog
    simp only [A,card_range,Nat.cast_add,Nat.cast_one]
    rw [add_mul,one_mul,div_mul_eq_mul_div,one_mul]
    linarith
  have hC : 0 ≤ 1/Real.log 2+1 := by positivity
  calc
    _ ≤ ((A.product B).card:ℝ) := by exact_mod_cast card_le_card hAB
    _ = (A.card:ℝ)*(B.card:ℝ) := by simp
    _ ≤ ((1/Real.log 2+1)*Real.log N)*((5/2:ℝ)*Real.log N) :=
      mul_le_mul hA hB (by positivity) (by positivity [show 0 ≤ Real.log N by linarith])
    _ ≤ _ := by
      have hLL : (Real.log N)^2 ≤ (1+Real.log N)^2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h := mul_le_mul_of_nonneg_left hLL (mul_nonneg hC (by norm_num : (0:ℝ) ≤ 5/2))
      convert h using 1 <;> ring

#print axioms horizontal
#print axioms label_range
#print axioms card_bound
end PintzResidualLabels
