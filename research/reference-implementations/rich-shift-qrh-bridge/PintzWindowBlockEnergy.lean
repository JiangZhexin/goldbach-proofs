import PintzFixedWindowHigh
import PintzFixedWindowEnergy

open MeasureTheory Finset

namespace PintzWindowBlockEnergy

/-- Canonical fixed clipped zero model with the same normalization as
the Gallagher short interval. -/
noncomputable def model {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ) (m : ι → ℝ)
    (a b Y x : ℝ) : ℂ :=
  Y⁻¹ • (if max x a ≤ min (x+Y) b then
    ∑ i ∈ S, (m i:ℂ) * c i *
      (((min (x+Y) b:ℝ):ℂ)^(ρ i) - ((max x a:ℝ):ℂ)^(ρ i))/(ρ i)
    else 0)

theorem model_as_primitive {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ) (m : ι → ℝ)
    {a b Y : ℝ} (hab : a ≤ b) (hY : 0 < Y) (x : ℝ) :
    let f (t : ℝ) := ∑ i ∈ S, (m i:ℂ)*c i*(t:ℂ)^(ρ i)/((Y:ℂ)*ρ i)
    model S ρ c m a b Y x =
      if a < x+Y ∧ x < b then f (min (x+Y) b)-f (max x a) else 0 := by
  dsimp only [model]
  have hEq : ((Y⁻¹:ℝ):ℂ) * (∑ i ∈ S, (m i:ℂ)*c i *
      (((min (x+Y) b:ℝ):ℂ)^(ρ i)-((max x a:ℝ):ℂ)^(ρ i))/(ρ i)) =
      (∑ i ∈ S, (m i:ℂ)*c i*((min (x+Y) b:ℝ):ℂ)^(ρ i)/((Y:ℂ)*ρ i)) -
        (∑ i ∈ S, (m i:ℂ)*c i*((max x a:ℝ):ℂ)^(ρ i)/((Y:ℂ)*ρ i)) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    simp only [Complex.ofReal_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  have hclip : a ≤ x+Y ∧ x ≤ b ↔ max x a ≤ min (x+Y) b := by
    rw [le_min_iff,max_le_iff,max_le_iff]
    constructor
    · intro h
      exact ⟨⟨by linarith,h.1⟩,⟨h.2,hab⟩⟩
    · exact fun h => ⟨h.1.2,h.2.1⟩
  by_cases h : a < x+Y ∧ x < b
  · rw [if_pos h, if_pos (hclip.mp ⟨h.1.le,h.2.le⟩), Complex.real_smul]
    exact hEq
  rw [if_neg h]
  split_ifs with h'
  · obtain ⟨h₁,h₂⟩ := hclip.mpr h'
    have he : min (x+Y) b = max x a := by
      apply le_antisymm _ h'
      by_cases h'₁ : a < x+Y
      · have h'₂ : b ≤ x := le_of_not_gt (fun h'₂ => h ⟨h'₁,h'₂⟩)
        exact (min_le_right _ _).trans (h'₂.trans (le_max_left _ _))
      · exact (min_le_left _ _).trans ((le_of_not_gt h'₁).trans (le_max_right _ _))
    simp [he]
  · simp

private theorem uniform_log {N T : ℝ} (hN : 1 ≤ N) (hT : 0 ≤ T) (hTN : T ≤ N) :
    1+Real.log (2*T+1) ≤ (2+Real.log 3)*(1+Real.log N) := by
  have h := Real.log_le_log (show 0 < 2*T+1 by linarith) (show 2*T+1 ≤ 3*N by linarith)
  rw [Real.log_mul (by norm_num) (by linarith)] at h
  have hL := Real.log_nonneg hN
  have h3 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
  nlinarith only [h,hL,h3,mul_nonneg h3 hL]

private theorem sum_budget {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ) (m : ι → ℝ)
    {N h K : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hc : ∀ i ∈ S, ‖c i‖ ≤ K)
    (hβ : ∀ i ∈ S, (ρ i).re ≤ 1-h) :
    (∑ i ∈ S, m i*(‖c i‖*N^((ρ i).re-1))^2) ≤
      K^2*N^(-2*h)*(∑ i ∈ S,m i) := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have hp := Real.rpow_le_rpow_of_exponent_le hN (show (ρ i).re-1 ≤ -h by linarith [hβ i hi])
  have hprod := mul_le_mul (hc i hi) hp (by positivity) hK
  have hs := pow_le_pow_left₀ (show 0 ≤ ‖c i‖*N^((ρ i).re-1) by positivity) hprod 2
  calc
    _ ≤ m i*(K*N^(-h))^2 := mul_le_mul_of_nonneg_left hs (hm i hi)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast (N^(-h)) 2, ← Real.rpow_mul (show 0 ≤ N by linarith)]
      push_cast
      rw [show -h*(2:ℝ) = -2*h by ring]
      ring

/-- A single high block: the window energy is the density weight times
N/M, up to an explicit local counting constant and two logarithms. -/
theorem high {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ) (m : ι → ℝ)
    {a b N Y M T C K h : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ N)
    (hY : 0 < Y) (hYN : Y ≤ N) (hM : 1 ≤ M) (hT : 0 ≤ T)
    (hTN : T ≤ N) (hTupper : T ≤ 2*(M*N/Y)) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hc : ∀ i ∈ S, ‖c i‖ ≤ K)
    (hβ₀ : ∀ i ∈ S, 0 ≤ (ρ i).re) (hβ : ∀ i ∈ S, (ρ i).re ≤ 1-h)
    (hγ : ∀ i ∈ S, M*N/Y ≤ |(ρ i).im|) (hx : ∀ i ∈ S, |(ρ i).im| ≤ T)
    (hlocal : ∀ t : ℝ, |t| ≤ T+1/2 →
      (∑ i ∈ S.filter (fun i => |(ρ i).im-t| ≤ 1/2), m i) ≤ C) :
    (∫ x : ℝ, ‖model S ρ c m a b Y x‖^2) ≤
      ((32*(2+Real.log 3)+20)*C*K^2)*(1+Real.log N)^2 *
        (N * M⁻¹ * N^(-2*h) * (∑ i ∈ S,m i)) := by
  have hN : 1 ≤ N := ha.trans (hab.trans hb)
  have hL : 1 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  let L := 1+Real.log N
  let D := 2+Real.log 3
  have hD : 0 ≤ D := by dsimp [D]; linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]
  have hb0 : 0 ≤ 1+Real.log (2*T+1) := by
    linarith [Real.log_nonneg (show 1 ≤ 2*T+1 by linarith)]
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  have hb' := uniform_log hN hT hTN
  have hU := sum_budget S ρ c m hN hK hm hc hβ
  have hA : 0 ≤ ∑ i ∈ S, m i*(‖c i‖*N^((ρ i).re-1))^2 :=
    sum_nonneg fun i hi => mul_nonneg (hm i hi) (sq_nonneg _)
  have h0 := PintzFixedWindowHigh.high_zero_window_energy_normalized S ρ c m
    ha hab hb hY hYN hM hT hTupper hC hm hβ₀ hγ hx hlocal
  simp_rw [model_as_primitive S ρ c m hab hY]
  dsimp only at h0
  apply h0.trans
  have hCoef : 4*(4*(1+Real.log N))*(2*C*(1+Real.log (2*T+1)))+20*C ≤
      (32*D+20)*C*L^2 := by
    have hd := mul_le_mul_of_nonneg_left hb' (show 0 ≤ 32*C*L by positivity)
    have he := mul_le_mul_of_nonneg_left hL2 (show 0 ≤ 20*C by positivity)
    change _ ≤ (32*D+20)*C*L^2
    dsimp only [D,L] at hd he ⊢
    linarith only [hd,he]
  calc
    _ ≤ ((32*D+20)*C*L^2)*(N/M)*(K^2*N^(-2*h)*(∑ i ∈ S,m i)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hCoef (by positivity)) hU hA (by positivity)
    _ = _ := by dsimp [D,L]; rw [div_eq_mul_inv]; ring

-- The first height bin uses the moving-average estimate and has M=1.
theorem low {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ) (m : ι → ℝ)
    {a b N Y T C K h : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ N)
    (hY : 0 < Y) (hT : 0 ≤ T) (hTN : T ≤ N) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hc : ∀ i ∈ S, ‖c i‖ ≤ K)
    (hβ₀ : ∀ i ∈ S, 1/2 ≤ (ρ i).re) (hβ : ∀ i ∈ S, (ρ i).re ≤ 1-h)
    (hx : ∀ i ∈ S, |(ρ i).im| ≤ T)
    (hlocal : ∀ t : ℝ, |t| ≤ T+1/2 →
      (∑ i ∈ S.filter (fun i => |(ρ i).im-t| ≤ 1/2), m i) ≤ C) :
    (∫ x : ℝ, ‖model S ρ c m a b Y x‖^2) ≤
      ((32*(2+Real.log 3)+20)*C*K^2)*(1+Real.log N)^2 *
        (N * N^(-2*h) * (∑ i ∈ S,m i)) := by
  have hN : 1 ≤ N := ha.trans (hab.trans hb)
  have hN0 : 0 < N := by linarith
  let L := 1+Real.log N
  let D := 2+Real.log 3
  have hL : 0 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN]
  have hD : 0 ≤ D := by dsimp [D]; linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]
  have hU := sum_budget S ρ c m hN hK hm hc hβ
  have hcoef : 4*L*(2*C*(1+Real.log (2*T+1))) ≤ (32*D+20)*C*L^2 := by
    have hl := mul_le_mul_of_nonneg_left (uniform_log hN hT hTN) (show 0 ≤ 8*C*L by positivity)
    have h0 : 0 ≤ (24*D+20)*C*L^2 := by positivity
    nlinarith only [hl,h0]
  have hEq : (∑ i ∈ S, m i*(‖c i‖*N^((ρ i).re-1/2))^2) =
      N*(∑ i ∈ S, m i*(‖c i‖*N^((ρ i).re-1))^2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    have H : N^((ρ i).re-1/2) = N^((ρ i).re-1)*N^(1/2:ℝ) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    simp only [H, mul_pow]
    rw [← Real.rpow_natCast (N^(1/2:ℝ)) 2, ← Real.rpow_mul hN0.le]
    norm_num
    ring
  have hU₀ : 0 ≤ ∑ i ∈ S, m i*(‖c i‖*N^((ρ i).re-1))^2 :=
    sum_nonneg fun i hi => mul_nonneg (hm i hi) (sq_nonneg _)
  have h0 := PintzFixedWindowEnergy.clipped_zero_energy S ρ c m ha hab hb hY hT hC hm hβ₀ hx hlocal
  change (∫ x : ℝ, ‖model S ρ c m a b Y x‖^2) ≤ _ at h0
  rw [hEq] at h0
  calc
    _ ≤ _ := h0
    _ ≤ ((32*D+20)*C*L^2)*(N*(K^2*N^(-2*h)*(∑ i ∈ S,m i))) :=
      mul_le_mul hcoef (mul_le_mul_of_nonneg_left hU hN0.le)
        (mul_nonneg hN0.le hU₀) (by positivity)
    _ = _ := by dsimp [D,L]; ring

#print axioms model_as_primitive
#print axioms high
#print axioms low
end PintzWindowBlockEnergy
