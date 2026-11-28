import PintzConditionalPoleOnly
import RichShiftSection8Coefficient263
import RichShiftMajorReduction263
import RichShiftDensityGroup263

open Finset Filter PintzMajorArcGeometry PintzPoleKernelTail
open PintzConditionalPoleOnly
namespace RichShiftPoleAssembly263

private theorem pow_unbounded {u : ℝ} (hu : 0 < u) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K ≤ (n:ℝ)^u :=
  ((tendsto_rpow_atTop hu).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)).eventually_ge_atTop K

private theorem absorb_error (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, C*(n:ℝ)^(1-1/8200:ℝ)*(1+Real.log (n:ℝ))^2 ≤ (n:ℝ)/16 := by
  let u : ℝ := 1/16400
  have hu : 0 < u := by norm_num [u]
  have H₀ : ∀ᶠ x : ℝ in atTop, ‖(Real.log x)^(2:ℝ)‖ ≤ 1*‖x^u‖ :=
    (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s := u) hu).bound (by norm_num : (0:ℝ)<1)
  have H := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually H₀
  have Hl := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  filter_upwards [H,Hl.eventually_ge_atTop (1:ℝ),pow_unbounded hu (64*C),
    eventually_ge_atTop (2:ℕ)] with n H hlog H' hn
  change 1 ≤ Real.log (n:ℝ) at hlog
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hL : (Real.log (n:ℝ))^2 ≤ (n:ℝ)^u := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0.le u),
      abs_of_nonneg (Real.rpow_nonneg (show 0 ≤ Real.log (n:ℝ) by linarith) (2:ℝ)),
      Real.rpow_ofNat] using H
  have hp : (1+Real.log (n:ℝ))^2 ≤ 4*((n:ℝ)^u) := by
    have H := pow_le_pow_left₀ (show 0 ≤ 1+Real.log (n:ℝ) by linarith)
      (show 1+Real.log (n:ℝ) ≤ 2*Real.log (n:ℝ) by linarith) 2
    nlinarith
  calc
    _ ≤ C*(n:ℝ)^(1-1/8200:ℝ)*(4*((n:ℝ)^u)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 4*C*(n:ℝ)^(1-u) := by
      rw [show (1-1/8200:ℝ)=1-u-u by norm_num [u]]
      rw [show C*(n:ℝ)^(1-u-u)*(4*(n:ℝ)^u) = 4*C*((n:ℝ)^(1-u-u)*(n:ℝ)^u) by ring]
      rw [← Real.rpow_add hn0,sub_add_cancel]
    _ = ((4*C)*(n:ℝ))/((n:ℝ)^u) := by rw [Real.rpow_sub hn0,Real.rpow_one,mul_div_assoc]
    _ ≤ _ := (div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)).2 (by
      have HH := mul_le_mul_of_nonneg_left H' hn0.le
      linarith)

private theorem arcs_separated {P : ℕ} {N : ℝ} (hN : 8 ≤ N)
    (hcut : (P:ℝ) ≤ N^(263/1000:ℝ)) : 2*(P:ℝ)^2 < N := by
  have hN1 : 1 < N := by linarith
  have hN0 : 0 < N := by linarith
  have hP : (P:ℝ)^2 ≤ N^(526/1000:ℝ) := by
    calc
      _ ≤ (N^(263/1000:ℝ))^2 := pow_le_pow_left₀ (by positivity) hcut 2
      _ = _ := by rw [← Real.rpow_mul_natCast hN0.le]; norm_num
  have hs : 2 ≤ N^(1/3:ℝ) := by
    calc
      _ = (8:ℝ)^(1/3:ℝ) := by
        rw [show (8:ℝ)=2^3 by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hN (by norm_num)
  have ht : (2:ℝ) < N^(474/1000:ℝ) := hs.trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num))
  calc
    _ ≤ 2*N^(526/1000:ℝ) := mul_le_mul_of_nonneg_left hP (by norm_num)
    _ < N^(474/1000:ℝ)*N^(526/1000:ℝ) := mul_lt_mul_of_pos_right ht (by positivity)
    _ = _ := by rw [← Real.rpow_add hN0]; norm_num

theorem major_floor (hGap : Gap) (hMB : RichShiftSection8Bound263.MassBound) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ X : ℕ in atTop,
      ∃ (P : ℕ) (a : ℝ), 1 ≤ P ∧ P ≤ 2*X ∧ ⌊a⌋₊ ≤ 2*X ∧
        2*(P:ℝ)^2 < ((2*X:ℕ):ℝ) ∧ ((2*X:ℕ):ℝ)^(263/1000:ℝ) ≤ 2*(P:ℝ) ∧
        ∀ m ∈ Finset.Icc X (2*X), Even m →
          2*κ*((2*X:ℕ):ℝ) ≤ (PintzExceptionFinalReduction.majorCoeff (2*X) P a m).re := by
  refine ⟨1/32, by norm_num, ?_⟩
  obtain ⟨C,hC,Hsec⟩ := RichShiftSection8Coefficient263.coefficient_eventual hMB
    (show (0:ℝ)<1/100 by norm_num) (show (1/100:ℝ)≤1/2 by norm_num)
  have hPows : Tendsto (fun X : ℕ => 2*X) atTop atTop :=
    tendsto_atTop_mono (fun X => by change X ≤ 2*X; omega) tendsto_id
  filter_upwards [hPows.eventually Hsec,
    hPows.eventually (PintzPolePolynomialFloor.polynomial_pole_floor (θ := 1/4) (by norm_num)),
    hPows.eventually (absorb_error C hC),
    hPows.eventually (pow_unbounded (show (0:ℝ)<13/1000 by norm_num) 2),
    hPows.eventually (pow_unbounded (show (0:ℝ)<737/1000 by norm_num) 12),
    hPows.eventually (eventually_ge_atTop (48:ℕ))] with X H F hE hpower hA hN
  let N : ℕ := 2*X
  let p : ℝ := (N:ℝ)^(263/1000:ℝ)
  let P : ℕ := ⌊p⌋₊
  let a : ℝ := (N:ℝ)/12
  have hN48 : (48:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hNp : N > 0 := by exact_mod_cast hN0
  have hp : 0 ≤ p := by positivity
  have hpN : p ≤ (N:ℝ) := by
    simpa only [p,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
      (show (263/1000:ℝ)≤1 by norm_num)
  have hp2 : 2 ≤ p := by
    refine hpower.trans ?_
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (13/1000:ℝ)≤263/1000)
  have hPcut : (P:ℝ) ≤ p := Nat.floor_le hp
  have hPlt : p < (P:ℝ)+1 := Nat.lt_floor_add_one p
  have hP2 : 2 ≤ P := Nat.le_floor (by exact_mod_cast hp2)
  have hPlow : p ≤ 2*(P:ℝ) := by linarith
  have hLow : (N:ℝ)^(263/1000:ℝ) ≤ 2*(P:ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (263/1000:ℝ)≤263/1000)).trans hPlow
  have hPθ : (N:ℝ)^(1/4:ℝ) ≤ P := by
    have hc : 2*(N:ℝ)^(1/4:ℝ) ≤ p := by
      unfold p
      rw [show (263/1000:ℝ)=13/1000+1/4 by norm_num,Real.rpow_add hN0]
      exact mul_le_mul_of_nonneg_right hpower (by positivity)
    linarith
  have hpa : p ≤ a := by
    change p ≤ (N:ℝ)/12
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<12)).2
    have h1 : (N:ℝ)^(737/1000:ℝ)*p = (N:ℝ) := by
      unfold p
      rw [← Real.rpow_add hN0,show (737/1000:ℝ)+263/1000=1 by norm_num,Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_right hA hp]
  have hpa' : (P:ℝ) ≤ a := hPcut.trans hpa
  have ha2 : 2 ≤ a := by dsimp [a]; linarith
  have haN : a ≤ N := by dsimp [a]; linarith
  have hP1 : 1 ≤ P := by omega
  have hP_N : 2*P ≤ N := by
    have H : 2*(P:ℝ) ≤ N := by dsimp [a] at hpa'; linarith
    exact_mod_cast H
  let L := ⌊a⌋₊+1
  let Len := N-⌊a⌋₊
  have hFloor : (⌊a⌋₊:ℝ) ≤ a := Nat.floor_le (by linarith)
  have hflN : ⌊a⌋₊ ≤ N := by exact_mod_cast hFloor.trans haN
  have hSep := arcs_separated (show (8:ℝ)≤N by linarith) (show (P:ℝ)≤(N:ℝ)^(263/1000:ℝ) from hPcut)
  refine ⟨P,a,hP1,by omega,hflN,hSep,hLow,?_⟩
  intro m hm hmEven
  obtain ⟨hml,hmN⟩ := Finset.mem_Icc.mp hm
  have hmHalf : (N:ℝ)/2 ≤ m := by
    have H : (N:ℝ) ≤ 2*(m:ℝ) := by
      exact_mod_cast (show N ≤ 2*m by dsimp [N]; omega)
    linarith
  have hLm : 2*L ≤ m := by
    have Hr : 2*(L:ℝ) ≤ m := by
      unfold L
      push_cast
      dsimp [a] at hFloor
      linarith
    exact_mod_cast Hr
  have hKN : m-2*L < Len := by dsimp [Len,L] at *; omega
  have hk : N ≤ 4*(m-2*L+1) := by
    have Hr : (N:ℝ) ≤ 4*((m:ℝ)-2*(L:ℝ)+1) := by
      unfold L
      push_cast
      dsimp [a] at hFloor
      linarith
    have Hr' : (N:ℝ) ≤ 4*((m-2*L+1:ℕ):ℝ) := by
      rw [Nat.cast_add,Nat.cast_sub hLm,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      push_cast; simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using Hr
    exact_mod_cast Hr'
  have hFloorPole := F P L Len m hP2 hP_N hPθ (by omega) hmN hmEven hLm hKN hk
  let B (i : ℕ×ℕ) (u : ℝ) := phase (-(m:ℝ)*(u+PintzMajorArcGeometry.center i))
  have Hbound := H P a N hP1 hPcut hpa' ha2 haN le_rfl B
    (fun i _ => by unfold B phase; fun_prop) (fun i _ u => by unfold B; rw [norm_phase])
  change ‖(∑ i ∈ reduced P, ∫ x in -(radius P N i)..radius P N i,
    (PintzSection8LiteralModels.full a N (x+PintzMajorArcGeometry.center i))^2*
        phase (-(m:ℝ)*(x+PintzMajorArcGeometry.center i))) -
      (∑ i ∈ reduced P, ∫ x in -(radius P N i)..radius P N i,
       (PintzReducedArcEnergy.slice (PintzSection8LiteralModels.retained N a N (1/100)) i x)^2*
        phase (-(m:ℝ)*(x+PintzMajorArcGeometry.center i)))‖ ≤ _ at Hbound
  rw [← major_translated N P a m hNp hSep,
    retained_translated_eq_pole hGap N P a m hflN] at Hbound
  have Herr : ‖PintzExceptionFinalReduction.majorCoeff N P a m - weightedPole P N L Len m‖ ≤
      (N:ℝ)/16 := Hbound.trans (by norm_num [N] at hE ⊢; exact hE)
  have Hre := (Complex.abs_re_le_norm _).trans Herr
  rw [Complex.sub_re] at Hre
  have hh := (abs_le.mp Hre).1
  linarith [hFloorPole]

#print axioms major_floor
theorem frozen_of_density_and_gap
    (hGap : Gap) (hDensity : RichShiftDensityGroup263.DensityBound) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
      ∀ e ∈ Finset.Icc 1 (Nat.log 2 X/2),
        (((Finset.Ico X (2*X)).filter (fun n => Even n ∧
          (((Finset.Icc 2 (n-2^e)).filter
            (fun p => Nat.Prime p ∧ Nat.Prime ((n-2^e)-p))).card:ℝ)
            < c*(X:ℝ)/Real.log (X:ℝ)^2)).card : ℝ)
          ≤ C*(X:ℝ) ^ (37/50:ℝ)  :=
  RichShift263.frozen_target_of_major (major_floor hGap (RichShiftDensityGroup263.global_mass hDensity))

#print axioms frozen_of_density_and_gap
end RichShiftPoleAssembly263
