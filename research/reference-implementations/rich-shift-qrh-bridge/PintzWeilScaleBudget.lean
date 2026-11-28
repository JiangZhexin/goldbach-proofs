import PintzWeilBump
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory
namespace PintzWeilScaleBudget

noncomputable def delta (N : ℝ) : ℝ := N^(-(1/3:ℝ))

theorem delta_pos {N : ℝ} (hN : 0 < N) : 0 < delta N := Real.rpow_pos_of_pos hN _
theorem delta_le_one {N : ℝ} (hN : 1 ≤ N) : delta N ≤ 1 := by
  simpa [delta] using Real.rpow_le_rpow_of_exponent_le hN (show -(1/3:ℝ) ≤ 0 by norm_num)

private theorem sqrt_le_self {N : ℝ} (hN : 1 ≤ N) : Real.sqrt N ≤ N := by
  rw [Real.sqrt_eq_rpow]
  simpa using Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1/2:ℝ) ≤ 1)

private theorem log_aux {N q : ℝ} (hN : 4 ≤ N) (hq : 1 ≤ q) (hqN : q ≤ N) :
    Real.log (q*(Real.sqrt N+4)) ≤ 3*(1+Real.log N) := by
  have hNp : 0 < N := by linarith
  have hqpos : 0 < q := by linarith
  have hs := sqrt_le_self (show 1 ≤ N by linarith)
  have h₂ : q*(Real.sqrt N+4) ≤ 2*N^2 := by
    have H := mul_le_mul hqN (show Real.sqrt N+4 ≤ 2*N by linarith) (by positivity) hNp.le
    nlinarith only [H]
  have H := Real.log_le_log (by positivity : 0 < q*(Real.sqrt N+4)) h₂
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hNp.ne'),Real.log_pow] at H
  have hL := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
  have hn := Real.log_nonneg (show 1 ≤ N by linarith)
  norm_num at H hL
  linarith

/-- Uniform in the conductor q; q=1 is the Riemann zeta case. -/
theorem tail_bracket {N q : ℝ} (hN : 4 ≤ N) (hq : 1 ≤ q) (hqN : q ≤ N) :
    let T := Real.sqrt N
    ((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (q*(T+4))+((T^2)⁻¹+T⁻¹)/(T+4) ≤
      5*(1+Real.log N)/N := by
  dsimp only
  let T := Real.sqrt N
  change ((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (q*(T+4))+((T^2)⁻¹+T⁻¹)/(T+4) ≤ _
  have hT : 2 ≤ T := by
    change 2 ≤ Real.sqrt N
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := by linarith
  have hTsq : T^2 = N := Real.sq_sqrt hNp.le
  have hlogL := log_aux hN hq hqN
  change Real.log (q*(T+4)) ≤ _ at hlogL
  have hqpos : 0 < q := by linarith
  have hlog : 0 ≤ Real.log (q*(T+4)) :=
    Real.log_nonneg ((show (1:ℝ)*1 ≤ q*(T+4) by gcongr; linarith).trans_eq' (by norm_num))
  have h₁ : (T^3)⁻¹+(T^2)⁻¹/2 ≤ 1/N := by
    rw [show T^3 = T^2*T by ring, hTsq, mul_inv]
    have hi : T⁻¹ ≤ 1/2 := by
      rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num]
      exact inv_anti₀ (by norm_num) hT
    simp only [one_div]
    nlinarith only [mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hNp.le)]
  have h₂ : ((T^2)⁻¹+T⁻¹)/(T+4) ≤ 2/N := by
    rw [hTsq]
    have ht : 0 < T+4 := by positivity
    apply (div_le_iff₀ ht).2
    rw [show 2/N*(T+4) = 2*(T+4)/N by ring]
    apply (le_div_iff₀ hNp).2
    rw [show (N⁻¹ + T⁻¹)*N = 1+T by
      rw [← hTsq]; field_simp [hTp.ne'], mul_comm (2:ℝ)]
    linarith
  have hln := Real.log_nonneg (show 1 ≤ N by linarith)
  have HH := mul_le_mul h₁ hlogL hlog (by positivity : 0 ≤ 1/N)
  apply (le_div_iff₀ hNp).2
  have hm := mul_le_mul_of_nonneg_right (add_le_add HH h₂) hNp.le
  have he : (1/N*(3*(1+Real.log N))+2/N)*N = 3*(1+Real.log N)+2 := by
    field_simp [hNp.ne']
  rw [he] at hm
  nlinarith only [hm,hln]

/-- Endpoint desmoothing error at radius N^(-1/3). -/
theorem endpoint_budget {N x y : ℝ} (hN : 4 ≤ N) (hx : 1 ≤ x)
    (hxy : x ≤ y) (hyN : y ≤ N) :
    (3*delta N*(x+y)+2)*Real.log (y*Real.exp (delta N)) ≤
      8*N^(2/3:ℝ)*(1+Real.log N) := by
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hy : 0 < y := by linarith
  have hδ := delta_pos hNp
  have hδ₁ := delta_le_one hN1
  have hp : 0 ≤ 3*delta N*(x+y)+2 := by positivity
  have hlog : Real.log (y*Real.exp (delta N)) ≤ 1+Real.log N := by
    rw [Real.log_mul hy.ne' (Real.exp_pos _).ne',Real.log_exp]
    linarith [Real.log_le_log hy hyN]
  have hlog0 : 0 ≤ Real.log (y*Real.exp (delta N)) := by
    rw [Real.log_mul hy.ne' (Real.exp_pos _).ne',Real.log_exp]
    linarith [Real.log_nonneg (hx.trans hxy)]
  have hδN : delta N*N = N^(2/3:ℝ) := by
    unfold delta
    rw [show (N^(-(1/3:ℝ)))*N = (N^(-(1/3:ℝ)))*N^(1:ℝ) by rw [Real.rpow_one], ← Real.rpow_add hNp]
    congr 1
    ring
  have hpow : 1 ≤ N^(2/3:ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 (show (0:ℝ) ≤ 2/3 by norm_num)
  apply mul_le_mul _ hlog hlog0 (by positivity)
  nlinarith only [mul_le_mul_of_nonneg_left (show x+y ≤ 2*N by linarith) (show 0 ≤ 3*delta N by positivity),hδN,hpow]

#print axioms tail_bracket
#print axioms endpoint_budget

/-- Full tail expression with scaled second-derivative bound. This is
uniform for ζ and every conductor q≤N. -/
theorem tail_budget {N q A K D x y : ℝ}
    (hN : 4 ≤ N) (hq : 1 ≤ q) (hqN : q ≤ N) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hD₀ : 0 ≤ D) (hD : D ≤ K/(delta N)^2)
    (hxy₀ : 0 ≤ x+y) (hxy : x+y ≤ 2*N) :
    let T := Real.sqrt N
    Real.exp (delta N)*D*(x+y) *
      (2*A*(((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (q*(T+4))+((T^2)⁻¹+T⁻¹)/(T+4)))
      ≤ (20*Real.exp 1*A*K)*N^(2/3:ℝ)*(1+Real.log N) := by
  dsimp only
  let T := Real.sqrt N
  let W := ((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (q*(T+4))+((T^2)⁻¹+T⁻¹)/(T+4)
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hδ := delta_pos hNp
  have hL : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN1]
  have hδpow : ((delta N)^2)⁻¹ = N^(2/3:ℝ) := by
    unfold delta
    rw [← Real.rpow_mul_natCast hNp.le, ← Real.rpow_neg hNp.le]
    push_cast
    congr 1
    ring
  have hE := Real.exp_le_exp.mpr (delta_le_one hN1)
  have hD' : D ≤ K*N^(2/3:ℝ) := by simpa [div_eq_mul_inv,hδpow] using hD
  have hX : Real.exp (delta N)*D*(x+y) ≤ Real.exp 1*(K*N^(2/3:ℝ))*(2*N) := by
    have H := mul_le_mul hE hD' hD₀ (Real.exp_pos _).le
    exact mul_le_mul H hxy hxy₀ (by positivity)
  have hXp : 0 ≤ Real.exp (delta N)*D*(x+y) := by positivity
  have hW : W ≤ 5*(1+Real.log N)/N := tail_bracket hN hq hqN
  have hWp : 0 ≤ 5*(1+Real.log N)/N := by positivity
  change Real.exp (delta N)*D*(x+y)*(2*A*W) ≤ _
  calc
    _ ≤ Real.exp (delta N)*D*(x+y)*(2*A*(5*(1+Real.log N)/N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW (by positivity)) hXp
    _ ≤ (Real.exp 1*(K*N^(2/3:ℝ))*(2*N))*(2*A*(5*(1+Real.log N)/N)) :=
      mul_le_mul_of_nonneg_right hX (mul_nonneg (by positivity) hWp)
    _ = _ := by field_simp [hNp.ne']; ring

theorem tail_plus_endpoint_budget {N q A K D x y : ℝ}
    (hN : 4 ≤ N) (hq : 1 ≤ q) (hqN : q ≤ N) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hD₀ : 0 ≤ D) (hD : D ≤ K/(delta N)^2)
    (hx : 1 ≤ x) (hxy : x ≤ y) (hyN : y ≤ N) :
    let T := Real.sqrt N
    Real.exp (delta N)*D*(x+y) *
      (2*A*(((T^3)⁻¹+(T^2)⁻¹/2)*Real.log (q*(T+4))+((T^2)⁻¹+T⁻¹)/(T+4))) +
      (3*delta N*(x+y)+2)*Real.log (y*Real.exp (delta N))
      ≤ (20*Real.exp 1*A*K+8)*N^(2/3:ℝ)*(1+Real.log N) := by
  dsimp only
  have H := tail_budget (x := x) (y := y) hN hq hqN hA hK hD₀ hD (by linarith) (by linarith)
  have E := endpoint_budget hN hx hxy hyN
  refine (add_le_add H E).trans_eq ?_
  ring

#print axioms tail_budget
#print axioms tail_plus_endpoint_budget
end PintzWeilScaleBudget
