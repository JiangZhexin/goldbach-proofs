import PintzResidualLabels
import PintzPrimitiveCatalogueLocal

open Finset MeasureTheory Zeta23 PintzWeilPrimitivePrimeWindow PintzPrimitiveResidual

namespace PintzPrimitiveDensityEnergy

/-- The Fourier scale attached to the primitive conductor. -/
noncomputable def width (N P r : ℝ) := r*N/(2*P)

theorem width_pos {N P r : ℝ} (hN : 0 < N) (hr : 0 < r) (hrP : r ≤ P) :
    0 < width N P r := by
  have hP := hr.trans_le hrP
  unfold width
  positivity

theorem width_le {N P r : ℝ} (hN : 0 ≤ N) (hr : 0 < r) (hrP : r ≤ P) :
    width N P r ≤ N := by
  have hP := hr.trans_le hrP
  unfold width
  apply (div_le_iff₀ (by positivity)).2
  nlinarith only [mul_le_mul_of_nonneg_right hrP hN,mul_nonneg hP.le hN]

theorem width_ratio {N P r : ℝ} (hN : 0 < N) (hr : 0 < r) (hrP : r ≤ P) :
    N/width N P r = 2*P/r := by
  have hP := hr.trans_le hrP
  unfold width
  field_simp [hN.ne',hr.ne',hP.ne']

theorem far_spec {Z : ZeroConfig} {N b : ℝ} (i : Z.carrier) (hi : i ∈ farCatalogue Z N b) :
    1/2 < (i:ℂ).re ∧ (i:ℂ).re ≤ 1-b ∧ |(i:ℂ).im| ≤ Real.sqrt N := by
  have H := (PintzResidualPartition.mem_far (trunc Z N) (fun z => (z:ℂ)) b i).1 hi
  exact ⟨H.2.1,H.2.2,(Set.Finite.mem_toFinset _).1 H.1⟩

/-- Uniform single occupied block estimate. Its output multiplicity
weight is exactly the weight from the verified finite density theorem,
with only three additional logarithms. -/
theorem occupied_block {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    {N P a v b : ℝ} (hN : 4 ≤ N) (hqP : (q:ℝ) ≤ P) (hqN : (q:ℝ) ≤ N)
    (ha : 2 ≤ a) (hav : a ≤ v) (hv : v ≤ N) (hb : 0 ≤ b)
    (k : ℕ×ℕ) :
    let Z := zeroConfig hp
    let S := (farCatalogue Z N b).filter (fun i : Z.carrier => PintzResidualLabels.index N P q (i:ℂ)=k)
    let Y := width N P q
    let M := (2:ℝ)^k.1
    let h := PintzResidualLabels.edge N k.2
    let D := (32*(2+Real.log 3)+20) *
      (18/Real.log (55/52)+11/Real.log (12/11)) * (Real.exp 1)^2 * Real.exp 2
    (∫ x : ℝ, ‖PintzWindowBlockEnergy.model S (fun i => (i:ℂ))
      (fun i => weight N i) (fun i => (Z.mult i:ℝ)) a v Y x‖^2) ≤
      D*(1+Real.log N)^3*(N*M⁻¹*N^(-2*h)*(∑ i ∈ S,(Z.mult i:ℝ))) := by
  dsimp only
  let Z := zeroConfig hp
  let S := (farCatalogue Z N b).filter (fun i : Z.carrier => PintzResidualLabels.index N P q (i:ℂ)=k)
  let Y := width N P q
  let M := (2:ℝ)^k.1
  let h := PintzResidualLabels.edge N k.2
  let L := 1+Real.log N
  let D₁ := 32*(2+Real.log 3)+20
  let D₂ := 18/Real.log (55/52)+11/Real.log (12/11)
  let K := Real.exp 1
  let d := h-1/Real.log N
  let H := 2*P/(q:ℝ)
  let T := min (Real.sqrt N) (2*M*H)
  let C := PintzLowRealBlock.actualC q T
  let w (i : Z.carrier) := (Z.mult i:ℝ)
  let c (i : Z.carrier) := weight N i
  have hn0 : 0 < N := by linarith
  have hn1 : 1 ≤ N := by linarith
  have hL : 0 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hn1]
  have hq0 : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hP0 := hq0.trans_le hqP
  have hY : 0 < Y := width_pos hn0 hq0 hqP
  have hYN : Y ≤ N := width_le hn0.le hq0 hqP
  have hHY : N/Y = H := width_ratio hn0 hq0 hqP
  have hH : 1 ≤ H := by dsimp [H]; apply (le_div_iff₀ hq0).2; linarith
  have hk1 : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hM : 0 ≤ M := zero_le_one.trans hk1
  have ht0 : 0 ≤ T := by dsimp [T]; exact le_min (by positivity) (by positivity)
  have htN : T ≤ N := (min_le_left _ _).trans (by
    have hh := Real.sq_sqrt hn0.le
    nlinarith)
  have htQ : T ≤ 2*(M*N/Y) := by
    refine (min_le_right _ _).trans_eq ?_
    rw [mul_div_assoc,hHY]
    ring
  have hS1 : 1 ≤ Real.sqrt N := by rw [Real.le_sqrt (by norm_num) hn0.le]; linarith
  have hS (i) (hi : i ∈ S) := (mem_filter.mp hi)
  have hf (i) (hi : i ∈ S) := far_spec i (hS i hi).1
  have hγ (i) (hi : i ∈ S) : |(i:ℂ).im| ≤ T := by
    have hh := PintzHeightBins.bounds hH hS1 (hf i hi).2.2
    dsimp only at hh
    have e : PintzHeightBins.idx H (i:ℂ).im = k.1 := congrArg Prod.fst (hS i hi).2
    rw [e] at hh
    exact le_min (hf i hi).2.2 hh.2.2.1.le
  have hγhigh (i) (hi : i ∈ S) (hk : k.1 ≠ 0) : M*N/Y ≤ |(i:ℂ).im| := by
    have hh := PintzHeightBins.bounds hH hS1 (hf i hi).2.2
    dsimp only at hh
    have e : PintzHeightBins.idx H (i:ℂ).im = k.1 := congrArg Prod.fst (hS i hi).2
    rw [e] at hh
    rw [mul_div_assoc,hHY]
    exact hh.2.2.2 hk
  have hβ (i) (hi : i ∈ S) : (i:ℂ).re ≤ 1-d := by
    obtain ⟨hlo,hup,_⟩ := hf i hi
    have H := PintzResidualLabels.horizontal (by linarith : 1 < N) hb hlo.le hup P q
    dsimp only at H
    rw [show (PintzResidualLabels.index N P q (i:ℂ)).2 = k.2 from congrArg Prod.snd (hS i hi).2] at H
    dsimp [d,h]
    linarith [H.2.2.2.1]
  have hC : 0 ≤ C := by
    unfold C PintzLowRealBlock.actualC
    apply le_max_of_le_right
    exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg T])) (Real.log_nonneg (by norm_num))
  have hD : 0 ≤ D₂ := by
    dsimp [D₂]
    exact add_nonneg (div_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
      (div_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
  have hC' : C ≤ D₂*L :=
    (PintzLowRealBlock.actualC_log_bound (by linarith) (NeZero.pos q)
      (hqN.trans (by linarith)) ht0 htN).trans (by dsimp [L]; nlinarith only [hD])
  let e : Z.carrier ↪ ℂ := Function.Embedding.subtype _
  have hlocal (t : ℝ) (ht : |t| ≤ T+1/2) :
      (∑ i ∈ S.filter (fun i : Z.carrier => |(i:ℂ).im-t| ≤ 1/2), w i) ≤ C := by
    have H₀ := PintzPrimitiveCatalogueLocal.local_count_real hp (Q := q) (le_refl q) ht0 (S.map e)
      (fun z hz => by
        obtain ⟨i,hi,rfl⟩ := mem_map.mp hz
        exact ⟨i.2,(hf i hi).1.le⟩) t ht
    rw [filter_map, sum_map] at H₀
    exact H₀
  have hc (i) (hi : i ∈ S) : ‖c i‖ ≤ K := weight_bound hn1 (Z.strip i i.2).1 (Z.strip i i.2).2
  have hw (i) (hi : i ∈ S) : 0 ≤ w i := by dsimp [w]; positivity
  have hEnergy :
      (∫ x : ℝ, ‖PintzWindowBlockEnergy.model S (fun i => (i:ℂ)) c w a v Y x‖^2) ≤
        (D₁*C*K^2)*L^2*(N*M⁻¹*N^(-2*d)*(∑ i ∈ S,w i)) := by
    by_cases hk : k.1 = 0
    · have hM1 : M = 1 := by simp [M,hk]
      rw [hM1, inv_one, mul_one]
      exact PintzWindowBlockEnergy.low S _ _ _ (by linarith) hav hv hY ht0 htN hC
        (by dsimp [K]; positivity) hw hc (fun i hi => (hf i hi).1.le) hβ hγ hlocal
    · exact PintzWindowBlockEnergy.high S _ _ _ (by linarith) hav hv hY hYN hk1 ht0 htN htQ hC
        (by dsimp [K]; positivity) hw hc (fun i _ => (Z.strip i i.2).1) hβ
        (fun i hi => hγhigh i hi hk) hγ hlocal
  refine hEnergy.trans ?_
  have hD₁ : 0 ≤ D₁ := by dsimp [D₁]; positivity [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hW : 0 ≤ ∑ i ∈ S,w i := sum_nonneg hw
  have hHpow := PintzFiniteDyadicAggregation.horizontal_loss (show 1 < N by linarith) (δ := d) (h := h) le_rfl
  calc
    _ ≤ (D₁*(D₂*L)*K^2)*L^2*(N*M⁻¹*(Real.exp 2*N^(-2*h))*(∑ i ∈ S,w i)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC' hD₁) (sq_nonneg _)) (sq_nonneg _)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHpow (by positivity)) hW
      · positivity
      · positivity
    _ = _ := by dsimp only [D₁,D₂,K,L]; ring

#print axioms occupied_block
end PintzPrimitiveDensityEnergy
