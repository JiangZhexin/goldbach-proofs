import PintzResidualWindow
import PintzWindowBlockEnergy
import PintzFiniteCatalogueEnergy

open Finset MeasureTheory PintzDiscreteZeroModel

namespace PintzResidualGallagher

noncomputable def zeroPrimitive {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ)
    (m : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, (m i:ℂ)*c i*((t:ℂ)^(ρ i)/(ρ i))

theorem model_eq {ι : Type*} (S : Finset ι) (ρ c : ι → ℂ) (m : ι → ℝ)
    (a b Y x : ℝ) :
    let F := zeroPrimitive S ρ c m
    PintzWindowBlockEnergy.model S ρ c m a b Y x =
      Y⁻¹ • (if max a x ≤ min b (x+Y) then F (min b (x+Y)) - F (max a x) else 0) := by
  dsimp only [PintzWindowBlockEnergy.model,zeroPrimitive]
  rw [max_comm x a,min_comm (x+Y) b]
  split_ifs with hh
  · congr 1
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    simp only [div_eq_mul_inv]
    ring
  · rfl

/-- Gallagher reduction with the discrete retained model already subtracted.
Only the pointwise explicit-formula error and the sum of clipped block
energies enter. This is the per-character analytic interface of §8. -/
theorem estimate {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (label : ι → κ) (ρ c : ι → ℂ) (m : ι → ℝ)
    (p : ℕ → ℂ) (K : ℝ → ℂ)
    {a b Y E R : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hY : 0 < Y)
    (hE : 0 ≤ E) (hR : 0 ≤ R)
    (hK : ∀ t, 1 ≤ t → ‖K t - K (⌊t⌋₊:ℕ)‖ ≤ R)
    (hformula : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      ‖(∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, p n) - (K v-K u) +
        (zeroPrimitive S ρ c m v - zeroPrimitive S ρ c m u)‖ ≤ E) :
    (∫ η in (-1/(2*Y))..(1/(2*Y)),
      ‖∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (p n-increment K n) *
        Complex.exp ((2*Real.pi*η*Complex.I)*(n:ℝ))‖^2) ≤
    (Real.pi^2/2)*(((S.image label).card:ℝ) *
        (∑ k ∈ S.image label, ∫ x : ℝ,
          ‖PintzWindowBlockEnergy.model (S.filter (fun i => label i=k)) ρ c m a b Y x‖^2)
        +(b-(a-Y))*((E+2*R)/Y)^2) := by
  let Z := PintzFiniteCatalogueEnergy.signedEndpointModel S ρ c m a b Y
  let B := Ioc ⌊a⌋₊ ⌊b⌋₊
  let w (n : ℕ) := p n - increment K n
  let W (x : ℝ) := ∑ n ∈ B.filter (fun n : ℕ => x < (n:ℝ) ∧ (n:ℝ) ≤ x+Y), w n
  let e (x : ℝ) := -(Y⁻¹ • W x + Z x)
  have hZ (x) : Z x = PintzWindowBlockEnergy.model S ρ c m a b Y x := by
    symm
    exact PintzWindowBlockEnergy.model_as_primitive S ρ c m hab hY x
  have he (x) : ‖e x‖ ≤ (E+2*R)/Y := by
    have H := PintzResidualWindow.estimate (p := p) (K := K)
      (F := zeroPrimitive S ρ c m) (x := x) (Y := Y) ha hE hR hK hformula
    dsimp only at H
    dsimp only [e]
    rw [norm_neg,hZ,model_eq,← smul_add,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hY.le),div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hY.le)
  have hes (x) (hx : x ∉ Set.Icc (a-Y) b) : e x = 0 := by
    have hzx : ¬ (a < x+Y ∧ x < b) := fun hz => hx ⟨by linarith [hz.1],hz.2.le⟩
    have hW : W x = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      obtain ⟨hn,hng,hnl⟩ := mem_filter.mp hn
      obtain ⟨hla,hnb⟩ := mem_Ioc.mp hn
      have hna : a < (n:ℝ) := (Nat.floor_lt (by linarith : 0 ≤ a)).mp hla
      have hbn : (n:ℝ) ≤ b := (Nat.le_floor_iff (by linarith : 0 ≤ b)).mp hnb
      exact False.elim (hzx ⟨hna.trans_le hnl,hng.trans_le hbn⟩)
    simp [e, Z, PintzFiniteCatalogueEnergy.signedEndpointModel,hW,hzx]
  have herr : 0 ≤ (E+2*R)/Y := by positivity
  have Hel := PintzFiniteCatalogueEnergy.signed_endpoint_energy_with_error
    S label ρ c m ha hab hY.le herr e he hes
  have hM (k : κ) (x : ℝ) :
      PintzFiniteCatalogueEnergy.signedEndpointModel (S.filter (fun i => label i=k)) ρ c m a b Y x =
        PintzWindowBlockEnergy.model (S.filter (fun i => label i=k)) ρ c m a b Y x :=
    (PintzWindowBlockEnergy.model_as_primitive _ ρ c m hab hY x).symm
  have hX (x) : Z x + e x = -(Y⁻¹ • W x) := by dsimp [e]; abel
  change (∫ x : ℝ, ‖Z x+e x‖^2) ≤ _ at Hel
  simp_rw [hX,norm_neg,hM] at Hel
  have hg := PintzGallagherReal.pintz_window B (fun n : ℕ => (n:ℝ)) w
    (D := 2*Y) (by positivity)
  have hsc : (∫ x : ℝ, ‖Y⁻¹ • W x‖^2) = (Y⁻¹)^2 * ∫ x : ℝ, ‖W x‖^2 := by
    simp_rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hY.le),
      mul_pow, integral_const_mul]
  have hhg : (∫ η in (-1/(2*Y))..(1/(2*Y)),
      ‖∑ n ∈ B, w n*Complex.exp ((2*Real.pi*η*Complex.I)*(n:ℝ))‖^2) ≤
        (Real.pi^2/4)*∫ x : ℝ, ‖Y⁻¹ • W x‖^2 := by
    rw [hsc]
    rw [show (2*Y)/2=Y by ring] at hg
    have hnorm : (Real.pi^2/4)*(Y⁻¹)^2 = Real.pi^2/(2*Y)^2 := by
      field_simp [hY.ne'] <;> ring
    rw [← mul_assoc,hnorm]
    exact hg
  apply hhg.trans
  refine (mul_le_mul_of_nonneg_left Hel (by positivity)).trans_eq ?_
  ring

#print axioms estimate
end PintzResidualGallagher
