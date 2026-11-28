import PintzMajorArcGeometry

noncomputable section
open Set MeasureTheory PintzMajorArcGeometry
namespace PintzMinorArcTransport

def published (N P : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ P ∧ a ≤ q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ (P:ℝ)/((q:ℝ)*N)}

def localUnion (N P : ℕ) : Set ℝ :=
  ⋃ i ∈ reduced P, arc P N i

def starts (N P : ℕ) : Set ℝ :=
  (fun i => center i - radius P N i) '' (↑(reduced P) : Set (ℕ × ℕ))

theorem published_meas (N P : ℕ) : MeasurableSet (published N P) := by
  have hE : published N P =
      ⋃ q : ℕ, ⋃ a : ℕ, {t : ℝ | 1 ≤ q ∧ q ≤ P ∧ a ≤ q ∧ a.Coprime q ∧
        |t-(a:ℝ)/q| ≤ (P:ℝ)/((q:ℝ)*N)} := by
    ext t
    simp only [published, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hE]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a =>
    show MeasurableSet ({t : ℝ | 1 ≤ q ∧ q ≤ P ∧ a ≤ q ∧ a.Coprime q ∧
      |t-(a:ℝ)/q| ≤ (P:ℝ)/((q:ℝ)*N)}) from by
      by_cases h : 1 ≤ q ∧ q ≤ P ∧ a ≤ q ∧ a.Coprime q
      · have H : {t : ℝ | 1 ≤ q ∧ q ≤ P ∧ a ≤ q ∧ a.Coprime q ∧
          |t-(a:ℝ)/q| ≤ (P:ℝ)/((q:ℝ)*N)} =
          {t : ℝ | |t-(a:ℝ)/q| ≤ (P:ℝ)/((q:ℝ)*N)} := by
          ext t
          exact ⟨fun ht => ht.2.2.2.2, fun ht => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,ht⟩⟩
        rw [H]
        exact measurableSet_le ((continuous_id.sub continuous_const).abs.measurable) measurable_const
      · have H : {t : ℝ | 1 ≤ q ∧ q ≤ P ∧ a ≤ q ∧ a.Coprime q ∧
          |t-(a:ℝ)/q| ≤ (P:ℝ)/((q:ℝ)*N)} = ∅ := by
          ext t
          simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
          intro ht
          exact h ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1⟩
        rw [H]
        exact MeasurableSet.empty

private theorem local_meas (N P : ℕ) : MeasurableSet (localUnion N P) := by
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => measurableSet_Ioc

private theorem starts_null (N P : ℕ) : volume (starts N P) = 0 :=
  ((reduced P).finite_toSet.image _).measure_zero _

theorem masks_agree {N P : ℕ} {t : ℝ} (ht : t < 1-(P:ℝ)/N) (hstart : t ∉ starts N P) :
    t ∈ published N P ↔ t ∈ localUnion N P := by
  constructor
  · rintro ⟨q,a,hq,hqP,ha,hc,hv⟩
    have hlt : a < q := by
      by_contra! H
      have he : a = q := le_antisymm ha H
      subst a
      have h1 : q = 1 := by simpa using hc
      subst q
      simp only [Nat.cast_one, div_one, one_mul] at hv
      linarith [(abs_le.mp hv).1]
    have hi : (q,a) ∈ reduced P := mem_reduced.mpr ⟨hq,hqP,hlt,hc⟩
    refine mem_iUnion₂.mpr ⟨(q,a),hi,?_⟩
    have hb := abs_le.mp hv
    change (a:ℝ)/q-(P:ℝ)/((q:ℝ)*N) < t ∧ t ≤ (a:ℝ)/q+(P:ℝ)/((q:ℝ)*N)
    constructor
    · refine lt_of_le_of_ne (by linarith [hb.1]) ?_
      intro h
      exact hstart ⟨(q,a),hi,h⟩
    · linarith [hb.2]
  · intro H
    obtain ⟨⟨q,a⟩,hi,hm⟩ := mem_iUnion₂.mp H
    obtain ⟨hq,hqP,ha,hc⟩ := mem_reduced.mp hi
    refine ⟨q,a,hq,hqP,ha.le,hc,abs_le.mpr ?_⟩
    change (a:ℝ)/q-(P:ℝ)/((q:ℝ)*N) < t ∧ t ≤ (a:ℝ)/q+(P:ℝ)/((q:ℝ)*N) at hm
    exact ⟨by linarith [hm.1],by linarith [hm.2]⟩

theorem exact_minor_transport {N P : ℕ} (hP : 1 ≤ P) (hPN : 2*(P:ℝ)^2 < (N:ℝ))
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, (published N P)ᶜ.indicator f t) =
      ∫ t in (-(P:ℝ)/N)..(1-(P:ℝ)/N), (localUnion N P)ᶜ.indicator f t := by
  let δ : ℝ := (P:ℝ)/N
  let b := 1-δ
  have hp : (1:ℝ) ≤ P := by exact_mod_cast hP
  have hN : 0 < (N:ℝ) := by nlinarith [sq_nonneg (P:ℝ)]
  have hd : 0 ≤ δ := by dsimp [δ]; positivity
  have hb : 0 ≤ b := by
    dsimp [b,δ]
    have hb' : (P:ℝ)/N ≤ 1 := (div_le_one hN).mpr (by nlinarith)
    linarith
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  let L := (published N P)ᶜ.indicator f
  let R := (localUnion N P)ᶜ.indicator f
  have hL (u v : ℝ) : IntervalIntegrable L volume u v :=
    ⟨(hf.intervalIntegrable u v).1.indicator (published_meas N P).compl,
      (hf.intervalIntegrable u v).2.indicator (published_meas N P).compl⟩
  have hR (u v : ℝ) : IntervalIntegrable R volume u v :=
    ⟨(hf.intervalIntegrable u v).1.indicator (local_meas N P).compl,
      (hf.intervalIntegrable u v).2.indicator (local_meas N P).compl⟩
  have hLeft : (∫ t in -δ..(0:ℝ), R t) = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith : -δ ≤ 0)]
    have H : ∀ t ∈ Ioc (-δ) (0:ℝ), R t = 0 := by
      intro t ht
      dsimp [R]
      apply indicator_of_notMem
      simp only [mem_compl_iff, not_not]
      have h01 : (1,0) ∈ reduced P := mem_reduced.mpr ⟨by decide,hP,by decide,by decide⟩
      apply mem_iUnion₂.mpr
      refine ⟨(1,0),h01,?_⟩
      simp only [arc, PintzMajorArcGeometry.center, radius, Nat.cast_zero, Nat.cast_one, zero_div, one_mul, zero_sub, zero_add]
      exact ⟨ht.1,ht.2.trans hd⟩
    rw [setIntegral_congr_fun measurableSet_Ioc H, integral_zero]
  have hRight : (∫ t in b..(1:ℝ), L t) = 0 := by
    rw [intervalIntegral.integral_of_le hb1]
    have H : ∀ t ∈ Ioc b (1:ℝ), L t = 0 := by
      intro t ht
      dsimp [L]
      apply indicator_of_notMem
      simp only [mem_compl_iff, not_not]
      refine ⟨1,1,le_rfl,hP,le_rfl,by decide,?_⟩
      simp only [Nat.cast_one, div_one, one_mul]
      rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
      exact (show 1-δ<t from ht.1).le |> fun H => by linarith
    rw [setIntegral_congr_fun measurableSet_Ioc H, integral_zero]
  have hcommon : (∫ t in (0:ℝ)..b, L t) = ∫ t in (0:ℝ)..b, R t := by
    rw [intervalIntegral.integral_of_le hb, intervalIntegral.integral_of_le hb]
    apply integral_congr_ae
    change ∀ᵐ t ∂volume.restrict (Ioc 0 b), L t = R t
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hS : ∀ᵐ t : ℝ, t ∉ starts N P := ae_iff.mpr (by
      change volume {t | ¬ t ∉ starts N P} = 0
      simp only [not_not]
      exact starts_null N P)
    have hB : ∀ᵐ t : ℝ, t ≠ b := ae_iff.mpr (by simpa [Set.setOf_eq_eq_singleton] using measure_singleton (μ := volume) b)
    filter_upwards [hS,hB] with t hst htb ht
    have hM := masks_agree (ht.2.lt_of_ne htb) hst
    by_cases hx : t ∈ published N P <;> simp [L,R,hx,← hM]
  rw [show -(P:ℝ)/N = -δ by dsimp [δ]; ring]
  change (∫ t in (0:ℝ)..1, L t) = ∫ t in -δ..b, R t
  rw [← intervalIntegral.integral_add_adjacent_intervals (hL 0 b) (hL b 1), hRight, add_zero,
      ← intervalIntegral.integral_add_adjacent_intervals (hR (-δ) 0) (hR 0 b), hLeft, zero_add]
  exact hcommon

#print axioms exact_minor_transport
end PintzMinorArcTransport
