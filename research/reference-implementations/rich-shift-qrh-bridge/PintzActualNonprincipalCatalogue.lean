/- The compact-subcover argument is adapted from the Apache-2.0
Anthropic formal-math Zeta23.ThmE.SeamL (LSeam_finite_window). -/
import PintzDavenportCount
import PintzWeightedNonprincipalCount
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Set Filter Finset PintzSieveToHybrid
open scoped Topology ComplexOrder

namespace PintzActualNonprincipalCatalogue

theorem finite_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hnp : χ ≠ 1) (T b σ : ℝ) (hσ : 0 ≤ σ) (hb : 0 ≤ b) :
    {z : ℂ | χ.LFunction z = 0 ∧ z.re ∈ Set.Icc σ (1-b) ∧ |z.im| ≤ T}.Finite := by
  have htwo : χ.LFunction (2:ℂ) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hnp) (by norm_num)
  have han : AnalyticOnNhd ℂ χ.LFunction Set.univ :=
    (DirichletCharacter.differentiable_LFunction hnp).differentiableOn.analyticOnNhd isOpen_univ
  have hloc : ∀ z : ℂ, ∃ t ∈ 𝓝 z, (t ∩ {ρ : ℂ | χ.LFunction ρ = 0}).Finite := by
    intro z
    rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with hzero | hcod
    · exact absurd (hzero (mem_univ (2 : ℂ))) htwo
    · rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
      obtain ⟨t, ht, hfin⟩ := hcod z (mem_univ z)
      refine ⟨t, ht, hfin.subset ?_⟩
      rintro s ⟨hst, hs0⟩
      exact ⟨hst, mem_univ s, by simpa using hs0⟩
  let K : Set ℂ := (Set.Icc 0 1) ×ℂ (Set.Icc (-T) T)
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  choose t ht hfin using hloc
  obtain ⟨I, -, hcover⟩ := hKc.elim_nhds_subcover t (fun z _ => ht z)
  have hfinU : (⋃ z ∈ I, (t z ∩ {ρ : ℂ | χ.LFunction ρ = 0})).Finite :=
    I.finite_toSet.biUnion fun z _ => hfin z
  refine hfinU.subset ?_
  rintro z ⟨hz, hre, him⟩
  have hzK : z ∈ K := ⟨⟨hσ.trans hre.1, by linarith [hre.2]⟩, abs_le.mp him⟩
  obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.mp (hcover hzK)
  exact mem_iUnion₂.mpr ⟨s, hs, hzs, hz⟩

noncomputable def catalogue (T b σ : ℝ) (hσ : 0 ≤ σ) (hb : 0 ≤ b)
    (j : PintzDyadicStripCount.Char) : Finset ℂ := by
  classical
  letI : NeZero (j.1+1) := ⟨by omega⟩
  exact if h : j.2 ≠ 1 then (finite_zeros j.2 h T b σ hσ hb).toFinset else ∅

theorem mem_catalogue (T b σ : ℝ) (hσ : 0 ≤ σ) (hb : 0 ≤ b)
    (j : PintzDyadicStripCount.Char) (z : ℂ) :
    z ∈ catalogue T b σ hσ hb j ↔
      j.2 ≠ 1 ∧ j.2.LFunction z = 0 ∧ z.re ∈ Set.Icc σ (1-b) ∧ |z.im| ≤ T := by
  classical
  unfold catalogue
  split_ifs with h <;> simp [h]

theorem mem_family {Q : ℕ} {j : PintzDyadicStripCount.Char} :
    j ∈ family Q → j.1+1 ≤ Q ∧ j.2.IsPrimitive := by
  classical
  intro hj
  obtain ⟨hq,hp⟩ := Finset.mem_sigma.mp hj
  exact ⟨by simpa only [Nat.succ_le_iff, Finset.mem_range] using hq,
    (Finset.mem_filter.mp hp).2⟩

/-- The multiplicity count used by the hybrid sieve, with a single explicit
natural bound independent of character and of the center of the unit box. -/
theorem uniform_local :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Q : ℕ} (hQ : 1 ≤ Q)
      {T b σ : ℝ} (hT : 0 ≤ T) (hb : 0 < b) (hσ : 0 < σ),
      ∀ j ∈ family Q, ∀ x : ℝ,
      ∑ z ∈ (catalogue T b σ hσ.le hb.le j).filter (fun z => |-z.im-x| ≤ 1/2),
        analyticOrderNatAt j.2.LFunction z ≤ ⌈A*Real.log (Q*(T+3))⌉₊ := by
  classical
  obtain ⟨A,hA,hD⟩ := PintzDavenportCount.window_count
  refine ⟨A,hA,?_⟩
  intro Q hQ T b σ hT hb hσ j hj x
  let S := (catalogue T b σ hσ.le hb.le j).filter (fun z => |-z.im-x| ≤ 1/2)
  change (∑ z ∈ S, _) ≤ _
  obtain ⟨hq,hp⟩ := mem_family hj
  letI : NeZero (j.1+1) := ⟨by omega⟩
  have hS (z) (hz : z ∈ S) := (Finset.mem_filter.mp hz)
  by_cases hs : S.Nonempty
  · obtain ⟨z,hz⟩ := hs
    have hh := (mem_catalogue T b σ hσ.le hb.le j z).mp (hS z hz).1
    have hx : |x| ≤ T + 1 := by
      have ht := abs_add_le (-z.im-x) z.im
      rw [show -z.im-x+z.im = -x by ring, abs_neg] at ht
      linarith [hh.2.2.2,(hS z hz).2]
    have hSum := hD (j.1+1) j.2 hp hh.1 (-x) S (fun u hu => by
      have hu' := (mem_catalogue T b σ hσ.le hb.le j u).mp (hS u hu).1
      refine ⟨hσ.trans_le hu'.2.2.1.1, by linarith [hu'.2.2.1.2], ?_⟩
      have hux : |u.im - (-x)| = |-u.im-x| := by rw [← abs_neg]; congr 1; ring
      rw [hux]
      linarith [(hS u hu).2])
    have hqr : ((j.1+1:ℕ):ℝ) ≤ Q := by exact_mod_cast hq
    have hlog : Real.log (((j.1+1:ℕ):ℝ)*(|-x|+2)) ≤ Real.log (Q*(T+3)) :=
      Real.log_le_log (by positivity) (mul_le_mul hqr (by rw [abs_neg]; linarith)
        (by positivity) (by positivity))
    have H := hSum.trans ((mul_le_mul_of_nonneg_left hlog hA).trans (Nat.le_ceil _))
    exact_mod_cast H
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    simp [hs]

#print axioms finite_zeros
#print axioms uniform_local
end PintzActualNonprincipalCatalogue
